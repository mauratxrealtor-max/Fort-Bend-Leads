"""
Fort Bend County Motivated Seller Lead Scraper
===============================================
Portal  : https://ccweb.co.fort-bend.tx.us/
Strategy: Playwright with full session-gate bypass, then search by Date Filed
          filtered by each document type.  Falls back to a broad date search
          and post-filters by doc-type keywords.
Output  : dashboard/records.json  +  data/records.json  +  data/ghl_export.csv
"""

import asyncio
import json
import csv
import io
import os
import re
import time
import zipfile
import struct
import logging
from datetime import datetime, timedelta
from pathlib import Path
from typing import Optional

import requests
from bs4 import BeautifulSoup
from playwright.async_api import async_playwright, TimeoutError as PWTimeout

# ── Logging ───────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-8s  %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger("scraper")

# ── Constants ─────────────────────────────────────────────────────────────────
BASE_URL    = "https://ccweb.co.fort-bend.tx.us"
HOME_URL    = "https://ccweb.co.fort-bend.tx.us/"
SEARCH_URL  = "https://ccweb.co.fort-bend.tx.us/RealEstate/SearchEntry.aspx"

FBCAD_BASE  = "https://www.fbcad.org"

OUTPUT_PATHS = [
    Path(__file__).parent.parent / "dashboard" / "records.json",
    Path(__file__).parent.parent / "data"      / "records.json",
]
GHL_PATH     = Path(__file__).parent.parent / "data" / "ghl_export.csv"
LOOK_BACK_DAYS = 7
RETRY_LIMIT    = 3

# ── Doc-type catalogue ────────────────────────────────────────────────────────
DOC_TYPES = {
    "LP":       ("Lis Pendens",             "Pre-Foreclosure"),
    "NOFC":     ("Notice of Foreclosure",   "Foreclosure"),
    "TAXDEED":  ("Tax Deed",                "Tax Default"),
    "JUD":      ("Judgment",                "Judgment"),
    "CCJ":      ("Certified Judgment",      "Judgment"),
    "DRJUD":    ("Domestic Judgment",       "Judgment"),
    "LNCORPTX": ("Corp Tax Lien",           "Tax Lien"),
    "LNIRS":    ("IRS Lien",                "Federal Lien"),
    "LNFED":    ("Federal Lien",            "Federal Lien"),
    "LN":       ("Lien",                    "Lien"),
    "LNMECH":   ("Mechanic Lien",           "Mechanic Lien"),
    "LNHOA":    ("HOA Lien",               "HOA Lien"),
    "MEDLN":    ("Medicaid Lien",           "Medicaid Lien"),
    "PRO":      ("Probate",                 "Probate"),
    "NOC":      ("Notice of Commencement",  "NOC"),
    "RELLP":    ("Release Lis Pendens",     "Release LP"),
}

# Keywords used to classify raw doc-type strings from the portal
DOC_TYPE_KEYWORDS = {
    "RELLP":    ["RELEASE LIS PENDENS", "REL LIS PENDENS", "RELLP"],
    "LP":       ["LIS PENDENS"],
    "NOFC":     ["NOTICE OF FORECLOSURE", "FORECLOSURE", "NOFC", "NFC"],
    "TAXDEED":  ["TAX DEED"],
    "CCJ":      ["CERTIFIED COPY", "CERTIFIED JUDGMENT", "CCJ"],
    "DRJUD":    ["DOMESTIC RELATION", "DRJUD"],
    "JUD":      ["JUDGMENT", "JUDGEMENT"],
    "LNCORPTX": ["STATE TAX LIEN", "CORP TAX LIEN", "FRANCHISE TAX"],
    "LNIRS":    ["IRS", "INTERNAL REVENUE", "FED TAX LIEN", "FEDERAL TAX"],
    "LNFED":    ["FEDERAL LIEN", "LNFED"],
    "LNMECH":   ["MECHANIC", "MATERIALMAN"],
    "LNHOA":    ["HOA", "HOMEOWNER", "HOME OWNER ASSOC"],
    "MEDLN":    ["MEDICAID", "MEDLN"],
    "PRO":      ["PROBATE", "LETTERS TEST", "LETTERS ADMIN", "WILL"],
    "NOC":      ["NOTICE OF COMMENCEMENT", " NOC"],
    "LN":       ["LIEN"],   # broad — checked last
}


def classify_doc_type(raw: str) -> tuple[str, str]:
    u = raw.upper().strip()
    for code, keywords in DOC_TYPE_KEYWORDS.items():
        for kw in keywords:
            if kw in u:
                return code, DOC_TYPES[code][0]
    return "OTHER", raw.title()


# ── Scoring ───────────────────────────────────────────────────────────────────
def score_record(rec: dict) -> tuple[int, list[str]]:
    flags, pts = [], 30
    cat = rec.get("cat", "")
    amt = 0
    try:
        amt = float(str(rec.get("amount") or "0").replace(",", "").replace("$", ""))
    except Exception:
        pass

    if cat in ("LP", "RELLP"):         flags.append("Lis pendens")
    if cat in ("LP", "NOFC"):          flags.append("Pre-foreclosure")
    if cat in ("JUD", "CCJ", "DRJUD"): flags.append("Judgment lien")
    if cat in ("LNCORPTX", "LNIRS", "LNFED", "TAXDEED"): flags.append("Tax lien")
    if cat == "LNMECH":  flags.append("Mechanic lien")
    if cat == "PRO":     flags.append("Probate / estate")
    if re.search(r"\b(LLC|INC|CORP|LTD|LP|TRUST)\b", rec.get("owner", ""), re.I):
        flags.append("LLC / corp owner")
    try:
        if datetime.strptime(rec.get("filed", ""), "%Y-%m-%d") >= datetime.now() - timedelta(days=7):
            flags.append("New this week")
    except Exception:
        pass

    pts += len(flags) * 10
    if "Lis pendens" in flags and "Pre-foreclosure" in flags: pts += 20
    if amt > 100_000: pts += 15
    elif amt > 50_000: pts += 10
    if "New this week" in flags: pts += 5
    if rec.get("prop_address") or rec.get("mail_address"): pts += 5
    return min(pts, 100), flags


# ═══════════════════════════════════════════════════════════════════════════════
#  PARCEL DB  (Fort Bend CAD bulk data)
# ═══════════════════════════════════════════════════════════════════════════════
class ParcelDB:
    BULK_URLS = [
        "https://www.fbcad.org/Property-Data/Bulk-Data-Downloads/",
        "https://downloads.fbcad.org/",
        "https://www.fbcad.org/resources/bulk-data/",
    ]

    def __init__(self):
        self._by_owner: dict[str, dict] = {}
        self._loaded = False

    def load(self):
        for url in self.BULK_URLS:
            try:
                log.info("Trying FBCAD bulk data: %s", url)
                if self._try_load_from_page(url):
                    log.info("Parcel DB loaded — %d records", len(self._by_owner))
                    self._loaded = True
                    return
            except Exception as e:
                log.warning("FBCAD %s failed: %s", url, e)
        log.warning("Parcel DB unavailable — address enrichment skipped")

    def lookup(self, owner: str) -> Optional[dict]:
        if not self._loaded or not owner:
            return None
        for v in self._name_variants(owner):
            hit = self._by_owner.get(v)
            if hit:
                return hit
        return None

    def _try_load_from_page(self, page_url: str) -> bool:
        sess = requests.Session()
        r = self._get(sess, page_url, timeout=20)
        soup = BeautifulSoup(r.text, "lxml")
        for a in soup.find_all("a", href=True):
            href = a["href"]
            if re.search(r"\.(zip|dbf|csv)(\?.*)?$", href, re.I):
                dl_url = href if href.startswith("http") else FBCAD_BASE + href
                log.info("Downloading parcel file: %s", dl_url)
                return self._download_and_parse(sess, dl_url)
        return False

    def _download_and_parse(self, sess, url: str) -> bool:
        r = self._get(sess, url, timeout=90, stream=True)
        content, ct = r.content, r.headers.get("content-type", "").lower()
        if "zip" in ct or url.lower().endswith(".zip"):
            try:
                zf = zipfile.ZipFile(io.BytesIO(content))
                for name in zf.namelist():
                    data = zf.read(name)
                    if name.lower().endswith(".dbf"):
                        self._parse_dbf_bytes(data)
                        return bool(self._by_owner)
                    if name.lower().endswith(".csv"):
                        self._parse_csv_bytes(data)
                        return bool(self._by_owner)
            except Exception as e:
                log.warning("ZIP: %s", e)
        elif url.lower().endswith(".dbf"):
            self._parse_dbf_bytes(content)
            return bool(self._by_owner)
        elif url.lower().endswith(".csv") or "csv" in ct or "text" in ct:
            self._parse_csv_bytes(content)
            return bool(self._by_owner)
        return False

    def _parse_dbf_bytes(self, data: bytes):
        try:
            import tempfile
            with tempfile.NamedTemporaryFile(delete=False, suffix=".dbf") as f:
                f.write(data)
                tmp = f.name
            try:
                from dbfread import DBF
                for rec in DBF(tmp, encoding="latin-1", load=True):
                    self._ingest_row(dict(rec))
            finally:
                os.unlink(tmp)
        except ImportError:
            self._parse_dbf_raw(data)

    def _parse_dbf_raw(self, data: bytes):
        try:
            if len(data) < 32:
                return
            num_recs  = struct.unpack_from("<I", data, 4)[0]
            hdr_bytes = struct.unpack_from("<H", data, 8)[0]
            rec_size  = struct.unpack_from("<H", data, 10)[0]
            fields, pos = [], 32
            while pos < hdr_bytes - 1:
                if data[pos] == 0x0D:
                    break
                name = data[pos:pos+11].rstrip(b"\x00").decode("latin-1")
                flen = data[pos+16]
                fields.append((name, flen))
                pos += 32
            for i in range(num_recs):
                rs = hdr_bytes + i * rec_size
                if rs + rec_size > len(data):
                    break
                if data[rs] == 0x2A:
                    continue
                row, col = {}, rs + 1
                for fname, flen in fields:
                    row[fname] = data[col:col+flen].decode("latin-1").strip()
                    col += flen
                self._ingest_row(row)
        except Exception as e:
            log.warning("DBF raw: %s", e)

    def _parse_csv_bytes(self, data: bytes):
        try:
            reader = csv.DictReader(io.StringIO(data.decode("latin-1", errors="replace")))
            for row in reader:
                self._ingest_row(row)
        except Exception as e:
            log.warning("CSV: %s", e)

    def _ingest_row(self, row: dict):
        r = {k.upper().strip(): str(v).strip() for k, v in row.items()}
        owner = (r.get("OWNER") or r.get("OWN1") or r.get("OWNER_NAME") or
                 r.get("OWNERNAME") or "").strip()
        if not owner:
            return
        parcel = {
            "prop_address": r.get("SITE_ADDR") or r.get("SITEADDR") or r.get("SITE_ADDRESS") or "",
            "prop_city":    r.get("SITE_CITY") or r.get("SITECITY") or "",
            "prop_state":   "TX",
            "prop_zip":     r.get("SITE_ZIP") or r.get("SITEZIP") or "",
            "mail_address": r.get("ADDR_1") or r.get("MAILADR1") or r.get("MAILADDR1") or "",
            "mail_city":    r.get("CITY") or r.get("MAILCITY") or "",
            "mail_state":   r.get("STATE") or r.get("MAILSTATE") or "TX",
            "mail_zip":     r.get("ZIP") or r.get("MAILZIP") or "",
        }
        for v in self._name_variants(owner):
            self._by_owner.setdefault(v, parcel)

    @staticmethod
    def _name_variants(name: str) -> list[str]:
        n = name.upper().strip()
        variants = {n}
        if "," in n:
            parts = [p.strip() for p in n.split(",", 1)]
            variants.add(f"{parts[1]} {parts[0]}")
            variants.add(f"{parts[0]} {parts[1]}")
        else:
            words = n.split()
            if len(words) >= 2:
                variants.add(f"{words[-1]}, {' '.join(words[:-1])}")
                variants.add(f"{words[-1]} {' '.join(words[:-1])}")
        return variants

    @staticmethod
    def _get(sess, url, **kw):
        for attempt in range(RETRY_LIMIT):
            try:
                r = sess.get(url, headers={"User-Agent": "Mozilla/5.0"}, **kw)
                r.raise_for_status()
                return r
            except Exception as e:
                if attempt == RETRY_LIMIT - 1:
                    raise
                time.sleep(2 ** attempt)


# ═══════════════════════════════════════════════════════════════════════════════
#  CLERK SCRAPER
# ═══════════════════════════════════════════════════════════════════════════════
class ClerkScraper:
    """
    Fort Bend County Clerk portal scraper.

    Session gate flow:
      GET /  →  click "Official Public Records"  →  click "Search Real Estate"
      →  fill date + doc type  →  parse results table  →  paginate

    Falls back to a broad date-only search if per-type search yields nothing.
    """

    def __init__(self, parcel_db: ParcelDB):
        self.parcel_db = parcel_db
        self.records: list[dict] = []

    async def run(self):
        date_from = (datetime.now() - timedelta(days=LOOK_BACK_DAYS)).strftime("%m/%d/%Y")
        date_to   = datetime.now().strftime("%m/%d/%Y")
        log.info("Fort Bend Clerk search window: %s → %s", date_from, date_to)

        async with async_playwright() as pw:
            browser = await pw.chromium.launch(
                headless=True,
                args=["--no-sandbox", "--disable-setuid-sandbox",
                      "--disable-blink-features=AutomationControlled"],
            )
            ctx = await browser.new_context(
                user_agent=(
                    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                    "AppleWebKit/537.36 (KHTML, like Gecko) "
                    "Chrome/122.0.0.0 Safari/537.36"
                ),
                viewport={"width": 1280, "height": 800},
                ignore_https_errors=True,
            )
            await ctx.add_init_script(
                "Object.defineProperty(navigator,'webdriver',{get:()=>undefined});"
                "Object.defineProperty(navigator,'plugins',{get:()=>[1,2,3]});"
                "window.chrome={runtime:{}};"
            )
            page = await ctx.new_page()

            # ── Step 1: navigate through the session gate ─────────────────────
            reached_form = await self._navigate_to_search(page)
            if not reached_form:
                log.error("Could not reach search form — aborting")
                await browser.close()
                return

            # ── Step 2: discover available dropdown options ───────────────────
            available_opts = await self._get_dropdown_options(page)
            log.info("Portal dropdown has %d instrument types", len(available_opts))

            # ── Step 3: search per doc type ───────────────────────────────────
            found_any = False
            for code, (label, _) in DOC_TYPES.items():
                for attempt in range(RETRY_LIMIT):
                    try:
                        recs = await self._search_one(
                            page, code, label, available_opts, date_from, date_to
                        )
                        if recs:
                            found_any = True
                        self.records.extend(recs)
                        log.info("  [%s] %s: %d records", code, label, len(recs))
                        break
                    except PWTimeout:
                        log.warning("  Timeout [%s] attempt %d", code, attempt + 1)
                        await asyncio.sleep(3)
                        await self._navigate_to_search(page)
                    except Exception as e:
                        log.warning("  Error [%s]: %s", code, e)
                        break

            # ── Step 4: broad fallback if nothing found ───────────────────────
            if not found_any:
                log.info("Per-type search yielded 0 — running broad date search…")
                broad_recs = await self._broad_date_search(page, date_from, date_to)
                self.records.extend(broad_recs)
                log.info("Broad search: %d records", len(broad_recs))

            await browser.close()

        log.info("Scraper finished — %d total raw records", len(self.records))

    # ── Session navigation ────────────────────────────────────────────────────
    async def _navigate_to_search(self, page) -> bool:
        """Navigate from the portal home through the session gate to the search form."""
        log.info("Navigating to Fort Bend Clerk search form…")
        for attempt in range(RETRY_LIMIT):
            try:
                await page.goto(HOME_URL, timeout=30_000, wait_until="domcontentloaded")
                await asyncio.sleep(2)
                html = await page.content()

                # Handle browser-test / session splash
                if any(kw in html.lower() for kw in
                       ["browser test", "keep working", "session will end",
                        "connection throughput"]):
                    log.info("  Session gate detected — clicking through…")
                    for label in ["Keep Working", "Continue", "Enter", "Proceed",
                                  "Accept", "Yes"]:
                        btn = page.locator(
                            f"input[value='{label}'], "
                            f"input[value='{label.upper()}'], "
                            f"button:has-text('{label}')"
                        )
                        if await btn.count() > 0:
                            await btn.first.click()
                            await asyncio.sleep(2)
                            break
                    else:
                        # Click any submit button
                        sub = page.locator("input[type='submit'], button[type='submit']")
                        if await sub.count() > 0:
                            await sub.first.click()
                            await asyncio.sleep(2)
                    html = await page.content()

                # Click "Official Public Records"
                opr = page.locator(
                    "a:has-text('Official Public Records'), "
                    "a:has-text('OFFICIAL PUBLIC RECORDS'), "
                    "a[href*='OfficialPublic'], a[href*='RealEstate']"
                )
                if await opr.count() > 0:
                    await opr.first.click()
                    await page.wait_for_load_state("domcontentloaded", timeout=15_000)
                    await asyncio.sleep(1)

                # Click "Search Real Estate Index"
                sei = page.locator(
                    "a:has-text('Search Real Estate'), "
                    "a:has-text('SEARCH REAL ESTATE'), "
                    "a[href*='SearchEntry']"
                )
                if await sei.count() > 0:
                    await sei.first.click()
                    await page.wait_for_load_state("domcontentloaded", timeout=15_000)
                    await asyncio.sleep(1)
                else:
                    await page.goto(SEARCH_URL, timeout=20_000,
                                    wait_until="domcontentloaded")
                    await asyncio.sleep(1)

                html = await page.content()
                if self._is_search_form(html):
                    log.info("  ✓ Search form reached")
                    return True

                # Direct navigation as last resort
                await page.goto(SEARCH_URL, timeout=20_000, wait_until="domcontentloaded")
                await asyncio.sleep(1)
                if self._is_search_form(await page.content()):
                    log.info("  ✓ Direct navigation succeeded")
                    return True

            except Exception as e:
                log.warning("  Navigation attempt %d failed: %s", attempt + 1, e)
                await asyncio.sleep(3)

        return False

    @staticmethod
    def _is_search_form(html: str) -> bool:
        h = html.lower()
        return (("date" in h or "instrument" in h) and
                ("search" in h or "grantor" in h or "party" in h))

    async def _get_dropdown_options(self, page) -> dict[str, str]:
        """Return {UPPER_TEXT: value} from the instrument-type dropdown."""
        for sel_pat in [
            "select[name*='InstrumentType']", "select[name*='DocType']",
            "select[name*='Type']",            "select[id*='Instrument']",
            "select[id*='DocType']",
        ]:
            sel = page.locator(sel_pat)
            if await sel.count() > 0:
                opts = await sel.first.evaluate("""el => Array.from(el.options).map(o => ({
                    text: o.text.trim(), value: o.value.trim()
                }))""")
                return {o["text"].upper(): (o["value"] or o["text"])
                        for o in opts
                        if o["text"] and o["text"].upper() not in
                        ("", "-- SELECT --", "SELECT TYPE", "ALL TYPES", "ALL")}
        return {}

    # ── Per-type search ───────────────────────────────────────────────────────
    async def _search_one(self, page, code: str, label: str,
                           available_opts: dict, date_from: str, date_to: str) -> list[dict]:
        await page.goto(SEARCH_URL, timeout=20_000, wait_until="domcontentloaded")
        await asyncio.sleep(0.5)

        html = await page.content()
        # Re-establish session if expired
        if "session" in html.lower() and "end" in html.lower():
            await self._navigate_to_search(page)
            await page.goto(SEARCH_URL, timeout=20_000, wait_until="domcontentloaded")
            await asyncio.sleep(0.5)

        # Fill dates
        await self._fill_dates(page, date_from, date_to)

        # Fill doc type
        type_set = await self._fill_doc_type(page, code, label, available_opts)

        # Submit
        await self._submit(page)
        await asyncio.sleep(1)

        return await self._paginate(page, code, label, type_set)

    async def _fill_dates(self, page, date_from: str, date_to: str):
        for patterns, value in [
            (["DateFrom", "StartDate", "BeginDate", "FromDate",
              "FileDateFrom", "RecordedDateFrom"], date_from),
            (["DateTo",   "EndDate",   "ToDate",
              "FileDateTo",   "RecordedDateTo"],   date_to),
        ]:
            for p in patterns:
                fld = page.locator(f"input[name*='{p}'], input[id*='{p}']")
                if await fld.count() > 0:
                    await fld.first.triple_click()
                    await fld.first.fill(value)
                    break

    async def _fill_doc_type(self, page, code: str, label: str,
                              available_opts: dict) -> bool:
        candidates = DOC_TYPE_KEYWORDS.get(code, [label.upper()])
        for sel_pat in [
            "select[name*='InstrumentType']", "select[name*='DocType']",
            "select[name*='Type']",            "select[id*='Instrument']",
        ]:
            sel = page.locator(sel_pat)
            if await sel.count() == 0:
                continue
            # Match against available options
            for opt_text, opt_val in available_opts.items():
                for cand in candidates:
                    if cand.upper() in opt_text or opt_text in cand.upper():
                        try:
                            await sel.first.select_option(value=opt_val)
                            return True
                        except Exception:
                            pass
            # Partial word match fallback
            label_words = [w for w in label.upper().split() if len(w) > 3]
            for opt_text, opt_val in available_opts.items():
                if any(w in opt_text for w in label_words):
                    try:
                        await sel.first.select_option(value=opt_val)
                        return True
                    except Exception:
                        pass
        return False

    async def _submit(self, page):
        for pat in [
            "input[value='Search']", "input[value='SEARCH']",
            "input[id*='Search'][type='submit']",
            "button:has-text('Search')", "input[type='submit']",
        ]:
            btn = page.locator(pat)
            if await btn.count() > 0:
                await btn.first.click()
                try:
                    await page.wait_for_load_state("domcontentloaded", timeout=20_000)
                except PWTimeout:
                    pass
                return
        await page.keyboard.press("Enter")
        await asyncio.sleep(2)

    async def _paginate(self, page, code: str, label: str,
                         exact: bool) -> list[dict]:
        all_recs, page_num = [], 1
        while True:
            recs = self._parse_table(await page.content(), code, label, exact)
            all_recs.extend(recs)

            next_btn = page.locator(
                "a:has-text('Next'), a:has-text('>>'), "
                "input[value*='Next >'], a[id*='Next'], a[id*='next']"
            )
            if await next_btn.count() == 0 or (not recs and page_num > 1):
                break
            try:
                await next_btn.first.click()
                await page.wait_for_load_state("domcontentloaded", timeout=15_000)
                await asyncio.sleep(0.6)
            except Exception:
                break
            page_num += 1
            if page_num > 30:
                break
        return all_recs

    # ── Broad date search fallback ────────────────────────────────────────────
    async def _broad_date_search(self, page, date_from: str, date_to: str) -> list[dict]:
        await page.goto(SEARCH_URL, timeout=20_000, wait_until="domcontentloaded")
        await asyncio.sleep(0.5)
        await self._fill_dates(page, date_from, date_to)
        await self._submit(page)
        await asyncio.sleep(1)
        all_recs = await self._paginate(page, "OTHER", "All Types", False)
        return [r for r in all_recs if r["cat"] != "OTHER"]

    # ── HTML table parser ─────────────────────────────────────────────────────
    def _parse_table(self, html: str, code: str, label: str,
                     exact_type: bool) -> list[dict]:
        soup    = BeautifulSoup(html, "lxml")
        today   = datetime.now()
        records = []

        # Find the results table (skip layout tables)
        target = None
        for tbl in soup.find_all("table"):
            cells = tbl.find_all(["th", "td"])
            if len(cells) < 4:
                continue
            cell_text = " ".join(c.get_text(strip=True).lower() for c in cells[:25])
            if any(kw in cell_text for kw in
                   ["grantor", "grantee", "instrument", "filed", "recorded"]):
                target = tbl
                break
        if not target:
            return records

        # Detect columns from header row
        hrow = target.find("tr")
        if not hrow:
            return records

        col_map = {}
        for i, cell in enumerate(hrow.find_all(["th", "td"])):
            h = cell.get_text(strip=True).lower()
            if re.search(r"inst(rument)?\s*(num|#|no|number)", h):
                col_map.setdefault("doc_num", i)
            elif re.search(r"(instrument|doc(ument)?)\s*type|type", h):
                col_map.setdefault("doc_type", i)
            elif re.search(r"(file|record)(ed)?\s*date|date\s*(file|record)", h):
                col_map.setdefault("filed", i)
            elif re.search(r"grantor|party\s*1|seller|owner", h):
                col_map.setdefault("owner", i)
            elif re.search(r"grantee|party\s*2|buyer", h):
                col_map.setdefault("grantee", i)
            elif re.search(r"legal|desc(ription)?|abstract", h):
                col_map.setdefault("legal", i)
            elif re.search(r"amount|consider|price|value", h):
                col_map.setdefault("amount", i)

        # Fallback: assume Fort Bend typical column order
        if not col_map:
            col_map = {
                "doc_num": 0, "doc_type": 1, "filed": 2,
                "owner": 3, "grantee": 4, "legal": 5, "amount": 6,
            }

        for tr in target.find_all("tr")[1:]:
            try:
                cells = tr.find_all(["td", "th"])
                if len(cells) < 2:
                    continue
                texts = [c.get_text(" ", strip=True) for c in cells]

                def _get(key, default=""):
                    idx = col_map.get(key)
                    return texts[idx].strip() if idx is not None and idx < len(texts) else default

                doc_num      = _get("doc_num") or (texts[0] if texts else "")
                raw_doc_type = _get("doc_type")
                raw_date     = _get("filed")
                raw_owner    = _get("owner")

                if not doc_num.strip() or re.match(
                        r"^(instrument\s*#|doc\s*#|num|no\.?)$",
                        doc_num.strip(), re.I):
                    continue

                # Parse date
                filed_str = ""
                for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y"):
                    try:
                        filed_str = datetime.strptime(raw_date.strip(), fmt).strftime("%Y-%m-%d")
                        break
                    except Exception:
                        pass
                if not filed_str:
                    continue

                # Skip outside window
                try:
                    if (today - datetime.strptime(filed_str, "%Y-%m-%d")).days > LOOK_BACK_DAYS + 1:
                        continue
                except Exception:
                    continue

                # Classify doc type
                if exact_type:
                    rec_code, rec_label = code, label
                else:
                    rec_code, rec_label = classify_doc_type(raw_doc_type or label)

                # Build direct clerk URL
                doc_idx = col_map.get("doc_num", 0)
                link = ""
                if doc_idx < len(cells):
                    a = cells[doc_idx].find("a")
                    if a and a.get("href"):
                        href = a["href"]
                        link = href if href.startswith("http") else BASE_URL + "/" + href.lstrip("/")

                rec = {
                    "doc_num":      doc_num.strip(),
                    "doc_type":     raw_doc_type or rec_label,
                    "filed":        filed_str,
                    "cat":          rec_code,
                    "cat_label":    rec_label,
                    "owner":        raw_owner,
                    "grantee":      _get("grantee"),
                    "amount":       _get("amount"),
                    "legal":        _get("legal"),
                    "clerk_url":    link or SEARCH_URL,
                    "prop_address": "",
                    "prop_city":    "",
                    "prop_state":   "TX",
                    "prop_zip":     "",
                    "mail_address": "",
                    "mail_city":    "",
                    "mail_state":   "TX",
                    "mail_zip":     "",
                }

                parcel = self.parcel_db.lookup(raw_owner)
                if parcel:
                    rec.update({k: v for k, v in parcel.items() if v})

                rec["flags"], rec["score"] = score_record(rec)
                records.append(rec)

            except Exception as e:
                log.debug("Row error: %s", e)

        return records


# ═══════════════════════════════════════════════════════════════════════════════
#  OUTPUT
# ═══════════════════════════════════════════════════════════════════════════════
def deduplicate(records: list[dict]) -> list[dict]:
    seen, out = set(), []
    for r in records:
        key = (r.get("doc_num", ""), r.get("cat", ""), r.get("filed", ""))
        if key not in seen:
            seen.add(key)
            out.append(r)
    return out


def build_output(records: list[dict]) -> dict:
    now = datetime.utcnow()
    return {
        "fetched_at":   now.isoformat() + "Z",
        "source":       "Fort Bend County Clerk (ccweb.co.fort-bend.tx.us) + Fort Bend CAD",
        "date_range":   {
            "from": (now - timedelta(days=LOOK_BACK_DAYS)).strftime("%Y-%m-%d"),
            "to":   now.strftime("%Y-%m-%d"),
        },
        "total":        len(records),
        "with_address": sum(1 for r in records
                            if r.get("prop_address") or r.get("mail_address")),
        "records":      sorted(records, key=lambda x: x.get("score", 0), reverse=True),
    }


def save_json(data: dict):
    for path in OUTPUT_PATHS:
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w") as f:
            json.dump(data, f, indent=2, default=str)
        log.info("Saved → %s", path)


def save_ghl_csv(records: list[dict]):
    GHL_PATH.parent.mkdir(parents=True, exist_ok=True)
    cols = [
        "First Name", "Last Name",
        "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
        "Property Address", "Property City", "Property State", "Property Zip",
        "Lead Type", "Document Type", "Date Filed", "Document Number",
        "Amount/Debt Owed", "Seller Score", "Motivated Seller Flags",
        "Source", "Public Records URL",
    ]
    with open(GHL_PATH, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols, extrasaction="ignore")
        w.writeheader()
        for r in records:
            parts = re.sub(r"[,]", " ", r.get("owner", "")).split()
            w.writerow({
                "First Name":             parts[0] if parts else "",
                "Last Name":              " ".join(parts[1:]) if len(parts) > 1 else "",
                "Mailing Address":        r.get("mail_address", ""),
                "Mailing City":           r.get("mail_city", ""),
                "Mailing State":          r.get("mail_state", "TX"),
                "Mailing Zip":            r.get("mail_zip", ""),
                "Property Address":       r.get("prop_address", ""),
                "Property City":          r.get("prop_city", ""),
                "Property State":         r.get("prop_state", "TX"),
                "Property Zip":           r.get("prop_zip", ""),
                "Lead Type":              r.get("cat_label", ""),
                "Document Type":          r.get("doc_type", ""),
                "Date Filed":             r.get("filed", ""),
                "Document Number":        r.get("doc_num", ""),
                "Amount/Debt Owed":       r.get("amount", ""),
                "Seller Score":           r.get("score", 0),
                "Motivated Seller Flags": "; ".join(r.get("flags", [])),
                "Source":                 "Fort Bend County Clerk",
                "Public Records URL":     r.get("clerk_url", ""),
            })
    log.info("GHL CSV → %s  (%d rows)", GHL_PATH, len(records))


# ═══════════════════════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════════════════════
async def main():
    log.info("=" * 60)
    log.info("Fort Bend County Motivated Seller Scraper")
    log.info("=" * 60)

    parcel_db = ParcelDB()
    parcel_db.load()

    scraper = ClerkScraper(parcel_db)
    await scraper.run()
    records = deduplicate(scraper.records)

    log.info("After dedup: %d records", len(records))
    output = build_output(records)
    save_json(output)
    save_ghl_csv(records)

    log.info(
        "Done — Total=%d  WithAddress=%d  HotLeads(>=70)=%d",
        output["total"],
        output["with_address"],
        sum(1 for r in records if r.get("score", 0) >= 70),
    )


if __name__ == "__main__":
    asyncio.run(main())
