"""
Fort Bend County Motivated Seller Lead Scraper
Targets: Harris County Clerk portal + Fort Bend CAD bulk parcel data
Runs daily via GitHub Actions, outputs dashboard/records.json + data/records.json
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

# ── Logging ──────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s  %(levelname)-8s  %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
log = logging.getLogger("scraper")

# ── Constants ─────────────────────────────────────────────────────────────────
CLERK_URL      = "https://cclerk.hctx.net/PublicRecords.aspx"
FBCAD_BASE     = "https://www.fbcad.org"          # Fort Bend CAD
FBCAD_EXPORT   = "https://www.fbcad.org/Property-Search/Export-Data/"  # may redirect
OUTPUT_PATHS   = [
    Path(__file__).parent.parent / "dashboard" / "records.json",
    Path(__file__).parent.parent / "data"      / "records.json",
]
GHL_PATH       = Path(__file__).parent.parent / "data" / "ghl_export.csv"
LOOK_BACK_DAYS = 7
RETRY_LIMIT    = 3

# ── Doc-type catalogue ────────────────────────────────────────────────────────
DOC_TYPES = {
    "LP":        ("Lis Pendens",              "⚠️ Pre-Foreclosure"),
    "NOFC":      ("Notice of Foreclosure",    "🔴 Foreclosure"),
    "TAXDEED":   ("Tax Deed",                 "💸 Tax Default"),
    "JUD":       ("Judgment",                 "⚖️ Judgment"),
    "CCJ":       ("Certified Judgment",       "⚖️ Judgment"),
    "DRJUD":     ("Domestic Judgment",        "⚖️ Judgment"),
    "LNCORPTX":  ("Corp Tax Lien",            "🏛️ Tax Lien"),
    "LNIRS":     ("IRS Lien",                 "🏛️ Federal Lien"),
    "LNFED":     ("Federal Lien",             "🏛️ Federal Lien"),
    "LN":        ("Lien",                     "🔗 Lien"),
    "LNMECH":    ("Mechanic Lien",            "🔧 Mechanic Lien"),
    "LNHOA":     ("HOA Lien",                 "🏘️ HOA Lien"),
    "MEDLN":     ("Medicaid Lien",            "🏥 Medicaid Lien"),
    "PRO":       ("Probate",                  "📜 Probate"),
    "NOC":       ("Notice of Commencement",   "🔨 NOC"),
    "RELLP":     ("Release Lis Pendens",      "✅ Release LP"),
}

# ── Scoring helpers ────────────────────────────────────────────────────────────
def score_record(rec: dict) -> tuple[int, list[str]]:
    flags  = []
    pts    = 30   # base

    cat = rec.get("cat", "")
    amt = rec.get("amount") or 0
    try:
        amt = float(str(amt).replace(",", "").replace("$", "")) if amt else 0
    except Exception:
        amt = 0

    # Flag assignment
    if cat in ("LP", "RELLP"):
        flags.append("Lis pendens")
    if cat in ("LP", "NOFC"):
        flags.append("Pre-foreclosure")
    if cat in ("JUD", "CCJ", "DRJUD"):
        flags.append("Judgment lien")
    if cat in ("LNCORPTX", "LNIRS", "LNFED", "TAXDEED"):
        flags.append("Tax lien")
    if cat == "LNMECH":
        flags.append("Mechanic lien")
    if cat == "PRO":
        flags.append("Probate / estate")

    owner = rec.get("owner", "")
    if re.search(r"\b(LLC|INC|CORP|LTD|LP|TRUST)\b", owner, re.I):
        flags.append("LLC / corp owner")

    try:
        filed_dt = datetime.strptime(rec.get("filed", ""), "%Y-%m-%d")
        if filed_dt >= datetime.now() - timedelta(days=7):
            flags.append("New this week")
    except Exception:
        pass

    # Points
    pts += len(flags) * 10

    # LP + FC combo bonus
    if "Lis pendens" in flags and "Pre-foreclosure" in flags:
        pts += 20

    if amt > 100_000:
        pts += 15
    elif amt > 50_000:
        pts += 10

    if "New this week" in flags:
        pts += 5

    has_addr = bool(rec.get("prop_address") or rec.get("mail_address"))
    if has_addr:
        pts += 5

    return min(pts, 100), flags


# ═══════════════════════════════════════════════════════════════════════════════
#  PART 1 — Fort Bend CAD parcel lookup
# ═══════════════════════════════════════════════════════════════════════════════

class ParcelDB:
    """
    Loads Fort Bend CAD bulk export into memory for owner→address lookup.
    Tries several known URL patterns; falls back gracefully if unavailable.
    """

    BULK_URLS = [
        "https://www.fbcad.org/Property-Data/Bulk-Data-Downloads/",
        "https://downloads.fbcad.org/",
        "https://www.fbcad.org/resources/bulk-data/",
    ]

    def __init__(self):
        self._by_owner: dict[str, dict] = {}   # normalised name → parcel dict
        self._loaded   = False

    # ── public API ─────────────────────────────────────────────────────────
    def load(self):
        for url in self.BULK_URLS:
            try:
                log.info("Trying FBCAD bulk data at %s", url)
                if self._try_load_from_page(url):
                    log.info("Parcel DB loaded — %d records", len(self._by_owner))
                    self._loaded = True
                    return
            except Exception as exc:
                log.warning("FBCAD attempt failed (%s): %s", url, exc)
        log.warning("Parcel DB unavailable — address enrichment will be skipped")

    def lookup(self, owner_name: str) -> Optional[dict]:
        if not self._loaded:
            return None
        for variant in self._name_variants(owner_name):
            hit = self._by_owner.get(variant)
            if hit:
                return hit
        return None

    # ── internals ──────────────────────────────────────────────────────────
    def _try_load_from_page(self, page_url: str) -> bool:
        sess = requests.Session()
        r = self._get(sess, page_url, timeout=20)
        soup = BeautifulSoup(r.text, "lxml")

        # Find a link to a zip / csv / dbf bulk download
        for a in soup.find_all("a", href=True):
            href = a["href"]
            if re.search(r"\.(zip|dbf|csv)(\?.*)?$", href, re.I):
                dl_url = href if href.startswith("http") else FBCAD_BASE + href
                log.info("Downloading parcel bulk file: %s", dl_url)
                return self._download_and_parse(sess, dl_url)

        # Try __doPostBack forms
        form = soup.find("form")
        if form:
            for inp in soup.find_all("input", {"type": "submit"}):
                val = inp.get("value", "")
                if re.search(r"(download|export|bulk|all)", val, re.I):
                    event_target = inp.get("name", "")
                    payload = self._build_viewstate_payload(soup, event_target, "")
                    r2 = sess.post(page_url, data=payload, timeout=60)
                    if self._looks_like_data(r2):
                        return self._parse_response(r2)
        return False

    def _download_and_parse(self, sess, url: str) -> bool:
        r = self._get(sess, url, timeout=90, stream=True)
        content = r.content
        ct = r.headers.get("content-type", "").lower()

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
                log.warning("ZIP parse error: %s", e)
        elif url.lower().endswith(".dbf"):
            self._parse_dbf_bytes(content)
            return bool(self._by_owner)
        elif url.lower().endswith(".csv") or "csv" in ct or "text" in ct:
            self._parse_csv_bytes(content)
            return bool(self._by_owner)
        return False

    def _parse_response(self, r) -> bool:
        ct = r.headers.get("content-type", "").lower()
        if "csv" in ct or "text" in ct:
            self._parse_csv_bytes(r.content)
        elif "zip" in ct:
            self._download_and_parse(requests.Session(), r.url)
        return bool(self._by_owner)

    # ── DBF parser (pure-Python, no external lib required) ────────────────
    def _parse_dbf_bytes(self, data: bytes):
        """Minimal DBF reader — handles dBASE III/IV format."""
        try:
            # Try dbfread first (installed in requirements)
            import tempfile, os
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
        """Fallback minimal DBF III parser."""
        try:
            if len(data) < 32:
                return
            num_recs  = struct.unpack_from("<I", data, 4)[0]
            hdr_bytes = struct.unpack_from("<H", data, 8)[0]
            rec_size  = struct.unpack_from("<H", data, 10)[0]
            fields = []
            pos = 32
            while pos < hdr_bytes - 1:
                if data[pos] == 0x0D:
                    break
                name   = data[pos:pos+11].rstrip(b"\x00").decode("latin-1")
                ftype  = chr(data[pos+11])
                flen   = data[pos+16]
                fields.append((name, ftype, flen))
                pos += 32
            for i in range(num_recs):
                rec_start = hdr_bytes + i * rec_size
                if rec_start + rec_size > len(data):
                    break
                if data[rec_start] == 0x2A:   # deleted
                    continue
                row, col = {}, rec_start + 1
                for fname, ftype, flen in fields:
                    raw = data[col:col+flen].decode("latin-1").strip()
                    row[fname] = raw
                    col += flen
                self._ingest_row(row)
        except Exception as e:
            log.warning("DBF raw parse error: %s", e)

    def _parse_csv_bytes(self, data: bytes):
        try:
            text = data.decode("latin-1", errors="replace")
            reader = csv.DictReader(io.StringIO(text))
            for row in reader:
                self._ingest_row(row)
        except Exception as e:
            log.warning("CSV parse error: %s", e)

    def _ingest_row(self, row: dict):
        # Normalise keys upper-case
        r = {k.upper().strip(): str(v).strip() for k, v in row.items()}

        owner = (r.get("OWNER") or r.get("OWN1") or r.get("OWNER_NAME") or
                 r.get("OWNERNAME") or "").strip()
        if not owner:
            return

        parcel = {
            "prop_address": r.get("SITE_ADDR") or r.get("SITEADDR") or r.get("SITE_ADDRESS") or "",
            "prop_city":    r.get("SITE_CITY") or r.get("SITECITY") or "",
            "prop_state":   "TX",
            "prop_zip":     r.get("SITE_ZIP")  or r.get("SITEZIP")  or "",
            "mail_address": r.get("ADDR_1") or r.get("MAILADR1") or r.get("MAILADDR1") or "",
            "mail_city":    r.get("CITY")   or r.get("MAILCITY") or "",
            "mail_state":   r.get("STATE")  or r.get("MAILSTATE") or "TX",
            "mail_zip":     r.get("ZIP")    or r.get("MAILZIP")   or "",
        }

        for variant in self._name_variants(owner):
            self._by_owner.setdefault(variant, parcel)

    @staticmethod
    def _name_variants(name: str) -> list[str]:
        n = name.upper().strip()
        variants = {n}
        # "LAST, FIRST" → "FIRST LAST"
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
    def _get(sess, url, **kw) -> requests.Response:
        for attempt in range(RETRY_LIMIT):
            try:
                r = sess.get(url, headers={"User-Agent": "Mozilla/5.0"}, **kw)
                r.raise_for_status()
                return r
            except Exception as e:
                if attempt == RETRY_LIMIT - 1:
                    raise
                time.sleep(2 ** attempt)

    @staticmethod
    def _build_viewstate_payload(soup, event_target: str, event_arg: str) -> dict:
        payload = {
            "__EVENTTARGET":   event_target,
            "__EVENTARGUMENT": event_arg,
        }
        for field in ("__VIEWSTATE", "__VIEWSTATEGENERATOR",
                      "__EVENTVALIDATION", "__VIEWSTATEENCRYPTED"):
            inp = soup.find("input", {"name": field})
            if inp:
                payload[field] = inp.get("value", "")
        return payload

    @staticmethod
    def _looks_like_data(r: requests.Response) -> bool:
        ct = r.headers.get("content-type", "")
        return ("csv" in ct or "zip" in ct or "octet" in ct or
                "dbf" in ct or len(r.content) > 1000)


# ═══════════════════════════════════════════════════════════════════════════════
#  PART 2 — Harris County Clerk scraper (Playwright)
# ═══════════════════════════════════════════════════════════════════════════════

class ClerkScraper:
    """
    Scrapes Harris County Clerk public records portal for Fort Bend
    motivated-seller document types using Playwright (headless Chromium).
    """

    # Note: The Harris County Clerk portal at cclerk.hctx.net covers Harris County.
    # Fort Bend County has its own clerk at fortbendcountytx.gov/clerk
    # We scrape BOTH to maximise coverage for the Houston metro area.
    PORTALS = [
        {
            "name":    "Harris County Clerk",
            "url":     "https://cclerk.hctx.net/PublicRecords.aspx",
            "county":  "Harris",
        },
        {
            "name":    "Fort Bend County Clerk",
            "url":     "https://www.fortbendcountytx.gov/government/departments/county-clerk/official-public-records",
            "county":  "Fort Bend",
        },
    ]

    def __init__(self, parcel_db: ParcelDB):
        self.parcel_db = parcel_db
        self.records: list[dict] = []

    async def run(self):
        date_from = (datetime.now() - timedelta(days=LOOK_BACK_DAYS)).strftime("%m/%d/%Y")
        date_to   = datetime.now().strftime("%m/%d/%Y")

        async with async_playwright() as pw:
            browser = await pw.chromium.launch(headless=True)
            ctx     = await browser.new_context(
                user_agent="Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
                           "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
            )
            for portal in self.PORTALS:
                try:
                    await self._scrape_portal(ctx, portal, date_from, date_to)
                except Exception as e:
                    log.error("Portal %s failed: %s", portal["name"], e)
            await browser.close()

        log.info("Clerk scraper finished — %d raw records", len(self.records))

    async def _scrape_portal(self, ctx, portal: dict, date_from: str, date_to: str):
        page = await ctx.new_page()
        log.info("Opening %s", portal["url"])
        try:
            await page.goto(portal["url"], timeout=30_000, wait_until="domcontentloaded")
        except PWTimeout:
            log.warning("Timeout loading %s — skipping", portal["name"])
            return

        # For each doc type, run a search
        for code, (label, _) in DOC_TYPES.items():
            for attempt in range(RETRY_LIMIT):
                try:
                    recs = await self._search_doc_type(page, portal, code, label, date_from, date_to)
                    self.records.extend(recs)
                    log.info("  %s [%s]: %d records", portal["county"], code, len(recs))
                    break
                except PWTimeout:
                    log.warning("  Timeout on %s/%s (attempt %d)", code, portal["county"], attempt + 1)
                    await asyncio.sleep(2)
                except Exception as e:
                    log.warning("  Error on %s/%s: %s", code, portal["county"], e)
                    break
        await page.close()

    async def _search_doc_type(self, page, portal: dict, code: str, label: str,
                                date_from: str, date_to: str) -> list[dict]:
        """
        Generic search handler — tries common clerk portal patterns.
        Harris County Clerk uses a specific ASP.NET form pattern.
        """
        records = []

        # --- Harris County Clerk specific flow ---
        if "hctx.net" in portal["url"]:
            records = await self._hctx_search(page, code, label, date_from, date_to)

        # --- Fort Bend County Clerk — static/REST approach ---
        elif "fortbend" in portal["url"]:
            records = await self._fbctx_search(page, code, label, date_from, date_to, portal)

        return records

    async def _hctx_search(self, page, code: str, label: str,
                            date_from: str, date_to: str) -> list[dict]:
        """Harris County Clerk — ASP.NET post-back form search."""
        records = []
        url = CLERK_URL

        await page.goto(url, timeout=30_000, wait_until="domcontentloaded")
        await asyncio.sleep(1)

        # Try to fill search form fields
        try:
            # Instrument type / doc type selector
            sel = page.locator("select[name*='DocType'], select[id*='DocType'], "
                               "select[name*='InstrumentType'], select[id*='Type']")
            if await sel.count() > 0:
                await sel.first.select_option(label=label)
            else:
                # Try text input
                inp = page.locator("input[name*='DocType'], input[id*='InstrumentType']")
                if await inp.count() > 0:
                    await inp.first.fill(code)

            # Date range fields
            for name_frag in ["DateFrom", "StartDate", "BeginDate", "FromDate"]:
                fld = page.locator(f"input[name*='{name_frag}'], input[id*='{name_frag}']")
                if await fld.count() > 0:
                    await fld.first.fill(date_from)
                    break

            for name_frag in ["DateTo", "EndDate", "ToDate"]:
                fld = page.locator(f"input[name*='{name_frag}'], input[id*='{name_frag}']")
                if await fld.count() > 0:
                    await fld.first.fill(date_to)
                    break

            # Submit
            btn = page.locator("input[type='submit'], button[type='submit']")
            if await btn.count() > 0:
                await btn.first.click()
                await page.wait_for_load_state("domcontentloaded", timeout=20_000)
                await asyncio.sleep(1)

            records = await self._parse_results_table(page, code, label)

            # Pagination
            page_num = 2
            while True:
                next_btn = page.locator("a:has-text('Next'), a:has-text('>'), "
                                        "input[value='Next'], a[id*='next']")
                if await next_btn.count() == 0:
                    break
                await next_btn.first.click()
                await page.wait_for_load_state("domcontentloaded", timeout=20_000)
                await asyncio.sleep(0.8)
                page_recs = await self._parse_results_table(page, code, label)
                if not page_recs:
                    break
                records.extend(page_recs)
                page_num += 1
                if page_num > 20:  # safety cap
                    break

        except PWTimeout:
            raise
        except Exception as e:
            log.debug("hctx_search error for %s: %s", code, e)

        return records

    async def _fbctx_search(self, page, code: str, label: str,
                             date_from: str, date_to: str, portal: dict) -> list[dict]:
        """Fort Bend County Clerk — attempt REST / search URL patterns."""
        records = []
        # Fort Bend often uses a different search endpoint
        search_urls = [
            f"https://www.fortbendcountytx.gov/government/departments/county-clerk/"
            f"official-public-records?doc_type={code}&from={date_from}&to={date_to}",
            f"https://fbctx.county-clerk.com/search?type={code}&startdate={date_from}&enddate={date_to}",
        ]
        for surl in search_urls:
            try:
                await page.goto(surl, timeout=20_000, wait_until="domcontentloaded")
                recs = await self._parse_results_table(page, code, label)
                if recs:
                    records.extend(recs)
                    break
            except Exception:
                pass
        return records

    async def _parse_results_table(self, page, code: str, label: str) -> list[dict]:
        """Parse standard HTML results table into record dicts."""
        records = []
        html  = await page.content()
        soup  = BeautifulSoup(html, "lxml")
        today = datetime.now()

        for table in soup.find_all("table"):
            headers = [th.get_text(strip=True).lower()
                       for th in table.find_all(["th", "td"])[:20]]
            header_str = " ".join(headers)

            # Only process tables that look like record results
            if not any(kw in header_str for kw in
                       ["doc", "instrument", "grantor", "grantee", "date", "filed"]):
                continue

            # Map column indices
            col_map = {}
            for i, h in enumerate(headers):
                if "doc" in h or "instrument" in h or "number" in h:
                    col_map.setdefault("doc_num", i)
                elif "type" in h:
                    col_map.setdefault("doc_type", i)
                elif "file" in h or "record" in h or "date" in h:
                    col_map.setdefault("filed", i)
                elif "grantor" in h or "owner" in h:
                    col_map.setdefault("owner", i)
                elif "grantee" in h:
                    col_map.setdefault("grantee", i)
                elif "legal" in h or "desc" in h:
                    col_map.setdefault("legal", i)
                elif "amount" in h or "consid" in h:
                    col_map.setdefault("amount", i)

            rows = table.find_all("tr")[1:]   # skip header row
            for tr in rows:
                cells = tr.find_all(["td", "th"])
                if len(cells) < 2:
                    continue
                texts = [c.get_text(strip=True) for c in cells]

                def _get(key, default=""):
                    idx = col_map.get(key)
                    return texts[idx] if idx is not None and idx < len(texts) else default

                # Extract doc link
                link = ""
                if col_map.get("doc_num") is not None:
                    a = cells[col_map["doc_num"]].find("a")
                    if a and a.get("href"):
                        href = a["href"]
                        link = href if href.startswith("http") else f"https://cclerk.hctx.net{href}"

                # Parse filed date
                raw_date = _get("filed")
                filed_str = ""
                for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y", "%d/%m/%Y"):
                    try:
                        filed_str = datetime.strptime(raw_date, fmt).strftime("%Y-%m-%d")
                        break
                    except Exception:
                        pass

                # Skip records outside look-back window
                if filed_str:
                    try:
                        fd = datetime.strptime(filed_str, "%Y-%m-%d")
                        if (today - fd).days > LOOK_BACK_DAYS + 1:
                            continue
                    except Exception:
                        pass

                raw_owner = _get("owner") or " ".join(texts[:2])
                doc_num   = _get("doc_num") or texts[0] if texts else ""

                if not doc_num:
                    continue

                rec = {
                    "doc_num":   doc_num,
                    "doc_type":  _get("doc_type") or label,
                    "filed":     filed_str or raw_date,
                    "cat":       code,
                    "cat_label": label,
                    "owner":     raw_owner,
                    "grantee":   _get("grantee"),
                    "amount":    _get("amount"),
                    "legal":     _get("legal"),
                    "clerk_url": link,
                    # Address fields filled in by parcel lookup
                    "prop_address": "",
                    "prop_city":    "Houston",
                    "prop_state":   "TX",
                    "prop_zip":     "",
                    "mail_address": "",
                    "mail_city":    "",
                    "mail_state":   "TX",
                    "mail_zip":     "",
                }

                # Enrich with parcel data
                parcel = self.parcel_db.lookup(raw_owner)
                if parcel:
                    rec.update(parcel)

                rec["flags"], rec["score"] = score_record(rec)
                records.append(rec)

        return records


# ═══════════════════════════════════════════════════════════════════════════════
#  PART 3 — Fallback: requests + BeautifulSoup static scraper
# ═══════════════════════════════════════════════════════════════════════════════

class StaticScraper:
    """
    Supplemental scraper using requests+BS4 for any clerk endpoints
    that are accessible without JS rendering.
    """

    def __init__(self, parcel_db: ParcelDB):
        self.parcel_db = parcel_db
        self.sess = requests.Session()
        self.sess.headers["User-Agent"] = (
            "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36"
        )

    def fetch_with_retry(self, url: str, method="GET", **kw) -> Optional[requests.Response]:
        for attempt in range(RETRY_LIMIT):
            try:
                r = self.sess.request(method, url, timeout=30, **kw)
                r.raise_for_status()
                return r
            except Exception as e:
                if attempt == RETRY_LIMIT - 1:
                    log.warning("Request failed after %d attempts: %s — %s", RETRY_LIMIT, url, e)
                    return None
                time.sleep(2 ** attempt)
        return None


# ═══════════════════════════════════════════════════════════════════════════════
#  PART 4 — Output helpers
# ═══════════════════════════════════════════════════════════════════════════════

def deduplicate(records: list[dict]) -> list[dict]:
    seen = set()
    out  = []
    for r in records:
        key = (r.get("doc_num", ""), r.get("cat", ""), r.get("owner", ""))
        if key in seen:
            continue
        seen.add(key)
        out.append(r)
    return out


def build_output(records: list[dict]) -> dict:
    now = datetime.utcnow()
    return {
        "fetched_at":    now.isoformat() + "Z",
        "source":        "Harris County Clerk + Fort Bend CAD",
        "date_range":    {
            "from": (now - timedelta(days=LOOK_BACK_DAYS)).strftime("%Y-%m-%d"),
            "to":   now.strftime("%Y-%m-%d"),
        },
        "total":        len(records),
        "with_address": sum(1 for r in records if r.get("prop_address") or r.get("mail_address")),
        "records":      sorted(records, key=lambda x: x.get("score", 0), reverse=True),
    }


def save_json(data: dict):
    for path in OUTPUT_PATHS:
        path.parent.mkdir(parents=True, exist_ok=True)
        with open(path, "w") as f:
            json.dump(data, f, indent=2, default=str)
        log.info("Saved %s", path)


def save_ghl_csv(records: list[dict]):
    GHL_PATH.parent.mkdir(parents=True, exist_ok=True)
    fieldnames = [
        "First Name", "Last Name",
        "Mailing Address", "Mailing City", "Mailing State", "Mailing Zip",
        "Property Address", "Property City", "Property State", "Property Zip",
        "Lead Type", "Document Type", "Date Filed", "Document Number",
        "Amount/Debt Owed", "Seller Score", "Motivated Seller Flags",
        "Source", "Public Records URL",
    ]
    with open(GHL_PATH, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
        w.writeheader()
        for r in records:
            owner = r.get("owner", "")
            # Best-effort name split
            parts = owner.replace(",", "").split()
            first = parts[0] if parts else ""
            last  = " ".join(parts[1:]) if len(parts) > 1 else ""

            w.writerow({
                "First Name":             first,
                "Last Name":              last,
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
                "Source":                 "Harris County Clerk / Fort Bend CAD",
                "Public Records URL":     r.get("clerk_url", ""),
            })
    log.info("GHL CSV saved → %s  (%d rows)", GHL_PATH, len(records))


# ═══════════════════════════════════════════════════════════════════════════════
#  MAIN
# ═══════════════════════════════════════════════════════════════════════════════

async def main():
    log.info("═" * 60)
    log.info("Fort Bend / Harris County Motivated Seller Scraper")
    log.info("Look-back: %d days  |  Doc types: %d", LOOK_BACK_DAYS, len(DOC_TYPES))
    log.info("═" * 60)

    # 1. Load parcel data
    parcel_db = ParcelDB()
    parcel_db.load()

    # 2. Clerk scraper (Playwright)
    clerk = ClerkScraper(parcel_db)
    await clerk.run()
    records = clerk.records

    # 3. Deduplicate
    records = deduplicate(records)
    log.info("After dedup: %d records", len(records))

    # 4. Build & save output
    output = build_output(records)
    save_json(output)
    save_ghl_csv(records)

    log.info("Done.  Total=%d  WithAddress=%d  HighScore(>=70)=%d",
             output["total"],
             output["with_address"],
             sum(1 for r in records if r.get("score", 0) >= 70))


if __name__ == "__main__":
    asyncio.run(main())
