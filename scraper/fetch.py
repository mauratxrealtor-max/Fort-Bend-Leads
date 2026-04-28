"""
Fort Bend County Motivated Seller Lead Scraper
===============================================
Portal: https://ccweb.co.fort-bend.tx.us/  (Infovision iGovern system)

The portal has a two-layer gate:
  Layer 1: Browser-test / connection-throughput page — a JS-driven splash that
           has a hidden Logon button (id=LoginForm1_btnLogon). Must be submitted
           via JavaScript, not a visible click.
  Layer 2: After JS submission, session is established and real estate search
           is accessible at /RealEstate/SearchEntry.aspx

Strategy:
  1. Load home page
  2. Execute JS to submit the hidden logon form directly
  3. Navigate to SearchEntry.aspx
  4. Fill date range + doc type, submit, parse results table
  5. Paginate
  6. Fallback: broad date-only search if per-type yields nothing
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
BASE_URL   = "https://ccweb.co.fort-bend.tx.us"
HOME_URL   = "https://ccweb.co.fort-bend.tx.us/"
SEARCH_URL = "https://ccweb.co.fort-bend.tx.us/RealEstate/SearchEntry.aspx"
FBCAD_BASE = "https://www.fbcad.org"

OUTPUT_PATHS = [
    Path(__file__).parent.parent / "dashboard" / "records.json",
    Path(__file__).parent.parent / "data"      / "records.json",
]
GHL_PATH       = Path(__file__).parent.parent / "data" / "ghl_export.csv"
LOOK_BACK_DAYS = 90
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
    "LNHOA":    ("HOA Lien",                "HOA Lien"),
    "MEDLN":    ("Medicaid Lien",           "Medicaid Lien"),
    "PRO":      ("Probate",                 "Probate"),
    "NOC":      ("Notice of Commencement",  "NOC"),
    "RELLP":    ("Release Lis Pendens",     "Release LP"),
}

# Keywords for classifying raw doc-type strings from portal
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
    "PRO":      ["PROBATE", "LETTERS TEST", "LETTERS ADMIN"],
    "NOC":      ["NOTICE OF COMMENCEMENT"],
    "LN":       ["LIEN"],  # broad — checked last
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

    if cat in ("LP", "RELLP"):          flags.append("Lis pendens")
    if cat in ("LP", "NOFC"):           flags.append("Pre-foreclosure")
    if cat in ("JUD", "CCJ", "DRJUD"):  flags.append("Judgment lien")
    if cat in ("LNCORPTX", "LNIRS", "LNFED", "TAXDEED"): flags.append("Tax lien")
    if cat == "LNMECH":  flags.append("Mechanic lien")
    if cat == "PRO":     flags.append("Probate / estate")
    if re.search(r"\b(LLC|INC|CORP|LTD|LP|TRUST)\b", rec.get("owner", ""), re.I):
        flags.append("LLC / corp owner")
    try:
        if datetime.strptime(rec.get("filed", ""), "%Y-%m-%d") >= \
                datetime.now() - timedelta(days=7):
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
#  PARCEL DB
# ═══════════════════════════════════════════════════════════════════════════════
class ParcelDB:
    """
    Fort Bend CAD bulk property data.
    Builds two lookup tables:
      1. by_instrument: InstrumentNumber -> {prop_address, mail_address, ...}
      2. by_owner:      OwnerName variants -> {prop_address, mail_address, ...}

    Data files (uploaded by user):
      PropertyDataExport4558080 = Property records (site address)
      PropertyDataExport4558081 = Owner records (mailing address)
      PropertyDataExport4558085 = Sales/deed records (InstrumentNumber)
    """

    # Paths to FBCAD data files — check multiple locations
    FILE_PROPERTY = "PropertyDataExport4558080_1_.txt"  # Situs address
    FILE_OWNER    = "PropertyDataExport4558081_1_.txt"  # Owner + mailing addr
    FILE_SALES    = "PropertyDataExport4558085_1_.txt"  # InstrumentNumber -> PropertyID

    @classmethod
    def _find_data_dir(cls) -> Optional[Path]:
        """Find the directory containing the FBCAD data files."""
        candidates = [
            Path("/mnt/user-data/uploads"),
            Path(__file__).parent.parent / "data" / "fbcad",
            Path(__file__).parent.parent / "data",
        ]
        for d in candidates:
            if (d / cls.FILE_SALES).exists():
                return d
        return None

    def __init__(self):
        self._by_instrument: dict[str, dict] = {}  # doc_num -> parcel
        self._by_owner: dict[str, dict] = {}        # owner name -> parcel
        self._loaded = False

    def load(self):
        """Load parcel lookup from compact CSV (gzipped or plain)."""
        base = Path(__file__).parent.parent / "data"
        # Check for compact CSV (preferred — small enough to commit to git)
        for fname in ["parcel_compact.csv.gz", "parcel_compact.csv"]:
            fpath = base / fname
            if fpath.exists():
                try:
                    self._load_compact_csv(fpath)
                    if self._by_owner or self._by_instrument:
                        log.info("Parcel DB loaded from %s — %d owner / %d instrument entries",
                                 fname, len(self._by_owner), len(self._by_instrument))
                        self._loaded = True
                        return
                except Exception as e:
                    log.warning("Compact CSV load failed: %s", e)

        # Fallback: raw FBCAD TXT files
        data_dir = self._find_data_dir()
        if not data_dir:
            log.warning("FBCAD data files not found — address enrichment skipped")
            return
        prop_path  = data_dir / self.FILE_PROPERTY
        owner_path = data_dir / self.FILE_OWNER
        sales_path = data_dir / self.FILE_SALES
        log.info("Using FBCAD raw TXT files from: %s", data_dir)
        available = [p for p in [prop_path, owner_path, sales_path] if p.exists()]
        if available:
            self._load_from_files(prop_path, owner_path, sales_path)
            if self._by_owner or self._by_instrument:
                log.info("Parcel DB loaded — %d owner / %d instrument entries",
                         len(self._by_owner), len(self._by_instrument))
                self._loaded = True
                return
        log.warning("Parcel DB unavailable — address enrichment skipped")

    def _load_compact_csv(self, path: Path):
        """Load the compact parcel CSV (plain or gzipped)."""
        import gzip as _gzip
        open_fn = _gzip.open if str(path).endswith('.gz') else open
        with open_fn(path, 'rt', encoding='utf-8') as f:
            reader = csv.DictReader(f)
            for row in reader:
                owner = row.get('owner','').strip()
                instr = row.get('instr','').strip()
                parcel = {
                    'mail_address': row.get('mail_addr','').strip(),
                    'mail_city':    row.get('mail_city','').strip(),
                    'mail_state':   row.get('mail_state','TX').strip() or 'TX',
                    'mail_zip':     row.get('mail_zip','').strip()[:5],
                    'prop_address': row.get('prop_addr','').strip(),
                    'prop_city':    row.get('prop_city','').strip(),
                    'prop_state':   row.get('prop_state','TX').strip() or 'TX',
                    'prop_zip':     row.get('prop_zip','').strip()[:5],
                }
                if owner:
                    for v in self._name_variants(owner):
                        self._by_owner.setdefault(v, parcel)
                if instr:
                    self._by_instrument[instr.upper()] = parcel
                    self._by_instrument[instr.upper().lstrip('0')] = parcel

    def lookup_instrument(self, doc_num: str) -> Optional[dict]:
        """Look up parcel data by instrument/document number."""
        return self._by_instrument.get(str(doc_num).strip())

    def lookup(self, owner: str) -> Optional[dict]:
        """Look up parcel data by owner name with fuzzy fallback."""
        if not self._loaded or not owner:
            return None
        # Try all name variants first (exact)
        for v in self._name_variants(owner):
            hit = self._by_owner.get(v)
            if hit:
                return hit
        # Clean noise words and retry
        clean = re.sub(
            r"\s*(\(\+\)|ET\s+AL|ET\s+UX|TRUSTEE|TRUST|LLC|INC|CORP|JR\.?|SR\.?|II|III)\s*",
            " ", owner.upper()
        ).strip()
        if clean != owner.upper().strip():
            for v in self._name_variants(clean):
                hit = self._by_owner.get(v)
                if hit:
                    return hit
        return None


    @staticmethod
    def _name_variants(name: str) -> list[str]:
        n = name.upper().strip()
        variants = {n}
        # Remove quotes
        n_clean = n.replace('"', '').replace("'", "")
        variants.add(n_clean)
        if "," in n_clean:
            parts = [p.strip() for p in n_clean.split(",", 1)]
            variants.add(f"{parts[1]} {parts[0]}")
            variants.add(f"{parts[0]} {parts[1]}")
        else:
            words = n_clean.split()
            if len(words) >= 2:
                variants.add(f"{words[-1]}, {' '.join(words[:-1])}")
                variants.add(f"{words[-1]} {' '.join(words[:-1])}")
        return variants


# ═══════════════════════════════════════════════════════════════════════════════
#  CLERK SCRAPER
# ═══════════════════════════════════════════════════════════════════════════════
class ClerkScraper:
    """
    Handles the Infovision iGovern session gate at ccweb.co.fort-bend.tx.us.

    Key insight from the error log:
      - The page has a hidden <input id="LoginForm1_btnLogon"> that cannot be
        clicked normally (element is not visible).
      - The fix: use page.evaluate() to call .click() directly on the DOM element,
        bypassing Playwright's visibility check. This submits the session form
        and establishes a valid server-side session cookie.
    """

    def __init__(self, parcel_db: ParcelDB):
        self.parcel_db = parcel_db
        self.records: list[dict] = []

    async def run(self):
        date_from = (datetime.now() - timedelta(days=LOOK_BACK_DAYS)).strftime("%m/%d/%Y")
        date_to   = datetime.now().strftime("%m/%d/%Y")
        log.info("Search window: %s -> %s", date_from, date_to)

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
            )
            page = await ctx.new_page()

            # Establish session
            ok = await self._establish_session(page)
            if not ok:
                log.error("Could not establish session")
                await browser.close()
                return

            # Run targeted searches for each motivated-seller type FIRST
            # Each gets up to 20 records for that type over 90 days.
            # Then broad search as fallback to catch anything missed.
            TARGETED = [
                ("LP",       "LIS PENDENS"),
                ("NOFC",     "FORECLOSURE"),
                ("JUD",      "JUDGMENT"),
                ("LNIRS",    "IRS"),
                ("LNCORPTX", "STATE TAX"),
                ("LNMECH",   "MECHANIC"),
                ("LNHOA",    "HOA"),
                ("PRO",      "PROBATE"),
                ("TAXDEED",  "TAX DEED"),
                ("LNFED",    "FEDERAL"),
                ("LN",       "LIEN"),
            ]
            existing = set()
            total_found = 0

            for code, term in TARGETED:
                try:
                    label = DOC_TYPES.get(code, (term, ""))[0]
                    recs = await self._targeted_search(
                        page, code, label, term, date_from, date_to
                    )
                    new_recs = [r for r in recs if r["doc_num"] not in existing]
                    if new_recs:
                        self.records.extend(new_recs)
                        existing.update(r["doc_num"] for r in new_recs)
                        total_found += len(new_recs)
                        log.info("  [%s] %s: +%d (total=%d)", code, term, len(new_recs), total_found)
                    else:
                        log.info("  [%s] %s: 0 new", code, term)
                except Exception as e:
                    log.warning("  Targeted [%s] error: %s", code, e)

            # Broad fallback — catches any doc types not in targeted list
            log.info("Running broad fallback search...")
            try:
                recs = await self._playwright_search(page, None, None, date_from, date_to)
                new_recs = [r for r in recs if r["doc_num"] not in existing]
                if new_recs:
                    self.records.extend(new_recs)
                    existing.update(r["doc_num"] for r in new_recs)
                    total_found += len(new_recs)
                log.info("Broad fallback: +%d new (grand total=%d)", len(new_recs), total_found)
            except Exception as e:
                log.warning("  Broad fallback error: %s", e)


            await browser.close()
        log.info("Scraper done — %d total raw records", len(self.records))

    async def _targeted_search(self, page, code, label, search_term,
                               date_from, date_to) -> list[dict]:
        """
        Search by doc type keyword using the DataTextEdit1 field.
        Unlike broad search, this sets the search term so the portal
        returns only matching doc types — but still navigates to SearchResults.
        """
        await page.goto(SEARCH_URL, timeout=20_000, wait_until="domcontentloaded")
        await asyncio.sleep(0.5)

        # Check session still valid
        html = await page.content()
        if "session" in html.lower() and "expired" in html.lower():
            await self._establish_session(page)
            await page.goto(SEARCH_URL, timeout=20_000, wait_until="domcontentloaded")
            await asyncio.sleep(0.5)

        # Fill dates
        date_filled = await page.evaluate(f"""() => {{
            const fromDate = new Date('{date_from.split('/')[2]}',
                                      {int(date_from.split('/')[0])-1},
                                      '{date_from.split('/')[1]}');
            const toDate   = new Date('{date_to.split('/')[2]}',
                                      {int(date_to.split('/')[0])-1},
                                      '{date_to.split('/')[1]}');
            const fromIds = ['cphNoMargin_f_ddcDateFiledFrom'];
            const toIds   = ['cphNoMargin_f_ddcDateFiledTo'];
            let ok = 0;
            for (const id of fromIds) {{
                try {{ const c = $find(id); if (c) {{ c.set_value(fromDate); ok++; break; }} }} catch(e) {{}}
            }}
            for (const id of toIds) {{
                try {{ const c = $find(id); if (c) {{ c.set_value(toDate); ok++; break; }} }} catch(e) {{}}
            }}
            return ok;
        }}""")

        # Fill doc type search field
        await page.evaluate(f"""() => {{
            const el = document.getElementById('cphNoMargin_f_DataTextEdit1') ||
                       document.querySelector('[name="cphNoMargin_f_DataTextEdit1"]');
            if (el) {{
                el.value = '{search_term}';
                el.dispatchEvent(new Event('change', {{bubbles:true}}));
            }}
            const sel = document.querySelector('[id*="ddlSearchType"],[name*="ddlSearchType"]');
            if (sel) sel.value = 'CONTAINS';
        }}""")

        # Submit
        await page.evaluate("""() => {
            document.getElementById('__EVENTTARGET').value =
                'ctl00$cphNoMargin$SearchButtons1$btnSearch';
            document.getElementById('__EVENTARGUMENT').value = '0';
            if (typeof WebForm_OnSubmit === 'function') WebForm_OnSubmit();
            document.forms[0].submit();
        }""")

        try:
            await page.wait_for_load_state("domcontentloaded", timeout=20_000)
        except PWTimeout:
            pass
        await asyncio.sleep(2)

        # Only process if we got SearchResults
        if "SearchResults" not in page.url:
            log.debug("  [%s] stayed on SearchEntry — no results", code)
            return []

        try:
            pg_content = await page.content()
        except Exception:
            await asyncio.sleep(2)
            pg_content = await page.content()

        # Click "get full count" to load all records for this type
        full_count = await page.evaluate("""() => {
            const fc = Array.from(document.querySelectorAll('a')).find(a =>
                a.textContent.trim().toLowerCase().includes('get full count'));
            if (fc) { fc.click(); return true; }
            return false;
        }""")
        if full_count:
            await asyncio.sleep(3)
            try:
                await page.wait_for_load_state("domcontentloaded", timeout=10_000)
            except Exception:
                pass
            await asyncio.sleep(1)
            try:
                pg_content = await page.content()
            except Exception:
                await asyncio.sleep(2)
                pg_content = await page.content()

        # Try full-count text parser first (handles concatenated cell format)
        if len(pg_content) > 400_000:
            from bs4 import BeautifulSoup as _BS
            import re as _re
            _soup = _BS(pg_content, "lxml")
            for _td in _soup.find_all(["td", "th"]):
                _txt = _td.get_text(" ")
                if len(_re.findall(r'View\s+20\d{8}', _txt)) >= 3:
                    recs = self._parse_full_count_text(_txt, code, label)
                    if recs:
                        log.info("  [%s] full-count parser: %d records", code, len(recs))
                        return recs
                    break

        # Fall back to standard table parser
        recs = self._parse_table(pg_content, code, label, True)
        return recs

    async def _playwright_search(self, page, code, label, date_from, date_to):
        """
        Fully Playwright-native search. Lets the Infragistics JS handle
        date serialization natively by typing into the date inputs directly.
        Uses __doPostBack to submit, then reads results from the same page.
        """
        await page.goto(SEARCH_URL, timeout=20_000, wait_until="domcontentloaded")
        await asyncio.sleep(0.8)

        # Check session still valid
        html = await page.content()
        if "session" in html.lower() and "expired" in html.lower():
            await self._establish_session(page)
            await page.goto(SEARCH_URL, timeout=20_000, wait_until="domcontentloaded")
            await asyncio.sleep(0.8)

        # ── Fill date fields via Infragistics API ────────────────────────────
        # The date pickers are Infragistics WebDatePicker controls.
        # clientState names: cphNoMargin_f_ddcDateFiledFrom / ddcDateFiledTo
        # We use $find() — Infragistics' own JS lookup — to get the control
        # and call set_value() with a JS Date object. This is exactly what
        # a real user's browser does, so the clientState serializes correctly.
        date_filled = await page.evaluate(f"""() => {{
            const fromDate = new Date('{date_from.split('/')[2]}',
                                      {int(date_from.split('/')[0])-1},
                                      '{date_from.split('/')[1]}');
            const toDate   = new Date('{date_to.split('/')[2]}',
                                      {int(date_to.split('/')[0])-1},
                                      '{date_to.split('/')[1]}');

            // Try Infragistics $find() with known control IDs
            const fromIds = [
                'cphNoMargin_f_ddcDateFiledFrom',
                'cphNoMargin_f_dcDateFiled_DateTextBox1',
                'cphNoMargin_f_ddcDateFiled_DateTextBox1',
            ];
            const toIds = [
                'cphNoMargin_f_ddcDateFiledTo',
                'cphNoMargin_f_dcDateFiled_DateTextBox2',
                'cphNoMargin_f_ddcDateFiled_DateTextBox2',
            ];

            let fromCtrl = null, toCtrl = null;
            for (const id of fromIds) {{
                try {{ fromCtrl = $find(id); if (fromCtrl) break; }} catch(e) {{}}
                // Also try as plain input
                const el = document.getElementById(id);
                if (el) {{ fromCtrl = {{_el: el, set_value: function(d) {{
                    el.value = (d.getMonth()+1).toString().padStart(2,'0') + '/' +
                               d.getDate().toString().padStart(2,'0') + '/' +
                               d.getFullYear();
                    ['change','blur'].forEach(ev => el.dispatchEvent(new Event(ev,{{bubbles:true}})));
                }}}}; break; }}
            }}
            for (const id of toIds) {{
                try {{ toCtrl = $find(id); if (toCtrl) break; }} catch(e) {{}}
                const el = document.getElementById(id);
                if (el) {{ toCtrl = {{_el: el, set_value: function(d) {{
                    el.value = (d.getMonth()+1).toString().padStart(2,'0') + '/' +
                               d.getDate().toString().padStart(2,'0') + '/' +
                               d.getFullYear();
                    ['change','blur'].forEach(ev => el.dispatchEvent(new Event(ev,{{bubbles:true}})));
                }}}}; break; }}
            }}

            if (fromCtrl && toCtrl) {{
                try {{ fromCtrl.set_value(fromDate); }} catch(e) {{}}
                try {{ toCtrl.set_value(toDate);   }} catch(e) {{}}
                return 'ig_set_value OK';
            }}

            // Last resort: find ALL inputs with mm/dd/yyyy value (no visibility filter)
            const allInputs = Array.from(document.querySelectorAll('input'));
            const dateInputs = allInputs.filter(i => i.value === 'mm/dd/yyyy');
            if (dateInputs.length >= 2) {{
                function fmt(d) {{
                    return (d.getMonth()+1).toString().padStart(2,'0') + '/' +
                           d.getDate().toString().padStart(2,'0') + '/' +
                           d.getFullYear();
                }}
                dateInputs[0].value = fmt(fromDate);
                ['change','blur'].forEach(ev =>
                    dateInputs[0].dispatchEvent(new Event(ev,{{bubbles:true}})));
                dateInputs[1].value = fmt(toDate);
                ['change','blur'].forEach(ev =>
                    dateInputs[1].dispatchEvent(new Event(ev,{{bubbles:true}})));
                return 'set by value filter: ' + dateInputs[0].id + ' / ' + dateInputs[1].id;
            }}
            return 'FAILED: inputs=' + allInputs.length + ' date_inputs=' + dateInputs.length;
        }}""")
        log.info("  Date fill: %s", date_filled)

        # ── Fill doc type ─────────────────────────────────────────────────────
        if code:
            search_term = DOC_TYPE_KEYWORDS.get(code, [label])[0] if label else ""
            await page.evaluate(f"""() => {{
                const el = document.getElementById('cphNoMargin_f_DataTextEdit1') ||
                           document.querySelector('[name="cphNoMargin_f_DataTextEdit1"]');
                if (el) {{
                    el.value = '{search_term}';
                    el.dispatchEvent(new Event('change', {{bubbles:true}}));
                }}
                const sel = document.querySelector('[id*="ddlSearchType"],[name*="ddlSearchType"]');
                if (sel) sel.value = 'CONTAINS';
            }}""")

        # ── Submit via __doPostBack ────────────────────────────────────────────
        await page.evaluate("""() => {
            document.getElementById('__EVENTTARGET').value =
                'ctl00$cphNoMargin$SearchButtons1$btnSearch';
            document.getElementById('__EVENTARGUMENT').value = '0';
            if (typeof WebForm_OnSubmit === 'function') WebForm_OnSubmit();
            document.forms[0].submit();
        }""")

        try:
            await page.wait_for_load_state("domcontentloaded", timeout=20_000)
        except PWTimeout:
            pass
        await asyncio.sleep(2)  # extra wait for Infragistics grid to render

        try:
            pg_content = await page.content()
        except Exception:
            await asyncio.sleep(2)
            pg_content = await page.content()

        log.info("  After submit URL: %s  len=%d", page.url, len(pg_content))

        # ── Step 1: Click "get full count" to load ALL results ──────────────
        full_count_result = await page.evaluate("""() => {
            const links = Array.from(document.querySelectorAll('a'));
            const fc = links.find(a =>
                a.textContent.trim().toLowerCase().includes('get full count') ||
                a.textContent.trim().toLowerCase().includes('full count')
            );
            if (fc) { fc.click(); return 'clicked: ' + fc.textContent.trim(); }
            return null;
        }""")
        if full_count_result:
            log.info("  %s", full_count_result)
            # Wait for navigation to fully settle after "get full count" click
            await asyncio.sleep(3)
            try:
                await page.wait_for_load_state("domcontentloaded", timeout=15_000)
            except Exception:
                pass
            await asyncio.sleep(2)
            try:
                pg_content = await page.content()
                log.info("  After full count: len=%d", len(pg_content))
            except Exception as e:
                log.warning("  Could not read after full count (%s) — using original page", e)
                # Re-navigate to results to get a stable page
                try:
                    await page.wait_for_load_state("domcontentloaded", timeout=10_000)
                    await asyncio.sleep(2)
                    pg_content = await page.content()
                    log.info("  Re-read after wait: len=%d", len(pg_content))
                except Exception:
                    pass

        # ── Step 2: Collect all global_id detail URLs from results page ───────
        detail_urls = await page.evaluate(f"""() => {{
            const base = '{BASE_URL}/RealEstate/';
            return Array.from(document.querySelectorAll('a[href*="global_id"]'))
                .map(a => {{
                    const href = a.getAttribute('href');
                    return href.startsWith('http') ? href : base + href.replace('./', '');
                }})
                .filter((v, i, arr) => arr.indexOf(v) === i);  // dedupe
        }}""")
        log.info("  Found %d document detail URLs", len(detail_urls))

        # ── Step 3: Parse ALL pages from the full-count results ─────────────
        all_recs = []
        page_num = 1
        MAX_PAGES = 200  # cap at 200 pages = 4000 records max per run

        while page_num <= MAX_PAGES:
            cur_html = pg_content

            # Try full-count text cell parser (faster, handles the big concatenated cell)
            if len(cur_html) > 400_000:
                from bs4 import BeautifulSoup as _BS
                _soup = _BS(cur_html, "lxml")
                page_recs = []
                for _td in _soup.find_all(["td", "th"]):
                    _txt = _td.get_text(" ")
                    if len(re.findall(r'View\s+20\d{8}', _txt)) >= 5:
                        log.info("  Page %d: parsing full-count cell (%d chars, ~%d records)",
                                 page_num, len(_txt),
                                 len(re.findall(r'View\s+20\d{8}', _txt)))
                        page_recs = self._parse_full_count_text(
                            _txt, code or "OTHER", label or "All")
                        break
                if not page_recs:
                    page_recs = self._parse_table(
                        cur_html, code or "OTHER", label or "All", bool(code))
            else:
                page_recs = self._parse_table(
                    cur_html, code or "OTHER", label or "All", bool(code))

            if not page_recs:
                log.info("  Page %d: no records — stopping pagination", page_num)
                break

            all_recs.extend(page_recs)
            log.info("  Page %d: +%d records (total so far: %d)",
                     page_num, len(page_recs), len(all_recs))

            if page_num >= MAX_PAGES:
                log.warning("  Hit %d-page cap", MAX_PAGES)
                break

            # Navigate to next page via __doPostBack
            next_page_num = page_num + 1
            clicked = await page.evaluate(f"""() => {{
                // Find "Page N" link where N = {next_page_num}
                const allLinks = Array.from(document.querySelectorAll('a'));
                for (const a of allLinks) {{
                    const txt = a.textContent.trim();
                    if (txt === 'Page {next_page_num}') {{
                        const href = a.getAttribute('href') || '';
                        if (href.includes('__doPostBack')) {{
                            const m = href.match(/__doPostBack\\('([^']+)','([^']*)'/);
                            if (m) {{ __doPostBack(m[1], m[2]); return 'postback'; }}
                        }}
                        a.click();
                        return 'click';
                    }}
                }}
                // Also check onclick attributes
                for (const el of document.querySelectorAll('[onclick]')) {{
                    const oc = el.getAttribute('onclick') || '';
                    if (oc.includes('Page {next_page_num}') ||
                        (el.textContent.trim() === 'Page {next_page_num}')) {{
                        el.click();
                        return 'onclick';
                    }}
                }}
                return null;
            }}""")

            if not clicked:
                log.info("  No 'Page %d' link found — done", next_page_num)
                break

            log.info("  Navigating to page %d (%s)...", next_page_num, clicked)
            try:
                await page.wait_for_load_state("domcontentloaded", timeout=20_000)
            except Exception:
                pass
            await asyncio.sleep(2)
            try:
                pg_content = await page.content()
            except Exception:
                await asyncio.sleep(2)
                pg_content = await page.content()
            page_num += 1

        if False:  # dummy block to maintain indentation for old fallback
            page_num = 1
            while True:
                html = pg_content  # updated after each page navigation
                recs = self._parse_table(html, code or "OTHER", label or "All", bool(code))
                all_recs.extend(recs)
                if not recs and page_num > 1:
                    break

                # Fort Bend Infragistics grid pager — find page number links/inputs
                next_result = await page.evaluate(f"""() => {{
                const nextPageNum = {page_num + 1};

                // Strategy 1: find page number link (e.g. "2", "3"...)
                const pageLinks = Array.from(document.querySelectorAll('a, span'))
                    .filter(el => el.textContent.trim() === String(nextPageNum));
                for (const el of pageLinks) {{
                    if (el.tagName === 'A') {{
                        const href = el.getAttribute('href') || '';
                        if (href.includes('__doPostBack')) {{
                            const m = href.match(/__doPostBack\\('([^']+)','([^']*)'/);
                            if (m) {{ __doPostBack(m[1], m[2]); return 'postback_page'; }}
                        }}
                        el.click();
                        return 'clicked_page_' + nextPageNum;
                    }}
                }}

                // Strategy 2: find any pager-style "next" control
                // Infragistics grid pager spans: look for spans with page numbers
                const allSpans = Array.from(document.querySelectorAll('span,td'))
                    .filter(el => {{
                        const cls = el.className || '';
                        return cls.includes('pager') || cls.includes('Pager') ||
                               cls.includes('page') || cls.includes('Page');
                    }});
                for (const span of allSpans) {{
                    const links = span.querySelectorAll('a');
                    for (const a of links) {{
                        if (a.textContent.trim() === '>' || a.textContent.trim() === '...') {{
                            a.click(); return 'pager_next';
                        }}
                    }}
                }}

                // Strategy 3: look at ALL anchors for numeric page > current
                const numLinks = Array.from(document.querySelectorAll('a'))
                    .filter(a => {{
                        const t = a.textContent.trim();
                        const n = parseInt(t);
                        return !isNaN(n) && n === nextPageNum && a.offsetParent !== null;
                    }});
                if (numLinks.length > 0) {{
                    numLinks[0].click();
                    return 'num_link_' + nextPageNum;
                }}

                return null;
            }}""")

                if not next_result:
                    log.info("  No next page found after page %d — done", page_num)
                    break

                log.info("  Paginating to page %d (%s)…", page_num + 1, next_result)
                try:
                    await page.wait_for_load_state("domcontentloaded", timeout=20_000)
                except Exception:
                    pass
                await asyncio.sleep(1.5)
                pg_content = await page.content()
                page_num += 1
                if page_num > 500:
                    log.warning("  Hit 500-page cap, stopping")
                    break

        # Detail page enrichment disabled — parcel DB provides better addresses
        # and detail page parsing was overwriting correct addresses with junk HTML
        log.info("  Skipping detail page enrichment (parcel DB addresses used)")

        return all_recs

    @staticmethod
    def _extract_viewstate(html: str) -> dict:
        """Extract ASP.NET hidden fields from page HTML."""
        soup = BeautifulSoup(html, "lxml")
        fields = {}
        for name in ["__VIEWSTATE", "__VIEWSTATEGENERATOR", "__EVENTVALIDATION",
                     "__VIEWSTATEENCRYPTED"]:
            inp = soup.find("input", {"name": name})
            if inp:
                fields[name] = inp.get("value", "")
        return fields

    def _http_search(self, sess: requests.Session, vs: dict,
                     code: Optional[str], label: Optional[str],
                     date_from: str, date_to: str) -> list[dict]:
        """
        POST directly to Fort Bend Clerk search using requests.
        The ASP.NET date-range fields are named via hidden inputs we extract
        from the page source. The doc-type field is cphNoMargin_f_DataTextEdit1.
        """
        search_term = ""
        if code:
            candidates = DOC_TYPE_KEYWORDS.get(code, [])
            search_term = candidates[0] if candidates else (label or "")

        # Build the POST payload using EXACT field names from intercepted POST
        # Date clientState format: "|0|01||[[[[]],[],[]],[{},[]],"MM/DD/YYYY"]"
        def date_client_state(date_str: str) -> str:
            return f'|0|01||[[[[]],[],[]],[{{}},[]],"1,{date_str}"]'

        # Doc type checkboxes: dclDocType$0 through $85
        # We need to find which checkbox index corresponds to our doc type.
        # The form has checkboxes for all available doc types.
        # For broad search we leave all unchecked; for per-type we check matching ones.
        doc_type_checkboxes = {}
        if code:
            # We'll set all doc type checkboxes — the server filters by date+type combo
            # The checkbox values come from the __EVENTVALIDATION which lists them
            # For now: use DataTextEdit1 text field (confirmed field name from POST)
            pass

        payload = {
            "__EVENTTARGET":  "ctl00$cphNoMargin$SearchButtons1$btnSearch",
            "__EVENTARGUMENT": "0",
            "__VIEWSTATE":     vs.get("__VIEWSTATE", ""),
            "__VIEWSTATEGENERATOR": vs.get("__VIEWSTATEGENERATOR", ""),
            "__EVENTVALIDATION": vs.get("__EVENTVALIDATION", ""),
            # Infragistics clientState blobs (from intercepted POST)
            "Header1_WebHDS_clientState":       "",
            "Header1_WebDataMenu1_clientState": "[[null,[[[null,[],null],[{},[]],null]],null],[{},[{},{}]],null]",
            # Name search mode
            "ctl00$cphNoMargin$f$NameSearchMode": "rdoCombine",
            "cphNoMargin_f_txtParty_clientState": '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtParty":             "",
            # Search type (CONTAINS)
            "ctl00$cphNoMargin$f$ddlSearchType":  "CONTAINS",
            "ctl00$cphNoMargin$f$drbPartyType":   "",
            "cphNoMargin_f_txtGrantor_clientState": '|0|00||[[[[]],[],[]],[{},[]],"00"]',
            "cphNoMargin_f_txtGrantee_clientState": '|0|00||[[[[]],[],[]],[{},[]],"00"]',
            # DATE FIELDS — Infragistics date picker clientState with actual date values
            "cphNoMargin_f_ddcDateFiledFrom_clientState": date_client_state(date_from),
            "cphNoMargin_f_ddcDateFiledTo_clientState":   date_client_state(date_to),
            # Instrument number fields
            "cphNoMargin_f_txtInstrumentNoFrom_clientState": '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtInstrumentNoFrom": "",
            "cphNoMargin_f_txtInstrumentNoTo_clientState":  '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtInstrumentNoTo":   "",
            "cphNoMargin_f_txtBook_clientState":  '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtBook":  "",
            "cphNoMargin_f_txtPage_clientState":  '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtPage":  "",
            # Doc type text search field
            "cphNoMargin_f_DataTextEdit1_clientState": '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_DataTextEdit1": search_term,
            # Legal description fields
            "cphNoMargin_f_txtLDLot_clientState":           '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtLDLot": "",
            "cphNoMargin_f_txtLDBook_clientState":          '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtLDBook": "",
            "cphNoMargin_f_txtLDSection_clientState":       '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtLDSection": "",
            "cphNoMargin_f_txtLDStreetAddress_clientState": '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtLDStreetAddress": "",
            "ctl00$cphNoMargin$f$ddlTown": "",
            "cphNoMargin_f_txtLDFreeForm_clientState":      '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtLDFreeForm": "",
            "cphNoMargin_f_txtLDVolume_clientState":        '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtLDVolume": "",
            "cphNoMargin_f_txtLDPage_clientState":          '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtLDPage": "",
            "cphNoMargin_f_txtLDMapcase_clientState":       '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtLDMapcase": "",
            "cphNoMargin_f_txtLDSlide_clientState":         '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "cphNoMargin_f_txtLDSlide": "",
            # Dialog/popup states
            "cphNoMargin_dlgPopup_clientState":  "[[[[null,3,null,null,null,null,1,1,0,0,null,0]],[[[[[null,\"Document Type List\",null]],[[[[[]],[],null],[null,null],[null]],[[[[]],[],null],[null,null],[null]],[[[[]],[],null],[null,null],[null]]],[]],[{},[]],null],[[[[null,null,null,null]],[],[]],[{},[]],null]],[]],[{},[]],\"3,0,,,,,0\"]",
            "dlgOptionWindow_clientState":       "[[[[null,3,null,null,\"700px\",\"550px\",1,1,0,0,null,0]],[[[[[null,\"Copy Options\",null]],[[[[[]],[],null],[null,null],[null]],[[[[]],[],null],[null,null],[null]],[[[[]],[],null],[null,null],[null]]],[]],[{},[]],null],[[[[null,null,null,null]],[],[]],[{},[]],null]],[]],[{},[]],\"3,0,,,700px,550px,0\"]",
            "RangeContextMenu_clientState":      "[[[[null,null,null,null,1]],[[[[[null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null,null]],[],[]],[{},[]],null]],null],[{},[{},{}]],null]",
            # Login form
            "LoginForm1_txtLogonName_clientState": '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "LoginForm1_txtLogonName": "",
            "LoginForm1_txtPassword_clientState":  '|0|01||[[[[]],[],[]],[{},[]],"01"]',
            "LoginForm1_txtPassword":  "",
            "ctl00$LoginForm1$logonType": "rdoPubCpu",
            # Calendar state — month/year of search window
            "_ig_def_dp_cal_clientState": f"[[null,[],null],[{{}},[]],'01,{date_to.split('/')[2]},{date_to.split('/')[0]}']",
            "ctl00$_IG_CSS_LINKS_": "~/Style/style.css|~/Style/styleforsearch.css|~/favicon.ico|~/localization/styleFromCounty.css",
        }
        all_records = []
        page_num = 1

        while True:
            try:
                r = sess.post(SEARCH_URL, data=payload,
                              timeout=30, verify=False)
                r.raise_for_status()
            except Exception as e:
                log.warning("  HTTP POST error: %s", e)
                break

            log.info("  POST -> %s  status=%d  len=%d",
                     r.url, r.status_code, len(r.text))

            # On first LP search, dump the full response to a file for inspection
            if code == "LP" and page_num == 1:
                dump_path = Path(__file__).parent.parent / "data" / "response_dump.html"
                dump_path.parent.mkdir(parents=True, exist_ok=True)
                dump_path.write_text(r.text, encoding="utf-8")
                log.info("  Response dumped to data/response_dump.html")
                # Also log key sections
                soup_d = BeautifulSoup(r.text, "lxml")
                # Find all form inputs to see what the server sent back
                all_inputs = soup_d.find_all("input", {"type": ["submit","button","image"]})
                log.info("  Submit buttons in response: %s",
                         [(i.get("name",""), i.get("value",""), i.get("id",""))
                          for i in all_inputs])
                # Find error/validation messages
                for cls in ["error", "validator", "validation", "message", "alert"]:
                    errs = soup_d.find_all(class_=lambda c: c and cls in c.lower())
                    if errs:
                        log.info("  [%s] elements: %s",
                                 cls, [e.get_text(strip=True)[:100] for e in errs[:3]])
                # Check if results table exists
                tbls = soup_d.find_all("table")
                log.info("  Tables in response: %d", len(tbls))
                for t in tbls[:5]:
                    log.info("    Table id=%s class=%s rows=%d",
                             t.get("id",""), t.get("class",""), len(t.find_all("tr")))

            recs = self._parse_table(r.text, code or "OTHER",
                                     label or "All Types", bool(code))
            if not recs:
                break

            all_records.extend(recs)
            log.info("  Page %d: %d rows", page_num, len(recs))

            # Check for next page link
            soup = BeautifulSoup(r.text, "lxml")
            next_link = soup.find("a", string=lambda t: t and "next" in t.lower())
            if not next_link:
                break

            # Build next-page payload using __doPostBack
            next_target = next_link.get("href", "")
            if "__doPostBack" in next_target:
                import re as _re
                m = _re.search(r"__doPostBack\(.(\w[\w\$]+)", next_target)
                if m:
                    payload["__EVENTTARGET"] = m.group(1)
                    payload["__EVENTARGUMENT"] = ""
            else:
                break

            page_num += 1
            if page_num > 30:
                break
            time.sleep(0.5)

        return all_records

    # ── Session gate ──────────────────────────────────────────────────────────
    async def _establish_session(self, page) -> bool:
        """
        Navigate the Infovision iGovern session gate.
        The hidden Logon button must be triggered via JS .click() not Playwright click.
        """
        log.info("Establishing session…")
        for attempt in range(RETRY_LIMIT):
            try:
                await page.goto(HOME_URL, timeout=30_000,
                                wait_until="domcontentloaded")
                await asyncio.sleep(2)

                html = await page.content()
                log.info("  Home page loaded (%d chars)", len(html))

                # ── Strategy 1: JS-click the hidden Logon button ──────────────
                # This is the exact element that was failing: LoginForm1_btnLogon
                logon_result = await page.evaluate("""() => {
                    // Try by ID first
                    let btn = document.getElementById('LoginForm1_btnLogon');
                    if (btn) { btn.click(); return 'clicked_by_id'; }

                    // Try by name
                    btn = document.querySelector('[name*="btnLogon"]');
                    if (btn) { btn.click(); return 'clicked_by_name'; }

                    // Try submitting the form directly
                    let form = document.getElementById('LoginForm1');
                    if (form) { form.submit(); return 'form_submitted'; }

                    // Try any form with logon
                    for (let f of document.forms) {
                        if (f.id && f.id.toLowerCase().includes('login')) {
                            f.submit(); return 'login_form_submitted';
                        }
                    }

                    // Try __doPostBack
                    if (typeof __doPostBack !== 'undefined') {
                        __doPostBack('LoginForm1$btnLogon', '');
                        return 'dopostback';
                    }

                    return 'no_logon_found';
                }""")
                log.info("  Logon JS result: %s", logon_result)

                if logon_result != 'no_logon_found':
                    await asyncio.sleep(2)
                    try:
                        await page.wait_for_load_state("domcontentloaded",
                                                        timeout=10_000)
                    except Exception:
                        pass

                # ── Navigate DIRECTLY — portal menu links have onclick=false ──
                # All menu items use onclick="{return false;}" which blocks
                # Playwright clicks. Direct URL navigation works once the
                # session cookie is established by the JS logon click above.
                log.info("  Navigating directly to RealEstate/SearchEntry.aspx…")
                await page.goto(SEARCH_URL, timeout=25_000,
                                wait_until="domcontentloaded")
                await asyncio.sleep(1)

                html = await page.content()
                log.info("  Current URL: %s", page.url)
                log.info("  Page snippet: %s",
                         html[:300].replace('\n', ' ').replace('\r', ''))

                if self._is_search_form(html):
                    log.info("  ✓ Search form confirmed!")
                    return True

                # Last resort: force direct navigation
                await page.goto(SEARCH_URL, timeout=20_000,
                                wait_until="domcontentloaded")
                await asyncio.sleep(1)
                html = await page.content()
                if self._is_search_form(html):
                    log.info("  ✓ Direct navigation succeeded!")
                    return True

                log.warning("  Attempt %d: form not confirmed, retrying…",
                            attempt + 1)
                await asyncio.sleep(3)

            except Exception as e:
                log.warning("  Session attempt %d failed: %s", attempt + 1, e)
                await asyncio.sleep(3)

        # Even if we can't confirm, try anyway
        log.warning("Could not confirm search form — attempting search anyway")
        return True

    @staticmethod
    def _is_search_form(html: str) -> bool:
        h = html.lower()
        return any(kw in h for kw in
                   ["date filed", "instrument type", "doc type",
                    "grantor", "party name", "searchentry",
                    "file date", "recorded date"])

    # ── Discover form fields ─────────────────────────────────────────────────
    async def _get_dropdown_options(self, page) -> dict[str, str]:
        """
        Dump the entire search form structure so we know exactly what fields exist.
        The Fort Bend portal uses a text search form — not a doc-type dropdown.
        We log all selects/inputs/radios so we can see the real field names.
        """
        import json as _json
        form_info = await page.evaluate("""() => {
            const r = {selects: [], inputs: [], radios: []};
            document.querySelectorAll('select').forEach(s => {
                r.selects.push({name: s.name, id: s.id,
                    options: Array.from(s.options).map(o => o.text.trim()+'=>'+o.value)});
            });
            document.querySelectorAll('input[type=text],input[type=date],input:not([type])').forEach(i => {
                r.inputs.push({name: i.name, id: i.id,
                               placeholder: i.placeholder, value: i.value});
            });
            document.querySelectorAll('input[type=radio]').forEach(rb => {
                r.radios.push({name: rb.name, id: rb.id, value: rb.value,
                    label: rb.labels&&rb.labels[0]?rb.labels[0].textContent.trim():''});
            });
            return r;
        }""")
        log.info("  FORM selects: %s", _json.dumps(form_info.get('selects',[]), separators=(',',':')))
        log.info("  FORM inputs:  %s", _json.dumps(form_info.get('inputs',[]),  separators=(',',':')))
        log.info("  FORM radios:  %s", _json.dumps(form_info.get('radios',[]),  separators=(',',':')))

        # Only return real instrument-type options (>4 items, excluding match-type words)
        skip = {"BEGINS WITH","CONTAINS","EXACT MATCH","SOUNDS LIKE",
                "-- SELECT --","SELECT TYPE","ALL TYPES","ALL","SELECT",""}
        result = {}
        for s in form_info.get('selects', []):
            opts = {}
            for o in s.get('options', []):
                parts = o.split('=>', 1)
                txt = parts[0].strip().upper()
                val = parts[1] if len(parts) > 1 else parts[0]
                if txt not in skip:
                    opts[txt] = val
            if len(opts) > 4:
                result.update(opts)
        return result

    # ── Per-type search ───────────────────────────────────────────────────────
    async def _search_one(self, page, code: str, label: str,
                           dropdown_opts: dict,
                           date_from: str, date_to: str) -> list[dict]:
        await page.goto(SEARCH_URL, timeout=20_000, wait_until="domcontentloaded")
        await asyncio.sleep(0.5)

        html = await page.content()
        if ("must be logged" in html.lower() or
                "session" in html.lower() and "expired" in html.lower()):
            await self._establish_session(page)
            await page.goto(SEARCH_URL, timeout=20_000,
                            wait_until="domcontentloaded")
            await asyncio.sleep(0.5)

        # Dump raw HTML once (for LP only) so we can see exact form fields
        if code == "LP":
            html_dump = await page.content()
            # Extract just the form portion to keep log manageable
            import re as _re
            form_match = _re.search(r'<form[^>]*>.*?</form>', html_dump,
                                     _re.S | _re.I)
            snippet = form_match.group(0)[:3000] if form_match else html_dump[:3000]
            log.info("  RAW FORM HTML: %s", snippet.replace('\n',' ').replace('\r',''))

        # Click the "Document Type" search category radio button if it exists
        await self._select_search_category(page, "document type")

        await self._fill_dates(page, date_from, date_to)
        type_set = await self._fill_doc_type(page, code, label, dropdown_opts)
        await self._submit(page)
        await asyncio.sleep(1)

        # Log results page info for first search only
        if code == "LP":
            result_html = await page.content()
            log.info("  Results URL: %s", page.url)
            log.info("  Results snippet: %s",
                     result_html[result_html.lower().find('<body'):
                                 result_html.lower().find('<body')+800
                                 ].replace('\n',' ')[:600]
                     if '<body' in result_html.lower() else result_html[:400])

        return await self._paginate(page, code, label, type_set)

    async def _select_search_category(self, page, category_keyword: str):
        """Click a radio button or tab matching the search category."""
        kw = category_keyword.lower()
        # Try radio buttons first
        radios = page.locator("input[type='radio']")
        count = await radios.count()
        for i in range(count):
            r = radios.nth(i)
            label_text = await page.evaluate("""(el) => {
                if (el.labels && el.labels[0]) return el.labels[0].textContent.trim().toLowerCase();
                const id = el.id;
                if (id) {
                    const lbl = document.querySelector('label[for="'+id+'"]');
                    if (lbl) return lbl.textContent.trim().toLowerCase();
                }
                return el.value.toLowerCase();
            }""", await r.element_handle())
            if kw in label_text:
                try:
                    await r.check()
                    await asyncio.sleep(0.3)
                    log.debug("  Selected radio: %s", label_text)
                    return
                except Exception:
                    pass

    async def _fill_dates(self, page, date_from: str, date_to: str):
        """
        Fort Bend date fields have no name/id — they are JS datepicker widgets.
        We fill them via JavaScript by finding inputs with placeholder mm/dd/yyyy.
        """
        result = await page.evaluate(f"""() => {{
            const inputs = Array.from(document.querySelectorAll('input[type=text],input:not([type])'));
            const dateInputs = inputs.filter(i =>
                i.value === 'mm/dd/yyyy' ||
                i.placeholder === 'mm/dd/yyyy' ||
                (i.id && i.id.toLowerCase().includes('date')) ||
                (i.name && i.name.toLowerCase().includes('date'))
            );
            if (dateInputs.length >= 2) {{
                dateInputs[0].value = '{date_from}';
                dateInputs[0].dispatchEvent(new Event('change', {{bubbles:true}}));
                dateInputs[0].dispatchEvent(new Event('blur', {{bubbles:true}}));
                dateInputs[1].value = '{date_to}';
                dateInputs[1].dispatchEvent(new Event('change', {{bubbles:true}}));
                dateInputs[1].dispatchEvent(new Event('blur', {{bubbles:true}}));
                return 'filled_' + dateInputs.length + '_date_fields';
            }}
            // Fallback: try all inputs with mm/dd/yyyy value
            const all = inputs.filter(i => i.value === 'mm/dd/yyyy');
            if (all.length >= 2) {{
                all[0].value = '{date_from}';
                all[0].dispatchEvent(new Event('change', {{bubbles:true}}));
                all[1].value = '{date_to}';
                all[1].dispatchEvent(new Event('change', {{bubbles:true}}));
                return 'filled_by_placeholder_' + all.length;
            }}
            return 'no_date_fields_found: ' + inputs.map(i=>i.name+'|'+i.id+'|'+i.value).join(', ');
        }}""")
        log.info("  Date fill result: %s", result)

    async def _fill_doc_type(self, page, code: str, label: str,
                              dropdown_opts: dict) -> bool:
        """
        Fort Bend form dump revealed:
          - Doc type text field: id="cphNoMargin_f_DataTextEdit1"
          - Search method select: id="cphNoMargin_f_ddlSearchType"
            options: CONTAINS, BEGINS WITH, EXACT MATCH, SOUNDS LIKE
        We type the doc type keyword and set method to CONTAINS.
        """
        search_term = DOC_TYPE_KEYWORDS.get(code, [label])[0]

        # Set search method to CONTAINS
        method_sel = page.locator(
            "select[id='cphNoMargin_f_ddlSearchType'], "
            "select[name='ctl00$cphNoMargin$f$ddlSearchType']"
        )
        if await method_sel.count() > 0:
            try:
                await method_sel.first.select_option(value="CONTAINS")
            except Exception:
                pass

        # Fill the document type text field — exact id from form dump
        doc_field = page.locator(
            "input[id='cphNoMargin_f_DataTextEdit1'], "
            "input[name='cphNoMargin_f_DataTextEdit1']"
        )
        if await doc_field.count() > 0:
            await doc_field.first.click()
            await doc_field.first.fill(search_term)
            log.info("  Doc type field set to: %s", search_term)
            return True

        # Fallback: try any text input not already filled
        for inp_pat in [
            "input[name*='DataTextEdit']",
            "input[name*='DocType']",
            "input[name*='InstrumentType']",
        ]:
            inp = page.locator(inp_pat)
            if await inp.count() > 0:
                await inp.first.click()
                await inp.first.fill(search_term)
                return True
        return False

    async def _submit(self, page):
        """
        Fort Bend form: onsubmit="javascript:return WebForm_OnSubmit();"
        Must call WebForm_OnSubmit() then form.submit() via JS — button click
        alone doesn't trigger the full ASP.NET postback navigation.
        """
        result = await page.evaluate("""() => {
            try {
                if (typeof WebForm_OnSubmit === 'function') {
                    const ok = WebForm_OnSubmit();
                    if (!ok) return 'webform_blocked';
                }
                const form = document.getElementById('form1') ||
                             document.querySelector('form[action*="SearchEntry"]') ||
                             document.querySelector('form');
                if (form) { form.submit(); return 'form_submitted'; }
                return 'no_form_found';
            } catch(e) { return 'error:' + e.message; }
        }""")
        log.info("  Submit result: %s", result)
        try:
            await page.wait_for_load_state("domcontentloaded", timeout=20_000)
        except PWTimeout:
            pass
        await asyncio.sleep(0.5)
        log.info("  Post-submit URL: %s", page.url)

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
                await page.wait_for_load_state("domcontentloaded",
                                                timeout=15_000)
                await asyncio.sleep(0.6)
            except Exception:
                break
            page_num += 1
            if page_num > 30:
                break
        return all_recs

    # ── Broad date search fallback ────────────────────────────────────────────
    async def _broad_search(self, page, date_from: str, date_to: str) -> list[dict]:
        """Search only by date range, collect everything, post-filter by doc type."""
        await page.goto(SEARCH_URL, timeout=20_000, wait_until="domcontentloaded")
        await asyncio.sleep(0.5)
        await self._fill_dates(page, date_from, date_to)
        await self._submit(page)
        await asyncio.sleep(1)
        # Log what we got back
        html = await page.content()
        log.info("  Broad search result URL: %s", page.url)
        log.info("  Broad result snippet: %s",
                 (html[html.lower().find('<body'):html.lower().find('<body')+500]
                 .replace('\n',' ').replace('\r','')) if '<body' in html.lower() else html[:400])
        all_recs = await self._paginate(page, "OTHER", "All Types", False)
        matched = [r for r in all_recs if r["cat"] != "OTHER"]
        log.info("  Broad: %d total rows → %d matched target types",
                 len(all_recs), len(matched))
        return matched

    # ── HTML table parser ─────────────────────────────────────────────────────
    def _parse_full_count_text(self, big_text: str, code: str,
                                label: str) -> list[dict]:
        """
        After "get full count", all 20 records are concatenated into one
        table cell as flat text. Parse them with regex.

        Format: "N View DOCNUM DOCNUM DOCNUM MM/DD/YYYY DOCTYPE DOCTYPE
                 [R] OWNER [E] GRANTEE R OWNER GRANTEE LEGAL Temp Temp E OPR_ID ..."
        """
        today = datetime.now()
        recs  = []

        # Split on each "N View 20xxxxxxxxxx" pattern
        SPLIT_RE = re.compile(r'(?=\d{1,4}\s+View\s+20\d{8}\s)')
        parts = SPLIT_RE.split(big_text)

        for part in parts:
            part = part.strip()
            if not part:
                continue
            try:
                doc_num_m = re.search(r'View\s+(20\d{8})', part)
                if not doc_num_m:
                    continue
                doc_num = doc_num_m.group(1)

                date_m = re.search(r'(\d{2}/\d{2}/\d{4})', part)
                if not date_m:
                    continue
                raw_date = date_m.group(1)

                try:
                    filed_dt  = datetime.strptime(raw_date, "%m/%d/%Y")
                    filed_str = filed_dt.strftime("%Y-%m-%d")
                    if (today - filed_dt).days > LOOK_BACK_DAYS + 1:
                        continue
                except Exception:
                    continue

                doc_type_m = re.search(
                    r'\d{2}/\d{2}/\d{4}\s+([A-Z][A-Z0-9 /]+?)\s+\[R\]', part)
                raw_doc_type = ""
                if doc_type_m:
                    # Doc type is repeated (e.g. "DEED DEED"), take unique part
                    dt = doc_type_m.group(1).strip()
                    words = dt.split()
                    mid = len(words) // 2
                    if words[:mid] == words[mid:]:
                        dt = " ".join(words[:mid])
                    raw_doc_type = dt

                owner_m = re.search(r'\[R\]\s*(.*?)\s+\[E\]', part)
                raw_owner = owner_m.group(1).strip() if owner_m else ""
                # Clean trailing (+)
                raw_owner = re.sub(r'\s*\(\+\)\s*$', '', raw_owner).strip()

                grantee_m = re.search(r'\[E\]\s*(.*?)\s+R\s', part)
                raw_grantee = grantee_m.group(1).strip() if grantee_m else ""
                raw_grantee = re.sub(r'\s*\(\+\)\s*$', '', raw_grantee).strip()

                legal_m = re.search(
                    r'(?:LT|TRACT|LOTS?|SEC)\s+[\w\s]+(?=\s+Temp)', part)
                legal = legal_m.group(0).strip().rstrip('Temp').strip() if legal_m else ""

                glob_m = re.search(r'(OPR\d+)', part)
                global_id = glob_m.group(1) if glob_m else ""
                clerk_url = (f"{BASE_URL}/RealEstate/SearchResults.aspx"
                             f"?global_id={global_id}&type=dtl") if global_id else SEARCH_URL

                rec_code, rec_label = classify_doc_type(raw_doc_type)

                rec = {
                    "doc_num":      doc_num,
                    "doc_type":     raw_doc_type,
                    "filed":        filed_str,
                    "cat":          rec_code,
                    "cat_label":    rec_label,
                    "owner":        raw_owner,
                    "grantee":      raw_grantee,
                    "amount":       "",
                    "legal":        legal,
                    "clerk_url":    clerk_url,
                    "prop_address": "",
                    "prop_city":    "",
                    "prop_state":   "TX",
                    "prop_zip":     "",
                    "mail_address": "",
                    "mail_city":    "",
                    "mail_state":   "TX",
                    "mail_zip":     "",
                }

                # Enrich from parcel DB
                parcel = (self.parcel_db.lookup_instrument(doc_num)
                          or self.parcel_db.lookup(raw_owner))
                if parcel:
                    rec.update({k: v for k, v in parcel.items()
                                 if v and isinstance(v, str) and len(v) < 100})

                _sc, rec["flags"] = score_record(rec)
                rec["score"] = int(_sc)
                recs.append(rec)
            except Exception as e:
                log.debug("  full_count parse error: %s", e)

        return recs

    def _enrich_from_detail(self, html: str, rec_map: dict):
        """
        Parse a Fort Bend document detail page to extract address and
        full party names, then update the matching record in rec_map.
        Detail pages are at: SearchResults.aspx?global_id=OPRxxxxxxx&type=dtl
        """
        soup = BeautifulSoup(html, "lxml")
        # Find instrument number to match back to our record
        doc_num = ""
        for label_patterns in [
            ["Instrument", "Reference", "Document Number", "Inst #"],
        ]:
            for pat in label_patterns:
                el = soup.find(string=re.compile(pat, re.I))
                if el:
                    parent = el.find_parent()
                    if parent:
                        sib = parent.find_next_sibling()
                        if sib:
                            doc_num = sib.get_text(strip=True)
                            break
            if doc_num:
                break

        if not doc_num or doc_num not in rec_map:
            # Try extracting from page title or URL patterns
            for tag in soup.find_all(["td", "th", "span"]):
                txt = tag.get_text(strip=True)
                if re.match(r"^20\d{8}$", txt) and txt in rec_map:
                    doc_num = txt
                    break

        if not doc_num or doc_num not in rec_map:
            return

        rec = rec_map[doc_num]
        # Try instrument lookup from FBCAD data first
        fbcad = self.parcel_db.lookup_instrument(doc_num)
        if fbcad:
            for k, v in fbcad.items():
                if v and not rec.get(k):
                    rec[k] = v
        page_text = soup.get_text(" ")

        # Extract grantor/grantee from detail page
        for label in ["Grantor:", "Grantor"]:
            m = re.search(label + r"\s*([A-Z][A-Z ,\.&]+)", page_text)
            if m and not rec.get("owner"):
                rec["owner"] = m.group(1).strip()
                break

        for label in ["Grantee:", "Grantee"]:
            m = re.search(label + r"\s*([A-Z][A-Z ,\.&]+)", page_text)
            if m and not rec.get("grantee"):
                rec["grantee"] = m.group(1).strip()
                break

        # Extract property address — look for common address patterns
        addr_match = re.search(
            r"(\d+\s+[A-Z][A-Z0-9 ]+(?:ST|AVE|DR|LN|RD|BLVD|CT|PL|WAY|CIR|TRL)[.,]?\s*"
            r"(?:[A-Z][A-Z ]+,?\s*TX\s*\d{5})?)",
            page_text, re.I
        )
        if addr_match and not rec.get("prop_address"):
            addr_parts = addr_match.group(1).strip().split()
            # Separate street from city/state/zip
            rec["prop_address"] = " ".join(addr_parts[:5])
            rec["prop_state"] = "TX"

        # Also look for table rows with Address label
        for row in soup.find_all("tr"):
            cells = row.find_all(["td", "th"])
            if len(cells) >= 2:
                lbl = cells[0].get_text(strip=True).lower()
                val = cells[1].get_text(strip=True)
                if "address" in lbl and val and not rec.get("prop_address"):
                    rec["prop_address"] = val
                elif "city" in lbl and val:
                    rec["prop_city"] = val
                elif "zip" in lbl and val:
                    rec["prop_zip"] = val
                elif "legal" in lbl and val and not rec.get("legal"):
                    rec["legal"] = val
                elif "amount" in lbl or "consideration" in lbl:
                    if val and not rec.get("amount"):
                        rec["amount"] = val

        # Re-score after enrichment
        _sc, rec["flags"] = score_record(rec)
        rec["score"] = int(_sc)

    def _parse_table(self, html: str, code: str, label: str,
                     exact_type: bool) -> list[dict]:
        """
        Parse Fort Bend results. The portal returns results on the SAME
        SearchEntry.aspx page in an Infragistics WebDataGrid.

        The grid rows are <tr> elements inside a table whose id contains
        'gridResults' or similar. Column data is in <td> cells. The column
        headers come from <th> or the first <tr>.

        We try multiple strategies:
        1. Find any table with date-like content and instrument numbers
        2. Look for Infragistics grid by id patterns
        3. Parse all tables and find the one with the most data rows
        """
        soup  = BeautifulSoup(html, "lxml")
        today = datetime.now()
        recs  = []

        # Strategy 1: find tables by Infragistics grid id patterns
        # The grid id typically contains 'grid' or 'grd' or 'results'
        target = None

        # Look for tables with ids matching grid patterns
        for tbl in soup.find_all("table"):
            tid = (tbl.get("id") or "").lower()
            if any(kw in tid for kw in ["grid", "grd", "result", "search"]):
                rows = tbl.find_all("tr")
                if len(rows) > 1:
                    target = tbl
                    log.info("  Found grid table by id: %s rows=%d", tid, len(rows))
                    break

        # Strategy 2: find largest table with date-like content
        if not target:
            best_tbl, best_score, best_rows = None, 0, 0
            for tbl in soup.find_all("table"):
                rows = tbl.find_all("tr")
                if len(rows) < 2:
                    continue
                # Check up to 200 rows for dates, weight by total row count
                date_rows = 0
                for tr in rows[:200]:
                    if re.search(r"\d{2}/\d{2}/\d{4}", tr.get_text(" ")):
                        date_rows += 1
                # Prefer tables with more date rows AND more total rows
                score = date_rows * len(rows)
                if score > best_score:
                    best_score = score
                    best_tbl = tbl
                    best_rows = len(rows)
            if best_score > 0:
                target = best_tbl
                log.info("  Found table by date content, score=%d total_rows=%d",
                         best_score, best_rows)

        if not target:
            log.info("  No results table found in HTML (len=%d)", len(html))
            return recs

        # Detect columns from first row
        all_rows = target.find_all("tr")
        hrow = all_rows[0]
        col_map = {}

        for i, cell in enumerate(hrow.find_all(["th", "td"])):
            h = cell.get_text(strip=True).lower()
            if re.search(r"inst(rument)?\s*(num|#|no|number)|ref", h):
                col_map.setdefault("doc_num", i)
            elif re.search(r"(instrument|doc(ument)?|action)\s*type|type|module", h):
                col_map.setdefault("doc_type", i)
            elif re.search(r"(file|record|action|added)\s*(date|time)|date", h):
                col_map.setdefault("filed", i)
            elif re.search(r"grantor|party\s*1|seller|owner", h):
                col_map.setdefault("owner", i)
            elif re.search(r"grantee|party\s*2|buyer", h):
                col_map.setdefault("grantee", i)
            elif re.search(r"legal|desc(ription)?|abstract", h):
                col_map.setdefault("legal", i)
            elif re.search(r"amount|consider|price|value|fee", h):
                col_map.setdefault("amount", i)

        # If no headers matched, use positional defaults
        # Fort Bend Infragistics grid column order from ViewState:
        # 0=session#, 1=batch#, 2=date_added, 3=module_id(doc_type),
        # 4=action_type(doc_type), 5=dest, 6=img, 7=img, 8=img,
        # 9=INSTRUMENT_NUMBER, 10=DOC_DESCRIPTION
        if not col_map:
            col_map = {"doc_num": 9, "doc_type": 4, "filed": 2,
                       "owner": 10, "grantee": 11}

        data_rows = all_rows[1:]
        log.info("  Parsing %d data rows, col_map=%s", len(data_rows), col_map)
        # Log first 3 rows to diagnose filtering
        for _i, _tr in enumerate(data_rows[:3]):
            _cells = _tr.find_all(["td","th"])
            _texts = [c.get_text(" ", strip=True)[:25] for c in _cells]
            log.info("  Row %d sample: %s", _i, _texts[:12])


        for tr in data_rows:
            try:
                cells = tr.find_all(["td", "th"])
                if len(cells) < 2:
                    continue
                texts = [c.get_text(" ", strip=True) for c in cells]
                if not any(t.strip() for t in texts):
                    continue

                def _get(key, default=""):
                    idx = col_map.get(key)
                    return texts[idx].strip() \
                        if idx is not None and idx < len(texts) else default

                doc_num      = _get("doc_num") or texts[0]
                raw_doc_type = _get("doc_type")
                raw_date     = _get("filed")

                # Fort Bend party field format: "[R] GRANTOR NAME (+) [E] GRANTEE NAME"
                # Find the party cell by scanning all cells for [R] pattern
                party_raw = ""
                for _t in texts:
                    if "[R]" in _t or "[E]" in _t:
                        party_raw = _t
                        break

                raw_owner   = ""
                raw_grantee = ""
                if party_raw:
                    # Extract grantor (Recorder/Grantor = [R])
                    r_match = re.search(r'\[R\]\s*([^(+\[]+)', party_raw)
                    if r_match:
                        raw_owner = r_match.group(1).strip().rstrip("(+").strip()
                    # Extract grantee ([E])
                    e_match = re.search(r'\[E\]\s*([^\[+]+)', party_raw)
                    if e_match:
                        raw_grantee = e_match.group(1).strip()
                else:
                    raw_owner = _get("owner")
                    raw_grantee = _get("grantee")

                # Skip header-like rows
                if re.match(r"^(instrument|doc|ref|session|batch|#|no\.?)$",
                            doc_num.strip(), re.I):
                    continue
                if not doc_num.strip():
                    continue

                # DEBUG: log what we extracted (first 3 rows only)
                if len(recs) < 3:
                    log.info("  DBG doc_num=%r filed=%r owner=%r len_texts=%d",
                             doc_num, raw_date, raw_owner, len(texts))

                # Parse date — look in ALL cells if needed
                filed_str = ""
                date_candidates = [raw_date] + texts
                for raw in date_candidates:
                    for fmt in ("%m/%d/%Y", "%Y-%m-%d", "%m-%d-%Y",
                                "%m/%d/%Y %I:%M %p", "%m/%d/%Y %H:%M"):
                        try:
                            dt_part = raw.strip().split()[0] if raw.strip() else ""
                            filed_str = datetime.strptime(dt_part, fmt.split()[0]).strftime("%Y-%m-%d")
                            break
                        except Exception:
                            pass
                    if filed_str:
                        break

                if not filed_str:
                    continue

                try:
                    if (today - datetime.strptime(filed_str, "%Y-%m-%d")).days > LOOK_BACK_DAYS + 1:
                        continue
                except Exception:
                    continue

                if exact_type:
                    rec_code, rec_label = code, label
                else:
                    rec_code, rec_label = classify_doc_type(raw_doc_type or label)

                # Build clerk URL — Fort Bend uses global_id links on doc numbers
                link = ""
                for cell in cells:
                    a = cell.find("a", href=True)
                    if a:
                        href = a["href"]
                        # Any link with global_id or SearchResults is a doc detail link
                        if "global_id" in href or "SearchResults" in href or                            "SearchDetail" in href or "Document" in href:
                            link = (href if href.startswith("http")
                                    else BASE_URL + "/RealEstate/" + href.lstrip("./"))
                            break

                rec = {
                    "doc_num":      doc_num.strip(),
                    "doc_type":     raw_doc_type or rec_label,
                    "filed":        filed_str,
                    "cat":          rec_code,
                    "cat_label":    rec_label,
                    "owner":        raw_owner,
                    "grantee":      raw_grantee or _get("grantee"),
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
                # Try instrument number lookup first (most precise)
                parcel = self.parcel_db.lookup_instrument(doc_num.strip())
                if not parcel:
                    # Fall back to owner name lookup
                    parcel = self.parcel_db.lookup(raw_owner)
                if parcel:
                    rec.update({k: v for k, v in parcel.items() if v})
                _sc, rec["flags"] = score_record(rec); rec["score"] = int(_sc)
                recs.append(rec)
            except Exception as e:
                log.debug("Row error: %s", e)

        return recs

# ═══════════════════════════════════════════════════════════════════════════════
#  OUTPUT
# ═══════════════════════════════════════════════════════════════════════════════
def deduplicate(records: list[dict]) -> list[dict]:
    seen, out = set(), []
    for r in records:
        key = (r.get("doc_num", ""), r.get("cat", ""), r.get("filed", ""))
        if key not in seen:
            seen.add(key); out.append(r)
    return out


def build_output(records: list[dict]) -> dict:
    now = datetime.utcnow()
    return {
        "fetched_at":   now.isoformat() + "Z",
        "source":       "Fort Bend County Clerk + Fort Bend CAD",
        "date_range":   {
            "from": (now - timedelta(days=LOOK_BACK_DAYS)).strftime("%Y-%m-%d"),
            "to":   now.strftime("%Y-%m-%d"),
        },
        "total":        len(records),
        "with_address": sum(1 for r in records
                            if (r.get("prop_address") and len(r.get("prop_address","")) < 80)
                            or (r.get("mail_address") and len(r.get("mail_address","")) < 80)),
        "records":      sorted(records,
                               key=lambda x: x.get("score", 0), reverse=True),
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
                "Motivated Seller Flags": "; ".join(r.get("flags", []) if isinstance(r.get("flags"), list) else []),
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
        sum(1 for r in records if int(r.get("score", 0) or 0) >= 70),
    )


if __name__ == "__main__":
    asyncio.run(main())
