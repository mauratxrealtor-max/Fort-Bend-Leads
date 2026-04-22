# Fort Bend County — Motivated Seller Lead Scraper

Automated daily scraper for Harris County & Fort Bend County public records.
Identifies motivated sellers via Lis Pendens, Foreclosure, Tax Deeds, Judgments,
Liens, Probate filings, and more.

---

## 📁 File Structure

```
.github/workflows/scrape.yml   ← GitHub Actions (daily 7 AM UTC + manual trigger)
scraper/
  fetch.py                     ← Main scraper (Playwright + BS4 + dbfread)
  requirements.txt
dashboard/
  index.html                   ← Live dashboard (GitHub Pages)
  records.json                 ← Latest records (updated by workflow)
data/
  records.json                 ← Duplicate output for downstream use
  ghl_export.csv               ← GHL / CRM import-ready CSV
```

---

## 🚀 First-Time Setup

### 1. Push this repo to GitHub

```bash
git init
git add -A
git commit -m "initial commit"
git remote add origin https://github.com/YOUR_USER/YOUR_REPO.git
git push -u origin main
```

### 2. Enable GitHub Pages

1. Go to **Settings → Pages**
2. Set **Source** → `GitHub Actions`
3. Save

### 3. Trigger the first run

1. Go to **Actions tab**
2. Click **Scrape & Deploy**
3. Click **Run workflow** → **Run workflow**
4. Wait ~5 minutes for completion
5. Your dashboard will be live at `https://YOUR_USER.github.io/YOUR_REPO/`

---

## 📊 Lead Types Scraped

| Code | Description | Score Boost |
|------|-------------|-------------|
| LP | Lis Pendens | +10, +20 if also NOFC |
| NOFC | Notice of Foreclosure | +10 |
| TAXDEED | Tax Deed | +10 |
| JUD/CCJ/DRJUD | Judgments | +10 |
| LNCORPTX/LNIRS/LNFED | Tax/Federal Liens | +10 |
| LN/LNMECH/LNHOA | Liens | +10 |
| MEDLN | Medicaid Lien | +10 |
| PRO | Probate | +10 |
| NOC | Notice of Commencement | base |
| RELLP | Release Lis Pendens | base |

---

## 🎯 Seller Score (0–100)

| Condition | Points |
|-----------|--------|
| Base | 30 |
| Per flag | +10 |
| LP + Foreclosure combo | +20 |
| Amount > $100k | +15 |
| Amount > $50k | +10 |
| Filed this week | +5 |
| Has address | +5 |

---

## 📤 GHL / GoHighLevel Export

After the dashboard loads, click **⬇ GHL CSV** to download a CSV with:
- First Name, Last Name
- Mailing Address (from parcel data)
- Property Address
- Lead Type, Document Type, Date Filed
- Amount/Debt Owed, Seller Score, Flags
- Public Records URL

---

## 🔄 Schedule

Runs daily at **7:00 AM UTC** (2 AM CDT / 1 AM CST).
Can be triggered manually from the Actions tab at any time.

---

## ⚙️ Notes

- **Harris County Clerk portal**: `https://cclerk.hctx.net/PublicRecords.aspx`  
  Uses Playwright (headless Chromium) for ASP.NET __doPostBack forms.

- **Fort Bend CAD**: Attempts bulk DBF/CSV download from `fbcad.org`.  
  If the bulk URL changes, update `ParcelDB.BULK_URLS` in `scraper/fetch.py`.

- **Retry logic**: All network calls retry 3× with exponential back-off.

- **Never crashes**: Each record is wrapped in try/except; bad records are skipped.
