"""
Peshawar High Court - Reported Judgments PDF Downloader (v2)
==============================================================

What changed from the previous version
----------------------------------------
Your last run got past clicking "Search" but then waited the full 300s and
never found the results table. That almost certainly means one of two
things: (a) leaving every filter on "All" asks the server for the entire
judgment archive at once and it never finishes rendering in time, or
(b) the site treats "no filter chosen" as an empty query and just shows a
"No records found" message instead of a table. This version fixes the
underlying blind-spot either way:

  1. POLLING WAIT instead of one blind 300s wait. Every ~10s it logs what
     it's seeing, so a long wait is never a silent black box again.
  2. "NO RECORDS" DETECTION. If the page says no records were found, the
     script logs that clearly and moves on, instead of waiting out the full
     timeout for a table that was never going to appear.
  3. GENERIC TABLE DETECTION. Instead of one fixed absolute XPath, it looks
     at every <table> on the page and picks the one with the most rows that
     contain a link - this survives small markup changes.
  4. HEADER-BASED COLUMN MAPPING. It reads the header row text ("Case",
     "Judgment", "SC Judgment") to find the right columns instead of
     trusting fixed column numbers - survives column reordering.
  5. OPTIONAL YEAR-BY-YEAR SEARCH. An unfiltered "All years" query is very
     likely too big. If you can find the id/name of the Year <select> on
     the page (open the debug HTML this script saves, or your browser's
     "Inspect element", and search for "<select"), put it in
     YEAR_FILTER_SELECT_ID below and the script will search one year at a
     time instead of everything at once. Left as None, it just does a
     single search like before, but now with the improved diagnostics above.
  6. NO MORE wkhtmltopdf DEPENDENCY. When the server returns an HTML page
     instead of a real PDF, it's now converted using a second, dedicated
     headless Chrome instance (via Chrome's native print-to-PDF), instead
     of the external pdfkit/wkhtmltopdf toolchain. One less thing to
     install - Chrome is already required for scraping.

One-time setup
---------------
    pip install -r requirements.txt

You also need:
  - Google Chrome installed (webdriver-manager fetches a matching
    chromedriver automatically). That's it - no separate PDF tool needed.

Run it with:
    python phc_judgment_downloader.py

If it stops for any reason (crash, internet drop, Ctrl+C), just run it
again - it reads progress_state.json from the download folder and resumes.
"""

import os
import re
import sys
import json
import time
import base64
import hashlib
import logging
import requests
from urllib.parse import urljoin
from datetime import datetime

from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait, Select
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.chrome.options import Options
from selenium.common.exceptions import TimeoutException, NoSuchElementException
from webdriver_manager.chrome import ChromeDriverManager


# ==========================================================================
# CONFIG - edit these to taste
# ==========================================================================
BASE_URL     = "https://www.peshawarhighcourt.gov.pk/PHCCMS/reportedJudgments.php"
DOWNLOAD_DIR = os.path.join(os.path.expanduser("~"), "Desktop", "peshawar_hc")
LOG_FILE     = os.path.join(DOWNLOAD_DIR, "download.log")
STATE_FILE   = os.path.join(DOWNLOAD_DIR, "progress_state.json")

# The button that runs the search.
SEARCH_BUTTON_XPATH = "/html/body/div[1]/div[2]/div[2]/form/table/tbody/tr[5]/td/input"

# Fallback column positions, only used if the header row can't be read for
# some reason (matches: S.No | Case | Remarks | Other Citation |
# PHC Neutral Citation | Decision Date | S.C.Status | Category | Judgment |
# SC Judgment).
COL_CASE        = 2
COL_JUDGMENT    = 9
COL_SC_JUDGMENT = 10

# --- Year-by-year search (recommended fix for the timeout you hit) --------
# Set this to the id or name attribute of the Year <select> element once you
# find it (search a saved debug *.html file for "<select"). Leave as None to
# do a single "All" search like before (now with much better diagnostics).
YEAR_FILTER_SELECT_ID = None
YEAR_RANGE = list(range(2026, 2009, -1))  # only used if the above is set

PAGE_LOAD_TIMEOUT    = 120
RESULTS_WAIT_TIMEOUT = 300     # max wait per query for the results table
POLL_INTERVAL        = 10      # how often (seconds) to log progress while waiting
REQUEST_TIMEOUT       = 90
MAX_DOWNLOAD_RETRIES  = 3
RETRY_BACKOFF_SEC     = 5

HEADLESS = True   # set False to watch the browser work

# Only set this to False if you get SSL errors like "self-signed certificate
# in certificate chain" (common on corporate networks / antivirus HTTPS
# scanning). Try `pip install pip-system-certs` first - it's the proper fix.
VERIFY_SSL = False

if not VERIFY_SSL:
    import urllib3
    urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
    os.environ["WDM_SSL_VERIFY"] = "0"


# ==========================================================================
# LOGGING
# ==========================================================================
os.makedirs(DOWNLOAD_DIR, exist_ok=True)

logger = logging.getLogger("phc_downloader")
logger.setLevel(logging.DEBUG)

_fmt = logging.Formatter("%(asctime)s | %(levelname)-7s | %(message)s", "%Y-%m-%d %H:%M:%S")

_fh = logging.FileHandler(LOG_FILE, encoding="utf-8")
_fh.setFormatter(_fmt)
_fh.setLevel(logging.DEBUG)

_ch = logging.StreamHandler(sys.stdout)
_ch.setFormatter(_fmt)
_ch.setLevel(logging.INFO)

logger.addHandler(_fh)
logger.addHandler(_ch)


# ==========================================================================
# RESUME / CHECKPOINT STATE
# ==========================================================================
def load_state():
    if os.path.exists(STATE_FILE):
        try:
            with open(STATE_FILE, "r", encoding="utf-8") as f:
                state = json.load(f)
        except Exception as e:
            logger.warning(f"Could not read existing state file, starting fresh: {e}")
            state = {}
    else:
        state = {}
    state.setdefault("downloaded", {})
    state.setdefault("completed_years", [])
    return state


def save_state(state):
    tmp = STATE_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(state, f, indent=2, ensure_ascii=False)
    os.replace(tmp, STATE_FILE)


# ==========================================================================
# HELPERS
# ==========================================================================
INVALID_CHARS = r'<>:"/\|?*'


def sanitize_filename(name, max_len=150):
    name = re.sub(f"[{re.escape(INVALID_CHARS)}]", "_", name)
    name = re.sub(r"\s+", " ", name).strip()
    return name[:max_len] if len(name) > max_len else name


def ensure_unique_path(path):
    if not os.path.exists(path):
        return path
    root, ext = os.path.splitext(path)
    i = 1
    while os.path.exists(f"{root} ({i}){ext}"):
        i += 1
    return f"{root} ({i}){ext}"


def sha256_of_file(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def _is_valid_pdf(path):
    try:
        with open(path, "rb") as f:
            return f.read(4) == b"%PDF"
    except OSError:
        return False


def make_pdf_converter_driver():
    """A second, always-headless Chrome instance used only to render
    HTML case documents to PDF (Page.printToPDF via CDP). Kept
    completely separate from the main scraping driver so converting a
    file never disturbs the search-results page or pagination state."""
    options = Options()
    options.add_argument("--headless=new")
    options.add_argument("--disable-gpu")
    options.add_argument("--no-sandbox")
    options.page_load_strategy = "eager"
    try:
        service = Service(ChromeDriverManager().install())
        driver = webdriver.Chrome(service=service, options=options)
    except Exception:
        driver = webdriver.Chrome(options=options)
    driver.set_page_load_timeout(PAGE_LOAD_TIMEOUT)
    return driver


def html_bytes_to_pdf(pdf_driver, html_bytes, dest_pdf_path):
    """Render raw HTML bytes to a real PDF file at dest_pdf_path using
    headless Chrome's native print-to-PDF. Returns True on success."""
    tmp_html = dest_pdf_path + ".src.html"
    try:
        with open(tmp_html, "wb") as f:
            f.write(html_bytes)

        file_url = "file:///" + os.path.abspath(tmp_html).replace("\\", "/")
        pdf_driver.get(file_url)
        time.sleep(0.5)  # let any late-loading content settle

        result = pdf_driver.execute_cdp_cmd(
            "Page.printToPDF",
            {
                "printBackground": True,
                "preferCSSPageSize": True,
                "marginTop": 0.4,
                "marginBottom": 0.4,
                "marginLeft": 0.4,
                "marginRight": 0.4,
            },
        )
        pdf_bytes = base64.b64decode(result["data"])
        tmp_pdf = dest_pdf_path + ".part"
        with open(tmp_pdf, "wb") as f:
            f.write(pdf_bytes)

        if not _is_valid_pdf(tmp_pdf):
            os.remove(tmp_pdf)
            raise ValueError("Chrome print-to-PDF did not produce a valid PDF")

        os.replace(tmp_pdf, dest_pdf_path)
        return True
    except Exception as e:
        logger.warning(f"HTML->PDF conversion failed for {dest_pdf_path}: {e}")
        return False
    finally:
        try:
            os.remove(tmp_html)
        except OSError:
            pass


# ==========================================================================
# SELENIUM SETUP / NAVIGATION
# ==========================================================================
def build_driver():
    options = webdriver.ChromeOptions()
    if HEADLESS:
        options.add_argument("--headless=new")
    options.add_argument("--disable-gpu")
    options.add_argument("--window-size=1920,1080")
    options.add_argument("--log-level=3")
    options.add_argument("--disable-extensions")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--blink-settings=imagesEnabled=false")
    options.page_load_strategy = "eager"
    service = Service(ChromeDriverManager().install())
    driver = webdriver.Chrome(service=service, options=options)
    driver.set_page_load_timeout(PAGE_LOAD_TIMEOUT)
    return driver


def dump_debug_snapshot(driver, tag):
    try:
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        png_path = os.path.join(DOWNLOAD_DIR, f"debug_{tag}_{ts}.png")
        html_path = os.path.join(DOWNLOAD_DIR, f"debug_{tag}_{ts}.html")
        driver.save_screenshot(png_path)
        with open(html_path, "w", encoding="utf-8") as f:
            f.write(driver.page_source)
        logger.info(f"Saved debug snapshot: {png_path} and {html_path}")
    except Exception as e:
        logger.warning(f"Could not save debug snapshot: {e}")


def open_page(driver):
    logger.info(f"Opening {BASE_URL}")
    driver.get(BASE_URL)


def select_year_if_configured(driver, year_value):
    """Best-effort: select the given year in the Year filter, if configured
    and found. Silently skipped (with a warning) if not found, so the
    script still runs an unfiltered search rather than crashing."""
    if not YEAR_FILTER_SELECT_ID:
        return
    el = None
    for by in (By.ID, By.NAME):
        try:
            el = driver.find_element(by, YEAR_FILTER_SELECT_ID)
            break
        except NoSuchElementException:
            continue
    if el is None:
        logger.warning(
            f"Could not find year filter element '{YEAR_FILTER_SELECT_ID}' - "
            f"running an unfiltered search instead for this pass."
        )
        return
    try:
        Select(el).select_by_visible_text(str(year_value))
    except Exception as e:
        logger.warning(f"Could not select year {year_value}: {e}")


def click_search(driver):
    wait = WebDriverWait(driver, PAGE_LOAD_TIMEOUT)
    search_btn = wait.until(EC.element_to_be_clickable((By.XPATH, SEARCH_BUTTON_XPATH)))
    logger.info("Clicking Search")
    search_btn.click()


def find_results_table(driver):
    """Picks the <table> on the page with the most rows containing a link -
    a decent generic proxy for 'the results table', regardless of exactly
    where it sits in the DOM."""
    tables = driver.find_elements(By.TAG_NAME, "table")
    best, best_score = None, 0
    for t in tables:
        try:
            rows = t.find_elements(By.TAG_NAME, "tr")
            link_rows = sum(1 for r in rows if r.find_elements(By.TAG_NAME, "a"))
        except Exception:
            continue
        if link_rows > best_score:
            best_score, best = link_rows, t
    return best, best_score


NO_RESULT_PHRASES = [
    "no record", "no records", "not found", "no data", "no result", "0 records",
]


def wait_for_results_or_empty(driver, timeout, poll_interval=POLL_INTERVAL):
    """Polls until either a results table shows up, the page indicates there
    are no results, or we time out. Logs progress along the way instead of
    waiting silently."""
    start = time.time()
    last_log = -poll_interval
    while time.time() - start < timeout:
        elapsed = time.time() - start

        table, score = find_results_table(driver)
        if table is not None and score > 0:
            return "table", table

        try:
            body_text = driver.find_element(By.TAG_NAME, "body").text.lower()
        except Exception:
            body_text = ""
        if any(p in body_text for p in NO_RESULT_PHRASES):
            return "empty", None

        if elapsed - last_log >= poll_interval:
            logger.info(f"  ... still waiting ({int(elapsed)}s/{timeout}s), page title='{driver.title}'")
            last_log = elapsed
        time.sleep(2)

    return "timeout", None


def get_column_map(table):
    """Reads the header row to map logical names -> 1-indexed <td>
    positions. Falls back to the fixed COL_* constants if that fails."""
    col_map = {}
    try:
        header_cells = table.find_elements(By.XPATH, ".//tr[1]/th | .//tr[1]/td")
        for idx, cell in enumerate(header_cells, start=1):
            h = cell.text.strip().lower()
            if not h:
                continue
            if "case" in h and "case" not in col_map:
                col_map["case"] = idx
            if "sc" in h and "judgment" in h:
                col_map["sc_judgment"] = idx
            elif "judgment" in h and "judgment" not in col_map:
                col_map["judgment"] = idx
    except Exception as e:
        logger.warning(f"Could not read header row, falling back to fixed columns: {e}")

    col_map.setdefault("case", COL_CASE)
    col_map.setdefault("judgment", COL_JUDGMENT)
    col_map.setdefault("sc_judgment", COL_SC_JUDGMENT)
    return col_map


def get_data_rows(table):
    rows = table.find_elements(By.XPATH, ".//tr")
    if rows and not rows[0].find_elements(By.TAG_NAME, "td"):
        rows = rows[1:]  # drop a <th>-only header row
    return rows


def go_to_next_page(driver):
    """Best-effort generic 'next page' handler. Returns False if no
    pagination control is found (also correct behaviour if there's only
    one page of results)."""
    candidates = [
        "//a[contains(translate(text(),'NEXT','next'),'next')]",
        "//a[@rel='next']",
        "//li[contains(@class,'next')]/a",
    ]
    for xp in candidates:
        try:
            btn = driver.find_element(By.XPATH, xp)
            if btn.is_displayed() and btn.is_enabled():
                btn.click()
                time.sleep(2)
                return True
        except NoSuchElementException:
            continue
    return False


# ==========================================================================
# DOWNLOADING
# ==========================================================================
def download_one(session, url, dest_path_no_ext, state, pdf_driver):
    if url in state["downloaded"] and os.path.exists(state["downloaded"][url]["file"]):
        logger.info(f"SKIP (already downloaded): {url}")
        return True

    for attempt in range(1, MAX_DOWNLOAD_RETRIES + 1):
        try:
            resp = session.get(url, timeout=REQUEST_TIMEOUT)
            resp.raise_for_status()
            content_type = resp.headers.get("Content-Type", "").lower()

            if "pdf" in content_type or resp.content[:4] == b"%PDF":
                final_path = ensure_unique_path(dest_path_no_ext + ".pdf")
                with open(final_path, "wb") as f:
                    f.write(resp.content)

            elif "html" in content_type:
                if pdf_driver is None:
                    logger.error(
                        f"Server returned HTML instead of a PDF for {url}, and the "
                        f"PDF-conversion Chrome instance isn't available this run. "
                        f"Skipping retries for this file - it will be picked up "
                        f"automatically on a future run once it's available."
                    )
                    return False
                final_path = ensure_unique_path(dest_path_no_ext + ".pdf")
                if not html_bytes_to_pdf(pdf_driver, resp.content, final_path):
                    raise RuntimeError("html-to-pdf conversion failed")

            else:
                ext = os.path.splitext(url)[1] or ".bin"
                final_path = ensure_unique_path(dest_path_no_ext + ext)
                with open(final_path, "wb") as f:
                    f.write(resp.content)
                logger.warning(f"Unrecognized content-type '{content_type}' for {url}, saved as-is.")

            state["downloaded"][url] = {
                "file": final_path,
                "sha256": sha256_of_file(final_path),
                "timestamp": datetime.now().isoformat(timespec="seconds"),
            }
            save_state(state)
            logger.info(f"OK   -> {final_path}")
            return True

        except Exception as e:
            logger.warning(f"Attempt {attempt}/{MAX_DOWNLOAD_RETRIES} failed for {url}: {e}")
            time.sleep(RETRY_BACKOFF_SEC * attempt)

    logger.error(f"FAILED (all retries exhausted): {url}")
    return False


def process_row(row, col_map, driver, session, state, pdf_driver):
    count = 0
    try:
        cells = row.find_elements(By.TAG_NAME, "td")
        if not cells:
            return 0

        case_idx = col_map.get("case", COL_CASE) - 1
        case_text = cells[case_idx].text.strip() if case_idx < len(cells) else ""
        case_name = sanitize_filename(case_text or "row")

        for key, suffix in (("judgment", "PHC"), ("sc_judgment", "SC")):
            idx = col_map.get(key)
            if idx is None or idx - 1 >= len(cells):
                continue
            for link_el in cells[idx - 1].find_elements(By.TAG_NAME, "a"):
                href = link_el.get_attribute("href")
                if not href:
                    continue
                href = urljoin(driver.current_url, href)
                dest_no_ext = os.path.join(DOWNLOAD_DIR, f"{case_name} [{suffix}]")
                if download_one(session, href, dest_no_ext, state, pdf_driver):
                    count += 1
    except Exception as e:
        logger.warning(f"Row processing failed, skipping: {e}")
    return count


def process_all_pages(driver, session, state, label, pdf_driver):
    total_ok = 0
    page_num = 1
    while True:
        status, table = wait_for_results_or_empty(driver, RESULTS_WAIT_TIMEOUT)

        if status == "empty":
            logger.info(f"[{label}] No records found (page {page_num}) - stopping this query.")
            break
        if status == "timeout":
            logger.error(f"[{label}] Timed out waiting for results (page {page_num}).")
            dump_debug_snapshot(driver, f"timeout_{label}_p{page_num}")
            break

        col_map = get_column_map(table)
        rows = get_data_rows(table)
        logger.info(f"[{label}] Page {page_num}: {len(rows)} data row(s) found")

        # refresh cookies each page in case the site rotates a session token
        for c in driver.get_cookies():
            session.cookies.set(c["name"], c["value"])

        for row in rows:
            total_ok += process_row(row, col_map, driver, session, state, pdf_driver)

        if not go_to_next_page(driver):
            logger.info(f"[{label}] No further pages.")
            break
        page_num += 1

    return total_ok


# ==========================================================================
# MAIN
# ==========================================================================
def main():
    state = load_state()
    driver = None
    pdf_driver = None
    session = requests.Session()
    session.headers.update({"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"})
    session.verify = VERIFY_SSL

    total_ok = 0
    try:
        driver = build_driver()

        try:
            pdf_driver = make_pdf_converter_driver()
        except Exception as e:
            logger.warning(
                f"Could not start the PDF-conversion Chrome instance ({e}). HTML "
                f"results will be skipped this run instead of converted - re-run "
                f"later to pick them up once this is working."
            )
            pdf_driver = None

        if YEAR_FILTER_SELECT_ID:
            years_to_run = [y for y in YEAR_RANGE if str(y) not in state["completed_years"]]
            logger.info(f"Year-by-year mode. Years remaining: {years_to_run}")
        else:
            years_to_run = [None]
            logger.info("No YEAR_FILTER_SELECT_ID configured - running a single unfiltered search.")

        for year in years_to_run:
            label = str(year) if year is not None else "All"
            logger.info(f"=== Searching: {label} ===")

            open_page(driver)
            if year is not None:
                select_year_if_configured(driver, year)
            click_search(driver)

            ok = process_all_pages(driver, session, state, label, pdf_driver)
            total_ok += ok

            if year is not None:
                state["completed_years"].append(str(year))
                save_state(state)

        logger.info(f"DONE. {total_ok} file(s) downloaded/verified this run.")

    except TimeoutException as e:
        logger.error(f"Timed out waiting for a page element (site may be slow or layout changed): {e}")
        if driver:
            dump_debug_snapshot(driver, "unexpected_timeout")
    except Exception as e:
        logger.exception(f"Unhandled error - progress has been saved, just re-run to resume: {e}")
    finally:
        if driver:
            driver.quit()
        if pdf_driver:
            pdf_driver.quit()


if __name__ == "__main__":
    main()
