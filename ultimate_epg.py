#!/usr/bin/env python3
"""Ultimate EPG - merge many M3U playlists and XMLTV guides into one editable
lineup, and serve it as a single playlist + guide link for any IPTV player.

No installs needed beyond Python 3.8+. Run:  python ultimate_epg.py
Then open http://localhost:8787 in a browser.
"""
import gzip
import sys
import hashlib
import html
import json
import os
import re
import shutil
import socket
import threading
import time
import traceback
import urllib.parse
import urllib.error
import urllib.request
import uuid
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse
from xml.sax.saxutils import escape, quoteattr

BASE = os.path.dirname(os.path.abspath(__file__))
DATA = os.path.join(BASE, "data")
CACHE = os.path.join(DATA, "cache")
OUT = os.path.join(DATA, "output")
CONFIG_PATH = os.path.join(DATA, "config.json")
UI_PATH = os.path.join(BASE, "ui.html")
PORT = int(os.environ.get("EPG_PORT", "8787"))
USER_AGENT = "Mozilla/5.0 (UltimateEPG) VLC/3.0"

FIELDS = ["name", "number", "group", "logo", "epg_id", "url", "desc", "enabled"]
DEFAULT_SETTINGS = {
    "refresh_hours": 12,       # automatic re-download of all sources
    "days": 3,                 # how many days of guide to keep
    "dummy_epg": True,         # fake hourly guide for channels with no guide (great for 24/7)
    "dummy_hours": 2,          # block length of dummy guide entries
    "new_enabled": True,       # are newly discovered channels enabled by default
    "auto_match": True,        # after each download, match guide-less channels by name
    "public_url": "",          # GitHub Pages address once put online
    "auto_discover": True,     # search the internet for guides covering guide-less channels
    "discover_per_run": 15,    # how many new guides to try per update
    "discover_max_mb": 80,     # skip guides bigger than this download size
    "health_minutes": 10,      # how often every source is checked to see if it still answers
    "priority_countries": "US,GB,CA",  # most important first; their sources are added and ranked first
    "hide_duplicates": True,   # the same channel from two playlists only appears once (best source wins)
    "full_guide": True,        # also publish epg-full.xml.gz: every channel of your priority countries (any provider)
    "full_guide_days": 2,      # days in the any-provider guides (they are big - fewer days keeps them light)
    "dead_remove_hours": 12,   # a source that keeps failing this long is removed automatically (0 = never)
    "stale_remove_hours": 48,  # a guide with no upcoming shows this long is removed automatically (0 = never)
}

LOCK = threading.RLock()
STATE = {"busy": False, "log": [], "last_build": None}
EPG_INDEX = {}  # xmltv channel id -> {"name", "icon", "source"}

os.makedirs(CACHE, exist_ok=True)
os.makedirs(OUT, exist_ok=True)


# ---------------------------------------------------------------- config

def load_config():
    if os.path.exists(CONFIG_PATH):
        with open(CONFIG_PATH, encoding="utf-8") as f:
            cfg = json.load(f)
    else:
        cfg = {}
    cfg.setdefault("settings", {})
    for k, v in DEFAULT_SETTINGS.items():
        cfg["settings"].setdefault(k, v)
    cfg.setdefault("sources", [])
    cfg.setdefault("channels", {})
    cfg.setdefault("status", {})
    cfg.setdefault("last_refresh", 0)
    cfg.setdefault("keep_urls", [])  # sources you restored - never removed automatically
    cfg.setdefault("dismissed", [])  # library sources you removed - never re-added automatically
    if not os.path.exists(CONFIG_PATH):  # first run: start with the recommended free sources
        try:
            with open(os.path.join(BASE, "catalog.json"), encoding="utf-8") as f:
                cfg["sources"] = [{"id": uuid.uuid4().hex[:8], "type": c["type"], "name": c["name"],
                                   "url": c["url"], "enabled": True}
                                  for c in json.load(f) if c.get("default")]
        except (OSError, ValueError):
            pass
    return cfg


def save_config():
    tmp = CONFIG_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(CFG, f, ensure_ascii=False, indent=1)
    os.replace(tmp, CONFIG_PATH)


CFG = load_config()
AUTO_PATH = os.path.join(DATA, "auto_sources.json")


def load_auto():
    """Guides the program found by itself (kept apart from the sources you chose)."""
    try:
        with open(AUTO_PATH, encoding="utf-8") as f:
            a = json.load(f)
    except (OSError, ValueError):
        a = {}
    for k, v in {"sources": [], "checked": {}, "blocked": [], "last_discovery": 0,
                 "known": 0, "cache": {}, "bad_since": {}, "removed": {}}.items():
        a.setdefault(k, v)
    return a


def save_auto():
    tmp = AUTO_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(AUTO, f, ensure_ascii=False, indent=1)
    os.replace(tmp, AUTO_PATH)


AUTO = load_auto()


def is_removed(src):
    return src["url"] in AUTO["removed"] and src["url"] not in CFG["keep_urls"]


def all_sources():
    """Every source in use: yours + auto-found, minus ones removed automatically for being dead."""
    return [s for s in CFG["sources"] + AUTO["sources"] if not is_removed(s)]


def log(msg):
    line = time.strftime("%H:%M:%S ") + msg
    print(line, flush=True)
    STATE["log"] = (STATE["log"] + [line])[-200:]


def effective(ch):
    e = dict(ch["up"])
    e.update(ch.get("ov", {}))
    return e


def source_by_id(sid):
    return next((s for s in all_sources() if s["id"] == sid), None)


# ---------------------------------------------------------------- download

def fetch(url, dest, max_bytes=None):
    """Download a URL (or copy a local file) to dest, un-gzipping if needed."""
    tmp = dest + ".part"
    if re.match(r"^https?://", url, re.I):
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        with urllib.request.urlopen(req, timeout=180) as r, open(tmp, "wb") as f:
            got = 0
            while chunk := r.read(1 << 20):
                got += len(chunk)
                if max_bytes and got > max_bytes:
                    f.close()
                    os.remove(tmp)
                    raise ValueError(f"bigger than {max_bytes >> 20} MB")
                f.write(chunk)
    else:
        path = url[7:] if url.lower().startswith("file://") else url
        shutil.copyfile(os.path.expanduser(path), tmp)
    with open(tmp, "rb") as f:
        gz = f.read(2) == b"\x1f\x8b"
    if gz:
        with gzip.open(tmp, "rb") as src, open(dest, "wb") as dst:
            shutil.copyfileobj(src, dst, 1 << 20)
        os.remove(tmp)
    else:
        os.replace(tmp, dest)


# ---------------------------------------------------------------- M3U

ATTR_RE = re.compile(r'([\w-]+)="([^"]*)"')


def unescape_all(v):
    """Some playlists write & as &amp; (even &amp;amp;) - turn it back into a plain &."""
    while True:
        u = html.unescape(v)
        if u == v:
            return v
        v = u


def parse_m3u(path):
    with open(path, encoding="utf-8", errors="replace") as f:
        lines = [l.strip() for l in f]
    entries, cur, extra = [], None, []
    for line in lines:
        if not line:
            continue
        if line.upper().startswith("#EXTINF"):
            head, _, title = line.partition(",")
            attrs = {k: unescape_all(v) for k, v in ATTR_RE.findall(head)}
            cur = {"attrs": attrs, "title": unescape_all(title.strip())}
            extra = []
        elif line.startswith("#EXTGRP:") and cur:
            cur["attrs"].setdefault("group-title", line[8:].strip())
        elif line.startswith("#"):
            if cur and not line.upper().startswith("#EXTM3U"):
                extra.append(line)  # #EXTVLCOPT / #KODIPROP etc, kept with the channel
        elif cur:
            a = cur["attrs"]
            entries.append({
                "name": cur["title"] or a.get("tvg-name", "") or "Unnamed",
                "number": a.get("tvg-chno", ""),
                "group": a.get("group-title", ""),
                "logo": a.get("tvg-logo", ""),
                "epg_id": a.get("tvg-id", ""),
                "url": line,
                "desc": "",
                "enabled": True,
                "extra": extra,
            })
            cur, extra = None, []
    return entries


def merge_m3u_source(src, entries):
    sid = src["id"]
    src_index = CFG["sources"].index(src)
    chans = CFG["channels"]
    seen = set()
    added = 0
    for i, e in enumerate(entries):
        base = f"{sid}|{e['epg_id']}|{e['name']}"
        key = hashlib.sha1(base.encode()).hexdigest()[:12]
        n = 1
        while key in seen:
            n += 1
            key = hashlib.sha1(f"{base}|{n}".encode()).hexdigest()[:12]
        seen.add(key)
        extra = e.pop("extra")
        ch = chans.get(key)
        if ch is None:
            ch = chans[key] = {"key": key, "source": sid, "ov": {}}
            if not CFG["settings"]["new_enabled"]:
                ch["ov"]["enabled"] = False
            added += 1
        ch.update(up=e, extra=extra, missing=False, order=(src_index + 1) * 1_000_000 + i)
    for ch in chans.values():
        if ch["source"] == sid and ch["key"] not in seen:
            ch["missing"] = True
    return added


# ---------------------------------------------------------------- XMLTV

def iter_xmltv(path, tags):
    """Stream top-level <channel>/<programme> elements without loading the file."""
    ctx = ET.iterparse(path, events=("start", "end"))
    _, root = next(ctx)
    for ev, el in ctx:
        if ev == "end" and el.tag in ("channel", "programme"):
            if el.tag in tags:
                yield el
            root.clear()


def scan_xmltv(path):
    """Read a guide's channel list and check it actually has upcoming shows."""
    idx, upcoming, last = {}, 0, None
    now = datetime.now(timezone.utc)
    try:
        for el in iter_xmltv(path, ("channel", "programme")):
            if el.tag == "channel":
                names = [d.text or "" for d in el.findall("display-name")]
                icon = el.find("icon")
                idx[el.get("id", "")] = {"names": names, "icon": icon.get("src", "") if icon is not None else ""}
            else:
                end = parse_xmltv_time(el.get("stop") or el.get("start"))
                if end and end > now:
                    upcoming += 1
                    last = max(last, end) if last else end
    except ET.ParseError:
        pass  # keep whatever was readable before the broken part
    fresh = bool(upcoming) and last is not None and last > now + timedelta(hours=12)
    return idx, upcoming, fresh


def index_xmltv_source(src):
    idx, upcoming, fresh = scan_xmltv(os.path.join(CACHE, src["id"] + ".xml"))
    with open(os.path.join(CACHE, src["id"] + ".channels.json"), "w", encoding="utf-8") as f:
        json.dump(idx, f, ensure_ascii=False)
    return len(idx), upcoming, fresh


def status_of(src):
    return src.setdefault("st", {}) if src.get("auto") else CFG["status"].setdefault(src["id"], {})


def load_catalog():
    try:
        with open(os.path.join(BASE, "catalog.json"), encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return []


CATALOG = load_catalog()
CATALOG_COUNTRY = {c["url"]: c["country"] for c in CATALOG}
COUNTRY_TOKENS = {"US": "us usa unitedstates", "GB": "uk gb unitedkingdom britain", "CA": "ca canada",
                  "AU": "au australia", "NZ": "nz newzealand", "IE": "ie ireland", "DE": "de germany",
                  "FR": "fr france", "ES": "es spain", "IT": "it italy", "MX": "mx mexico", "BR": "br brazil",
                  "IN": "in india", "NL": "nl netherlands"}


def priority_list():
    raw = CFG["settings"].get("priority_countries", "") or ""
    out = []
    for c in re.split(r"[,\s]+", raw.upper()):
        c = "GB" if c == "UK" else c
        if c and c not in out:
            out.append(c)
    return out


def guess_country(url, name=""):
    """Which country a source is for: from the library, else from its link/name."""
    if url in CATALOG_COUNTRY:
        return CATALOG_COUNTRY[url]
    text = (url + " " + name).lower()
    for cc in priority_list() + [c for c in COUNTRY_TOKENS if c not in priority_list()]:
        for w in COUNTRY_TOKENS.get(cc, cc.lower()).split():
            if re.search(rf"(^|[^a-z]){w}([^a-z]|$)", text):
                return cc
    return ""


def priority_rank(src):
    order = priority_list()
    cc = src.get("country") or guess_country(src["url"], src.get("name", ""))
    return order.index(cc) if cc in order else len(order)


def sync_priority_sources():
    """Add every library source for your priority countries, and keep sources ranked
    by country (first country in the list wins when two guides cover the same channel)."""
    order = priority_list()
    have = {s["url"] for s in CFG["sources"]}
    added = 0
    for c in CATALOG:
        if c["country"] in order and c["url"] not in have and c["url"] not in CFG["dismissed"]:
            CFG["sources"].append({"id": uuid.uuid4().hex[:8], "type": c["type"], "name": c["name"],
                                   "url": c["url"], "enabled": True})
            added += 1
    CFG["sources"].sort(key=priority_rank)  # stable: your own order is kept within each country
    if added:
        log(f"Added {added} source(s) for your priority countries ({', '.join(order)})")
    return added


def guide_sources():
    """Enabled guides that are working and up to date, priority countries first."""
    return sorted((s for s in all_sources() if s["type"] == "xmltv" and s.get("enabled", True)
                   and status_of(s).get("fresh", True)), key=priority_rank)


def load_epg_index():
    global EPG_INDEX
    new = {}
    for src in guide_sources():
        p = os.path.join(CACHE, src["id"] + ".channels.json")
        if not os.path.exists(p):
            continue
        with open(p, encoding="utf-8") as f:
            for cid, info in json.load(f).items():
                if cid not in new:
                    new[cid] = {"name": (info["names"] or [cid])[0], "names": info["names"],
                                "icon": info["icon"], "source": src["id"]}
    EPG_INDEX = new


TIME_RE = re.compile(r"(\d{14})\s*([+-]\d{4})?")


def parse_xmltv_time(s):
    m = TIME_RE.match(s or "")
    if not m:
        return None
    dt = datetime.strptime(m[1], "%Y%m%d%H%M%S")
    off = m[2] or "+0000"
    delta = timedelta(hours=int(off[1:3]), minutes=int(off[3:5]))
    return dt.replace(tzinfo=timezone.utc) - (delta if off[0] == "+" else -delta)


def fmt_xmltv_time(dt):
    return dt.astimezone(timezone.utc).strftime("%Y%m%d%H%M%S +0000")


# ---------------------------------------------------------------- matching

QUALITY_RE = re.compile(r"\b(hd|fhd|uhd|sd|4k|8k|hevc|h265|h264|1080p?|720p?|50fps|60fps|raw|backup)\b")
PREFIX_RE = re.compile(r"^\s*[\[(|]?\s*[a-z]{2,3}\s*[\])|:]\s*")


def norm(s):
    s = (s or "").lower().replace("&", "and").replace("+", "plus")
    s = PREFIX_RE.sub("", s)
    s = QUALITY_RE.sub("", s)
    return re.sub(r"[^a-z0-9]", "", s)


def auto_match(only_unmatched=True):
    lookup = {}
    for cid, info in EPG_INDEX.items():
        for n in info["names"] + [cid.split(".")[0]]:
            lookup.setdefault(norm(n), cid)
    matched = 0
    for ch in CFG["channels"].values():
        e = effective(ch)
        if only_unmatched and e["epg_id"] in EPG_INDEX:
            continue
        cid = lookup.get(norm(e["name"]))
        if cid:
            ch["ov"]["epg_id"] = cid
            if ch["up"]["epg_id"] == cid:
                del ch["ov"]["epg_id"]
            matched += 1
    return matched


# ---------------------------------------------------------------- auto-discovery

ISO2 = ("AD AE AF AG AL AM AO AR AT AU AZ BA BB BD BE BF BG BH BI BJ BN BO BR BS BT BW BY BZ CA CD CF "
        "CG CH CI CL CM CN CO CR CU CV CY CZ DE DJ DK DM DO DZ EC EE EG ER ES ET FI FJ FM FR GA GB GD GE "
        "GH GM GN GQ GR GT GW GY HK HN HR HT HU ID IE IL IN IQ IR IS IT JM JO JP KE KG KH KI KM KN KP KR "
        "KW KZ LA LB LC LI LK LR LS LT LU LV LY MA MC MD ME MG MH MK ML MM MN MO MR MT MU MV MW MX MY MZ "
        "NA NE NG NI NL NO NP NR NZ OM PA PE PG PH PK PL PR PS PT PW PY QA RO RS RU RW SA SB SC SD SE SG "
        "SI SK SL SM SN SO SR SS ST SV SY SZ TD TG TH TJ TL TM TN TO TR TT TV TW TZ UA UG US UY UZ VA VC "
        "VE VN VU WS XK YE ZA ZM ZW").split()
GUIDE_FILE_RE = re.compile(r"\.xml(\.gz)?$", re.I)
DIR_RE = re.compile(r'href="([^"./?][^"?]*/)"')


def http_text(url, timeout=30):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (UltimateEPG)"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read().decode("utf-8", "replace")


def http_size(url):
    """Download size from the server, or None if it won't say."""
    try:
        req = urllib.request.Request(url, method="HEAD", headers={"User-Agent": "Mozilla/5.0 (UltimateEPG)"})
        with urllib.request.urlopen(req, timeout=20) as r:
            n = r.headers.get("Content-Length")
            return int(n) if n and n.isdigit() else None
    except Exception:
        return None


def http_exists(url):
    try:
        req = urllib.request.Request(url, method="HEAD", headers={"User-Agent": "Mozilla/5.0 (UltimateEPG)"})
        with urllib.request.urlopen(req, timeout=20) as r:
            return r.status == 200 and r.headers.get("Content-Length") != "0"
    except Exception:
        return False


def github_api(path):
    headers = {"User-Agent": "UltimateEPG", "Accept": "application/vnd.github+json"}
    if os.environ.get("GITHUB_TOKEN"):
        headers["Authorization"] = "Bearer " + os.environ["GITHUB_TOKEN"]
    req = urllib.request.Request("https://api.github.com" + path, headers=headers)
    with urllib.request.urlopen(req, timeout=30) as r:
        return json.load(r)


def cached_scan(name, max_age_h, fn):
    """Run an expensive search at most every max_age_h hours."""
    c = AUTO["cache"].get(name)
    if c and time.time() - c["time"] < max_age_h * 3600:
        return c["found"]
    try:
        found = fn()
    except Exception as ex:
        log(f"  could not search {name}: {ex}")
        return c["found"] if c else {}
    AUTO["cache"][name] = {"time": time.time(), "found": found}
    log(f"  {name}: {len(found)} guides listed")
    return found


def scan_mjh():
    found, root = {}, "https://i.mjh.nz/"

    def walk(path, depth):
        listing = http_text(root + path)
        for f in re.findall(r'href="([^"/?]+\.xml\.gz)"', listing):
            found[root + path + f] = f"{path.strip('/')} {f.split('.')[0]} (i.mjh.nz)"
        if depth:
            for d in DIR_RE.findall(listing):
                walk(path + d, depth - 1)
    walk("", 2)
    return found


def scan_epgshare():
    base = "https://epgshare01.online/epgshare01/"
    return {base + f: f[11:-7].replace("_", " ") + " (epgshare01)"
            for f in set(re.findall(r"epg_ripper_[A-Za-z0-9_]+\.xml\.gz", http_text(base)))}


def scan_iptv_epg():
    codes = set(re.findall(r"files/epg-([a-z]{2})\.xml\.gz", http_text("https://iptv-epg.org/")))
    return {f"https://iptv-epg.org/files/epg-{c}.xml.gz": f"{c.upper()} (iptv-epg.org)" for c in codes}


def scan_epg_pw():
    from concurrent.futures import ThreadPoolExecutor
    urls = {c: f"https://epg.pw/xmltv/epg_{c}.xml.gz" for c in ISO2}
    with ThreadPoolExecutor(16) as ex:
        ok = dict(zip(urls, ex.map(http_exists, urls.values())))
    return {u: f"{c} (epg.pw)" for c, u in urls.items() if ok[c]}


def scan_github():
    since = (datetime.now(timezone.utc) - timedelta(days=21)).strftime("%Y-%m-%d")
    repos = {}
    for q in ("xmltv", "epg xmltv", "epg guide", "iptv epg"):
        try:
            r = github_api(f"/search/repositories?q={urllib.parse.quote(q)}+pushed:>{since}&sort=updated&per_page=30")
        except Exception:
            if not repos:
                raise  # rate limited - keep the previous results instead
            break
        for it in r.get("items", []):
            repos.setdefault(it["full_name"], it["default_branch"])
    limit = 60 if os.environ.get("GITHUB_TOKEN") else 25
    found = {}
    max_bytes = CFG["settings"]["discover_max_mb"] << 20
    for repo, branch in list(repos.items())[:limit]:
        try:
            tree = github_api(f"/repos/{repo}/git/trees/{branch}?recursive=1")
        except Exception:
            continue
        files = [t for t in tree.get("tree", [])
                 if t["type"] == "blob" and GUIDE_FILE_RE.search(t["path"])
                 and 20_000 < t.get("size", 0) < max_bytes and re.search(r"epg|guide|xmltv|tv", t["path"], re.I)]
        files.sort(key=lambda t: -t["size"])  # the biggest files are usually the combined guides
        for t in files[:8]:
            url = f"https://raw.githubusercontent.com/{repo}/{branch}/{urllib.parse.quote(t['path'])}"
            found[url] = f"{repo.split('/')[1]}: {os.path.basename(t['path'])} (GitHub)"
    return found


def find_candidates():
    """Every guide file we can find on the internet, best leads first."""
    cands, origin = {}, {}

    def add(found, kind="web"):
        for url, label in found.items():
            if GUIDE_FILE_RE.search(urlparse(url).path) and url not in cands:
                cands[url] = label
                origin[url] = kind
    # 1. guides your own playlists point to
    for src in CFG["sources"]:
        p = os.path.join(CACHE, src["id"] + ".m3u")
        if src["type"] == "m3u" and os.path.exists(p):
            with open(p, encoding="utf-8", errors="replace") as f:
                head = f.readline()
            for attr in ("url-tvg", "x-tvg-url"):
                m = re.search(attr + r'="([^"]+)"', head)
                if m:
                    add({u.strip(): f"guide linked by '{src['name']}'" for u in m[1].split(",")}, "playlist")
    # 2. the verified library
    try:
        with open(os.path.join(BASE, "catalog.json"), encoding="utf-8") as f:
            add({c["url"]: c["name"] for c in json.load(f) if c["type"] == "xmltv"}, "library")
    except (OSError, ValueError):
        pass
    # 3. public guide sites and GitHub
    add(cached_scan("i.mjh.nz", 24, scan_mjh))
    add(cached_scan("epgshare01", 24, scan_epgshare))
    add(cached_scan("iptv-epg.org", 24, scan_iptv_epg))
    add(cached_scan("epg.pw", 24 * 7, scan_epg_pw))
    add(cached_scan("GitHub", 24, scan_github))
    return cands, origin


COUNTRY_WORDS = {"us": "usa unitedstates", "gb": "uk unitedkingdom britain", "uk": "gb unitedkingdom",
                 "ca": "canada", "au": "australia", "nz": "newzealand", "de": "germany deutschland",
                 "fr": "france", "es": "spain espana", "it": "italy italia", "nl": "netherlands",
                 "mx": "mexico", "br": "brazil brasil", "in": "india", "ie": "ireland", "pt": "portugal"}


def rank_candidates(todo, wanted, sources):
    """Try guides from your playlists, the library, and your channels' countries first."""
    counts = {}
    for cid, _ in wanted.values():
        m = re.search(r"\.([a-z]{2})(?:@|$)", cid.lower())
        if m:
            counts[m[1]] = counts.get(m[1], 0) + 1
    weights = {}  # your priority countries first, then your most common channel countries
    for i, cc in enumerate(priority_list()):
        for w in COUNTRY_TOKENS.get(cc, cc.lower()).split():
            weights.setdefault(w, 10 - 2 * i)
    for i, cc in enumerate(sorted(counts, key=counts.get, reverse=True)[:5]):
        for w in [cc] + COUNTRY_WORDS.get(cc, "").split():
            weights.setdefault(w, 5 - i)

    def score(item):
        url, label = item
        u = url.lower()
        sc = {"playlist": 6, "library": 4}.get(sources.get(url), 0)
        sc += max([wt for w, wt in weights.items() if re.search(rf"(^|[^a-z]){w}([^a-z]|$)", u)] or [0])
        if "raw.githubusercontent.com" in u:
            sc -= 1
        if url in AUTO["checked"]:
            sc -= 2  # give never-tried guides a turn first
        return -sc
    return sorted(todo, key=score)


def guide_lookup(idx):
    names = set()
    for cid, info in idx.items():
        names.update(norm(n) for n in info["names"] + [cid.split(".")[0]])
    names.discard("")
    return set(idx), names


def discover():
    """Find guides on the internet that cover channels which still have no guide,
    and add them automatically. Guides that don't help are remembered and re-checked later."""
    settings = CFG["settings"]
    started = time.time()
    with LOCK:
        lineup = {e["key"]: (e["epg_id"], norm(e["name"])) for e in output_channels()}
        wanted = {k: v for k, v in lineup.items() if v[0] not in EPG_INDEX}
    priority = set(priority_list())
    log(f"Searching the internet for guides ({len(wanted)} channels still have no real guide)")
    cands, origin = find_candidates()
    AUTO["known"] = len(cands)
    have = {s["url"] for s in all_sources()} | set(AUTO["blocked"])
    todo = []
    for url, label in cands.items():
        ck = AUTO["checked"].get(url)
        if url in have or (ck and time.time() - ck["t"] < (7 if ck.get("fresh") else 14) * 86400):
            continue
        todo.append((url, label))
    todo = rank_candidates(todo, wanted, origin)
    log(f"  {len(cands)} guides known, {len(todo)} not checked recently")
    if not wanted:  # still collect backup guides for your priority countries
        todo = [t for t in todo if guess_country(*t) in priority]
        log(f"  every channel has a guide - checking {len(todo)} backup guide(s) for {', '.join(priority_list())}")
    tmp = os.path.join(CACHE, "candidate.xml")
    tried = 0
    for url, label in todo:
        if tried >= settings["discover_per_run"] or time.time() - started > 1200:
            break
        tried += 1
        rec = {"t": time.time(), "fresh": False, "gain": 0, "name": label}
        gain, backup = [], False
        try:
            size = http_size(url)
            if size and size > settings["discover_max_mb"] << 20:
                raise ValueError(f"bigger than {settings['discover_max_mb']} MB")
            fetch(url, tmp, settings["discover_max_mb"] << 20)
            idx, upcoming, fresh = scan_xmltv(tmp)
            ids, names = guide_lookup(idx)
            gain = [k for k, (cid, n) in wanted.items() if (cid and cid in ids) or n in names]
            backup = (not gain and guess_country(url, label) in priority
                      and sum(1 for cid, n in lineup.values() if (cid and cid in ids) or n in names) >= 5)
            rec.update(fresh=fresh, gain=len(gain), channels=len(idx),
                       why="not a TV guide" if not idx else "out of date" if not fresh
                       else "covers nothing new" if not gain else "added")
        except Exception as ex:
            rec["why"] = str(ex)[:120]
        if rec["fresh"] and (gain or backup):
            if not gain:
                rec["why"] = "added as backup"
            sid = "a" + uuid.uuid4().hex[:7]
            os.replace(tmp, os.path.join(CACHE, sid + ".xml"))
            src = {"id": sid, "type": "xmltv", "name": label, "url": url, "enabled": True,
                   "auto": True, "added": time.time(), "gain": len(gain), "fails": 0}
            n, upcoming, fresh = index_xmltv_source(src)
            src["st"] = {"ok": True, "fresh": fresh, "time": time.time(),
                         "msg": f"{n} guide channels, {upcoming} upcoming shows"}
            AUTO["sources"].append(src)
            for k in gain:
                wanted.pop(k, None)
            log(f"  + added '{label}' - " + (f"gives a guide to {len(gain)} more channel(s)" if gain
                                             else "backup guide for your priority countries"))
        else:
            log(f"  - skipped '{label}': {rec.get('why')}")
        AUTO["checked"][url] = rec
        save_auto()
    if os.path.exists(tmp):
        os.remove(tmp)
    AUTO["last_discovery"] = time.time()
    log(f"Guide search done: tried {tried}, {len(wanted)} channel(s) still without a guide")


def mark_health(src, bad, kind="dead", why=""):
    """Remember since when a source has been failing (kept in auto_sources.json so the
    GitHub copy remembers it between runs)."""
    if bad:
        rec = AUTO["bad_since"].get(src["url"])
        if not rec or rec.get("kind") != kind:
            AUTO["bad_since"][src["url"]] = {"t": time.time(), "kind": kind, "why": why[:200]}
        else:
            rec["why"] = why[:200]
    else:
        AUTO["bad_since"].pop(src["url"], None)


def remove_dead_sources():
    """Take sources out of use once they have been dead (or out of date) for too long."""
    settings = CFG["settings"]
    limits = {"dead": float(settings.get("dead_remove_hours") or 0),
              "stale": float(settings.get("stale_remove_hours") or 0)}
    for src in list(all_sources()):
        rec = AUTO["bad_since"].get(src["url"])
        if not rec or src["url"] in CFG["keep_urls"] or not limits.get(rec["kind"]):
            continue
        hours = (time.time() - rec["t"]) / 3600
        if hours >= limits[rec["kind"]]:
            what = "dead" if rec["kind"] == "dead" else "out of date"
            AUTO["removed"][src["url"]] = {"t": time.time(), "name": src["name"], "type": src["type"],
                                           "why": f"{what} for {int(hours)} hours: {rec['why']}",
                                           "retry": time.time() + 3 * 86400}
            text = f"'{src['name']}' was removed automatically - {what} for {int(hours)} hours"
            HEALTH_EVENTS.append({"t": time.time(), "id": src["id"], "name": src["name"],
                                  "state": "removed", "text": text})
            HEALTH.pop(src["id"], None)
            log(text)


def retry_removed_sources():
    """Every 3 days, removed sources get another chance: if they answer again they come back."""
    for url in list(AUTO["removed"]):
        rec = AUTO["removed"][url]
        if url in CFG["keep_urls"]:
            AUTO["removed"].pop(url)
            continue
        if time.time() < rec.get("retry", 0):
            continue
        ok, why, _ = ping(url)
        if ok:
            AUTO["removed"].pop(url)
            AUTO["bad_since"].pop(url, None)
            log(f"'{rec['name']}' answers again - put back into use")
        else:
            rec["retry"] = time.time() + 3 * 86400


def drop_dead_auto_sources():
    """Auto-found guides that fail or go stale twice in a row are removed (and re-checked later)."""
    keep = []
    for src in AUTO["sources"]:
        if src.get("fails", 0) >= 2:
            log(f"Removing auto-found guide '{src['name']}' - it stopped working")
            AUTO["checked"][src["url"]] = {"t": time.time(), "fresh": False, "gain": 0,
                                           "name": src["name"], "why": "stopped working"}
            for f in os.listdir(CACHE):
                if f.startswith(src["id"] + "."):
                    os.remove(os.path.join(CACHE, f))
        else:
            keep.append(src)
    AUTO["sources"] = keep


# ---------------------------------------------------------------- build output

DUPES = set()  # channel keys hidden because a better copy exists


def output_channels():
    active = {s["id"] for s in all_sources() if s.get("enabled", True)} | {"custom"}
    rows = []
    for ch in CFG["channels"].values():
        e = effective(ch)
        if not e["enabled"] or ch.get("missing") or ch["source"] not in active:
            continue
        e["key"], e["extra"], e["order"] = ch["key"], ch.get("extra", []), ch["order"]
        e["tvg_id"] = e["epg_id"] or "ue." + ch["key"]
        rows.append(e)

    def sort_key(e):
        try:
            return (float(e["number"]), e["order"])
        except (TypeError, ValueError):
            return (1e12, e["order"])
    rows.sort(key=sort_key)
    DUPES.clear()
    if CFG["settings"].get("hide_duplicates"):
        rank = {s["id"]: priority_rank(s) for s in CFG["sources"]}
        rank["custom"] = -1  # your own channels always win
        best = sorted(rows, key=lambda e: (rank.get(CFG["channels"][e["key"]]["source"], 99), e["order"]))
        seen_url, seen_id = set(), set()
        for e in best:
            ident = (norm(e["name"]), e["epg_id"]) if e["epg_id"] else None
            if e["url"] in seen_url or (ident and ident in seen_id):
                DUPES.add(e["key"])
            seen_url.add(e["url"])
            if ident:
                seen_id.add(ident)
        rows = [e for e in rows if e["key"] not in DUPES]
    return rows


def m3u_attr(v):
    """Playlists are not XML: keep & as-is (players match tvg-id to the guide character by character)."""
    return '"' + str(v).replace('"', "'").replace("\n", " ") + '"'


SLIM_TAGS = {"credits", "image", "rating", "star-rating", "review", "video", "audio", "previously-shown",
             "premiere", "last-chance", "subtitles", "length", "country", "keyword", "url", "language",
             "orig-language"}  # left out of the full guides to keep them small


def full_name(key):
    return "epg-full.xml.gz" if key == "full" else f"epg-{'uk' if key == 'GB' else key.lower()}.xml.gz"


def build():
    with LOCK:
        rows = output_channels()
        settings = dict(CFG["settings"])
        xml_sources = guide_sources()
    log(f"Building output for {len(rows)} channels")

    # playlist; {EPG_URL} is swapped for the real address when served
    m3u = ['#EXTM3U url-tvg="{EPG_URL}" x-tvg-url="{EPG_URL}"']
    for e in rows:
        attrs = f'tvg-id={m3u_attr(e["tvg_id"])} tvg-name={m3u_attr(e["name"])}'
        if e["number"]:
            attrs += f' tvg-chno={m3u_attr(e["number"])}'
        if e["logo"]:
            attrs += f' tvg-logo={m3u_attr(e["logo"])}'
        attrs += f' group-title={m3u_attr(e["group"] or "Other")}'
        m3u.append(f"#EXTINF:-1 {attrs},{e['name']}")
        m3u.extend(e["extra"])
        m3u.append(e["url"])
    tmp = os.path.join(OUT, "playlist.m3u.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write("\n".join(m3u) + "\n")
    os.replace(tmp, os.path.join(OUT, "playlist.m3u"))

    # guide
    now = datetime.now(timezone.utc)
    start_cut = now - timedelta(hours=6)
    end_cut = now + timedelta(days=settings["days"])
    wanted = {}
    for e in rows:
        wanted.setdefault(e["tvg_id"], e)
    real = {cid for cid in wanted if cid in EPG_INDEX}
    # full guide: every channel in your priority countries' guides, so any provider's channels match
    # full guides: every channel in your priority countries' guides, so any provider's channels match.
    # One combined file plus one per country; bulky extras TV apps don't show are left out.
    full = None
    full_end_cut = now + timedelta(days=float(settings.get("full_guide_days") or 2))
    if settings.get("full_guide"):
        n_pri = len(priority_list())
        full_src = [x for x in xml_sources if priority_rank(x) < n_pri]
        src_cc = {x["id"]: guess_country(x["url"], x["name"]) for x in full_src}
        full_owner, full_info = {}, {}
        for x in full_src:
            p = os.path.join(CACHE, x["id"] + ".channels.json")
            if os.path.exists(p):
                with open(p, encoding="utf-8") as fh:
                    for cid, info in json.load(fh).items():
                        if cid not in full_owner:
                            full_owner[cid], full_info[cid] = x["id"], info
        full = {"full": None, **{cc: None for cc in priority_list()}}
        for key in full:
            full[key] = gzip.open(os.path.join(OUT, f"{full_name(key)}.tmp"), "wt", encoding="utf-8", compresslevel=6)
            full[key].write('<?xml version="1.0" encoding="UTF-8"?>\n<tv generator-info-name="Ultimate EPG">\n')

        def full_write(cid, text):
            full["full"].write(text)
            cc = src_cc.get(full_owner.get(cid))
            if cc in full:
                full[cc].write(text)
        for cid, info in full_info.items():
            text = f"<channel id={quoteattr(cid)}>" + "".join(
                f"<display-name>{escape(n)}</display-name>" for n in info["names"] if n)
            if info.get("icon"):
                text += f"<icon src={quoteattr(info['icon'])}/>"
            full_write(cid, text + "</channel>\n")
        for cid, e in wanted.items():  # your own lineup is always in the full guide too
            if cid not in full_owner:
                full_write(cid, f"<channel id={quoteattr(cid)}><display-name>{escape(e['name'])}</display-name></channel>\n")
    full_count = 0
    tmp = os.path.join(OUT, "epg.xml.tmp")
    count = 0
    with open(tmp, "w", encoding="utf-8") as f:
        f.write('<?xml version="1.0" encoding="UTF-8"?>\n<tv generator-info-name="Ultimate EPG">\n')
        for cid, e in wanted.items():
            f.write(f"<channel id={quoteattr(cid)}><display-name>{escape(e['name'])}</display-name>")
            logo = e["logo"] or EPG_INDEX.get(cid, {}).get("icon", "")
            if logo:
                f.write(f"<icon src={quoteattr(logo)}/>")
            f.write("</channel>\n")
        claimed = set()
        for src in xml_sources:
            path = os.path.join(CACHE, src["id"] + ".xml")
            if not os.path.exists(path):
                continue
            here = set()
            try:
                for el in iter_xmltv(path, ("programme",)):
                    cid = el.get("channel", "")
                    to_main = cid in real and cid not in claimed
                    to_full = full is not None and (full_owner.get(cid) == src["id"]
                                                    or (to_main and cid not in full_owner))
                    if not (to_main or to_full):
                        continue
                    st, sp = parse_xmltv_time(el.get("start")), parse_xmltv_time(el.get("stop"))
                    if sp and sp < start_cut:
                        continue
                    to_main = to_main and not (st and st > end_cut)
                    to_full = to_full and not (st and st > full_end_cut)
                    if not (to_main or to_full):
                        continue
                    el.tail = "\n"
                    text = ET.tostring(el, encoding="unicode")
                    if to_main:
                        f.write(text)
                        here.add(cid)
                        count += 1
                    if to_full:
                        for child in list(el):
                            if child.tag in SLIM_TAGS:
                                el.remove(child)
                        full_write(cid, ET.tostring(el, encoding="unicode"))
                        full_count += 1
            except ET.ParseError as ex:
                log(f"Guide '{src['name']}' is partly broken XML ({ex}); kept what was readable")
            claimed |= here
        if settings["dummy_epg"]:
            block = timedelta(hours=max(1, int(settings["dummy_hours"])))
            hours = int(block.total_seconds() // 3600)
            t0 = now.replace(minute=0, second=0, microsecond=0) - timedelta(hours=now.hour % hours)
            for cid, e in wanted.items():
                if cid in claimed:
                    continue
                t = t0
                desc = e["desc"] or f"{e['name']} - live 24/7"
                while t < end_cut:
                    text = (f'<programme start="{fmt_xmltv_time(t)}" stop="{fmt_xmltv_time(t + block)}" '
                            f'channel={quoteattr(cid)}><title>{escape(e["name"])}</title>'
                            f'<desc>{escape(desc)}</desc></programme>\n')
                    f.write(text)
                    if full is not None and cid not in full_owner:
                        full_write(cid, text)
                    t += block
                    count += 1
        f.write("</tv>\n")
    os.replace(tmp, os.path.join(OUT, "epg.xml"))
    with open(os.path.join(OUT, "epg.xml"), "rb") as src, gzip.open(os.path.join(OUT, "epg.xml.gz.tmp"), "wb") as dst:
        shutil.copyfileobj(src, dst, 1 << 20)
    os.replace(os.path.join(OUT, "epg.xml.gz.tmp"), os.path.join(OUT, "epg.xml.gz"))
    if full is not None:
        sizes = []
        for key, fh in full.items():
            fh.write("</tv>\n")
            fh.close()
            name = full_name(key)
            os.replace(os.path.join(OUT, name + ".tmp"), os.path.join(OUT, name))
            sizes.append(f"{name} {os.path.getsize(os.path.join(OUT, name)) >> 20} MB")
        log(f"Full guides: {len(full_owner)} channels, {full_count} shows - " + ", ".join(sizes))
    STATE["last_build"] = time.time()
    log(f"Done: {len(rows)} channels, {count} guide entries ({len(claimed)} channels with real guide)")


# ---------------------------------------------------------------- refresh

def refresh(only=None):
    if not only:
        with LOCK:
            sync_priority_sources()
            save_config()
        retry_removed_sources()
    for src in list(all_sources()):
        if not src.get("enabled", True) or (only and src["id"] not in only):
            continue
        st = status_of(src)
        try:
            log(f"Downloading {src['type'].upper()} '{src['name']}'")
            dest = os.path.join(CACHE, src["id"] + (".m3u" if src["type"] == "m3u" else ".xml"))
            fetch(src["url"], dest)
            if src["type"] == "m3u":
                entries = parse_m3u(dest)
                with LOCK:
                    added = merge_m3u_source(src, entries)
                msg = f"{len(entries)} channels ({added} new)"
            else:
                n, upcoming, fresh = index_xmltv_source(src)
                msg = f"{n} guide channels, {upcoming} upcoming shows"
                if not fresh:
                    msg += " - OUT OF DATE, not used"
                st["fresh"] = fresh
            st.update(ok=True, msg=msg, time=time.time())
            log(f"  OK: {msg}")
        except Exception as ex:
            st.update(ok=False, fresh=False, msg=str(ex)[:300], time=time.time())
            log(f"  FAILED: {ex}")
        if src.get("auto"):
            src["fails"] = 0 if st.get("fresh") else src.get("fails", 0) + 1
        if not st.get("ok"):
            mark_health(src, True, "dead", st.get("msg", ""))
        elif src["type"] == "xmltv" and not st.get("fresh"):
            mark_health(src, True, "stale", "guide has no upcoming shows")
        else:
            mark_health(src, False)
        update_health(src, ping_ok=st.get("ok"), ping_msg=st.get("msg", ""))
    drop_dead_auto_sources()
    remove_dead_sources()
    with LOCK:
        load_epg_index()
        if CFG["settings"]["auto_match"]:
            n = auto_match(only_unmatched=True)
            log(f"Auto-matched {n} channel(s) without a guide")
    if not only and CFG["settings"]["auto_discover"]:
        try:
            discover()
        except Exception as ex:
            log(f"Guide search stopped early: {ex}")
        with LOCK:
            load_epg_index()
            auto_match(only_unmatched=True)
    with LOCK:
        if not only:
            CFG["last_refresh"] = time.time()
        save_config()
    save_auto()


def discover_now():
    discover()
    with LOCK:
        load_epg_index()
        auto_match(only_unmatched=True)
        save_config()
    save_auto()


JOBS = []
JOB_LOCK = threading.Lock()


def run_job(fn=None, *args):
    """Queue a job (or just a rebuild when fn is None). One worker runs them in
    order and rebuilds the output once the queue is empty."""
    with JOB_LOCK:
        if fn:
            JOBS.append((fn, args))
        STATE["dirty"] = True
        if STATE["busy"]:
            return
        STATE["busy"] = True

    def work():
        while True:
            with JOB_LOCK:
                if JOBS:
                    job = JOBS.pop(0)
                elif STATE.get("dirty"):
                    job, STATE["dirty"] = (build, ()), False
                else:
                    STATE["busy"] = False
                    return
            try:
                job[0](*job[1])
            except Exception:
                log("Error: " + traceback.format_exc().strip().splitlines()[-1])
                traceback.print_exc()
    threading.Thread(target=work, daemon=True).start()


# ---------------------------------------------------------------- source health

HEALTH = {}          # source id -> {"state", "detail", "checked", "since", "ms"}
HEALTH_EVENTS = []   # recent changes, newest last
HEALTH_NOW = threading.Event()
RECOVERY_TRIED = {}


def ping(url):
    """Does the source still answer? Returns (ok, detail, milliseconds)."""
    t0 = time.time()
    if not re.match(r"^https?://", url, re.I):
        path = url[7:] if url.lower().startswith("file://") else url
        ok = os.path.exists(os.path.expanduser(path))
        return ok, "file found" if ok else "file not found on this PC", 0
    for method, headers in (("HEAD", {}), ("GET", {"Range": "bytes=0-1023"})):
        try:
            req = urllib.request.Request(url, method=method, headers={"User-Agent": USER_AGENT, **headers})
            with urllib.request.urlopen(req, timeout=20) as r:
                if method == "GET":
                    r.read(1024)
                return True, f"answered ({r.status})", int((time.time() - t0) * 1000)
        except urllib.error.HTTPError as ex:
            if method == "HEAD" and ex.code in (403, 405, 501):
                continue  # some servers refuse HEAD - try a tiny GET instead
            return False, f"server says {ex.code} {ex.reason}", int((time.time() - t0) * 1000)
        except Exception as ex:
            reason = getattr(ex, "reason", ex)
            return False, f"not responding ({reason})", int((time.time() - t0) * 1000)
    return False, "not responding", int((time.time() - t0) * 1000)


def update_health(src, ping_ok, ping_msg, ms=None):
    """Work out the light for one source and record when it changes."""
    st = status_of(src)
    if not ping_ok:
        state, detail = "dead", ping_msg
    elif st.get("ok") is False:
        state, detail = "dead", "answers again but the last download failed - retrying"
    elif src["type"] == "xmltv" and st.get("fresh") is False:
        state, detail = "stale", "works, but the guide has no upcoming shows (out of date)"
    elif not st:
        state, detail = "checking", "not downloaded yet"
    else:
        state, detail = "healthy", st.get("msg", "working")
    now = time.time()
    old = HEALTH.get(src["id"])
    if not old or old["state"] != state:
        since = now
        if old and old["state"] != "checking":
            words = {"dead": "is DEAD", "stale": "is OUT OF DATE", "healthy": "is working again"}
            HEALTH_EVENTS.append({"t": now, "id": src["id"], "name": src["name"], "state": state,
                                  "text": f"'{src['name']}' {words.get(state, state)}: {detail}"})
            del HEALTH_EVENTS[:-50]
            log(HEALTH_EVENTS[-1]["text"])
    else:
        since = old["since"]
    HEALTH[src["id"]] = {"state": state, "detail": detail, "checked": now, "since": since,
                         "ms": ms if ms is not None else (old or {}).get("ms")}
    # a source that answers again after failing gets re-downloaded (at most every 15 minutes)
    if ping_ok and st.get("ok") is False and now - RECOVERY_TRIED.get(src["id"], 0) > 900:
        RECOVERY_TRIED[src["id"]] = now
        run_job(refresh, {src["id"]})


def check_all_sources():
    from concurrent.futures import ThreadPoolExecutor
    srcs = [s for s in all_sources() if s.get("enabled", True)]
    with ThreadPoolExecutor(8) as ex:
        results = list(ex.map(lambda s: ping(s["url"]), srcs))
    for src, (ok, msg, ms) in zip(srcs, results):
        if not ok:
            mark_health(src, True, "dead", msg)
        elif AUTO["bad_since"].get(src["url"], {}).get("kind") == "dead" and status_of(src).get("ok"):
            mark_health(src, False)
        update_health(src, ok, msg, ms)
    before = len(AUTO["removed"])
    remove_dead_sources()
    if len(AUTO["removed"]) != before:
        with LOCK:
            load_epg_index()
        run_job()  # rebuild without the removed source
    for sid in list(HEALTH):  # forget removed sources
        if not source_by_id(sid):
            del HEALTH[sid]


def health_loop():
    last = 0
    while True:
        HEALTH_NOW.wait(30)
        due = time.time() - last > float(CFG["settings"].get("health_minutes") or 10) * 60
        if HEALTH_NOW.is_set() or due:
            HEALTH_NOW.clear()
            last = time.time()
            try:
                check_all_sources()
                save_auto()
            except Exception as ex:
                log(f"Health check failed: {ex}")


def health_payload():
    counts = {}
    for h in HEALTH.values():
        counts[h["state"]] = counts.get(h["state"], 0) + 1
    return {"health": HEALTH, "health_counts": counts, "health_events": HEALTH_EVENTS[-30:]}


def scheduler():
    while True:
        time.sleep(60)
        hours = float(CFG["settings"].get("refresh_hours") or 0)
        if (hours > 0 and not STATE["busy"] and all_sources()
                and time.time() - CFG["last_refresh"] > hours * 3600):
            run_job(refresh)


# ---------------------------------------------------------------- online (GitHub)

def git(*args, check=True):
    import subprocess
    r = subprocess.run(["git", *args], cwd=BASE, capture_output=True, text=True)
    if check and r.returncode:
        raise RuntimeError((r.stderr or r.stdout).strip())
    return r.stdout.strip()


def build_site(outdir, base_url):
    """Used by the GitHub Action: download everything, build, write a static site."""
    base_url = base_url.rstrip("/")
    refresh()
    build()
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(OUT, "playlist.m3u"), encoding="utf-8") as f:
        m3u = f.read().replace("{EPG_URL}", base_url + "/epg.xml.gz")
    with open(os.path.join(outdir, "playlist.m3u"), "w", encoding="utf-8") as f:
        f.write(m3u)
    for name in ["epg.xml", "epg.xml.gz"] + sorted(f for f in os.listdir(OUT) if re.fullmatch(r"epg-[a-z]+\.xml\.gz", f)):
        if not os.path.exists(os.path.join(OUT, name)):
            continue
        if name == "epg.xml" and os.path.getsize(os.path.join(OUT, name)) > 95_000_000:
            log("Full-size guide is over 95 MB - publishing only the compressed epg.xml.gz")
            continue
        shutil.copyfile(os.path.join(OUT, name), os.path.join(outdir, name))
    links = "".join(f'<p>{label}<br><a href="{base_url}/{n}">{base_url}/{n}</a></p>' for label, n in
                    [("Playlist", "playlist.m3u"), ("Guide for this playlist", "epg.xml.gz"),
                     ("Full guide - use with any provider", "epg-full.xml.gz")] +
                    [(f"{c} guide (any provider)", full_name(c)) for c in priority_list()])
    with open(os.path.join(outdir, "index.html"), "w", encoding="utf-8") as f:
        f.write(f'<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width">'
                f'<title>My EPG</title><body style="font:16px system-ui;max-width:640px;margin:40px auto;padding:0 16px">'
                f'<h1>My EPG</h1>{links}<p style="color:#777">Updated {time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime())}</p>')
    print(f"Site written to {outdir}")


def sync_from_github():
    """Fetch guides GitHub found on its own (the online copy of auto_sources.json wins)."""
    global AUTO
    git("checkout", "--", "data/auto_sources.json", check=False)
    git("pull", "-q", "--rebase", "--autostash", "origin", "main")
    AUTO = load_auto()
    load_epg_index()


def publish():
    """Push the current sources + channel edits to GitHub; the Action rebuilds from them."""
    if not os.path.isdir(os.path.join(BASE, ".git")):
        raise RuntimeError("Not online yet - run 'Put online (GitHub).bat' first.")
    git("add", "data/config.json")
    if git("status", "--porcelain", "data/config.json"):
        git("commit", "-m", "Update channels and sources")
    sync_from_github()
    git("push", "-q", "origin", "HEAD")
    log("Published to GitHub - online links update in about 2-5 minutes")


def open_setup_window():
    """Run the one-time GitHub setup in its own window, then pick up the new settings."""
    import subprocess
    python = os.path.join(os.path.dirname(sys.executable), "python.exe")
    if not os.path.exists(python):
        python = sys.executable
    proc = subprocess.Popen([python, os.path.join(BASE, "ultimate_epg.py"), "--setup-github"], cwd=BASE,
                            creationflags=getattr(subprocess, "CREATE_NEW_CONSOLE", 0))

    def reload_when_done():
        proc.wait()
        with LOCK:
            fresh = load_config()
            CFG["settings"]["public_url"] = fresh["settings"]["public_url"]
            save_config()
        log("Online setup window closed")
    threading.Thread(target=reload_when_done, daemon=True).start()


def setup_github():
    """One-time interactive setup: create a GitHub repo, enable Pages, push."""
    import subprocess

    def gh(*args, check=True):
        r = subprocess.run(["gh", *args], cwd=BASE, capture_output=True, text=True)
        if check and r.returncode:
            raise SystemExit("GitHub CLI error: " + (r.stderr or r.stdout).strip())
        return r.stdout.strip()

    if shutil.which("gh") is None or shutil.which("git") is None:
        raise SystemExit("Please install Git (git-scm.com) and GitHub CLI (cli.github.com) first.")
    if subprocess.run(["gh", "auth", "status"], capture_output=True).returncode:
        print("Sign in to GitHub in the browser window that opens (free account is fine).")
        subprocess.run(["gh", "auth", "login", "--web", "--git-protocol", "https"], cwd=BASE)
    gh("auth", "setup-git")
    owner = gh("api", "user", "--jq", ".login")
    uid = gh("api", "user", "--jq", ".id")
    if os.path.isdir(os.path.join(BASE, ".git")) and git("remote", check=False):
        raise SystemExit("This folder is already online. Use the Publish button in the editor.")
    name = input("Name for your online EPG [my-epg]: ").strip() or "my-epg"
    print("NOTE: the repository is public (free GitHub Pages needs that). Anyone with the link can")
    print("see your playlist and source links - do NOT add paid provider links with your password in them.")
    if input("Continue? [y/N]: ").strip().lower() != "y":
        raise SystemExit("Cancelled.")
    if not os.path.isdir(os.path.join(BASE, ".git")):
        git("init", "-q", "-b", "main")
    if not git("config", "user.email", check=False):
        git("config", "user.name", owner)
        git("config", "user.email", f"{uid}+{owner}@users.noreply.github.com")
    url = f"https://{owner.lower()}.github.io/{name}"
    with LOCK:
        CFG["settings"]["public_url"] = url
        save_config()
    save_auto()
    git("add", "-A")
    git("commit", "-q", "-m", "My Ultimate EPG")
    gh("repo", "create", name, "--public", "--source", ".", "--remote", "origin")
    gh("api", "-X", "POST", f"repos/{owner}/{name}/pages", "-f", "build_type=workflow", check=False)
    git("push", "-q", "-u", "origin", "main")  # the push starts the first build
    print("\nDone! GitHub is building your EPG now (first build takes ~5 minutes).")
    print(f"  Playlist: {url}/playlist.m3u")
    print(f"  Guide:    {url}/epg.xml.gz")
    print(f"  Progress: https://github.com/{owner}/{name}/actions")


# ---------------------------------------------------------------- API

def lan_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("10.255.255.255", 1))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return "127.0.0.1"


def api_state():
    with LOCK:
        output_channels()  # refreshes which channels are duplicates
        names = {s["id"]: s["name"] for s in CFG["sources"]}
        names["custom"] = "Custom"
        chans = []
        for ch in CFG["channels"].values():
            e = effective(ch)
            e.update(key=ch["key"], source=ch["source"], source_name=names.get(ch["source"], "?"),
                     missing=bool(ch.get("missing")), order=ch["order"],
                     edited=sorted(ch.get("ov", {}).keys()), duplicate=ch["key"] in DUPES,
                     guide="real" if e["epg_id"] in EPG_INDEX else
                           ("dummy" if CFG["settings"]["dummy_epg"] else "none"))
            chans.append(e)
        chans.sort(key=lambda c: c["order"])
        return {
            "settings": CFG["settings"], "status": CFG["status"],
            "sources": [{**x, "country": guess_country(x["url"], x["name"])} for x in CFG["sources"]],
            **health_payload(),
            "removed": [{"url": u, **r} for u, r in AUTO["removed"].items() if u not in CFG["keep_urls"]],
            "auto": AUTO["sources"], "auto_info": {
                "known": AUTO["known"], "checked": len(AUTO["checked"]), "blocked": len(AUTO["blocked"]),
                "last": AUTO["last_discovery"],
                "recent": sorted(({"url": u, **c} for u, c in AUTO["checked"].items()),
                                 key=lambda c: -c["t"])[:40]},
            "channels": chans, "busy": STATE["busy"], "log": STATE["log"][-40:],
            "last_refresh": CFG["last_refresh"], "last_build": STATE["last_build"],
            "epg_count": len(EPG_INDEX), "lan": f"http://{lan_ip()}:{PORT}",
        }


def api_epg_search(q):
    nq = norm(q)
    ql = q.lower().strip()
    out = []
    for cid, info in EPG_INDEX.items():
        hay = cid.lower() + " " + " ".join(info["names"]).lower()
        if not ql or ql in hay or (nq and nq in norm(hay)):
            out.append({"id": cid, "name": info["name"], "icon": info["icon"],
                        "source": (source_by_id(info["source"]) or {}).get("name", "")})
            if len(out) >= 60:
                break
    return out


def api_save_channels(items):
    with LOCK:
        for it in items:
            ch = CFG["channels"].get(it.get("key"))
            if not ch:
                continue
            for k in FIELDS:
                if k not in it:
                    continue
                v = it[k]
                if ch["source"] == "custom":
                    ch["up"][k] = v
                elif v == ch["up"].get(k):
                    ch["ov"].pop(k, None)
                else:
                    ch["ov"][k] = v
            if it.get("reset"):
                ch["ov"] = {}
        save_config()


def api_add_channel(it):
    key = "c" + uuid.uuid4().hex[:11]
    up = {k: it.get(k, "") for k in FIELDS}
    up["enabled"] = True
    with LOCK:
        n = sum(1 for c in CFG["channels"].values() if c["source"] == "custom")
        CFG["channels"][key] = {"key": key, "source": "custom", "up": up, "ov": {},
                                "extra": [], "missing": False, "order": 900_000_000 + n}
        save_config()
    return key


def api_delete_channels(keys):
    with LOCK:
        for k in keys:
            ch = CFG["channels"].get(k)
            if ch and (ch["source"] == "custom" or ch.get("missing")):
                del CFG["channels"][k]
        save_config()


def api_save_sources(sources):
    with LOCK:
        old = {s["id"] for s in CFG["sources"]}
        clean = []
        for s in sources:
            if not s.get("url"):
                continue
            clean.append({"id": s.get("id") or uuid.uuid4().hex[:8],
                          "type": "xmltv" if s.get("type") == "xmltv" else "m3u",
                          "name": s.get("name") or "Source", "url": s["url"].strip(),
                          "enabled": bool(s.get("enabled", True))})
        removed = {s["url"] for s in CFG["sources"]} - {s["url"] for s in clean}
        CFG["dismissed"] = sorted(set(CFG["dismissed"]) | {u for u in removed if u in CATALOG_COUNTRY})
        CFG["sources"] = clean
        CFG["sources"].sort(key=priority_rank)
        keep = {s["id"] for s in clean}
        for sid in old - keep:
            CFG["status"].pop(sid, None)
            for f in os.listdir(CACHE):
                if f.startswith(sid + "."):
                    os.remove(os.path.join(CACHE, f))
        CFG["channels"] = {k: c for k, c in CFG["channels"].items()
                           if c["source"] == "custom" or c["source"] in keep}
        for c in CFG["channels"].values():  # re-sort when sources are re-ordered
            if c["source"] != "custom":
                i = next(n for n, s in enumerate(clean) if s["id"] == c["source"])
                c["order"] = (i + 1) * 1_000_000 + c["order"] % 1_000_000
        load_epg_index()
        save_config()
    return [s["id"] for s in clean if s["id"] not in old]


class Handler(BaseHTTPRequestHandler):
    protocol_version = "HTTP/1.1"

    def log_message(self, fmt, *args):
        pass

    def send(self, code, body, ctype="application/json; charset=utf-8", extra=None):
        if isinstance(body, (dict, list)):
            body = json.dumps(body, ensure_ascii=False)
        if isinstance(body, str):
            body = body.encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Cache-Control", "no-cache")
        for k, v in (extra or {}).items():
            self.send_header(k, v)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def send_file(self, path, ctype):
        if not os.path.exists(path):
            return self.send(404, "Not built yet - add sources and press Refresh.", "text/plain")
        with open(path, "rb") as f:
            self.send(200, f.read(), ctype)

    def base_url(self):
        return "http://" + (self.headers.get("Host") or f"{lan_ip()}:{PORT}")

    def do_HEAD(self):
        self.do_GET()

    def do_GET(self):
        u = urlparse(self.path)
        p = u.path.rstrip("/") or "/"
        if p == "/":
            return self.send_file(UI_PATH, "text/html; charset=utf-8")
        if p in ("/playlist.m3u", "/playlist.m3u8", "/get.php"):
            path = os.path.join(OUT, "playlist.m3u")
            if not os.path.exists(path):
                return self.send(404, "Not built yet", "text/plain")
            with open(path, encoding="utf-8") as f:
                body = f.read().replace("{EPG_URL}", self.base_url() + "/epg.xml")
            return self.send(200, body, "audio/x-mpegurl; charset=utf-8")
        if p in ("/epg.xml", "/xmltv.php"):
            return self.send_file(os.path.join(OUT, "epg.xml"), "application/xml; charset=utf-8")
        if p == "/epg.xml.gz":
            return self.send_file(os.path.join(OUT, "epg.xml.gz"), "application/gzip")
        if re.fullmatch(r"/epg-[a-z]+\.xml\.gz", p):
            return self.send_file(os.path.join(OUT, p[1:]), "application/gzip")
        if p == "/api/catalog":
            return self.send_file(os.path.join(BASE, "catalog.json"), "application/json; charset=utf-8")
        if p == "/api/state":
            if "lite" in u.query:
                return self.send(200, {"busy": STATE["busy"], "log": STATE["log"][-40:],
                                       "status": CFG["status"], "last_build": STATE["last_build"],
                                       **health_payload()})
            return self.send(200, api_state())
        if p == "/api/epg-search":
            return self.send(200, api_epg_search(parse_qs(u.query).get("q", [""])[0]))
        self.send(404, {"error": "not found"})

    def do_POST(self):
        p = urlparse(self.path).path
        n = int(self.headers.get("Content-Length") or 0)
        try:
            body = json.loads(self.rfile.read(n) or b"{}")
        except ValueError:
            return self.send(400, {"error": "bad json"})
        if p == "/api/sources":
            new = api_save_sources(body.get("sources", []))
            if new:  # download freshly added sources straight away
                run_job(refresh, set(new))
            else:
                run_job()
            return self.send(200, {"ok": True})
        if p == "/api/settings":
            with LOCK:
                for k, v in body.items():
                    if k in DEFAULT_SETTINGS:
                        CFG["settings"][k] = type(DEFAULT_SETTINGS[k])(v)
                save_config()
            run_job()
            return self.send(200, {"ok": True})
        if p == "/api/channels":
            api_save_channels(body.get("channels", []))
            run_job()
            return self.send(200, {"ok": True})
        if p == "/api/channels/add":
            key = api_add_channel(body)
            run_job()
            return self.send(200, {"ok": True, "key": key})
        if p == "/api/channels/delete":
            api_delete_channels(body.get("keys", []))
            run_job()
            return self.send(200, {"ok": True})
        if p == "/api/automatch":
            with LOCK:
                n = auto_match(body.get("only_unmatched", True))
                save_config()
            run_job()
            return self.send(200, {"ok": True, "matched": n})
        if p == "/api/refresh":
            sid = body.get("source")
            run_job(refresh, {sid} if sid else None)
            return self.send(200, {"ok": True})
        if p == "/api/build":
            run_job()
            return self.send(200, {"ok": True})
        if p == "/api/discover":
            run_job(discover_now)
            return self.send(200, {"ok": True})
        if p in ("/api/auto/keep", "/api/auto/remove"):
            with LOCK:
                src = next((x for x in AUTO["sources"] if x["id"] == body.get("id")), None)
                if src:
                    AUTO["sources"].remove(src)
                    if p.endswith("keep"):  # becomes one of your own sources
                        CFG["sources"].append({k: src[k] for k in ("id", "type", "name", "url", "enabled")})
                        CFG["status"][src["id"]] = src.get("st", {})
                    else:
                        AUTO["blocked"].append(src["url"])
                        for f in os.listdir(CACHE):
                            if f.startswith(src["id"] + "."):
                                os.remove(os.path.join(CACHE, f))
                    load_epg_index()
                    save_config()
                    save_auto()
            run_job()
            return self.send(200, {"ok": bool(src)})
        if p == "/api/restore":
            url = body.get("url", "")
            with LOCK:
                if url and url not in CFG["keep_urls"]:
                    CFG["keep_urls"].append(url)
                AUTO["removed"].pop(url, None)
                AUTO["bad_since"].pop(url, None)
                save_config()
                save_auto()
                src = next((x for x in all_sources() if x["url"] == url), None)
            run_job(refresh, {src["id"]} if src else None)
            return self.send(200, {"ok": True})
        if p == "/api/health-check":
            HEALTH_NOW.set()
            return self.send(200, {"ok": True})
        if p == "/api/quit":
            self.send(200, {"ok": True})
            threading.Timer(0.5, os._exit, [0]).start()
            return
        if p == "/api/setup-github":
            open_setup_window()
            return self.send(200, {"ok": True})
        if p == "/api/publish":
            try:
                with LOCK:
                    publish()
                return self.send(200, {"ok": True})
            except Exception as ex:
                return self.send(200, {"ok": False, "error": str(ex)})
        self.send(404, {"error": "not found"})


def main():
    if "--setup-github" in sys.argv:
        try:
            setup_github()
        except SystemExit as ex:
            if ex.code:
                print(ex.code)
        except Exception as ex:
            print("Something went wrong:", ex)
        input("\nPress Enter to close this window.")
        return
    if "--build-site" in sys.argv:
        args = sys.argv[sys.argv.index("--build-site") + 1:]
        base = os.environ.get("PUBLIC_URL") or CFG["settings"]["public_url"] or "http://localhost"
        return build_site(args[0] if args else "site", base)
    if os.path.isdir(os.path.join(BASE, ".git")):
        try:
            with LOCK:
                sync_from_github()
            print("Got the latest auto-found guides from GitHub")
        except Exception as ex:
            print(f"Could not sync with GitHub right now ({ex})")
    load_epg_index()
    threading.Thread(target=scheduler, daemon=True).start()
    threading.Thread(target=health_loop, daemon=True).start()
    HEALTH_NOW.set()  # check everything right away
    if all_sources() and not os.path.exists(os.path.join(OUT, "epg.xml")):
        run_job(refresh)
    try:
        srv = ThreadingHTTPServer(("0.0.0.0", PORT), Handler)
    except OSError:
        print(f"Port {PORT} is busy - Ultimate EPG is probably already running.")
        print(f"Open http://localhost:{PORT} in your browser.")
        if "--open" in sys.argv:
            import webbrowser
            webbrowser.open(f"http://localhost:{PORT}")
        return
    if "--open" in sys.argv:
        import webbrowser
        threading.Timer(1.0, webbrowser.open, [f"http://localhost:{PORT}"]).start()
    print("=" * 60)
    print(" Ultimate EPG is running")
    print(f"  Editor (this PC):    http://localhost:{PORT}")
    print(f"  Playlist for players: http://{lan_ip()}:{PORT}/playlist.m3u")
    print(f"  Guide for players:    http://{lan_ip()}:{PORT}/epg.xml")
    print(" Keep this window open. Press Ctrl+C to stop.")
    print("=" * 60, flush=True)
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
