#!/usr/bin/env python3
"""Ultimate EPG - merge many M3U playlists and XMLTV guides into one editable
lineup, and serve it as a single playlist + guide link for any IPTV player.

No installs needed beyond Python 3.8+. Run:  python ultimate_epg.py
Then open http://localhost:8787 in a browser.
"""
import bisect
import difflib
import gzip
import lzma
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
import unicodedata
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
    "discover_per_run": 30,    # how many new guides to try per update
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
SAVE_LOCK = threading.Lock()
STATE = {"busy": False, "log": [], "last_build": None}
EPG_INDEX = {}  # xmltv channel id -> {"name", "icon", "source"}

os.makedirs(CACHE, exist_ok=True)
os.makedirs(OUT, exist_ok=True)


# ---------------------------------------------------------------- config

SETTING_MAX = {"days": 14, "full_guide_days": 7, "dummy_hours": 24, "discover_per_run": 500}
MUST_BE_POSITIVE = {"days", "dummy_hours", "full_guide_days", "health_minutes", "discover_per_run",
                    "discover_max_mb"}


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
    cfg.setdefault("provider_channels", [])  # your provider's channel names/codes + matched guide (no links)
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
    except OSError:
        a = {}
    except ValueError:  # never overwrite a damaged file with an empty one
        shutil.copyfile(AUTO_PATH, AUTO_PATH + ".broken")
        a = {}
    for k, v in {"sources": [], "checked": {}, "blocked": [], "last_discovery": 0,
                 "known": 0, "cache": {}, "bad_since": {}, "removed": {}}.items():
        a.setdefault(k, v)
    return a


def write_atomic(path, text):
    """A crash or a second thread can never leave a half-written file."""
    tmp = f"{path}.{threading.get_ident()}.tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
    os.replace(tmp, path)


def save_auto():
    with SAVE_LOCK:
        for attempt in range(5):
            try:
                text = json.dumps(AUTO, ensure_ascii=False, indent=1)
                break
            except RuntimeError:  # another thread was changing it mid-way
                time.sleep(0.05)
        else:
            return
        write_atomic(AUTO_PATH, text)


AUTO = load_auto()
PRIVATE_PATH = os.path.join(DATA, "private.json")  # your provider link (has your password) - stays on this PC


def load_private():
    try:
        with open(PRIVATE_PATH, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {"providers": []}


def save_private():
    write_atomic(PRIVATE_PATH, json.dumps(PRIVATE, indent=1))


PRIVATE = load_private()


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
    try:
        if re.match(r"^https?://", url, re.I):
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=180) as r, open(tmp, "wb") as f:
                got = 0
                while chunk := r.read(1 << 20):
                    got += len(chunk)
                    if max_bytes and got > max_bytes:
                        raise ValueError(f"bigger than {max_bytes >> 20} MB")
                    f.write(chunk)
                size = r.headers.get("Content-Length")
                if size and size.isdigit() and not r.headers.get("Content-Encoding") and got < int(size):
                    raise ValueError(f"download was cut off ({got} of {size} bytes)")
        else:
            path = url[7:] if url.lower().startswith("file://") else url
            shutil.copyfile(os.path.expanduser(path), tmp)
        with open(tmp, "rb") as f:
            magic = f.read(6)
        gz, xz = magic[:2] == b"\x1f\x8b", magic == b"\xfd7zXZ\x00"
        if gz or xz:
            with (gzip.open if gz else lzma.open)(tmp, "rb") as src, open(dest + ".unz", "wb") as dst:
                shutil.copyfileobj(src, dst, 1 << 20)
            os.replace(dest + ".unz", dest)
        else:
            os.replace(tmp, dest)
    finally:  # also removes anything that could hold a provider login
        for leftover in (tmp, dest + ".unz"):
            if os.path.exists(leftover):
                os.remove(leftover)


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
            line = clean_text(line)
            m = re.match(r'((?:[^,"]|"[^"]*")*),(.*)$', line)
            head, title = (m[1], m[2]) if m else (line, "")
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

BAD_XML_BYTES = re.compile(rb"[\x00-\x08\x0b\x0c\x0e-\x1f]|\xef\xbf[\xbe\xbf]|"
                           rb"&#(?:0*(?:[0-8]|1[124-9]|2\d|3[01])|[xX]0*(?:[0-8bcefBCEF]|1[0-9a-fA-F]));")
BARE_AMP = re.compile(rb"&(?!(?:amp|lt|gt|quot|apos|#\d+|#[xX][0-9a-fA-F]+);)")
CTRL_RE = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\ufffe\uffff]")


class CleanReader:
    """Reads a file with the control characters that break XML parsers taken out."""

    def __init__(self, path):
        self.f = open(path, "rb")
        self.carry = b""
        self.utf16 = self.f.read(2) in (b"\xff\xfe", b"\xfe\xff")
        self.f.seek(0)

    def read(self, n=-1):
        if self.utf16:
            return self.f.read(n)
        while True:  # an empty answer would mean "end of file" to the parser
            raw = self.f.read(n)
            data = self.carry + raw
            self.carry = b""
            if raw:  # a "&...;" or a bad character may be cut in two between reads
                cut = max(data.rfind(b"&", max(0, len(data) - 16)), data.rfind(b"\xef", max(0, len(data) - 3)))
                if cut >= 0:
                    data, self.carry = data[:cut], data[cut:]
            data = BARE_AMP.sub(b"&amp;", BAD_XML_BYTES.sub(b"", data))
            if data or not raw:
                return data

    def close(self):
        self.f.close()


def clean_text(t):
    return CTRL_RE.sub("", t or "")


def iter_xmltv(path, tags):
    """Stream top-level <channel>/<programme> elements without loading the file."""
    reader = CleanReader(path)
    try:
        yield from _iter_xmltv(reader, tags)
    finally:
        reader.close()


def _iter_xmltv(path, tags):
    ctx = ET.iterparse(path, events=("start", "end"))
    _, root = next(ctx)
    for ev, el in ctx:
        if ev == "end" and el.tag in ("channel", "programme"):
            if el.tag in tags:
                yield el
            root.clear()


JUNK_TITLE_RE = re.compile(r"no longer available|no (programme |program )?information|information not available|"
                           r"^(off ?air|no data|not available|closedown)$", re.I)


def is_junk(el):
    return bool(JUNK_TITLE_RE.search((el.findtext("title") or "").strip()))


class ShowCleaner:
    """Keeps each channel's shows clean for every player: no duplicates, no overlaps, no empty or 0-minute shows.
    Works even when a guide lists shows out of order (the night the clocks change)."""

    def __init__(self):
        self.kept = {}  # channel -> sorted [(start, stop)] in seconds
        self.dropped = 0

    def check(self, cid, el, st, sp):
        """Returns the (start, stop) to write, or None to skip the show."""
        if not st or (sp and sp <= st) or not (el.findtext("title") or "").strip():
            self.dropped += 1
            return None
        a, b = int(st.timestamp()), int((sp or st).timestamp())
        kept = self.kept.setdefault(cid, [])
        i = bisect.bisect_left(kept, (a, a))
        if i < len(kept) and kept[i][0] == a:
            self.dropped += 1  # same start = same show again
            return None
        if i and kept[i - 1][1] > a:  # starts while the previous show is still on
            a = kept[i - 1][1]
        if i < len(kept) and sp and kept[i][0] < b:  # runs into the next show
            b = kept[i][0]
        if sp and b <= a or not sp and i and kept[i - 1][1] > int(st.timestamp()):
            self.dropped += 1
            return None
        kept.insert(i, (a, b if sp else a))
        tz = timezone.utc
        return datetime.fromtimestamp(a, tz), (datetime.fromtimestamp(b, tz) if sp else None)


def scan_xmltv(path):
    """Read a guide's channel list and check it actually has upcoming shows."""
    idx, upcoming, last, per, langs = {}, 0, None, {}, {}
    now = datetime.now(timezone.utc)
    try:
        for el in iter_xmltv(path, ("channel", "programme")):
            if el.tag == "channel":
                names = [d.text or "" for d in el.findall("display-name")]
                icon = el.find("icon")
                idx[el.get("id", "")] = {"names": names, "icon": icon.get("src", "") if icon is not None else ""}
            else:
                end = parse_xmltv_time(el.get("stop") or el.get("start"))
                if end and end > now and not is_junk(el):
                    upcoming += 1
                    last = max(last, end) if last else end
                    cid = el.get("channel", "")
                    per[cid] = per.get(cid, 0) + 1
                    idx.setdefault(cid, {"names": [], "icon": ""})  # some guides (Rytec) have no channel list
                    t = el.find("title")
                    lang = (t.get("lang") or "").lower()[:2] if t is not None else ""
                    if lang:
                        langs.setdefault(cid, {}).setdefault(lang, 0)
                        langs[cid][lang] += 1
    except Exception as ex:  # keep whatever was readable before the broken part
        log(f"  guide is partly broken ({ex}) - kept what was readable")
    for cid, info in idx.items():
        info["n"] = per.get(cid, 0)
        if cid in langs:
            info["lang"] = max(langs[cid], key=langs[cid].get)  # upcoming shows - channels listed with no shows are skipped when matching
    fresh = bool(upcoming) and last is not None and last > now + timedelta(hours=2)
    return idx, upcoming, fresh


def index_xmltv_source(src):
    idx, upcoming, fresh = scan_xmltv(os.path.join(CACHE, src["id"] + ".xml"))
    write_atomic(os.path.join(CACHE, src["id"] + ".channels.json"), json.dumps(idx, ensure_ascii=False))
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
        try:
            with open(p, encoding="utf-8") as f:
                data = json.load(f)
        except ValueError:
            log(f"Index of '{src['name']}' was damaged - it is rebuilt on the next update")
            os.remove(p)
            continue
        for cid, info in data.items():
            if cid not in new and info.get("n", 1):
                new[cid] = {"name": (info["names"] or [cid])[0], "names": info["names"],
                            "icon": info["icon"], "source": src["id"]}
    EPG_INDEX = new


TIME_RE = re.compile(r"(\d{12}(?:\d\d)?)(?!\d)\s*([+-]\d\d:?\d\d|[A-Za-z]{3,4})?")
ZONES = {"UTC": "+0000", "GMT": "+0000", "EST": "-0500", "EDT": "-0400", "CST": "-0600", "CDT": "-0500", "MST": "-0700",
         "MDT": "-0600", "PST": "-0800", "PDT": "-0700", "BST": "+0100", "CET": "+0100", "CEST": "+0200"}


def parse_xmltv_time(s):
    m = TIME_RE.match(s or "")
    if not m:
        return None
    off = m[2] or "+0000"
    off = ZONES.get(off.upper(), "") if off[0].isalpha() else off.replace(":", "")
    if not off:
        return None  # a time zone we can't place would put the show at the wrong hour
    try:  # a broken time ("hour 24", "Feb 30", year 0001) must never stop the whole guide
        dt = datetime.strptime(m[1].ljust(14, "0"), "%Y%m%d%H%M%S")
        delta = timedelta(hours=int(off[1:3]), minutes=int(off[3:5]))
        return dt.replace(tzinfo=timezone.utc) - (delta if off[0] == "+" else -delta)
    except (ValueError, OverflowError):
        return None


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
            if norm(n):
                lookup.setdefault(norm(n), cid)
    matched = 0
    for ch in CFG["channels"].values():
        e = effective(ch)
        if only_unmatched and e["epg_id"] in EPG_INDEX:
            continue
        cid = lookup.get(norm(e["name"])) if norm(e["name"]) else None
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
    for c in CFG.get("provider_channels") or []:  # "AMC RO", "Canal 5 MX" -> look for RO / MX guides
        if not c.get("guide") and c.get("how") != "event":
            cc = entry_country(c["name"], c.get("group", ""), c.get("id", ""))
            if cc and cc not in ("us", "uk", "ca"):
                counts[cc] = counts.get(cc, 0) + 1
    weights = {}  # your priority countries first, then your most common channel countries
    for i, cc in enumerate(priority_list()):
        for w in COUNTRY_TOKENS.get(cc, cc.lower()).split():
            weights.setdefault(w, 10 - 2 * i)
    for i, cc in enumerate(sorted(counts, key=counts.get, reverse=True)[:8]):
        for w in [cc] + COUNTRY_WORDS.get(cc, "").split():
            weights.setdefault(w, max(1, 6 - i))

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
        for n in info["names"] + [cid.split(".")[0]]:
            names.add(norm(n))
            names.add(pkey(n))
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
        for c in CFG.get("provider_channels") or []:  # your providers' channels without a guide too
            if not c.get("guide") and c.get("how") != "event":
                wanted["p:" + c["key"]] = (c["id"], pkey(c["name"]))
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
            AUTO["bad_since"][src["url"]] = {"t": time.time(), "kind": kind, "why": why[:200], "count": 1}
        else:
            rec["why"] = why[:200]
            rec["count"] = rec.get("count", 1) + 1
    else:
        AUTO["bad_since"].pop(src["url"], None)


def outage_hosts():
    """Websites where most guides fail together: that is an outage (or a block), not dead guides."""
    per = {}
    for x in all_sources():
        if x.get("enabled", True):
            host = urllib.parse.urlparse(x["url"]).hostname or ""
            rec = per.setdefault(host, [0, 0])
            rec[0] += 1
            rec[1] += AUTO["bad_since"].get(x["url"], {}).get("kind") == "dead"
    return {h for h, (n, bad) in per.items() if n >= 3 and bad >= n * 0.7}


def on_outage(src, hosts):
    return (urllib.parse.urlparse(src["url"]).hostname or "") in hosts


def mass_failure():
    """True when half or more of the sources look dead together (Wi-Fi down, PC just woke up...)."""
    srcs = [x for x in all_sources() if x.get("enabled", True)]
    dead = sum(1 for x in srcs if AUTO["bad_since"].get(x["url"], {}).get("kind") == "dead")
    return len(srcs) >= 4 and dead >= len(srcs) / 2


def remove_dead_sources():
    """Take sources out of use once they have been dead (or out of date) for too long."""
    settings = CFG["settings"]
    limits = {"dead": float(settings.get("dead_remove_hours") or 0),
              "stale": float(settings.get("stale_remove_hours") or 0)}
    if mass_failure():
        log("Most sources are failing at once - that is a network problem here, not dead sources; removing nothing")
        return
    hosts = outage_hosts()
    for src in list(all_sources()):
        rec = AUTO["bad_since"].get(src["url"])
        if not rec or src["url"] in CFG["keep_urls"] or not limits.get(rec["kind"]) or on_outage(src, hosts):
            continue
        hours = (time.time() - rec["t"]) / 3600
        if hours >= limits[rec["kind"]] and rec.get("count", 1) >= 3:
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
    """Auto-found guides that stay broken for 2 days are removed; the finder tries them again 3 days later."""
    keep = []
    if mass_failure():
        return
    hosts = outage_hosts()
    for src in AUTO["sources"]:
        bad = AUTO["bad_since"].get(src["url"])
        days = (time.time() - bad["t"]) / 86400 if bad else 0
        if src.get("fails", 0) >= 4 and days >= 2 and src["url"] not in CFG["keep_urls"] and not on_outage(src, hosts):
            log(f"Removing auto-found guide '{src['name']}' - it stopped working")
            AUTO["bad_since"].pop(src["url"], None)
            AUTO["checked"][src["url"]] = {"t": time.time() - 11 * 86400, "fresh": False, "gain": 0,
                                           "name": src["name"], "why": "stopped working"}
            for f in os.listdir(CACHE):
                if f.startswith(src["id"] + "."):
                    os.remove(os.path.join(CACHE, f))
        else:
            keep.append(src)
    AUTO["sources"] = keep


# ---------------------------------------------------------------- build output

PROVIDER_PREFIX_RE = re.compile(r"^\s*[\[(|]?\s*(us|usa|uk|gb|ca|can|cdn)\s*[\])|:\-]+\s*", re.I)
FEED_RE = re.compile(r"\b(east|west|pacific|feed|backup|alt|hd|fhd|uhd|sd|4k|raw|vip|ultra|hevc|eu)\b|(?<=\d)hd\+?(?=\s|$)|\bhd\+")
NOT_COUNTRY = {"hd", "sd", "tv", "fm", "am", "tc"}


def id_country(cid):
    """'HGTV.co' -> 'co', 'ESPN.HD.us2' -> 'us', 'CNN' -> ''."""
    m = re.search(r"\.([a-z]{2})\d?(?:@|$)", cid.lower())
    if not m or m[1] in NOT_COUNTRY:
        return ""
    return CC_ALIAS.get(m[1], m[1])


CC_ALIAS = {"usa": "us", "united states": "us", "gb": "uk", "united kingdom": "uk", "can": "ca", "cdn": "ca",
            "canada": "ca"}


ANY_PREFIX_RE = re.compile(r"^\s*[\[(|]?\s*((?:ca|us)\s+(?:en|fr)|[a-z]{2,3})\s*[\])|:\-]+\s*")
EXTRA_PREFIX = {"usa", "can", "cdn", "ban", "uga", "arg", "bih", "gre", "tur", "ger", "ita", "esp"}
BH_ALIAS = {"bh": "ba", "bih": "ba", "ban": "bd", "uga": "ug", "arg": "ar", "gre": "gr", "tur": "tr", "ger": "de",
            "ita": "it", "esp": "es"}


def plain(text):
    """'T\u00e9l\u00e9 Qu\u00e9bec' -> 'Tele Quebec', tiny 'RAW' letters -> 'RAW', no decoration symbols."""
    text = unicodedata.normalize("NFKD", unescape_all(text or ""))
    return "".join(ch for ch in text if not unicodedata.combining(ch) and ch not in "\u25c9\u2605\u2022")


def name_prefix(name):
    """The country a guide writes in front of a name: 'DK - TV 2', '[CA] Citytv', 'CA EN: CTV', 'BH: Nova'."""
    m = ANY_PREFIX_RE.match(name.lower())
    if not m:
        return "", name
    word = m[1].split()[0]
    if word == "ar":  # Arabic or Argentina: strip it, but it says nothing about the country
        return "", name[m.end():]
    known = word in EXTRA_PREFIX or (word.upper() in ISO2 and word not in NOT_COUNTRY) or word in ("uk", "bh")
    return (BH_ALIAS.get(word, CC_ALIAS.get(word, word)), name[m.end():]) if known else ("", name)


def clean_name(name):
    return name_prefix(plain(name).lower())[1]


TRAILING_CC_RE = re.compile(r"[\s\-|:(]*\b(us|usa|uk|gb|ca|can|cdn)\b\)?\.?\s*$", re.I)
GENERIC_RE = re.compile(r"\b(the|network|networks|channel|tv|television|hd|east|eastern|and)\b")
# channels that changed their name - providers often still use the old one
RENAMES = {"EPIX": "MGM+", "EPIX 2": "MGM+ Hits", "EPIX Hits": "MGM+ Hits", "EPIX Drive-In": "MGM+ Drive-In",
           "EPIX DriveIn": "MGM+ Drive-In", "EPIX Marquee": "MGM+ Marquee", "Decades": "Catchy Comedy",
           "Court TV Mystery": "ION Mystery", "Escape": "ION Mystery", "NBC Sports Network": "NBCSN",
           "Fox Sports 1": "FS1", "Fox Sports 2": "FS2", "Universal Kids": "Universal Kids",
           "AT&T SportsNet Pittsburgh": "SportsNet Pittsburgh", "AT&T SportsNet Rocky Mountain": "Altitude",
           "Bally Sports": "FanDuel Sports", "HLN TV": "HLN", "Starz Kids Family": "Starz Kids & Family",
           "Hallmark Movies Mysteries": "Hallmark Movies & Mysteries", "Hallmark Drama": "Hallmark Family",
           "DIY Network": "Magnolia Network", "Esquire": "Esquire Network", "Discovery Life": "Discovery Life Channel",
           "Las Estrella": "Las Estrellas", "Travel + Escape": "Travel Escapes",
           "Global Montreal Quebec": "Global News Montreal", "CTV News Winnipeg": "CTV Winnipeg",
           "Sudbury CTV News": "CTV Sudbury", "CITY Vancouver BC": "City TV Vancouver", "CityCT Montreal": "Citytv Montreal",
           "TVI 24": "CNN Portugal", "BBC London": "BBC One London", "BBC One Scot": "BBC One Scotland",
           "Investigacao Discovery": "Investigacao Discovery", "Black News": "Black News Channel",
           "Science": "Science Channel", "Sundance": "SundanceTV", "Ovation": "Ovation TV", "Nat Geo": "National Geographic",
           "Bay News 9": "Spectrum Bay News 9 Tampa", "Global National": "Global News National",
           "Comedy Network": "CTV Comedy Channel", "Teletoon": "Cartoon Network", "Tele Toon": "Cartoon Network",
           "Family CHRGD": "WildBrainTV", "H2": "Sky History 2", "Space": "CTV Sci-Fi", "Bravo CA": "CTV Drama",
           "Discovery Velocity": "Discovery Velocity", "Much": "CTV Much", "MuchMusic": "CTV Much",
           "Fox Sports 1": "FS1", "NBC Universo": "Universo", "Univision Deportes": "TUDN", "TUDN USA": "TUDN",
           "Fox College Sports": "Fox College Sports", "Pac 12": "Pac-12 Network", "Turner Classic Movies": "TCM",
           "WE TV": "WE tv", "TV Land": "TV Land", "Freeform": "Freeform", "ABC Family": "Freeform"}


NUM_WORDS = {"one": "1", "two": "2", "three": "3", "four": "4", "five": "5", "six": "6", "seven": "7",
             "eight": "8", "nine": "9", "ten": "10"}
NUM_RE = re.compile(r"\b(" + "|".join(NUM_WORDS) + r")\b")


def numbers(n):
    return NUM_RE.sub(lambda m: NUM_WORDS[m[1]], n)


def pkey_words(name):
    """Same words in any order: "Bloomberg BNN CA" = "BNN Bloomberg", "Spectrum News - NY1 - STVA" = "Spectrum News NY1"."""
    n = clean_name(name)
    n = TRAILING_CC_RE.sub("", n)
    n = re.sub(r"\b(us|uk|ca|stva|us2|ca2)\b", " ", numbers(n.replace("&", " ")))
    n = GENERIC_RE.sub(" ", FEED_RE.sub(" ", n))
    words = sorted(set(re.findall(r"[a-z0-9+]+", n)))
    return " ".join(words) if len(words) >= 2 else ""


def pkey(name):
    """Name used to compare a provider channel with a guide channel ("US| ESPN HD", "ESPN (East) US" -> "espn")."""
    n = clean_name(name)
    n = TRAILING_CC_RE.sub("", n)
    n = re.sub(r"\(x\d+\)", " ", n)
    n = re.sub(r"\b(us|uk|ca)\b", " ", n)  # "Showtime Next US (East) US"
    n = re.sub(r"(?<=\S)\s+usa\b", " ", n)  # "MTV USA" - but not "USA Network"
    return norm(FEED_RE.sub(" ", numbers(n)))


def pkey_loose(name):
    """Looser name: also ignores words like Network/Channel/TV ("COZI Network" = "Cozi TV")."""
    n = clean_name(name)
    n = TRAILING_CC_RE.sub("", n)
    n = re.sub(r"\(x\d+\)", " ", n)
    n = re.sub(r"\b(us|uk|ca)\b", " ", n)
    n = re.sub(r"(?<=\S)\s+usa\b", " ", n)  # "MTV USA" - but not "USA Network"
    n = numbers(n.replace("&", " "))
    n = GENERIC_RE.sub(" ", FEED_RE.sub(" ", n))
    return re.sub(r"[^a-z0-9+]", "", n)


RENAME_LOOKUP = None


def renamed_name(name):
    global RENAME_LOOKUP
    if RENAME_LOOKUP is None:
        RENAME_LOOKUP = {pkey_loose(k): v for k, v in RENAMES.items()}
    return RENAME_LOOKUP.get(pkey_loose(name))


EVENT_RE = re.compile(r"\bevents?\b|\bppv\b|pay.?per.?view", re.I)


def is_event_channel(c):
    """Temporary game/PPV slots - no guide exists anywhere for these."""
    return bool(EVENT_RE.search(c.get("group", "")) or re.match(r"^\s*(event|ppv)\s*\d", c.get("name", ""), re.I))


ISO2_SET = None


def entry_country(name, group, tid):
    global ISO2_SET
    if ISO2_SET is None:
        ISO2_SET = {c.lower() for c in ISO2} | {"uk"}
    own = id_country(tid or "")
    if own in ("us", "uk", "ca"):  # "abc.wsb.atlanta.ga.us" is US - "GA" is Georgia, not Gabon
        return own
    lead = re.match(r"^\s*[\[(|]?\s*(usa|us|uk|gb|canada|can|cdn|ca)\s*[\])|:\-]", (name or "").lower())
    if lead:  # "US: FOX SPORTS AZ" - the prefix wins over the state letters at the end
        return CC_ALIAS.get(lead[1], lead[1])
    g = re.search(r"\b(usa|united states|united kingdom|uk|canada|us|ca)\b", (group or "").lower())
    if g:  # "NBC Sports CA" in a US group is California
        return CC_ALIAS.get(g[1], g[1])
    t = re.search(r"\s([A-Z]{2})\s*\)?\s*$", name or "")  # trailing upper-case country code: "AMC RO"
    if t and t[1].lower() in ISO2_SET and t[1].lower() not in NOT_COUNTRY and (t[1] != "AR" or own == "ar"):
        return CC_ALIAS.get(t[1].lower(), t[1].lower())  # "AR" alone may mean Arabic, the code decides
    m = re.search(r"\.(us|uk|gb|ca)\d?(?:@|$)", (tid or "").lower())
    if not m:
        m = (re.match(r"^\s*[\[(|]?\s*(usa|us|uk|gb|canada|can|cdn|ca)\b", (name or "").lower())
             or re.search(r"\b(usa|us|uk|gb|ca|can)\s*\)?\s*$", (name or "").lower())
             or re.search(r"\b(usa|united states|united kingdom|uk|canada|us|ca)\b", (group or "").lower()))
    return CC_ALIAS.get(m[1], m[1]) if m else ""


def raw_key(name):
    """Names in any alphabet, letters kept: 'Карусель HD' and 'Карусель'."""
    n = PROVIDER_PREFIX_RE.sub("", unescape_all(name or "").lower())
    n = re.sub(r"\b(hd|fhd|uhd|sd|4k|ua|ru|by|kz|tv|\u0442\u0432)\b", " ", n)
    return re.sub(r"[\W_]+", "", n)


def code_key(cid):
    """'history.en.espanol.us' = 'HistoryenEspanol.us@SD'."""
    return re.sub(r"[^a-z0-9]", "", plain(cid).lower().split("@")[0])


def provider_index():
    """All channels of all working guides, best sources first."""
    owner, names, src_cc, langs = {}, {}, {}, {}
    for x in guide_sources():
        src_cc[x["id"]] = CC_ALIAS.get(guess_country(x["url"], x["name"]).lower(),
                                       guess_country(x["url"], x["name"]).lower())
        path = os.path.join(CACHE, x["id"] + ".channels.json")
        if os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                for cid, info in json.load(fh).items():
                    if cid not in owner and info.get("n", 1):
                        owner[cid], names[cid] = x["id"], info["names"]
                        langs[cid] = info.get("lang", "")
    by_id = {cid.lower(): cid for cid in owner}
    by_code = {}
    for cid in owner:
        by_code.setdefault(code_key(cid), cid)
    by_name, by_loose, by_call, by_words, by_raw = {}, {}, {}, {}, {}
    for cid, ns in names.items():
        for n in ns or [cid.split(".")[0]]:
            k = raw_key(n)
            if len(k) >= 3 and not mostly_latin([n]) and cid not in by_raw.setdefault(k, []):
                by_raw[k].append(cid)
            k = pkey(n)
            if k and cid not in by_name.setdefault(k, []):
                by_name[k].append(cid)
            k = pkey_loose(n)
            if len(k) >= 2 and cid not in by_loose.setdefault(k, []):
                by_loose[k].append(cid)
            k = pkey_words(n)
            if k and cid not in by_words.setdefault(k, []):
                by_words[k].append(cid)
        for call in callsigns(" ".join(ns) + " " + cid.replace(".", " ")):
            if cid not in by_call.setdefault(call, []):
                by_call[call].append(cid)

    def cc_of(cid):
        first = plain((names.get(cid) or [""])[0])
        cc = id_country(cid) or name_prefix(first)[0] or src_cc.get(owner[cid], "")
        return "" if cc in ("all", "int", "xx") else cc
    loose_by_len = {}
    for k in by_loose:
        loose_by_len.setdefault(len(k), []).append(k)
    return {"loose_by_len": loose_by_len, "by_id": by_id, "by_name": by_name, "by_loose": by_loose, "by_call": by_call, "by_words": by_words, "by_code": by_code, "by_raw": by_raw, "cc": cc_of,
            "names": names, "langs": langs}


CALL_RE = re.compile(r"(?<![A-Za-z])([KW][A-Z]{3}|C[BFHIJK][A-Z]{2})(?![A-Za-z])")
NOT_CALLS = {"CITY", "CINE", "CLUB", "CHAT", "KICK", "WEST", "WILD", "WORD", "KIDS", "WETV", "WOOD", "WORK", "KING", "KISS", "WINE", "WALL", "WIDE"}


BOXED_CALL_RE = re.compile(r"\(((?:[KW][A-Z]{2,3})|C[A-Z]{3})[)/\-]")
CALL3_RE = re.compile(r"(?<![A-Za-z])(?i:abc|cbs|nbc|fox|cw|pbs|mnt|ion)\s*[(\-]?\s*([KW][A-Z]{2})(?![A-Za-z])")


def callsigns(text):
    """Local TV call letters in a name, e.g. 'ABC 7 New York (WABC)' -> {'WABC'}, 'CBS (WBZ) Boston' -> {'WBZ'}."""
    found = {c for c in CALL_RE.findall(text or "") if c not in NOT_CALLS}
    boxed = {c for c in BOXED_CALL_RE.findall(text or "") if c not in ("WEST", "CITY", "CINE", "KIDS")}
    return found | boxed | set(CALL3_RE.findall(text or ""))


NET_RE = re.compile(r"\b(abc|cbs|nbc|fox|pbs|cw|mnt|myn|ion|telemundo|univision|unimas|cbc|ctv|global|citytv)\b")
LOOSE_STOP = {"music", "happy", "movies", "movie", "sports", "sport", "news", "kids", "comedy", "drama", "action",
              "classic", "classics", "family", "life", "style", "food", "church", "faith", "local", "world"}


INTL_RE = re.compile(r"\b(cnn|bbc|nhk|france 24|dw|euronews|al jazeera|bloomberg|cnbc|sky news|fashion|mtv|trace|"
                     r"rt|cgtn|tv5|arirang|ewtn|red bull)\b", re.I)


WORLD_RE = re.compile(r"\b(cnn international|bbc world|bbc news|euronews|france 24|kbs world|nhk world|tv5 ?monde|"
                      r"dw\b|al jazeera|cgtn|arirang)", re.I)
NATIONAL_RE = re.compile(r"boomerang|viasat|paramount|discovery|nat ?geo|national geographic|cnn|hbo|fox|espn|mtv|nick|disney|cartoon|comedy|history|"
                         r"animal|tlc|sky|star|amc|universal|paramount|syfy|cinemax|showtime|bbc|cbs|nbc|abc|tnt|tbs|"
                         r"eurosport|bein|dazn|canal|rtl|sport|kids|movie|film|cinema|news|music", re.I)
NAME_TAG_RE = re.compile(r"\s+(?:[A-Z]{2,3}|HAM|LOCAL|FHD|HD)\s*\)?$")
HOST_CC = {"be", "cy", "ch", "at", "cz", "lu", "sv", "al", "hk"}  # sites here re-share other countries' channels
NAME_STOP = {"curacao", "teletoon"}
BALKANS = {"hr", "rs", "ba", "mk", "si", "me", "al", "xk"}


def shorter_names(name):
    """'Kanal 5 SE' -> 'Kanal 5'; 'TRT 1 HD HAM' -> 'TRT 1 HD', 'TRT 1'; 'Nova BH BIH US' -> 'Nova BH BIH', 'Nova BH'."""
    out = []
    while NAME_TAG_RE.search(name) and len(out) < 2:
        name = NAME_TAG_RE.sub("", name)
        out.append(name)
    return out


def similar_spelling(key, idx):
    """One slip in a long name: 'Africa Magic Lgbo' = 'Igbo', 'Globo Internatioanal' = 'International'."""
    if len(key) < 10:
        return []
    near = difflib.get_close_matches(key, idx["loose_by_len"].get(len(key), []) + idx["loose_by_len"].get(len(key) - 1, [])
                                     + idx["loose_by_len"].get(len(key) + 1, []), 3, 0.93)
    return [k for k in near if re.findall(r"\d+", k) == re.findall(r"\d+", key)]


def mostly_latin(names):
    text = "".join(names)
    letters = [ch for ch in text if ch.isalpha()]
    return not letters or sum(ch.isascii() for ch in letters) / len(letters) > 0.7


def pick_best(cands, c, idx):
    """Several guide channels share the name: prefer same country and the same time-zone feed."""
    want_cc = entry_country(c["name"], c.get("group", ""), c.get("id", "")) or id_country(c.get("id") or "")
    pname = PROVIDER_PREFIX_RE.sub("", unescape_all(c["name"]).lower())
    want_west = wants_west(c)
    exact = norm(re.sub(r"\b(hd|fhd|uhd|sd|4k)\b", " ", pname))

    want_net = set(NET_RE.findall(pname))
    want_sub = bool(re.search(r"dt\d|\.\d\b", pname))

    def score(cid):
        text = (" ".join(idx["names"].get(cid, [])) + " " + cid).lower()
        west = bool(re.search(r"\bpacific\b|\bwest\b|\(p\)", text))
        sc = 0
        nets = set(NET_RE.findall(text))
        if want_net and nets:
            sc += 3 if want_net & nets else -3  # same network as the provider says
        if re.search(r"dt\d", text) and not want_sub:
            sc -= 2  # prefer the main channel over a sub-channel
        if want_cc and idx["cc"](cid) == want_cc:
            sc += 4
        if west != want_west:
            sc -= 5  # never put the West Coast feed on an East Coast channel (3 hours off)
        if (want_cc or idx["cc"](cid)) in ("us", "uk", "ca") and idx["langs"].get(cid, "") not in ("", "en"):
            sc -= 4  # an English channel should get English listings
        if any(norm(re.sub(r"\b(hd|fhd|uhd|sd|4k)\b", " ", n.lower())) == exact for n in idx["names"].get(cid, [])):
            sc += 2
        return -sc
    return sorted(cands, key=score)[0]


def wants_west(c):
    """A West Coast feed: "MTV West", "HBO (Pacific)", "hbo.pacific.us" - not "West Palm Beach" or "BBC One West"."""
    if entry_country(c.get("name", ""), c.get("group", ""), c.get("id", "")) not in ("us", "ca", ""):
        return False
    name, tid = c.get("name", "").lower(), (c.get("id") or "").lower()
    return bool(re.search(r"\((?:west|pacific)\)|\b(?:west|pacific)(?:\s+(?:us|usa|ca))?\s*$", name)
                or re.search(r"\.(?:west|pacific)(?:\.(?:us|ca)\d?)?(?:@|$)", tid))


def is_west_feed(cid, idx):
    return bool(re.search(r"\bpacific\b|\bwest\b|\(p\)", (" ".join(idx["names"].get(cid, [])) + " " + re.sub(r"[._]", " ", cid)).lower()))


def match_provider_channel(c, idx):
    """Find the guide channel; a West Coast channel with only an East listing gets it shifted 3 hours."""
    guide, how = _match_provider_channel(c, idx)
    c["shift"] = 0
    if guide and wants_west(c) and not is_west_feed(guide, idx):
        c["shift"] = 180
        how += " (East +3h)"
    return guide, how


def _match_provider_channel(c, idx):
    """Find the guide channel for one provider channel: exact code, then name (+ country)."""
    tid = (c.get("id") or "").strip()
    if tid:
        for t in (tid.lower(), tid.split("@")[0].lower()):
            if t in idx["by_id"]:
                return idx["by_id"][t], "code"
        ck = code_key(tid)
        if len(ck) >= 7 and not ck.isdigit() and ck in idx["by_code"]:
            return idx["by_code"][ck], "same code"
    in_name = callsigns(c["name"])
    for call in sorted(callsigns(c["name"] + " " + tid.upper().replace(".", " ")), key=lambda x: (x not in in_name, x)):
        if call in idx["by_call"]:
            return pick_best(idx["by_call"][call], c, idx), "call letters"
    if is_event_channel(c):
        return "", "event"
    want = entry_country(c["name"], c.get("group", ""), tid)
    latin = mostly_latin([c["name"]])
    own = id_country(tid)
    own = own if own.upper() in ISO2 or own in ("uk", "") else ""
    intl = bool(INTL_RE.search(c["name"]))
    world = bool(WORLD_RE.search(plain(c["name"])))

    def ok(cid):  # wrong listings are worse than none
        cc = idx["cc"](cid)
        if want and cc not in (want, "") and not world:
            return False
        if not cc and want in ("us", "uk", "ca") and idx["langs"].get(cid, "") not in ("", "en"):
            return False  # unknown country: an English channel only takes English listings
        if own not in ("", "us", "uk", "ca") and cc in ("us", "uk", "ca") and not intl:
            return False  # "antena.3.ro" never gets a US/UK/CA channel's listings
        if own and cc and own != cc and cc not in HOST_CC and not world and not intl \
                and not {own, cc} <= BALKANS and not {own, cc} <= {"ru", "ua", "by", "kz"}:
            return False  # "kuchnia.pl" never gets the Russian channel with a similar name
        return not latin or mostly_latin(idx["names"].get(cid, []))
    if not latin:
        cands = [x for x in idx["by_raw"].get(raw_key(c["name"]), []) if ok(x)]
        return (pick_best(cands, c, idx), "same name") if cands else ("", "")
    cands = [x for x in idx["by_name"].get(pkey(c["name"]), []) if ok(x)]
    if cands and pkey(c["name"]) not in NAME_STOP:
        return pick_best(cands, c, idx), "name"
    key = pkey_loose(c["name"])
    if key in NAME_STOP:
        return "", ""
    renamed = renamed_name(c["name"])
    if renamed:
        cands = [x for x in idx["by_name"].get(pkey(renamed), []) + idx["by_loose"].get(pkey_loose(renamed), []) if ok(x)]
        if cands:
            return pick_best(cands, c, idx), "renamed channel"
    if key and key not in LOOSE_STOP:
        cands = [x for x in idx["by_loose"].get(key, []) if ok(x)]
        if len(key) < 4:  # short names like "FX": only when the country is certain
            cands = [x for x in cands if want and idx["cc"](x) == want]
        if cands:
            return pick_best(cands, c, idx), "similar name"
    cands = [x for x in idx["by_words"].get(pkey_words(c["name"]), []) if ok(x)]
    if cands:
        return pick_best(cands, c, idx), "same words"
    tag = re.search(r"\s([A-Z]{2,3})\s*\)?$", re.sub(r"\s+(?:US|USA)$", "", plain(c["name"])))
    tag = tag[1].lower() if tag else ""
    tag = BH_ALIAS.get(tag, CC_ALIAS.get(tag, tag))
    tag_cc = tag if tag.upper() in ISO2 else ""
    home = want or own or tag_cc
    national = bool(NATIONAL_RE.search(plain(c["name"])))

    def fits(cid):  # exact country, or an unmistakable name with no country of its own
        cc = idx["cc"](cid)
        if world or cc == home:
            return True
        return not national and not cc and not (tag_cc and cc)

    for short in shorter_names(plain(c["name"])):  # country and quality tags at the end of the name
        for pool, k in ((idx["by_name"], pkey(short)), (idx["by_loose"], pkey_loose(short))):
            if k not in LOOSE_STOP:
                cands = [x for x in pool.get(k, []) if ok(x) and fits(x) and (idx["cc"](x) == home or (
                    len(k) >= 5 and not re.fullmatch(r"(channel|canal)\d+", k)))]
                if cands:
                    return pick_best(cands, c, idx), "name without tags"
    for k in similar_spelling(key, idx):
        cands = [x for x in idx["by_loose"].get(k, []) if ok(x) and (not national or idx["cc"](x) == home)]
        if cands:
            return pick_best(cands, c, idx), "similar spelling"
    # a provider filed it under the wrong country ("Wigan Athletic" with a .us code): only if it can't be a national version
    if not national and want in ("us", "") and own in ("us", ""):
        for short in [plain(c["name"])] + shorter_names(plain(c["name"])):
            k = pkey_loose(short)
            cands = [x for x in idx["by_loose"].get(k, []) if mostly_latin(idx["names"].get(x, []))]
            if len(k) >= 6 and k not in LOOSE_STOP and len({idx["cc"](x) for x in cands} - {""}) == 1:
                return pick_best(cands, c, idx), "only copy anywhere"
    return "", ""


def rematch_provider(idx=None):
    """Match every provider channel again with the newest guides and rules (your own picks stay). Needs no provider link."""
    chans = CFG.get("provider_channels") or []
    if not chans:
        return 0
    idx = idx or provider_index()
    n = 0
    for c in chans:
        if c.get("how") == "event":
            continue
        if c.get("manual"):
            pick = c.get("picked") or c.get("guide") or ""
            if pick.lower() in idx["by_id"] or not pick:
                c.update(guide=pick, how="manual", shift=0)
                continue
            c["picked"] = pick  # its guide is gone for now: use the automatic match until it returns
        c["guide"], c["how"] = match_provider_channel(c, idx)
        n += bool(c["guide"])
    return n


def refresh_provider():
    """Read your provider's channel list (on this PC only) and match every channel to a guide."""
    if not PRIVATE.get("providers"):
        return False
    entries, failed = [], set()
    for i, prov in enumerate(PRIVATE["providers"]):
        dest = os.path.join(CACHE, f"provider{i}.m3u")
        pname = prov.get("name") or f"Provider {i + 1}"
        try:
            log(f"Reading your provider list '{pname}'")
            fetch(prov["url"], dest)
            got = [e for e in parse_m3u(dest) if not re.search(r"/(movie|series)/", e["url"], re.I)]
            before = sum(1 for c in CFG["provider_channels"] if c.get("prov") == pname)
            if not got or (before > 50 and len(got) < before / 2):
                raise RuntimeError(f"list came back with {len(got)} channels (had {before}) - "
                                   "login expired or provider busy?")
            for e in got:
                e["prov"] = pname
                entries.append(e)
        except Exception as ex:
            log(f"  could not read '{pname}': {ex} - keeping its previous matches")
            failed.add(pname)
        finally:
            if os.path.exists(dest):
                os.remove(dest)  # don't keep a copy with your login in it
    old = {c["key"]: c for c in CFG["provider_channels"]}
    idx = provider_index()
    new, seen = [], set()
    for e in entries:
        key = e["epg_id"] or "name:" + e["name"]
        if key in seen:
            continue
        seen.add(key)
        c = {"key": key, "id": e["epg_id"] or e["name"], "name": e["name"], "group": e["group"], "prov": e["prov"]}
        prev = old.get(key)
        if prev and prev.get("manual"):
            c.update(guide=prev["guide"], how="manual", manual=True)
        else:
            c["guide"], c["how"] = match_provider_channel(c, idx)
        new.append(c)
    new += [c for c in CFG["provider_channels"] if c.get("prov") in failed and c["key"] not in seen]
    changed = [(c["key"], c["guide"]) for c in new] != [(c["key"], c.get("guide")) for c in CFG["provider_channels"]]
    CFG["provider_channels"] = new
    matched = sum(1 for c in new if c["guide"])
    log(f"Your providers: {len(new)} live channels, {matched} matched to a guide")
    return changed


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
    k = key.lower()
    return "epg-full.xml.gz" if k == "full" else f"epg-{'uk' if k in ('gb', 'uk') else k}.xml.gz"


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

    # guide for the playlist above (small, loads fast)
    now = datetime.now(timezone.utc)
    start_cut = now - timedelta(hours=6)
    end_cut = now + timedelta(days=settings["days"])
    wanted = {}
    for e in rows:
        wanted.setdefault(e["tvg_id"], e)
    real = {cid for cid in wanted if cid in EPG_INDEX}
    owner = channel_owners(xml_sources)
    tmp = os.path.join(OUT, "epg.xml.tmp")
    count = 0
    with open(tmp, "w", encoding="utf-8") as f:
        f.write('<?xml version="1.0" encoding="UTF-8"?>\n<tv generator-info-name="Ultimate EPG">\n')
        for cid, e in wanted.items():
            f.write(f"<channel id={quoteattr(cid)}><display-name>{escape(clean_text(e['name']))}</display-name>")
            logo = e["logo"] or EPG_INDEX.get(cid, {}).get("icon", "")
            if logo:
                f.write(f"<icon src={quoteattr(logo)}/>")
            f.write("</channel>\n")
        claimed, clean = set(), ShowCleaner()
        for src in xml_sources:
            path = os.path.join(CACHE, src["id"] + ".xml")
            if not os.path.exists(path):
                continue
            here = set()
            try:
                for el in iter_xmltv(path, ("programme",)):
                    cid = el.get("channel", "")
                    if cid not in real or cid in claimed or owner.get(cid) != src["id"] or is_junk(el):
                        continue
                    st, sp = parse_xmltv_time(el.get("start")), parse_xmltv_time(el.get("stop"))
                    if not st or (sp or st) < start_cut or st > end_cut:
                        continue
                    times = clean.check(cid, el, st, sp)
                    if not times:
                        continue
                    el.set("start", fmt_xmltv_time(times[0]))  # always a full time with its zone
                    if sp:
                        el.set("stop", fmt_xmltv_time(times[1]))
                    el.tail = "\n"
                    f.write(ET.tostring(el, encoding="unicode"))
                    here.add(cid)
                    count += 1
            except Exception as ex:
                log(f"Guide '{src['name']}' could not be fully read ({ex}); kept what was readable")
            claimed |= here
        if settings["dummy_epg"]:
            for cid, e in wanted.items():
                if cid not in claimed:
                    count += write_placeholder(f, cid, e["name"], e["desc"] or f"{e['name']} - live 24/7", now, end_cut)
        f.write("</tv>\n")
    os.replace(tmp, os.path.join(OUT, "epg.xml"))
    with open(os.path.join(OUT, "epg.xml"), "rb") as src, gzip.open(os.path.join(OUT, "epg.xml.gz.tmp"), "wb") as dst:
        shutil.copyfileobj(src, dst, 1 << 20)
    os.replace(os.path.join(OUT, "epg.xml.gz.tmp"), os.path.join(OUT, "epg.xml.gz"))
    log(f"Playlist guide: {len(rows)} channels, {count} guide entries ({len(claimed)} channels with real guide)")

    if settings.get("full_guide"):
        build_universal(xml_sources, wanted, now, start_cut,
                        now + timedelta(days=float(settings.get("full_guide_days") or 2)))
    old = os.path.join(OUT, "epg-provider.xml.gz")  # replaced by the universal guide
    if os.path.exists(old):
        os.remove(old)
    STATE["last_build"] = time.time()
    log("Done")


def channel_owners(xml_sources):
    """Which guide site each channel code belongs to (codes like "172" mean different channels on different sites)."""
    owner = {}
    for x in xml_sources:
        path = os.path.join(CACHE, x["id"] + ".channels.json")
        if os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                for cid, info in json.load(fh).items():
                    if cid not in owner and info.get("n", 1):
                        owner[cid] = x["id"]
    return owner


def event_is_over(name, now):
    """Event names can carry a date ("... Oct 30 01:00 AM") that is long gone when your PC stays off."""
    m = re.search(r"\b(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\.?\s+(\d{1,2})\b", name, re.I)
    try:
        if m:
            month = "jan feb mar apr may jun jul aug sep oct nov dec".split().index(m[1].lower()) + 1
            when = datetime(now.year, month, int(m[2]), tzinfo=timezone.utc)
            if when > now + timedelta(days=180):  # December's event seen in January
                when = when.replace(year=now.year - 1)
        else:
            m = re.search(r"\b(\d{4})-(\d\d)-(\d\d)\b", name)
            when = m and datetime(int(m[1]), int(m[2]), int(m[3]), tzinfo=timezone.utc)
    except ValueError:
        return False
    return bool(when) and when < now - timedelta(days=1)


def write_placeholder(f, cid, title, desc, now, end_cut):
    block = timedelta(hours=max(1, int(CFG["settings"]["dummy_hours"])))
    hours = int(block.total_seconds() // 3600)
    t = now.replace(minute=0, second=0, microsecond=0) - timedelta(hours=now.hour % hours)
    n = 0
    while t < end_cut:
        f.write(f'<programme start="{fmt_xmltv_time(t)}" stop="{fmt_xmltv_time(t + block)}" '
                f'channel={quoteattr(cid)}><title>{escape(clean_text(title))}</title>'
                + (f'<desc>{escape(clean_text(desc))}</desc>' if desc else '') + '</programme>\n')
        t += block
        n += 1
    return n


NO_SCHEDULE = "This channel doesn't publish a schedule."
LABEL_KINDS = ((re.compile(r"big brother|fazenda", re.I), "Live Camera"),
               (re.compile(r"music|stingray|proturk|lionbox|redbox|byzbox", re.I), "Music Channel"),
               (re.compile(r"sport|world cup|center ice|racing", re.I), "Live Sports"),
               (re.compile(r"movies", re.I), "Movies"),
               (re.compile(r"news", re.I), "News"))


def channel_label(c):
    """'Stingray Latin Pop - Music Channel': says what the channel is, never pretends to be a show."""
    name = clean_text(unescape_all(c["name"])).strip()
    text = f'{name} {c.get("group") or ""}'
    kind = next((k for rx, k in LABEL_KINDS if rx.search(text)), "")
    return {"name": f"{name} - {kind}" if kind else name, "desc": NO_SCHEDULE, "logo": ""}


NAME_PREFIXES = {"us": ["US: ", "US| ", "USA: ", "US - "], "uk": ["UK: ", "UK| ", "UK - "],
                 "ca": ["CA: ", "CA| ", "CA - "]}


def is_readable_id(cid):
    """Codes providers actually use look like 'ESPN.us' - not '172' or 'I229.14902.schedulesdirect.org'."""
    return bool(re.search(r"[A-Za-z]{3,}", cid)) and not re.match(r"I\d+\.\d+\.schedulesdirect", cid)


def name_variants(name, cc):
    """The ways providers write a channel name: 'ESPN', 'ESPN HD', 'US: ESPN', 'US| ESPN HD'..."""
    base = PROVIDER_PREFIX_RE.sub("", unescape_all(name)).strip()
    base = re.sub(r"\s+(HD|FHD|UHD|SD|4K)$", "", base, flags=re.I).strip()
    if not base:
        return []
    bases = [base]
    for alt in (re.sub(r"([A-Za-z])(\d)", r"\1 \2", base), re.sub(r"([A-Za-z]) (\d)", r"\1\2", base)):
        if alt not in bases:
            bases.append(alt)  # "ITV1" <-> "ITV 1"
    out = []
    for b in bases:
        out += [b, b + " HD"]
        for p in NAME_PREFIXES.get(cc, []):
            out += [p + b, p + b + " HD"]
    return out


WEEK_DAYS = 7


def build_universal(xml_sources, wanted, now, start_cut, end_cut):
    """ONE guide for any provider and any player.
    Every copy of a real channel (ESPN on five guide sites under five codes) is grouped together.
    The group answers to every known code - including codes learned from your providers and
    playlists - and to every common way of writing its name. Codes with no shows of their own
    are filled from the best copy in the group. Also split per priority country."""
    pri = priority_list()
    n_pri = len(pri)
    # codes and names learned from your providers and playlists
    learned = {}  # their code -> (matched guide code, [their channel names])
    shifts, events = {}, []
    for c in CFG.get("provider_channels") or []:
        if c.get("guide"):
            learned.setdefault(c["id"], (c["guide"], []))[1].append(c["name"])
            if c.get("shift"):
                shifts[c["id"]] = c["shift"]
        elif c.get("how") == "event":
            events.append(c)
    for ch in CFG["channels"].values():
        up, e = ch["up"], effective(ch)
        if up.get("epg_id") and e.get("epg_id") and up["epg_id"] != e["epg_id"]:
            learned.setdefault(up["epg_id"], (e["epg_id"], []))[1].append(e["name"])
    targets = {g for g, _ in learned.values()} | set(wanted)  # your own playlist's guides come along too
    prov = [c for c in CFG.get("provider_channels") or [] if c.get("id")]
    lite_codes = {c["id"] for c in prov} | set(learned)  # light guide: just the channels your providers carry

    chans = {}
    for x in xml_sources:
        in_pri = priority_rank(x) < n_pri
        xcc = guess_country(x["url"], x["name"]).lower()
        xcc = CC_ALIAS.get(xcc, xcc)
        path = os.path.join(CACHE, x["id"] + ".channels.json")
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as fh:
            for cid, info in json.load(fh).items():
                if cid in chans or not info.get("n", 1) or not (in_pri or cid in targets):
                    continue
                chans[cid] = {"src": x["id"], "names": [n for n in info["names"] if n] or [cid],
                              "icon": info.get("icon", ""), "n": info.get("n", 1),
                              "cc": id_country(cid) or xcc, "lang": info.get("lang", "")}

    # group the copies of each real-world channel
    clusters = {}
    for cid, c in chans.items():
        calls = sorted(callsigns(" ".join(c["names"]) + " " + re.sub(r"[._]", " ", cid)))
        if calls:
            key = ("call", calls[0])
        else:
            raw = PROVIDER_PREFIX_RE.sub("", unescape_all(c["names"][0]).lower())
            west = bool(re.search(r"\b(pacific|west)\b", raw + " " + cid.lower()))
            key = (c["cc"], pkey(raw) or cid, west)
        clusters.setdefault(key, []).append(cid)

    out = {}  # published code -> where its shows come from + its names
    for key, cids in clusters.items():
        def rank(k):
            c = chans[k]
            english_ok = c["lang"] in ("", "en") or c["cc"] not in ("us", "uk", "ca")
            return (c["n"] > 0, english_ok, is_readable_id(k), c["n"])
        best = max(cids, key=rank)
        names, seen = [], set()
        for k in cids:
            for n in chans[k]["names"]:
                if n.lower() not in seen:
                    seen.add(n.lower())
                    names.append(n)
        for n in name_variants(chans[best]["names"][0], chans[best]["cc"]):
            if n.lower() not in seen:
                seen.add(n.lower())
                names.append(n)
        icon = next((chans[k]["icon"] for k in [best] + cids if chans[k]["icon"]), "")
        group = {"names": names, "seen": seen, "icon": icon, "cc": chans[best]["cc"], "best": best}
        for k in cids:
            chans[k]["group"] = group
        for k in [k for k in cids if is_readable_id(k)] or [best]:
            out[k] = {"from": k if chans[k]["n"] else best, "group": group}
    for code, (g, names) in learned.items():
        if g not in chans:
            continue
        group = chans[g]["group"]
        for n in names:  # their names help name-matching players for the whole group
            if n.lower() not in group["seen"]:
                group["seen"].add(n.lower())
                group["names"].append(n)
        if code not in out:
            out[code] = {"from": g if chans[g]["n"] else group["best"], "group": group,
                         "shift": shifts.get(code, 0)}
    for c in events:  # game/PPV slots: show the event name from the channel name instead of "No information"
        if c["id"] not in out:
            title = re.sub(r"\s*\|\s*\(?\d{4}-\d\d-\d\d.*$", "", c["name"]).strip() or c["name"]
            if event_is_over(c["name"], now):
                title = "No event scheduled"
            out[c["id"]] = {"from": None, "group": {"names": [c["name"]], "icon": "", "cc": "", "best": c["id"]},
                            "placeholder": {"name": title, "desc": f"Live event on {c['group'] or 'this channel'}"}}
    for c in prov:  # no shows from any guide: a clear label instead of an empty row
        if c.get("how") == "event":
            continue
        if c["id"] not in out:
            out[c["id"]] = {"from": None, "group": {"names": [c["name"]], "icon": "", "cc": "", "best": c["id"]}}
        out[c["id"]].setdefault("placeholder", channel_label(c))
    for cid, e in wanted.items():  # your own playlist's channels are always in it too
        if cid not in out:
            out[cid] = {"from": cid if cid in chans else None,
                        "group": {"names": [e["name"]], "icon": e["logo"], "cc": "", "best": cid},
                        "placeholder": e}

    def file_key(cc):
        cc = cc.lower()
        return "uk" if cc in ("gb", "uk") else cc
    keys = ["full", "lite", "week"] + [file_key(c) for c in pri]
    week_cut = max(end_cut, now + timedelta(days=WEEK_DAYS))
    files = {k: gzip.open(os.path.join(OUT, full_name(k) + ".tmp"), "wt", encoding="utf-8", compresslevel=6)
             for k in keys}
    for fh in files.values():
        fh.write('<?xml version="1.0" encoding="UTF-8"?>\n<tv generator-info-name="Ultimate EPG (universal)">\n')

    def write(code, text, far=False):
        if code in lite_codes:
            files["week"].write(text)
        if far:  # past the normal guide's last day: the week guide only
            return
        files["full"].write(text)
        if code in lite_codes:
            files["lite"].write(text)
        k = file_key(out[code]["group"]["cc"] or "")
        if k in files and k != "full":
            files[k].write(text)

    for code, o in out.items():
        g = o["group"]
        own = chans[code]["names"][:8] if code in chans and code != g["best"] else g["names"][:16]
        own = [clean_text(n).strip() for n in own if clean_text(n).strip()] or [code]
        text = f"<channel id={quoteattr(code)}>" + "".join(f"<display-name>{escape(n)}</display-name>" for n in own)
        if g["icon"]:
            text += f"<icon src={quoteattr(g['icon'])}/>"
        write(code, text + "</channel>\n")
    fill = {}
    for code, o in out.items():
        if o["from"]:
            fill.setdefault(o["from"], []).append(code)

    shows, live_from, clean = 0, set(), ShowCleaner()
    for x in xml_sources:
        path = os.path.join(CACHE, x["id"] + ".xml")
        if not os.path.exists(path):
            continue
        try:
            for el in iter_xmltv(path, ("programme",)):
                cid = el.get("channel", "")
                if cid not in fill or chans.get(cid, {}).get("src") != x["id"] or is_junk(el):
                    continue
                st, sp = parse_xmltv_time(el.get("start")), parse_xmltv_time(el.get("stop"))
                if not st or (sp or st) < start_cut or st > week_cut:
                    continue
                times = clean.check(cid, el, st, sp)
                if not times:
                    continue
                st, sp = times
                el.set("start", fmt_xmltv_time(st))  # always a full time with its zone
                if sp:
                    el.set("stop", fmt_xmltv_time(sp))
                for child in list(el):
                    if child.tag in SLIM_TAGS:
                        el.remove(child)
                el.tail = "\n"
                for code in fill[cid]:
                    el.set("channel", code)
                    shift = out[code].get("shift")
                    if shift:
                        el.set("start", fmt_xmltv_time(st + timedelta(minutes=shift)))
                        if sp:
                            el.set("stop", fmt_xmltv_time(sp + timedelta(minutes=shift)))
                    write(code, ET.tostring(el, encoding="unicode"), st > end_cut)
                    if shift:
                        el.set("start", fmt_xmltv_time(st))
                        if sp:
                            el.set("stop", fmt_xmltv_time(sp))
                    shows += 1
                live_from.add(cid)
        except Exception as ex:  # one broken guide never stops the others
            log(f"Guide '{x['name']}' could not be fully read ({ex}); kept what was readable")
    for code, o in out.items():  # placeholders so nothing shows "No information"
        e = o.get("placeholder")
        if e and CFG["settings"]["dummy_epg"] and not (o["from"] and o["from"] in live_from):
            text = []

            class W:
                def write(self, t):
                    text.append(t)
            write_placeholder(W(), code, e["name"], e["desc"] or f"{e['name']} - live 24/7", now, end_cut)
            near = len(text)
            write(code, "".join(text))
            text.clear()
            write_placeholder(W(), code, e["name"], e["desc"] or f"{e['name']} - live 24/7", now, week_cut)
            write(code, "".join(text[near:]), True)

    log(f"Cleaned out {clean.dropped} duplicate/overlapping/empty shows")
    sizes = []
    for k, fh in files.items():
        fh.write("</tv>\n")
        fh.close()
        os.replace(os.path.join(OUT, full_name(k) + ".tmp"), os.path.join(OUT, full_name(k)))
        sizes.append(f"{full_name(k)} {os.path.getsize(os.path.join(OUT, full_name(k))) >> 20} MB")
    prov = CFG.get("provider_channels") or []
    STATE["provider_live"] = sum(1 for c in prov if c.get("guide") and out.get(c["id"], {}).get("from") in live_from)
    STATE["universal"] = {"channels": len(clusters), "codes": len(out), "learned": len(learned), "shows": shows,
                          "real_channels": len(live_from)}
    log(f"Universal guide: {len(clusters)} real channels answering to {len(out)} codes "
        f"({len(learned)} learned from your providers/playlists), {shows} shows - " + ", ".join(sizes))

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
                if not entries:
                    raise ValueError("playlist came back empty")
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
            fresh = False
            if src["type"] == "xmltv" and os.path.exists(dest):
                try:  # last good copy: its remaining shows still go in the guide
                    fresh = index_xmltv_source(src)[2]
                except Exception:
                    pass
            st.update(ok=False, fresh=fresh, msg=str(ex)[:300], time=time.time())
            log(f"  FAILED: {ex}" + (" - using the last good copy" if fresh else ""))
        if src.get("auto"):
            src["fails"] = 0 if st.get("ok") and st.get("fresh") else src.get("fails", 0) + 1
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
        gone = set(CFG.get("blocked_urls") or [])  # guides you removed, on any device
        AUTO["blocked"] = sorted(set(AUTO["blocked"]) | gone)
        AUTO["sources"] = [x for x in AUTO["sources"] if x["url"] not in gone]
        load_epg_index()
        if CFG["settings"]["auto_match"]:
            n = auto_match(only_unmatched=True)
            log(f"Auto-matched {n} channel(s) without a guide")
    provider_changed = False
    with LOCK:
        if PRIVATE.get("providers") and not only:
            provider_changed = refresh_provider()
        else:
            rematch_provider()
    if not only and CFG["settings"]["auto_discover"]:
        try:
            discover()
        except Exception as ex:
            log(f"Guide search stopped early: {ex}")
        with LOCK:
            load_epg_index()
            auto_match(only_unmatched=True)
    with LOCK:
        rematch_provider()
        if not only:
            CFG["last_refresh"] = time.time()
        save_config()
    save_auto()
    if provider_changed and CFG["settings"].get("public_url") and os.path.isdir(os.path.join(BASE, ".git")):
        try:  # keep the online provider guide in step with your provider's channels
            with LOCK:
                publish()
        except Exception as ex:
            log(f"Could not publish provider changes: {ex}")


def provider_job():
    with LOCK:
        changed = refresh_provider()
        save_config()
    if changed and CFG["settings"].get("public_url") and os.path.isdir(os.path.join(BASE, ".git")):
        try:
            with LOCK:
                publish()
        except Exception as ex:
            log(f"Could not publish provider changes: {ex}")


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
    before = json.dumps(AUTO)
    refresh()
    build()
    sizes = {f: os.path.getsize(os.path.join(OUT, f)) for f in os.listdir(OUT)
             if re.fullmatch(r"epg(-[a-z]+)?\.xml\.gz|playlist\.m3u", f)}
    last = AUTO.get("good_sizes") or {}
    small = [f for f, n in sizes.items() if n < 5000 or n < last.get(f, 0) * 0.5]
    since = AUTO.get("guard_since") or time.time()
    if small and time.time() - since < 24 * 3600:  # the online guide covers 2 days, so there is time to wait
        reason = ", ".join(f"{f} {sizes[f]} bytes (last good {last.get(f, 0)})" for f in small)
        AUTO.clear()
        AUTO.update(json.loads(before))  # a bad run changes nothing, except remembering it happened
        AUTO["guard_since"] = since
        save_auto()
        raise SystemExit(f"Guide came out far too small: {reason} - keeping the previous online guide")
    if small:
        log("Guide stayed small for a whole day - accepting it as the new normal")
    AUTO["good_sizes"], AUTO["guard_since"] = sizes, 0
    save_auto()
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
                     ("Full guide - use with any provider", "epg-full.xml.gz"),
                     ("Light guide - your providers' channels only (Firestick, Smarters, Kodi)", "epg-lite.xml.gz"),
                     ("Week guide - your providers' channels, up to 7 days (TiviMate, OTT Navigator)", "epg-week.xml.gz")] +
                    [(f"{c} guide (any provider)", full_name(c)) for c in priority_list()] +
                    ([("Guide made for your provider (TiviMate etc.)", "epg-provider.xml.gz")]
                     if os.path.exists(os.path.join(OUT, "epg-provider.xml.gz")) else []))
    with open(os.path.join(outdir, "index.html"), "w", encoding="utf-8") as f:
        f.write(f'<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width">'
                f'<title>My EPG</title><body style="font:16px system-ui;max-width:640px;margin:40px auto;padding:0 16px">'
                f'<h1>My EPG</h1>{links}<p style="color:#777">Updated {time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime())}</p>')
    print(f"Site written to {outdir}")


def sync_from_github():
    """Fetch guides GitHub found on its own (the online copy of auto_sources.json wins)."""
    global AUTO
    with SAVE_LOCK:
        git("reset", "-q", "--", "data/auto_sources.json", check=False)
        git("checkout", "--", "data/auto_sources.json", check=False)
        git("pull", "-q", "--rebase", "--autostash", "origin", "main")
        fresh = load_auto()
        AUTO.clear()  # same object: running jobs keep working on it
        AUTO.update(fresh)
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
            "universal": STATE.get("universal"),
            "provider": {
                "names": [x.get("name", "Provider") for x in PRIVATE.get("providers", [])],
                "per": {n: sum(1 for c in CFG["provider_channels"] if c.get("prov") == n)
                        for n in [x.get("name", "Provider") for x in PRIVATE.get("providers", [])]},
                "count": sum(1 for c in CFG["provider_channels"] if c.get("how") != "event"),
                "events": sum(1 for c in CFG["provider_channels"] if c.get("how") == "event"),
                "matched": sum(1 for c in CFG["provider_channels"] if c.get("guide")),
                "live": STATE.get("provider_live"),
                "unmatched": [c for c in CFG["provider_channels"] if not c.get("guide") and c.get("how") != "event"][:800]},
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
        if not self.path.startswith("/api"):
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
        origin = self.headers.get("Origin")
        if origin and urlparse(origin).netloc != self.headers.get("Host"):
            return self.send(403, {"error": "not allowed from another website"})
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
                    if k not in DEFAULT_SETTINGS:
                        continue
                    kind = type(DEFAULT_SETTINGS[k])
                    if v is None or v == "":
                        continue  # left empty: keep the old value
                    if kind is bool:
                        v = v.lower() in ("true", "1", "yes", "on") if isinstance(v, str) else bool(v)
                    else:
                        try:
                            v = kind(v)
                        except (TypeError, ValueError, OverflowError):
                            continue
                        if kind in (int, float):
                            if v != v or v < 0 or v == float("inf") or (v == 0 and k in MUST_BE_POSITIVE):
                                continue
                            v = min(v, SETTING_MAX.get(k, v))
                    CFG["settings"][k] = v
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
                        CFG.setdefault("blocked_urls", []).append(src["url"])
                        save_config()
                        for f in os.listdir(CACHE):
                            if f.startswith(src["id"] + "."):
                                os.remove(os.path.join(CACHE, f))
                    load_epg_index()
                    save_config()
                    save_auto()
            run_job()
            return self.send(200, {"ok": bool(src)})
        if p == "/api/provider":
            url = (body.get("url") or "").strip()
            with LOCK:
                provs = PRIVATE.setdefault("providers", [])
                if "remove" in body:
                    i = int(body["remove"])
                    if 0 <= i < len(provs):
                        gone = provs.pop(i).get("name")
                        CFG["provider_channels"] = [c for c in CFG["provider_channels"] if c.get("prov") != gone]
                elif url:
                    name = (body.get("name") or "").strip() or f"Provider {len(provs) + 1}"
                    provs[:] = [x for x in provs if x.get("name") != name] + [{"name": name, "url": url}]
                save_private()
                if not provs:
                    CFG["provider_channels"] = []
                save_config()
            run_job(provider_job)
            return self.send(200, {"ok": True})
        if p == "/api/provider/map":
            with LOCK:
                for c in CFG["provider_channels"]:
                    if c["key"] == body.get("key"):
                        c.update(guide=body.get("guide", ""), how="manual", manual=True, shift=0, picked="")
                save_config()
            run_job()
            return self.send(200, {"ok": True})
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
