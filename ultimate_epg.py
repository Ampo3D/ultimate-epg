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
import itertools
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
import xml.parsers.expat
import zlib
from concurrent.futures import ThreadPoolExecutor
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


def safe_replace(tmp, path):
    """Windows refuses while a player or antivirus has the file open, usually only for a moment."""
    for attempt in range(5):
        try:
            return os.replace(tmp, path)
        except PermissionError:
            if attempt == 4:
                raise
            time.sleep(1)


def load_config():
    if os.path.exists(CONFIG_PATH):
        try:
            with open(CONFIG_PATH, encoding="utf-8") as f:
                cfg = json.load(f)
        except ValueError:  # cut off by a power failure
            with open(CONFIG_PATH, encoding="utf-8") as f:
                if "<<<<<<<" in f.read():  # a git clash: the backup is older than both sides, never publish it
                    raise SystemExit("config.json has git clash marks (<<<<<<<) - fix it before starting")
            print("config.json was damaged - using config.json.bak")
            with open(CONFIG_PATH + ".bak", encoding="utf-8") as f:
                cfg = json.load(f)
    else:
        cfg = {}
    config_defaults(cfg)
    if not os.path.exists(CONFIG_PATH):  # first run: start with the recommended free sources
        try:
            with open(os.path.join(BASE, "catalog.json"), encoding="utf-8") as f:
                cfg["sources"] = [{"id": uuid.uuid4().hex[:8], "type": c["type"], "name": c["name"],
                                   "url": c["url"], "enabled": True}
                                  for c in json.load(f) if c.get("default")]
        except (OSError, ValueError):
            pass
    CFG_SEEN.update(stamp=config_stamp(), base=json.dumps(cfg, ensure_ascii=False))
    return cfg


def config_defaults(cfg):
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
    return cfg


def read_config_file():
    """config.json as it is now, or None when it can't be trusted for a merge: missing, cut off mid-save, git clash marks."""
    try:
        with open(CONFIG_PATH, encoding="utf-8") as f:
            text = f.read()
        return None if "<<<<<<<" in text else config_defaults(json.loads(text))
    except (OSError, ValueError):
        return None


CFG_SEEN = {}  # config.json as last read or written: an edit made to the file meanwhile is merged, never lost
_GONE = object()


def config_stamp():
    try:
        st = os.stat(CONFIG_PATH)
        return st.st_mtime_ns, st.st_size
    except OSError:
        return None


def merge3(base, mine, disk):
    """Keep both the app's changes and an edit made to the file meanwhile (the file wins a clash)."""
    if mine == base:
        return disk
    if disk == base or disk == mine:
        return mine
    if all(isinstance(x, dict) for x in (base, mine, disk)):
        out = {}
        for k in list(mine) + [k for k in disk if k not in mine]:
            v = merge3(base.get(k, _GONE), mine.get(k, _GONE), disk.get(k, _GONE))
            if v is not _GONE:
                out[k] = v
        return out
    lists = (base, mine, disk)
    if all(isinstance(x, list) and all(isinstance(i, (str, int, float)) for i in x) for x in lists):
        gone = [i for i in base if i not in mine]  # blocked links, kept links: the app's removals and additions on top of the file's
        return [i for i in disk if i not in gone] + [i for i in mine if i not in base and i not in disk]
    if all(isinstance(x, list) and all(isinstance(i, dict) and "id" in i for i in x) for x in lists):
        for key in (lambda i: i["id"], lambda i: json.dumps([i["id"], i.get("name"), i.get("group")])):
            by_id = [{key(i): i for i in x} for x in lists]
            if all(len(d) == len(x) for d, x in zip(by_id, lists)):  # provider channels, sources: merged one by one
                return list(merge3(*by_id).values())
    return disk


def adopt(old, new):
    """Put the merged config into the objects already in use: a running job holding a part of it keeps a live part."""
    if isinstance(old, dict) and isinstance(new, dict):
        for k in [k for k in old if k not in new]:
            del old[k]
        for k, v in new.items():
            old[k] = adopt(old[k], v) if k in old else v
        return old
    if isinstance(old, list) and isinstance(new, list):
        ids = {}
        for i in old:
            if isinstance(i, dict) and isinstance(i.get("id"), str):
                ids.setdefault(i["id"], []).append(i)
        old[:] = [adopt(ids[i["id"]].pop(0), i) if isinstance(i, dict) and ids.get(i.get("id")) else i for i in new]
        return old
    return new


def save_config():
    readable = True
    if CFG_SEEN.get("stamp") and config_stamp() != CFG_SEEN["stamp"]:
        disk = read_config_file()
        readable = disk is not None
        if readable:
            adopt(CFG, merge3(json.loads(CFG_SEEN["base"]), json.loads(json.dumps(CFG, ensure_ascii=False)), disk))
            log("config.json was changed outside the app - merged those changes in")
        else:  # half-saved by an editor, or clash marks: never merge with the old backup or an empty config
            log("config.json was changed outside the app but can't be read - saved the app's copy (the last good one stays in config.json.bak)")
    for k in [k for k, c in CFG["channels"].items() if LOGIN_URL_RE.search(effective(c).get("url") or "")]:
        del CFG["channels"][k]  # a login that leaked into a public list is never published
    text = json.dumps(CFG, ensure_ascii=False, indent=1)
    tmp = CONFIG_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(text)
        f.flush()
        os.fsync(f.fileno())
    if not readable and CFG_SEEN.get("base"):  # the backup is the last good file: what the app last read or wrote
        write_atomic(CONFIG_PATH + ".bak", CFG_SEEN["base"])
    elif os.path.exists(CONFIG_PATH):
        shutil.copyfile(CONFIG_PATH, CONFIG_PATH + ".bak")
    safe_replace(tmp, CONFIG_PATH)
    CFG_SEEN.update(stamp=config_stamp(), base=text)


MAX_UNPACKED = 4 << 30
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
    safe_replace(tmp, path)


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
    seen, out = set(), []
    for s in CFG["sources"] + AUTO["sources"]:  # a kept auto-found guide is in both lists
        if s["id"] not in seen and not is_removed(s):
            seen.add(s["id"])
            out.append(s)
    return out


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

MAX_DOWNLOADS = 12   # at once
HOST_DOWNLOADS = 3   # at once from one site, to stay polite
MIN_SPEED = 50_000   # bytes a second, checked after the first minute


def looks_valid(path, dest):
    """An error page or empty answer must not replace the last good copy."""
    with open(path, "rb") as f:
        head = f.read(1 << 16).replace(b"\0", b"").lstrip(b"\xef\xbb\xbf\xff\xfe \r\n\t")
    if not head:
        return False
    if dest.endswith(".xml"):  # "<?xml ...><Error>" pages and an empty <tv></tv> are not guides
        return b"<tv" in head and (b"<channel" in head or b"<programme" in head)
    return not head.startswith(b"<")


def fetch(url, dest, max_bytes=None):
    """Download a URL (or copy a local file) to dest, un-gzipping if needed."""
    tmp = dest + ".part"
    try:
        if re.match(r"^https?://", url, re.I):
            req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
            with urllib.request.urlopen(req, timeout=30) as r, open(tmp, "wb") as f:
                got, began = 0, time.time()
                while chunk := r.read(1 << 18):
                    got += len(chunk)
                    if max_bytes and got > max_bytes:
                        raise ValueError(f"bigger than {max_bytes >> 20} MB")
                    took = time.time() - began
                    if took > 60 and got < took * MIN_SPEED:
                        raise ValueError(f"too slow ({got >> 10} KB in {int(took)} s)")
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
                total = 0
                while chunk := src.read(1 << 20):
                    total += len(chunk)
                    if total > MAX_UNPACKED:
                        raise ValueError(f"unpacks to over {MAX_UNPACKED >> 30} GB")
                    dst.write(chunk)
        final = dest + ".unz" if gz or xz else tmp
        if not looks_valid(final, dest):
            raise ValueError("not a guide or playlist (error page or empty)")
        safe_replace(final, dest)
    finally:  # also removes anything that could hold a provider login
        for leftover in (tmp, dest + ".unz"):
            if os.path.exists(leftover):
                os.remove(leftover)


def download_all(sources, dest_of):
    """Fetch many sources at once so one slow site holds up nobody else. Returns {source id: error}."""
    hosts, failed = {}, {}
    for src in sources:
        hosts.setdefault(urlparse(src["url"]).netloc, threading.Semaphore(HOST_DOWNLOADS))

    def one(src):
        with hosts[urlparse(src["url"]).netloc]:
            try:
                fetch(src["url"], dest_of(src))
            except Exception as ex:
                failed[src["id"]] = ex
    with ThreadPoolExecutor(MAX_DOWNLOADS) as pool:
        list(pool.map(one, sources))
    return failed


# ---------------------------------------------------------------- M3U

ATTR_RE = re.compile(r'([\w-]+)="([^"]*)"')


def unescape_all(v):
    """Some playlists write & as &amp; (even &amp;amp;) - turn it back into a plain &."""
    while True:
        u = html.unescape(v)
        if u == v:
            return v
        v = u


NEWLINE_RE = re.compile("[\t\r\n\x0b\x0c\x85\u2028\u2029]")


def parse_m3u(path):
    with open(path, encoding="utf-8", errors="replace") as f:
        lines = [l.strip() for l in f]
    entries, cur, extra = [], None, []
    for line in lines:
        if not line:
            continue
        if line.upper().startswith("#EXTINF"):
            line = NEWLINE_RE.sub(" ", clean_text(line))
            m = re.match(r'((?:[^,"]|"[^"]*")*),(.*)$', line)
            head, title = (m[1], m[2]) if m else (line, "")
            attrs = {k: NEWLINE_RE.sub(" ", unescape_all(v)) for k, v in ATTR_RE.findall(head)}
            cur = {"attrs": attrs, "title": NEWLINE_RE.sub(" ", unescape_all(title.strip()))}
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
    entries = [e for e in entries if not LOGIN_URL_RE.search(e["url"])]  # someone's paid login: config.json is public
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

CHAR_REF = re.compile(rb"&#([xX][0-9a-fA-F]+|[0-9]+);")


def char_ref_ok(m):  # "&#55357;" (half an emoji) or "&#x110000;" would stop the parser: the rest of the guide lost
    if len(m[1]) > 12:
        return b""
    n = int(m[1][1:], 16) if m[1][:1] in b"xX" else int(m[1])
    return m[0] if n in (9, 10, 13) or 0x20 <= n <= 0xD7FF or 0xE000 <= n <= 0xFFFD or 0x10000 <= n <= 0x10FFFF else b""


BAD_XML_BYTES = re.compile(rb"[\x00-\x08\x0b\x0c\x0e-\x1f]|\xef\xbf[\xbe\xbf]|"
                           rb"&#(?:0*(?:[0-8]|1[124-9]|2\d|3[01])|[xX]0*(?:[0-8bcefBCEF]|1[0-9a-fA-F]));")
BARE_AMP = re.compile(rb"&(?!(?:amp|lt|gt|quot|apos|#\d+|#[xX][0-9a-fA-F]+);)")
CTRL_RE = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f\ufffe\uffff]")


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
            data = BARE_AMP.sub(b"&amp;", CHAR_REF.sub(char_ref_ok, BAD_XML_BYTES.sub(b"", data)))
            if data or not raw:
                return data

    def close(self):
        self.f.close()


ESCAPED_TWICE_RE = re.compile(r"&amp;(?=(?:amp|lt|gt|quot|apos|#\d+|#x[0-9a-fA-F]+);)")
ESCAPED_RE = re.compile(r"&([a-zA-Z]{2,8}|#\d+|#x[0-9a-fA-F]+);")  # "&eacute;" too


LOST_U_RE = re.compile(r"(?<!\\)u00([c-fC-F][0-9a-fA-F])")  # "Notu00edcias": a \u escape that lost its backslash
MOJIBAKE_RE = re.compile("(?:[\u00c2\u00c3][\u0080-\u00bf\u0152\u0153\u0160\u0161\u0178\u017d\u017e\u0192\u02c6\u02dc\u2013-\u2122]|\u00e2\u20ac.)+")  # UTF-8 read as Windows-1252: "Â£", "â€™"
TAG_RE = re.compile(r"<!--.*?(?:-->|$)|<style\b.*?(?:</style>|$)|</?(?:a|b|i|u|s|br|hr|p|em|strong|small|big|sup|sub|span|div|font|center|meta|link|"
                    r"img|button|li|ul|ol|dl|dt|dd|h[1-6]|table|thead|tbody|tr|td|th|blockquote|section|article|header|footer|nav|"
                    r"label|input|form|iframe|script|noscript|wbr)(?:\s+[^<>]*=[^<>]*)?\s*/?>", re.I | re.S)  # web-page tags, comments, styles; "<Idol Booth> is" stays
JSON_ESC_RE = re.compile(r"\\u([0-9a-fA-F]{4})")  # "Rehras Sahib \u0026 Shabad"
NEEDS_TIDY_RE = re.compile("[&\ufffd<\u00c2\u00c3\u00e2\u00d0\u00fb\\\\\x80-\x9f\\[\ufb50-\ufdff\ufe70-\ufefc]|u00[c-fC-F]|\",\\s*\"")
JSON_LEFTOVER_RE = re.compile(r'",\s*"[A-Za-z]{1,20}"\s*:\s*(?:"|\{|\[|true\b|false\b|null\b|-?\d).*$', re.S)  # 'The Late Show","audioDescription":false,...'
SPORT_TAG_RE = re.compile("[\U0001F300-\U0001FAFF\u2600-\u27BF\uFE0F\u200D]+\\s*\\[[A-Za-z0-9 ]{1,15}\\]\\s*")  # "\u26bd\U0001f525 [MLS] Chicago Fire" is the drama
NEW_TAG_RE = re.compile(r"(?:\s*\[(?:NEW|LIVE)\]:?)+\s*$")
GARBLED_TAIL_RE = re.compile("[\u00fb\u00f4\u00e3\u00c2\u20ac\u0161\u0192\u02dc\u201a\u00ce]{6,}$")
ARABIC_FORMS_RE = re.compile("[\ufb50-\ufdff\ufe70-\ufefc]+")  # presentation forms many TV fonts can't draw
C1_RE = re.compile("[\x80-\x9f]")  # Windows quote marks and dashes read as Latin-1: "\x93Hello\x94"


def fix_mojibake(m):
    try:
        return bytes(ord(c) if ord(c) < 256 else c.encode("cp1252")[0] for c in m[0]).decode("utf-8")
    except (UnicodeError, ValueError):
        try:  # "â€ś": a Central European page read the same way
            return bytes(ord(c) if ord(c) < 128 else c.encode("cp1250")[0] for c in m[0]).decode("utf-8")
        except (UnicodeError, ValueError):
            return m[0]  # a real "Ã" next to other letters: leave it


def tidy_text(t):
    t = re.sub(r'\\+"', '"', t.replace("\\r\\n", "\n").replace("\\n", "\n").replace("\\t", " ").replace("\\r", ""))  # a literal "\n" from a JSON copy
    t = JSON_LEFTOVER_RE.sub("", t)
    while ESCAPED_TWICE_RE.search(t):
        t = ESCAPED_TWICE_RE.sub("&", t)
    t = CTRL_RE.sub("", ESCAPED_RE.sub(lambda m: html.unescape(m[0]) if m[1][0] == "#" or m[1] + ";" in html.entities.html5 else m[0], t))  # "&amp;#12;" is a form feed: not allowed in XML
    t = re.sub(r"(?<=\w)\ufffd(?=[a-z]\b)", "'", t).replace(" \ufffd ", " - ")
    t = t.replace("\ufffd", "")
    if JSON_ESC_RE.search(t):  # first, so escaped garbled text is repaired too; emoji pairs joined, no control characters
        t = JSON_ESC_RE.sub(lambda m: chr(int(m[1], 16)), t)
        t = CTRL_RE.sub("", t.encode("utf-16", "surrogatepass").decode("utf-16", "ignore"))
    t = C1_RE.sub(lambda m: bytes([ord(m[0])]).decode("cp1252", "ignore") or m[0], t)
    for _ in range(2):  # run by run: one real em dash must not stop the rest; twice for text garbled twice
        t = MOJIBAKE_RE.sub(fix_mojibake, t)
    t = C1_RE.sub("", t)  # control bytes nothing could repair
    t = re.sub("(?<=[.,!?:;])Â ", " ", t)  # a garbled non-breaking space: "Richmond.Â Tiger fans"
    t = LOST_U_RE.sub(lambda m: chr(int(m[1], 16)), t)
    t = GARBLED_TAIL_RE.sub("", re.sub("(?<= )\u00d0(?= )", "\u2013", t))  # a Mac dash read as "\u00d0"
    t = ARABIC_FORMS_RE.sub(lambda m: unicodedata.normalize("NFKC", m[0]), t)
    if "[" in t:
        u = re.sub(r"^\s*\[[K\u039a]\d{0,2}\]\s*", "", SPORT_TAG_RE.sub("", t))  # Greek age ratings "[K8] ..."
        u = re.sub(r"^\s*\[LIVE\]\s*:?\s*(?=\S)", "Live: ", u)
        t = NEW_TAG_RE.sub("", u) or u or t  # a title that is only "[LIVE]" keeps it
    return re.sub(r" {2,}", " ", TAG_RE.sub(" ", t)).strip() if TAG_RE.search(t) else t


RYTEC_SEP_RE = re.compile(r"\s*\u2551\s*")
RYTEC_CODE_RE = re.compile(r"S\d+(?:\s*[/:]?\s*E\d+(?:/\d+)?)?|E\d+(?:/\d+|S\d+)?|(?:Episode|Folge|Aflevering|Epizod[ae]?|Ep\.?)\s*\d+|"
                           r"\d\d[./]\d\d[./]\d{4},?\s*(?:\d\d?:\d\d\.?)?", re.I)  # leading episode codes and dates
RYTEC_DROP_RE = re.compile(r'\d{1,4}|M?\d{1,2}\+?|\d\d?\.(?:\s*\d\d?\.)*|"?(?-i:[A-Z]{1,3})"?(?:\s*,\s*(?-i:[A-Z]{1,3}))*|serie|film', re.I)  # years, ages, countries
PLAIN_GENRE_RE = re.compile(r"\s*[^\W\d_]{3,}(?:[ -][^\W\d_]{3,})?\s*")  # one or two words, no digits
RYTEC_TOK_RE = re.compile(r"\s*(?:[,/&;:]|\b(?:and|und|en|et|e|y)\b)\s*", re.I)
RYTEC_VOCAB = {}  # guide file -> (genre words, parts many different shows share)
RYTEC_ALL = [0, set()]  # every guide's genre words: "Documentary" alone is a genre in a guide that never names episodes too


def rytec_parts(text):
    parts = [p for p in (p.strip().strip("'").strip() for p in RYTEC_SEP_RE.split(text)) if p]
    while parts and RYTEC_CODE_RE.fullmatch(parts[0]):
        parts.pop(0)
    return parts


def rytec_words(part):
    return {w.lower() for w in RYTEC_TOK_RE.split(part) if w}


def rytec_learn(pairs):
    """From one guide's "S1E2 ║ name ║ genre ║ country" lines: the words used as genres, and parts shared by many shows."""
    words, firsts = {}, {}
    for title, sub in pairs:
        parts = rytec_parts(sub)
        for p in parts[1:]:
            for w in rytec_words(p):
                words.setdefault(w, set()).add(sub)
        if parts:
            firsts.setdefault(parts[0].lower(), set()).add(title)
    return {w for w, x in words.items() if len(x) >= 3}, {p for p, x in firsts.items() if len(x) >= 3}


def rytec_vocab(path):
    if path not in RYTEC_VOCAB:
        try:
            with open(path[:-4] + ".genres.json", encoding="utf-8") as f:
                g, p = json.load(f)
            RYTEC_VOCAB[path] = (set(g), set(p))
        except (OSError, ValueError):
            RYTEC_VOCAB[path] = (set(), set())
    return RYTEC_ALL[1], RYTEC_VOCAB[path][1]


def rytec_prepare(xml_sources):
    """Before a build: every guide's genre words, also after a restart or a one-guide refresh (saved files fill the gaps)."""
    paths = [os.path.join(CACHE, x["id"] + ".xml") for x in xml_sources]
    for p in paths:
        rytec_vocab(p)
    RYTEC_ALL[1] = set().union(*(RYTEC_VOCAB[p][0] for p in paths))
PRIVATE_URL_RE = re.compile(r"^\s*[a-z]+://(?:[^/@\s]*@)?(?:127\.|10\.|192\.168\.|172\.(?:1[6-9]|2\d|3[01])\.|169\.254\.|\[?::1\]?|"
                            r"(?:localhost|[^/:\s]+\.(?:local|lan|internal|home\.arpa))(?=[:/]|$))", re.I)


def tidy_show(el, vocab=(frozenset(), frozenset())):
    """Guides that escaped their text twice would show "&amp;" and diamonds on screen."""
    for child in el:
        if child.tag == "sub-title" and child.text and "\u2551" in child.text:  # "S4E20 ║ Episode 20 ║ Gameshow ║ GB ║ 2025"
            parts = rytec_parts(child.text)  # after the codes: the episode name, if there is one, then genre, country, year
            name = re.sub(r"^S\d+\s*:?\s*E\d+\s+", "", parts[0]) if parts else ""  # "S5:E2 Alte Wunden"
            genre = (not name or RYTEC_DROP_RE.fullmatch(name) or rytec_words(name) <= vocab[0] or parts[0].lower() in vocab[1] or
                     re.fullmatch(r"[^\W\d_][\w'-]*(?:\s*[,/]\s*[^\W\d_][\w'-]*)+", name))  # "Tekenfilm, Kinderen, Komedie"
            child.text = "" if genre or name.lower() == (el.findtext("title") or "").strip().lower() else name  # no name: empty, not a genre
        t = child.text
        if child.tag == "title" and t and t.endswith(" (?)"):
            t = child.text = t[:-4]  # one guide marks unsure titles with "(?)"
        if child.tag in ("title", "sub-title", "desc", "category") and t and (NEEDS_TIDY_RE.search(t) or SPORT_TAG_RE.search(t)):
            t = child.text = tidy_text(t)
        elif child.tag == "icon" and "&amp;" in child.get("src", ""):
            child.set("src", tidy_text(child.get("src")))
        if child.tag in ("title", "sub-title") and t and NEWLINE_RE.search(t):  # "Anderson Cooper 360\nEn Vivo": one line
            child.text = re.sub(r"\s+", " ", NEWLINE_RE.sub(" ", t)).strip()
    for child in el:
        if child.tag in ("title", "sub-title", "desc") and child.text and re.search(r"</[A-Za-z]|<[A-Za-z][\w:-]*\s*/>", child.text):
            child.text = ""  # escaped XML in the text ("<original-title /> ... <subevent>no</subevent>"): empty, not markup
    sub = el.find("sub-title")
    if sub is not None and sub.text and (re.fullmatch(r"\s*S\d+\s*", sub.text) or sub.text.strip().lower() in
                                         {(c.text or "").strip().lower() for c in el.findall("category")} or
                                         sub.text.strip().lower() in vocab[1] and rytec_words(sub.text.strip()) <= vocab[0]):
        sub.text = ""  # "S1", or the genre again ("Film policier"), is no episode name
    el[:] = sorted((c for c in el if c.tag in DTD_ORDER and not (  # strict players reject other tags and orders
        c.tag in ("sub-title", "desc", "category") and not (c.text or "").strip() or  # left empty by tidying
        c.tag == "icon" and (not re.match(r"https?://", c.get("src", ""), re.I) or PRIVATE_URL_RE.match(c.get("src", ""))))),
        key=lambda c: DTD_ORDER[c.tag])  # "/imgs/717.png" and a stranger's home server can't load


DTD_ORDER = {t: i for i, t in enumerate("title sub-title desc credits date category keyword language orig-language length icon "
                                        "url country episode-num video audio previously-shown premiere last-chance new "
                                        "subtitles rating star-rating review image".split())}


def clean_text(t):
    return tidy_text(CTRL_RE.sub("", t or ""))


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
                           r"^(off ?air|no data|not available|closedown|sign[- ]?off|sendepause)$|^upcoming\b|"
                           r"^beIN SPORTS, le plus grand des spectacles$|^unknown title$", re.I)


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
        if not st or (sp and (sp <= st or sp - st >= timedelta(hours=18))) or not (el.findtext("title") or "").strip():
            self.dropped += 1
            return None
        a, b = int(st.timestamp()), int((sp or st).timestamp())
        b = min(b, a + 86400)  # a few guides stretch one show over two weeks, which fills the grid with it
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


def title_key(t):  # "New: Chicago Fire" and "CHICAGO FIRE" are the same show
    t = re.sub(r"^(?:new|live|premiere)\s*[:-]\s*", "", (t or "").strip(), flags=re.I)
    return re.sub(r"\W", "", t.lower())[:8]


def same_shows(a, b):
    """Two copies with the same start times AND the same titles there (same times alone was wrong for MBC 2)."""
    x, y = (dict(zip(c.get("starts") or (), c.get("heads") or ())) for c in (a, b))
    both = x.keys() & y.keys()
    return (len(both) >= 3 and 3 * len(both) >= 2 * min(len(x), len(y)) and
            3 * sum(x[k] == y[k] for k in both) >= 2 * len(both))


def scan_xmltv(path, src=None):
    """Read a guide's channel list and check it actually has upcoming shows (times as published, clock fixes applied)."""
    idx, upcoming, last, per, langs, seen, parts, ends, starts, heads, lasts = {}, 0, None, {}, {}, {}, {}, {}, {}, {}, {}
    rytec, plain = set(), {}
    window_done = set()
    now = datetime.now(timezone.utc)
    try:
        for el in iter_xmltv(path, ("channel", "programme")):
            if el.tag == "channel":
                names = [d.text or "" for d in el.findall("display-name")]
                icon = el.find("icon")
                logo = icon.get("src", "") if icon is not None else ""  # not "src": that is the guide itself
                idx[el.get("id", "")] = {"names": names, "icon": logo if re.match(r"https?://", logo, re.I) and not PRIVATE_URL_RE.match(logo) else ""}
            else:
                end = parse_xmltv_time(el.get("stop") or el.get("start"))
                fix = timedelta(minutes=clock_fix(src, el.get("channel", ""), el.get("start") or "")) if src and end else None
                if fix:
                    end += fix
                if end and end > now and not is_junk(el):
                    upcoming += 1
                    last = max(last, end) if last else end
                    cid = el.get("channel", "")
                    per[cid] = per.get(cid, 0) + 1
                    ends[cid] = max(ends.get(cid, end), end)
                    st0 = parse_xmltv_time(el.get("start"))
                    if st0:
                        lasts[cid] = max(lasts.get(cid, 0), int((st0 + (fix or timedelta(0))).timestamp()))
                    if len(starts.setdefault(cid, [])) < 48 and cid not in window_done:  # the next day's start times,
                        st = parse_xmltv_time(el.get("start"))                              # compared with other copies
                        st = st and fix and st + fix or st
                        if st and st > now + timedelta(hours=24):
                            window_done.add(cid)
                        elif st and st > now - timedelta(hours=3):
                            starts[cid].append(int(st.timestamp()) // 60)
                            heads.setdefault(cid, []).append(title_key(el.findtext("title")))  # and their titles
                    idx.setdefault(cid, {"names": [], "icon": ""})  # some guides (Rytec) have no channel list
                    t = el.find("title")
                    sub = el.findtext("sub-title") or ""
                    if "\u2551" in sub:  # learn this guide's genre words
                        rytec.add(((el.findtext("title") or "").strip().lower(), sub))
                    elif sub and len(sub) <= 30 and PLAIN_GENRE_RE.fullmatch(sub):  # "Documentar" as the episode of every show
                        ts = plain.setdefault(sub.strip().lower(), set())
                        if len(ts) < 5:
                            ts.add((el.findtext("title") or "").strip().lower())
                    if len(seen.setdefault(cid, set())) < 2:
                        seen[cid].add((el.findtext("title") or "").strip().lower())
                    if len(parts.setdefault(cid, set())) < 3:  # a one-show channel still has different episodes
                        parts[cid].add((el.findtext("sub-title") or "") + "|" + (el.findtext("desc") or "")[:60])
                    lang = (t.get("lang") or "").lower()[:2] if t is not None else ""
                    if lang:
                        langs.setdefault(cid, {}).setdefault(lang, 0)
                        langs[cid][lang] += 1
    except Exception as ex:  # keep whatever was readable before the broken part
        log(f"  guide is partly broken ({ex}) - kept what was readable")
    for cid, info in idx.items():
        filler = len(seen.get(cid, ())) == 1 and len(parts.get(cid, ())) < 3
        info["n"] = 0 if filler else per.get(cid, 0)  # one title all day isn't a schedule: treated like a channel with no shows
        if cid in ends:
            info["end"], info["starts"], info["heads"] = int(ends[cid].timestamp()), starts.get(cid, []), heads.get(cid, [])
            info["last"] = lasts.get(cid, 0)
        if cid in langs:
            info["lang"] = max(langs[cid], key=langs[cid].get)  # upcoming shows - channels listed with no shows are skipped when matching
    fresh = bool(upcoming) and last is not None and last > now + timedelta(hours=2)
    g, p = rytec_learn(rytec) if src and src.get("id") else (set(), set())
    p |= {k for k, ts in plain.items() if len(ts) >= 5}  # one word under 5+ different shows: a genre, not an episode
    if not (src and src.get("id")):
        return idx, upcoming, fresh  # a guide being tried out: its words are not learned
    RYTEC_VOCAB[path] = (g, p)
    try:
        if g or p or os.path.exists(path[:-4] + ".genres.json"):
            write_atomic(path[:-4] + ".genres.json", json.dumps([sorted(g), sorted(p)], ensure_ascii=False))
    except OSError:
        pass
    return idx, upcoming, fresh


def index_xmltv_source(src):
    idx, upcoming, fresh = scan_xmltv(os.path.join(CACHE, src["id"] + ".xml"), src)
    if re.search(r"xmltvepg\.nl/rytec", src["url"], re.I):  # Rai 1 in Rytec's Italian guide, beIN Gurme in the German one say "de"
        for cid, info in idx.items():
            if info.get("lang") == "de" and id_country(cid) not in ("de", "at", "ch"):
                info["lang"] = ""  # unknown, not German: copies are then compared by their shows only
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
    m = re.search(r"/epg_ripper_([A-Z]{2})\d+\.xml", url)
    if m:  # epgshare's file names say the country: epg_ripper_RO1
        return {"UK": "GB"}.get(m[1], m[1])
    m = re.search(r"iptv-epg\.org/files/epg-([a-z]{2})\.xml", url)
    if m:  # and iptv-epg.org's: epg-pe.xml
        return {"UK": "GB"}.get(m[1].upper(), m[1].upper())
    name = re.sub(r"^guide linked by '.*?'", "", name)  # the playlist that linked it, not the guide's country
    text = (url.replace("i.mjh.nz", "") + " " + name).lower()  # that site's address isn't a New Zealand guide
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


BAD_CLOCK_RE = re.compile(r"epg\.pw/|/tivimate-epg/|/MyEPG/|/iptv-epg-builder/|piizitv-epg/|epg_ripper_NG|epg_ripper_BEIN1|open-epg\.com/files/(germany1|spain1)|/Robync27/personal-epg/", re.I)  # times hours off, in both directions
# guides whose clock is off for some channels: (guide link, channel code, time zone stamp, minutes to add).
# epgshare's Serbian codes stamped +0100 are an hour late (93 of 94 checked against iptv-epg.org RS; the +0000 ones are right).
# A rule stops by itself when the guide changes its stamp.
# Ghaleb's Arabic guide is an hour early on Al Aoula's main news, Jordan TV's 3 o'clock news, and on MBC 4/Action/Drama/
# Iraq, SBC and Rotana Khalijia against the UAE guide (the same shows an hour later). Roya and Oman TV were not shown wrong.
# epgshare's South African codes (+0700) are an hour late: SABC 3 "News @ 20:00" at 21:00, Uzalo and Generations too.
CLOCK_FIXES = ((re.compile(r"epgshare01\.online/.*_(?:RS1|ALL_SOURCES1)\.xml", re.I), re.compile(r"\.rs$"), "+0100", -60),
               (re.compile(r"epgshare01\.online/.*_(?:ZA1|ALL_SOURCES1)\.xml", re.I), re.compile(r"\.za$"), "+0700", -60),
               (re.compile(r"/GhalebAldoboni/EPG-Guide/", re.I),
                re.compile(r"^(?:AlAoula\.ma|Al Aoula Morocco|JordanTV\.jo|Jordan TV|MBC.*|Mbc.*|Rotana.*|SBC)$"), "+0400", 60))


def clock_fix(src, cid, start):
    z = re.search(r"([+-])(\d\d):?(\d\d)\s*$", start or "")
    zone = z and z[1] + z[2] + z[3]
    return next((m for u, c, r, m in CLOCK_FIXES if zone == r and c.search(cid) and u.search(src["url"])), 0)


NHL_FEEDS = (("SNW", re.compile(r"^Sportsnet\W?West\b", re.I)), ("SNP", re.compile(r"^Sportsnet\W{0,2}Pacific\b", re.I)),
             ("SNE", re.compile(r"^Sportsnet\W?East\b", re.I)), ("SNO", re.compile(r"^Sportsnet\W?Ontario\b", re.I)))
NHL_FIX = {}  # (guide id, channel) -> minutes, measured against the NHL's own schedule


def show_fix(src, cid, start):
    """Clock fix used when building: the fixed rules plus what the NHL check measured."""
    return clock_fix(src, cid, start) + NHL_FIX.get((src.get("id"), cid), 0)


def nhl_check(xml_sources, now):
    """Some guides kept Sportsnet's regional feeds on summer time after Nov 1, and fix it whenever they like:
    each guide's next NHL games are compared with the league's schedule, and only a clear 1-hour offset is corrected."""
    games = {}
    try:
        for day in ("now", (now + timedelta(days=7)).strftime("%Y-%m-%d")):
            for wk in json.loads(http_text(f"https://api-web.nhle.com/v1/schedule/{day}", 20)).get("gameWeek", []):
                for g in wk.get("games", []):
                    st = datetime.strptime(g["startTimeUTC"], "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)
                    for b in g.get("tvBroadcasts", []):
                        games.setdefault(b.get("network"), set()).add(int(st.timestamp()) // 60)
    except Exception as ex:
        games = None
        log(f"  NHL schedule not available ({str(ex)[:80]}) - Sportsnet times as last checked")
    memory = AUTO.setdefault("nhl_fix", {})
    NHL_FIX.clear()
    for x in xml_sources:
        try:
            with open(os.path.join(CACHE, x["id"] + ".channels.json"), encoding="utf-8") as f:
                idx = json.load(f)
        except (OSError, ValueError):
            continue
        for cid, info in idx.items():
            net = next((n for n, r in NHL_FEEDS if r.search(cid)), None)
            if not net:
                continue
            key = x["id"] + " " + cid
            hockey = [st for st, h in zip(info.get("starts", []), info.get("heads", [])) if h.startswith("nhlhock")]
            if games is not None and hockey:
                sched = games.get(net, set()) | games.get("SN", set())  # national games are on every regional feed
                hits = {d: sum(1 for st in hockey if st + d in sched) for d in (0, -60, 60)}
                best = max(hits, key=lambda d: (hits[d], d == 0))
                if hits[best]:
                    memory[key] = [best, int(time.time())]
            d, when = memory.get(key, [0, 0])
            if d and time.time() - when < 4 * 86400:  # no game in the next day: the last measurement holds for 4 days
                NHL_FIX[(x["id"], cid)] = d
    for key in [k for k, (d, when) in memory.items() if time.time() - when > 14 * 86400]:
        del memory[key]
    if NHL_FIX:
        log(f"  Sportsnet times corrected by the NHL schedule: {sorted({f'{c} {d:+d} min' for (i, c), d in NHL_FIX.items()})}")


WRONG_FEED_RE = re.compile(r"/melocalex/lighteye/|/M3UPT/|/lucianodias089/", re.I)  # every show twice 3 h apart; other countries' feeds under local codes


def picks_only(src):
    """Guides used only for channels picked by hand: never for automatic matches."""
    return src.get("picks_only") or BAD_CLOCK_RE.search(src["url"]) or WRONG_FEED_RE.search(src["url"])


def guide_sources():
    """Enabled guides that are working and up to date, priority countries first."""
    return sorted((s for s in all_sources() if s["type"] == "xmltv" and s.get("enabled", True)
                   and status_of(s).get("fresh", True)), key=priority_rank)


def load_epg_index():
    global EPG_INDEX
    new = {}
    for src in guide_sources():
        p = os.path.join(CACHE, src["id"] + ".channels.json")
        if not os.path.exists(p) or picks_only(src):
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


TIME_RE = re.compile(r"(\d{12}(?:\d\d)?)(?!\d)\s*(\S*)")
ZONE_RE = re.compile(r"(?:UTC|GMT)?([+-])(\d{1,2}):?(\d\d)?", re.I)
ZONES = {"UTC": "+0000", "GMT": "+0000", "EST": "-0500", "EDT": "-0400", "CST": "-0600", "CDT": "-0500", "MST": "-0700",
         "MDT": "-0600", "PST": "-0800", "PDT": "-0700", "BST": "+0100", "CET": "+0100", "CEST": "+0200"}


def parse_xmltv_time(s):
    m = TIME_RE.match(s or "")
    if not m:
        return None
    z = ZONE_RE.fullmatch(m[2])
    off = z[1] + z[2].zfill(2) + (z[3] or "00") if z else ZONES.get(m[2].upper(), "") if m[2] else "+0000"
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
        if cid.isdigit():
            continue  # epg.pw's numeric codes run hours off
        for n in info["names"] + ([cid.split(".")[0]] if re.fullmatch(r"[^.]+\.[a-zA-Z]{2,3}\d?", cid) else []):
            if norm(n) and cid not in lookup.setdefault(norm(n), []):
                lookup[norm(n)].append(cid)
    matched = 0
    for ch in CFG["channels"].values():
        e = effective(ch)
        if ch.get("epg_mine") or only_unmatched and e["epg_id"] in EPG_INDEX:
            continue  # a code you typed (or emptied) yourself is never replaced
        up_id = ch["up"].get("epg_id") or ""
        want = id_country(up_id) or entry_country(e["name"], e.get("group", ""), up_id)
        if not id_country(up_id) and want not in ("us", "uk", "ca"):
            want = ""  # "Shop LC" is not Saint Lucia
        cands = lookup.get(norm(e["name"]), []) if norm(e["name"]) else []
        cid = next((x for x in cands if not want or id_country(x) in (want, "")), None)  # "CCTV" in a US list is not China's CCTV 8K
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
            if re.match(r"https?://", url, re.I) and GUIDE_FILE_RE.search(urlparse(url).path) and url not in cands:
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
            idx, upcoming, fresh = scan_xmltv(tmp, {"url": url})
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
            safe_replace(tmp, os.path.join(CACHE, sid + ".xml"))
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


def provider_index(picks=False):
    """All channels of all working guides, best sources first.
    picks=True adds the guides that are only used for channels you picked by hand."""
    owner, names, src_cc, langs = {}, {}, {}, {}
    for x in guide_sources():
        if picks_only(x) and not picks:
            continue
        cc = (x.get("country") or guess_country(x["url"], x["name"])).lower()
        src_cc[x["id"]] = CC_ALIAS.get(cc, cc)
        path = os.path.join(CACHE, x["id"] + ".channels.json")
        if os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                for cid, info in json.load(fh).items():
                    if cid not in owner and info.get("n", 1):
                        owner[cid], names[cid] = x["id"], info["names"]
                        langs[cid] = info.get("lang", "")
    spellings = {}
    for cid in owner:
        spellings.setdefault(cid.lower(), []).append(cid)
    twins = {cid for v in spellings.values() if len(v) > 1 for cid in v}
    info_of = {}  # only for codes written two ways (Sixx.de / sixx.de): their start times decide below
    for sid in {owner[cid] for cid in twins}:
        with open(os.path.join(CACHE, sid + ".channels.json"), encoding="utf-8") as fh:
            info_of.update((cid, info) for cid, info in json.load(fh).items() if cid in twins and owner[cid] == sid)
    by_id = {}
    for k, v in spellings.items():  # the better-ranked spelling (SPORT1.de, not CTVU's Sport1.de an hour off),
        by_id[k] = v[0]             # unless another has the same shows at the same times and runs a day longer
        for cid in v[1:]:
            if better_copy(cid, info_of.get(by_id[k], {}), info_of.get(cid, {})):
                by_id[k] = cid
    by_code = {}
    for cid in owner:
        by_code.setdefault(code_key(cid), by_id[cid.lower()])
    by_name, by_loose, by_call, by_words, by_raw = {}, {}, {}, {}, {}
    for cid, ns in names.items():
        for n in ns or [cid.split(".")[0]]:
            k = raw_key(n)
            if not mostly_latin([n]):
                if len(k) >= 3 and cid not in by_raw.setdefault(k, []):
                    by_raw[k].append(cid)
                continue  # "ТНТ Music" is not a channel called "Music"
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


CALL_RE = re.compile(r"(?<![A-Za-z])([KW][A-Z]{3}|C[BFHIJK][A-Z]{2})(?=(?:DT\d+)?(?![A-Za-z]))")
NOT_CALLS = {"CITY", "CINE", "CLUB", "CHAT", "KICK", "WEST", "WILD", "WORD", "KIDS", "WETV", "WOOD", "WORK", "KING", "KISS", "WINE", "WALL", "WIDE", "KINO",
             "WITH", "CBBC", "CBSN"}
CALL_CODE_RE = re.compile(r"^([KW][A-Z]{3}|C[BFHIJK][A-Z]{2})(?:-?(?:DT|CD|LD|TV)\d*)?(?:\.|$)")


SAMSUNG_CC_RE = re.compile(r"^(US|GB|CA)(?=[A-Z]*\d)[A-Z0-9]{7,12}$")


def code_country(code):
    """The country a published code itself says: Samsung TV Plus 'GB1700005U8', iptv-org's UK feed '5Cops.us@UK', 'CBBC.uk@SD'."""
    m = SAMSUNG_CC_RE.match(code) or re.search(r"@(US|UK|GB|CA)$", code, re.I) or re.match(r"ee_(us|uk|ca)\.", code)  # "ee_uk.419" Sky Sports
    return {"GB": "uk"}.get(m[1].upper(), m[1].lower()) if m else id_country(code)


def call_country(code):
    """'WIVB-DT.us_locals1' is a US station, 'CHNB-DT.us_locals1' a Canadian one."""
    m = CALL_CODE_RE.match(code)
    return ("us" if m[1][0] in "KW" else "ca") if m and m[1] not in NOT_CALLS else ""


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
        if want_cc == "us" and want_net and re.search(r"\bnews\b", text) and not re.search(r"\bnews\b", pname):
            sc -= 2  # "KPTV FOX 12 Oregon News" is the station's streaming news channel, not FOX 12 itself
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
        if canada_west(c):
            return "", ""  # a label beats listings an hour off half the year
        c["shift"] = 180
        how += " (East +3h)"
    return guide, how


def canada_west(c):
    """US Pacific is always 3 h after Eastern; BC stays on UTC-7 since 2026, so no fixed number fits Canada."""
    return entry_country(c.get("name", ""), c.get("group", ""), c.get("id", "")) == "ca"


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
    named = bool(NATIONAL_RE.search(plain(c["name"])))
    intl = bool(INTL_RE.search(c["name"]))
    world = bool(WORLD_RE.search(plain(c["name"])))

    def ok(cid):  # wrong listings are worse than none
        cc = idx["cc"](cid)
        if cid.endswith(".schedulesdirect.org") and own not in ("", "us", "uk", "ca"):
            return False  # these codes say nothing of their country (Russian TNT got a Spanish schedule)
        if cid.startswith("piizi."):
            return False  # this guide's codes are scrambled (Rotana Music showed BBC News)
        if named and not world and not intl and cc in HOST_CC and cc != own:
            return False  # a national version never takes a re-shared copy from elsewhere (Russian Discovery showed German shows)
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


def rematch_provider():
    """Match every provider channel again with the newest guides and rules (your own picks stay). Needs no provider link."""
    chans = CFG.get("provider_channels") or []
    if not chans:
        return 0
    idx = provider_index()
    pidx = provider_index(picks=True)
    by_id = pidx["by_id"]
    n = 0
    for c in chans:
        if c.get("how") == "event":
            continue
        if c.get("manual"):
            pick = c.get("picked") or c.get("guide") or ""
            if pick.lower() in by_id or not pick:
                c.update(guide=pick, how="manual", shift=c.pop("picked_shift", c.get("shift", 0)))  # a West pick keeps its 3 hours
                continue
            spare = next((b for b in c.get("backups") or [] if b.lower() in by_id), "")
            c.setdefault("picked_shift", c.get("shift", 0))  # the pick's own hours, for when it returns
            west = spare and wants_west(c) and not is_west_feed(by_id[spare.lower()], pidx)
            if west and canada_west(c):
                spare = west = ""
            c.update(picked=pick, guide=spare, how="manual", shift=180 if west else 0)  # back on its pick when that returns; a label beats a wrong match
            continue
        c["guide"], c["how"] = match_provider_channel(c, idx)
        n += bool(c["guide"])
    return n


def provider_label(prov):
    """config.json is public, so channels carry a plain label; the real name stays in private.json."""
    if not prov.get("label"):
        used = {x.get("label") for x in PRIVATE["providers"]}
        prov["label"] = next(f"Provider {n}" for n in itertools.count(1) if f"Provider {n}" not in used)
        save_private()
    return prov["label"]


def refresh_provider():
    """Read your provider's channel list (on this PC only) and match every channel to a guide."""
    if not PRIVATE.get("providers"):
        return False
    entries, failed = [], set()
    for i, prov in enumerate(PRIVATE["providers"]):
        dest = os.path.join(CACHE, f"provider{i}.m3u")
        pname = prov.get("name") or f"Provider {i + 1}"
        label = provider_label(prov)
        try:
            log(f"Reading your provider list '{pname}'")
            fetch(prov["url"], dest)
            got = [e for e in parse_m3u(dest) if not re.search(r"/(movie|series)/", e["url"], re.I)]
            before = sum(1 for c in CFG["provider_channels"] if c.get("prov") == label)
            if not got or (before > 50 and len(got) < before / 2):
                raise RuntimeError(f"list came back with {len(got)} channels (had {before}) - "
                                   "login expired or provider busy?")
            for e in got:
                e["prov"] = label
                entries.append(e)
        except Exception as ex:
            log(f"  could not read '{pname}': {ex} - keeping its previous matches")
            failed.add(label)
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
            c.update({k: prev[k] for k in ("picked", "backups", "shift", "picked_shift") if k in prev})
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


FEED_CODES = {"SD": ("{b}",), "HD": ("{b}",), "East": ("{b}", "{n}East.{c}"), "Eastern": ("{b}", "{n}East.{c}"),
              "West": ("{n}West.{c}", "{n}Pacific.{c}"), "Pacific": ("{n}Pacific.{c}", "{n}West.{c}")}


def guide_code(tid):
    """'ESPN.us@SD' -> 'ESPN.us' when only the plain code has listings; a West feed only ever to a West/Pacific code."""
    if not tid or tid in EPG_INDEX or "@" not in tid:
        return tid
    base, feed = tid.split("@", 1)
    name, _, cc = base.rpartition(".")
    for pat in FEED_CODES.get(feed, ()):
        alt = pat.format(b=base, n=name, c=cc)
        if alt in EPG_INDEX:
            return alt
    return tid


def output_channels():
    active = {s["id"] for s in all_sources() if s.get("enabled", True)} | {"custom"}
    rows = []
    for ch in CFG["channels"].values():
        e = effective(ch)
        if not e["enabled"] or ch.get("missing") or ch["source"] not in active or LOGIN_URL_RE.search(e.get("url") or ""):
            continue  # someone's paid login leaked into a public list: never pass it on
        e["key"], e["extra"], e["order"] = ch["key"], ch.get("extra", []), ch["order"]
        e["tvg_id"] = guide_code(e["epg_id"]) if e["epg_id"] else "ue." + ch["key"]
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


LOGIN_URL_RE = re.compile(
    r"/(?:live|movie|series|timeshift)/[^/?#\s]+/[^/?#\s]+/\d+(?:\.\w{2,4})?(?=$|[?#])"  # Xtream: /live/<user>/<pass>/<id>.ts
    r"|^[a-z]+://[^/@\s]+:\d+/[^/?#\s]+/[^/?#\s]+/\d+(?:\.\w{2,4})?(?=$|[?#])"  # short form on a port: host:8080/<user>/<pass>/<id>
    r"|^[a-z]+://[^/@\s:]+/[^/?#\s]+/[^/?#\s]+/\d+(?:\.ts)?(?=$|[?#])"  # the same on port 80 (.m3u8 CDN paths stay)
    r"|[?&](?:username|password|user|pass)=|^[a-z]+://[^/@\s]+:[^/@\s]+@", re.I)  # get.php?username= and user:pass@host


def m3u_attr(v):
    """Playlists are not XML: keep & as-is (players match tvg-id to the guide character by character)."""
    return '"' + NEWLINE_RE.sub(" ", str(v).replace('"', "'")) + '"'


SLIM_TAGS = {"credits", "image", "rating", "star-rating", "review", "video", "audio", "previously-shown",
             "premiere", "last-chance", "subtitles", "length", "country", "keyword", "url", "language",
             "orig-language", "series-id", "live"}  # left out of the full guides to keep them small


def full_name(key):
    k = key.lower()
    return "epg-full.xml.gz" if k == "full" else f"epg-{'uk' if k in ('gb', 'uk') else k}.xml.gz"


def build():
    with LOCK:
        rows = output_channels()
        settings = dict(CFG["settings"])
        xml_sources = guide_sources()
        rytec_prepare(xml_sources)
        nhl_check(xml_sources, datetime.now(timezone.utc))
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
        m3u.append(f"#EXTINF:-1 {attrs},{NEWLINE_RE.sub(' ', e['name'])}")
        m3u.extend(e["extra"])
        m3u.append(e["url"])
    tmp = os.path.join(OUT, "playlist.m3u.tmp")
    with open(tmp, "w", encoding="utf-8") as f:
        f.write("\n".join(m3u) + "\n")
    safe_replace(tmp, os.path.join(OUT, "playlist.m3u"))

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
        needed = {owner[cid] for cid in real if cid in owner}
        for src in xml_sources:
            path = os.path.join(CACHE, src["id"] + ".xml")
            if src["id"] not in needed or not os.path.exists(path):
                continue
            here = set()
            try:
                for el in iter_xmltv(path, ("programme",)):
                    cid = el.get("channel", "")
                    if cid not in real or cid in claimed or owner.get(cid) != src["id"] or is_junk(el):
                        continue
                    st, sp = parse_xmltv_time(el.get("start")), parse_xmltv_time(el.get("stop"))
                    fix = st and show_fix(src, cid, el.get("start"))
                    if fix:
                        st, sp = st + timedelta(minutes=fix), sp and sp + timedelta(minutes=fix)
                    if not st or (sp or st) < start_cut or st > end_cut:
                        continue
                    tidy_show(el, rytec_vocab(path))  # first: a title that tidying empties is no show
                    times = clean.check(cid, el, st, sp)
                    if not times:
                        continue
                    el.set("start", fmt_xmltv_time(times[0]))  # always a full time with its zone
                    if sp:
                        el.set("stop", fmt_xmltv_time(times[1]))
                    else:
                        el.attrib.pop("stop", None)  # "20261104176000": players reject it
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
    safe_replace(tmp, os.path.join(OUT, "epg.xml"))
    with open(os.path.join(OUT, "epg.xml"), "rb") as src, gzip.open(os.path.join(OUT, "epg.xml.gz.tmp"), "wb") as dst:
        shutil.copyfileobj(src, dst, 1 << 20)
    safe_replace(os.path.join(OUT, "epg.xml.gz.tmp"), os.path.join(OUT, "epg.xml.gz"))
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
    for x in sorted(xml_sources, key=lambda x: bool(picks_only(x))):
        path = os.path.join(CACHE, x["id"] + ".channels.json")
        if os.path.exists(path):
            with open(path, encoding="utf-8") as fh:
                for cid, info in json.load(fh).items():
                    if cid not in owner and info.get("n", 1):
                        owner[cid] = x["id"]
    return owner


def event_is_over(name, now):
    """Event names can carry a date ("... Oct 30 01:00 AM") that is long gone when your PC stays off."""
    m = re.search(r"\b(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)(?:uary|ruary|ch|il|e|y|ust|tember|t|ober|ember)?\.?\s+(\d{1,2})\b", name, re.I)
    try:
        if m:
            month = "jan feb mar apr may jun jul aug sep oct nov dec".split().index(m[1].lower()) + 1
            when = datetime(now.year, month, int(m[2]), tzinfo=timezone.utc)
            if when > now + timedelta(days=180):  # December's event seen in January
                when = when.replace(year=now.year - 1)
            elif when < now - timedelta(days=180):  # January's event seen in December
                when = when.replace(year=now.year + 1)
        else:
            m = re.search(r"\b(\d{4})-(\d\d)-(\d\d)\b", name)
            when = m and datetime(int(m[1]), int(m[2]), int(m[3]), tzinfo=timezone.utc)
    except ValueError:
        return False
    if not when:
        return False
    t = re.search(r"\b(\d{1,2}):(\d\d)\s*([AP]M)?\s*(ET|EST|EDT|CT|CST|CDT|MT|MST|MDT|PT|PST|PDT|UK|GMT|UTC)?\b",
                  name[m.end():], re.I)
    if not t:  # no time: a late-evening game in America ends after midnight UTC
        return when < now - timedelta(hours=36)
    hour = int(t[1]) % 12 + (12 if (t[3] or "").upper() == "PM" else 0) if t[3] else int(t[1])
    zone = (t[4] or "ET").upper()[:1]  # no zone: American event lists use Eastern time
    behind = {"E": 5, "C": 6, "M": 7, "P": 8}.get(zone, 0)  # standard time: in summer this says over an hour late, never early
    start = when + timedelta(hours=hour + behind, minutes=int(t[2]))
    return start < now - timedelta(hours=6)


def write_placeholder(f, cid, title, desc, now, end_cut, stop_at=None, start_at=None):
    block = timedelta(hours=max(1, int(CFG["settings"]["dummy_hours"])))
    hours = int(block.total_seconds() // 3600)
    t = now.replace(minute=0, second=0, microsecond=0) - timedelta(hours=now.hour % hours)
    n = 0
    while t < min(end_cut, stop_at or end_cut):
        stop = min(t + block, stop_at) if stop_at else t + block  # never on top of the first real show
        begin = max(t, start_at) if start_at else t  # ...nor on top of the last one that already ran
        if stop > begin:
            f.write(f'<programme start="{fmt_xmltv_time(begin)}" stop="{fmt_xmltv_time(stop)}" '
                    f'channel={quoteattr(cid)}><title>{escape(clean_text(title))}</title>'
                    + (f'<desc>{escape(clean_text(desc))}</desc>' if desc else '') + '</programme>\n')
            n += 1
        t += block
    return n


NO_SCHEDULE = "This channel doesn't publish a schedule."
NOT_YET = "Listings for this time aren't published yet."
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


MORNING_RE = re.compile(r"good morning america|cbs mornings|today", re.I)
NETWORK_SHOWS = {"ABC": r"good morning america|world news|the view|general hospital|this week|gma",
                 "NBC": r"^today|nightly news|meet the press|sunday night football|tonight show|access hollywood",
                 "CBS": r"cbs |face the nation|young and the restless|price is right|60 minutes|the talk|bold and the beautiful"}
NETWORK_CHANGED = re.compile(r"KRQE|WIAT|WJTV|WGCL|KDNL|WPLG|WSPA")  # every guide agrees, with the station's own news: they left the network the provider's name says
SPANISH_RE = re.compile(r"\b(el|la|los|las|del|una|noticias|película|programa pagado)\b|[ñ¿¡]", re.I)


def guide_health(path, base_url):
    """What the finished light guide really shows per provider channel: anything that looks wrong goes in a public report."""
    chans = [c for c in CFG.get("provider_channels") or [] if c.get("how") != "event"]
    titles, labels, details, mornings, last = {}, set(), {}, {}, {}
    with gzip.open(path, "rb") as fh:
        for _, el in ET.iterparse(fh, events=("end",)):
            if el.tag == "programme":
                if NO_SCHEDULE in (el.findtext("desc") or ""):
                    labels.add(el.get("channel"))
                elif NOT_YET in (el.findtext("desc") or ""):
                    pass
                else:
                    titles.setdefault(el.get("channel"), []).append(el.findtext("title") or "")
                    last[el.get("channel")] = max(last.get(el.get("channel"), ""), (el.get("stop") or el.get("start") or "")[:14])
                    details.setdefault(el.get("channel"), set()).add((el.findtext("sub-title") or "") + (el.findtext("desc") or "")[:60])
                    if MORNING_RE.fullmatch((el.findtext("title") or "").strip()):
                        mornings.setdefault(el.get("channel"), []).append(int(el.get("start")[8:10]))
            if el.tag in ("programme", "channel"):
                el.clear()
    report = {"time": int(time.time()), "channels": len(chans), "with_shows": 0, "labels": 0, "blank": [], "wrong_network": [],
              "wrong_language": [], "wrong_time": [], "name_only": [], "picks_waiting": [], "on_backup": [], "runs_out": []}
    soon = time.strftime("%Y%m%d%H%M%S", time.gmtime(time.time() + 12 * 3600))
    for c in chans:
        shown, name = titles.get(c["id"]), c["name"]
        if c.get("picked") and c["picked"] != c.get("guide"):
            report["on_backup" if c.get("guide") else "picks_waiting"].append(name)
        if not shown:
            report["labels" if c["id"] in labels else "blank"] += 1 if c["id"] in labels else [name]
            continue
        report["with_shows"] += 1
        if last.get(c["id"], "") < soon:
            report["runs_out"].append(name)
        net = next((n for n in NETWORK_SHOWS if name.startswith(n + " (") and not NETWORK_CHANGED.search(name)), None)
        hours = mornings.get(c["id"])  # UTC: 6am in the east to 7am in Hawaii
        if net and hours and not any(10 <= h <= 18 for h in hours):
            report["wrong_time"].append(name)
        if len({t.strip().lower() for t in shown}) <= 1 and len(details.get(c["id"], ())) < 3:
            report["name_only"].append(name)
        elif net and not any(re.search(NETWORK_SHOWS[net], t, re.I) for t in shown):
            report["wrong_network"].append(name)
        elif (c["group"] in ("US", "UK", "Canada") or re.search(r" (US|UK|CA)$", name)) and not re.search(
                r"espa|latin|pelicula|tele|uni|caracol|wapa|tudn|azteca|estrella|\bcr\b|\bmx\b", name, re.I)                 and sum(bool(SPANISH_RE.search(t)) for t in shown) > len(shown) * 0.6:
            report["wrong_language"].append(name)
    with open(os.path.join(OUT, "playlist.m3u"), encoding="utf-8") as fh:
        playlist = report["playlist"] = sum(line.startswith("#EXTINF") for line in fh)
    try:
        for attempt in range(3):
            try:
                with urllib.request.urlopen(base_url + "/health.json", timeout=30) as r:
                    old = json.load(r)
                break
            except (OSError, ValueError):
                if attempt == 2:
                    raise
                time.sleep(10)
        report["lost_since_last_run"] = old["with_shows"] - report["with_shows"]
        report["new"] = {k: [n for n in report[k] if n not in old.get(k, [])]
                         for k in ("picks_waiting", "blank", "wrong_network", "wrong_language", "wrong_time")}
        report["playlist_lost"] = old.get("playlist", playlist) - playlist
        week = [r for r in old.get("recent") or AUTO.get("health_recent", []) if report["time"] - r[0] < 7 * 86400]
        report["recent"] = week + [[report["time"], report["with_shows"]]]
        report["lost_this_week"] = max(r[1] for r in report["recent"]) - report["with_shows"]
        before = old.get("lost_this_week", AUTO.get("health_lost_week", 0 if old.get("recent") else 150))  # no history last time: it may have alerted already
        report["new_weekly_loss"] = report["lost_this_week"] >= 150 and before < 150
    except Exception as ex:
        report["recent"] = [r for r in AUTO.get("health_recent", []) if report["time"] - r[0] < 7 * 86400] + [
            [report["time"], report["with_shows"]]]
        report["lost_since_last_run"] = report["playlist_lost"] = 0
        report["lost_this_week"] = max(r[1] for r in report["recent"]) - report["with_shows"]
        report["new_weekly_loss"] = report["lost_this_week"] >= 150 and AUTO.get("health_lost_week", 150) < 150
        report["new"] = {}
        report["no_comparison"] = not (isinstance(ex, urllib.error.HTTPError) and ex.code == 404)  # a brand-new site has none yet
    return report


def health_alert(r):
    """The text of the email, or '' when nothing has got worse since the last update."""
    def names(n):
        n = sorted(n)
        return ", ".join(n[:40]) + (f" and {len(n) - 40} more" if len(n) > 40 else "")
    lines = [f"- {title}: {names(r['new'][key])}" for title, key in
             (("Picked guide ran out", "picks_waiting"), ("No shows and no label", "blank"),
              ("Local station without its network's shows", "wrong_network"),
              ("Mostly Spanish listings on an English channel", "wrong_language"),
              ("Morning show at the wrong hour", "wrong_time")) if r["new"].get(key)]
    if r["lost_since_last_run"] >= 100:
        lines.insert(0, f"- {r['lost_since_last_run']} channels lost their listings since the last update")
    elif r.get("new_weekly_loss"):
        lines.insert(0, f"- {r['lost_this_week']} channels lost their listings over the last few days")
    if r.get("playlist_lost", 0) >= 100:
        lines.insert(0, f"- The public playlist lost {r['playlist_lost']} channels since the last update")
    if r.get("no_comparison"):
        lines.append("- The health report couldn't compare with the last update")
    return chr(10).join(lines)


def health_page(r):
    rows = "".join(f"<h2>{escape(title)} ({len(r[key])})</h2><p>{escape(', '.join(sorted(r[key]))) or 'None'}</p>" for title, key in
                   (("Picked guide ran out, showing a label", "picks_waiting"), ("Picked guide ran out, using its backup", "on_backup"),
                    ("No shows and no label", "blank"), ("Local station without its network's shows", "wrong_network"),
                    ("Mostly Spanish listings on an English channel", "wrong_language"), ("Morning show at the wrong hour", "wrong_time"),
                    ("One title all day", "name_only"), ("Listings run out within 12 hours", "runs_out")))
    return (f'<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>Guide health</title>'
            f'<body style="font:16px system-ui;max-width:760px;margin:40px auto;padding:0 16px"><h1>Guide health</h1>'
            f'<p>{r["with_shows"]} of {r["channels"]} channels have listings, {r["labels"]} show a label. '
            f'Change since the last update: {-r["lost_since_last_run"]:+d}.</p>{rows}'
            f'<p style="color:#777">Checked {time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime(r["time"]))}</p>')


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


LANG_OF = {"us": "en", "uk": "en", "au": "en", "nz": "en", "ie": "en", "hr": "hr", "rs": "sr", "si": "sl", "de": "de",
           "at": "de", "es": "es", "mx": "es", "ar": "es", "co": "es", "cl": "es", "pe": "es", "pt": "pt", "br": "pt",
           "fr": "fr", "it": "it", "pl": "pl", "ro": "ro", "nl": "nl", "se": "sv", "dk": "da", "fi": "fi", "gr": "el",
           "tr": "tr", "hu": "hu", "cz": "cs", "sk": "sk", "bg": "bg", "ru": "ru"}
LANG_ALIAS = {"se": "sv", "dk": "da", "gr": "el", "cz": "cs", "rs": "sr", "si": "sl"}


def better_copy(cid, old, new):
    """The same code in two guides: the first guide wins, unless it is in another country's language and the other
    copy (really a different schedule) is in the right one - RTL.hr in German - or the other copy has the same shows
    at the same times and runs at least a day longer."""
    a, b = set(old.get("starts") or ()), set(new.get("starts") or ())
    same_times = len(a & b) >= 3 and 3 * len(a & b) >= 2 * min(len(a), len(b))
    same = same_times and (same_shows(old, new) if old.get("heads") and new.get("heads") else True)  # JBS.us: a crime channel's shows
    want = LANG_OF.get(id_country(cid), "")
    lo, ln = (LANG_ALIAS.get(x[:2], x[:2]) for x in (old.get("lang") or "", new.get("lang") or ""))
    if want and lo not in ("", "en", want) and ln == want and a and b and not same_times:  # many guides tag every show "en": not a sign
        return True
    return same and (lo == ln or not lo or not ln) and new.get("end", 0) >= old.get("end", 0) + 86400


def build_universal(xml_sources, wanted, now, start_cut, end_cut):
    rytec_prepare(xml_sources)
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
    prov_ids = {c["id"] for c in CFG.get("provider_channels") or [] if c.get("guide")}
    for c in CFG.get("provider_channels") or []:
        if c.get("guide"):
            learned.setdefault(c["id"], (c["guide"], []))[1].append(c["name"])
            if c.get("shift"):
                shifts[c["id"]] = c["shift"]
        elif c.get("how") == "event":
            events.append(c)
    for ch in CFG["channels"].values():
        if ch.get("missing"):
            continue  # gone from its playlist: its code may belong to another channel now
        up, e = ch["up"], effective(ch)
        if up.get("epg_id") and e.get("epg_id") and up["epg_id"] != e["epg_id"]:
            learned.setdefault(up["epg_id"], (e["epg_id"], []))[1].append(e["name"])
    hand = {c["guide"] for c in CFG.get("provider_channels") or [] if c.get("manual") and c.get("guide")}
    spare = {b for c in CFG.get("provider_channels") or [] if c.get("manual") for b in c.get("backups") or []}
    hand |= {effective(ch)["epg_id"] for ch in CFG["channels"].values()
                                               if ch.get("epg_mine") and effective(ch)["epg_id"]}
    targets = hand | spare | {g for g, _ in learned.values()} | set(wanted)  # your own playlist's guides come along too
    prov = [c for c in CFG.get("provider_channels") or [] if c.get("id")]
    lite_codes = {c["id"] for c in prov} | set(learned)  # light guide: just the channels your providers carry
    prov_cc = {c["id"]: entry_country(c["name"], c.get("group", ""), c["id"]) or  # "Sky Sports Main Event" in "Sports": its guide says UK
               (lambda g: g if g in ("us", "uk", "ca") else "")(code_country(c.get("guide") or "")) for c in prov}

    pri_cc = {"uk" if c.lower() in ("gb", "uk") else c.lower() for c in priority_list()}
    chans = {}
    for x in sorted(xml_sources, key=lambda x: bool(picks_only(x))):  # the same code in a reliable guide wins
        in_pri = priority_rank(x) < n_pri or x.get("name", "").startswith("guide linked by")  # the universal guide keeps them
        xcc = guess_country(x["url"], x["name"]).lower()
        xcc = CC_ALIAS.get(xcc, xcc)
        path = os.path.join(CACHE, x["id"] + ".channels.json")
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as fh:
            for cid, info in json.load(fh).items():
                if not info.get("n", 1) or not (in_pri or cid in targets or (not xcc and "epgshare01" in x["url"] and id_country(cid) in pri_cc)):
                    continue
                if picks_only(x) and cid not in hand:
                    continue  # only the channels you picked from it, never its other listings
                if cid in chans and (picks_only(x) or chans[cid]["picks"] or not better_copy(cid, chans[cid], info)):
                    continue
                chans[cid] = {"src": x["id"], "names": [n for n in info["names"] if n] or [cid],
                              "icon": info.get("icon", ""), "n": info.get("n", 1), "picks": bool(picks_only(x)),
                              "cc": id_country(cid) or xcc, "lang": info.get("lang", ""),
                              "end": info.get("end", 0), "starts": info.get("starts", []), "heads": info.get("heads", []),
                              "last": info.get("last", 0)}

    # group the copies of each real-world channel
    clusters = {}
    for cid, c in chans.items():
        text = " ".join(c["names"]) + " " + re.sub(r"[._]", " ", cid)
        calls = sorted(callsigns(text))
        if calls:  # "CW KIFIDT3" is KIFI's third channel, often another network: a group of its own
            sub = re.search(rf"(?<![A-Za-z]){calls[0]}-?DT(\d+)", text)
            key = ("call", calls[0], sub[1] if sub and sub[1] != "1" else "")
        else:
            raw = PROVIDER_PREFIX_RE.sub("", unescape_all(c["names"][0]).lower())
            w = re.search(r"\b(pacific|west)\b", raw + " " + cid.lower())
            west = (w[1] if c["cc"] == "ca" else True) if w else False  # Sportsnet West and Pacific are two feeds
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
        group = {"names": names, "seen": seen, "icon": icon, "cc": chans[best]["cc"], "best": best, "cids": cids, "call": key[0] == "call"}
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
        if code not in out or (code in prov_ids and (code != g or shifts.get(code))):  # the provider's pick wins
            out[code] = {"from": g if chans[g]["n"] else group["best"], "group": group,
                         "shift": shifts.get(code, 0)}
    def is_call(t):
        text = " ".join(chans[t]["names"]) + " " + t
        if re.search(r"(?<![A-Za-z0-9])[KW]\d\d[A-Z]{2}(?:-?(?:D|LD|CD))?\b", text):
            return True
        return chans[t]["group"].get("call") or bool(callsigns(re.sub(r"(?<=[A-Z]{4})DT\b", " ", " ".join(chans[t]["names"]) + " " + re.sub(r"[._]", " ", t))))
    def per_day(t):
        return chans[t]["n"] * 86400 / max(43200, chans[t]["end"] - now.timestamp())
    by_start = None
    backups_of = {c["guide"]: c.get("backups") or [] for c in prov if c.get("manual") and c.get("guide")}
    for o in out.values():  # TNT Sports 1 ran out at 3 pm while a copy with the same shows ran two days: use the longer one
        k = o["from"]
        if not k or chans[k]["picks"]:
            continue
        if k in hand:  # hand picks: only from the owner's own backups, and only with the same shows
            twin = max((t for t in backups_of.get(k, ()) if t in chans and chans[t]["n"] and not chans[t]["picks"] and
                        chans[t]["end"] >= chans[k]["end"] + 43200 and per_day(t) >= 0.8 * per_day(k) and same_shows(chans[k], chans[t])),
                       key=lambda t: chans[t]["end"], default=None)
            if twin:
                o["ext"] = (twin, datetime.fromtimestamp(max(chans[k]["end"], chans[k].get("last", 0) + 60), timezone.utc))
            continue
        twin = max((t for t in o["group"].get("cids", ()) if t != k and chans[t]["n"] and not chans[t]["picks"] and
                    chans[t]["end"] >= chans[k]["end"] + 43200 and per_day(t) >= 0.8 * per_day(k) and same_shows(chans[k], chans[t])),
                   key=lambda t: chans[t]["end"], default=None)
        if not twin and not is_call(k) and chans[k]["end"] < (now + timedelta(days=WEEK_DAYS)).timestamp() - 43200 and len(chans[k]["starts"]) >= 12 and len(chans[k].get("heads") or ()) == len(chans[k]["starts"]):
            if by_start is None:  # built once, only from copies that run long
                by_start = {}
                for t, c in chans.items():
                    if c["n"] and not c["picks"] and c.get("heads") and c["end"] > now.timestamp() + 36 * 3600:
                        for m0 in c["starts"]:
                            by_start.setdefault(m0, []).append(t)
            mine = dict(zip(chans[k]["starts"], chans[k]["heads"]))
            hits = {}
            for m0 in mine:
                for t in by_start.get(m0, ()):
                    hits[t] = hits.get(t, 0) + 1
            twin = max((t for t, n in hits.items() if n == len(mine) and t != k and chans[t]["cc"] == chans[k]["cc"] and not is_call(t) and
                        chans[t]["end"] >= chans[k]["end"] + 43200 and per_day(t) >= 0.8 * per_day(k) and
                        all(dict(zip(chans[t]["starts"], chans[t]["heads"])).get(m0) == h for m0, h in mine.items())),
                       key=lambda t: chans[t]["end"], default=None)
        if twin:
            o["ext"] = (twin, datetime.fromtimestamp(max(chans[k]["end"], chans[k].get("last", 0) + 60), timezone.utc))  # from here on
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
        own0 = code_country(code)
        k = "" if own0 and own0 not in ("us", "uk", "gb", "ca") else file_key(prov_cc.get(code) or "")
        if k not in files:  # "Monroe LA" is Louisiana, not Laos: back to the guide's own country
            cc = out[code]["group"]["cc"]
            own = code_country(code)  # "CBBC.uk@SD" says its country, even under a US playlist's guide
            k = file_key(own if own and (code in chans or own in ("us", "uk", "gb", "ca")) else
                         (cc in ("us", "ca", "") and not own and call_country(code)) or cc or "")
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
    fill, ext = {}, {}
    for code, o in out.items():
        if o["from"]:
            fill.setdefault(o["from"], []).append(code)
        if o.get("ext"):
            ext.setdefault(o["ext"][0], []).append((code, o["ext"][1]))

    shows, live_from, live_soon, nxt, clean, ended, last_stop = 0, set(), set(), {}, ShowCleaner(), {}, {}
    needed = {chans[cid]["src"] for cid in list(fill) + list(ext) if cid in chans}
    for x in xml_sources:
        path = os.path.join(CACHE, x["id"] + ".xml")
        if x["id"] not in needed or not os.path.exists(path):
            continue
        try:
            for el in iter_xmltv(path, ("programme",)):
                cid = el.get("channel", "")
                if (cid not in fill and cid not in ext) or chans.get(cid, {}).get("src") != x["id"] or is_junk(el):
                    continue
                st, sp = parse_xmltv_time(el.get("start")), parse_xmltv_time(el.get("stop"))
                fix = st and show_fix(x, cid, el.get("start"))
                if fix:
                    st, sp = st + timedelta(minutes=fix), sp and sp + timedelta(minutes=fix)
                if not st or (sp or st) < start_cut or st > week_cut:
                    continue
                for child in list(el):
                    if child.tag in SLIM_TAGS:
                        el.remove(child)
                tidy_show(el, rytec_vocab(path))  # first: a title that tidying empties is no show
                times = clean.check(cid, el, st, sp)
                if not times:
                    continue
                st, sp = times
                el.set("start", fmt_xmltv_time(st))  # always a full time with its zone
                if sp:
                    el.set("stop", fmt_xmltv_time(sp))
                else:
                    el.attrib.pop("stop", None)  # "20261104176000": players reject it
                el.tail = "\n"
                for code in fill.get(cid, []) + [c for c, after in ext.get(cid, ()) if st >= after]:
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
                if sp:
                    last_stop[cid] = max(last_stop.get(cid, sp), sp)
                if (sp or st) <= now:
                    ended[cid] = max(ended.get(cid, st), sp or st)
                if (sp or st) > now:
                    nxt[cid] = min(nxt.get(cid, st), st)
                    if st <= now + timedelta(hours=6):
                        live_soon.add(cid)
        except Exception as ex:  # one broken guide never stops the others
            log(f"Guide '{x['name']}' could not be fully read ({ex}); kept what was readable")
    for code, o in out.items():  # placeholders so nothing shows "No information"
        e = o.get("placeholder")
        mine = [k for k in (o["from"], (o.get("ext") or (None,))[0]) if k]
        if e and CFG["settings"]["dummy_epg"] and not any(k in live_soon for k in mine):  # a match day next week
            text = []

            class W:
                def write(self, t):
                    text.append(t)
            later = min((nxt[k] for k in mine if k in live_from and k in nxt), default=None)  # a match day next week: label until then
            done = max((ended[k] for k in mine if k in ended), default=None)
            done = done and done + timedelta(minutes=o.get("shift") or 0)
            if later:
                later += timedelta(minutes=o.get("shift") or 0)
            write_placeholder(W(), code, e["name"], e["desc"] or f"{e['name']} - live 24/7", now, end_cut,
                              later or None, done)
            near = len(text)
            write(code, "".join(text))
            text.clear()
            if not any(k in live_from for k in mine):  # real shows later in the week: no label on top of them
                write_placeholder(W(), code, e["name"], e["desc"] or f"{e['name']} - live 24/7", now, week_cut, None, done)
                write(code, "".join(text[near:]), True)
        if e and CFG["settings"]["dummy_epg"] and any(k in last_stop and k in nxt for k in mine):  # Clubland's guide ends 5 hours ahead
            gap = max(last_stop[k] for k in mine if k in last_stop) + timedelta(minutes=o.get("shift") or 0)
            if gap < end_cut - timedelta(hours=1):
                buf = []
                write_placeholder(type("Buf", (), {"write": lambda self, t: buf.append(t)})(), code, e["name"], NOT_YET,
                                  now, end_cut, None, gap)
                write(code, "".join(buf))

    log(f"Cleaned out {clean.dropped} duplicate/overlapping/empty shows")
    sizes = []
    for k, fh in files.items():
        fh.write("</tv>\n")
        fh.close()
        safe_replace(os.path.join(OUT, full_name(k) + ".tmp"), os.path.join(OUT, full_name(k)))
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
    def dest_of(src):
        return os.path.join(CACHE, src["id"] + (".m3u" if src["type"] == "m3u" else ".xml"))
    todo = [s for s in list(all_sources()) if s.get("enabled", True) and (not only or s["id"] in only)]
    log(f"Downloading {len(todo)} sources")
    failed = download_all(todo, dest_of)
    log(f"Downloads finished, {len(failed)} failed")
    for src in todo:
        st = status_of(src)
        try:
            log(f"Reading {src['type'].upper()} '{src['name']}'")
            dest = dest_of(src)
            if src["id"] in failed:
                raise failed[src["id"]]
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
    lock = os.path.join(BASE, ".git", "index.lock")  # left behind by a crash or power cut
    if os.path.exists(lock) and time.time() - os.path.getmtime(lock) > 600:
        os.remove(lock)
    r = subprocess.run(["git", *args], cwd=BASE, capture_output=True, text=True, timeout=300,
                       creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
    if check and r.returncode:
        raise RuntimeError((r.stderr or r.stdout).strip())
    return r.stdout.strip()


def xml_ok(path):
    parser = xml.parsers.expat.ParserCreate()
    try:
        with gzip.open(path, "rb") as fh:
            while chunk := fh.read(1 << 20):
                parser.Parse(chunk, False)
            parser.Parse(b"", True)
        return True
    except (xml.parsers.expat.ExpatError, OSError, EOFError, zlib.error):
        return False


def build_site(outdir, base_url):
    """Used by the GitHub Action: download everything, build, write a static site."""
    base_url = base_url.rstrip("/")
    before = json.dumps(AUTO)
    refresh()
    used = {s["id"] for s in CFG["sources"] + AUTO["sources"]}
    for f in os.listdir(CACHE):  # sources taken out by hand: their copies only fill the server's disk
        if f.split(".")[0] not in used and not f.startswith(("provider", "candidate")):
            os.remove(os.path.join(CACHE, f))
    build()
    sizes = {f: os.path.getsize(os.path.join(OUT, f)) for f in os.listdir(OUT)
             if re.fullmatch(r"epg(-[a-z]+)?\.xml\.gz|playlist\.m3u", f)}
    for f in sizes:
        if f.endswith(".gz") and not xml_ok(os.path.join(OUT, f)):
            log(f"{f} is not readable XML - not publishing it")
            sizes[f] = 0  # one bad character makes a whole guide unreadable in strict players
    last = AUTO.get("good_sizes") or {}
    built = {"epg.xml.gz", "playlist.m3u"} | ({full_name(k) for k in ["full", "lite", "week"] + priority_list()}
                                               if CFG["settings"].get("full_guide") else set())
    sizes.update({f: 0 for f in last if f not in sizes and f in built})  # a missing file is a failed file
    last = {f: n for f, n in last.items() if f in built}  # a country you took off the list is not a failure
    small = [f for f, n in sizes.items() if n < 5000 or n < last.get(f, 0) * 0.5]
    since = AUTO.get("guard_since") or time.time()
    if small and time.time() - since < 24 * 3600:  # most channels in the online guide run 2 days (some free ones only hours), so there is time to wait
        reason = ", ".join(f"{f} {sizes[f]} bytes (last good {last.get(f, 0)})" for f in small)
        AUTO.clear()
        AUTO.update(json.loads(before))  # a bad run changes nothing, except remembering it happened
        AUTO["guard_since"] = since
        save_auto()
        raise SystemExit(f"Guide came out far too small: {reason} - keeping the previous online guide")
    if any(sizes[f] < 5000 for f in small):
        raise SystemExit(f"A guide is missing or nearly empty: {small} - keeping the previous online guide")
    if small:
        log("Guide stayed small for a whole day - accepting it as the new normal")
    else:  # falls slowly, so many small drops in a row still trip the check
        sizes = {f: max(n, int(last.get(f, 0) * 0.9)) for f, n in sizes.items()}
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
                f'<h1>My EPG</h1>{links}<p><a href="{base_url}/health.html">Guide health report</a></p><p style="color:#777">Updated {time.strftime("%Y-%m-%d %H:%M UTC", time.gmtime())}</p>')
    try:  # the report never stops your links going out
        health = guide_health(os.path.join(OUT, "epg-lite.xml.gz"), base_url)
        AUTO["health_recent"], AUTO["health_lost_week"] = health.get("recent", []), health.get("lost_this_week", 0)
        save_auto()
        with open(os.path.join(outdir, "health.json"), "w", encoding="utf-8") as f:
            json.dump(health, f, ensure_ascii=False)
        with open(os.path.join(outdir, "health.html"), "w", encoding="utf-8") as f:
            f.write(health_page(health))
        alert = health_alert(health)
        if alert:
            with open(os.path.join(BASE, "alert.md"), "w", encoding="utf-8") as f:
                print(alert, file=f)
    except Exception as ex:
        log(f"Guide health report failed: {ex}")
        with open(os.path.join(BASE, "alert.md"), "a", encoding="utf-8") as f:
            print(f"- The guide health report failed: {ex}", file=f)
    print(f"Site written to {outdir}")


def sync_from_github():
    """Fetch guides GitHub found on its own (the online copy of auto_sources.json wins)."""
    global AUTO
    with SAVE_LOCK:
        git("reset", "-q", "--", "data/auto_sources.json", check=False)
        git("checkout", "--", "data/auto_sources.json", check=False)
        if git("status", "--porcelain", "data/config.json", check=False):  # as a commit, a clash stops the pull instead of
            git("add", "data/config.json")                                # leaving <<<<<<< marks in config.json
            git("commit", "-q", "-m", "Update channels and sources")
        try:
            git("pull", "-q", "--rebase", "--autostash", "origin", "main")
        except Exception:
            git("rebase", "--abort", check=False)  # never leave a half-merged, unreadable config behind
            raise
        clash = git("diff", "--name-only", "--diff-filter=U", check=False)
        if clash:  # an autostashed file clashed: git still says "ok", the stash keeps your copy
            raise RuntimeError(f"GitHub's copy clashes with your changes in {clash} - your changes are in 'git stash list'")
        fresh, config = load_auto(), load_config()
        adopt(AUTO, fresh)  # same objects: running jobs keep working on them
        with LOCK:  # or an older copy in memory would undo the fixes just pulled
            adopt(CFG, config)
    load_epg_index()


def publish():
    """Push the current sources + channel edits to GitHub; the Action rebuilds from them."""
    if not os.path.isdir(os.path.join(BASE, ".git")):
        raise RuntimeError("Not online yet - set up GitHub in the app first.")
    if git("rev-parse", "--abbrev-ref", "HEAD", check=False) != "main":
        raise RuntimeError("Not on the main branch - switch back with: git checkout main")
    save_config()  # changes still only in memory go out too
    git("add", "data/config.json")
    if git("status", "--porcelain", "data/config.json"):
        git("commit", "-m", "Update channels and sources")
    sync_from_github()
    git("push", "-q", "origin", "refs/heads/main:refs/heads/main")
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
                "per": {x.get("name", "Provider"): sum(1 for c in CFG["provider_channels"] if c.get("prov") == x.get("label"))
                        for x in PRIVATE.get("providers", [])},
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
            if "epg_id" in it:
                ch["epg_mine"] = True
            if it.get("reset"):
                ch["ov"] = {}
                ch.pop("epg_mine", None)
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
        before = {s["id"]: s for s in CFG["sources"]}
        clean = []
        for s in sources:
            if not s.get("url"):
                continue
            sid = str(s.get("id") or "")
            sid = sid if re.fullmatch(r"[A-Za-z0-9_-]{1,32}", sid) else uuid.uuid4().hex[:8]
            clean.append({**before.get(sid, {}), "id": sid,  # keeps picks_only and the like
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

    def from_this_pc(self):
        """Players on the network may read the playlist and guide; only this PC may use the editor."""
        host = (self.headers.get("Host") or "").rsplit(":", 1)[0].lower()
        return self.client_address[0] in ("127.0.0.1", "::1") and host in ("localhost", "127.0.0.1", "[::1]")

    def do_GET(self):
        u = urlparse(self.path)
        p = u.path.rstrip("/") or "/"
        if (p == "/" or p.startswith("/api")) and not self.from_this_pc():
            return self.send(403, {"error": "only available on this PC"})
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
        if not self.from_this_pc():
            return self.send(403, {"error": "only available on this PC"})
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
        if p in ("/api/channels", "/api/channels/add") and any(
                LOGIN_URL_RE.search(it.get("url") or "") for it in (body.get("channels") or [body])):
            return self.send(200, {"ok": False, "error": "This link holds a login. config.json is public, so it can't be "
                                                         "stored here - add it as a provider instead."})
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
                        gone = provs.pop(i).get("label")
                        CFG["provider_channels"] = [c for c in CFG["provider_channels"] if c.get("prov") != gone]
                elif url:
                    name = (body.get("name") or "").strip() or next(
                        f"Provider {n}" for n in itertools.count(1) if f"Provider {n}" not in {x.get("name") for x in provs})
                    was = next((x for x in provs if x.get("name") == name), {})
                    provs[:] = [x for x in provs if x is not was] + [{**was, "name": name, "url": url}]
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
                        g = body.get("guide", "")
                        west = g and wants_west(c) and not is_west_feed(g, {"names": {g: EPG_INDEX.get(g, {}).get("names", [])}})
                        c.update(guide=g, how="manual", manual=True, shift=180 if west else 0, picked="", backups=[])
                        c.pop("picked_shift", None)  # the old pick's backups and hours don't belong to the new pick
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
        ThreadingHTTPServer.allow_reuse_address = False  # a second copy must fail, not share the port
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
