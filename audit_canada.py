"""One-off check: do the listings on Canadian channels agree with other sources for the same channels?"""
import copy, json, os, re
from datetime import datetime, timedelta, timezone
import ultimate_epg as u


def plain(t):
    return re.sub(r"[^a-z0-9]+", "", (t or "").lower())


def same(a, b):
    a, b = plain(a), plain(b)
    return bool(a and b) and (a == b or (min(len(a), len(b)) >= 5 and (a in b or b in a)))


def agree(mine, other):
    if not mine or not other:
        return None
    hit = sum(1 for t, x in mine if any(abs(t - t2) <= 1800 and same(x, y) for t2, y in other))
    return round(hit / len(mine), 2)


def canadian(c):
    g, n = (c.get("guide") or "").lower(), c["name"]
    return c.get("how") != "event" and (c["group"] in ("Canada", "Canada French") or g.endswith(".ca")
                                        or n.endswith(" CA") or n.startswith("CA ") or "canada" in n.lower())


all_guides = u.guide_sources
for s in u.all_sources():
    if s.get("type") == "xmltv" and os.path.exists(os.path.join(u.CACHE, s["id"] + ".xml")):
        u.status_of(s)["fresh"] = True
u.load_epg_index()
u.rematch_provider()
sources = all_guides()
order = {s["id"]: i for i, s in enumerate(sources)}
holders = {}
for s in sources:
    p = os.path.join(u.CACHE, s["id"] + ".channels.json")
    if os.path.exists(p):
        with open(p, encoding="utf-8") as f:
            for cid, info in json.load(f).items():
                if info.get("n", 1):
                    holders.setdefault(cid, []).append(s["id"])

urls = {s["id"]: s["url"] for s in sources}
oe = lambda c: any("open-epg.com" in urls[x] for x in holders.get(c.get("guide"), [])[:1])
chans = [c for c in u.CFG["provider_channels"] if c.get("how") != "event" and (canadian(c) or oe(c))]
real = [c for c in chans if c.get("guide")]
print("canadian", len(chans), "with a guide", len(real), flush=True)

indexes = {}


def alternate(c, skip):
    """The guide the normal matcher would pick if the skipped sources did not exist."""
    key = frozenset(skip)
    if key not in indexes:
        u.guide_sources = lambda: [s for s in sources if s["id"] not in key]
        indexes[key] = u.provider_index()
        u.guide_sources = all_guides
        print("index without", len(key), "sources:", len(indexes), flush=True)
    d = copy.deepcopy(c)
    cid = u.match_provider_channel(d, indexes[key])[0]
    if not cid:
        return None
    src = next((x for x in holders.get(cid, []) if x not in key), None)
    return (src, cid, d.get("shift", 0)) if src else None


rows = []
want = {}
for c in real:
    src = next((x for x in holders.get(c["guide"], [])), None)
    if not src:
        rows.append({"c": c, "src": None, "alts": []})
        continue
    want.setdefault(src, set()).add(c["guide"])
    alts, skip = [], [src]
    for _ in range(3):
        a = alternate(c, skip)
        if not a:
            break
        alts.append(a)
        skip.append(a[0])
        want.setdefault(a[0], set()).add(a[1])
    rows.append({"c": c, "src": src, "alts": alts})

now = datetime.now(timezone.utc)
end = now + timedelta(hours=24)
shows = {}
for s in sources:
    ids = want.get(s["id"])
    if not ids:
        continue
    print("reading", s["name"], flush=True)
    try:
        for el in u.iter_xmltv(os.path.join(u.CACHE, s["id"] + ".xml"), ("channel", "programme")):
            cid = el.get("channel", "")
            if el.tag == "programme" and cid in ids:
                st = u.parse_xmltv_time(el.get("start"))
                if st and now - timedelta(hours=4) <= st < end + timedelta(hours=4):
                    shows.setdefault((s["id"], cid), []).append((st.timestamp(), el.findtext("title") or ""))
    except Exception as ex:
        print("  stopped early:", ex)

names = {s["id"]: s["url"] for s in sources}


def timed(src, cid, shift):
    a, b = now.timestamp(), end.timestamp()
    return sorted((t + shift * 60, x) for t, x in shows.get((src, cid), []) if a <= t + shift * 60 < b)


mine = {}
for r in rows:
    if r["src"]:
        mine[r["c"]["key"]] = timed(r["src"], r["c"]["guide"], r["c"].get("shift", 0))
out = []
for r in rows:
    c = r["c"]
    m = mine.get(c["key"], [])
    alts = []
    for src, cid, shift in r["alts"]:
        o = timed(src, cid, shift)
        alts.append({"guide": cid, "url": names[src], "shows": len(o), "agree": agree(m, o), "titles": [y for _, y in o[:4]]})
    twin, score = "", 0
    for r2 in rows:
        c2 = r2["c"]
        if c2["key"] != c["key"] and c2.get("guide") != c.get("guide"):
            a = agree(m, mine.get(c2["key"], [])) or 0
            if a > score:
                twin, score = c2["name"], a
    scores = [a["agree"] for a in alts if a["agree"] is not None]
    out.append({"name": c["name"], "group": c["group"], "guide": c["guide"], "how": c.get("how"), "manual": bool(c.get("manual")),
                "url": names.get(r["src"], ""), "shows": len(m), "best": max(scores) if scores else None, "alts": alts,
                "twin": twin, "twin_score": score, "titles": [x for _, x in m[:6]]})
out.sort(key=lambda r: (r["best"] is None, r["best"] or 0))
with open("audit.json", "w", encoding="utf-8") as f:
    json.dump({"labels": [c["name"] for c in chans if not c.get("guide")], "rows": out}, f, ensure_ascii=False, indent=0)
print("done", len(out))
