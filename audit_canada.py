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


def alternates(items):
    """Per group of channels with the same skipped sources, what the normal matcher would pick without those sources."""
    groups = {}
    for r in items:
        groups.setdefault(frozenset(r["skip"]), []).append(r)
    print("rebuilding", len(groups), "indexes", flush=True)
    for key, members in groups.items():
        u.guide_sources = lambda: [s for s in sources if s["id"] not in key]
        idx = u.provider_index()
        u.guide_sources = all_guides
        for r in members:
            d = copy.deepcopy(r["c"])
            cid = u.match_provider_channel(d, idx)[0]
            src = next((x for x in holders.get(cid, []) if x not in key), None) if cid else None
            if src:
                r["alts"].append((src, cid, d.get("shift", 0)))
                r["skip"].append(src)
                want.setdefault(src, set()).add(cid)


rows = []
want = {}
for c in real:
    held = holders.get(c["guide"], [])
    src = held[0] if held else None
    r = {"c": c, "src": src, "alts": [], "skip": [src]}
    rows.append(r)
    if src:
        want.setdefault(src, set()).add(c["guide"])
        for other in held[1:3]:  # the same channel code published by another source
            r["alts"].append((other, c["guide"], c.get("shift", 0)))
            want.setdefault(other, set()).add(c["guide"])
live = [r for r in rows if r["src"]]
alternates(live)
alternates(live)

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
