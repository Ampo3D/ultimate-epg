"""One-off check: do open-epg listings agree with other guides for the same channels?"""
import copy, json, os, re
from datetime import datetime, timedelta, timezone
import ultimate_epg as u


def plain(t):
    return re.sub(r"[^a-z0-9]+", "", (t or "").lower())


def same(a, b):
    a, b = plain(a), plain(b)
    return bool(a and b) and (a == b or (min(len(a), len(b)) >= 5 and (a in b or b in a)))


oe = [s for s in u.all_sources() if "open-epg.com" in s.get("url", "")]
for s in u.all_sources():
    if s.get("type") == "xmltv" and os.path.exists(os.path.join(u.CACHE, s["id"] + ".xml")):
        u.status_of(s)["fresh"] = True
oe_ids = {s["id"] for s in oe}
u.load_epg_index()
u.rematch_provider()
index = dict(u.EPG_INDEX)
used = [c for c in u.CFG["provider_channels"] if c.get("guide") in index and index[c["guide"]]["source"] in oe_ids]
print("provider channels fed by open-epg", len(used), flush=True)

all_guides = u.guide_sources
u.guide_sources = lambda: [s for s in all_guides() if s["id"] not in oe_ids]
alt_idx = u.provider_index()
pairs = []
for c in used:
    alt = u.match_provider_channel(copy.deepcopy(c), alt_idx)[0]
    pairs.append((c, alt))
u.guide_sources = all_guides
u.load_epg_index()

want = {c["guide"] for c, _ in pairs} | {a for _, a in pairs if a}
read = {u.EPG_INDEX[g]["source"] for g in want if g in u.EPG_INDEX}
now = datetime.now(timezone.utc)
end = now + timedelta(hours=24)
shows = {}
for s in all_guides():
    if s["id"] not in read:
        continue
    print("reading", s["name"], flush=True)
    try:
        for el in u.iter_xmltv(os.path.join(u.CACHE, s["id"] + ".xml"), ("channel", "programme")):
            cid = el.get("channel", "")
            if el.tag == "programme" and cid in want and u.EPG_INDEX.get(cid, {}).get("source") == s["id"]:
                st = u.parse_xmltv_time(el.get("start"))
                if st and now <= st < end:
                    shows.setdefault(cid, []).append((st.timestamp(), el.findtext("title") or ""))
    except Exception as ex:
        print("  stopped early:", ex)

rows = []
for c, alt in pairs:
    mine = sorted(shows.get(c["guide"], []))
    other = sorted(shows.get(alt, [])) if alt else []
    hit = sum(1 for t, x in mine if any(abs(t - t2) <= 1800 and same(x, y) for t2, y in other))
    rows.append({"name": c["name"], "group": c["group"], "guide": c["guide"], "alt": alt or "",
                 "how": c.get("how"), "source": u.EPG_INDEX[c["guide"]]["source"], "shows": len(mine),
                 "alt_shows": len(other), "agree": round(hit / len(mine), 2) if mine and other else None,
                 "titles": [x for _, x in mine[:5]], "alt_titles": [y for _, y in other[:5]]})
rows.sort(key=lambda r: (r["agree"] is None, r["agree"] or 0))
names = {s["id"]: s["url"].rsplit("/", 1)[-1] for s in oe}
for r in rows:
    r["source"] = names[r["source"]]
with open("audit.json", "w", encoding="utf-8") as f:
    json.dump(rows, f, ensure_ascii=False, indent=0)
print("done", len(rows))
