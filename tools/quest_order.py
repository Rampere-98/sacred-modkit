#!/usr/bin/env python
"""Builds src/game/quest_order.inc: every quest of the Ancaria campaign in the order the agent does them, by level,
then region, then number (a main quest always after the one before it).

Usage: python -I tools/quest_order.py <sacred-bild docs dir> [numtitles.json]

Sources, each row tagged with the one its level comes from:
  giver   the sector's lowest level at the quest's giver (docs/Sacred/Misiones-dadores.tsv, Manolito's block BN: the
          game's own sector table)
  goal    the same at the quest's objective (the TSV's «objetivo» rows)
  region  the lowest sector level of the quest's region among the TSV's rows (RRnn: region RR; region 1 is 15n)
  zone    docs/QUESTS.md «nivel zona» (CobaltBlu v1.06, Bronze; «(inf.)» inferred by its zone)
  chain   a main quest with none of these: the level of the main quest before it (the chain only goes up)
  none    no source has a level (the Underworld's DQ_1025x, some DQ_150xx): last, level 0
Numbers as the journal has them: DQ_n, GQ_n, NQ_n are n; RrrNQqq is 100*rr + qq, region 1's 150 + qq. Titles: the
game's own (the «Lore: Misión» lines of the copies' logs, numtitles.json) when known, else QUESTS.md's.
"""
import json, os, re, sys

docs = sys.argv[1]
titles_path = sys.argv[2] if len(sys.argv) > 2 else None
here = os.path.dirname(os.path.abspath(__file__))
out_path = os.path.join(here, "..", "src", "game", "quest_order.inc")


def rq(region, quest):
    return 150 + quest if region == 1 else 100 * region + quest


def number_of(key):
    if m := re.match(r"(?:DQ|GQ|NQ)_(\d+)$", key):
        return int(m.group(1))
    if m := re.match(r"R(\d+)[a-zA-Z]?NQ(\d+)$", key):
        return rq(int(m.group(1)), int(m.group(2)))
    return None


def region_of(number):
    if 151 <= number <= 199:
        return 1
    if 200 <= number < 10000:
        return number // 100
    return 0


text = open(os.path.join(docs, "QUESTS.md"), encoding="utf8").read()
table = text[text.index("## Tabla para el código"):]
quests = {}     # number -> dict
mains = []      # HQ rows: (key, name, zone level)
for m in re.finditer(r"^\| `([A-Za-z0-9_]+)` \| ([^|]+)\| ([^|]*)\| ([^|]*)\| ([^|]*)\| ([^|]*)\| ([^|]*)\| ([^|]*)\|",
                     table, re.M):
    key, name, zone = m.group(1), m.group(2).strip(), m.group(8).strip()
    if key.startswith(("NQ_UW", "RB_")):
        continue
    lv = re.match(r"(\d+)", zone)
    if key.startswith("HQ_"):
        mains.append((key, name, int(lv.group(1)) if lv else None))
        continue
    n = number_of(key)
    if n is None:
        continue
    q = quests.setdefault(n, {"number": n, "key": key, "title": name.split(" (")[0], "main": False})
    if lv and "zone" not in q:
        q["zone"] = int(lv.group(1))

# The game's titles (and the journal's main quests, 1-82)
seen = {}
if titles_path and os.path.exists(titles_path):
    seen = {int(k): v for k, v in json.load(open(titles_path, encoding="utf8")).items()}
for n, (title, kind, _, _) in seen.items():
    q = quests.setdefault(n, {"number": n, "key": "", "title": title, "main": n < 100})
    q["title"] = title
    if n < 100:
        q["main"] = True
# A main quest's zone level from QUESTS.md's HQ row of the same title
def norm(s):
    return re.sub(r"[^a-z0-9]", "", s.lower())
for key, name, zone in mains:
    for q in quests.values():
        if q["main"] and norm(q["title"]) == norm(name.split(" (")[0]) and zone is not None:
            q.setdefault("zone", zone)
            q["key"] = key

# The game's sector levels at givers and objectives
rows = [l.rstrip("\n").split("\t") for l in open(os.path.join(docs, "Sacred", "Misiones-dadores.tsv"), encoding="utf8")][1:]
region_lo = {}
for r in rows:
    n, role, region, lo = int(r[0]), r[1], int(r[6]), int(r[7])
    region_lo[region] = min(region_lo.get(region, 999), lo)
    q = quests.setdefault(n, {"number": n, "key": "", "title": "?", "main": False})
    q.setdefault("giver" if role == "dador" else "goal", lo)

# Neither a title nor a giver (209: only an objective's row in the TSV, no quest in the journal's titles nor in
# QUESTS.md): a step's variable, not a quest
quests = {n: q for n, q in quests.items() if q["title"] != "?" or "giver" in q}
for q in quests.values():
    for src in ("giver", "goal"):
        if src in q:
            q["level"], q["source"] = q[src], src
            break
    else:
        if region_of(q["number"]) in region_lo:
            q["level"], q["source"] = region_lo[region_of(q["number"])], "region"
        elif "zone" in q:
            q["level"], q["source"] = q["zone"], "zone"
# Main quests: the chain only goes up
last = 1
for q in sorted((q for q in quests.values() if q["main"]), key=lambda q: q["number"]):
    if "level" not in q:
        q["level"], q["source"] = last, "chain"
    q["level"] = max(q["level"], last)
    last = q["level"]
missing = sorted(n for n, q in quests.items() if "level" not in q)
ordered = sorted((q for q in quests.values() if "level" in q), key=lambda q: (q["level"], region_of(q["number"]), q["number"]))
# A main quest after the one before it: a stable pass moving each main behind its predecessor
pos = {q["number"]: i for i, q in enumerate(ordered)}
main_numbers = sorted(q["number"] for q in ordered if q["main"])
for a, b in zip(main_numbers, main_numbers[1:]):
    if pos[b] < pos[a]:
        qb = ordered.pop(pos[b])
        ordered.insert(pos[a], qb)
        pos = {q["number"]: i for i, q in enumerate(ordered)}

with open(out_path, "w", encoding="utf8", newline="\n") as f:
    f.write("// The campaign's quests in the order the agent does them (generated by tools/quest_order.py from docs/QUESTS.md,\n"
            "// docs/Sacred/Misiones-dadores.tsv and the game's quest titles in the copies' logs; do not edit by hand):\n"
            "// {journal number, level, main}, // title (level's source)\n")
    for q in ordered:
        title = q["title"].replace("*/", "")
        f.write(f'{{{q["number"]}, {q["level"]}, {"true" if q["main"] else "false"}}},  // {title} ({q["source"]})\n')
    # No level from any source: last, level 0 (no farming for them), in number order
    for n in missing:
        f.write(f'{{{n}, 0, false}},  // {quests[n]["title"].replace("*/", "")} (no level known: last)\n')
print(f"{len(ordered) + len(missing)} quests written to {os.path.normpath(out_path)}; no level for {len(missing)}: {missing}")
src_count = {}
for q in ordered:
    src_count[q["source"]] = src_count.get(q["source"], 0) + 1
print("levels from:", src_count)
