#!/usr/bin/env python3
"""Board-sync check for holes-graph.json / holes-edges.txt / HOLES.md.

Fails (exit 1) if
  * a node marked done has a hard predecessor that is not done
    (a result whose statement or proof still waits on an open tip is not done),
  * an edge names an unknown node,
  * a hard edge of holes-graph.json is missing from holes-edges.txt,
  * a node with a HOLES.md table row disagrees with it on done-ness.
"""
import json, re, sys, os
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
g = json.load(open(os.path.join(root, 'holes-graph.json')))
N = {n['id']: n for n in g['nodes']}
bad = []
for e in g['edges']:
    for k in ('from', 'to'):
        if e[k] not in N:
            bad.append(f"unknown node in edge: {e['from']} --> {e['to']}")
for e in g['edges']:
    if e.get('kind') == 'hard' and e['from'] in N and e['to'] in N:
        if N[e['to']].get('status') == 'done' and N[e['from']].get('status') != 'done':
            bad.append(f"done node {e['to']} has non-done hard predecessor {e['from']} ({N[e['from']].get('status')})")
txt = open(os.path.join(root, 'holes-edges.txt')).read()
lines = set(l.strip() for l in txt.split('\n'))
for e in g['edges']:
    if e.get('kind') == 'hard' and f"{e['from']} --> {e['to']}" not in lines:
        bad.append(f"hard edge missing from holes-edges.txt: {e['from']} --> {e['to']}")
md = open(os.path.join(root, 'HOLES.md')).read()
for l in md.split('\n'):
    m = re.match(r"\| `([^`]+)` \|", l)
    if m and m.group(1) in N:
        st = N[m.group(1)].get('status')
        says_done = '(**done**' in l
        if says_done != (st == 'done') and ('**blocked**' in l or '**open**' in l or says_done):
            bad.append(f"HOLES.md row for {m.group(1)} disagrees with status {st}")
for b in bad:
    print("BOARD CHECK FAIL:", b)
print(f"board check: {len(bad)} problem(s); done={sum(1 for n in N.values() if n.get('status')=='done')}")
sys.exit(1 if bad else 0)
