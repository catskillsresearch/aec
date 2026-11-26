#!/usr/bin/env python3
"""Propagate hard-edge status on the holes board (holes-graph.json + HOLES.md).

* A done node with a non-done hard predecessor becomes blocked and is tagged CASCADE-BLOCKED
  (its Lean proof may be sorry-free; it waits on an upstream tip, e.g. an open fidelity gap).
* A CASCADE-BLOCKED node whose hard predecessors are all done again becomes done.
Iterates to a fixpoint. Run after any status change, then scripts/check_board.py.
"""
import json, os, re
root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
P = os.path.join(root, 'holes-graph.json'); M = os.path.join(root, 'HOLES.md')
g = json.load(open(P)); N = {n['id']: n for n in g['nodes']}
preds = {}
for e in g['edges']:
    if e.get('kind') == 'hard':
        preds.setdefault(e['to'], []).append(e['from'])
TAG = 'CASCADE-BLOCKED'
md = open(M).read().split('\n')
def row(i):
    for k, l in enumerate(md):
        if l.startswith('| `' + i + '` |'):
            return k
    return None
changed = True; log = []
while changed:
    changed = False
    for i, n in N.items():
        ps = [p for p in preds.get(i, []) if p in N]
        undone = [p for p in ps if N[p].get('status') != 'done']
        if n.get('status') == 'done' and undone:
            n['status'] = 'blocked'
            n['detail'] = f"{TAG} on {', '.join(undone)} (proof itself sorry-free; not done while a hard predecessor is open). " + n.get('detail', '')
            k = row(i)
            if k is not None:
                md[k] = md[k].replace('(**done**', f"(**blocked** on `{'`, `'.join(undone)}` ({TAG}); proof sorry-free, was done", 1)
            changed = True; log.append(('blocked', i, undone))
        elif n.get('status') == 'blocked' and n.get('detail', '').startswith(TAG) and not undone:
            n['status'] = 'done'
            n['detail'] = re.sub(r'^' + TAG + r' on [^)]*\)\. ', '', n['detail'])
            k = row(i)
            if k is not None:
                md[k] = re.sub(r"\(\*\*blocked\*\* on [^(]*\(" + TAG + r"\); proof sorry-free, was done", "(**done**", md[k])
            changed = True; log.append(('done', i, []))
g['doneCount'] = sum(1 for n in N.values() if n.get('status') == 'done')
json.dump(g, open(P, 'w'), indent=1, ensure_ascii=False); open(P, 'a').write('\n')
open(M, 'w').write('\n'.join(md))
for x in log: print(*x)
print('done', g['doneCount'])
