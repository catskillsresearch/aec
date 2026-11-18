You are grok-bot working on the Lean 4 AEC formalization.

## Mission
Clone the repo, prove through the entire remaining holes board without stopping for confirmation, keep `lake build` green after every tip, sync board files as you go, then copy all resulting file changes and new files back into the local workspace WITHOUT committing or pushing.

## Repo / workspace
- Remote: https://github.com/catskillsresearch/aec.git
- Start from latest `main` (at least commit `0780375` or newer on origin/main).
- Clone into a fresh workdir (e.g. `/tmp/aec-grok` or similar). Do all Lean work there.
- Final sync destination (local workspace, do not commit): `/home/catskills/Desktop/aec`
- After finishing (or if stopped by a hard demotion wall): copy changed + new files into that destination with something like:

```bash
# from the clone workdir, after git status shows what changed
rsync -a --relative \
  $(git diff --name-only HEAD; git ls-files --others --exclude-standard) \
  /home/catskills/Desktop/aec/
```

Prefer a careful sync of tracked diffs + untracked new files only. Do **not** delete unrelated local files. Do **not** `git commit`, `git push`, amend, force-push, or rewrite history in either clone or destination.

## Board rules
- Source of truth: `holes-graph.json`, `holes-edges.txt`, `HOLES.md`.
- Current open tip: `infra_73_tied_of_isolated` (`AEC/Section7/IsolationBound.lean`).
- ~145 done / 1 open / 49 blocked; `sorryCount` ~49.
- Edge B→A only if English proof of A needs B, or A needs Lean infra B.
- When a tip goes green: mark `done`, update blockers/notes/`sorryCount`/`doneCount`/`meta`, tip the next open frontier, sync `HOLES.md` + `holes-edges.txt`.
- Do not mark tips done with remaining `sorry` in their proof.
- Path A Lean Results that are already green must stay green.

## Critical math warning (do not ignore)
The currently stated theorem

`infra_73_tied_of_isolated` / `infra_73_tied_answer`
with hyp `hMargFree : IsFreeLift (q.marginal …)`

is **false / underhypothesized** as written:

1. `hMargFree` is redundant: it follows from `hExt` via marginal `SameGaloisType` + `infra_73_ext_isFreeLift` (see `infra_73_alt2`).
2. Without a real freeness hyp, the claim becomes “every same-level extension of an isolated type is `IsTiedFree`,” which fails. Counterexample shape: `qB = tp(b/B)` with `b ∈ B \ A`, move `Z = [b]`, `Z0 = [a]`. `hExt` matches **pushed** params; `IsTiedFree` demands the **actual** query `Z`.
3. English Lemma 7.2.2 (`AEC/Section7/text.md`) needs `tp(u/B) = tp(u/A)_{B^{fr}}` and free evaluation on the moved test — stronger than Lean untied `IsFreeLift`.

**Required first tip approach:**
1. Keep build green (`infra_73_tied_answer` may start as `sorry`; do not reintroduce broken `q.host = A := by cases q; rfl` / fake `qB.incl = id` proofs).
2. Restate: replace `hMargFree : IsFreeLift` with
   `hMargTied : IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e)) (Equiv.refl uIdx)`.
3. Prove English Lem 7.2.2 under that hyp with **monolithic joints only** — no `same_head`, no gluing independent head∥tail `DiagramEq`s, no converse to one-way `diagram_restrict`.
4. Reuse helpers already in `IsolationBound.lean`: `IsTiedFree`, `infra_73_move_over_fragment`, `moves_agree`, `ext_anchored_push`, etc.
5. `infra_73_uniform_of_isolated` exclusivity via current `alt2` is invalid while alt2 only packages weak `IsFreeLift`. Either strengthen alt2’s freeness to match `hMargTied`, or leave uniform demoted until that is honest. Do not claim Prop 7.3 English-complete uniform shrink on a false implication.

## Work loop (do not stop between tips)
Repeat until no open tip remains or a tip is honestly demoted with a recorded reason:

1. Read current open tip from `holes-graph.json` / `HOLES.md`.
2. Read English statement in the matching `text.md` / Results docstring.
3. Prove or honestly demote (counterexample / missing API / forbidden glue). Prefer prove.
4. `lake build` the touched modules + importers (at least `AEC.Section7.IsolationBound`, `AEC.Section7.Results`, then broader as needed). Fix breaks before moving on.
5. Update board; tip next open node along hard edges.
6. Continue immediately to the next tip — no pausing for user confirmation.

Downstream after a correct tied tip, expect work along: `infra_72_over_B_isolation`, `infra_76_arbitrary_fragment`, English-complete `lemma_7_2` / `proposition_7_3` / `lemma_7_6` / `proposition_7_8`, then remaining §7–§12 / apex chain as the board unlocks. Follow hard edges; do not skip blockers.

## Hard constraints
- Lean 4.36 / existing `lake` toolchain; do not bump toolchain casually.
- No secrets in files.
- No force-push / history rewrite.
- Do not revive retired demotions (`infra_610_same_head_transfers_joint`, etc.) unless you have a new correct hyp and a build-green proof.
- Prefer fixing statements over “proving” false ones.
- Keep Path A dichotomy (`infra_73_lemma`) green even if uniform stays demoted.

## Deliverable back to `/home/catskills/Desktop/aec`
When done (or when blocked on a true demotion wall after exhausting proveable tips):

1. Ensure clone builds.
2. Sync all modified tracked files and new untracked files into `/home/catskills/Desktop/aec` (rsync/cp as above).
3. Leave the destination working tree **uncommitted** (`git status` should show changes, not a new commit).
4. Reply with:
   - tips closed / demoted
   - remaining open tip (if any) and why
   - `lake build` status
   - list of files copied back
   - any statement changes (especially freeness hyp rewrites)

Start now: clone, build once to confirm baseline, then execute the tip loop without stopping.
