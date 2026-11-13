# Proposition 6.13

Proposition 6.13 (Local character and continuity). Let $(A_i : i < \delta)$ be an increasing chain of objects at one eligible level $\mu$, whose union $A$ has size $\mu$, and let $\delta$ be a nonzero limit ordinal. If $p = \mathrm{tp}(v/A)$ and either $v$ is finite or $|v| < \mathrm{cf}(\delta)$, then $p$ is free from some $A_i$. If, in addition, every restriction $\mathrm{tp}(v/A_i)$ is free from a fixed base $X \le A_0$, then $p$ is free from $X$.

**Done** for same-level `SingleModelData` ([`LocalCharacter.lean`](LocalCharacter.lean), thin wrap in [`Results.lean`](Results.lean)). The chain is `SameLevelChain`: nonzero limit ordinal, transition arrows for `i ≤ j`, cocone into a level-`μ` union, joint cover of occurrences. The tail is the recursion-closed levels at or above `σ⁺`. Local character traps a Lemma 6.9 code in one stage (`infra_613_bounded_in_stage`, `infra_613_trap_in_stage`) and discharges `IsFreeFrom` by `infra_611_isFreeFrom`, after `infra_613_stage_majority` (`infra_610_move_query`, `infra_610_majority_eq_type`, `diagram_trans`). Continuity is `infra_613_continuity`: local character picks the stage, and `infra_613_freeFrom_trans` moves freeness from `X` up the cocone. The type-joint form of that step is `infra_613_strong_trans` (`infra_610_majority_unique` and Lemma 6.11).

**Deferred:** mixed levels `ν < μ` in Prop 6.13 itself; Section 7 `SatisfiesContinuity`. Proposition 6.15, Corollary 6.16, and Lemma 6.17 are done. **Next tip:** Lemma 7.2.

**[Results.lean](Results.lean)**

@import "Results.lean"
