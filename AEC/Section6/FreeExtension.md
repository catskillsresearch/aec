# Free lift

From [Theorem 6.10](Theorem_6.10.md).

Theorem 6.10 (Stationary free extension). Let $A \to B$ be an arrow at a sufficiently closed level and let $p = \mathrm{tp}(v/A)$, where $|v| \le \sigma$. There is a specified actual type $p_B$ over $B$, called its free lift, extending $p$. At every desired query size whose approximation and testing costs are bounded at the originating level, it is computed by transporting sufficiently long approximations in $A$. At one level this includes every bounded query size; in a mixed-level use the costs must remain below the level of $A$.

We say that an actual type over $B$ is free from $A$ when it is the free lift of its restriction to $A$.

## English ↔ Lean (paper pp. 44–45)

Proof body is in `source/eventual.pdf` §6.2. Lean decls live in [`StationaryFreeExtension.lean`](StationaryFreeExtension.lean) unless noted.

| Paper step | Lean | Status |
|---|---|---|
| E1 Fix approximation sequence $I$ at $\tau=c(\sigma)$, $\kappa=\tau^+$ | `SingleModelData.exists_approximationSequence` + arity in `stationary_free_extension_exists` | done |
| E2 Move query $Z$ in $B$ into $A$ over the sequence | `infra_610_move_query` | done |
| E3 Majority answer on $Z$ equals $p\upharpoonright Z_0$ | `infra_610_majority_eq_type` / `infra_610_exists_majority` | done |
| E4 Independence / uniqueness of majority values | `infra_610_majority_unique` | done |
| E5 Local majority prescriptions on a chart of $B$ | `infra_610_chart_prescriptions` | **open** |
| E6 Lemma 6.4 compact placement → actual tuple over $B$ | `infra_610_place_prescriptions` | **done** (`proposition_4_9` + chart-root `TupleOver` on `B`) |
| Majority transport of the placed type | `infra_610_majority_of_placement` | **done** (chart-root `hmajority` packaging) |
| E7 Theorem 6.6 uniqueness / Galois diagram tests for $p_B$ | `infra_610_galois_tests_of_placement` (tests); `infra_610_same_galois` (amalgam) | tests **done** (chart-root `hgalois`), amalgam done |
| E5–E7 packaged | `infra_610_majority_prescription` → `infra_610_place_on_B` | assembler / wrapper |
| E8–E11 Mixed queries, restrict, iso, transitivity, Lem 6.9 code | deferred / narrowed in `IsFreeLift` ([`FreeExtension.lean`](FreeExtension.lean)) | later |
| *(no English step)* ClosedLevel for scheme bound $P.g$ | `infra_610_closed_level` | **done** (`ClosedLevel.of_closurePoint` via `P.tester`) |

Hard chain: `move_query → chart_prescriptions → place_prescriptions → majority_of_placement → majority_prescription → place_on_B → stationary_free_extension_exists → theorem_6_10`, with `galois_tests_of_placement → majority_prescription` and `closed_level → same_galois → stationary_free_extension_exists` separate.

**[FreeExtension.lean](FreeExtension.lean)**

@import "FreeExtension.lean"
