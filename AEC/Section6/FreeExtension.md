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
| E5a Chart of $B$ | `infra_610_chart_of_B` | **done** |
| E5a′ Power-fixed $\chi$ | `infra_610_choose_chi` | **done** |
| E5a″ Empty-good free-root | `infra_610_free_root` | **done** |
| E5b Majority Prop 4.9 `q`/`hnat`/`hcoh` | `infra_610_majority_qPres` | **done** |
| E5c Support package | `infra_610_chart_support` | **done** |
| E5d Moved majority (good `vi` push) | `infra_610_moved_majority` | **done** |
| E5d′ Match majority prescription to placed root | `infra_610_majority_matches_root` | **done** (reflected `eB∘qPres`; `diagram_refl`) |
| E5d″ Root majority field | `infra_610_root_majority` | **done** |
| E5e Root Galois tests | `infra_610_root_galois` | **done** (reflected `eB∘qPres` RHS; majority transport) |
| E5 soft join to empty `chartRoot` (Path A) | `infra_610_chartRoot_joint_majority` → `infra_610_reflected_matches_chartRoot` | **open pad**: `infra_610_diagramEq_sum_elim_inl` |
| E5 Local majority prescriptions (assembler) | `infra_610_chart_prescriptions` | **done** |
| E6 Lemma 6.4 compact placement → actual tuple over $B$ | `infra_610_place_prescriptions` | **done** (`chartRoot` as `d₁`) |
| Majority transport of the placed type | `infra_610_majority_of_placement` | **done** |
| E7 Theorem 6.6 uniqueness / Galois diagram tests for $p_B$ | `infra_610_same_galois_tests_chartRoot`; `infra_610_same_galois` | **done** (modulo Path A pad) |
| E5–E7 packaged | `infra_610_majority_prescription` → `infra_610_place_on_B` | **done** (`SameGaloisType` + majority; Path A) |
| E8–E11 Mixed queries, restrict, iso, transitivity, Lem 6.9 code | deferred / narrowed in `IsFreeLift` | later |
| ClosedLevel for scheme bound $P.g` | `infra_610_closed_level` | **done** |

Hard chain closed through E5e / packaging / `theorem_6_10` with Path A soft join to empty `chartRoot` as amalgam `d₁`. Open tip: `infra_610_diagramEq_sum_elim_inl` — pad `DiagramEq` of heads along a common parameter tail (blocks finishing Path A without `sorry`).

**[FreeExtension.lean](FreeExtension.lean)**

@import "FreeExtension.lean"
