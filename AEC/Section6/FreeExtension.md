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
| E5 soft join to empty `chartRoot` (Path A) | `infra_610_diagramEq_sum_elim_inl` / `chartRoot_joint_majority` | **retired** (no English sentence) |
| E5 Local majority prescriptions (assembler) | `infra_610_chart_prescriptions` | **done** |
| E6 Lemma 6.4 placement $z$ as $p_B$ | `infra_610_place_z_as_free_lift` → `infra_610_reflected_matches_chartRoot` | **blocked** on qPres soft-pad |
| E6 place_z: Prop 4.9 package | `infra_610_place_z_prop49` | **done** |
| E6 place_z: empty hPlace | `infra_610_hPlace_empty` | **done** |
| E6 place_z: full hPlace | `infra_610_hPlace_full` | **done** |
| E6 place_z: qPres~empty on $E(I)$ | `infra_610_qPres_matches_empty_joint` | **open** (soft-pad of empty hPlace on $J$) |
| E6 place_z: reflect $E(I)\to B$ | `infra_610_reflect_joint_eB` | **done** |
| E6 wrap placement as `TupleOver` over $B$ | `infra_610_place_prescriptions` | **done** (`chartRoot` = $B$-rep of $z$; retains Prop 4.9 `z`) |
| Majority transport of the placed type | `infra_610_majority_of_placement` | **done** |
| E7 Theorem 6.6 uniqueness / Galois diagram tests for $p_B$ | `infra_610_same_galois_tests_chartRoot`; `infra_610_same_galois` | **done** (modulo place_z tip) |
| E5–E7 packaged | `infra_610_majority_prescription` → `infra_610_place_on_B` | **done** (`SameGaloisType` + majority; modulo place_z) |
| E8–E11 Mixed queries, restrict, iso, transitivity, Lem 6.9 code | deferred / narrowed in `IsFreeLift` | later |
| ClosedLevel for scheme bound $P.g` | `infra_610_closed_level` | **done** |

Hard chain follows English §6.2: majority prescriptions → Lem 6.4 / Prop 4.9 placement → Thm 6.6 uniqueness. Open tip: `infra_610_qPres_matches_empty_joint` — promote empty `hPlace` α-equality to the joint with shared params on `J` (not a `StableDiagram` axiom; same combinatorial gap as retired Path A).

**[FreeExtension.lean](FreeExtension.lean)**

@import "FreeExtension.lean"
