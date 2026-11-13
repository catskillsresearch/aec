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
| E6 μ-hull of chart∪$z$ | `infra_610_placement_mu_hull` | **done** |
| E6 global $\varphi:N\to B$ fixing $eB$ | `infra_610_placement_to_B` | **retired** (impossible; no §6.2 sentence) |
| E6 pull $zN$ into $B$ | `infra_610_pull_z_to_B` | **done** (`exists_transport` empty base) |
| E6 per-param transport joint into $B$ | `infra_610_transport_joint` | **done** |
| E6 empty prescription joint on $E(I)$ | `infra_610_qPres_empty_joint_on_I` | **retired** (soft-pad; `preserves_atomic`) |
| E6 per-query freeness on $B$ | `infra_610_qPres_empty_free` | **done** (type-good push; E4 uniqueness) |
| E6 pull-root AgreeOn free ref | `infra_610_pull_root_agrees_free_ref` | **done** (wrapper of `qPres_empty_free`) |
| E6 same-head transfers joint | `infra_610_same_head_transfers_joint` | **demoted** (under-hypothesized) |
| E6 saturate prescriptions into $B$ | `infra_610_placement_saturate_to_B` | **done** (per query; type-good push) |
| E6 Lem 6.4 placement root on $B$ | `infra_610_placement_root_on_B` | **done** (per query) |
| E6 place_z: qPres head ~ empty | `infra_610_qPres_inl_matches_empty` | **done** (`hcoh`) |
| E5 glue reflected vs a realizing head | `infra_610_reflected_matches_chartRoot` | **done** (per-query type-good head) |
| E6 Galois tests of $p$ vs $eB\circ qPres$ | `infra_610_place_z_as_free_lift` → `infra_610_same_galois_tests_chartRoot` | **done** (`hgalois`; not the empty-head joint) |
| E6 place_z: Prop 4.9 package | `infra_610_place_z_prop49` | **done** |
| E6 place_z: empty hPlace | `infra_610_hPlace_empty` | **done** |
| E6 place_z: full hPlace | `infra_610_hPlace_full` | **done** |
| E6 place_z: qPres~empty on $E(I)$ | `infra_610_qPres_matches_empty_joint` | **retired** (no §6.2 sentence; soft-pad) |
| E6 place_z: reflect $E(I)\to B$ | `infra_610_reflect_joint_eB` | **done** |
| E6 wrap placement as `TupleOver` over $B$ | `infra_610_place_prescriptions` | **done** (`chartRoot` = `placeRoot`) |
| Majority transport of the placed type | `infra_610_majority_of_placement` | **done** |
| E7 Theorem 6.6 uniqueness / Galois diagram tests for $p_B$ | `infra_610_same_galois_tests_chartRoot` (prescription tests); `infra_610_same_galois` | **done** |
| E5–E7 packaged | `infra_610_majority_prescription` → `infra_610_place_on_B` | **done** (amalgam `IsFreeLift` + majority transport) |
| E8–E11 Mixed queries, restrict, iso, transitivity, Lem 6.9 code | deferred / narrowed in `IsFreeLift` | later |
| ClosedLevel for scheme bound $P.g` | `infra_610_closed_level` | **done** |

Hard chain follows English §6.2: majority prescriptions → per-query type-good push on $B$ (`qPres_empty_free`) → Galois tests of $p$ against $eB\circ qPres$. A single head in $B$ for every parameter list is retired with the soft-pad (`qPres_empty_joint_on_I`, `preserves_atomic`). `IsFreeLift` is the amalgam of $p$'s host with $B$, with majority values pushed along the $B$ leg. **Thm 6.10 done** for `SingleModelData`. **Lemma 6.11 done** for the same-level average criterion ([`AverageDescent.lean`](AverageDescent.lean)): fresh Lemma 6.9 code, majority bridge, moved parameter queries, `infra_610_same_galois`. Mixed $\nu < \mu$ stays deferred with E8–E11. **Proposition 6.12** is done for same-level existence and anchored independence ([`Proposition_6.12.md`](Proposition_6.12.md)); untied free-lift stationarity stays with `same_head`. **Proposition 6.13** is done for same-level local character and continuity ([`Proposition_6.13.md`](Proposition_6.13.md), [`LocalCharacter.lean`](LocalCharacter.lean)): a `SameLevelChain` traps a Lemma 6.9 code and Lemma 6.11 gives `IsFreeFrom` some stage; `infra_613_freeFrom_trans` is continuity along the cocone. Mixed levels and §7 `SatisfiesContinuity` stay deferred. **Proposition 6.15** is done for the two-sided strip with `G = P.E` ([`FreshStrip.lean`](FreshStrip.lean)); `infra_615_terminal` is the one-sided specialization. **Corollary 6.16** is done for `SingleModelData` ([`ApproxRetractionProof.lean`](ApproxRetractionProof.lean)). **Next tip:** Lemma 6.17 in [`Results.lean`](Results.lean). Retired: global `placement_to_B`, soft-pad placeRoot, empty-head joint, `same_head_transfers_joint`.

**[FreeExtension.lean](FreeExtension.lean)**

@import "FreeExtension.lean"
