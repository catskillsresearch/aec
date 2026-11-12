# Proof holes (BFS dependency order)

Inventory of Lean `sorry` holes in this repository, ordered **prove-first**: Layer 0
are holes with no remaining unfinished prerequisites; later layers wait on earlier
ones. Apex theorems 1.2 and 1.3 are **last**.

**Count:** 58 `sorry`, 0 `admit`.
Sections **2**, **3**, **4**, and **13** have no holes.

**Dependency basis:** paper/logical order from `dependencies.mermaid`
(`A --> B` means B waits on A), reconciled with the current hole set, plus
within-section paper numbering and Lean `Results`→`Results` imports
(S7–S11 on S5/S6).

**Note on Lean-import BFS:** A module-only BFS among hole-bearing `Results.lean`
files would place S1, S12, and S14 in Layer 0 because those stubs do not import
later Results. That ranking is wrong for prove-first work; this file uses the
logical order instead.

**Reconciliation with `dependencies.mermaid`:** The mermaid “Presentations”
subgraph (Lemmas 2.1–2.5, Theorem 2.6, Proposition 2.3 converse) is **filled**
(Section 2 has no `sorry`). Those nodes are omitted from the cluster DAG below.
Section 13 is complete and was never on that chain.

---

## Counts by section

| Section | Holes | File |
|--------:|------:|------|
| 1 | 2 | `AEC/Section1/Results.lean` |
| 2 | 0 | — |
| 3 | 0 | — |
| 4 | 0 | — |
| 5 | 1 | `AEC/Section5/Results.lean` |
| 6 | 7 | `AEC/Section6/Results.lean` |
| 7 | 9 | `AEC/Section7/Results.lean` |
| 8 | 5 | `AEC/Section8/Results.lean` |
| 9 | 7 | `AEC/Section9/Results.lean` |
| 10 | 9 | `AEC/Section10/Results.lean` |
| 11 | 8 | `AEC/Section11/Results.lean` |
| 12 | 4 | `AEC/Section12/Results.lean` |
| 13 | 0 | — |
| 14 | 4 | `AEC/Section14/Results.lean` |
| **Total** | **56** | |

The table is the previous `Results.lean` rollup. The live token count is **60**,
including the Thm 6.10 open tip `chart_prescriptions` and
`WorkingScheme.exists_approximationSequence`.

---

## Remaining hole clusters (prove-first DAG)

```mermaid
flowchart TD
  subgraph L0 [L0 Foundations]
    S4["Section 4: Lem 4.5 … Thm 4.11"]
  end
  subgraph L1 [L1 Schemes start]
    S5["Section 5: Prop 5.6–5.8"]
  end
  subgraph L2 [L2]
    S6["Section 6: 7 holes"]
  end
  subgraph L3to6 [L3–L6]
    S7["Section 7"]
    S8["Section 8"]
    S9["Section 9"]
    S10["Section 10"]
  end
  subgraph L7 [L7 Geometry systems]
    S11["Section 11"]
  end
  subgraph L8 [L8]
    S12["Section 12"]
  end
  subgraph L9 [L9 Transfer]
    S14["Section 14"]
  end
  subgraph L10 [L10 Apex]
    T12["Theorem 1.2"]
    T13["Theorem 1.3"]
  end
  S4 --> S5 --> S6 --> S7 --> S8 --> S9 --> S10
  S5 --> S8
  S5 --> S9
  S5 --> S10
  S6 --> S8
  S6 --> S9
  S6 --> S10
  S10 --> S11 --> S12 --> S14 --> T12
  S14 --> T13
```

Within a layer, siblings are listed in paper number order.

---

## BFS layers (individual holes)

### L0 — Independent foundations (0 open)

No unfinished Results prerequisites. Section 3 is complete (Theorem 3.11 closed by the
`θ⁺ · a^θ` renaming kill); Section 4 (the diagrams/orbits stack) is complete (Theorem 4.11 closed
by the countable tower of Lemma 4.10 lifts into one categorical `E(J)`).

**Live board:** [`holes.html`](holes.html) + [`holes-graph.json`](holes-graph.json).
Edge **B→A** means the English proof of A requires B (no soft/narrative-only edges).
Blue = done; green = open; grey = blocked. No separate failed status unless a
counterexample refutes the program.

**Dependency rule:** edge B→A only if the English proof of A requires B, or A
needs an explicit Lean infra subgoal B (not a paper-number chain).

**Open (frontier):** E5d′ `infra_610_majority_matches_root` (statement repaired to placed empty-majority root; residual `DiagramEq` join of `hinr`+`hcoh`), E5e `infra_610_root_galois` (retargeted to placed root). Map: [`AEC/Section6/FreeExtension.md`](AEC/Section6/FreeExtension.md). Majority `qPres` / `chart_support` (`χ = seq.τ`), E5d `moved_majority`, E5d″ `root_majority` **done**. Assembler `chart_prescriptions` blocked on E5e; `majority_prescription` blocked on E5d′ join. E6–E7 packaging, `closed_level`, `move_query`, `same_galois`, `place_on_B` **done**. Existence picks power-fixed `χ` then builds `seq` with `τ = χ`.
**Note:** `lemma_6_1`, `theorem_3_11`, `proposition_5_6`, `proposition_5_7`, `lemma_4_6`, `lemma_6_14`, `proposition_4_3`, `lemma_4_5`, `lemma_4_7`, `proposition_4_8`, `proposition_4_9`, `lemma_4_10`, `theorem_4_11`, `theorem_6_6`, `corollary_6_7`, `proposition_5_8`, `proposition_5_9`,
`infra_pair_coloring_glue`, `infra_rank_slice`, `infra_type_u_witness_set`, `infra_countable_back_and_forth`, `infra_stable_diagram_realize`, `infra_zeta_model_existence`, `infra_eligible_reclass`, `infra_template_fixed_support`, `infra_named_working_scheme`, `infra_named_working_package`, `infra_single_model_scheme`, `infra_single_model_package` are done.
Lean 5.8 is the residual `diagram_iso`+`structural_iso` form.
False `6.13→6.14` / `5.8→5.9` edges removed. Later adjacent-number edges still suspect.
`4.7→4.8` is hard again: `proposition_4_8` on the support encoding tests two full lists on their joint support and does not use Lemma 4.7, but the English form over the base needed by Lemma 4.10 (`proposition_4_8_over_base`, `PlacedTester`) is proved from Lemma 4.7.
`4.2→4.9` added (hard): local realizability and restriction of diagrams in Prop 4.9 use Prop 4.2's strong-map clause. `4.2→4.10`, `4.3→4.10`, `4.8→4.10` added (hard): Lemma 4.10 uses strong maps `B → E(I)` fixing parameters (Prop 4.2 at `μ`), common hulls and categoricity at `μ` (Prop 4.3), and the placed tester (Prop 4.8). Lemma 4.10 is done. `4.2→4.11`, `4.8→4.11` added (hard): Theorem 4.11 uses the strong-map clause of Prop 4.2 (`StableDiagram.to_strong`, for each lifted stage of the tower) and the placed tester of Prop 4.8 (clause 2, and the codes of clause 3). Theorem 4.11 is done, **with a repaired statement** (see the table); Proposition 5.6 is unblocked.
Proposition 5.6 is done, **with a strengthened statement and after three repairs of Definition 5.2** (next paragraph). Its Lean proof uses the closure points of Theorem 4.11 (`ClosedLevels.lean`), Prop 4.3 and Theorem 2.6, and does not call `theorem_4_11` or `PlacedTester` (amalgamation is not a clause of a working scheme); the edges `2.6, 4.2, 4.3, 4.11 → 5.6` stay as English dependencies.

**Definition 5.2 repairs (made for Proposition 5.6).** The planned statement of Proposition 5.6 (a working package with an object at every eligible level) was refutable from the definitions; each obstruction was checked in Lean before the repair.
1. `WorkingScheme.diagram_iso` is now for lists with `#α < μ`, and `WorkingScheme.diagram_preserved` for lists with `#α < μ` and `#α < ν` (`AEC/Section5/WorkingScheme.lean`). Unbounded, the two fields applied to the list of all occurrences of an object made every permitted arrow between objects at one level vertexwise bijective; the stable diagram `D` only controls bounded lists. `diagram_refl`, `diagram_symm`, `diagram_trans`, `diagram_reindex`, `diagram_restrict`, `diagram_empty` are unchanged.
2. `IsSaturated.saturated` now assumes `∀ i, ext (Sum.inl i) = base i` (`AEC/Section5/PackageClauses.lean`): the witness extends the list whose diagram is that of the actual list. Before, `ext` was unrelated to `base` and `xs`, and the clause failed for a constant `ext` over an injective `xs`.
3. `HasChainUnions.union` now assumes the cocone condition `∀ i j, SystemArrow.comp (le i j) (toZ j) = toZ i` in its universal property (`AEC/Section5/PackageClauses.lean`). This repair was not planned: after 1 and 2 the statement was still refutable, since for a two-element constant family the clause identified any two permitted arrows `X → Z`, which with mixed downward closure refutes every package that has an object.

Callers: `namedWorkingScheme` now takes `hι : #ι < μ0`, `hTail : ∀ μ ∈ T, μ0 ≤ μ`, `hinf : ∀ μ ∈ T, ℵ₀ ≤ μ` (a bounded list together with the names is bounded); `named_index_lt_of_tail` and `sum_mk_lt_of_lt` moved to `NamedWorkingScheme.lean`. Props 5.7, 5.8, 5.9 remain proved without `sorry`.

**Known residual in `HasChainUnions`.** The clause quantifies over arrows `le i j` for *every* ordered pair `(i, j)`, composing strictly, so its families consist of mutually inverse isomorphisms; with the cocone condition the clause holds in every scheme (take `U := obj i₀`). A faithful clause would index `le` over `i ≤ j` in a directed order. It was left unchanged (minimal repairs); the real content for single models is `SingleModelData.exists_directed_union`. Re-index the clause when Sections 6–11 first need a chain union.

**Lemma 6.1 is done, with a repaired statement** (`AEC/Section6/ParameterOrbits.lean`). The bare-scheme statement was refutable (`DiagramEq` may be equality of lists). Assuming a working package with presentations is not enough: `IsWorkingPackage` and `HasPresentations` do not make the automorphisms of the vertex models, which Lemma 4.5 produces, structural isomorphisms of the scheme (counterexample pattern, not formalized: isomorphisms that preserve a colouring by more than `χ` colours). The statement now has:
1. `hiso : AssemblesStructIso W b` (new definition): at every object there is a set `B` of at most `b` occurrences such that strong vertex automorphisms fixing `B` and commuting with the specified maps are the vertex maps of a structural isomorphism. The English bound `b` and `hb : b + σ < χ` are kept.
2. `hχ : ls K + 2^(2^σ) ≤ χ`, the bound of Lemma 4.5, `hcat : ∀ μ ∈ W.eligible, Categorical K μ`, and `[CategoricalUnbounded K]`.
3. `hedge : ∀ i j, ¬ S.specified i j`: the shape has no specified map. Lemma 4.5 gives vertex automorphisms one vertex at a time, and they need not commute with the maps of a system. Any finite number of vertices is covered. A one-vertex hypothesis was not used: it is not needed, and it does not suffice for this proof (one vertex with a specified map to itself).

`IsWorkingPackage` and `HasPresentations` are not hypotheses; the proof does not use them. `hiso` holds for the Prop 5.6 scheme with `b = 0` (`SingleModelData.assemblesStructIso`, from `assemblesStructIso_bijective`) and for the Prop 5.7 named scheme with `b + #names` (`WorkingScheme.assemblesStructIso_named`). `SingleModelData.exists_parameter_orbit_reps` is the lemma for the Prop 5.6 scheme with no scheme hypothesis left. `proposition_5_6` does not export `hedge`, `hcat` or `hiso` for its existential scheme: callers of Lemma 6.1 use `SingleModelData.scheme` directly, or the statement of Prop 5.6 has to be extended. Shapes with specified maps remain open for Lemma 6.1 (they need orbits of system automorphisms, not of vertex automorphisms). Hard edge `4.5 → 6.1` added; Prop 6.3 is done (PlacedTester packaging); Lemma 6.4 is done; Lemma 6.5 is done (next paragraph).

**Lemma 6.5 is done, with a repaired statement** (`AEC/Section6/PlacedComparisons.lean`). The old Lean form had `SameGaloisType` (scheme amalgamation) on the left of the iff; that is Theorem 6.6, and English Lemma 6.5 says its argument "does not require an amalgamation relation on types". Its `g` was only monotone (the iff fails for small `g`), and a bare `WorkingScheme` has no presentation in which to place a tuple. The statement is now at the level of a presentation, like Prop 6.3 and Lemma 6.4: `hL : ClosedLevel K E D g μ`, `I` a well-order of size `μ`, `A = E(I)`, and tuples `d₀`, `d₁` of length at most `σ < μ` in strong `μ`-extensions `B₀`, `B₁` of `A`. It has three clauses:
1. existence: some placement over `I` lifts the bounded diagrams of `d₀` (`Placement.LiftsBounded`), from `exists_boundedDiagramLift` (Lemma 4.10);
2. uniqueness: two such placements agree over all of `A` (`Placement.AgreeOn … Set.univ`), from `Placement.LiftsBounded.agreeOn_univ`. This clause is not in the planned statement; it is the English sentence "unique as a diagram over all of `A`";
3. testing: for lifts `P₀` of `d₀` and `P₁` of `d₁`, `P₀.AgreeOn E D P₁ Set.univ` iff the diagrams of `d₀` and `d₁` agree at the bounded levels `ρ < μ` over all `p : β → A` with `#β ≤ g σ + ls K` (the right side of Theorem 4.11 (2)). `←` is `agreeOn_univ_of_tests` (the placed tester). `→` is new, `Placement.LiftsBounded.same_of_agreeOn`: equal comparisons make `P₀` lift `d₁` as well (`Placement.LiftsBounded.of_agreeOn`), so both tuples have the diagram of its placed tuple; it holds for every bounded query, without the bound on `#β`.

`σ` is any infinite bound on the length, in place of `|v| + ℵ₀`. The separate hypothesis `hg : PlacedTester K E D g` of the planned statement is omitted, since it is the field `hL.tester`. `hs₁ : K.Strong incl₁` is kept but not used by the proof (a comparison of `d₁` is a hypothesis of clause 3). The last sentence of the English statement (other natural parameter layouts) is not formalized: `NaturalParameterLayout` has no placement data. Hard edges `4.10 → 6.5`, `4.8 → 6.5` and `6.3 → 6.5` added (the English proof says Proposition 6.3 identifies the full placed comparisons; in Lean its `PlacedTester` is the tester of `ClosedLevel`); `6.4 → 6.5` stays hard (the English proof applies Lemma 6.4, and the Lean proof reaches the same `compact_placement` through Lemma 4.10). Theorem 6.6 is done (next paragraph). By hard edges alone `lemma_5_4`, `lemma_5_5`, `proposition_5_8`, `proposition_5_9` and `lemma_6_1` do not reach the apex (`lemma_6_1` has only the soft edge to `proposition_6_3`); the header of `holes-edges.txt` now says so.

**Theorem 6.6 is done, with a repaired statement.** The old Lean form quantified over a bare `WorkingScheme` with unconstrained `g` and ad-hoc vertex matching (`SameGaloisType` / scheme amalgamation), which is refutable. It is now the presentation-level packaging of `ClosedLevel.amalgamation` and `ClosedLevel.tuple_amalgamation_iff` under `hL : ClosedLevel K E D g μ`: strong `μ`-extensions of a `μ`-model amalgamate, and an amalgam identifying two bounded tuples exists iff their diagrams agree on parameter queries of size at most `g(σ) + ℓ` at levels `ρ < μ`. The English ω-tower / Lem 6.4–6.5 argument is already the engine of Theorem 4.11 (2); Section 6 numbering packages that. Hard edge `4.11 → 6.6`; `6.5 → 6.6` softened (English narrative). Corollary 6.7 is done (next paragraph).

**Corollary 6.7 is done, with a repaired statement** (`AEC/Section6/LargerLevelRealization.lean`). The old Lean form quantified over a bare `WorkingScheme` (`Tail` / `SystemArrow` / `permitted`) with no closed levels, strongness, sizes or testing bound for the Theorem 4.11 engine to use, and it had neither the prescribed tuple nor the type clause of the English statement. It is now at the level of a presentation, like Theorem 6.6, under two closed levels `hν : ClosedLevel K E D g ν`, `hμ : ClosedLevel K E D g μ`, `ν < μ`, for a strong `f : A → B` of `ν`-models and a strong `i : A → N` into a `μ`-model. It has three clauses:
1. realization: a strong `F : B → N` with `F ∘ f = i` (`exists_strong_embedding_into_larger_base`, the empty tuple in clause 2);
2. prescribed tuple: for `d : α → B`, `z : α → N` with `#α < ν`, if the diagrams of `(d, f p)` and `(z, i p)` agree at the bounded levels `ρ < ν` over all `p : β → A` with `#β ≤ g(#α ⊔ ℵ₀) + ls K`, there is such an `F` with `F ∘ d = z` (`exists_strong_embedding_into_larger`);
3. actual `ν`-types: a tuple `x : α → N` with `#α < ν` lies in a strong `ν`-submodel `B'` of `N` containing `A`, and the diagrams of `(x, i p)` in `N` and of its copy in `B'` agree at every bounded level `ρ < ν` (`exists_actual_nu_type`: exact-size strong hull, coherence, `D.of_strong`).

Proof of clause 2. Identify `N` with its chart `E(Below μ)` (categoricity at `μ`). The images of `A` and `z` are at most `ν` terms, so they lie in `N₀ = E(S)` for a suborder `S ⊆ Below μ` of size `ν` (`exists_suborder_cover`), and `A → N₀` is strong by coherence. `B` and `N₀` are `ν`-sized strong extensions of `A` whose tuples pass the tests, so Theorem 4.11 (2) at `ν` (`ClosedLevel.exists_tuple_amalgam`) gives a `ν`-sized amalgam `P` over `A` identifying `d` with `z`. Now `N₀ → N` is an order map of the presentation and `μ ≥ t(ν)` is a categoricity cardinal, so the countable tower of Theorem 4.11 at the source level `ν` (`exists_strong_embedding_over`, with target chart `J = Below μ`) embeds `P` into `N` over `N₀`; the target is not enlarged. The English proof runs the exhaustion of Theorem 6.6 directly into `N`: it places each new tuple in a chart of `N` and uses saturation at `μ` to realize the joint diagram of the placed tuple, `A` and the previously assigned list back in `N`. That saturation step is not formalized. A direct Lean version by lift extensions was tried and not closed: a lift found over the chart of `A` lives in a presentation `E(J₁)`, and `D.exists_transport` into `N` matches the previously assigned list but not the image of `A`; fixing all of `A` would take a comparison of length `ν` between its images in `N` and in `E(J₁)`, and `D.of_strong` from the `ν`-model `A` does not give one (`t(ν) > ν`). Passing through `N₀ = E(S)` makes the inclusion into `N` an order map, where the level-`ν` comparisons of Theorem 4.11 apply. Hard edge `4.11 → 6.7`; `6.6 → 6.7` softened (the English proof reuses the exhaustion of Theorem 6.6; the Lean proof calls `ClosedLevel.exists_tuple_amalgam` and `exists_strong_embedding_over`, not `theorem_6_6`). Soft edge `corollary_6_7 → lemma_6_9` (English 6.9 does not use Cor 6.7). Theorem 6.10 is unblocked (hard `lemma_6_9 → theorem_6_10`).

**Lemma 6.9 is done for `SingleModelData`.** The chain is `infra_69_recursion_tail`, then `infra_69_assemble` at a same-level tuple `p.ν = μ`. Theorem 6.10 is restated the same way; `stationary_free_extension_exists` is assembled and blocked on E5d′–E5e (`infra_610_majority_matches_root`, `infra_610_root_galois`; E5 support, `moved_majority`, and `root_majority` done). Majority uniqueness is proved. No constant-family alternate.

**Wired (intended use, reach apex):** `5.6 → 9.3, 10.2`; `5.7 → 9.3, 10.6, 10.8`;
`2.3 → 1.2`; `3.11 → 4.2, 5.8`; `4.2 → 4.9, 4.10, 4.11`; `4.3 → 4.10, 4.11`; `4.5 → 6.1`; `4.6 → 4.9`; `4.7 → 4.8, 12.5`; `4.8 → 4.10, 4.11, 6.3, 6.5`; `4.10 → 4.11, 6.5`; `6.3 → 6.5`; `6.4 → 6.5`; `4.11 → 5.6, 6.6, 6.7`; `infra_69_place_on_fills → infra_69_assemble → 6.9` (hard; 6.9 done for `SingleModelData`); `infra_610_move_query → infra_610_free_root / infra_610_param_freeing_qPres → infra_610_chart_support → infra_610_moved_majority → infra_610_root_majority + infra_610_root_galois → infra_610_chart_prescriptions → infra_610_place_prescriptions → infra_610_majority_of_placement → infra_610_majority_prescription → infra_610_place_on_B → stationary_free_extension_exists → 6.10` with `infra_610_majority_matches_root → infra_610_majority_prescription` and `infra_610_galois_tests_of_placement → infra_610_majority_prescription` with `infra_610_closed_level → infra_610_same_galois → stationary_free_extension_exists` (hard; E5 support / moved_majority / root_majority done; open tips E5d′ matches_root, E5e root_galois); paper `5.4/5.5/6.1/6.5/4.6` → matching `infra_69_*` / `infra_55_*`; `6.9 → 6.10`; `6.14 → 12.6`; `13.5 → 10.9, 14.2`.
Full hard-edge list: [`holes-edges.txt`](holes-edges.txt). Target: every Results/paper
node reaches Thm 1.2 or 1.3; completed work should admit dead-code analysis of each edge.

| Decl | Title | Location |
|------|-------|----------|
| `theorem_3_11` | Theorem 3.11 | `AEC/Section3/Results.lean` (**done**: no `sorryAx`; recurring-profile pigeonhole `exists_asymmetric_common_setup` in `ReversalKill.lean`, Prop 3.9 alignment, `θ⁺ · a^θ` kill `exists_killed_copy` in `RenamingKill.lean` via chains of strong self-maps `selfChainRec`) |
| `proposition_4_3` | Proposition 4.3 | `AEC/Section4/Results.lean` (**done**: `prop43_hull_back_and_forth` in `Prop43BAF.lean`; hull back-and-forth on `HullMatch` stages, uses the new `StableDiagram.trans` field) |
| `lemma_4_5` | Lemma 4.5 | `AEC/Section4/Results.lean` (**done**: no `sorryAx`; mixed S⊕new occupancy closed in `fingerprint_same_order_and_occupancy`) |
| `lemma_4_6` | Lemma 4.6 | `AEC/Section4/BlockInterchange.lean` (**done**: English tree/repeat/orbit via `BlockRegions` + `lemma_4_5_with_E`; `DisjointBlockSwap` packaging is degenerate) |
| `lemma_4_7` | Lemma 4.7 | `AEC/Section4/Results.lean` (**done**: `type_u_witness_set_param`) |
| `proposition_4_8` | Proposition 4.8 | `AEC/Section4/Results.lean` (**done**: no `sorryAx`; `g σ = max ℵ₀ σ`, test set = joint support `testingSet`; `sameNaturalDiagram_restrict_iff` via the cut-lex amalgam `exists_linearOrder_amalgam` in `UniformTesting.lean`. Statement changes: `DiagramsDifferOnSubset` now compares the restrictions of the given placements, and the hypothesis `ℵ₀ ≤ σ` was added since `StableDiagram.of_strong` is only available for infinite `σ`) |
| `proposition_4_9` | Proposition 4.9 | `AEC/Section4/Results.lean` (**done**: no `sorryAx`; English support-profile obstruction `compact_placement` in `CompactPlacement.lean`: profiles over `S_X` (`SameProfile`, `SupportProfile.ofTerms`, at most `χ` codes `mk_profileCode_le`), no-event continuations `exists_inert_continuation`, no-event comparison by Lemma 4.6 on the slots `sameNaturalDiagram_of_sameProfile_noEvent`, local realizability by Prop 4.2 `exists_local_placement`, `σ⁺` stages with at most `σ` new events. Statement changes: added `[CategoricalUnbounded K]`, `ℵ₀ ≤ σ`, the natural-parameter clause `hnat` and the coherence clause `hcoh`; possibility needs no hypothesis since the prescription for `p` is the diagram of the tuple `q p` of `E(I)`) |
| `lemma_4_10` | Lemma 4.10 | `AEC/Section4/Results.lean` (**done**: no `sorryAx`; `boundedDiagramLift` in `BoundedDiagramLift.lean`: cofinal `χ = 2^(κ ⊔ σ)`, prescription `(φ ∘ d, p)` for a strong `φ : B → E(I)` fixing `p` (`exists_paramFixing`), `compact_placement` at `χ` (`exists_placement_lifting`), agreement of two lifts on `≤ g(σ)` positions (`agreeOn_of_lifts`) and hence everywhere by the placed tester, uniqueness `Placement.LiftsBounded.agreeOn_univ`, restriction `Placement.LiftsBounded.reindex`; the placed tester is the English Prop 4.8 over the base, `exists_placedTester` in `PlacedTesting.lean` (`FrozenData`, `Layout`, Lemma 4.7), exposed as `proposition_4_8_over_base`. Statement changes: the old statement was vacuous (each test clause assumed `D.t μ ≤ Model.card B` with `Model.card B = μ < D.t μ`); the lift clauses are now at bounded levels `ρ < μ`, `J` is produced with `D.t μ ≤ ‖E(J)‖`, uniqueness is the level-`μ` comparison over all of `A`; added `[CategoricalUnbounded K]`, `hcat : Categorical K μ`, `ℵ₀ ≤ σ`, `hg : PlacedTester K E D g`) |
| `theorem_4_11` | Theorem 4.11 | `AEC/Section4/Results.lean` (**done**: no `sorryAx`; `S` = closure points `μ > ℓ` of `{t, g}`, unbounded by `exists_closurePoint_ge` and categorical by Prop 4.3 (`categorical_of_closurePoint`) in `ClosedLevels.lean`. `ClosedLevelAmalgam.lean`: `A ≅ E(I)`, `I` of order type `μ`; `G = E(J)` of a categoricity size `≥ t(μ)`; `LiftsTuple` (a tuple of `E(J)` lifting the bounded diagrams over `A`), one step `exists_lift_extension` (Lemma 4.10 lift, uniqueness at level `μ`, transport into `G` by `StableDiagram.exists_transport`), countable tower of small strong submodels `exists_strong_tower`, each lifted stage strong by `to_strong` (`exists_strong_of_liftsTuple`), union `exists_strong_of_nat_exhaustion`, giving `exists_strong_embedding_over` and the amalgams `exists_amalgam_of_common_lift` / `exists_amalgam_of_agreeOn`; clause 2 from the placed tester `agreeOn_univ_of_tests` and necessity `StableDiagram.same_of_amalgam`. `ClosedLevelTypes.lean`: clauses `ClosedLevel.amalgamation`, `ClosedLevel.tuple_amalgamation_iff`, `ClosedLevel.singleton_types`; singleton codes = label + cuts of the finite support in `I` (`Placement.singletonCode`, `mk_singletonCode_le`, `Placement.AgreeOn.of_sameProfile_univ`). Statement changes: added `[CategoricalUnbounded K]`, `E : OrderPresentation K`, `hg : PlacedTester K E D g` (replacing monotone `g`); clause 2: added `ℵ₀ ≤ σ`, and the old right side, vacuous under `D.t μ ≤ Model.card Bᵢ`, is now the tests at the bounded levels `ρ < μ` over **all** parameter lists `p : β → A` with `#β ≤ g σ + ls K` (`β` is quantified inside the iff: with one fixed `β` the iff fails for small `β`; `+ ls K` because `PlacedTester` bounds positions of `I`, and `≤ g(σ)` positions support `≤ g(σ) + ℓ` elements); clause 3: the old form compared `x, y ∈ A` under `g₀ = g₁` on `A`, which forces `x = y` and is satisfied by any injection `A → μ`; now `code B f x` for elements of all `μ`-extensions `(B, f)` of `A`, with equal codes iff an amalgam over `A` identifies them (the old form is the case `B₀ = B₁ = A`)) |

Section 4 is complete: Theorem 4.11, its last hole, is done (hard deps 4.2, 4.3, 4.8, 4.10 closed).

### L1 — Section 5 after diagrams (1 open)

Proposition 5.6 is done (single-model working package on the closure points of `{t, g}` above `ℓ`). The remaining hole is the seed object `objectOfEmptyChain`.

| Decl | Title | Location |
|------|-------|----------|
| `proposition_5_6` | Proposition 5.6 | `AEC/Section5/Results.lean` (**done**: no `sorryAx`; `SingleModelData.scheme` in `SingleModelScheme.lean` and `SingleModelData.isWorkingPackage` in `SingleModelPackage.lean`. One vertex; objects at `μ` = `K`-structures on the carrier `μ.ord.ToType` in `K` (`SMObject`); arrows = strong maps; eligible = closure points of `{D.t, g}` above `ls K`; `E` from `exists_orderPresentation_of_categoricalUnbounded`, with `CategoricalUnbounded K` from `D`. `DiagramEq` compares two lists by `D.same` inside the presentation `E(ρ)` at every eligible `ρ` above both levels and the length, after canonical charts (`chart`, `push`); for lists bounded at both levels it is `D.same` in the models (`diagramEq_iff_sameD`); `diagram_iso` by Prop 4.3. Saturation `exists_saturation`: a Prop 4.3 automorphism of `E(max μ ν)` moves the base of the witness onto the actual list, then a strong hull of size `μ`. Statement changes: inputs stay `(K) (D) (g)`; the conclusion is now `∃ S W, IsWorkingPackage W ∧ HasPresentations W W.template ∧ (∀ μ hμ, Nonempty (W.Object μ hμ)) ∧ Nonempty S.Vertex ∧ Subsingleton S.Vertex ∧ (∀ κ, ∃ μ, κ ≤ μ ∧ μ ∈ W.eligible) ∧ ∀ μ ∈ W.eligible, IsClosurePoint {D.t, g} μ`, the hypotheses that Proposition 5.7 consumes. Needed the Definition 5.2 repairs above. Feeds Thm 9.3, Prop 10.2) |
| `infra_single_model_scheme` | Single-model WorkingScheme | `AEC/Section5/SingleModelScheme.lean` (**done**: `oneVertexShape`, `SMObject`, `SingleModelData`, `SingleModelData.DiagramEq`, `SingleModelData.scheme`; no `sorry`) |
| `infra_single_model_package` | Single-model package clauses | `AEC/Section5/SingleModelPackage.lean` (**done**: `nonempty_object`, `hasPresentations`, `hasMixedDownward`, `isSaturated`, `satisfiesExhaustion`, `hasChainUnions`, `isWorkingPackage`, `exists_directed_union`; no `sorry`) |
| `proposition_5_7` | Proposition 5.7 | `AEC/Section5/Results.lean` (**done**: no `sorryAx`; `exists_named_realization_of_arrow` via `wellOrder_arrow` + `diagram_preserved` in `NamedRealizationExistence.lean`; packaged with `namedWorkingScheme` / `isWorkingPackage_namedWorkingScheme` on `eligibleTail (μ0 ⊔ ℵ₀)`; the named scheme takes `#ι < μ0` and the tail bounds after the Definition 5.2 repairs) |
| `infra_template_fixed_support` | Template F(J+H) | `AEC/Section5/TermTemplate.lean` (**done**: `withFixedSupport`, `sumLexEmbedRight` / `sumLexEmbedLeftIncl`, `fixedSupportArrow`) |
| `infra_eligible_reclass` | Convention 5.3 tails / Lim | `AEC/Section5/EligibleSubclass.lean` (**done**: `eligibleTail`, `EligibleSubclass.tail` / `lim` / `aboveNamingThreshold`) |
| `infra_named_working_scheme` | Named WorkingScheme ctor | `AEC/Section5/NamedWorkingScheme.lean` (**done**: `WorkingScheme.IsStructIso` + `namedWorkingScheme` packer; no `sorry`) |
| `infra_named_working_package` | Named package transfer | `AEC/Section5/NamedPackageTransfer.lean` (**done**: `isWorkingPackage_namedWorkingScheme`; no `sorry`) |
| `objectOfEmptyChain` | Seed object at eligible level | `AEC/Section5/Results.lean` (**open**: nonempty chain unions no longer supply empty-index objects) |
| `proposition_5_8` | Proposition 5.8 | `AEC/Section5/Results.lean` (**done**: Lean residual via `diagram_iso` + `structural_iso`) |

### L2 — Section 6 unlock (Lem 6.9 infra board + package)

Waits on Section 5 working package. Lean: later Results import this module.

| Decl | Title | Location |
|------|-------|----------|
| `lemma_6_1` | Lemma 6.1 | `AEC/Section6/Results.lean` (**done**: no `sorryAx`; `WorkingScheme.exists_parameter_orbit_reps` in `ParameterOrbits.lean`: Lemma 4.5 at each vertex over the parameters and the exceptional occurrences (`exists_vertexwise_orbit_reps`), `AssemblesStructIso`, `W.diagram_iso` for the list of length `≤ χ < μ`; tail = eligible levels above `χ` and the threshold of Lemma 4.5. Statement changes: added `[CategoricalUnbounded K]`, `hedge`, `hcat`, `hχ`, `hiso : AssemblesStructIso W b`; `b` and `b + σ < χ` kept; see the paragraph above) |
| `proposition_6_3` | Proposition 6.3 | `AEC/Section6/Results.lean` (**done**: no `sorryAx`; `exists_layoutTestingFunction` in `LayoutTesting.lean` packages `exists_placedTester` as `TestingFunction layout` with `g.g σ = max σ g0 σ`. Statement repair: dropped `SameGaloisType`/`Tail`/`WorkingScheme` (English placed comparisons; amalgamation is Lem 6.5); inputs `[CategoricalUnbounded K]`, `E`, `D`, `layout`. Softened false `6.1→6.3` and `6.3→6.4`; hard `4.8→6.3`, `4.7→6.3`) |
| `lemma_6_4` | Lemma 6.4 | `AEC/Section6/Results.lean` (**done**: no `sorryAx`; alias of `proposition_4_9` / `compact_placement`. Statement repair: presentation-level with `hnat`/`hcoh`; dropped bare `WorkingScheme` and unused `b`; `hχ = ls K + σ < χ`. Hard `4.9→6.4`) |
| `lemma_6_5` | Lemma 6.5 | `AEC/Section6/Results.lean` (**done**: no `sorryAx`; `placedComparisons` in `PlacedComparisons.lean`: `exists_placedComparison` (`exists_boundedDiagramLift`), `placedComparison_unique` (`Placement.LiftsBounded.agreeOn_univ`), `placedComparison_agree_iff_tests` (← `agreeOn_univ_of_tests`, → `Placement.LiftsBounded.same_of_agreeOn`). Statement repair: dropped `SameGaloisType`/`Tail`/`WorkingScheme` and the monotone-only `g`; presentation-level under `ClosedLevel K E D g μ`, with existence, uniqueness over all of `A`, and the testing iff at bounded levels `ρ < μ` with `#β ≤ g σ + ls K`. Hard `4.10→6.5`, `4.8→6.5`, `6.3→6.5`; `6.4→6.5` kept hard) |
| `theorem_6_6` | Theorem 6.6 | `AEC/Section6/Results.lean` (**done**: no `sorryAx`; packages `ClosedLevel.amalgamation` and `ClosedLevel.tuple_amalgamation_iff`. Statement repair: dropped bare `WorkingScheme`/`SameGaloisType`/unconstrained `g`; presentation-level under `ClosedLevel K E D g μ`. Hard `4.11→6.6`; soft `6.5→6.6`) |
| `corollary_6_7` | Corollary 6.7 | `AEC/Section6/Results.lean` (**done**: no `sorryAx`; `exists_strong_embedding_into_larger`, `exists_strong_embedding_into_larger_base`, `exists_actual_nu_type` in `LargerLevelRealization.lean`: chart `N ≅ E(Below μ)`, suborder `S` of size `ν` covering the images of `A` and the tuple (`exists_suborder_cover`), `ClosedLevel.exists_tuple_amalgam` at `ν`, then `exists_strong_embedding_over` at `ν` into the chart of `N`. Statement repair: dropped bare `WorkingScheme`/`Tail`/`SystemArrow`; presentation-level under `ClosedLevel` at `ν < μ`, with realization, prescribed tuple (tests `#β ≤ g(#α ⊔ ℵ₀) + ls K` at `ρ < ν`) and actual `ν`-types. Hard `4.11→6.7`; soft `6.6→6.7`) |
| `infra_55_one_point_cut` | Infra: one-point cut | `AEC/Section5/OrderPatternRealization.lean` (**open**) |
| `infra_55_enumerate_added` | Infra: enumerate added | `AEC/Section5/OrderPatternRealization.lean` (**open**) |
| `infra_55_pattern_realize` | Infra: pattern realize | `AEC/Section5/OrderPatternRealization.lean` (**open**: was `order_pattern_realized_over_old`) |
| `infra_69_present_padded` | Infra: present padded | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_chart_iso` | Infra: chart iso | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_place_type` | Infra: place type | `AEC/Section6/UniformApproximations.lean` (**done**: placement ≤τ on the IsPadded well-ordered skeleton; that skeleton does not fill cuts) |
| `infra_69_pad_recursion` | Infra: σ⁺ profile recursion | `AEC/Section6/PaddedPlacement.lean` (**done**: `β₀`, `2^β+σ+b`, suprema at limits) |
| `infra_69_pad_recursion_closed` | Infra: recursion below the level | `AEC/Section6/PaddedPlacement.lean` (**done**: the hypothesis, not a `{D.t,g}`-closure theorem) |
| `infra_69_pad_exists_closed` | Infra: recursion-closed levels | `AEC/Section6/PaddedPlacement.lean` (**done**: cofinality-`ℵ₀` strong limits above one full recursion) |
| `infra_69_pad_downset` | Infra: down-set profile code | `AEC/Section6/PaddedPlacement.lean` (**done**: no `leastElt`; equal codes are `SameProfile`) |
| `infra_69_pad_count` | Infra: down-set profile count | `AEC/Section6/PaddedPlacement.lean` (**done**: at most `2^{\|S\|+σ+b}`) |
| `infra_69_pad_stage_card` | Infra: σ⁺ stage cardinals | `AEC/Section6/PaddedPlacement.lean` (**done**: stages and their union stay under the recursion) |
| `infra_69_pad_obstruction` | Infra: padded profile obstruction | `AEC/Section6/PaddedPlacement.lean` (**done**: `σ⁺` first-time events; reuses inert continuation, no-event comparison, event codes, local placement) |
| `infra_69_place_on_fills` | Infra: place on cut-filling chart | `AEC/Section6/UniformApproximations.lean` (**done**: under `infra_69_pad_recursion_closed`; one `Placement` over the padded chart lifting joints of size at most `max σ τ`) |
| `infra_69_shared_supports` | Infra: shared supports | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_cut_clusters` | Infra: cut clusters | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_separators` | Infra: separators | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_include_shared` | Infra: include shared | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_anchor_bound` | Infra: anchor bound | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_slot_assignment` | Infra: slot assignment | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_disjoint_regions` | Infra: disjoint regions | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_copy_cluster` | Infra: copy cluster | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_richness_arity` | Infra: richness arity | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_interpret_copies` | Infra: interpret copies | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_choose_supports` | Infra: choose supports | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_whole_block_diff` | Infra: whole-block diff | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_no_internal_hits` | Infra: no internal hits | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_lem61_off_hits` | Infra: Lem 6.1 off hits | `AEC/Section6/UniformApproximations.lean` (**done**: `SameNaturalDiagram` by `lemma_4_6_blockInterchange` on `ChartOffHit` / `CopyInterchange` in `OffHitBlock.lean`. Statement narrowed: the scheme sentence is `OffHitCopyDiagramEq`) |
| `infra_69_off_hit_diagramEq` | Infra: off-hit DiagramEq | `AEC/Section6/UniformApproximations.lean` (**done**: `OffHitCopyDiagramEq` on `SingleModelData`. `ChartOffHit.readCopy` is the occurrence reading of `movedJoint`; `Placement.Lifts`, `SameNaturalDiagram.same`, and `diagramEq_iff_sameD` give `D(vᵢ, Z) = p↾Z`. Caller supplies `hplaced` and `hread`) |
| `infra_69_hit_bound` | Infra: hit bound | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_finitary_exceptions` | Infra: finitary exceptions | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_subtuple_uniform` | Infra: subtuple uniform | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_uniformity_bounds` | Infra: uniformity bounds | `AEC/Section6/UniformApproximations.lean` (**open**) |
| `infra_69_assemble` | Infra: assemble approx seq | `AEC/Section6/UniformApproximations.lean` (**done** under `infra_69_pad_recursion_closed`: `present_padded`, chart equivalence, `place_on_fills`, `support_copy_sequence`) |
| `infra_69_recursion_tail` | Infra: recursion-closed tail | `AEC/Section6/UniformApproximations.lean` (**done**: eligible levels closed under `{D.t, g}` and under the `σ⁺` profile recursion at every smaller test size) |
| `infra_69_transfer_tuple` | Infra: push occurrences | `AEC/Section6/UniformApproximations.lean` (**done**: occurrence list along a carrier equivalence) |
| `infra_69_diagram_transport` | Infra: diagram transport | `AEC/Section6/UniformApproximations.lean` (**done** inside `P.scheme`: carrier equiv → permitted bijective arrow → `DiagramEq`) |
| `infra_69_transfer_sequence` | Infra: transfer approximation sequence | `AEC/Section6/UniformApproximations.lean` (**done**/retired: not the path to Theorem 6.10) |
| `lemma_6_9` | Lemma 6.9 | `AEC/Section6/Results.lean` (**done** for `SingleModelData` on `infra_69_recursion_tail`, by `infra_69_assemble`) |
| `infra_610_move_query` | Infra: move query B→A | `AEC/Section6/StationaryFreeExtension.lean` (**done**: saturate over concat, `diagram_iso` pullback into `A`) |
| `infra_610_chart_of_B` | Infra: E5a chart of B | `AEC/Section6/StationaryFreeExtension.lean` (**done**) |
| `infra_610_choose_chi` | Infra: E5a′ power-fixed χ | `AEC/Section6/StationaryFreeExtension.lean` (**done**) |
| `infra_610_free_root` | Infra: E5a″ empty-good free-root | `AEC/Section6/StationaryFreeExtension.lean` (**done**) |
| `infra_610_param_freeing_qPres` | Infra: E5b legacy param-freeing q/hnat/hcoh | `AEC/Section6/StationaryFreeExtension.lean` (**done**; retired from support) |
| `infra_610_majority_qPres` | Infra: E5b majority-valued q/hnat/hcoh/hinr | `AEC/Section6/StationaryFreeExtension.lean` (**done**) |
| `infra_610_chart_support` | Infra: E5c support package | `AEC/Section6/StationaryFreeExtension.lean` (**done**: majority `qPres`, `χ = seq.τ`) |
| `infra_610_moved_majority` | Infra: E5d moved majority | `AEC/Section6/StationaryFreeExtension.lean` (**done**) |
| `infra_610_majority_matches_root` | Infra: E5d′ match majority to placed root | `AEC/Section6/StationaryFreeExtension.lean` (**open**: returns `qPres` majority witness vs empty-majority joint; residual `DiagramEq` join) |
| `infra_610_root_majority` | Infra: E5d″ root majority field | `AEC/Section6/StationaryFreeExtension.lean` (**done**: packaging of `moved_majority`) |
| `infra_610_root_galois` | Infra: E5e placed-root Galois tests | `AEC/Section6/StationaryFreeExtension.lean` (**open**) |
| `infra_610_chart_prescriptions` | Infra: E5 assembler | `AEC/Section6/StationaryFreeExtension.lean` (**assembler**; blocked on E5e) |
| `infra_610_place_prescriptions` | Infra: E6 Lem 6.4 place prescriptions | `AEC/Section6/StationaryFreeExtension.lean` (**done**: `proposition_4_9` + chart-root `TupleOver` over `B` with `q.ν = μ`) |
| `infra_610_majority_of_placement` | Infra: majority clause after placement | `AEC/Section6/StationaryFreeExtension.lean` (**done**: packaging of chart-root `hmajority`) |
| `infra_610_galois_tests_of_placement` | Infra: E7 Galois diagram tests | `AEC/Section6/StationaryFreeExtension.lean` (**done**: unfold chart-root packaging of `data.hgalois`) |
| `infra_610_majority_prescription` | Infra: E5–E7 assembler | `AEC/Section6/StationaryFreeExtension.lean` (**blocked** on E5d′ `majority_matches_root`; no own `sorry`) |
| `infra_610_place_on_B` | Infra: place majority on B | `AEC/Section6/StationaryFreeExtension.lean` (**done**: packaging wrapper of `infra_610_majority_prescription`) |
| `infra_610_closed_level` | Infra: ClosedLevel for `P.g` | `AEC/Section6/StationaryFreeExtension.lean` (**done**: `ClosedLevel.of_closurePoint P.tester`; `SingleModelData` carries `PlacedTester`) |
| `infra_610_same_galois` | Infra: SameGaloisType free lift | `AEC/Section6/StationaryFreeExtension.lean` (**done**: `exists_tuple_amalgam` + `SMObject.ofModel` under `ClosedLevel` and diagram tests) |
| `stationary_free_extension_exists` | Infra: free-lift existence | `AEC/Section6/StationaryFreeExtension.lean` (**blocked** on E5d′–E5e; root_majority / E6 / E7 / closed-level / same-galois done; caller arity `c(σ)`) |
| `theorem_6_10` | Theorem 6.10 | `AEC/Section6/Results.lean` (**blocked** on `stationary_free_extension_exists`) |
| `lemma_6_11` | Lemma 6.11 | `AEC/Section6/Results.lean:349` |
| `proposition_6_12` | Proposition 6.12 | `AEC/Section6/Results.lean:367` |
| `proposition_6_13` | Proposition 6.13 | `AEC/Section6/Results.lean:379` |
| `proposition_6_15` | Proposition 6.15 | `AEC/Section6/Results.lean:407` |
| `corollary_6_16` | Corollary 6.16 | `AEC/Section6/Results.lean:425` |
| `lemma_6_17` | Lemma 6.17 | `AEC/Section6/Results.lean:437` |

(`lemma_6_14` is already proved; `lemma_6_1` is done and stays in the table for its statement changes.)

### L3 — Section 7 (9)

Lean: imports `AEC.Section6.Results`.

| Decl | Title | Location |
|------|-------|----------|
| `lemma_7_2` | Lemma 7.2 | `AEC/Section7/Results.lean:39` |
| `proposition_7_3` | Proposition 7.3 | `AEC/Section7/Results.lean:59` |
| `proposition_7_5` | Proposition 7.5 | `AEC/Section7/Results.lean:82` |
| `lemma_7_6` | Lemma 7.6 | `AEC/Section7/Results.lean:100` |
| `proposition_7_8` | Proposition 7.8 | `AEC/Section7/Results.lean:118` |
| `theorem_7_9` | Theorem 7.9 | `AEC/Section7/Results.lean:134` |
| `lemma_7_11` | Lemma 7.11 | `AEC/Section7/Results.lean:151` |
| `lemma_7_12` | Lemma 7.12 | `AEC/Section7/Results.lean:163` |
| `theorem_7_13` | Theorem 7.13 | `AEC/Section7/Results.lean:176` |

### L4 — Section 8 (5)

Lean: imports `Section5.Results` and `Section6.Results`. Soft paper chain after S7.

| Decl | Title | Location |
|------|-------|----------|
| `lemma_8_2` | Lemma 8.2 | `AEC/Section8/Results.lean:35` |
| `lemma_8_3` | Lemma 8.3 | `AEC/Section8/Results.lean:48` |
| `lemma_8_4` | Lemma 8.4 | `AEC/Section8/Results.lean:65` |
| `lemma_8_5` | Lemma 8.5 | `AEC/Section8/Results.lean:76` |
| `theorem_8_6` | Theorem 8.6 | `AEC/Section8/Results.lean:86` |

### L5 — Section 9 (7)

Lean: imports S5/S6 Results. Unlocks boundary story for later geometry.

| Decl | Title | Location |
|------|-------|----------|
| `proposition_9_1` | Proposition 9.1 | `AEC/Section9/Results.lean:35` |
| `corollary_9_2` | Corollary 9.2 | `AEC/Section9/Results.lean:50` |
| `theorem_9_3` | Theorem 9.3 | `AEC/Section9/Results.lean:57` |
| `lemma_9_5` | Lemma 9.5 | `AEC/Section9/Results.lean:87` |
| `theorem_9_6` | Theorem 9.6 | `AEC/Section9/Results.lean:96` |
| `lemma_9_7` | Lemma 9.7 | `AEC/Section9/Results.lean:119` |
| `theorem_9_8` | Theorem 9.8 | `AEC/Section9/Results.lean:129` |

### L6 — Section 10 (9)

Lean: imports S5/S6 Results. Soft chain after S9; feeds Corollary 10.10 into S11.

| Decl | Title | Location |
|------|-------|----------|
| `lemma_10_1` | Lemma 10.1 | `AEC/Section10/Results.lean:31` |
| `proposition_10_2` | Proposition 10.2 | `AEC/Section10/Results.lean:38` |
| `lemma_10_4` | Lemma 10.4 | `AEC/Section10/Results.lean:48` |
| `theorem_10_5` | Theorem 10.5 | `AEC/Section10/Results.lean:63` |
| `proposition_10_6` | Proposition 10.6 | `AEC/Section10/Results.lean:72` |
| `proposition_10_7` | Proposition 10.7 | `AEC/Section10/Results.lean:80` |
| `lemma_10_8` | Lemma 10.8 | `AEC/Section10/Results.lean:92` |
| `theorem_10_9` | Theorem 10.9 | `AEC/Section10/Results.lean:104` |
| `corollary_10_10` | Corollary 10.10 | `AEC/Section10/Results.lean:117` |

### L7 — Section 11 (8)

Lean: imports S5/S6 Results. Soft internal chain:
`claim_11_10 → claim_11_11 → claim_11_12 → claim_11_13 → theorem_11_9`
(plus `lemma_11_2` last clause after Corollary 10.10).

| Decl | Title | Location |
|------|-------|----------|
| `lemma_11_2` | Lemma 11.2 | `AEC/Section11/Results.lean:33` |
| `proposition_11_6` | Proposition 11.6 | `AEC/Section11/Results.lean:135` |
| `proposition_11_7` | Proposition 11.7 | `AEC/Section11/Results.lean:145` |
| `claim_11_10` | Claim 11.10 | `AEC/Section11/Results.lean:200` |
| `claim_11_11` | Claim 11.11 | `AEC/Section11/Results.lean:306` |
| `claim_11_12` | Claim 11.12 | `AEC/Section11/Results.lean:340` |
| `claim_11_13` | Claim 11.13 | `AEC/Section11/Results.lean:369` |
| `theorem_11_9` | Theorem 11.9 | `AEC/Section11/Results.lean:156` |

### L8 — Section 12 (4)

Waits on geometric systems / exact boundary story (soft: fewer-axis lifting).

| Decl | Title | Location |
|------|-------|----------|
| `theorem_12_2` | Theorem 12.2 | `AEC/Section12/Results.lean:29` |
| `lemma_12_3` | Lemma 12.3 | `AEC/Section12/Results.lean:65` |
| `lemma_12_5` | Lemma 12.5 | `AEC/Section12/Results.lean:84` |
| `lemma_12_6` | Lemma 12.6 | `AEC/Section12/Results.lean:99` |

### L9 — Section 14 transfer (4)

Chain: `lemma_14_2 → theorem_14_3 → corollary_14_4 → theorem_14_5`.

| Decl | Title | Location |
|------|-------|----------|
| `lemma_14_2` | Lemma 14.2 | `AEC/Section14/Results.lean:85` |
| `theorem_14_3` | Theorem 14.3 | `AEC/Section14/Results.lean:96` |
| `corollary_14_4` | Corollary 14.4 | `AEC/Section14/Results.lean:105` |
| `theorem_14_5` | Theorem 14.5 | `AEC/Section14/Results.lean:112` |

### L10 — Apex (2)

Uniform eventual categoricity and the qualitative form. Depend on the transfer
layer (and thus the whole stack).

| Decl | Title | Location |
|------|-------|----------|
| `theorem_1_2` | Theorem 1.2 | `AEC/Section1/Results.lean:22` |
| `theorem_1_3` | Theorem 1.3 | `AEC/Section1/Results.lean:28` |

---

## Layer size check

| Layer | Count |
|------:|------:|
| L0 | 0 |
| L1 | 1 |
| L2 | 8 |
| L3 | 9 |
| L4 | 5 |
| L5 | 7 |
| L6 | 9 |
| L7 | 8 |
| L8 | 4 |
| L9 | 4 |
| L10 | 2 |
| **Total** | **56** |
