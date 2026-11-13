module

public import AEC.Section6.FreeExtension
public import AEC.Section6.ProductType
public import AEC.Section6.SchemeAmalgam
public import AEC.Section6.ApproximateRetraction
public import AEC.Section7.AllDominated
public import AEC.Section6.TestingFunction
public import AEC.Section6.LayoutTesting
public import AEC.Section5.PackageClauses
public import AEC.Section6.SupportClosure
public import AEC.Section6.ParameterOrbits
public import AEC.Section6.PlacedComparisons
public import AEC.Section4.ClosedLevelTypes
public import AEC.Section6.LargerLevelRealization
public import AEC.Section6.UniformApproximations
public import AEC.Section6.TestCardinal
public import AEC.Section6.StationaryFreeExtension
public import AEC.Section6.AverageDescent
public import AEC.Section6.BoundedProducts
public import AEC.Section6.LocalCharacter
public import AEC.Section6.FreshStrip
public import AEC.Section6.ApproxRetractionProof
public import AEC.Section6.DescentRetraction

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- `T` is an unbounded subclass of the eligible levels. -/
def Tail (S T : Set Cardinal.{u}) : Prop :=
  T ⊆ S ∧ ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ T

theorem Tail.mem {S T : Set Cardinal.{u}} (h : Tail S T) {μ : Cardinal.{u}}
    (hμ : μ ∈ T) : μ ∈ S :=
  h.1 hμ

/-- **Lemma 6.1** (Parameter orbits for a scheme). If `χ ^ σ = χ` and `χ > b + σ`, then at
every sufficiently closed level greater than `χ` there are at most `χ` diagrams of `σ`-tuples
over a parameter tuple of length at most `χ`.

Hypotheses on the scheme. For a bare `WorkingScheme` the statement fails (`DiagramEq` may be
equality of lists). Assuming a working package with presentations is not enough either:
`IsWorkingPackage` and `HasPresentations` do not make the automorphisms of the vertex models
structural isomorphisms, for instance when the isomorphisms of the scheme respect a colouring
of the occurrences by more than `χ` colours. The link to Lemma 4.5 is
`hiso : AssemblesStructIso W b`: strong vertex automorphisms fixing a set of at most `b`
occurrences assemble into structural isomorphisms.
`b` is the bound of the English statement, and `hb : b + σ < χ` is the English hypothesis. For
the single-model scheme of Proposition 5.6, `b = 0` (`SingleModelData.assemblesStructIso`); for
the named scheme of Proposition 5.7, `b` grows by the number of names
(`WorkingScheme.assemblesStructIso_named`). Further hypotheses: `hcat`, categoricity at the
levels (true at closure points), `hχ`, the bound of Lemma 4.5, and `hedge`, the shape has no
specified map.

`hedge` is needed by this proof. Lemma 4.5 gives automorphisms of the vertex models one vertex
at a time, with nothing forcing them to commute with the maps of a system, and
`AssemblesStructIso` assembles commuting families only. The number of vertices is not
restricted. A single vertex with a specified map to itself is not covered.

Proof: `WorkingScheme.exists_parameter_orbit_reps` (`ParameterOrbits.lean`), from Lemma 4.5 at
each vertex and `W.diagram_iso`. The tail is the levels above `χ` and the threshold of
Lemma 4.5. The clause of the English statement on block transpositions is `lemma_4_6`. -/
theorem lemma_6_1 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    [CategoricalUnbounded K]
    (W : WorkingScheme K S)
    (hedge : ∀ i j, ¬ S.specified i j)
    (hcat : ∀ μ ∈ W.eligible, Categorical K μ)
    (σ χ b : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hpow : χ ^ σ = χ)
    (hb : b + σ < χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ)
    (hiso : AssemblesStructIso W b) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : W.Object μ (Tail.mem hT hμ))
        {ι ρ : Type u} (hι : #ι ≤ σ) (hρ : #ρ ≤ χ)
        (params : ρ → Occurrence K S (W.asSystem _ X))
        (family : Set (ι → Occurrence K S (W.asSystem _ X))),
        ∃ reps : Set (ι → Occurrence K S (W.asSystem _ X)),
          #reps ≤ χ ∧ ∀ xs ∈ family, ∃ ys ∈ reps,
            W.DiagramEq (X := X) (Y := X)
              (Sum.elim xs params) (Sum.elim ys params) := by
  obtain ⟨κ0, h⟩ := W.exists_parameter_orbit_reps hedge hcat σ χ b hσ hpow hb hχ hiso
  have hT : Tail W.eligible {μ | μ ∈ W.eligible ∧ κ0 ≤ μ ∧ χ < μ} := by
    refine ⟨fun μ hμ => hμ.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ⟩ := W.eligible_unbounded (max κ (max κ0 (Order.succ χ)))
    exact ⟨μ, (le_max_left _ _).trans hle, hμ,
      ((le_max_left _ _).trans (le_max_right _ _)).trans hle,
      (Order.lt_succ χ).trans_le (((le_max_right _ _).trans (le_max_right _ _)).trans hle)⟩
  refine ⟨_, hT, fun μ hμ X ι ρ hι hρ params family => ?_⟩
  obtain ⟨reps, hreps, hrep⟩ := h μ hμ.1 hμ.2.1 hμ.2.2 X hι hρ params
  exact ⟨reps, hreps, fun xs _ => hrep xs⟩

/-- **Proposition 6.3** (Uniform testing for natural layouts). For each fixed natural layout
there is a monotone `g` with `g(σ) ≥ σ` such that two placed comparisons of tuples of length
at most `σ` over the whole-object presentation agree iff they agree on parameter queries of
size at most `g(σ)`. The bound is independent of any eligible level.

The old Lean form used `SameGaloisType` (scheme amalgamation) on the left of the iff, which
needs Theorem 6.6 and is not the English statement; English Prop 6.3 is the ordinal-vector
tester of Proposition 4.8 for placed comparisons (cf. Lemma 6.5: amalgamation is not required).
With `NaturalParameterLayout` still a descriptor skeleton, the conclusion is
`PlacedTester K E D g.g` packaged as `TestingFunction layout` (`LayoutTesting.lean`), from
`exists_placedTester`. Lemma 6.1 is not used. The placed comparisons of actual tuples are
Lemma 6.5; the Galois-type form is Theorem 6.6. -/
theorem proposition_6_3 (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K)
    (layout : NaturalParameterLayout.{u}) :
    ∃ g : TestingFunction layout,
      (∀ σ, aleph0 ≤ g.g σ) ∧ PlacedTester K E D g.g :=
  exists_layoutTestingFunction K E D layout

/-- **Lemma 6.4** (Compact placement for a scheme). Coherent prescriptions of diagrams for a
tuple of length at most `σ` over every parameter list of length at most `χ`, with
`χ ^ σ = χ` and `ls K + σ < χ`, are realized by one order enlargement of a well-ordered
presentation.

The old Lean form quantified over a bare `WorkingScheme` without coherence, which is
refutable (conflicting local prescriptions). English Lemma 6.4 works in a well-ordered
presentation chart; its combinatorial engine is Proposition 4.9 /
`compact_placement` (profiles, inert continuations, Lemma 4.6, σ⁺-obstruction). This is
that packaging under Section 6 numbering: same hypotheses and conclusion as
`proposition_4_9`. Unused English `b` is absorbed by Prop 4.9’s `hχ`. -/
theorem lemma_6_4 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K)
    (D : StableDiagram K) {I : Type u} [LinearOrder I] [Nonempty I] [WellFoundedLT I]
    {α : Type u} (σ χ : Cardinal.{u}) (hσinf : aleph0 ≤ σ) (hσ : #α ≤ σ)
    (hχ : ls K + σ < χ) (hpow : χ ^ σ = χ) (hI : K.Mem (E.obj I))
    (q : ∀ {β : Type u}, #β ≤ χ → (β → (E.obj I).carrier) → α ⊕ β → (E.obj I).carrier)
    (hnat : ∀ {β : Type u} (hβ : #β ≤ χ) (p : β → (E.obj I).carrier)
      (hpar : #β ≤ σ + χ) (hcardI : D.t (σ + χ) ≤ Model.card (E.obj I)),
      D.same hpar hI hI hcardI hcardI (fun b => q hβ p (Sum.inr b)) p)
    (hcoh : ∀ {β β' : Type u} (hβ : #β ≤ χ) (hβ' : #β' ≤ χ) (p : β → (E.obj I).carrier)
      (ι : β' → β) (hjoint : #(α ⊕ β') ≤ σ + χ)
      (hcardI : D.t (σ + χ) ≤ Model.card (E.obj I)),
      D.same hjoint hI hI hcardI hcardI
        (fun i => q hβ p (Sum.map id ι i)) (q hβ' (fun b => p (ι b)))) :
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (f : I ↪o J)
      (z : α → (E.obj J).carrier) (hJ : K.Mem (E.obj J)),
      ∀ {β : Type u} (hβ : #β ≤ χ) (p : β → (E.obj I).carrier)
        (hjoint : #(α ⊕ β) ≤ σ + χ)
        (hcardI : D.t (σ + χ) ≤ Model.card (E.obj I))
        (hcardJ : D.t (σ + χ) ≤ Model.card (E.obj J)),
        D.same hjoint hJ hJ hcardJ hcardJ
          (Sum.elim z (fun b => E.map f (p b)))
          (Sum.elim (fun a => E.map f (q hβ p (Sum.inl a)))
            (fun b => E.map f (q hβ p (Sum.inr b)))) :=
  proposition_4_9 K E D σ χ hσinf hσ hχ hpow hI q hnat hcoh

/-- **Lemma 6.5** (Placed comparisons of actual tuples). Let `A = E(I)` be a well-ordered
presentation of a `μ`-model at a closed level `μ`, and let `d₀`, `d₁` be tuples of length at
most `σ < μ` in strong extensions `B₀`, `B₁` of `A` of size `μ`. Then:

1. the diagrams of `d₀` over the bounded subsets of `A` have a placed comparison: a placement
   over `I` lifting them (`Placement.LiftsBounded`);
2. this comparison is unique as a diagram over all of `A` (`Placement.AgreeOn … Set.univ`);
3. the comparisons of `d₀` and `d₁` are equal if and only if the diagrams of `d₀` and `d₁`
   agree over the queries in `A` of size at most `g(σ) + ℓ`.

The old Lean form had `SameGaloisType` (scheme amalgamation) on the left of the iff. That is
Theorem 6.6, and English Lemma 6.5 does not use an amalgamation relation on types. Its `g`
was only monotone, so the iff failed for small `g`, and a bare `WorkingScheme` has no
presentation in which to place a tuple. The statement is now at the level of a presentation,
as for Proposition 6.3 and Lemma 6.4, with the hypotheses of Lemma 4.10 and Theorem 4.11 (2):

* `hL : ClosedLevel K E D g μ` (`g` is a `PlacedTester`, `μ > ℓ` is a closure point of
  `{t, g}` and a categoricity cardinal) replaces the tail of eligible levels;
* the tests are at the bounded levels `ρ < μ`, over all parameter lists `p : β → A` with
  `#β ≤ g σ + ls K` (`β` is quantified inside the iff; `+ ls K` because `PlacedTester` bounds
  positions of `I`, and at most `g(σ)` positions support at most `g(σ) + ℓ` elements);
* `σ` is any infinite bound on the length, in place of `|v| + ℵ₀`.

`hs₁` is not used by the proof: a comparison of `d₁` is assumed in clause 3, and its existence
is clause 1 with the two extensions exchanged. The last sentence of the English statement
(other natural parameter layouts) is not formalized, since `NaturalParameterLayout` carries no
placement data.

Proof: `placedComparisons` (`PlacedComparisons.lean`). Existence and uniqueness are Lemma 4.10
(`exists_boundedDiagramLift`, `Placement.LiftsBounded.agreeOn_univ`). In clause 3, sufficiency
is the placed tester of Proposition 4.8 (`agreeOn_univ_of_tests`); for necessity, equal
comparisons make the placement of `d₀` lift `d₁` as well, so both tuples have the diagram of
its placed tuple (`Placement.LiftsBounded.same_of_agreeOn`). -/
theorem lemma_6_5 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K)
    (g : Cardinal.{u} → Cardinal.{u})
    {μ : Cardinal.{u}} (hL : ClosedLevel K E D g μ)
    {I : Type u} [LinearOrder I] [Nonempty I] [WellFoundedLT I] (hI : #I = μ)
    {B₀ B₁ : Model K.τ}
    (incl₀ : Language.Embedding K.τ (E.obj I).carrier B₀.carrier)
    (incl₁ : Language.Embedding K.τ (E.obj I).carrier B₁.carrier)
    (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁)
    (hs₀ : K.Strong incl₀) (hs₁ : K.Strong incl₁)
    (hc₀ : Model.card B₀ = μ) (hc₁ : Model.card B₁ = μ)
    {α : Type u} {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hσ : σ < μ) (hα : #α ≤ σ)
    (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier) :
    (∃ P₀ : Placement E.lab E.arity I α, P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) ∧
    (∀ P P' : Placement E.lab E.arity I α,
      P.LiftsBounded E D hB₀ incl₀ d₀ μ → P'.LiftsBounded E D hB₀ incl₀ d₀ μ →
      P.AgreeOn E D P' Set.univ) ∧
    (∀ P₀ P₁ : Placement E.lab E.arity I α,
      P₀.LiftsBounded E D hB₀ incl₀ d₀ μ →
      P₁.LiftsBounded E D hB₁ incl₁ d₁ μ →
      (P₀.AgreeOn E D P₁ Set.univ ↔
        ∀ {β : Type u}, #β ≤ g σ + ls K → ∀ (ρ : Cardinal.{u}),
          aleph0 ≤ ρ → ρ < μ → ∀ (p : β → (E.obj I).carrier)
            (hj : #(α ⊕ β) ≤ ρ)
            (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁),
          D.same hj hB₀ hB₁ ht₀ ht₁
            (Sum.elim d₀ (fun b => incl₀ (p b)))
            (Sum.elim d₁ (fun b => incl₁ (p b))))) :=
  placedComparisons hL hI hs₀ hc₀ hc₁ hσinf hσ hα d₀ d₁

/-- **Theorem 6.6** (Amalgamation and types for a scheme). At a closed level `μ`, strong
extensions of a `μ`-model amalgamate, and an amalgam identifying two bounded tuples exists if
and only if their diagrams agree on parameter queries of size at most `g(σ) + ℓ`.

The old Lean form quantified over a bare `WorkingScheme` with an unconstrained `g`, which is
refutable (small `g`; arbitrary `DiagramEq`). English Theorem 6.6 works at sufficiently closed
levels with the testing bound of Proposition 6.3 / 4.8; its ω-tower argument is the engine of
Theorem 4.11 (2) in `ClosedLevelAmalgam` / `ClosedLevelTypes`. This is that packaging under
Section 6 numbering: `ClosedLevel.amalgamation` and `ClosedLevel.tuple_amalgamation_iff`.
Scheme-level `SameGaloisType` / `SchemeAmalgam` forms are deferred. -/
theorem theorem_6_6 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K)
    (g : Cardinal.{u} → Cardinal.{u})
    {μ : Cardinal.{u}} (hL : ClosedLevel K E D g μ)
    (A B₀ B₁ : Model K.τ)
    (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
    (f₁ : Language.Embedding K.τ A.carrier B₁.carrier)
    (hA : K.Mem A) (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁)
    (hf₀ : K.Strong f₀) (hf₁ : K.Strong f₁)
    (hcA : Model.card A = μ) (hc₀ : Model.card B₀ = μ) (hc₁ : Model.card B₁ = μ) :
    (∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
        (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
        K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧ Model.card P = μ ∧
        ∀ x, g₀ (f₀ x) = g₁ (f₁ x)) ∧
    ∀ {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hσ : σ < μ)
      {α : Type u} (hα : #α ≤ σ)
      (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier),
      (∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
          (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
          K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧
          (∀ x, g₀ (f₀ x) = g₁ (f₁ x)) ∧ ∀ i, g₀ (d₀ i) = g₁ (d₁ i)) ↔
        ∀ {β : Type u} (_ : #β ≤ g σ + ls K) (ρ : Cardinal.{u})
          (_ : aleph0 ≤ ρ) (_ : ρ < μ) (p : β → A.carrier)
          (hjoint : #(α ⊕ β) ≤ ρ)
          (h₀ : D.t ρ ≤ Model.card B₀) (h₁ : D.t ρ ≤ Model.card B₁),
          D.same hjoint hB₀ hB₁ h₀ h₁
            (Sum.elim d₀ (fun b => f₀ (p b)))
            (Sum.elim d₁ (fun b => f₁ (p b))) :=
  ⟨hL.amalgamation A B₀ B₁ f₀ f₁ hA hB₀ hB₁ hf₀ hf₁ hcA hc₀ hc₁,
    fun {σ} hσinf hσ {α} hα d₀ d₁ =>
      hL.tuple_amalgamation_iff (σ := σ) hσinf hσ (α := α) hα A B₀ B₁ f₀ f₁ d₀ d₁
        hA hB₀ hB₁ hf₀ hf₁ hcA hc₀ hc₁⟩

/-- **Corollary 6.7** (Realization into a larger level). Let `ν < μ` be closed levels, `f : A → B`
a strong map of `ν`-models and `i : A → N` a strong map into a `μ`-model. Then:

1. a strong map `B → N` extends `i`;
2. the image of a tuple `d` of `B` of length less than `ν` may be prescribed as a tuple `z` of
   `N` whose diagrams over the queries in `A` of size at most `g(|d| + ℵ₀) + ℓ`, at the bounds
   `ρ < ν`, already match those of `d`;
3. a tuple of `N` of length less than `ν` lies in a strong `ν`-submodel `B'` of `N` containing
   `A` (an actual `ν`-type over `A`), and its diagrams with the parameters of `A` at the bounds
   `ρ < ν` are the same in `N` and in `B'` (the mixed comparisons agree).

The old Lean form quantified over a bare `WorkingScheme` (`Tail` / `SystemArrow` / `permitted`)
with no closed levels, strongness, sizes or testing bound, which is refutable, and it had
neither the prescribed tuple nor the type clause. The statement is now at the level of a
presentation under two closed levels, as for Theorem 6.6. The scheme-level form is deferred.

Proof: `exists_strong_embedding_into_larger`, `exists_strong_embedding_into_larger_base` and
`exists_actual_nu_type` (`LargerLevelRealization.lean`). For clause 2, identify `N` with its
chart `E(Below μ)`; the images of `A` and `z` lie in `N₀ = E(S)` for a suborder `S` of size `ν`
(`exists_suborder_cover`). Theorem 4.11 (2) at `ν` (`ClosedLevel.exists_tuple_amalgam`)
amalgamates `B` and `N₀` over `A`, identifying `d` with `z`, in a `ν`-model `P`. Since
`N₀ → N` is an order map of the presentation and `μ ≥ t(ν)` is a categoricity cardinal, the
countable tower of Theorem 4.11 at the source level `ν` (`exists_strong_embedding_over`) embeds
`P` into `N` over `N₀`, without enlarging the target. Clause 1 is the case of the empty tuple.
Clause 3 is an exact-size strong hull, coherence and `D.of_strong`. `theorem_6_6` is not
called. -/
theorem corollary_6_7 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K)
    (g : Cardinal.{u} → Cardinal.{u})
    {ν μ : Cardinal.{u}} (hν : ClosedLevel K E D g ν) (hμ : ClosedLevel K E D g μ)
    (hlt : ν < μ)
    (A B N : Model K.τ)
    (f : Language.Embedding K.τ A.carrier B.carrier)
    (i : Language.Embedding K.τ A.carrier N.carrier)
    (hA : K.Mem A) (hB : K.Mem B) (hN : K.Mem N)
    (hf : K.Strong f) (hi : K.Strong i)
    (hcA : Model.card A = ν) (hcB : Model.card B = ν) (hcN : Model.card N = μ) :
    (∃ F : Language.Embedding K.τ B.carrier N.carrier,
        K.Strong F ∧ ∀ a, F (f a) = i a) ∧
    (∀ {α : Type u} (d : α → B.carrier) (z : α → N.carrier) (hα : #α < ν),
        (∀ {β : Type u} (_ : #β ≤ g (#α ⊔ aleph0) + ls K) (ρ : Cardinal.{u})
          (_ : aleph0 ≤ ρ) (_ : ρ < ν) (p : β → A.carrier)
          (hjoint : #(α ⊕ β) ≤ ρ)
          (h₀ : D.t ρ ≤ Model.card B) (h₁ : D.t ρ ≤ Model.card N),
          D.same hjoint hB hN h₀ h₁
            (Sum.elim d (fun b => f (p b)))
            (Sum.elim z (fun b => i (p b)))) →
        ∃ F : Language.Embedding K.τ B.carrier N.carrier,
          K.Strong F ∧ (∀ a, F (f a) = i a) ∧ ∀ j, F (d j) = z j) ∧
    (∀ {α : Type u} (x : α → N.carrier) (hα : #α < ν),
        ∃ (B' : Model K.τ) (hB' : K.Mem B')
          (j : Language.Embedding K.τ A.carrier B'.carrier)
          (y : α → B'.carrier),
          K.Strong j ∧ Model.card B' = ν ∧
          (∀ {β : Type u} (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ) (_ : ρ < ν)
            (p : β → A.carrier) (hjoint : #(α ⊕ β) ≤ ρ)
            (h₀ : D.t ρ ≤ Model.card N) (h₁ : D.t ρ ≤ Model.card B'),
            D.same hjoint hN hB' h₀ h₁
              (Sum.elim x (fun b => i (p b)))
              (Sum.elim y (fun b => j (p b))))) :=
  ⟨exists_strong_embedding_into_larger_base hν hμ hlt A B N f i hA hB hN hf hi hcA hcB hcN,
    fun {α} d z hα htest =>
      exists_strong_embedding_into_larger hν hμ hlt A B N f i hA hB hN hf hi hcA hcB hcN
        d z hα htest,
    fun {α} x hα => exists_actual_nu_type hν hμ hlt A N i hA hN hi hcA hcN x hα⟩

/-- **Lemma 6.9** (Uniform majority approximations). Let `|v| ≤ σ` and let `τ, κ` be bounded
infinite cardinals. At sufficiently closed levels, there are approximation sequences for
`p = tp(v/A)` of length `κ` at query size `τ`. They satisfy Definition 6.8(2) simultaneously
for every subtuple of `v`.

**S3.** Discharged by `ApproximationSequence.subtuple_uniform`: every approximation sequence,
hence every `seq` returned here, satisfies `seq.HasSubtupleBound`. For an injective reindexing
`ρ : ι → p.idx`, the restricted copies `fun i j => seq.family i (ρ j)` obey the same
`|Z| + ℵ₀` exception bound. `DiagramEq` of a full joint restricts to the subtuple joint by
`WorkingScheme.diagram_reindex` and `WorkingScheme.diagram_restrict`.

**S4 — uniformity.** The cardinal parameters of the construction depend only on `b`, `σ`,
`τ`, `κ`, and the fixed scheme, not on the level `μ` or the type `p`. Packaging hypotheses
discharge English “sufficiently closed / fixed scheme”; they are not extra conclusions:

* `HasPresentations`, `HasChainUnions` — padded chart (Lemmas 5.4 and 5.5).
* `hedge` — no specified structural maps.
* `hcat` — categoricity on eligible levels.
* `hiso : AssemblesStructIso W b` — automorphisms fixing at most `b` occurrences assemble
  into structural isomorphisms. `b` bounds labels and the fixed scheme data (Lemma 6.1).
* `χ`, `hpow`, `hb`, `hχ` — the uniform orbit threshold of Lemma 6.1, determined by `b`,
  `σ`, and the fixed scheme (`ls K` and `2 ^ (2 ^ σ)`). `hpow` is `χ ^ σ = χ`; `hb` is
  `b + σ < χ`.
* `σ`, `τ`, `κ` — the tuple bound, the query size, and the sequence length.

The proof-side uniformity sentence is `infra_69_uniformity_bounds`.

**S6.** A code at `c(σ)` (`lemma_6_9_code`) is a code for `p` in the transport sense of
Theorem 6.10. This lemma does not prove that transport.

**English gloss** (`UniformApproximations.lean`). The construction is the single-model
chain `infra_69_assemble`, at levels in `infra_69_recursion_tail` where the `σ⁺` profile
recursion lies below the level. A general `WorkingScheme` is not that chain.
`TupleOver.InBase` and `ApproximationSequence.ofConstFamily` are **not** a Lemma 6.9
proof. -/
theorem lemma_6_9 {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A) (τ κ : Cardinal.{u}),
        p.ν = μ →
        #p.idx ≤ σ → #p.idx < μ →
        aleph0 ≤ τ → τ < μ → aleph0 ≤ κ → κ < μ →
        κ * #p.idx < μ →
        ∃ seq : ApproximationSequence p, seq.τ = τ ∧ #(seq.κIndex) = κ ∧
          seq.HasSubtupleBound := by
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun μ hμ A p τ κ hνμ hσidx hidx hτ hμτ hκ hκμ hμκ => ?_⟩
  have hσμ : σ < μ := (Order.lt_succ σ).trans_le hμ.2
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let β₀ : Cardinal.{u} := max (max σ τ) b
  have hβ : β₀ < μ :=
    max_lt (max_lt hσμ hμτ) (max_lt (P.ls_lt (Tail.mem hT hμ)) (P.aleph0_lt (Tail.mem hT hμ)))
  have hclosed : infra_69_pad_recursion_closed σ b β₀ μ := hμ.1.2 β₀ hβ
  obtain ⟨seq, hτ', hκ'⟩ :=
    P.exists_approximationSequence (Tail.mem hT hμ) A p hνμ σ τ κ hσ hσμ hσidx hτ hμτ hκ
      hκμ hμκ hclosed
  exact ⟨seq, hτ', hκ', seq.subtuple_uniform⟩

/-- **Lemma 6.9, subtuples (S3).** The sequence from `lemma_6_9` satisfies Definition 6.8(2)
for every injective reindexing, by `ApproximationSequence.subtuple_uniform`. -/
theorem lemma_6_9_subtuple {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A) (τ κ : Cardinal.{u}),
        p.ν = μ →
        #p.idx ≤ σ → #p.idx < μ →
        aleph0 ≤ τ → τ < μ → aleph0 ≤ κ → κ < μ →
        κ * #p.idx < μ →
        ∃ seq : ApproximationSequence p, seq.τ = τ ∧ #(seq.κIndex) = κ ∧
          seq.HasSubtupleBound := by
  obtain ⟨T, hT, h⟩ := lemma_6_9 (P := P) σ hσ
  refine ⟨T, hT, fun μ hμ A p τ κ hνμ hσidx hidx hτ hμτ hκ hκμ hμκ => ?_⟩
  obtain ⟨seq, hτ', hκ', _⟩ := h μ hμ A p τ κ hνμ hσidx hidx hτ hμτ hκ hκμ hμκ
  exact ⟨seq, hτ', hκ', seq.subtuple_uniform⟩

/-- **Lemma 6.9, code at `c(σ)` (S5).** Same packaging as `lemma_6_9`, plus a testing
function `g : Cardinal → Cardinal`. Let `c := testCardinal b g`, so
`c σ = 2 ^ (g σ + b + σ + ℵ₀)`. Take `τ = c σ` and `κ = Order.succ (c σ)` (that is,
`κ = (c σ)⁺`). Whenever `τ < μ`, `κ < μ`, and `κ * #p.idx < μ`, the approximation sequence
has concatenated length bounded by a cardinal that depends only on `σ` and the fixed scheme
data `b` and `g`, not on the level or the type:

`#(seq.κIndex × p.idx) ≤ Order.succ (testCardinal b g σ)`.

**S6.** The concatenated diagram is a code for `p` in the transport sense of Theorem 6.10.
This theorem only bounds the length; it does not prove the transport. -/
theorem lemma_6_9_code {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    (b : Cardinal.{u}) (g : Cardinal.{u} → Cardinal.{u}) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A),
        p.ν = μ →
        #p.idx ≤ σ → #p.idx < μ →
        testCardinal b g σ < μ →
        Order.succ (testCardinal b g σ) < μ →
        Order.succ (testCardinal b g σ) * #p.idx < μ →
        ∃ seq : ApproximationSequence p,
          seq.τ = testCardinal b g σ ∧
          #(seq.κIndex) = Order.succ (testCardinal b g σ) ∧
          #(seq.κIndex × p.idx) ≤ Order.succ (testCardinal b g σ) := by
  obtain ⟨T, hT, h⟩ := lemma_6_9 (P := P) σ hσ
  refine ⟨T, hT, fun μ hμ A p hνμ hidxσ hidxμ hτμ hκμ hprod => ?_⟩
  have hτInf : aleph0 ≤ testCardinal b g σ := by
    rw [testCardinal, testPair]
    exact le_trans (cantor aleph0).le
      (power_le_power_left two_ne_zero
        (le_add_self : aleph0 ≤ (g σ + b + σ) + aleph0))
  have hκInf : aleph0 ≤ Order.succ (testCardinal b g σ) :=
    hτInf.trans (Order.le_succ _)
  have hσle : σ ≤ Order.succ (testCardinal b g σ) := by
    have hσc : σ < testCardinal b g σ := by
      rw [testCardinal, testPair]
      exact lt_of_lt_of_le (cantor σ)
        (power_le_power_left two_ne_zero
          (le_trans (le_add_self : σ ≤ (g σ + b) + σ)
            (le_self_add : (g σ + b) + σ ≤ ((g σ + b) + σ) + aleph0)))
    exact (le_of_lt hσc).trans (Order.le_succ _)
  have hσne : σ ≠ 0 := (aleph0_pos.trans_le hσ).ne'
  obtain ⟨seq, hτeq, hκeq, _⟩ :=
    h μ hμ A p (testCardinal b g σ) (Order.succ (testCardinal b g σ))
      hνμ hidxσ hidxμ hτInf hτμ hκInf hκμ hprod
  refine ⟨seq, hτeq, hκeq, ?_⟩
  have hcard : #(seq.κIndex × p.idx) = #(seq.κIndex) * #p.idx := by
    simp [mk_prod, lift_id]
  rw [hcard, hκeq]
  calc Order.succ (testCardinal b g σ) * #p.idx
      ≤ Order.succ (testCardinal b g σ) * σ := mul_le_mul' le_rfl hidxσ
    _ = Order.succ (testCardinal b g σ) := mul_eq_left hκInf hσle hσne

/-- **Theorem 6.10** (Stationary free extension). See `StationaryFreeExtension.lean` for the
English gloss. Clauses:

1. (Existence) At sufficiently closed levels, `p = tp(v/A)` with `#p.idx ≤ σ` has a free lift
   `p_B` over `B` along `A → B`.
2. (Transport) Bounded query/testing costs at `A` are computed by transporting long approximation
   sequences in `A` (`IsFreeLift` / `IsMajorityValue`).
3. (Scope) Single-level: every bounded query size; mixed-level: costs below the level of `A`
   (English uses Corollary 6.7 for the actual ν-restriction).
4. (Code / free-from) A Lemma 6.9 code at `c(σ)` transports under arrows; `IsFreeFrom` means the
   type is the free lift of its restriction to `A`.

**Statement repair.** Same packaging as Lemma 6.9: `SingleModelData` at recursion-closed levels,
same-level host `p.ν = μ`. Cross-scheme transfer is not used.

**Pinned.** Packaging calls `stationary_free_extension_exists` (E5e reflected Galois tests;
majority-only `IsFreeLift`). Move-query, place packaging, and majority uniqueness from
`few_exceptions` are proved. Scheme `SameGaloisType` amalgam is retained but deferred from
`IsFreeLift`. -/
theorem theorem_6_10 {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B : P.scheme.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
        (hf : P.scheme.permitted (X := A) (Y := B) f)
        (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A),
        p.ν = μ → #p.idx ≤ σ → #p.idx < μ →
        ∃ q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B,
          ∃ e : p.idx ≃ q.idx, IsFreeLift p q f hf e := by
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun μ hμ A B f hf p hνμ hσidx hidx => ?_⟩
  obtain ⟨q, e, h, _⟩ :=
    stationary_free_extension_exists P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 f hf p
      hνμ hσidx hidx
  exact ⟨q, e, h⟩

/-- **Lemma 6.11** (An average criterion for descent). At a recursion-closed level, a type
`q` over `B` whose restrictions to a long sequence in `A` have majority value `q ↾ Z` on
every short query `Z ⊆ B` is free from `A`.

Same packaging as Theorem 6.10: `SingleModelData`, same-level host `q.ν = μ`. The proof is
`infra_611_isFreeFrom` (`AverageDescent.lean`): a fresh Lemma 6.9 code for `q.restrict`,
the bridge through `infra_610_majority_eq_type` and `infra_610_majority_unique`, moved
parameter queries, and `infra_610_same_galois`. Mixed levels `ν < μ` are deferred. -/
theorem lemma_6_11 {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B : P.scheme.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
        (hf : P.scheme.permitted (X := A) (Y := B) f)
        (q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
        (seq : ApproximationSequence (q.restrict f hf)),
        q.ν = μ → #q.idx ≤ σ → #q.idx < μ →
        seq.τ < μ → seq.τ + aleph0 < #seq.κIndex → #seq.κIndex < μ →
        (∀ {ι : Type u}
          (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem _ B)),
          #ι ≤ seq.τ →
          ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem _ A),
            IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z)) →
        IsFreeFrom f hf q := by
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun μ hμ A B f hf q seq hνμ hidx hidxμ hτμ hκ hκμ hmaj => ?_⟩
  exact infra_611_isFreeFrom P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 f hf q seq
    hνμ hidx hidxμ hτμ hκ hκμ hmaj

/-- **Proposition 6.12** (Products of bounded types). At a recursion-closed level, bounded
types `p` and `q` over a same-level base have a product. Two products along one realization
of `p` are the same Galois type when their free lifts of `q` are anchored to one
approximation code: on every query up to that code's arity, both type joints are majority
values of the code on a single parameter list.

Symmetry, finite products, base change `(p ⊗ q)^B = p_B ⊗ q^B`, and mixed levels are
deferred. So is stationarity for an untied `IsFreeLift`: its majority witness need not be
the type joint (`same_head` stays demoted), so a bare `IsProduct` does not by itself fix
the cross-diagram. -/
theorem proposition_6_12 {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (p q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A),
        p.ν = μ → q.ν = μ → #p.idx ≤ σ → #q.idx ≤ σ → #p.idx < μ → #q.idx < μ →
        (∃ joint : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A,
          ∃ e : p.idx ⊕ q.idx ≃ joint.idx, IsProduct p q joint e) ∧
        (∀ (x : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
          (ex : p.idx ≃ x.idx)
          (y₁ y₂ : TupleOver K oneVertexShape P.scheme x.hν x.host)
          (ey₁ : q.idx ≃ y₁.idx) (ey₂ : q.idx ≃ y₂.idx)
          (seq : ApproximationSequence q)
          (joint₁ joint₂ : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
          (e₁ : p.idx ⊕ q.idx ≃ joint₁.idx) (e₂ : p.idx ⊕ q.idx ≃ joint₂.idx),
          y₁.ν = μ → y₂.ν = μ → joint₁.ν = μ → joint₂.ν = μ →
          σ + (P.g σ + ls K) ≤ seq.τ → seq.τ < μ →
          seq.τ + aleph0 < #seq.κIndex →
          (∀ {ι : Type u}
            (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem x.hν x.host)),
            #ι ≤ seq.τ →
            ∃ Z0 : ι → Occurrence K oneVertexShape
                (P.scheme.asSystem (Tail.mem hT hμ) A),
              IsMajorityValue seq Z0 y₁.hν y₁.host
                  (infra_612_anchored ey₁ y₁.incl y₁.val Z) ∧
                IsMajorityValue seq Z0 y₂.hν y₂.host
                  (infra_612_anchored ey₂ y₂.incl y₂.val Z)) →
          SameGaloisType joint₁ (x.join y₁)
            (e₁.symm.trans (Equiv.sumCongr ex ey₁)) (Equiv.refl (x.idx ⊕ y₁.idx)) →
          SameGaloisType joint₂ (x.join y₂)
            (e₂.symm.trans (Equiv.sumCongr ex ey₂)) (Equiv.refl (x.idx ⊕ y₂.idx)) →
          SameGaloisType joint₁ joint₂ (e₁.symm.trans e₂) (Equiv.refl joint₂.idx)) := by
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun μ hμ A p q hνp hνq hpσ hqσ hpμ hqμ =>
    ⟨infra_612_exists_product P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 p q hνp hνq hpσ hqσ hpμ hqμ,
      fun x ex y₁ y₂ ey₁ ey₂ seq joint₁ joint₂ e₁ e₂ hν₁ hν₂ hνj₁ hνj₂ hτ hτμ hκ hanchor
          hJ₁ hJ₂ =>
        infra_612_product_unique P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 p q hpσ hqσ x ex y₁ y₂
          ey₁ ey₂ hν₁ hν₂ seq hτ hτμ hκ hanchor joint₁ joint₂ e₁ e₂ hJ₁ hJ₂ hνj₁ hνj₂⟩⟩

/-- **Proposition 6.13** (Local character and continuity). At a recursion-closed level, a
same-level chain `(A_i : i < δ)` with union `A` has local character for tuples shorter than
`cf(δ)`: the type over `A` is free from some stage. If every stage restriction is free from a
fixed base `X ≤ A_0`, the union type is free from `X`.

Same packaging as Theorem 6.10. The chain is `SameLevelChain` (joint cover, not
`HasChainUnions`). The proof is `infra_613_local` (trap a Lemma 6.9 code in one stage, then
`infra_611_isFreeFrom`) and `infra_613_continuity` (`infra_613_freeFrom_trans` along the
cocone). Mixed levels and Section 7 `SatisfiesContinuity` stay deferred. -/
theorem proposition_6_13 {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (C : SameLevelChain P (Tail.mem hT hμ))
        (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) C.unionObj),
        p.ν = μ → #p.idx ≤ σ → #p.idx < C.δ.cof →
        (∃ (i : Ordinal.{u}) (hi : i < C.δ),
          IsFreeFrom (C.toUnion i hi) (C.toUnion_arrow i hi) p) ∧
        (∀ (X : P.scheme.Object μ (Tail.mem hT hμ))
          (g : SystemArrow K oneVertexShape
            (P.scheme.asSystem _ X)
            (P.scheme.asSystem _ (C.obj 0 C.hlim.1)))
          (hg : P.scheme.permitted (X := X) (Y := C.obj 0 C.hlim.1) g),
          (∀ (i : Ordinal.{u}) (hi : i < C.δ),
            IsFreeFrom
              (SystemArrow.comp g
                (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
              (P.scheme.comp g
                (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hg
                (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
              (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi))) →
          IsFreeFrom
            (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
            (P.scheme.comp g (C.toUnion 0 C.hlim.1) hg (C.toUnion_arrow 0 C.hlim.1))
            p) := by
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun μ hμ C p hνμ hidx hcof =>
    ⟨infra_613_local P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 C p hνμ hidx hcof,
      fun X g hg hAll =>
        infra_613_continuity P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 C p hνμ hidx hcof
          X g hg hAll⟩⟩

/-- **Lemma 6.14** (Closure of a bounded support set). A bounded colored set of positions,
together with a fixed support enumeration `T★` of size at most `λ`, can be enlarged to a set
of size at most `2^λ` that realizes every order/equality/color pattern of a query indexed by
at most `χ` positions, over every parameter list of size at most `χ` and over `T★`. A terminal
strip needs no side-of-`V` coloring: pass a constant `color`. -/
theorem lemma_6_14 {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) :
    ∀ {τ : Type u} (Tstar : τ → J) (_hτ : #τ ≤ lam) (S0 : Set J), #S0 ≤ lam →
      ∃ S : Set J, S0 ⊆ S ∧ (∀ t, Tstar t ∈ S) ∧ #S ≤ (2 : Cardinal.{u}) ^ lam ∧
        ∀ {ι : Type u} (hι : #ι ≤ χ) (p : ι → J), (∀ i, p i ∈ S) →
          ∀ {ρ : Type u} (hρ : #ρ ≤ χ) (q : ρ → J),
            ∃ q' : ρ → J, (∀ i, q' i ∈ S) ∧
              SameOrderDiagram (Sum.elim (Sum.elim p Tstar) q)
                (Sum.elim (Sum.elim p Tstar) q') ∧
              ∀ i, color (q i) = color (q' i) :=
  lemma_6_14_proof color χ lam hχ hlam

/-- **Infra `infra_615_terminal`.** Terminal-strip specialization: well-ordered `E(J)` extends
by `J ⊕ₗ (ℕ ×ₗ lvlOrder μ)` with fibers in the right summand, and every same-level strong
extension embeds over `E.map emb`. This is **not** Proposition 6.15 (paper ID requires a
two-sided / middle strip). -/
theorem infra_615_terminal {K : AbstractElementaryClass.{u}} (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (J : Type u) [LinearOrder J] [WellFoundedLT J] [Nonempty J],
        #J = μ →
        ∃ (H : Type u) (_ : LinearOrder H) (_ : WellFoundedLT H) (_ : Nonempty H)
          (emb : J ↪o (J ⊕ₗ H)),
          #H = μ ∧
          (∃ V : ℕ → Set (J ⊕ₗ H),
            (∀ n, IsConvexRegion (V n) ∧ #(V n) = μ) ∧
            Pairwise (Function.onFun Disjoint V) ∧
            (∀ n, V n ⊆ Set.range Sum.inr)) ∧
          ∀ (B : Model K.τ)
            (f : Language.Embedding K.τ (P.E.obj J).carrier B.carrier),
            K.Mem B → K.Strong f → Model.card B = μ →
            ∃ g : Language.Embedding K.τ B.carrier (P.E.obj (J ⊕ₗ H)).carrier,
              K.Strong g ∧ ∀ a, g (f a) = P.E.map emb a := by
  exact ⟨infra_615_closed P, infra_615_tail P, fun μ hμ J _ _ _ hJ => by
    have hμinf : ℵ₀ ≤ μ := P.aleph0_le (Tail.mem (infra_615_tail P) hμ)
    letI : LinearOrder (ℕ ×ₗ lvlOrder μ) := Prod.Lex.instLinearOrder ℕ (lvlOrder μ)
    exact ⟨ℕ ×ₗ lvlOrder μ, inferInstance, inferInstance, inferInstance,
      sumLexEmbedLeftIncl J (ℕ ×ₗ lvlOrder μ), freshOrder_card hμinf,
      ⟨freshFiber μ, fun n => ⟨freshFiber_convex μ n, freshFiber_card hμinf n⟩,
        freshFiber_disjoint μ, freshFiber_subset_inr μ⟩,
      fun B f hB hf hc => infra_615_exhaust_embed P hμ hJ f hB hf hc⟩⟩

/-- **Proposition 6.15** (Universality of a fresh strip). At a closed level, for `G = P.E` and
a nonempty linear order `J` of size `μ`, there is an enlargement `J⁺` obtained by inserting
into `J` a fresh convex strip of size `μ` with countably many disjoint convex μ-fibers, so
that old points of `J` may lie on **both** sides of the strip, and every same-level strong
extension of `E(J)` embeds strongly into `E(J⁺)` over `E.map emb`.

Paper ID matches the English middle-strip statement (for `G = F = P.E`). The terminal
specialization is `infra_615_terminal`, not this theorem. -/
theorem proposition_6_15 {K : AbstractElementaryClass.{u}} (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (J : Type u) [LinearOrder J] [Nonempty J],
        #J = μ →
        ∃ (Jplus : Type u) (_ : LinearOrder Jplus) (_ : Nonempty Jplus) (emb : J ↪o Jplus)
          (strip : Set Jplus) (V : ℕ → Set Jplus),
          #Jplus = μ ∧
          IsConvexRegion strip ∧ #strip = μ ∧
          (∀ n, IsConvexRegion (V n) ∧ #(V n) = μ ∧ V n ⊆ strip) ∧
          Pairwise (Function.onFun Disjoint V) ∧
          (∃ (a b : J), emb a < emb b ∧
            (∃ s ∈ strip, emb a < s ∧ s < emb b)) ∧
          ∀ (B : Model K.τ)
            (f : Language.Embedding K.τ (P.E.obj J).carrier B.carrier),
            K.Mem B → K.Strong f → Model.card B = μ →
            ∃ g : Language.Embedding K.τ B.carrier (P.E.obj Jplus).carrier,
              K.Strong g ∧ ∀ a, g (f a) = P.E.map emb a :=
  ⟨infra_615_closed P, infra_615_tail P, fun μ hμ J _ _ hJ =>
    infra_615_two_sided P hμ J hJ⟩

/-- **Corollary 6.16** (Approximate retractions). At a closed level, for same-level
`A ≤ B` in the single-model scheme there is a family of arrows `B → A`, indexed by the
level, such that each element of `A` is moved only finitely often. `A` is presented on
`lvlOrder μ ×ₗ (ℕ ×ₗ lvlOrder μ)`; each nonzero block is the fresh middle strip of
Proposition 6.15, and the exhaustion is postcomposed back onto `A`. -/
theorem corollary_6_16 {K : AbstractElementaryClass.{u}} (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B : P.scheme.Object μ (Tail.mem hT hμ))
        (incl : SystemArrow K oneVertexShape
          (P.scheme.asSystem (Tail.mem hT hμ) A)
          (P.scheme.asSystem (Tail.mem hT hμ) B)),
        P.scheme.permitted (X := A) (Y := B) incl →
        Nonempty (ApproximateRetraction K oneVertexShape P.scheme
          (Tail.mem hT hμ) A B incl) :=
  ⟨infra_615_closed P, infra_615_tail P, fun μ hμ A B incl _ =>
    corollary_6_16_family P hμ A B incl⟩

/-- **Lemma 6.17** (Descent through approximate retractions). At closed levels `ν ≤ μ`, if
arrows `rᵢ : U → A` almost-fix `A` and send `U'` into `A'`, then for every short tuple of
`U'` the actual type over `A` is the free lift of `tp(d/A'; U')`, with majority values the
large type joints. Mixed diagrams at arities below `ν` are included. Proof:
`infra_617_from_retractions` (`DescentRetraction.lean`): factor restrictions, SameGaloisType
from the square, ApproximationSequence from a short restr subsequence, mixed move-query, and
almost-identity exceptions. -/
theorem lemma_6_17 {K : AbstractElementaryClass.{u}} (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) ν (hν : ν ∈ T)
        (A : P.scheme.Object μ (Tail.mem hT hμ)) (U : P.scheme.Object μ (Tail.mem hT hμ))
        (A' : P.scheme.Object ν (Tail.mem hT hν)) (U' : P.scheme.Object ν (Tail.mem hT hν))
        (toA : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ A') (P.scheme.asSystem _ A))
        (toU : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ U') (P.scheme.asSystem _ U))
        (incl : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ A) (P.scheme.asSystem _ U))
        (incl' : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ A') (P.scheme.asSystem _ U')),
        ν ≤ μ →
        (htoA : P.scheme.permitted (X := A') (Y := A) toA) →
        (htoU : P.scheme.permitted (X := U') (Y := U) toU) →
        (hincl : P.scheme.permitted (X := A) (Y := U) incl) →
        (hincl' : P.scheme.permitted (X := A') (Y := U') incl') →
        (∀ v, (incl.onVertex v).comp (toA.onVertex v) =
          (toU.onVertex v).comp (incl'.onVertex v)) →
        ∀ {ι : Type u}
          (r : ι → SystemArrow K oneVertexShape
            (P.scheme.asSystem _ U) (P.scheme.asSystem _ A)),
          #ι = ν →
          (∀ i, P.scheme.permitted (X := U) (Y := A) (r i)) →
          (∀ a : Occurrence K oneVertexShape (P.scheme.asSystem _ A),
            Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2}) →
          (∀ i (x : ((P.scheme.asSystem _ U').obj PUnit.unit).carrier),
            ∃ y, toA.onVertex PUnit.unit y =
              (r i).onVertex PUnit.unit (toU.onVertex PUnit.unit x)) →
          ∀ {dIdx : Type u}
            (d : dIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U')),
            #dIdx < ν →
            IsFreeLift (asTuple incl' hincl' d)
              (asTuple incl hincl
                (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩))
              toA htoA (Equiv.refl dIdx) :=
  ⟨infra_615_closed P, infra_615_tail P, fun μ hμ ν hν A U A' U' toA toU incl incl'
      hνμ htoA htoU hincl hincl' hsq ι r hιcard hr halmost himg dIdx d hd =>
    infra_617_from_retractions P hν hμ hνμ A U A' U' toA toU incl incl'
      htoA htoU hincl hincl' hsq r hιcard hr halmost himg d hd⟩

end
end AEC
