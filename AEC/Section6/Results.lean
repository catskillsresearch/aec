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

/-- **Corollary 6.7** (Realization into a larger level). An arrow `A → B` at level `ν` and an
arrow `A → N` at a larger level `μ` extend to an arrow `B → N`. -/
theorem corollary_6_7 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ ν (hν : ν ∈ T) μ (hμ : μ ∈ T), ν < μ →
        ∀ (A : W.Object ν (Tail.mem hT hν)) (B : W.Object ν (Tail.mem hT hν))
          (N : W.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B))
          (g : SystemArrow K S (W.asSystem _ A) (W.asSystem _ N)),
          W.permitted (X := A) (Y := B) f → W.permitted (X := A) (Y := N) g →
          ∃ h : SystemArrow K S (W.asSystem _ B) (W.asSystem _ N),
            W.permitted (X := B) (Y := N) h ∧ SystemArrow.comp f h = g := by
  sorry

/-- **Lemma 6.9** (Uniform majority approximations). At sufficiently closed levels, a bounded
type has approximation sequences of every prescribed bounded infinite length. -/
theorem lemma_6_9 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (p : TupleOver K S W (Tail.mem hT hμ) A) (τ κ : Cardinal.{u}),
        #p.idx < μ → aleph0 ≤ τ → τ < μ → aleph0 ≤ κ → κ < μ →
        ∃ seq : ApproximationSequence p, seq.τ = τ ∧ #(seq.κIndex) = κ := by
  sorry

/-- **Theorem 6.10** (Stationary free extension). A type over `A` has a free lift to any arrow
`A → B` at a sufficiently closed level, and an actual type is free from `A` precisely when it
is that free lift. -/
theorem theorem_6_10 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B : W.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B))
        (hf : W.permitted (X := A) (Y := B) f)
        (p : TupleOver K S W (Tail.mem hT hμ) A),
        #p.idx < μ →
        ∃ q : TupleOver K S W (Tail.mem hT hμ) B, ∃ e : p.idx ≃ q.idx,
          IsFreeLift p q f hf e := by
  sorry

/-- **Lemma 6.11** (An average criterion for descent). A type whose restrictions to a long
sequence in `A` have the stated majority is the free lift of its restriction to `A`. -/
theorem lemma_6_11 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) ν (hν : ν ∈ T) (A : W.Object ν (Tail.mem hT hν))
        (B : W.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B))
        (hf : W.permitted (X := A) (Y := B) f)
        (q : TupleOver K S W (Tail.mem hT hμ) B)
        (seq : ApproximationSequence (q.restrict f hf)),
        ν ≤ μ → #q.idx < ν → seq.τ < ν → #(seq.κIndex) < ν →
        (∀ {ι : Type u} (Z : ι → Occurrence K S (W.asSystem _ B)), #ι ≤ seq.τ →
          ∃ Z0 : ι → Occurrence K S (W.asSystem _ A),
            IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z)) →
        IsFreeFrom f hf q := by
  sorry

/-- **Proposition 6.12** (Products of bounded types). Bounded types have a product over `A`,
independent of the choice of realization, symmetric, and commuting with free lifts. -/
theorem proposition_6_12 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (p q : TupleOver K S W (Tail.mem hT hμ) A),
        #p.idx < μ → #q.idx < μ →
        ∃ joint : TupleOver K S W (Tail.mem hT hμ) A,
          ∃ e : p.idx ⊕ q.idx ≃ joint.idx, IsProduct p q joint e := by
  sorry

/-- **Proposition 6.13** (Local character and continuity). A type over the union of a chain,
of length below the cofinality of the chain, is free from some stage. -/
theorem proposition_6_13 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (p : TupleOver K S W (Tail.mem hT hμ) A),
        #p.idx < μ →
        ∃ (ν : Cardinal.{u}) (hν : ν ∈ T) (A₀ : W.Object ν (Tail.mem hT hν))
          (f : SystemArrow K S (W.asSystem _ A₀) (W.asSystem _ A))
          (hf : W.permitted (X := A₀) (Y := A) f),
          ν ≤ μ ∧ IsFreeFrom f hf p := by
  sorry

/-- **Lemma 6.14** (Closure of a bounded support set). A bounded colored set of positions
outside a convex strip can be enlarged to a still bounded set that realizes every
order/equality/color pattern of length at most `χ` over its subsets of size at most `χ`. -/
theorem lemma_6_14 {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) :
    ∀ (S0 : Set J), #S0 ≤ lam →
      ∃ S : Set J, S0 ⊆ S ∧ #S ≤ (2 : Cardinal.{u}) ^ lam ∧
        ∀ {ι : Type u} (hι : #ι ≤ χ) (p : ι → J), (∀ i, p i ∈ S) →
          ∀ {n : ℕ} (q : Fin n → J), n ≤ χ →
            ∃ q' : Fin n → J, (∀ i, q' i ∈ S) ∧
              SameOrderDiagram (Sum.elim p q) (Sum.elim p q') ∧
              ∀ i, color (q i) = color (q' i) :=
  lemma_6_14_proof color χ lam hχ hlam

/-- **Proposition 6.15** (Universality of a fresh strip). Every same-level extension of a
presented object `A` embeds into the object obtained by inserting a fresh convex strip. -/
theorem proposition_6_15 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (hpack : HasChainUnions W) (hmix : HasMixedDownward W)
    (hsat : IsSaturated W) (hexh : SatisfiesExhaustion W) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ)),
        ∃ Ap : W.Object μ (Tail.mem hT hμ),
          ∃ incl : SystemArrow K S (W.asSystem _ A) (W.asSystem _ Ap),
            W.permitted (X := A) (Y := Ap) incl ∧
            ∀ (B : W.Object μ (Tail.mem hT hμ))
              (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B)),
              W.permitted (X := A) (Y := B) f →
              ∃ g : SystemArrow K S (W.asSystem _ B) (W.asSystem _ Ap),
                W.permitted (X := B) (Y := Ap) g ∧ SystemArrow.comp f g = incl := by
  sorry

/-- **Corollary 6.16** (Approximate retractions). For same-level `A ≤ B` there is a family of
arrows `B → A`, indexed by the level, such that each element of `A` is moved only finitely
often. -/
theorem corollary_6_16 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B : W.Object μ (Tail.mem hT hμ))
        (incl : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B)),
        W.permitted (X := A) (Y := B) incl →
        Nonempty (ApproximateRetraction K S W (Tail.mem hT hμ) A B incl) := by
  sorry

/-- **Lemma 6.17** (Descent through approximate retractions). If retractions of `U` onto `A`
fix `A` up to a finite set and preserve a smaller pair `A' ≤ U'`, then a bounded tuple of `U'`
is free from `A'` over `A`. -/
theorem lemma_6_17 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) ν (hν : ν ∈ T)
        (A : W.Object μ (Tail.mem hT hμ)) (U : W.Object μ (Tail.mem hT hμ))
        (A' : W.Object ν (Tail.mem hT hν)) (U' : W.Object ν (Tail.mem hT hν))
        (toA : SystemArrow K S (W.asSystem _ A') (W.asSystem _ A))
        (toU : SystemArrow K S (W.asSystem _ U') (W.asSystem _ U))
        (incl : SystemArrow K S (W.asSystem _ A) (W.asSystem _ U))
        (incl' : SystemArrow K S (W.asSystem _ A') (W.asSystem _ U')),
        ν ≤ μ →
        (htoA : W.permitted (X := A') (Y := A) toA) →
        (htoU : W.permitted (X := U') (Y := U) toU) →
        (hincl : W.permitted (X := A) (Y := U) incl) →
        W.permitted (X := A') (Y := U') incl' →
        (∀ v, (incl.onVertex v).comp (toA.onVertex v) =
          (toU.onVertex v).comp (incl'.onVertex v)) →
        (∃ (ι : Type u) (r : ι → SystemArrow K S (W.asSystem _ U) (W.asSystem _ A)),
          #ι = ν ∧ (∀ i, W.permitted (X := U) (Y := A) (r i)) ∧
          (∀ a : Occurrence K S (W.asSystem _ A),
            Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2}) ∧
          ∀ i v (x : ((W.asSystem _ U').obj v).carrier),
            ∃ y, toA.onVertex v y = (r i).onVertex v (toU.onVertex v x)) →
        ∀ {dIdx : Type u} (d : dIdx → Occurrence K S (W.asSystem _ U')),
          #dIdx < ν →
          IsFreeFrom toA htoA (asTuple incl hincl
            (fun i => ⟨(d i).1, toU.onVertex (d i).1 (d i).2⟩)) := by
  sorry

end
end AEC
