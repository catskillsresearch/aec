module

public import AEC.Section4.ClosedLevelAmalgam

@[expose] public section

/-!
# Placed comparisons of actual tuples (Lemma 6.5)

Let `μ` be a closed level (`ClosedLevel K E D g μ`), `I` a well-order of size `μ`, so that
`A = E(I)` is a well-ordered presentation of a `μ`-model, and let `incl : A → B` be a strong
extension of size `μ`. A bounded tuple `d` of `B` is an *actual tuple*; its *placed comparison*
is a placement `P` over `I` lifting the bounded diagrams `D(d, X; B)`, `X ⊆ A`, `|X| < μ`
(`Placement.LiftsBounded`), taken up to agreement over all of `A`
(`Placement.AgreeOn … Set.univ`).

English Lemma 6.5 has three clauses, none of which uses an amalgamation relation on types:

* `exists_placedComparison`: an actual tuple has a placed comparison (Lemma 4.10,
  `exists_boundedDiagramLift`).
* `placedComparison_unique`: it is unique as a diagram over all of `A`
  (`Placement.LiftsBounded.agreeOn_univ`).
* `placedComparison_agree_iff_tests`: two actual tuples, in two extensions of `A`, have equal
  comparisons if and only if their diagrams agree over the queries in `A` of size at most
  `g(σ) + ℓ`. Sufficiency is the placed tester (`agreeOn_univ_of_tests`, Proposition 4.8).
  Necessity is `Placement.LiftsBounded.same_of_agreeOn`: equal comparisons make one placement
  lift both tuples, so both have the diagram of its placed tuple; this gives agreement over
  every bounded query, not only the small ones.

`placedComparisons` is the conjunction, used by `lemma_6_5`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}} {E : OrderPresentation K} {D : StableDiagram K}
  {g : Cardinal.{u} → Cardinal.{u}} {μ : Cardinal.{u}} {I : Type u} [LinearOrder I]
  [Nonempty I] {B₀ B₁ : Model K.τ} {hB₀ : K.Mem B₀} {hB₁ : K.Mem B₁}
  {incl₀ : Language.Embedding K.τ (E.obj I).carrier B₀.carrier}
  {incl₁ : Language.Embedding K.τ (E.obj I).carrier B₁.carrier}
  {α : Type u}

/-- **Necessity.** Two actual tuples with the same placed comparison over `A` have the same
diagram with every bounded parameter tuple of `A`: by `Placement.LiftsBounded.of_agreeOn` the
placement of the first tuple lifts the second one as well, and both tuples have the diagram of
its placed tuple. No bound on the number of parameters is needed beyond `ρ < μ`. -/
theorem Placement.LiftsBounded.same_of_agreeOn (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    {d₀ : α → B₀.carrier} {d₁ : α → B₁.carrier} {P₀ P₁ : Placement E.lab E.arity I α}
    (h₀ : P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) (h₁ : P₁.LiftsBounded E D hB₁ incl₁ d₁ μ)
    (hag : P₀.AgreeOn E D P₁ Set.univ) {β : Type u} (ρ : Cardinal.{u}) (hρinf : aleph0 ≤ ρ)
    (hρ : ρ < μ) (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ ρ)
    (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁) :
    D.same hj hB₀ hB₁ ht₀ ht₁ (Sum.elim d₀ (fun b => incl₀ (p b)))
      (Sum.elim d₁ (fun b => incl₁ (p b))) := by
  have hIc : Model.card (E.obj I) = μ :=
    orderPresentation_obj_card E hI hL.ls_lt.le hL.inf
  have hPμ : ∀ (P : Placement E.lab E.arity I α) ρ, aleph0 ≤ ρ → ρ < μ →
      D.t ρ ≤ Model.card (E.obj P.J) := fun P ρ h1 h2 =>
    ((hL.t_lt h1 h2).le.trans hIc.ge).trans (mk_le_of_injective (E.map P.f).injective)
  have h₁' : P₀.LiftsBounded E D hB₁ incl₁ d₁ μ := h₁.of_agreeOn hag (hPμ P₁)
  have hJc := hPμ P₀ ρ hρinf hρ
  exact D.trans hj hB₀ _ hB₁ ht₀ hJc ht₁ _ _ _ (h₀ ρ hρinf hρ p hj ht₀ hJc)
    (D.symm hj hB₁ _ ht₁ hJc _ _ (h₁' ρ hρinf hρ p hj ht₁ hJc))

variable [CategoricalUnbounded K] [WellFoundedLT I]

/-- **Existence of the placed comparison.** The bounded diagrams of an actual tuple over the
bounded subsets of `A` are lifted by a placement over the well-ordered presentation of `A`
(Lemma 4.10). -/
theorem exists_placedComparison (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    (hs₀ : K.Strong incl₀) (hc₀ : Model.card B₀ = μ) {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ)
    (hσ : σ < μ) (hα : #α ≤ σ) (d₀ : α → B₀.carrier) :
    ∃ P₀ : Placement E.lab E.arity I α, P₀.LiftsBounded E D hB₀ incl₀ d₀ μ := by
  obtain ⟨P₀, hP₀, -⟩ := exists_boundedDiagramLift (hB := hB₀) (incl := incl₀) (d := d₀)
    hL.tester hL.closure hσinf hσ hL.ls_lt hL.cat hI hs₀ hc₀ hα
  exact ⟨P₀, hP₀⟩

/-- **Uniqueness of the placed comparison.** Two placements lifting the bounded diagrams of
one actual tuple have the same comparison over all of `A`. -/
theorem placedComparison_unique (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    (hc₀ : Model.card B₀ = μ) {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hσ : σ < μ)
    (hα : #α ≤ σ) {d₀ : α → B₀.carrier} {P P' : Placement E.lab E.arity I α}
    (h : P.LiftsBounded E D hB₀ incl₀ d₀ μ) (h' : P'.LiftsBounded E D hB₀ incl₀ d₀ μ) :
    P.AgreeOn E D P' Set.univ :=
  h.agreeOn_univ hL.tester hL.closure hσinf hσ hL.ls_lt hI hc₀ hα h'

/-- **Equal comparisons are detected by small queries.** The placed comparisons of two actual
tuples of length at most `σ` are equal if and only if the diagrams of the tuples agree over the
parameter tuples of `A` of length at most `g(σ) + ℓ`, at the bounded levels `ρ < μ`. -/
theorem placedComparison_agree_iff_tests (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    (hc₀ : Model.card B₀ = μ) (hc₁ : Model.card B₁ = μ) {σ : Cardinal.{u}}
    (hσinf : aleph0 ≤ σ) (hσ : σ < μ) (hα : #α ≤ σ) {d₀ : α → B₀.carrier}
    {d₁ : α → B₁.carrier} {P₀ P₁ : Placement E.lab E.arity I α}
    (h₀ : P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) (h₁ : P₁.LiftsBounded E D hB₁ incl₁ d₁ μ) :
    P₀.AgreeOn E D P₁ Set.univ ↔
      ∀ {β : Type u}, #β ≤ g σ + ls K → ∀ (ρ : Cardinal.{u}), aleph0 ≤ ρ → ρ < μ →
        ∀ (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ ρ)
          (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁),
          D.same hj hB₀ hB₁ ht₀ ht₁ (Sum.elim d₀ (fun b => incl₀ (p b)))
            (Sum.elim d₁ (fun b => incl₁ (p b))) := by
  constructor
  · intro hag β _ ρ hρinf hρ p hj ht₀ ht₁
    exact h₀.same_of_agreeOn hL hI h₁ hag ρ hρinf hρ p hj ht₀ ht₁
  · intro htest
    exact agreeOn_univ_of_tests hL hI hc₀ hc₁ hσinf hσ hα d₀ d₁ h₀ h₁ htest

/-- **Lemma 6.5** (Placed comparisons of actual tuples), at the level of a presentation. Let
`A = E(I)` be a well-ordered presentation of a `μ`-model at a closed level `μ`, and let `d₀`,
`d₁` be tuples of length at most `σ < μ` in two strong extensions of `A` of size `μ`. The
bounded diagrams of `d₀` over `A` have a placed comparison; it is unique over all of `A`; and
the comparisons of `d₀` and `d₁` are equal if and only if the diagrams of `d₀` and `d₁` agree
over the queries in `A` of size at most `g(σ) + ℓ`. -/
theorem placedComparisons (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    (hs₀ : K.Strong incl₀) (hc₀ : Model.card B₀ = μ) (hc₁ : Model.card B₁ = μ)
    {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hσ : σ < μ) (hα : #α ≤ σ)
    (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier) :
    (∃ P₀ : Placement E.lab E.arity I α, P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) ∧
    (∀ P P' : Placement E.lab E.arity I α,
      P.LiftsBounded E D hB₀ incl₀ d₀ μ → P'.LiftsBounded E D hB₀ incl₀ d₀ μ →
      P.AgreeOn E D P' Set.univ) ∧
    ∀ P₀ P₁ : Placement E.lab E.arity I α,
      P₀.LiftsBounded E D hB₀ incl₀ d₀ μ → P₁.LiftsBounded E D hB₁ incl₁ d₁ μ →
      (P₀.AgreeOn E D P₁ Set.univ ↔
        ∀ {β : Type u}, #β ≤ g σ + ls K → ∀ (ρ : Cardinal.{u}), aleph0 ≤ ρ → ρ < μ →
          ∀ (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ ρ)
            (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁),
            D.same hj hB₀ hB₁ ht₀ ht₁ (Sum.elim d₀ (fun b => incl₀ (p b)))
              (Sum.elim d₁ (fun b => incl₁ (p b)))) :=
  ⟨exists_placedComparison hL hI hs₀ hc₀ hσinf hσ hα d₀,
    fun _ _ h h' => placedComparison_unique hL hI hc₀ hσinf hσ hα h h',
    fun _ _ h₀ h₁ => placedComparison_agree_iff_tests hL hI hc₀ hc₁ hσinf hσ hα h₀ h₁⟩

end
end AEC
