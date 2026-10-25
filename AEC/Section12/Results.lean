module

public import AEC.Section12.PrescribedBoundaryIso
public import AEC.Section2.OrderPresentation
public import AEC.Section4.NaturalDiagram

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Theorem 12.2** (Exact geometric boundary lifting). At all sufficiently closed uniform
levels, a prescribed boundary isomorphism extends to an isomorphism of the tops, and that
isomorphism is an isomorphism of the systems. -/
theorem theorem_12_2 (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (X Y : GeometricSystem K n L)
    (h : PrescribedBoundaryIso K X Y) :
    ∃ e : (X.vertex Finset.univ).carrier ≃[K.τ] (Y.vertex Finset.univ).carrier,
      K.Strong e.toEmbedding ∧
      ∀ (s : Finset (Fin n)) (hs : s ≠ Finset.univ) (x : (X.vertex s).carrier),
        e (X.le (Finset.subset_univ s) x) =
          Y.le (Finset.subset_univ s) ((h.onFace s hs) x) := by
  sorry

/-- **Lemma 12.3** (Joint boundary comparisons). Assuming exact boundary lifting in fewer
axes, a prescribed boundary isomorphism preserves the bounded diagrams, computed in the top
models, of occurrence-tagged boundary lists. -/
theorem lemma_12_3 (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (X Y : GeometricSystem K n L)
    (h : PrescribedBoundaryIso K X Y) (D : StableDiagram K) {α : Type u}
    (xs : α → (X.vertex Finset.univ).carrier)
    (hfrom : ∀ i, ∃ (s : Finset (Fin n)) (hs : s ≠ Finset.univ) (x : (X.vertex s).carrier),
      xs i = X.le (Finset.subset_univ s) x)
    (hpres : ∀ {M N : Model K.τ} {β : Type u}
        (f : Language.Embedding K.τ M.carrier N.carrier) (zs : β → M.carrier)
        (σ : Cardinal.{u}) (hσ : #β ≤ σ) (hM : K.Mem M) (hN : K.Mem N)
        (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N),
        K.Strong f → D.same hσ hM hN hMcard hNcard zs (fun i => f (zs i)))
    (htrans : ∀ {M N P : Model K.τ} {β : Type u}
        (as : β → M.carrier) (bs : β → N.carrier) (cs : β → P.carrier)
        (σ : Cardinal.{u}) (hσ : #β ≤ σ)
        (hM : K.Mem M) (hN : K.Mem N) (hP : K.Mem P)
        (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N)
        (hPcard : D.t σ ≤ Model.card P),
        D.same hσ hM hN hMcard hNcard as bs →
        D.same hσ hN hP hNcard hPcard bs cs →
        D.same hσ hM hP hMcard hPcard as cs) :
    ∃ ys : α → (Y.vertex Finset.univ).carrier,
      (∀ i, ∃ (s : Finset (Fin n)) (hs : s ≠ Finset.univ) (x : (X.vertex s).carrier),
        xs i = X.le (Finset.subset_univ s) x ∧
        ys i = Y.le (Finset.subset_univ s) ((h.onFace s hs) x)) ∧
      ∀ (σ : Cardinal.{u}) (hσ : #α ≤ σ)
        (hX : D.t σ ≤ Model.card (X.vertex Finset.univ))
        (hY : D.t σ ≤ Model.card (Y.vertex Finset.univ)),
        (∀ i, ∃ (s : Finset (Fin n)) (hs : s ≠ Finset.univ) (x : (X.vertex s).carrier),
          xs i = X.le (Finset.subset_univ s) x ∧
          D.t σ ≤ Model.card (X.vertex s) ∧ D.t σ ≤ Model.card (Y.vertex s)) →
        D.same hσ (X.inK Finset.univ) (Y.inK Finset.univ) hX hY xs ys := by
  sorry

/-- **Lemma 12.5** (Testing on rationally tiled parameter orders). There is a monotone bound
`g(σ, τ)` such that two placements of tuples of length at most `σ`, in the presence of a
fixed tuple of length at most `τ`, agree over the tiled parameter layout once they agree on
queries of size at most that bound. -/
theorem lemma_12_5 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) :
    ∃ g : Cardinal.{u} → Cardinal.{u} → Cardinal.{u},
      (∀ σ τ σ' τ', σ ≤ σ' → τ ≤ τ' → g σ τ ≤ g σ' τ') ∧
      ∀ {I : Type u} [LinearOrder I] [Nonempty I] {α β ι : Type u}
        (σ τ : Cardinal.{u}) (hσ : #α ≤ σ) (hτ : #β ≤ τ)
        (hsum : #(α ⊕ β) ≤ σ + τ)
        (t s : α → SupportTerm E.lab E.arity I) (c : β → SupportTerm E.lab E.arity I),
        (∀ (q : ι → SupportTerm E.lab E.arity I) (hq : #ι ≤ g σ τ)
            (hquery : #((α ⊕ β) ⊕ ι) ≤ σ + τ + g σ τ),
          SameNaturalDiagram K E D (σ + τ + g σ τ) hquery
            (Sum.elim (Sum.elim t c) q) (Sum.elim (Sum.elim s c) q)) →
        SameNaturalDiagram K E D (σ + τ) hsum (Sum.elim t c) (Sum.elim s c) := by
  sorry

/-- **Lemma 12.6** (Realization using an unoccupied strip). A placed comparison whose
parameters avoid a convex strip `V` is realized by a tuple of `E(J)` that retains the
specified old entries. -/
theorem lemma_12_6 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) {J Jstar : Type u} [LinearOrder J] [LinearOrder Jstar]
    [Nonempty J] [Nonempty Jstar] (incl : J ↪o Jstar) {α : Type u}
    (σ : Cardinal.{u}) (hσ : #α ≤ σ)
    (zStar : α → SupportTerm E.lab E.arity Jstar) (old : Set α)
    (hold : ∀ i ∈ old, ∃ t : SupportTerm E.lab E.arity J,
      zStar i = SupportTerm.along incl t) :
    ∃ z : α → SupportTerm E.lab E.arity J,
      SameNaturalDiagram K E D σ hσ z zStar ∧
      ∀ i ∈ old, zStar i = SupportTerm.along incl (z i) := by
  sorry

end
end AEC
