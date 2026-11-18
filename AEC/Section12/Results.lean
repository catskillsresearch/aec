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
isomorphism is an isomorphism of the systems. 

**False as stated (kept open, needs hypotheses):** fails for arbitrary geometric systems on `0`
axes (`AEC.Audit.theorem_12_2_arbitrary_false`). -/
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
models, of occurrence-tagged boundary lists.

**False as formalized (kept open, needs hypotheses):** a `PrescribedBoundaryIso` only matches the
faces; nothing ties the top vertex to the free amalgam of its faces, so two faces may be disjoint
in `X` and identified in `Y` (`AEC.Audit.lemma_12_3_false`, two axes, AEC of all sets,
equality-pattern diagram). Needs the paper's hypothesis that both tops are generated freely
(independently) over the boundary. -/
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
queries of size at most that bound.

**Statement fix:** the query index type `ι` is now quantified inside the hypothesis. With `ι`
fixed outside, a query type larger than `g σ τ` makes the hypothesis vacuous and the lemma
false (`AEC.Audit.lemma_12_5_original_false`). -/
theorem lemma_12_5 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) :
    ∃ g : Cardinal.{u} → Cardinal.{u} → Cardinal.{u},
      (∀ σ τ σ' τ', σ ≤ σ' → τ ≤ τ' → g σ τ ≤ g σ' τ') ∧
      ∀ {I : Type u} [LinearOrder I] [Nonempty I] {α β : Type u}
        (σ τ : Cardinal.{u}) (hσ : #α ≤ σ) (hτ : #β ≤ τ)
        (hsum : #(α ⊕ β) ≤ σ + τ)
        (t s : α → SupportTerm E.lab E.arity I) (c : β → SupportTerm E.lab E.arity I),
        (∀ (ι : Type u) (q : ι → SupportTerm E.lab E.arity I) (hq : #ι ≤ g σ τ)
            (hquery : #((α ⊕ β) ⊕ ι) ≤ σ + τ + g σ τ),
          SameNaturalDiagram K E D (σ + τ + g σ τ) hquery
            (Sum.elim (Sum.elim t c) q) (Sum.elim (Sum.elim s c) q)) →
        SameNaturalDiagram K E D (σ + τ) hsum (Sum.elim t c) (Sum.elim s c) := by
  sorry

/-- **Lemma 12.6** (Realization using an unoccupied strip). A placed comparison whose
parameters avoid a convex strip `V` is realized by a tuple of `E(J)` that retains the
specified old entries.

**False as formalized (kept open, needs the strip hypothesis):** the paper's unoccupied convex
strip `V ⊆ J` is not in the statement, so `J` may be a single point and two distinct new terms
over `Jstar` cannot be realized over `J` (`AEC.Audit.lemma_12_6_false`, using the
equality-pattern presentation and diagram on the AEC of all sets). -/
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
