module

public import AEC.Section9.BoundaryMap
public import AEC.Section6.Results
public import AEC.Section5.Results
public import AEC.Section4.StableDiagram

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Proposition 9.1** (Type correspondence under projection). At sufficiently closed levels,
equality of bounded diagrams in the retained sorts is equivalent before and after a projection
that preserves and reflects diagram equality, and free lifts correspond. -/
theorem proposition_9_1 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (C : WorkingScheme K S) (hC : IsWorkingPackage C) :
    ∃ T, ∃ hT : Tail C.eligible T,
      ∀ μ (hμ : μ ∈ T) ν (hν : ν ∈ T)
        (X : C.Object μ (Tail.mem hT hμ)) (Y : C.Object ν (Tail.mem hT hν))
        (f : SystemArrow K S (C.asSystem _ X) (C.asSystem _ Y))
        (hf : C.permitted (X := X) (Y := Y) f)
        {α : Type u} (xs ys : α → Occurrence K S (C.asSystem _ X)),
        #α < μ →
        C.DiagramEq (X := X) (Y := X) xs ys ↔
          C.DiagramEq (X := Y) (Y := Y)
            (fun i => ⟨(xs i).1, f.onVertex (xs i).1 (xs i).2⟩)
            (fun i => ⟨(ys i).1, f.onVertex (ys i).1 (ys i).2⟩) := by
  sorry

/-- **Corollary 9.2** (Lifting an extension of a projection). An arrow out of the projection of
`X` lifts to an arrow out of `X` in the original scheme. -/
theorem corollary_9_2 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (X Z : W.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K S (W.asSystem _ X) (W.asSystem _ Z)),
        W.permitted (X := X) (Y := Z) f →
        ∃ (X' : W.Object μ (Tail.mem hT hμ))
          (g : SystemArrow K S (W.asSystem _ X) (W.asSystem _ X'))
          (h : SystemArrow K S (W.asSystem _ Z) (W.asSystem _ X')),
          W.permitted (X := X) (Y := X') g ∧ W.permitted (X := Z) (Y := X') h ∧
          SystemArrow.comp f h = g := by
  sorry

/-- **Theorem 9.3** (Finite marked systems). For each finite `n` the `n`-fold marked increment
of the single-model scheme is a working scheme at sufficiently closed levels. -/
theorem theorem_9_3 (K : AbstractElementaryClass.{u}) (n : ℕ) :
    ∃ S : SystemShape.{u}, ∃ W : WorkingScheme K S, IsWorkingPackage W ∧
      #S.Vertex = (n + 1 : Cardinal.{u}) ∧ ∀ μ ∈ W.eligible, IsWorkingLevel μ := by
  sorry

/-- **Lemma 9.5** (Joint diagrams on the boundary). A boundary map between same-level `n`-axis
objects preserves bounded diagrams of their boundary unions. -/
theorem lemma_9_5 (K : AbstractElementaryClass.{u}) (n : ℕ)
    (J Kf : FaceFamily K n) (h : BoundaryMap K J Kf) (D : StableDiagram K)
    (hpres : ∀ {M N : Model K.τ} {β : Type u}
        (f : Language.Embedding K.τ M.carrier N.carrier) (zs : β → M.carrier)
        (σ : Cardinal.{u}) (hσ : #β ≤ σ) (hM : K.Mem M) (hN : K.Mem N)
        (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N),
        K.Strong f → D.same hσ hM hN hMcard hNcard zs (fun i => f (zs i)))
    (htrans : ∀ {M N P : Model K.τ} {β : Type u}
        (xs : β → M.carrier) (ys : β → N.carrier) (zs : β → P.carrier)
        (σ : Cardinal.{u}) (hσ : #β ≤ σ)
        (hM : K.Mem M) (hN : K.Mem N) (hP : K.Mem P)
        (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N)
        (hPcard : D.t σ ≤ Model.card P),
        D.same hσ hM hN hMcard hNcard xs ys →
        D.same hσ hN hP hNcard hPcard ys zs →
        D.same hσ hM hP hMcard hPcard xs zs) :
    ∀ {α : Type u} (s : Set (Fin n)) (hs : IsProper s)
      (xs : α → (J.obj s).carrier) (σ : Cardinal.{u})
      (hσ : #α ≤ σ)
      (hfaceJ : D.t σ ≤ Model.card (J.obj s))
      (hfaceK : D.t σ ≤ Model.card (Kf.obj s))
      (htopJ : D.t σ ≤ Model.card (J.obj Set.univ))
      (htopK : D.t σ ≤ Model.card (Kf.obj Set.univ)),
      D.same hσ (J.inK Set.univ) (Kf.inK Set.univ) htopJ htopK
        (fun i => J.incl (Set.subset_univ s) (xs i))
        (fun i => Kf.incl (Set.subset_univ s) (h.onFace hs (xs i))) := by
  sorry

/-- **Theorem 9.6** (Amalgamated boundary completion). A boundary map between same-level
objects extends to arrows of both objects into a common same-level extension. -/
theorem theorem_9_6 (K : AbstractElementaryClass.{u}) (n : ℕ) :
    ∀ (J Kf : FaceFamily K n) (h : BoundaryMap K J Kf),
      ∃ (Star : FaceFamily K n) (toJ : BoundaryMap K J Star) (toK : BoundaryMap K Kf Star),
        ∀ (s : Set (Fin n)) (hs : IsProper s),
          (toK.onFace hs).comp (h.onFace hs) = toJ.onFace hs := by
  sorry

/-- **Lemma 9.7** (Fixed parameters for a boundary test function). A bounded tuple's diagrams
against boundary tuples of length at most `σ` are fixed by boundary automorphisms that fix a
bounded parameter list. -/
theorem lemma_9_7 (K : AbstractElementaryClass.{u}) {n : ℕ} (J : FaceFamily K n)
    (D : StableDiagram K) {α : Type u} (z : α → (J.obj Set.univ).carrier)
    (σ : Cardinal.{u}) :
    ∃ (β : Type u) (a : β → (J.obj Set.univ).carrier), #β ≤ σ + #α ∧
      ∀ (h : BoundaryMap K J J), IsBoundaryIso h →
        (∀ i, ∃ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
          a i = J.incl (Set.subset_univ s) x ∧ h.onFace hs x = x) →
        ∀ {ι : Type u} (t : ι → (J.obj Set.univ).carrier), #ι ≤ σ →
          (∀ k, ∃ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
            t k = J.incl (Set.subset_univ s) x) →
          ∃ t' : ι → (J.obj Set.univ).carrier,
            (∀ k, ∃ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
              t k = J.incl (Set.subset_univ s) x ∧
              t' k = J.incl (Set.subset_univ s) (h.onFace hs x)) ∧
            ∀ (hσ : #(α ⊕ ι) ≤ σ + #α)
              (hcard : D.t (σ + #α) ≤ Model.card (J.obj Set.univ)),
              D.same hσ (J.inK Set.univ) (J.inK Set.univ) hcard hcard
                (Sum.elim z t) (Sum.elim z t') := by
  sorry

/-- **Theorem 9.8** (Exact boundary lifting). A boundary isomorphism of same-level `n`-axis
objects extends to an isomorphism of the objects. -/
theorem theorem_9_8 (K : AbstractElementaryClass.{u}) (n : ℕ)
    (J Kf : FaceFamily K n) (h : BoundaryMap K J Kf) (hiso : IsBoundaryIso h) :
    ∃ e : (J.obj Set.univ).carrier ≃[K.τ] (Kf.obj Set.univ).carrier,
      K.Strong e.toEmbedding ∧
      ∀ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
        e (J.incl (Set.subset_univ s) x) = Kf.incl (Set.subset_univ s) (h.onFace hs x) := by
  sorry

end
end AEC
