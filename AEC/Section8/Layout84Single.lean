module

public import AEC.Section8.Lemma84Single
public import AEC.Section7.RelativeIsolationTransfer

@[expose] public section

/-!
# Lemma 8.4 for the Prop 5.6 scheme: the natural layout (8), diagram level (cycle 100)

English (Lemma 8.4 proof): "The joint bounded diagrams of U and A_{H'} inside T are the diagrams of
the natural layout U_H ∪ A_{H'} inside U_{H'}. (8) Indeed, each bounded tuple of U, together with
b, is isolated over A, whereas the marginal of b over A_{H'} is the prescribed free extension.
Lemma 7.2 determines its joint type. The argument applies both to (8) and to the specified image
inside T'. It includes equalities between the two parts of the layout; an additional actual
overlap is not ignored."

Target (`infra_84_layout_amalgam`, diagram level): bounded joint diagrams of `U` (with the mark)
and the `C`-side read in `T` equal those read in `T′` through the specified map.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Layout (8), diagram level: equal types over `C` give equal bounded joint diagrams.**
If a list `w` in `T` and `w′` in `T′` (both over `C` at level `μ`) have the same Galois type over
`C`, then for every list `ZC` from `C` of size `< μ` the joint lists `w ⌢ cT ZC` and `w′ ⌢ cT′ ZC`
have equal diagrams. This includes equalities between the two parts (an actual overlap of `w` with
the image of `C` is recorded). Theorem 6.6 (`infra_72_diagramEq_of_sameGalois`). -/
theorem infra_84_layout_diagrams_of_type (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (C Tt Tt' : P.scheme.Object μ hμ)
    (cT : SystemArrow K oneVertexShape (P.scheme.asSystem hμ C) (P.scheme.asSystem hμ Tt))
    (cT' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ C) (P.scheme.asSystem hμ Tt'))
    (hcT : P.scheme.permitted (X := C) (Y := Tt) cT)
    (hcT' : P.scheme.permitted (X := C) (Y := Tt') cT')
    {κ : Type u} (w : κ → Occurrence K oneVertexShape (P.scheme.asSystem hμ Tt))
    (w' : κ → Occurrence K oneVertexShape (P.scheme.asSystem hμ Tt')) (hκ : #κ < μ)
    (h : SameGaloisType (⟨μ, hμ, Tt, cT, hcT, κ, w⟩ : TupleOver K oneVertexShape P.scheme hμ C)
      (⟨μ, hμ, Tt', cT', hcT', κ, w'⟩ : TupleOver K oneVertexShape P.scheme hμ C)
      (Equiv.refl _) (Equiv.refl _))
    {β : Type u} (ZC : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ C)) (hβ : #β < μ) :
    P.scheme.DiagramEq (X := Tt) (Y := Tt')
      (Sum.elim w (fun i => cT.mapOcc (ZC i))) (Sum.elim w' (fun i => cT'.mapOcc (ZC i))) := by
  have H := infra_72_diagramEq_of_sameGalois h ZC rfl rfl hκ hβ
  exact infra_73_diagramEq_of_eq H (fun x => by rcases x with i | j <;> rfl)
    (fun x => by rcases x with i | j <;> rfl)

/-- **Layout (8) for Lemma 8.4, diagram level (Lemma 7.2 step).** In the situation of Lemma 8.4
for `P.scheme`: if corresponding bounded tuples of `U`, `U′` jointly with the marks have equal
types over `C` (the hypothesis of Lemma 8.4, which the paper derives from Lemma 7.2: the tuple with
`b` is isolated over `A` and `b/C` is the prescribed free extension), then every bounded joint
diagram of `U` (with the mark) and `C` read in `T` equals the corresponding one read in `T′`
through the specified map. Tuple from `U` of size `< ν`, `C`-part of size `< μ`. -/
theorem infra_84_layout_diagrams_single (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (M M' : MarkedPair K oneVertexShape P.scheme Pr) (hνμ : M.μ < μ)
    (iso : MarkedArrow K oneVertexShape P.scheme Pr M M')
    (C Tt Tt' : P.scheme.Object μ hμ)
    (cT : SystemArrow K oneVertexShape (P.scheme.asSystem hμ C) (P.scheme.asSystem hμ Tt))
    (cT' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ C) (P.scheme.asSystem hμ Tt'))
    (hcT : P.scheme.permitted (X := C) (Y := Tt) cT)
    (hcT' : P.scheme.permitted (X := C) (Y := Tt') cT')
    (uT : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.Y) (P.scheme.asSystem hμ Tt))
    (uT' : SystemArrow K oneVertexShape (P.scheme.asSystem M'.hμ M'.Y)
      (P.scheme.asSystem hμ Tt'))
    (htypes : ∀ {ι : Type u} (t : ι → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y)),
      #ι < M.μ →
      SameGaloisType
        (⟨μ, hμ, Tt, cT, hcT, ι ⊕ M.bIdx,
          Sum.elim (fun i => uT.mapOcc (t i)) (fun j => uT.mapOcc (M.b j))⟩ :
          TupleOver K oneVertexShape P.scheme hμ C)
        (⟨μ, hμ, Tt', cT', hcT', ι ⊕ M.bIdx,
          Sum.elim (fun i => uT'.mapOcc (iso.onY.mapOcc (t i)))
            (fun j => uT'.mapOcc (iso.onY.mapOcc (M.b j)))⟩ :
          TupleOver K oneVertexShape P.scheme hμ C)
        (Equiv.refl _) (Equiv.refl _))
    {ιU ιC : Type u} (ZU : ιU → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y))
    (ZC : ιC → Occurrence K oneVertexShape (P.scheme.asSystem hμ C))
    (hU : #ιU < M.μ) (hC : #ιC < μ) :
    P.scheme.DiagramEq (X := Tt) (Y := Tt')
      (Sum.elim (Sum.elim (fun i => uT.mapOcc (ZU i)) (fun j => uT.mapOcc (M.b j)))
        (fun i => cT.mapOcc (ZC i)))
      (Sum.elim (Sum.elim (fun i => uT'.mapOcc (iso.onY.mapOcc (ZU i)))
          (fun j => uT'.mapOcc (iso.onY.mapOcc (M.b j))))
        (fun i => cT'.mapOcc (ZC i))) := by
  have hfinB : Finite M.bIdx :=
    Finite.of_equiv _ (M.realEq.trans (Pr.arity M.hμ M.X)).symm
  have hμ0 : ℵ₀ < M.μ := P.aleph0_lt M.hμ
  have hBlt : #M.bIdx < M.μ := (Cardinal.lt_aleph0_of_finite M.bIdx).trans hμ0
  have hκ : #(ιU ⊕ M.bIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact (add_lt_of_lt hμ0.le hU hBlt).trans hνμ
  exact infra_84_layout_diagrams_of_type P hμ C Tt Tt' cT cT' hcT hcT' _ _ hκ (htypes ZU hU) ZC hC

end AEC
