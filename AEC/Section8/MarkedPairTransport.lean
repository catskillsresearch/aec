module

public import AEC.Section8.MarkedPairExists

@[expose] public section

/-!
# Marked pairs are invariant under isomorphism of the upper object (Lemma 8.3 support)

Toward faithful Lemma 8.3 (`infra_83_lemma_8_3_full_single`): the template values `(X_I, Y_I, b_I)`
are shown to be marked pairs by identifying them, over the base, with a marked pair `M` over `X_I`
(Lemma 8.2 (1)). This file proves the transport step: pushing the upper object `Y` of a pair along
a permitted arrow `h : Y → Y'` keeps the Galois type of the mark over `X`, so the prescribed-type
clause `realizes` (with the same `realEq`) transfers.
-/

universe u

open Cardinal FirstOrder
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- Pushing a tuple along a permitted arrow of its host does not change its Galois type over the
base (witnessed by the pushed host itself as the common top). -/
theorem infra_83_sameGalois_push {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y Y' : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ Y'))
    {idx : Type u} (b : idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)) :
    SameGaloisType (asTuple incl hincl b)
      (asTuple (SystemArrow.comp incl h) trivial (fun i => h.mapOcc (b i)))
      (Equiv.refl _) (Equiv.refl _) :=
  ⟨μ, hμ, Y', h, SystemArrow.refl _, trivial, trivial, fun _ => rfl, fun _ => rfl⟩

/-- **Prescribed-type clause transports along the upper object.** If the mark `b` of `X ≤ Y`
realizes the prescribed type `Pr.assign X` (via `realEq`), so does its image under any arrow
`h : Y → Y'`, for the pushed inclusion and the same `realEq`. -/
theorem infra_83_realizes_push (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y Y' : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ Y'))
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (realEq : bIdx ≃ (Pr.assign hμ X).idx)
    (hr : SameGaloisType (asTuple incl hincl b) (Pr.assign hμ X) realEq (Equiv.refl _)) :
    SameGaloisType (asTuple (SystemArrow.comp incl h) trivial (fun i => h.mapOcc (b i)))
      (Pr.assign hμ X) realEq (Equiv.refl _) := by
  have hidx : #(Pr.assign hμ X).idx ≤ ℵ₀ := by
    have : Finite (Pr.assign hμ X).idx := Finite.of_equiv _ (Pr.arity hμ X).symm
    exact (Cardinal.lt_aleph0_of_finite _).le
  have h12 : SameGaloisType (Pr.assign hμ X) (asTuple incl hincl b) realEq.symm
      (Equiv.refl _) := SameGaloisType.unswap_refl hr.symm
  have h32 := infra_83_sameGalois_push incl hincl h b
  have S := infra_612_galois_trans_last_base h12 h32 ℵ₀ le_rfl (P.aleph0_lt hμ) hidx rfl
  have S' := SameGaloisType.unswap_refl S.symm
  exact S'

/-- Move both coordinate identifications onto the second tuple. -/
theorem infra_83_sgt_to_refl {S : SystemShape.{u}} {W : WorkingScheme K S}
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    {t1 t2 : TupleOver K S W hμ base} {ι : Type u} {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι}
    (h : SameGaloisType t1 t2 e1 e2) :
    SameGaloisType t1 t2 (Equiv.refl _) (e2.trans e1.symm) := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, fun i => ?_⟩
  have := hval (e1 i)
  rw [Equiv.symm_apply_apply] at this
  exact this

/-- Converse of `infra_83_sgt_to_refl`. -/
theorem infra_83_sgt_of_refl {S : SystemShape.{u}} {W : WorkingScheme K S}
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    {t1 t2 : TupleOver K S W hμ base} {ι : Type u} {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι}
    (h : SameGaloisType t1 t2 (Equiv.refl _) (e2.trans e1.symm)) :
    SameGaloisType t1 t2 e1 e2 := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, fun i => ?_⟩
  have key : (e2.trans e1.symm).symm (e1.symm i) = e2.symm i := by simp
  have := hval (e1.symm i)
  rw [key] at this
  exact this

/-- **Relative isolation transports along the upper object.** If `tp(v/X)` (hosted in `Y`, with
coordinates split by `e`) is relatively isolated, so is the type of the pushed tuple `h ∘ v` in
`Y'` for any arrow `h : Y → Y'` (same isolating parameters). -/
theorem infra_83_relIso_push (P : SingleModelData K) {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y Y' : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ Y'))
    {idx uIdx cIdx : Type u} (v : idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (e : idx ≃ uIdx ⊕ cIdx) (hcard : #idx < μ)
    (hI : IsRelativelyIsolated (asTuple incl hincl v) e) :
    IsRelativelyIsolated (asTuple (SystemArrow.comp incl h) trivial (fun i => h.mapOcc (v i)))
      e := by
  obtain ⟨ι, Z, hZ, H⟩ := hI
  refine ⟨ι, Z, hZ, fun q' e' hν hmarg hdiag => ?_⟩
  have hlt : ℵ₀ < μ := P.aleph0_lt hμ
  have hσ : max ℵ₀ #idx < μ := max_lt hlt hcard
  have hu : #uIdx ≤ #idx := by
    have := Cardinal.mk_le_of_injective (f := fun x : uIdx => e.symm (Sum.inl x))
      (fun a b hab => by simpa using hab)
    exact this
  -- marginal hypothesis for the original tuple
  have hm0 : SameGaloisType ((asTuple incl hincl v).marginal e) (q'.marginal e')
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
    have h12 := infra_83_sameGalois_push incl hincl h
      (fun i : uIdx => v (e.symm (Sum.inl i)))
    exact infra_612_galois_trans_last_base h12 hmarg (max ℵ₀ #idx) (le_max_left _ _) hσ
      (hu.trans (le_max_right _ _)) hν
  -- diagram hypothesis for the original tuple
  have hd0 : P.scheme.DiagramEq (X := Y) (Y := q'.host)
      (alignJoint e (typeJoint (p := asTuple incl hincl v) Z))
      (alignJoint e' (typeJoint (p := q') Z)) := by
    have hα : #((uIdx ⊕ cIdx) ⊕ ι) < μ := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, ← Cardinal.mk_congr e]
      exact Cardinal.add_lt_of_lt (hlt.le) hcard hZ
    have hp := P.scheme.diagram_preserved Y Y' h trivial
      (alignJoint e (typeJoint (p := asTuple incl hincl v) Z)) hα hα
    refine P.scheme.diagram_trans _ _ _ _ _ _ hp ?_
    have hx : (fun i => (⟨(alignJoint e (typeJoint (p := asTuple incl hincl v) Z) i).1,
        h.onVertex _ (alignJoint e (typeJoint (p := asTuple incl hincl v) Z) i).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ Y'))) =
        alignJoint e (typeJoint (p := asTuple (SystemArrow.comp incl h) trivial
          (fun i => h.mapOcc (v i))) Z) := by
      funext s
      rcases s with s | s <;> rfl
    exact hx ▸ hdiag
  have S0 := H q' e' hν hm0 hd0
  -- compose with the push identification
  have h12 := (infra_83_sameGalois_push incl hincl h v).symm
  have h32 := infra_83_sgt_to_refl S0
  have S := infra_612_galois_trans_last_base h12 h32 (max ℵ₀ #idx) (le_max_left _ _) hσ
    (le_max_right _ _) hν
  apply infra_83_sgt_of_refl
  exact SameGaloisType.swap_refl S

/-- **All-domination transports along a surjective upper arrow.** If `Y` is all-dominated over
`X + b` and `h : Y → Y'` is onto (vertexwise), then `Y'` is all-dominated over `X + h(b)`
(for the pushed inclusion); `b` is bounded (`#bIdx < μ`). -/
theorem infra_83_dominated_push (P : SingleModelData K) {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y Y' : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ Y'))
    (hsurj : ∀ v, Function.Surjective (h.onVertex v))
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (hb : #bIdx < μ) (hd : AllDominated incl hincl bIdx b) :
    AllDominated (SystemArrow.comp incl h) trivial bIdx (fun i => h.mapOcc (b i)) := by
  intro cIdx c hc
  let c0 : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y) :=
    fun j => ⟨(c j).1, Function.surjInv (hsurj (c j).1) (c j).2⟩
  have hc0 : ∀ j, h.mapOcc (c0 j) = c j := fun j => by
    show (⟨(c j).1, h.onVertex (c j).1 (Function.surjInv (hsurj (c j).1) (c j).2)⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ Y')) = c j
    rw [Function.surjInv_eq (hsurj (c j).1)]
  have hcard : #(bIdx ⊕ cIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_lt hμ).le hb hc
  have H := infra_83_relIso_push P incl hincl h (seqJoint b c0) (Equiv.refl _) hcard
    (hd cIdx c0 hc)
  have hx : (fun s => h.mapOcc (seqJoint b c0 s)) = seqJoint (fun i => h.mapOcc (b i)) c := by
    funext s
    rcases s with s | s
    · rfl
    · exact hc0 s
  rw [hx] at H
  exact H

/-- **Marked pairs are invariant under isomorphism of the upper object (Lemma 8.3 support).**
For a marked pair `M` and an onto arrow `h : M.Y → Y'` (an isomorphism of the upper object at the
same level), `(M.X, Y', h ∘ M.incl, h(M.b))` is again a marked pair, with the same `realEq`. -/
noncomputable def MarkedPair.pushY {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    (M : MarkedPair K oneVertexShape P.scheme Pr) (Y' : P.scheme.Object M.μ M.hμ)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.Y) (P.scheme.asSystem M.hμ Y'))
    (hsurj : ∀ v, Function.Surjective (h.onVertex v)) :
    MarkedPair K oneVertexShape P.scheme Pr :=
  ⟨M.μ, M.hμ, M.X, Y', SystemArrow.comp M.incl h, trivial, M.bIdx,
    fun i => h.mapOcc (M.b i), M.realEq,
    infra_83_realizes_push P Pr M.incl M.incl_arrow h M.b M.realEq M.realizes,
    infra_83_dominated_push P M.incl M.incl_arrow h hsurj M.b
      (by
        have : Finite M.bIdx :=
          Finite.of_equiv _ (M.realEq.trans (Pr.arity M.hμ M.X)).symm
        exact (Cardinal.lt_aleph0_of_finite _).trans (P.aleph0_lt M.hμ))
      M.dominated⟩

/-- The pushed marked pair has the same base and level, upper object `Y'`, inclusion `h ∘ incl`
and marks `h(b)`. -/
theorem infra_83_markedPair_push {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    (M : MarkedPair K oneVertexShape P.scheme Pr) (Y' : P.scheme.Object M.μ M.hμ)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.Y) (P.scheme.asSystem M.hμ Y'))
    (hsurj : ∀ v, Function.Surjective (h.onVertex v)) :
    (M.pushY Y' h hsurj).μ = M.μ ∧ (M.pushY Y' h hsurj).X = M.X ∧
      (M.pushY Y' h hsurj).Y = Y' ∧
      (M.pushY Y' h hsurj).incl = SystemArrow.comp M.incl h ∧
      (M.pushY Y' h hsurj).bIdx = M.bIdx ∧
      (∀ i, (M.pushY Y' h hsurj).b i = h.mapOcc (M.b i)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

end AEC
