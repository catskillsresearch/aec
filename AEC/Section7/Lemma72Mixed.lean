module

public import AEC.Section7.IsolationBound
public import AEC.Section7.MixedLevel
public import AEC.Section7.Theorem79

@[expose] public section

/-!
# Lemma 7.2, last sentence (mixed levels)

English Lemma 7.2 ends: "The second assertion also holds when `A` is at a smaller eligible level
than `B`, provided `(u, c)` and the required uniform bounds are below the level of `A`."
`infra_72_over_B_isolation` is the same-level clause 2; this file states the mixed-level clause:
`A` at level `ν ≤ μ`, `B` at level `μ`, the bounds (`recursionClosedLevels`, `σ⁺ ≤ ν`, `|q| < ν`)
at the level of `A`, and the tied-free marginal hypothesis in its mixed form `IsTiedFreeMixed`.
Needed for Lemma 8.2(5) preservation across levels. Open (audit finding, cycle 96).
-/

namespace AEC
section

universe u
open Cardinal Classical FirstOrder Function
variable {K : AbstractElementaryClass.{u}}

/-- **Mixed-level `hExt` alignment (proved; port of `infra_73_ext_align`, step (b) of
`infra_72_mixed_level`).** `hExt` read on any parameter list of `A` bounded below the level `ν`
of `A`, aligned along `e`, with `B` at a level `μ ≥ ν`. -/
theorem infra_72_ext_align_mixed
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (hνμ : ν ≤ μ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hν A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = ν) (hBν : qB.ν = μ) (hidxν : #q.idx < ν)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    {γ : Type u} (Y : γ → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (hγ : #γ < ν) :
    P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (alignJoint e (typeJoint (p := q) Y))
      (alignJoint (eB.symm.trans e) (typeJoint (p := qB.restrict f hf) Y)) := by
  have hqBidx : #qB.idx < ν := by
    rw [← Cardinal.mk_congr eB]; exact hidxν
  have hsum : #(qB.idx ⊕ γ) < ν := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hν) hqBidx hγ
  have h0 := infra_78_diagramEq_of_sameGalois (P := P) hExt Y (by rw [hqν]; exact hsum)
    (by change #(qB.idx ⊕ γ) < qB.ν; rw [hBν]; exact hsum.trans_le hνμ)
  let eq : qB.idx ⊕ γ ≃ (uIdx ⊕ cIdx) ⊕ γ := Equiv.sumCongr (eB.symm.trans e) (Equiv.refl γ)
  have h1 := (P.scheme.diagram_reindex q.host qB.host eq _ _).mp h0
  have hL : (fun b => alignJoint eB (typeJoint (p := q) Y) (eq.symm b)) =
      alignJoint e (typeJoint (p := q) Y) := by
    funext b
    cases b with
    | inl k =>
      simp only [eq, alignJoint, typeJoint, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    | inr w => rfl
  have hR : (fun b => alignJoint (Equiv.refl qB.idx)
        (typeJoint (p := qB.restrict f hf) Y) (eq.symm b)) =
      alignJoint (eB.symm.trans e) (typeJoint (p := qB.restrict f hf) Y) := by
    funext b
    cases b <;> rfl
  exact infra_73_diagramEq_of_eq h1 (congrFun hL) (congrFun hR)

/-- **Mixed-level tied moves (proved; port of `infra_73_tied_move`, toward
`infra_72_mixed_level`).** For `A` at a level `ν` in the `σ`-tail and `f : A → B` with `B` at
`μ ≥ ν`, every query from `B` of size at most `g(σ) + LS(K)` is a mixed sequence-move of a query
from `A`, for a long approximation sequence of `p`. -/
theorem infra_72_tied_move_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible) (hνT : ν ∈ infra_73_tailSet P σ)
    {hμ : μ ∈ P.eligible} (hνμ : ν ≤ μ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hν A) (hidx : #p.idx ≤ σ)
    {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hβ : #β ≤ P.g σ + ls K) :
    ∃ (seq : ApproximationSequence p)
      (Y0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      seq.τ + ℵ₀ < #(seq.κIndex) ∧ #β ≤ seq.τ ∧ #β < ν ∧
        infra_78_isMoveMixed f seq Y Y0 := by
  classical
  have hσlt : σ < ν := (Order.lt_succ σ).trans_le (infra_73_tail_succ hνT)
  have hhν : infra_73_h P σ < ν := infra_73_h_lt hν hνT
  obtain ⟨seq, -, hκ, hg, hlong⟩ := infra_78_sequence_mixed P σ hσ hν hνT p hidx
  have hτlt : seq.τ < ν := (lt_of_le_of_lt le_self_add hlong).trans (hκ ▸ hhν)
  have hβτ : #β ≤ seq.τ := hβ.trans hg
  have hβν : #β < ν := hβτ.trans_lt hτlt
  let xs : seq.κIndex × p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν A) :=
    fun ij => seq.family ij.1 ij.2
  have hα : #(seq.κIndex × p.idx) < ν := by
    rw [mk_prod, lift_id, lift_id]
    exact mul_lt_of_lt (P.aleph0_le hν) (hκ ▸ hhν) (hidx.trans_lt hσlt)
  obtain ⟨Y0, hY0⟩ := infra_78_move_mixed f hf hνμ xs Y hα hβν
  refine ⟨seq, Y0, hlong, hβτ, hβν, ?_⟩
  intro i
  have h := infra_73_scheme_comp hY0
    (fun t : p.idx ⊕ β => Sum.map (fun j => (i, j)) id t)
  exact infra_73_diagramEq_of_eq h (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)

/-- **Mixed-level uniqueness of tied-free extensions (proved; port of `infra_73_tied_unique`).**
Two mixed tied-free extensions over `B` (level `μ`, recursion closed) of `p` over `A` (level `ν`
in the `σ`-tail) have the same Galois type over `B`. The level hypothesis at `μ` is the one of
`infra_73_differing_test` (testing over `B`). -/
theorem infra_72_tied_unique_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible) (hνT : ν ∈ infra_73_tailSet P σ)
    (hμ : μ ∈ P.eligible) (hνμ : ν ≤ μ)
    (hrecμ : μ ∈ recursionClosedLevels P σ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hν A) (hidx : #p.idx ≤ σ)
    (pB1 pB2 : TupleOver K oneVertexShape P.scheme hμ B)
    (eB1 : p.idx ≃ pB1.idx) (eB2 : p.idx ≃ pB2.idx)
    (h1ν : pB1.ν = μ) (h2ν : pB2.ν = μ)
    (hT1 : IsTiedFreeMixed f p pB1 eB1) (hT2 : IsTiedFreeMixed f p pB2 eB2) :
    SameGaloisType pB1 pB2 eB1.symm eB2.symm := by
  classical
  have hσSuccν : Order.succ σ ≤ ν := infra_73_tail_succ hνT
  have hσSucc : Order.succ σ ≤ μ := hσSuccν.trans hνμ
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidx1 : #pB1.idx ≤ σ := by rw [← Cardinal.mk_congr eB1]; exact hidx
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ :=
    infra_73_differing_test P σ hσ hμ hrecμ hσSucc pB1 pB2 eB1.symm eB2.symm h1ν h2ν
      hidx1 (hidx1.trans_lt hσlt) hneq
  apply hnot
  obtain ⟨seq, Y0, hlong, hβτ, hβν, hmv⟩ :=
    infra_72_tied_move_mixed P σ hσ hν hνT hνμ f hf p hidx Y hβ
  have d1 := hT1 seq Y Y0 hlong hβτ hβν hmv
  have d2 := hT2 seq Y Y0 hlong hβτ hβν hmv
  have d := P.scheme.diagram_trans pB1.host p.host pB2.host _ _ _
    (P.scheme.diagram_symm p.host pB1.host _ _ d1) d2
  exact infra_73_diagramEq_of_eq d (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)

/-- **Mixed tied freeness transfers along equal Galois types over `B` (proved; step (d) of
`infra_72_mixed_level`).** If `qB` is a mixed tied-free extension of `q` and `q''` has the same
Galois type as `qB` over `B` (identity on indices), then `q''` is a mixed tied-free extension of
`q` as well. -/
theorem infra_72_tiedFreeMixed_of_sameGalois
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (hνμ : ν ≤ μ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (q : TupleOver K oneVertexShape P.scheme hν A)
    (qB q'' : TupleOver K oneVertexShape P.scheme hμ B)
    {ι0 : Type u} (eB : q.idx ≃ ι0) (eq'' : q''.idx ≃ ι0) (eqB : qB.idx ≃ ι0)
    (hBν : μ ≤ qB.ν) (hν'' : μ ≤ q''.ν) (hidx : #ι0 < ν)
    (hT : IsTiedFreeMixed f q qB (eB.trans eqB.symm))
    (hSame : SameGaloisType qB q'' eqB eq'') :
    IsTiedFreeMixed f q q'' (eB.trans eq''.symm) := by
  intro seq ι Z Z0 hlong hιτ hιν hmove
  have d1 := hT seq Z Z0 hlong hιτ hιν hmove
  have hs : #(ι0 ⊕ ι) < ν := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hν) hidx hιν
  have d2 := infra_78_diagramEq_of_sameGalois hSame Z
    (hs.trans_le (hνμ.trans hBν)) (hs.trans_le (hνμ.trans hν''))
  have d1' := infra_73_diagramEq_of_eq d1 (fun _ => rfl)
    (ys' := fun t => alignJoint eqB (typeJoint (p := qB) Z) (Sum.map (eB) id t))
    (fun t => by
      cases t with
      | inl k =>
        simp only [infra_612_anchored, alignJoint, typeJoint, Sum.map_inl, Equiv.trans_apply]
      | inr j => rfl)
  have d2' := infra_73_scheme_comp d2 (Sum.map eB id)
  have d := P.scheme.diagram_trans q.host qB.host q''.host _ _ _ d1' d2'
  exact infra_73_diagramEq_of_eq d (fun _ => rfl) (fun t => by
    cases t with
    | inl k =>
      simp only [infra_612_anchored, alignJoint, typeJoint, Sum.map_inl, Equiv.trans_apply]
    | inr j => rfl)

set_option maxHeartbeats 3200000 in
/-- **Same `u`-marginal over `A` (proved; step (a) of `infra_72_mixed_level`).** If the
`u`-marginal of `qB` is a mixed tied-free extension of that of `q` and a competitor `q''` over `B`
has the same `u`-marginal type over `B`, then `q''` read over `A` has the same `u`-marginal type
as `q` over `A`. Only the bounds at the level `ν` of `A` are used: the competitor's marginal is
first realized at level `ν` (`infra_78_same_level_realization`), the bounded tests are compared
there (`infra_78_sameGalois_of_diagramEq`), and the result is carried back. -/
theorem infra_72_marginal_over_A_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible) (hμ : μ ∈ P.eligible) (hνμ : ν ≤ μ)
    (hrec : ν ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ ν)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hν A)
    (qB q'' : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx) (e'' : q''.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = ν) (hBν : μ ≤ qB.ν) (hν'' : μ ≤ q''.ν)
    (hidx : #q.idx ≤ σ)
    (hMargTied : IsTiedFreeMixed f (q.marginal e) (qB.marginal (eB.symm.trans e))
      (Equiv.refl uIdx))
    (hMargB : SameGaloisType (qB.marginal (eB.symm.trans e)) (q''.marginal e'')
      (Equiv.refl uIdx) (Equiv.refl uIdx)) :
    SameGaloisType (q.marginal e) ((q''.restrict f hf).marginal e'')
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
  classical
  have hσlt : σ < ν := (Order.lt_succ σ).trans_le hσSucc
  have huidx : #uIdx ≤ #q.idx :=
    Cardinal.mk_le_of_injective (f := fun i : uIdx => e.symm (Sum.inl i))
      (fun a b h => Sum.inl.inj (e.symm.injective h))
  have huσ : #uIdx ≤ σ := huidx.trans hidx
  have huν : #uIdx < ν := huσ.trans_lt hσlt
  let r : TupleOver K oneVertexShape P.scheme hν A := (q''.restrict f hf).marginal e''
  obtain ⟨r', e', hr'ν, hR⟩ := infra_78_same_level_realization r huν
  obtain ⟨seqU, -, -, hτU, hlongU⟩ :=
    infra_73_sequence_rec P σ hσ hν hrec hσSucc (q.marginal e) hqν huσ
  have hg : P.g σ < ν :=
    (hν.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
  have hD : ∀ {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      #β ≤ P.g σ + ls K →
      P.scheme.DiagramEq (X := (q.marginal e).host) (Y := r'.host)
        (alignJoint e'.symm (typeJoint (p := q.marginal e) Y)) (typeJoint (p := r') Y) := by
    intro β Y hβ
    have hβν : #β < ν := hβ.trans_lt (add_lt_of_lt (P.aleph0_le hν) hg (P.ls_lt hν))
    have hcard : #(uIdx ⊕ β) < ν := by
      rw [mk_sum, lift_id, lift_id]
      exact add_lt_of_lt (P.aleph0_le hν) huν hβν
    have hmv : infra_78_isMoveMixed f seqU (pushParams f Y) Y := by
      intro i
      have h := P.scheme.diagram_preserved A B f hf (seqJoint (seqU.family i) Y) hcard
        (hcard.trans_le hνμ)
      exact infra_73_diagramEq_of_eq h (fun _ => rfl) (fun t => by cases t <;> rfl)
    have d1 := hMargTied seqU (pushParams f Y) Y hlongU (hβ.trans hτU) hβν hmv
    have d2 := infra_78_diagramEq_of_sameGalois (P := P) hMargB (pushParams f Y)
      ((hcard.trans_le hνμ).trans_le hBν) ((hcard.trans_le hνμ).trans_le hν'')
    have d1' := infra_73_diagramEq_of_eq d1 (fun t => (by cases t <;> rfl :
        typeJoint (p := q.marginal e) Y t = alignJoint (Equiv.refl uIdx)
          (typeJoint (p := q.marginal e) Y) t))
      (fun t => (by cases t <;> rfl :
        infra_612_anchored (Equiv.refl uIdx) (qB.marginal (eB.symm.trans e)).incl
          (qB.marginal (eB.symm.trans e)).val (pushParams f Y) t =
        alignJoint (Equiv.refl uIdx) (typeJoint (p := qB.marginal (eB.symm.trans e))
          (pushParams f Y)) t))
    have d := P.scheme.diagram_trans _ _ _ _ _ _ d1' d2
    have d' := infra_73_diagramEq_of_eq d (fun _ => rfl)
      (ys' := typeJoint (p := r) Y) (fun t => by cases t <;> rfl)
    have d3 := infra_78_diagramEq_of_sameGalois hR Y
      (hcard.trans_le ((hνμ.trans hν'')))
      (by rw [hr'ν]; exact hcard)
    have d3' := infra_73_diagramEq_of_eq d3 (xs' := typeJoint (p := r) Y)
      (fun t => by cases t <;> rfl) (fun _ => rfl)
    have D := P.scheme.diagram_trans _ _ _ _ _ _ d' d3'
    have D1 := infra_73_scheme_comp D (Sum.map e' id)
    exact infra_73_diagramEq_of_eq D1 (fun t => by cases t <;> rfl)
      (fun t => by cases t <;> simp [alignJoint, typeJoint])
  have hS := infra_78_sameGalois_of_diagramEq P σ hσ hν hrec hσlt (q.marginal e) r' e'.symm
    huσ hqν hr'ν hD
  have h12 := infra_73_sgt_uncommon hR
  have hfin := infra_612_galois_trans_last_base h12 (SameGaloisType.symm hS) σ hσ hσlt
    huσ hqν
  have hE : ((Equiv.refl r.idx).trans e'.symm).trans e'.symm.symm = Equiv.refl r.idx := by
    ext k
    simp only [Equiv.trans_apply, Equiv.refl_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  have hfin' : SameGaloisType r (q.marginal e) (Equiv.refl r.idx)
      (Equiv.refl (q.marginal e).idx) := by
    exact cast (congrArg (fun E => SameGaloisType r (q.marginal e) E
      (Equiv.refl (q.marginal e).idx)) hE) hfin
  exact SameGaloisType.symm hfin'

/-- **English Lemma 7.2, clause 2 at mixed levels (open).** -/
theorem infra_72_mixed_level
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible) (hμ : μ ∈ P.eligible) (hνμ : ν ≤ μ)
    (hrec : ν ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ ν)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hν A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = ν) (hBν : qB.ν = μ)
    (hidx : #q.idx ≤ σ) (hidxν : #q.idx < ν)
    {wι : Type u} (W : wι → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (hW : IsIsolatingFragment q e W)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    (hMargTied : IsTiedFreeMixed f (q.marginal e) (qB.marginal (eB.symm.trans e))
      (Equiv.refl uIdx)) :
    IsIsolatingFragment qB (eB.symm.trans e) (pushParams f W) := by
  sorry

end
end AEC
