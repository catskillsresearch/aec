module

public import AEC.Section7.IsolationBound
public import AEC.Section7.MixedLevel

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
