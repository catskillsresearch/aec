module

public import AEC.Section7.TiedFreeProject

@[expose] public section

/-!
# Tied products under base change, level form (cycle 92; toward `infra_713_lift_pi`)

* `infra_713_productTied_congr_joint`: a tied product `p ⊗ q` can be replaced by any joint of the
  same Galois type (both at the level), by cross-level transitivity with an end at the level.
* `infra_713_tied_exists_level`: existence of `p ⊗ q` with a level-`μ` joint.
* `infra_713_productTied_base_change`: tied free lifts along `f : X → B` of `p`, `q` and of a
  level product `p ⊗ q` give a product over `B`: `(p ⊗ q)^B` is `p^B ⊗ q^B`
  (`infra_612_tied_base_change_level_joints`).
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- Pointwise congruence of the coordinate identification of a tied product. -/
theorem infra_713_productTied_congr_e {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}
    {p q j : TupleOver K oneVertexShape P.scheme hμ A} {e e' : p.idx ⊕ q.idx ≃ j.idx}
    (h : IsProductTied p q j e) (he : ∀ x, e x = e' x) : IsProductTied p q j e' :=
  Equiv.ext he ▸ h

/-- **Replacing the joint of a tied product (proved, cycle 92).** -/
theorem infra_713_productTied_congr_joint {P : SingleModelData K} (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    {p q j j' : TupleOver K oneVertexShape P.scheme hμ A} (e' : p.idx ⊕ q.idx ≃ j'.idx)
    (g : j.idx ≃ j'.idx) (hj : SameGaloisType j j' g (Equiv.refl _))
    (hjν : j.ν = μ) (hj'ν : j'.ν = μ) (hidx : #j.idx ≤ σ)
    (h : IsProductTied p q j' e') : IsProductTied p q j (e'.trans g.symm) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  obtain ⟨x, ex, hx, y, ey, hy, hJ⟩ := h
  refine ⟨x, ex, hx, y, ey, hy, ?_⟩
  set E := e'.symm.trans (Equiv.sumCongr ex ey) with hE
  have h32 : SameGaloisType j' (x.join y) (Equiv.refl _) E.symm := by
    have := infra_612_sameGalois_trans_equiv hJ E.symm
    exact infra_712u_sg_congr_right (infra_712_sg_congr_left this (fun t => E.symm_apply_apply t))
      (fun t => rfl)
  have H := infra_612_galois_trans_cross_level_left_base hj h32 σ hσ hσlt hidx hrec hjν hj'ν
  exact infra_712_sg_congr_left H (fun t => rfl)

/-- **Existence of a level product (proved, cycle 92).** -/
theorem infra_713_tied_exists_level (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hqσ : #q.idx ≤ σ) :
    ∃ joint : TupleOver K oneVertexShape P.scheme hμ A,
      ∃ e : p.idx ⊕ q.idx ≃ joint.idx, IsProductTied p q joint e ∧ joint.ν = μ := by
  obtain ⟨ν, hν, host, incl, hincl, idx, val⟩ := p
  dsimp only at hνp
  subst hνp
  let x : TupleOver K oneVertexShape P.scheme hμ A := ⟨ν, hν, host, incl, hincl, idx, val⟩
  obtain ⟨y, ey, hyν, -, hT⟩ :=
    infra_610_tied_free_lift P σ hσ hν hrec hσμ incl hincl q hνq hqσ
  refine ⟨x.join y, Equiv.sumCongr (Equiv.refl idx) ey, ⟨x, Equiv.refl _,
    SameGaloisType.refl x, y, ey, hT, ?_⟩, hyν⟩
  have h : (Equiv.sumCongr (Equiv.refl idx) ey).symm.trans
      (Equiv.sumCongr (Equiv.refl idx) ey) = Equiv.refl (idx ⊕ y.idx) :=
    Equiv.symm_trans_self _
  exact h ▸ SameGaloisType.refl (x.join y)

/-- **Tied products under base change, level form (proved, cycle 92).** If `joint = p ⊗ q`
over `X` (level joint) and `pB`, `qB`, `jB` are tied free lifts of `p`, `q`, `joint` along
`f : X → B` (all at the level), then `jB = pB ⊗ qB`. -/
theorem infra_713_productTied_base_change (P : SingleModelData K) (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {X B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := X) (Y := B) f)
    (p q joint : TupleOver K oneVertexShape P.scheme hμ X) (e : p.idx ⊕ q.idx ≃ joint.idx)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hjν : joint.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (pB qB jB : TupleOver K oneVertexShape P.scheme hμ B)
    (eP : p.idx ≃ pB.idx) (eQ : q.idx ≃ qB.idx) (eJ : joint.idx ≃ jB.idx)
    (hpBν : pB.ν = μ) (hqBν : qB.ν = μ) (hjBν : jB.ν = μ)
    (hprod : IsProductTied p q joint e)
    (hP : IsTiedFree f p pB eP) (hQ : IsTiedFree f q qB eQ) (hJ : IsTiedFree f joint jB eJ) :
    IsProductTied pB qB jB ((Equiv.sumCongr eP.symm eQ.symm).trans (e.trans eJ)) := by
  have hqBσ : #qB.idx ≤ σ := (Cardinal.mk_congr eQ).symm.trans_le hqσ
  obtain ⟨jB', e', hprodB, hjB'ν⟩ :=
    infra_713_tied_exists_level P σ hσ hμ hrec hσμ pB qB hpBν hqBν hqBσ
  have H := infra_612_tied_base_change_level_joints P σ hσ hμ hrec hσμ p q hνp hνq hpσ hqσ hμ hrec
    hσμ le_rfl B f hf joint e pB qB jB jB' eP eQ eJ e' hprod hP hQ hJ hprodB hjν hjBν hjB'ν
  have hpqσ : #(p.idx ⊕ q.idx) ≤ σ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hσ hpσ hqσ
  have hjBσ : #jB.idx ≤ σ := (Cardinal.mk_congr (eJ.symm.trans e.symm)).trans_le hpqσ
  let g : jB.idx ≃ jB'.idx :=
    (eJ.symm.trans e.symm).trans ((Equiv.sumCongr eP eQ).trans e')
  have hg : SameGaloisType jB jB' g (Equiv.refl _) := by
    have := infra_612_sameGalois_trans_equiv H ((Equiv.sumCongr eP eQ).trans e')
    refine infra_712u_sg_congr_right (infra_712_sg_congr_left this (fun t => rfl)) (fun t => ?_)
    show e' ((Equiv.sumCongr eP eQ) ((Equiv.sumCongr eP.symm eQ.symm) (e'.symm t))) = t
    have hs : ∀ s, Equiv.sumCongr eP eQ (Equiv.sumCongr eP.symm eQ.symm s) = s := by
      rintro (a | b)
      · exact congrArg Sum.inl (eP.apply_symm_apply a)
      · exact congrArg Sum.inr (eQ.apply_symm_apply b)
    exact (congrArg e' (hs _)).trans (e'.apply_symm_apply t)
  have R := infra_713_productTied_congr_joint σ hσ hrec hσμ e' g hg hjBν hjB'ν hjBσ hprodB
  refine infra_713_productTied_congr_e R (fun t => ?_)
  show g.symm (e' t) = _
  simp [g]

/-- **Finite tied products under base change, all partial products at the level (proved,
cycle 92).** If `j = b₀ ⊗ ⋯ ⊗ b_{n-1}` over `X` (all partial products at the level) and `bB i`,
`jB` are tied free lifts of `b i`, `j` along `f : X → B` (at the level), then
`jB = bB₀ ⊗ ⋯ ⊗ bB_{n-1}` (all partial products at the level). -/
theorem infra_713_finite_base_change (P : SingleModelData K) (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {X B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := X) (Y := B) f) :
    ∀ (n : ℕ) (b : Fin n → TupleOver K oneVertexShape P.scheme hμ X)
      (_hb : ∀ i, (b i).ν = μ ∧ #(b i).idx ≤ σ)
      (j : TupleOver K oneVertexShape P.scheme hμ X) (E : (Σ i, (b i).idx) ≃ j.idx)
      (_hj : j.ν = μ), IsFiniteProductTiedLevel n b j E →
      ∀ (bB : Fin n → TupleOver K oneVertexShape P.scheme hμ B)
        (eB : ∀ i, (b i).idx ≃ (bB i).idx) (_hbB : ∀ i, (bB i).ν = μ)
        (_hT : ∀ i, IsTiedFree f (b i) (bB i) (eB i))
        (jB : TupleOver K oneVertexShape P.scheme hμ B) (eJ : j.idx ≃ jB.idx)
        (_hjB : jB.ν = μ) (_hJ : IsTiedFree f j jB eJ),
        IsFiniteProductTiedLevel n bB jB ((Equiv.sigmaCongrRight eB).symm.trans (E.trans eJ))
  | 0, b, hb, j, E, hj, h, bB, eB, hbB, hT, jB, eJ, hjB, hJ => by
    have : IsEmpty j.idx := h
    exact eJ.symm.isEmpty
  | n + 1, b, hb, j, E, hj, h, bB, eB, hbB, hT, jB, eJ, hjB, hJ => by
    obtain ⟨left, El, hlν, hL, e, hP, h1, h2⟩ := h
    have hlσ : #left.idx ≤ σ := (Cardinal.mk_congr El).symm.trans_le
      (infra_612_card_sigma_fin _ hσ (fun i => (hb _).2))
    obtain ⟨leftB, eL, hLν, -, hTL⟩ :=
      infra_610_tied_free_lift P σ hσ hμ hrec hσμ f hf left hlν hlσ
    have IH := infra_713_finite_base_change P σ hσ hμ hrec hσμ f hf n (fun i => b i.castSucc)
      (fun i => hb _) left El hlν hL (fun i => bB i.castSucc) (fun i => eB i.castSucc)
      (fun i => hbB _) (fun i => hT _) leftB eL hLν hTL
    have hPB := infra_713_productTied_base_change P σ hσ hμ hrec hσμ f hf left (b (Fin.last n)) j
      e hlν (hb _).1 hj hlσ (hb _).2 leftB (bB (Fin.last n)) jB eL (eB _) eJ hLν (hbB _) hjB hP
      hTL (hT _) hJ
    refine ⟨leftB, _, hLν, IH, _, hPB, fun i k => ?_, fun k => ?_⟩
    · show eJ (E ⟨i.castSucc, (eB i.castSucc).symm k⟩) =
        eJ (e (Sum.inl (eL.symm (eL (El ⟨i, (eB i.castSucc).symm k⟩)))))
      exact congrArg eJ ((h1 i _).trans (by rw [eL.symm_apply_apply]))
    · exact congrArg eJ (h2 ((eB (Fin.last n)).symm k))

end
end AEC
