module

public import AEC.Section7.Lemma712Recursion

/-!
# Lemma 7.12 (1): toward `infra_712_products` (cycle 86)

Product independence (`ProductIndependentTied`) gives *plain* finite tied products, whose partial
products may be hosted at any level. `infra_712_finiteProduct_toLevel` converts them to level
products (`IsFiniteProductTiedLevel`, where the proved level-joint symmetry / associativity /
permutation lemmas of Proposition 6.12 apply) by replacing every partial product with its
level-`μ` copy (`infra_612_exists_level_copy_arrow`). The Galois identifications pull back along
the copy's host arrow *inside the same amalgam* (`infra_712_sameGalois_pull`), so this uses no
cross-level transitivity and in particular not `infra_612_galois_trans_cross_level_both_off`.
-/

@[expose] public section

namespace AEC
noncomputable section
open Cardinal
variable {K : AbstractElementaryClass.{u}}
variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
  {A : P.scheme.Object μ hμ}

/-- Galois identifications pull back along a host relation (one amalgam, no transitivity). -/
theorem infra_712_sameGalois_pull {t' t s : TupleOver K oneVertexShape P.scheme hμ A}
    {r : SystemArrow K oneVertexShape (P.scheme.asSystem t'.hν t'.host)
      (P.scheme.asSystem t.hν t.host)} (hr : P.scheme.permitted (X := t'.host) (Y := t.host) r)
    {e : t'.idx ≃ t.idx} (hR : infra_78_HostRel t' t r e) {ι : Type u}
    {e1 : t.idx ≃ ι} {e2 : s.idx ≃ ι} (h : SameGaloisType t s e1 e2) :
    SameGaloisType t' s (e.trans e1) e2 := by
  obtain ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩ := h
  refine ⟨ρ, hρ, top, SystemArrow.comp r f1, f2, P.scheme.comp r f1 hr hf1, hf2, fun v => ?_,
    fun i => ?_⟩
  · rw [← hc v]
    ext x
    show f1.onVertex v (r.onVertex v (t'.incl.onVertex v x)) = _
    rw [hR.1 v x]; rfl
  · rw [← hv i]
    have hk := hR.2 (e.symm (e1.symm i))
    rw [Equiv.apply_symm_apply] at hk
    show (⟨(t'.val (e.symm (e1.symm i))).1, f1.onVertex _ (r.onVertex _
      (t'.val (e.symm (e1.symm i))).2)⟩ : Occurrence K oneVertexShape _) = _
    rw [hk]

/-- A level-`μ` copy with its host relation. -/
theorem infra_712_level_copy (t : TupleOver K oneVertexShape P.scheme hμ A) (hidx : #t.idx ≤ μ) :
    ∃ (t' : TupleOver K oneVertexShape P.scheme hμ A) (e : t'.idx ≃ t.idx)
      (r : SystemArrow K oneVertexShape (P.scheme.asSystem t'.hν t'.host)
        (P.scheme.asSystem t.hν t.host)),
      t'.ν = μ ∧ P.scheme.permitted (X := t'.host) (Y := t.host) r ∧ infra_78_HostRel t' t r e := by
  obtain ⟨host, incl, hincl, val, r, hr, hcomp, hval⟩ := infra_612_exists_level_copy_arrow t hidx
  refine ⟨⟨μ, hμ, host, incl, hincl, t.idx, val⟩, Equiv.refl _, r, rfl, hr, fun v x => ?_,
    fun k => ?_⟩
  · exact DFunLike.congr_fun (congrArg (fun f => f.onVertex v) hcomp) x
  · exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (hval _ k).symm)

/-- Tied products pull back along a host relation of the joint. -/
theorem infra_712_productTied_pull_joint {p q j j' : TupleOver K oneVertexShape P.scheme hμ A}
    {e : p.idx ⊕ q.idx ≃ j.idx}
    {r : SystemArrow K oneVertexShape (P.scheme.asSystem j'.hν j'.host)
      (P.scheme.asSystem j.hν j.host)} (hr : P.scheme.permitted (X := j'.host) (Y := j.host) r)
    {eJ : j'.idx ≃ j.idx} (hR : infra_78_HostRel j' j r eJ) (h : IsProductTied p q j e) :
    IsProductTied p q j' (e.trans eJ.symm) := by
  obtain ⟨x, ex, hS, y, ey, hT, hJ⟩ := h
  refine ⟨x, ex, hS, y, ey, hT, ?_⟩
  exact infra_712_sameGalois_pull hr hR hJ

/-- Tied products pull back along a host relation of the first factor. -/
theorem infra_712_productTied_pull_left {p p' q j : TupleOver K oneVertexShape P.scheme hμ A}
    {e : p.idx ⊕ q.idx ≃ j.idx}
    {r : SystemArrow K oneVertexShape (P.scheme.asSystem p'.hν p'.host)
      (P.scheme.asSystem p.hν p.host)} (hr : P.scheme.permitted (X := p'.host) (Y := p.host) r)
    {ep : p'.idx ≃ p.idx} (hR : infra_78_HostRel p' p r ep) (h : IsProductTied p q j e) :
    IsProductTied p' q j ((Equiv.sumCongr ep (Equiv.refl _)).trans e) := by
  obtain ⟨x, ex, hS, y, ey, hT, hJ⟩ := h
  refine ⟨x, ep.trans ex, infra_712_sameGalois_pull hr hR hS, y, ey, hT, ?_⟩
  have heq : ((Equiv.sumCongr ep (Equiv.refl q.idx)).trans e).symm.trans
      (Equiv.sumCongr (ep.trans ex) ey) = e.symm.trans (Equiv.sumCongr ex ey) := by
    ext k
    rcases hk : e.symm k with a | b <;> simp [hk]
  rw [heq]
  exact hJ

/-- **Plain finite tied products of finite factors are level products (proved, cycle 86).**
Every partial product (and the joint) is replaced by its level-`μ` copy
(`infra_612_exists_level_copy_arrow`); Galois identifications pull back along the copy's host
arrow inside the same amalgam, so no cross-level transitivity is used. -/
theorem infra_712_finiteProduct_toLevel :
    ∀ (n : ℕ) (b : Fin n → TupleOver K oneVertexShape P.scheme hμ A),
      (∀ i, Finite (b i).idx) →
      ∀ (j : TupleOver K oneVertexShape P.scheme hμ A) (E : (Σ i, (b i).idx) ≃ j.idx),
      IsFiniteProductTied n b j E →
      ∀ (j' : TupleOver K oneVertexShape P.scheme hμ A) (eJ : j'.idx ≃ j.idx)
        (r : SystemArrow K oneVertexShape (P.scheme.asSystem j'.hν j'.host)
          (P.scheme.asSystem j.hν j.host)),
        P.scheme.permitted (X := j'.host) (Y := j.host) r → infra_78_HostRel j' j r eJ →
        IsFiniteProductTiedLevel n b j' (E.trans eJ.symm)
  | 0, _, _, _, _, h, _, eJ, _, _, _ => ⟨fun k => h.false (eJ k)⟩
  | n + 1, b, hb, j, E, h, j', eJ, r, hr, hR => by
    obtain ⟨left, El, hL, e, hP, h1, h2⟩ := h
    have hfin : Finite left.idx := by
      have : Finite (Σ i : Fin n, (b i.castSucc).idx) := by
        have := fun i : Fin n => hb i.castSucc
        exact inferInstance
      exact Finite.of_equiv _ El
    obtain ⟨left', eL, rL, hν, hrL, hRL⟩ :=
      infra_712_level_copy left ((Cardinal.lt_aleph0_of_finite _).le.trans (P.aleph0_le hμ))
    have hIH : IsFiniteProductTiedLevel n (fun i => b i.castSucc) left' (El.trans eL.symm) :=
      infra_712_finiteProduct_toLevel n (fun i => b i.castSucc) (fun i => hb _) left El hL left'
        eL rL hrL hRL
    have hP1 : IsProductTied left' (b (Fin.last n)) j
        ((Equiv.sumCongr eL (Equiv.refl _)).trans e) :=
      infra_712_productTied_pull_left (p := left) (p' := left') (q := b (Fin.last n)) (j := j)
        (e := e) hrL hRL hP
    have hP2 : IsProductTied left' (b (Fin.last n)) j'
        (((Equiv.sumCongr eL (Equiv.refl _)).trans e).trans eJ.symm) :=
      infra_712_productTied_pull_joint (p := left') (q := b (Fin.last n)) (j := j) (j' := j')
        (e := (Equiv.sumCongr eL (Equiv.refl _)).trans e) hr hR hP1
    refine ⟨left', El.trans eL.symm, hν, hIH,
      ((Equiv.sumCongr eL (Equiv.refl _)).trans e).trans eJ.symm, hP2, fun i k => ?_, fun k => ?_⟩
    · show eJ.symm (E ⟨i.castSucc, k⟩) = eJ.symm (e (Sum.inl (eL (eL.symm (El ⟨i, k⟩)))))
      rw [Equiv.apply_symm_apply, h1]
    · show eJ.symm (E ⟨Fin.last n, k⟩) = eJ.symm (e (Sum.inr k))
      rw [h2]

/-- **Tied products are invariant under Galois-type changes of the factors and the joint, all at
the level of `A` (proved).** Transitivity only through middles at the level
(`infra_612_galois_trans_cross_level_of_base_end`), tied freeness via
`infra_78_tiedFreeMixed_left_congr`. -/
theorem infra_712_productTied_transfer (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
    {A : P.scheme.Object μ hμ} {p q J p' q' J' : TupleOver K oneVertexShape P.scheme hμ A}
    {e : p.idx ⊕ q.idx ≃ J.idx} (e' : p'.idx ⊕ q'.idx ≃ J'.idx)
    (ep : p'.idx ≃ p.idx) (eq : q'.idx ≃ q.idx) (g : J'.idx ≃ J.idx)
    (hg : ∀ s, g (e' s) = e (Sum.map ep eq s))
    (hP : SameGaloisType p' p ep (Equiv.refl _)) (hQ : SameGaloisType q' q eq (Equiv.refl _))
    (hJ : SameGaloisType J' J g (Equiv.refl _))
    (hp : p.ν = μ) (hp' : p'.ν = μ) (hq : q.ν = μ) (hq' : q'.ν = μ) (hj : J.ν = μ)
    (hj' : J'.ν = μ) (hfp : Finite p'.idx) (hfq : Finite q.idx) (hfj : Finite J'.idx)
    (h : IsProductTied p q J e) : IsProductTied p' q' J' e' := by
  classical
  have hlt : ℵ₀ < μ := (Order.lt_succ ℵ₀).trans_le h1
  obtain ⟨x, ex, hSx, y, ey, hT, hJx⟩ := h
  have hSx' : SameGaloisType p x (Equiv.refl _) ex.symm := by
    have h := infra_612_sameGalois_trans_equiv hSx ex.symm
    rwa [Equiv.self_trans_symm, Equiv.refl_trans] at h
  have hX := infra_612_galois_trans_cross_level_of_base_end P ℵ₀ le_rfl hμ h0 h1 A p' p x ep
    ex.symm (Cardinal.lt_aleph0_of_finite _).le hp (Or.inl hp') hP hSx'
  refine ⟨x, ep.trans ex, by simpa using hX, y, eq.trans ey, ?_, ?_⟩
  · refine infra_78_tiedFreeMixed_left_congr (q := q) (q' := q') (qB := y) x.incl ey eq hT
      (fun {β} Z hβ => ?_)
    have D := infra_72_diagramEq_of_sameGalois hQ Z hq' hq
      ((Cardinal.lt_aleph0_of_finite _).trans hlt) hβ
    refine infra_612_dEq_comp D (Sum.map eq id) ?_ ?_
    · rintro (k | j)
      · show _ = typeJoint (p := q') Z (Sum.inl (eq.symm (eq k)))
        rw [Equiv.symm_apply_apply]
      · rfl
    · rintro (k | j) <;> rfl
  · have hJx' := infra_612_sameGalois_trans_equiv hJx (e.symm.trans (Equiv.sumCongr ex ey)).symm
    rw [Equiv.self_trans_symm] at hJx'
    have R := infra_612_galois_trans_cross_level_of_base_end P ℵ₀ le_rfl hμ h0 h1 A J' J
      (x.join y) g _ (Cardinal.lt_aleph0_of_finite _).le hj (Or.inl hj') hJ hJx'
    have hE : g.trans ((Equiv.refl (x.idx ⊕ y.idx)).trans
        (e.symm.trans (Equiv.sumCongr ex ey)).symm).symm =
        e'.symm.trans (Equiv.sumCongr (ep.trans ex) (eq.trans ey)) := by
      ext t
      obtain ⟨s, rfl⟩ := e'.surjective t
      rcases s with a | b <;> simp [hg]
    rw [← hE]
    exact R

/-- The joint `bᵢ ⌢ (b_{ix 0}, …)` of a list entry and a selection, in the list's ambient. -/
def TupleList.consJoint {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} (L : TupleList P.scheme hμ A) (i : L.δ) (n : ℕ)
    (ix : Fin n → L.δ) : TupleOver K oneVertexShape P.scheme hμ A where
  ν := μ
  hν := hμ
  host := L.host
  incl := L.incl
  incl_arrow := L.incl_arrow
  idx := L.indexAt i ⊕ Σ s : Fin n, L.indexAt (ix s)
  val := fun
    | Sum.inl k => L.val i k
    | Sum.inr p => L.val (ix p.1) p.2

/-- **7.12(1), products in the list (statement; open tip `infra_712_products_L`).** For a
product-independent list, each entry `bᵢ` has the tied product over `A` with every finite
injective selection of earlier entries, joint = the actual concatenation in the list's ambient.
(Def 7.10 product independence regrouped as `bᵢ ⊗ (selection)`.) -/
def infra_712_products_L_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ], ProductIndependentTied L →
      ∀ (i : L.δ) (n : ℕ) (ix : Fin n → L.δ), Function.Injective ix → (∀ s, ix s < i) →
        IsProductTied (L.one i) (L.subConcat n ix) (L.consJoint i n ix) (Equiv.refl _)

/-- **Products along the truncated chain from products in the list (proved glue, cycle 87).**
Chain marks and list entries coincide in `C.top` (`mark_spec`, `mark_step`, `comm_A`), one
amalgam each; then `infra_712_productTied_transfer`. -/
theorem infra_712_products_of_L (P : SingleModelData K) (hL : infra_712_products_L_statement P) :
    infra_712_products_statement P := by
  intro μ hμ h0 h1 hw1 hw2 A L _ _ hind C hC i hfree n ix hinj
  have hinj' : Function.Injective (fun s => (ix s).1) := fun a b h => hinj (Subtype.ext h)
  have H := hL hμ h0 h1 hw1 hw2 A L hind i n (fun s => (ix s).1) hinj' (fun s => (ix s).2)
  have hincl : ∀ v, (C.toTop.onVertex v).comp (((C.step (le_top : (i : WithTop L.δ) ≤ ⊤)).onVertex v).comp
      ((C.into (i : WithTop L.δ)).onVertex v)) = (C.listToTop.onVertex v).comp (L.incl.onVertex v) := by
    intro v
    rw [C.into_step]
    exact C.comm_A v
  have hsel : ∀ (s : Fin n) (a : L.indexAt (ix s).1),
      C.toTop.mapOcc ((C.step (le_top : (i : WithTop L.δ) ≤ ⊤)).mapOcc
        (C.mark (ix s).1 (i : WithTop L.δ) (WithTop.coe_lt_coe.2 (ix s).2) a)) =
      C.listToTop.mapOcc (L.val (ix s).1 a) := by
    intro s a
    rw [C.mark_step]
    exact C.mark_spec _ a
  refine infra_712_productTied_transfer P hμ h0 h1 (p := L.one i)
    (q := L.subConcat n (fun s => (ix s).1)) (J := L.consJoint i n (fun s => (ix s).1))
    (p' := TupleOver.restrict ((C.truncate i hfree).into ⊤) _ (C.markTuple i))
    (q' := (C.truncate i hfree).selectionOver (C.markTuple i) n ix)
    (J' := (C.truncate i hfree).jointWith (C.markTuple i) n ix)
    (e := Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
    (Equiv.refl _) (by rintro (a | b) <;> rfl) ?_ ?_ ?_ rfl rfl rfl rfl rfl rfl
    (L.finite_each i) ?_ ?_ H
  · exact ⟨μ, hμ, C.top, C.toTop, C.listToTop, trivial, trivial, hincl,
      fun k => C.mark_spec i k⟩
  · exact ⟨μ, hμ, C.top, C.toTop, C.listToTop, trivial, trivial, hincl,
      fun k => hsel k.1 k.2⟩
  · refine ⟨μ, hμ, C.top, C.toTop, C.listToTop, trivial, trivial, hincl, ?_⟩
    rintro (k | ⟨s, a⟩)
    · exact C.mark_spec i k
    · exact hsel s a
  · have := fun s : Fin n => L.finite_each (ix s).1
    exact inferInstanceAs (Finite (Σ s : Fin n, L.indexAt (ix s).1))
  · have := fun s : Fin n => L.finite_each (ix s).1
    have := L.finite_each i
    exact inferInstanceAs (Finite (L.indexAt i ⊕ Σ s : Fin n, L.indexAt (ix s).1))

end
end AEC
