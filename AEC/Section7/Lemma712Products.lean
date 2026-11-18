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

/-- Two Galois identifications through a level-`μ` middle compose (finite first tuple). -/
theorem infra_712_gtrans (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
    {t1 t2 t3 : TupleOver K oneVertexShape P.scheme hμ A} {ι ι' : Type u}
    (a : t1.idx ≃ ι) (b : t2.idx ≃ ι) (c : t2.idx ≃ ι') (d : t3.idx ≃ ι')
    (h2 : t2.ν = μ) (hend : t1.ν = μ ∨ t3.ν = μ) (hf : Finite t1.idx)
    (h12 : SameGaloisType t1 t2 a b) (h23 : SameGaloisType t2 t3 c d) :
    SameGaloisType t1 t3 ((a.trans b.symm).trans (c.trans d.symm)) (Equiv.refl _) := by
  have h12' := infra_612_sameGalois_trans_equiv h12 b.symm
  rw [Equiv.self_trans_symm] at h12'
  have h23' := infra_612_sameGalois_trans_equiv h23 d.symm
  rw [Equiv.self_trans_symm] at h23'
  have := infra_612_galois_trans_cross_level_of_base_end P ℵ₀ le_rfl hμ h0 h1 A t1 t2 t3
    (a.trans b.symm) (c.trans d.symm).symm (Cardinal.lt_aleph0_of_finite _).le h2 hend h12'
    h23'.swap_refl
  rwa [Equiv.symm_symm] at this

theorem infra_712_sg_congr_left {t1 t2 : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    {f f' : t1.idx ≃ ι} {g : t2.idx ≃ ι} (h : SameGaloisType t1 t2 f g)
    (hf : ∀ x, f x = f' x) : SameGaloisType t1 t2 f' g := Equiv.ext hf ▸ h

theorem infra_712_card_le_fin {α : Type u} [Finite α] (hμ : μ ∈ P.eligible) : #α ≤ μ :=
  (Cardinal.lt_aleph0_of_finite _).le.trans (P.aleph0_le hμ)

/-- **List products, last entry of an injective selection (proved, cycle 87).** -/
theorem infra_712_products_L_snoc (h0 : μ ∈ recursionClosedLevels P ℵ₀)
    (h1 : Order.succ ℵ₀ ≤ μ) (L : TupleList P.scheme hμ A) (hind : ProductIndependentTied L)
    (n : ℕ) (ixs : Fin (n + 1) → L.δ) (hinj : Function.Injective ixs) :
    IsProductTied (L.one (ixs (Fin.last n))) (L.subConcat n (fun s => ixs s.castSucc))
      (L.consJoint (ixs (Fin.last n)) n (fun s => ixs s.castSucc)) (Equiv.refl _) := by
  classical
  have hfe := L.finite_each
  have hfS : ∀ m (jx : Fin m → L.δ), Finite (Σ s, (L.one (jx s)).idx) := fun m jx =>
    inferInstanceAs (Finite (Σ s, L.indexAt (jx s)))
  obtain ⟨joint, E, hF, hS⟩ := hind (n + 1) ixs hinj
  obtain ⟨left, El, hleft, e, hP, hc1, hc2⟩ := hF
  have hfJ : Finite joint.idx := Finite.of_equiv _ E
  have hfL : Finite left.idx := Finite.of_equiv _ El
  obtain ⟨joint', eJ, rJ, hJν, hrJ, hRJ⟩ := infra_712_level_copy joint (infra_712_card_le_fin hμ)
  obtain ⟨left', eL, rL, hLν, hrL, hRL⟩ := infra_712_level_copy left (infra_712_card_le_fin hμ)
  have hfL' : Finite left'.idx := Finite.of_equiv _ eL.symm
  have hfJ' : Finite joint'.idx := Finite.of_equiv _ eJ.symm
  have hfb : Finite (L.one (ixs (Fin.last n))).idx := hfe _
  have hP1 := infra_712_productTied_pull_left hrL hRL (infra_712_productTied_pull_joint hrJ hRJ hP)
  obtain ⟨J2, e2, hP2⟩ := infra_612_tied_exists P ℵ₀ le_rfl hμ h0 h1
    (L.one (ixs (Fin.last n))) left' rfl hLν (Cardinal.lt_aleph0_of_finite _).le
  have hfJ2 : Finite J2.idx := Finite.of_equiv _ e2
  obtain ⟨J2', eJ2, rJ2, hJ2ν, hrJ2, hRJ2⟩ := infra_712_level_copy J2 (infra_712_card_le_fin hμ)
  have hfJ2' : Finite J2'.idx := Finite.of_equiv _ eJ2.symm
  have hP2' := infra_712_productTied_pull_joint hrJ2 hRJ2 hP2
  have hsym := infra_612_tied_symm_level_joints P ℵ₀ le_rfl hμ h0 h1 left'
    (L.one (ixs (Fin.last n))) hLν rfl (Cardinal.lt_aleph0_of_finite _).le
    (Cardinal.lt_aleph0_of_finite _).le joint' J2' _ _ hP1 hP2' hJν hJ2ν
  -- the joint side
  let c : (L.consJoint (ixs (Fin.last n)) n (fun s => ixs s.castSucc)).idx ≃
      (L.subConcat (n + 1) ixs).idx :=
    (Equiv.sumComm _ _).trans ((Equiv.sumCongr El (Equiv.refl _)).trans (e.trans E.symm))
  have hcv : ∀ k, (L.subConcat (n + 1) ixs).val (c k) =
      (L.consJoint (ixs (Fin.last n)) n (fun s => ixs s.castSucc)).val k := by
    rintro (a | ⟨s, a⟩)
    · have hc : c (Sum.inl a) = ⟨Fin.last n, a⟩ := by
        show E.symm (e (Sum.inr a)) = _
        exact E.symm_apply_eq.2 (hc2 a).symm
      rw [hc]; rfl
    · have hc : c (Sum.inr ⟨s, a⟩) = ⟨s.castSucc, a⟩ := by
        show E.symm (e (Sum.inl (El ⟨s, a⟩))) = _
        exact E.symm_apply_eq.2 (hc1 s a).symm
      rw [hc]; rfl
  have hJ0 : SameGaloisType (L.consJoint (ixs (Fin.last n)) n (fun s => ixs s.castSucc)) joint
      (c.trans E) (Equiv.refl _) := by
    obtain ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩ := hS
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, fun i => ?_⟩
    rw [← hcv, show c ((c.trans E).symm i) = E.symm i from c.apply_symm_apply (E.symm i)]
    exact hval i
  have hJ1 := (infra_712_sameGalois_pull hrJ hRJ hJ0.symm).symm
  have hJ := infra_712_gtrans h0 h1 _ _ _ _ hJν (Or.inl rfl) (
    inferInstanceAs (Finite (L.indexAt (ixs (Fin.last n)) ⊕ Σ s : Fin n, L.indexAt (ixs s.castSucc))))
    hJ1 hsym
  -- the selection side
  obtain ⟨joint0, E0, hF0, hS0⟩ := hind n (fun s => ixs s.castSucc)
    (hinj.comp (Fin.castSucc_injective _))
  have hfJ0 : Finite joint0.idx := Finite.of_equiv _ E0
  obtain ⟨joint0', eJ0, r0, hJ0ν, hr0, hR0⟩ := infra_712_level_copy joint0 (infra_712_card_le_fin hμ)
  have hQ1 := (infra_712_sameGalois_pull hr0 hR0 hS0.symm).symm
  have hlev0 := infra_712_finiteProduct_toLevel n (fun s => L.one (ixs s.castSucc))
    (fun s => hfe _) joint0 E0 hF0 joint0' eJ0 r0 hr0 hR0
  have hlevL := infra_712_finiteProduct_toLevel n (fun s => L.one (ixs s.castSucc))
    (fun s => hfe _) left El hleft left' eL rL hrL hRL
  have hperm := infra_612_tied_finite_perm_level P ℵ₀ le_rfl hμ h0 h1 n
    (fun s => L.one (ixs s.castSucc)) (fun s => ⟨rfl, (Cardinal.lt_aleph0_of_finite (L.indexAt (ixs s.castSucc))).le⟩) 1
    joint0' left' _ _ hlev0 hlevL hJ0ν hLν
  have hQ := infra_712_gtrans h0 h1 _ _ _ _ hJ0ν (Or.inl rfl)
    (hfS n (fun s => ixs s.castSucc)) hQ1 hperm
  have hQ' : SameGaloisType (L.subConcat n (fun s => ixs s.castSucc)) left' (El.trans eL.symm)
      (Equiv.refl _) := by
    refine infra_712_sg_congr_left hQ (fun x => ?_)
    have h : E0.symm (eJ0 ((E0.trans (eJ0.trans (Equiv.refl _)).symm) x)) = x := by
      show E0.symm (eJ0 (eJ0.symm (E0 x))) = x
      rw [eJ0.apply_symm_apply]; exact E0.symm_apply_apply x
    exact congrArg (El.trans eL.symm) h
  have hJ' : SameGaloisType (L.consJoint (ixs (Fin.last n)) n (fun s => ixs s.castSucc)) J2'
      ((Equiv.sumCongr (Equiv.refl _) (El.trans eL.symm)).trans (e2.trans eJ2.symm))
      (Equiv.refl _) := by
    refine infra_712_sg_congr_left hJ (fun k => ?_)
    rcases k with a | y
    · have hE : E (c (Sum.inl a)) = e (Sum.inr a) := E.apply_symm_apply _
      have h1 : ((eL.sumCongr (Equiv.refl (L.one (ixs (Fin.last n))).idx)).trans
          (e.trans eJ.symm)).symm (eJ.symm (e (Sum.inr a))) = Sum.inr a :=
        Equiv.symm_apply_apply _ (Sum.inr a)
      show (e2.trans eJ2.symm) ((Equiv.sumComm _ _).symm
        (((eL.sumCongr (Equiv.refl (L.one (ixs (Fin.last n))).idx)).trans
          (e.trans eJ.symm)).symm (eJ.symm (E (c (Sum.inl a)))))) = (e2.trans eJ2.symm) (Sum.inl a)
      rw [hE, h1]
      rfl
    · have hE : E (c (Sum.inr y)) = e (Sum.inl (El y)) := E.apply_symm_apply _
      have h1 : ((eL.sumCongr (Equiv.refl (L.one (ixs (Fin.last n))).idx)).trans
          (e.trans eJ.symm)).symm (eJ.symm (e (Sum.inl (El y)))) = Sum.inl (eL.symm (El y)) := by
        rw [Equiv.symm_apply_eq]
        show _ = eJ.symm (e (Sum.inl (eL (eL.symm (El y)))))
        rw [eL.apply_symm_apply]
      show (e2.trans eJ2.symm) ((Equiv.sumComm _ _).symm
        (((eL.sumCongr (Equiv.refl (L.one (ixs (Fin.last n))).idx)).trans
          (e.trans eJ.symm)).symm (eJ.symm (E (c (Sum.inr y)))))) = (e2.trans eJ2.symm) _
      rw [hE, h1]
      rfl
  exact infra_712_productTied_transfer P hμ h0 h1 (p := L.one (ixs (Fin.last n))) (q := left')
    (J := J2') (e := e2.trans eJ2.symm) (p' := L.one (ixs (Fin.last n)))
    (q' := L.subConcat n (fun s => ixs s.castSucc))
    (J' := L.consJoint (ixs (Fin.last n)) n (fun s => ixs s.castSucc))
    (Equiv.refl _) (Equiv.refl _) (El.trans eL.symm)
    ((Equiv.sumCongr (Equiv.refl _) (El.trans eL.symm)).trans (e2.trans eJ2.symm))
    (fun s => rfl) (SameGaloisType.refl _) hQ' hJ' rfl rfl hLν rfl hJ2ν rfl hfb hfL'
    (inferInstanceAs (Finite (L.indexAt (ixs (Fin.last n)) ⊕ Σ s : Fin n, L.indexAt (ixs s.castSucc))))
    hP2'

/-- **7.12(1), products in the list (proved, cycle 87).** Apply `infra_712_products_L_snoc` to
the injective selection `snoc ix i`. -/
theorem infra_712_products_L (P : SingleModelData K) : infra_712_products_L_statement P := by
  intro μ hμ h0 h1 _ _ A L _ _ hind i n ix hinj hlt
  let ixs : Fin (n + 1) → L.δ := Fin.snoc (α := fun _ => L.δ) ix i
  have hinj' : Function.Injective ixs := by
    intro a b hab
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast t =>
        simp only [ixs, Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab.symm (hlt t).ne
    | cast s =>
      induction b using Fin.lastCases with
      | last =>
        simp only [ixs, Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab (hlt s).ne
      | cast t =>
        simp only [ixs, Fin.snoc_castSucc] at hab
        rw [hinj hab]
  have key := infra_712_products_L_snoc h0 h1 L hind n ixs hinj'
  have e1 : ixs (Fin.last n) = i := Fin.snoc_last (α := fun _ => L.δ) _ _
  have e2 : (fun s : Fin n => ixs s.castSucc) = ix :=
    funext fun s => Fin.snoc_castSucc (α := fun _ => L.δ) _ _ _
  rw [e1, e2] at key
  exact key


/-- **7.12(1), products along the chain (proved, cycle 87).** -/
theorem infra_712_products (P : SingleModelData K) : infra_712_products_statement P :=
  infra_712_products_of_L P (infra_712_products_L P)

/-- **7.12(1), the free step (proved, cycle 87).** -/
theorem infra_712_free_step (P : SingleModelData K) : infra_712_free_step_statement P :=
  infra_712_free_step_of_products P (infra_712_products P)

/-- **7.12(1), all marks free (proved, cycle 87).** -/
theorem infra_712_free_marks (P : SingleModelData K) : infra_712_free_marks_statement P :=
  infra_712_free_marks_of_step P (infra_712_free_step P)

/-- **Lemma 7.12 (1) (proved, cycle 87).** At every level of `A` that is a Theorem 7.9 level
(`infra_78_closedTail P ∩ infra_615_closed P`) and a Lemma 7.11 level (closed for the
`ℵ₀`- and `infra_75_wide P ℵ₀`-recursions, above their successors): "If `L` is well-ordered
[of length `≤ μ`] and product-independent over `A`, then `L` has a witnessing chain in which
all increments are all-dominated" — exactly clause (1) of `lemma_7_12`
(`infra_712_existence_at`). -/
theorem lemma_7_12_existence (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (ht : μ ∈ infra_78_closedTail P) (hc : μ ∈ infra_615_closed P)
    (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
    (hw1 : μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀))
    (hw2 : Order.succ (infra_75_wide P ℵ₀) ≤ μ) (A : P.scheme.Object μ hμ) :
    infra_712_existence_at P hμ A :=
  infra_712_existence_at_of_products P (infra_712_products P) hμ ht hc h0 h1 hw1 hw2 A

/-- The 7.12(1) levels: Theorem 7.9 levels above `infra_75_wide P ℵ₀`. -/
def infra_712_levels (P : SingleModelData K) : Set Cardinal.{u} :=
  {μ | μ ∈ infra_78_closedTail P ∧ μ ∈ infra_615_closed P ∧ infra_75_wide P ℵ₀ < μ}

/-- A Section 6.15 closed level is closed for the recursion at every smaller infinite size. -/
theorem infra_712_recursionClosed_of_615 {P : SingleModelData K} {μ σ : Cardinal.{u}}
    (hc : μ ∈ infra_615_closed P) (hσ : ℵ₀ ≤ σ) (hlt : σ < μ) :
    μ ∈ recursionClosedLevels P σ :=
  ⟨hc.1, fun β₀ hβ => hc.2 σ hσ hlt β₀ hβ⟩

/-- **The 7.12(1) levels form a tail (proved, cycle 88).** -/
theorem infra_712_levels_tail (P : SingleModelData K) : Tail P.eligible (infra_712_levels P) := by
  refine ⟨fun μ hμ => hμ.2.1.1, fun κ => ?_⟩
  obtain ⟨μ, hle, ht, hc⟩ := infra_79_tail P (max κ (Order.succ (infra_75_wide P ℵ₀)))
  exact ⟨μ, (le_max_left _ _).trans hle, ht, hc,
    (Order.lt_succ _).trans_le ((le_max_right _ _).trans hle)⟩

/-- **Lemma 7.12 (1) on a tail (proved, cycle 88).** "At sufficiently closed eligible levels":
on the tail `infra_712_levels P` every level satisfies the hypotheses of
`lemma_7_12_existence`, so clause (1) of `lemma_7_12` holds there. -/
theorem lemma_7_12_existence_tail (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T, ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ)),
      infra_712_existence_at P (Tail.mem hT hμ) A := by
  refine ⟨infra_712_levels P, infra_712_levels_tail P, fun μ hμ A => ?_⟩
  obtain ⟨ht, hc, hw⟩ := hμ
  have hw0 : ℵ₀ ≤ infra_75_wide P ℵ₀ := le_self_add
  have h0lt : ℵ₀ < μ := hw0.trans_lt hw
  exact lemma_7_12_existence P _ ht hc (infra_712_recursionClosed_of_615 hc le_rfl h0lt)
    (Order.succ_le_of_lt h0lt) (infra_712_recursionClosed_of_615 hc hw0 hw)
    (Order.succ_le_of_lt hw) A

end
end AEC
