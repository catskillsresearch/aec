module

public import AEC.Section6.BoundedProducts
public import AEC.Section4.ClosedLevelAmalgam
public import AEC.Section4.CompactPlacement

@[expose] public section

/-!
# Cross-level transitivity of Galois types (`infra_612_galois_trans_cross_level`)

`SameGaloisType.trans_via` composes Galois-type equalities when all three hosts sit at the
base level `μ`. Here the first host may sit at any level `ν₁ ≥ μ`.

The off-level host `t1.host` is charted onto `E(lvlOrder ν₁)`. The image of the base `A` and of
the tuple of `t1` has size `μ`, so (finite term supports) it lies in a sub-presentation `E(I)`,
`I ⊆ lvlOrder ν₁`, `#I = μ`. The level-`μ` amalgam of Theorem 4.11 (`exists_tuple_amalgam`)
identifies the restricted tuple with the tuple of `t3` over `A`; the amalgam then embeds over
`E(I)` into a presentation `E(lvlOrder ρ')` at a level `ρ' ≥ ν₁, D.t μ`
(`exists_strong_embedding_over`), and the chart of `t1.host` pushed to `ρ'` closes the square.

No off-level amalgam (`tuple_amalgam_large`) is used. The case with *both* ends off-level stays
open (`infra_612_galois_trans_cross_level_both_off`).
-/

namespace AEC
section

universe u

open Cardinal FirstOrder

variable {K : AbstractElementaryClass.{u}}

/-- A set of size `≤ μ` of a presentation `E(J)`, `μ ≤ #J`, has all its fixed term supports in
a suborder of size exactly `μ`. -/
theorem infra_612_small_support (E : OrderPresentation K) {J : Type u} [LinearOrder J]
    [Nonempty J] {μ : Cardinal.{u}} (hμ : aleph0 ≤ μ) (hJ : μ ≤ #J)
    (S : Set (E.obj J).carrier) (hS : #S ≤ μ) :
    ∃ I : Set J, #I = μ ∧ ∀ x ∈ S, termSupport (supportTermOf E x) ⊆ I := by
  obtain ⟨T, hT⟩ := Cardinal.le_mk_iff_exists_set.mp hJ
  refine ⟨paramSupport E S ∪ T, le_antisymm ?_ ?_, fun x hx =>
    (termSupport_subset_paramSupport E hx).trans Set.subset_union_left⟩
  · refine (mk_union_le _ _).trans ?_
    rw [hT]
    exact (add_le_add_left (mk_paramSupport_le E hμ hS) μ).trans (add_eq_self hμ).le
  · rw [← hT]
    exact mk_le_mk_of_subset Set.subset_union_right

/-- An element whose term support lies in `I` comes from the sub-presentation `E(I)`. -/
theorem infra_612_map_restrict (E : OrderPresentation K) {J : Type u} [LinearOrder J]
    [Nonempty J] (I : Set J) [Nonempty I] (x : (E.obj J).carrier)
    (h : termSupport (supportTermOf E x) ⊆ I) :
    E.map (OrderEmbedding.subtype (· ∈ I))
      (E.realize ((supportTermOf E x).restrict I h)) = x := by
  rw [E.realize_along, SupportTerm.along_restrict, realize_supportTermOf]

/-- **Done.** The testing criterion with the first host at any level: if the bounded diagrams
over `A` of the tuple of `t1` (host at any eligible level) and of `t3` (host at `μ`) agree,
`t1` and `t3` have the same Galois type. -/
theorem infra_612_same_galois_left_large
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    (t1 t3 : TupleOver K oneVertexShape P.scheme hμ A)
    (e : t1.idx ≃ t3.idx)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hσμ : σ < μ)
    (hidx : #t1.idx ≤ σ) (hν3 : t3.ν = μ)
    (hL : ClosedLevel K P.E P.D P.g μ)
    (htest : ∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(t3.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card t1.host.model)
      (h₁ : P.D.t ρ ≤ Model.card t3.host.model),
      P.D.same hjoint t1.host.mem t3.host.mem h₀ h₁
        (Sum.elim (fun i => t1.host.val (t1.val (e.symm i)))
          (fun b => t1.incl.onVertex PUnit.unit (params b)))
        (Sum.elim (fun i => t3.host.val (t3.val i))
          (fun b => t3.incl.onVertex PUnit.unit (params b)))) :
    SameGaloisType t1 t3 e (Equiv.refl t3.idx) := by
  classical
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  have hν1 : t1.ν ∈ P.eligible := t1.hν
  let c : t1.host.model.carrier ≃[K.τ] (P.G t1.ν).carrier := SingleModelData.chart hν1 t1.host
  have hc : K.Strong c.toEmbedding := strong_of_equiv K c t1.host.mem
  let a1 : Language.Embedding K.τ A.model.carrier t1.host.model.carrier :=
    t1.incl.onVertex PUnit.unit
  have ha1 : K.Strong a1 := t1.incl.onVertex_strong PUnit.unit
  let a3 : Language.Embedding K.τ A.model.carrier t3.host.model.carrier :=
    t3.incl.onVertex PUnit.unit
  have ha3 : K.Strong a3 := t3.incl.onVertex_strong PUnit.unit
  let x1 : t3.idx → t1.host.model.carrier := fun i => t1.host.val (t1.val (e.symm i))
  let d3 : t3.idx → t3.host.model.carrier := fun i => t3.host.val (t3.val i)
  have hcA : Model.card A.model = μ := A.card
  have hc1 : Model.card t1.host.model = t1.ν := t1.host.card
  have hc3 : Model.card t3.host.model = μ := by simpa [hν3] using t3.host.card
  have hα : #t3.idx ≤ σ := (Cardinal.mk_congr e).symm.trans_le hidx
  have hαμ : #t3.idx < μ := hα.trans_lt hσμ
  have hμinf : aleph0 ≤ μ := SingleModelData.aleph0_le hμ
  have hμν : μ ≤ t1.ν := by
    have h := Cardinal.mk_le_of_injective a1.injective
    have e1 : #A.model.carrier = μ := hcA
    have e2 : #t1.host.model.carrier = t1.ν := hc1
    rwa [e1, e2] at h
  -- the image of `A` and of the tuple in the chart
  let S : Set (P.G t1.ν).carrier := Set.range (fun a => c (a1 a)) ∪ Set.range (fun i => c (x1 i))
  have hS : #S ≤ μ := by
    refine (mk_union_le _ _).trans ?_
    refine (add_le_add mk_range_le mk_range_le).trans ?_
    have h1 : #A.model.carrier = μ := hcA
    rw [h1]
    exact (add_le_add_right (hα.trans hσμ.le) μ).trans (add_eq_self hμinf).le
  have hJ : μ ≤ #(lvlOrder t1.ν) := by
    rw [mk_lvlOrder (SingleModelData.aleph0_le hν1)]; exact hμν
  obtain ⟨I, hIμ, hIS⟩ := infra_612_small_support P.E hμinf hJ S hS
  have : Nonempty I := by
    rw [← Cardinal.mk_ne_zero_iff, hIμ]
    exact (aleph0_pos.trans_le hμinf).ne'
  let ι : I ↪o lvlOrder t1.ν := OrderEmbedding.subtype (· ∈ I)
  have hpre : ∀ x ∈ S, ∃ y, P.E.map ι y = x := fun x hx =>
    ⟨_, infra_612_map_restrict P.E I x (hIS x hx)⟩
  have hB0 : K.Mem (P.E.obj I) := P.hE _
  have hcB0 : Model.card (P.E.obj I) = μ := SingleModelData.card_obj_eq hμ _ hIμ
  have hιs : K.Strong (P.E.map ι) := P.E.map_strong ι
  let f0 : Language.Embedding K.τ A.model.carrier (P.E.obj I).carrier :=
    factorEmbedding (c.toEmbedding.comp a1) (P.E.map ι) (fun a => hpre _ (Or.inl ⟨a, rfl⟩))
  have hf0 : ∀ a, P.E.map ι (f0 a) = c (a1 a) := fun a =>
    factorEmbedding_apply _ _ _ a
  have hf0s : K.Strong f0 :=
    strong_factorEmbedding _ _ (K.strong_trans _ _ ha1 hc) hιs _
  let d0 : t3.idx → (P.E.obj I).carrier := fun i =>
    Classical.choose (hpre _ (Or.inr ⟨i, rfl⟩))
  have hd0 : ∀ i, P.E.map ι (d0 i) = c (x1 i) := fun i =>
    Classical.choose_spec (hpre _ (Or.inr ⟨i, rfl⟩))
  -- `E(I) → t1.host` along the chart
  let r : Language.Embedding K.τ (P.E.obj I).carrier t1.host.model.carrier :=
    c.symm.toEmbedding.comp (P.E.map ι)
  have hr : K.Strong r := K.strong_trans _ _ hιs (strong_of_equiv K c.symm (P.mem_G _))
  -- tests for the level-`μ` amalgam
  have htest' : ∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (p : β → A.model.carrier) (hjoint : #(t3.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card (P.E.obj I)) (h₁ : P.D.t ρ ≤ Model.card t3.host.model),
      P.D.same hjoint hB0 t3.host.mem h₀ h₁
        (Sum.elim d0 (fun b => f0 (p b))) (Sum.elim d3 (fun b => a3 (p b))) := by
    intro β hβ ρ hρinf hρμ p hj h0 h1
    have hH : P.D.t ρ ≤ Model.card t1.host.model := by
      rw [hc1]; exact (SingleModelData.t_lt hμ hρinf hρμ).le.trans hμν
    have hT := htest hβ ρ hρinf hρμ p hj hH h1
    have hR := P.D.of_strong hj hB0 t1.host.mem h0 hH (Sum.elim d0 (fun b => f0 (p b)))
      (Sum.elim x1 (fun b => a1 (p b))) r hρinf hr (by
        rintro (i | b)
        · change c.symm (P.E.map ι (d0 i)) = x1 i
          rw [hd0]; exact c.symm_apply_apply _
        · change c.symm (P.E.map ι (f0 (p b))) = a1 (p b)
          rw [hf0]; exact c.symm_apply_apply _)
    exact P.D.trans hj hB0 t1.host.mem t3.host.mem h0 hH h1 _ _ _ hR hT
  obtain ⟨P₀, g₀, g₃, hP₀, hg₀, hg₃, hcP₀, hbase, hd⟩ :=
    hL.exists_tuple_amalgam hσ hσμ hα A.model (P.E.obj I) t3.host.model f0 a3 d0 d3
      A.mem hB0 t3.host.mem hf0s ha3 hcA hcB0 hc3 htest'
  -- a level above `ν₁` and `D.t μ`
  obtain ⟨ρ', hρ'ge, hρ'⟩ := P.exists_ge (max t1.ν (P.D.t μ))
  have hle : t1.ν ≤ ρ' := (le_max_left _ _).trans hρ'ge
  let j : lvlOrder t1.ν ↪o lvlOrder ρ' := lvlEmb hle
  let f : I ↪o lvlOrder ρ' := ι.trans j
  have hcL : Model.card (P.E.obj (lvlOrder ρ')) = ρ' := SingleModelData.card_G hρ'
  have hcatL : Categorical K (Model.card (P.E.obj (lvlOrder ρ'))) := by
    rw [hcL]; exact SingleModelData.categorical hρ'
  have hLc : P.D.t μ ≤ Model.card (P.E.obj (lvlOrder ρ')) := by
    rw [hcL]; exact (le_max_right _ _).trans hρ'ge
  have hz : LiftsTuple P.E P.D hP₀ g₀ μ f (fun i => g₀ (d0 i)) (fun i => P.E.map f (d0 i)) := by
    intro β ρ hρ hρμ p hj hBc hJc
    have hc0 : P.D.t ρ ≤ Model.card (P.E.obj I) := by
      rw [hcB0]; exact (SingleModelData.t_lt hμ hρ hρμ).le
    have h1 := P.D.of_strong hj hB0 hP₀ hc0 hBc (Sum.elim d0 p)
      (Sum.elim (fun i => g₀ (d0 i)) (fun b => g₀ (p b))) g₀ hρ hg₀ (by rintro (_ | _) <;> rfl)
    have h2 := P.D.of_strong hj hB0 (orderPresentation_obj_mem P.E _) hc0 hJc
      (Sum.elim d0 p) (Sum.elim (fun i => P.E.map f (d0 i)) (fun b => P.E.map f (p b)))
      (P.E.map f) hρ (P.E.map_strong f) (by rintro (_ | _) <;> rfl)
    exact P.D.trans hj hP₀ hB0 _ hBc hc0 hJc _ _ _
      (P.D.symm hj hB0 hP₀ hc0 hBc _ _ h1) h2
  obtain ⟨F, hF, hFincl, hFd⟩ :=
    exists_strong_embedding_over hL hIμ hg₀ hcP₀ f hcatL hLc (fun i => g₀ (d0 i)) hαμ
      (fun i => P.E.map f (d0 i)) hz
  have hmap : ∀ y, P.E.map f y = P.E.map j (P.E.map ι y) := fun y => by
    change P.E.map (ι.trans j) y = _
    rw [P.E.map_comp]; rfl
  -- the common top
  let top : SMObject K ρ' := SMObject.ofModel (P.E.obj (lvlOrder ρ')) (P.hE _) hcL
  let φ : (P.E.obj (lvlOrder ρ')).carrier ≃[K.τ] top.model.carrier :=
    SMObject.ofModelEquiv (P.E.obj (lvlOrder ρ')) (P.hE _) hcL
  have hφ : K.Strong φ.toEmbedding := strong_of_equiv K φ (P.hE _)
  let emb₁ : Language.Embedding K.τ t1.host.model.carrier top.model.carrier :=
    φ.toEmbedding.comp ((P.E.map j).comp c.toEmbedding)
  let emb₃ : Language.Embedding K.τ t3.host.model.carrier top.model.carrier :=
    φ.toEmbedding.comp (F.comp g₃)
  have hs₁ : K.Strong emb₁ :=
    K.strong_trans _ _ (K.strong_trans _ _ hc (P.E.map_strong j)) hφ
  have hs₃ : K.Strong emb₃ := K.strong_trans _ _ (K.strong_trans _ _ hg₃ hF) hφ
  let arr₁ : SystemArrow K oneVertexShape (P.scheme.asSystem t1.hν t1.host)
      (P.scheme.asSystem hρ' top) :=
    oneVertexArrow emb₁ hs₁
  let arr₃ : SystemArrow K oneVertexShape (P.scheme.asSystem t3.hν t3.host)
      (P.scheme.asSystem hρ' top) :=
    oneVertexArrow emb₃ hs₃
  refine ⟨ρ', hρ', top, arr₁, arr₃, trivial, trivial, ?_, ?_⟩
  · intro v
    refine DFunLike.ext _ _ fun x => ?_
    have hv : v = PUnit.unit := Subsingleton.elim _ _
    subst hv
    change φ (P.E.map j (c (a1 x))) = φ (F (g₃ (a3 x)))
    rw [← hbase x, hFincl, hmap]
    exact congrArg (fun y => φ (P.E.map j y)) (hf0 x).symm
  · intro i
    change
      (⟨(t1.val (e.symm i)).1, emb₁ (t1.val (e.symm i)).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hρ' top)) =
      ⟨(t3.val ((Equiv.refl t3.idx).symm i)).1,
        emb₃ (t3.val ((Equiv.refl t3.idx).symm i)).2⟩
    have hv : (t1.val (e.symm i)).1 = PUnit.unit := Subsingleton.elim _ _
    have hw : (t3.val i).1 = PUnit.unit := Subsingleton.elim _ _
    simp only [Equiv.refl_symm, Equiv.refl_apply, hv, hw]
    change (⟨PUnit.unit, φ (P.E.map j (c (x1 i)))⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hρ' top)) =
      ⟨PUnit.unit, φ (F (g₃ (d3 i)))⟩
    rw [← hd i, hFd, hmap]
    exact congrArg (fun y => (⟨PUnit.unit, φ (P.E.map j y)⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hρ' top))) (hd0 i).symm

/-- Move the nontrivial coordinate equivalence from the second tuple back onto the first
(converse of `SameGaloisType.swap_refl`). -/
theorem SameGaloisType.unswap_refl {S : SystemShape.{u}} {W : WorkingScheme K S}
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    {t1 t2 : TupleOver K S W hμ base} {e : t2.idx ≃ t1.idx}
    (h : SameGaloisType t1 t2 (Equiv.refl t1.idx) e) :
    SameGaloisType t1 t2 e.symm (Equiv.refl t2.idx) := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro j
  have h := hval (e j)
  rw [Equiv.symm_apply_apply, Equiv.refl_symm] at h
  rw [Equiv.refl_symm, Equiv.symm_symm]
  exact h

/-- **Done (one end at the base level).** `infra_612_galois_trans_cross_level` when the last
host is at `μ`; the first host may be at any eligible level. -/
theorem infra_612_galois_trans_cross_level_right_base
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {t1 t2 t3 : TupleOver K oneVertexShape P.scheme hμ A}
    {e12 : t1.idx ≃ t2.idx} {e32 : t3.idx ≃ t2.idx}
    (h12 : SameGaloisType t1 t2 e12 (Equiv.refl t2.idx))
    (h32 : SameGaloisType t2 t3 (Equiv.refl t2.idx) e32)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hσμ : σ < μ)
    (hidx : #t1.idx ≤ σ) (hrec : μ ∈ recursionClosedLevels P σ)
    (hν2 : t2.ν = μ) (hν3 : t3.ν = μ) :
    SameGaloisType t1 t3 (e12.trans e32.symm) (Equiv.refl t3.idx) := by
  have hL := infra_610_closed_level P σ hσ hμ hrec
  apply infra_612_same_galois_left_large t1 t3 (e12.trans e32.symm) σ hσ hσμ hidx hν3 hL
  intro β hβ ρ0 hρinf hρμ params hjnt h0 h1
  have hc2 : Model.card t2.host.model = μ := by simpa [hν2] using t2.host.card
  have h2 : P.D.t ρ0 ≤ Model.card t2.host.model :=
    (P.t_lt hμ hρinf hρμ).le.trans hc2.ge
  have h23 : #t3.idx = #t2.idx := Cardinal.mk_congr e32
  have hj2 : #t2.idx + #β ≤ ρ0 := by simpa [h23] using hjnt
  have hab := SameGaloisType.to_sameD h12 params ρ0 hρinf (by simpa using hj2) h0 h2
  have hbc := SameGaloisType.to_sameD h32 params ρ0 hρinf (by simpa using hj2) h2 h1
  have hmid := P.D.trans hj2 t1.host.mem t2.host.mem t3.host.mem h0 h2 h1 _ _ _
    (by simpa [Equiv.refl_symm] using hab) (by simpa [Equiv.refl_symm] using hbc)
  have hμ1 : μ ≤ Model.card t1.host.model := by
    have h : #A.model.carrier ≤ #t1.host.model.carrier :=
      Cardinal.mk_le_of_injective (t1.incl.onVertex PUnit.unit).injective
    have e1 : #A.model.carrier = μ := A.card
    rw [e1] at h
    exact h
  have hc3 : Model.card t3.host.model = μ := by simpa [hν3] using t3.host.card
  let σ' : Cardinal.{u} := max ρ0 (ls K)
  have hσ'μ : σ' < μ := max_lt hρμ (P.ls_lt hμ)
  have hσ'inf : aleph0 ≤ σ' := hρinf.trans (le_max_left _ _)
  have ht' : P.D.t σ' ≤ μ := (P.t_lt hμ hσ'inf hσ'μ).le
  let hι : (t3.idx ⊕ β) → (t2.idx ⊕ β) := Sum.map e32 id
  have hL1 := P.D.same_relevel hj2 hρinf hρinf (le_max_left ρ0 (ls K)) (le_max_left ρ0 (ls K))
    (le_max_right ρ0 (ls K)) t1.host.mem t3.host.mem h0 h1
    (ht'.trans hμ1) (ht'.trans hc3.ge) h0 h1 _ _ hmid hjnt hι
  convert hL1 using 1
  · funext c
    cases c with
    | inl k =>
      dsimp [hι, Sum.map]
      rfl
    | inr b =>
      dsimp [hι, Sum.map]
      exact congrArg (fun v => t1.incl.onVertex v (params b)) (Subsingleton.elim _ _)
  · funext c
    cases c with
    | inl k =>
      change t3.host.val (t3.val k) = t3.host.val (t3.val (e32.symm (e32 k)))
      rw [Equiv.symm_apply_apply]
    | inr b =>
      dsimp [hι, Sum.map]
      exact congrArg (fun v => t3.incl.onVertex v (params b)) (Subsingleton.elim _ _)

/-- **Done (one end at the base level).** `infra_612_galois_trans_cross_level` when the first
host is at `μ`; the last host may be at any eligible level. Reverse the chain and apply
`infra_612_galois_trans_cross_level_right_base`. -/
theorem infra_612_galois_trans_cross_level_left_base
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {t1 t2 t3 : TupleOver K oneVertexShape P.scheme hμ A}
    {e12 : t1.idx ≃ t2.idx} {e32 : t3.idx ≃ t2.idx}
    (h12 : SameGaloisType t1 t2 e12 (Equiv.refl t2.idx))
    (h32 : SameGaloisType t2 t3 (Equiv.refl t2.idx) e32)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hσμ : σ < μ)
    (hidx : #t1.idx ≤ σ) (hrec : μ ∈ recursionClosedLevels P σ)
    (hν1 : t1.ν = μ) (hν2 : t2.ν = μ) :
    SameGaloisType t1 t3 (e12.trans e32.symm) (Equiv.refl t3.idx) := by
  have hidx3 : #t3.idx ≤ σ := (Cardinal.mk_congr e32).trans_le
    ((Cardinal.mk_congr e12).symm.trans_le hidx)
  have h := infra_612_galois_trans_cross_level_right_base (t1 := t3) (t2 := t2) (t3 := t1)
    (e12 := e32) (e32 := e12) h32.symm h12.symm σ hσ hσμ hidx3 hrec hν2 hν1
  have h' := SameGaloisType.unswap_refl h.symm
  have he : (e32.trans e12.symm).symm = e12.trans e32.symm := by
    ext x; rfl
  rwa [he] at h'

/-- **`infra_612_galois_trans_cross_level` (board statement).** Galois-type equality composes
through a middle tuple whose host is at the base level `μ`; the outer hosts may sit at any
eligible levels. Recursion-closed `μ`, `σ⁺ ≤ μ`, `#t1.idx ≤ σ`, `t2.ν = μ`. -/
def infra_612_galois_trans_cross_level_statement (P : SingleModelData K) : Prop :=
  ∀ (σ : Cardinal.{u}) (_ : aleph0 ≤ σ) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (_ : μ ∈ recursionClosedLevels P σ) (_ : Order.succ σ ≤ μ)
    (A : P.scheme.Object μ hμ) (t1 t2 t3 : TupleOver K oneVertexShape P.scheme hμ A)
    (e12 : t1.idx ≃ t2.idx) (e32 : t3.idx ≃ t2.idx),
    #t1.idx ≤ σ → t2.ν = μ →
    SameGaloisType t1 t2 e12 (Equiv.refl t2.idx) →
    SameGaloisType t2 t3 (Equiv.refl t2.idx) e32 →
    SameGaloisType t1 t3 (e12.trans e32.symm) (Equiv.refl t3.idx)

/-- **Done.** The board statement of `infra_612_galois_trans_cross_level` whenever at least
one outer host is at the base level. The case with both outer hosts off-level is the open tip
`infra_612_galois_trans_cross_level_both_off`. -/
theorem infra_612_galois_trans_cross_level_of_base_end (P : SingleModelData K)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    (A : P.scheme.Object μ hμ) (t1 t2 t3 : TupleOver K oneVertexShape P.scheme hμ A)
    (e12 : t1.idx ≃ t2.idx) (e32 : t3.idx ≃ t2.idx)
    (hidx : #t1.idx ≤ σ) (hν2 : t2.ν = μ) (hend : t1.ν = μ ∨ t3.ν = μ)
    (h12 : SameGaloisType t1 t2 e12 (Equiv.refl t2.idx))
    (h32 : SameGaloisType t2 t3 (Equiv.refl t2.idx) e32) :
    SameGaloisType t1 t3 (e12.trans e32.symm) (Equiv.refl t3.idx) := by
  have hlt : σ < μ := (Order.lt_succ_of_not_isMax (not_isMax σ)).trans_le hσμ
  rcases hend with h1 | h3
  · exact infra_612_galois_trans_cross_level_left_base h12 h32 σ hσ hlt hidx hrec h1 hν2
  · exact infra_612_galois_trans_cross_level_right_base h12 h32 σ hσ hlt hidx hrec hν2 h3

/-- **A level-`μ` copy of a tuple (proved).** A tuple `t` over `A` (level `μ`) whose host sits
at any eligible level, with `#t.idx ≤ μ`, has the Galois type of a tuple with the same index type
whose host is at `μ`, by a direct witness: the host is a sub-presentation `E(I)`, `#I = μ`, of
the chart of `t.host` containing the image of `A` and of the tuple. -/
theorem infra_612_exists_level_copy
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    (t : TupleOver K oneVertexShape P.scheme hμ A) (hidx : #t.idx ≤ μ) :
    ∃ (host : P.scheme.Object μ hμ)
      (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ host))
      (hincl : P.scheme.permitted (X := A) (Y := host) incl)
      (val : t.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ host)),
      SameGaloisType t (⟨μ, hμ, host, incl, hincl, t.idx, val⟩ :
        TupleOver K oneVertexShape P.scheme hμ A) (Equiv.refl t.idx) (Equiv.refl t.idx) := by
  classical
  have hν1 : t.ν ∈ P.eligible := t.hν
  let c : t.host.model.carrier ≃[K.τ] (P.G t.ν).carrier := SingleModelData.chart hν1 t.host
  have hc : K.Strong c.toEmbedding := strong_of_equiv K c t.host.mem
  let a1 : Language.Embedding K.τ A.model.carrier t.host.model.carrier :=
    t.incl.onVertex PUnit.unit
  have ha1 : K.Strong a1 := t.incl.onVertex_strong PUnit.unit
  let x1 : t.idx → t.host.model.carrier := fun i => t.host.val (t.val i)
  have hcA : Model.card A.model = μ := A.card
  have hc1 : Model.card t.host.model = t.ν := t.host.card
  have hμinf : aleph0 ≤ μ := SingleModelData.aleph0_le hμ
  have hμν : μ ≤ t.ν := by
    have h := Cardinal.mk_le_of_injective a1.injective
    have e1 : #A.model.carrier = μ := hcA
    have e2 : #t.host.model.carrier = t.ν := hc1
    rwa [e1, e2] at h
  let S : Set (P.G t.ν).carrier := Set.range (fun a => c (a1 a)) ∪ Set.range (fun i => c (x1 i))
  have hS : #S ≤ μ := by
    refine (mk_union_le _ _).trans ?_
    refine (add_le_add mk_range_le mk_range_le).trans ?_
    have h1 : #A.model.carrier = μ := hcA
    rw [h1]
    exact (add_le_add_right hidx μ).trans (add_eq_self hμinf).le
  have hJ : μ ≤ #(lvlOrder t.ν) := by
    rw [mk_lvlOrder (SingleModelData.aleph0_le hν1)]; exact hμν
  obtain ⟨I, hIμ, hIS⟩ := infra_612_small_support P.E hμinf hJ S hS
  have : Nonempty I := by
    rw [← Cardinal.mk_ne_zero_iff, hIμ]
    exact (aleph0_pos.trans_le hμinf).ne'
  let ι : I ↪o lvlOrder t.ν := OrderEmbedding.subtype (· ∈ I)
  have hpre : ∀ x ∈ S, ∃ y, P.E.map ι y = x := fun x hx =>
    ⟨_, infra_612_map_restrict P.E I x (hIS x hx)⟩
  have hB0 : K.Mem (P.E.obj I) := P.hE _
  have hcB0 : Model.card (P.E.obj I) = μ := SingleModelData.card_obj_eq hμ _ hIμ
  have hιs : K.Strong (P.E.map ι) := P.E.map_strong ι
  let f0 : Language.Embedding K.τ A.model.carrier (P.E.obj I).carrier :=
    factorEmbedding (c.toEmbedding.comp a1) (P.E.map ι) (fun a => hpre _ (Or.inl ⟨a, rfl⟩))
  have hf0 : ∀ a, P.E.map ι (f0 a) = c (a1 a) := fun a =>
    factorEmbedding_apply _ _ _ a
  have hf0s : K.Strong f0 :=
    strong_factorEmbedding _ _ (K.strong_trans _ _ ha1 hc) hιs _
  let d0 : t.idx → (P.E.obj I).carrier := fun i =>
    Classical.choose (hpre _ (Or.inr ⟨i, rfl⟩))
  have hd0 : ∀ i, P.E.map ι (d0 i) = c (x1 i) := fun i =>
    Classical.choose_spec (hpre _ (Or.inr ⟨i, rfl⟩))
  let host : SMObject K μ := SMObject.ofModel (P.E.obj I) hB0 hcB0
  let ψ : (P.E.obj I).carrier ≃[K.τ] host.model.carrier := SMObject.ofModelEquiv _ hB0 hcB0
  have hψ : K.Strong ψ.toEmbedding := strong_of_equiv K ψ hB0
  have hψs : K.Strong ψ.symm.toEmbedding := strong_of_equiv K ψ.symm host.mem
  let r : Language.Embedding K.τ host.model.carrier t.host.model.carrier :=
    c.symm.toEmbedding.comp ((P.E.map ι).comp ψ.symm.toEmbedding)
  have hr : K.Strong r := K.strong_trans _ _ (K.strong_trans _ _ hψs hιs)
    (strong_of_equiv K c.symm (P.mem_G _))
  have hrd : ∀ i, r (ψ (d0 i)) = x1 i := fun i => by
    change c.symm (P.E.map ι (ψ.symm (ψ (d0 i)))) = x1 i
    rw [ψ.symm_apply_apply, hd0]; exact c.symm_apply_apply _
  have hrf : ∀ a, r (ψ (f0 a)) = a1 a := fun a => by
    change c.symm (P.E.map ι (ψ.symm (ψ (f0 a)))) = a1 a
    rw [ψ.symm_apply_apply, hf0]; exact c.symm_apply_apply _
  let incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ host) :=
    oneVertexArrow (ψ.toEmbedding.comp f0) (K.strong_trans _ _ hf0s hψ)
  let val : t.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ host) :=
    fun i => ⟨PUnit.unit, ψ (d0 i)⟩
  refine ⟨host, incl, trivial, val, t.ν, t.hν, t.host, SystemArrow.refl _,
    oneVertexArrow r hr, trivial, trivial, ?_, ?_⟩
  · intro v
    refine DFunLike.ext _ _ fun x => ?_
    have hv : v = PUnit.unit := Subsingleton.elim _ _
    subst hv
    change a1 x = r (ψ (f0 x))
    exact (hrf x).symm
  · intro i
    change (⟨(t.val i).1, (t.val i).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem t.hν t.host)) =
      ⟨PUnit.unit, r (ψ (d0 i))⟩
    rw [hrd]
    have hv : (t.val i).1 = PUnit.unit := Subsingleton.elim _ _
    change (⟨(t.val i).1, (t.val i).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem t.hν t.host)) =
      ⟨PUnit.unit, (t.val i).2⟩
    rw [hv]

end
end AEC
