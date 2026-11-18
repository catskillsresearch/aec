module

public import AEC.Section7.RnextClosure

@[expose] public section

/-!
# Outputs of the Prop 7.8 matrix recursion (grokbot cycle 54)

`infra_78_recursion_outputs`.

* `infra_78_limit_inv5_cocone`: invariant (5) at a limit for ANY covering cocone (the engine's
  limit stage is a chosen cocone, not necessarily the one built in `infra_78_matrix_limit_step`).
* `infra_78_rc_inv5_all`: invariant (5) at every stage of the recursion matrix
  `infra_78_rcMatrix`, by induction (seed: hypothesis; successor: `infra_78_opMatrix_succ`;
  limit: the cocone lemma with mark/base coherence `infra_78_opMatrix_coherent`).
* Seeds (paper: the invariant (5) is relative to `X_0`): base `X_b = X_0`, base map the identity
  (`infra_78_tiedFree_of_id`, `infra_78_seedStage_inv5`), seeds `infra_78_seedSet I_p b y`.
* `infra_78_recursion_outputs`: matrix laws, (5) everywhere, `b ⊆ S_k`, `I_p ⊆ R_k`, and all
  bookkeeping outputs; `infra_78_rc_failing_list`: the failing-list property at every stage.
  Marks must be shorter than every limit cofinality (finite marks: `infra_78_finite_lt_stage_cof`);
  bounded marks at small cofinality are the Def 7.7 case tracked as
  `infra_78_def77_bounded_marks`.
-/

universe u
open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}

section LimitCocone
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

theorem infra_78_comp_apply {X Y Z : P.scheme.Object κ hκ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Y) (P.scheme.asSystem hκ Z)) (x) :
    (SystemArrow.comp f g).onVertex PUnit.unit x = g.onVertex PUnit.unit (f.onVertex PUnit.unit x) :=
  rfl

/-- **Invariant (5) at a limit for any covering cocone.** Same hypotheses as
`infra_78_matrix_limit_step`, but the union pair `X_δ → Y_δ` with legs, the base `g_δ` and the
mark `b_δ` are given (any cocone with commuting legs, commuting squares and covering `X`-legs). -/
theorem infra_78_limit_inv5_cocone (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (hrec : κ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ κ)
    {δ : (Order.succ ρ).ord.ToType}
    (hδ : Order.IsSuccLimit δ) (X Y : Set.Iio δ → P.scheme.Object κ hκ)
    (pair : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
      (P.scheme.asSystem hκ (Y j)))
    (sX : ∀ {a b : Set.Iio δ}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a)) (P.scheme.asSystem hκ (X b)))
    (hXt : ∀ {a b c : Set.Iio δ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sX (h₁.trans h₂) = SystemArrow.comp (sX h₁) (sX h₂))
    (Xb : P.scheme.Object κ hκ)
    (g : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb) (P.scheme.asSystem hκ (X j)))
    (hg : ∀ {a b : Set.Iio δ} (h : a ≤ b), SystemArrow.comp (g a) (sX h) = g b)
    {uIdx : Type u} (b : ∀ j, uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ (Y j)))
    (hidx : #uIdx ≤ σ) (hcof : #uIdx < (Ordinal.ToType.toOrd δ).1.cof)
    (h5 : ∀ j, IsTiedFree (g j) ((infra_78_markTuple (pair j) (b j)).restrict (g j) trivial)
      (infra_78_markTuple (pair j) (b j)) (Equiv.refl _))
    (Xδ Yδ : P.scheme.Object κ hκ)
    (lX : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j)) (P.scheme.asSystem hκ Xδ))
    (lY : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y j)) (P.scheme.asSystem hκ Yδ))
    (pδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xδ) (P.scheme.asSystem hκ Yδ))
    (hcX : ∀ {a c : Set.Iio δ} (h : a ≤ c), SystemArrow.comp (sX h) (lX c) = lX a)
    (hsq : ∀ j, SystemArrow.comp (pair j) (lY j) = SystemArrow.comp (lX j) pδ)
    (hcovX : ∀ x : (Xδ.model).carrier, ∃ j y, (lX j).onVertex PUnit.unit y = x)
    (gδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb) (P.scheme.asSystem hκ Xδ))
    (hgδ : ∀ j, SystemArrow.comp (g j) (lX j) = gδ)
    (bδ : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Yδ))
    (hbδ : ∀ j k, bδ k = pushOcc (lY j) (b j k)) :
    IsTiedFree gδ ((infra_78_markTuple pδ bδ).restrict gδ trivial)
      (infra_78_markTuple pδ bδ) (Equiv.refl _) := by
  classical
  let C := infra_78_partialChain hδ X sX hXt Xδ lX hcX hcovX
  let j0 : Set.Iio δ := ⟨infra_78_stg δ 0 C.hlim.1, infra_78_stg_lt δ 0 C.hlim.1⟩
  obtain rfl : SystemArrow.comp (g j0) (lX j0) = gδ := hgδ j0
  have hqκ : #uIdx < κ := hidx.trans_lt (Order.succ_le_iff.1 hσSucc)
  let p : TupleOver K oneVertexShape P.scheme hκ C.unionObj := infra_78_markTuple pδ bδ
  have hsqx : ∀ j (x : (X j).model.carrier),
      (lY j).onVertex PUnit.unit ((pair j).onVertex PUnit.unit x) =
        pδ.onVertex PUnit.unit ((lX j).onVertex PUnit.unit x) := fun j x =>
    DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hsq j)) x
  have hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree
        (SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
          (SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (P.scheme.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) trivial
            (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _) := by
    intro i hi
    let ji : Set.Iio δ := ⟨infra_78_stg δ i hi, infra_78_stg_lt δ i hi⟩
    have e1 : SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) =
        g ji := hg _
    have hR : infra_78_HostRel (infra_78_markTuple (pair ji) (b ji))
        (p.restrict (lX ji) trivial) (lY ji) (Equiv.refl _) :=
      ⟨fun v x => by cases v; exact hsqx ji x, fun k => hbδ ji k⟩
    have hR' : infra_78_HostRel ((infra_78_markTuple (pair ji) (b ji)).restrict (g ji) trivial)
        ((p.restrict (lX ji) trivial).restrict (g ji) trivial) (lY ji) (Equiv.refl _) :=
      ⟨fun v x => by cases v; exact hsqx ji _, fun k => hbδ ji k⟩
    have h1 := (infra_78_tiedFree_host_target (g ji)
      ((infra_78_markTuple (pair ji) (b ji)).restrict (g ji) trivial) trivial hR rfl rfl hqκ
      (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 (h5 ji)
    have h2 := infra_78_tiedFree_host_source (g ji) trivial hR' rfl rfl hqκ
      (p.restrict (lX ji) trivial) (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) h1
    exact infra_78_tiedFree_congr_arrow trivial trivial (p.restrict (lX ji) trivial) e1.symm h2
  exact infra_78_tied_continuity P σ hσ hκ hrec hσSucc C p rfl hidx hcof Xb (g j0) trivial hAll

end LimitCocone

section SeedInv5
variable {P : SingleModelData K} {κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

/-- **Tied freeness along an identity arrow**: a tuple is the tied free lift of its own
restriction along an arrow acting as the identity (two good copies of a long approximation
sequence chain `b ⌢ Z₀ ≡ copy ⌢ Z₀ ≡ copy ⌢ Z ≡ b ⌢ Z`). -/
theorem infra_78_tiedFree_of_id {A : P.scheme.Object κ hκ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hκ A) (P.scheme.asSystem hκ A))
    (hfid : ∀ x, f.onVertex PUnit.unit x = x) (hf : P.scheme.permitted (X := A) (Y := A) f)
    (q : TupleOver K oneVertexShape P.scheme hκ A) :
    IsTiedFree f (q.restrict f hf) q (Equiv.refl _) := by
  intro seq ι Z Z0 hκI hι _ hmove
  have hb0 := seq.few_exceptions Z0 hι
  have hb1 := seq.few_exceptions Z hι
  have hex : ∃ i, P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q.restrict f hf) Z0) (seqJoint (seq.family i) Z0) ∧
      P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q.restrict f hf) Z) (seqJoint (seq.family i) Z) := by
    by_contra hno
    have hsub : (Set.univ : Set seq.κIndex) ⊆
        {i | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
          (typeJoint (p := q.restrict f hf) Z0) (seqJoint (seq.family i) Z0)} ∪
        {i | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
          (typeJoint (p := q.restrict f hf) Z) (seqJoint (seq.family i) Z)} := by
      intro i _
      by_cases h0 : P.scheme.DiagramEq (X := q.host) (Y := A)
          (typeJoint (p := q.restrict f hf) Z0) (seqJoint (seq.family i) Z0)
      · exact Or.inr fun h1 => hno ⟨i, h0, h1⟩
      · exact Or.inl h0
    have hc := (Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_union_le _ _)
    rw [Cardinal.mk_univ] at hc
    have hτ : #ι + ℵ₀ ≤ seq.τ + ℵ₀ := add_le_add hι le_rfl
    have h2 : #seq.κIndex ≤ seq.τ + ℵ₀ :=
      hc.trans ((add_le_add (hb0.trans hτ) (hb1.trans hτ)).trans
        (Cardinal.add_eq_self ((le_add_left le_rfl : ℵ₀ ≤ seq.τ + ℵ₀))).le)
    exact absurd hκI (not_lt.2 h2)
  obtain ⟨i, h0, h1⟩ := hex
  have hmv := hmove i
  have hfam : (fun j => (⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hκ A))) = seq.family i := by
    funext j
    rcases hfx : seq.family i j with ⟨v, x⟩
    cases v
    exact congrArg (fun y => (⟨PUnit.unit, y⟩ : Occurrence K oneVertexShape
      (P.scheme.asSystem hκ A))) (hfid x)
  rw [hfam] at hmv
  have hJ : typeJoint (p := q.restrict f hf) Z =
      infra_612_anchored (Equiv.refl (q.restrict f hf).idx) q.incl q.val Z := by
    funext x
    rcases x with a | j
    · rfl
    · show (⟨(Z j).1, q.incl.onVertex (Z j).1 (f.onVertex (Z j).1 (Z j).2)⟩ :
          Occurrence K oneVertexShape _) = ⟨(Z j).1, q.incl.onVertex (Z j).1 (Z j).2⟩
      rcases hz : Z j with ⟨v, x⟩
      cases v
      exact congrArg (fun y => (⟨PUnit.unit, q.incl.onVertex PUnit.unit y⟩ :
        Occurrence K oneVertexShape _)) (hfid x)
  have key := P.scheme.diagram_trans _ _ _ _ _ _ h0
    (P.scheme.diagram_trans _ _ _ _ _ _ hmv (P.scheme.diagram_symm _ _ _ _ h1))
  exact hJ ▸ key

variable {uIdx : Type u}

/-- **Invariant (5) at the seed** (paper: the invariant is relative to `X_0`): with base
`X_b = X_0` and base map the identity, the seed stage satisfies (5). -/
theorem infra_78_seedStage_inv5 (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (X0 Y0 : P.scheme.Object κ hκ) (p0 : κ.ord.ToType → κ.ord.ToType)
    (hp0 : infra_78_IsArr X0 Y0 p0) (b0 : uIdx → κ.ord.ToType)
    (seeds : Set (κ.ord.ToType ⊕ κ.ord.ToType)) :
    infra_78_StageInv5 X0 (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 id b0 seeds) :=
  ⟨infra_78_isArr_id X0, infra_78_tiedFree_of_id _ (infra_78_toArr_apply _) trivial _⟩

/-- **The seed set**: the approximation list `I_p` on the `X`-side, the mark `b` and one more
point `y` on the `Y`-side (so `S_0 ≠ ∅` even for an empty mark). -/
def infra_78_seedSet (I : Set κ.ord.ToType) (b0 : uIdx → κ.ord.ToType) (y : κ.ord.ToType) :
    Set (κ.ord.ToType ⊕ κ.ord.ToType) :=
  Sum.inl '' I ∪ Sum.inr '' insert y (Set.range b0)

theorem infra_78_seedSet_card {ρ : Cardinal.{u}} (hρ : ℵ₀ ≤ ρ) {I : Set κ.ord.ToType}
    (hI : #I ≤ ρ) {b0 : uIdx → κ.ord.ToType} (hb : #uIdx ≤ ρ) (y : κ.ord.ToType) :
    #(infra_78_seedSet I b0 y) ≤ ρ := by
  refine (Cardinal.mk_union_le _ _).trans ((add_le_add (Cardinal.mk_image_le.trans hI)
    (Cardinal.mk_image_le.trans ((Cardinal.mk_insert_le).trans ?_))).trans (add_eq_self hρ).le)
  exact (add_le_add (Cardinal.mk_range_le.trans hb) (Cardinal.one_le_aleph0.trans hρ)).trans
    (add_eq_self hρ).le

end SeedInv5

section Inv5All
variable (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
  {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ) {uIdx cIdx L : Type u}
  {ρ : Cardinal.{u}} (hρκ : Order.succ ρ < μ)
  (Xb : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)) {ℓ : Cardinal.{u}}
  (hℓel : ℓ ∈ P.eligible)
  (cand : (Order.succ ρ).ord.ToType →
    Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx) →
    L → cIdx → μ.ord.ToType)
  (s0 : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
  (e0 : Infra78MarkData μ uIdx)

include hρκ in
/-- **Invariant (5) at every stage** of the recursion matrix with the concrete operators, from
(5) at the seed stage: successor stages by `infra_78_opMatrix_succ` (Prop 7.3 + type-identifying
amalgamation + transitivity), limit stages by tied continuity on the chosen covering cocone
(`infra_78_limit_inv5_cocone`, English Prop 6.13 / Def 7.7), for marks shorter than every limit
cofinality (e.g. finite marks, `infra_78_rc_inv5_all_finite`). -/
theorem infra_78_rc_inv5_all (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (hcof : ∀ δ : (Order.succ ρ).ord.ToType, Order.IsSuccLimit δ →
      #uIdx < (Ordinal.ToType.toOrd δ).1.cof)
    (h5seed : infra_78_StageInv5 Xb s0) (k : (Order.succ ρ).ord.ToType) :
    infra_78_StageInv5 Xb (infra_78_rcObj Xb hℓel cand s0 e0 k) := by
  have hsop := infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand
  obtain ⟨hA, -, -⟩ := infra_78_pairChain_laws hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) hsop
  have hM := infra_78_pairMatrix_compLaw hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) hsop
  have hCont := infra_78_pairMatrix_contAtLimits hρκ s0
    (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand) (infra_78_limMarkE e0) hsop
  have hu : #uIdx ≤ σ := (Cardinal.mk_le_of_injective Sum.inl_injective).trans hidx
  induction k using WellFoundedLT.induction with
  | _ k IH =>
  rcases infra_78_stage_trichotomy k with hmin | ⟨β, hβ⟩ | hk
  · have h : infra_78_rcObj Xb hℓel cand s0 e0 k = s0 := infra_78_pairMatrix_min s0 _ _ hmin
    rw [h]; exact h5seed
  · obtain ⟨-, -, -, -, -, -, h5, -⟩ := infra_78_opMatrix_succ P σ hσ hμT hρκ Xb
      (infra_78_rcl ρ hℓel) cand hidx s0 (infra_78_limMarkE e0) hβ (IH β hβ.lt)
    exact h5
  -- limit stage
  have hsX : ∀ {i j : (Order.succ ρ).ord.ToType} (h : i ≤ j) x,
      ((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepX h).onVertex PUnit.unit x =
        (infra_78_rcMap Xb hℓel cand s0 e0 i j).1 x := fun h x =>
    infra_78_pairMatrix_stepX_apply hρκ s0 _ _ hsop h x
  have hsY : ∀ {i j : (Order.succ ρ).ord.ToType} (h : i ≤ j) x,
      ((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepY h).onVertex PUnit.unit x =
        (infra_78_rcMap Xb hℓel cand s0 e0 i j).2 x := fun h x =>
    infra_78_pairMatrix_stepY_apply hρκ s0 _ _ hsop h x
  have IH' : ∀ j : Set.Iio k, infra_78_StageInv5 Xb (infra_78_rcObj Xb hℓel cand s0 e0 j.1) := fun j => IH j.1 j.2
  have hcoh := infra_78_opMatrix_coherent hρκ Xb (infra_78_rcl ρ hℓel) cand s0 e0
  obtain ⟨j0, hj0⟩ := not_isMin_iff.1 hk.not_isMin
  have hgk : infra_78_IsArr Xb (infra_78_rcObj Xb hℓel cand s0 e0 k).X (infra_78_rcObj Xb hℓel cand s0 e0 k).e.g := by
    have e := (hcoh j0 k hj0.le).1
    have h := infra_78_isArr_comp (IH j0 hj0).1 (hA j0 k hj0.le).1
    change infra_78_IsArr Xb (infra_78_rcObj Xb hℓel cand s0 e0 k).X ((infra_78_rcMap Xb hℓel cand s0 e0 j0 k).1 ∘ (infra_78_rcObj Xb hℓel cand s0 e0 j0).e.g) at h
    rw [← e] at h
    exact h
  refine ⟨hgk, ?_⟩
  exact infra_78_limit_inv5_cocone σ hσ hμT.1 (infra_73_tail_succ hμT) hk
    (fun j => (infra_78_rcObj Xb hℓel cand s0 e0 j.1).X) (fun j => (infra_78_rcObj Xb hℓel cand s0 e0 j.1).Y) (fun j => infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 j.1).hp)
    (fun {a b} h => (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepX (show a.1 ≤ b.1 from h))
    (fun h₁ h₂ => hM.1 h₁ h₂) Xb
    (fun j => infra_78_toArr (IH' j).1)
    (fun {a b} h => infra_78_arrow_ext fun x =>
      ((hsX (show a.1 ≤ b.1 from h) _).trans ((congrArg _ (infra_78_toArr_apply _ x)).trans
        (congrFun (hcoh a.1 b.1 h).1 x).symm)).trans (infra_78_toArr_apply _ x).symm)
    (fun j => infra_78_stageMark (infra_78_rcObj Xb hℓel cand s0 e0 j.1)) hu (hcof k hk)
    (fun j => (IH' j).2)
    (infra_78_rcObj Xb hℓel cand s0 e0 k).X (infra_78_rcObj Xb hℓel cand s0 e0 k).Y (fun j => (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepX j.2.le) (fun j => (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepY j.2.le)
    (infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 k).hp)
    (fun {a c'} h => (hM.1 (show a.1 ≤ c'.1 from h) c'.2.le).symm)
    (fun j => (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).comm j.2.le)
    (fun x => by
      obtain ⟨j, hj, y, hy⟩ := hCont.1 k hk x
      exact ⟨⟨j, hj⟩, y, hy⟩)
    (infra_78_toArr hgk)
    (fun j => infra_78_arrow_ext fun x =>
      ((hsX j.2.le _).trans ((congrArg _ (infra_78_toArr_apply _ x)).trans
        (congrFun (hcoh j.1 k j.2.le).1 x).symm)).trans (infra_78_toArr_apply _ x).symm)
    (infra_78_stageMark (infra_78_rcObj Xb hℓel cand s0 e0 k))
    (fun j u => by
      show (⟨PUnit.unit, (infra_78_rcObj Xb hℓel cand s0 e0 k).e.b u⟩ : Occurrence K oneVertexShape _) =
        ⟨PUnit.unit, ((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepY j.2.le).onVertex PUnit.unit ((infra_78_rcObj Xb hℓel cand s0 e0 j.1).e.b u)⟩
      rw [(hcoh j.1 k j.2.le).2]
      exact congrArg (fun y => (⟨PUnit.unit, y⟩ : Occurrence K oneVertexShape
        (P.scheme.asSystem _ (infra_78_rcObj Xb hℓel cand s0 e0 k).Y))) (hsY j.2.le _).symm)

/-- Finite marks are shorter than every limit cofinality. -/
theorem infra_78_finite_lt_stage_cof [Finite uIdx] (δ : (Order.succ ρ).ord.ToType)
    (hδ : Order.IsSuccLimit δ) : #uIdx < (Ordinal.ToType.toOrd δ).1.cof :=
  (Cardinal.mk_lt_aleph0_iff.2 ‹_›).trans_le
    (Ordinal.aleph0_le_cof_iff.mpr (Ordinal.one_lt_cof_iff.mpr (infra_78_stg_ord_limit δ hδ).2))

include hρκ in
/-- **`infra_78_recursion_outputs`.** The recursion matrix `infra_78_rcMatrix` built from the
seed stage with base `X_b = X_0`, base map the identity, mark `b_0` and seeds
`infra_78_seedSet I b_0 y` (`I = I_p`), for marks shorter than every limit cofinality (e.g.
finite, `infra_78_finite_lt_stage_cof`): the matrix laws (`IdLaw`, `CompLaw`, `ContAtLimits`),
invariant (5) at every stage, `b ⊆ S_k` and `I_p` (moved) `⊆ R_k` at every stage, and all
bookkeeping outputs of `infra_78_rnext_closure` (sizes, forward closure, continuity, pair
closure, `S_k ≠ ∅`, requirements 1/2 at non-limit and cofinality `> λ` stages). The failing-list
property at every stage is `infra_78_rc_failing_list`. -/
theorem infra_78_recursion_outputs (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (hcof : ∀ δ : (Order.succ ρ).ord.ToType, Order.IsSuccLimit δ →
      #uIdx < (Ordinal.ToType.toOrd δ).1.cof)
    (hℓκ : ℓ ≤ μ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    {Y0 : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)} {p0 : μ.ord.ToType → μ.ord.ToType}
    (hp0 : infra_78_IsArr Xb Y0 p0) (b0 : uIdx → μ.ord.ToType) (I : Set μ.ord.ToType)
    (y : μ.ord.ToType) (hI : #I ≤ ρ) (hb : #uIdx ≤ ρ)
    (hs0 : s0 = infra_78_seedStage ρ hℓel Xb Y0 p0 hp0 id b0 (infra_78_seedSet I b0 y)) :
    (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).IdLaw ∧
    (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).CompLaw ∧
    (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).ContAtLimits ∧
    (∀ k, infra_78_StageInv5 Xb (infra_78_rcObj Xb hℓel cand s0 e0 k)) ∧
    (∀ k u, (Sum.inr ((infra_78_rcObj Xb hℓel cand s0 e0 k).e.b u) : μ.ord.ToType ⊕ μ.ord.ToType) ∈
      (infra_78_rcObj Xb hℓel cand s0 e0 k).e.R) ∧
    (∀ i k, IsMin i → ∀ x ∈ I, (Sum.inl ((infra_78_rcMap Xb hℓel cand s0 e0 i k).1 x) :
      μ.ord.ToType ⊕ μ.ord.ToType) ∈ (infra_78_rcObj Xb hℓel cand s0 e0 k).e.R) ∧
    (∀ i, #(infra_78_rcSets hρκ Xb hℓel cand s0 e0 i) ≤ ρ) ∧
    (∀ {j i} (h : j < i), infra_78_bkStep (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) h ''
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 j ⊆ infra_78_rcSets hρκ Xb hℓel cand s0 e0 i) ∧
    (∀ i, Order.IsSuccLimit i → infra_78_rcSets hρκ Xb hℓel cand s0 e0 i =
      ⋃ j : Set.Iio i, infra_78_bkStep (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) j.2 ''
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 j.1) ∧
    (∀ i x, (Sum.inl x : infra_78_bkCarrier (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) i) ∈
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 i →
      (Sum.inr (((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).pair i).onVertex PUnit.unit x) :
        infra_78_bkCarrier (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) i) ∈
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 i) ∧
    (∀ i, ∃ y, y ∈ infra_78_Spart (infra_78_rcObj Xb hℓel cand s0 e0 i)) ∧
    (∀ i, (¬ Order.IsSuccLimit i ∨ ℓ < Order.cof (Set.Iio i)) →
      ∀ s ⊆ infra_78_rcSets hρκ Xb hℓel cand s0 e0 i, #s ≤ ℓ →
      infra_78_bkReq1 (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) hℓel i s
        (infra_78_rcSets hρκ Xb hℓel cand s0 e0 i)) ∧
    (∀ σ' : Cardinal.{u}, ℵ₀ ≤ σ' → μ ∈ recursionClosedLevels P σ' → Order.succ σ' ≤ μ → ℓ < μ →
      ∀ i, (¬ Order.IsSuccLimit i ∨ ℓ < Order.cof (Set.Iio i)) →
      ∀ s ⊆ infra_78_rcSets hρκ Xb hℓel cand s0 e0 i, #s ≤ ℓ →
      #(Sum.inr ⁻¹' s : Set ((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).Y i).model.carrier) ≤ σ' →
      ∃ seq : ApproximationSequence
          (infra_78_bkTuple (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) i s), seq.τ = ℓ ∧
        ℓ + ℵ₀ < #seq.κIndex ∧
        ∀ a b, (Sum.inl (((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).X i).val (seq.family a b)) :
          infra_78_bkCarrier (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) i) ∈
          infra_78_rcSets hρκ Xb hℓel cand s0 e0 i) := by
  have hℓ : ℵ₀ ≤ ℓ := P.aleph0_le hℓel
  have hρ : ℵ₀ ≤ ρ := hℓ.trans hℓρ.le
  have hsop := infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand
  have hseedc : #(infra_78_seedSet I b0 y) ≤ ρ := infra_78_seedSet_card hρ hI hb y
  have h5seed : infra_78_StageInv5 Xb s0 := by
    rw [hs0]; exact infra_78_seedStage_inv5 ρ hℓel Xb Y0 p0 hp0 b0 _
  have h0 : #s0.e.R ≤ ρ := by
    rw [hs0]; exact infra_78_seedStage_card ρ hℓel Xb Y0 p0 hp0 id b0 _ hseedc
  have hseed : infra_78_PairClosed ρ hℓel (infra_78_toArr s0.hp) trivial s0.e.R := by
    rw [hs0]; exact infra_78_seedStage_closed ρ hℓel Xb Y0 p0 hp0 id b0 _ hℓκ hℓρ hpow hseedc
  have hsub : infra_78_seedSet I b0 y ⊆ s0.e.R := by
    rw [hs0]; exact infra_78_seedStage_seeds ρ hℓel Xb Y0 p0 hp0 id b0 _
  have hS0 : ∃ y, (Sum.inr y : μ.ord.ToType ⊕ μ.ord.ToType) ∈ s0.e.R :=
    ⟨y, hsub (Or.inr ⟨y, Set.mem_insert _ _, rfl⟩)⟩
  have hb0 : s0.e.b = b0 := by rw [hs0]; rfl
  have h5 := infra_78_rc_inv5_all P σ hσ hμT hρκ Xb hℓel cand s0 e0 hidx hcof h5seed
  have hmin : ∀ i, IsMin i → infra_78_rcObj Xb hℓel cand s0 e0 i = s0 := fun i hi =>
    infra_78_pairMatrix_min s0 _ _ hi
  refine ⟨infra_78_pairMatrix_idLaw hρκ s0 _ _ hsop, infra_78_pairMatrix_compLaw hρκ s0 _ _ hsop,
    infra_78_pairMatrix_contAtLimits hρκ s0 _ _ hsop, h5, ?_, ?_,
    (fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩)
      (infra_78_rnext_closure P σ hσ hμT hρκ Xb hℓel cand s0 e0 hidx h5 hℓκ hℓρ hpow h0 hseed
        hS0)⟩
  · intro k u
    obtain ⟨i0, -, hi0⟩ := (wellFounded_lt (α := (Order.succ ρ).ord.ToType)).has_min Set.univ
      ⟨k, trivial⟩
    have hm : IsMin i0 := fun b _ => not_lt.1 (hi0 b trivial)
    have hik : i0 ≤ k := not_lt.1 (hi0 k trivial)
    have hmem : (Sum.inr (b0 u) : μ.ord.ToType ⊕ μ.ord.ToType) ∈
        (infra_78_rcObj Xb hℓel cand s0 e0 i0).e.R := by
      rw [hmin i0 hm]; exact hsub (Or.inr ⟨b0 u, Set.mem_insert_of_mem _ ⟨u, rfl⟩, rfl⟩)
    have hfw := infra_78_rc_forward hρκ Xb hℓel cand s0 e0 i0 k hik ⟨_, hmem, rfl⟩
    have hcoh := (infra_78_opMatrix_coherent hρκ Xb (infra_78_rcl ρ hℓel) cand s0 e0 i0 k hik).2
    have hb' : (infra_78_rcObj Xb hℓel cand s0 e0 i0).e.b = b0 := by rw [hmin i0 hm]; exact hb0
    rw [hcoh, hb']
    exact hfw
  · intro i k hi x hx
    have hik : i ≤ k := (le_total i k).elim id fun h => hi h
    have hmem : (Sum.inl x : μ.ord.ToType ⊕ μ.ord.ToType) ∈
        (infra_78_rcObj Xb hℓel cand s0 e0 i).e.R := by
      rw [hmin i hi]; exact hsub (Or.inl ⟨x, hx, rfl⟩)
    exact infra_78_rc_forward hρκ Xb hℓel cand s0 e0 i k hik ⟨_, hmem, rfl⟩

include hρκ in
/-- **Failing-list property at every stage** of the recursion matrix with the concrete update and
the `S`-part candidates: `infra_78_opMatrix_failing_list` with its hypotheses ((5) at the stage,
an `S`-list) discharged by `infra_78_rc_inv5_all` and `infra_78_rc_S_nonempty`. -/
theorem infra_78_rc_failing_list {cIdx : Type u} (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (hcof : ∀ δ : (Order.succ ρ).ord.ToType, Order.IsSuccLimit δ →
      #uIdx < (Ordinal.ToType.toOrd δ).1.cof)
    (s0 : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
    (e0 : Infra78MarkData μ uIdx) (h5seed : infra_78_StageInv5 Xb s0)
    (hS0 : ∃ y, (Sum.inr y : μ.ord.ToType ⊕ μ.ord.ToType) ∈ s0.e.R)
    {β k : (Order.succ ρ).ord.ToType} (hβ : β ⋖ k) :
    let c := infra_78_pcObj s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) (infra_78_candS cIdx)) (infra_78_limMarkE e0)
    let m := infra_78_pcMap s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) (infra_78_candS cIdx)) (infra_78_limMarkE e0)
    ∃ (hX : infra_78_IsArr (c β).X (c k).X (m β k).1),
      (∀ d : cIdx → μ.ord.ToType, Set.range d ⊆ infra_78_Spart (c β) →
        IsRelativelyIsolated (infra_78_markTuple (infra_78_toArr (c β).hp)
          (Sum.elim (infra_78_stageMark (c β)) (fun x => ⟨PUnit.unit, d x⟩)))
          (Equiv.refl (uIdx ⊕ cIdx))) ∨
      ∃ d : cIdx → μ.ord.ToType, Set.range d ⊆ infra_78_Spart (c β) ∧
        ¬ IsRelativelyIsolated (infra_78_markTuple (infra_78_toArr (c β).hp)
          (Sum.elim (infra_78_stageMark (c β)) (fun x => ⟨PUnit.unit, d x⟩)))
          (Equiv.refl (uIdx ⊕ cIdx)) ∧
        ¬ IsTiedFree (infra_78_toArr hX)
          ((infra_78_markTuple (infra_78_toArr (c k).hp)
            (fun x => (⟨PUnit.unit, (m β k).2 (Sum.elim (c β).e.b d x)⟩ :
              Occurrence K oneVertexShape (P.scheme.asSystem _ (c k).Y)))).restrict
            (infra_78_toArr hX) trivial)
          (infra_78_markTuple (infra_78_toArr (c k).hp)
            (fun x => (⟨PUnit.unit, (m β k).2 (Sum.elim (c β).e.b d x)⟩ :
              Occurrence K oneVertexShape (P.scheme.asSystem _ (c k).Y)))) (Equiv.refl _) := by
  obtain ⟨x, hx⟩ := infra_78_rc_S_nonempty hρκ Xb hℓel (infra_78_candS cIdx) s0 e0 hS0 β
  exact infra_78_opMatrix_failing_list P σ hσ hμT hρκ Xb (infra_78_rcl ρ hℓel) hidx s0 e0 hβ
    (infra_78_rc_inv5_all P σ hσ hμT hρκ Xb hℓel (infra_78_candS cIdx) s0 e0 hidx hcof h5seed β)
    (infra_78_exists_Slist _ hx)

end Inv5All
end AEC
