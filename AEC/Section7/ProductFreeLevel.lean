module

public import AEC.Section7.TiedListChain

/-!
# Proposition 7.5(3), actual-coupling level form (statement)

English Proposition 7.5(3): "In an actual coupling, if a bounded tuple `x` has product with `b`
over `X`, then `tp(x/Y)` is free from `X`" (for `Y` all-dominated over `X + b`).

`infra_75_product_free_level_statement` is the narrowed form used by Lemma 7.11's successor
step: the coupling is actual (`x.ν = μ`), so `x`, the copy of `b` and their joint are all
hosted at the level `μ` of `X`, and the 6.12 product facts needed are exactly the proved
level-joint cases (`infra_612_tied_symm_level_joints`, `infra_612_tied_finite_proj_level`,
`infra_612_tied_base_change_level_joints`). The general clause (any bounded `x`, any host
level) stays tracked as `infra_75_product_free`.
-/

@[expose] public section

namespace AEC
noncomputable section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}

/-- The marks `b ⊆ Y`, read as a tuple over `X` hosted with `x`. -/
def infra_75_markOver {X Y : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (x : TupleOver K oneVertexShape P.scheme hμ Y) {bIdx : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)) :
    TupleOver K oneVertexShape P.scheme hμ X where
  ν := x.ν
  hν := x.hν
  host := x.host
  incl := SystemArrow.comp f x.incl
  incl_arrow := P.scheme.comp f x.incl hf x.incl_arrow
  idx := bIdx
  val := fun k => x.incl.mapOcc (b k)

/-- The joint `(x, b)` over `X`. -/
def infra_75_jointOver {X Y : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (x : TupleOver K oneVertexShape P.scheme hμ Y) {bIdx : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)) :
    TupleOver K oneVertexShape P.scheme hμ X where
  ν := x.ν
  hν := x.hν
  host := x.host
  incl := SystemArrow.comp f x.incl
  incl_arrow := P.scheme.comp f x.incl hf x.incl_arrow
  idx := x.idx ⊕ bIdx
  val := fun
    | Sum.inl k => x.val k
    | Sum.inr k => x.incl.mapOcc (b k)

/-- The arity `σ + (g(σ) + LS(K))`: bounded tests of size `≤ g(σ) + LS(K)` together with the
marks. The level form of 7.5(3) is stated at levels closed at this arity as well (the paper's
"sufficiently closed eligible level"), since its symmetry step runs on `(b, c)`. -/
def infra_75_wide (P : SingleModelData K) (σ : Cardinal.{u}) : Cardinal.{u} :=
  σ + (P.g σ + ls K)

/-- **Proposition 7.5(3), actual coupling, level joints (statement; open tip
`infra_75_product_free_level`).** -/
def infra_75_product_free_level_statement (P : SingleModelData K) : Prop :=
  ∀ (σ : Cardinal.{u}), ℵ₀ ≤ σ → ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible),
    μ ∈ recursionClosedLevels P σ → Order.succ σ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P σ) → Order.succ (infra_75_wide P σ) ≤ μ →
    ∀ (X Y : P.scheme.Object μ hμ)
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
      (hf : P.scheme.permitted (X := X) (Y := Y) f)
      (bIdx : Type u) (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      #bIdx ≤ σ → AllDominated f hf bIdx b →
      ∀ x : TupleOver K oneVertexShape P.scheme hμ Y, x.ν = μ → #x.idx ≤ σ →
        IsProductTied (x.restrict f hf) (infra_75_markOver f hf x b)
          (infra_75_jointOver f hf x b) (Equiv.refl _) →
        IsTiedFree f (x.restrict f hf) x (Equiv.refl _)

set_option maxHeartbeats 1600000 in
/-- **Testing theorem for tied freeness.** If `q` over `B` agrees with the tied free lift `qB`
of `q ↾ A` on every bounded test `Z ⊆ B` of size `≤ g(σ) + LS(K)`, then `q` is tied-free from
`A` (Theorem 6.6 testing via `infra_73_differing_test`, then the free lift's answers carried to
`q`, as in `infra_78_tiedFree_of_upTo`). -/
theorem infra_75_tiedFree_of_tests
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ)
    (htest : ∀ (qB : TupleOver K oneVertexShape P.scheme hμ B)
      (eB : (q.restrict f hf).idx ≃ qB.idx), qB.ν = μ →
      IsTiedFree f (q.restrict f hf) qB eB →
      ∀ (β : Type u) (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #β ≤ P.g σ + ls K →
        P.scheme.DiagramEq (X := qB.host) (Y := q.host)
          (infra_612_anchored eB qB.incl qB.val Z)
          (infra_612_anchored (Equiv.refl q.idx) q.incl q.val Z)) :
    IsTiedFree f (q.restrict f hf) q (Equiv.refl _) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hidxμ : #q.idx < μ := hidx.trans_lt hσlt
  obtain ⟨qB, eB, hBν, -, hTB⟩ :=
    infra_610_tied_free_lift P σ hσ hμ hrec hσμ f hf (q.restrict f hf) hqν hidx
  have hidxB : #qB.idx ≤ σ := by rw [← Cardinal.mk_congr eB]; exact hidx
  have hS : SameGaloisType qB q eB.symm (Equiv.refl q.idx).symm := by
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ :=
      infra_73_differing_test P σ hσ hμ hrec hσμ qB q eB.symm (Equiv.refl q.idx).symm hBν hqν
        hidxB (hidxB.trans_lt hσlt) hneq
    apply hnot
    have d := htest qB eB hBν hTB β Y hβ
    exact infra_73_diagramEq_of_eq d (fun t => by cases t <;> rfl)
      (fun t => by cases t <;> rfl)
  intro seq' ι Z Z0' hlong' hι' hιμ hmv
  have dL := hTB seq' Z Z0' hlong' hι' hιμ hmv
  have dS := infra_72_diagramEq_of_sameGalois (P := P) hS Z hBν hqν hidxμ hιμ
  have dS' : P.scheme.DiagramEq (X := qB.host) (Y := q.host)
      (infra_612_anchored eB qB.incl qB.val Z)
      (infra_612_anchored (Equiv.refl q.idx) q.incl q.val Z) :=
    infra_73_diagramEq_of_eq dS (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  exact P.scheme.diagram_trans q.host qB.host q.host _ _ _ dL dS'

/-- **Prop 7.5(3), level form: free evaluation on bounded tests (statement; open tip
`infra_75_free_eval_level`).** Under the hypotheses of `infra_75_product_free_level_statement`,
`x` agrees with every tied free lift of `x ↾ X` on every bounded test `Z ⊆ Y` of size at most
the testing arity: the paper's "symmetry and projection give the free evaluation of `x` on
every bounded test `c` from `Y`". -/
def infra_75_free_eval_level_statement (P : SingleModelData K) : Prop :=
  ∀ (σ : Cardinal.{u}), ℵ₀ ≤ σ → ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible),
    μ ∈ recursionClosedLevels P σ → Order.succ σ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P σ) → Order.succ (infra_75_wide P σ) ≤ μ →
    ∀ (X Y : P.scheme.Object μ hμ)
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
      (hf : P.scheme.permitted (X := X) (Y := Y) f)
      (bIdx : Type u) (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      #bIdx ≤ σ → AllDominated f hf bIdx b →
      ∀ x : TupleOver K oneVertexShape P.scheme hμ Y, x.ν = μ → #x.idx ≤ σ →
        IsProductTied (x.restrict f hf) (infra_75_markOver f hf x b)
          (infra_75_jointOver f hf x b) (Equiv.refl _) →
        ∀ (qB : TupleOver K oneVertexShape P.scheme hμ Y)
          (eB : (x.restrict f hf).idx ≃ qB.idx), qB.ν = μ →
          IsTiedFree f (x.restrict f hf) qB eB →
          ∀ (β : Type u) (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
            #β ≤ P.g σ + ls K →
            P.scheme.DiagramEq (X := qB.host) (Y := x.host)
              (infra_612_anchored eB qB.incl qB.val Z)
              (infra_612_anchored (Equiv.refl x.idx) x.incl x.val Z)

/-- **Prop 7.5(3), level form, from free evaluation on bounded tests** (testing theorem). -/
theorem infra_75_product_free_level_of_eval (P : SingleModelData K)
    (h : infra_75_free_eval_level_statement P) : infra_75_product_free_level_statement P :=
  fun σ hσ _ hμ hrec hσμ hrw hσw X Y f hf bIdx b hb hdom x hxν hxσ hprod =>
    infra_75_tiedFree_of_tests P σ hσ hμ hrec hσμ f hf x hxν hxσ
      (h σ hσ hμ hrec hσμ hrw hσw X Y f hf bIdx b hb hdom x hxν hxσ hprod)

/-- The marks `b` together with a test `Z ⊆ Y`, read over `X` hosted with `x`. -/
def infra_75_markTestOver {X Y : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (x : TupleOver K oneVertexShape P.scheme hμ Y) {bIdx β : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)) :
    TupleOver K oneVertexShape P.scheme hμ X :=
  infra_75_markOver f hf x (Sum.elim b Z)

/-- The joint `(x, b, Z)` over `X`. -/
def infra_75_jointTestOver {X Y : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (x : TupleOver K oneVertexShape P.scheme hμ Y) {bIdx β : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)) :
    TupleOver K oneVertexShape P.scheme hμ X :=
  infra_75_jointOver f hf x (Sum.elim b Z)

/-- The common hypotheses of the level form of Proposition 7.5(3), with a conclusion `C`. -/
def infra_75_levelHyps (P : SingleModelData K)
    (C : ∀ (_σ : Cardinal.{u}) (μ : Cardinal.{u}) (hμ : μ ∈ P.eligible)
      (X Y : P.scheme.Object μ hμ)
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
      (_hf : P.scheme.permitted (X := X) (Y := Y) f)
      (bIdx : Type u) (_b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
      (_x : TupleOver K oneVertexShape P.scheme hμ Y), Prop) : Prop :=
  ∀ (σ : Cardinal.{u}), ℵ₀ ≤ σ → ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible),
    μ ∈ recursionClosedLevels P σ → Order.succ σ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P σ) → Order.succ (infra_75_wide P σ) ≤ μ →
    ∀ (X Y : P.scheme.Object μ hμ)
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
      (hf : P.scheme.permitted (X := X) (Y := Y) f)
      (bIdx : Type u) (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      #bIdx ≤ σ → AllDominated f hf bIdx b →
      ∀ x : TupleOver K oneVertexShape P.scheme hμ Y, x.ν = μ → #x.idx ≤ σ →
        IsProductTied (x.restrict f hf) (infra_75_markOver f hf x b)
          (infra_75_jointOver f hf x b) (Equiv.refl _) →
        C σ μ hμ X Y f hf bIdx b x

/-- **Step (i)–(iii) of 7.5(3) (statement; open tip `infra_75_eval_product`).** `x` has the
tied product over `X` with `(b, Z)` for every bounded test `Z ⊆ Y` (paper: "Hence `x` and
`(b, c)` have product over `X`"). -/
def infra_75_eval_product_statement (P : SingleModelData K) : Prop :=
  infra_75_levelHyps P fun σ _ hμ' _ Y f hf _ b x =>
    ∀ (β : Type u) (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ' Y)),
      #β ≤ P.g σ + ls K →
      IsProductTied (x.restrict f hf) (infra_75_markTestOver f hf x b Z)
        (infra_75_jointTestOver f hf x b Z) (Equiv.refl _)

/-- **Step (iv) of 7.5(3) (statement; open tip `infra_75_eval_project`).** From the products
with every `(b, Z)`, symmetry and projection give the free evaluation of `x` on every bounded
test `Z ⊆ Y`. -/
def infra_75_eval_project_statement (P : SingleModelData K) : Prop :=
  infra_75_levelHyps P fun σ μ' hμ' _ Y f hf _ b x =>
    (∀ (β : Type u) (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ' Y)),
      #β ≤ P.g σ + ls K →
      IsProductTied (x.restrict f hf) (infra_75_markTestOver f hf x b Z)
        (infra_75_jointTestOver f hf x b Z) (Equiv.refl _)) →
    ∀ (qB : TupleOver K oneVertexShape P.scheme hμ' Y)
      (eB : (x.restrict f hf).idx ≃ qB.idx), qB.ν = μ' →
      IsTiedFree f (x.restrict f hf) qB eB →
      ∀ (β : Type u) (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ' Y)),
        #β ≤ P.g σ + ls K →
        P.scheme.DiagramEq (X := qB.host) (Y := x.host)
          (infra_612_anchored eB qB.incl qB.val Z)
          (infra_612_anchored (Equiv.refl x.idx) x.incl x.val Z)

set_option maxHeartbeats 3200000 in
/-- **Free evaluation from one product (proved).** If `x` has the tied product over `X` with
marks `c ⊆ Y` (level joints), then on every sublist of `c` `x` answers as any tied free lift of
`x ↾ X`. Symmetry of the level-joint product (`infra_612_tied_symm_level_joints`, at the wider
arity `σ'`) makes `x` the free side; the free lift `y` of `x ↾ X` into the host of `x` and the
given lift `qB` answer the test alike on one sequence-move (`infra_78_move_query_mixed`); the
sublist is read off by restriction (`infra_73_scheme_comp`), so no projection lemma is needed. -/
theorem infra_75_eval_one
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    (σ' : Cardinal.{u}) (hσσ' : σ ≤ σ')
    (hrec' : μ ∈ recursionClosedLevels P σ') (hσμ' : Order.succ σ' ≤ μ)
    {X Y : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (x : TupleOver K oneVertexShape P.scheme hμ Y) (hxν : x.ν = μ) (hxσ : #x.idx ≤ σ)
    {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (hcσ : #cIdx ≤ σ')
    (hprod : IsProductTied (x.restrict f hf) (infra_75_markOver f hf x c)
      (infra_75_jointOver f hf x c) (Equiv.refl _))
    (qB : TupleOver K oneVertexShape P.scheme hμ Y)
    (eB : (x.restrict f hf).idx ≃ qB.idx)
    (hqB : IsTiedFree f (x.restrict f hf) qB eB)
    {β : Type u} (ι : β → cIdx) (hβ : #β ≤ σ') :
    P.scheme.DiagramEq (X := qB.host) (Y := x.host)
      (infra_612_anchored eB qB.incl qB.val (fun d => c (ι d)))
      (infra_612_anchored (Equiv.refl x.idx) x.incl x.val (fun d => c (ι d))) := by
  classical
  rcases x with ⟨ν, hν, H, xi, hxi, idx, val⟩
  simp only at hxν
  subst hxν
  have hσ' : ℵ₀ ≤ σ' := hσ.trans hσσ'
  have hσlt' : σ' < ν := (Order.lt_succ σ').trans_le hσμ'
  have hβμ : #β < ν := hβ.trans_lt hσlt'
  let x : TupleOver K oneVertexShape P.scheme hμ Y := ⟨ν, hν, H, xi, hxi, idx, val⟩
  let q := x.restrict f hf
  let pc := infra_75_markOver f hf x c
  -- tied free lift of `x ↾ X` into the host of `x`
  obtain ⟨y, ey, hyν, -, hyT⟩ :=
    infra_610_tied_free_lift P σ' hσ' hμ hrec' hσμ' (B := H) pc.incl pc.incl_arrow q rfl
      (hxσ.trans hσσ')
  have hprod2 : IsProductTied pc q (pc.join y) (Equiv.sumCongr (Equiv.refl _) ey) := by
    refine ⟨pc, Equiv.refl _, SameGaloisType.refl pc, y, ey, hyT, ?_⟩
    have h : (Equiv.sumCongr (Equiv.refl pc.idx) ey).symm.trans
        (Equiv.sumCongr (Equiv.refl pc.idx) ey) = Equiv.refl (pc.idx ⊕ y.idx) :=
      Equiv.symm_trans_self _
    exact h ▸ SameGaloisType.refl (pc.join y)
  have S := infra_612_tied_symm_level_joints P σ' hσ' hμ hrec' hσμ' q pc rfl rfl
    (hxσ.trans hσσ') hcσ (infra_75_jointOver f hf x c) (pc.join y) (Equiv.refl _)
    (Equiv.sumCongr (Equiv.refl _) ey) hprod hprod2 rfl hyν
  have hιc : #(idx ⊕ cIdx) ≤ σ' := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hσ' (hxσ.trans hσσ') hcσ
  have hιE : #((idx ⊕ cIdx) ⊕ PEmpty.{u + 1}) < ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_eq_zero PEmpty.{u + 1}, add_zero]
    exact hιc.trans_lt hσlt'
  have D := infra_78_diagramEq_of_sameGalois S
    (fun e : PEmpty.{u + 1} => e.elim) hιE (by change _ < y.ν; rw [hyν]; exact hιE)
  let ρ : idx ⊕ β → (idx ⊕ cIdx) ⊕ PEmpty.{u + 1}
    | Sum.inl k => Sum.inl (Sum.inl k)
    | Sum.inr d => Sum.inl (Sum.inr (ι d))
  have D' := infra_73_scheme_comp D ρ
  let Z' : β → Occurrence K oneVertexShape (P.scheme.asSystem hν H) :=
    fun d => xi.mapOcc (c (ι d))
  have Dx : P.scheme.DiagramEq (X := H) (Y := y.host)
      (infra_612_anchored (Equiv.refl idx) xi val (fun d => c (ι d)))
      (infra_612_anchored ey y.incl y.val Z') :=
    infra_73_diagramEq_of_eq D' (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  -- a long sequence for `x ↾ X` and a move of the test
  obtain ⟨seq, hτlo, -, hlong⟩ :=
    infra_78_exists_seq_ge P σ hσ hμ hrec hσμ q rfl hxσ hβμ
  obtain ⟨Z0, hZ0⟩ := infra_78_move_query_mixed f hf le_rfl seq (fun d => c (ι d)) hβμ
  have TqB := hqB seq (fun d => c (ι d)) Z0 hlong hτlo hβμ hZ0
  have hmv : infra_78_isMoveMixed pc.incl seq Z' Z0 := by
    intro i
    have hα : #(idx ⊕ β) < ν := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) ((hxσ.trans hσσ').trans_lt hσlt') hβμ
    have hp := P.scheme.diagram_preserved Y H xi hxi
      (seqJoint (fun j => (⟨(seq.family i j).1,
        f.onVertex (seq.family i j).1 (seq.family i j).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))) (fun d => c (ι d))) hα hα
    exact P.scheme.diagram_trans _ _ _ _ _ _ (hZ0 i)
      (infra_73_diagramEq_of_eq hp (fun t => rfl) (fun t => by cases t <;> rfl))
  have Ty := hyT seq Z' Z0 hlong hτlo hβμ hmv
  exact P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ TqB)
    (P.scheme.diagram_trans _ _ _ _ _ _ Ty (P.scheme.diagram_symm _ _ _ _ Dx))

/-- **Step (iv) of 7.5(3) (proved).** -/
theorem infra_75_eval_project (P : SingleModelData K) : infra_75_eval_project_statement P := by
  intro σ hσ μ hμ hrec hσμ hrw hσw X Y f hf bIdx b hb _ x hxν hxσ _ hall qB eB _ hT β Z hβ
  have hσw' : σ ≤ infra_75_wide P σ := le_self_add
  have hc : #(bIdx ⊕ β) ≤ infra_75_wide P σ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact add_le_add hb hβ
  have hβw : #β ≤ infra_75_wide P σ := hβ.trans le_add_self
  exact infra_75_eval_one P σ hσ hμ hrec hσμ (infra_75_wide P σ) hσw' hrw hσw f hf x hxν hxσ
    (Sum.elim b Z) hc (hall β Z hβ) qB eB hT Sum.inr hβw

/-- **Free evaluation from its two steps** (`infra_75_free_eval_level` split, glue). -/
theorem infra_75_free_eval_of_parts (P : SingleModelData K)
    (h1 : infra_75_eval_product_statement P) (h2 : infra_75_eval_project_statement P) :
    infra_75_free_eval_level_statement P :=
  fun σ hσ _ hμ hrec hσμ hrw hσw X Y f hf bIdx b hb hdom x hxν hxσ hprod qB eB hqB hT β Z hβ =>
    h2 σ hσ hμ hrec hσμ hrw hσw X Y f hf bIdx b hb hdom x hxν hxσ hprod
      (h1 σ hσ hμ hrec hσμ hrw hσw X Y f hf bIdx b hb hdom x hxν hxσ hprod) qB eB hqB hT β Z hβ

end
end AEC
