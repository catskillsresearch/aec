module

public import AEC.Section7.TiedLocalCharacter

@[expose] public section

/-!
# Proposition 6.12 (products of bounded types, tied form)

English Proposition 6.12 with "realize `q^B`" read as the tied free lift (`IsTiedFreeMixed`;
the untied `IsFreeLift` is vacuous, `AEC/Audit/FreeFromVacuous.lean`). It lives here, not in
`AEC/Section6/Results.lean`, because the tied infrastructure is in Section 7, which imports
`AEC.Section6.Results`.

* `IsProductTied p q joint e`: `joint` is the type over `A` of `(x, y)` where `x` realizes `p`
  (in an extension at any eligible level) and `y` realizes the tied free lift of `q` to the host
  of `x` (so the definition covers the English "across eligible levels").
* `IsFiniteProductTied n b joint E`: the iterated product, with an explicit identification `E`
  of the coordinates `Σ i, (b i).idx` with those of `joint`.

Status: existence is proved (`infra_612_tied_exists`); independence is proved when the two
joints sit at the level of `A`, with realizations and free lifts at any levels
(`infra_612_tied_indep_level_joints`), and for joints at any levels it is proved for their
`μ`-level copies (`infra_612_tied_indep_copies`). Passing back from the copies to the joints
needs Galois-type transitivity through a `μ`-level middle (open `infra_612_galois_trans_cross_level`).
Independence across levels (full clause 2), symmetry,
associativity, permutation invariance, projections, and base change are the open sub-tips
`infra_612_tied_independence`, `infra_612_tied_symmetry`, `infra_612_tied_assoc`,
`infra_612_tied_finite`, `infra_612_tied_base_change`.
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- **Product of types (tied).** `joint` is `p ⊗ q`: the type over `A` of a realization `x`
of `p` followed by a tied free lift `y` of `q` to the host of `x`. -/
def IsProductTied {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    (p q joint : TupleOver K oneVertexShape P.scheme hμ A) (e : p.idx ⊕ q.idx ≃ joint.idx) :
    Prop :=
  ∃ (x : TupleOver K oneVertexShape P.scheme hμ A) (ex : p.idx ≃ x.idx),
    SameGaloisType p x ex (Equiv.refl x.idx) ∧
    ∃ (y : TupleOver K oneVertexShape P.scheme x.hν x.host) (ey : q.idx ≃ y.idx),
      IsTiedFreeMixed x.incl q y ey ∧
      SameGaloisType joint (x.join y)
        (e.symm.trans (Equiv.sumCongr ex ey)) (Equiv.refl (x.idx ⊕ y.idx))

/-- **Finite products (tied).** `joint` is `b 0 ⊗ ⋯ ⊗ b (n-1)` (left-bracketed), with `E`
identifying the coordinates `Σ i, (b i).idx` with those of `joint`. -/
def IsFiniteProductTied {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} :
    (n : ℕ) → (b : Fin n → TupleOver K oneVertexShape P.scheme hμ A) →
    (joint : TupleOver K oneVertexShape P.scheme hμ A) →
    ((Σ i, (b i).idx) ≃ joint.idx) → Prop
  | 0, _, joint, _ => IsEmpty joint.idx
  | n + 1, b, joint, E =>
      ∃ (left : TupleOver K oneVertexShape P.scheme hμ A)
        (El : (Σ i : Fin n, (b i.castSucc).idx) ≃ left.idx),
        IsFiniteProductTied n (fun i => b i.castSucc) left El ∧
        ∃ e : left.idx ⊕ (b (Fin.last n)).idx ≃ joint.idx,
          IsProductTied left (b (Fin.last n)) joint e ∧
          (∀ (i : Fin n) (k : (b i.castSucc).idx), E ⟨i.castSucc, k⟩ = e (Sum.inl (El ⟨i, k⟩))) ∧
          (∀ k : (b (Fin.last n)).idx, E ⟨Fin.last n, k⟩ = e (Sum.inr k))

/-- Existence of the tied product, with the realization given by a host at level `μ`. -/
theorem infra_612_tied_exists_aux
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    {ν : Cardinal.{u}} (hνμ : ν = μ) (hν : ν ∈ P.eligible)
    (host : P.scheme.Object ν hν)
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hν host))
    (hincl : P.scheme.permitted (X := A) (Y := host) incl)
    (idx : Type u) (val : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν host))
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνq : q.ν = μ) (hqσ : #q.idx ≤ σ) :
    ∃ joint : TupleOver K oneVertexShape P.scheme hμ A,
      ∃ e : idx ⊕ q.idx ≃ joint.idx,
        IsProductTied (⟨ν, hν, host, incl, hincl, idx, val⟩ :
          TupleOver K oneVertexShape P.scheme hμ A) q joint e := by
  subst hνμ
  let x : TupleOver K oneVertexShape P.scheme hν A := ⟨ν, hν, host, incl, hincl, idx, val⟩
  obtain ⟨y, ey, -, -, hT⟩ :=
    infra_610_tied_free_lift P σ hσ hν hrec hσμ incl hincl q hνq hqσ
  refine ⟨x.join y, Equiv.sumCongr (Equiv.refl idx) ey, x, Equiv.refl _,
    SameGaloisType.refl x, y, ey, hT, ?_⟩
  have h : (Equiv.sumCongr (Equiv.refl idx) ey).symm.trans
      (Equiv.sumCongr (Equiv.refl idx) ey) = Equiv.refl (idx ⊕ y.idx) :=
    Equiv.symm_trans_self _
  exact h ▸ SameGaloisType.refl (x.join y)

/-- **Existence of `p ⊗ q` (tied, proved).** -/
theorem infra_612_tied_exists
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hqσ : #q.idx ≤ σ) :
    ∃ joint : TupleOver K oneVertexShape P.scheme hμ A,
      ∃ e : p.idx ⊕ q.idx ≃ joint.idx, IsProductTied p q joint e :=
  infra_612_tied_exists_aux P σ hσ hμ hrec hσμ hνp p.hν p.host p.incl p.incl_arrow
    p.idx p.val q hνq hqσ

/-- Reindexing both sides of a Galois identification along one equivalence. -/
theorem infra_612_sameGalois_trans_equiv {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hμ A} {ι ι' : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι} (h : SameGaloisType t1 t2 e1 e2) (g : ι ≃ ι') :
    SameGaloisType t1 t2 (e1.trans g) (e2.trans g) := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
  exact ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun i => hv (g.symm i)⟩

/-- Transport a diagram equality along a reindexing with pointwise identification. -/
theorem infra_612_dEq_transport {P : SingleModelData K} {μ ν : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {X : P.scheme.Object μ hμ} {Y : P.scheme.Object ν hν} {α β : Type u}
    {xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ X)}
    {ys : α → Occurrence K oneVertexShape (P.scheme.asSystem hν Y)}
    (h : P.scheme.DiagramEq (X := X) (Y := Y) xs ys) (π : β ≃ α)
    {xs' : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ X)}
    {ys' : β → Occurrence K oneVertexShape (P.scheme.asSystem hν Y)}
    (hx : ∀ b, xs' b = xs (π b)) (hy : ∀ b, ys' b = ys (π b)) :
    P.scheme.DiagramEq (X := X) (Y := Y) xs' ys' := by
  have h2 := (P.scheme.diagram_reindex X Y π.symm xs ys).mp h
  exact infra_73_diagramEq_of_eq h2 (fun b => (hx b).symm) (fun b => (hy b).symm)

/-- `a ⊕ (b ⊕ c) ≃ b ⊕ (a ⊕ c)`. -/
def infra_612_swap3 (a b c : Type u) : a ⊕ (b ⊕ c) ≃ b ⊕ (a ⊕ c) where
  toFun
    | Sum.inl x => Sum.inr (Sum.inl x)
    | Sum.inr (Sum.inl y) => Sum.inl y
    | Sum.inr (Sum.inr z) => Sum.inr (Sum.inr z)
  invFun
    | Sum.inl y => Sum.inr (Sum.inl y)
    | Sum.inr (Sum.inl x) => Sum.inl x
    | Sum.inr (Sum.inr z) => Sum.inr (Sum.inr z)
  left_inv := by rintro (x | y | z) <;> rfl
  right_inv := by rintro (y | x | z) <;> rfl

/-- `(a ⊕ b) ⊕ c ≃ b ⊕ (a ⊕ c)`. -/
def infra_612_swap3' (a b c : Type u) : (a ⊕ b) ⊕ c ≃ b ⊕ (a ⊕ c) where
  toFun
    | Sum.inl (Sum.inl x) => Sum.inr (Sum.inl x)
    | Sum.inl (Sum.inr y) => Sum.inl y
    | Sum.inr z => Sum.inr (Sum.inr z)
  invFun
    | Sum.inl y => Sum.inl (Sum.inr y)
    | Sum.inr (Sum.inl x) => Sum.inl (Sum.inl x)
    | Sum.inr (Sum.inr z) => Sum.inr z
  left_inv := by rintro ((x | y) | z) <;> rfl
  right_inv := by rintro (y | x | z) <;> rfl

set_option maxHeartbeats 1600000 in
/-- **Independence of `p ⊗ q`, single level (proved).** Two tied products of `p` and `q`
whose realizations, free lifts and joints all sit at the level `μ` of `A` have one Galois type.

For a test list `Y` in `A`, take a long sequence for `q` and a move `Z₀` of `(x₁, Y)` along
`x₁`; since `x₁` and `x₂` both realize `p`, `Z₀` is also a move of `(x₂, Y)` along `x₂`
(`infra_72_diagramEq_of_sameGalois` on the parameter list `seq_i ⌢ Y`). Tied freeness gives
both `(y_k, x_k, Y)` the type of `q` on `Z₀`; Theorem 6.6 (`infra_73_differing_test`) closes. -/
theorem infra_612_tied_indep_same_level
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (j₁ j₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : p.idx ⊕ q.idx ≃ j₂.idx)
    (x₁ x₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (ex₁ : p.idx ≃ x₁.idx) (ex₂ : p.idx ≃ x₂.idx)
    (hS₁ : SameGaloisType p x₁ ex₁ (Equiv.refl x₁.idx))
    (hS₂ : SameGaloisType p x₂ ex₂ (Equiv.refl x₂.idx))
    (y₁ : TupleOver K oneVertexShape P.scheme x₁.hν x₁.host)
    (y₂ : TupleOver K oneVertexShape P.scheme x₂.hν x₂.host)
    (ey₁ : q.idx ≃ y₁.idx) (ey₂ : q.idx ≃ y₂.idx)
    (hT₁ : IsTiedFreeMixed x₁.incl q y₁ ey₁) (hT₂ : IsTiedFreeMixed x₂.incl q y₂ ey₂)
    (hJ₁ : SameGaloisType j₁ (x₁.join y₁)
      (e₁.symm.trans (Equiv.sumCongr ex₁ ey₁)) (Equiv.refl (x₁.idx ⊕ y₁.idx)))
    (hJ₂ : SameGaloisType j₂ (x₂.join y₂)
      (e₂.symm.trans (Equiv.sumCongr ex₂ ey₂)) (Equiv.refl (x₂.idx ⊕ y₂.idx)))
    (hx₁ : x₁.ν = μ) (hx₂ : x₂.ν = μ) (hy₁ : y₁.ν = μ) (hy₂ : y₂.ν = μ)
    (hj₁ : j₁.ν = μ) (hj₂ : j₂.ν = μ) :
    SameGaloisType j₁ j₂ e₁.symm e₂.symm := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hpμ : #p.idx < μ := hpσ.trans_lt hσlt
  have hqμ : #q.idx < μ := hqσ.trans_lt hσlt
  have hpqσ : #(p.idx ⊕ q.idx) ≤ σ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hσ hpσ hqσ
  have hj₁σ : #j₁.idx ≤ σ := (Cardinal.mk_congr e₁).symm.trans_le hpqσ
  -- the realizations, reindexed by `p`
  have hS'₁ : SameGaloisType p x₁ (Equiv.refl p.idx) ex₁.symm := by
    have h := infra_612_sameGalois_trans_equiv hS₁ ex₁.symm
    rwa [Equiv.self_trans_symm, Equiv.refl_trans] at h
  have hS'₂ : SameGaloisType p x₂ (Equiv.refl p.idx) ex₂.symm := by
    have h := infra_612_sameGalois_trans_equiv hS₂ ex₂.symm
    rwa [Equiv.self_trans_symm, Equiv.refl_trans] at h
  have hJ'₁ : SameGaloisType j₁ (x₁.join y₁) e₁.symm (Equiv.sumCongr ex₁ ey₁).symm := by
    have h := infra_612_sameGalois_trans_equiv hJ₁ (Equiv.sumCongr ex₁ ey₁).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  have hJ'₂ : SameGaloisType j₂ (x₂.join y₂) e₂.symm (Equiv.sumCongr ex₂ ey₂).symm := by
    have h := infra_612_sameGalois_trans_equiv hJ₂ (Equiv.sumCongr ex₂ ey₂).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ :=
    infra_73_differing_test P σ hσ hμ hrec hσμ j₁ j₂ e₁.symm e₂.symm hj₁ hj₂ hj₁σ
      (hj₁σ.trans_lt hσlt) hneq
  apply hnot
  have hβμ : #β < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    exact hβ.trans_lt (add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ))
  have hpβμ : #(p.idx ⊕ β) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hpμ hβμ
  have hqβμ : #(q.idx ⊕ β) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hqμ hβμ
  obtain ⟨seq, hτlo, -, hlong⟩ :=
    infra_78_exists_seq_ge P σ hσ hμ hrec hσμ q hνq hqσ hpβμ
  let W₁ : p.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem x₁.hν x₁.host) :=
    fun t => typeJoint (p := x₁) Y (Equiv.sumCongr ex₁ (Equiv.refl β) t)
  let W₂ : p.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem x₂.hν x₂.host) :=
    fun t => typeJoint (p := x₂) Y (Equiv.sumCongr ex₂ (Equiv.refl β) t)
  obtain ⟨Z0, hZ0⟩ := infra_78_move_query_mixed x₁.incl x₁.incl_arrow hx₁.ge seq W₁ hpβμ
  -- `Z₀` is also a move of `W₂` along `x₂`
  have hmove₂ : infra_78_isMoveMixed x₂.incl seq W₂ Z0 := by
    intro i
    let Z' : q.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
      Sum.elim (seq.family i) Y
    have D₁ := infra_72_diagramEq_of_sameGalois (P := P) hS'₁ Z' hνp hx₁ hpμ hqβμ
    have D₂ := infra_72_diagramEq_of_sameGalois (P := P) hS'₂ Z' hνp hx₂ hpμ hqβμ
    have M := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ D₁) D₂
    have M' := infra_612_dEq_transport M (infra_612_swap3 q.idx p.idx β)
      (xs' := seqJoint (fun j => (⟨(seq.family i j).1,
        x₁.incl.onVertex (seq.family i j).1 (seq.family i j).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem x₁.hν x₁.host))) W₁)
      (ys' := seqJoint (fun j => (⟨(seq.family i j).1,
        x₂.incl.onVertex (seq.family i j).1 (seq.family i j).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem x₂.hν x₂.host))) W₂)
      (by rintro (j | k | b) <;> rfl) (by rintro (j | k | b) <;> rfl)
    exact P.scheme.diagram_trans _ _ _ _ _ _ (hZ0 i) M'
  have hιτ : #(p.idx ⊕ β) ≤ seq.τ := hτlo
  have T₁ := hT₁ seq W₁ Z0 hlong hιτ hpβμ hZ0
  have T₂ := hT₂ seq W₂ Z0 hlong hιτ hpβμ hmove₂
  have N := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ T₁) T₂
  have G := infra_612_dEq_transport N (infra_612_swap3' p.idx q.idx β)
    (xs' := alignJoint (Equiv.sumCongr ex₁ ey₁).symm (typeJoint (p := x₁.join y₁) Y))
    (ys' := alignJoint (Equiv.sumCongr ex₂ ey₂).symm (typeJoint (p := x₂.join y₂) Y))
    (by rintro ((k | j) | b) <;> rfl) (by rintro ((k | j) | b) <;> rfl)
  have hpqμ : #(p.idx ⊕ q.idx) < μ := hpqσ.trans_lt hσlt
  have DJ₁ := infra_72_diagramEq_of_sameGalois (P := P) hJ'₁ Y hj₁ hy₁ hpqμ hβμ
  have DJ₂ := infra_72_diagramEq_of_sameGalois (P := P) hJ'₂ Y hj₂ hy₂ hpqμ hβμ
  exact P.scheme.diagram_trans _ _ _ _ _ _ DJ₁
    (P.scheme.diagram_trans _ _ _ _ _ _ G (P.scheme.diagram_symm _ _ _ _ DJ₂))

/-- Every tuple over `A` (level `μ`) has its host at a level `≥ μ`. -/
theorem infra_612_le_nu {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} (t : TupleOver K oneVertexShape P.scheme hμ A) : μ ≤ t.ν := by
  have a := P.scheme.vertex_card hμ A PUnit.unit
  have b := P.scheme.vertex_card t.hν t.host PUnit.unit
  exact a.symm.le.trans
    ((Cardinal.mk_le_of_injective (t.incl.onVertex PUnit.unit).injective).trans b.le)

/-- `SameGaloisType` ⇒ `DiagramEq` of aligned type-joints, hosts at any levels (parameters
bounded below the level of `A`). -/
theorem infra_612_dEq_of_sameGalois {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι}
    (h : SameGaloisType t1 t2 e1 e2)
    {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hι : #ι < μ) (hβ : #β < μ) :
    P.scheme.DiagramEq (X := t1.host) (Y := t2.host)
      (alignJoint e1 (typeJoint (p := t1) Z))
      (alignJoint e2 (typeJoint (p := t2) Z)) := by
  have hα : #(ι ⊕ β) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hι hβ
  exact infra_78_diagramEq_of_sameGalois h Z (hα.trans_le (infra_612_le_nu t1))
    (hα.trans_le (infra_612_le_nu t2))

set_option maxHeartbeats 1600000 in
/-- **Independence core (proved).** Joints `j₁, j₂` at the level `μ` of `A`; realizations
`x_k` of `p` and tied free lifts `y_k` of `q` at ANY eligible levels; each `j_k` agrees with
`(x_k, y_k)` on every bounded test list from `A` (diagram form). Then `j₁` and `j₂` have one
Galois type. -/
theorem infra_612_tied_indep_core
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνq : q.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (j₁ j₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : p.idx ⊕ q.idx ≃ j₂.idx)
    (x₁ x₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (ex₁ : p.idx ≃ x₁.idx) (ex₂ : p.idx ≃ x₂.idx)
    (hS₁ : SameGaloisType p x₁ ex₁ (Equiv.refl x₁.idx))
    (hS₂ : SameGaloisType p x₂ ex₂ (Equiv.refl x₂.idx))
    (y₁ : TupleOver K oneVertexShape P.scheme x₁.hν x₁.host)
    (y₂ : TupleOver K oneVertexShape P.scheme x₂.hν x₂.host)
    (ey₁ : q.idx ≃ y₁.idx) (ey₂ : q.idx ≃ y₂.idx)
    (hT₁ : IsTiedFreeMixed x₁.incl q y₁ ey₁) (hT₂ : IsTiedFreeMixed x₂.incl q y₂ ey₂)
    (hD₁ : ∀ {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #β < μ → P.scheme.DiagramEq (X := j₁.host) (Y := (x₁.join y₁).host)
        (alignJoint e₁.symm (typeJoint (p := j₁) Y))
        (alignJoint (Equiv.sumCongr ex₁ ey₁).symm (typeJoint (p := x₁.join y₁) Y)))
    (hD₂ : ∀ {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #β < μ → P.scheme.DiagramEq (X := j₂.host) (Y := (x₂.join y₂).host)
        (alignJoint e₂.symm (typeJoint (p := j₂) Y))
        (alignJoint (Equiv.sumCongr ex₂ ey₂).symm (typeJoint (p := x₂.join y₂) Y)))
    (hj₁ : j₁.ν = μ) (hj₂ : j₂.ν = μ) :
    SameGaloisType j₁ j₂ e₁.symm e₂.symm := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hpμ : #p.idx < μ := hpσ.trans_lt hσlt
  have hqμ : #q.idx < μ := hqσ.trans_lt hσlt
  have hpqσ : #(p.idx ⊕ q.idx) ≤ σ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hσ hpσ hqσ
  have hj₁σ : #j₁.idx ≤ σ := (Cardinal.mk_congr e₁).symm.trans_le hpqσ
  have hS'₁ : SameGaloisType p x₁ (Equiv.refl p.idx) ex₁.symm := by
    have h := infra_612_sameGalois_trans_equiv hS₁ ex₁.symm
    rwa [Equiv.self_trans_symm, Equiv.refl_trans] at h
  have hS'₂ : SameGaloisType p x₂ (Equiv.refl p.idx) ex₂.symm := by
    have h := infra_612_sameGalois_trans_equiv hS₂ ex₂.symm
    rwa [Equiv.self_trans_symm, Equiv.refl_trans] at h
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ :=
    infra_73_differing_test P σ hσ hμ hrec hσμ j₁ j₂ e₁.symm e₂.symm hj₁ hj₂ hj₁σ
      (hj₁σ.trans_lt hσlt) hneq
  apply hnot
  have hβμ : #β < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    exact hβ.trans_lt (add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ))
  have hpβμ : #(p.idx ⊕ β) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hpμ hβμ
  have hqβμ : #(q.idx ⊕ β) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hqμ hβμ
  obtain ⟨seq, hτlo, -, hlong⟩ :=
    infra_78_exists_seq_ge P σ hσ hμ hrec hσμ q hνq hqσ hpβμ
  let W₁ : p.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem x₁.hν x₁.host) :=
    fun t => typeJoint (p := x₁) Y (Equiv.sumCongr ex₁ (Equiv.refl β) t)
  let W₂ : p.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem x₂.hν x₂.host) :=
    fun t => typeJoint (p := x₂) Y (Equiv.sumCongr ex₂ (Equiv.refl β) t)
  obtain ⟨Z0, hZ0⟩ :=
    infra_78_move_query_mixed x₁.incl x₁.incl_arrow (infra_612_le_nu x₁) seq W₁ hpβμ
  have hmove₂ : infra_78_isMoveMixed x₂.incl seq W₂ Z0 := by
    intro i
    let Z' : q.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
      Sum.elim (seq.family i) Y
    have D₁ := infra_612_dEq_of_sameGalois (P := P) hS'₁ Z' hpμ hqβμ
    have D₂ := infra_612_dEq_of_sameGalois (P := P) hS'₂ Z' hpμ hqβμ
    have M := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ D₁) D₂
    have M' := infra_612_dEq_transport M (infra_612_swap3 q.idx p.idx β)
      (xs' := seqJoint (fun j => (⟨(seq.family i j).1,
        x₁.incl.onVertex (seq.family i j).1 (seq.family i j).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem x₁.hν x₁.host))) W₁)
      (ys' := seqJoint (fun j => (⟨(seq.family i j).1,
        x₂.incl.onVertex (seq.family i j).1 (seq.family i j).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem x₂.hν x₂.host))) W₂)
      (by rintro (j | k | b) <;> rfl) (by rintro (j | k | b) <;> rfl)
    exact P.scheme.diagram_trans _ _ _ _ _ _ (hZ0 i) M'
  have hιτ : #(p.idx ⊕ β) ≤ seq.τ := hτlo
  have T₁ := hT₁ seq W₁ Z0 hlong hιτ hpβμ hZ0
  have T₂ := hT₂ seq W₂ Z0 hlong hιτ hpβμ hmove₂
  have N := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ T₁) T₂
  have G := infra_612_dEq_transport N (infra_612_swap3' p.idx q.idx β)
    (xs' := alignJoint (Equiv.sumCongr ex₁ ey₁).symm (typeJoint (p := x₁.join y₁) Y))
    (ys' := alignJoint (Equiv.sumCongr ex₂ ey₂).symm (typeJoint (p := x₂.join y₂) Y))
    (by rintro ((k | j) | b) <;> rfl) (by rintro ((k | j) | b) <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ (hD₁ Y hβμ)
    (P.scheme.diagram_trans _ _ _ _ _ _ G (P.scheme.diagram_symm _ _ _ _ (hD₂ Y hβμ)))

/-- **Independence of `p ⊗ q`, joints at the level of `A` (proved).** Realizations and free
lifts at any eligible levels; the two joints `j₁, j₂` at the level `μ` of `A`. -/
theorem infra_612_tied_indep_level_joints
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνq : q.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (j₁ j₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : p.idx ⊕ q.idx ≃ j₂.idx)
    (h₁ : IsProductTied p q j₁ e₁) (h₂ : IsProductTied p q j₂ e₂)
    (hj₁ : j₁.ν = μ) (hj₂ : j₂.ν = μ) :
    SameGaloisType j₁ j₂ e₁.symm e₂.symm := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hpqμ : #(p.idx ⊕ q.idx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) (hpσ.trans_lt hσlt) (hqσ.trans_lt hσlt)
  obtain ⟨x₁, ex₁, hS₁, y₁, ey₁, hT₁, hJ₁⟩ := h₁
  obtain ⟨x₂, ex₂, hS₂, y₂, ey₂, hT₂, hJ₂⟩ := h₂
  have hJ'₁ : SameGaloisType j₁ (x₁.join y₁) e₁.symm (Equiv.sumCongr ex₁ ey₁).symm := by
    have h := infra_612_sameGalois_trans_equiv hJ₁ (Equiv.sumCongr ex₁ ey₁).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  have hJ'₂ : SameGaloisType j₂ (x₂.join y₂) e₂.symm (Equiv.sumCongr ex₂ ey₂).symm := by
    have h := infra_612_sameGalois_trans_equiv hJ₂ (Equiv.sumCongr ex₂ ey₂).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  exact infra_612_tied_indep_core P σ hσ hμ hrec hσμ p q hνq hpσ hqσ j₁ j₂ e₁ e₂ x₁ x₂
    ex₁ ex₂ hS₁ hS₂ y₁ y₂ ey₁ ey₂ hT₁ hT₂
    (fun Y hβ => infra_612_dEq_of_sameGalois hJ'₁ Y hpqμ hβ)
    (fun Y hβ => infra_612_dEq_of_sameGalois hJ'₂ Y hpqμ hβ) hj₁ hj₂

/-- **Independence of `p ⊗ q`, joints at any levels, via their `μ`-level copies (proved).**
For tied products `j₁, j₂` at arbitrary eligible levels and any realizations `j'_k` of their
Galois types at the level `μ` of `A` (these exist: `infra_78_same_level_realization`), the
copies `j'₁, j'₂` have one Galois type. Concluding `SameGaloisType j₁ j₂` from this needs the
transitivity of Galois types through a `μ`-level middle with ends above `μ`
(open tip `infra_612_galois_trans_cross_level`). -/
theorem infra_612_tied_indep_copies
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνq : q.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (j₁ j₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : p.idx ⊕ q.idx ≃ j₂.idx)
    (h₁ : IsProductTied p q j₁ e₁) (h₂ : IsProductTied p q j₂ e₂)
    (j'₁ j'₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (r₁ : j'₁.idx ≃ j₁.idx) (r₂ : j'₂.idx ≃ j₂.idx)
    (hR₁ : SameGaloisType j₁ j'₁ (Equiv.refl j₁.idx) r₁)
    (hR₂ : SameGaloisType j₂ j'₂ (Equiv.refl j₂.idx) r₂)
    (hj'₁ : j'₁.ν = μ) (hj'₂ : j'₂.ν = μ) :
    SameGaloisType j'₁ j'₂ (r₁.trans e₁.symm) (r₂.trans e₂.symm) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hpqμ : #(p.idx ⊕ q.idx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) (hpσ.trans_lt hσlt) (hqσ.trans_lt hσlt)
  obtain ⟨x₁, ex₁, hS₁, y₁, ey₁, hT₁, hJ₁⟩ := h₁
  obtain ⟨x₂, ex₂, hS₂, y₂, ey₂, hT₂, hJ₂⟩ := h₂
  have hJ'₁ : SameGaloisType j₁ (x₁.join y₁) e₁.symm (Equiv.sumCongr ex₁ ey₁).symm := by
    have h := infra_612_sameGalois_trans_equiv hJ₁ (Equiv.sumCongr ex₁ ey₁).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  have hJ'₂ : SameGaloisType j₂ (x₂.join y₂) e₂.symm (Equiv.sumCongr ex₂ ey₂).symm := by
    have h := infra_612_sameGalois_trans_equiv hJ₂ (Equiv.sumCongr ex₂ ey₂).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  have hR'₁ : SameGaloisType j₁ j'₁ e₁.symm (r₁.trans e₁.symm) :=
    infra_612_sameGalois_trans_equiv hR₁ e₁.symm
  have hR'₂ : SameGaloisType j₂ j'₂ e₂.symm (r₂.trans e₂.symm) :=
    infra_612_sameGalois_trans_equiv hR₂ e₂.symm
  refine infra_612_tied_indep_core P σ hσ hμ hrec hσμ p q hνq hpσ hqσ j'₁ j'₂
    (r₁.trans e₁.symm).symm (r₂.trans e₂.symm).symm x₁ x₂
    ex₁ ex₂ hS₁ hS₂ y₁ y₂ ey₁ ey₂ hT₁ hT₂ ?_ ?_ hj'₁ hj'₂
  · intro β Y hβ
    rw [Equiv.symm_symm]
    exact P.scheme.diagram_trans _ _ _ _ _ _
      (P.scheme.diagram_symm _ _ _ _ (infra_612_dEq_of_sameGalois hR'₁ Y hpqμ hβ))
      (infra_612_dEq_of_sameGalois hJ'₁ Y hpqμ hβ)
  · intro β Y hβ
    rw [Equiv.symm_symm]
    exact P.scheme.diagram_trans _ _ _ _ _ _
      (P.scheme.diagram_symm _ _ _ _ (infra_612_dEq_of_sameGalois hR'₂ Y hpqμ hβ))
      (infra_612_dEq_of_sameGalois hJ'₂ Y hpqμ hβ)

/-- **Proposition 6.12** (Products of bounded types). For bounded types `p(x)`, `q(y)` over
`A`, realize `p` in an extension `B ≥ A` and then realize `q^B` (the free lift) in a further
extension; the joint type `p ⊗ q` of `(x, y)` over `A` (`IsProductTied`):

1. exists;
2. is independent of all choices (any two products are the same Galois type);
3. is symmetric, with the coordinate swap: `p ⊗ q = q ⊗ p`;
4. associates: `(p ⊗ q) ⊗ r = p ⊗ (q ⊗ r)` (with `Equiv.sumAssoc`); iterated finite products
   then associate by induction;
5. finite products (`IsFiniteProductTied`) are permutation invariant;
6. finite products commute with coordinate projections (sub-lists of factors);
7. base change: for `A → B`, `(p ⊗ q)^B = p_B ⊗ q^B` (free lifts tied, `IsTiedFreeMixed`).

"Across eligible levels": realizations and the base change target may sit at any eligible level
of the tail at or above that of `A` (all arities are bounded at the level of `A`).
Packaging as Theorem 6.10: a tail of recursion-closed levels `μ ≥ σ⁺`, factors of size `≤ σ`
realized at the level of `A`.

**Status:** clause 1 proved (`infra_612_tied_exists`); clauses 2–7 are `sorry`, tracked as
`infra_612_tied_independence`, `infra_612_tied_symmetry`, `infra_612_tied_assoc`,
`infra_612_tied_finite` (5 and 6), `infra_612_tied_base_change`. -/
theorem proposition_6_12 {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ)),
      let TO := TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A
      ∀ (p q : TO), p.ν = μ → q.ν = μ → #p.idx ≤ σ → #q.idx ≤ σ →
        -- 1. existence
        (∃ (joint : TO) (e : p.idx ⊕ q.idx ≃ joint.idx), IsProductTied p q joint e) ∧
        -- 2. independence of choices
        (∀ (j₁ j₂ : TO) (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : p.idx ⊕ q.idx ≃ j₂.idx),
          IsProductTied p q j₁ e₁ → IsProductTied p q j₂ e₂ →
          SameGaloisType j₁ j₂ e₁.symm e₂.symm) ∧
        -- 3. symmetry
        (∀ (j₁ j₂ : TO) (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : q.idx ⊕ p.idx ≃ j₂.idx),
          IsProductTied p q j₁ e₁ → IsProductTied q p j₂ e₂ →
          SameGaloisType j₁ j₂ e₁.symm (e₂.symm.trans (Equiv.sumComm _ _))) ∧
        -- 4. associativity
        (∀ (r : TO), r.ν = μ → #r.idx ≤ σ →
          ∀ (pq qr j₁ j₂ : TO) (epq : p.idx ⊕ q.idx ≃ pq.idx) (eqr : q.idx ⊕ r.idx ≃ qr.idx)
            (e₁ : pq.idx ⊕ r.idx ≃ j₁.idx) (e₂ : p.idx ⊕ qr.idx ≃ j₂.idx),
            IsProductTied p q pq epq → IsProductTied pq r j₁ e₁ →
            IsProductTied q r qr eqr → IsProductTied p qr j₂ e₂ →
            SameGaloisType j₁ j₂
              (e₁.symm.trans ((Equiv.sumCongr epq.symm (Equiv.refl _)).trans
                (Equiv.sumAssoc _ _ _)))
              (e₂.symm.trans (Equiv.sumCongr (Equiv.refl _) eqr.symm))) ∧
        -- 5. permutation invariance of finite products
        (∀ (n : ℕ) (b : Fin n → TO), (∀ i, (b i).ν = μ ∧ #(b i).idx ≤ σ) →
          ∀ (π : Equiv.Perm (Fin n)) (j₁ j₂ : TO)
            (E₁ : (Σ i, (b i).idx) ≃ j₁.idx) (E₂ : (Σ i, (b (π i)).idx) ≃ j₂.idx),
            IsFiniteProductTied n b j₁ E₁ → IsFiniteProductTied n (fun i => b (π i)) j₂ E₂ →
            SameGaloisType j₁ j₂ E₁.symm (E₂.symm.trans (Equiv.sigmaCongrLeft (β := fun i => (b i).idx) π))) ∧
        -- 6. finite products commute with coordinate projections
        (∀ (n m : ℕ) (b : Fin n → TO), (∀ i, (b i).ν = μ ∧ #(b i).idx ≤ σ) →
          ∀ (s : Fin m ↪ Fin n) (j j' : TO)
            (E : (Σ i, (b i).idx) ≃ j.idx) (E' : (Σ i, (b (s i)).idx) ≃ j'.idx),
            IsFiniteProductTied n b j E → IsFiniteProductTied m (fun i => b (s i)) j' E' →
            SameGaloisType (j.reindex (fun t : (Σ i, (b (s i)).idx) => E ⟨s t.1, t.2⟩)) j'
              (Equiv.refl _) E'.symm) ∧
        -- 7. base change `(p ⊗ q)^B = p_B ⊗ q^B`
        (∀ μ' (hμ' : μ' ∈ T), μ ≤ μ' →
          ∀ (B : P.scheme.Object μ' (Tail.mem hT hμ'))
            (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
            (_hf : P.scheme.permitted (X := A) (Y := B) f)
            (joint : TO) (e : p.idx ⊕ q.idx ≃ joint.idx)
            (pB qB jB jB' : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ') B)
            (eP : p.idx ≃ pB.idx) (eQ : q.idx ≃ qB.idx) (eJ : joint.idx ≃ jB.idx)
            (e' : pB.idx ⊕ qB.idx ≃ jB'.idx),
            IsProductTied p q joint e →
            IsTiedFreeMixed f p pB eP → IsTiedFreeMixed f q qB eQ →
            IsTiedFreeMixed f joint jB eJ →
            IsProductTied pB qB jB' e' →
            SameGaloisType jB jB' (eJ.symm.trans e.symm)
              (e'.symm.trans (Equiv.sumCongr eP.symm eQ.symm))) := by
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun μ hμ A p q hνp hνq hpσ hqσ =>
    ⟨infra_612_tied_exists P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 p q hνp hνq hqσ, ?_⟩⟩
  -- clauses 2–7: open sub-tips (see the module docstring)
  sorry

end
end AEC
