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
Symmetry is proved for joints at the level of `A` (`infra_612_tied_symm_level_joints`, the
English array argument with sequences of lengths `κ < λ`).
Base change is proved for joints at their base levels (`infra_612_tied_base_change_level_joints`,
via `infra_612_pushSeq` and `infra_612_product_entry`).
Associativity is proved for intermediate products and joints at the level of `A`
(`infra_612_tied_assoc_level_joints`, the three-dimensional array argument).
Permutation invariance and projections (clauses 5, 6) are proved when every partial product
and both joints sit at the level of `A` (`IsFiniteProductTiedLevel`,
`infra_612_tied_finite_perm_level`, `infra_612_tied_finite_proj_level`: generic entries of the
`n`-dimensional array, `infra_612_finite_generic`, along sequences of strictly increasing
lengths).
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

/-- A tied product of `p` and `q` whose realization and free lift sit at the level `μ`
(the witness of `infra_612_tied_exists_aux`, with the level recorded). -/
theorem infra_612_tied_exists_witness_aux
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
    ∃ (y : TupleOver K oneVertexShape P.scheme hν host) (ey : q.idx ≃ y.idx),
      y.ν = μ ∧ IsTiedFreeMixed incl q y ey ∧ IsProductTied (⟨ν, hν, host, incl, hincl, idx, val⟩ :
          TupleOver K oneVertexShape P.scheme hμ A) q
        ((⟨ν, hν, host, incl, hincl, idx, val⟩ : TupleOver K oneVertexShape P.scheme hμ A).join y)
        (Equiv.sumCongr (Equiv.refl idx) ey) := by
  subst hνμ
  let x : TupleOver K oneVertexShape P.scheme hν A := ⟨ν, hν, host, incl, hincl, idx, val⟩
  obtain ⟨y, ey, hyν, -, hT⟩ :=
    infra_610_tied_free_lift P σ hσ hν hrec hσμ incl hincl q hνq hqσ
  refine ⟨y, ey, hyν, hT, x, Equiv.refl _, SameGaloisType.refl x, y, ey, hT, ?_⟩
  have h : (Equiv.sumCongr (Equiv.refl idx) ey).symm.trans
      (Equiv.sumCongr (Equiv.refl idx) ey) = Equiv.refl (idx ⊕ y.idx) :=
    Equiv.symm_trans_self _
  exact h ▸ SameGaloisType.refl (x.join y)

/-- **A level-`μ` copy of a tied product is a tied product (proved, cycle 93).** If `j` (any
eligible level) is `p ⊗ q` and `j'` is a level-`μ` copy of `j`, then `j'` is `p ⊗ q`. -/
theorem infra_612_isProductTied_copy
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (j : TupleOver K oneVertexShape P.scheme hμ A) (e : p.idx ⊕ q.idx ≃ j.idx)
    (h : IsProductTied p q j e)
    (j' : TupleOver K oneVertexShape P.scheme hμ A) (r : j'.idx ≃ j.idx)
    (hR : SameGaloisType j j' (Equiv.refl j.idx) r) (hj' : j'.ν = μ) :
    IsProductTied p q j' (e.trans r.symm) := by
  obtain ⟨y, ey, hyν, hT, h0⟩ := infra_612_tied_exists_witness_aux P σ hσ hμ hrec hσμ hνp p.hν
    p.host p.incl p.incl_arrow p.idx p.val q hνq hqσ
  have h01 := infra_612_tied_indep_copies P σ hσ hμ hrec hσμ p q hνq hpσ hqσ j (p.join y) e
    (Equiv.sumCongr (Equiv.refl p.idx) ey) h h0 j' (p.join y) r (Equiv.refl _) hR
    (SameGaloisType.refl _) hj' hyν
  refine ⟨p, Equiv.refl _, SameGaloisType.refl p, y, ey, hT, ?_⟩
  · have h2 := infra_612_sameGalois_trans_equiv h01 (Equiv.sumCongr (Equiv.refl p.idx) ey)
    have heq2 : ((Equiv.refl (p.join y).idx).trans
        (Equiv.sumCongr (Equiv.refl p.idx) ey).symm).trans
        (Equiv.sumCongr (Equiv.refl p.idx) ey) = Equiv.refl (p.idx ⊕ y.idx) := by
      ext t
      exact Equiv.apply_symm_apply (Equiv.sumCongr (Equiv.refl p.idx) ey) t
    have heq1 : (r.trans e.symm).trans (Equiv.sumCongr (Equiv.refl p.idx) ey) =
        (e.trans r.symm).symm.trans (Equiv.sumCongr (Equiv.refl p.idx) ey) := rfl
    erw [heq2, heq1] at h2
    exact h2

/-- `infra_78_exists_seq_ge` with the index length also below `μ`. -/
theorem infra_612_exists_seq_small
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {base : P.scheme.Object μ hμ} (p : TupleOver K oneVertexShape P.scheme hμ base)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) {t : Cardinal.{u}} (ht : t < μ) :
    ∃ seq : ApproximationSequence p, t ≤ seq.τ ∧ seq.τ < μ ∧ seq.τ + ℵ₀ < #seq.κIndex ∧
      #seq.κIndex < μ := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #p.idx < μ := hidx.trans_lt hσlt
  let τ : Cardinal.{u} := max t ℵ₀
  have hτ : ℵ₀ ≤ τ := le_max_right _ _
  have hτμ : τ < μ := max_lt ht (P.aleph0_lt hμ)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ := by
    apply hrec.2
    exact max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
  let ρ : Cardinal.{u} := max τ #p.idx
  have hρinf : ℵ₀ ≤ ρ := hτ.trans (le_max_left _ _)
  have hρμ : ρ < μ := max_lt hτμ hidxμ
  let κ : Cardinal.{u} := Order.succ ρ
  have hκinf : ℵ₀ ≤ κ := hρinf.trans (Order.le_succ _)
  have hκμ : κ < μ :=
    (Order.succ_le_of_lt (cantor ρ)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hρμ)
  have hprodκ : κ * #p.idx < μ := by
    have hmul : κ * #p.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    rcases le_total σ κ with hσκ | hκσ
    · have heq : κ * σ = κ :=
        mul_eq_left hκinf hσκ (aleph0_pos.trans_le hσ).ne'
      rw [heq] at hmul
      exact hmul.trans_lt hκμ
    · have heq : κ * σ = σ := by
        rw [mul_comm]
        exact mul_eq_left hσ hκσ (aleph0_pos.trans_le hκinf).ne'
      rw [heq] at hmul
      exact hmul.trans_lt hσlt
  obtain ⟨seq, hseqτ, hseqκ⟩ :=
    P.exists_approximationSequence hμ base p hνμ σ τ κ hσ hσlt hidx hτ hτμ hκinf hκμ
      hprodκ hclosed
  refine ⟨seq, ?_, ?_, ?_, ?_⟩
  · rw [hseqτ]; exact le_max_left _ _
  · rw [hseqτ]; exact hτμ
  · rw [hseqτ, hseqκ, add_eq_left hτ hτ]
    exact (le_max_left _ _).trans_lt (Order.lt_succ ρ)
  · rw [hseqκ]; exact hκμ

set_option maxHeartbeats 3200000 in
/-- **Symmetry of `p ⊗ q`, joints at the level of `A` (proved).** For tied products
`IsProductTied p q j₁ e₁` and `IsProductTied q p j₂ e₂` with `j₁, j₂` at the level `μ` of `A`
(realizations and free lifts at any eligible levels), `j₁` and `j₂` have one Galois type, up to
the coordinate swap. English proof of Proposition 6.12 (the array `D(aᵢ, bⱼ, Z)`): sequences
`a` for `p` (length `κ`) and `b` for `q` (length `λ > κ`); realizing `x` then `y` makes the
type agree with the array entries off at most `e` columns and, in each such column, off at most
`e` rows; the reverse order agrees off at most `e` rows and, in each such row, off at most `e`
columns. A column outside all `κ · e` row-exceptions and a row outside both exceptional sets
give one common entry. Theorem 6.6 testing (`infra_73_differing_test`) closes. -/
theorem infra_612_tied_symm_core
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (j₁ j₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : q.idx ⊕ p.idx ≃ j₂.idx)
    (x₁ x₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (ex₁ : p.idx ≃ x₁.idx) (ex₂ : q.idx ≃ x₂.idx)
    (hS₁ : SameGaloisType p x₁ ex₁ (Equiv.refl x₁.idx))
    (hS₂ : SameGaloisType q x₂ ex₂ (Equiv.refl x₂.idx))
    (y₁ : TupleOver K oneVertexShape P.scheme x₁.hν x₁.host)
    (y₂ : TupleOver K oneVertexShape P.scheme x₂.hν x₂.host)
    (ey₁ : q.idx ≃ y₁.idx) (ey₂ : p.idx ≃ y₂.idx)
    (hT₁ : IsTiedFreeMixed x₁.incl q y₁ ey₁) (hT₂ : IsTiedFreeMixed x₂.incl p y₂ ey₂)
    (hD₁ : ∀ {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #β < μ → P.scheme.DiagramEq (X := j₁.host) (Y := (x₁.join y₁).host)
        (alignJoint e₁.symm (typeJoint (p := j₁) Y))
        (alignJoint (Equiv.sumCongr ex₁ ey₁).symm (typeJoint (p := x₁.join y₁) Y)))
    (hD₂ : ∀ {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #β < μ → P.scheme.DiagramEq (X := j₂.host) (Y := (x₂.join y₂).host)
        (alignJoint e₂.symm (typeJoint (p := j₂) Y))
        (alignJoint (Equiv.sumCongr ex₂ ey₂).symm (typeJoint (p := x₂.join y₂) Y)))
    (hj₁ : j₁.ν = μ) (hj₂ : j₂.ν = μ) :
    SameGaloisType j₁ j₂ e₁.symm (e₂.symm.trans (Equiv.sumComm _ _)) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hpμ : #p.idx < μ := hpσ.trans_lt hσlt
  have hqμ : #q.idx < μ := hqσ.trans_lt hσlt
  have hpqσ : #(p.idx ⊕ q.idx) ≤ σ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hσ hpσ hqσ
  have hpqμ : #(p.idx ⊕ q.idx) < μ := hpqσ.trans_lt hσlt
  have hqpμ : #(q.idx ⊕ p.idx) < μ :=
    (Cardinal.mk_congr (Equiv.sumComm _ _)).symm.trans_lt hpqμ
  have hj₁σ : #j₁.idx ≤ σ := (Cardinal.mk_congr e₁).symm.trans_le hpqσ
  have hS'₁ : SameGaloisType p x₁ (Equiv.refl p.idx) ex₁.symm := by
    have h := infra_612_sameGalois_trans_equiv hS₁ ex₁.symm
    rwa [Equiv.self_trans_symm, Equiv.refl_trans] at h
  have hS'₂ : SameGaloisType q x₂ (Equiv.refl q.idx) ex₂.symm := by
    have h := infra_612_sameGalois_trans_equiv hS₂ ex₂.symm
    rwa [Equiv.self_trans_symm, Equiv.refl_trans] at h
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ :=
    infra_73_differing_test P σ hσ hμ hrec hσμ j₁ j₂ e₁.symm
      (e₂.symm.trans (Equiv.sumComm _ _)) hj₁ hj₂ hj₁σ (hj₁σ.trans_lt hσlt) hneq
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
  have hallμ : #((p.idx ⊕ q.idx) ⊕ β) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hpqμ hβμ
  have hpβle : #(p.idx ⊕ β) ≤ #((p.idx ⊕ q.idx) ⊕ β) :=
    Cardinal.mk_le_of_injective (f := Sum.map Sum.inl id)
      (Sum.map_injective.mpr ⟨Sum.inl_injective, Function.injective_id⟩)
  have hqβle : #(q.idx ⊕ β) ≤ #((p.idx ⊕ q.idx) ⊕ β) :=
    Cardinal.mk_le_of_injective (f := Sum.map Sum.inr id)
      (Sum.map_injective.mpr ⟨Sum.inr_injective, Function.injective_id⟩)
  -- the two sequences: `a` for `p`, then a longer `b` for `q`
  obtain ⟨a, haτ, -, halong, haμ⟩ :=
    infra_612_exists_seq_small P σ hσ hμ hrec hσμ p hνp hpσ hallμ
  obtain ⟨b, hbτ, -, hblong, -⟩ :=
    infra_612_exists_seq_small P σ hσ hμ hrec hσμ q hνq hqσ
      (max_lt (hpβle.trans_lt hallμ) haμ)
  set E : Cardinal.{u} := a.τ + aleph0 with hEdef
  have hEinf : aleph0 ≤ E := le_add_left le_rfl
  have hpβa : #(p.idx ⊕ β) ≤ a.τ := hpβle.trans haτ
  have hqβa : #(q.idx ⊕ β) ≤ a.τ := hqβle.trans haτ
  have hpβb : #(p.idx ⊕ β) ≤ b.τ := (le_max_left _ _).trans hbτ
  have haκb : #a.κIndex ≤ b.τ := (le_max_right _ _).trans hbτ
  have hEa : E < #a.κIndex := halong
  have hainf : aleph0 ≤ #a.κIndex := hEinf.trans hEa.le
  have hab : #a.κIndex < #b.κIndex := (haκb.trans le_self_add).trans_lt hblong
  -- product 1: `x₁ ⊨ p`, `y₁` the tied free lift of `q`, moved over `b`
  let W₁ : p.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem x₁.hν x₁.host) :=
    fun t => typeJoint (p := x₁) Y (Equiv.sumCongr ex₁ (Equiv.refl β) t)
  obtain ⟨Z0, hZ0⟩ :=
    infra_78_move_query_mixed x₁.incl x₁.incl_arrow (infra_612_le_nu x₁) b W₁ hpβμ
  have T₁ := hT₁ b W₁ Z0 hblong hpβb hpβμ hZ0
  -- product 2: `x₂ ⊨ q`, `y₂` the tied free lift of `p`, moved over `a`
  let W₂ : q.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem x₂.hν x₂.host) :=
    fun t => typeJoint (p := x₂) Y (Equiv.sumCongr ex₂ (Equiv.refl β) t)
  obtain ⟨Z0', hZ0'⟩ :=
    infra_78_move_query_mixed x₂.incl x₂.incl_arrow (infra_612_le_nu x₂) a W₂ hqβμ
  have T₂ := hT₂ a W₂ Z0' halong hqβa hqβμ hZ0'
  -- exceptional sets
  let badCol : Set b.κIndex := {j | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
    (typeJoint (p := q) Z0) (seqJoint (b.family j) Z0)}
  let badRow1 : b.κIndex → Set a.κIndex := fun j => {i | ¬ P.scheme.DiagramEq (X := p.host)
    (Y := A) (typeJoint (p := p) (Sum.elim (b.family j) Y))
    (seqJoint (a.family i) (Sum.elim (b.family j) Y))}
  let badRow2 : Set a.κIndex := {i | ¬ P.scheme.DiagramEq (X := p.host) (Y := A)
    (typeJoint (p := p) Z0') (seqJoint (a.family i) Z0')}
  let badCol2 : a.κIndex → Set b.κIndex := fun i => {j | ¬ P.scheme.DiagramEq (X := q.host)
    (Y := A) (typeJoint (p := q) (Sum.elim (a.family i) Y))
    (seqJoint (b.family j) (Sum.elim (a.family i) Y))}
  have hbadCol : #badCol ≤ E :=
    (b.few_exceptions Z0 hpβb).trans (add_le_add hpβa le_rfl)
  have hbadRow1 : ∀ j, #(badRow1 j) ≤ E := fun j =>
    (a.few_exceptions (Sum.elim (b.family j) Y) hqβa).trans (add_le_add hqβa le_rfl)
  have hbadRow2 : #badRow2 ≤ E :=
    (a.few_exceptions Z0' hqβa).trans (add_le_add hqβa le_rfl)
  have hbadCol2 : ∀ i, #(badCol2 i) ≤ E := fun i =>
    (b.few_exceptions (Sum.elim (a.family i) Y) hpβb).trans (add_le_add hpβa le_rfl)
  -- a good column
  obtain ⟨j, hj⟩ : ∃ j, j ∉ badCol ∪ ⋃ i, badCol2 i := by
    by_contra hall
    push_neg at hall
    have hU : #(⋃ i, badCol2 i) ≤ #a.κIndex := by
      refine (Cardinal.mk_iUnion_le _).trans ?_
      calc #a.κIndex * ⨆ i, #(badCol2 i) ≤ #a.κIndex * #a.κIndex :=
            mul_le_mul' le_rfl (ciSup_le' fun i => (hbadCol2 i).trans hEa.le)
        _ = #a.κIndex := Cardinal.mul_eq_self hainf
    have h1 : #b.κIndex ≤ #a.κIndex :=
      calc #b.κIndex = #(Set.univ : Set b.κIndex) := Cardinal.mk_univ.symm
        _ ≤ #(badCol ∪ ⋃ i, badCol2 i : Set b.κIndex) :=
            Cardinal.mk_le_mk_of_subset fun j _ => hall j
        _ ≤ #badCol + #(⋃ i, badCol2 i) := Cardinal.mk_union_le _ _
        _ ≤ #a.κIndex + #a.κIndex := add_le_add (hbadCol.trans hEa.le) hU
        _ = #a.κIndex := Cardinal.add_eq_self hainf
    exact absurd hab (not_lt.2 h1)
  -- a good row
  obtain ⟨i, hi⟩ : ∃ i, i ∉ badRow1 j ∪ badRow2 := by
    by_contra hall
    push_neg at hall
    have h1 : #a.κIndex ≤ E :=
      calc #a.κIndex = #(Set.univ : Set a.κIndex) := Cardinal.mk_univ.symm
        _ ≤ #(badRow1 j ∪ badRow2 : Set a.κIndex) :=
            Cardinal.mk_le_mk_of_subset fun i _ => hall i
        _ ≤ #(badRow1 j) + #badRow2 := Cardinal.mk_union_le _ _
        _ ≤ E + E := add_le_add (hbadRow1 j) hbadRow2
        _ = E := Cardinal.add_eq_self hEinf
    exact absurd hEa (not_lt.2 h1)
  have hjc : j ∉ badCol := fun h => hj (Or.inl h)
  have hjc2 : j ∉ badCol2 i := fun h => hj (Or.inr (Set.mem_iUnion.2 ⟨i, h⟩))
  have hir1 : i ∉ badRow1 j := fun h => hi (Or.inl h)
  have hir2 : i ∉ badRow2 := fun h => hi (Or.inr h)
  have Fj : P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q) Z0) (seqJoint (b.family j) Z0) := not_not.1 hjc
  have Gij : P.scheme.DiagramEq (X := p.host) (Y := A)
      (typeJoint (p := p) (Sum.elim (b.family j) Y))
      (seqJoint (a.family i) (Sum.elim (b.family j) Y)) := not_not.1 hir1
  have Fi : P.scheme.DiagramEq (X := p.host) (Y := A)
      (typeJoint (p := p) Z0') (seqJoint (a.family i) Z0') := not_not.1 hir2
  have Gji : P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q) (Sum.elim (a.family i) Y))
      (seqJoint (b.family j) (Sum.elim (a.family i) Y)) := not_not.1 hjc2
  -- chain 1: `(y₁, x₁, Y)` agrees with the entry `D(aᵢ, bⱼ, Y)`
  have C1 := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ T₁)
    (P.scheme.diagram_trans _ _ _ _ _ _ Fj (hZ0 j))
  have D₁ := infra_612_dEq_of_sameGalois (P := P) hS'₁ (Sum.elim (b.family j) Y) hpμ hqβμ
  have C1' := infra_612_dEq_transport C1 (infra_612_swap3 p.idx q.idx β)
    (xs' := fun s => infra_612_anchored ey₁ y₁.incl y₁.val W₁ (infra_612_swap3 p.idx q.idx β s))
    (ys' := alignJoint ex₁.symm (typeJoint (p := x₁) (Sum.elim (b.family j) Y)))
    (fun _ => rfl) (by rintro (k | l | c) <;> rfl)
  have G1' := infra_612_dEq_transport Gij (Equiv.refl _)
    (xs' := alignJoint (Equiv.refl p.idx) (typeJoint (p := p) (Sum.elim (b.family j) Y)))
    (ys' := seqJoint (a.family i) (Sum.elim (b.family j) Y))
    (by rintro (k | l | c) <;> rfl) (fun _ => rfl)
  have fin1 := P.scheme.diagram_trans _ _ _ _ _ _ C1'
    (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ D₁) G1')
  -- chain 2: `(y₂, x₂, Y)` agrees with the same entry, read as `D(bⱼ, aᵢ, Y)`
  have C2 := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ T₂)
    (P.scheme.diagram_trans _ _ _ _ _ _ Fi (hZ0' i))
  have D₂ := infra_612_dEq_of_sameGalois (P := P) hS'₂ (Sum.elim (a.family i) Y) hqμ hpβμ
  have C2' := infra_612_dEq_transport C2 (infra_612_swap3 q.idx p.idx β)
    (xs' := fun s => infra_612_anchored ey₂ y₂.incl y₂.val W₂ (infra_612_swap3 q.idx p.idx β s))
    (ys' := alignJoint ex₂.symm (typeJoint (p := x₂) (Sum.elim (a.family i) Y)))
    (fun _ => rfl) (by rintro (k | l | c) <;> rfl)
  have G2' := infra_612_dEq_transport Gji (Equiv.refl _)
    (xs' := alignJoint (Equiv.refl q.idx) (typeJoint (p := q) (Sum.elim (a.family i) Y)))
    (ys' := seqJoint (b.family j) (Sum.elim (a.family i) Y))
    (by rintro (k | l | c) <;> rfl) (fun _ => rfl)
  have fin2 := P.scheme.diagram_trans _ _ _ _ _ _ C2'
    (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ D₂) G2')
  -- compare in the coordinates `q ⊕ (p ⊕ β)`
  have fin1' := infra_612_dEq_transport fin1 (infra_612_swap3 q.idx p.idx β)
    (xs' := infra_612_anchored ey₁ y₁.incl y₁.val W₁)
    (ys' := seqJoint (b.family j) (Sum.elim (a.family i) Y))
    (by rintro (k | l | c) <;> rfl) (by rintro (k | l | c) <;> rfl)
  have H := P.scheme.diagram_trans _ _ _ _ _ _ fin1' (P.scheme.diagram_symm _ _ _ _ fin2)
  have H' := infra_612_dEq_transport H (infra_612_swap3' p.idx q.idx β)
    (xs' := alignJoint (Equiv.sumCongr ex₁ ey₁).symm (typeJoint (p := x₁.join y₁) Y))
    (ys' := fun t => alignJoint (Equiv.sumCongr ex₂ ey₂).symm (typeJoint (p := x₂.join y₂) Y)
      (Equiv.sumCongr (Equiv.sumComm p.idx q.idx) (Equiv.refl β) t))
    (by rintro ((k | l) | c) <;> rfl) (by rintro ((k | l) | c) <;> rfl)
  have DJ₁ := hD₁ Y hβμ
  have DJ₂ := hD₂ Y hβμ
  have DJ₂' := infra_612_dEq_transport (P.scheme.diagram_symm _ _ _ _ DJ₂)
    (Equiv.sumCongr (Equiv.sumComm p.idx q.idx) (Equiv.refl β))
    (xs' := fun t => alignJoint (Equiv.sumCongr ex₂ ey₂).symm (typeJoint (p := x₂.join y₂) Y)
      (Equiv.sumCongr (Equiv.sumComm p.idx q.idx) (Equiv.refl β) t))
    (ys' := alignJoint (e₂.symm.trans (Equiv.sumComm _ _)) (typeJoint (p := j₂) Y))
    (fun _ => rfl) (by rintro ((k | l) | c) <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ DJ₁
    (P.scheme.diagram_trans _ _ _ _ _ _ H' DJ₂')


/-- **Pushed approximation sequence.** If `qB` over `B` is tied free from `q` along
`f : A → B`, an approximation sequence `b` for `q` pushed along `f` is one for `qB`
(same length, same query size; English Theorem 6.10, transitivity of the free evaluation). -/
noncomputable def infra_612_pushSeq
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f) (hνμ : ν ≤ μ)
    (q : TupleOver K oneVertexShape P.scheme hν A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B) (eQ : q.idx ≃ qB.idx)
    (hQ : IsTiedFreeMixed f q qB eQ) (b : ApproximationSequence q)
    (hb : b.τ + ℵ₀ < #b.κIndex) (hbν : b.τ < ν) : ApproximationSequence qB where
  τ := b.τ
  κIndex := b.κIndex
  family := fun j k => ⟨(b.family j (eQ.symm k)).1,
    f.onVertex (b.family j (eQ.symm k)).1 (b.family j (eQ.symm k)).2⟩
  concat_bounded := by
    rw [← Cardinal.mk_congr (Equiv.prodCongr (Equiv.refl b.κIndex) eQ)]
    exact b.concat_bounded.trans_le hνμ
  few_exceptions := fun {ι} W hW => by
    classical
    obtain ⟨W0, hW0⟩ := infra_78_move_query_mixed f hf hνμ b W (hW.trans_lt hbν)
    have ht := hQ b W W0 hb hW (hW.trans_lt hbν) hW0
    refine le_trans ?_ (b.few_exceptions W0 hW)
    refine Cardinal.mk_le_of_injective (f := fun j => ⟨j.1, fun hgood => j.2 ?_⟩)
      (by
        intro j₁ j₂ hj
        apply Subtype.ext
        have := congrArg Subtype.val hj
        exact this)
    have e3 := P.scheme.diagram_trans _ _ _ _ _ _
      (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ ht) hgood) (hW0 j.1)
    refine infra_612_dEq_transport e3 (Equiv.sumCongr eQ.symm (Equiv.refl ι)) ?_ ?_
    · rintro (k | c)
      · simp [typeJoint, infra_612_anchored]
      · rfl
    · rintro (k | c) <;> rfl

set_option maxHeartbeats 1600000 in
/-- **Symmetry of `p ⊗ q`, joints at the level of `A` (proved; corollary of the core).** -/
theorem infra_612_tied_symm_level_joints
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (j₁ j₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : q.idx ⊕ p.idx ≃ j₂.idx)
    (h₁ : IsProductTied p q j₁ e₁) (h₂ : IsProductTied q p j₂ e₂)
    (hj₁ : j₁.ν = μ) (hj₂ : j₂.ν = μ) :
    SameGaloisType j₁ j₂ e₁.symm (e₂.symm.trans (Equiv.sumComm _ _)) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hpqμ : #(p.idx ⊕ q.idx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) (hpσ.trans_lt hσlt) (hqσ.trans_lt hσlt)
  have hqpμ : #(q.idx ⊕ p.idx) < μ :=
    (Cardinal.mk_congr (Equiv.sumComm _ _)).symm.trans_lt hpqμ
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
  exact infra_612_tied_symm_core P σ hσ hμ hrec hσμ p q hνp hνq hpσ hqσ j₁ j₂ e₁ e₂ x₁ x₂
    ex₁ ex₂ hS₁ hS₂ y₁ y₂ ey₁ ey₂ hT₁ hT₂
    (fun Y hβ => infra_612_dEq_of_sameGalois hJ'₁ Y hpqμ hβ)
    (fun Y hβ => infra_612_dEq_of_sameGalois hJ'₂ Y hqpμ hβ) hj₁ hj₂

/-- **Symmetry of `p ⊗ q` for the actual `μ`-types (proved, cycle 93).** Joints `j₁, j₂` at ANY
eligible levels; any level-`μ` copies `j'₁, j'₂` (same Galois type, `j'_k.ν = μ`) have one Galois
type up to the coordinate swap. This is Prop 6.12 "Binary products are symmetric" for the actual
`μ`-types of Cor 6.7. -/
theorem infra_612_tied_symm_copies
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (j₁ j₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : q.idx ⊕ p.idx ≃ j₂.idx)
    (h₁ : IsProductTied p q j₁ e₁) (h₂ : IsProductTied q p j₂ e₂)
    (j'₁ j'₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (r₁ : j'₁.idx ≃ j₁.idx) (r₂ : j'₂.idx ≃ j₂.idx)
    (hR₁ : SameGaloisType j₁ j'₁ (Equiv.refl j₁.idx) r₁)
    (hR₂ : SameGaloisType j₂ j'₂ (Equiv.refl j₂.idx) r₂)
    (hj'₁ : j'₁.ν = μ) (hj'₂ : j'₂.ν = μ) :
    SameGaloisType j'₁ j'₂ (r₁.trans e₁.symm)
      ((r₂.trans e₂.symm).trans (Equiv.sumComm _ _)) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hpqμ : #(p.idx ⊕ q.idx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) (hpσ.trans_lt hσlt) (hqσ.trans_lt hσlt)
  have hqpμ : #(q.idx ⊕ p.idx) < μ :=
    (Cardinal.mk_congr (Equiv.sumComm _ _)).symm.trans_lt hpqμ
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
  have h := infra_612_tied_symm_core P σ hσ hμ hrec hσμ p q hνp hνq hpσ hqσ j'₁ j'₂
    (r₁.trans e₁.symm).symm (r₂.trans e₂.symm).symm x₁ x₂
    ex₁ ex₂ hS₁ hS₂ y₁ y₂ ey₁ ey₂ hT₁ hT₂ ?_ ?_ hj'₁ hj'₂
  · simpa [Equiv.symm_symm] using h
  · intro β Y hβ
    rw [Equiv.symm_symm]
    exact P.scheme.diagram_trans _ _ _ _ _ _
      (P.scheme.diagram_symm _ _ _ _ (infra_612_dEq_of_sameGalois hR'₁ Y hpqμ hβ))
      (infra_612_dEq_of_sameGalois hJ'₁ Y hpqμ hβ)
  · intro β Y hβ
    rw [Equiv.symm_symm]
    exact P.scheme.diagram_trans _ _ _ _ _ _
      (P.scheme.diagram_symm _ _ _ _ (infra_612_dEq_of_sameGalois hR'₂ Y hqpμ hβ))
      (infra_612_dEq_of_sameGalois hJ'₂ Y hqpμ hβ)

set_option maxHeartbeats 1600000 in
/-- **Product entry (proved).** For a tied product `(x, y)` of `p` and `q` over a base `A₀`
(any eligible level), sequences `a` for `p` and `b` for `q`, and a test list `Y` from `A₀`:
off a set of at most `|p| + |Y| + ℵ₀` columns `j`, every row `i` that is good for the query
`bⱼ ⌢ Y` makes the joint `(x, y, Y)` agree with the array entry `D(aᵢ, bⱼ, Y)` (English
Proposition 6.12, first-realize-`x` order). -/
theorem infra_612_product_entry
    {P : SingleModelData K} {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {A : P.scheme.Object ν hν}
    (p q : TupleOver K oneVertexShape P.scheme hν A)
    (x : TupleOver K oneVertexShape P.scheme hν A) (ex : p.idx ≃ x.idx)
    (hS : SameGaloisType p x ex (Equiv.refl x.idx))
    (y : TupleOver K oneVertexShape P.scheme x.hν x.host) (ey : q.idx ≃ y.idx)
    (hT : IsTiedFreeMixed x.incl q y ey)
    (a : ApproximationSequence p) (b : ApproximationSequence q)
    {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (hpν : #p.idx < ν) (hpβν : #(p.idx ⊕ β) < ν) (hqβν : #(q.idx ⊕ β) < ν)
    (hpβb : #(p.idx ⊕ β) ≤ b.τ) (hblong : b.τ + ℵ₀ < #b.κIndex) :
    ∃ C : Set b.κIndex, #C ≤ #(p.idx ⊕ β) + ℵ₀ ∧ ∀ j, j ∉ C → ∀ i,
      P.scheme.DiagramEq (X := p.host) (Y := A)
        (typeJoint (p := p) (Sum.elim (b.family j) Y))
        (seqJoint (a.family i) (Sum.elim (b.family j) Y)) →
      P.scheme.DiagramEq (X := y.host) (Y := A)
        (alignJoint (Equiv.sumCongr ex ey).symm (typeJoint (p := x.join y) Y))
        (fun t => seqJoint (a.family i) (Sum.elim (b.family j) Y) (Equiv.sumAssoc _ _ _ t)) := by
  classical
  have hS' : SameGaloisType p x (Equiv.refl p.idx) ex.symm := by
    have h := infra_612_sameGalois_trans_equiv hS ex.symm
    rwa [Equiv.self_trans_symm, Equiv.refl_trans] at h
  let W : p.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem x.hν x.host) :=
    fun t => typeJoint (p := x) Y (Equiv.sumCongr ex (Equiv.refl β) t)
  obtain ⟨Z0, hZ0⟩ :=
    infra_78_move_query_mixed x.incl x.incl_arrow (infra_612_le_nu x) b W hpβν
  have T := hT b W Z0 hblong hpβb hpβν hZ0
  refine ⟨{j | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
    (typeJoint (p := q) Z0) (seqJoint (b.family j) Z0)}, b.few_exceptions Z0 hpβb, ?_⟩
  intro j hj i Gij
  have Fj : P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q) Z0) (seqJoint (b.family j) Z0) := not_not.1 hj
  have C1 := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ T)
    (P.scheme.diagram_trans _ _ _ _ _ _ Fj (hZ0 j))
  have D₁ := infra_612_dEq_of_sameGalois (P := P) hS' (Sum.elim (b.family j) Y) hpν hqβν
  have C1' := infra_612_dEq_transport C1 (infra_612_swap3 p.idx q.idx β)
    (xs' := fun s => infra_612_anchored ey y.incl y.val W (infra_612_swap3 p.idx q.idx β s))
    (ys' := alignJoint ex.symm (typeJoint (p := x) (Sum.elim (b.family j) Y)))
    (fun _ => rfl) (by rintro (k | l | c) <;> rfl)
  have G1' := infra_612_dEq_transport Gij (Equiv.refl _)
    (xs' := alignJoint (Equiv.refl p.idx) (typeJoint (p := p) (Sum.elim (b.family j) Y)))
    (ys' := seqJoint (a.family i) (Sum.elim (b.family j) Y))
    (by rintro (k | l | c) <;> rfl) (fun _ => rfl)
  have fin1 := P.scheme.diagram_trans _ _ _ _ _ _ C1'
    (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ D₁) G1')
  exact infra_612_dEq_transport fin1 (Equiv.sumAssoc p.idx q.idx β)
    (by rintro ((k | l) | c) <;> rfl) (fun _ => rfl)


set_option maxHeartbeats 3200000 in
/-- **Base change `(p ⊗ q)^B = p_B ⊗ q^B`, joints at their base levels (proved).** For
`f : A → B` from the level `μ` of `A` to a closed level `μ' ≥ μ`, a tied product `joint` of
`p, q` over `A` with `joint` at `μ`, tied free lifts `pB, qB, jB` along `f`, and a tied product
`jB'` of `pB, qB` over `B`, with `jB, jB'` at `μ'`: `jB` and `jB'` have one Galois type.
English proof (Proposition 6.12, formula (4)): sequences `a` for `p`, `b` for `q` (pushed to
`B` by `infra_612_pushSeq`) and `K` for `p ⊗ q`; a test list `Y` in `B` is moved into `A` over
all three; both sides are an entry of the array `D(aᵢ, bⱼ, ·)` (`infra_612_product_entry` over
`A` and over `B`), identified by the move. Theorem 6.6 testing at `μ'` closes. -/
theorem infra_612_tied_base_change_level_joints
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    {μ' : Cardinal.{u}} (hμ' : μ' ∈ P.eligible)
    (hrec' : μ' ∈ recursionClosedLevels P σ) (hσμ' : Order.succ σ ≤ μ') (hμμ' : μ ≤ μ')
    (B : P.scheme.Object μ' hμ')
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ' B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (joint : TupleOver K oneVertexShape P.scheme hμ A) (e : p.idx ⊕ q.idx ≃ joint.idx)
    (pB qB jB jB' : TupleOver K oneVertexShape P.scheme hμ' B)
    (eP : p.idx ≃ pB.idx) (eQ : q.idx ≃ qB.idx) (eJ : joint.idx ≃ jB.idx)
    (e' : pB.idx ⊕ qB.idx ≃ jB'.idx)
    (hprod : IsProductTied p q joint e)
    (hP : IsTiedFreeMixed f p pB eP) (hQ : IsTiedFreeMixed f q qB eQ)
    (hJ : IsTiedFreeMixed f joint jB eJ)
    (hprodB : IsProductTied pB qB jB' e')
    (hjν : joint.ν = μ) (hjB : jB.ν = μ') (hjB' : jB'.ν = μ') :
    SameGaloisType jB jB' (eJ.symm.trans e.symm)
      (e'.symm.trans (Equiv.sumCongr eP.symm eQ.symm)) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hσlt' : σ < μ' := (Order.lt_succ σ).trans_le hσμ'
  have hpμ : #p.idx < μ := hpσ.trans_lt hσlt
  have hqμ : #q.idx < μ := hqσ.trans_lt hσlt
  have hpqσ : #(p.idx ⊕ q.idx) ≤ σ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hσ hpσ hqσ
  have hpqμ : #(p.idx ⊕ q.idx) < μ := hpqσ.trans_lt hσlt
  have hjσ : #joint.idx ≤ σ := (Cardinal.mk_congr e).symm.trans_le hpqσ
  have hjBσ : #jB.idx ≤ σ := (Cardinal.mk_congr (eJ.symm.trans e.symm)).trans_le hpqσ
  have hpqBμ' : #(pB.idx ⊕ qB.idx) < μ' :=
    (Cardinal.mk_congr (Equiv.sumCongr eP eQ)).symm.trans_lt (hpqμ.trans_le hμμ')
  obtain ⟨x, ex, hS, y, ey, hT, hJ0⟩ := hprod
  obtain ⟨xB, exB, hSB, yB, eyB, hTB, hJB0⟩ := hprodB
  have hJ' : SameGaloisType joint (x.join y) e.symm (Equiv.sumCongr ex ey).symm := by
    have h := infra_612_sameGalois_trans_equiv hJ0 (Equiv.sumCongr ex ey).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  have hJB' : SameGaloisType jB' (xB.join yB) e'.symm (Equiv.sumCongr exB eyB).symm := by
    have h := infra_612_sameGalois_trans_equiv hJB0 (Equiv.sumCongr exB eyB).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ :=
    infra_73_differing_test P σ hσ hμ' hrec' hσμ' jB jB' (eJ.symm.trans e.symm)
      (e'.symm.trans (Equiv.sumCongr eP.symm eQ.symm)) hjB hjB' hjBσ
      (hjBσ.trans_lt hσlt') hneq
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
  have hallμ : #((p.idx ⊕ q.idx) ⊕ β) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hpqμ hβμ
  have hpβle : #(p.idx ⊕ β) ≤ #((p.idx ⊕ q.idx) ⊕ β) :=
    Cardinal.mk_le_of_injective (f := Sum.map Sum.inl id)
      (Sum.map_injective.mpr ⟨Sum.inl_injective, Function.injective_id⟩)
  have hqβle : #(q.idx ⊕ β) ≤ #((p.idx ⊕ q.idx) ⊕ β) :=
    Cardinal.mk_le_of_injective (f := Sum.map Sum.inr id)
      (Sum.map_injective.mpr ⟨Sum.inr_injective, Function.injective_id⟩)
  have hpBβ : #(pB.idx ⊕ β) = #(p.idx ⊕ β) :=
    (Cardinal.mk_congr (Equiv.sumCongr eP (Equiv.refl β))).symm
  have hqBβ : #(qB.idx ⊕ β) = #(q.idx ⊕ β) :=
    (Cardinal.mk_congr (Equiv.sumCongr eQ (Equiv.refl β))).symm
  have hpBμ' : #pB.idx < μ' := (Cardinal.mk_congr eP).symm.trans_lt (hpμ.trans_le hμμ')
  -- the three sequences in `A`
  obtain ⟨a, haτ, haτμ, halong⟩ :=
    infra_78_exists_seq_ge P σ hσ hμ hrec hσμ p hνp hpσ hallμ
  obtain ⟨b, hbτ, hbτμ, hblong⟩ :=
    infra_78_exists_seq_ge P σ hσ hμ hrec hσμ q hνq hqσ hallμ
  obtain ⟨Kq, hKτ, -, hKlong⟩ :=
    infra_78_exists_seq_ge P σ hσ hμ hrec hσμ joint hjν hjσ hβμ
  -- move the test list `Y` into `A` over all three sequences at once
  let xs : ((a.κIndex × p.idx) ⊕ (b.κIndex × q.idx)) ⊕ (Kq.κIndex × joint.idx) →
      Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    Sum.elim (Sum.elim (fun ij => a.family ij.1 ij.2) (fun ij => b.family ij.1 ij.2))
      (fun ij => Kq.family ij.1 ij.2)
  have hxs : #(((a.κIndex × p.idx) ⊕ (b.κIndex × q.idx)) ⊕ (Kq.κIndex × joint.idx)) < μ := by
    rw [Cardinal.mk_sum, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id,
      Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ)
      (Cardinal.add_lt_of_lt (P.aleph0_le hμ) a.concat_bounded b.concat_bounded)
      Kq.concat_bounded
  obtain ⟨Y0, hY0⟩ := infra_78_move_mixed f hf hμμ' xs Y hxs hβμ
  have hKmove : infra_78_isMoveMixed f Kq Y Y0 := fun k => by
    have h := infra_73_scheme_comp hY0 (fun t : joint.idx ⊕ β => match t with
      | Sum.inl l => Sum.inl (Sum.inr (k, l))
      | Sum.inr c => Sum.inr c)
    exact infra_73_diagramEq_of_eq h (by rintro (l | c) <;> rfl) (by rintro (l | c) <;> rfl)
  -- left side: `jB` is the free lift of `p ⊗ q`
  have LJ := hJ Kq Y Y0 hKlong hKτ hβμ hKmove
  have L1 := infra_612_dEq_transport LJ (Equiv.sumCongr e (Equiv.refl β))
    (xs' := alignJoint e.symm (typeJoint (p := joint) Y0))
    (ys' := alignJoint (eJ.symm.trans e.symm) (typeJoint (p := jB) Y))
    (by rintro (s | c) <;> rfl) (by rintro (s | c) <;> rfl)
  have DJ := infra_612_dEq_of_sameGalois hJ' Y0 hpqμ hβμ
  -- the pushed sequences in `B`
  let aB := infra_612_pushSeq f hf hμμ' p pB eP hP a halong haτμ
  let bB := infra_612_pushSeq f hf hμμ' q qB eQ hQ b hblong hbτμ
  obtain ⟨CA, hCA, hEA⟩ := infra_612_product_entry p q x ex hS y ey hT a b Y0 hpμ hpβμ hqβμ
    (hpβle.trans hbτ) hblong
  obtain ⟨CB, hCB, hEB⟩ := infra_612_product_entry pB qB xB exB hSB yB eyB hTB aB bB Y hpBμ'
    (hpBβ ▸ hpβμ.trans_le hμμ') (hqBβ ▸ hqβμ.trans_le hμμ')
    (hpBβ ▸ hpβle.trans hbτ) hblong
  set E : Cardinal.{u} := #((p.idx ⊕ q.idx) ⊕ β) + aleph0 with hEdef
  have hEinf : aleph0 ≤ E := le_add_self
  have hEb : E < #b.κIndex := (add_le_add hbτ le_rfl).trans_lt hblong
  have hEa : E < #a.κIndex := (add_le_add haτ le_rfl).trans_lt halong
  obtain ⟨j, hjA, hjB⟩ := infra_78_exists_outside_two CA CB hEinf
    (hCA.trans (add_le_add hpβle le_rfl)) (hCB.trans (by rw [hpBβ]; exact add_le_add hpβle le_rfl))
    hEb
  obtain ⟨i, hiA, hiB⟩ := infra_78_exists_outside_two
    {i | ¬ P.scheme.DiagramEq (X := p.host) (Y := A)
      (typeJoint (p := p) (Sum.elim (b.family j) Y0))
      (seqJoint (a.family i) (Sum.elim (b.family j) Y0))}
    {i | ¬ P.scheme.DiagramEq (X := pB.host) (Y := B)
      (typeJoint (p := pB) (Sum.elim (bB.family j) Y))
      (seqJoint (aB.family i) (Sum.elim (bB.family j) Y))} hEinf
    ((a.few_exceptions _ (hqβle.trans haτ)).trans (add_le_add hqβle le_rfl))
    ((aB.few_exceptions _ (hqBβ ▸ hqβle.trans haτ)).trans
      (by rw [hqBβ]; exact add_le_add hqβle le_rfl))
    hEa
  have EA := hEA j hjA i (not_not.1 hiA)
  have EB := hEB j hjB i (not_not.1 hiB)
  -- the move identifies the two array entries
  let π : (p.idx ⊕ q.idx) ⊕ β ≃ (pB.idx ⊕ qB.idx) ⊕ β :=
    Equiv.sumCongr (Equiv.sumCongr eP eQ) (Equiv.refl β)
  have Mv : P.scheme.DiagramEq (X := A) (Y := B)
      (fun t => seqJoint (a.family i) (Sum.elim (b.family j) Y0) (Equiv.sumAssoc _ _ _ t))
      (fun t => seqJoint (aB.family i) (Sum.elim (bB.family j) Y)
        (Equiv.sumAssoc _ _ _ (π t))) := by
    have h := infra_73_scheme_comp hY0 (fun t : (p.idx ⊕ q.idx) ⊕ β => match t with
      | Sum.inl (Sum.inl k) => Sum.inl (Sum.inl (Sum.inl (i, k)))
      | Sum.inl (Sum.inr l) => Sum.inl (Sum.inl (Sum.inr (j, l)))
      | Sum.inr c => Sum.inr c)
    refine infra_73_diagramEq_of_eq h (by rintro ((k | l) | c) <;> rfl) ?_
    rintro ((k | l) | c)
    · exact congrArg (fun k' => (⟨(a.family i k').1, f.onVertex (a.family i k').1
        (a.family i k').2⟩ : Occurrence K oneVertexShape (P.scheme.asSystem hμ' B)))
        (eP.symm_apply_apply k).symm
    · exact congrArg (fun l' => (⟨(b.family j l').1, f.onVertex (b.family j l').1
        (b.family j l').2⟩ : Occurrence K oneVertexShape (P.scheme.asSystem hμ' B)))
        (eQ.symm_apply_apply l).symm
    · rfl
  have EB' := infra_612_dEq_transport EB π
    (xs' := fun t => alignJoint (Equiv.sumCongr exB eyB).symm
      (typeJoint (p := xB.join yB) Y) (π t))
    (ys' := fun t => seqJoint (aB.family i) (Sum.elim (bB.family j) Y)
      (Equiv.sumAssoc _ _ _ (π t)))
    (fun _ => rfl) (fun _ => rfl)
  have DJB := infra_612_dEq_of_sameGalois hJB' Y hpqBμ' (hβμ.trans_le hμμ')
  have DJB' := infra_612_dEq_transport (P.scheme.diagram_symm _ _ _ _ DJB) π
    (xs' := fun t => alignJoint (Equiv.sumCongr exB eyB).symm
      (typeJoint (p := xB.join yB) Y) (π t))
    (ys' := alignJoint (e'.symm.trans (Equiv.sumCongr eP.symm eQ.symm)) (typeJoint (p := jB') Y))
    (fun _ => rfl) (by rintro ((k | l) | c) <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ L1)
    (P.scheme.diagram_trans _ _ _ _ _ _ DJ
      (P.scheme.diagram_trans _ _ _ _ _ _ EA
        (P.scheme.diagram_trans _ _ _ _ _ _ Mv
          (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ EB') DJB'))))


/-- A set of size `≤ c` and an `ι`-indexed family of sets of size `≤ c` (with `c ≤ #ι`
infinite) do not cover a type of size `> #ι`. -/
theorem infra_612_exists_outside_union {κ ι : Type u} (S : Set κ) (F : ι → Set κ)
    {c : Cardinal.{u}} (hc : ℵ₀ ≤ c) (hcι : c ≤ #ι) (hS : #S ≤ c) (hF : ∀ i, #(F i) ≤ c)
    (hlt : #ι < #κ) : ∃ k, k ∉ S ∧ ∀ i, k ∉ F i := by
  classical
  by_contra hcon
  push_neg at hcon
  have hι : ℵ₀ ≤ #ι := hc.trans hcι
  have hcov : (Set.univ : Set κ) ⊆ S ∪ ⋃ i, F i := fun k _ => by
    by_cases hk : k ∈ S
    · exact Or.inl hk
    · obtain ⟨i, hi⟩ := hcon k hk
      exact Or.inr (Set.mem_iUnion.2 ⟨i, hi⟩)
  have hU : #(⋃ i, F i) ≤ #ι := by
    refine (Cardinal.mk_iUnion_le _).trans ?_
    calc #ι * ⨆ i, #(F i) ≤ #ι * #ι :=
          mul_le_mul' le_rfl (ciSup_le' fun i => (hF i).trans hcι)
      _ = #ι := Cardinal.mul_eq_self hι
  have h1 : #κ ≤ #ι :=
    calc #κ = #(Set.univ : Set κ) := Cardinal.mk_univ.symm
      _ ≤ #(S ∪ ⋃ i, F i : Set κ) := Cardinal.mk_le_mk_of_subset hcov
      _ ≤ #S + #(⋃ i, F i) := Cardinal.mk_union_le _ _
      _ ≤ #ι + #ι := add_le_add (hS.trans hcι) hU
      _ = #ι := Cardinal.add_eq_self hι
  exact absurd hlt (not_lt.2 h1)

/-- Precompose a diagram equality with any reindexing, with pointwise identifications. -/
theorem infra_612_dEq_comp {P : SingleModelData K} {μ ν : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {X : P.scheme.Object μ hμ} {Y : P.scheme.Object ν hν} {α γ : Type u}
    {xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ X)}
    {ys : α → Occurrence K oneVertexShape (P.scheme.asSystem hν Y)}
    (h : P.scheme.DiagramEq (X := X) (Y := Y) xs ys) (ι : γ → α)
    {xs' : γ → Occurrence K oneVertexShape (P.scheme.asSystem hμ X)}
    {ys' : γ → Occurrence K oneVertexShape (P.scheme.asSystem hν Y)}
    (hx : ∀ c, xs' c = xs (ι c)) (hy : ∀ c, ys' c = ys (ι c)) :
    P.scheme.DiagramEq (X := X) (Y := Y) xs' ys' :=
  infra_73_diagramEq_of_eq (infra_73_scheme_comp h ι) (fun c => (hx c).symm)
    (fun c => (hy c).symm)

set_option maxHeartbeats 6400000 in
/-- **Associativity `(p ⊗ q) ⊗ r = p ⊗ (q ⊗ r)`, binary factors and joints at the level of `A`
(proved).** Realizations and free lifts at any eligible levels. Both triple products agree with
one entry `D(aᵢ, bⱼ, c_k, Y)` of the three-dimensional array of approximation sequences `a, b, c`
for `p, q, r` (with auxiliary sequences `K, L` for `p ⊗ q`, `q ⊗ r`): `(p ⊗ q) ⊗ r` is read
`k`, then `j`, then `i` (`infra_612_product_entry` twice); `p ⊗ (q ⊗ r)` is read `i`, then `k`,
then `j`. The sequences `b, c, L` are longer than `a`, so a common good triple exists. Theorem
6.6 testing closes. -/
theorem infra_612_tied_assoc_level_joints
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q r : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hνr : r.ν = μ)
    (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ) (hrσ : #r.idx ≤ σ)
    (pq qr j₁ j₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (epq : p.idx ⊕ q.idx ≃ pq.idx) (eqr : q.idx ⊕ r.idx ≃ qr.idx)
    (e₁ : pq.idx ⊕ r.idx ≃ j₁.idx) (e₂ : p.idx ⊕ qr.idx ≃ j₂.idx)
    (hPQ : IsProductTied p q pq epq) (h₁ : IsProductTied pq r j₁ e₁)
    (hQR : IsProductTied q r qr eqr) (h₂ : IsProductTied p qr j₂ e₂)
    (hνpq : pq.ν = μ) (hνqr : qr.ν = μ) (hj₁ : j₁.ν = μ) (hj₂ : j₂.ν = μ) :
    SameGaloisType j₁ j₂
      (e₁.symm.trans ((Equiv.sumCongr epq.symm (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _)))
      (e₂.symm.trans (Equiv.sumCongr (Equiv.refl _) eqr.symm)) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hsum2 : ∀ {U V : Type u}, #U ≤ σ → #V ≤ σ → #(U ⊕ V) ≤ σ := fun hU hV => by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hσ hU hV
  have hpqσ : #pq.idx ≤ σ := (Cardinal.mk_congr epq).symm.trans_le (hsum2 hpσ hqσ)
  have hqrσ : #qr.idx ≤ σ := (Cardinal.mk_congr eqr).symm.trans_le (hsum2 hqσ hrσ)
  have hj₁σ : #j₁.idx ≤ σ := (Cardinal.mk_congr e₁).symm.trans_le (hsum2 hpqσ hrσ)
  obtain ⟨x, ex, hSx, y, ey, hTy, hJpq⟩ := hPQ
  obtain ⟨X1, eX1, hSX1, Y1, eY1, hTY1, hJ1⟩ := h₁
  obtain ⟨x3, ex3, hSx3, y3, ey3, hTy3, hJqr⟩ := hQR
  obtain ⟨x2, ex2, hSx2, y2, ey2, hTy2, hJ2⟩ := h₂
  have hJpq' : SameGaloisType _ (x.join y) epq.symm (Equiv.sumCongr ex ey).symm := by
    have h := infra_612_sameGalois_trans_equiv hJpq (Equiv.sumCongr ex ey).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  have hJ1' : SameGaloisType _ (X1.join Y1) e₁.symm (Equiv.sumCongr eX1 eY1).symm := by
    have h := infra_612_sameGalois_trans_equiv hJ1 (Equiv.sumCongr eX1 eY1).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  have hJqr' : SameGaloisType _ (x3.join y3) eqr.symm (Equiv.sumCongr ex3 ey3).symm := by
    have h := infra_612_sameGalois_trans_equiv hJqr (Equiv.sumCongr ex3 ey3).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  have hJ2' : SameGaloisType _ (x2.join y2) e₂.symm (Equiv.sumCongr ex2 ey2).symm := by
    have h := infra_612_sameGalois_trans_equiv hJ2 (Equiv.sumCongr ex2 ey2).symm
    rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
    exact h
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ :=
    infra_73_differing_test P σ hσ hμ hrec hσμ j₁ j₂
      (e₁.symm.trans ((Equiv.sumCongr epq.symm (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _)))
      (e₂.symm.trans (Equiv.sumCongr (Equiv.refl _) eqr.symm)) hj₁ hj₂ hj₁σ
      (hj₁σ.trans_lt hσlt) hneq
  apply hnot
  have hβμ : #β < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    exact hβ.trans_lt (add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ))
  -- the uniform query bound `s = σ + |β|`
  set s : Cardinal.{u} := σ + #β with hsdef
  have hsμ : s < μ := add_lt_of_lt (P.aleph0_le hμ) hσlt hβμ
  have hβs : #β ≤ s := le_add_self
  have hsum : ∀ {U V : Type u}, #U ≤ σ → #V ≤ s → #(U ⊕ V) ≤ s := fun hU hV => by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    calc #_ + #_ ≤ σ + (σ + #β) := add_le_add hU hV
      _ = σ + #β := by rw [← add_assoc, Cardinal.add_eq_self hσ]
  have hlt : ∀ {U : Type u}, #U ≤ s → #U < μ := fun h => h.trans_lt hsμ
  have hpμ : #p.idx < μ := hpσ.trans_lt hσlt
  have hqμ : #q.idx < μ := hqσ.trans_lt hσlt
  have hpqμ : #pq.idx < μ := hpqσ.trans_lt hσlt
  set E : Cardinal.{u} := s + aleph0 with hEdef
  have hEinf : aleph0 ≤ E := le_add_self
  have hE : ∀ {U : Type u}, #U ≤ s → #U + aleph0 ≤ E := fun h => add_le_add h le_rfl
  -- sequences: `a` short; `K` for `p ⊗ q`; `b, c, L` longer than `a`
  obtain ⟨a, haτ, haτμ, halong, haμ⟩ :=
    infra_612_exists_seq_small P σ hσ hμ hrec hσμ p hνp hpσ hsμ
  obtain ⟨Kq, hKτ, -, hKlong⟩ :=
    infra_78_exists_seq_ge P σ hσ hμ hrec hσμ pq hνpq hpqσ hsμ
  have hmax : max s #a.κIndex < μ := max_lt hsμ haμ
  obtain ⟨b, hbτ, -, hblong⟩ := infra_78_exists_seq_ge P σ hσ hμ hrec hσμ q hνq hqσ hmax
  obtain ⟨c, hcτ, -, hclong⟩ := infra_78_exists_seq_ge P σ hσ hμ hrec hσμ r hνr hrσ hmax
  obtain ⟨L, hLτ, -, hLlong⟩ :=
    infra_78_exists_seq_ge P σ hσ hμ hrec hσμ qr hνqr hqrσ hmax
  have hsb : s ≤ b.τ := (le_max_left _ _).trans hbτ
  have hsc : s ≤ c.τ := (le_max_left _ _).trans hcτ
  have hsL : s ≤ L.τ := (le_max_left _ _).trans hLτ
  have hEa : E < #a.κIndex := (add_le_add haτ le_rfl).trans_lt halong
  have hEK : E < #Kq.κIndex := (add_le_add hKτ le_rfl).trans_lt hKlong
  have hlong : ∀ {τ' : Cardinal.{u}} {κ' : Type u}, max s #a.κIndex ≤ τ' →
      τ' + aleph0 < #κ' → #a.κIndex < #κ' := fun h1 h2 =>
    ((le_max_right _ _).trans (h1.trans le_self_add)).trans_lt h2
  have hab : #a.κIndex < #b.κIndex := hlong hbτ hblong
  have hac : #a.κIndex < #c.κIndex := hlong hcτ hclong
  have haL : #a.κIndex < #L.κIndex := hlong hLτ hLlong
  have hEa' : E ≤ #a.κIndex := hEa.le
  -- the test lists `Z'_k = c_k ⌢ Y` and `Z''_i = a_i ⌢ Y`
  let Z' : c.κIndex → r.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun k => Sum.elim (c.family k) Y
  let Z'' : a.κIndex → p.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun i => Sum.elim (a.family i) Y
  have hrβ : #(r.idx ⊕ β) ≤ s := hsum hrσ hβs
  have hpβ : #(p.idx ⊕ β) ≤ s := hsum hpσ hβs
  -- `(p ⊗ q) ⊗ r`: columns `k` of `c`
  obtain ⟨C1, hC1, hE1⟩ := infra_612_product_entry pq r X1 eX1 hSX1 Y1 eY1 hTY1 Kq c Y hpqμ
    (hlt (hsum hpqσ hβs)) (hlt hrβ) ((hsum hpqσ hβs).trans hsc) hclong
  -- `q ⊗ r` inside `p ⊗ (q ⊗ r)`: for each row `i`, columns `k` of `c`
  have h4 : ∀ i, ∃ C : Set c.κIndex, #C ≤ #(q.idx ⊕ (p.idx ⊕ β)) + ℵ₀ ∧ ∀ k, k ∉ C → ∀ j,
      P.scheme.DiagramEq (X := q.host) (Y := A)
        (typeJoint (p := q) (Sum.elim (c.family k) (Z'' i)))
        (seqJoint (b.family j) (Sum.elim (c.family k) (Z'' i))) →
      P.scheme.DiagramEq (X := y3.host) (Y := A)
        (alignJoint (Equiv.sumCongr ex3 ey3).symm (typeJoint (p := x3.join y3) (Z'' i)))
        (fun t => seqJoint (b.family j) (Sum.elim (c.family k) (Z'' i))
          (Equiv.sumAssoc _ _ _ t)) := fun i =>
    infra_612_product_entry q r x3 ex3 hSx3 y3 ey3 hTy3 b c (Z'' i) hqμ
      (hlt (hsum hqσ hpβ)) (hlt (hsum hrσ hpβ)) ((hsum hqσ hpβ).trans hsc) hclong
  choose C4 hC4 hE4 using h4
  obtain ⟨k, hk1, hk4⟩ := infra_612_exists_outside_union C1 C4 hEinf hEa'
    (hC1.trans (hE (hsum hpqσ hβs))) (fun i => (hC4 i).trans (hE (hsum hqσ hpβ))) hac
  -- `p ⊗ q` on the list `Z'_k`: columns `j` of `b`
  obtain ⟨C2, hC2, hE2⟩ := infra_612_product_entry p q x ex hSx y ey hTy a b (Z' k) hpμ
    (hlt (hsum hpσ hrβ)) (hlt (hsum hqσ hrβ)) ((hsum hpσ hrβ).trans hsb) hblong
  obtain ⟨j, hj2, hjb⟩ := infra_612_exists_outside_union C2
    (fun i => {j | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q) (Sum.elim (c.family k) (Z'' i)))
      (seqJoint (b.family j) (Sum.elim (c.family k) (Z'' i)))}) hEinf hEa'
    (hC2.trans (hE (hsum hpσ hrβ)))
    (fun i => (b.few_exceptions _ ((hsum hrσ hpβ).trans hsb)).trans (hE (hsum hrσ hpβ))) hab
  -- `p ⊗ (q ⊗ r)`: columns `n` of `L`
  obtain ⟨C3, hC3, hE3⟩ := infra_612_product_entry p qr x2 ex2 hSx2 y2 ey2 hTy2 a L Y hpμ
    (hlt hpβ) (hlt (hsum hqrσ hβs)) (hpβ.trans hsL) hLlong
  obtain ⟨n, hn3, hnX⟩ := infra_612_exists_outside_union C3
    (fun i => {n | ¬ P.scheme.DiagramEq (X := qr.host) (Y := A)
      (typeJoint (p := qr) (Z'' i)) (seqJoint (L.family n) (Z'' i))}) hEinf hEa'
    (hC3.trans (hE hpβ)) (fun i => (L.few_exceptions _ (hpβ.trans hsL)).trans (hE hpβ)) haL
  -- the row `i`
  obtain ⟨i, hiA, hiB⟩ := infra_78_exists_outside_two
    {i | ¬ P.scheme.DiagramEq (X := p.host) (Y := A)
      (typeJoint (p := p) (Sum.elim (b.family j) (Z' k)))
      (seqJoint (a.family i) (Sum.elim (b.family j) (Z' k)))}
    {i | ¬ P.scheme.DiagramEq (X := p.host) (Y := A)
      (typeJoint (p := p) (Sum.elim (L.family n) Y))
      (seqJoint (a.family i) (Sum.elim (L.family n) Y))} hEinf
    ((a.few_exceptions _ ((hsum hqσ hrβ).trans haτ)).trans (hE (hsum hqσ hrβ)))
    ((a.few_exceptions _ ((hsum hqrσ hβs).trans haτ)).trans (hE (hsum hqrσ hβs))) hEa
  -- the row `m` of `K`
  obtain ⟨m, hm, -⟩ := infra_78_exists_outside_two
    {m | ¬ P.scheme.DiagramEq (X := pq.host) (Y := A)
      (typeJoint (p := pq) (Z' k)) (seqJoint (Kq.family m) (Z' k))}
    {m | ¬ P.scheme.DiagramEq (X := pq.host) (Y := A)
      (typeJoint (p := pq) (Z' k)) (seqJoint (Kq.family m) (Z' k))} hEinf
    ((Kq.few_exceptions _ (hrβ.trans hKτ)).trans (hE hrβ))
    ((Kq.few_exceptions _ (hrβ.trans hKτ)).trans (hE hrβ)) hEK
  have Gm : P.scheme.DiagramEq (X := pq.host) (Y := A)
      (typeJoint (p := pq) (Z' k)) (seqJoint (Kq.family m) (Z' k)) := not_not.1 hm
  have E1 := hE1 k hk1 m Gm
  have E2 := hE2 j hj2 i (not_not.1 hiA)
  have E3 := hE3 n hn3 i (not_not.1 hiB)
  have Xn : P.scheme.DiagramEq (X := qr.host) (Y := A)
      (typeJoint (p := qr) (Z'' i)) (seqJoint (L.family n) (Z'' i)) := not_not.1 (hnX i)
  have E4 := hE4 i k (hk4 i) j (not_not.1 (hjb i))
  -- the common entry
  let M : p.idx ⊕ (q.idx ⊕ (r.idx ⊕ β)) → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    seqJoint (a.family i) (Sum.elim (b.family j) (Sum.elim (c.family k) Y))
  let Φ : (p.idx ⊕ (q.idx ⊕ r.idx)) ⊕ β → p.idx ⊕ (q.idx ⊕ (r.idx ⊕ β)) := fun t =>
    match t with
    | Sum.inl (Sum.inl u) => Sum.inl u
    | Sum.inl (Sum.inr (Sum.inl u)) => Sum.inr (Sum.inl u)
    | Sum.inl (Sum.inr (Sum.inr u)) => Sum.inr (Sum.inr (Sum.inl u))
    | Sum.inr d => Sum.inr (Sum.inr (Sum.inr d))
  -- side 1: `(p ⊗ q) ⊗ r`
  let ψ : (p.idx ⊕ (q.idx ⊕ r.idx)) ⊕ β → (pq.idx ⊕ r.idx) ⊕ β := fun t =>
    match t with
    | Sum.inl (Sum.inl u) => Sum.inl (Sum.inl (epq (Sum.inl u)))
    | Sum.inl (Sum.inr (Sum.inl u)) => Sum.inl (Sum.inl (epq (Sum.inr u)))
    | Sum.inl (Sum.inr (Sum.inr u)) => Sum.inl (Sum.inr u)
    | Sum.inr d => Sum.inr d
  let φ : (p.idx ⊕ (q.idx ⊕ r.idx)) ⊕ β → (p.idx ⊕ q.idx) ⊕ (r.idx ⊕ β) := fun t =>
    match t with
    | Sum.inl (Sum.inl u) => Sum.inl (Sum.inl u)
    | Sum.inl (Sum.inr (Sum.inl u)) => Sum.inl (Sum.inr u)
    | Sum.inl (Sum.inr (Sum.inr u)) => Sum.inr (Sum.inl u)
    | Sum.inr d => Sum.inr (Sum.inr d)
  have DJ1 := infra_612_dEq_of_sameGalois hJ1' Y ((hsum2 hpqσ hrσ).trans_lt hσlt) hβμ
  have Gm' := infra_612_dEq_comp (P.scheme.diagram_symm _ _ _ _ Gm)
    (Equiv.sumAssoc pq.idx r.idx β)
    (xs' := fun t => seqJoint (Kq.family m) (Z' k) (Equiv.sumAssoc _ _ _ t))
    (ys' := fun t => typeJoint (p := pq) (Z' k) (Equiv.sumAssoc _ _ _ t))
    (fun _ => rfl) (fun _ => rfl)
  have A1 := P.scheme.diagram_trans _ _ _ _ _ _ DJ1 (P.scheme.diagram_trans _ _ _ _ _ _ E1 Gm')
  have A1' := infra_612_dEq_comp A1 ψ
    (xs' := alignJoint (e₁.symm.trans ((Equiv.sumCongr epq.symm (Equiv.refl _)).trans
      (Equiv.sumAssoc _ _ _))) (typeJoint (p := j₁) Y))
    (ys' := fun t => typeJoint (p := pq) (Z' k) (Equiv.sumAssoc _ _ _ (ψ t)))
    (by rintro ((u | u | u) | d) <;> rfl) (fun _ => rfl)
  have DJpq := infra_612_dEq_of_sameGalois hJpq' (Z' k) ((hsum2 hpσ hqσ).trans_lt hσlt)
    (hlt hrβ)
  have D' := infra_612_dEq_comp DJpq φ
    (xs' := fun t => typeJoint (p := pq) (Z' k) (Equiv.sumAssoc _ _ _ (ψ t)))
    (ys' := fun t => alignJoint (Equiv.sumCongr ex ey).symm
      (typeJoint (p := x.join y) (Z' k)) (φ t))
    (by rintro ((u | u | u) | d) <;> rfl) (fun _ => rfl)
  have E2' := infra_612_dEq_comp E2 φ
    (xs' := fun t => alignJoint (Equiv.sumCongr ex ey).symm
      (typeJoint (p := x.join y) (Z' k)) (φ t))
    (ys' := fun t => M (Φ t))
    (fun _ => rfl) (by rintro ((u | u | u) | d) <;> rfl)
  have S1 := P.scheme.diagram_trans _ _ _ _ _ _ A1'
    (P.scheme.diagram_trans _ _ _ _ _ _ D' E2')
  -- side 2: `p ⊗ (q ⊗ r)`
  let χ : (p.idx ⊕ (q.idx ⊕ r.idx)) ⊕ β → (p.idx ⊕ qr.idx) ⊕ β := fun t =>
    match t with
    | Sum.inl (Sum.inl u) => Sum.inl (Sum.inl u)
    | Sum.inl (Sum.inr u) => Sum.inl (Sum.inr (eqr u))
    | Sum.inr d => Sum.inr d
  let ω : (p.idx ⊕ (q.idx ⊕ r.idx)) ⊕ β → qr.idx ⊕ (p.idx ⊕ β) := fun t =>
    match t with
    | Sum.inl (Sum.inl u) => Sum.inr (Sum.inl u)
    | Sum.inl (Sum.inr u) => Sum.inl (eqr u)
    | Sum.inr d => Sum.inr (Sum.inr d)
  let ω' : (p.idx ⊕ (q.idx ⊕ r.idx)) ⊕ β → (q.idx ⊕ r.idx) ⊕ (p.idx ⊕ β) := fun t =>
    match t with
    | Sum.inl (Sum.inl u) => Sum.inr (Sum.inl u)
    | Sum.inl (Sum.inr u) => Sum.inl u
    | Sum.inr d => Sum.inr (Sum.inr d)
  have DJ2 := infra_612_dEq_of_sameGalois hJ2' Y ((hsum2 hpσ hqrσ).trans_lt hσlt) hβμ
  have T1 := infra_612_dEq_comp (P.scheme.diagram_trans _ _ _ _ _ _ DJ2 E3) χ
    (xs' := alignJoint (e₂.symm.trans (Equiv.sumCongr (Equiv.refl _) eqr.symm))
      (typeJoint (p := j₂) Y))
    (ys' := fun t => seqJoint (a.family i) (Sum.elim (L.family n) Y)
      (Equiv.sumAssoc _ _ _ (χ t)))
    (by rintro ((u | u) | d) <;> rfl) (fun _ => rfl)
  have T3 := infra_612_dEq_comp (P.scheme.diagram_symm _ _ _ _ Xn) ω
    (xs' := fun t => seqJoint (a.family i) (Sum.elim (L.family n) Y)
      (Equiv.sumAssoc _ _ _ (χ t)))
    (ys' := fun t => typeJoint (p := qr) (Z'' i) (ω t))
    (by rintro ((u | u) | d) <;> rfl) (fun _ => rfl)
  have DJqr := infra_612_dEq_of_sameGalois hJqr' (Z'' i) ((hsum2 hqσ hrσ).trans_lt hσlt)
    (hlt hpβ)
  have T4 := infra_612_dEq_comp (P.scheme.diagram_trans _ _ _ _ _ _ DJqr E4) ω'
    (xs' := fun t => typeJoint (p := qr) (Z'' i) (ω t))
    (ys' := fun t => M (Φ t))
    (by rintro ((u | u) | d) <;> rfl) (by rintro ((u | u | u) | d) <;> rfl)
  have S2 := P.scheme.diagram_trans _ _ _ _ _ _ T1 (P.scheme.diagram_trans _ _ _ _ _ _ T3 T4)
  exact P.scheme.diagram_trans _ _ _ _ _ _ S1 (P.scheme.diagram_symm _ _ _ _ S2)

/-- **Associativity for the actual `μ`-types (proved, cycle 93 audit).** Prop 6.12: "Finite
products associate". Factors `p, q, r` and the intermediate products `p ⊗ q`, `q ⊗ r` are types
at the level `μ` of `A`; the triple products `j₁ = (p ⊗ q) ⊗ r`, `j₂ = p ⊗ (q ⊗ r)` may be
realized at any eligible level and are compared on any level-`μ` copies (Cor 6.7: "Types of
tuples of length less than ν over A obtained in a larger object are actual ν-types").
Copies are products (`infra_612_isProductTied_copy`); `infra_612_tied_assoc_level_joints`. -/
theorem infra_612_tied_assoc_copies
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q r : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hνr : r.ν = μ)
    (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ) (hrσ : #r.idx ≤ σ)
    (pq qr j₁ j₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (epq : p.idx ⊕ q.idx ≃ pq.idx) (eqr : q.idx ⊕ r.idx ≃ qr.idx)
    (e₁ : pq.idx ⊕ r.idx ≃ j₁.idx) (e₂ : p.idx ⊕ qr.idx ≃ j₂.idx)
    (hPQ : IsProductTied p q pq epq) (h₁ : IsProductTied pq r j₁ e₁)
    (hQR : IsProductTied q r qr eqr) (h₂ : IsProductTied p qr j₂ e₂)
    (hνpq : pq.ν = μ) (hνqr : qr.ν = μ)
    (j'₁ j'₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (r₁ : j'₁.idx ≃ j₁.idx) (r₂ : j'₂.idx ≃ j₂.idx)
    (hR₁ : SameGaloisType j₁ j'₁ (Equiv.refl j₁.idx) r₁)
    (hR₂ : SameGaloisType j₂ j'₂ (Equiv.refl j₂.idx) r₂)
    (hj₁ : j'₁.ν = μ) (hj₂ : j'₂.ν = μ) :
    SameGaloisType j'₁ j'₂
      ((r₁.trans e₁.symm).trans ((Equiv.sumCongr epq.symm (Equiv.refl _)).trans
        (Equiv.sumAssoc _ _ _)))
      ((r₂.trans e₂.symm).trans (Equiv.sumCongr (Equiv.refl _) eqr.symm)) := by
  have hsum2 : ∀ {U V : Type u}, #U ≤ σ → #V ≤ σ → #(U ⊕ V) ≤ σ := fun hU hV => by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hσ hU hV
  have hpqσ : #pq.idx ≤ σ := (Cardinal.mk_congr epq).symm.trans_le (hsum2 hpσ hqσ)
  have hqrσ : #qr.idx ≤ σ := (Cardinal.mk_congr eqr).symm.trans_le (hsum2 hqσ hrσ)
  have h₁' := infra_612_isProductTied_copy P σ hσ hμ hrec hσμ pq r hνpq hνr hpqσ hrσ
    j₁ e₁ h₁ j'₁ r₁ hR₁ hj₁
  have h₂' := infra_612_isProductTied_copy P σ hσ hμ hrec hσμ p qr hνp hνqr hpσ hqrσ
    j₂ e₂ h₂ j'₂ r₂ hR₂ hj₂
  have h := infra_612_tied_assoc_level_joints P σ hσ hμ hrec hσμ p q r hνp hνq hνr hpσ hqσ hrσ
    pq qr j'₁ j'₂ epq eqr _ _ hPQ h₁' hQR h₂' hνpq hνqr hj₁ hj₂
  exact h

/-- **A level copy of a tied free lift is a tied free lift (proved, cycle 93).** If `qB` over `B`
(any eligible level) is a tied free lift of `q` along `f`, and `qB'` is a copy of `qB` at the level
`μ'` of `B`, then `qB'` is a tied free lift of `q` (same majority diagrams, via Theorem 6.6 for the
copy and an index bijection). -/
theorem infra_612_tiedFreeMixed_copy {P : SingleModelData K} {ν μ' : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hμ' : μ' ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ' hμ'}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ' B))
    (q : TupleOver K oneVertexShape P.scheme hν A)
    (qB qB' : TupleOver K oneVertexShape P.scheme hμ' B)
    (eB : q.idx ≃ qB.idx) (r : qB'.idx ≃ qB.idx)
    (hR : SameGaloisType qB qB' (Equiv.refl qB.idx) r)
    (hνμ' : ν ≤ μ') (hq : #qB.idx < μ')
    (h : IsTiedFreeMixed f q qB eB) :
    IsTiedFreeMixed f q qB' (eB.trans r.symm) := by
  intro seq ι Z Z0 h1 h2 h3 hmove
  have D1 := h seq Z Z0 h1 h2 h3 hmove
  have D2 := infra_612_dEq_of_sameGalois hR Z hq (h3.trans_le hνμ')
  have D3 := infra_612_dEq_comp D2 (Sum.map eB id)
    (xs' := infra_612_anchored eB qB.incl qB.val Z)
    (ys' := infra_612_anchored (eB.trans r.symm) qB'.incl qB'.val Z)
    (by rintro (a | b) <;> rfl) (by rintro (a | b) <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ D1 D3

/-- **Base change for the actual types (proved, cycle 93 audit).** Prop 6.12: "Furthermore
(p ⊗ q)^B = p^B ⊗ q^B." The joint `p ⊗ q` is a `μ`-type and the lifts `p^B`, `q^B` are
`μ'`-types (Cor 6.7); the two sides `(p ⊗ q)^B` and `p^B ⊗ q^B` may be realized at any eligible
level and are compared on any level-`μ'` copies. Copies of a tied free lift are tied free lifts
(`infra_612_tiedFreeMixed_copy`), copies of a product are products
(`infra_612_isProductTied_copy`); then `infra_612_tied_base_change_level_joints`. -/
theorem infra_612_tied_base_change_copies
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ) (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    {μ' : Cardinal.{u}} (hμ' : μ' ∈ P.eligible)
    (hrec' : μ' ∈ recursionClosedLevels P σ) (hσμ' : Order.succ σ ≤ μ') (hμμ' : μ ≤ μ')
    (B : P.scheme.Object μ' hμ')
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ' B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (joint : TupleOver K oneVertexShape P.scheme hμ A) (e : p.idx ⊕ q.idx ≃ joint.idx)
    (pB qB jB jB' : TupleOver K oneVertexShape P.scheme hμ' B)
    (eP : p.idx ≃ pB.idx) (eQ : q.idx ≃ qB.idx) (eJ : joint.idx ≃ jB.idx)
    (e' : pB.idx ⊕ qB.idx ≃ jB'.idx)
    (hprod : IsProductTied p q joint e)
    (hP : IsTiedFreeMixed f p pB eP) (hQ : IsTiedFreeMixed f q qB eQ)
    (hJ : IsTiedFreeMixed f joint jB eJ)
    (hprodB : IsProductTied pB qB jB' e')
    (hjν : joint.ν = μ) (hpB : pB.ν = μ') (hqB : qB.ν = μ')
    (jC jC' : TupleOver K oneVertexShape P.scheme hμ' B)
    (rC : jC.idx ≃ jB.idx) (rC' : jC'.idx ≃ jB'.idx)
    (hRC : SameGaloisType jB jC (Equiv.refl jB.idx) rC)
    (hRC' : SameGaloisType jB' jC' (Equiv.refl jB'.idx) rC')
    (hjC : jC.ν = μ') (hjC' : jC'.ν = μ') :
    SameGaloisType jC jC' ((rC.trans eJ.symm).trans e.symm)
      ((rC'.trans e'.symm).trans (Equiv.sumCongr eP.symm eQ.symm)) := by
  have hσlt' : σ < μ' := (Order.lt_succ σ).trans_le hσμ'
  have hsum2 : ∀ {U V : Type u}, #U ≤ σ → #V ≤ σ → #(U ⊕ V) ≤ σ := fun hU hV => by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hσ hU hV
  have hjBσ : #jB.idx ≤ σ :=
    (Cardinal.mk_congr (e.trans eJ)).symm.trans_le (hsum2 hpσ hqσ)
  have hpBσ : #pB.idx ≤ σ := (Cardinal.mk_congr eP).symm.trans_le hpσ
  have hqBσ : #qB.idx ≤ σ := (Cardinal.mk_congr eQ).symm.trans_le hqσ
  have hJC := infra_612_tiedFreeMixed_copy f joint jB jC eJ rC hRC hμμ'
    (hjBσ.trans_lt hσlt') hJ
  have hprodC := infra_612_isProductTied_copy P σ hσ hμ' hrec' hσμ' pB qB hpB hqB hpBσ hqBσ
    jB' e' hprodB jC' rC' hRC' hjC'
  exact infra_612_tied_base_change_level_joints P σ hσ hμ hrec hσμ p q hνp hνq hpσ hqσ hμ'
    hrec' hσμ' hμμ' B f hf joint e pB qB jC jC' eP eQ (eJ.trans rC.symm) (e'.trans rC'.symm)
    hprod hP hQ hJC hprodC hjν hjC hjC'

theorem infra_612_card_sigma_fin {n : ℕ} (α : Fin n → Type u) {σ : Cardinal.{u}}
    (hσ : ℵ₀ ≤ σ) (h : ∀ i, #(α i) ≤ σ) : #(Σ i, α i) ≤ σ := by
  rw [Cardinal.mk_sigma]
  refine (Cardinal.sum_le_sum _ (fun _ => σ) h).trans ?_
  rw [Cardinal.sum_const]
  simp only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero]
  exact (mul_le_mul' (Cardinal.natCast_lt_aleph0 (n := n)).le le_rfl).trans (Cardinal.aleph0_mul_eq hσ).le

theorem infra_612_card_pi_fin {n : ℕ} (α : Fin n → Type u) {σ : Cardinal.{u}}
    (hσ : ℵ₀ ≤ σ) (h : ∀ i, #(α i) ≤ σ) : #((i : Fin n) → α i) ≤ σ := by
  rw [Cardinal.mk_pi]
  refine (Cardinal.prod_le_prod _ (fun _ => σ) h).trans ?_
  rw [Cardinal.prod_const]
  simp only [Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_uzero, Cardinal.power_natCast]
  exact Cardinal.power_nat_le hσ

/-- **Generic tuples.** For index types of strictly increasing infinite sizes above `c`, and
bad sets `G i k ⊆ κ i` of size `≤ c` not depending on the `i`-th coordinate of `k`, some tuple
avoids all its bad sets (choose coordinates from the longest down). -/
theorem infra_612_comb : ∀ (n : ℕ) (κ : Fin n → Type u) {c : Cardinal.{u}}, ℵ₀ ≤ c →
    (∀ i, c < #(κ i)) → (∀ i j : Fin n, i < j → #(κ i) < #(κ j)) →
    ∀ (G : (i : Fin n) → ((j : Fin n) → κ j) → Set (κ i)),
    (∀ i k, #(G i k) ≤ c) →
    (∀ i k k', (∀ j, j ≠ i → k j = k' j) → G i k = G i k') →
    ∃ k : (j : Fin n) → κ j, ∀ i, k i ∉ G i k
  | 0, κ, c, _, _, _, G, _, _ => ⟨fun i => i.elim0, fun i => i.elim0⟩
  | n + 1, κ, c, hc, hlen, hmono, G, hG, hind => by
    classical
    have hne : Nonempty (κ (Fin.last n)) := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have h2 := hlen (Fin.last n)
      rw [Cardinal.mk_eq_zero] at h2
      exact absurd h2 (not_lt.2 bot_le)
    obtain ⟨w0⟩ := hne
    let κ' : Fin n → Type u := fun j => κ j.castSucc
    -- a bound `M` for the shorter coordinates
    obtain ⟨M, hcM, hM, hMlt⟩ : ∃ M : Cardinal.{u}, c ≤ M ∧ (∀ j, #(κ' j) ≤ M) ∧
        M < #(κ (Fin.last n)) := by
      rcases n with _ | m
      · exact ⟨c, le_rfl, fun j => j.elim0, hlen _⟩
      · refine ⟨#(κ (Fin.last m).castSucc), (hlen _).le, fun j => ?_, hmono _ _ ?_⟩
        · rcases (Fin.le_last j).lt_or_eq with hj | hj
          · exact (hmono _ _ (Fin.castSucc_lt_castSucc_iff.2 hj)).le
          · rw [hj]
        · exact Fin.castSucc_lt_last _
    have hMinf : ℵ₀ ≤ M := hc.trans hcM
    let U : Set (κ (Fin.last n)) :=
      ⋃ k' : ((j : Fin n) → κ' j), G (Fin.last n) (Fin.snoc (α := κ) k' w0)
    have hU : #U ≤ M := by
      refine (Cardinal.mk_iUnion_le _).trans ?_
      calc #((j : Fin n) → κ' j) * ⨆ k', #(G (Fin.last n) (Fin.snoc (α := κ) k' w0))
          ≤ M * M := mul_le_mul' (infra_612_card_pi_fin κ' hMinf hM)
            (ciSup_le' fun k' => (hG _ _).trans hcM)
        _ = M := Cardinal.mul_eq_self hMinf
    obtain ⟨v, hv⟩ : ∃ v, v ∉ U := by
      by_contra hall
      push Not at hall
      have : #(κ (Fin.last n)) ≤ M :=
        (Cardinal.mk_le_mk_of_subset (s := Set.univ) (fun v _ => hall v)).trans' 
          Cardinal.mk_univ.ge |>.trans hU
      exact absurd hMlt (not_lt.2 this)
    let G' : (j : Fin n) → ((j' : Fin n) → κ' j') → Set (κ' j) :=
      fun j k' => G j.castSucc (Fin.snoc (α := κ) k' v)
    obtain ⟨k', hk'⟩ := infra_612_comb n κ' hc (fun j => hlen _)
      (fun i j hij => hmono _ _ (Fin.castSucc_lt_castSucc_iff.2 hij)) G'
      (fun j k' => hG _ _)
      (fun j k₁ k₂ h => hind _ _ _ (by
        intro i hi
        induction i using Fin.lastCases with
        | last => simp
        | cast i =>
          simp only [Fin.snoc_castSucc]
          exact h i (fun hh => hi (by rw [hh]))))
    refine ⟨Fin.snoc (α := κ) k' v, fun i => ?_⟩
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.snoc_last]
      intro hmem
      apply hv
      refine Set.mem_iUnion.2 ⟨k', ?_⟩
      rwa [hind (Fin.last n) (Fin.snoc (α := κ) k' w0) (Fin.snoc (α := κ) k' v) (by
        intro j hj
        induction j using Fin.lastCases with
        | last => exact absurd rfl hj
        | cast j => simp)]
    | cast j =>
      rw [Fin.snoc_castSucc]
      exact hk' j



/-- Finite tied products with every partial product at the level of `A`. -/
def IsFiniteProductTiedLevel {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} :
    (n : ℕ) → (b : Fin n → TupleOver K oneVertexShape P.scheme hμ A) →
    (joint : TupleOver K oneVertexShape P.scheme hμ A) →
    ((Σ i, (b i).idx) ≃ joint.idx) → Prop
  | 0, _, joint, _ => IsEmpty joint.idx
  | n + 1, b, joint, E =>
      ∃ (left : TupleOver K oneVertexShape P.scheme hμ A)
        (El : (Σ i : Fin n, (b i.castSucc).idx) ≃ left.idx),
        left.ν = μ ∧
        IsFiniteProductTiedLevel n (fun i => b i.castSucc) left El ∧
        ∃ e : left.idx ⊕ (b (Fin.last n)).idx ≃ joint.idx,
          IsProductTied left (b (Fin.last n)) joint e ∧
          (∀ (i : Fin n) (k : (b i.castSucc).idx), E ⟨i.castSucc, k⟩ = e (Sum.inl (El ⟨i, k⟩))) ∧
          (∀ k : (b (Fin.last n)).idx, E ⟨Fin.last n, k⟩ = e (Sum.inr k))

theorem IsFiniteProductTiedLevel.toPlain {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ} :
    ∀ (n : ℕ) (b : Fin n → TupleOver K oneVertexShape P.scheme hμ A)
      (joint : TupleOver K oneVertexShape P.scheme hμ A) (E : (Σ i, (b i).idx) ≃ joint.idx),
      IsFiniteProductTiedLevel n b joint E → IsFiniteProductTied n b joint E
  | 0, _, _, _, h => h
  | n + 1, b, joint, E, h => by
    obtain ⟨left, El, -, hL, e, hP, h1, h2⟩ := h
    exact ⟨left, El, IsFiniteProductTiedLevel.toPlain n _ left El hL, e, hP, h1, h2⟩

/-- Split the last factor off a `Fin (n+1)`-indexed sigma (with a parameter summand). -/
def infra_612_finSplit {n : ℕ} {α : Fin (n + 1) → Type u} {β : Type u} :
    (Σ i, α i) ⊕ β → (Σ j : Fin n, α j.castSucc) ⊕ (α (Fin.last n) ⊕ β)
  | Sum.inl ⟨i, l⟩ =>
    Fin.lastCases (motive := fun i => α i → (Σ j : Fin n, α j.castSucc) ⊕ (α (Fin.last n) ⊕ β))
      (fun l => Sum.inr (Sum.inl l)) (fun j l => Sum.inl ⟨j, l⟩) i l
  | Sum.inr d => Sum.inr (Sum.inr d)

theorem infra_612_finSplit_castSucc {n : ℕ} {α : Fin (n + 1) → Type u} {β : Type u}
    (j : Fin n) (l : α j.castSucc) :
    infra_612_finSplit (β := β) (Sum.inl ⟨j.castSucc, l⟩) = Sum.inl ⟨j, l⟩ := by
  simp [infra_612_finSplit]

theorem infra_612_finSplit_last {n : ℕ} {α : Fin (n + 1) → Type u} {β : Type u}
    (l : α (Fin.last n)) :
    infra_612_finSplit (β := β) (Sum.inl ⟨Fin.last n, l⟩) = Sum.inr (Sum.inl l) := by
  simp [infra_612_finSplit]

set_option maxHeartbeats 3200000 in
/-- **Generic entries of a finite tied product (levels at `A`).** -/
theorem infra_612_finite_generic
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ} {t : Cardinal.{u}} (ht : σ + t < μ) :
    ∀ (n : ℕ) (b : Fin n → TupleOver K oneVertexShape P.scheme hμ A)
      (joint : TupleOver K oneVertexShape P.scheme hμ A) (E : (Σ i, (b i).idx) ≃ joint.idx),
      IsFiniteProductTiedLevel n b joint E →
      (∀ i, (b i).ν = μ ∧ #(b i).idx ≤ σ) →
      ∀ (s : (i : Fin n) → ApproximationSequence (b i)),
      (∀ i, σ + t ≤ (s i).τ ∧ (s i).τ + ℵ₀ < #(s i).κIndex) →
      ∀ {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #β ≤ σ + t →
      ∃ F : (i : Fin n) → ((j : Fin n) → (s j).κIndex) → Set (s i).κIndex,
        (∀ i k, #(F i k) ≤ σ + t) ∧
        (∀ i k k', (∀ j, j ≠ i → k j = k' j) → F i k = F i k') ∧
        ∀ k : (j : Fin n) → (s j).κIndex, (∀ i, k i ∉ F i k) →
          P.scheme.DiagramEq (X := joint.host) (Y := A)
            (alignJoint E.symm (typeJoint (p := joint) Y))
            (Sum.elim (fun u : Σ i, (b i).idx => (s u.1).family (k u.1) u.2) Y)
  | 0, b, joint, E, h, hb, s, hs, β, Y, hβ => by
    refine ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun k _ => ?_⟩
    have hc : #((Σ i : Fin 0, (b i).idx) ⊕ β) < μ := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      have : #(Σ i : Fin 0, (b i).idx) = 0 := Cardinal.mk_eq_zero _
      rw [this, zero_add]
      exact hβ.trans_lt ht
    have hp := P.scheme.diagram_preserved A joint.host joint.incl joint.incl_arrow
      (Sum.elim (fun u : Σ i : Fin 0, (b i).idx => (s u.1).family (k u.1) u.2) Y) hc
      (hc.trans_le (infra_612_le_nu joint))
    refine infra_612_dEq_comp (P.scheme.diagram_symm _ _ _ _ hp) id ?_ (fun _ => rfl)
    rintro (u | d)
    · exact u.1.elim0
    · rfl
  | n + 1, b, joint, E, h, hb, s, hs, β, Y, hβ => by
    classical
    obtain ⟨left, El, hlν, hL, e, hP, hc1, hc2⟩ := h
    have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
    have hcinf : ℵ₀ ≤ σ + t := hσ.trans le_self_add
    have hsum : ∀ {U V : Type u}, #U ≤ σ → #V ≤ σ + t → #(U ⊕ V) ≤ σ + t := fun hU hV => by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      calc #_ + #_ ≤ σ + (σ + t) := add_le_add hU hV
        _ = σ + t := by rw [← add_assoc, Cardinal.add_eq_self hσ]
    have hsum2 : ∀ {U V : Type u}, #U ≤ σ → #V ≤ σ → #(U ⊕ V) ≤ σ := fun hU hV => by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.add_le_of_le hσ hU hV
    have hlt : ∀ {U : Type u}, #U ≤ σ + t → #U < μ := fun h => h.trans_lt ht
    have hleftσ : #left.idx ≤ σ := (Cardinal.mk_congr El).symm.trans_le
      (infra_612_card_sigma_fin _ hσ (fun i => (hb _).2))
    have hlastσ : #(b (Fin.last n)).idx ≤ σ := (hb _).2
    have IH := infra_612_finite_generic P σ hσ hμ hrec hσμ ht n (fun i => b i.castSucc) left El
      hL (fun i => hb _) (fun i => s i.castSucc) (fun i => hs _) (β := (b (Fin.last n)).idx ⊕ β)
    obtain ⟨Kq, hKτ, -, hKlong⟩ :=
      infra_78_exists_seq_ge P σ hσ hμ hrec hσμ left hlν hleftσ ht
    obtain ⟨x, ex, hS, y, ey, hT, hJ⟩ := hP
    have hJ' : SameGaloisType _ (x.join y) e.symm (Equiv.sumCongr ex ey).symm := by
      have h := infra_612_sameGalois_trans_equiv hJ (Equiv.sumCongr ex ey).symm
      rw [Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.trans_refl] at h
      exact h
    obtain ⟨C, hC, hEnt⟩ := infra_612_product_entry left (b (Fin.last n)) x ex hS y ey hT Kq
      (s (Fin.last n)) Y (hleftσ.trans_lt hσlt) (hlt (hsum hleftσ hβ))
      (hlt (hsum hlastσ hβ)) ((hsum hleftσ hβ).trans (hs _).1) (hs _).2
    choose F' hF'c hF'i hF' using fun v : (s (Fin.last n)).κIndex =>
      IH (Sum.elim ((s (Fin.last n)).family v) Y) (hsum hlastσ hβ)
    refine ⟨fun i k => Fin.lastCases (motive := fun i => Set (s i).κIndex) C
      (fun j => F' (k (Fin.last n)) j (fun j' => k j'.castSucc)) i, ?_, ?_, ?_⟩
    · intro i k
      induction i using Fin.lastCases with
      | last =>
        simp only [Fin.lastCases_last]
        refine hC.trans ?_
        calc #(left.idx ⊕ β) + ℵ₀ ≤ (σ + t) + (σ + t) := add_le_add (hsum hleftσ hβ) hcinf
          _ = σ + t := Cardinal.add_eq_self hcinf
      | cast j =>
        simp only [Fin.lastCases_castSucc]
        exact hF'c _ _ _
    · intro i k k' hkk
      induction i using Fin.lastCases with
      | last => simp only [Fin.lastCases_last]
      | cast j =>
        simp only [Fin.lastCases_castSucc]
        rw [hkk (Fin.last n) (Fin.castSucc_lt_last j).ne']
        exact hF'i _ _ _ _ (fun j' hj' => hkk _ (fun hh => hj' (Fin.castSucc_injective _ hh)))
    · intro k hk
      have hv : k (Fin.last n) ∉ C := by
        have := hk (Fin.last n)
        simpa only [Fin.lastCases_last] using this
      have hkj : ∀ j, k j.castSucc ∉ F' (k (Fin.last n)) j (fun j' => k j'.castSucc) := by
        intro j
        have := hk j.castSucc
        simpa only [Fin.lastCases_castSucc] using this
      have I1 := hF' (k (Fin.last n)) (fun j' => k j'.castSucc) hkj
      set v := k (Fin.last n) with hvdef
      let Y' : (b (Fin.last n)).idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
        Sum.elim ((s (Fin.last n)).family v) Y
      have hY' : #((b (Fin.last n)).idx ⊕ β) ≤ σ + t := hsum hlastσ hβ
      have hKE : σ + t + ℵ₀ < #Kq.κIndex := by
        rw [Cardinal.add_eq_left hcinf hcinf]
        exact hKτ.trans_lt (le_self_add.trans_lt hKlong)
      obtain ⟨m, hm, -⟩ := infra_78_exists_outside_two
        {m | ¬ P.scheme.DiagramEq (X := left.host) (Y := A)
          (typeJoint (p := left) Y') (seqJoint (Kq.family m) Y')}
        {m | ¬ P.scheme.DiagramEq (X := left.host) (Y := A)
          (typeJoint (p := left) Y') (seqJoint (Kq.family m) Y')} (hcinf.trans le_self_add)
        ((Kq.few_exceptions _ (hY'.trans hKτ)).trans (add_le_add hY' le_rfl))
        ((Kq.few_exceptions _ (hY'.trans hKτ)).trans (add_le_add hY' le_rfl)) hKE
      have Gm : P.scheme.DiagramEq (X := left.host) (Y := A)
          (typeJoint (p := left) Y') (seqJoint (Kq.family m) Y') := not_not.1 hm
      have E1 := hEnt v hv m Gm
      have DJ := infra_612_dEq_of_sameGalois hJ' Y ((hsum2 hleftσ hlastσ).trans_lt hσlt)
        (hlt (hβ))
      have Gm' := infra_612_dEq_comp (P.scheme.diagram_symm _ _ _ _ Gm)
        (Equiv.sumAssoc left.idx (b (Fin.last n)).idx β)
        (xs' := fun t => seqJoint (Kq.family m) Y' (Equiv.sumAssoc _ _ _ t))
        (ys' := fun t => typeJoint (p := left) Y' (Equiv.sumAssoc _ _ _ t))
        (fun _ => rfl) (fun _ => rfl)
      have A1 := P.scheme.diagram_trans _ _ _ _ _ _ DJ (P.scheme.diagram_trans _ _ _ _ _ _ E1 Gm')
      have A1' := infra_612_dEq_comp A1
        (fun u => Sum.elim (fun jl => Sum.inl (Sum.inl (El jl)))
          (Sum.elim (fun l => Sum.inl (Sum.inr l)) (fun d => Sum.inr d))
          (infra_612_finSplit (α := fun i => (b i).idx) (β := β) u))
        (xs' := alignJoint E.symm (typeJoint (p := joint) Y))
        (ys' := fun u => alignJoint El.symm (typeJoint (p := left) Y')
          (infra_612_finSplit (α := fun i => (b i).idx) (β := β) u))
        (by
          rintro (⟨i, l⟩ | d)
          · induction i using Fin.lastCases with
            | last =>
              simp only [infra_612_finSplit_last]
              exact congrArg (fun z => typeJoint (p := joint) Y (Sum.inl z)) (hc2 l)
            | cast j =>
              simp only [infra_612_finSplit_castSucc]
              exact congrArg (fun z => typeJoint (p := joint) Y (Sum.inl z)) (hc1 j l)
          · rfl)
        (by
          rintro (⟨i, l⟩ | d)
          · induction i using Fin.lastCases with
            | last => simp only [infra_612_finSplit_last]; rfl
            | cast j => simp only [infra_612_finSplit_castSucc]; rfl
          · rfl)
      have I1' := infra_612_dEq_comp I1 (infra_612_finSplit (α := fun i => (b i).idx) (β := β))
        (xs' := fun u => alignJoint El.symm (typeJoint (p := left) Y')
          (infra_612_finSplit (α := fun i => (b i).idx) (β := β) u))
        (ys' := Sum.elim (fun u : Σ i, (b i).idx => (s u.1).family (k u.1) u.2) Y)
        (fun _ => rfl)
        (by
          rintro (⟨i, l⟩ | d)
          · induction i using Fin.lastCases with
            | last => simp only [infra_612_finSplit_last]; rfl
            | cast j => simp only [infra_612_finSplit_castSucc]; rfl
          · rfl)
      exact P.scheme.diagram_trans _ _ _ _ _ _ A1' I1'

/-- `infra_78_exists_seq_ge` with the index length `succ (max (max t ℵ₀) |p|)`. -/
theorem infra_612_exists_seq_len
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {base : P.scheme.Object μ hμ} (p : TupleOver K oneVertexShape P.scheme hμ base)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) {t : Cardinal.{u}} (ht : t < μ) :
    ∃ seq : ApproximationSequence p, t ≤ seq.τ ∧ seq.τ + ℵ₀ < #seq.κIndex ∧
      #seq.κIndex = Order.succ (max (max t ℵ₀) #p.idx) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #p.idx < μ := hidx.trans_lt hσlt
  let τ : Cardinal.{u} := max t ℵ₀
  have hτ : ℵ₀ ≤ τ := le_max_right _ _
  have hτμ : τ < μ := max_lt ht (P.aleph0_lt hμ)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ := by
    apply hrec.2
    exact max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
  let ρ : Cardinal.{u} := max τ #p.idx
  have hρinf : ℵ₀ ≤ ρ := hτ.trans (le_max_left _ _)
  have hρμ : ρ < μ := max_lt hτμ hidxμ
  let κ : Cardinal.{u} := Order.succ ρ
  have hκinf : ℵ₀ ≤ κ := hρinf.trans (Order.le_succ _)
  have hκμ : κ < μ :=
    (Order.succ_le_of_lt (cantor ρ)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hρμ)
  have hprodκ : κ * #p.idx < μ := by
    have hmul : κ * #p.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    rcases le_total σ κ with hσκ | hκσ
    · have heq : κ * σ = κ :=
        mul_eq_left hκinf hσκ (aleph0_pos.trans_le hσ).ne'
      rw [heq] at hmul
      exact hmul.trans_lt hκμ
    · have heq : κ * σ = σ := by
        rw [mul_comm]
        exact mul_eq_left hσ hκσ (aleph0_pos.trans_le hκinf).ne'
      rw [heq] at hmul
      exact hmul.trans_lt hσlt
  obtain ⟨seq, hseqτ, hseqκ⟩ :=
    P.exists_approximationSequence hμ base p hνμ σ τ κ hσ hσlt hidx hτ hτμ hκinf hκμ
      hprodκ hclosed
  refine ⟨seq, ?_, ?_, ?_⟩
  · rw [hseqτ]; exact le_max_left _ _
  · rw [hseqτ, hseqκ, add_eq_left hτ hτ]
    exact (le_max_left _ _).trans_lt (Order.lt_succ ρ)
  · rw [hseqκ]

/-- Approximation sequences for finitely many factors, with strictly increasing lengths. -/
theorem infra_612_increasing_seqs
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ} {n : ℕ} (b : Fin n → TupleOver K oneVertexShape P.scheme hμ A)
    (hb : ∀ i, (b i).ν = μ ∧ #(b i).idx ≤ σ) {t0 : Cardinal.{u}} (ht0 : t0 < μ)
    (hσt0 : σ ≤ t0) :
    ∃ s : (i : Fin n) → ApproximationSequence (b i),
      (∀ i, t0 ≤ (s i).τ ∧ (s i).τ + ℵ₀ < #(s i).κIndex) ∧
      ∀ i j, i < j → #(s i).κIndex < #(s j).κIndex := by
  let T : ℕ → Cardinal.{u} := fun m => Order.succ^[m] t0
  have hTμ : ∀ m, T m < μ := by
    intro m
    induction m with
    | zero => exact ht0
    | succ m ih =>
      show Order.succ^[m + 1] t0 < μ
      rw [Function.iterate_succ_apply']
      exact (Order.succ_le_of_lt (cantor _)).trans_lt
        (hμ.1.working.strongLimit.isStrongPrelimit ih)
  have hTmono : Monotone T := monotone_nat_of_le_succ (fun m => by
    show Order.succ^[m] t0 ≤ Order.succ^[m + 1] t0
    rw [Function.iterate_succ_apply']
    exact Order.le_succ _)
  have hT0 : ∀ m, t0 ≤ T m := fun m => hTmono (Nat.zero_le m)
  have hex : ∀ i : Fin n, ∃ seq : ApproximationSequence (b i), T i.val ≤ seq.τ ∧
      seq.τ + ℵ₀ < #seq.κIndex ∧ #seq.κIndex ≤ T (i.val + 1) := by
    intro i
    obtain ⟨seq, h1, h2, h3⟩ := infra_612_exists_seq_len P σ hσ hμ hrec hσμ (b i) (hb i).1
      (hb i).2 (hTμ i.val)
    refine ⟨seq, h1, h2, ?_⟩
    rw [h3]
    show _ ≤ Order.succ^[i.val + 1] t0
    rw [Function.iterate_succ_apply']
    have hinf : ℵ₀ ≤ T i.val := hσ.trans (hσt0.trans (hT0 _))
    have : max (max (T i.val) ℵ₀) #(b i).idx = T i.val :=
      by rw [max_eq_left hinf, max_eq_left ((hb i).2.trans (hσt0.trans (hT0 _)))]
    rw [this]
  choose s hs1 hs2 hs3 using hex
  refine ⟨s, fun i => ⟨(hT0 _).trans (hs1 i), hs2 i⟩, fun i j hij => ?_⟩
  calc #(s i).κIndex ≤ T (i.val + 1) := hs3 i
    _ ≤ T j.val := hTmono (Nat.succ_le_of_lt hij)
    _ ≤ (s j).τ := hs1 j
    _ < #(s j).κIndex := le_self_add.trans_lt (hs2 j)

set_option maxHeartbeats 3200000 in
/-- **Finite tied products are invariant under permuting the factors, all partial products at
the level of `A` (proved).** -/
theorem infra_612_tied_finite_perm_level
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ} (n : ℕ)
    (b : Fin n → TupleOver K oneVertexShape P.scheme hμ A)
    (hb : ∀ i, (b i).ν = μ ∧ #(b i).idx ≤ σ) (π : Equiv.Perm (Fin n))
    (j₁ j₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (E₁ : (Σ i, (b i).idx) ≃ j₁.idx) (E₂ : (Σ i, (b (π i)).idx) ≃ j₂.idx)
    (h₁ : IsFiniteProductTiedLevel n b j₁ E₁)
    (h₂ : IsFiniteProductTiedLevel n (fun i => b (π i)) j₂ E₂)
    (hj₁ : j₁.ν = μ) (hj₂ : j₂.ν = μ) :
    SameGaloisType j₁ j₂ E₁.symm
      (E₂.symm.trans (Equiv.sigmaCongrLeft (β := fun i => (b i).idx) π)) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hj₁σ : #j₁.idx ≤ σ := (Cardinal.mk_congr E₁).symm.trans_le
    (infra_612_card_sigma_fin _ hσ (fun i => (hb i).2))
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ :=
    infra_73_differing_test P σ hσ hμ hrec hσμ j₁ j₂ E₁.symm
      (E₂.symm.trans (Equiv.sigmaCongrLeft (β := fun i => (b i).idx) π)) hj₁ hj₂ hj₁σ
      (hj₁σ.trans_lt hσlt) hneq
  apply hnot
  have hβμ : #β < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    exact hβ.trans_lt (add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ))
  have ht : σ + #β < μ := add_lt_of_lt (P.aleph0_le hμ) hσlt hβμ
  have hcinf : ℵ₀ ≤ σ + #β := hσ.trans le_self_add
  obtain ⟨s, hs, hsmono⟩ := infra_612_increasing_seqs P σ hσ hμ hrec hσμ b hb ht le_self_add
  obtain ⟨F, hFc, hFi, hF⟩ := infra_612_finite_generic P σ hσ hμ hrec hσμ ht n b j₁ E₁ h₁ hb s
    hs Y le_add_self
  obtain ⟨F', hF'c, hF'i, hF'⟩ := infra_612_finite_generic P σ hσ hμ hrec hσμ ht n
    (fun i => b (π i)) j₂ E₂ h₂ (fun i => hb (π i)) (fun i => s (π i)) (fun i => hs (π i)) Y
    le_add_self
  let κ : Fin n → Type u := fun i => (s i).κIndex
  let G : (i : Fin n) → ((j : Fin n) → κ j) → Set (κ i) := fun i k =>
    F i k ∪ (fun v : κ i => cast (congrArg κ (π.apply_symm_apply i).symm) v) ⁻¹'
      F' (π.symm i) (fun j => k (π j))
  obtain ⟨k, hk⟩ := infra_612_comb n κ hcinf
    (fun i => ((hs i).1.trans le_self_add).trans_lt (hs i).2) hsmono G
    (fun i k => by
      refine (Cardinal.mk_union_le _ _).trans ?_
      calc _ ≤ (σ + #β) + (σ + #β) := add_le_add (hFc i k)
            ((Cardinal.mk_preimage_of_injective _ _ (fun _ _ hh => (cast_inj _).1 hh)).trans (hF'c _ _))
        _ = σ + #β := Cardinal.add_eq_self hcinf)
    (fun i k k' hkk => by
      show F i k ∪ _ = F i k' ∪ _
      rw [hFi i k k' hkk, hF'i (π.symm i) (fun j => k (π j)) (fun j => k' (π j)) (fun j hj =>
        hkk (π j) (fun hh => hj (by rw [← hh, Equiv.symm_apply_apply])))])
  have hk1 : ∀ i, k i ∉ F i k := fun i hi => hk i (Or.inl hi)
  have h3 : ∀ (j a : Fin n) (ha : a = j) (h' : κ (π j) = κ (π a)),
      k (π j) ∈ F' j (fun j => k (π j)) → cast h' (k (π j)) ∈ F' a (fun j => k (π j)) := by
    intro j a ha h' hm; subst ha; simpa using hm
  have hk2 : ∀ j, k (π j) ∉ F' j (fun j => k (π j)) := fun j hj =>
    hk (π j) (Or.inr (h3 j (π.symm (π j)) (π.symm_apply_apply j) _ hj))
  have D1 := hF k hk1
  have D2 := hF' (fun j => k (π j)) hk2
  let σπ := Equiv.sigmaCongrLeft (β := fun i => (b i).idx) π
  have D2' := infra_612_dEq_comp D2 (Sum.map σπ.symm id)
    (xs' := alignJoint (E₂.symm.trans σπ) (typeJoint (p := j₂) Y))
    (ys' := Sum.elim (fun u : Σ i, (b i).idx => (s u.1).family (k u.1) u.2) Y)
    (by rintro (u | d) <;> rfl)
    (by
      rintro (u | d)
      · exact (congrArg (fun w : Σ i, (b i).idx => (s w.1).family (k w.1) w.2)
          (σπ.apply_symm_apply u)).symm
      · rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ D1 (P.scheme.diagram_symm _ _ _ _ D2')

set_option maxHeartbeats 3200000 in
/-- **Restricting a finite tied product to a subfamily of factors, all partial products at the
level of `A` (proved).** -/
theorem infra_612_tied_finite_proj_level
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ} (n m : ℕ)
    (b : Fin n → TupleOver K oneVertexShape P.scheme hμ A)
    (hb : ∀ i, (b i).ν = μ ∧ #(b i).idx ≤ σ) (sf : Fin m ↪ Fin n)
    (j j' : TupleOver K oneVertexShape P.scheme hμ A)
    (E : (Σ i, (b i).idx) ≃ j.idx) (E' : (Σ i, (b (sf i)).idx) ≃ j'.idx)
    (h : IsFiniteProductTiedLevel n b j E)
    (h' : IsFiniteProductTiedLevel m (fun i => b (sf i)) j' E')
    (hj : j.ν = μ) (hj' : j'.ν = μ) :
    SameGaloisType (j.reindex (fun t : (Σ i, (b (sf i)).idx) => E ⟨sf t.1, t.2⟩)) j'
      (Equiv.refl _) E'.symm := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hqσ : #(Σ i, (b (sf i)).idx) ≤ σ := infra_612_card_sigma_fin _ hσ (fun i => (hb _).2)
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ :=
    infra_73_differing_test P σ hσ hμ hrec hσμ
      (j.reindex (fun t : (Σ i, (b (sf i)).idx) => E ⟨sf t.1, t.2⟩)) j'
      (Equiv.refl _) E'.symm hj hj' hqσ (hqσ.trans_lt hσlt) hneq
  apply hnot
  have hβμ : #β < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    exact hβ.trans_lt (add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ))
  have ht : σ + #β < μ := add_lt_of_lt (P.aleph0_le hμ) hσlt hβμ
  have hcinf : ℵ₀ ≤ σ + #β := hσ.trans le_self_add
  obtain ⟨s, hs, hsmono⟩ := infra_612_increasing_seqs P σ hσ hμ hrec hσμ b hb ht le_self_add
  obtain ⟨F, hFc, hFi, hF⟩ := infra_612_finite_generic P σ hσ hμ hrec hσμ ht n b j E h hb s
    hs Y le_add_self
  obtain ⟨F', hF'c, hF'i, hF'⟩ := infra_612_finite_generic P σ hσ hμ hrec hσμ ht m
    (fun i => b (sf i)) j' E' h' (fun i => hb (sf i)) (fun i => s (sf i)) (fun i => hs (sf i)) Y
    le_add_self
  let κ : Fin n → Type u := fun i => (s i).κIndex
  let G : (i : Fin n) → ((l : Fin n) → κ l) → Set (κ i) := fun i k =>
    F i k ∪ (if hi : ∃ a, sf a = i then
      (fun v : κ i => cast (congrArg κ (Classical.choose_spec hi).symm) v) ⁻¹'
        F' (Classical.choose hi) (fun a => k (sf a)) else ∅)
  obtain ⟨k, hk⟩ := infra_612_comb n κ hcinf
    (fun i => ((hs i).1.trans le_self_add).trans_lt (hs i).2) hsmono G
    (fun i k => by
      refine (Cardinal.mk_union_le _ _).trans ?_
      have h2 : #((if hi : ∃ a, sf a = i then
          (fun v : κ i => cast (congrArg κ (Classical.choose_spec hi).symm) v) ⁻¹'
            F' (Classical.choose hi) (fun a => k (sf a)) else ∅ : Set (κ i))) ≤ σ + #β := by
        split_ifs with hi
        · exact (Cardinal.mk_preimage_of_injective _ _ (fun _ _ hh => (cast_inj _).1 hh)).trans
            (hF'c _ _)
        · simp
      calc _ ≤ (σ + #β) + (σ + #β) := add_le_add (hFc i k) h2
        _ = σ + #β := Cardinal.add_eq_self hcinf)
    (fun i k k' hkk => by
      show F i k ∪ _ = F i k' ∪ _
      rw [hFi i k k' hkk]
      congr 1
      by_cases hi : ∃ a, sf a = i
      · simp only [dif_pos hi]
        rw [hF'i (Classical.choose hi) (fun a => k (sf a)) (fun a => k' (sf a)) (fun a ha =>
          hkk (sf a) (fun hh => ha (sf.injective (hh.trans (Classical.choose_spec hi).symm))))]
      · simp only [dif_neg hi])
  have hk1 : ∀ i, k i ∉ F i k := fun i hi => hk i (Or.inl hi)
  have h3 : ∀ (a c : Fin m) (hc : c = a) (h' : κ (sf a) = κ (sf c)),
      k (sf a) ∈ F' a (fun a => k (sf a)) → cast h' (k (sf a)) ∈ F' c (fun a => k (sf a)) := by
    intro a c hc h' hm; subst hc; simpa using hm
  have hk2 : ∀ a, k (sf a) ∉ F' a (fun a => k (sf a)) := fun a ha => by
    have h0 : ∃ a', sf a' = sf a := ⟨a, rfl⟩
    apply hk (sf a)
    refine Or.inr ?_
    show k (sf a) ∈ (if hi : ∃ a', sf a' = sf a then
      (fun v : κ (sf a) => cast (congrArg κ (Classical.choose_spec hi).symm) v) ⁻¹'
        F' (Classical.choose hi) (fun a => k (sf a)) else ∅)
    rw [dif_pos h0]
    exact h3 a _ (sf.injective (Classical.choose_spec h0)) _ ha
  have D1 := hF k hk1
  have D2 := hF' (fun a => k (sf a)) hk2
  have D1' := infra_612_dEq_comp D1
    (Sum.map (fun t : (Σ a, (b (sf a)).idx) => (⟨sf t.1, t.2⟩ : Σ i, (b i).idx)) id)
    (xs' := alignJoint (Equiv.refl _)
      (typeJoint (p := j.reindex (fun t : (Σ i, (b (sf i)).idx) => E ⟨sf t.1, t.2⟩)) Y))
    (ys' := Sum.elim (fun u : Σ a, (b (sf a)).idx => (s (sf u.1)).family (k (sf u.1)) u.2) Y)
    (by rintro (u | d) <;> rfl) (by rintro (u | d) <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ D1' (P.scheme.diagram_symm _ _ _ _ D2)

/-- **A level copy of a finite product (partial products `μ`-types) is one (proved, cycle 93).**
If `j` (any eligible level) is `b 0 ⊗ ⋯ ⊗ b (n-1)` with every partial product a `μ`-type, so is
any level-`μ` copy `j'` of `j` (only the last binary step changes:
`infra_612_isProductTied_copy`). -/
theorem infra_612_finiteLevel_copy
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ} :
    ∀ (n : ℕ) (b : Fin n → TupleOver K oneVertexShape P.scheme hμ A),
      (∀ i, (b i).ν = μ ∧ #(b i).idx ≤ σ) →
      ∀ (j : TupleOver K oneVertexShape P.scheme hμ A) (E : (Σ i, (b i).idx) ≃ j.idx),
      IsFiniteProductTiedLevel n b j E →
      ∀ (j' : TupleOver K oneVertexShape P.scheme hμ A) (r : j'.idx ≃ j.idx),
      SameGaloisType j j' (Equiv.refl j.idx) r → j'.ν = μ →
      IsFiniteProductTiedLevel n b j' (E.trans r.symm)
  | 0, _, _, _, _, h, _, r, _, _ => by
      haveI : IsEmpty _ := h
      exact r.isEmpty
  | n + 1, b, hb, j, E, h, j', r, hR, hj' => by
      obtain ⟨left, El, hlν, hL, e, hprod, hE1, hE2⟩ := h
      have hlσ : #left.idx ≤ σ := (Cardinal.mk_congr El).symm.trans_le
        (infra_612_card_sigma_fin _ hσ (fun i => (hb i.castSucc).2))
      refine ⟨left, El, hlν, hL, e.trans r.symm, ?_, ?_, ?_⟩
      · exact infra_612_isProductTied_copy P σ hσ hμ hrec hσμ left (b (Fin.last n)) hlν
          (hb _).1 hlσ (hb _).2 j e hprod j' r hR hj'
      · intro i k
        simp only [Equiv.trans_apply, hE1 i k]
      · intro k
        simp only [Equiv.trans_apply, hE2 k]

/-- **Proposition 6.12** (Products of bounded types). For bounded types `p(x)`, `q(y)` over
`A`, realize `p` in an extension `B ≥ A` and then realize `q^B` (the free lift) in a further
extension; the joint type `p ⊗ q` of `(x, y)` over `A` (`IsProductTied`):

1. exists;
2. is independent of all choices: any two products have the same actual `μ`-type, i.e. any
   `μ`-level copies of them have the same Galois type (English: "The joint type of (x, y) over
   A, denoted p ⊗ q, is independent of all choices", with Cor 6.7: "Types of tuples of length
   less than ν over A obtained in a larger object are actual ν-types"; proved,
   `infra_612_tied_indep_copies`, cycle 93 audit);
3. is symmetric, with the coordinate swap: `p ⊗ q = q ⊗ p`, for the actual `μ`-types (any
   level-`μ` copies; English "Binary products are symmetric, with the indicated permutation of
   coordinates"; proved, `infra_612_tied_symm_copies`, cycle 93);
4. associates: `(p ⊗ q) ⊗ r = p ⊗ (q ⊗ r)` (with `Equiv.sumAssoc`), for the actual `μ`-types
   (intermediate products `μ`-types, triple products on level-`μ` copies; English "Finite
   products associate"; proved, `infra_612_tied_assoc_copies`, cycle 93);
5. finite products are permutation invariant, for the actual `μ`-types (every partial product a
   `μ`-type, `IsFiniteProductTiedLevel`; products on level-`μ` copies; English "Finite products
   associate, are permutation invariant, and commute with coordinate projections"; proved,
   `infra_612_finiteLevel_copy` + `infra_612_tied_finite_perm_level`, cycle 93);
6. finite products commute with coordinate projections (sub-lists of factors), same reading
   (proved, `infra_612_finiteLevel_copy` + `infra_612_tied_finite_proj_level`, cycle 93);
7. base change: for `A → B`, `(p ⊗ q)^B = p^B ⊗ q^B` (free lifts tied, `IsTiedFreeMixed`), for the
   actual types (`p ⊗ q` a `μ`-type, `p^B`, `q^B` `μ'`-types, both sides on level-`μ'` copies;
   English "Furthermore (p ⊗ q)^B = p^B ⊗ q^B"; proved, `infra_612_tied_base_change_copies`,
   cycle 93).

"Across eligible levels": realizations and the base change target may sit at any eligible level
of the tail at or above that of `A` (all arities are bounded at the level of `A`).
Packaging as Theorem 6.10: a tail of recursion-closed levels `μ ≥ σ⁺`, factors of size `≤ σ`
realized at the level of `A`.

**Status:** all clauses proved (cycle 93; clauses 2–7 restated to the actual-`μ`-type copy
form, Cor 6.7). Copies exist (`infra_78_same_level_realization`), so no clause is vacuous; the
at-level `*_level_joints` / `*_level` lemmas are the corollaries for joints already at level. -/
theorem proposition_6_12 {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ)),
      let TO := TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A
      ∀ (p q : TO), p.ν = μ → q.ν = μ → #p.idx ≤ σ → #q.idx ≤ σ →
        -- 1. existence
        (∃ (joint : TO) (e : p.idx ⊕ q.idx ≃ joint.idx), IsProductTied p q joint e) ∧
        -- 2. independence of choices: the actual `μ`-types of any two products agree
        -- (Cor 6.7: a type over `A` obtained in a larger object is its actual `μ`-type, read
        -- on any `μ`-level copy; cycle 93 audit)
        (∀ (j₁ j₂ : TO) (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : p.idx ⊕ q.idx ≃ j₂.idx),
          IsProductTied p q j₁ e₁ → IsProductTied p q j₂ e₂ →
          ∀ (j'₁ j'₂ : TO) (r₁ : j'₁.idx ≃ j₁.idx) (r₂ : j'₂.idx ≃ j₂.idx),
            SameGaloisType j₁ j'₁ (Equiv.refl j₁.idx) r₁ →
            SameGaloisType j₂ j'₂ (Equiv.refl j₂.idx) r₂ → j'₁.ν = μ → j'₂.ν = μ →
            SameGaloisType j'₁ j'₂ (r₁.trans e₁.symm) (r₂.trans e₂.symm)) ∧
        -- 3. symmetry, for the actual `μ`-types (level-`μ` copies; cycle 93 audit)
        (∀ (j₁ j₂ : TO) (e₁ : p.idx ⊕ q.idx ≃ j₁.idx) (e₂ : q.idx ⊕ p.idx ≃ j₂.idx),
          IsProductTied p q j₁ e₁ → IsProductTied q p j₂ e₂ →
          ∀ (j'₁ j'₂ : TO) (r₁ : j'₁.idx ≃ j₁.idx) (r₂ : j'₂.idx ≃ j₂.idx),
            SameGaloisType j₁ j'₁ (Equiv.refl j₁.idx) r₁ →
            SameGaloisType j₂ j'₂ (Equiv.refl j₂.idx) r₂ → j'₁.ν = μ → j'₂.ν = μ →
            SameGaloisType j'₁ j'₂ (r₁.trans e₁.symm)
              ((r₂.trans e₂.symm).trans (Equiv.sumComm _ _))) ∧
        -- 4. associativity, for the actual `μ`-types: factors and the intermediate products
        -- `p ⊗ q`, `q ⊗ r` are `μ`-types; triple products compared on level-`μ` copies
        -- (cycle 93 audit)
        (∀ (r : TO), r.ν = μ → #r.idx ≤ σ →
          ∀ (pq qr j₁ j₂ : TO) (epq : p.idx ⊕ q.idx ≃ pq.idx) (eqr : q.idx ⊕ r.idx ≃ qr.idx)
            (e₁ : pq.idx ⊕ r.idx ≃ j₁.idx) (e₂ : p.idx ⊕ qr.idx ≃ j₂.idx),
            IsProductTied p q pq epq → IsProductTied pq r j₁ e₁ →
            IsProductTied q r qr eqr → IsProductTied p qr j₂ e₂ →
            pq.ν = μ → qr.ν = μ →
            ∀ (j'₁ j'₂ : TO) (r₁ : j'₁.idx ≃ j₁.idx) (r₂ : j'₂.idx ≃ j₂.idx),
            SameGaloisType j₁ j'₁ (Equiv.refl j₁.idx) r₁ →
            SameGaloisType j₂ j'₂ (Equiv.refl j₂.idx) r₂ → j'₁.ν = μ → j'₂.ν = μ →
            SameGaloisType j'₁ j'₂
              ((r₁.trans e₁.symm).trans ((Equiv.sumCongr epq.symm (Equiv.refl _)).trans
                (Equiv.sumAssoc _ _ _)))
              ((r₂.trans e₂.symm).trans (Equiv.sumCongr (Equiv.refl _) eqr.symm))) ∧
        -- 5. permutation invariance of finite products, for the actual `μ`-types: every partial
        -- product is a `μ`-type (`IsFiniteProductTiedLevel`), the products are compared on
        -- level-`μ` copies (cycle 93 audit)
        (∀ (n : ℕ) (b : Fin n → TO), (∀ i, (b i).ν = μ ∧ #(b i).idx ≤ σ) →
          ∀ (π : Equiv.Perm (Fin n)) (j₁ j₂ : TO)
            (E₁ : (Σ i, (b i).idx) ≃ j₁.idx) (E₂ : (Σ i, (b (π i)).idx) ≃ j₂.idx),
            IsFiniteProductTiedLevel n b j₁ E₁ →
            IsFiniteProductTiedLevel n (fun i => b (π i)) j₂ E₂ →
            ∀ (j'₁ j'₂ : TO) (r₁ : j'₁.idx ≃ j₁.idx) (r₂ : j'₂.idx ≃ j₂.idx),
            SameGaloisType j₁ j'₁ (Equiv.refl j₁.idx) r₁ →
            SameGaloisType j₂ j'₂ (Equiv.refl j₂.idx) r₂ → j'₁.ν = μ → j'₂.ν = μ →
            SameGaloisType j'₁ j'₂ (r₁.trans E₁.symm)
              ((r₂.trans E₂.symm).trans (Equiv.sigmaCongrLeft (β := fun i => (b i).idx) π))) ∧
        -- 6. finite products commute with coordinate projections (same reading)
        (∀ (n m : ℕ) (b : Fin n → TO), (∀ i, (b i).ν = μ ∧ #(b i).idx ≤ σ) →
          ∀ (s : Fin m ↪ Fin n) (j j' : TO)
            (E : (Σ i, (b i).idx) ≃ j.idx) (E' : (Σ i, (b (s i)).idx) ≃ j'.idx),
            IsFiniteProductTiedLevel n b j E →
            IsFiniteProductTiedLevel m (fun i => b (s i)) j' E' →
            ∀ (jc jc' : TO) (r : jc.idx ≃ j.idx) (r' : jc'.idx ≃ j'.idx),
            SameGaloisType j jc (Equiv.refl j.idx) r →
            SameGaloisType j' jc' (Equiv.refl j'.idx) r' → jc.ν = μ → jc'.ν = μ →
            SameGaloisType
              (jc.reindex (fun t : (Σ i, (b (s i)).idx) => r.symm (E ⟨s t.1, t.2⟩))) jc'
              (Equiv.refl _) (r'.trans E'.symm)) ∧
        -- 7. base change `(p ⊗ q)^B = p^B ⊗ q^B`, for the actual types: `p ⊗ q` a `μ`-type,
        -- `p^B`, `q^B` `μ'`-types, both sides compared on level-`μ'` copies (cycle 93 audit)
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
            joint.ν = μ → pB.ν = μ' → qB.ν = μ' →
            ∀ (jC jC' : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ') B)
              (rC : jC.idx ≃ jB.idx) (rC' : jC'.idx ≃ jB'.idx),
            SameGaloisType jB jC (Equiv.refl jB.idx) rC →
            SameGaloisType jB' jC' (Equiv.refl jB'.idx) rC' → jC.ν = μ' → jC'.ν = μ' →
            SameGaloisType jC jC' ((rC.trans eJ.symm).trans e.symm)
              ((rC'.trans e'.symm).trans (Equiv.sumCongr eP.symm eQ.symm))) := by
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun μ hμ A p q hνp hνq hpσ hqσ =>
    ⟨infra_612_tied_exists P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 p q hνp hνq hqσ,
      fun j₁ j₂ e₁ e₂ h₁ h₂ j'₁ j'₂ r₁ r₂ hR₁ hR₂ hj₁ hj₂ =>
        infra_612_tied_indep_copies P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 p q hνq hpσ hqσ
          j₁ j₂ e₁ e₂ h₁ h₂ j'₁ j'₂ r₁ r₂ hR₁ hR₂ hj₁ hj₂,
      fun j₁ j₂ e₁ e₂ h₁ h₂ j'₁ j'₂ r₁ r₂ hR₁ hR₂ hj₁ hj₂ =>
        infra_612_tied_symm_copies P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 p q hνp hνq hpσ hqσ
          j₁ j₂ e₁ e₂ h₁ h₂ j'₁ j'₂ r₁ r₂ hR₁ hR₂ hj₁ hj₂,
      fun r hνr hrσ pq qr j₁ j₂ epq eqr e₁ e₂ hPQ h₁ hQR h₂ hνpq hνqr j'₁ j'₂ r₁ r₂ hR₁ hR₂
          hj₁ hj₂ =>
        infra_612_tied_assoc_copies P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 p q r hνp hνq hνr hpσ hqσ
          hrσ pq qr j₁ j₂ epq eqr e₁ e₂ hPQ h₁ hQR h₂ hνpq hνqr j'₁ j'₂ r₁ r₂ hR₁ hR₂ hj₁ hj₂,
      fun n b hb π j₁ j₂ E₁ E₂ h₁ h₂ j'₁ j'₂ r₁ r₂ hR₁ hR₂ hj₁ hj₂ =>
        infra_612_tied_finite_perm_level P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 n b hb π j'₁ j'₂
          (E₁.trans r₁.symm) (E₂.trans r₂.symm)
          (infra_612_finiteLevel_copy P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 n b hb j₁ E₁ h₁
            j'₁ r₁ hR₁ hj₁)
          (infra_612_finiteLevel_copy P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 n (fun i => b (π i))
            (fun i => hb (π i)) j₂ E₂ h₂ j'₂ r₂ hR₂ hj₂) hj₁ hj₂,
      fun n m b hb sf j j' E E' h h' jc jc' r r' hR hR' hjc hjc' =>
        infra_612_tied_finite_proj_level P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 n m b hb sf jc jc'
          (E.trans r.symm) (E'.trans r'.symm)
          (infra_612_finiteLevel_copy P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 n b hb j E h
            jc r hR hjc)
          (infra_612_finiteLevel_copy P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 m (fun i => b (sf i))
            (fun i => hb (sf i)) j' E' h' jc' r' hR' hjc') hjc hjc',
      fun μ' hμ' hμμ' B f hf joint e pB qB jB jB' eP eQ eJ e' hprod hP hQ hJ hprodB hjν hpB hqB
          jC jC' rC rC' hRC hRC' hjC hjC' =>
        infra_612_tied_base_change_copies P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 p q hνp hνq hpσ hqσ
          (Tail.mem hT hμ') hμ'.1 hμ'.2 hμμ' B f hf joint e pB qB jB jB' eP eQ eJ e' hprod hP hQ
          hJ hprodB hjν hpB hqB jC jC' rC rC' hRC hRC' hjC hjC'⟩⟩

/-- **Copies persist over a later base (Prop 7.8 closure requirement 2 at limits; proved).**
If `q` over `X_i = B` is tied free from an earlier `X_j = X` along `X → A → B` (as local
character gives at a stage of cofinality `> λ`), then every long approximation sequence of
`q ↾ A` for an intervening base `A = X_k` still computes `q` over `B`: its copies pushed along
`A → B` form an approximation sequence of `q` with the same test size `τ` and the same
copies (base monotonicity, then `infra_612_pushSeq`, the free-extension theorem). -/
theorem infra_78_copies_persist_at_limits
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {X A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := X) (Y := A) g)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hνμ : q.ν = μ) (hidx : #q.idx ≤ σ)
    (hfree : IsTiedFree (SystemArrow.comp g f)
      (q.restrict (SystemArrow.comp g f) (P.scheme.comp g f hg hf)) q (Equiv.refl _))
    (s : ApproximationSequence (q.restrict f hf))
    (hs : s.τ + ℵ₀ < #s.κIndex) (hsμ : s.τ < μ) :
    ∃ seq : ApproximationSequence q, seq.τ = s.τ ∧ ∃ e : seq.κIndex ≃ s.κIndex,
      ∀ a b, seq.family a b = pushOcc f (s.family (e a) b) := by
  have hF := infra_78_tiedFree_base_mono P σ hσ hμ hrec hσSucc g hg f hf q hνμ hidx hfree
  exact ⟨infra_612_pushSeq f hf le_rfl (q.restrict f hf) q (Equiv.refl _) hF s hs hsμ, rfl,
    Equiv.refl _, fun _ _ => rfl⟩

/-- **Copies persist along a chain (chain form; proved).** For a same-level chain and `p` over
its union with `#p.idx < cf δ`, past some stage `j`, for all `j ≤ k ≤ i`, every long
approximation sequence of `p ↾ X_k` pushed to `X_i` is an approximation sequence of `p ↾ X_i`
(`infra_78_fixed_list_eventually_free` + `infra_612_pushSeq`). -/
theorem infra_78_copies_persist_chain
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    (C : SameLevelChain P hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ C.unionObj)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hcof : #p.idx < C.δ.cof) :
    ∃ j : Ordinal.{u}, ∃ _hj : j < C.δ, ∀ (k i : Ordinal.{u}) (hk : k < C.δ) (hi : i < C.δ),
      j ≤ k → ∀ hki : k ≤ i,
      ∀ s : ApproximationSequence
          ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict (C.le hk hi hki)
            (C.le_arrow hk hi hki)),
        s.τ + ℵ₀ < #s.κIndex → s.τ < μ →
        ∃ seq : ApproximationSequence (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)),
          seq.τ = s.τ ∧ ∃ e : seq.κIndex ≃ s.κIndex,
            ∀ a b, seq.family a b = pushOcc (C.le hk hi hki) (s.family (e a) b) := by
  obtain ⟨j, hj, hF⟩ := infra_78_fixed_list_eventually_free P σ hσ hμ hrec hσSucc C p hνμ hidx hcof
  refine ⟨j, hj, fun k i hk hi hjk hki s hs hsμ => ?_⟩
  exact ⟨infra_612_pushSeq (C.le hk hi hki) (C.le_arrow hk hi hki) le_rfl
    ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict (C.le hk hi hki)
      (C.le_arrow hk hi hki))
    (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)
    (hF k i hk hi hjk hki) s hs hsμ, rfl, Equiv.refl _, fun _ _ => rfl⟩


end
end AEC
