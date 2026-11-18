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

Status: existence is proved (`infra_612_tied_exists`). Independence of choices, symmetry,
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
