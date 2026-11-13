module

public import AEC.Section6.ProductType
public import AEC.Section6.AverageDescent

@[expose] public section

/-!
# Proposition 6.12 — products of bounded types

Same-level `SingleModelData`. Existence realizes `p` by itself and freely lifts `q` along
`p.incl`. Independence, when two free lifts of `q` along one realization of `p` are anchored
to a single approximation code (both type joints are majority values on one parameter list),
is `infra_610_majority_unique` plus the testing criterion.

Deferred: symmetry, `IsFiniteProduct`, base change `(p ⊗ q)^B = p_B ⊗ q^B`, mixed levels,
and stationarity for an untied `IsFreeLift` (its majority witness need not be the type joint;
`same_head` stays demoted).
-/

namespace AEC
section

universe u

open Cardinal FirstOrder

variable {K : AbstractElementaryClass.{u}}

/-- Identity arrows witness `SameGaloisType t t`. The identity is permitted because it is a
structural isomorphism. -/
theorem SameGaloisType.refl {S : SystemShape.{u}} {W : WorkingScheme K S}
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    (t : TupleOver K S W hμ base) :
    SameGaloisType t t (Equiv.refl t.idx) (Equiv.refl t.idx) := by
  have hperm : W.permitted (X := t.host) (Y := t.host)
      (SystemArrow.refl (W.asSystem t.hν t.host)) :=
    W.structural_iso t.host t.host (SystemArrow.refl _) (W.isStructIso_refl t.host)
  refine ⟨t.ν, t.hν, t.host, SystemArrow.refl _, SystemArrow.refl _, hperm, hperm, ?_, ?_⟩
  · intro v
    rfl
  · intro i
    simp [Equiv.refl_symm, SystemArrow.refl, Language.Embedding.refl_apply]

/-- Existence, with the host level a binder so `ν = μ` substitutes. The packed source is the
eta-expansion of the caller's `p`. -/
theorem infra_612_exists_product_aux
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
    (hνq : q.ν = μ) (hqσ : #q.idx ≤ σ) (hqμ : #q.idx < μ) :
    ∃ joint : TupleOver K oneVertexShape P.scheme hμ A,
      ∃ e : idx ⊕ q.idx ≃ joint.idx,
        IsProduct (⟨ν, hν, host, incl, hincl, idx, val⟩ :
            TupleOver K oneVertexShape P.scheme hμ A) q joint e := by
  cases hνμ
  have hmem : hν = hμ := Subsingleton.elim _ _
  cases hmem
  let x : TupleOver K oneVertexShape P.scheme hμ A :=
    ⟨μ, hμ, host, incl, hincl, idx, val⟩
  obtain ⟨y, ey, hy, hyν⟩ :=
    stationary_free_extension_exists P σ hσ hμ hrec hσμ incl hincl q hνq hqσ hqμ
  let joint : TupleOver K oneVertexShape P.scheme hμ A := x.join y
  let ex : idx ≃ x.idx := Equiv.refl _
  let e : idx ⊕ q.idx ≃ joint.idx := Equiv.sumCongr ex ey
  have hjoinν : joint.ν = μ := hyν
  refine ⟨joint, e, x, ex, SameGaloisType.refl x, rfl, y, ey, hy, hyν, hjoinν, ?_⟩
  have hperm : P.scheme.permitted (X := joint.host) (Y := joint.host)
      (SystemArrow.refl (P.scheme.asSystem joint.hν joint.host)) :=
    P.scheme.structural_iso joint.host joint.host (SystemArrow.refl _)
      (P.scheme.isStructIso_refl joint.host)
  refine ⟨joint.ν, joint.hν, joint.host, SystemArrow.refl _, SystemArrow.refl _,
    hperm, hperm, ?_, ?_⟩
  · intro v
    rfl
  · intro i
    have hi : (e.symm.trans (Equiv.sumCongr ex ey)).symm i = i := by
      have hcomp : e.symm.trans (Equiv.sumCongr ex ey) = e.symm.trans e := rfl
      rw [hcomp, Equiv.symm_trans_self]
      rfl
    rw [hi]
    rfl

theorem SameGaloisType.symm {S : SystemShape.{u}} {W : WorkingScheme K S}
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    {t1 t2 : TupleOver K S W hμ base} {ι : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι}
    (h : SameGaloisType t1 t2 e1 e2) : SameGaloisType t2 t1 e2 e1 := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f2, f1, hf2, hf1, ?_, ?_⟩
  · intro v
    exact (hcomm v).symm
  · intro i
    exact (hval i).symm

/-- Move the nontrivial coordinate equivalence from the first tuple onto the second. -/
theorem SameGaloisType.swap_refl {S : SystemShape.{u}} {W : WorkingScheme K S}
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    {t1 t2 : TupleOver K S W hμ base} {e : t1.idx ≃ t2.idx}
    (h : SameGaloisType t1 t2 e (Equiv.refl t2.idx)) :
    SameGaloisType t1 t2 (Equiv.refl t1.idx) e.symm := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro j
  have h := hval (e j)
  rw [Equiv.symm_apply_apply, Equiv.refl_symm] at h
  rw [Equiv.refl_symm, Equiv.symm_symm]
  exact h

/-- Two tuples over the same level-`μ` base have the same Galois type when their diagrams agree
on parameter queries of size at most `P.g σ + ℓ`. Thin wrapper of `infra_610_same_galois` along
the identity arrow. -/
theorem infra_612_same_galois
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    (t1 t2 : TupleOver K oneVertexShape P.scheme hμ A)
    (e : t1.idx ≃ t2.idx)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hσμ : σ < μ)
    (hidx : #t1.idx ≤ σ) (hν1 : t1.ν = μ) (hν2 : t2.ν = μ)
    (hL : ClosedLevel K P.E P.D P.g μ)
    (htest : ∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(t2.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card t1.host.model)
      (h₁ : P.D.t ρ ≤ Model.card t2.host.model),
      P.D.same hjoint t1.host.mem t2.host.mem h₀ h₁
        (Sum.elim (fun i => t1.host.val (t1.val (e.symm i)))
          (fun b => t1.incl.onVertex PUnit.unit (params b)))
        (Sum.elim (fun i => t2.host.val (t2.val i))
          (fun b => t2.incl.onVertex PUnit.unit (params b)))) :
    SameGaloisType t1 t2 e (Equiv.refl t2.idx) := by
  have hId : P.scheme.permitted (X := A) (Y := A)
      (SystemArrow.refl (P.scheme.asSystem hμ A)) :=
    P.scheme.structural_iso A A (SystemArrow.refl _) (P.scheme.isStructIso_refl A)
  have hS := infra_610_same_galois (SystemArrow.refl (P.scheme.asSystem hμ A)) hId t1 t2 e σ hσ
    hσμ hidx hν1 hν2 hL htest
  rcases hS with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, ?_, ?_⟩
  · intro v
    have hcomp : (SystemArrow.comp (SystemArrow.refl (P.scheme.asSystem hμ A)) t2.incl).onVertex v =
        t2.incl.onVertex v := by
      ext x
      simp [SystemArrow.comp, SystemArrow.refl, Language.Embedding.comp_apply,
        Language.Embedding.refl_apply]
    exact (hcomm v).trans (congrArg (f2.onVertex v).comp hcomp)
  · intro i
    have hval' := hval i
    simp only [TupleOver.restrict, Equiv.refl_symm, Equiv.refl_apply] at hval'
    exact hval'

/-- Existence of a binary product: realize `p` by itself and freely lift `q` along `p.incl`. -/
theorem infra_612_exists_product
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hνp : p.ν = μ) (hνq : q.ν = μ)
    (_hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (_hpμ : #p.idx < μ) (hqμ : #q.idx < μ) :
    ∃ joint : TupleOver K oneVertexShape P.scheme hμ A,
      ∃ e : p.idx ⊕ q.idx ≃ joint.idx, IsProduct p q joint e :=
  infra_612_exists_product_aux P σ hσ hμ hrec hσμ hνp p.hν p.host p.incl p.incl_arrow
    p.idx p.val q hνq hqσ hqμ

/-- A Galois identification is a diagram identification over every parameter list. -/
theorem SameGaloisType.to_sameD
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι}
    (h : SameGaloisType t1 t2 e1 e2)
    {β : Type u} (params : β → A.model.carrier)
    (ρ : Cardinal.{u}) (hρinf : aleph0 ≤ ρ) (hjoint : #(ι ⊕ β) ≤ ρ)
    (h₀ : P.D.t ρ ≤ Model.card t1.host.model)
    (h₁ : P.D.t ρ ≤ Model.card t2.host.model) :
    P.D.same hjoint t1.host.mem t2.host.mem h₀ h₁
      (Sum.elim (fun i => t1.host.val (t1.val (e1.symm i)))
        (fun b => t1.incl.onVertex (A.occ (params b)).1 (params b)))
      (Sum.elim (fun i => t2.host.val (t2.val (e2.symm i)))
        (fun b => t2.incl.onVertex (A.occ (params b)).1 (params b))) := by
  rcases h with ⟨_, _, top, f1, f2, _, _, hcomm, hval⟩
  let v0 : oneVertexShape.Vertex := Classical.choice inferInstance
  let g0 : Language.Embedding K.τ t1.host.model.carrier top.model.carrier := f1.onVertex v0
  let g1 : Language.Embedding K.τ t2.host.model.carrier top.model.carrier := f2.onVertex v0
  let xs := Sum.elim (fun i => t1.host.val (t1.val (e1.symm i)))
    (fun b => t1.incl.onVertex (A.occ (params b)).1 (params b))
  let ys := Sum.elim (fun i => t2.host.val (t2.val (e2.symm i)))
    (fun b => t2.incl.onVertex (A.occ (params b)).1 (params b))
  have hmap : ∀ c, g0 (xs c) = g1 (ys c) := by
    intro c
    cases c with
    | inl i =>
      have hv0 : (t1.val (e1.symm i)).1 = v0 := Subsingleton.elim _ _
      have hw0 : (t2.val (e2.symm i)).1 = v0 := Subsingleton.elim _ _
      have hv := hval i
      rw [hv0, hw0] at hv
      change f1.onVertex v0 (t1.val (e1.symm i)).2 = f2.onVertex v0 (t2.val (e2.symm i)).2
      exact eq_of_heq (Sigma.mk.inj hv).2
    | inr b =>
      have hv0 : (A.occ (params b)).1 = v0 := Subsingleton.elim _ _
      change g0 (t1.incl.onVertex v0 (params b)) = g1 (t2.incl.onVertex v0 (params b))
      exact DFunLike.congr_fun (hcomm v0) (params b)
  exact P.D.same_of_amalgam t1.host.mem t2.host.mem top.mem g0 g1
    (f1.onVertex_strong v0) (f2.onVertex_strong v0) xs ys hmap hρinf hjoint h₀ h₁

/-- Compose Galois identifications through a common middle tuple at level `μ`. -/
theorem SameGaloisType.trans_via
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {t1 t2 t3 : TupleOver K oneVertexShape P.scheme hμ A}
    {e12 : t1.idx ≃ t2.idx} {e32 : t3.idx ≃ t2.idx}
    (h12 : SameGaloisType t1 t2 e12 (Equiv.refl t2.idx))
    (h32 : SameGaloisType t2 t3 (Equiv.refl t2.idx) e32)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hσμ : σ < μ)
    (hidx : #t1.idx ≤ σ) (_hrec : μ ∈ recursionClosedLevels P σ)
    (hν1 : t1.ν = μ) (hν2 : t2.ν = μ) (hν3 : t3.ν = μ) :
    SameGaloisType t1 t3 (e12.trans e32.symm) (Equiv.refl t3.idx) := by
  have hL := infra_610_closed_level P σ hσ hμ _hrec
  have hidx3 : #t3.idx ≤ σ := (Cardinal.mk_congr e32).trans_le
    ((Cardinal.mk_congr e12).symm.trans_le hidx)
  apply infra_612_same_galois t1 t3 (e12.trans e32.symm) σ hσ hσμ hidx hν1 hν3 hL
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
  have hc1 : Model.card t1.host.model = μ := by simpa [hν1] using t1.host.card
  have hc3 : Model.card t3.host.model = μ := by simpa [hν3] using t3.host.card
  let σ' : Cardinal.{u} := max ρ0 (ls K)
  have hσ'μ : σ' < μ := max_lt hρμ (P.ls_lt hμ)
  have hσ'inf : aleph0 ≤ σ' := hρinf.trans (le_max_left _ _)
  have ht' : P.D.t σ' ≤ μ := (P.t_lt hμ hσ'inf hσ'μ).le
  let hι : (t3.idx ⊕ β) → (t2.idx ⊕ β) := Sum.map e32 id
  have hL1 := P.D.same_relevel hj2 hρinf hρinf (le_max_left ρ0 (ls K)) (le_max_left ρ0 (ls K))
    (le_max_right ρ0 (ls K)) t1.host.mem t3.host.mem h0 h1
    (ht'.trans hc1.ge) (ht'.trans hc3.ge) h0 h1 _ _ hmid hjnt hι
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

/-- The joint of a free lift with a query from its base, read on the source index of `q`. -/
def infra_612_anchored {qIdx yIdx ι : Type u} {XB XY : SystemObject K oneVertexShape}
    (e : qIdx ≃ yIdx) (incl : SystemArrow K oneVertexShape XB XY)
    (val : yIdx → Occurrence K oneVertexShape XY)
    (Z : ι → Occurrence K oneVertexShape XB) : qIdx ⊕ ι → Occurrence K oneVertexShape XY
  | Sum.inl i => val (e i)
  | Sum.inr j => ⟨(Z j).1, incl.onVertex (Z j).1 (Z j).2⟩

/-- Turn a majority `DiagramEq` into the diagram test used by `infra_612_same_galois`. -/
theorem infra_612_test_of_diagram
    {P : SingleModelData K}
    {ν₁ ν₂ : Cardinal.{u}} {hν₁ : ν₁ ∈ P.eligible} {hν₂ : ν₂ ∈ P.eligible}
    {Y₁ : P.scheme.Object ν₁ hν₁} {Y₂ : P.scheme.Object ν₂ hν₂}
    {α : Type u}
    (xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hν₁ Y₁))
    (ys : α → Occurrence K oneVertexShape (P.scheme.asSystem hν₂ Y₂))
    (hDE : P.scheme.DiagramEq (X := Y₁) (Y := Y₂) xs ys)
    (hα₁ : #α < ν₁) (hα₂ : #α < ν₂)
    (μ : Cardinal.{u}) (hμ : μ ∈ P.eligible)
    (hc₁ : Model.card Y₁.model = μ) (hc₂ : Model.card Y₂.model = μ)
    {β : Type u} {ρ : Cardinal.{u}} (hρinf : aleph0 ≤ ρ) (hρμ : ρ < μ)
    (hjoint : #β ≤ ρ) (ι : β → α) (hαle : #α ≤ ρ)
    (h₀ : P.D.t ρ ≤ Model.card Y₁.model) (h₁ : P.D.t ρ ≤ Model.card Y₂.model) :
    P.D.same hjoint Y₁.mem Y₂.mem h₀ h₁
      (fun c => Y₁.val (xs (ι c))) (fun c => Y₂.val (ys (ι c))) := by
  have hSame : P.D.SameD Y₁.model Y₂.model (fun t => Y₁.val (xs t)) (fun t => Y₂.val (ys t)) :=
    (SingleModelData.diagramEq_iff_sameD (P := P) (α := α) hν₁ hν₂ Y₁ Y₂
      (fun t => Y₁.val (xs t)) (fun t => Y₂.val (ys t)) hα₁ hα₂).mp hDE
  obtain ⟨_, _, hMc, hNc, hs⟩ := hSame
  let ρ0 : Cardinal.{u} := max #α aleph0
  let ρ' : Cardinal.{u} := max ρ (ls K)
  have hρ0inf : aleph0 ≤ ρ0 := le_max_right _ _
  have hρ0le : ρ0 ≤ ρ' :=
    max_le (hαle.trans (le_max_left _ _)) (hρinf.trans (le_max_left _ _))
  have hls : ls K ≤ ρ' := le_max_right _ _
  have hρle' : ρ ≤ ρ' := le_max_left _ _
  have hρ'μ : ρ' < μ := max_lt hρμ (P.ls_lt hμ)
  have hρ'inf : aleph0 ≤ ρ' := hρinf.trans hρle'
  have hMc' : P.D.t ρ' ≤ Model.card Y₁.model :=
    (P.t_lt hμ hρ'inf hρ'μ).le.trans hc₁.ge
  have hNc' : P.D.t ρ' ≤ Model.card Y₂.model :=
    (P.t_lt hμ hρ'inf hρ'μ).le.trans hc₂.ge
  exact P.D.same_relevel (σ := ρ0) (τ := ρ) (σ' := ρ')
    (le_max_left _ _) hρ0inf hρinf hρ0le hρle' hls Y₁.mem Y₂.mem hMc hNc hMc' hNc' h₀ h₁
    _ _ hs hjoint ι

/-- Two free lifts of `q` along one arrow, anchored to one code on a common parameter list,
have the same Galois type over the base. -/
theorem infra_612_freeLift_unique
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (hqσ : #q.idx ≤ σ)
    (y₁ y₂ : TupleOver K oneVertexShape P.scheme hμ B)
    (e₁ : q.idx ≃ y₁.idx) (e₂ : q.idx ≃ y₂.idx)
    (h₁ : IsFreeLift q y₁ f hf e₁) (h₂ : IsFreeLift q y₂ f hf e₂)
    (hν₁ : y₁.ν = μ) (hν₂ : y₂.ν = μ)
    (seq : ApproximationSequence q)
    (hτ : P.g σ + ls K ≤ seq.τ) (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hanchor : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seq Z0 y₁.hν y₁.host
            (infra_612_anchored e₁ y₁.incl y₁.val Z) ∧
          IsMajorityValue seq Z0 y₂.hν y₂.host
            (infra_612_anchored e₂ y₂.incl y₂.val Z)) :
    SameGaloisType y₁ y₂ (e₁.symm.trans e₂) (Equiv.refl y₂.idx) := by
  have hL := infra_610_closed_level P σ hσ hμ hrec
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hidx : #y₁.idx ≤ σ := (Cardinal.mk_congr e₁).symm.trans_le hqσ
  apply infra_612_same_galois y₁ y₂ (e₁.symm.trans e₂) σ hσ hσlt hidx hν₁ hν₂ hL
  intro β hβ ρ0 hρinf hρμ params hjnt h0 h1
  have hβτ : #β ≤ seq.τ := hβ.trans hτ
  let Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) := fun b => B.occ (params b)
  obtain ⟨Z0, hM₁, hM₂⟩ := hanchor Z hβτ
  have hbound : #β + aleph0 < #seq.κIndex := (add_le_add hβτ le_rfl).trans_lt hκ
  have hDE := infra_610_majority_unique seq Z0
    (infra_612_anchored e₁ y₁.incl y₁.val Z) (infra_612_anchored e₂ y₂.incl y₂.val Z)
    hM₁ hM₂ hbound
  let eR : (q.idx ⊕ β) ≃ (y₂.idx ⊕ β) := Equiv.sumCongr e₂ (Equiv.refl β)
  have hDEr : P.scheme.DiagramEq (X := y₁.host) (Y := y₂.host)
      (fun t => infra_612_anchored e₁ y₁.incl y₁.val Z (eR.symm t))
      (fun t => infra_612_anchored e₂ y₂.incl y₂.val Z (eR.symm t)) :=
    (P.scheme.diagram_reindex y₁.host y₂.host eR _ _).mp hDE
  have hαμ : #(q.idx ⊕ β) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) (hqσ.trans_lt hσlt) (hβτ.trans_lt hτμ)
  have hαR : #(y₂.idx ⊕ β) < μ := (Cardinal.mk_congr eR).symm.trans_lt hαμ
  have hc₁ : Model.card y₁.host.model = μ := by simpa [hν₁] using y₁.host.card
  have hc₂ : Model.card y₂.host.model = μ := by simpa [hν₂] using y₂.host.card
  have hα₁ : #(y₂.idx ⊕ β) < y₁.ν := by simpa [hν₁] using hαR
  have hα₂ : #(y₂.idx ⊕ β) < y₂.ν := by simpa [hν₂] using hαR
  have htest := infra_612_test_of_diagram
    (fun t => infra_612_anchored e₁ y₁.incl y₁.val Z (eR.symm t))
    (fun t => infra_612_anchored e₂ y₂.incl y₂.val Z (eR.symm t))
    hDEr hα₁ hα₂ μ hμ hc₁ hc₂ hρinf hρμ hjnt id hjnt h0 h1
  convert htest using 1
  · funext t
    cases t with
    | inl k =>
      simp [infra_612_anchored, eR, Equiv.sumCongr_symm, Equiv.refl_symm,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      rfl
    | inr b =>
      simp [infra_612_anchored, eR, Equiv.sumCongr_symm, Equiv.refl_symm, Z,
        SMObject.occ, oneVertexOcc, SMObject.val, oneVertexVal]
      rfl
  · funext t
    cases t with
    | inl k =>
      simp [infra_612_anchored, eR, Equiv.sumCongr_symm, Equiv.refl_symm,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply]
      rfl
    | inr b =>
      simp [infra_612_anchored, eR, Equiv.sumCongr_symm, Equiv.refl_symm, Z,
        SMObject.occ, oneVertexOcc, SMObject.val, oneVertexVal]
      rfl

/-- Along one realization of `p`, two free lifts of `q` anchored to one code have the same
joint with that realization. The code must reach queries of size `σ + (g(σ) + ℓ)`, the
realization together with a Galois test. -/
theorem infra_612_anchored_join
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (x : TupleOver K oneVertexShape P.scheme hμ A)
    (ex : p.idx ≃ x.idx)
    (y₁ y₂ : TupleOver K oneVertexShape P.scheme x.hν x.host)
    (ey₁ : q.idx ≃ y₁.idx) (ey₂ : q.idx ≃ y₂.idx)
    (hν₁ : y₁.ν = μ) (hν₂ : y₂.ν = μ)
    (seq : ApproximationSequence q)
    (hτ : σ + (P.g σ + ls K) ≤ seq.τ) (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hanchor : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem x.hν x.host)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seq Z0 y₁.hν y₁.host
            (infra_612_anchored ey₁ y₁.incl y₁.val Z) ∧
          IsMajorityValue seq Z0 y₂.hν y₂.host
            (infra_612_anchored ey₂ y₂.incl y₂.val Z)) :
    SameGaloisType (x.join y₁) (x.join y₂)
      (Equiv.sumCongr (Equiv.refl x.idx) (ey₁.symm.trans ey₂))
      (Equiv.refl (x.idx ⊕ y₂.idx)) := by
  have hL := infra_610_closed_level P σ hσ hμ hrec
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hidxEq : (x.join y₁).idx = (x.idx ⊕ y₁.idx) := rfl
  have hidx : #(x.join y₁).idx ≤ σ := by
    rw [hidxEq, mk_sum, lift_id, lift_id]
    exact (add_le_add ((Cardinal.mk_congr ex).symm.trans_le hpσ)
      ((Cardinal.mk_congr ey₁).symm.trans_le hqσ)).trans (Cardinal.add_eq_left hσ le_rfl).le
  apply infra_612_same_galois (x.join y₁) (x.join y₂)
    (Equiv.sumCongr (Equiv.refl x.idx) (ey₁.symm.trans ey₂)) σ hσ hσlt hidx hν₁ hν₂ hL
  intro β hβ ρ0 hρinf hρμ params hjnt h0 h1
  let ι := x.idx ⊕ β
  let Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem x.hν x.host) :=
    Sum.elim x.val (fun b => ⟨(A.occ (params b)).1, x.incl.onVertex (A.occ (params b)).1 (params b)⟩)
  have hι : #ι ≤ seq.τ := by
    rw [show #ι = #(x.idx ⊕ β) from rfl, mk_sum, lift_id, lift_id]
    exact (add_le_add ((Cardinal.mk_congr ex).symm.trans_le hpσ) hβ).trans hτ
  obtain ⟨Z0, hM₁, hM₂⟩ := hanchor Z hι
  have hbound : #ι + aleph0 < #seq.κIndex := (add_le_add hι le_rfl).trans_lt hκ
  have hDE := infra_610_majority_unique seq Z0
    (infra_612_anchored ey₁ y₁.incl y₁.val Z) (infra_612_anchored ey₂ y₂.incl y₂.val Z)
    hM₁ hM₂ hbound
  let ρ : (x.idx ⊕ y₂.idx) ⊕ β → q.idx ⊕ ι
    | Sum.inl (Sum.inl j) => Sum.inr (Sum.inl j)
    | Sum.inl (Sum.inr k) => Sum.inl (ey₂.symm k)
    | Sum.inr b => Sum.inr (Sum.inr b)
  have hαμ : #(q.idx ⊕ ι) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) (hqσ.trans_lt hσlt) (hι.trans_lt hτμ)
  have hc₁ : Model.card y₁.host.model = μ := by simpa [hν₁] using y₁.host.card
  have hc₂ : Model.card y₂.host.model = μ := by simpa [hν₂] using y₂.host.card
  have hα₁ : #(q.idx ⊕ ι) < y₁.ν := by simpa [hν₁] using hαμ
  have hα₂ : #(q.idx ⊕ ι) < y₂.ν := by simpa [hν₂] using hαμ
  have hjoinIdx : (x.join y₂).idx = (x.idx ⊕ y₂.idx) := rfl
  have hαle : #(q.idx ⊕ ι) ≤ ρ0 := by
    have hy : #q.idx = #y₂.idx := Cardinal.mk_congr ey₂
    rw [hjoinIdx] at hjnt
    simp only [ι, mk_sum, lift_id, hy, add_assoc, add_comm, add_left_comm] at hjnt ⊢
    exact hjnt
  have htest := infra_612_test_of_diagram
    (infra_612_anchored ey₁ y₁.incl y₁.val Z) (infra_612_anchored ey₂ y₂.incl y₂.val Z)
    hDE hα₁ hα₂ μ hμ hc₁ hc₂ hρinf hρμ hjnt ρ hαle h0 h1
  have hL : (Sum.elim
      (fun i => (x.join y₁).host.val ((x.join y₁).val
        ((Equiv.sumCongr (Equiv.refl x.idx) (ey₁.symm.trans ey₂)).symm i)))
      (fun b => (x.join y₁).incl.onVertex PUnit.unit (params b))) =
      fun c => y₁.host.val (infra_612_anchored ey₁ y₁.incl y₁.val Z (ρ c)) := by
    funext t
    cases t with
    | inl k =>
      change (x.join y₁).host.val ((x.join y₁).val
        ((Equiv.sumCongr (Equiv.refl x.idx) (ey₁.symm.trans ey₂)).symm k)) = _
      cases k with
      | inl j =>
        rw [Equiv.sumCongr_symm, Equiv.refl_symm, Equiv.sumCongr_apply, Sum.map_inl,
          Equiv.refl_apply]
        simp only [TupleOver.join, infra_612_anchored, ρ, Z, Sum.elim_inl, SMObject.val,
          oneVertexVal]
        rfl
      | inr k =>
        rw [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr, Equiv.symm_trans,
          Equiv.trans_apply, Equiv.symm_symm]
        simp only [TupleOver.join, infra_612_anchored, ρ, SMObject.val, oneVertexVal]
        rfl
    | inr b =>
      change (x.join y₁).incl.onVertex PUnit.unit (params b) =
        y₁.host.val (infra_612_anchored ey₁ y₁.incl y₁.val Z (ρ (Sum.inr b)))
      simp only [infra_612_anchored, ρ, Z, Sum.elim_inr, TupleOver.join, SystemArrow.comp,
        SMObject.occ, oneVertexOcc, SMObject.val, oneVertexVal]
      exact Language.Embedding.comp_apply _ _ _
  have hR : (Sum.elim (fun i => (x.join y₂).host.val ((x.join y₂).val i))
      (fun b => (x.join y₂).incl.onVertex PUnit.unit (params b))) =
      fun c => y₂.host.val (infra_612_anchored ey₂ y₂.incl y₂.val Z (ρ c)) := by
    funext t
    cases t with
    | inl k =>
      change (x.join y₂).host.val ((x.join y₂).val k) = _
      cases k with
      | inl j =>
        simp only [TupleOver.join, infra_612_anchored, ρ, Z, Sum.elim_inl, SMObject.val,
          oneVertexVal]
        rfl
      | inr k =>
        change y₂.host.val (y₂.val k) =
          y₂.host.val (infra_612_anchored ey₂ y₂.incl y₂.val Z (ρ (Sum.inl (Sum.inr k))))
        simp only [infra_612_anchored, ρ, SMObject.val, oneVertexVal]
        rw [Equiv.apply_symm_apply]
    | inr b =>
      change (x.join y₂).incl.onVertex PUnit.unit (params b) =
        y₂.host.val (infra_612_anchored ey₂ y₂.incl y₂.val Z (ρ (Sum.inr b)))
      simp only [infra_612_anchored, ρ, Z, Sum.elim_inr, TupleOver.join, SystemArrow.comp,
        SMObject.occ, oneVertexOcc, SMObject.val, oneVertexVal]
      exact Language.Embedding.comp_apply _ _ _
  refine Eq.mp ?_ htest
  congr 1
  · exact hL.symm
  · exact hR.symm

/-- Independence of two products along one realization, once the free lifts are anchored. -/
theorem infra_612_product_unique
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hpσ : #p.idx ≤ σ) (hqσ : #q.idx ≤ σ)
    (x : TupleOver K oneVertexShape P.scheme hμ A) (ex : p.idx ≃ x.idx)
    (y₁ y₂ : TupleOver K oneVertexShape P.scheme x.hν x.host)
    (ey₁ : q.idx ≃ y₁.idx) (ey₂ : q.idx ≃ y₂.idx)
    (hν₁ : y₁.ν = μ) (hν₂ : y₂.ν = μ)
    (seq : ApproximationSequence q)
    (hτ : σ + (P.g σ + ls K) ≤ seq.τ) (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hanchor : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem x.hν x.host)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seq Z0 y₁.hν y₁.host
            (infra_612_anchored ey₁ y₁.incl y₁.val Z) ∧
          IsMajorityValue seq Z0 y₂.hν y₂.host
            (infra_612_anchored ey₂ y₂.incl y₂.val Z))
    (joint₁ joint₂ : TupleOver K oneVertexShape P.scheme hμ A)
    (e₁ : p.idx ⊕ q.idx ≃ joint₁.idx) (e₂ : p.idx ⊕ q.idx ≃ joint₂.idx)
    (hJ₁ : SameGaloisType joint₁ (x.join y₁)
      (e₁.symm.trans (Equiv.sumCongr ex ey₁)) (Equiv.refl (x.idx ⊕ y₁.idx)))
    (hJ₂ : SameGaloisType joint₂ (x.join y₂)
      (e₂.symm.trans (Equiv.sumCongr ex ey₂)) (Equiv.refl (x.idx ⊕ y₂.idx)))
    (hνj₁ : joint₁.ν = μ) (hνj₂ : joint₂.ν = μ) :
    SameGaloisType joint₁ joint₂ (e₁.symm.trans e₂) (Equiv.refl joint₂.idx) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hsum : #(p.idx ⊕ q.idx) ≤ σ := by
    rw [mk_sum, lift_id, lift_id]
    exact (add_le_add hpσ hqσ).trans (Cardinal.add_eq_left hσ le_rfl).le
  have hcard₁ : #joint₁.idx ≤ σ := (Cardinal.mk_congr e₁).symm.trans_le hsum
  have hidxJoin : #(x.join y₁).idx ≤ σ := by
    have hidxEq : (x.join y₁).idx = (x.idx ⊕ y₁.idx) := rfl
    rw [hidxEq, mk_sum, lift_id, lift_id]
    exact (add_le_add ((Cardinal.mk_congr ex).symm.trans_le hpσ)
      ((Cardinal.mk_congr ey₁).symm.trans_le hqσ)).trans (Cardinal.add_eq_left hσ le_rfl).le
  let φ₁ : joint₁.idx ≃ (x.idx ⊕ y₁.idx) := e₁.symm.trans (Equiv.sumCongr ex ey₁)
  let φ₂ : joint₂.idx ≃ (x.idx ⊕ y₂.idx) := e₂.symm.trans (Equiv.sumCongr ex ey₂)
  let ψ : (x.idx ⊕ y₁.idx) ≃ (x.idx ⊕ y₂.idx) :=
    Equiv.sumCongr (Equiv.refl x.idx) (ey₁.symm.trans ey₂)
  have hjoin := infra_612_anchored_join P σ hσ hμ hrec hσμ p q hpσ hqσ x ex y₁ y₂ ey₁ ey₂
    hν₁ hν₂ seq hτ hτμ hκ hanchor
  have hJ₁' : SameGaloisType joint₁ (x.join y₁) φ₁ (Equiv.refl (x.idx ⊕ y₁.idx)) := hJ₁
  have hJ₂' : SameGaloisType joint₂ (x.join y₂) φ₂ (Equiv.refl (x.idx ⊕ y₂.idx)) := hJ₂
  have hmid := SameGaloisType.trans_via hjoin hJ₂'.symm σ hσ hσlt hidxJoin hrec hν₁ hν₂ hνj₂
  have hbridge := hmid.swap_refl
  have hvia := SameGaloisType.trans_via hJ₁' hbridge σ hσ hσlt hcard₁ hrec hνj₁ hν₁ hνj₂
  have hcomp : φ₁.trans (ψ.trans φ₂.symm) = e₁.symm.trans e₂ := by
    ext j
    cases hsumm : e₁.symm j with
    | inl a =>
      simp [φ₁, φ₂, ψ, hsumm, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.sumCongr_symm,
        Equiv.symm_apply_apply, Equiv.refl_apply, Equiv.refl_symm]
    | inr b =>
      simp [φ₁, φ₂, ψ, hsumm, Equiv.trans_apply, Equiv.sumCongr_apply, Equiv.sumCongr_symm,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply, Equiv.refl_symm]
  exact hcomp ▸ hvia

end
end AEC
