module

public import AEC.Section7.AllDominated
public import AEC.Section7.RelativeIsolationTransfer
public import AEC.Section4.ClosedLevelAmalgam
public import AEC.Section4.Prop43BAF
public import AEC.Section5.SingleModelPackage

@[expose] public section

/-!
# Proposition 7.5 — primeness of all-dominated objects

Path A close for `SingleModelData`: same-level clause 1 (embedding over `X` sending `b` to `b'`)
and clause 2 (structural isomorphism of two all-dominated objects). English clause 3 (product
freeness), mixed-level targets, and prescribed extra tuple matches are demoted.
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function Set

attribute [local instance] Classical.propDecidable

set_option linter.unusedVariables false

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-! ## Tail -/

def infra_75_tailSet (P : SingleModelData K) (σ : Cardinal.{u}) : Set Cardinal.{u} :=
  {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}

theorem infra_75_tail (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    Tail P.eligible (infra_75_tailSet P σ) := by
  refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
  obtain ⟨μ, hle, hμ, hrec⟩ :=
    (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
  exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩

/-! ## Small lemmas -/

theorem infra_75_onVertex_unit
    {X Y : SystemObject K oneVertexShape}
    (f : SystemArrow K oneVertexShape X Y) (v : oneVertexShape.Vertex) :
    f.onVertex v = f.onVertex PUnit.unit := by
  have hv : v = PUnit.unit := Subsingleton.elim _ _
  rw [hv]

theorem infra_75_occ_carrier_inl
    {Y : SystemObject K oneVertexShape} {bIdx γ : Type u}
    (b : bIdx → Occurrence K oneVertexShape Y)
    (c : γ → Occurrence K oneVertexShape Y) (i : bIdx) :
    (seqJoint b c (Sum.inl i)).2 = (b i).2 :=
  rfl

theorem infra_75_occ_carrier_inr
    {Y : SystemObject K oneVertexShape} {bIdx γ : Type u}
    (b : bIdx → Occurrence K oneVertexShape Y)
    (c : γ → Occurrence K oneVertexShape Y) (j : γ) :
    (seqJoint b c (Sum.inr j)).2 = (c j).2 :=
  rfl

theorem infra_75_add2_lt {μ a b : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (ha : a < μ) (hb : b < μ) :
    a + b < μ :=
  add_lt_of_lt hμ ha hb

theorem infra_75_refl_coe {α : Type u} (x : α) : (Equiv.refl α) x = x := rfl

theorem infra_75_refl_symm_coe {α : Type u} (x : α) : (Equiv.refl α).symm x = x := rfl

theorem infra_75_sum_lt {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) {α β : Type u}
    (hα : #α < μ) (hβ : #β < μ) : #(α ⊕ β) < μ := by
  simp only [mk_sum, lift_id]
  exact infra_75_add2_lt hμ hα hβ

theorem infra_75_onVertex_eq_unit
    {X Y : SystemObject K oneVertexShape}
    (f : SystemArrow K oneVertexShape X Y)
    {v : oneVertexShape.Vertex} (hv : v = PUnit.unit)
    (x : (X.obj PUnit.unit).carrier) :
    f.onVertex v x = f.onVertex PUnit.unit x := by
  subst hv
  rfl

/-- Push a carrier through the unique vertex map. -/
theorem infra_75_push_unit
    {X Y : SystemObject K oneVertexShape}
    (f : SystemArrow K oneVertexShape X Y)
    (x : Occurrence K oneVertexShape X) :
    f.onVertex x.1 x.2 = f.onVertex PUnit.unit x.2 := by
  cases x with
  | mk v a =>
      cases Subsingleton.elim v PUnit.unit
      rfl

theorem infra_75_galois_symm
    {S : SystemShape.{u}} {W : WorkingScheme K S}
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    {t1 t2 : TupleOver K S W hμ base} {idx : Type u}
    {e1 : t1.idx ≃ idx} {e2 : t2.idx ≃ idx}
    (h : SameGaloisType t1 t2 e1 e2) :
    SameGaloisType t2 t1 e2 e1 := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  exact ⟨ρ, hρ, top, f2, f1, hf2, hf1, fun v => (hcomm v).symm, fun i => (hval i).symm⟩

theorem infra_75_galois_image
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X Y N : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hf : P.scheme.permitted (X := X) (Y := N) f)
    {bIdx δ : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (s : δ → Y.model.carrier) (s' t : δ → N.model.carrier)
    (hs : ∀ k, s' k = t k)
    (h : SameGaloisType
      (asTuple incl hincl (seqJoint b (fun k => Y.occ (s k))))
      (asTuple f hf (seqJoint b' (fun k => N.occ (s' k))))
      (Equiv.refl (bIdx ⊕ δ)) (Equiv.refl (bIdx ⊕ δ))) :
    SameGaloisType
      (asTuple incl hincl (seqJoint b (fun k => Y.occ (s k))))
      (asTuple f hf (seqJoint b' (fun k => N.occ (t k))))
      (Equiv.refl (bIdx ⊕ δ)) (Equiv.refl (bIdx ⊕ δ)) := by
  have hseq : seqJoint b' (fun k => N.occ (s' k)) = seqJoint b' (fun k => N.occ (t k)) := by
    funext i
    cases i with
    | inl _ => rfl
    | inr k => exact congrArg N.occ (hs k)
  rw [← hseq]
  exact h

/-- A Galois match of `b` is a Galois match of `b` padded by the empty index. -/
theorem infra_75_galois_pad_empty
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X Y N : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hf : P.scheme.permitted (X := X) (Y := N) f)
    {bIdx : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (h : SameGaloisType (asTuple incl hincl b) (asTuple f hf b')
      (Equiv.refl bIdx) (Equiv.refl bIdx)) :
    SameGaloisType
      (asTuple incl hincl (seqJoint b (fun e : PEmpty.{u + 1} => Y.occ e.elim)))
      (asTuple f hf (seqJoint b' (fun e : PEmpty.{u + 1} => N.occ e.elim)))
      (Equiv.refl (bIdx ⊕ PEmpty.{u + 1})) (Equiv.refl (bIdx ⊕ PEmpty.{u + 1})) := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro i
  cases i with
  | inl a =>
      simp only [asTuple, seqJoint, Equiv.refl_symm]
      exact hval a
  | inr e => exact e.elim

/-- Appending base parameters, with the prescribed images under the two base arrows, preserves
the Galois type (the same amalgam identifies the new coordinates by commutation). -/
theorem infra_75_append_base
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X Y N : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hf : P.scheme.permitted (X := X) (Y := N) f)
    {bIdx γ β : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (c : γ → Y.model.carrier) (c' : γ → N.model.carrier)
    (z : β → X.model.carrier)
    (hGal : SameGaloisType
      (asTuple incl hincl (seqJoint b (fun j => Y.occ (c j))))
      (asTuple f hf (seqJoint b' (fun j => N.occ (c' j))))
      (Equiv.refl (bIdx ⊕ γ)) (Equiv.refl (bIdx ⊕ γ))) :
    SameGaloisType
      (asTuple incl hincl (seqJoint b
        (fun j : γ ⊕ β => Y.occ (Sum.elim c (fun k => incl.onVertex PUnit.unit (z k)) j))))
      (asTuple f hf (seqJoint b'
        (fun j : γ ⊕ β => N.occ (Sum.elim c' (fun k => f.onVertex PUnit.unit (z k)) j))))
      (Equiv.refl (bIdx ⊕ (γ ⊕ β))) (Equiv.refl (bIdx ⊕ (γ ⊕ β))) := by
  rcases hGal with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro i
  cases i with
  | inl a =>
      simp only [asTuple, seqJoint, Equiv.refl_symm]
      exact hval (Sum.inl a)
  | inr j =>
      cases j with
      | inl t =>
          simp only [asTuple, seqJoint, Equiv.refl_symm, Sum.elim_inl]
          exact hval (Sum.inr t)
      | inr k =>
          let v0 : oneVertexShape.Vertex := PUnit.unit
          have hpush := DFunLike.congr_fun (hcomm v0) (z k)
          simp only [asTuple, seqJoint, Equiv.refl_symm, Sum.elim_inr]
          exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq hpush)

/-- Equal coordinates of a Galois match have equal images. -/
theorem infra_75_preserves_eq
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X Y N : P.scheme.Object μ hμ} {ι : Type u}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hf : P.scheme.permitted (X := X) (Y := N) f)
    (v1 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (v2 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (h : SameGaloisType (asTuple incl hincl v1) (asTuple f hf v2)
      (Equiv.refl ι) (Equiv.refl ι))
    (hidx : #ι < μ) {i j : ι} (hij : (v1 i).2 = (v1 j).2) :
    (v2 i).2 = (v2 j).2 := by
  rcases h with ⟨_, _, top, f1, f2, _, _, _, hval⟩
  let v0 : oneVertexShape.Vertex := PUnit.unit
  let g0 := f1.onVertex v0
  let g1 := f2.onVertex v0
  let ρc : Cardinal.{u} := max #ι ℵ₀
  have hρinf : ℵ₀ ≤ ρc := le_max_right _ _
  have hρμ : ρc < μ := max_lt hidx (P.aleph0_lt hμ)
  have hle : #ι ≤ ρc := le_max_left _ _
  have hc1 : P.D.t ρc ≤ Model.card Y.model := by
    rw [Y.card]; exact (P.t_lt hμ hρinf hρμ).le
  have hc2 : P.D.t ρc ≤ Model.card N.model := by
    rw [N.card]; exact (P.t_lt hμ hρinf hρμ).le
  have hmap : ∀ k, g0 (v1 k).2 = g1 (v2 k).2 := by
    intro k
    have hv := hval k
    obtain ⟨_, hsnd⟩ := Sigma.ext_iff.mp hv
    have hEqv := eq_of_heq hsnd
    have hEL := infra_75_onVertex_eq_unit
      (v := ((asTuple incl hincl v1).val ((Equiv.refl ι).symm k)).1)
      f1 (Subsingleton.elim _ _)
      ((asTuple incl hincl v1).val ((Equiv.refl ι).symm k)).2
    have hER := infra_75_onVertex_eq_unit
      (v := ((asTuple f hf v2).val ((Equiv.refl ι).symm k)).1)
      f2 (Subsingleton.elim _ _)
      ((asTuple f hf v2).val ((Equiv.refl ι).symm k)).2
    exact hEL.symm.trans (hEqv.trans hER)
  have hsame := P.D.same_of_amalgam Y.mem N.mem top.mem g0 g1
    (f1.onVertex_strong v0) (f2.onVertex_strong v0)
    (fun k => (v1 k).2) (fun k => (v2 k).2) hmap hρinf hle hc1 hc2
  exact (P.D.preserves_atomic hle Y.mem N.mem hc1 hc2 _ _ hsame i j).mp hij

/-- A coordinate equal to a base parameter is sent to the image of that parameter. -/
theorem infra_75_fixes_carrier
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X Y N : P.scheme.Object μ hμ} {ι : Type u}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hf : P.scheme.permitted (X := X) (Y := N) f)
    (v1 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (v2 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (h : SameGaloisType (asTuple incl hincl v1) (asTuple f hf v2)
      (Equiv.refl ι) (Equiv.refl ι))
    {i : ι} {a : X.model.carrier}
    (hi : (v1 i).2 = incl.onVertex PUnit.unit a) :
    (v2 i).2 = f.onVertex PUnit.unit a := by
  rcases h with ⟨_, _, _, f1, f2, _, _, hcomm, hval⟩
  let v0 : oneVertexShape.Vertex := PUnit.unit
  have hv := hval i
  obtain ⟨_, hsnd⟩ := Sigma.ext_iff.mp hv
  have hEqv := eq_of_heq hsnd
  have hEL := infra_75_onVertex_eq_unit
    (v := ((asTuple incl hincl v1).val ((Equiv.refl ι).symm i)).1)
    f1 (Subsingleton.elim _ _)
    ((asTuple incl hincl v1).val ((Equiv.refl ι).symm i)).2
  have hER := infra_75_onVertex_eq_unit
    (v := ((asTuple f hf v2).val ((Equiv.refl ι).symm i)).1)
    f2 (Subsingleton.elim _ _)
    ((asTuple f hf v2).val ((Equiv.refl ι).symm i)).2
  have himg := hEL.symm.trans (hEqv.trans hER)
  have himg' : f1.onVertex v0 (v1 i).2 = f2.onVertex v0 (v2 i).2 := himg
  have hpush : f1.onVertex v0 (incl.onVertex v0 a) = f2.onVertex v0 (f.onVertex v0 a) :=
    DFunLike.congr_fun (hcomm v0) a
  have : f2.onVertex v0 (v2 i).2 = f2.onVertex v0 (f.onVertex v0 a) := by
    rw [← himg', hi, hpush]
  exact (f2.onVertex v0).injective this

theorem infra_75_cd_of_hits
    {ι A Y N : Type u} [K.τ.Structure A] [K.τ.Structure Y] [K.τ.Structure N]
    (ιA : A ↪[K.τ] Y) (ρA : A ↪[K.τ] N)
    (ys : ι → Y) (ns : ι → N)
    (h : ∀ i, ∃ a, ιA a = ys i ∧ ρA a = ns i) :
    CommonDomain K.τ (Set.range fun i => (ys i, ns i)) :=
  ⟨A, inferInstance, ιA, ρA, fun p hp => by
    rcases hp with ⟨i, rfl⟩
    simpa using h i⟩

/-! ## Placing one bounded extension inside `N` -/

/-- Realize a bounded list `s` from `Y` inside `N`, extending a Galois match of `b + c` and
using relative isolation of `b + s`. The common hull is the saturation step: its second leg
lands in `N`. -/
theorem infra_75_place
    {P : SingleModelData K} {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {X Y N : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hf : P.scheme.permitted (X := X) (Y := N) f)
    {bIdx γ δ : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (c : γ → Y.model.carrier) (c' : γ → N.model.carrier)
    (s : δ → Y.model.carrier)
    (hγ : #(bIdx ⊕ γ) < μ) (hδ : #δ < μ)
    (hGalB : SameGaloisType (asTuple incl hincl b) (asTuple f hf b')
      (Equiv.refl bIdx) (Equiv.refl bIdx))
    (hGal : SameGaloisType
      (asTuple incl hincl (seqJoint b (fun j => Y.occ (c j))))
      (asTuple f hf (seqJoint b' (fun j => N.occ (c' j))))
      (Equiv.refl (bIdx ⊕ γ)) (Equiv.refl (bIdx ⊕ γ)))
    (hIso : IsRelativelyIsolated (uIdx := bIdx) (cIdx := δ)
      (asTuple incl hincl (seqJoint b (fun k => Y.occ (s k))))
      (Equiv.refl (bIdx ⊕ δ))) :
    ∃ s' : δ → N.model.carrier,
      SameGaloisType
        (asTuple incl hincl (seqJoint b (fun k => Y.occ (s k))))
        (asTuple f hf (seqJoint b' (fun k => N.occ (s' k))))
        (Equiv.refl (bIdx ⊕ δ)) (Equiv.refl (bIdx ⊕ δ)) ∧
      (∀ k (i : bIdx ⊕ γ),
        s k = (seqJoint b (fun j => Y.occ (c j)) i).2 →
        s' k = (seqJoint b' (fun j => N.occ (c' j)) i).2) ∧
      ∃ (A : Model K.τ)
        (ιA : Language.Embedding K.τ A.carrier Y.model.carrier)
        (ρA : Language.Embedding K.τ A.carrier N.model.carrier),
        K.Strong ιA ∧ K.Strong ρA ∧
        (∀ i : bIdx ⊕ δ, ∃ a,
          ιA a = (seqJoint b (fun k => Y.occ (s k)) i).2 ∧
          ρA a = (seqJoint b' (fun k => N.occ (s' k)) i).2) := by
  classical
  rcases hIso with ⟨β, Z, hβ, hfrag⟩
  let tOld := asTuple incl hincl (seqJoint b (fun j => Y.occ (c j)))
  let tOld' := asTuple f hf (seqJoint b' (fun j => N.occ (c' j)))
  let zc : β → X.model.carrier := fun j => (Z j).2
  let κ : Cardinal.{u} :=
    max (max (max #(bIdx ⊕ γ) #β) (max #δ ℵ₀)) (ls K)
  have hκinf : ℵ₀ ≤ κ :=
    (le_max_right (#δ) ℵ₀).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hκμ : κ < μ :=
    max_lt (max_lt (max_lt hγ hβ) (max_lt hδ (P.aleph0_lt hμ))) (P.ls_lt hμ)
  have hls : ls K ≤ κ := le_max_right _ _
  have hγle : #(bIdx ⊕ γ) ≤ κ :=
    (le_max_left (#(bIdx ⊕ γ)) #β).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hβle : #β ≤ κ :=
    (le_max_right (#(bIdx ⊕ γ)) #β).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hδle : #δ ≤ κ :=
    (le_max_left #δ ℵ₀).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hαle : #((bIdx ⊕ γ) ⊕ β) ≤ κ := by
    simp only [mk_sum, lift_id]
    exact add_le_of_le hκinf hγle hβle
  have hMc : P.D.t κ ≤ Model.card Y.model := by
    rw [Y.card]; exact (P.t_lt hμ hκinf hκμ).le
  have hNc : P.D.t κ ≤ Model.card N.model := by
    rw [N.card]; exact (P.t_lt hμ hκinf hκμ).le
  let e0 : (bIdx ⊕ γ) ≃ (bIdx ⊕ γ) := Equiv.refl _
  let xs : ((bIdx ⊕ γ) ⊕ β) → Y.model.carrier :=
    Sum.elim (fun i => tOld.host.val (tOld.val (e0 i)))
      (fun j => tOld.incl.onVertex (X.occ (zc j)).1 (zc j))
  let ys : ((bIdx ⊕ γ) ⊕ β) → N.model.carrier :=
    Sum.elim (fun i => tOld'.host.val (tOld'.val (e0 i)))
      (fun j => tOld'.incl.onVertex (X.occ (zc j)).1 (zc j))
  have hsame : P.D.same hαle Y.mem N.mem hMc hNc xs ys :=
    SameGaloisType.to_sameD (P := P) hGal zc κ hκinf hαle hMc hNc
  let S : Set Y.model.carrier := Set.range s
  have hS : #S ≤ P.D.t κ :=
    (mk_range_le.trans hδle).trans (le_of_lt (sigma_lt_t P.D hκinf))
  obtain ⟨A, ιA, ρA, hAmem, hcA, hιA, hρA, hhit, hcovS⟩ :=
    P.D.exists_common_hull hαle hκinf (le_refl κ) hls Y.mem N.mem hMc hNc hMc hNc xs ys hsame S hS
  have hPick : ∀ k, ∃ a, ιA a = s k := fun k => hcovS (s k) ⟨k, rfl⟩
  let aS : δ → A.carrier := fun k => Classical.choose (hPick k)
  have haS : ∀ k, ιA (aS k) = s k := fun k => Classical.choose_spec (hPick k)
  let s' : δ → N.model.carrier := fun k => ρA (aS k)
  have hover : ∀ k (i : bIdx ⊕ γ),
      s k = (seqJoint b (fun j => Y.occ (c j)) i).2 →
      s' k = (seqJoint b' (fun j => N.occ (c' j)) i).2 := by
    intro k i hk
    obtain ⟨a, haι, haρ⟩ := hhit (Sum.inl i)
    have hxs : xs (Sum.inl i) = (seqJoint b (fun j => Y.occ (c j)) i).2 := by
      simp only [xs, Sum.elim_inl, tOld, asTuple, e0, infra_75_refl_coe, SMObject.val, oneVertexVal]
      rfl
    have hys : ys (Sum.inl i) = (seqJoint b' (fun j => N.occ (c' j)) i).2 := by
      simp only [ys, Sum.elim_inl, tOld', asTuple, e0, infra_75_refl_coe, SMObject.val, oneVertexVal]
      rfl
    have haι' : ιA a = s k := hk ▸ hxs.symm ▸ haι
    have haeq : aS k = a := ιA.injective ((haS k).trans haι'.symm)
    have hs' : s' k = ρA (aS k) := rfl
    exact hs'.trans ((congrArg ρA haeq).trans (haρ.trans hys))
  let qS := asTuple incl hincl (seqJoint b (fun k => Y.occ (s k)))
  let qS' := asTuple f hf (seqJoint b' (fun k => N.occ (s' k)))
  let listY := alignJoint (Equiv.refl (bIdx ⊕ δ)) (typeJoint (p := qS) Z)
  let listN := alignJoint (Equiv.refl (bIdx ⊕ δ)) (typeJoint (p := qS') Z)
  let θ := (bIdx ⊕ δ) ⊕ β
  have hsumγ : #bIdx + #γ < μ := by simpa [mk_sum, lift_id] using hγ
  have hbμ : #bIdx < μ := lt_of_le_of_lt le_self_add hsumγ
  have hθμ : #θ < μ :=
    infra_75_sum_lt (P.aleph0_le hμ) (infra_75_sum_lt (P.aleph0_le hμ) hbμ hδ) hβ
  have hθle : #θ ≤ κ := by
    have hb : #bIdx ≤ #(bIdx ⊕ γ) := by
      simp only [mk_sum, lift_id]; exact le_self_add
    have hbκ : #bIdx ≤ κ := hb.trans hγle
    simp only [θ, mk_sum, lift_id]
    have hbd : #bIdx + #δ ≤ κ := add_le_of_le hκinf hbκ hδle
    exact add_le_of_le hκinf hbd hβle
  let zY : β → Y.model.carrier := fun j => incl.onVertex (X.occ (zc j)).1 (zc j)
  let zN : β → N.model.carrier := fun j => f.onVertex (X.occ (zc j)).1 (zc j)
  let fullY : θ → Y.model.carrier
    | Sum.inl (Sum.inl i) => (b i).2
    | Sum.inl (Sum.inr k) => s k
    | Sum.inr j => zY j
  let fullN : θ → N.model.carrier
    | Sum.inl (Sum.inl i) => (b' i).2
    | Sum.inl (Sum.inr k) => s' k
    | Sum.inr j => zN j
  have hBspec : ∀ i : bIdx, ∃ a, ιA a = (b i).2 ∧ ρA a = (b' i).2 := by
    intro i
    obtain ⟨a, haι, haρ⟩ := hhit (Sum.inl (Sum.inl i))
    have hxs : xs (Sum.inl (Sum.inl i)) = (b i).2 := by
      simp only [xs, Sum.elim_inl, tOld, asTuple, e0, infra_75_refl_coe, seqJoint, SMObject.val,
        oneVertexVal]
      rfl
    have hys : ys (Sum.inl (Sum.inl i)) = (b' i).2 := by
      simp only [ys, Sum.elim_inl, tOld', asTuple, e0, infra_75_refl_coe, seqJoint, SMObject.val,
        oneVertexVal]
      rfl
    exact ⟨a, haι.trans hxs, haρ.trans hys⟩
  let aθ : θ → A.carrier
    | Sum.inl (Sum.inl i) => Classical.choose (hBspec i)
    | Sum.inl (Sum.inr k) => aS k
    | Sum.inr j => Classical.choose (hhit (Sum.inr j))
  have haθι : ∀ t, ιA (aθ t) = fullY t := by
    intro t
    match t with
    | Sum.inl (Sum.inl i) =>
        simpa [aθ, fullY] using (Classical.choose_spec (hBspec i)).1
    | Sum.inl (Sum.inr k) =>
        simpa [aθ, fullY] using haS k
    | Sum.inr j =>
        have hspec := Classical.choose_spec (hhit (Sum.inr j))
        have hxs : xs (Sum.inr j) = zY j := by
          simp only [xs, Sum.elim_inr, zY]
          rfl
        simpa [aθ, fullY, hxs] using hspec.1
  have haθρ : ∀ t, ρA (aθ t) = fullN t := by
    intro t
    match t with
    | Sum.inl (Sum.inl i) =>
        simpa [aθ, fullN] using (Classical.choose_spec (hBspec i)).2
    | Sum.inl (Sum.inr k) =>
        simp [aθ, fullN, s']
    | Sum.inr j =>
        have hspec := Classical.choose_spec (hhit (Sum.inr j))
        have hys : ys (Sum.inr j) = zN j := by
          simp only [ys, Sum.elim_inr, zN]
          rfl
        simpa [aθ, fullN, hys] using hspec.2
  let σs : Cardinal.{u} := max #θ ℵ₀
  have hσsinf : ℵ₀ ≤ σs := le_max_right _ _
  have hσsμ : σs < μ := max_lt hθμ (P.aleph0_lt hμ)
  have hσsle : #θ ≤ σs := le_max_left _ _
  have hσsκ : σs ≤ κ := max_le hθle hκinf
  have hYs : P.D.t σs ≤ Model.card Y.model := by
    rw [Y.card]; exact (P.t_lt hμ hσsinf hσsμ).le
  have hNs : P.D.t σs ≤ Model.card N.model := by
    rw [N.card]; exact (P.t_lt hμ hσsinf hσsμ).le
  have hAs : P.D.t σs ≤ Model.card A := by
    rw [hcA]; exact P.D.mono σs κ hσsκ
  have hsameθ := P.D.same_of_common_hull hσsle hσsinf hAmem Y.mem N.mem hAs hYs hNs
    ιA ρA hιA hρA aθ fullY fullN haθι haθρ
  have hSameD : P.D.SameD Y.model N.model fullY fullN :=
    ⟨Y.mem, N.mem, hYs, hNs, hsameθ⟩
  have hDE : SingleModelData.DiagramEq hμ hμ Y N fullY fullN :=
    (SingleModelData.diagramEq_iff_sameD hμ hμ Y N fullY fullN hθμ hθμ).mpr hSameD
  have hcarrierY : ∀ t, (listY t).2 = fullY t := by
    intro t
    match t with
    | Sum.inl (Sum.inl i) =>
        simp [listY, alignJoint, typeJoint, qS, asTuple, seqJoint, fullY, Equiv.refl_symm]
    | Sum.inl (Sum.inr k) =>
        simp [listY, alignJoint, typeJoint, qS, asTuple, seqJoint, fullY, Equiv.refl_symm,
          SMObject.val, SMObject.occ, oneVertexOcc]
        rfl
    | Sum.inr j =>
        simp [listY, alignJoint, typeJoint, qS, asTuple, fullY, zY, zc, Equiv.refl_symm,
          SMObject.occ, oneVertexOcc]
        exact infra_75_push_unit incl (Z j)
  have hcarrierN : ∀ t, (listN t).2 = fullN t := by
    intro t
    match t with
    | Sum.inl (Sum.inl i) =>
        simp [listN, alignJoint, typeJoint, qS', asTuple, seqJoint, fullN, Equiv.refl_symm]
    | Sum.inl (Sum.inr k) =>
        simp [listN, alignJoint, typeJoint, qS', asTuple, seqJoint, fullN, Equiv.refl_symm,
          SMObject.val, SMObject.occ, oneVertexOcc]
        rfl
    | Sum.inr j =>
        simp [listN, alignJoint, typeJoint, qS', asTuple, fullN, zN, zc, Equiv.refl_symm,
          SMObject.occ, oneVertexOcc]
        exact infra_75_push_unit f (Z j)
  have hDiag : P.scheme.DiagramEq (X := qS.host) (Y := qS'.host) listY listN := by
    have hfunY : (fun t => (listY t).2) = fullY := funext hcarrierY
    have hfunN : (fun t => (listN t).2) = fullN := funext hcarrierN
    change SingleModelData.DiagramEq hμ hμ qS.host qS'.host
      (fun t => (listY t).2) (fun t => (listN t).2)
    simp only [hfunY, hfunN, asTuple] at hDE ⊢
    exact hDE
  have hMarg : SameGaloisType (qS.marginal (Equiv.refl (bIdx ⊕ δ)))
      (qS'.marginal (Equiv.refl (bIdx ⊕ δ))) (Equiv.refl bIdx) (Equiv.refl bIdx) := by
    simpa [qS, qS', TupleOver.marginal, asTuple, seqJoint, Equiv.refl_symm] using hGalB
  have hGalS := hfrag qS' (Equiv.refl (bIdx ⊕ δ)) rfl hMarg hDiag
  refine ⟨s', hGalS, hover, A, ιA, ρA, hιA, hρA, ?_⟩
  intro i
  refine ⟨aθ (Sum.inl i), ?_, ?_⟩
  · have h1 := haθι (Sum.inl i)
    cases i with
    | inl a =>
        simpa [fullY, seqJoint, SMObject.val, oneVertexVal] using h1
    | inr k =>
        have hocc : (Y.occ (s k)).2 = s k := rfl
        simpa [fullY, seqJoint, hocc] using h1
  · have h1 := haθρ (Sum.inl i)
    cases i with
    | inl a =>
        simpa [fullN, seqJoint, SMObject.val, oneVertexVal] using h1
    | inr k =>
        have hocc : (N.occ (s' k)).2 = s' k := rfl
        simpa [fullN, seqJoint, s', hocc] using h1

/-! ## Clause 1: the embedding -/

theorem infra_75_tower_step
    {P : SingleModelData K} {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {X Y N : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hf : P.scheme.permitted (X := X) (Y := N) f)
    {bIdx : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (hGalB : SameGaloisType (asTuple incl hincl b) (asTuple f hf b')
      (Equiv.refl bIdx) (Equiv.refl bIdx))
    {M M' : Model K.τ}
    (j : Language.Embedding K.τ M.carrier Y.model.carrier) (hj : K.Strong j)
    (j' : Language.Embedding K.τ M'.carrier Y.model.carrier) (hj' : K.Strong j')
    (hM : Model.card M < μ) (hM' : Model.card M' < μ)
    (ι : M.carrier → M'.carrier) (hι : ∀ x, j' (ι x) = j x)
    (hPrev : Language.Embedding K.τ M.carrier N.model.carrier)
    (hγ : #(bIdx ⊕ M.carrier) < μ) (hb : #bIdx < μ)
    (hGal : SameGaloisType
      (asTuple incl hincl (seqJoint b (fun x => Y.occ (j x))))
      (asTuple f hf (seqJoint b' (fun x => N.occ (hPrev x))))
      (Equiv.refl (bIdx ⊕ M.carrier)) (Equiv.refl (bIdx ⊕ M.carrier)))
    (hIso : IsRelativelyIsolated (uIdx := bIdx) (cIdx := M'.carrier)
      (asTuple incl hincl (seqJoint b (fun x => Y.occ (j' x))))
      (Equiv.refl (bIdx ⊕ M'.carrier))) :
    ∃ h' : Language.Embedding K.τ M'.carrier N.model.carrier,
      K.Strong h' ∧
      SameGaloisType
        (asTuple incl hincl (seqJoint b (fun x => Y.occ (j' x))))
        (asTuple f hf (seqJoint b' (fun x => N.occ (h' x))))
        (Equiv.refl (bIdx ⊕ M'.carrier)) (Equiv.refl (bIdx ⊕ M'.carrier)) ∧
      ∀ x, h' (ι x) = hPrev x := by
  classical
  obtain ⟨s', hGalS, hover, A, ιA, ρA, hιA, hρA, hhit⟩ :=
    infra_75_place hμ incl hincl f hf b b' (fun x => j x) (fun x => hPrev x)
      (fun x => j' x) hγ (by simpa [Model.card] using hM') hGalB hGal hIso
  have himg : ∀ x : M'.carrier, ∃ a, ιA a = j' x := by
    intro x
    obtain ⟨a, ha, _⟩ := hhit (Sum.inr x)
    have hocc : (Y.occ (j' x)).2 = j' x := rfl
    exact ⟨a, by simpa [seqJoint, hocc] using ha⟩
  let h' := ρA.comp (factorEmbedding j' ιA himg)
  have hh' : K.Strong h' :=
    K.strong_trans _ _ (strong_factorEmbedding j' ιA hj' hιA himg) hρA
  have hfun : ∀ x, h' x = s' x := by
    intro x
    obtain ⟨a, haι, haρ⟩ := hhit (Sum.inr x)
    have hocc : (Y.occ (j' x)).2 = j' x := rfl
    have hocc' : (N.occ (s' x)).2 = s' x := rfl
    have haι' : ιA a = j' x := by simpa [seqJoint, hocc] using haι
    have haρ' : ρA a = s' x := by simpa [seqJoint, hocc'] using haρ
    have hfac := factorEmbedding_apply j' ιA himg x
    have haeq : factorEmbedding j' ιA himg x = a := ιA.injective (hfac.trans haι'.symm)
    have hs' : h' x = ρA (factorEmbedding j' ιA himg x) := rfl
    exact hs'.trans ((congrArg ρA haeq).trans haρ')
  refine ⟨h', hh', infra_75_galois_image incl hincl f hf b b' (fun x => j' x) s' h'
      (fun x => (hfun x).symm) hGalS, ?_⟩
  intro x
  have harg : j' (ι x) = (seqJoint b (fun y => Y.occ (j y)) (Sum.inr x)).2 := by
    have hocc : (Y.occ (j x)).2 = j x := rfl
    simpa [seqJoint, hocc] using hι x
  have hprev : (seqJoint b' (fun y => N.occ (hPrev y)) (Sum.inr x)).2 = hPrev x := by
    have hocc : (N.occ (hPrev x)).2 = hPrev x := rfl
    simp [seqJoint, hocc]
    rfl
  exact (hfun (ι x)).trans ((hover (ι x) (Sum.inr x) harg).trans hprev)

theorem infra_75_stage0
    {P : SingleModelData K} {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {X Y N : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hf : P.scheme.permitted (X := X) (Y := N) f)
    {bIdx : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (hGalB : SameGaloisType (asTuple incl hincl b) (asTuple f hf b')
      (Equiv.refl bIdx) (Equiv.refl bIdx))
    {M : Model K.τ}
    (j : Language.Embedding K.τ M.carrier Y.model.carrier) (hj : K.Strong j)
    (hM : Model.card M < μ) (hb : #bIdx < μ)
    (hIso : IsRelativelyIsolated (uIdx := bIdx) (cIdx := M.carrier)
      (asTuple incl hincl (seqJoint b (fun x => Y.occ (j x))))
      (Equiv.refl (bIdx ⊕ M.carrier))) :
    ∃ h : Language.Embedding K.τ M.carrier N.model.carrier,
      K.Strong h ∧
      SameGaloisType
        (asTuple incl hincl (seqJoint b (fun x => Y.occ (j x))))
        (asTuple f hf (seqJoint b' (fun x => N.occ (h x))))
        (Equiv.refl (bIdx ⊕ M.carrier)) (Equiv.refl (bIdx ⊕ M.carrier)) := by
  classical
  have hγ : #(bIdx ⊕ PEmpty.{u + 1}) < μ := by
    simp only [mk_sum, mk_pempty, lift_id, add_zero]; exact hb
  have hPad := infra_75_galois_pad_empty incl hincl f hf b b' hGalB
  obtain ⟨s', hGalS, _, A, ιA, ρA, hιA, hρA, hhit⟩ :=
    infra_75_place hμ incl hincl f hf b b'
      (fun e : PEmpty.{u + 1} => e.elim) (fun e : PEmpty.{u + 1} => e.elim)
      (fun x => j x) hγ (by simpa [Model.card] using hM) hGalB hPad hIso
  have himg : ∀ x : M.carrier, ∃ a, ιA a = j x := by
    intro x
    obtain ⟨a, ha, _⟩ := hhit (Sum.inr x)
    have hocc : (Y.occ (j x)).2 = j x := rfl
    exact ⟨a, by simpa [seqJoint, hocc] using ha⟩
  let h := ρA.comp (factorEmbedding j ιA himg)
  have hh : K.Strong h :=
    K.strong_trans _ _ (strong_factorEmbedding j ιA hj hιA himg) hρA
  have hfun : ∀ x, h x = s' x := by
    intro x
    obtain ⟨a, haι, haρ⟩ := hhit (Sum.inr x)
    have hocc : (Y.occ (j x)).2 = j x := rfl
    have hocc' : (N.occ (s' x)).2 = s' x := rfl
    have haι' : ιA a = j x := by simpa [seqJoint, hocc] using haι
    have haρ' : ρA a = s' x := by simpa [seqJoint, hocc'] using haρ
    have hfac := factorEmbedding_apply j ιA himg x
    have haeq : factorEmbedding j ιA himg x = a := ιA.injective (hfac.trans haι'.symm)
    have hs' : h x = ρA (factorEmbedding j ιA himg x) := rfl
    exact hs'.trans ((congrArg ρA haeq).trans haρ')
  exact ⟨h, hh, infra_75_galois_image incl hincl f hf b b' (fun x => j x) s' h
    (fun x => (hfun x).symm) hGalS⟩

theorem infra_75_embed
    {P : SingleModelData K} {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (X Y N : P.scheme.Object μ hμ)
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hf : P.scheme.permitted (X := X) (Y := N) f)
    {bIdx : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (hb : #bIdx < μ)
    (hGalB : SameGaloisType (asTuple incl hincl b) (asTuple f hf b')
      (Equiv.refl bIdx) (Equiv.refl bIdx))
    (hAll : AllDominated incl hincl bIdx b) :
    ∃ g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ N),
      P.scheme.permitted (X := Y) (Y := N) g ∧
      SystemArrow.comp incl g = f ∧
      ∀ i, g.onVertex (b i).1 (b i).2 = (b' i).2 := by
  classical
  obtain ⟨M, j, hj, hMc, hmono, hcov, hd⟩ :=
    exists_strong_tower Y.mem (P.aleph0_le hμ) hμ.1.working.countableCof (P.ls_lt hμ)
      Y.card (fun i => (b i).2) hb
  choose ιS hιS using hmono
  have hIso0 := hAll (M 0).carrier (fun x => Y.occ (j 0 x)) (by simpa [Model.card] using hMc 0)
  obtain ⟨h0, hh0, hGal0⟩ :=
    infra_75_stage0 hμ incl hincl f hf b b' hGalB (j 0) (hj 0) (hMc 0) hb hIso0
  let Stage (n : ℕ) :=
    { p : Language.Embedding K.τ (M n).carrier N.model.carrier //
      K.Strong p ∧
      SameGaloisType
        (asTuple incl hincl (seqJoint b (fun x => Y.occ (j n x))))
        (asTuple f hf (seqJoint b' (fun x => N.occ (p x))))
        (Equiv.refl (bIdx ⊕ (M n).carrier)) (Equiv.refl (bIdx ⊕ (M n).carrier)) }
  have hstep : ∀ n (prev : Stage n), ∃ s : Stage (n + 1), ∀ x, s.1 (ιS n x) = prev.1 x := by
    intro n prev
    have hIso := hAll (M (n + 1)).carrier (fun x => Y.occ (j (n + 1) x))
      (by simpa [Model.card] using hMc (n + 1))
    have hγ : #(bIdx ⊕ (M n).carrier) < μ :=
      infra_75_sum_lt (P.aleph0_le hμ) hb (by simpa [Model.card] using hMc n)
    obtain ⟨h', hh', hGal', hext⟩ :=
      infra_75_tower_step hμ incl hincl f hf b b' hGalB (j n) (hj n) (j (n + 1)) (hj (n + 1))
        (hMc n) (hMc (n + 1)) (ιS n) (hιS n) prev.1 hγ hb prev.2.2 hIso
    exact ⟨⟨h', hh', hGal'⟩, hext⟩
  let seq : ∀ n, Stage n := fun n =>
    Nat.rec (motive := fun n => Stage n) ⟨h0, hh0, hGal0⟩
      (fun n prev => Classical.choose (hstep n prev)) n
  have hseq : ∀ n x, (seq (n + 1)).1 (ιS n x) = (seq n).1 x :=
    fun n => Classical.choose_spec (hstep n (seq n))
  have hcoh : ∀ n x y, j (n + 1) y = j n x → (seq (n + 1)).1 y = (seq n).1 x := by
    intro n x y hxy
    have hy : y = ιS n x := (j (n + 1)).injective (hxy.trans (hιS n x).symm)
    rw [hy]
    exact hseq n x
  obtain ⟨F, hF, hFj⟩ := exists_strong_of_nat_exhaustion Y.mem N.mem M j hj
    (fun n x => ⟨ιS n x, hιS n x⟩) hcov (fun n => (seq n).1) (fun n => (seq n).2.1) hcoh
  refine ⟨oneVertexArrow F hF, trivial, ?_, ?_⟩
  · apply SystemArrow.ext
    intro v
    ext a
    have hv : v = PUnit.unit := Subsingleton.elim _ _
    have hunit : incl.onVertex v a = incl.onVertex PUnit.unit a :=
      infra_75_onVertex_eq_unit incl hv a
    have funit : f.onVertex v a = f.onVertex PUnit.unit a :=
      infra_75_onVertex_eq_unit f hv a
    obtain ⟨n, x, hx⟩ := hcov (incl.onVertex PUnit.unit a)
    have hidx : #(bIdx ⊕ (M n).carrier) < μ :=
      infra_75_sum_lt (P.aleph0_le hμ) hb (by simpa [Model.card] using hMc n)
    have hi : (seqJoint b (fun y => Y.occ (j n y)) (Sum.inr x)).2 =
        incl.onVertex PUnit.unit a := by
      have hseq : (seqJoint b (fun y => Y.occ (j n y)) (Sum.inr x)).2 = j n x := rfl
      exact hseq.trans hx
    have hfix := infra_75_fixes_carrier incl hincl f hf
      (seqJoint b (fun y => Y.occ (j n y)))
      (seqJoint b' (fun y => N.occ ((seq n).1 y))) (seq n).2.2 (i := Sum.inr x) hi
    have hFx : F (j n x) = (seq n).1 x := hFj n x
    change F (incl.onVertex v a) = f.onVertex v a
    rw [hunit, funit, ← hx, hFx]
    exact hfix
  · intro i
    obtain ⟨x, hx⟩ := hd i
    have hidx : #(bIdx ⊕ (M 0).carrier) < μ :=
      infra_75_sum_lt (P.aleph0_le hμ) hb (by simpa [Model.card] using hMc 0)
    have hij : (seqJoint b (fun y => Y.occ (j 0 y)) (Sum.inl i)).2 =
        (seqJoint b (fun y => Y.occ (j 0 y)) (Sum.inr x)).2 := by
      have hL : (seqJoint b (fun y => Y.occ (j 0 y)) (Sum.inl i)).2 = (b i).2 := rfl
      have hR : (seqJoint b (fun y => Y.occ (j 0 y)) (Sum.inr x)).2 = j 0 x := rfl
      exact hL.trans ((hx.symm).trans hR.symm)
    have heq := infra_75_preserves_eq incl hincl f hf
      (seqJoint b (fun y => Y.occ (j 0 y)))
      (seqJoint b' (fun y => N.occ ((seq 0).1 y))) (seq 0).2.2 hidx hij
    have hFx : F (j 0 x) = (seq 0).1 x := hFj 0 x
    change (oneVertexArrow (hM := Y.mem) (hN := N.mem) F hF).onVertex (b i).1 (b i).2 = (b' i).2
    have hv : (b i).1 = PUnit.unit := Subsingleton.elim _ _
    have hcar := infra_75_onVertex_eq_unit
      (oneVertexArrow (hM := Y.mem) (hN := N.mem) F hF) hv (b i).2
    rw [hcar]
    change F (b i).2 = (b' i).2
    have hbcar : (b i).2 = j 0 x := hx.symm
    rw [hbcar, hFx]
    have hb' : (seqJoint b' (fun y => N.occ ((seq 0).1 y)) (Sum.inl i)).2 = (b' i).2 := by
      simp [seqJoint]
    have himg : (seqJoint b' (fun y => N.occ ((seq 0).1 y)) (Sum.inr x)).2 = (seq 0).1 x := by
      have hocc : (N.occ ((seq 0).1 x)).2 = (seq 0).1 x := rfl
      simp [seqJoint, hocc]
      rfl
    rw [← himg, ← hb', heq]

/-! ## Clause 2: the structural isomorphism -/

theorem infra_75_extend_list
    {P : SingleModelData K} {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {X Y N : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hf : P.scheme.permitted (X := X) (Y := N) f)
    {bIdx γ δ : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (c : γ → Y.model.carrier) (c' : γ → N.model.carrier)
    (s : δ → Y.model.carrier)
    (hγ : #(bIdx ⊕ γ) < μ) (hδ : #δ < μ) (hb : #bIdx < μ)
    (hGalB : SameGaloisType (asTuple incl hincl b) (asTuple f hf b')
      (Equiv.refl bIdx) (Equiv.refl bIdx))
    (hGal : SameGaloisType
      (asTuple incl hincl (seqJoint b (fun j => Y.occ (c j))))
      (asTuple f hf (seqJoint b' (fun j => N.occ (c' j))))
      (Equiv.refl (bIdx ⊕ γ)) (Equiv.refl (bIdx ⊕ γ)))
    (hIso : IsRelativelyIsolated (uIdx := bIdx) (cIdx := γ ⊕ δ)
      (asTuple incl hincl (seqJoint b (fun t : γ ⊕ δ => Y.occ (Sum.elim c s t))))
      (Equiv.refl (bIdx ⊕ (γ ⊕ δ)))) :
    ∃ s' : (γ ⊕ δ) → N.model.carrier,
      SameGaloisType
        (asTuple incl hincl (seqJoint b (fun t : γ ⊕ δ => Y.occ (Sum.elim c s t))))
        (asTuple f hf (seqJoint b' (fun t : γ ⊕ δ => N.occ (s' t))))
        (Equiv.refl (bIdx ⊕ (γ ⊕ δ))) (Equiv.refl (bIdx ⊕ (γ ⊕ δ))) ∧
      (∀ j, s' (Sum.inl j) = c' j) ∧
      ∃ (A : Model K.τ)
        (ιA : Language.Embedding K.τ A.carrier Y.model.carrier)
        (ρA : Language.Embedding K.τ A.carrier N.model.carrier),
        K.Strong ιA ∧ K.Strong ρA ∧
        ∀ i : bIdx ⊕ (γ ⊕ δ), ∃ a,
          ιA a = (seqJoint b (fun t => Y.occ (Sum.elim c s t)) i).2 ∧
          ρA a = (seqJoint b' (fun t => N.occ (s' t)) i).2 := by
  have hδ' : #(γ ⊕ δ) < μ := by
    have hγ' : #γ < μ := by
      have hinj : #γ ≤ #(bIdx ⊕ γ) :=
        Cardinal.mk_le_of_injective (f := fun j : γ => Sum.inr j) (fun a b h => Sum.inr.inj h)
      exact hinj.trans_lt hγ
    exact infra_75_sum_lt (P.aleph0_le hμ) hγ' hδ
  obtain ⟨s', hGalS, hover, A, ιA, ρA, hιA, hρA, hhit⟩ :=
    infra_75_place hμ incl hincl f hf b b' c c' (fun t => Sum.elim c s t) hγ hδ' hGalB hGal hIso
  refine ⟨s', hGalS, ?_, A, ιA, ρA, hιA, hρA, hhit⟩
  intro j
  have harg : Sum.elim c s (Sum.inl j) =
      (seqJoint b (fun k => Y.occ (c k)) (Sum.inr j)).2 := by
    have hocc : (Y.occ (c j)).2 = c j := rfl
    simp [seqJoint, hocc, Sum.elim_inl]
  have hprev : (seqJoint b' (fun k => N.occ (c' k)) (Sum.inr j)).2 = c' j := by
    have hocc : (N.occ (c' j)).2 = c' j := rfl
    simp [seqJoint, hocc]
    rfl
  exact (hover (Sum.inl j) (Sum.inr j) harg).trans hprev

structure Infra75Enum (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (X Y Y₂ : P.scheme.Object μ hμ)
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (incl₂ : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y₂))
    (hincl₂ : P.scheme.permitted (X := X) (Y := Y₂) incl₂)
    (bIdx : Type u)
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b₂ : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y₂)) where
  γ : Type u
  c : γ → Y.model.carrier
  c₂ : γ → Y₂.model.carrier
  card : #(bIdx ⊕ γ) < μ
  gal : SameGaloisType
    (asTuple incl hincl (seqJoint b (fun j => Y.occ (c j))))
    (asTuple incl₂ hincl₂ (seqJoint b₂ (fun j => Y₂.occ (c₂ j))))
    (Equiv.refl (bIdx ⊕ γ)) (Equiv.refl (bIdx ⊕ γ))
  cd : CommonDomain K.τ
    (Set.range (fun i : bIdx ⊕ γ =>
      (((seqJoint b (fun j => Y.occ (c j)) i).2 : Y.model.carrier),
       ((seqJoint b₂ (fun j => Y₂.occ (c₂ j)) i).2 : Y₂.model.carrier))) :
      Set (Y.model.carrier × Y₂.model.carrier))

theorem infra_75_baf_step
    {P : SingleModelData K} {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {X Y Y₂ : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (incl₂ : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y₂))
    (hincl₂ : P.scheme.permitted (X := X) (Y := Y₂) incl₂)
    {bIdx : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b₂ : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y₂))
    (hb : #bIdx < μ)
    (hGalB : SameGaloisType (asTuple incl hincl b) (asTuple incl₂ hincl₂ b₂)
      (Equiv.refl bIdx) (Equiv.refl bIdx))
    (hAll : AllDominated incl hincl bIdx b)
    (hAll₂ : AllDominated incl₂ hincl₂ bIdx b₂)
    (st : Infra75Enum P hμ X Y Y₂ incl hincl incl₂ hincl₂ bIdx b b₂)
    {β δY δ₂ : Type u}
    (z : β → X.model.carrier) (sY : δY → Y.model.carrier) (s₂ : δ₂ → Y₂.model.carrier)
    (hβ : #β < μ) (hδY : #δY < μ) (hδ₂ : #δ₂ < μ) :
    ∃ st' : Infra75Enum P hμ X Y Y₂ incl hincl incl₂ hincl₂ bIdx b b₂,
      ∃ θ : bIdx ⊕ st.γ → bIdx ⊕ st'.γ,
        (∀ i,
          (seqJoint b (fun j => Y.occ (st'.c j)) (θ i)).2 =
            (seqJoint b (fun j => Y.occ (st.c j)) i).2 ∧
          (seqJoint b₂ (fun j => Y₂.occ (st'.c₂ j)) (θ i)).2 =
            (seqJoint b₂ (fun j => Y₂.occ (st.c₂ j)) i).2) ∧
        (∀ k, ∃ i, st'.c i = sY k) ∧
        (∀ k, ∃ i, st'.c₂ i = s₂ k) ∧
        (∀ k, ∃ i, st'.c i = incl.onVertex PUnit.unit (z k) ∧
          st'.c₂ i = incl₂.onVertex PUnit.unit (z k)) := by
  classical
  have hγlt : #st.γ < μ := by
    have hinj : #st.γ ≤ #(bIdx ⊕ st.γ) :=
      Cardinal.mk_le_of_injective (f := fun j : st.γ => Sum.inr j) (fun a b h => Sum.inr.inj h)
    exact hinj.trans_lt st.card
  have hγβ : #(st.γ ⊕ β) < μ := infra_75_sum_lt (P.aleph0_le hμ) hγlt hβ
  have hcard1 : #(bIdx ⊕ (st.γ ⊕ β)) < μ := infra_75_sum_lt (P.aleph0_le hμ) hb hγβ
  let c1 : st.γ ⊕ β → Y.model.carrier :=
    Sum.elim st.c (fun k => incl.onVertex PUnit.unit (z k))
  let c21 : st.γ ⊕ β → Y₂.model.carrier :=
    Sum.elim st.c₂ (fun k => incl₂.onVertex PUnit.unit (z k))
  have hGal1 := infra_75_append_base incl hincl incl₂ hincl₂ b b₂ st.c st.c₂ z st.gal
  have hjoin : #((st.γ ⊕ β) ⊕ δY) < μ := infra_75_sum_lt (P.aleph0_le hμ) hγβ hδY
  have hIso1 := hAll ((st.γ ⊕ β) ⊕ δY) (fun t => Y.occ (Sum.elim c1 sY t)) hjoin
  obtain ⟨sY', hGalY, hExtY, _, _, _, _, _, _⟩ :=
    infra_75_extend_list hμ incl hincl incl₂ hincl₂ b b₂ c1 c21 sY hcard1 hδY hb hGalB hGal1 hIso1
  have hGalY' := infra_75_galois_symm hGalY
  let yEnum : (st.γ ⊕ β) ⊕ δY → Y.model.carrier := Sum.elim c1 sY
  have hcard2 : #(bIdx ⊕ ((st.γ ⊕ β) ⊕ δY)) < μ := infra_75_sum_lt (P.aleph0_le hμ) hb hjoin
  have hjoin2 : #(((st.γ ⊕ β) ⊕ δY) ⊕ δ₂) < μ := infra_75_sum_lt (P.aleph0_le hμ) hjoin hδ₂
  have hIso2 := hAll₂ (((st.γ ⊕ β) ⊕ δY) ⊕ δ₂) (fun t => Y₂.occ (Sum.elim sY' s₂ t)) hjoin2
  have hGalB' := infra_75_galois_symm hGalB
  obtain ⟨sPre, hGalBack, hExtBack, A, ιA, ρA, hιA, hρA, hhit⟩ :=
    infra_75_extend_list hμ incl₂ hincl₂ incl hincl b₂ b sY' yEnum s₂ hcard2 hδ₂ hb hGalB' hGalY'
      hIso2
  have hGal' := infra_75_galois_symm hGalBack
  let src : ((st.γ ⊕ β) ⊕ δY) ⊕ δ₂ → Y₂.model.carrier := Sum.elim sY' s₂
  have hcd := infra_75_cd_of_hits ρA ιA
    (fun i : bIdx ⊕ (((st.γ ⊕ β) ⊕ δY) ⊕ δ₂) =>
      (seqJoint b (fun j => Y.occ (sPre j)) i).2)
    (fun i => (seqJoint b₂ (fun j => Y₂.occ (src j)) i).2)
    (fun i => by
      obtain ⟨a, haι, haρ⟩ := hhit i
      exact ⟨a, haρ, haι⟩)
  let st' : Infra75Enum P hμ X Y Y₂ incl hincl incl₂ hincl₂ bIdx b b₂ :=
    { γ := ((st.γ ⊕ β) ⊕ δY) ⊕ δ₂
      c := sPre
      c₂ := src
      card := infra_75_sum_lt (P.aleph0_le hμ) hb hjoin2
      gal := hGal'
      cd := hcd }
  let θ : bIdx ⊕ st.γ → bIdx ⊕ st'.γ
    | Sum.inl i => Sum.inl i
    | Sum.inr j => Sum.inr (Sum.inl (Sum.inl (Sum.inl j)))
  refine ⟨st', θ, ?_, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | inl _ =>
        exact ⟨rfl, rfl⟩
    | inr j =>
        have hY : sPre (Sum.inl (Sum.inl (Sum.inl j))) = st.c j := by
          have h1 := hExtBack (Sum.inl (Sum.inl j))
          have hy : yEnum (Sum.inl (Sum.inl j)) = st.c j := rfl
          exact h1.trans hy
        have h2s : src (Sum.inl (Sum.inl (Sum.inl j))) = st.c₂ j := by
          have h1 := hExtY (Sum.inl j)
          have hs : src (Sum.inl (Sum.inl (Sum.inl j))) = sY' (Sum.inl (Sum.inl j)) := rfl
          have hc : c21 (Sum.inl j) = st.c₂ j := rfl
          exact hs.trans (h1.trans hc)
        have hθ : θ (Sum.inr j) = Sum.inr (Sum.inl (Sum.inl (Sum.inl j))) := rfl
        refine ⟨?_, ?_⟩
        · rw [hθ]
          have hocc : (seqJoint b (fun t => Y.occ (st'.c t))
              (Sum.inr (Sum.inl (Sum.inl (Sum.inl j))))).2 =
              sPre (Sum.inl (Sum.inl (Sum.inl j))) := rfl
          have hright : (seqJoint b (fun t => Y.occ (st.c t)) (Sum.inr j)).2 = st.c j := rfl
          exact (hocc.trans hY).trans hright.symm
        · rw [hθ]
          have hocc : (seqJoint b₂ (fun t => Y₂.occ (st'.c₂ t))
              (Sum.inr (Sum.inl (Sum.inl (Sum.inl j))))).2 =
              src (Sum.inl (Sum.inl (Sum.inl j))) := rfl
          have hright : (seqJoint b₂ (fun t => Y₂.occ (st.c₂ t)) (Sum.inr j)).2 = st.c₂ j := rfl
          exact (hocc.trans h2s).trans hright.symm
  · intro k
    refine ⟨Sum.inl (Sum.inr k), ?_⟩
    have h1 := hExtBack (Sum.inr k)
    have hy : yEnum (Sum.inr k) = sY k := rfl
    exact h1.trans hy
  · intro k
    exact ⟨Sum.inr k, rfl⟩
  · intro k
    refine ⟨Sum.inl (Sum.inl (Sum.inr k)), ?_, ?_⟩
    · have h1 := hExtBack (Sum.inl (Sum.inr k))
      have hy : yEnum (Sum.inl (Sum.inr k)) = incl.onVertex PUnit.unit (z k) := rfl
      exact h1.trans hy
    · have h1 := hExtY (Sum.inr k)
      have hs : src (Sum.inl (Sum.inl (Sum.inr k))) = sY' (Sum.inl (Sum.inr k)) := rfl
      have hc : c21 (Sum.inr k) = incl₂.onVertex PUnit.unit (z k) := rfl
      exact hs.trans (h1.trans hc)

theorem infra_75_iso
    {P : SingleModelData K} {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (X Y Y₂ : P.scheme.Object μ hμ)
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    (incl₂ : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y₂))
    (hincl₂ : P.scheme.permitted (X := X) (Y := Y₂) incl₂)
    {bIdx : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b₂ : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y₂))
    (hb : #bIdx < μ)
    (hAll : AllDominated incl hincl bIdx b)
    (hAll₂ : AllDominated incl₂ hincl₂ bIdx b₂)
    (hGalB : SameGaloisType (asTuple incl hincl b) (asTuple incl₂ hincl₂ b₂)
      (Equiv.refl bIdx) (Equiv.refl bIdx)) :
    ∃ φ : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ Y₂),
      P.scheme.IsStructIso (X := Y) (Y := Y₂) φ ∧
      SystemArrow.comp incl φ = incl₂ ∧
      ∀ i, φ.onVertex (b i).1 (b i).2 = (b₂ i).2 := by
  classical
  obtain ⟨AY, hAY, _, hAYcov⟩ := exists_countable_set_exhaustion
    (by simpa [Model.card] using Y.card) (P.aleph0_le hμ) hμ.1.working.countableCof
  obtain ⟨A2, hA2, _, hA2cov⟩ := exists_countable_set_exhaustion
    (by simpa [Model.card] using Y₂.card) (P.aleph0_le hμ) hμ.1.working.countableCof
  obtain ⟨AX, hAX, _, hAXcov⟩ := exists_countable_set_exhaustion
    (by simpa [Model.card] using X.card) (P.aleph0_le hμ) hμ.1.working.countableCof
  have hγ0 : #(bIdx ⊕ PEmpty.{u + 1}) < μ := by
    simp only [mk_sum, mk_pempty, lift_id, add_zero]; exact hb
  have hPad := infra_75_galois_pad_empty incl hincl incl₂ hincl₂ b b₂ hGalB
  have hempty : #(PEmpty.{u + 1}) < μ := by
    simpa [mk_pempty] using (Cardinal.aleph0_pos.trans_le (P.aleph0_le hμ))
  have hIsoE := hAll PEmpty.{u + 1} (fun e => Y.occ e.elim) hempty
  obtain ⟨s0, hGal0, _, _, ιA0, ρA0, _, _, hhit0⟩ :=
    infra_75_place hμ incl hincl incl₂ hincl₂ b b₂
      (fun e : PEmpty.{u + 1} => e.elim) (fun e : PEmpty.{u + 1} => e.elim)
      (fun e : PEmpty.{u + 1} => e.elim) hγ0 hempty hGalB hPad hIsoE
  have hcd0 : CommonDomain K.τ
      (Set.range (fun i : bIdx ⊕ PEmpty.{u + 1} =>
        (((seqJoint b (fun j => Y.occ (j.elim : Y.model.carrier)) i).2 : Y.model.carrier),
         ((seqJoint b₂ (fun j => Y₂.occ (s0 j)) i).2 : Y₂.model.carrier))) :
        Set (Y.model.carrier × Y₂.model.carrier)) :=
    infra_75_cd_of_hits ιA0 ρA0 _ _ hhit0
  let st0 : Infra75Enum P hμ X Y Y₂ incl hincl incl₂ hincl₂ bIdx b b₂ :=
    { γ := PEmpty.{u + 1}
      c := fun e => e.elim
      c₂ := s0
      card := hγ0
      gal := hGal0
      cd := hcd0 }
  have hstep : ∀ n (st : Infra75Enum P hμ X Y Y₂ incl hincl incl₂ hincl₂ bIdx b b₂),
      ∃ st' : Infra75Enum P hμ X Y Y₂ incl hincl incl₂ hincl₂ bIdx b b₂,
        ∃ θ : bIdx ⊕ st.γ → bIdx ⊕ st'.γ,
          (∀ i,
            (seqJoint b (fun j => Y.occ (st'.c j)) (θ i)).2 =
              (seqJoint b (fun j => Y.occ (st.c j)) i).2 ∧
            (seqJoint b₂ (fun j => Y₂.occ (st'.c₂ j)) (θ i)).2 =
              (seqJoint b₂ (fun j => Y₂.occ (st.c₂ j)) i).2) ∧
          (∀ a : ↥(AY n), ∃ i, st'.c i = a.1) ∧
          (∀ a : ↥(A2 n), ∃ i, st'.c₂ i = a.1) ∧
          (∀ a : ↥(AX n), ∃ i, st'.c i = incl.onVertex PUnit.unit a.1 ∧
            st'.c₂ i = incl₂.onVertex PUnit.unit a.1) := by
    intro n st
    have hβ : #(↥(AX n)) < μ := by simpa using hAX n
    have hδY : #(↥(AY n)) < μ := by simpa using hAY n
    have hδ₂ : #(↥(A2 n)) < μ := by simpa using hA2 n
    exact infra_75_baf_step hμ incl hincl incl₂ hincl₂ b b₂ hb hGalB hAll hAll₂ st
      (fun a : ↥(AX n) => a.1) (fun a : ↥(AY n) => a.1) (fun a : ↥(A2 n) => a.1) hβ hδY hδ₂
  let next (n : ℕ) (st : Infra75Enum P hμ X Y Y₂ incl hincl incl₂ hincl₂ bIdx b b₂) :=
    Classical.choose (hstep n st)
  let seq : ℕ → Infra75Enum P hμ X Y Y₂ incl hincl incl₂ hincl₂ bIdx b b₂ :=
    fun n => Nat.rec (motive := fun _ => Infra75Enum P hμ X Y Y₂ incl hincl incl₂ hincl₂ bIdx b b₂)
      st0 (fun n st => next n st) n
  let rel (st : Infra75Enum P hμ X Y Y₂ incl hincl incl₂ hincl₂ bIdx b b₂) :
      Set (Y.model.carrier × Y₂.model.carrier) :=
    Set.range fun i : bIdx ⊕ st.γ =>
      ((seqJoint b (fun j => Y.occ (st.c j)) i).2,
       (seqJoint b₂ (fun j => Y₂.occ (st.c₂ j)) i).2)
  let R : ℕ → Set (Y.model.carrier × Y₂.model.carrier) := fun n => rel (seq n)
  have hmono : ∀ n, R n ⊆ R (Nat.succ n) := by
    intro n p hp
    rcases hp with ⟨i, rfl⟩
    obtain ⟨θ, hθ, _, _, _⟩ := Classical.choose_spec (hstep n (seq n))
    have hsub :
        ((seqJoint b (fun j => Y.occ ((seq n).c j)) i).2,
          (seqJoint b₂ (fun j => Y₂.occ ((seq n).c₂ j)) i).2) ∈
          rel (Classical.choose (hstep n (seq n))) :=
      ⟨θ i, Prod.ext (hθ i).1 (hθ i).2⟩
    show
      ((seqJoint b (fun j => Y.occ ((seq n).c j)) i).2,
        (seqJoint b₂ (fun j => Y₂.occ ((seq n).c₂ j)) i).2) ∈ R (Nat.succ n)
    dsimp [R, rel, seq, next]
    exact hsub
  have hcd : ∀ n, CommonDomain K.τ (R n) := fun n => (seq n).cd
  have htot : ∀ y : Y.model.carrier, ∃ n z, (y, z) ∈ R n := by
    intro y
    obtain ⟨n, hn⟩ := hAYcov y
    obtain ⟨_, _, hY, _, _⟩ := Classical.choose_spec (hstep n (seq n))
    obtain ⟨i, hi⟩ := hY ⟨y, hn⟩
    refine ⟨Nat.succ n, (seqJoint b₂ (fun j => Y₂.occ ((seq (Nat.succ n)).c₂ j)) (Sum.inr i)).2, ?_⟩
    refine ⟨Sum.inr i, ?_⟩
    apply Prod.ext
    · have hocc : (seqJoint b (fun j => Y.occ ((seq (Nat.succ n)).c j)) (Sum.inr i)).2 =
          (seq (Nat.succ n)).c i := rfl
      exact hocc.trans hi
    · rfl
  have hsurj : ∀ y : Y₂.model.carrier, ∃ n x, (x, y) ∈ R n := by
    intro y
    obtain ⟨n, hn⟩ := hA2cov y
    obtain ⟨_, _, _, h2, _⟩ := Classical.choose_spec (hstep n (seq n))
    obtain ⟨i, hi⟩ := h2 ⟨y, hn⟩
    refine ⟨Nat.succ n, (seqJoint b (fun j => Y.occ ((seq (Nat.succ n)).c j)) (Sum.inr i)).2, ?_⟩
    refine ⟨Sum.inr i, ?_⟩
    apply Prod.ext
    · rfl
    · have hocc : (seqJoint b₂ (fun j => Y₂.occ ((seq (Nat.succ n)).c₂ j)) (Sum.inr i)).2 =
          (seq (Nat.succ n)).c₂ i := rfl
      exact hocc.trans hi
  obtain ⟨e, he⟩ := exists_equiv_of_commonDomain_chain R hmono hcd htot hsurj
  let φ := oneVertexArrow (hM := Y.mem) (hN := Y₂.mem) e.toEmbedding (strong_of_equiv K e Y.mem)
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro v
    have hv : v = PUnit.unit := Subsingleton.elim _ _
    rw [hv]
    exact e.bijective
  · apply SystemArrow.ext
    intro v
    ext a
    have hv : v = PUnit.unit := Subsingleton.elim _ _
    obtain ⟨n, hn⟩ := hAXcov a
    obtain ⟨_, _, _, _, hX⟩ := Classical.choose_spec (hstep n (seq n))
    obtain ⟨i, hi, hi₂⟩ := hX ⟨a, hn⟩
    have hmem : (incl.onVertex PUnit.unit a, incl₂.onVertex PUnit.unit a) ∈ R (Nat.succ n) := by
      refine ⟨Sum.inr i, ?_⟩
      apply Prod.ext
      · have hy : (seqJoint b (fun j => Y.occ ((seq (Nat.succ n)).c j)) (Sum.inr i)).2 =
            (seq (Nat.succ n)).c i := rfl
        exact hy.trans hi
      · have h2 : (seqJoint b₂ (fun j => Y₂.occ ((seq (Nat.succ n)).c₂ j)) (Sum.inr i)).2 =
            (seq (Nat.succ n)).c₂ i := rfl
        exact h2.trans hi₂
    have heq := he (Nat.succ n) _ hmem
    change e (incl.onVertex v a) = incl₂.onVertex v a
    rw [infra_75_onVertex_eq_unit incl hv a, infra_75_onVertex_eq_unit incl₂ hv a]
    exact heq
  · intro i
    have hmem : ((b i).2, (b₂ i).2) ∈ R 0 := ⟨Sum.inl i, rfl⟩
    have heq := he 0 _ hmem
    have hv : (b i).1 = PUnit.unit := Subsingleton.elim _ _
    have hφ := infra_75_onVertex_eq_unit φ hv (b i).2
    have hcoe : φ.onVertex PUnit.unit (b i).2 = e (b i).2 := rfl
    exact hφ.trans (hcoe.trans heq)

theorem infra_75_lemma (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (X Y : P.scheme.Object μ (Tail.mem hT hμ))
        (incl : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y))
        (hincl : P.scheme.permitted (X := X) (Y := Y) incl) {bIdx : Type u}
        (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y)),
        #bIdx ≤ σ → #bIdx < μ → AllDominated incl hincl bIdx b →
        (∀ (N : P.scheme.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ N))
          (hf : P.scheme.permitted (X := X) (Y := N) f)
          (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ N)),
          SameGaloisType (asTuple incl hincl b) (asTuple f hf b')
            (Equiv.refl bIdx) (Equiv.refl bIdx) →
          ∃ g : SystemArrow K oneVertexShape (P.scheme.asSystem _ Y) (P.scheme.asSystem _ N),
            P.scheme.permitted (X := Y) (Y := N) g ∧
            SystemArrow.comp incl g = f ∧
            ∀ i, g.onVertex (b i).1 (b i).2 = (b' i).2) ∧
        (∀ (Y₂ : P.scheme.Object μ (Tail.mem hT hμ))
          (incl₂ : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y₂))
          (hincl₂ : P.scheme.permitted (X := X) (Y := Y₂) incl₂)
          (b₂ : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y₂)),
          AllDominated incl₂ hincl₂ bIdx b₂ →
          SameGaloisType (asTuple incl hincl b) (asTuple incl₂ hincl₂ b₂)
            (Equiv.refl bIdx) (Equiv.refl bIdx) →
          ∃ φ : SystemArrow K oneVertexShape (P.scheme.asSystem _ Y) (P.scheme.asSystem _ Y₂),
            P.scheme.IsStructIso (X := Y) (Y := Y₂) φ ∧
            SystemArrow.comp incl φ = incl₂ ∧
            ∀ i, φ.onVertex (b i).1 (b i).2 = (b₂ i).2) := by
  refine ⟨infra_75_tailSet P σ, infra_75_tail P σ hσ, ?_⟩
  intro μ hμ X Y incl hincl bIdx b _hbσ hbμ hAll
  have hμel : μ ∈ P.eligible := hμ.1.1
  refine ⟨?_, ?_⟩
  · intro N f hf b' hGal
    exact infra_75_embed hμel X Y N incl hincl f hf b b' hbμ hGal hAll
  · intro Y₂ incl₂ hincl₂ b₂ hAll₂ hGal
    exact infra_75_iso hμel X Y Y₂ incl hincl incl₂ hincl₂ b b₂ hbμ hAll hAll₂ hGal
