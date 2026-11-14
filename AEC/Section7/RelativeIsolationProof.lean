module

public import AEC.Section7.RelativeIsolation
public import AEC.Section6.StationaryFreeExtension
public import AEC.Section6.AverageDescent
public import AEC.Section6.BoundedProducts
public import AEC.Section6.DescentRetraction
public import AEC.Section6.UniformApproximations
public import AEC.Section6.Results
public import AEC.Section5.SingleModelPackage

@[expose] public section

/-!
# Lemma 7.2 — relative isolation under projection and free lift
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-! ## Tail -/

def infra_72_tailSet (P : SingleModelData K) (σ : Cardinal.{u}) : Set Cardinal.{u} :=
  {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}

theorem infra_72_tail (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    Tail P.eligible (infra_72_tailSet P σ) := by
  refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
  obtain ⟨μ, hle, hμ, hrec⟩ :=
    (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
  exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩

/-! ## Helpers -/

theorem infra_72_same_galois_reindex
    {S : SystemShape.{u}} {W : WorkingScheme K S}
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    {t1 t2 : TupleOver K S W hμ base} {ι ι' : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι}
    (h : SameGaloisType t1 t2 e1 e2) (ρ : ι' → ι) :
    SameGaloisType (t1.reindex (fun j => e1.symm (ρ j)))
      (t2.reindex (fun j => e2.symm (ρ j)))
      (Equiv.refl ι') (Equiv.refl ι') := by
  rcases h with ⟨ρ0, hρ0, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ0, hρ0, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro j
  change
      (⟨(t1.val (e1.symm (ρ j))).1,
          f1.onVertex (t1.val (e1.symm (ρ j))).1 (t1.val (e1.symm (ρ j))).2⟩ :
        Occurrence K S (W.asSystem hρ0 top)) =
      ⟨(t2.val (e2.symm (ρ j))).1,
          f2.onVertex (t2.val (e2.symm (ρ j))).1 (t2.val (e2.symm (ρ j))).2⟩
  simpa [TupleOver.reindex] using hval (ρ j)

def pushParams {P : SingleModelData K} {μ ν : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {H : P.scheme.Object ν hν}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hν H))
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) :
    ι → Occurrence K oneVertexShape (P.scheme.asSystem hν H)
  | j => ⟨(Z j).1, incl.onVertex (Z j).1 (Z j).2⟩

theorem projectUC0_val
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {uIdx c0Idx c1Idx : Type u}
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (e : q.idx ≃ uIdx ⊕ (c0Idx ⊕ c1Idx)) (i : uIdx ⊕ c0Idx) :
    (q.projectUC0 e).val i = q.val (e.symm (Sum.map id Sum.inl i)) := by
  cases i <;> rfl

theorem mk_c1_le_three {uIdx c0Idx c1Idx : Type u} :
    #c1Idx ≤ #(uIdx ⊕ (c0Idx ⊕ c1Idx)) := by
  simp only [mk_sum, lift_id]
  exact le_trans le_add_self le_add_self

theorem mk_uc0_le_three {uIdx c0Idx c1Idx : Type u} :
    #(uIdx ⊕ c0Idx) ≤ #(uIdx ⊕ (c0Idx ⊕ c1Idx)) := by
  simp only [mk_sum, lift_id]
  exact add_le_add le_rfl le_self_add

/-! ## Clause 1 -/

noncomputable def infra_721_full_in_host
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {uIdx c0Idx c1Idx : Type u}
    (q0' : TupleOver K oneVertexShape P.scheme hμ A)
    (e0' : q0'.idx ≃ uIdx ⊕ c0Idx)
    (c1' : c1Idx → Occurrence K oneVertexShape (P.scheme.asSystem q0'.hν q0'.host)) :
    TupleOver K oneVertexShape P.scheme hμ A where
  ν := q0'.ν
  hν := q0'.hν
  host := q0'.host
  incl := q0'.incl
  incl_arrow := q0'.incl_arrow
  idx := uIdx ⊕ (c0Idx ⊕ c1Idx)
  val := fun t =>
    match t with
    | Sum.inl i => q0'.val (e0'.symm (Sum.inl i))
    | Sum.inr (Sum.inl j) => q0'.val (e0'.symm (Sum.inr j))
    | Sum.inr (Sum.inr k) => c1' k

/-- Reindex for saturation lists. -/
def infra_721_ρ {uIdx c0Idx c1Idx ι : Type u} :
    (uIdx ⊕ (c0Idx ⊕ c1Idx)) ⊕ ι → ((uIdx ⊕ c0Idx) ⊕ ι) ⊕ c1Idx
  | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl (Sum.inl a))
  | Sum.inl (Sum.inr (Sum.inl b)) => Sum.inl (Sum.inl (Sum.inr b))
  | Sum.inl (Sum.inr (Sum.inr c)) => Sum.inr c
  | Sum.inr j => Sum.inl (Sum.inr j)

theorem infra_721_ρ_injective {uIdx c0Idx c1Idx ι : Type u} :
    Injective (infra_721_ρ (uIdx := uIdx) (c0Idx := c0Idx) (c1Idx := c1Idx) (ι := ι)) := by
  intro x y hxy
  simp only [infra_721_ρ] at hxy
  match x, y with
  | Sum.inl (Sum.inl a), Sum.inl (Sum.inl a') =>
    obtain ⟨rfl⟩ := Sum.inl.inj (Sum.inl.inj (Sum.inl.inj hxy)); rfl
  | Sum.inl (Sum.inr (Sum.inl b)), Sum.inl (Sum.inr (Sum.inl b')) =>
    obtain ⟨rfl⟩ := Sum.inr.inj (Sum.inl.inj (Sum.inl.inj hxy)); rfl
  | Sum.inl (Sum.inr (Sum.inr c)), Sum.inl (Sum.inr (Sum.inr c')) =>
    obtain ⟨rfl⟩ := Sum.inr.inj hxy; rfl
  | Sum.inr j, Sum.inr j' =>
    obtain ⟨rfl⟩ := Sum.inr.inj (Sum.inl.inj hxy); rfl
  | Sum.inl (Sum.inl _), Sum.inl (Sum.inr (Sum.inl _)) => cases hxy
  | Sum.inl (Sum.inl _), Sum.inl (Sum.inr (Sum.inr _)) => cases hxy
  | Sum.inl (Sum.inl _), Sum.inr _ => cases hxy
  | Sum.inl (Sum.inr (Sum.inl _)), Sum.inl (Sum.inl _) => cases hxy
  | Sum.inl (Sum.inr (Sum.inl _)), Sum.inl (Sum.inr (Sum.inr _)) => cases hxy
  | Sum.inl (Sum.inr (Sum.inl _)), Sum.inr _ => cases hxy
  | Sum.inl (Sum.inr (Sum.inr _)), Sum.inl (Sum.inl _) => cases hxy
  | Sum.inl (Sum.inr (Sum.inr _)), Sum.inl (Sum.inr (Sum.inl _)) => cases hxy
  | Sum.inl (Sum.inr (Sum.inr _)), Sum.inr _ => cases hxy
  | Sum.inr _, Sum.inl (Sum.inl _) => cases hxy
  | Sum.inr _, Sum.inl (Sum.inr (Sum.inl _)) => cases hxy
  | Sum.inr _, Sum.inl (Sum.inr (Sum.inr _)) => cases hxy

theorem infra_721_projection
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {uIdx c0Idx c1Idx : Type u}
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (e : q.idx ≃ uIdx ⊕ (c0Idx ⊕ c1Idx))
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hIso : IsIsolatingFragment q e Z)
    (hqν : q.ν = μ)
    (huc0 : #(uIdx ⊕ c0Idx) < μ) (hc1 : #c1Idx < μ) (hιμ : #ι < μ) :
    IsIsolatingFragment (q.projectUC0 e)
      (projectDecomp (uIdx := uIdx) (c0Idx := c0Idx)) Z := by
  refine ⟨hIso.1, ?_⟩
  intro q0' e0' hq0ν hMarg hDE
  let α : Type u := (uIdx ⊕ c0Idx) ⊕ ι
  let β : Type u := c1Idx
  let xs : α → Occurrence K oneVertexShape (P.scheme.asSystem q0'.hν q0'.host) :=
    Sum.elim (fun i => q0'.val (e0'.symm i)) (pushParams q0'.incl Z)
  let base : α → Occurrence K oneVertexShape (P.scheme.asSystem q.hν q.host) :=
    Sum.elim (fun i => q.val (e.symm (Sum.map id Sum.inl i))) (pushParams q.incl Z)
  let ext : α ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem q.hν q.host) :=
    Sum.elim base (fun k => q.val (e.symm (Sum.inr (Sum.inr k))))
  have hαμ : #α < μ := by
    change #((uIdx ⊕ c0Idx) ⊕ ι) < μ
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) huc0 hιμ
  have hα : #α < q0'.ν := by simpa [← hq0ν] using hαμ
  have hc1ν : #β < q0'.ν := by simpa [← hq0ν] using hc1
  have hEqα : P.scheme.DiagramEq (X := q0'.host) (Y := q.host) xs base := by
    have hx : xs = alignJoint e0' (typeJoint (p := q0') Z) := by
      funext t; cases t <;> rfl
    have hy : base =
        alignJoint (projectDecomp (uIdx := uIdx) (c0Idx := c0Idx))
          (typeJoint (p := q.projectUC0 e) Z) := by
      funext t; cases t with
      | inl i =>
        simp only [alignJoint, projectDecomp, Equiv.refl_symm, Equiv.refl_apply, typeJoint,
          projectUC0_val, Sum.map, pushParams]; rfl
      | inr j => rfl
    rw [hx, hy]
    exact P.scheme.diagram_symm _ _ _ _ hDE
  obtain ⟨H, g, zs, hg, hzs, hzsEq⟩ :=
    (SingleModelData.isSaturated (P := P)).saturated
      q0'.host q.host xs base ext hα hc1ν (fun _ => rfl) hEqα
  have hPushG : P.scheme.DiagramEq (X := q0'.host) (Y := H) xs
      (fun ij => ⟨(xs ij).1, g.onVertex (xs ij).1 (xs ij).2⟩) :=
    P.scheme.diagram_preserved q0'.host H g trivial xs hα hα
  have hxsZs : (fun ij => ⟨(xs ij).1, g.onVertex (xs ij).1 (xs ij).2⟩) =
      fun ij => zs (Sum.inl ij) := funext fun ij => (hzs ij).symm
  have hEqZsInl : P.scheme.DiagramEq (X := q0'.host) (Y := H) xs
      (fun ij => zs (Sum.inl ij)) := by rw [← hxsZs]; exact hPushG
  obtain ⟨φ, hφiso, hφ⟩ :=
    (P.scheme.diagram_iso q0'.host H xs (fun ij => zs (Sum.inl ij)) hα).mp hEqZsInl
  have hφbij : Bijective (φ.onVertex PUnit.unit) := hφiso PUnit.unit
  let eφ : q0'.host.model.carrier ≃ H.model.carrier := Equiv.ofBijective _ hφbij
  let c1pull : c1Idx → Occurrence K oneVertexShape (P.scheme.asSystem q0'.hν q0'.host) :=
    fun k => q0'.host.occ (eφ.symm (H.val (zs (Sum.inr k))))
  let qFull := infra_721_full_in_host q0' e0' c1pull
  let eFull : qFull.idx ≃ uIdx ⊕ (c0Idx ⊕ c1Idx) := Equiv.refl _
  let joint0 : α ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem q0'.hν q0'.host) :=
    Sum.elim xs c1pull
  have hφjoint : ∀ t, zs t =
      ⟨(joint0 t).1, φ.onVertex (joint0 t).1 (joint0 t).2⟩ := by
    intro t; cases t with
    | inl ij => exact hφ ij
    | inr k =>
      have happly : φ.onVertex PUnit.unit (eφ.symm (H.val (zs (Sum.inr k)))) =
          H.val (zs (Sum.inr k)) := eφ.apply_symm_apply _
      refine Eq.trans (SMObject.occ_val H (zs (Sum.inr k))).symm ?_
      refine Eq.trans (congrArg H.occ happly.symm) ?_
      simp only [joint0, c1pull, SMObject.occ, oneVertexOcc, SMObject.val, oneVertexVal]; rfl
  have hcardαβ : #(α ⊕ β) < q0'.ν := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (by simpa [← hq0ν] using P.aleph0_le hμ) hα hc1ν
  have hPushφ : P.scheme.DiagramEq (X := q0'.host) (Y := H) joint0 zs := by
    have h := P.scheme.diagram_preserved q0'.host H φ trivial joint0 hcardαβ hcardαβ
    have heq : (fun t => ⟨(joint0 t).1, φ.onVertex (joint0 t).1 (joint0 t).2⟩) = zs :=
      funext fun t => (hφjoint t).symm
    rwa [heq] at h
  have hJointExt : P.scheme.DiagramEq (X := q0'.host) (Y := q.host) joint0 ext :=
    P.scheme.diagram_trans q0'.host H q.host joint0 zs ext hPushφ hzsEq
  have hFullDE : P.scheme.DiagramEq (X := q.host) (Y := qFull.host)
      (alignJoint e (typeJoint (p := q) Z))
      (alignJoint eFull (typeJoint (p := qFull) Z)) := by
    have hpre :=
      WorkingScheme.diagramEq_precomp (W := P.scheme) q0'.host q.host joint0 ext
        (infra_721_ρ (uIdx := uIdx) (c0Idx := c0Idx) (c1Idx := c1Idx) (ι := ι))
        infra_721_ρ_injective hJointExt
    have hx : (fun j => joint0 (infra_721_ρ j)) =
        alignJoint eFull (typeJoint (p := qFull) Z) := by
      funext t
      match t with
      | Sum.inl (Sum.inl a) => rfl
      | Sum.inl (Sum.inr (Sum.inl b)) => rfl
      | Sum.inl (Sum.inr (Sum.inr c)) => rfl
      | Sum.inr j => rfl
    have hy : (fun j => ext (infra_721_ρ j)) = alignJoint e (typeJoint (p := q) Z) := by
      funext t
      match t with
      | Sum.inl (Sum.inl a) => rfl
      | Sum.inl (Sum.inr (Sum.inl b)) => rfl
      | Sum.inl (Sum.inr (Sum.inr c)) => rfl
      | Sum.inr j => rfl
    rw [← hx, ← hy]
    exact P.scheme.diagram_symm _ _ _ _ hpre
  have hMargFull : SameGaloisType (q.marginal e) (qFull.marginal eFull)
      (Equiv.refl uIdx) (Equiv.refl uIdx) := hMarg
  have hFull : SameGaloisType q qFull e eFull :=
    hIso.2 qFull eFull hq0ν hMargFull hFullDE
  -- Restrict the full Galois identification to the `(u, c₀)` coordinates, then rewrite
  -- `qFull`'s projection to `q0'` (identical host / values).
  rcases hFull with ⟨ρg, hρg, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρg, hρg, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro i
  cases i with
  | inl a =>
    have hv := hval (Sum.inl a)
    -- LHS: projectUC0 at `inl a` is `q.val (e.symm (inl a))`
    -- RHS: `q0'.val` equals `qFull.val` at that coordinate
    simp only [TupleOver.projectUC0, TupleOver.reindex, projectUC0ρ, projectDecomp,
      Equiv.refl_symm, Equiv.refl_apply, infra_721_full_in_host, eFull,
      Equiv.refl] at hv ⊢
    exact hv
  | inr b =>
    have hv := hval (Sum.inr (Sum.inl b))
    simp only [TupleOver.projectUC0, TupleOver.reindex, projectUC0ρ, projectDecomp,
      Equiv.refl_symm, Equiv.refl_apply, infra_721_full_in_host, eFull,
      Equiv.refl] at hv ⊢
    exact hv

end
end
end AEC
