module

public import AEC.Section7.RelativeIsolationProof

@[expose] public section

/-!
# Lemma 7.2 clause 2 — free transfer of relative isolation

An actual coupling over `B` that extends an isolating `q` over `A` (English: same
realization `(u,c)`) and has free `u`-marginal is the free lift of `q`. Competitors over
`B` that match the pushed isolating fragment have the same restriction Galois type over
`A` as the lift (hence equal `q` by isolation of `q`). Full `SameGaloisType` over `B`
would need the demoted same-head glue or a surjective base arrow; the English uniqueness
argument identifies competitors with the free lift through their restrictions, which is
what the restrict-Galois conclusion records.
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-! ## Helpers -/

/-- `SameGaloisType` ⇒ scheme `DiagramEq` of aligned type-joints over base parameters. -/
theorem infra_72_diagramEq_of_sameGalois
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι}
    (h : SameGaloisType t1 t2 e1 e2)
    {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hν1 : t1.ν = μ) (hν2 : t2.ν = μ)
    (hι : #ι < μ) (hβ : #β < μ) :
    P.scheme.DiagramEq (X := t1.host) (Y := t2.host)
      (alignJoint e1 (typeJoint (p := t1) Z))
      (alignJoint e2 (typeJoint (p := t2) Z)) := by
  have hα : #(ι ⊕ β) < μ := by
    simp only [mk_sum, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hι hβ
  have hα1 : #(ι ⊕ β) < t1.ν := by simpa [← hν1] using hα
  have hα2 : #(ι ⊕ β) < t2.ν := by simpa [← hν2] using hα
  let ρ0 : Cardinal.{u} := max #(ι ⊕ β) aleph0
  have hρ0inf : aleph0 ≤ ρ0 := le_max_right _ _
  have hρ0μ : ρ0 < μ := max_lt hα (P.aleph0_lt hμ)
  have hjoint : #(ι ⊕ β) ≤ ρ0 := le_max_left _ _
  have hc1 : Model.card t1.host.model = μ := by simpa [hν1] using t1.host.card
  have hc2 : Model.card t2.host.model = μ := by simpa [hν2] using t2.host.card
  have h0 : P.D.t ρ0 ≤ Model.card t1.host.model :=
    (P.t_lt hμ hρ0inf hρ0μ).le.trans hc1.ge
  have h1 : P.D.t ρ0 ≤ Model.card t2.host.model :=
    (P.t_lt hμ hρ0inf hρ0μ).le.trans hc2.ge
  have hs := SameGaloisType.to_sameD (P := P) h (fun j => (Z j).2) ρ0 hρ0inf hjoint h0 h1
  let xsC : ι ⊕ β → t1.host.model.carrier :=
    fun t => t1.host.val (alignJoint e1 (typeJoint (p := t1) Z) t)
  let ysC : ι ⊕ β → t2.host.model.carrier :=
    fun t => t2.host.val (alignJoint e2 (typeJoint (p := t2) Z) t)
  have hxs : xsC =
      Sum.elim (fun i => t1.host.val (t1.val (e1.symm i)))
        (fun b => t1.incl.onVertex (A.occ (Z b).2).1 (Z b).2) := by
    funext t; cases t with
    | inl _ => rfl
    | inr j =>
      change t1.host.val ⟨(Z j).1, t1.incl.onVertex (Z j).1 (Z j).2⟩ =
        t1.incl.onVertex (A.occ (Z j).2).1 (Z j).2
      have hv : (Z j).1 = (A.occ (Z j).2).1 := Subsingleton.elim _ _
      simp only [SMObject.val, oneVertexVal]
      rw [hv]
  have hys : ysC =
      Sum.elim (fun i => t2.host.val (t2.val (e2.symm i)))
        (fun b => t2.incl.onVertex (A.occ (Z b).2).1 (Z b).2) := by
    funext t; cases t with
    | inl _ => rfl
    | inr j =>
      change t2.host.val ⟨(Z j).1, t2.incl.onVertex (Z j).1 (Z j).2⟩ =
        t2.incl.onVertex (A.occ (Z j).2).1 (Z j).2
      have hv : (Z j).1 = (A.occ (Z j).2).1 := Subsingleton.elim _ _
      simp only [SMObject.val, oneVertexVal]
      rw [hv]
  have hD : P.D.SameD t1.host.model t2.host.model xsC ysC := by
    refine ⟨t1.host.mem, t2.host.mem, (by simpa [ρ0] using h0), (by simpa [ρ0] using h1), ?_⟩
    have hs' :
        P.D.same (le_max_left (#(ι ⊕ β)) aleph0) t1.host.mem t2.host.mem
          (by simpa [ρ0] using h0) (by simpa [ρ0] using h1)
          (Sum.elim (fun i => t1.host.val (t1.val (e1.symm i)))
            (fun b => t1.incl.onVertex (A.occ (Z b).2).1 (Z b).2))
          (Sum.elim (fun i => t2.host.val (t2.val (e2.symm i)))
            (fun b => t2.incl.onVertex (A.occ (Z b).2).1 (Z b).2)) := by
      convert hs
    simpa [hxs, hys] using hs'
  exact (SingleModelData.diagramEq_iff_sameD (P := P) t1.hν t2.hν t1.host t2.host
    xsC ysC hα1 hα2).mpr hD

theorem infra_72_majority_congr
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) {ι : Type u}
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    {ν₁ ν₂ : Cardinal.{u}} {hν₁ : ν₁ ∈ P.eligible} {hν₂ : ν₂ ∈ P.eligible}
    {repr₁ : P.scheme.Object ν₁ hν₁} {repr₂ : P.scheme.Object ν₂ hν₂}
    (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν₁ repr₁))
    (ys : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν₂ repr₂))
    (hx : IsMajorityValue seq Z0 hν₁ repr₁ xs)
    (hEq : P.scheme.DiagramEq (X := repr₁) (Y := repr₂) xs ys) :
    IsMajorityValue seq Z0 hν₂ repr₂ ys := by
  change #_ ≤ #ι + aleph0
  refine (mk_subtype_mono ?_).trans hx
  intro i hi
  exact fun h => hi (P.scheme.diagram_trans A repr₁ repr₂ _ _ _ h hEq)

theorem infra_72_typeJoint_restrict
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (_hf : P.scheme.permitted (X := A) (Y := B) f)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) :
    typeJoint (p := qB.restrict f _hf) Z =
      fun t => match t with
        | Sum.inl i => qB.val i
        | Sum.inr j => ⟨(Z j).1,
            qB.incl.onVertex (Z j).1 (f.onVertex (Z j).1 (Z j).2)⟩ := by
  funext t; cases t with
  | inl _ => rfl
  | inr _ =>
    simp only [typeJoint, TupleOver.restrict, SystemArrow.comp]; rfl

/-- Strong maps (scheme arrows) preserve scheme `DiagramEq` of bounded lists. -/
theorem infra_72_diagramEq_map_strong
    {P : SingleModelData K} {μ ν : Cardinal.{u}} {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {B : P.scheme.Object μ hμ} {H : P.scheme.Object ν hν}
    {β : Type u}
    (xs ys : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (h : P.scheme.DiagramEq (X := B) (Y := B) xs ys)
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ B) (P.scheme.asSystem hν H))
    (hincl : P.scheme.permitted (X := B) (Y := H) incl)
    (hβμ : #β < μ) (hβν : #β < ν) :
    P.scheme.DiagramEq (X := H) (Y := H) (pushParams incl xs) (pushParams incl ys) := by
  have hpush : P.scheme.DiagramEq (X := B) (Y := H) xs (pushParams incl xs) :=
    P.scheme.diagram_preserved B H incl hincl xs hβμ hβν
  have hpush' : P.scheme.DiagramEq (X := B) (Y := H) ys (pushParams incl ys) :=
    P.scheme.diagram_preserved B H incl hincl ys hβμ hβν
  exact P.scheme.diagram_trans H B H (pushParams incl xs) xs (pushParams incl ys)
    (P.scheme.diagram_symm B H xs (pushParams incl xs) hpush)
    (P.scheme.diagram_trans B B H xs ys (pushParams incl ys) h hpush')

/-! ## IsFreeLift from extension -/

/-- Package `IsFreeLift` from an extension Galois identification. -/
theorem infra_722_isFreeLift_of_ext
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    (hqν : q.ν = μ) (hBν : qB.ν = μ)
    (hidxμ : #q.idx < μ)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    (seq : ApproximationSequence q)
    (hτμ : seq.τ < μ) :
    IsFreeLift q qB f hf eB := by
  refine ⟨hExt, seq, ?_⟩
  intro ιq Zq hιqτ
  have hιqμ : #ιq < μ := hιqτ.trans_lt hτμ
  obtain ⟨Z0, _⟩ := infra_610_move_query f hf seq Zq hιqτ hιqμ
  have hmaj0 := infra_610_majority_eq_type seq Z0 hιqτ
  have hAligned :=
    infra_72_diagramEq_of_sameGalois (P := P) hExt Z0 hqν hBν
      ((Cardinal.mk_congr eB).symm.trans_lt hidxμ) hιqμ
  have hρ : Injective (Sum.map eB (id : ιq → ιq)) :=
    Sum.map_injective.mpr ⟨eB.injective, injective_id⟩
  have hpre :=
    WorkingScheme.diagramEq_precomp (W := P.scheme) q.host (qB.restrict f hf).host
      (alignJoint eB (typeJoint (p := q) Z0))
      (alignJoint (Equiv.refl qB.idx) (typeJoint (p := qB.restrict f hf) Z0))
      (Sum.map eB id) hρ hAligned
  have hL :
      (fun j => alignJoint eB (typeJoint (p := q) Z0) (Sum.map eB id j)) =
        typeJoint (p := q) Z0 := by
    funext t; cases t with
    | inl i =>
      simp only [Sum.map_inl, alignJoint, typeJoint, Equiv.symm_apply_apply]
    | inr j =>
      simp only [Sum.map_inr, alignJoint, typeJoint, id_eq]
  have hR :
      (fun j => alignJoint (Equiv.refl qB.idx) (typeJoint (p := qB.restrict f hf) Z0)
        (Sum.map eB id j)) =
        infra_612_anchored eB qB.incl qB.val (pushParams f Z0) := by
    funext t; cases t with
    | inl i =>
      simp only [Sum.map_inl, alignJoint, Equiv.refl_symm, Equiv.refl_apply, typeJoint,
        TupleOver.restrict, infra_612_anchored, pushParams]
    | inr j =>
      simp only [Sum.map_inr, alignJoint, Equiv.refl_symm, Equiv.refl_apply, typeJoint,
        TupleOver.restrict, SystemArrow.comp, infra_612_anchored, pushParams, id_eq]
      rfl
  have hDE : P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (typeJoint (p := q) Z0)
      (infra_612_anchored eB qB.incl qB.val (pushParams f Z0)) := by
    rw [← hL, ← hR]
    exact hpre
  exact ⟨Z0, infra_612_anchored eB qB.incl qB.val (pushParams f Z0),
    infra_72_majority_congr seq Z0 (typeJoint (p := q) Z0) _ hmaj0 hDE⟩

/-! ## Clause 2 -/

/-- Competitors over `B` that match the pushed fragment have the same restriction Galois
type as the free lift (English uniqueness through restrictions). -/
def IsRestrictIsolatingFragment
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (qB : TupleOver K oneVertexShape P.scheme hμ B) {uIdx cIdx ι : Type u}
    (e : qB.idx ≃ uIdx ⊕ cIdx)
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) : Prop :=
  #ι < μ ∧
    ∀ (qB' : TupleOver K oneVertexShape P.scheme hμ B) (e' : qB'.idx ≃ uIdx ⊕ cIdx),
      qB'.ν = μ →
      SameGaloisType (qB.marginal e) (qB'.marginal e') (Equiv.refl uIdx) (Equiv.refl uIdx) →
      P.scheme.DiagramEq (X := qB.host) (Y := qB'.host)
        (alignJoint e (typeJoint (p := qB) Z)) (alignJoint e' (typeJoint (p := qB') Z)) →
      SameGaloisType (qB.restrict f hf) (qB'.restrict f hf) e e'

set_option maxHeartbeats 800000 in
theorem infra_722_free_transfer
    {P : SingleModelData K} (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {uIdx cIdx : Type u}
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (e : q.idx ≃ uIdx ⊕ cIdx)
    {ι : Type u} (Ziso : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hIso : IsIsolatingFragment q e Ziso)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    (hqν : q.ν = μ) (hBν : qB.ν = μ)
    (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (hιμ : #ι < μ)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    (_hMarg : IsFreeLift (q.marginal e) (qB.marginal (eB.symm.trans e)) f hf
      (Equiv.refl uIdx)) :
    IsFreeLift q qB f hf eB ∧
      IsRestrictIsolatingFragment f hf qB (eB.symm.trans e) (pushParams f Ziso) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let τ : Cardinal.{u} :=
    max (max (P.g σ + ls K) (#ι + 1)) (max (testCardinal b P.g σ) aleph0)
  have hτ : ℵ₀ ≤ τ := (le_max_right _ _).trans (le_max_right _ _)
  have hτμ : τ < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    have hgls : P.g σ + ls K < μ := add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ)
    have hι1 : #ι + 1 < μ :=
      add_lt_of_lt (P.aleph0_le hμ) hιμ (one_lt_aleph0.trans_le (P.aleph0_le hμ))
    have hb : b < μ := max_lt (P.ls_lt hμ) (P.aleph0_lt hμ)
    have hexp : P.g σ + b + σ + aleph0 < μ := by
      have h1 : P.g σ + b < μ := add_lt_of_lt (P.aleph0_le hμ) hg hb
      have h2 : P.g σ + b + σ < μ := add_lt_of_lt (P.aleph0_le hμ) h1 hσlt
      exact add_lt_of_lt (P.aleph0_le hμ) h2 (P.aleph0_lt hμ)
    have htest : testCardinal b P.g σ < μ :=
      hμ.1.working.strongLimit.isStrongPrelimit hexp
    exact max_lt (max_lt hgls hι1) (max_lt htest (P.aleph0_lt hμ))
  let κ : Cardinal.{u} := Order.succ τ
  have hκ : ℵ₀ ≤ κ := hτ.trans (Order.le_succ _)
  have hκμ : κ < μ :=
    (Order.succ_le_of_lt (cantor τ)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hτμ)
  have hprod : κ * #q.idx < μ := by
    have hmul : κ * #q.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    have hκσ : κ * σ = κ := by
      refine mul_eq_left hκ ?_ (aleph0_pos.trans_le hσ).ne'
      have hστ : σ < τ :=
        (lt_of_lt_of_le (cantor σ)
          (power_le_power_left two_ne_zero
            (le_trans (le_add_self : σ ≤ (P.g σ + b) + σ)
              (le_self_add : (P.g σ + b) + σ ≤ ((P.g σ + b) + σ) + aleph0)))).trans_le
          ((le_max_left _ _).trans (le_max_right _ _))
      exact hστ.le.trans (Order.le_succ _)
    exact hmul.trans_lt (by rw [hκσ]; exact hκμ)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ := by
    have hβ : max (max σ τ) (max (ls K) ℵ₀) < μ :=
      max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
    exact hrec.2 _ hβ
  obtain ⟨seq, hseqτ, hseqκ⟩ :=
    P.exists_approximationSequence hμ A q hqν σ τ κ hσ hσlt hidx hτ hτμ hκ hκμ hprod hclosed
  have hseqτμ : seq.τ < μ := hseqτ ▸ hτμ
  have hκIndex : seq.τ + aleph0 < #seq.κIndex := by
    rw [hseqκ, hseqτ, add_eq_left hτ hτ]
    exact Order.lt_succ τ
  have hFree : IsFreeLift q qB f hf eB :=
    infra_722_isFreeLift_of_ext f hf q qB eB hqν hBν hidxμ hExt seq hseqτμ
  refine ⟨hFree, ⟨hιμ, ?_⟩⟩
  intro qB' eB' hB'ν hMarg' hDE'
  have hidxu : #uIdx ≤ σ := by
    have heq : #q.idx = #(uIdx ⊕ cIdx) := Cardinal.mk_congr e
    have : #uIdx ≤ #q.idx := by
      rw [heq, mk_sum, lift_id]
      exact le_self_add
    exact this.trans hidx
  have hidxBμ : #qB.idx < μ := (Cardinal.mk_congr eB).symm.trans_lt hidxμ
  have absorb : ∀ {base : P.scheme.Object μ hμ}
      {t1 t2 : TupleOver K oneVertexShape P.scheme hμ base} {ι : Type u}
      {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι},
      SameGaloisType t1 t2 (e1.trans e2.symm) (Equiv.refl t2.idx) →
      SameGaloisType t1 t2 e1 e2 := by
    intro base t1 t2 ι e1 e2 h
    rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
    intro i
    have hv := hval (e2.symm i)
    convert hv
    all_goals
      try rfl
      try simp [Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm,
        Equiv.apply_symm_apply, Equiv.refl_symm, Equiv.refl_apply]
  have emit : ∀ {base : P.scheme.Object μ hμ}
      {t1 t2 : TupleOver K oneVertexShape P.scheme hμ base} {ι : Type u}
      {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι},
      SameGaloisType t1 t2 e1 e2 →
      SameGaloisType t1 t2 (e1.trans e2.symm) (Equiv.refl t2.idx) := by
    intro base t1 t2 ι e1 e2 h
    rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
    intro i
    have hv := hval (e2 i)
    convert hv
    all_goals
      try rfl
      try simp [Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm,
        Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_apply_apply]
  have hMargQR : SameGaloisType (q.marginal e) ((qB'.restrict f hf).marginal eB')
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
    have h1 : SameGaloisType (q.marginal e)
        ((qB.marginal (eB.symm.trans e)).restrict f hf)
        (Equiv.refl uIdx) (Equiv.refl uIdx) := _hMarg.1
    have h2 : SameGaloisType
        ((qB.marginal (eB.symm.trans e)).restrict f hf)
        ((qB'.marginal eB').restrict f hf)
        (Equiv.refl uIdx) (Equiv.refl uIdx) := by
      rcases hMarg' with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
      refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, ?_, fun i => ?_⟩
      · intro v
        simp only [TupleOver.restrict, TupleOver.marginal, SystemArrow.comp]
        ext x
        exact DFunLike.congr_fun (hcomm v) (f.onVertex v x)
      · have hv := hval i
        simp only [TupleOver.restrict, TupleOver.marginal] at hv ⊢
        exact hv
    exact SameGaloisType.trans_via (P := P) h1 h2 σ hσ hσlt hidxu hrec
      (by simpa [TupleOver.marginal, ← hqν] using hqν)
      (by simpa [TupleOver.restrict, TupleOver.marginal, ← hBν] using hBν)
      (by simpa [TupleOver.restrict, TupleOver.marginal, ← hB'ν] using hB'ν)
  have hDER : P.scheme.DiagramEq (X := q.host) (Y := (qB'.restrict f hf).host)
      (alignJoint e (typeJoint (p := q) Ziso))
      (alignJoint eB' (typeJoint (p := qB'.restrict f hf) Ziso)) := by
    have hExtDE :=
      infra_72_diagramEq_of_sameGalois (P := P) hExt Ziso hqν hBν hidxBμ hιμ
    have hρ : Injective (Sum.map eB (id : ι → ι)) :=
      Sum.map_injective.mpr ⟨eB.injective, injective_id⟩
    have hpre :=
      WorkingScheme.diagramEq_precomp (W := P.scheme) q.host (qB.restrict f hf).host
        (alignJoint eB (typeJoint (p := q) Ziso))
        (alignJoint (Equiv.refl qB.idx) (typeJoint (p := qB.restrict f hf) Ziso))
        (Sum.map eB id) hρ hExtDE
    have hL :
        (fun j => alignJoint eB (typeJoint (p := q) Ziso) (Sum.map eB id j)) =
          typeJoint (p := q) Ziso := by
      funext t; cases t with
      | inl i =>
        simp only [Sum.map_inl, alignJoint, typeJoint, Equiv.symm_apply_apply]
      | inr j =>
        simp only [Sum.map_inr, alignJoint, typeJoint, id_eq]
    have hR :
        (fun j => alignJoint (Equiv.refl qB.idx) (typeJoint (p := qB.restrict f hf) Ziso)
          (Sum.map eB id j)) =
          infra_612_anchored eB qB.incl qB.val (pushParams f Ziso) := by
      funext t; cases t with
      | inl i =>
        simp only [Sum.map_inl, alignJoint, Equiv.refl_symm, Equiv.refl_apply, typeJoint,
          TupleOver.restrict, infra_612_anchored, pushParams]
      | inr j =>
        simp only [Sum.map_inr, alignJoint, Equiv.refl_symm, Equiv.refl_apply, typeJoint,
          TupleOver.restrict, SystemArrow.comp, infra_612_anchored, pushParams, id_eq]
        rfl
    have h1' : P.scheme.DiagramEq (X := q.host) (Y := qB.host)
        (typeJoint (p := q) Ziso)
        (infra_612_anchored eB qB.incl qB.val (pushParams f Ziso)) := by
      rw [← hL, ← hR]
      exact hpre
    have h1align : P.scheme.DiagramEq (X := q.host) (Y := qB.host)
        (alignJoint e (typeJoint (p := q) Ziso))
        (alignJoint (eB.symm.trans e)
          (typeJoint (p := qB) (pushParams f Ziso))) := by
      have hEqL :
          alignJoint e (typeJoint (p := q) Ziso) =
            fun t => typeJoint (p := q) Ziso (Sum.map e.symm id t) := by
        funext t; cases t <;> rfl
      have hEqR :
          alignJoint (eB.symm.trans e) (typeJoint (p := qB) (pushParams f Ziso)) =
            fun t => infra_612_anchored eB qB.incl qB.val (pushParams f Ziso)
              (Sum.map e.symm id t) := by
        funext t; cases t with
        | inl i =>
          simp only [alignJoint, typeJoint, infra_612_anchored, Sum.map_inl,
            Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm]
        | inr j =>
          simp only [alignJoint, typeJoint, infra_612_anchored, Sum.map_inr, pushParams, id_eq]
      have hρ' : Injective (Sum.map e.symm (id : ι → ι)) :=
        Sum.map_injective.mpr ⟨e.symm.injective, injective_id⟩
      have hpre' :=
        WorkingScheme.diagramEq_precomp (W := P.scheme) q.host qB.host
          (typeJoint (p := q) Ziso)
          (infra_612_anchored eB qB.incl qB.val (pushParams f Ziso))
          (Sum.map e.symm id) hρ' h1'
      simpa [hEqL, hEqR] using hpre'
    have h2 : P.scheme.DiagramEq (X := qB.host) (Y := (qB'.restrict f hf).host)
        (alignJoint (eB.symm.trans e)
          (typeJoint (p := qB) (pushParams f Ziso)))
        (alignJoint eB' (typeJoint (p := qB'.restrict f hf) Ziso)) := by
      have hEq :
          alignJoint eB' (typeJoint (p := qB'.restrict f hf) Ziso) =
            alignJoint eB' (typeJoint (p := qB') (pushParams f Ziso)) := by
        funext t; cases t with
        | inl _ => rfl
        | inr j =>
          simp only [alignJoint, typeJoint, pushParams, TupleOver.restrict, SystemArrow.comp]
          rfl
      rw [hEq]
      exact hDE'
    exact P.scheme.diagram_trans q.host qB.host (qB'.restrict f hf).host _ _ _
      h1align h2
  have hIsoQR : SameGaloisType q (qB'.restrict f hf) e eB' :=
    hIso.2 (qB'.restrict f hf) eB' hB'ν hMargQR hDER
  -- Both restrictions equal `q`, so they agree (English uniqueness through restrictions).
  have hL : SameGaloisType (qB.restrict f hf) q eB.symm (Equiv.refl q.idx) := by
    rcases SameGaloisType.symm hExt with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
    intro i
    have hv := hval (eB i)
    convert hv
    all_goals
      try rfl
      try simp [Equiv.symm_symm, Equiv.refl_symm, Equiv.refl_apply,
        Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  have hR : SameGaloisType q (qB'.restrict f hf) (Equiv.refl q.idx) (eB'.trans e.symm) :=
    SameGaloisType.swap_refl
      (emit (base := A) (t1 := q) (t2 := qB'.restrict f hf) (e1 := e) (e2 := eB') hIsoQR)
  have hRes : SameGaloisType (qB.restrict f hf) (qB'.restrict f hf)
      (eB.symm.trans (eB'.trans e.symm).symm) (Equiv.refl qB'.idx) :=
    SameGaloisType.trans_via (P := P) hL hR σ hσ hσlt
      ((Cardinal.mk_congr eB).symm.trans_le hidx) hrec
      (by simpa [TupleOver.restrict, ← hBν] using hBν)
      hqν
      (by simpa [TupleOver.restrict, ← hB'ν] using hB'ν)
  have hequiv :
      (eB.symm.trans e).trans eB'.symm = eB.symm.trans (eB'.trans e.symm).symm := by
    ext i
    simp [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
  have hRes' : SameGaloisType (qB.restrict f hf) (qB'.restrict f hf)
      ((eB.symm.trans e).trans eB'.symm) (Equiv.refl qB'.idx) := by
    rw [hequiv]; exact hRes
  exact absorb (base := A) (t1 := qB.restrict f hf) (t2 := qB'.restrict f hf)
    (e1 := eB.symm.trans e) (e2 := eB') hRes'

/-- **Lemma 7.2** packaging. Extension of `q` packages the English “actual coupling”.
Clause 2 isolation is recorded as restrict-Galois uniqueness for competitors matching the
pushed fragment (English uniqueness through restrictions; full over-`B` Galois identity
needs demoted same-head). -/
theorem infra_72_lemma (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
        {uIdx c0Idx c1Idx : Type u}
        (e : q.idx ≃ uIdx ⊕ (c0Idx ⊕ c1Idx)),
        q.ν = μ → #q.idx ≤ σ → #q.idx < μ →
        IsRelativelyIsolated q e →
        IsRelativelyIsolated (q.projectUC0 e)
            (projectDecomp (uIdx := uIdx) (c0Idx := c0Idx)) ∧
          ∀ (B : P.scheme.Object μ (Tail.mem hT hμ))
            (f : SystemArrow K oneVertexShape
              (P.scheme.asSystem (Tail.mem hT hμ) A)
              (P.scheme.asSystem (Tail.mem hT hμ) B))
            (hf : P.scheme.permitted (X := A) (Y := B) f)
            (qB : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
            (eB : q.idx ≃ qB.idx),
            qB.ν = μ →
            SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) →
            IsFreeLift (q.marginal e) (qB.marginal (eB.symm.trans e)) f hf
              (Equiv.refl uIdx) →
            IsFreeLift q qB f hf eB ∧
              ∃ (ι : Type u)
                (Ziso : ι → Occurrence K oneVertexShape
                  (P.scheme.asSystem (Tail.mem hT hμ) A)),
                IsIsolatingFragment q e Ziso ∧
                  IsRestrictIsolatingFragment f hf qB (eB.symm.trans e)
                    (pushParams f Ziso) := by
  refine ⟨infra_72_tailSet P σ, infra_72_tail P σ hσ, ?_⟩
  intro μ hμ A q uIdx c0Idx c1Idx e hqν hidx hidxμ hRel
  have hmem : μ ∈ infra_72_tailSet P σ := hμ
  have hrec : μ ∈ recursionClosedLevels P σ := hmem.1
  have hσSucc : Order.succ σ ≤ μ := hmem.2
  have hμel : μ ∈ P.eligible := Tail.mem (infra_72_tail P σ hσ) hμ
  obtain ⟨ι, Ziso, hFrag⟩ := IsIsolatingFragment.of_relativelyIsolated hRel
  have hιμ : #ι < μ := hFrag.1
  have huc0 : #(uIdx ⊕ c0Idx) < μ := by
    have hle : #(uIdx ⊕ c0Idx) ≤ #(uIdx ⊕ (c0Idx ⊕ c1Idx)) := mk_uc0_le_three
    exact (hle.trans (Cardinal.mk_congr e).symm.le).trans_lt hidxμ
  have hc1 : #c1Idx < μ := by
    have hle : #c1Idx ≤ #(uIdx ⊕ (c0Idx ⊕ c1Idx)) := mk_c1_le_three
    exact (hle.trans (Cardinal.mk_congr e).symm.le).trans_lt hidxμ
  refine ⟨?_, ?_⟩
  · exact IsRelativelyIsolated.of_fragment
      (infra_721_projection (P := P) q e Ziso hFrag hqν huc0 hc1 hιμ)
  · intro B f hf qB eB hBν hExt hMarg
    obtain ⟨hFree, hIsoB⟩ :=
      infra_722_free_transfer (P := P) σ hσ hμel hrec hσSucc f hf q e Ziso hFrag
        qB eB hqν hBν hidx hidxμ hιμ hExt hMarg
    exact ⟨hFree, ι, Ziso, hFrag, hIsoB⟩

end
end
end AEC
