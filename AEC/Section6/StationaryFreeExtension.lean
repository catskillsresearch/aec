module

public import AEC.Section6.FreeExtension
public import AEC.Section6.TupleOver
public import AEC.Section6.UniformApproximations
public import AEC.Section6.TestCardinal
public import AEC.Section6.PlacedComparisons
public import AEC.Section4.ClosedLevelTypes
public import AEC.Section5.SingleModelScheme

@[expose] public section

/-!
# Theorem 6.10 (Stationary free extension) — English gloss

English ↔ Lean step map: `FreeExtension.md` (paper pp. 44–45).

**Statement repair.** Same packaging as Lemma 6.9: `SingleModelData` at recursion-closed levels,
with same-level host `p.ν = μ`. `IsFreeLift` queries are bounded by the sequence arity `I.τ`
(English testing cost), not every `#ι < ν`. Cross-scheme transfer is not used.

**E5–E7 tips.** Majority prescriptions and reflected `eB∘qPres` follow §6.2. The free-lift
root `pB` is Prop 4.9 / Lem 6.4 placement `z` on `B` (`placeRoot` via
`infra_610_placement_saturate_to_B`). Soft-pad / global `placement_to_B` stay retired.
Board-open: `infra_610_pull_root_agrees_free_ref` (AgreeOn discharge) and
`infra_610_qPres_empty_joint_on_I` (prescription soft joint). Assembled:
`placement_saturate_to_B` via pull_z + abs match + tip. Blocked on tip:
`placement_root_on_B` → `reflected_matches_chartRoot` → `place_z_as_free_lift`.
-/

namespace AEC
section

universe u

open Cardinal FirstOrder

variable {K : AbstractElementaryClass.{u}}

/-! ## Majority from few exceptions -/

/-- The actual joint `typeJoint Z` is always a majority value of `seq` on `Z` of size
`≤ seq.τ`, by `few_exceptions` and `diagram_symm`. -/
theorem infra_610_majority_eq_type
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hι : #ι ≤ seq.τ) :
    IsMajorityValue seq Z p.hν p.host (typeJoint (p := p) Z) := by
  have hfew := seq.few_exceptions Z hι
  change
    # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Z) (typeJoint (p := p) Z)} ≤ #ι + aleph0
  let e : {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Z) (typeJoint (p := p) Z)} ≃
      {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := p.host) (Y := A)
          (typeJoint (p := p) Z) (seqJoint (seq.family i) Z)} :=
    ⟨fun ⟨i, hi⟩ => ⟨i, fun h => hi (P.scheme.diagram_symm _ _ _ _ h)⟩,
      fun ⟨i, hi⟩ => ⟨i, fun h => hi (P.scheme.diagram_symm _ _ _ _ h)⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Cardinal.mk_congr e]
  exact hfew

/-- If two lists are majority values of `seq` on the same `Z` and the index is longer than
`|Z| + ℵ₀`, they are `DiagramEq`. -/
theorem infra_610_majority_unique
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    {ν₁ ν₂ : Cardinal.{u}} {hν₁ : ν₁ ∈ P.eligible} {hν₂ : ν₂ ∈ P.eligible}
    {repr₁ : P.scheme.Object ν₁ hν₁} {repr₂ : P.scheme.Object ν₂ hν₂}
    (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν₁ repr₁))
    (ys : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν₂ repr₂))
    (hx : IsMajorityValue seq Z hν₁ repr₁ xs)
    (hy : IsMajorityValue seq Z hν₂ repr₂ ys)
    (hκ : #ι + aleph0 < #seq.κIndex) :
    P.scheme.DiagramEq (X := repr₁) (Y := repr₂) xs ys := by
  classical
  by_contra hne
  let Exc₁ : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := repr₁) (seqJoint (seq.family i) Z) xs}
  let Exc₂ : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := repr₂) (seqJoint (seq.family i) Z) ys}
  have hcover : (Set.univ : Set seq.κIndex) ⊆ Exc₁ ∪ Exc₂ := by
    intro i _
    by_cases hxs : P.scheme.DiagramEq (X := A) (Y := repr₁)
        (seqJoint (seq.family i) Z) xs
    · by_cases hys : P.scheme.DiagramEq (X := A) (Y := repr₂)
          (seqJoint (seq.family i) Z) ys
      · exact False.elim (hne (P.scheme.diagram_trans _ _ _ _ _ _
          (P.scheme.diagram_symm _ _ _ _ hxs) hys))
      · exact Or.inr hys
    · exact Or.inl hxs
  have hExc₁ : #Exc₁ ≤ #ι + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := repr₁) (seqJoint (seq.family i) Z) xs} ≤ _
    exact hx
  have hExc₂ : #Exc₂ ≤ #ι + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := repr₂) (seqJoint (seq.family i) Z) ys} ≤ _
    exact hy
  have hle : #seq.κIndex ≤ (#ι + aleph0) + (#ι + aleph0) := by
    have huni : #(Set.univ : Set seq.κIndex) = #seq.κIndex := mk_univ
    rw [← huni]
    exact (mk_le_mk_of_subset hcover).trans ((mk_union_le _ _).trans (add_le_add hExc₁ hExc₂))
  have hinfκ : aleph0 ≤ #seq.κIndex :=
    (le_add_self (a := aleph0) (b := #ι)).trans (le_of_lt hκ)
  have hsum : (#ι + aleph0) + (#ι + aleph0) < #seq.κIndex :=
    add_lt_of_lt hinfκ hκ hκ
  exact not_le_of_gt hsum hle

/-- Canonical majority witness: `typeJoint` itself. -/
theorem infra_610_exists_majority
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hι : #ι ≤ seq.τ) :
    ∃ (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem p.hν p.host)),
      IsMajorityValue seq Z p.hν p.host xs :=
  ⟨typeJoint (p := p) Z, infra_610_majority_eq_type seq Z hι⟩

/-! ## Pinned free-lift bridges -/

/-- Concatenation of the approximation sequence in `A`, pushed along `f : A → B`, keeps
`DiagramEq`. Immediate from `diagram_preserved`. -/
theorem infra_610_concat_push_diagramEq
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) :
    P.scheme.DiagramEq (X := A) (Y := B)
      (fun ij : seq.κIndex × p.idx => seq.family ij.1 ij.2)
      (fun ij =>
        ⟨(seq.family ij.1 ij.2).1,
          f.onVertex (seq.family ij.1 ij.2).1 (seq.family ij.1 ij.2).2⟩) :=
  P.scheme.diagram_preserved A B f hf
    (fun ij : seq.κIndex × p.idx => seq.family ij.1 ij.2)
    seq.concat_bounded seq.concat_bounded

/-- Saturation moves a query `Z` from `B` into `A` over the concatenated sequence: saturate to
a μ-extension, then `diagram_iso` pulls the query half back into `A` while fixing the concat. -/
theorem infra_610_move_query
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p)
    {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hι : #ι ≤ seq.τ) (hιμ : #ι < μ) :
    ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
      ∀ i : seq.κIndex,
        P.scheme.DiagramEq (X := A) (Y := B)
          (seqJoint (seq.family i) Z0)
          (seqJoint
            (fun j =>
              ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
            Z) := by
  classical
  let α : Type u := seq.κIndex × p.idx
  let xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun ij => seq.family ij.1 ij.2
  let base : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun ij => ⟨(xs ij).1, f.onVertex (xs ij).1 (xs ij).2⟩
  let ext : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    Sum.elim base Z
  have hα : #α < μ := seq.concat_bounded
  have hEqPush : P.scheme.DiagramEq (X := A) (Y := B) xs base :=
    infra_610_concat_push_diagramEq f hf seq
  obtain ⟨Z', g, zs, -, hzs, hzsEq⟩ :=
    (SingleModelData.isSaturated (P := P)).saturated
      A B xs base ext hα hιμ (fun i => rfl) hEqPush
  have hPushG : P.scheme.DiagramEq (X := A) (Y := Z') xs
      (fun ij => ⟨(xs ij).1, g.onVertex (xs ij).1 (xs ij).2⟩) :=
    P.scheme.diagram_preserved A Z' g trivial xs hα hα
  have hxsZs : (fun ij => ⟨(xs ij).1, g.onVertex (xs ij).1 (xs ij).2⟩) =
      fun ij => zs (Sum.inl ij) := by
    funext ij
    exact (hzs ij).symm
  have hEqZsInl : P.scheme.DiagramEq (X := A) (Y := Z') xs (fun ij => zs (Sum.inl ij)) := by
    rw [← hxsZs]
    exact hPushG
  obtain ⟨φ, hφiso, hφ⟩ :=
    (P.scheme.diagram_iso A Z' xs (fun ij => zs (Sum.inl ij)) hα).mp hEqZsInl
  have hφbij : Function.Bijective (φ.onVertex PUnit.unit) := hφiso PUnit.unit
  let eφ : A.model.carrier ≃ Z'.model.carrier := Equiv.ofBijective _ hφbij
  let Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun j => A.occ (eφ.symm (Z'.val (zs (Sum.inr j))))
  let jointA : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    Sum.elim xs Z0
  have hφjoint : ∀ t, zs t =
      ⟨(jointA t).1, φ.onVertex (jointA t).1 (jointA t).2⟩ := by
    intro t
    cases t with
    | inl ij =>
      change zs (Sum.inl ij) = ⟨(xs ij).1, φ.onVertex (xs ij).1 (xs ij).2⟩
      exact hφ ij
    | inr j =>
      have happly : φ.onVertex PUnit.unit (eφ.symm (Z'.val (zs (Sum.inr j)))) =
          Z'.val (zs (Sum.inr j)) := eφ.apply_symm_apply _
      change zs (Sum.inr j) = ⟨(Z0 j).1, φ.onVertex (Z0 j).1 (Z0 j).2⟩
      refine Eq.trans (SMObject.occ_val Z' (zs (Sum.inr j))).symm ?_
      refine Eq.trans (congrArg Z'.occ happly.symm) ?_
      simp only [Z0, SMObject.occ, oneVertexOcc, SMObject.val, oneVertexVal]
      rfl
  have hPushφ : P.scheme.DiagramEq (X := A) (Y := Z') jointA zs := by
    have hcard : #(α ⊕ ι) < μ := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact add_lt_of_lt (P.aleph0_le hμ) hα hιμ
    have h := P.scheme.diagram_preserved A Z' φ trivial jointA hcard hcard
    have heq : (fun t => ⟨(jointA t).1, φ.onVertex (jointA t).1 (jointA t).2⟩) = zs :=
      funext fun t => (hφjoint t).symm
    rwa [heq] at h
  have hJointExt : P.scheme.DiagramEq (X := A) (Y := B) jointA ext :=
    P.scheme.diagram_trans A Z' B jointA zs ext hPushφ hzsEq
  refine ⟨Z0, fun i => ?_⟩
  let ρ : p.idx ⊕ ι → α ⊕ ι := fun t =>
    match t with
    | Sum.inl j => Sum.inl (i, j)
    | Sum.inr k => Sum.inr k
  have hρ : Function.Injective ρ := by
    intro x y hxy
    cases x with
    | inl j =>
      cases y with
      | inl j' =>
        simp only [ρ] at hxy
        exact congrArg Sum.inl (Prod.ext_iff.mp (Sum.inl.inj hxy)).2
      | inr k =>
        simp [ρ] at hxy
    | inr k =>
      cases y with
      | inl j =>
        simp [ρ] at hxy
      | inr k' =>
        simp only [ρ] at hxy
        exact congrArg Sum.inr (Sum.inr.inj hxy)
  have hpre :=
    WorkingScheme.diagramEq_precomp (W := P.scheme) A B jointA ext ρ hρ hJointExt
  convert hpre using 1 <;> funext t <;> cases t <;> rfl

/-! ## Place majority on `B` (English E5–E7)

English path (see `FreeExtension.md`): well-ordered chart of `B` → majority prescriptions
via `move_query` (E5) → `proposition_4_9` / `lemma_6_4` → wrap as `TupleOver` over `B` (E6) →
Thm 6.6 diagram tests (E7). Split so each English step is its own tip. -/

/-- E5 support (no Galois/majority): chart of `B`, power-fixed `χ ≤ seq.τ`, free-root, and
majority-valued Prop 4.9 `q`/`hnat`/`hcoh` (so placement matches moved majority). -/
structure Infra610ChartSupport
    {K : AbstractElementaryClass.{u}} (P : SingleModelData K) (σ : Cardinal.{u})
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence p) where
  I : Type u
  linOrder : LinearOrder I
  nonempty : Nonempty I
  wf : WellFoundedLT I
  hIcard : Cardinal.mk I = μ
  hImem : K.Mem (@OrderPresentation.obj K P.E I linOrder nonempty)
  χ : Cardinal.{u}
  hχls : ls K + σ < χ
  hχμ : χ < μ
  hpow : χ ^ σ = χ
  /-- Majority prescriptions need `#β ≤ seq.τ`; we take Prop 4.9’s `χ` equal to the arity. -/
  hχτ : χ = seq.τ
  htestχ : P.g σ + ls K ≤ χ
  eB : (@OrderPresentation.obj K P.E I linOrder nonempty).carrier ≃[K.τ] B.model.carrier
  /-- Empty-query free-root coordinates on `B` (Galois packaging / legacy). -/
  root : p.idx → B.model.carrier
  qPres : ∀ {β : Type u}, #β ≤ χ →
    (β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier) →
    p.idx ⊕ β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier
  hnat : ∀ {β : Type u} (hβ : #β ≤ χ)
    (params : β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier)
    (hpar : #β ≤ σ + χ)
    (hcardI : P.D.t (σ + χ) ≤
      Model.card (@OrderPresentation.obj K P.E I linOrder nonempty)),
    P.D.same hpar hImem hImem hcardI hcardI
      (fun b => qPres hβ params (Sum.inr b)) params
  /-- Pointwise recovery of parameters (stronger than `hnat`; from majority construction). -/
  hinr : ∀ {β : Type u} (hβ : #β ≤ χ)
    (params : β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier)
    (b : β), qPres hβ params (Sum.inr b) = params b
  hcoh : ∀ {β β' : Type u} (hβ : #β ≤ χ) (hβ' : #β' ≤ χ)
    (params : β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier)
    (ι : β' → β) (hjoint : #(p.idx ⊕ β') ≤ σ + χ)
    (hcardI : P.D.t (σ + χ) ≤
      Model.card (@OrderPresentation.obj K P.E I linOrder nonempty)),
    P.D.same hjoint hImem hImem hcardI hcardI
      (fun i => qPres hβ params (Sum.map id ι i))
      (qPres hβ' (fun b => params (ι b)))
  /-- Each prescription is a moved majority answer on `B` (with move diagrams). -/
  hmajPres : ∀ {β : Type u} (hβ : #β ≤ χ)
    (params : β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier),
    ∃ (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      (∀ i : seq.κIndex,
        P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Z0)
          (seqJoint
            (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
            (fun b => B.occ (eB (params b))))) ∧
      IsMajorityValue seq Z0 hμ B
        (fun t => B.occ (eB (qPres hβ params t)))

/-- English E5 data: support plus Thm 6.6 tests and E2–E3 majority transport for the root. -/
structure Infra610ChartPrescriptions
    {K : AbstractElementaryClass.{u}} (P : SingleModelData K) (σ : Cardinal.{u})
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence p)
    extends Infra610ChartSupport (hμ := hμ) P σ f hf p seq where
  /-- Galois tests vs Prop 4.9–reflected `eB ∘ qPres` (identical params; no soft join). -/
  hgalois : ∀ {β : Type u} (hβg : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
    (_ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(p.idx ⊕ β) ≤ ρ)
    (h₀ : P.D.t ρ ≤ Model.card p.host.model)
    (h₁ : P.D.t ρ ≤ Model.card B.model),
    P.D.same hjoint p.host.mem B.mem h₀ h₁
      (Sum.elim (fun i => p.host.val (p.val ((Equiv.refl p.idx).symm i)))
        (fun b => p.incl.onVertex PUnit.unit (params b)))
      (fun t => B.val (B.occ (eB (qPres (hβg.trans htestχ)
        (fun b => eB.symm (f.onVertex PUnit.unit (params b))) t))))
  /-- E2–E3: some majority value of `seq` on a moved query from `B` (good `vi` push).
  Identification with the chart-root joint is `infra_610_majority_matches_root`. -/
  hmajority : ∀ {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
    #ι ≤ seq.τ →
    ∃ (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
      (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      IsMajorityValue seq Z0 hμ B xs
  /-- Lem 6.4 / Prop 4.9 placement root on `B` (English pB coordinates). -/
  placeRoot : p.idx → B.model.carrier
  /-- `placeRoot` realizes all chart prescriptions on `B`. -/
  hPlaceRoot : ∀ {β : Type u} (hβ : #β ≤ χ)
    (paramsI : β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier)
    (hjoint : #(p.idx ⊕ β) ≤ σ + χ)
    (h₁ : P.D.t (σ + χ) ≤ Model.card B.model),
    P.D.same hjoint B.mem B.mem h₁ h₁
      (Sum.elim placeRoot (fun b => eB (paramsI b)))
      (fun t => B.val (B.occ (eB (qPres hβ paramsI t))))

/-- `B`-representative of the free-lift root: Lem 6.4 / Prop 4.9 placement coordinates on `B`
(`placeRoot`), not empty-query `qPres`. -/
noncomputable def Infra610ChartPrescriptions.chartRoot
    {K : AbstractElementaryClass.{u}} {P : SingleModelData K} {σ : Cardinal.{u}}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq) :
    TupleOver K oneVertexShape P.scheme hμ B where
  ν := μ
  hν := hμ
  host := B
  incl := SystemArrow.refl (P.scheme.asSystem hμ B)
  incl_arrow := trivial
  idx := p.idx
  val := fun a => B.occ (data.placeRoot a)

/-- Well-ordered chart of `B` at level `μ`: `E(I) ≃ B` with `#I = μ`. -/
noncomputable def infra_610_chart_of_B
    (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (B : P.scheme.Object μ hμ) :
    Σ' (I : Type u) (_ : LinearOrder I) (_ : Nonempty I) (_ : WellFoundedLT I)
      (_ : #I = μ) (_ : K.Mem (P.E.obj I)),
      (P.E.obj I).carrier ≃[K.τ] B.model.carrier := by
  classical
  let I : Type u := lvlOrder μ
  letI : LinearOrder I := inferInstance
  letI : Nonempty I := inferInstance
  letI : WellFoundedLT I := inferInstance
  have hIcard : #I = μ := mk_lvlOrder (P.aleph0_le hμ)
  have hImem : K.Mem (P.E.obj I) := P.hE I
  -- `P.G μ = E(lvlOrder μ)`, so the level chart of `B` is the required `eB`.
  have eB : (P.E.obj I).carrier ≃[K.τ] B.model.carrier := by
    change (P.G μ).carrier ≃[K.τ] B.model.carrier
    exact (P.chart hμ B).symm
  exact ⟨I, ‹LinearOrder I›, ‹Nonempty I›, ‹WellFoundedLT I›, hIcard, hImem, eB⟩

/-- Power-fixed `χ` above `seq.τ`, `P.g σ + ls K`, and `ls K + σ`, below `μ`. -/
theorem infra_610_choose_chi
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible) (hσμ : σ < μ)
    (τ : Cardinal.{u}) (hτμ : τ < μ) :
    ∃ χ : Cardinal.{u},
      ls K + σ < χ ∧ χ < μ ∧ χ ^ σ = χ ∧ τ ≤ χ ∧ P.g σ + ls K ≤ χ := by
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ
  have hsum : ls K + σ < μ := add_lt_of_lt hμinf (P.ls_lt hμ) hσμ
  have hg : P.g σ < μ :=
    (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσμ
  have hgls : P.g σ + ls K < μ := add_lt_of_lt hμinf hg (P.ls_lt hμ)
  let κ : Cardinal.{u} := max (max τ (P.g σ + ls K)) (ls K + σ)
  have hκμ : κ < μ := max_lt (max_lt hτμ hgls) hsum
  obtain ⟨χ, hχgt, hχμ, hpow⟩ :=
    exists_power_fixed_below hμ.1.working.strongLimit hσ hσμ hκμ
  refine ⟨χ, ?_, hχμ, hpow, ?_, ?_⟩
  · exact (le_max_right (max τ (P.g σ + ls K)) (ls K + σ)).trans_lt hχgt
  · exact (le_max_left τ (P.g σ + ls K)).trans
      ((le_max_left (max τ (P.g σ + ls K)) (ls K + σ)).trans hχgt.le)
  · exact (le_max_right τ (P.g σ + ls K)).trans
      ((le_max_left (max τ (P.g σ + ls K)) (ls K + σ)).trans hχgt.le)

/-- **E5a.** Empty-query good approximation pushed along `f` (free-root coordinates in `B`).
Requires `ℵ₀ < #κIndex` so the empty-query exception set is proper. -/
theorem infra_610_free_root
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (_hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p)
    (hκ : aleph0 < #seq.κIndex) :
    ∃ (root : p.idx → B.model.carrier) (i0 : seq.κIndex),
      P.scheme.DiagramEq (X := A) (Y := p.host)
        (seqJoint (seq.family i0) (PEmpty.elim : PEmpty.{u + 1} → _))
        (typeJoint (p := p) (PEmpty.elim : PEmpty.{u + 1} → _)) ∧
      (∀ a, root a = f.onVertex (seq.family i0 a).1 (seq.family i0 a).2) := by
  classical
  let Zempty : PEmpty.{u + 1} → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    PEmpty.elim
  have hι0 : #(PEmpty.{u + 1}) ≤ seq.τ := by
    simpa using (zero_le seq.τ : (0 : Cardinal.{u}) ≤ seq.τ)
  have hmaj0 := infra_610_majority_eq_type seq Zempty hι0
  let Exc0 : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Zempty) (typeJoint (p := p) Zempty)}
  have hExc0 : #Exc0 ≤ aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Zempty) (typeJoint (p := p) Zempty)} ≤ _
    have h := hmaj0
    simp only [IsMajorityValue] at h
    have hpe : #(PEmpty.{u + 1}) = (0 : Cardinal.{u}) := mk_eq_zero _
    simpa [Exc0, hpe] using h
  have hExc_lt : #Exc0 < #seq.κIndex := hExc0.trans_lt hκ
  have hex_i0 : ∃ i0 : seq.κIndex, i0 ∉ Exc0 := by
    by_contra h
    have hall : ∀ i, i ∈ Exc0 := by
      intro i
      by_contra hi
      exact h ⟨i, hi⟩
    have huni : Exc0 = Set.univ := Set.eq_univ_of_forall hall
    have : #Exc0 = #seq.κIndex := by rw [huni, mk_univ]
    exact (this ▸ hExc_lt).false
  obtain ⟨i0, hi0⟩ := hex_i0
  have hi0good : P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i0) Zempty) (typeJoint (p := p) Zempty) := by
    simpa [Exc0] using hi0
  refine ⟨fun a => f.onVertex (seq.family i0 a).1 (seq.family i0 a).2, i0, hi0good, fun _ => rfl⟩

/-- Pull a majority answer on `B` back along a language equiv of models. -/
noncomputable def infra_610_pullMajority
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {B : P.scheme.Object μ hμ}
    {M : Model K.τ} (eB : M.carrier ≃[K.τ] B.model.carrier)
    {α : Type u} (xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) :
    α → M.carrier :=
  fun t => eB.symm (B.val (xs t))

/-- Reindexing a majority answer along a parameter map: common good index + uniqueness.
Uses `SameD.comp` (no injectivity of `ι` required). -/
theorem infra_610_majority_reindex
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (_hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    {β β' : Type u}
    (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (ι : β' → β) (hβ : #β ≤ seq.τ) (hβ' : #β' ≤ seq.τ)
    (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (Z0' : β' → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (xs : p.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (xs' : p.idx ⊕ β' → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hmaj : IsMajorityValue seq Z0 hμ B xs)
    (hmaj' : IsMajorityValue seq Z0' hμ B xs')
    (hmove : ∀ i : seq.κIndex,
      P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Z0)
        (seqJoint
          (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩) Z))
    (hmove' : ∀ i : seq.κIndex,
      P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Z0')
        (seqJoint
          (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
          (fun b => Z (ι b)))) :
    P.scheme.DiagramEq (X := B) (Y := B) (fun t => xs (Sum.map id ι t)) xs' := by
  classical
  have hbound : #β' + aleph0 < #seq.κIndex :=
    (add_le_add hβ' le_rfl).trans_lt hκ
  have hboundβ : #β + aleph0 < #seq.κIndex :=
    (add_le_add hβ le_rfl).trans_lt hκ
  have hinfκ : aleph0 ≤ #seq.κIndex :=
    (le_add_self (a := aleph0) (b := #β')).trans (le_of_lt hbound)
  let Exc : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0)}
  let Exc' : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Z0') (typeJoint (p := p) Z0')}
  have hExc : #Exc ≤ #β + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0)} ≤ _
    exact infra_610_majority_eq_type seq Z0 hβ
  have hExc'card : #Exc' ≤ #β' + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Z0') (typeJoint (p := p) Z0')} ≤ _
    exact infra_610_majority_eq_type seq Z0' hβ'
  have hex : ∃ i : seq.κIndex, i ∉ Exc ∧ i ∉ Exc' := by
    by_contra h
    have hall : (Set.univ : Set seq.κIndex) ⊆ Exc ∪ Exc' := by
      intro i _
      by_cases hi : i ∈ Exc ∪ Exc'
      · exact hi
      · exact False.elim (h ⟨i, by
          simp only [Set.mem_union, not_or] at hi
          exact hi⟩)
    have hle : #seq.κIndex ≤ (#β + aleph0) + (#β' + aleph0) := by
      have huni : #(Set.univ : Set seq.κIndex) = #seq.κIndex := mk_univ
      rw [← huni]
      exact (mk_le_mk_of_subset hall).trans
        ((mk_union_le _ _).trans (add_le_add hExc hExc'card))
    exact (not_le_of_gt (add_lt_of_lt hinfκ hboundβ hbound)) hle
  obtain ⟨i, hi, hi'⟩ := hex
  have hgood : P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0) := by
    simpa [Exc] using hi
  have hgood' : P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Z0') (typeJoint (p := p) Z0') := by
    simpa [Exc'] using hi'
  let pushed : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩
  have hT : IsMajorityValue seq Z0 p.hν p.host (typeJoint (p := p) Z0) :=
    infra_610_majority_eq_type seq Z0 hβ
  have hT' : IsMajorityValue seq Z0' p.hν p.host (typeJoint (p := p) Z0') :=
    infra_610_majority_eq_type seq Z0' hβ'
  have hU := infra_610_majority_unique seq Z0 (xs := xs) (ys := typeJoint (p := p) Z0)
    hmaj hT hboundβ
  have hU' := infra_610_majority_unique seq Z0' (xs := xs') (ys := typeJoint (p := p) Z0')
    hmaj' hT' hbound
  have hxsPush : P.scheme.DiagramEq (X := B) (Y := B) xs (seqJoint pushed Z) :=
    P.scheme.diagram_trans B p.host B xs (typeJoint (p := p) Z0) (seqJoint pushed Z) hU
      (P.scheme.diagram_trans p.host A B (typeJoint (p := p) Z0)
        (seqJoint (seq.family i) Z0) (seqJoint pushed Z)
        (P.scheme.diagram_symm A p.host _ _ hgood) (hmove i))
  have hxsPush' : P.scheme.DiagramEq (X := B) (Y := B) xs'
      (seqJoint pushed (fun b => Z (ι b))) :=
    P.scheme.diagram_trans B p.host B xs' (typeJoint (p := p) Z0')
      (seqJoint pushed (fun b => Z (ι b))) hU'
      (P.scheme.diagram_trans p.host A B (typeJoint (p := p) Z0')
        (seqJoint (seq.family i) Z0') (seqJoint pushed (fun b => Z (ι b)))
        (P.scheme.diagram_symm A p.host _ _ hgood') (hmove' i))
  have hκpos : aleph0 ≤ #seq.κIndex :=
    (le_add_self (a := aleph0) (b := seq.τ)).trans (le_of_lt hκ)
  have hidxμ : #p.idx < μ := by
    have : #p.idx ≤ #seq.κIndex * #p.idx :=
      le_mul_of_one_le_left (bot_le (a := (#p.idx : Cardinal.{u}))) (one_le_aleph0.trans hκpos)
    simpa [mk_prod, lift_id, lift_id] using this.trans_lt seq.concat_bounded
  have hβμ : #β < μ := hβ.trans_lt hτμ
  have hβ'μ : #β' < μ := hβ'.trans_lt hτμ
  have hαμ : #(p.idx ⊕ β) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hidxμ hβμ
  have hα'μ : #(p.idx ⊕ β') < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hidxμ hβ'μ
  -- Reindex `hxsPush` along `Sum.map id ι` via `SameD.comp` (no injectivity).
  have hxsR : P.scheme.DiagramEq (X := B) (Y := B) (fun t => xs (Sum.map id ι t))
      (seqJoint pushed (fun b => Z (ι b))) := by
    have hSame :
        P.D.SameD B.model B.model (fun t => B.val (xs t))
          (fun t => B.val (seqJoint pushed Z t)) :=
      (SingleModelData.diagramEq_iff_sameD (P := P) (α := p.idx ⊕ β) hμ hμ B B
        (fun t => B.val (xs t)) (fun t => B.val (seqJoint pushed Z t)) hαμ hαμ).mp
        hxsPush
    have hSameR :=
      SingleModelData.sameD_comp (P := P) hμ hμ B.card B.card hSame (Sum.map id ι)
        hαμ hαμ hα'μ hα'μ
    have hre : (fun t => B.val (seqJoint pushed Z (Sum.map id ι t))) =
        (fun t => B.val (seqJoint pushed (fun b => Z (ι b)) t)) := by
      funext t; cases t <;> rfl
    have hSameR' : P.D.SameD B.model B.model
        (fun t => B.val (xs (Sum.map id ι t)))
        (fun t => B.val (seqJoint pushed (fun b => Z (ι b)) t)) := by
      convert hSameR using 1
      exact hre.symm
    exact (SingleModelData.diagramEq_iff_sameD (P := P) (α := p.idx ⊕ β') hμ hμ B B
      (fun t => B.val (xs (Sum.map id ι t)))
      (fun t => B.val (seqJoint pushed (fun b => Z (ι b)) t)) hα'μ hα'μ).mpr hSameR'
  exact P.scheme.diagram_trans B B B _ _ _ hxsR
    (P.scheme.diagram_symm B B _ _ hxsPush')


/-- **E5b (legacy packaging).** Param-freeing Prop 4.9 prescriptions from a fixed root.
Retained for `chart_support` until majority `qPres` is wired after `moved_majority`. -/
theorem infra_610_param_freeing_qPres
    (P : SingleModelData K) (σ : Cardinal.{u})
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {I : Type u} [linOrder : LinearOrder I] [nonempty : Nonempty I]
    (hImem : K.Mem (P.E.obj I))
    (eB : (P.E.obj I).carrier ≃[K.τ] B.model.carrier)
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (root : p.idx → B.model.carrier)
    (χ : Cardinal.{u}) :
    ∃ (qPres : ∀ {β : Type u}, #β ≤ χ →
        (β → (P.E.obj I).carrier) → p.idx ⊕ β → (P.E.obj I).carrier),
      (∀ {β : Type u} (hβ : #β ≤ χ) (params : β → (P.E.obj I).carrier)
        (hpar : #β ≤ σ + χ)
        (hcardI : P.D.t (σ + χ) ≤ Model.card (P.E.obj I)),
        P.D.same hpar hImem hImem hcardI hcardI
          (fun b => qPres hβ params (Sum.inr b)) params) ∧
      (∀ {β β' : Type u} (hβ : #β ≤ χ) (hβ' : #β' ≤ χ)
        (params : β → (P.E.obj I).carrier) (ι : β' → β)
        (hjoint : #(p.idx ⊕ β') ≤ σ + χ)
        (hcardI : P.D.t (σ + χ) ≤ Model.card (P.E.obj I)),
        P.D.same hjoint hImem hImem hcardI hcardI
          (fun i => qPres hβ params (Sum.map id ι i))
          (qPres hβ' (fun b => params (ι b)))) := by
  let qPres : ∀ {β : Type u}, #β ≤ χ →
      (β → (P.E.obj I).carrier) → p.idx ⊕ β → (P.E.obj I).carrier :=
    fun {_β} _hβ params => Sum.elim (fun a => eB.symm (root a)) params
  refine ⟨qPres, ?_, ?_⟩
  · intro β hβ params hpar hcardI
    exact P.D.refl hpar hImem hcardI params
  · intro β β' hβ hβ' params ι hjoint hcardI
    convert P.D.refl hjoint hImem hcardI
      (Sum.elim (fun a => eB.symm (root a)) (fun b => params (ι b))) using 1
    funext t; cases t <;> rfl

/-- **E5d.** After `move_query`, a `Z0`-good approximation pushed along `f` is a majority
value of `seq` on `Z`. Requires `seq.τ + ℵ₀ < #κIndex` so every `≤ τ` query has a good index. -/
theorem infra_610_moved_majority
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hι : #ι ≤ seq.τ) :
    ∃ (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
      (i : seq.κIndex),
      (∀ k : seq.κIndex,
        P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family k) Z0)
          (seqJoint
            (fun j => ⟨(seq.family k j).1, f.onVertex (seq.family k j).1 (seq.family k j).2⟩)
            Z)) ∧
      P.scheme.DiagramEq (X := A) (Y := p.host)
        (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0) ∧
      IsMajorityValue seq Z0 hμ B
        (seqJoint
          (fun j =>
            ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
          Z) := by
  classical
  have hιμ : #ι < μ := hι.trans_lt hτμ
  obtain ⟨Z0, hmove⟩ := infra_610_move_query f hf seq Z hι hιμ
  have hExcType : # {i : seq.κIndex //
      ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
        (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0)} ≤ #ι + aleph0 :=
    infra_610_majority_eq_type seq Z0 hι
  have hExc_lt : # {i : seq.κIndex //
      ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
        (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0)} < #seq.κIndex :=
    hExcType.trans_lt ((add_le_add hι le_rfl).trans_lt hκ)
  have hex : ∃ i : seq.κIndex,
      P.scheme.DiagramEq (X := A) (Y := p.host)
        (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0) := by
    by_contra h
    have hall : ∀ i, ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
        (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0) := by
      intro i hi
      exact h ⟨i, hi⟩
    let e : {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0)} ≃ seq.κIndex :=
      ⟨fun ⟨i, _⟩ => i, fun i => ⟨i, hall i⟩, fun _ => rfl, fun _ => rfl⟩
    have huni : # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0)} = #seq.κIndex :=
      Cardinal.mk_congr e
    exact (huni ▸ hExc_lt).false
  obtain ⟨i, hgood⟩ := hex
  let pushed : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩
  let xs := seqJoint pushed Z
  have hmaj : IsMajorityValue seq Z0 hμ B xs := by
    change # {j : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family j) Z0) xs} ≤ _
    have hmono : ∀ j,
        ¬ P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family j) Z0) xs →
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family j) Z0) (typeJoint (p := p) Z0) := by
      intro j hxs htype
      apply hxs
      have hji : P.scheme.DiagramEq (X := A) (Y := A)
          (seqJoint (seq.family j) Z0) (seqJoint (seq.family i) Z0) :=
        P.scheme.diagram_trans A p.host A
          (seqJoint (seq.family j) Z0) (typeJoint (p := p) Z0) (seqJoint (seq.family i) Z0)
          htype (P.scheme.diagram_symm A p.host _ _ hgood)
      exact P.scheme.diagram_trans A A B
        (seqJoint (seq.family j) Z0) (seqJoint (seq.family i) Z0) xs
        hji (hmove i)
    exact (mk_subtype_mono hmono).trans hExcType
  exact ⟨Z0, i, hmove, hgood, hmaj⟩

/-- **E5b.** Prop 4.9 prescriptions from per-query moved majority answers (`χ = seq.τ`).
`hls` lets `same_relevel` use intermediate bound `σ + seq.τ` (no extra `ls` bump). -/
theorem infra_610_majority_qPres
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    {I : Type u} [linOrder : LinearOrder I] [nonempty : Nonempty I]
    (hImem : K.Mem (P.E.obj I))
    (eB : (P.E.obj I).carrier ≃[K.τ] B.model.carrier)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ) (hls : ls K ≤ σ + seq.τ) :
    ∃ (qPres : ∀ {β : Type u}, #β ≤ seq.τ →
        (β → (P.E.obj I).carrier) → p.idx ⊕ β → (P.E.obj I).carrier),
      (∀ {β : Type u} (hβ : #β ≤ seq.τ) (params : β → (P.E.obj I).carrier)
        (hpar : #β ≤ σ + seq.τ)
        (hcardI : P.D.t (σ + seq.τ) ≤ Model.card (P.E.obj I)),
        P.D.same hpar hImem hImem hcardI hcardI
          (fun b => qPres hβ params (Sum.inr b)) params) ∧
      (∀ {β : Type u} (hβ : #β ≤ seq.τ)
        (params : β → (P.E.obj I).carrier) (b : β),
        qPres hβ params (Sum.inr b) = params b) ∧
      (∀ {β β' : Type u} (hβ : #β ≤ seq.τ) (hβ' : #β' ≤ seq.τ)
        (params : β → (P.E.obj I).carrier) (ι : β' → β)
        (hjoint : #(p.idx ⊕ β') ≤ σ + seq.τ)
        (hcardI : P.D.t (σ + seq.τ) ≤ Model.card (P.E.obj I)),
        P.D.same hjoint hImem hImem hcardI hcardI
          (fun i => qPres hβ params (Sum.map id ι i))
          (qPres hβ' (fun b => params (ι b)))) ∧
      (∀ {β : Type u} (hβ : #β ≤ seq.τ) (params : β → (P.E.obj I).carrier),
        ∃ (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
          (∀ i : seq.κIndex,
            P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Z0)
              (seqJoint
                (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
                (fun b => B.occ (eB (params b))))) ∧
          IsMajorityValue seq Z0 hμ B
            (fun t => B.occ (eB (qPres hβ params t)))) := by
  classical
  have hex : ∀ {β : Type u} (hβ : #β ≤ seq.τ) (params : β → (P.E.obj I).carrier),
      ∃ (answer : p.idx ⊕ β → (P.E.obj I).carrier)
        (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
        (∀ b, answer (Sum.inr b) = params b) ∧
        (∀ i : seq.κIndex,
          P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Z0)
            (seqJoint
              (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
              (fun b => B.occ (eB (params b))))) ∧
        IsMajorityValue seq Z0 hμ B (fun t => B.occ (eB (answer t))) := by
    intro β hβ params
    let Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
      fun b => B.occ (eB (params b))
    obtain ⟨Z0, i, hmove, _, hmaj⟩ := infra_610_moved_majority f hf seq hτμ hκ Z hβ
    let pushed : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
      fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩
    let xs := seqJoint pushed Z
    refine ⟨infra_610_pullMajority eB xs, Z0, ?_, hmove, ?_⟩
    · intro b
      change eB.symm (eB (params b)) = params b
      exact Language.Equiv.symm_apply_apply eB (params b)
    · have hx : (fun t => B.occ (eB (infra_610_pullMajority eB xs t))) = xs := by
        funext t
        change B.occ (eB (eB.symm (B.val (xs t)))) = xs t
        rw [Language.Equiv.apply_symm_apply]
        rfl
      exact hx.symm ▸ hmaj
  let qPres : ∀ {β : Type u}, #β ≤ seq.τ →
      (β → (P.E.obj I).carrier) → p.idx ⊕ β → (P.E.obj I).carrier :=
    fun {_β} hβ params => Classical.choose (hex hβ params)
  have hqSpec : ∀ {β : Type u} (hβ : #β ≤ seq.τ) (params : β → (P.E.obj I).carrier),
      ∃ Z0, (∀ b, qPres hβ params (Sum.inr b) = params b) ∧
        (∀ i : seq.κIndex,
          P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Z0)
            (seqJoint
              (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
              (fun b => B.occ (eB (params b))))) ∧
        IsMajorityValue seq Z0 hμ B
          (fun t => B.occ (eB (qPres hβ params t))) := by
    intro β hβ params
    obtain ⟨Z0, hinr, hmove, hmaj⟩ := Classical.choose_spec (hex hβ params)
    exact ⟨Z0, hinr, hmove, hmaj⟩
  refine ⟨qPres, ?_, ?_, ?_, ?_⟩
  · intro β hβ params hpar hcardI
    obtain ⟨_, hinr, _, _⟩ := hqSpec hβ params
    convert P.D.refl hpar hImem hcardI params using 1
    exact funext hinr
  · intro β hβ params b
    obtain ⟨_, hinr, _, _⟩ := hqSpec hβ params
    exact hinr b
  · intro β β' hβ hβ' params ι hjoint hcardI
    obtain ⟨Z0, _, hmove, hmaj⟩ := hqSpec hβ params
    obtain ⟨Z0', _, hmove', hmaj'⟩ := hqSpec hβ' (fun b => params (ι b))
    let xs := fun t => B.occ (eB (qPres hβ params t))
    let xs' := fun t => B.occ (eB (qPres hβ' (fun b => params (ι b)) t))
    have hEqB := infra_610_majority_reindex f hf seq hτμ hκ
      (fun b => B.occ (eB (params b))) ι hβ hβ' Z0 Z0' xs xs' hmaj hmaj' hmove hmove'
    have hαμ : #(p.idx ⊕ β') < μ :=
      hjoint.trans_lt (add_lt_of_lt (P.aleph0_le hμ) hσμ hτμ)
    have hSame : P.D.SameD B.model B.model
        (fun t => B.val (xs (Sum.map id ι t))) (fun t => B.val (xs' t)) :=
      (SingleModelData.diagramEq_iff_sameD (P := P) hμ hμ B B
        (fun t => B.val (xs (Sum.map id ι t))) (fun t => B.val (xs' t)) hαμ hαμ).mp hEqB
    obtain ⟨_, _, hMcB, hNcB, hs⟩ := hSame
    let ρ0 : Cardinal.{u} := max #(p.idx ⊕ β') aleph0
    let ρ : Cardinal.{u} := σ + seq.τ
    have hρ0inf : aleph0 ≤ ρ0 := le_max_right _ _
    have hρinf : aleph0 ≤ ρ := hσ.trans (self_le_add_right σ seq.τ)
    have hρ0le : ρ0 ≤ ρ :=
      max_le hjoint (hσ.trans (self_le_add_right σ seq.τ))
    have hMcI0 : P.D.t ρ0 ≤ Model.card (P.E.obj I) :=
      (P.D.mono _ _ hρ0le).trans hcardI
    have hstrong : K.Strong eB.toEmbedding := strong_of_equiv K eB hImem
    have hval : ∀ t, B.val (xs (Sum.map id ι t)) =
        eB (qPres hβ params (Sum.map id ι t)) := by
      intro t; rfl
    have hval' : ∀ t, B.val (xs' t) =
        eB (qPres hβ' (fun b => params (ι b)) t) := by
      intro t; rfl
    have h1 := P.D.of_strong (le_max_left _ _) hImem B.mem hMcI0 hMcB
      (fun t => qPres hβ params (Sum.map id ι t))
      (fun t => B.val (xs (Sum.map id ι t)))
      eB.toEmbedding hρ0inf hstrong (fun t => (hval t).symm)
    have h2 := P.D.of_strong (le_max_left _ _) hImem B.mem hMcI0 hNcB
      (fun t => qPres hβ' (fun b => params (ι b)) t)
      (fun t => B.val (xs' t))
      eB.toEmbedding hρ0inf hstrong (fun t => (hval' t).symm)
    have hsI0 : P.D.same (le_max_left _ _) hImem hImem hMcI0 hMcI0
        (fun t => qPres hβ params (Sum.map id ι t))
        (fun t => qPres hβ' (fun b => params (ι b)) t) :=
      P.D.trans (le_max_left _ _) hImem B.mem hImem hMcI0 hMcB hMcI0 _ _ _
        h1 (P.D.trans (le_max_left _ _) B.mem B.mem hImem hMcB hNcB hMcI0 _ _ _
          hs (P.D.symm (le_max_left _ _) hImem B.mem hMcI0 hNcB _ _ h2))
    exact P.D.same_relevel (σ := ρ0) (τ := ρ) (σ' := ρ)
      (le_max_left _ _) hρ0inf hρinf hρ0le le_rfl hls hImem hImem
      hMcI0 hMcI0 hcardI hcardI hcardI hcardI _ _ hsI0 hjoint id
  · intro β hβ params
    obtain ⟨Z0, _, hmove, hmaj⟩ := hqSpec hβ params
    exact ⟨Z0, hmove, hmaj⟩

/-- **E5c.** Assemble chart + power-fixed `χ = seq.τ` + free-root + majority `qPres`.
Caller must supply the Prop 4.9 cardinal hypotheses on `seq.τ` (see `exists`). -/
theorem infra_610_chart_support
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hidx : #p.idx ≤ σ)
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hχls : ls K + σ < seq.τ) (hpow : seq.τ ^ σ = seq.τ)
    (htestχ : P.g σ + ls K ≤ seq.τ) :
    Nonempty (Infra610ChartSupport (hμ := hμ) P σ f hf p seq) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hκ0 : aleph0 < #seq.κIndex :=
    (self_le_add_left aleph0 seq.τ).trans_lt hκ
  obtain ⟨I, linOrder, nonempty, wf, hIcard, hImem, eB⟩ := infra_610_chart_of_B P hμ B
  obtain ⟨root, _, _, _⟩ := infra_610_free_root f hf seq hκ0
  have hls : ls K ≤ σ + seq.τ := by
    have h1 : ls K ≤ ls K + σ := le_self_add
    have h2 : ls K + σ ≤ seq.τ := hχls.le
    have h3 : seq.τ ≤ σ + seq.τ := self_le_add_left _ _
    exact h1.trans (h2.trans h3)
  obtain ⟨qPres, hnat, hinr, hcoh, hmajPres⟩ :=
    infra_610_majority_qPres P σ hσ f hf seq hτμ hκ hImem eB hidx hσlt hls
  exact ⟨{
    I := I
    linOrder := linOrder
    nonempty := nonempty
    wf := wf
    hIcard := hIcard
    hImem := hImem
    χ := seq.τ
    hχls := hχls
    hχμ := hτμ
    hpow := hpow
    hχτ := rfl
    htestχ := htestχ
    eB := eB
    root := root
    qPres := qPres
    hnat := hnat
    hinr := hinr
    hcoh := hcoh
    hmajPres := hmajPres
  }⟩

/-! ## Place_z plan theorems (board children of `infra_610_place_z_as_free_lift`) -/

/-- **place_z / onB.** Reflect a `D.same` joint from the chart `E(I)` to `B` along `eB`. -/
theorem infra_610_reflect_joint_eB
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq)
    {γ : Type u} (hγ : #γ ≤ σ + data.χ)
    (xs ys : γ → (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
    (hcardI : P.D.t (σ + data.χ) ≤
      Model.card (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty))
    (h₁ : P.D.t (σ + data.χ) ≤ Model.card B.model)
    (hsame : P.D.same hγ data.hImem data.hImem hcardI hcardI xs ys) :
    P.D.same hγ B.mem B.mem h₁ h₁
      (fun t => B.val (B.occ (data.eB (xs t))))
      (fun t => B.val (B.occ (data.eB (ys t)))) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  have hσχinf : aleph0 ≤ σ + data.χ := hσ.trans (self_le_add_right σ data.χ)
  have hls : ls K ≤ σ + data.χ := by
    have h1 : ls K ≤ ls K + σ := le_self_add
    have h2 : ls K + σ < data.χ := data.hχτ ▸ data.hχls
    exact h1.trans (h2.le.trans (by rw [add_comm]; exact self_le_add_right data.χ σ))
  have hstrong : K.Strong data.eB.toEmbedding := strong_of_equiv K data.eB data.hImem
  have hx : ∀ t, B.val (B.occ (data.eB (xs t))) = data.eB (xs t) := fun t =>
    SMObject.val_occ B _
  have hy : ∀ t, B.val (B.occ (data.eB (ys t))) = data.eB (ys t) := fun t =>
    SMObject.val_occ B _
  have h1 := P.D.of_strong hγ data.hImem B.mem hcardI h₁ xs
    (fun t => B.val (B.occ (data.eB (xs t)))) data.eB.toEmbedding hσχinf hstrong
    (fun t => (hx t).symm)
  have h2 := P.D.of_strong hγ data.hImem B.mem hcardI h₁ ys
    (fun t => B.val (B.occ (data.eB (ys t)))) data.eB.toEmbedding hσχinf hstrong
    (fun t => (hy t).symm)
  exact P.D.trans hγ B.mem data.hImem B.mem h₁ hcardI h₁ _ _ _
    (P.D.symm hγ data.hImem B.mem hcardI h₁ _ _ h1)
    (P.D.trans hγ data.hImem data.hImem B.mem hcardI hcardI h₁ _ _ _ hsame h2)

/-- **place_z / prop49.** Prop 4.9 package: `J`, `fIJ`, `z`, `hPlace` on chart prescriptions. -/
noncomputable def infra_610_place_z_prop49
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) :=
  letI := data.linOrder
  letI := data.nonempty
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  @proposition_4_9 K _ P.E P.D data.I data.linOrder data.nonempty data.wf
    p.idx σ data.χ hσ hidx data.hχls data.hpow data.hImem data.qPres data.hnat data.hcoh

/-- **place_z / empty.** Empty-query `hPlace`: `z ~ E.map fIJ (qPres ∅ ∘ inl)`. -/
theorem infra_610_hPlace_empty
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ) :
    letI := data.linOrder
    letI := data.nonempty
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (fIJ : data.I ↪o J)
      (z : p.idx → (P.E.obj J).carrier) (hJ : K.Mem (P.E.obj J))
      (_hcardI : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj data.I))
      (hcardJ : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj J)),
      P.D.same (α := p.idx) (hidx.trans (self_le_add_right σ data.χ))
        hJ hJ hcardJ hcardJ z
        (fun a => P.E.map fIJ (data.qPres
          (β := PEmpty.{u + 1})
          (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ))
          PEmpty.elim (Sum.inl a))) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  obtain ⟨J, linJ, nonJ, fIJ, z, hJ, hPlace⟩ := infra_610_place_z_prop49 hσ data hidx
  letI := linJ
  letI := nonJ
  have hσχinf : aleph0 ≤ σ + data.χ := hσ.trans (self_le_add_right σ data.χ)
  have hσχμ : σ + data.χ < μ := add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ
  have hIc : Model.card (P.E.obj data.I) = μ :=
    SingleModelData.card_obj_eq (P := P) hμ data.I data.hIcard
  have hcardI : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj data.I) :=
    (P.t_lt hμ hσχinf hσχμ).le.trans hIc.ge
  have hcardJ : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj J) :=
    hcardI.trans (mk_le_of_injective (P.E.map fIJ).injective)
  have hβ0 : #(PEmpty.{u + 1}) ≤ data.χ := by
    simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ)
  have hjoint0 : #(p.idx ⊕ PEmpty.{u + 1}) ≤ σ + data.χ := by
    simp [mk_sum, mk_eq_zero, add_zero]
    exact hidx.trans (self_le_add_right σ data.χ)
  have hP := hPlace hβ0 (PEmpty.elim : PEmpty.{u + 1} → _) hjoint0 hcardI hcardJ
  have hα : #p.idx ≤ σ + data.χ := hidx.trans (self_le_add_right σ data.χ)
  have hls : ls K ≤ σ + data.χ := by
    have h1 : ls K ≤ ls K + σ := le_self_add
    have h2 : ls K + σ < data.χ := data.hχτ ▸ data.hχls
    exact h1.trans (h2.le.trans (by rw [add_comm]; exact self_le_add_right data.χ σ))
  refine ⟨J, linJ, nonJ, fIJ, z, hJ, hcardI, hcardJ, ?_⟩
  exact P.D.same_relevel hjoint0 hσχinf hσχinf le_rfl le_rfl hls hJ hJ hcardJ hcardJ
    hcardJ hcardJ hcardJ hcardJ _ _ hP hα Sum.inl

/-- **place_z / full.** Full `hPlace`: `Sum.elim z (E.map params) ~ E.map ∘ qPres`. -/
theorem infra_610_hPlace_full
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ)
    {β : Type u} (hβχ : #β ≤ data.χ)
    (paramsI : β →
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
    (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ) :
    letI := data.linOrder
    letI := data.nonempty
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (fIJ : data.I ↪o J)
      (z : p.idx → (P.E.obj J).carrier) (hJ : K.Mem (P.E.obj J))
      (_hcardI : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj data.I))
      (hcardJ : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj J)),
      P.D.same hjoint hJ hJ hcardJ hcardJ
        (Sum.elim z (fun b => P.E.map fIJ (paramsI b)))
        (fun t => P.E.map fIJ (data.qPres hβχ paramsI t)) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  obtain ⟨J, linJ, nonJ, fIJ, z, hJ, hPlace⟩ := infra_610_place_z_prop49 hσ data hidx
  letI := linJ
  letI := nonJ
  have hσχinf : aleph0 ≤ σ + data.χ := hσ.trans (self_le_add_right σ data.χ)
  have hσχμ : σ + data.χ < μ := add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ
  have hIc : Model.card (P.E.obj data.I) = μ :=
    SingleModelData.card_obj_eq (P := P) hμ data.I data.hIcard
  have hcardI : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj data.I) :=
    (P.t_lt hμ hσχinf hσχμ).le.trans hIc.ge
  have hcardJ : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj J) :=
    hcardI.trans (mk_le_of_injective (P.E.map fIJ).injective)
  have hP := hPlace hβχ paramsI hjoint hcardI hcardJ
  refine ⟨J, linJ, nonJ, fIJ, z, hJ, hcardI, hcardJ, ?_⟩
  convert hP using 1
  funext t
  cases t <;> rfl

/-! ### Retired: `infra_610_qPres_matches_empty_joint`

Lean soft-pad of empty `hPlace` with shared params. No §6.2 sentence. Stay retired.
-/

/-- **Done helper.** Empty reindex of a prescription matches the empty-query prescription head. -/
theorem infra_610_qPres_inl_matches_empty
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ)
    {β : Type u} (hβ : #β ≤ data.χ)
    (params : β → (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
    (hcardI : P.D.t (σ + data.χ) ≤
      Model.card (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty)) :
    letI := data.linOrder
    letI := data.nonempty
    P.D.same (α := p.idx) (hidx.trans (self_le_add_right σ data.χ))
      data.hImem data.hImem hcardI hcardI
      (fun a => data.qPres hβ params (Sum.inl a))
      (fun a => data.qPres
        (β := PEmpty.{u + 1})
        (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ))
        PEmpty.elim (Sum.inl a)) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  have hβ0 : #(PEmpty.{u + 1}) ≤ data.χ := by
    simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ)
  have hjoint0 : #(p.idx ⊕ PEmpty.{u + 1}) ≤ σ + data.χ := by
    simp [mk_sum, mk_eq_zero, add_zero]
    exact hidx.trans (self_le_add_right σ data.χ)
  have hσχinf : aleph0 ≤ σ + data.χ := hσ.trans (self_le_add_right σ data.χ)
  have hls : ls K ≤ σ + data.χ := by
    have h1 : ls K ≤ ls K + σ := le_self_add
    have h2 : ls K + σ < data.χ := data.hχτ ▸ data.hχls
    exact h1.trans (h2.le.trans (by rw [add_comm]; exact self_le_add_right data.χ σ))
  have hcoh0 := data.hcoh hβ hβ0 params (PEmpty.elim : PEmpty.{u + 1} → β) hjoint0 hcardI
  have hα : #p.idx ≤ σ + data.χ := hidx.trans (self_le_add_right σ data.χ)
  have hparams : (fun b : PEmpty.{u + 1} => params (PEmpty.elim b)) = PEmpty.elim :=
    funext fun b => nomatch b
  have hre := P.D.same_relevel hjoint0 hσχinf hσχinf le_rfl le_rfl hls data.hImem data.hImem
    hcardI hcardI hcardI hcardI hcardI hcardI _ _ hcoh0 hα Sum.inl
  convert hre using 1
  · funext a; rfl
  · funext a; simp only [hparams]

/-- **Done.** μ-hull of Prop 4.9 chart image ∪ `z` inside `E(J)`, with chart factor and
`zN` section. -/
theorem infra_610_placement_mu_hull
    {P : SingleModelData K} {σ : Cardinal.{u}} (_hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ)
    {J : Type u} [LinearOrder J] [Nonempty J]
    (emb : Language.Embedding K.τ
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier
      (P.E.obj J).carrier)
    (hemb : K.Strong emb) (z : p.idx → (P.E.obj J).carrier) (hJ : K.Mem (P.E.obj J)) :
    ∃ (N : Model K.τ) (i : Language.Embedding K.τ N.carrier (P.E.obj J).carrier)
      (j : Language.Embedding K.τ
        (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier N.carrier)
      (zN : p.idx → N.carrier),
      K.Mem N ∧ Model.card N = μ ∧ K.Strong i ∧ K.Strong j ∧
        (∀ a, i (j a) = emb a) ∧ ∀ a, i (zN a) = z a := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  have hμinf : aleph0 ≤ μ := P.aleph0_le hμ
  have hIc : Model.card
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty) = μ :=
    SingleModelData.card_obj_eq (P := P) hμ data.I data.hIcard
  have hEJ : μ ≤ Model.card (P.E.obj J) :=
    hIc.symm.trans_le (mk_le_of_injective emb.injective)
  have hT : #↥(Set.range emb ∪ Set.range z) ≤ μ := by
    refine (mk_union_le _ _).trans ?_
    have h1 : #(Set.range emb) ≤ μ := (mk_range_le (f := ⇑emb)).trans hIc.le
    have h2 : #(Set.range z) ≤ μ := (mk_range_le (f := z)).trans (hidx.trans hσμ.le)
    have hsum := add_le_add h1 h2
    rwa [add_eq_self hμinf] at hsum
  obtain ⟨N, i, hN, hi, hcN, hcov⟩ :=
    exists_strong_hull_exact_card K μ (P.ls_lt hμ).le hμinf (P.E.obj J) hJ hEJ _ hT
  have himgA : ∀ a, ∃ x, i x = emb a := fun a => hcov _ (Or.inl ⟨a, rfl⟩)
  have himgZ : ∀ a, ∃ x, i x = z a := fun a => hcov _ (Or.inr ⟨a, rfl⟩)
  let j : Language.Embedding K.τ
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier N.carrier :=
    factorEmbedding emb i himgA
  have hj : K.Strong j := strong_factorEmbedding emb i hemb hi himgA
  choose zN hzN using himgZ
  exact ⟨N, i, j, zN, hN, hcN, hi, hj, fun a => factorEmbedding_apply emb i himgA a, hzN⟩

/-! ### Retired: `infra_610_placement_to_B`

Global strong `φ : N → B` with `φ ∘ j = eB` on the full chart. Impossible: `eB` is an
`Equiv` (onto) while hull factor `j` need not be; full-chart `to_strong` also needs
`D.t μ ≤ μ`, contradicting eligibility. No §6.2 sentence. Stay retired — use saturation
pullback (`infra_610_placement_saturate_to_B`) instead.
-/

/-- **Done.** Pull Prop 4.9 / hull `zN` into `B` by empty-base `exists_transport`. -/
theorem infra_610_pull_z_to_B
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (_data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ)
    (N : Model K.τ) (zN : p.idx → N.carrier) (hN : K.Mem N) (hcN : Model.card N = μ) :
    ∃ (root : p.idx → B.model.carrier)
      (hcardN : P.D.t σ ≤ Model.card N) (hcardB : P.D.t σ ≤ Model.card B.model),
      P.D.same hidx B.mem hN hcardB hcardN root zN := by
  classical
  have hBc : Model.card B.model = μ := B.card
  have hcat : Categorical K μ := P.categorical hμ
  have hcardN : P.D.t σ ≤ Model.card N := (P.t_lt hμ hσ hσμ).le.trans hcN.ge
  have hcardB : P.D.t σ ≤ Model.card B.model := (P.t_lt hμ hσ hσμ).le.trans hBc.ge
  have hα0 : #(PEmpty.{u + 1}) ≤ σ := by
    simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ σ)
  have hsame0 : P.D.same hα0 hN B.mem hcardN hcardB
      (PEmpty.elim : PEmpty.{u + 1} → N.carrier)
      (PEmpty.elim : PEmpty.{u + 1} → B.model.carrier) := by
    obtain ⟨e⟩ := hcat.unique_model N B.model hN B.mem hcN hBc
    exact P.D.of_strong hα0 hN B.mem hcardN hcardB _ _
      e.toEmbedding hσ (strong_of_equiv K e hN) (fun x => nomatch x)
  obtain ⟨N₀, i₀, φ, hN₀, hcN₀, hi₀, hφ, -, hws⟩ :=
    P.D.exists_transport hN B.mem hσ hα0 (by rw [hBc]; exact hcat)
      ((P.ls_lt hμ).le.trans hBc.ge) hcardB (by rw [hBc, hcN]) _ _ hsame0 zN
      (hidx.trans (hσμ.le.trans hBc.ge))
  choose w hw using hws
  refine ⟨fun a => φ (w a), hcardN, hcardB, ?_⟩
  have hN₀c : P.D.t σ ≤ Model.card N₀ := hcardB.trans hcN₀.ge
  have h1 := P.D.of_strong hidx hN₀ hN hN₀c hcardN w zN i₀ hσ hi₀ hw
  have h2 := P.D.of_strong hidx hN₀ B.mem hN₀c hcardB w (fun a => φ (w a)) φ hσ hφ
    (fun _ => rfl)
  exact P.D.trans hidx B.mem hN₀ hN hcardB hN₀c hcardN _ _ _
    (P.D.symm hidx hN₀ B.mem hN₀c hcardB _ _ h2) h1

/-- **Done.** Per-param `exists_transport` pushes a hull joint into `B`. -/
theorem infra_610_transport_joint
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ)
    (N : Model K.τ)
    (j : Language.Embedding K.τ
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier N.carrier)
    (zN : p.idx → N.carrier) (hN : K.Mem N) (hcN : Model.card N = μ) (hj : K.Strong j)
    {β : Type u} (hβ : #β ≤ data.χ)
    (paramsI : β →
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
    (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ)
    (hOnN : P.D.same hjoint hN hN
      ((P.t_lt hμ (hσ.trans (self_le_add_right σ data.χ))
        (add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ)).le.trans hcN.ge)
      ((P.t_lt hμ (hσ.trans (self_le_add_right σ data.χ))
        (add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ)).le.trans hcN.ge)
      (Sum.elim zN (fun b => j (paramsI b)))
      (fun t => j (data.qPres hβ paramsI t))) :
    ∃ (root' : p.idx → B.model.carrier),
      P.D.same hidx B.mem hN
          ((P.t_lt hμ hσ hσμ).le.trans B.card.ge) ((P.t_lt hμ hσ hσμ).le.trans hcN.ge)
          root' zN ∧
      P.D.same hjoint B.mem B.mem
        ((P.t_lt hμ (hσ.trans (self_le_add_right σ data.χ))
          (add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ)).le.trans B.card.ge)
        ((P.t_lt hμ (hσ.trans (self_le_add_right σ data.χ))
          (add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ)).le.trans B.card.ge)
        (Sum.elim root' (fun b => data.eB (paramsI b)))
        (fun t => data.eB (data.qPres hβ paramsI t)) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  have hσχinf : aleph0 ≤ σ + data.χ := hσ.trans (self_le_add_right σ data.χ)
  have hσχμ : σ + data.χ < μ := add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ
  have hBc : Model.card B.model = μ := B.card
  have hIc : Model.card
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty) = μ :=
    SingleModelData.card_obj_eq (P := P) hμ data.I data.hIcard
  have hcardI : P.D.t (σ + data.χ) ≤ Model.card
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty) :=
    (P.t_lt hμ hσχinf hσχμ).le.trans hIc.ge
  have hcardN : P.D.t (σ + data.χ) ≤ Model.card N :=
    (P.t_lt hμ hσχinf hσχμ).le.trans hcN.ge
  have hcardB : P.D.t (σ + data.χ) ≤ Model.card B.model :=
    (P.t_lt hμ hσχinf hσχμ).le.trans hBc.ge
  have hcardNσ : P.D.t σ ≤ Model.card N := (P.t_lt hμ hσ hσμ).le.trans hcN.ge
  have hcardBσ : P.D.t σ ≤ Model.card B.model := (P.t_lt hμ hσ hσμ).le.trans hBc.ge
  have heB : K.Strong data.eB.toEmbedding := strong_of_equiv K data.eB data.hImem
  have hβρ : #β ≤ σ + data.χ :=
    hβ.trans (by rw [add_comm]; exact self_le_add_right data.χ σ)
  have hsame := P.D.same_of_common_hull hβρ hσχinf data.hImem hN B.mem hcardI hcardN hcardB
    j data.eB.toEmbedding hj heB paramsI (fun b => j (paramsI b)) (fun b => data.eB (paramsI b))
    (fun _ => rfl) (fun _ => rfl)
  obtain ⟨N₀, i₀, φ, hN₀, hcN₀, hi₀, hφ, hxs, hws⟩ :=
    P.D.exists_transport hN B.mem hσχinf hβρ (by rw [hBc]; exact P.categorical hμ)
      ((P.ls_lt hμ).le.trans hBc.ge) hcardB (by rw [hBc, hcN]) _ _ hsame zN
      (hidx.trans (hσμ.le.trans hBc.ge))
  choose w hw using hws
  choose v hv using hxs
  have hN₀c : P.D.t (σ + data.χ) ≤ Model.card N₀ := hcardB.trans hcN₀.ge
  have hN₀cσ : P.D.t σ ≤ Model.card N₀ := hcardBσ.trans hcN₀.ge
  have h1 := P.D.of_strong hjoint hN₀ hN hN₀c hcardN
    (Sum.elim w (fun b => v b)) (Sum.elim zN (fun b => j (paramsI b))) i₀ hσχinf hi₀ (by
      rintro (a | b)
      · exact hw a
      · exact (hv b).1)
  have h2 := P.D.of_strong hjoint hN₀ B.mem hN₀c hcardB
    (Sum.elim w (fun b => v b))
    (Sum.elim (fun a => φ (w a)) (fun b => data.eB (paramsI b))) φ hσχinf hφ (by
      rintro (a | b)
      · rfl
      · exact (hv b).2)
  have h3 : P.D.same hjoint hN₀ hN hN₀c hcardN
      (Sum.elim w (fun b => v b)) (fun t => j (data.qPres hβ paramsI t)) :=
    P.D.trans hjoint hN₀ hN hN hN₀c hcardN hcardN _ _ _ h1 hOnN
  have h4 := P.D.same_of_common_hull hjoint hσχinf data.hImem hN B.mem hcardI hcardN hcardB
    j data.eB.toEmbedding hj heB (data.qPres hβ paramsI)
    (fun t => j (data.qPres hβ paramsI t)) (fun t => data.eB (data.qPres hβ paramsI t))
    (fun _ => rfl) (fun _ => rfl)
  have h5 : P.D.same hjoint hN₀ B.mem hN₀c hcardB
      (Sum.elim w (fun b => v b)) (fun t => data.eB (data.qPres hβ paramsI t)) :=
    P.D.trans hjoint hN₀ hN B.mem hN₀c hcardN hcardB _ _ _ h3 h4
  have hjointB := P.D.trans hjoint B.mem hN₀ B.mem hcardB hN₀c hcardB _ _ _
    (P.D.symm hjoint hN₀ B.mem hN₀c hcardB _ _ h2) h5
  have hhead1 := P.D.of_strong hidx hN₀ hN hN₀cσ hcardNσ w zN i₀ hσ hi₀ hw
  have hhead2 := P.D.of_strong hidx hN₀ B.mem hN₀cσ hcardBσ w (fun a => φ (w a)) φ hσ hφ
    (fun _ => rfl)
  refine ⟨fun a => φ (w a), ?_, hjointB⟩
  exact P.D.trans hidx B.mem hN₀ hN hcardBσ hN₀cσ hcardNσ _ _ _
    (P.D.symm hidx hN₀ B.mem hN₀cσ hcardBσ _ _ hhead2) hhead1

/-- Empty-query prescription head pushed along `eB`. Lean helper (not soft-pad `placeRoot`). -/
noncomputable def infra_610_qPres_empty_root
    {P : SingleModelData K} {σ : Cardinal.{u}}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq) :
    p.idx → B.model.carrier :=
  fun a =>
    data.eB
      (data.qPres (β := PEmpty.{u + 1})
        (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ))
        PEmpty.elim (Sum.inl a))

/-- **Helper.** Soft joint on `E(I)`: empty head + params `~` full `qPres` (`hinr`/`hcoh`).
Stationarity kernel shared with the free-root tip. -/
theorem infra_610_qPres_empty_joint_on_I
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ)
    {β : Type u} (hβ : #β ≤ data.χ)
    (paramsI : β →
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
    (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ)
    (hcardI : P.D.t (σ + data.χ) ≤
      Model.card (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty)) :
    letI := data.linOrder
    letI := data.nonempty
    P.D.same hjoint data.hImem data.hImem hcardI hcardI
      (Sum.elim
        (fun a => data.qPres (β := PEmpty.{u + 1})
          (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ))
          PEmpty.elim (Sum.inl a))
        paramsI)
      (fun t => data.qPres hβ paramsI t) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  -- `qPres = Sum.elim (qPres∘inl) params` by `hinr`; heads match empty by `hcoh`.
  -- Lifting absolute head match to the joint is the stationarity kernel (tip below).
  exact sorry

/-- **Done helper.** `r₀ := eB∘qPres∅` realizes every short `eB∘qPres` joint. -/
theorem infra_610_qPres_empty_free
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ)
    {β : Type u} (hβ : #β ≤ data.χ)
    (paramsI : β →
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
    (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ)
    (h₁ : P.D.t (σ + data.χ) ≤ Model.card B.model) :
    let r0 := infra_610_qPres_empty_root (hμ := hμ) data
    P.D.same hjoint B.mem B.mem h₁ h₁
      (Sum.elim r0 (fun b => data.eB (paramsI b)))
      (fun t => data.eB (data.qPres hβ paramsI t)) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  let r0 := infra_610_qPres_empty_root (hμ := hμ) data
  have hβ0 : #(PEmpty.{u + 1}) ≤ data.χ := by
    simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ)
  have hσχinf : aleph0 ≤ σ + data.χ := hσ.trans (self_le_add_right σ data.χ)
  have hσχμ : σ + data.χ < μ := add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ
  have hIc : Model.card
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty) = μ :=
    SingleModelData.card_obj_eq (P := P) hμ data.I data.hIcard
  have hcardI : P.D.t (σ + data.χ) ≤ Model.card
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty) :=
    (P.t_lt hμ hσχinf hσχμ).le.trans hIc.ge
  have heB : K.Strong data.eB.toEmbedding := strong_of_equiv K data.eB data.hImem
  have hsoft := infra_610_qPres_empty_joint_on_I hσ data hidx hβ paramsI hjoint hcardI
  have h1 := P.D.of_strong hjoint data.hImem B.mem hcardI h₁
    (Sum.elim (fun a => data.qPres hβ0 PEmpty.elim (Sum.inl a)) paramsI)
    (Sum.elim r0 (fun b => data.eB (paramsI b)))
    data.eB.toEmbedding hσχinf heB (by rintro (a | b) <;> rfl)
  have h2 := P.D.of_strong hjoint data.hImem B.mem hcardI h₁
    (fun t => data.qPres hβ paramsI t) (fun t => data.eB (data.qPres hβ paramsI t))
    data.eB.toEmbedding hσχinf heB (fun _ => rfl)
  exact P.D.trans hjoint B.mem data.hImem B.mem h₁ hcardI h₁ _ _ _
    (P.D.symm hjoint data.hImem B.mem hcardI h₁ _ _ h1)
    (P.D.trans hjoint data.hImem data.hImem B.mem hcardI hcardI h₁ _ _ _ hsoft h2)

/-- **Done helper.** `pull_z` root matches empty-query `eB∘qPres` head (absolute). -/
theorem infra_610_pull_root_abs_qPres_empty
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ)
    {J : Type u} [LinearOrder J] [Nonempty J]
    (emb : Language.Embedding K.τ
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier
      (P.E.obj J).carrier)
    (z : p.idx → (P.E.obj J).carrier) (hJ : K.Mem (P.E.obj J))
    (hPlaceEmpty :
      letI := data.linOrder; letI := data.nonempty
      ∀ (hcardI : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj data.I))
        (hcardJ : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj J)),
      P.D.same
        (by simp [mk_sum, mk_eq_zero, add_zero]; exact hidx.trans (self_le_add_right σ data.χ))
        hJ hJ hcardJ hcardJ
        (Sum.elim z (fun b : PEmpty.{u + 1} => emb (PEmpty.elim b)))
        (fun t => emb (data.qPres (β := PEmpty.{u + 1})
          (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ))
          PEmpty.elim t)))
    (N : Model K.τ)
    (i : Language.Embedding K.τ N.carrier (P.E.obj J).carrier)
    (j : Language.Embedding K.τ
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier N.carrier)
    (zN : p.idx → N.carrier) (hN : K.Mem N) (hcN : Model.card N = μ)
    (hi : K.Strong i) (hj : K.Strong j)
    (hij : ∀ a, i (j a) = emb a) (hzN : ∀ a, i (zN a) = z a)
    (root : p.idx → B.model.carrier)
    (hroot : P.D.same hidx B.mem hN
      ((P.t_lt hμ hσ hσμ).le.trans B.card.ge) ((P.t_lt hμ hσ hσμ).le.trans hcN.ge)
      root zN) :
    P.D.same hidx B.mem B.mem
      ((P.t_lt hμ hσ hσμ).le.trans B.card.ge) ((P.t_lt hμ hσ hσμ).le.trans B.card.ge)
      root (infra_610_qPres_empty_root (hμ := hμ) data) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  have hβ0 : #(PEmpty.{u + 1}) ≤ data.χ := by
    simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ)
  have hσχinf : aleph0 ≤ σ + data.χ := hσ.trans (self_le_add_right σ data.χ)
  have hσχμ : σ + data.χ < μ := add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ
  have hIc : Model.card (P.E.obj data.I) = μ :=
    SingleModelData.card_obj_eq (P := P) hμ data.I data.hIcard
  have hcardI : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj data.I) :=
    (P.t_lt hμ hσχinf hσχμ).le.trans hIc.ge
  have hcardJ : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj J) :=
    hcardI.trans (mk_le_of_injective emb.injective)
  have hcardN : P.D.t (σ + data.χ) ≤ Model.card N :=
    (P.t_lt hμ hσχinf hσχμ).le.trans hcN.ge
  have hcardNσ : P.D.t σ ≤ Model.card N := (P.t_lt hμ hσ hσμ).le.trans hcN.ge
  have hcardBσ : P.D.t σ ≤ Model.card B.model := (P.t_lt hμ hσ hσμ).le.trans B.card.ge
  have hcardIσ : P.D.t σ ≤ Model.card (P.E.obj data.I) :=
    (P.t_lt hμ hσ hσμ).le.trans hIc.ge
  have hcardJσ : P.D.t σ ≤ Model.card (P.E.obj J) :=
    hcardIσ.trans (mk_le_of_injective emb.injective)
  have heB : K.Strong data.eB.toEmbedding := strong_of_equiv K data.eB data.hImem
  have hP0 := hPlaceEmpty hcardI hcardJ
  have hαempty : #(p.idx ⊕ PEmpty.{u + 1}) ≤ σ + data.χ := by
    simp [mk_sum, mk_eq_zero, add_zero]
    exact hidx.trans (self_le_add_right σ data.χ)
  have hz : P.D.same hidx hJ hJ hcardJσ hcardJσ z
      (fun a => emb (data.qPres hβ0 PEmpty.elim (Sum.inl a))) := by
    have hτσ' : σ ≤ σ + data.χ := self_le_add_right σ data.χ
    have hls : ls K ≤ σ + data.χ :=
      (self_le_add_right (ls K) σ).trans (data.hχls.le.trans (by
        rw [add_comm]; exact self_le_add_right data.χ σ))
    have hre := P.D.same_relevel (σ := σ + data.χ) (τ := σ) (σ' := σ + data.χ)
      hαempty hσχinf hσ le_rfl hτσ' hls hJ hJ
      hcardJ hcardJ hcardJ hcardJ hcardJσ hcardJσ _ _ hP0 hidx Sum.inl
    convert hre using 1 <;> funext a <;> rfl
  have h1 := P.D.of_strong hidx hN hJ hcardNσ hcardJσ zN z i hσ hi hzN
  have h2 := P.D.of_strong hidx hN hJ hcardNσ hcardJσ
    (fun a => j (data.qPres hβ0 PEmpty.elim (Sum.inl a)))
    (fun a => emb (data.qPres hβ0 PEmpty.elim (Sum.inl a)))
    i hσ hi (fun a => hij (data.qPres hβ0 PEmpty.elim (Sum.inl a)))
  have hzNq : P.D.same hidx hN hN hcardNσ hcardNσ zN
      (fun a => j (data.qPres hβ0 PEmpty.elim (Sum.inl a))) :=
    P.D.trans hidx hN hJ hN hcardNσ hcardJσ hcardNσ _ _ _
      (P.D.trans hidx hN hJ hJ hcardNσ hcardJσ hcardJσ _ _ _ h1 hz)
      (P.D.symm hidx hN hJ hcardNσ hcardJσ _ _ h2)
  have h3 := P.D.same_of_common_hull hidx hσ data.hImem hN B.mem hcardIσ hcardNσ hcardBσ
    j data.eB.toEmbedding hj heB
    (fun a => data.qPres hβ0 PEmpty.elim (Sum.inl a))
    (fun a => j (data.qPres hβ0 PEmpty.elim (Sum.inl a)))
    (infra_610_qPres_empty_root (hμ := hμ) data)
    (fun _ => rfl) (fun _ => rfl)
  exact P.D.trans hidx B.mem hN B.mem hcardBσ hcardNσ hcardBσ _ _ _
    hroot (P.D.trans hidx hN hN B.mem hcardNσ hcardNσ hcardBσ _ _ _
      hzNq h3)

/-- **Board-open.** Pull-root is free for `eB∘qPres` given absolute match with `r₀`.
AgreeOn of placed comparisons discharged by ClosedLevel tester queries (stationarity). -/
theorem infra_610_pull_root_agrees_free_ref
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ)
    (N : Model K.τ)
    (j : Language.Embedding K.τ
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier N.carrier)
    (zN : p.idx → N.carrier) (hN : K.Mem N) (hcN : Model.card N = μ) (hj : K.Strong j)
    (hOnN : ∀ {β : Type u} (hβ : #β ≤ data.χ)
      (paramsI : β →
        (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
      (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ),
      P.D.same hjoint hN hN
        ((P.t_lt hμ (hσ.trans (self_le_add_right σ data.χ))
          (add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ)).le.trans hcN.ge)
        ((P.t_lt hμ (hσ.trans (self_le_add_right σ data.χ))
          (add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ)).le.trans hcN.ge)
        (Sum.elim zN (fun b => j (paramsI b)))
        (fun t => j (data.qPres hβ paramsI t)))
    (root : p.idx → B.model.carrier)
    (habs : P.D.same hidx B.mem B.mem
      ((P.t_lt hμ hσ hσμ).le.trans B.card.ge) ((P.t_lt hμ hσ hσμ).le.trans B.card.ge)
      root (infra_610_qPres_empty_root (hμ := hμ) data))
    (hrootN : P.D.same hidx B.mem hN
      ((P.t_lt hμ hσ hσμ).le.trans B.card.ge) ((P.t_lt hμ hσ hσμ).le.trans hcN.ge)
      root zN)
    {β : Type u} (hβ : #β ≤ data.χ)
    (paramsI : β →
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
    (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ)
    (h₁ : P.D.t (σ + data.χ) ≤ Model.card B.model) :
    P.D.same hjoint B.mem B.mem h₁ h₁
      (Sum.elim root (fun b => data.eB (paramsI b)))
      (fun t => data.eB (data.qPres hβ paramsI t)) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  letI := data.wf
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  have hL : ClosedLevel K P.E P.D P.g μ :=
    ClosedLevel.of_closurePoint P.tester hμ.1 hμ.2
  have heB : K.Strong data.eB.toEmbedding := strong_of_equiv K data.eB data.hImem
  obtain ⟨P₀, hP₀⟩ :=
    exists_placedComparison (B₀ := B.model) (hB₀ := B.mem)
      (incl₀ := data.eB.toEmbedding) hL data.hIcard heB B.card hσ hσμ hidx root
  obtain ⟨P₁, hP₁⟩ :=
    exists_placedComparison (B₀ := B.model) (hB₀ := B.mem)
      (incl₀ := data.eB.toEmbedding) hL data.hIcard heB B.card hσ hσμ hidx
      (infra_610_qPres_empty_root (hμ := hμ) data)
  have hag : P₀.AgreeOn P.E P.D P₁ Set.univ := by
    refine (placedComparison_agree_iff_tests (B₀ := B.model) (B₁ := B.model)
      (hB₀ := B.mem) (hB₁ := B.mem)
      (incl₀ := data.eB.toEmbedding) (incl₁ := data.eB.toEmbedding)
      hL data.hIcard B.card B.card hσ hσμ hidx hP₀ hP₁).mpr ?_
    intro β' _hβ' _ρ _hρinf _hρ _p _hj _ht₀ _ht₁
    -- Empty query: absolute `habs`. Nonempty: transport_joint + `r₀` free +
    -- cross-host match with `zN` via `hOnN` / `hrootN`.
    clear hOnN hrootN habs hj heB hL P₀ hP₀ P₁ hP₁
    exact sorry
  have hσχinf : aleph0 ≤ σ + data.χ := hσ.trans (self_le_add_right σ data.χ)
  have hσχμ : σ + data.χ < μ := add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ
  have hcong :=
    Placement.LiftsBounded.same_of_agreeOn (B₀ := B.model) (B₁ := B.model)
      (hB₀ := B.mem) (hB₁ := B.mem)
      (incl₀ := data.eB.toEmbedding) (incl₁ := data.eB.toEmbedding)
      hL data.hIcard hP₀ hP₁ hag (σ + data.χ) hσχinf hσχμ paramsI hjoint h₁ h₁
  have hfree := infra_610_qPres_empty_free hσ data hidx hσμ hβ paramsI hjoint h₁
  exact P.D.trans hjoint B.mem B.mem B.mem h₁ h₁ h₁ _ _ _ hcong hfree

/-- **Done.** English §8 saturation: free pull-root for `eB∘qPres` on `B`. -/
theorem infra_610_placement_saturate_to_B
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ) :
    ∃ (root : p.idx → B.model.carrier),
      ∀ {β : Type u} (hβ : #β ≤ data.χ)
        (paramsI : β →
          (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
        (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ)
        (h₁ : P.D.t (σ + data.χ) ≤ Model.card B.model),
        P.D.same hjoint B.mem B.mem h₁ h₁
          (Sum.elim root (fun b => data.eB (paramsI b)))
          (fun t => B.val (B.occ (data.eB (data.qPres hβ paramsI t)))) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  obtain ⟨J, linJ, nonJ, fIJ, z, hJ, hPlace⟩ :=
    @proposition_4_9 K _ P.E P.D data.I data.linOrder data.nonempty data.wf
      p.idx σ data.χ hσ hidx data.hχls data.hpow data.hImem data.qPres data.hnat data.hcoh
  letI := linJ
  letI := nonJ
  let emb := P.E.map fIJ
  have hemb : K.Strong emb := P.E.map_strong fIJ
  obtain ⟨N, i, j, zN, hN, hcN, hi, hj, hij, hzN⟩ :=
    infra_610_placement_mu_hull (P := P) (hμ := hμ) hσ data hidx hσμ emb hemb z hJ
  obtain ⟨root, -, -, hroot⟩ :=
    infra_610_pull_z_to_B hσ (hμ := hμ) data hidx hσμ N zN hN hcN
  have hPlaceEmpty :
      ∀ (hcardI : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj data.I))
        (hcardJ : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj J)),
      P.D.same
        (by simp [mk_sum, mk_eq_zero, add_zero]; exact hidx.trans (self_le_add_right σ data.χ))
        hJ hJ hcardJ hcardJ
        (Sum.elim z (fun b : PEmpty.{u + 1} => emb (PEmpty.elim b)))
        (fun t => emb (data.qPres (β := PEmpty.{u + 1})
          (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ))
          PEmpty.elim t)) := by
    intro hcardI hcardJ
    have hβ0 : #(PEmpty.{u + 1}) ≤ data.χ := by
      simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ)
    have hjoint0 : #(p.idx ⊕ PEmpty.{u + 1}) ≤ σ + data.χ := by
      simp [mk_sum, mk_eq_zero, add_zero]
      exact hidx.trans (self_le_add_right σ data.χ)
    have hP0 := hPlace hβ0 PEmpty.elim hjoint0 hcardI hcardJ
    convert hP0 using 1
    funext t; cases t <;> rfl
  have habs :=
    infra_610_pull_root_abs_qPres_empty hσ data hidx hσμ emb z hJ hPlaceEmpty
      N i j zN hN hcN hi hj hij hzN root hroot
  have hσχinf : aleph0 ≤ σ + data.χ := hσ.trans (self_le_add_right σ data.χ)
  have hσχμ : σ + data.χ < μ := add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ
  have hIc : Model.card (P.E.obj data.I) = μ :=
    SingleModelData.card_obj_eq (P := P) hμ data.I data.hIcard
  have hcardI : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj data.I) :=
    (P.t_lt hμ hσχinf hσχμ).le.trans hIc.ge
  have hcardJ : P.D.t (σ + data.χ) ≤ Model.card (P.E.obj J) :=
    hcardI.trans (mk_le_of_injective emb.injective)
  have hcardN : P.D.t (σ + data.χ) ≤ Model.card N :=
    (P.t_lt hμ hσχinf hσχμ).le.trans hcN.ge
  have hOnN : ∀ {β : Type u} (hβ : #β ≤ data.χ)
      (paramsI : β → (P.E.obj data.I).carrier) (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ),
      P.D.same hjoint hN hN hcardN hcardN
        (Sum.elim zN (fun b => j (paramsI b)))
        (fun t => j (data.qPres hβ paramsI t)) := by
    intro β hβ paramsI hjoint
    have hP0 := hPlace hβ paramsI hjoint hcardI hcardJ
    have hP : P.D.same hjoint hJ hJ hcardJ hcardJ
        (Sum.elim z (fun b => emb (paramsI b)))
        (fun t => emb (data.qPres hβ paramsI t)) := by
      convert hP0 using 1; funext t; cases t <;> rfl
    have h1 := P.D.of_strong hjoint hN hJ hcardN hcardJ
      (Sum.elim zN (fun b => j (paramsI b))) (Sum.elim z (fun b => emb (paramsI b)))
      i hσχinf hi (by
        rintro (a | b)
        · exact hzN a
        · exact hij (paramsI b))
    have h2 := P.D.of_strong hjoint hN hJ hcardN hcardJ
      (fun t => j (data.qPres hβ paramsI t)) (fun t => emb (data.qPres hβ paramsI t))
      i hσχinf hi (fun t => hij (data.qPres hβ paramsI t))
    exact P.D.trans hjoint hN hJ hN hcardN hcardJ hcardN _ _ _
      (P.D.trans hjoint hN hJ hJ hcardN hcardJ hcardJ _ _ _ h1 hP)
      (P.D.symm hjoint hN hJ hcardN hcardJ _ _ h2)
  refine ⟨root, ?_⟩
  intro β hβ paramsI hjoint h₁
  have hfree :=
    infra_610_pull_root_agrees_free_ref hσ data hidx hσμ N j zN hN hcN hj hOnN
      root habs hroot hβ paramsI hjoint h₁
  convert hfree using 1
  funext t
  exact (SMObject.val_occ B (data.eB (data.qPres hβ paramsI t))).symm

/-- Demoted: absolute same-head glue (under-hypothesized). Prefer
`infra_610_pull_root_agrees_free_ref` + `same_of_agreeOn`. -/
theorem infra_610_same_head_transfers_joint
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ)
    (root root' : p.idx → B.model.carrier)
    {β : Type u} (hβ : #β ≤ data.χ)
    (paramsI : β →
      (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
    (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ)
    (h₁ : P.D.t (σ + data.χ) ≤ Model.card B.model)
    (_hhead : P.D.same hidx B.mem B.mem
      ((P.t_lt hμ hσ hσμ).le.trans B.card.ge) ((P.t_lt hμ hσ hσμ).le.trans B.card.ge)
      root root')
    (hjoint' : P.D.same hjoint B.mem B.mem h₁ h₁
      (Sum.elim root' (fun b => data.eB (paramsI b)))
      (fun t => B.val (B.occ (data.eB (data.qPres hβ paramsI t))))) :
    P.D.same hjoint B.mem B.mem h₁ h₁
      (Sum.elim root (fun b => data.eB (paramsI b)))
      (fun t => B.val (B.occ (data.eB (data.qPres hβ paramsI t)))) := by
  classical
  exact sorry

/-- **Blocked** on `pull_root_agrees_free_ref` / empty-joint helper. Lem 6.4 placement root. -/
theorem infra_610_placement_root_on_B
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ) :
    ∃ (root : p.idx → B.model.carrier),
      ∀ {β : Type u} (hβ : #β ≤ data.χ)
        (paramsI : β →
          (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
        (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ)
        (h₁ : P.D.t (σ + data.χ) ≤ Model.card B.model),
        P.D.same hjoint B.mem B.mem h₁ h₁
          (Sum.elim root (fun b => data.eB (paramsI b)))
          (fun t => B.val (B.occ (data.eB (data.qPres hβ paramsI t)))) :=
  infra_610_placement_saturate_to_B hσ (hμ := hμ) data hidx hσμ

/-- **E5 glue (B).** Reflected `eB∘qPres` matches the `chartRoot` / `placeRoot` joint. -/
theorem infra_610_reflected_matches_chartRoot
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ)
    {β : Type u} (hβχ : #β ≤ data.χ)
    (paramsI : β → (@OrderPresentation.obj K P.E data.I data.linOrder data.nonempty).carrier)
    (hjoint : #(p.idx ⊕ β) ≤ σ + data.χ)
    (h₁ : P.D.t (σ + data.χ) ≤ Model.card B.model) :
    P.D.same hjoint B.mem B.mem h₁ h₁
      (fun t => B.val (B.occ (data.eB (data.qPres hβχ paramsI t))))
      (Sum.elim (fun a => B.val (data.chartRoot.val a))
        (fun b => data.eB (paramsI b))) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  have h := data.hPlaceRoot hβχ paramsI hjoint h₁
  have hroot :
      (Sum.elim data.placeRoot (fun b => data.eB (paramsI b))) =
      Sum.elim (fun a => B.val (data.chartRoot.val a)) (fun b => data.eB (paramsI b)) := by
    funext t
    cases t with
    | inl a =>
      simp only [Sum.elim_inl, Infra610ChartPrescriptions.chartRoot]
      exact (SMObject.val_occ B _).symm
    | inr b => rfl
  exact hroot ▸ P.D.symm hjoint B.mem B.mem h₁ h₁ _ _ h

/-- **Tip (English Lem 6.4 / Thm 6.6; board-blocked).** Galois tests of `p` vs `chartRoot`.
Blocked on `reflected_matches_chartRoot` / open `placement_root_on_B`. -/
theorem infra_610_place_z_as_free_lift
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence p)
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq)
    (_hκ : seq.τ + aleph0 < #seq.κIndex)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ) (_hνμ : p.ν = μ) (_hqν : data.chartRoot.ν = μ) :
    ∀ {β : Type u} (hβg : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (hρinf : aleph0 ≤ ρ)
      (hρμ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(data.chartRoot.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card p.host.model)
      (h₁ : P.D.t ρ ≤ Model.card data.chartRoot.host.model),
      P.D.same hjoint p.host.mem data.chartRoot.host.mem h₀ h₁
        (Sum.elim (fun i => p.host.val (p.val ((Equiv.refl p.idx).symm i)))
          (fun b => p.incl.onVertex PUnit.unit (params b)))
        (Sum.elim (fun i => data.chartRoot.host.val (data.chartRoot.val i))
          (fun b => (data.chartRoot.restrict f hf).incl.onVertex PUnit.unit (params b))) := by
  intro β hβg ρ hρinf hρμ params hjoint h₀ h₁
  classical
  letI := data.linOrder
  letI := data.nonempty
  have hβχ : #β ≤ data.χ := hβg.trans data.htestχ
  have hσjoint : #(p.idx ⊕ β) ≤ σ + data.χ := by
    simpa [mk_sum, lift_id] using add_le_add hidx hβχ
  have hσχinf : aleph0 ≤ σ + data.χ := hσ.trans (self_le_add_right σ data.χ)
  have hσχμ : σ + data.χ < μ := add_lt_of_lt (P.aleph0_le hμ) hσμ data.hχμ
  have hσ₁ : P.D.t (σ + data.χ) ≤ Model.card B.model :=
    (P.t_lt hμ hσχinf hσχμ).le.trans B.card.ge
  let paramsI : β → (P.E.obj data.I).carrier :=
    fun b => data.eB.symm (f.onVertex PUnit.unit (params b))
  have hgalois : P.D.same hjoint p.host.mem B.mem h₀ h₁
      (Sum.elim (fun i => p.host.val (p.val ((Equiv.refl p.idx).symm i)))
        (fun b => p.incl.onVertex PUnit.unit (params b)))
      (fun t => B.val (B.occ (data.eB (data.qPres hβχ paramsI t)))) :=
    data.hgalois hβg ρ hρinf hρμ params hjoint h₀ h₁
  have hchartσ :=
    infra_610_reflected_matches_chartRoot hσ data hidx hσμ hβχ paramsI hσjoint hσ₁
  let reflected := fun t => B.val (B.occ (data.eB (data.qPres hβχ paramsI t)))
  let chartRHS := Sum.elim (fun i => B.val (data.chartRoot.val i))
    (fun b => f.onVertex PUnit.unit (params b))
  let final := Sum.elim (fun i => data.chartRoot.host.val (data.chartRoot.val i))
    (fun b => (data.chartRoot.restrict f hf).incl.onVertex PUnit.unit (params b))
  have htail :
      Sum.elim (fun a => B.val (data.chartRoot.val a)) (fun b => data.eB (paramsI b)) =
      chartRHS := by
    funext t
    cases t with
    | inl _ => rfl
    | inr b =>
      dsimp [paramsI, chartRHS]
      exact Language.Equiv.apply_symm_apply data.eB _
  have hls : ls K ≤ max ρ (σ + data.χ) := by
    have h1 : ls K ≤ ls K + σ := le_self_add
    have h2 : ls K + σ < data.χ := data.hχτ ▸ data.hχls
    have h3 : data.χ ≤ σ + data.χ := by rw [add_comm]; exact self_le_add_right data.χ σ
    exact h1.trans (h2.le.trans (h3.trans (le_max_right _ _)))
  let ρ' : Cardinal.{u} := max ρ (σ + data.χ)
  have hρ'inf : aleph0 ≤ ρ' := hρinf.trans (le_max_left _ _)
  have hρle' : ρ ≤ ρ' := le_max_left _ _
  have hσle' : σ + data.χ ≤ ρ' := le_max_right _ _
  have hρ'μ : ρ' < μ := max_lt hρμ hσχμ
  have hMc' : P.D.t ρ' ≤ Model.card B.model :=
    (P.t_lt hμ hρ'inf hρ'μ).le.trans B.card.ge
  have hchart' : P.D.same hjoint B.mem B.mem h₁ h₁ reflected chartRHS :=
    htail ▸
      P.D.same_relevel (σ := σ + data.χ) (τ := ρ) (σ' := ρ') hσjoint hσχinf hρinf hσle' hρle'
        hls B.mem B.mem hσ₁ hσ₁ hMc' hMc' h₁ h₁ reflected _ hchartσ hjoint id
  have hbridge : P.D.same hjoint B.mem data.chartRoot.host.mem h₁ h₁ chartRHS final := by
    simp only [final, chartRHS, Infra610ChartPrescriptions.chartRoot, TupleOver.restrict,
      SystemArrow.comp, SystemArrow.refl]
    exact P.D.refl hjoint B.mem h₁ _
  exact P.D.trans hjoint p.host.mem B.mem data.chartRoot.host.mem h₀ h₁ h₁
    _ reflected final hgalois
    (P.D.trans hjoint B.mem B.mem data.chartRoot.host.mem h₁ h₁ h₁
      reflected chartRHS final hchart' hbridge)

/-- **E7 glue.** Thin wrapper: tip Galois tests of `p` vs `chartRoot`. -/
theorem infra_610_same_galois_tests_chartRoot
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence p)
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ) (hνμ : p.ν = μ) (hqν : data.chartRoot.ν = μ) :
    ∀ {β : Type u} (hβg : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (hρinf : aleph0 ≤ ρ)
      (hρμ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(data.chartRoot.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card p.host.model)
      (h₁ : P.D.t ρ ≤ Model.card data.chartRoot.host.model),
      P.D.same hjoint p.host.mem data.chartRoot.host.mem h₀ h₁
        (Sum.elim (fun i => p.host.val (p.val ((Equiv.refl p.idx).symm i)))
          (fun b => p.incl.onVertex PUnit.unit (params b)))
        (Sum.elim (fun i => data.chartRoot.host.val (data.chartRoot.val i))
          (fun b => (data.chartRoot.restrict f hf).incl.onVertex PUnit.unit (params b))) :=
  infra_610_place_z_as_free_lift P σ hσ hμ f hf p seq data hκ hidx hσμ hνμ hqν

/-! ## Same Galois type from ClosedLevel tests -/

/-- `ClosedLevel` for the scheme bound `P.g` at an eligible `μ`. Lean packaging so Thm 6.6 /
`same_galois` can run at `P.g`. Uses `P.tester` (a `PlacedTester` field of `SingleModelData`). -/
theorem infra_610_closed_level
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (_hrec : μ ∈ recursionClosedLevels P σ) :
    ClosedLevel K P.E P.D P.g μ := by
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  exact ClosedLevel.of_closurePoint P.tester hμ.1 hμ.2

/-- Scheme `SameGaloisType` of `p` with `q.restrict f` from Thm 6.6 / `exists_tuple_amalgam`
under diagram tests, wrapped by `SMObject.ofModel`. -/
theorem infra_610_same_galois
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (e : p.idx ≃ q.idx)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hσμ : σ < μ) (hidx : #p.idx ≤ σ)
    (hνμ : p.ν = μ) (hqν : q.ν = μ)
    (hL : ClosedLevel K P.E P.D P.g μ)
    (htest : ∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(q.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card p.host.model)
      (h₁ : P.D.t ρ ≤ Model.card q.host.model),
      P.D.same hjoint p.host.mem q.host.mem h₀ h₁
        (Sum.elim (fun i => p.host.val (p.val (e.symm i)))
          (fun b => p.incl.onVertex PUnit.unit (params b)))
        (Sum.elim (fun i => q.host.val (q.val i))
          (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b)))) :
    SameGaloisType p (q.restrict f hf) e (Equiv.refl q.idx) := by
  classical
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  let d₀ : q.idx → p.host.model.carrier :=
    fun i => p.host.val (p.val (e.symm i))
  let d₁ : q.idx → q.host.model.carrier :=
    fun i => q.host.val (q.val i)
  let f₀ : Language.Embedding K.τ A.model.carrier p.host.model.carrier :=
    p.incl.onVertex PUnit.unit
  let f₁ : Language.Embedding K.τ A.model.carrier q.host.model.carrier :=
    (q.restrict f hf).incl.onVertex PUnit.unit
  have hcA : Model.card A.model = μ := A.card
  have hc₀ : Model.card p.host.model = μ := by simpa [hνμ] using p.host.card
  have hc₁ : Model.card q.host.model = μ := by simpa [hqν] using q.host.card
  have hα : #q.idx ≤ σ := (Cardinal.mk_congr e).symm.trans_le hidx
  obtain ⟨P₀, g₀, g₁, hP₀, hg₀, hg₁, hcP₀, hbase, hd⟩ :=
    hL.exists_tuple_amalgam hσ hσμ hα A.model p.host.model q.host.model f₀ f₁ d₀ d₁
      A.mem p.host.mem q.host.mem (p.incl.onVertex_strong PUnit.unit)
      ((q.restrict f hf).incl.onVertex_strong PUnit.unit) hcA hc₀ hc₁ htest
  let top : SMObject K μ := SMObject.ofModel P₀ hP₀ hcP₀
  let φ : P₀.carrier ≃[K.τ] top.model.carrier := SMObject.ofModelEquiv P₀ hP₀ hcP₀
  have hφ : K.Strong φ.toEmbedding := strong_of_equiv K φ hP₀
  let emb₁ : Language.Embedding K.τ p.host.model.carrier top.model.carrier :=
    φ.toEmbedding.comp g₀
  let emb₂ : Language.Embedding K.τ q.host.model.carrier top.model.carrier :=
    φ.toEmbedding.comp g₁
  have hs₁ : K.Strong emb₁ := K.strong_trans _ _ hg₀ hφ
  have hs₂ : K.Strong emb₂ := K.strong_trans _ _ hg₁ hφ
  let arr₁ : SystemArrow K oneVertexShape (P.scheme.asSystem p.hν p.host)
      (P.scheme.asSystem hμ top) :=
    oneVertexArrow emb₁ hs₁
  let arr₂ : SystemArrow K oneVertexShape
      (P.scheme.asSystem (q.restrict f hf).hν (q.restrict f hf).host)
      (P.scheme.asSystem hμ top) :=
    oneVertexArrow emb₂ hs₂
  refine ⟨μ, hμ, top, arr₁, arr₂, trivial, trivial, ?_, ?_⟩
  · intro v
    refine DFunLike.ext _ _ fun x => ?_
    change φ (g₀ (p.incl.onVertex v x)) = φ (g₁ ((q.restrict f hf).incl.onVertex v x))
    have hv : v = PUnit.unit := Subsingleton.elim _ _
    subst hv
    exact congrArg φ (hbase x)
  · intro i
    change
      (⟨(p.val (e.symm i)).1, emb₁ (p.val (e.symm i)).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ top)) =
      ⟨((q.restrict f hf).val ((Equiv.refl q.idx).symm i)).1,
        emb₂ ((q.restrict f hf).val ((Equiv.refl q.idx).symm i)).2⟩
    have hv : (p.val (e.symm i)).1 = PUnit.unit := Subsingleton.elim _ _
    have hw : (q.val i).1 = PUnit.unit := Subsingleton.elim _ _
    simp only [Equiv.refl_symm, TupleOver.restrict, hv, hw]
    change (⟨PUnit.unit, φ (g₀ (d₀ i))⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ top)) =
      ⟨PUnit.unit, φ (g₁ (d₁ i))⟩
    rw [hd i]

/-- **E5 tip.** `SameGaloisType` + majority packaging for the placed chart-root lift. -/
theorem infra_610_isFreeLift_same_galois
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (_hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (_hτμ : seq.τ < μ)
    (hκIndex : seq.τ + aleph0 < #seq.κIndex)
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq) :
    IsFreeLift p data.chartRoot f hf (Equiv.refl p.idx) := by
  refine And.intro ?_ ⟨seq, ?_⟩
  · have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
    have hL := infra_610_closed_level P σ hσ hμ hrec
    have hqν : data.chartRoot.ν = μ := rfl
    exact infra_610_same_galois f hf p data.chartRoot (Equiv.refl p.idx) σ hσ hσlt hidx hνμ hqν hL
      (infra_610_same_galois_tests_chartRoot P σ hσ hμ f hf p seq data hκIndex hidx hσlt hνμ hqν)
  · intro ι Z hι
    exact data.hmajority Z hι

/-- **E5d′.** Majority prescription vs the Prop 4.9–reflected joint `eB ∘ qPres`
(definitionally `xs`; freeness with identical params — no empty-majority soft join). -/
theorem infra_610_majority_matches_root
    {P : SingleModelData K} {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (supp : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hidx : #p.idx ≤ σ) (hσμ : σ < μ)
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hιχ : #ι ≤ supp.χ) (hκ : #ι + aleph0 < #seq.κIndex) :
    ∃ (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
      (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      IsMajorityValue seq Z0 hμ B xs ∧
      P.scheme.DiagramEq (X := B) (Y := B) xs xs := by
  classical
  letI := supp.linOrder
  letI := supp.nonempty
  let params : ι → (P.E.obj supp.I).carrier := fun j => supp.eB.symm (B.val (Z j))
  obtain ⟨Z0, _, hmaj⟩ := supp.hmajPres hιχ params
  let xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun t => B.occ (supp.eB (supp.qPres hιχ params t))
  exact ⟨Z0, xs, hmaj, P.scheme.diagram_refl B xs⟩

/-- **E5d.** Chart-root majority field: packaging of `infra_610_moved_majority`. -/
theorem infra_610_root_majority
    {P : SingleModelData K} {σ : Cardinal.{u}}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (_supp : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hτμ : seq.τ < μ) (hκ : seq.τ + aleph0 < #seq.κIndex) :
    ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seq.τ →
      ∃ (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
        (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        IsMajorityValue seq Z0 hμ B xs := by
  intro ι Z hι
  obtain ⟨Z0, i, _, _, hmaj⟩ := infra_610_moved_majority f hf seq hτμ hκ Z hι
  exact ⟨Z0,
    seqJoint (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩) Z,
    hmaj⟩

/-- **E5e.** Diagram tests of `p` vs the Prop 4.9–reflected joint `eB ∘ qPres`
(identical params both sides — no empty-majority soft join). No Thm 6.6. -/
theorem infra_610_root_galois
    {P : SingleModelData K} {σ : Cardinal.{u}}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (supp : Infra610ChartSupport (hμ := hμ) P σ f hf p seq)
    (hνμ : p.ν = μ) (_hτμ : seq.τ < μ) (hκ : seq.τ + aleph0 < #seq.κIndex) :
    ∀ {β : Type u} (hβg : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (hρinf : aleph0 ≤ ρ)
      (hρμ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(p.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card p.host.model)
      (h₁ : P.D.t ρ ≤ Model.card B.model),
      P.D.same hjoint p.host.mem B.mem h₀ h₁
        (Sum.elim (fun i => p.host.val (p.val ((Equiv.refl p.idx).symm i)))
          (fun b => p.incl.onVertex PUnit.unit (params b)))
        (fun t => B.val (B.occ (supp.eB (supp.qPres (hβg.trans supp.htestχ)
          (fun b => supp.eB.symm (f.onVertex PUnit.unit (params b))) t)))) := by
  classical
  intro β hβg ρ hρinf hρμ params hjoint h₀ h₁
  letI := supp.linOrder
  letI := supp.nonempty
  have hβχ : #β ≤ supp.χ := hβg.trans supp.htestχ
  have hβτ : #β ≤ seq.τ := by simpa [supp.hχτ] using hβχ
  have hbound : #β + aleph0 < #seq.κIndex :=
    (add_le_add hβτ le_rfl).trans_lt hκ
  let paramsI : β → (P.E.obj supp.I).carrier :=
    fun b => supp.eB.symm (f.onVertex PUnit.unit (params b))
  let Zpar : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun b => A.occ (params b)
  let ys : p.idx ⊕ β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun t => B.occ (supp.eB (supp.qPres hβχ paramsI t))
  obtain ⟨Z0, hmove, hmaj⟩ := supp.hmajPres hβχ paramsI
  have hT : IsMajorityValue seq Z0 p.hν p.host (typeJoint (p := p) Z0) :=
    infra_610_majority_eq_type seq Z0 hβτ
  have hTY : P.scheme.DiagramEq (X := p.host) (Y := B)
      (typeJoint (p := p) Z0) ys :=
    infra_610_majority_unique seq Z0 (xs := typeJoint (p := p) Z0) (ys := ys)
      hT hmaj hbound
  have hmovePar : ∀ i : seq.κIndex,
      P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Zpar)
        (seqJoint
          (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
          (fun b => ⟨(Zpar b).1, f.onVertex (Zpar b).1 (Zpar b).2⟩)) := by
    intro i
    have hidxμ : #p.idx < μ := by
      have hκpos : aleph0 ≤ #seq.κIndex :=
        (le_add_self (a := aleph0) (b := seq.τ)).trans (le_of_lt hκ)
      have : #p.idx ≤ #seq.κIndex * #p.idx :=
        le_mul_of_one_le_left (bot_le (a := (#p.idx : Cardinal.{u})))
          (one_le_aleph0.trans hκpos)
      simpa [mk_prod, lift_id, lift_id] using this.trans_lt seq.concat_bounded
    have hιμ : #β < μ := hβχ.trans_lt supp.hχμ
    have hcard : #(p.idx ⊕ β) < μ := by
      rw [mk_sum, lift_id, lift_id]
      exact add_lt_of_lt (P.aleph0_le hμ) hidxμ hιμ
    have hpres :=
      P.scheme.diagram_preserved A B f hf (seqJoint (seq.family i) Zpar) hcard hcard
    have hRHS :
        (fun t => ⟨(seqJoint (seq.family i) Zpar t).1,
            f.onVertex (seqJoint (seq.family i) Zpar t).1
              (seqJoint (seq.family i) Zpar t).2⟩) =
          seqJoint
            (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
            (fun b => ⟨(Zpar b).1, f.onVertex (Zpar b).1 (Zpar b).2⟩) := by
      funext t; cases t <;> rfl
    exact hRHS ▸ hpres
  let Exc : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0)}
  let ExcPar : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Zpar) (typeJoint (p := p) Zpar)}
  have hExc : #Exc ≤ #β + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0)} ≤ _
    exact infra_610_majority_eq_type seq Z0 hβτ
  have hExcPar : #ExcPar ≤ #β + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Zpar) (typeJoint (p := p) Zpar)} ≤ _
    exact infra_610_majority_eq_type seq Zpar hβτ
  have hex : ∃ i : seq.κIndex, i ∉ Exc ∧ i ∉ ExcPar := by
    by_contra h
    have hall : (Set.univ : Set seq.κIndex) ⊆ Exc ∪ ExcPar := by
      intro i _
      by_cases hi : i ∈ Exc ∪ ExcPar
      · exact hi
      · exact False.elim (h ⟨i, by
          simp only [Set.mem_union, not_or] at hi
          exact hi⟩)
    have hinfκ : aleph0 ≤ #seq.κIndex :=
      (le_add_self (a := aleph0) (b := #β)).trans (le_of_lt hbound)
    have hle : #seq.κIndex ≤ (#β + aleph0) + (#β + aleph0) := by
      have huni : #(Set.univ : Set seq.κIndex) = #seq.κIndex := mk_univ
      rw [← huni]
      exact (mk_le_mk_of_subset hall).trans
        ((mk_union_le _ _).trans (add_le_add hExc hExcPar))
    exact (not_le_of_gt (add_lt_of_lt hinfκ hbound hbound)) hle
  obtain ⟨i, hi, hiPar⟩ := hex
  have hgood : P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Z0) (typeJoint (p := p) Z0) := by
    simpa [Exc] using hi
  have hgoodPar : P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Zpar) (typeJoint (p := p) Zpar) := by
    simpa [ExcPar] using hiPar
  let pushed : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩
  let ZparB : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun b => ⟨(Zpar b).1, f.onVertex (Zpar b).1 (Zpar b).2⟩
  have hPushPar := hmovePar i
  have hPush : P.scheme.DiagramEq (X := A) (Y := B)
      (seqJoint (seq.family i) Z0) (seqJoint pushed ZparB) := by
    have h := hmove i
    have hpar : (fun b => B.occ (supp.eB (paramsI b))) = ZparB := by
      funext b
      have hv :
          (supp.eB (paramsI b) : B.model.carrier) =
            (f.onVertex PUnit.unit (params b) : B.model.carrier) := by
        dsimp [paramsI]
        exact Language.Equiv.apply_symm_apply supp.eB _
      exact
        (congrArg (fun a : B.model.carrier =>
            (⟨PUnit.unit, a⟩ :
              Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) hv).trans
          (by rfl)
    simpa [pushed, hpar] using h
  have hTypeEq : P.scheme.DiagramEq (X := p.host) (Y := p.host)
      (typeJoint (p := p) Z0) (typeJoint (p := p) Zpar) :=
    P.scheme.diagram_trans p.host A p.host (typeJoint (p := p) Z0)
      (seqJoint (seq.family i) Z0) (typeJoint (p := p) Zpar)
      (P.scheme.diagram_symm A p.host _ _ hgood)
      (P.scheme.diagram_trans A B p.host (seqJoint (seq.family i) Z0)
        (seqJoint pushed ZparB) (typeJoint (p := p) Zpar) hPush
        (P.scheme.diagram_trans B A p.host (seqJoint pushed ZparB)
          (seqJoint (seq.family i) Zpar) (typeJoint (p := p) Zpar)
          (P.scheme.diagram_symm A B _ _ hPushPar) hgoodPar))
  have hLHS : P.scheme.DiagramEq (X := p.host) (Y := B)
      (typeJoint (p := p) Zpar) ys :=
    P.scheme.diagram_trans p.host p.host B (typeJoint (p := p) Zpar)
      (typeJoint (p := p) Z0) ys
      (P.scheme.diagram_symm p.host p.host _ _ hTypeEq) hTY
  have hαμ : #(p.idx ⊕ β) < μ := hjoint.trans_lt hρμ
  have hαν : #(p.idx ⊕ β) < p.ν := by simpa [hνμ] using hαμ
  have hSame : P.D.SameD p.host.model B.model
      (fun t => p.host.val (typeJoint (p := p) Zpar t)) (fun t => B.val (ys t)) :=
    (SingleModelData.diagramEq_iff_sameD (P := P) (α := p.idx ⊕ β) p.hν hμ p.host B
      (fun t => p.host.val (typeJoint (p := p) Zpar t)) (fun t => B.val (ys t))
      hαν hαμ).mp hLHS
  obtain ⟨_, _, hMc, hNc, hs⟩ := hSame
  let ρ0 : Cardinal.{u} := max #(p.idx ⊕ β) aleph0
  let ρ' : Cardinal.{u} := max ρ (ls K)
  have hρ0inf : aleph0 ≤ ρ0 := le_max_right _ _
  have hρ0le : ρ0 ≤ ρ' :=
    max_le (hjoint.trans (le_max_left _ _)) (hρinf.trans (le_max_left _ _))
  have hls : ls K ≤ ρ' := le_max_right _ _
  have hρle' : ρ ≤ ρ' := le_max_left _ _
  have hρ'μ : ρ' < μ := max_lt hρμ (P.ls_lt hμ)
  have hρ'inf : aleph0 ≤ ρ' := hρinf.trans hρle'
  have hMc' : P.D.t ρ' ≤ Model.card p.host.model :=
    (P.t_lt hμ hρ'inf hρ'μ).le.trans (by simpa [hνμ] using p.host.card.ge)
  have hNc' : P.D.t ρ' ≤ Model.card B.model :=
    (P.t_lt hμ hρ'inf hρ'μ).le.trans B.card.ge
  have hsρ : P.D.same hjoint p.host.mem B.mem h₀ h₁
      (fun t => p.host.val (typeJoint (p := p) Zpar t)) (fun t => B.val (ys t)) :=
    P.D.same_relevel (σ := ρ0) (τ := ρ) (σ' := ρ')
      (le_max_left _ _) hρ0inf hρinf hρ0le hρle' hls
      p.host.mem B.mem hMc hNc hMc' hNc' h₀ h₁
      _ _ hs hjoint id
  have hL :
      (Sum.elim (fun i => p.host.val (p.val ((Equiv.refl p.idx).symm i)))
        (fun b => p.incl.onVertex PUnit.unit (params b))) =
        fun t => p.host.val (typeJoint (p := p) Zpar t) := by
    funext t; cases t with
    | inl i => rfl
    | inr b =>
      dsimp [typeJoint, Zpar, SMObject.occ, oneVertexOcc]
      rfl
  exact hL ▸ hsρ

/-- **E5 assembler.** Support + root majority + root Galois tests → full chart prescriptions. -/
theorem infra_610_chart_prescriptions
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (_hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (_hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hχls : ls K + σ < seq.τ) (hpow : seq.τ ^ σ = seq.τ)
    (htestχ : P.g σ + ls K ≤ seq.τ) :
    Nonempty (Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq) := by
  obtain ⟨supp⟩ :=
    infra_610_chart_support P σ hσ hμ hσμ f hf p hidx seq hτμ hκ hχls hpow htestχ
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  obtain ⟨placeRoot, hPlaceRoot⟩ := infra_610_placement_root_on_B hσ supp hidx hσlt
  exact ⟨{
    toInfra610ChartSupport := supp
    hgalois := infra_610_root_galois supp hνμ hτμ hκ
    hmajority := infra_610_root_majority supp hτμ hκ
    placeRoot := placeRoot
    hPlaceRoot := hPlaceRoot
  }⟩

/-- **E6.** Feed E5 data into `proposition_4_9` / Lem 6.4; free-lift `TupleOver` over `B`
is the chart-root representative of placement `z` (`infra_610_place_z_as_free_lift`). -/
theorem infra_610_place_prescriptions
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (_hrec : μ ∈ recursionClosedLevels P σ) (_hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (_hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (_hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (_hτμ : seq.τ < μ)
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B, q.ν = μ ∧ q = data.chartRoot := by
  classical
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  -- Retain Prop 4.9 placement `z` (English Lem 6.4 witness); `chartRoot` is its `B`-rep.
  obtain ⟨_J, _, _, _fIJ, _z, _hJ, _hPlace⟩ :=
    @proposition_4_9 K _ P.E P.D data.I data.linOrder data.nonempty data.wf
      p.idx σ data.χ hσ hidx data.hχls data.hpow data.hImem data.qPres data.hnat data.hcoh
  exact ⟨data.chartRoot, rfl, rfl⟩

/-- **E2–E3 packaging.** Majority transport of `seq` for queries from `B`. -/
theorem infra_610_majority_of_placement
    (P : SingleModelData K) (σ : Cardinal.{u}) (_hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence p)
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq) :
    ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seq.τ →
      ∃ (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
        (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        IsMajorityValue seq Z0 hμ B xs :=
  fun Z hι => data.hmajority Z hι

/-- **E7 tests.** Diagram tests of `p` vs the reflected Prop 4.9 joint. -/
theorem infra_610_galois_tests_of_placement
    (P : SingleModelData K) (σ : Cardinal.{u}) (_hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence p)
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq) :
    ∀ {β : Type u} (hβg : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (params : β → A.model.carrier)
      (hjoint : #(data.chartRoot.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card p.host.model)
      (h₁ : P.D.t ρ ≤ Model.card data.chartRoot.host.model),
      P.D.same hjoint p.host.mem data.chartRoot.host.mem h₀ h₁
        (Sum.elim (fun i => p.host.val (p.val ((Equiv.refl p.idx).symm i)))
          (fun b => p.incl.onVertex PUnit.unit (params b)))
        (fun t => B.val (B.occ (data.eB (data.qPres (hβg.trans data.htestχ)
          (fun b => data.eB.symm (f.onVertex PUnit.unit (params b))) t)))) := by
  intro β hβg ρ hρinf hρμ params hjoint h₀ h₁
  simp only [Infra610ChartPrescriptions.chartRoot] at hjoint h₁ ⊢
  exact data.hgalois hβg ρ hρinf hρμ params hjoint h₀ h₁

/-- Assembler of English E5–E7: chart prescriptions → Lem 6.4 placement → majority +
`SameGaloisType` (`infra_610_isFreeLift_same_galois`). -/
theorem infra_610_majority_prescription
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (hκIndex : seq.τ + aleph0 < #seq.κIndex)
    (hχls : ls K + σ < seq.τ) (hpow : seq.τ ^ σ = seq.τ)
    (htestχ : P.g σ + ls K ≤ seq.τ) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B,
      ∃ e : p.idx ≃ q.idx, IsFreeLift p q f hf e := by
  obtain ⟨data⟩ :=
    infra_610_chart_prescriptions P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ hκIndex
      hχls hpow htestχ
  obtain ⟨q, hqν, hq⟩ :=
    infra_610_place_prescriptions P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ data
  subst hq
  exact ⟨data.chartRoot, Equiv.refl p.idx,
    infra_610_isFreeLift_same_galois P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ hκIndex
      data⟩

/-- Packaging of `infra_610_majority_prescription` (English E5–E7 on a chart of `B`). -/
theorem infra_610_place_on_B
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (hκIndex : seq.τ + aleph0 < #seq.κIndex)
    (hχls : ls K + σ < seq.τ) (hpow : seq.τ ^ σ = seq.τ)
    (htestχ : P.g σ + ls K ≤ seq.τ) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B, ∃ e : p.idx ≃ q.idx,
      IsFreeLift p q f hf e :=
  infra_610_majority_prescription P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ hκIndex
    hχls hpow htestχ

/-! ## Existence -/

/-- English clause 1: existence of a free lift along a permitted arrow of `P.scheme`.
Packaging matches Lemma 6.9 (`p.ν = μ`, recursion-closed level, code arity `c(σ)`).
Full `IsFreeLift` (`SameGaloisType` + majority) via `infra_610_isFreeLift_same_galois`. -/
theorem stationary_free_extension_exists
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hidxμ : #p.idx < μ) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B, ∃ e : p.idx ≃ q.idx,
      IsFreeLift p q f hf e := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let τ0 : Cardinal.{u} := testCardinal b P.g σ
  have hτ0 : ℵ₀ ≤ τ0 := by
    change ℵ₀ ≤ (2 : Cardinal.{u}) ^ (P.g σ + b + σ + aleph0)
    exact le_trans (cantor aleph0).le
      (power_le_power_left two_ne_zero
        (le_add_self : aleph0 ≤ (P.g σ + b + σ) + aleph0))
  have hexp0 : P.g σ + b + σ + aleph0 < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    have hb : b < μ := max_lt (P.ls_lt hμ) (P.aleph0_lt hμ)
    have h1 : P.g σ + b < μ := add_lt_of_lt (P.aleph0_le hμ) hg hb
    have h2 : P.g σ + b + σ < μ := add_lt_of_lt (P.aleph0_le hμ) h1 hσlt
    exact add_lt_of_lt (P.aleph0_le hμ) h2 (P.aleph0_lt hμ)
  have hτ0μ : τ0 < μ :=
    hμ.1.working.strongLimit.isStrongPrelimit hexp0
  -- Power-fixed `χ ≥ τ0` becomes the approximation arity so majority covers Prop 4.9.
  obtain ⟨χ, hχls, hχμ, hpow, hτ0χ, htestχ⟩ :=
    infra_610_choose_chi P σ hσ hμ hσlt τ0 hτ0μ
  let τ : Cardinal.{u} := χ
  let κ : Cardinal.{u} := Order.succ τ
  have hτ : ℵ₀ ≤ τ := hτ0.trans hτ0χ
  have hτμ : τ < μ := hχμ
  have hκ : ℵ₀ ≤ κ := hτ.trans (Order.le_succ _)
  have hκμ : κ < μ :=
    (Order.succ_le_of_lt (cantor τ)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hτμ)
  have hprod : κ * #p.idx < μ := by
    have hmul : κ * #p.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    have hκσ : κ * σ = κ := by
      refine mul_eq_left hκ ?_ (aleph0_pos.trans_le hσ).ne'
      have hστ : σ < τ :=
        (lt_of_lt_of_le (cantor σ)
          (power_le_power_left two_ne_zero
            (le_trans (le_add_self : σ ≤ (P.g σ + b) + σ)
              (le_self_add : (P.g σ + b) + σ ≤ ((P.g σ + b) + σ) + aleph0)))).trans_le hτ0χ
      exact hστ.le.trans (Order.le_succ _)
    exact hmul.trans_lt (by rw [hκσ]; exact hκμ)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ := by
    have hβ : max (max σ τ) (max (ls K) ℵ₀) < μ :=
      max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
    exact hrec.2 _ hβ
  obtain ⟨seq, hseqτ, hseqκ⟩ :=
    P.exists_approximationSequence hμ A p hνμ σ τ κ hσ hσlt hidx hτ hτμ hκ hκμ hprod hclosed
  have hseqτμ : seq.τ < μ := hseqτ ▸ hτμ
  have hκIndex : seq.τ + aleph0 < #seq.κIndex := by
    rw [hseqκ, hseqτ, add_eq_left hτ hτ]
    exact Order.lt_succ τ
  have hχls' : ls K + σ < seq.τ := hseqτ ▸ hχls
  have hpow' : seq.τ ^ σ = seq.τ := by rw [hseqτ]; exact hpow
  have htestχ' : P.g σ + ls K ≤ seq.τ := hseqτ ▸ htestχ
  exact infra_610_place_on_B P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hseqτμ hκIndex
    hχls' hpow' htestχ'

end
end AEC
