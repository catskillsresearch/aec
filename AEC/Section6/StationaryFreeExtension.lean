module

public import AEC.Section6.FreeExtension
public import AEC.Section6.TupleOver
public import AEC.Section6.UniformApproximations
public import AEC.Section6.TestCardinal
public import AEC.Section4.ClosedLevelTypes

@[expose] public section

/-!
# Theorem 6.10 (Stationary free extension) — English gloss

English ↔ Lean step map: `FreeExtension.md` (paper pp. 44–45).

**Statement repair.** Same packaging as Lemma 6.9: `SingleModelData` at recursion-closed levels,
with same-level host `p.ν = μ`. `IsFreeLift` queries are bounded by the sequence arity `I.τ`
(English testing cost), not every `#ι < ν`. Cross-scheme transfer is not used.

**Open tips.** English E5 `infra_610_chart_prescriptions`, majority clause
`infra_610_majority_of_placement`, E7 tests `infra_610_galois_tests_of_placement`
(assembled by `infra_610_majority_prescription`). E6 `infra_610_place_prescriptions` is done.
Lean-only: `infra_610_closed_level` (`PlacedTester` / `ClosedLevel` for `P.g`).
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

/-- English E5 data: Prop 4.9 `q` / `hnat` / `hcoh` package on a well-ordered chart of `B`. -/
structure Infra610ChartPrescriptions
    {K : AbstractElementaryClass.{u}} (P : SingleModelData K) (σ : Cardinal.{u})
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    (B : P.scheme.Object μ hμ) (α : Type u) (τBound : Cardinal.{u}) where
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
  hτχ : τBound ≤ χ
  eB : (@OrderPresentation.obj K P.E I linOrder nonempty).carrier ≃[K.τ] B.model.carrier
  qPres : ∀ {β : Type u}, #β ≤ χ →
    (β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier) →
    α ⊕ β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier
  hnat : ∀ {β : Type u} (hβ : #β ≤ χ)
    (params : β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier)
    (hpar : #β ≤ σ + χ)
    (hcardI : P.D.t (σ + χ) ≤
      Model.card (@OrderPresentation.obj K P.E I linOrder nonempty)),
    P.D.same hpar hImem hImem hcardI hcardI
      (fun b => qPres hβ params (Sum.inr b)) params
  hcoh : ∀ {β β' : Type u} (hβ : #β ≤ χ) (hβ' : #β' ≤ χ)
    (params : β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier)
    (ι : β' → β) (hjoint : #(α ⊕ β') ≤ σ + χ)
    (hcardI : P.D.t (σ + χ) ≤
      Model.card (@OrderPresentation.obj K P.E I linOrder nonempty)),
    P.D.same hjoint hImem hImem hcardI hcardI
      (fun i => qPres hβ params (Sum.map id ι i))
      (qPres hβ' (fun b => params (ι b)))

/-- **Open (E5).** Well-ordered chart of `B` and majority prescriptions as Prop 4.9
`q`/`hnat`/`hcoh` data (via `move_query` + uniqueness). No placement yet. -/
theorem infra_610_chart_prescriptions
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ) :
    Nonempty (Infra610ChartPrescriptions (hμ := hμ) P σ B p.idx seq.τ) := by
  sorry

/-- **E6.** Feed E5 data into `proposition_4_9` / Lem 6.4, then represent the placed type as a
same-level `TupleOver` over `B` (`q.ν = μ`) by the chart-root of the prescriptions (English:
local majority prescriptions are already realized in the chart of `B`). -/
theorem infra_610_place_prescriptions
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (_hrec : μ ∈ recursionClosedLevels P σ) (_hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (_f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (_hf : P.scheme.permitted (X := A) (Y := B) _f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (_hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (_hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (_hτμ : seq.τ < μ)
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ B p.idx seq.τ) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B,
      ∃ e : p.idx ≃ q.idx, q.ν = μ := by
  classical
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  -- English Lem 6.4: the majority prescriptions cohere in an order enlargement.
  -- Instances are the structure fields (not `haveI`), so they match `data.hImem` / `qPres`.
  obtain ⟨_J, _, _, _fIJ, _z, _hJ, _hPlace⟩ :=
    @proposition_4_9 K _ P.E P.D data.I data.linOrder data.nonempty data.wf
      p.idx σ data.χ hσ hidx data.hχls data.hpow data.hImem data.qPres data.hnat data.hcoh
  -- Chart-root representative on `B` (local realizations already live in the chart).
  have hβ0 : #(PEmpty.{u + 1}) ≤ data.χ := by
    simpa using (zero_le data.χ : (0 : Cardinal.{u}) ≤ data.χ)
  let root : p.idx → B.model.carrier := fun a =>
    data.eB (data.qPres hβ0 PEmpty.elim (Sum.inl a))
  let q : TupleOver K oneVertexShape P.scheme hμ B :=
    { ν := μ
      hν := hμ
      host := B
      incl := SystemArrow.refl (P.scheme.asSystem hμ B)
      incl_arrow := trivial
      idx := p.idx
      val := fun a => B.occ (root a) }
  exact ⟨q, Equiv.refl _, rfl⟩

/-- **Open (majority clause).** After E6 placement, queries from `B` of size `≤ seq.τ` are
answered by majority transport of `seq` (English E2–E3). -/
theorem infra_610_majority_of_placement
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ B p.idx seq.τ)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (e : p.idx ≃ q.idx) (hqν : q.ν = μ) :
    ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seq Z0 q.hν q.host
          (typeJoint (p := q) Z ∘ Sum.map e id) := by
  sorry

/-- **Open (E7 tests).** Diagram tests of `p` vs `q.restrict f` for Thm 6.6 / `same_galois`. -/
theorem infra_610_galois_tests_of_placement
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (e : p.idx ≃ q.idx) (hνμ : p.ν = μ) (hqν : q.ν = μ)
    (hidx : #p.idx ≤ σ) :
    ∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(q.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card p.host.model)
      (h₁ : P.D.t ρ ≤ Model.card q.host.model),
      P.D.same hjoint p.host.mem q.host.mem h₀ h₁
        (Sum.elim (fun i => p.host.val (p.val (e.symm i)))
          (fun b => p.incl.onVertex PUnit.unit (params b)))
        (Sum.elim (fun i => q.host.val (q.val i))
          (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b))) := by
  sorry

/-- Assembler of English E5–E7: chart prescriptions → Lem 6.4 placement → majority → Galois
tests. -/
theorem infra_610_majority_prescription
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B,
      ∃ e : p.idx ≃ q.idx,
        q.ν = μ ∧
        (∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
          (_ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(q.idx ⊕ β) ≤ ρ)
          (h₀ : P.D.t ρ ≤ Model.card p.host.model)
          (h₁ : P.D.t ρ ≤ Model.card q.host.model),
          P.D.same hjoint p.host.mem q.host.mem h₀ h₁
            (Sum.elim (fun i => p.host.val (p.val (e.symm i)))
              (fun b => p.incl.onVertex PUnit.unit (params b)))
            (Sum.elim (fun i => q.host.val (q.val i))
              (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b)))) ∧
        ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
          #ι ≤ seq.τ →
          ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
            IsMajorityValue seq Z0 q.hν q.host
              (typeJoint (p := q) Z ∘ Sum.map e id) := by
  obtain ⟨data⟩ :=
    infra_610_chart_prescriptions P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ
  obtain ⟨q, e, hqν⟩ :=
    infra_610_place_prescriptions P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ data
  refine ⟨q, e, hqν, ?_, ?_⟩
  · exact infra_610_galois_tests_of_placement P σ hσ hμ f hf p q e hνμ hqν hidx
  · exact infra_610_majority_of_placement P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ
      seq hτμ data q e hqν

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
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B,
      ∃ e : p.idx ≃ q.idx,
        q.ν = μ ∧
        (∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
          (_ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(q.idx ⊕ β) ≤ ρ)
          (h₀ : P.D.t ρ ≤ Model.card p.host.model)
          (h₁ : P.D.t ρ ≤ Model.card q.host.model),
          P.D.same hjoint p.host.mem q.host.mem h₀ h₁
            (Sum.elim (fun i => p.host.val (p.val (e.symm i)))
              (fun b => p.incl.onVertex PUnit.unit (params b)))
            (Sum.elim (fun i => q.host.val (q.val i))
              (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b)))) ∧
        ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
          #ι ≤ seq.τ →
          ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
            IsMajorityValue seq Z0 q.hν q.host
              (typeJoint (p := q) Z ∘ Sum.map e id) :=
  infra_610_majority_prescription P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ

/-! ## Same Galois type from ClosedLevel tests -/

/-- **Open (Lean-only).** `ClosedLevel` for the scheme bound `P.g` at a recursion-closed
eligible `μ`. Not an English Thm 6.10 step: packaging so Thm 6.6 / `same_galois` can run at
`P.g`.

`exists_placedTester P.E P.D` yields some `g0`, not `P.g`. Eligibility is only
`IsClosurePoint {P.D.t, P.g}`, so it does not force `placedTestBound θ < μ`. Do not substitute
`g0` or weaken the Thm 6.6 testing bound. -/
theorem infra_610_closed_level
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (_hrec : μ ∈ recursionClosedLevels P σ) :
    ClosedLevel K P.E P.D P.g μ := by
  sorry

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

/-! ## Existence -/

/-- English clause 1: existence of a free lift along a permitted arrow of `P.scheme`.
Packaging matches Lemma 6.9 (`p.ν = μ`, recursion-closed level, code arity `c(σ)`).
Open tips are E5–E7 (`chart_prescriptions` / `place_prescriptions` /
`galois_tests_of_placement`) and Lean-only `infra_610_closed_level`. -/
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
  let τ : Cardinal.{u} := testCardinal b P.g σ
  let κ : Cardinal.{u} := Order.succ τ
  have hτ : ℵ₀ ≤ τ := by
    change ℵ₀ ≤ (2 : Cardinal.{u}) ^ (P.g σ + b + σ + aleph0)
    exact le_trans (cantor aleph0).le
      (power_le_power_left two_ne_zero
        (le_add_self : aleph0 ≤ (P.g σ + b + σ) + aleph0))
  have hexp : P.g σ + b + σ + aleph0 < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    have hb : b < μ := max_lt (P.ls_lt hμ) (P.aleph0_lt hμ)
    have h1 : P.g σ + b < μ := add_lt_of_lt (P.aleph0_le hμ) hg hb
    have h2 : P.g σ + b + σ < μ := add_lt_of_lt (P.aleph0_le hμ) h1 hσlt
    exact add_lt_of_lt (P.aleph0_le hμ) h2 (P.aleph0_lt hμ)
  have hτμ : τ < μ :=
    hμ.1.working.strongLimit.isStrongPrelimit hexp
  have hκ : ℵ₀ ≤ κ := hτ.trans (Order.le_succ _)
  have hκμ : κ < μ :=
    (Order.succ_le_of_lt (cantor τ)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hτμ)
  have hprod : κ * #p.idx < μ := by
    have hmul : κ * #p.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    have hκσ : κ * σ = κ := by
      refine mul_eq_left hκ ?_ (aleph0_pos.trans_le hσ).ne'
      have hστ : σ < τ := by
        change σ < (2 : Cardinal.{u}) ^ (P.g σ + b + σ + aleph0)
        exact lt_of_lt_of_le (cantor σ)
          (power_le_power_left two_ne_zero
            (le_trans (le_add_self : σ ≤ (P.g σ + b) + σ)
              (le_self_add : (P.g σ + b) + σ ≤ ((P.g σ + b) + σ) + aleph0)))
      exact hστ.le.trans (Order.le_succ _)
    exact hmul.trans_lt (by rw [hκσ]; exact hκμ)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ := by
    have hβ : max (max σ τ) (max (ls K) ℵ₀) < μ :=
      max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
    exact hrec.2 _ hβ
  obtain ⟨seq, hseqτ, _⟩ :=
    P.exists_approximationSequence hμ A p hνμ σ τ κ hσ hσlt hidx hτ hτμ hκ hκμ hprod hclosed
  have hseqτμ : seq.τ < μ := hseqτ ▸ hτμ
  obtain ⟨q, e, hqν, htest, hmaj⟩ :=
    infra_610_place_on_B P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hseqτμ
  have hL := infra_610_closed_level P σ hσ hμ hrec
  refine ⟨q, e, ⟨infra_610_same_galois f hf p q e σ hσ hσlt hidx hνμ hqν hL htest, ⟨seq, ?_⟩⟩⟩
  intro ι Z hι
  obtain ⟨Z0, hZ0⟩ := hmaj Z hι
  refine ⟨Z0, typeJoint (p := q) Z ∘ Sum.map e id, hZ0, ?_⟩
  have hre : reindexJoint e (typeJoint (p := q) Z ∘ Sum.map e id) =
      typeJoint (p := q) Z := by
    funext t
    cases t with
    | inl i =>
      simp [reindexJoint, Function.comp, Sum.map, Equiv.symm_apply_apply]
    | inr j =>
      rfl
  rw [hre]
  exact P.scheme.diagram_refl q.host _

end
end AEC
