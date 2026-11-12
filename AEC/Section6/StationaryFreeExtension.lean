module

public import AEC.Section6.FreeExtension
public import AEC.Section6.TupleOver
public import AEC.Section6.UniformApproximations
public import AEC.Section6.TestCardinal
public import AEC.Section4.ClosedLevelTypes
public import AEC.Section5.SingleModelScheme

@[expose] public section

/-!
# Theorem 6.10 (Stationary free extension) — English gloss

English ↔ Lean step map: `FreeExtension.md` (paper pp. 44–45).

**Statement repair.** Same packaging as Lemma 6.9: `SingleModelData` at recursion-closed levels,
with same-level host `p.ν = μ`. `IsFreeLift` queries are bounded by the sequence arity `I.τ`
(English testing cost), not every `#ι < ν`. Cross-scheme transfer is not used.

**Open tips (E5 split).** `infra_610_majority_matches_root` (residual: join `hinr`+`hcoh`
into `DiagramEq` of the placed joint), `infra_610_root_galois`. Done: majority `qPres`
(`infra_610_majority_qPres` / `chart_support` with `χ = seq.τ`), `moved_majority`, placed
`chartRoot` from empty majority prescription, E6–E7 packaging and `closed_level`.
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
  /-- Each prescription is a moved majority answer on `B`. -/
  hmajPres : ∀ {β : Type u} (hβ : #β ≤ χ)
    (params : β → (@OrderPresentation.obj K P.E I linOrder nonempty).carrier),
    ∃ (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
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
  /-- Thm 6.6 tests: `p` vs the placed empty-query majority root on `B`. -/
  hgalois : ∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
    (_ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(p.idx ⊕ β) ≤ ρ)
    (h₀ : P.D.t ρ ≤ Model.card p.host.model)
    (h₁ : P.D.t ρ ≤ Model.card B.model),
    P.D.same hjoint p.host.mem B.mem h₀ h₁
      (Sum.elim (fun i => p.host.val (p.val ((Equiv.refl p.idx).symm i)))
        (fun b => p.incl.onVertex PUnit.unit (params b)))
      (Sum.elim
        (fun i => B.val (B.occ (eB (qPres
          (β := PEmpty.{u + 1})
          (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ χ))
          PEmpty.elim (Sum.inl i)))))
        (fun b =>
          (SystemArrow.comp f (SystemArrow.refl (P.scheme.asSystem hμ B))).onVertex
            PUnit.unit (params b)))
  /-- E2–E3: some majority value of `seq` on a moved query from `B` (good `vi` push).
  Identification with the chart-root joint is `infra_610_majority_matches_root`. -/
  hmajority : ∀ {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
    #ι ≤ seq.τ →
    ∃ (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
      (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      IsMajorityValue seq Z0 hμ B xs

/-- Placed free-lift representative on `B` (E6 wrap): empty-query majority prescription
pulled along the chart iso (agrees with Prop 4.9’s `z` by `hcoh` / empty reindexing). -/
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
  val := fun a =>
    B.occ (data.eB (data.qPres
      (β := PEmpty.{u + 1})
      (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ))
      PEmpty.elim (Sum.inl a)))

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
      -- `val_occ` is `rfl`; recover `params` along `eB`.
      change eB.symm (eB (params b)) = params b
      exact Language.Equiv.symm_apply_apply eB (params b)
    · have hx : (fun t => B.occ (eB (infra_610_pullMajority eB xs t))) = xs := by
        funext t
        -- `pullMajority` then `eB` recovers `val`; `occ_val` is `rfl`.
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
    obtain ⟨Z0, _, _, hmaj⟩ := hqSpec hβ params
    exact ⟨Z0, hmaj⟩

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

/-- **E5d′.** The majority prescription on a query `Z` is `DiagramEq` to the placed
chart-root joint. Returns the majority witness so the free-lift assembler need not
re-derive it from `root_majority`. -/
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
      P.scheme.DiagramEq (X := B) (Y := B) xs
        (Sum.elim
          (fun a => B.occ (supp.eB (supp.qPres
            (β := PEmpty.{u + 1})
            (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ supp.χ))
            PEmpty.elim (Sum.inl a))))
          (fun j =>
            ⟨(Z j).1,
              (SystemArrow.refl (P.scheme.asSystem hμ B)).onVertex (Z j).1 (Z j).2⟩)) := by
  classical
  letI := supp.linOrder
  letI := supp.nonempty
  let params : ι → (P.E.obj supp.I).carrier := fun j => supp.eB.symm (B.val (Z j))
  have hZ : ∀ j, B.occ (supp.eB (params j)) = Z j := by
    intro j
    change B.occ (supp.eB (supp.eB.symm (B.val (Z j)))) = Z j
    rw [Language.Equiv.apply_symm_apply]
    rfl
  obtain ⟨Z0, hmaj⟩ := supp.hmajPres hιχ params
  let xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun t => B.occ (supp.eB (supp.qPres hιχ params t))
  refine ⟨Z0, xs, hmaj, ?_⟩
  -- Remaining glue: `hinr` + `hcoh` (or Prop 4.9 empty-vs-params) give
  -- `D.same (Sum.elim empty-root params) (qPres params)` on the chart; push by `eB`.
  have hEmpty : #(PEmpty.{u + 1}) ≤ supp.χ := by
    simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ supp.χ)
  have hjointEmpty : #(p.idx ⊕ PEmpty.{u + 1}) ≤ σ + supp.χ := by
    simpa [mk_sum, lift_id, mk_eq_zero, add_zero] using
      (hidx.trans (self_le_add_right σ supp.χ) : #p.idx ≤ σ + supp.χ)
  have hcardObj : Model.card (P.E.obj supp.I) = μ :=
    P.card_obj_eq hμ supp.I supp.hIcard
  have hσχμ : σ + supp.χ < μ :=
    add_lt_of_lt (P.aleph0_le hμ) hσμ supp.hχμ
  have hcardI : P.D.t (σ + supp.χ) ≤ Model.card (P.E.obj supp.I) :=
    ((P.t_lt hμ (hσ.trans (self_le_add_right σ supp.χ)) hσχμ).le).trans hcardObj.ge
  have _hcoh :=
    supp.hcoh (hβ := hιχ) (hβ' := hEmpty) params PEmpty.elim hjointEmpty hcardI
  have _hinr := fun b => supp.hinr hιχ params b
  have _hZ := hZ
  sorry

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

/-- **Open (E5e).** Thm 6.6 diagram tests of `p` vs the placed empty-query majority root. -/
theorem infra_610_root_galois
    {P : SingleModelData K} {σ : Cardinal.{u}}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hμ A} {seq : ApproximationSequence p}
    (supp : Infra610ChartSupport (hμ := hμ) P σ f hf p seq) :
    ∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (params : β → A.model.carrier) (hjoint : #(p.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card p.host.model)
      (h₁ : P.D.t ρ ≤ Model.card B.model),
      P.D.same hjoint p.host.mem B.mem h₀ h₁
        (Sum.elim (fun i => p.host.val (p.val ((Equiv.refl p.idx).symm i)))
          (fun b => p.incl.onVertex PUnit.unit (params b)))
        (Sum.elim
          (fun i => B.val (B.occ (supp.eB (supp.qPres
            (β := PEmpty.{u + 1})
            (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ supp.χ))
            PEmpty.elim (Sum.inl i)))))
          (fun b =>
            (SystemArrow.comp f (SystemArrow.refl (P.scheme.asSystem hμ B))).onVertex
              PUnit.unit (params b))) := by
  sorry

/-- **E5 assembler.** Support + root majority + root Galois tests → full chart prescriptions. -/
theorem infra_610_chart_prescriptions
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (_hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (_hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (_hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hχls : ls K + σ < seq.τ) (hpow : seq.τ ^ σ = seq.τ)
    (htestχ : P.g σ + ls K ≤ seq.τ) :
    Nonempty (Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq) := by
  obtain ⟨supp⟩ :=
    infra_610_chart_support P σ hσ hμ hσμ f hf p hidx seq hτμ hκ hχls hpow htestχ
  exact ⟨{
    toInfra610ChartSupport := supp
    hgalois := infra_610_root_galois supp
    hmajority := infra_610_root_majority supp hτμ hκ
  }⟩

/-- **E6.** Feed E5 data into `proposition_4_9` / Lem 6.4, then take the chart-root
`TupleOver` over `B`. -/
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

/-- **E7 tests.** Diagram tests of `p` vs `data.chartRoot.restrict f` (identity reindexing). -/
theorem infra_610_galois_tests_of_placement
    (P : SingleModelData K) (σ : Cardinal.{u}) (_hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence p)
    (data : Infra610ChartPrescriptions (hμ := hμ) P σ f hf p seq) :
    ∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (params : β → A.model.carrier)
      (hjoint : #(data.chartRoot.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card p.host.model)
      (h₁ : P.D.t ρ ≤ Model.card data.chartRoot.host.model),
      P.D.same hjoint p.host.mem data.chartRoot.host.mem h₀ h₁
        (Sum.elim (fun i => p.host.val (p.val ((Equiv.refl p.idx).symm i)))
          (fun b => p.incl.onVertex PUnit.unit (params b)))
        (Sum.elim (fun i => data.chartRoot.host.val (data.chartRoot.val i))
          (fun b => (data.chartRoot.restrict f hf).incl.onVertex PUnit.unit (params b))) := by
  intro β hβ ρ hρinf hρμ params hjoint h₀ h₁
  simp only [Infra610ChartPrescriptions.chartRoot, TupleOver.restrict] at hjoint h₁ ⊢
  exact data.hgalois hβ ρ hρinf hρμ params hjoint h₀ h₁

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
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (hκIndex : seq.τ + aleph0 < #seq.κIndex)
    (hχls : ls K + σ < seq.τ) (hpow : seq.τ ^ σ = seq.τ)
    (htestχ : P.g σ + ls K ≤ seq.τ) :
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
          ∃ (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
            (xs : p.idx ⊕ ι → Occurrence K oneVertexShape
              (P.scheme.asSystem q.hν q.host)),
            IsMajorityValue seq Z0 q.hν q.host xs ∧
            P.scheme.DiagramEq (X := q.host) (Y := q.host)
              (reindexJoint e xs) (typeJoint (p := q) Z) := by
  obtain ⟨data⟩ :=
    infra_610_chart_prescriptions P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ hκIndex
      hχls hpow htestχ
  obtain ⟨q, hqν, hq⟩ :=
    infra_610_place_prescriptions P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ data
  -- Specialize to the chart-root so `q.idx` is definitionally `p.idx`.
  subst hq
  refine ⟨data.chartRoot, Equiv.refl p.idx, hqν, ?_, ?_⟩
  · exact infra_610_galois_tests_of_placement P σ hσ hμ f hf p seq data
  · intro ι Z hι
    have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
    have hιχ : #ι ≤ data.χ := by simpa [data.hχτ] using hι
    have hbound : #ι + aleph0 < #seq.κIndex :=
      (add_le_add hι le_rfl).trans_lt hκIndex
    obtain ⟨Z0, xs, hmaj, heq⟩ :=
      infra_610_majority_matches_root (hσ := hσ)
        (supp := data.toInfra610ChartSupport) hidx hσlt Z hιχ hbound
    have hre : reindexJoint (Equiv.refl p.idx) xs = xs := by
      funext t
      cases t with
      | inl i =>
        simp [reindexJoint, Equiv.refl_symm]
      | inr j =>
        rfl
    have hroot :
        Sum.elim
          (fun a => B.occ (data.eB (data.qPres
            (β := PEmpty.{u + 1})
            (by simpa [mk_eq_zero] using (bot_le : (0 : Cardinal.{u}) ≤ data.χ))
            PEmpty.elim (Sum.inl a))))
          (fun j =>
            ⟨(Z j).1,
              (SystemArrow.refl (P.scheme.asSystem hμ B)).onVertex (Z j).1 (Z j).2⟩) =
          typeJoint (p := data.chartRoot) Z := by
      funext t
      cases t with
      | inl _ => rfl
      | inr _ => rfl
    refine ⟨Z0, xs, hmaj, ?_⟩
    change P.scheme.DiagramEq (X := B) (Y := B) (reindexJoint (Equiv.refl p.idx) xs)
      (typeJoint (p := data.chartRoot) Z)
    exact cast (congrArg₂ (P.scheme.DiagramEq (X := B) (Y := B)) hre.symm hroot) heq

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
          ∃ (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
            (xs : p.idx ⊕ ι → Occurrence K oneVertexShape
              (P.scheme.asSystem q.hν q.host)),
            IsMajorityValue seq Z0 q.hν q.host xs ∧
            P.scheme.DiagramEq (X := q.host) (Y := q.host)
              (reindexJoint e xs) (typeJoint (p := q) Z) :=
  infra_610_majority_prescription P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ hκIndex
    hχls hpow htestχ

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

/-! ## Existence -/

/-- English clause 1: existence of a free lift along a permitted arrow of `P.scheme`.
Packaging matches Lemma 6.9 (`p.ν = μ`, recursion-closed level, code arity `c(σ)`).
Open tip is E5 `chart_prescriptions` (`hgalois` / `hmajority`). -/
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
  obtain ⟨q, e, hqν, htest, hmaj⟩ :=
    infra_610_place_on_B P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hseqτμ hκIndex
      hχls' hpow' htestχ'
  have hL := infra_610_closed_level P σ hσ hμ hrec
  refine ⟨q, e, ⟨infra_610_same_galois f hf p q e σ hσ hσlt hidx hνμ hqν hL htest, ⟨seq, ?_⟩⟩⟩
  intro ι Z hι
  obtain ⟨Z0, xs, hZ0, heq⟩ := hmaj Z hι
  exact ⟨Z0, xs, hZ0, heq⟩

end
end AEC
