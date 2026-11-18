module

public import AEC.Section7.MixedLevel
public import AEC.Section6.GaloisCrossLevel

@[expose] public section

/-!
# Mixed-level tied free lift (grokbot_02)

Port of the English §6.2 chart placement (`Infra610ChartSupport`, `infra_610_tied_placement`,
`infra_610_tied_at`, `infra_610_tied_free_lift`) to a base `A` at a recursion-closed level `ν`
and a target `B` at a level `μ ≥ ν`.  The same-level proof used a structural isomorphism
`A ≅ B` only to *move* queries from `B` into `A`; here every move is the mixed saturation move
`infra_78_move_mixed` (bounded below `ν`).  The chart of `B`, the Proposition 4.9 placement and
the strong hull all live at `B`'s level `μ`, exactly as in the same-level proof.
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-- Mixed `move_query`: one move of `Z` (bounded below `ν`) over the whole concatenated sequence. -/
theorem infra_78_move_query_mixed
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f) (hνμ : ν ≤ μ)
    {p : TupleOver K oneVertexShape P.scheme hν A}
    (seq : ApproximationSequence p) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) (hιν : #ι < ν) :
    ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A),
      infra_78_isMoveMixed f seq Z Z0 := by
  classical
  let xs : seq.κIndex × p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν A) :=
    fun ij => seq.family ij.1 ij.2
  obtain ⟨Z0, hZ0⟩ := infra_78_move_mixed f hf hνμ xs Z seq.concat_bounded hιν
  refine ⟨Z0, fun i => ?_⟩
  let ρ : p.idx ⊕ ι → (seq.κIndex × p.idx) ⊕ ι := fun t =>
    match t with
    | Sum.inl j => Sum.inl (i, j)
    | Sum.inr k => Sum.inr k
  have hρ : Function.Injective ρ := by
    intro x y hxy
    cases x <;> cases y <;> simp_all [ρ]
  have hpre := WorkingScheme.diagramEq_precomp (W := P.scheme) A B _ _ ρ hρ hZ0
  convert hpre using 1 <;> funext t <;> cases t <;> rfl

/-- Mixed common move: one query from `B` is a sequence-move over two approximation sequences
at once (`infra_78_move_mixed` over the union of both concatenations). -/
theorem infra_78_common_move_mixed
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f) (hνμ : ν ≤ μ)
    {q : TupleOver K oneVertexShape P.scheme hν A}
    (seq seq' : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) (hιν : #ι < ν) :
    ∃ Z1 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A),
      infra_78_isMoveMixed f seq Z Z1 ∧ infra_78_isMoveMixed f seq' Z Z1 := by
  classical
  let xs : (seq.κIndex × q.idx) ⊕ (seq'.κIndex × q.idx) →
      Occurrence K oneVertexShape (P.scheme.asSystem hν A) :=
    Sum.elim (fun ij => seq.family ij.1 ij.2) (fun ij => seq'.family ij.1 ij.2)
  have hxs : #((seq.κIndex × q.idx) ⊕ (seq'.κIndex × q.idx)) < ν := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hν) seq.concat_bounded seq'.concat_bounded
  obtain ⟨Z1, hZ1⟩ := infra_78_move_mixed f hf hνμ xs Z hxs hιν
  refine ⟨Z1, fun i => ?_, fun i => ?_⟩
  · let ρ : q.idx ⊕ ι → ((seq.κIndex × q.idx) ⊕ (seq'.κIndex × q.idx)) ⊕ ι := fun t =>
      match t with
      | Sum.inl j => Sum.inl (Sum.inl (i, j))
      | Sum.inr k => Sum.inr k
    have hρ : Function.Injective ρ := by
      intro x y hxy
      cases x <;> cases y <;> simp_all [ρ]
    have hpre := WorkingScheme.diagramEq_precomp (W := P.scheme) A B _ _ ρ hρ hZ1
    convert hpre using 1 <;> funext t <;> cases t <;> rfl
  · let ρ : q.idx ⊕ ι → ((seq.κIndex × q.idx) ⊕ (seq'.κIndex × q.idx)) ⊕ ι := fun t =>
      match t with
      | Sum.inl j => Sum.inl (Sum.inr (i, j))
      | Sum.inr k => Sum.inr k
    have hρ : Function.Injective ρ := by
      intro x y hxy
      cases x <;> cases y <;> simp_all [ρ]
    have hpre := WorkingScheme.diagramEq_precomp (W := P.scheme) A B _ _ ρ hρ hZ1
    convert hpre using 1 <;> funext t <;> cases t <;> rfl

/-- E5 support (no Galois/majority): chart of `B`, power-fixed `χ ≤ seq.τ`, free-root, and
majority-valued Prop 4.9 `q`/`hnat`/`hcoh` (so placement matches moved majority). -/
structure Infra78ChartSupportMixed
    {K : AbstractElementaryClass.{u}} (P : SingleModelData K) (σ : Cardinal.{u})
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hν A)
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
  /-- Stationarity length: `#β + ℵ₀ ≤ χ + ℵ₀ < #κIndex` for majority uniqueness. -/
  hκ : χ + aleph0 < #seq.κIndex
  htestχ : P.g σ + ls K ≤ χ
  eB : (@OrderPresentation.obj K P.E I linOrder nonempty).carrier ≃[K.τ] B.model.carrier
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
    ∃ (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      (∀ i : seq.κIndex,
        P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Z0)
          (seqJoint
            (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
            (fun b => B.occ (eB (params b))))) ∧
      IsMajorityValue seq Z0 hμ B
        (fun t => B.occ (eB (qPres hβ params t)))


/-- Reindexing a majority answer along a parameter map: common good index + uniqueness.
Uses `SameD.comp` (no injectivity of `ι` required). -/
theorem infra_78_majority_reindex_mixed
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (_hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hν A}
    (hνμ : ν ≤ μ) (seq : ApproximationSequence p) (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    {β β' : Type u}
    (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (ι : β' → β) (hβ : #β ≤ seq.τ) (hβ' : #β' ≤ seq.τ)
    (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (Z0' : β' → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
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
    simpa [mk_prod, lift_id, lift_id] using (this.trans_lt seq.concat_bounded).trans_le hνμ
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



/-- **E5d.** After `move_query`, a `Z0`-good approximation pushed along `f` is a majority
value of `seq` on `Z`. Requires `seq.τ + ℵ₀ < #κIndex` so every `≤ τ` query has a good index. -/
theorem infra_78_moved_majority_mixed
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hν A}
    (hνμ : ν ≤ μ) (seq : ApproximationSequence p) (hτν : seq.τ < ν)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hι : #ι ≤ seq.τ) :
    ∃ (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
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
  have hιν : #ι < ν := hι.trans_lt hτν
  obtain ⟨Z0, hmove⟩ := infra_78_move_query_mixed f hf hνμ seq Z hιν
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
theorem infra_78_majority_qPres_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hν A}
    (hνμ : ν ≤ μ) (seq : ApproximationSequence p) (hτν : seq.τ < ν)
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
        ∃ (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
          (∀ i : seq.κIndex,
            P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Z0)
              (seqJoint
                (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
                (fun b => B.occ (eB (params b))))) ∧
          IsMajorityValue seq Z0 hμ B
            (fun t => B.occ (eB (qPres hβ params t)))) := by
  classical
  have hτμ : seq.τ < μ := hτν.trans_le hνμ
  have hex : ∀ {β : Type u} (hβ : #β ≤ seq.τ) (params : β → (P.E.obj I).carrier),
      ∃ (answer : p.idx ⊕ β → (P.E.obj I).carrier)
        (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
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
    obtain ⟨Z0, i, hmove, _, hmaj⟩ := infra_78_moved_majority_mixed f hf hνμ seq hτν hκ Z hβ
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
    have hEqB := infra_78_majority_reindex_mixed f hf hνμ seq hτμ hκ
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
theorem infra_78_chart_support_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible) (hμ : μ ∈ P.eligible)
    (hσμ : Order.succ σ ≤ μ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hν A)
    (hidx : #p.idx ≤ σ)
    (hνμ : ν ≤ μ) (seq : ApproximationSequence p) (hτν : seq.τ < ν)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hχls : ls K + σ < seq.τ) (hpow : seq.τ ^ σ = seq.τ)
    (htestχ : P.g σ + ls K ≤ seq.τ) :
    Nonempty (Infra78ChartSupportMixed (hμ := hμ) P σ f hf p seq) := by
  classical
  have hτμ : seq.τ < μ := hτν.trans_le hνμ
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hκ0 : aleph0 < #seq.κIndex :=
    (self_le_add_left aleph0 seq.τ).trans_lt hκ
  obtain ⟨I, linOrder, nonempty, wf, hIcard, hImem, eB⟩ := infra_610_chart_of_B P hμ B
  have hls : ls K ≤ σ + seq.τ := by
    have h1 : ls K ≤ ls K + σ := le_self_add
    have h2 : ls K + σ ≤ seq.τ := hχls.le
    have h3 : seq.τ ≤ σ + seq.τ := self_le_add_left _ _
    exact h1.trans (h2.trans h3)
  obtain ⟨qPres, hnat, hinr, hcoh, hmajPres⟩ :=
    infra_78_majority_qPres_mixed P σ hσ f hf hνμ seq hτν hκ hImem eB hidx hσlt hls
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
    hκ := hκ
    htestχ := htestχ
    eB := eB
    qPres := qPres
    hnat := hnat
    hinr := hinr
    hcoh := hcoh
    hmajPres := hmajPres
  }⟩


/-- **Done.** μ-hull of Prop 4.9 chart image ∪ `z` inside `E(J)`, with chart factor and
`zN` section. -/
theorem infra_78_placement_mu_hull_mixed
    {P : SingleModelData K} {σ : Cardinal.{u}} (_hσ : aleph0 ≤ σ)
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B)}
    {hf : P.scheme.permitted (X := A) (Y := B) f}
    {p : TupleOver K oneVertexShape P.scheme hν A} {seq : ApproximationSequence p}
    (data : Infra78ChartSupportMixed (hμ := hμ) P σ f hf p seq)
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

/-- **Mixed majority answers are tied** (port of `infra_610_tied_of_majority`; the common move
is `infra_78_common_move_mixed`). -/
theorem infra_78_tied_of_majority_mixed
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f) (hνμ : ν ≤ μ)
    (p : TupleOver K oneVertexShape P.scheme hν A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx)
    (seq : ApproximationSequence p) (hlong : seq.τ + ℵ₀ < #(seq.κIndex))
    (χ : Cardinal.{u}) (hχ : χ ≤ seq.τ)
    (hmaj : ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ χ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A),
        infra_78_isMoveMixed f seq Z Z0 ∧
        IsMajorityValue seq Z0 qB.hν qB.host (infra_612_anchored eB qB.incl qB.val Z))
    (seq' : ApproximationSequence p) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (hlong' : seq'.τ + ℵ₀ < #(seq'.κIndex))
    (hι' : #ι ≤ seq'.τ) (hιχ : #ι ≤ χ) (hιν : #ι < ν)
    (hmv : infra_78_isMoveMixed f seq' Z Z0') :
    P.scheme.DiagramEq (X := p.host) (Y := qB.host)
      (typeJoint (p := p) Z0') (infra_612_anchored eB qB.incl qB.val Z) := by
  obtain ⟨Z0, hmv0, hmaj0⟩ := hmaj Z hιχ
  have hι : #ι ≤ seq.τ := hιχ.trans hχ
  have hκ : #ι + ℵ₀ < #(seq.κIndex) := (add_le_add hι le_rfl).trans_lt hlong
  have hκ' : #ι + ℵ₀ < #(seq'.κIndex) := (add_le_add hι' le_rfl).trans_lt hlong'
  have hans := infra_610_type_eq_majority seq Z0 _ hmaj0 hι hκ
  obtain ⟨Z1, hmv1, hmv1'⟩ := infra_78_common_move_mixed f hf hνμ seq seq' Z hιν
  have h01 := infra_78_moves_agree_mixed f seq Z Z0 Z1 hmv0 hmv1 hι hκ
  have h01' := infra_78_moves_agree_mixed f seq' Z Z0' Z1 hmv hmv1' hι' hκ'
  exact P.scheme.diagram_trans p.host p.host qB.host _ _ _ h01'
    (P.scheme.diagram_trans p.host p.host qB.host _ _ _
      (P.scheme.diagram_symm p.host p.host _ _ h01) hans)

set_option maxHeartbeats 3200000 in
/-- **Tied placement (English §6.2, “an actual tuple in an extension object”).** The
Proposition 4.9 placement `z ∈ E(J)` of the chart prescriptions, in a strong hull `N` of
`E(I) ∪ z` of size `μ`, is a tuple over `B` whose answer on every query `Z` of size at most the
chart arity is the majority prescription on a move of `Z`. -/
theorem infra_78_tied_placement_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible) (hμ : μ ∈ P.eligible) (hσμ : σ < μ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hν A) (hidx : #p.idx ≤ σ)
    (seq : ApproximationSequence p)
    (data : Infra78ChartSupportMixed (hμ := hμ) P σ f hf p seq) :
    ∃ (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx), qB.ν = μ ∧
      ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #ι ≤ seq.τ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A),
          infra_78_isMoveMixed f seq Z Z0 ∧
          IsMajorityValue seq Z0 qB.hν qB.host (infra_612_anchored eB qB.incl qB.val Z) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  haveI := data.wf
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  obtain ⟨J, linJ, nonJ, fIJ, z, hJ, hPlace⟩ :=
    @proposition_4_9 K _ P.E P.D data.I data.linOrder data.nonempty data.wf
      p.idx σ data.χ hσ hidx data.hχls data.hpow data.hImem data.qPres data.hnat data.hcoh
  letI := linJ
  letI := nonJ
  obtain ⟨N, i, j, zN, hN, hcN, hi, hj, hij, hiz⟩ :=
    infra_78_placement_mu_hull_mixed hσ data hidx hσμ (P.E.map fIJ) (P.E.map_strong fIJ) z hJ
  let top : SMObject K μ := SMObject.ofModel N hN hcN
  let φ : N.carrier ≃[K.τ] top.model.carrier := SMObject.ofModelEquiv N hN hcN
  have hφ : K.Strong φ.toEmbedding := strong_of_equiv K φ hN
  have hsB : K.Strong data.eB.symm.toEmbedding := strong_of_equiv K data.eB.symm B.mem
  have hsE : K.Strong data.eB.toEmbedding := strong_of_equiv K data.eB data.hImem
  let embB : Language.Embedding K.τ B.model.carrier top.model.carrier :=
    φ.toEmbedding.comp (j.comp data.eB.symm.toEmbedding)
  have hembB : K.Strong embB := K.strong_trans _ _ (K.strong_trans _ _ hsB hj) hφ
  let qB : TupleOver K oneVertexShape P.scheme hμ B :=
    { ν := μ
      hν := hμ
      host := top
      incl := oneVertexArrow embB hembB
      incl_arrow := trivial
      idx := p.idx
      val := fun a => top.occ (φ (zN a)) }
  refine ⟨qB, Equiv.refl p.idx, rfl, ?_⟩
  intro ι Z hι
  have hιχ : #ι ≤ data.χ := by rw [data.hχτ]; exact hι
  let params : ι → (P.E.obj data.I).carrier := fun k => data.eB.symm (B.val (Z k))
  obtain ⟨Z0, hmove, hmaj⟩ := data.hmajPres hιχ params
  have hZ : (fun b => B.occ (data.eB (params b))) = Z := by
    funext b
    change B.occ (data.eB (data.eB.symm (B.val (Z b)))) = Z b
    rw [show data.eB (data.eB.symm (B.val (Z b))) = B.val (Z b) from
      data.eB.apply_symm_apply _]
    exact SMObject.occ_val B (Z b)
  refine ⟨Z0, ?_, ?_⟩
  · intro k
    have h := hmove k
    rwa [hZ] at h
  -- cardinal bookkeeping
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ
  have hχμ : data.χ < μ := data.hχμ
  have hιμ : #ι < μ := hιχ.trans_lt hχμ
  have hidxμ : #p.idx < μ := hidx.trans_lt hσμ
  have hα : #(p.idx ⊕ ι) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt hμinf hidxμ hιμ
  let ρ : Cardinal.{u} := σ + data.χ
  have hρinf : ℵ₀ ≤ ρ := hσ.trans (self_le_add_right σ data.χ)
  have hρμ : ρ < μ := add_lt_of_lt hμinf hσμ hχμ
  have hjoint : #(p.idx ⊕ ι) ≤ ρ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_le_add hidx hιχ
  have hls : ls K ≤ ρ := by
    have h1 : ls K ≤ ls K + σ := le_self_add
    have h2 : ls K + σ < data.χ := data.hχls
    exact h1.trans (h2.le.trans le_add_self)
  have hIc : Model.card (P.E.obj data.I) = μ :=
    SingleModelData.card_obj_eq (P := P) hμ data.I data.hIcard
  have htρ : P.D.t ρ < μ := P.t_lt hμ hρinf hρμ
  have hcI : P.D.t ρ ≤ Model.card (P.E.obj data.I) := htρ.le.trans hIc.ge
  have hcJ : P.D.t ρ ≤ Model.card (P.E.obj J) :=
    hcI.trans (mk_le_of_injective (P.E.map fIJ).injective)
  have hcN : P.D.t ρ ≤ Model.card N := htρ.le.trans hcN.ge
  have hcT : P.D.t ρ ≤ Model.card top.model := htρ.le.trans top.card.ge
  have hcB : P.D.t ρ ≤ Model.card B.model := htρ.le.trans B.card.ge
  let LN : p.idx ⊕ ι → N.carrier := Sum.elim zN (fun k => j (params k))
  let LJ : p.idx ⊕ ι → (P.E.obj J).carrier :=
    Sum.elim z (fun k => P.E.map fIJ (params k))
  let LQ : p.idx ⊕ ι → (P.E.obj data.I).carrier := data.qPres hιχ params
  let LB : p.idx ⊕ ι → B.model.carrier := fun t => data.eB (LQ t)
  let LT : p.idx ⊕ ι → top.model.carrier := fun t => φ (LN t)
  have s1 : P.D.same hjoint hN top.mem hcN hcT LN LT :=
    P.D.of_strong hjoint hN top.mem hcN hcT LN LT φ.toEmbedding hρinf hφ (fun _ => rfl)
  have s2 : P.D.same hjoint hN hJ hcN hcJ LN LJ := by
    refine P.D.of_strong hjoint hN hJ hcN hcJ LN LJ i hρinf hi ?_
    intro t
    cases t with
    | inl a => exact hiz a
    | inr k => exact hij (params k)
  have s3 := hPlace hιχ params hjoint hcI hcJ
  have s4 : P.D.same hjoint data.hImem hJ hcI hcJ LQ
      (Sum.elim (fun a => P.E.map fIJ (LQ (Sum.inl a)))
        (fun b => P.E.map fIJ (LQ (Sum.inr b)))) := by
    refine P.D.of_strong hjoint data.hImem hJ hcI hcJ _ _ (P.E.map fIJ) hρinf
      (P.E.map_strong fIJ) ?_
    intro t
    cases t <;> rfl
  have s5 : P.D.same hjoint data.hImem B.mem hcI hcB LQ LB :=
    P.D.of_strong hjoint data.hImem B.mem hcI hcB LQ LB data.eB.toEmbedding hρinf hsE
      (fun _ => rfl)
  have sNI : P.D.same hjoint hN data.hImem hcN hcI LN LQ :=
    P.D.trans hjoint hN hJ data.hImem hcN hcJ hcI _ _ _ s2
      (P.D.trans hjoint hJ hJ data.hImem hcJ hcJ hcI _ _ _ s3
        (P.D.symm hjoint data.hImem hJ hcI hcJ _ _ s4))
  have sNB : P.D.same hjoint hN B.mem hcN hcB LN LB :=
    P.D.trans hjoint hN data.hImem B.mem hcN hcI hcB _ _ _ sNI s5
  have sBT : P.D.same hjoint B.mem top.mem hcB hcT LB LT :=
    P.D.trans hjoint B.mem hN top.mem hcB hcN hcT _ _ _
      (P.D.symm hjoint hN B.mem hcN hcB _ _ sNB) s1
  -- relevel to the canonical bound
  have hmaxμ : max #(p.idx ⊕ ι) ℵ₀ < μ := max_lt hα (P.aleph0_lt hμ)
  have htm : P.D.t (max #(p.idx ⊕ ι) ℵ₀) < μ := P.t_lt hμ (le_max_right _ _) hmaxμ
  have hcBm : P.D.t (max #(p.idx ⊕ ι) ℵ₀) ≤ Model.card B.model := htm.le.trans B.card.ge
  have hcTm : P.D.t (max #(p.idx ⊕ ι) ℵ₀) ≤ Model.card top.model :=
    htm.le.trans top.card.ge
  have sBTm := P.D.same_relevel (σ := ρ) (τ := max #(p.idx ⊕ ι) ℵ₀) (σ' := ρ)
    hjoint hρinf (le_max_right _ _) le_rfl (max_le hjoint hρinf) hls B.mem top.mem
    hcB hcT hcB hcT hcBm hcTm LB LT sBT (le_max_left _ _) id
  have hSameD : P.D.SameD B.model top.model LB LT := ⟨B.mem, top.mem, hcBm, hcTm, sBTm⟩
  have hD : P.scheme.DiagramEq (X := B) (Y := top)
      (fun t => B.occ (data.eB (data.qPres hιχ params t)))
      (infra_612_anchored (Equiv.refl p.idx) qB.incl qB.val Z) := by
    have hEq : P.scheme.DiagramEq (X := B) (Y := top) (fun t => B.occ (LB t))
        (fun t => top.occ (LT t)) :=
      (SingleModelData.diagramEq_iff_sameD (P := P) (α := p.idx ⊕ ι) hμ hμ B top
        LB LT hα hα).mpr hSameD
    refine infra_73_diagramEq_of_eq hEq (fun _ => rfl) ?_
    intro t
    cases t with
    | inl a => rfl
    | inr k => rfl
  change # {i : seq.κIndex //
      ¬ P.scheme.DiagramEq (X := A) (Y := top) (seqJoint (seq.family i) Z0)
        (infra_612_anchored (Equiv.refl p.idx) qB.incl qB.val Z)} ≤ _
  have hmono : ∀ i : seq.κIndex,
      ¬ P.scheme.DiagramEq (X := A) (Y := top) (seqJoint (seq.family i) Z0)
        (infra_612_anchored (Equiv.refl p.idx) qB.incl qB.val Z) →
      ¬ P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Z0)
        (fun t => B.occ (data.eB (data.qPres hιχ params t))) := by
    intro i hbad hgood
    exact hbad (P.scheme.diagram_trans A B top _ _ _ hgood hD)
  exact (mk_subtype_mono hmono).trans hmaj

set_option maxHeartbeats 1600000 in
/-- A tied placement whose chart arity is at least a prescribed `λ < μ` (English: “For a larger
desired bounded query size `τ′`, repeat with a power closed bound at least `c(σ, τ′)`”). -/
theorem infra_78_tied_at_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible)
    (hrec : ν ∈ recursionClosedLevels P σ) (hσν : Order.succ σ ≤ ν)
    (hμ : μ ∈ P.eligible) (hνμ : ν ≤ μ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hν A)
    (hpν : p.ν = ν) (hidx : #p.idx ≤ σ) (lam : Cardinal.{u}) (hlam : lam < ν) :
    ∃ (seq : ApproximationSequence p) (qB : TupleOver K oneVertexShape P.scheme hμ B)
      (eB : p.idx ≃ qB.idx), qB.ν = μ ∧ lam ≤ seq.τ ∧ P.g σ + ls K ≤ seq.τ ∧
      seq.τ + ℵ₀ < #(seq.κIndex) ∧ seq.τ < ν ∧
      ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #ι ≤ seq.τ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A),
          infra_78_isMoveMixed f seq Z Z0 ∧
          IsMajorityValue seq Z0 qB.hν qB.host (infra_612_anchored eB qB.incl qB.val Z) := by
  have hσlt : σ < ν := (Order.lt_succ σ).trans_le hσν
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let τ0 : Cardinal.{u} := testCardinal b P.g σ
  have hτ0 : ℵ₀ ≤ τ0 := by
    change ℵ₀ ≤ (2 : Cardinal.{u}) ^ (P.g σ + b + σ + aleph0)
    exact le_trans (cantor aleph0).le
      (power_le_power_left two_ne_zero
        (le_add_self : aleph0 ≤ (P.g σ + b + σ) + aleph0))
  have hexp0 : P.g σ + b + σ + aleph0 < ν := by
    have hg : P.g σ < ν :=
      (hν.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    have hb : b < ν := max_lt (P.ls_lt hν) (P.aleph0_lt hν)
    have h1 : P.g σ + b < ν := add_lt_of_lt (P.aleph0_le hν) hg hb
    have h2 : P.g σ + b + σ < ν := add_lt_of_lt (P.aleph0_le hν) h1 hσlt
    exact add_lt_of_lt (P.aleph0_le hν) h2 (P.aleph0_lt hν)
  have hτ0ν : τ0 < ν :=
    hν.1.working.strongLimit.isStrongPrelimit hexp0
  obtain ⟨χ, hχls, hχν, hpow, hτ0χ', htestχ⟩ :=
    infra_610_choose_chi P σ hσ hν hσlt (max τ0 lam) (max_lt hτ0ν hlam)
  have hτ0χ : τ0 ≤ χ := (le_max_left _ _).trans hτ0χ'
  have hlamχ : lam ≤ χ := (le_max_right _ _).trans hτ0χ'
  let τ : Cardinal.{u} := χ
  let κ : Cardinal.{u} := Order.succ τ
  have hτ : ℵ₀ ≤ τ := hτ0.trans hτ0χ
  have hτν : τ < ν := hχν
  have hκ : ℵ₀ ≤ κ := hτ.trans (Order.le_succ _)
  have hκν : κ < ν :=
    (Order.succ_le_of_lt (cantor τ)).trans_lt
      (hν.1.working.strongLimit.isStrongPrelimit hτν)
  have hprod : κ * #p.idx < ν := by
    have hmul : κ * #p.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    have hκσ : κ * σ = κ := by
      refine mul_eq_left hκ ?_ (aleph0_pos.trans_le hσ).ne'
      have hστ : σ < τ :=
        (lt_of_lt_of_le (cantor σ)
          (power_le_power_left two_ne_zero
            (le_trans (le_add_self : σ ≤ (P.g σ + b) + σ)
              (le_self_add : (P.g σ + b) + σ ≤ ((P.g σ + b) + σ) + aleph0)))).trans_le hτ0χ
      exact hστ.le.trans (Order.le_succ _)
    exact hmul.trans_lt (by rw [hκσ]; exact hκν)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) ν := by
    have hβ : max (max σ τ) (max (ls K) ℵ₀) < ν :=
      max_lt (max_lt hσlt hτν) (max_lt (P.ls_lt hν) (P.aleph0_lt hν))
    exact hrec.2 _ hβ
  obtain ⟨seq, hseqτ, hseqκ⟩ :=
    P.exists_approximationSequence hν A p hpν σ τ κ hσ hσlt hidx hτ hτν hκ hκν hprod hclosed
  have hseqτν : seq.τ < ν := hseqτ ▸ hτν
  have hκIndex : seq.τ + aleph0 < #seq.κIndex := by
    rw [hseqκ, hseqτ, add_eq_left hτ hτ]
    exact Order.lt_succ τ
  have hχls' : ls K + σ < seq.τ := hseqτ ▸ hχls
  have hpow' : seq.τ ^ σ = seq.τ := by rw [hseqτ]; exact hpow
  have htestχ' : P.g σ + ls K ≤ seq.τ := hseqτ ▸ htestχ
  obtain ⟨data⟩ :=
    infra_78_chart_support_mixed P σ hσ hν hμ (hσν.trans hνμ) f hf p hidx hνμ seq hseqτν
      hκIndex hχls' hpow' htestχ'
  obtain ⟨qB, eB, hqν, hmaj⟩ :=
    infra_78_tied_placement_mixed P σ hσ hν hμ (hσlt.trans_le hνμ) f hf p hidx seq data
  exact ⟨seq, qB, eB, hqν, hseqτ ▸ hlamχ, htestχ', hκIndex, hseqτν, hmaj⟩

set_option maxHeartbeats 3200000 in
/-- **Mixed-level tied free lift (proved; English Theorem 6.10 in a mixed-level use).** Along a
permitted arrow `f : A → B` from a recursion-closed level `ν` to a recursion-closed level
`μ ≥ ν`, a bounded type `p` over `A` realized at `ν` has an extension `qB` over `B`, realized at
`μ`, which

* restricts to `p`: on every parameter list `Z` from `A` bounded below `ν`, the joint diagram
  of `qB ↾ A` with `Z` is the joint diagram of `p` with `Z`; and
* is tied free across levels (`IsTiedFreeMixed`): on every move into `A` of a bounded query
  from `B` it answers as `p`.

The witness is the Proposition 4.9 chart placement over `B`'s chart (`infra_78_tied_at_mixed`);
different arities give one Galois type over `B` by Theorem 6.6 at `μ`
(`infra_73_differing_test`), and the restriction clause is tied freeness on the trivial move
`Z ↦ f Z`.  The cross-level Galois identification `SameGaloisType p (qB ↾ A)` (an amalgam of a
`ν`-host with a `μ`-host over `A`) is the separate open tip `infra_78_cross_level_galois`. -/
theorem infra_78_tied_free_lift_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible)
    (hrec : ν ∈ recursionClosedLevels P σ) (hσν : Order.succ σ ≤ ν)
    (hμ : μ ∈ P.eligible) (hrecμ : μ ∈ recursionClosedLevels P σ) (hνμ : ν ≤ μ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hν A)
    (hpν : p.ν = ν) (hidx : #p.idx ≤ σ) :
    ∃ (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx), qB.ν = μ ∧
      (∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
        #β < ν →
        P.scheme.DiagramEq (X := p.host) (Y := qB.host)
          (typeJoint (p := p) Z) (alignJoint eB.symm (typeJoint (p := qB.restrict f hf) Z))) ∧
      IsTiedFreeMixed f p qB eB := by
  classical
  have hσlt : σ < ν := (Order.lt_succ σ).trans_le hσν
  have hσμ : Order.succ σ ≤ μ := hσν.trans hνμ
  have hσltμ : σ < μ := hσlt.trans_le hνμ
  have hidxμ : #p.idx < μ := hidx.trans_lt hσltμ
  have h0ν : (0 : Cardinal.{u}) < ν := aleph0_pos.trans (P.aleph0_lt hν)
  -- placements answer every bounded query they cover by the type of `p`
  have hanswer : ∀ (seqX : ApproximationSequence p) (qX : TupleOver K oneVertexShape P.scheme hμ B)
      (eX : p.idx ≃ qX.idx), seqX.τ + ℵ₀ < #(seqX.κIndex) →
      (∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #ι ≤ seqX.τ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A),
          infra_78_isMoveMixed f seqX Z Z0 ∧
          IsMajorityValue seqX Z0 qX.hν qX.host (infra_612_anchored eX qX.incl qX.val Z)) →
      ∀ (seq' : ApproximationSequence p) {ι : Type u}
        (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
        (Z0' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
        seq'.τ + ℵ₀ < #(seq'.κIndex) → #ι ≤ seq'.τ → #ι ≤ seqX.τ → #ι < ν →
        infra_78_isMoveMixed f seq' Z Z0' →
        P.scheme.DiagramEq (X := p.host) (Y := qX.host)
          (typeJoint (p := p) Z0') (infra_612_anchored eX qX.incl qX.val Z) := by
    intro seqX qX eX hlongX hmajX seq' ι Z Z0' hlong' hι' hιX hιν hmv
    exact infra_78_tied_of_majority_mixed f hf hνμ p qX eX seqX hlongX seqX.τ le_rfl
      (fun Z hZ => hmajX Z hZ) seq' Z Z0' hlong' hι' hιX hιν hmv
  -- two placements covering the test size have one Galois type over `B`
  have hsame : ∀ (seq1 seq2 : ApproximationSequence p)
      (q1 q2 : TupleOver K oneVertexShape P.scheme hμ B) (e1 : p.idx ≃ q1.idx)
      (e2 : p.idx ≃ q2.idx), q1.ν = μ → q2.ν = μ →
      P.g σ + ls K ≤ seq1.τ → P.g σ + ls K ≤ seq2.τ →
      seq1.τ + ℵ₀ < #(seq1.κIndex) → seq2.τ + ℵ₀ < #(seq2.κIndex) →
      (∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #ι ≤ seq1.τ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A),
          infra_78_isMoveMixed f seq1 Z Z0 ∧
          IsMajorityValue seq1 Z0 q1.hν q1.host (infra_612_anchored e1 q1.incl q1.val Z)) →
      (∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #ι ≤ seq2.τ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A),
          infra_78_isMoveMixed f seq2 Z Z0 ∧
          IsMajorityValue seq2 Z0 q2.hν q2.host (infra_612_anchored e2 q2.incl q2.val Z)) →
      SameGaloisType q1 q2 e1.symm e2.symm := by
    intro seq1 seq2 q1 q2 e1 e2 h1ν h2ν ht1 ht2 hl1 hl2 hm1 hm2
    have hidx1 : #q1.idx ≤ σ := by rw [← Cardinal.mk_congr e1]; exact hidx
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ :=
      infra_73_differing_test P σ hσ hμ hrecμ hσμ q1 q2 e1.symm e2.symm h1ν h2ν
        hidx1 (hidx1.trans_lt hσltμ) hneq
    apply hnot
    obtain ⟨seq, -, -, -, -, htest, hlong, hτν, -⟩ :=
      infra_78_tied_at_mixed P σ hσ hν hrec hσν hμ hνμ f hf p hpν hidx 0 h0ν
    have hβτ : #β ≤ seq.τ := hβ.trans htest
    have hβν : #β < ν := hβτ.trans_lt hτν
    obtain ⟨Y0, hmv⟩ := infra_78_move_query_mixed f hf hνμ seq Y hβν
    have d1 := hanswer seq1 q1 e1 hl1 hm1 seq Y Y0 hlong hβτ (hβ.trans ht1) hβν hmv
    have d2 := hanswer seq2 q2 e2 hl2 hm2 seq Y Y0 hlong hβτ (hβ.trans ht2) hβν hmv
    have d := P.scheme.diagram_trans q1.host p.host q2.host _ _ _
      (P.scheme.diagram_symm p.host q1.host _ _ d1) d2
    exact infra_73_diagramEq_of_eq d (fun t => by cases t <;> rfl)
      (fun t => by cases t <;> rfl)
  obtain ⟨seqA, qA, eA, hAν, -, htA, hlA, -, hmA⟩ :=
    infra_78_tied_at_mixed P σ hσ hν hrec hσν hμ hνμ f hf p hpν hidx 0 h0ν
  have hTied : IsTiedFreeMixed f p qA eA := by
    intro seq' ι Z Z0' hlong' hι' hιν hmv
    have hιμ : #ι < μ := hιν.trans_le hνμ
    obtain ⟨seqL, qL, eL, hLν, hιL, htL, hlL, -, hmL⟩ :=
      infra_78_tied_at_mixed P σ hσ hν hrec hσν hμ hνμ f hf p hpν hidx #ι hιν
    have dL := hanswer seqL qL eL hlL hmL seq' Z Z0' hlong' hι' hιL hιν hmv
    have hS := hsame seqA seqL qA qL eA eL hAν hLν htA htL hlA hlL hmA hmL
    have dAL := infra_72_diagramEq_of_sameGalois (P := P) hS Z hAν hLν hidxμ hιμ
    have dAL' : P.scheme.DiagramEq (X := qA.host) (Y := qL.host)
        (infra_612_anchored eA qA.incl qA.val Z) (infra_612_anchored eL qL.incl qL.val Z) :=
      infra_73_diagramEq_of_eq dAL (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    exact P.scheme.diagram_trans p.host qL.host qA.host _ _ _ dL
      (P.scheme.diagram_symm qA.host qL.host _ _ dAL')
  refine ⟨qA, eA, hAν, ?_, hTied⟩
  -- the restriction to `A` answers as `p`: tied freeness on the trivial move `f Z` of `Z`
  intro β Y hβν
  obtain ⟨seqY, -, -, -, hβτ, -, hlY, -, -⟩ :=
    infra_78_tied_at_mixed P σ hσ hν hrec hσν hμ hνμ f hf p hpν hidx #β hβν
  have hmvY : infra_78_isMoveMixed f seqY (pushParams f Y) Y := by
    intro i
    have hcard : #(p.idx ⊕ β) < ν := by
      rw [mk_sum, lift_id, lift_id]
      exact add_lt_of_lt (P.aleph0_le hν) (hidx.trans_lt hσlt) hβν
    have h := P.scheme.diagram_preserved A B f hf (seqJoint (seqY.family i) Y) hcard
      (hcard.trans_le hνμ)
    exact infra_73_diagramEq_of_eq h (fun _ => rfl) (fun t => by cases t <;> rfl)
  have d := hTied seqY (pushParams f Y) Y hlY hβτ hβν hmvY
  refine infra_73_diagramEq_of_eq d (fun _ => rfl) ?_
  intro t
  cases t with
  | inl k =>
    simp only [infra_612_anchored, alignJoint, typeJoint, TupleOver.restrict, Equiv.symm_symm]
  | inr b => rfl

/-- **Theorem 6.6 clause 2 with a large second host (open sub-tip).** At a closed level `μ`,
tuples of length `≤ σ < μ` in a `μ`-sized strong extension `B₀` of `A` and in a strong extension
`B₁` of `A` of any size `≥ μ` are identified in one amalgam over `A` (of size `#B₁`) when their
diagrams agree over the subsets of `A` of size at most `g(σ) + ℓ`.  `ClosedLevel.exists_tuple_amalgam`
is the case `#B₁ = μ`; its proof embeds `B₁` over `A` into a presentation `E(J)` along a
countable tower of submodels of size `< μ` (`exists_strong_embedding_over`), which cannot
exhaust a larger `B₁`. -/
theorem infra_78_tuple_amalgam_large [CategoricalUnbounded K]
    {E : OrderPresentation K} {D : StableDiagram K} {g : Cardinal.{u} → Cardinal.{u}}
    {μ : Cardinal.{u}} (hL : ClosedLevel K E D g μ) {σ : Cardinal.{u}}
    (hσinf : aleph0 ≤ σ) (hσ : σ < μ) {α : Type u} (hα : #α ≤ σ) (A B₀ B₁ : Model K.τ)
    (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
    (f₁ : Language.Embedding K.τ A.carrier B₁.carrier)
    (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier)
    (hA : K.Mem A) (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁) (hf₀ : K.Strong f₀) (hf₁ : K.Strong f₁)
    (hcA : Model.card A = μ) (hc₀ : Model.card B₀ = μ) (hc₁ : μ ≤ Model.card B₁)
    (htest : ∀ {β : Type u} (_ : #β ≤ g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (p : β → A.carrier) (hjoint : #(α ⊕ β) ≤ ρ)
      (h₀ : D.t ρ ≤ Model.card B₀) (h₁ : D.t ρ ≤ Model.card B₁),
      D.same hjoint hB₀ hB₁ h₀ h₁
        (Sum.elim d₀ (fun b => f₀ (p b))) (Sum.elim d₁ (fun b => f₁ (p b)))) :
    ∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
      (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
      K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧ Model.card P = Model.card B₁ ∧
      (∀ x, g₀ (f₀ x) = g₁ (f₁ x)) ∧ ∀ i, g₀ (d₀ i) = g₁ (d₁ i) := by
  sorry

/-- `infra_612_test_of_diagram` with hosts of size at least `μ` (not exactly `μ`). -/
theorem infra_78_test_of_diagram_ge
    {P : SingleModelData K}
    {ν₁ ν₂ : Cardinal.{u}} {hν₁ : ν₁ ∈ P.eligible} {hν₂ : ν₂ ∈ P.eligible}
    {Y₁ : P.scheme.Object ν₁ hν₁} {Y₂ : P.scheme.Object ν₂ hν₂}
    {α : Type u}
    (xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hν₁ Y₁))
    (ys : α → Occurrence K oneVertexShape (P.scheme.asSystem hν₂ Y₂))
    (hDE : P.scheme.DiagramEq (X := Y₁) (Y := Y₂) xs ys)
    (hα₁ : #α < ν₁) (hα₂ : #α < ν₂)
    (μ : Cardinal.{u}) (hμ : μ ∈ P.eligible)
    (hc₁ : μ ≤ Model.card Y₁.model) (hc₂ : μ ≤ Model.card Y₂.model)
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
  have hMc' : P.D.t ρ' ≤ Model.card Y₁.model := (P.t_lt hμ hρ'inf hρ'μ).le.trans hc₁
  have hNc' : P.D.t ρ' ≤ Model.card Y₂.model := (P.t_lt hμ hρ'inf hρ'μ).le.trans hc₂
  exact P.D.same_relevel (σ := ρ0) (τ := ρ) (σ' := ρ')
    (le_max_left _ _) hρ0inf hρinf hρ0le hρle' hls Y₁.mem Y₂.mem hMc hNc hMc' hNc' h₀ h₁
    _ _ hs hjoint ι

/-- **Cross-level Galois identification (proved modulo `infra_78_tuple_amalgam_large`).**
Theorem 6.6 with one host above the base level: if `p` over `A` is realized at the closed level
`ν` and `q` over `A` is realized at any level `≥ ν`, and their joint diagrams agree on every
parameter list from `A` bounded below `ν`, then they have the same Galois type over `A`. -/
theorem infra_78_cross_level_galois
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν : Cardinal.{u}} (hν : ν ∈ P.eligible)
    (hrec : ν ∈ recursionClosedLevels P σ) (hσν : Order.succ σ ≤ ν)
    {A : P.scheme.Object ν hν}
    (p q : TupleOver K oneVertexShape P.scheme hν A) (e : p.idx ≃ q.idx)
    (hidx : #p.idx ≤ σ) (hpν : p.ν = ν) (hqν : ν ≤ q.ν)
    (hD : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      #β < ν →
      P.scheme.DiagramEq (X := p.host) (Y := q.host)
        (typeJoint (p := p) Z) (alignJoint e.symm (typeJoint (p := q) Z))) :
    SameGaloisType p q e (Equiv.refl q.idx) := by
  classical
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  have hL := infra_610_closed_level P σ hσ hν hrec
  have hσlt : σ < ν := (Order.lt_succ σ).trans_le hσν
  have hνinf : aleph0 ≤ ν := P.aleph0_le hν
  have hg : P.g σ < ν := (hν.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
  have hgls : P.g σ + ls K < ν := add_lt_of_lt hνinf hg (P.ls_lt hν)
  have hidxq : #q.idx ≤ σ := (Cardinal.mk_congr e).symm.trans_le hidx
  have hc₀ : Model.card p.host.model = ν := by simpa [hpν] using p.host.card
  have hcq : Model.card q.host.model = q.ν := q.host.card
  have hc₁ : ν ≤ Model.card q.host.model := by rw [hcq]; exact hqν
  have h := infra_612_same_galois_left_large (P := P) q p e.symm σ hσ hσlt hidxq hpν hL
    (by
      intro β hβ ρ hρinf hρν params hjoint h₀ h₁
      let Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A) :=
        fun b => A.occ (params b)
      have hβν : #β < ν := hβ.trans_lt hgls
      have hDE := P.scheme.diagram_symm p.host q.host _ _ (hD Z hβν)
      have hαν : #(p.idx ⊕ β) < ν := hjoint.trans_lt hρν
      have hαq : #(p.idx ⊕ β) < q.ν := hαν.trans_le hqν
      have hαp : #(p.idx ⊕ β) < p.ν := by rw [hpν]; exact hαν
      have h := infra_78_test_of_diagram_ge
        (alignJoint e.symm (typeJoint (p := q) Z)) (typeJoint (p := p) Z) hDE hαq hαp ν hν
        hc₁ hc₀.ge hρinf hρν hjoint id hjoint h₀ h₁
      convert h using 1
      · funext c
        cases c with
        | inl i =>
          simp only [alignJoint, typeJoint, id, Equiv.symm_symm]
          rfl
        | inr b =>
          change q.incl.onVertex PUnit.unit (params b) = q.host.val
            ⟨(Z b).1, q.incl.onVertex (Z b).1 (Z b).2⟩
          rfl
      · funext c
        cases c with
        | inl i => rfl
        | inr b =>
          change p.incl.onVertex PUnit.unit (params b) = p.host.val
            ⟨(Z b).1, p.incl.onVertex (Z b).1 (Z b).2⟩
          rfl)
  exact SameGaloisType.unswap_refl (SameGaloisType.symm h)

end
end
end AEC
