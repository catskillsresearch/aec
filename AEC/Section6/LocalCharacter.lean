module

public import AEC.Section6.AverageDescent
public import Mathlib.SetTheory.Cardinal.Pigeonhole
public import Mathlib.SetTheory.Cardinal.Cofinality.Basic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

@[expose] public section

/-!
# Proposition 6.13 — local character and continuity

Same-level `SingleModelData`. An increasing ordinal chain at one eligible level, with a
joint cover of the union in the sense of `exists_directed_union` (not `HasChainUnions`).
A tuple over the union of length `< cf(δ)` is free from some stage: a Lemma 6.9 code is
trapped in that stage and Lemma 6.11 supplies `IsFreeFrom`. Continuity along a base
`X ≤ A₀` is transitivity of that freeness.

Deferred: mixed levels `ν < μ`, and Section 7 `SatisfiesContinuity`.
-/

namespace AEC
section

universe u

open Cardinal Ordinal FirstOrder Function Set

set_option linter.unusedVariables false

variable {K : AbstractElementaryClass.{u}}

/-! ## Arrows and restrictions -/

theorem SystemArrow.ext {S : SystemShape.{u}} {X Y : SystemObject K S}
    {f g : SystemArrow K S X Y} (h : ∀ v, f.onVertex v = g.onVertex v) : f = g := by
  cases f
  cases g
  rename_i fV fS fC gV gS gC
  have hV : fV = gV := funext h
  subst hV
  congr

theorem SystemArrow.comp_assoc {S : SystemShape.{u}}
    {W X Y Z : SystemObject K S}
    (f : SystemArrow K S W X) (g : SystemArrow K S X Y) (h : SystemArrow K S Y Z) :
    SystemArrow.comp (SystemArrow.comp f g) h =
      SystemArrow.comp f (SystemArrow.comp g h) := by
  apply SystemArrow.ext
  intro _v
  rfl

/-- Push an occurrence along a one-vertex arrow. -/
abbrev pushOcc {X Y : SystemObject K oneVertexShape}
    (f : SystemArrow K oneVertexShape X Y) (x : Occurrence K oneVertexShape X) :
    Occurrence K oneVertexShape Y :=
  ⟨x.1, f.onVertex x.1 x.2⟩

theorem pushOcc_comp {X Y Z : SystemObject K oneVertexShape}
    (f : SystemArrow K oneVertexShape X Y) (g : SystemArrow K oneVertexShape Y Z)
    (x : Occurrence K oneVertexShape X) :
    pushOcc (SystemArrow.comp f g) x = pushOcc g (pushOcc f x) :=
  rfl

theorem seqJoint_pushOcc {idx ι : Type u} {X Y : SystemObject K oneVertexShape}
    (f : SystemArrow K oneVertexShape X Y)
    (v : idx → Occurrence K oneVertexShape X)
    (Z : ι → Occurrence K oneVertexShape X) :
    (fun t => pushOcc f (seqJoint v Z t)) =
      seqJoint (fun j => pushOcc f (v j)) (fun b => pushOcc f (Z b)) := by
  funext t
  cases t <;> rfl

/-- At one level the single-model composition proof is `trivial`, so restrictions
associate on the nose once the underlying arrows do. -/
theorem TupleOver.restrict_comp_single
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := X) (Y := A) g)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B) :
    (q.restrict f hf).restrict g hg =
      q.restrict (SystemArrow.comp g f) (P.scheme.comp g f hg hf) := by
  cases q
  simp only [TupleOver.restrict]
  congr 1

theorem IsFreeFrom.congr_arrow
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f f' : SystemArrow K oneVertexShape
      (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (hf' : P.scheme.permitted (X := A) (Y := B) f')
    (hff : f = f')
    {q : TupleOver K oneVertexShape P.scheme hμ B}
    (h : IsFreeFrom f hf q) : IsFreeFrom f' hf' q := by
  subst hff
  exact h

/-! ## Same-level chains -/

/-- An increasing chain of objects at one eligible level, indexed by a nonzero limit
ordinal, together with a cocone whose legs jointly cover the union. -/
structure SameLevelChain (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) where
  δ : Ordinal.{u}
  hlim : (0 : Ordinal.{u}) < δ ∧ Order.IsSuccLimit δ
  obj : (i : Ordinal.{u}) → i < δ → P.scheme.Object μ hμ
  le : ∀ {i j : Ordinal.{u}} (hi : i < δ) (hj : j < δ), i ≤ j →
    SystemArrow K oneVertexShape
      (P.scheme.asSystem hμ (obj i hi)) (P.scheme.asSystem hμ (obj j hj))
  le_arrow : ∀ {i j : Ordinal.{u}} (hi : i < δ) (hj : j < δ) (hij : i ≤ j),
    P.scheme.permitted (X := obj i hi) (Y := obj j hj) (le hi hj hij)
  le_comp : ∀ {i j k : Ordinal.{u}} (hi : i < δ) (hj : j < δ) (hk : k < δ)
    (hij : i ≤ j) (hjk : j ≤ k),
    SystemArrow.comp (le hi hj hij) (le hj hk hjk) = le hi hk (hij.trans hjk)
  unionObj : P.scheme.Object μ hμ
  toUnion : ∀ (i : Ordinal.{u}) (hi : i < δ),
    SystemArrow K oneVertexShape
      (P.scheme.asSystem hμ (obj i hi)) (P.scheme.asSystem hμ unionObj)
  toUnion_arrow : ∀ i (hi : i < δ),
    P.scheme.permitted (X := obj i hi) (Y := unionObj) (toUnion i hi)
  toUnion_comp : ∀ {i j : Ordinal.{u}} (hi : i < δ) (hj : j < δ) (hij : i ≤ j),
    SystemArrow.comp (le hi hj hij) (toUnion j hj) = toUnion i hi
  joint : ∀ x : Occurrence K oneVertexShape (P.scheme.asSystem hμ unionObj),
    ∃ i : Ordinal.{u}, ∃ hi : i < δ,
      ∃ y : Occurrence K oneVertexShape (P.scheme.asSystem hμ (obj i hi)),
        pushOcc (toUnion i hi) y = x

namespace SameLevelChain

variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}

theorem cof_aleph0 (C : SameLevelChain P hμ) : aleph0 ≤ C.δ.cof :=
  aleph0_le_cof_iff.mpr (one_lt_cof_iff.mpr C.hlim.2)

theorem toUnion_le_apply (C : SameLevelChain P hμ)
    {i j : Ordinal.{u}} (hi : i < C.δ) (hj : j < C.δ) (hij : i ≤ j)
    (y : Occurrence K oneVertexShape (P.scheme.asSystem hμ (C.obj i hi))) :
    pushOcc (C.toUnion j hj) (pushOcc (C.le hi hj hij) y) =
      pushOcc (C.toUnion i hi) y := by
  rw [← pushOcc_comp]
  exact congrArg (fun e => pushOcc e y) (C.toUnion_comp hi hj hij)

/-- A stage and a preimage for one union element. -/
structure PointPre (C : SameLevelChain P hμ)
    (x : Occurrence K oneVertexShape (P.scheme.asSystem hμ C.unionObj)) where
  i : Ordinal.{u}
  hi : i < C.δ
  y : Occurrence K oneVertexShape (P.scheme.asSystem hμ (C.obj i hi))
  push_eq : pushOcc (C.toUnion i hi) y = x

theorem PointPre.nonempty (C : SameLevelChain P hμ)
    (x : Occurrence K oneVertexShape (P.scheme.asSystem hμ C.unionObj)) :
    Nonempty (C.PointPre x) := by
  obtain ⟨i, hi, y, hy⟩ := C.joint x
  exact ⟨⟨i, hi, y, hy⟩⟩

/-- One stage containing a whole row of the chain, with chosen preimages. -/
structure RowPre (C : SameLevelChain P hμ) {idx : Type u}
    (fam : idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ C.unionObj)) where
  i : Ordinal.{u}
  hi : i < C.δ
  pre : idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ (C.obj i hi))
  push_eq : ∀ j, pushOcc (C.toUnion i hi) (pre j) = fam j

end SameLevelChain

/-- Fewer than `cf(δ)` union elements lie in a single stage. -/
theorem infra_613_bounded_in_stage
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    (C : SameLevelChain P hμ) {ι : Type u}
    (t : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ C.unionObj))
    (hι : #ι < C.δ.cof) :
    ∃ i : Ordinal.{u}, ∃ hi : i < C.δ,
      ∃ t0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ (C.obj i hi)),
        ∀ j, pushOcc (C.toUnion i hi) (t0 j) = t j := by
  classical
  let pp : ∀ j, SameLevelChain.PointPre C (t j) :=
    fun j => Classical.choice (SameLevelChain.PointPre.nonempty C (t j))
  let iFun : ι → Ordinal.{u} := fun j => (pp j).i
  have hs : iSup iFun < C.δ :=
    Ordinal.iSup_lt_of_lt_cof hι (fun j => (pp j).hi)
  refine ⟨iSup iFun, hs, fun j =>
    pushOcc (C.le (pp j).hi hs (Ordinal.le_iSup iFun j)) (pp j).y, fun j => ?_⟩
  rw [← (pp j).push_eq]
  exact C.toUnion_le_apply (pp j).hi hs (Ordinal.le_iSup iFun j) (pp j).y

theorem SameLevelChain.rowPre_nonempty
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    (C : SameLevelChain P hμ) {idx : Type u}
    (fam : idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ C.unionObj))
    (hidx : #idx < C.δ.cof) : Nonempty (C.RowPre fam) := by
  obtain ⟨i, hi, t0, ht0⟩ := infra_613_bounded_in_stage C fam hidx
  exact ⟨⟨i, hi, t0, ht0⟩⟩

/-! ## Ordinal spine -/

theorem infra_613_toType_lt {o : Ordinal.{u}} (x : o.ToType) : (x : Ordinal) < o :=
  (ToType.toOrd x).2

theorem infra_613_toType_le {o : Ordinal.{u}} {x y : o.ToType} (h : x ≤ y) :
    (x : Ordinal) ≤ (y : Ordinal) :=
  (ToType.mk (o := o)).symm.le_iff_le.mpr h

theorem infra_613_mk_coe {o : Ordinal.{u}} (i : Set.Iio o) :
    ((ToType.mk i : o.ToType) : Ordinal) = i.1 := by
  change (ToType.toOrd (ToType.mk i)).1 = i.1
  rw [show ToType.toOrd (ToType.mk i) = i from (ToType.mk (o := o)).symm_apply_apply i]

/-! ## Pulling a sequence into a stage -/

theorem infra_613_pull_exceptions
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ B)
    (seq : ApproximationSequence p)
    {S : Set seq.κIndex}
    (family' : ↥S → p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hpush : ∀ s j, pushOcc f (family' s j) = seq.family s.1 j)
    (hidxμ : #p.idx < μ) (hτμ : seq.τ < μ)
    {β : Type u}
    (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hβ : #β ≤ seq.τ) :
    # {s : ↥S //
        ¬ P.scheme.DiagramEq (X := (p.restrict f hf).host) (Y := A)
          (typeJoint (p := p.restrict f hf) Z0) (seqJoint (family' s) Z0)} ≤
      #β + aleph0 := by
  classical
  let pR := p.restrict f hf
  let Zb : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun b => pushOcc f (Z0 b)
  have hjoint : #(p.idx ⊕ β) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hidxμ (hβ.trans_lt hτμ)
  have htype : typeJoint (p := pR) Z0 = typeJoint (p := p) Zb := by
    funext t
    cases t <;> rfl
  have hpres : ∀ s : ↥S,
      P.scheme.DiagramEq (X := A) (Y := B)
        (seqJoint (family' s) Z0) (seqJoint (seq.family s.1) Zb) := by
    intro s
    have hraw := P.scheme.diagram_preserved A B f hf (seqJoint (family' s) Z0) hjoint hjoint
    have hseq : seqJoint (fun j => pushOcc f (family' s j)) Zb =
        seqJoint (seq.family s.1) Zb := by
      have hfam : (fun j => pushOcc f (family' s j)) = seq.family s.1 :=
        funext fun j => hpush s j
      rw [hfam]
    have hform : (fun i =>
        ⟨(seqJoint (family' s) Z0 i).1,
          f.onVertex (seqJoint (family' s) Z0 i).1 (seqJoint (family' s) Z0 i).2⟩) =
        fun i => pushOcc f (seqJoint (family' s) Z0 i) := by
      funext i; rfl
    rw [hform, seqJoint_pushOcc, hseq] at hraw
    exact hraw
  let φ :
      {s : ↥S // ¬ P.scheme.DiagramEq (X := pR.host) (Y := A)
          (typeJoint (p := pR) Z0) (seqJoint (family' s) Z0)} →
      {k : seq.κIndex // ¬ P.scheme.DiagramEq (X := p.host) (Y := B)
          (typeJoint (p := p) Zb) (seqJoint (seq.family k) Zb)} :=
    fun ⟨s, hs⟩ => ⟨s.1, by
      intro hgood
      apply hs
      have hback : P.scheme.DiagramEq (X := p.host) (Y := A)
          (typeJoint (p := p) Zb) (seqJoint (family' s) Z0) :=
        P.scheme.diagram_trans p.host B A
          (typeJoint (p := p) Zb) (seqJoint (seq.family s.1) Zb)
          (seqJoint (family' s) Z0) hgood
          (P.scheme.diagram_symm A B _ _ (hpres s))
      rw [← htype] at hback
      exact hback⟩
  have hφ : Injective φ := by
    rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hv : (φ ⟨s, hs⟩).1 = (φ ⟨s', hs'⟩).1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext hv)
  exact (Cardinal.mk_le_of_injective hφ).trans (seq.few_exceptions Zb hβ)

/-- Majority values of the pulled stage sequence on queries from the union. -/
theorem infra_613_stage_majority
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ B)
    (seq : ApproximationSequence p)
    (seq' : ApproximationSequence (p.restrict f hf))
    (emb : seq'.κIndex ↪ seq.κIndex)
    (hτ : seq'.τ = seq.τ)
    (hpush : ∀ s j, pushOcc f (seq'.family s j) = seq.family (emb s) j)
    {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hι : #ι ≤ seq'.τ) (hιμ : #ι < μ) :
    ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
      IsMajorityValue seq' Z0 p.hν p.host (typeJoint (p := p) Z) := by
  classical
  obtain ⟨Z0, hmove⟩ := infra_610_move_query f hf seq' Z hι hιμ
  have hιseq : #ι ≤ seq.τ := hτ ▸ hι
  let φ :
      {s : seq'.κIndex // ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq'.family s) Z0) (typeJoint (p := p) Z)} →
      {k : seq.κIndex // ¬ P.scheme.DiagramEq (X := p.host) (Y := B)
          (typeJoint (p := p) Z) (seqJoint (seq.family k) Z)} :=
    fun ⟨s, hs⟩ => ⟨emb s, by
      intro hgood
      apply hs
      have hfam : (fun j => pushOcc f (seq'.family s j)) = seq.family (emb s) :=
        funext fun j => hpush s j
      have hmove' : P.scheme.DiagramEq (X := A) (Y := B)
          (seqJoint (seq'.family s) Z0) (seqJoint (seq.family (emb s)) Z) := by
        have hrew := hmove s
        have hseq : seqJoint
            (fun j => ⟨(seq'.family s j).1,
              f.onVertex (seq'.family s j).1 (seq'.family s j).2⟩) Z =
            seqJoint (seq.family (emb s)) Z := by
          congr 1
        rw [hseq] at hrew
        exact hrew
      exact P.scheme.diagram_trans A B p.host
        (seqJoint (seq'.family s) Z0) (seqJoint (seq.family (emb s)) Z)
        (typeJoint (p := p) Z) hmove'
        (P.scheme.diagram_symm p.host B _ _ hgood)⟩
  have hφ : Injective φ := by
    rintro ⟨s, _⟩ ⟨s', _⟩ h
    exact Subtype.ext (emb.inj' (congrArg Subtype.val h))
  refine ⟨Z0, ?_⟩
  exact (Cardinal.mk_le_of_injective hφ).trans (seq.few_exceptions Z hιseq)

/-! ## Trap -/

theorem infra_613_trap_in_stage
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    (C : SameLevelChain P hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ C.unionObj)
    (seq : ApproximationSequence p)
    (hidxCof : #p.idx < C.δ.cof) (hidxμ : #p.idx < μ) (hτμ : seq.τ < μ)
    (hprod : #seq.κIndex * #p.idx < μ) (hlen : seq.τ + aleph0 < #seq.κIndex)
    (hκμ : #seq.κIndex < μ) (hreg : (#seq.κIndex).IsRegular)
    (hside : #seq.κIndex < C.δ.cof ∨ C.δ.cof < #seq.κIndex) :
    ∃ i : Ordinal.{u}, ∃ hi : i < C.δ,
      ∃ seq' : ApproximationSequence
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)),
        ∃ emb : seq'.κIndex ↪ seq.κIndex,
          seq'.τ = seq.τ ∧
          seq.τ + aleph0 < #seq'.κIndex ∧
          #seq'.κIndex < μ ∧
          ∀ s j, pushOcc (C.toUnion i hi) (seq'.family s j) = seq.family (emb s) j := by
  classical
  rcases hside with hsmall | hbig
  · -- The whole concatenation is shorter than the cofinality.
    let t : seq.κIndex × p.idx →
        Occurrence K oneVertexShape (P.scheme.asSystem hμ C.unionObj) :=
      fun ij => seq.family ij.1 ij.2
    have hpair : #(seq.κIndex × p.idx) < C.δ.cof := by
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.mul_lt_of_lt C.cof_aleph0 hsmall hidxCof
    obtain ⟨i, hi, t0, ht0⟩ := infra_613_bounded_in_stage C t hpair
    let S : Set seq.κIndex := univ
    let family' : ↥S → p.idx →
        Occurrence K oneVertexShape (P.scheme.asSystem hμ (C.obj i hi)) :=
      fun s j => t0 ⟨s.1, j⟩
    have hpush : ∀ s j, pushOcc (C.toUnion i hi) (family' s j) = seq.family s.1 j :=
      fun s j => ht0 ⟨s.1, j⟩
    have hSmk : #↥S = #seq.κIndex := Cardinal.mk_univ
    let seq' : ApproximationSequence
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) :=
      { τ := seq.τ
        κIndex := ↥S
        family := family'
        concat_bounded := by
          rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, hSmk]
          exact hprod
        few_exceptions := fun {β} Z0 hβ =>
          infra_613_pull_exceptions (C.toUnion i hi) (C.toUnion_arrow i hi) p seq
            family' hpush hidxμ hτμ Z0 hβ }
    let emb : seq'.κIndex ↪ seq.κIndex := Embedding.subtype (· ∈ S)
    refine ⟨i, hi, seq', emb, rfl, ?_, ?_, ?_⟩
    · rw [hSmk]; exact hlen
    · rw [hSmk]; exact hκμ
    · intro s j
      have hs : emb s = s.1 := rfl
      have hf : seq'.family s j = family' s j := rfl
      rw [hs, hf]
      exact hpush s j
  · -- Cofinality is small: pigeonhole the copies along a cofinal spine.
    let rp : ∀ k : seq.κIndex, C.RowPre (seq.family k) :=
      fun k => Classical.choice (C.rowPre_nonempty (seq.family k) hidxCof)
    obtain ⟨spineSet, hcofSet, hcardSet⟩ := Order.exists_cof_eq C.δ.ToType
    have hcardCof : #spineSet = C.δ.cof := by
      rw [hcardSet, cof_toType]
    have hreach : ∀ x : C.δ.ToType, ∃ y : ↥spineSet, x ≤ y.1 := fun x => by
      obtain ⟨y, hy, hle⟩ := hcofSet x
      exact ⟨⟨y, hy⟩, hle⟩
    choose spine hge using fun k =>
      hreach (ToType.mk ⟨(rp k).i, (rp k).hi⟩)
    have hspineCard : #↥spineSet < (#seq.κIndex).ord.cof := by
      rw [hcardCof, hreg.cof_ord]
      exact hbig
    obtain ⟨a, ha⟩ :=
      infinite_pigeonhole spine hreg.aleph0_le hspineCard
    let S : Set seq.κIndex := spine ⁻¹' {a}
    have hSmk : #↥S = #seq.κIndex := ha
    let i : Ordinal.{u} := (a.1 : Ordinal)
    have hi : i < C.δ := infra_613_toType_lt a.1
    have hle_stage : ∀ s : ↥S, (rp s.1).i ≤ i := by
      intro s
      have hsp : spine s.1 = a := s.2
      have hord : ((spine s.1).1 : Ordinal) = i := by
        have hv : (spine s.1).1 = a.1 := congrArg Subtype.val hsp
        exact congrArg (fun z : C.δ.ToType => (z : Ordinal)) hv
      have hcoe := infra_613_toType_le (hge s.1)
      have hmk := infra_613_mk_coe ⟨(rp s.1).i, (rp s.1).hi⟩
      calc (rp s.1).i
          = ((ToType.mk ⟨(rp s.1).i, (rp s.1).hi⟩ : C.δ.ToType) : Ordinal) := hmk.symm
        _ ≤ ((spine s.1).1 : Ordinal) := hcoe
        _ = i := hord
    let family' : ↥S → p.idx →
        Occurrence K oneVertexShape (P.scheme.asSystem hμ (C.obj i hi)) :=
      fun s j =>
        pushOcc (C.le (rp s.1).hi hi (hle_stage s)) ((rp s.1).pre j)
    have hpush : ∀ s j, pushOcc (C.toUnion i hi) (family' s j) = seq.family s.1 j := by
      intro s j
      rw [show family' s j =
          pushOcc (C.le (rp s.1).hi hi (hle_stage s)) ((rp s.1).pre j) from rfl]
      rw [C.toUnion_le_apply (rp s.1).hi hi (hle_stage s)]
      exact (rp s.1).push_eq j
    let seq' : ApproximationSequence
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) :=
      { τ := seq.τ
        κIndex := ↥S
        family := family'
        concat_bounded := by
          rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, hSmk]
          exact hprod
        few_exceptions := fun {β} Z0 hβ =>
          infra_613_pull_exceptions (C.toUnion i hi) (C.toUnion_arrow i hi) p seq
            family' hpush hidxμ hτμ Z0 hβ }
    let emb : seq'.κIndex ↪ seq.κIndex := Embedding.subtype (· ∈ S)
    refine ⟨i, hi, seq', emb, rfl, ?_, ?_, ?_⟩
    · rw [hSmk]; exact hlen
    · rw [hSmk]; exact hκμ
    · intro s j
      have hs : emb s = s.1 := rfl
      have hf : seq'.family s j = family' s j := rfl
      rw [hs, hf]
      exact hpush s j

/-! ## Local character -/

theorem infra_613_local
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    (C : SameLevelChain P hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ C.unionObj)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hcof : #p.idx < C.δ.cof) :
    ∃ i : Ordinal.{u}, ∃ hi : i < C.δ,
      IsFreeFrom (C.toUnion i hi) (C.toUnion_arrow i hi) p := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #p.idx < μ := hidx.trans_lt hσlt
  let τ : Cardinal.{u} := aleph0
  have hτ : aleph0 ≤ τ := le_rfl
  have hτμ : τ < μ := P.aleph0_lt hμ
  have hclosed₀ : infra_69_pad_recursion_closed σ (max (ls K) aleph0)
      (max (max σ τ) (max (ls K) aleph0)) μ := by
    apply hrec.2
    exact max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
  suffices ∃ κ : Cardinal.{u}, aleph0 ≤ κ ∧ κ < μ ∧ κ.IsRegular ∧
      κ * #p.idx < μ ∧ τ + aleph0 < κ ∧
      (#(κ.ord.ToType) < C.δ.cof ∨ C.δ.cof < κ) by
    obtain ⟨κ, hκinf, hκμ, hregκ, hprodκ, hlenκ, hsideκ⟩ := this
    obtain ⟨seq, hseqτ, hseqκ⟩ :=
      P.exists_approximationSequence hμ C.unionObj p hνμ σ τ κ hσ hσlt hidx hτ hτμ
        hκinf hκμ hprodκ hclosed₀
    have hreg : (#seq.κIndex).IsRegular := by
      rw [hseqκ]; exact hregκ
    have hprod : #seq.κIndex * #p.idx < μ := by
      rw [hseqκ]; exact hprodκ
    have hlen : seq.τ + aleph0 < #seq.κIndex := by
      rw [hseqτ, hseqκ]; exact hlenκ
    have hseqμ : #seq.κIndex < μ := by rw [hseqκ]; exact hκμ
    have hside : #seq.κIndex < C.δ.cof ∨ C.δ.cof < #seq.κIndex := by
      rw [hseqκ]
      rcases hsideκ with h | h
      · -- `#κ.ord.ToType = κ`, so the bound is on `κ`.
        have hto : #(κ.ord.ToType) = κ := Cardinal.mk_ord_toType κ
        rw [hto] at h
        exact Or.inl h
      · exact Or.inr h
    obtain ⟨i, hi, seq', emb, hτeq, hlen', hκμ', hpush⟩ :=
      infra_613_trap_in_stage C p seq hcof hidxμ (hseqτ.symm ▸ hτμ) hprod hlen hseqμ hreg
        hside
    have hmaj : ∀ {ι : Type u}
        (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ C.unionObj)),
        #ι ≤ seq'.τ →
        ∃ Z0, IsMajorityValue seq' Z0 p.hν p.host (typeJoint (p := p) Z) := by
      intro ι Z hι
      exact infra_613_stage_majority (C.toUnion i hi) (C.toUnion_arrow i hi) p seq seq'
        emb hτeq hpush Z hι (hι.trans_lt (hτeq.symm ▸ hseqτ.symm ▸ hτμ))
    exact ⟨i, hi, infra_611_isFreeFrom P σ hσ hμ hrec hσSucc
      (C.toUnion i hi) (C.toUnion_arrow i hi) p seq' hνμ hidx hidxμ
      (hτeq.symm ▸ hseqτ.symm ▸ hτμ) (hτeq.symm ▸ hlen') hκμ' hmaj⟩
  by_cases hcfμ : C.δ.cof < μ
  · let ρ : Cardinal.{u} := max τ (max #p.idx C.δ.cof)
    have hρinf : aleph0 ≤ ρ := le_max_left _ _
    have hρμ : ρ < μ := max_lt hτμ (max_lt hidxμ hcfμ)
    let κ : Cardinal.{u} := Order.succ ρ
    have hκinf : aleph0 ≤ κ := hρinf.trans (Order.le_succ _)
    have hκμ : κ < μ :=
      (Order.succ_le_of_lt (cantor ρ)).trans_lt
        (hμ.1.working.strongLimit.isStrongPrelimit hρμ)
    have hregκ : κ.IsRegular := isRegular_succ hρinf
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
    have hlenκ : τ + aleph0 < κ := by
      have hsum : τ + aleph0 = τ := add_eq_left hτ hτ
      rw [hsum]
      exact (le_max_left _ _).trans_lt (Order.lt_succ ρ)
    have hside : #(κ.ord.ToType) < C.δ.cof ∨ C.δ.cof < κ :=
      Or.inr (((le_max_right #p.idx C.δ.cof).trans (le_max_right τ _)).trans_lt
        (Order.lt_succ ρ))
    exact ⟨κ, hκinf, hκμ, hregκ, hprodκ, hlenκ, hside⟩
  · let ρ : Cardinal.{u} := max τ #p.idx
    have hρinf : aleph0 ≤ ρ := le_max_left _ _
    have hρμ : ρ < μ := max_lt hτμ hidxμ
    let κ : Cardinal.{u} := Order.succ ρ
    have hκinf : aleph0 ≤ κ := hρinf.trans (Order.le_succ _)
    have hκμ : κ < μ :=
      (Order.succ_le_of_lt (cantor ρ)).trans_lt
        (hμ.1.working.strongLimit.isStrongPrelimit hρμ)
    have hregκ : κ.IsRegular := isRegular_succ hρinf
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
    have hlenκ : τ + aleph0 < κ := by
      have hsum : τ + aleph0 = τ := add_eq_left hτ hτ
      rw [hsum]
      exact (le_max_left _ _).trans_lt (Order.lt_succ ρ)
    have hside : #(κ.ord.ToType) < C.δ.cof ∨ C.δ.cof < κ := by
      left
      rw [Cardinal.mk_ord_toType]
      exact hκμ.trans_le (le_of_not_gt hcfμ)
    exact ⟨κ, hκinf, hκμ, hregκ, hprodκ, hlenκ, hside⟩

/-! ## Transitivity -/

/-- Type-joint transitivity at one level. A code in `X` that computes `q ↾ A`, and a code
in `A` that computes `q`, together compute `q` from `X`. Lemma 6.11 turns that into
`IsFreeFrom`. -/
theorem infra_613_strong_trans
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {X A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := X) (Y := A) g)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hνμ : q.ν = μ) (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (seqA : ApproximationSequence (q.restrict f hf))
    (hκA : seqA.τ + aleph0 < #seqA.κIndex)
    (hmajA : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seqA.τ →
      ∃ ZA : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seqA ZA q.hν q.host (typeJoint (p := q) Z))
    (seqX : ApproximationSequence ((q.restrict f hf).restrict g hg))
    (hτle : seqX.τ ≤ seqA.τ)
    (hτXμ : seqX.τ < μ)
    (hκX : seqX.τ + aleph0 < #seqX.κIndex)
    (hκXμ : #seqX.κIndex < μ)
    (hmajX : ∀ {ι : Type u}
      (ZA : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #ι ≤ seqX.τ →
      ∃ ZX : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ X),
        IsMajorityValue seqX ZX (q.restrict f hf).hν (q.restrict f hf).host
          (typeJoint (p := q.restrict f hf) ZA)) :
    IsFreeFrom (SystemArrow.comp g f) (P.scheme.comp g f hg hf) q := by
  let hcomp := P.scheme.comp g f hg hf
  have hincl : ((q.restrict f hf).restrict g hg).incl =
      (q.restrict (SystemArrow.comp g f) hcomp).incl :=
    (SystemArrow.comp_assoc g f q.incl).symm
  let seqR : ApproximationSequence (q.restrict (SystemArrow.comp g f) hcomp) :=
    { τ := seqX.τ
      κIndex := seqX.κIndex
      family := seqX.family
      concat_bounded := seqX.concat_bounded
      few_exceptions := fun {β} Z hβ => by
        have hty : typeJoint (p := (q.restrict f hf).restrict g hg) Z =
            typeJoint (p := q.restrict (SystemArrow.comp g f) hcomp) Z := by
          funext t
          cases t <;> rfl
        rw [← hty]
        exact seqX.few_exceptions Z hβ }
  have hmajR : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seqR.τ →
      ∃ ZX : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ X),
        IsMajorityValue seqR ZX q.hν q.host (typeJoint (p := q) Z) := by
    intro ι Z hι
    have hιA : #ι ≤ seqA.τ := hι.trans hτle
    obtain ⟨ZA, hZA⟩ := hmajA Z hιA
    have hP : IsMajorityValue seqA ZA (q.restrict f hf).hν (q.restrict f hf).host
        (typeJoint (p := q.restrict f hf) ZA) :=
      infra_610_majority_eq_type seqA ZA hιA
    have hbound : #ι + aleph0 < #seqA.κIndex := (add_le_add hιA le_rfl).trans_lt hκA
    have hEq := infra_610_majority_unique seqA ZA
      (typeJoint (p := q.restrict f hf) ZA) (typeJoint (p := q) Z) hP hZA hbound
    obtain ⟨ZX, hZX⟩ := hmajX ZA hι
    exact ⟨ZX, infra_611_majority_transport seqX ZX
      (typeJoint (p := q.restrict f hf) ZA) (typeJoint (p := q) Z) hZX hEq⟩
  exact infra_611_isFreeFrom P σ hσ hμ hrec hσSucc
    (SystemArrow.comp g f) hcomp q seqR hνμ hidx hidxμ hτXμ hκX hκXμ hmajR

/-- Same-level E11. `IsFreeFrom` along `A → B` and along `X → A` give `IsFreeFrom`
along `X → B`. The base code is the one carried by freeness from `X`; its majority
witness is a majority value in the common host, which is what the Lean `IsFreeLift`
clause asks for. -/
theorem infra_613_freeFrom_trans
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := X) (Y := A) g)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hXA : IsFreeFrom g hg (q.restrict f hf))
    (_hAB : IsFreeFrom f hf q) :
    IsFreeFrom (SystemArrow.comp g f) (P.scheme.comp g f hg hf) q := by
  rcases hXA with ⟨pX, eX, hSG, seqX, hmajX⟩
  refine ⟨pX, eX, ?_, seqX, ?_⟩
  · rcases hSG with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    have hincl : ((q.restrict f hf).restrict g hg).incl =
        (q.restrict (SystemArrow.comp g f) (P.scheme.comp g f hg hf)).incl :=
      (SystemArrow.comp_assoc g f q.incl).symm
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, ?_, ?_⟩
    · intro v
      exact hcomm v
    · intro i
      exact hval i
  · intro ι Z hι
    classical
    have hne : Nonempty ((P.scheme.asSystem hμ A).obj PUnit.unit).carrier := by
      have hc : Model.card ((P.scheme.asSystem hμ A).obj PUnit.unit) = μ :=
        P.scheme.vertex_card hμ A PUnit.unit
      have hμ0 : μ ≠ 0 := (aleph0_pos.trans_le (P.aleph0_le hμ)).ne'
      rw [← Cardinal.mk_ne_zero_iff]
      rw [show #((P.scheme.asSystem hμ A).obj PUnit.unit).carrier =
          Model.card ((P.scheme.asSystem hμ A).obj PUnit.unit) from rfl, hc]
      exact hμ0
    let ZA : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
      fun _ => ⟨PUnit.unit, Classical.choice hne⟩
    obtain ⟨Z0, xs, hxs⟩ := hmajX ZA hι
    exact ⟨Z0, xs, hxs⟩

theorem infra_613_cocone_arrow
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    (C : SameLevelChain P hμ)
    {X : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape
      (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ (C.obj 0 C.hlim.1)))
    {i : Ordinal.{u}} (hi : i < C.δ) :
    SystemArrow.comp
        (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        (C.toUnion i hi) =
      SystemArrow.comp g (C.toUnion 0 C.hlim.1) := by
  rw [SystemArrow.comp_assoc, C.toUnion_comp C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)]

/-- Local character supplies a stage; freeness of that stage's restriction from `X`
transfers to the union along the cocone. -/
theorem infra_613_continuity
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    (C : SameLevelChain P hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ C.unionObj)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hcof : #p.idx < C.δ.cof)
    (X : P.scheme.Object μ hμ)
    (g : SystemArrow K oneVertexShape
      (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ (C.obj 0 C.hlim.1)))
    (hg : P.scheme.permitted (X := X) (Y := C.obj 0 C.hlim.1) g)
    (hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsFreeFrom
        (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        (P.scheme.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hg
          (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi))) :
    IsFreeFrom (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
      (P.scheme.comp g (C.toUnion 0 C.hlim.1) hg (C.toUnion_arrow 0 C.hlim.1)) p := by
  obtain ⟨i, hi, hF⟩ := infra_613_local P σ hσ hμ hrec hσSucc C p hνμ hidx hcof
  have hzero : (0 : Ordinal.{u}) ≤ i := bot_le
  let gA := SystemArrow.comp g (C.le C.hlim.1 hi hzero)
  have hgA := P.scheme.comp g (C.le C.hlim.1 hi hzero) hg (C.le_arrow C.hlim.1 hi hzero)
  have htrans := infra_613_freeFrom_trans gA hgA (C.toUnion i hi) (C.toUnion_arrow i hi) p
    (hAll i hi) hF
  have harr := infra_613_cocone_arrow C g hi
  exact IsFreeFrom.congr_arrow _ _ harr htrans

end
end AEC
