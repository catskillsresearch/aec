module

public import AEC.Section6.ApproximationSequence
public import AEC.Section6.ParameterOrbits
public import AEC.Section5.PackageClauses
public import AEC.Section5.Results

@[expose] public section

/-!
# Uniform approximation sequences (Lemma 6.9)

English support-copy: rich padded chart (Lemmas 5.5, 5.4), placement (Lemma 6.5),
block repetition (Lemma 4.6), parameter orbits (Lemma 6.1). The proved engine builds
constant `κ`-families for `tp(v/A)` in the base (`TupleOver.InBase`). Cross-level hosts
and `κ` distinct approximants remain open; see `HOLES.md`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}

/-- Dense rich order of size `2^η` (Lemma 5.5, first clause). -/
theorem exists_denseRichOrder (η : Cardinal.{u}) (hη : aleph0 ≤ η) :
    ∃ (Q : Type u) (_ : LinearOrder Q),
      #Q = (2 : Cardinal.{u}) ^ η ∧
      (∀ a b : Q, a < b → ∃ c, a < c ∧ c < b) ∧
      (∀ a : Q, ∃ b, b < a) ∧ (∀ a : Q, ∃ c, a < c) ∧
      ∀ (L R : Set Q), #L ≤ η → #R ≤ η → (∀ a ∈ L, ∀ b ∈ R, a < b) →
        ∃ x : Q, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b) :=
  (lemma_5_5 η hη).1

/-- Rich padded order at a strong limit (Lemma 5.5, second clause). -/
theorem exists_richPaddedOrder (η : Cardinal.{u}) (hη : aleph0 ≤ η)
    {μ : Cardinal.{u}} (hμ : μ.IsStrongLimit) (hημ : η < μ) :
    ∃ (I : Type u) (_ : LinearOrder I) (_ : IsPadded I),
      #I = μ ∧
      (∀ a b : I, a < b → ∃ c, a < c ∧ c < b) ∧
      ∀ (L R : Set I), #L ≤ η → #R ≤ η → (∀ a ∈ L, ∀ b ∈ R, a < b) →
        ∃ x : I, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b) :=
  (lemma_5_5 η hη).2 μ hμ hημ

/-- At level `μ`, data in the base with reflexive inclusion (in-base actual type). -/
structure TupleOver.InBase {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible}
    {base : W.Object μ hμ} where
  idx : Type u
  val : idx → Occurrence K S (W.asSystem hμ base)
  hincl : W.permitted (X := base) (Y := base) (SystemArrow.refl (W.asSystem hμ base))

/-- The corresponding `TupleOver` for `InBase` data. -/
def TupleOver.InBase.toOver {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible}
    {base : W.Object μ hμ} (d : TupleOver.InBase (base := base)) :
    TupleOver K S W hμ base :=
  ⟨μ, hμ, base, SystemArrow.refl (W.asSystem hμ base), d.hincl, d.idx, d.val⟩

/-- Constant `κ`-sequence with the same realizing tuple at every index. -/
def ApproximationSequence.ofConstFamily
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    (p : TupleOver K S W hμ base) {κ τ : Cardinal.{u}}
    (κIndex : Type u) (hκ : #κIndex = κ)
    (f : p.idx → Occurrence K S (W.asSystem hμ base))
    (hconcat : #(κIndex × p.idx) < μ)
    (hreal : ∀ {ι : Type u} (Z : ι → Occurrence K S (W.asSystem hμ base)),
      #ι ≤ τ →
        W.DiagramEq (X := p.host) (Y := base)
          (typeJoint (p := p) Z) (seqJoint f Z)) :
    ApproximationSequence p where
  τ := τ
  κIndex := κIndex
  family := fun _ => f
  concat_bounded := hconcat
  few_exceptions := by
    intro ι Z hι
    have h0 :
        #{i : κIndex // ¬ W.DiagramEq (X := p.host) (Y := base)
            (typeJoint (p := p) Z) (seqJoint f Z)} = 0 := by
      rw [Cardinal.mk_eq_zero_iff, isEmpty_subtype]
      intro i h
      exact h (hreal (ι := ι) (Z := Z) hι)
    rw [h0]
    simp

/-- Uniform approximation sequences for in-base types (English support-copy packaging). -/
theorem WorkingScheme.exists_approximationSequence
    [CategoricalUnbounded K] (_F : TermTemplate K S) [_hpres : HasPresentations W _F]
    [_hpack : HasChainUnions W]
    (_hedge : ∀ i j, ¬ S.specified i j)
    (_hcat : ∀ μ' ∈ W.eligible, Categorical K μ')
    (_σ _χ _b τ κ : Cardinal.{u})
    (_hσ : aleph0 ≤ _σ) (_hτ : aleph0 ≤ τ) (_hκ : aleph0 ≤ κ)
    (_hpow : _χ ^ _σ = _χ) (_hb : _b + _σ < _χ)
    (_hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ _σ) ≤ _χ)
    (_hiso : AssemblesStructIso W _b)
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} (base : W.Object μ hμ)
    (d : TupleOver.InBase (base := base))
    (_hidx : #d.idx ≤ _σ) (_hidxμ : #d.idx < μ)
    (_hμτ : τ < μ) (_hκμ : κ < μ) (hμκ : κ * #d.idx < μ)
    (_hχμ : _χ < μ) :
    ∃ seq : ApproximationSequence (d.toOver), seq.τ = τ ∧ #(seq.κIndex) = κ := by
  -- Constant family: for in-base `d`, `typeJoint Z = seqJoint d.val Z`, so every index is good.
  -- English support-copy (rich chart, placement, block regions, orbits) is not used here.
  let p : TupleOver K S W hμ base :=
    ⟨μ, hμ, base, SystemArrow.refl (W.asSystem hμ base), d.hincl, d.idx, d.val⟩
  let κIndex := κ.out
  have hκIndex : #κIndex = κ := Cardinal.mk_out κ
  have hconcat : #(κIndex × d.idx) < μ := by
    simpa [hκIndex, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id] using hμκ
  have hjoint : ∀ (ι : Type u) (Z : ι → Occurrence K S (W.asSystem hμ base)),
      typeJoint (p := p) Z = seqJoint d.val Z := by
    intro ι Z
    funext x
    cases x with
    | inl i => rfl
    | inr j => rfl
  refine ⟨ApproximationSequence.ofConstFamily p (κ := κ) (τ := τ) κIndex hκIndex d.val hconcat
    (by
      intro ι Z hιZ
      rw [← hjoint ι Z]
      exact W.diagram_refl (X := base) (typeJoint (p := p) Z)),
    rfl, hκIndex⟩

end
end AEC
