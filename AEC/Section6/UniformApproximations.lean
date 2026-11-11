module

public import AEC.Section6.ApproximationSequence
public import AEC.Section6.ParameterOrbits
public import AEC.Section5.PackageClauses
public import AEC.Section5.Results

@[expose] public section

/-!
# Uniform approximation sequences (Lemma 6.9)

1:1 Lean gloss of the English support-copy proof (eventual.pdf §6.2; see also Lemma 5.5.md
equivalence clause).

English steps:

1. By the rich-order and padding constructions of Lemmas 5.5 and 5.4, present `A` on a padded
   chart (`exists_denseRichOrder`, `exists_richPaddedOrder`, `lemma_5_4`).
2. Lemma 6.5 / compact placement places `p = tp(v/A)` at query size `τ`.
3. Keep shared old-chart supports; partition other supports by cuts; anchors have size at most
   `σ + ℵ₀`.
4. In each anchor slot, choose `κ` pairwise disjoint convex regions and put a copy of the
   pattern; richness realizes the needed order patterns (English: Lemma 5.5 equivalence).
5. If supports avoid every region, Lemma 6.1 gives `D(vᵢ,Z) = p↾Z` for all but at most
   `|Z|+ℵ₀` indices; block interchange (Lemma 4.6) for the copy-region bookkeeping.
6. Assemble an `ApproximationSequence` (bounded concatenation, `few_exceptions`, subtuples).

Step 4 uses `english_orderPattern_realized_over_old` (cut filling ⇒ pattern realization;
embedding construction in `order_pattern_realized_over_old` may still be pinned). The constant-family
helpers `TupleOver.InBase` / `ApproximationSequence.ofConstFamily` are **not** used for
Lemma 6.9 (they do not discharge English support-copy).
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}

/-! ## Lemma 5.5 exports (English step 1) -/

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

/-! ## English step 4 — pattern richness (Lemma 5.5 equivalence) -/

/-- English Lemma 5.5 (equivalence): "every extension of an order pattern with at most η old and
at most η added positions can be realized over its old positions."

On any `Q` with `η`-bounded cut filling (`OrderFillsCuts`), use
`orderPatternRealized_of_fillsCuts` (`AEC/Section5/OrderPatternRealization.lean`). Rich padded
charts from step 1 satisfy cut filling via `lemma_5_5`. -/
abbrev EnglishOrderPatternRealized (η : Cardinal.{u}) : Prop :=
  ∀ {Q : Type u} [LinearOrder Q], OrderFillsCuts η Q → OrderPatternRealized η Q

theorem english_orderPattern_realized_over_old (η : Cardinal.{u}) (hη : aleph0 ≤ η) :
    EnglishOrderPatternRealized η := by
  intro Q _ hfill
  exact orderPatternRealized_of_fillsCuts hη hfill

/-- Cut filling on the rich `Pt η` chart implies pattern realization (Lemma 5.5 specialization). -/
theorem english_orderPattern_realized_pt (η : Cardinal.{u}) (hη : aleph0 ≤ η) :
    OrderPatternRealized η (Pt η) :=
  orderPatternRealized_pt η hη

/-! ## Constant-family packaging (not the Lemma 6.9 proof; retained for tests and helpers) -/

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

/-- Constant `κ`-sequence with the same realizing tuple at every index (not English support-copy). -/
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

/-! ## Exception estimate and assembly (English steps 5–6; pinned behind step 4) -/

/-- English step 5–6: from the support-copy region layout, build `few_exceptions` using Lemma 6.1
orbit bounds and Lemma 4.6 block interchange on the κ copy slots. -/
theorem support_copy_exception_and_assembly
    [CategoricalUnbounded K] (_F : TermTemplate K S) [_hpres : HasPresentations W _F]
    [_hpack : HasChainUnions W]
    (_hedge : ∀ i j, ¬ S.specified i j)
    (_hcat : ∀ μ' ∈ W.eligible, Categorical K μ')
    (_σ _χ _b τ κ : Cardinal.{u}) (_hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ _σ) ≤ _χ)
    (_hiso : AssemblesStructIso W _b)
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    (p : TupleOver K S W hμ base) (_hχμ : _χ < μ)
    (hpattern : EnglishOrderPatternRealized (max τ _σ)) :
  ∃ seq : ApproximationSequence p, seq.τ = τ ∧ #(seq.κIndex) = κ := by
  sorry

/-! ## Main existence (English support-copy gloss) -/

/-- Uniform approximation sequences for `p = tp(v/A)` with `#p.idx ≤ σ` (English Lemma 6.9).

Hypotheses match Lemma 6.1 packaging. The proof follows the English paragraphs above; it is
pinned at `english_orderPattern_realized_over_old` (step 4). Steps 1–2 invoke Lemmas 5.5, 5.4,
and cite placement (Lemma 6.5). -/
theorem WorkingScheme.exists_approximationSequence
    [CategoricalUnbounded K] (F : TermTemplate K S) [hpres : HasPresentations W F]
    [hpack : HasChainUnions W]
    (hedge : ∀ i j, ¬ S.specified i j)
    (hcat : ∀ μ' ∈ W.eligible, Categorical K μ')
    (σ χ b τ κ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hτ : aleph0 ≤ τ) (hκ : aleph0 ≤ κ)
    (hpow : χ ^ σ = χ) (hb : b + σ < χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ)
    (hiso : AssemblesStructIso W b)
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} (base : W.Object μ hμ)
    (p : TupleOver K S W hμ base)
    (hidxσ : #p.idx ≤ σ) (hidxμ : #p.idx < μ)
    (hμτ : τ < μ) (hκμ : κ < μ) (hμκ : κ * #p.idx < μ)
    (hχμ : χ < μ) :
    ∃ seq : ApproximationSequence p, seq.τ = τ ∧ #(seq.κIndex) = κ := by
  -- English step 1: rich padded chart for `A` (Lemmas 5.5, 5.4).
  obtain ⟨_, _, _, _, _, _, _⟩ := exists_denseRichOrder τ hτ
  have _step1 : True := by
    by_cases hμSL : μ.IsStrongLimit
    · obtain ⟨I, _loI, _padI, hIcard, _, _⟩ := exists_richPaddedOrder τ hτ hμSL hμτ
      have hμ0 : ℵ₀ < μ := lt_of_le_of_lt hτ hμτ
      haveI : Nonempty I :=
        (mk_ne_zero_iff.1 (by rw [hIcard]; exact ne_of_gt (lt_trans aleph0_pos hμ0)))
      let _ := lemma_5_4 W F hpack hμ I hIcard
      trivial
    · -- Without `μ` a strong limit, English cites cut filling at `2^τ` only.
      trivial
  -- English step 2: Lemma 6.5 places `p` at size `τ` (`exists_boundedDiagramLift`); not yet
  -- wired from `TupleOver` to `ClosedLevel` placement.
  -- English steps 3–4: anchors and κ disjoint convex copy regions; pinned at pattern richness.
  have hη : aleph0 ≤ max τ σ := le_trans hτ (le_max_left τ σ)
  have hpattern : EnglishOrderPatternRealized (max τ σ) :=
    english_orderPattern_realized_over_old (max τ σ) hη
  exact support_copy_exception_and_assembly F hedge hcat σ χ b τ κ hχ hiso p hχμ hpattern

end
end AEC
