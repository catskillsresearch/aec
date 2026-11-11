module

public import AEC.Section6.ApproximationSequence
public import AEC.Section6.PaddedPlacement
public import AEC.Section6.OffHitBlock
public import AEC.Section6.ParameterOrbits
public import AEC.Section5.PackageClauses
public import AEC.Section5.Results
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

@[expose] public section

/-!
# Uniform approximation sequences (Lemma 6.9)

1:1 Lean gloss of the English support-copy proof (eventual.pdf §6.2; see also Lemma 5.5.md
equivalence clause).

English steps:

1. By the rich-order and padding constructions of Lemmas 5.5 and 5.4, present `A` on a padded
   chart (`exists_denseRichOrder`, `exists_richPaddedOrder`, `lemma_5_4`).
2. Lemma 6.5 places `p` on the well-ordered skeleton (`infra_69_place_type`). The copy
   chain needs the same placement on the padded chart. That is Lemma 6.4's padded
   clause (`infra_69_place_on_fills`): down-set profiles and the `σ⁺` recursion
   `β ↦ 2^β + σ + b`, under the hypothesis that the supremum lies strictly below `μ`
   (`infra_69_pad_recursion_closed`). A `{D.t, g}`-closure point need not satisfy it.
3. Keep shared old-chart supports; partition other supports by cuts; anchors have size at most
   `σ + ℵ₀` (`ChartSupport`, the pure-order infras below).
4. In each anchor slot, choose `κ` pairwise disjoint convex regions and put a copy of the
   pattern; richness realizes the needed order patterns (English: Lemma 5.5 equivalence).
5. If supports avoid every region, the copy and the original differ by simultaneous disjoint
   block transpositions. Lemma 4.6 (`infra_69_lem61_off_hits`) keeps the natural diagram.
   On `SingleModelData`, `infra_69_off_hit_diagramEq` reads that copy back onto the skeleton
   (`ChartOffHit.readCopy`) and turns the natural diagram into `D(vᵢ, Z) = p↾Z`
   (`OffHitCopyDiagramEq`).
6. Assemble an `ApproximationSequence` (bounded concatenation, `few_exceptions`, subtuples).

Step 4 uses `english_orderPattern_realized_over_old` (cut filling ⇒ pattern realization;
embedding construction in `order_pattern_realized_over_old` may still be pinned). The constant-family
helpers `TupleOver.InBase` / `ApproximationSequence.ofConstFamily` are
**NOT a Lemma 6.9 proof** (they do not discharge English support-copy). See the section
header below.
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

/-! ## NOT a Lemma 6.9 proof

`TupleOver.InBase` and `ApproximationSequence.ofConstFamily` are constant-family helpers
retained for tests. They are **not** the proof of Lemma 6.9 and are not used by
`WorkingScheme.exists_approximationSequence`. -/

/-- At level `μ`, data in the base with reflexive inclusion (in-base actual type).
**NOT a Lemma 6.9 proof.** -/
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

/-- Constant `κ`-sequence with the same realizing tuple at every index.
**NOT a Lemma 6.9 proof** (not English support-copy). -/
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

/-! ## Infra board stubs (English Lem 6.9 proof sentences; board `infra_69_*`)

Each theorem quotes one eventual.pdf sentence. Signatures are filled on the corresponding
prove pass; stubs may be `True` until the API bridge for that sentence is wired. -/

/-- **Infra `infra_69_present_padded`:** By Lemmas 5.5 and 5.4, present `A` on a padded dense
order sufficiently saturated for every support size used below.

`η` bounds the support sizes used below (`ℵ₀ ≤ η < μ`), and `μ` is a strong limit so Lemma 5.5
supplies a padded dense order of cardinality `μ`. Every cut of size at most `η` is filled.
Lemma 5.4 realizes that presentation as a scheme object, and `HasPresentations` identifies the
presentation with `A`. -/
theorem infra_69_present_padded
    (F : TermTemplate K S) [hpres : HasPresentations W F]
    (hpack : HasChainUnions W)
    {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (hμSL : μ.IsStrongLimit)
    {η : Cardinal.{u}} (hη : aleph0 ≤ η) (hημ : η < μ)
    (A : W.Object μ hμ) :
    ∃ (I : Type u) (_ : LinearOrder I) (_ : Nonempty I) (_ : IsPadded I),
      #I = μ ∧
      (∀ a b : I, a < b → ∃ c, a < c ∧ c < b) ∧
      (∀ ρ : Cardinal.{u}, ρ ≤ η → OrderFillsCuts ρ I) ∧
      ∃ X : W.Object μ hμ,
        (∀ v, Nonempty (((F.present I).obj v).carrier ≃[K.τ]
          ((W.asSystem hμ X).obj v).carrier)) ∧
        ∀ v, Nonempty (((F.present I).obj v).carrier ≃[K.τ]
          ((W.asSystem hμ A).obj v).carrier) := by
  obtain ⟨I, lo, pad, hIcard, hdense, hcut⟩ := exists_richPaddedOrder η hη hμSL hημ
  have hne : Nonempty I :=
    mk_ne_zero_iff.1 (by
      rw [hIcard]
      exact ne_of_gt (lt_trans aleph0_pos (lt_of_le_of_lt hη hημ)))
  have hfill : ∀ ρ : Cardinal.{u}, ρ ≤ η → OrderFillsCuts ρ I := by
    intro ρ hρ L R hL hR hLR
    exact hcut L R (le_trans hL hρ) (le_trans hR hρ) hLR
  obtain ⟨X, hX, _⟩ := lemma_5_4 W F hpack hμ I hIcard
  exact ⟨I, lo, hne, pad, hIcard, hdense, hfill,
    ⟨X, hX, fun v => hpres.present_equiv hμ A I hIcard v⟩⟩

/-- **Infra `infra_69_chart_iso`:** The presentation is an object of the current scheme;
categoricity in the package gives an isomorphism with `A`.

Lemma 5.4 supplies the scheme object of the padded presentation. Categoricity at `μ` identifies
that object with `A`, and transporting along the presentation equivalence is the chart of `A`. -/
theorem infra_69_chart_iso
    (F : TermTemplate K S) [hpres : HasPresentations W F]
    (hpack : HasChainUnions W)
    (hcat : ∀ μ' ∈ W.eligible, Categorical K μ')
    {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible)
    (I : Type u) [LinearOrder I] [Nonempty I] [IsPadded I] (hI : #I = μ)
    (A : W.Object μ hμ) :
    ∃ X : W.Object μ hμ,
      (∀ v, Nonempty (((F.present I).obj v).carrier ≃[K.τ]
        ((W.asSystem hμ X).obj v).carrier)) ∧
      (∀ v, Nonempty (((W.asSystem hμ X).obj v).carrier ≃[K.τ]
        ((W.asSystem hμ A).obj v).carrier)) ∧
      ∀ v, Nonempty (((F.present I).obj v).carrier ≃[K.τ]
        ((W.asSystem hμ A).obj v).carrier) := by
  obtain ⟨X, hX, _⟩ := lemma_5_4 W F hpack hμ I hI
  refine ⟨X, hX, ?_, ?_⟩
  · intro v
    exact (hcat μ hμ).unique_model
      ((W.asSystem hμ X).obj v) ((W.asSystem hμ A).obj v)
      ((W.asSystem hμ X).inK v) ((W.asSystem hμ A).inK v)
      (W.vertex_card hμ X v) (W.vertex_card hμ A v)
  · intro v
    obtain ⟨ePX⟩ := hX v
    obtain ⟨eXA⟩ := (hcat μ hμ).unique_model
      ((W.asSystem hμ X).obj v) ((W.asSystem hμ A).obj v)
      ((W.asSystem hμ X).inK v) ((W.asSystem hμ A).inK v)
      (W.vertex_card hμ X v) (W.vertex_card hμ A v)
    exact ⟨eXA.comp ePX⟩

/-- **Infra `infra_69_place_type`:** Lemma 6.5, or its compact-placement proof in the padded
chart, places `p` correctly at size `τ`.

English (eventual.pdf §6.2): "Lemma 6.5, or its compact-placement proof in the padded chart,
places `p` correctly at size `τ`."

Lemma 5.5's padded chart `I` is dense. `IsPadded` supplies a skeleton `s ⊆ I` with
`#s = #I = μ` and `WellFoundedLT s` (the inclusion into the padded chart is
`OrderEmbedding.subtype (· ∈ s)`). Categoricity identifies `E(s)` with the base, and `p.incl`
carries that chart into the host of `p`. The tuple `d` is `p` read in the host. So `s` is a
well-ordered presentation of `A` of size `μ`, in the sense of Lemma 6.5, sitting inside the
padded index. The placement is over `s`. It is not a placement over the dense order `I`, and
`I` is not treated as `WellFoundedLT`.

`exists_boundedDiagramLift` needs one function that is both a `PlacedTester` and a strict
closure bound of `μ`. `exists_placedTester P.E P.D` gives `placedTestBound`, while
`μ ∈ P.eligible` is only `IsClosurePoint {P.D.t, P.g}` (`P.g` is the closure bound of the
eligible levels). Nothing puts `placedTestBound θ < μ` for every infinite `θ < μ`, so the full
`LiftsBounded` witness (every query of size `< μ`) is not obtained from these APIs. Compact
placement (`exists_placement_lifting`) at one `χ` with `max σ τ ≤ χ < μ`, `χ ^ σ = χ`, and
`ℓ + σ < χ` does not need a tester. The resulting placement realizes every joint of size at
most `max σ τ`, hence every query of size at most `τ` together with `p`.

A general `WorkingScheme` still has no `Placement`: this statement is for `SingleModelData`,
whose template is the order presentation `E`. No constant-family substitute is used. -/
theorem infra_69_place_type
    (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (base : P.scheme.Object μ hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ base)
    (hνμ : p.ν = μ)
    {σ τ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hσμ : σ < μ) (hidx : #p.idx ≤ σ)
    (hτ : ℵ₀ ≤ τ) (hτμ : τ < μ)
    (I : Type u) [LinearOrder I] [Nonempty I] [IsPadded I] (hI : #I = μ) :
    ∃ (s : Set I) (_ : Nonempty s) (_ : WellFoundedLT s),
      #s = μ ∧
      ∃ (e : (P.E.obj s).carrier ≃[K.τ] base.model.carrier)
        (incl : Language.Embedding K.τ (P.E.obj s).carrier p.host.model.carrier)
        (d : p.idx → p.host.model.carrier),
        K.Strong incl ∧
        (∀ a, incl a = (p.incl.onVertex PUnit.unit) (e a)) ∧
        (∀ i, d i = p.host.val (p.val i)) ∧
        Model.card p.host.model = μ ∧
        ∃ Q : Placement P.E.lab P.E.arity s p.idx,
          ∀ {β : Type u} (ρ : Cardinal.{u}), ℵ₀ ≤ ρ → ρ ≤ max σ τ →
            ∀ (q : β → (P.E.obj s).carrier) (hj : #(p.idx ⊕ β) ≤ ρ),
              Q.Lifts P.E P.D p.host.mem incl d ρ hj q := by
  obtain ⟨s, hsCard, hsWF⟩ := IsPadded.padded (I := I)
  have hsμ : #s = μ := hsCard.trans hI
  let _ : WellFoundedLT s := hsWF
  have hsNe : Nonempty s :=
    mk_ne_zero_iff.mp (by
      rw [hsμ]
      exact ne_of_gt (aleph0_pos.trans_le (P.aleph0_le hμ)))
  let _ : Nonempty s := hsNe
  have : CategoricalUnbounded K := P.D.categoricalUnbounded
  obtain ⟨e⟩ := P.hasPresentations.present_equiv hμ base s hsμ PUnit.unit
  let incl : Language.Embedding K.τ (P.E.obj s).carrier p.host.model.carrier :=
    (p.incl.onVertex PUnit.unit).comp e.toEmbedding
  let d : p.idx → p.host.model.carrier := fun i => p.host.val (p.val i)
  have hstrong : K.Strong incl :=
    K.strong_trans e.toEmbedding (p.incl.onVertex PUnit.unit)
      (strong_of_equiv K e (P.hE s)) (p.incl.onVertex_strong PUnit.unit)
  have hcardB : Model.card p.host.model = μ := by simpa [hνμ] using p.host.card
  have hcardS : Model.card (P.E.obj s) = μ := P.card_obj_eq hμ s hsμ
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ
  have hsum : ls K + σ < μ := add_lt_of_lt hμinf (P.ls_lt hμ) hσμ
  have hκμ : max τ (ls K + σ) < μ := max_lt hτμ hsum
  obtain ⟨χ, hχgt, hχμ, hpow⟩ :=
    exists_power_fixed_below hμ.1.working.strongLimit hσ hσμ hκμ
  have hτχ : τ < χ := (le_max_left τ (ls K + σ)).trans_lt hχgt
  have hlsχ : ls K + σ < χ := (le_max_right τ (ls K + σ)).trans_lt hχgt
  have hσχ : σ < χ := (self_le_add_left σ (ls K)).trans_lt hlsχ
  have hmaxχ : max σ τ < χ := max_lt hσχ hτχ
  have hρχμ : σ + χ < μ := add_lt_of_lt hμinf hσμ hχμ
  have hρinf : ℵ₀ ≤ σ + χ := (hτ.trans hτχ.le).trans (self_le_add_left χ σ)
  have ht : P.D.t (σ + χ) ≤ μ := (P.t_lt hμ hρinf hρχμ).le
  obtain ⟨Q, hQ⟩ := exists_placement_lifting (hB := p.host.mem) (incl := incl) (d := d)
    hstrong (P.categorical hμ) hcardB hcardS hσ hidx hlsχ hpow ht
  refine ⟨s, hsNe, hsWF, hsμ, e, incl, d, hstrong, fun _ => rfl, fun _ => rfl, hcardB, Q, ?_⟩
  intro β ρ hρinf' hρτ q hj
  have hβχ : #β ≤ χ := by
    refine le_trans ?_ (hj.trans (hρτ.trans hmaxχ.le))
    rw [mk_sum, lift_id, lift_id]
    exact self_le_add_left _ _
  have hjχ : #(p.idx ⊕ β) ≤ σ + χ :=
    hj.trans (hρτ.trans (hmaxχ.le.trans (self_le_add_left χ σ)))
  have hls : ls K ≤ σ + χ :=
    (self_le_add_right (ls K) σ).trans (hlsχ.le.trans (self_le_add_left χ σ))
  have hBc : P.D.t (σ + χ) ≤ Model.card p.host.model := ht.trans hcardB.ge
  have hJc : P.D.t (σ + χ) ≤ Model.card (P.E.obj Q.J) :=
    (ht.trans hcardS.ge).trans (mk_le_of_injective (P.E.map Q.f).injective)
  exact (hQ hβχ q hjχ).relevel hρinf hρinf' le_rfl
    (hρτ.trans (hmaxχ.le.trans (self_le_add_left χ σ))) hls hBc hJc hj id

/-! ## Profile-count cardinals

The padded clause of Lemma 6.4 counts profiles by down-sets, at most `2^{|X| + σ + b}` many,
and iterates `β₀` above the test size, `β_{i+1} = 2^{β_i} + σ + b`, through `i ≤ σ⁺`.
`exists_local_placement` applies to the stage union only when that union is strictly below
the level (`D.t ρ ≤ ‖E(I)‖`). A strong limit kills each single power. The stage-`ω`
supremum is the relative tower `profileTower β₀`. Eligible `μ` is a closure point of
`{D.t, g}`: `exists_closurePoint_ge` builds it as `⨆ n, closureTower t g κ`, one power
set and one `closureBound` per step. If that bound is absorbed by the power set, every
relative tower that starts in `[θ₀, μ)` is cofinal in `μ` (`iSup_profileTower_eq_of_ge`).
Cofinality `ℵ₀` then forces the supremum to equal `μ`; it does not do so for a tower that
stays bounded. The zero bounds are absorbed, the resulting closure point is `ℶ_ω`, and
every infinite `β₀ < ℶ_ω` has relative supremum `ℶ_ω`
(`exists_closurePoint_profileSup_eq`). A start below `θ₀` is a different tower.
`D.t σ ≥ σ⁺` does not escape one power set (`succ_le_two_pow`). -/

/-- One English profile step stays strictly below a strong limit. -/
theorem profileStep_lt_of_strongLimit {μ β σ b : Cardinal.{u}} (hμ : μ.IsStrongLimit)
    (hβ : β < μ) (hσ : σ < μ) (hb : b < μ) :
    (2 : Cardinal.{u}) ^ β + σ + b < μ := by
  have h2 : (2 : Cardinal.{u}) ^ β < μ := hμ.isStrongPrelimit hβ
  exact add_lt_of_lt hμ.aleph0_le (add_lt_of_lt hμ.aleph0_le h2 hσ) hb

/-- Eligible levels kill each single power set. -/
theorem eligible_pow_lt (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {β : Cardinal.{u}} (hβ : β < μ) : (2 : Cardinal.{u}) ^ β < μ :=
  hμ.1.working.strongLimit.isStrongPrelimit hβ

/-- `ℶ_ω` is a strong limit. -/
theorem isStrongLimit_beth_omega : IsStrongLimit (beth (Ordinal.omega0 : Ordinal.{u})) :=
  isStrongLimit_beth.mpr Ordinal.isSuccLimit_omega0.isSuccPrelimit

/-- The `ω`-iteration of the beth function is `ℶ_ω` itself. -/
theorem iSup_nat_beth_eq_beth_omega :
    (⨆ n : ℕ, beth (n : Ordinal.{u})) = beth (Ordinal.omega0 : Ordinal.{u}) := by
  refine le_antisymm
      (ciSup_le fun n => beth_mono (le_of_lt (Ordinal.natCast_lt_omega0 n))) ?_
  rw [beth_limit Ordinal.isSuccLimit_omega0]
  have : Nonempty ↑(Set.Iio (Ordinal.omega0 : Ordinal.{u})) :=
    ⟨⟨(0 : ℕ), Ordinal.natCast_lt_omega0 0⟩⟩
  refine ciSup_le fun a => ?_
  rcases Ordinal.eq_natCast_or_omega0_le a.1 with ⟨n, hn⟩ | hω
  · rw [hn]
    exact le_ciSup (f := fun n : ℕ => beth (n : Ordinal.{u})) bddAbove_of_small n
  · exact absurd hω (not_le_of_gt a.2)

/-- `ℶ_ω` has cofinality `ℵ₀`, as a cardinal. -/
theorem cof_ord_beth_omega :
    Ordinal.cof (beth (Ordinal.omega0 : Ordinal.{u})).ord = ℵ₀ := by
  have hEq : (beth (Ordinal.omega0 : Ordinal.{u})).ord =
      ⨆ n : ℕ, (beth (n : Ordinal.{u})).ord := by
    rw [← Ordinal.iSup_ord, iSup_nat_beth_eq_beth_omega]
  rw [hEq]
  have h := Ordinal.lift_cof_iSup (β := ℕ)
    (f := fun n => (beth (n : Ordinal.{u})).ord)
    (fun a b hab => Cardinal.ord_lt_ord.mpr (beth_strictMono (Nat.cast_lt.mpr hab)))
  rw [Order.cof_nat, Cardinal.lift_uzero, Cardinal.lift_aleph0] at h
  exact h

/-- The relative power-set tower from `β`: `β`, `2^β`, `2^(2^β)`, …. -/
def profileTower (β : Cardinal.{u}) : ℕ → Cardinal.{u}
  | 0 => β
  | n + 1 => (2 : Cardinal.{u}) ^ profileTower β n

theorem profileTower_mono_start {a b : Cardinal.{u}} (h : a ≤ b) (n : ℕ) :
    profileTower a n ≤ profileTower b n := by
  induction n with
  | zero => exact h
  | succ _ ih => exact power_le_power_left two_ne_zero ih

theorem profileTower_aleph0 (n : ℕ) : profileTower ℵ₀ n = beth (n : Ordinal.{u}) := by
  induction n with
  | zero => simp [profileTower, beth_zero]
  | succ n ih =>
    rw [show profileTower ℵ₀ (n + 1) = (2 : Cardinal.{u}) ^ profileTower ℵ₀ n from rfl, ih,
      ← beth_add_one]
    simp [Nat.cast_succ]

/-- The absolute tower from `ℵ₀` is `ℶ_ω`. -/
theorem iSup_profileTower_aleph0_eq_beth_omega :
    (⨆ n, profileTower (ℵ₀ : Cardinal.{u}) n) = beth (Ordinal.omega0 : Ordinal.{u}) := by
  rw [← iSup_nat_beth_eq_beth_omega]
  refine le_antisymm ?_ ?_
  · refine ciSup_le fun n => ?_
    rw [profileTower_aleph0]
    exact le_ciSup (f := fun n : ℕ => beth (n : Ordinal.{u})) bddAbove_of_small n
  · refine ciSup_le fun n => ?_
    rw [← profileTower_aleph0]
    exact le_ciSup (f := fun n : ℕ => profileTower (ℵ₀ : Cardinal.{u}) n) bddAbove_of_small n

/-- A cardinal successor lies under one power set. `σ⁺ ≤ D.t σ` does not exceed `2^σ`. -/
theorem succ_le_two_pow (a : Cardinal.{u}) : Order.succ a ≤ (2 : Cardinal.{u}) ^ a :=
  Order.succ_le_of_lt (cantor a)

theorem closureTower_succ_of_absorbed (t g : Cardinal.{u} → Cardinal.{u}) (κ : Cardinal.{u})
    (n : ℕ) (habs : closureBound t g (closureTower t g κ n) ≤
      (2 : Cardinal.{u}) ^ closureTower t g κ n) :
    closureTower t g κ (n + 1) =
      Order.succ ((2 : Cardinal.{u}) ^ closureTower t g κ n) := by
  have hmax : (2 : Cardinal.{u}) ^ closureTower t g κ n ⊔
      closureBound t g (closureTower t g κ n) =
      (2 : Cardinal.{u}) ^ closureTower t g κ n := max_eq_left habs
  have hdef : closureTower t g κ (n + 1) =
      Order.succ ((2 : Cardinal.{u}) ^ closureTower t g κ n ⊔
        closureBound t g (closureTower t g κ n)) := rfl
  rw [hdef, hmax]

theorem profileTower_le_closureTower (t g : Cardinal.{u} → Cardinal.{u}) {κ : Cardinal.{u}}
    (hκ : ℵ₀ ≤ κ)
    (habs : ∀ n, closureBound t g (closureTower t g κ n) ≤
      (2 : Cardinal.{u}) ^ closureTower t g κ n)
    (n : ℕ) : profileTower κ n ≤ closureTower t g κ n := by
  induction n with
  | zero =>
    have h0 : closureTower t g κ 0 = κ := by
      change max κ ℵ₀ = κ
      exact max_eq_left hκ
    rw [show profileTower κ 0 = κ from rfl, h0]
  | succ n ih =>
    change (2 : Cardinal.{u}) ^ profileTower κ n ≤ closureTower t g κ (n + 1)
    exact (power_le_power_left two_ne_zero ih).trans (by
      rw [closureTower_succ_of_absorbed t g κ n (habs n)]
      exact (Order.lt_succ _).le)

theorem closureTower_le_profileTower_even (t g : Cardinal.{u} → Cardinal.{u})
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (habs : ∀ n, closureBound t g (closureTower t g κ n) ≤
      (2 : Cardinal.{u}) ^ closureTower t g κ n)
    (n : ℕ) : closureTower t g κ n ≤ profileTower κ (2 * n) := by
  induction n with
  | zero =>
    have h0 : closureTower t g κ 0 = κ := by
      change max κ ℵ₀ = κ
      exact max_eq_left hκ
    rw [h0]
    exact le_of_eq (show κ = profileTower κ 0 from rfl)
  | succ n ih =>
    rw [closureTower_succ_of_absorbed t g κ n (habs n)]
    refine le_trans (Order.succ_le_succ (power_le_power_left two_ne_zero ih)) ?_
    refine le_trans (Order.succ_le_of_lt (cantor _)) ?_
    have hstep : (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ profileTower κ (2 * n)) =
        profileTower κ (2 * (n + 1)) := by
      have h1 : (2 : Cardinal.{u}) ^ profileTower κ (2 * n) =
          profileTower κ (2 * n + 1) := rfl
      have h2 : (2 : Cardinal.{u}) ^ profileTower κ (2 * n + 1) =
          profileTower κ (2 * n + 2) := rfl
      have h3 : 2 * n + 2 = 2 * (n + 1) := (Nat.mul_succ 2 n).symm
      rw [h1, h2, h3]
    exact le_of_eq hstep

/-- Under absorption, the relative tower from the base of a closure tower is the closure point. -/
theorem iSup_profileTower_eq_iSup_closureTower (t g : Cardinal.{u} → Cardinal.{u})
    {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (habs : ∀ n, closureBound t g (closureTower t g κ n) ≤
      (2 : Cardinal.{u}) ^ closureTower t g κ n) :
    (⨆ n, profileTower κ n) = ⨆ n, closureTower t g κ n := by
  refine le_antisymm
      (ciSup_le fun n => (profileTower_le_closureTower t g hκ habs n).trans
        (closureTower_le_iSup t g κ n)) ?_
  refine ciSup_le fun n => (closureTower_le_profileTower_even t g hκ habs n).trans ?_
  exact le_ciSup (f := profileTower κ) bddAbove_of_small (2 * n)

/-- A relative tower that starts at or above the base of an absorbed closure tower, and
strictly below the closure point, is cofinal: its supremum equals the closure point.
Cofinality `ℵ₀` is used only through that equality. A start below `θ₀` is not claimed. -/
theorem iSup_profileTower_eq_of_ge (t g : Cardinal.{u} → Cardinal.{u})
    {κ β₀ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (habs : ∀ n, closureBound t g (closureTower t g κ n) ≤
      (2 : Cardinal.{u}) ^ closureTower t g κ n)
    (hβ : κ ≤ β₀) (hβμ : β₀ < ⨆ n, closureTower t g κ n) :
    (⨆ n, profileTower β₀ n) = ⨆ n, closureTower t g κ n := by
  have hSL : (⨆ n, closureTower t g κ n).IsStrongLimit :=
    (closureTower_iSup_isWorkingLevel t g κ).strongLimit
  have hstep : ∀ n, profileTower β₀ n < ⨆ k, closureTower t g κ k := by
    intro n
    induction n with
    | zero => exact hβμ
    | succ _ ih => exact hSL.isStrongPrelimit ih
  refine le_antisymm (ciSup_le fun n => (hstep n).le) ?_
  rw [← iSup_profileTower_eq_iSup_closureTower t g hκ habs]
  refine ciSup_le fun n => (profileTower_mono_start hβ n).trans ?_
  exact le_ciSup (f := profileTower β₀) bddAbove_of_small n

theorem closureBound_aleph0 (κ : Cardinal.{u}) :
    closureBound (fun _ : Cardinal.{u} => ℵ₀) (fun _ : Cardinal.{u} => ℵ₀) κ = ℵ₀ := by
  have : Nonempty (Set.Iic κ) := ⟨⟨κ, Set.mem_Iic.mpr le_rfl⟩⟩
  unfold closureBound
  simp only [sup_idem]
  exact ciSup_const

theorem absorbed_const_aleph0 (n : ℕ) :
    closureBound (fun _ : Cardinal.{u} => ℵ₀) (fun _ : Cardinal.{u} => ℵ₀)
        (closureTower (fun _ : Cardinal.{u} => ℵ₀) (fun _ : Cardinal.{u} => ℵ₀) ℵ₀ n) ≤
      (2 : Cardinal.{u}) ^
        closureTower (fun _ : Cardinal.{u} => ℵ₀) (fun _ : Cardinal.{u} => ℵ₀) ℵ₀ n := by
  rw [closureBound_aleph0]
  have h0 : ℵ₀ ≤ closureTower (fun _ : Cardinal.{u} => ℵ₀) (fun _ : Cardinal.{u} => ℵ₀) ℵ₀ 0 := by
    change ℵ₀ ≤ max ℵ₀ ℵ₀
    exact le_max_left _ _
  have hθ : ℵ₀ ≤
      closureTower (fun _ : Cardinal.{u} => ℵ₀) (fun _ : Cardinal.{u} => ℵ₀) ℵ₀ n :=
    h0.trans ((closureTower_strictMono (fun _ : Cardinal.{u} => ℵ₀)
      (fun _ : Cardinal.{u} => ℵ₀) ℵ₀).monotone (Nat.zero_le n))
  exact hθ.trans (le_of_lt (cantor _))

theorem iSup_const_closureTower_eq_beth_omega :
    (⨆ n, closureTower (fun _ : Cardinal.{u} => ℵ₀) (fun _ : Cardinal.{u} => ℵ₀) ℵ₀ n) =
      beth (Ordinal.omega0 : Ordinal.{u}) := by
  rw [← iSup_profileTower_eq_iSup_closureTower (fun _ : Cardinal.{u} => ℵ₀)
      (fun _ : Cardinal.{u} => ℵ₀) le_rfl absorbed_const_aleph0]
  exact iSup_profileTower_aleph0_eq_beth_omega

theorem isClosurePoint_const_aleph0 :
    IsClosurePoint {(fun _ : Cardinal.{u} => ℵ₀), (fun _ : Cardinal.{u} => ℵ₀)}
      (⨆ n, closureTower (fun _ : Cardinal.{u} => ℵ₀) (fun _ : Cardinal.{u} => ℵ₀) ℵ₀ n) := by
  let t : Cardinal.{u} → Cardinal.{u} := fun _ => ℵ₀
  let g : Cardinal.{u} → Cardinal.{u} := fun _ => ℵ₀
  refine ⟨closureTower_iSup_isWorkingLevel t g ℵ₀, fun u hu => ⟨fun θ _ hθμ => ?_⟩⟩
  have h := closureTower_iSup_closed t g ℵ₀ θ hθμ
  rcases Set.mem_insert_iff.mp hu with rfl | hu
  · exact le_sup_left.trans_lt h
  · rw [Set.mem_singleton_iff] at hu
    subst hu
    exact le_sup_right.trans_lt h

/-- The zero-bound closure point is `ℶ_ω`. Every infinite `β₀` below it has relative
power-set supremum equal to the closure point, not strictly below it. -/
theorem exists_closurePoint_profileSup_eq :
    ∃ (t g : Cardinal.{u} → Cardinal.{u}) (μ : Cardinal.{u}),
      IsClosurePoint {t, g} μ ∧
      μ = beth (Ordinal.omega0 : Ordinal.{u}) ∧
      ∀ β₀, ℵ₀ ≤ β₀ → β₀ < μ → (⨆ n, profileTower β₀ n) = μ := by
  let t : Cardinal.{u} → Cardinal.{u} := fun _ => ℵ₀
  let g : Cardinal.{u} → Cardinal.{u} := fun _ => ℵ₀
  refine ⟨t, g, ⨆ n, closureTower t g ℵ₀ n, isClosurePoint_const_aleph0,
    iSup_const_closureTower_eq_beth_omega, fun β₀ hβ hβμ => ?_⟩
  exact iSup_profileTower_eq_of_ge t g le_rfl absorbed_const_aleph0 hβ hβμ

theorem not_profileSup_lt_const_closurePoint {β₀ : Cardinal.{u}} (hβ : ℵ₀ ≤ β₀)
    (hβμ : β₀ < ⨆ n, closureTower (fun _ : Cardinal.{u} => ℵ₀)
      (fun _ : Cardinal.{u} => ℵ₀) ℵ₀ n) :
    ¬ (⨆ n, profileTower β₀ n) <
        ⨆ n, closureTower (fun _ : Cardinal.{u} => ℵ₀) (fun _ : Cardinal.{u} => ℵ₀) ℵ₀ n := by
  rw [iSup_profileTower_eq_of_ge (fun _ : Cardinal.{u} => ℵ₀) (fun _ : Cardinal.{u} => ℵ₀)
      le_rfl absorbed_const_aleph0 hβ hβμ]
  exact lt_irrefl _

/-- **Infra `infra_69_place_on_fills`:** Lemma 6.4, padded clause, at one test size.

English (Lemma 6.4, last sentence): for a padded order that need not be well-ordered, locally
possible coherent prescriptions on every bounded subset, closed under the profile-count growth
of the compact-placement proof, are realized simultaneously at any one specified bounded test
size.

This is the placement `infra_69_support_copy_sequence` consumes. `I` is the padded chart of
`infra_69_present_padded` (dense, `IsPadded`, and, in the caller, `OrderFillsCuts (σ + κ)`).
The conclusion is one `Placement` over that same `I` lifting every joint of size at most
`max σ τ`. `WellFoundedLT I` is not assumed, and `I` is not pretended to be well-ordered.

Two bridges from `infra_69_place_type` do not supply this witness.

* Transport along the skeleton inclusion. `place_type` returns a placement over the
  well-ordered skeleton `s ⊆ I`. `exists_linearOrder_amalgam` pushes that placement along
  `OrderEmbedding.subtype (· ∈ s)` to an extension of `I`, so the old chart can be `I`.
  `Placement.Lifts` does not travel with it: the skeleton lift knows parameters of `E(s)`
  only, while `infra_69_off_hit_diagramEq` quantifies parameters of `E(I)`. An arbitrary
  element of `E(I)` need not lie in the image of `E.map` of the subtype, and freeness that
  would move it is Theorem 6.10, which depends on this chain.
* A split input to the copy. `ChartOffHit.copy` lands in the old chart and
  `embCopy = copy.trans old` lands in the placement order. `readCopy` pulls the moved term
  back along that same old chart, and `infra_69_off_hit_diagramEq` requires
  `H : ChartOffHit I Q.J` with `Q : Placement … I`. Copies in `I \ s` are not on the
  skeleton chart, and a skeleton chart does not fill cuts, so the region step has nowhere
  to put them.

`exists_placement_lifting` and `compact_placement` do not apply: their cut codes take least
elements of subsets of `I`, so they assume `WellFoundedLT I`. Replacing those codes by
down-sets changes the profile bound from `χ` with `χ ^ σ = χ` to `2^{|X| + σ + b}`. One
step of that bound lies below every eligible `μ` (`eligible_pow_lt`,
`profileStep_lt_of_strongLimit`). The iteration through `i ≤ σ⁺` takes a supremum at
stage `ω`, the relative tower `profileTower β₀`. Eligible `μ` is a closure point of
`{D.t, g}`, built by `closureTower`. When `closureBound` is absorbed by one power set,
every relative tower from `β₀` with `θ₀ ≤ β₀ < μ` has supremum `μ`
(`iSup_profileTower_eq_of_ge`): cofinality `ℵ₀` equates that cofinal sequence with `μ`,
and does not do so for a bounded sequence. The zero bounds are absorbed; their closure
point is `ℶ_ω`, and every infinite `β₀` below it fails the strict inequality
(`exists_closurePoint_profileSup_eq`, `not_profileSup_lt_const_closurePoint`). The proved
lower bound `σ⁺ ≤ D.t σ` still lies under `2^σ` (`succ_le_two_pow`), so it does not force
`closureBound` past one power set. The proof is `infra_69_pad_obstruction` under `infra_69_pad_recursion_closed`: the `σ⁺`
supremum of `β ↦ 2^β + σ + b` lies strictly below `μ`. That hypothesis is not true of every
`{D.t, g}`-closure point (`iSup_profileTower_eq_of_ge`). `infra_69_pad_exists_closed` shows
strong limits of cofinality `ℵ₀` satisfying it are unbounded.

`TupleOver.InBase` and `ApproximationSequence.ofConstFamily` are not a substitute. -/
theorem infra_69_place_on_fills
    (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (base : P.scheme.Object μ hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ base)
    (hνμ : p.ν = μ)
    {σ τ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hσμ : σ < μ) (hidx : #p.idx ≤ σ)
    (hτ : ℵ₀ ≤ τ) (hτμ : τ < μ)
    {I : Type u} [LinearOrder I] [Nonempty I] [IsPadded I] (hI : #I = μ)
    (e : (P.E.obj I).carrier ≃[K.τ] base.model.carrier)
    (incl : Language.Embedding K.τ (P.E.obj I).carrier p.host.model.carrier)
    (d : p.idx → p.host.model.carrier)
    (hstrong : K.Strong incl)
    (hincl : ∀ a, incl a = (p.incl.onVertex PUnit.unit) (e a))
    (hd : ∀ a, d a = p.host.val (p.val a))
    (hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ) :
    ∃ Q : Placement P.E.lab P.E.arity I p.idx,
      ∀ {β : Type u} (ρ : Cardinal.{u}), ℵ₀ ≤ ρ → ρ ≤ max σ τ →
        ∀ (q : β → (P.E.obj I).carrier) (hj : #(p.idx ⊕ β) ≤ ρ),
          Q.Lifts P.E P.D p.host.mem incl d ρ hj q := by
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let β₀ : Cardinal.{u} := max (max σ τ) b
  have hb : ℵ₀ ≤ b := le_max_right _ _
  have hσβ : σ ≤ β₀ := (le_max_left σ τ).trans (le_max_left _ _)
  have hbβ : b ≤ β₀ := le_max_right _ _
  have hlab : #P.E.lab ≤ b := by
    have hℓ : #P.E.lab ≤ ls K := by simpa [P.E.ell_eq] using P.E.lab_small
    exact hℓ.trans (le_max_left _ _)
  let γ : Cardinal.{u} := infra_69_pad_recursion σ b β₀ (Order.succ σ).ord
  have hγ : γ < μ := hclosed
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ
  have hγμ : σ + γ < μ := add_lt_of_lt hμinf hσμ hγ
  have hρinf : ℵ₀ ≤ σ + γ := hσ.trans le_self_add
  have ht : P.D.t (σ + γ) ≤ μ := (P.t_lt hμ hρinf hγμ).le
  have hcardB : Model.card p.host.model = μ := by simpa [hνμ] using p.host.card
  have hcardI : Model.card (P.E.obj I) = μ := P.card_obj_eq hμ I hI
  have hcB : P.D.t (σ + γ) ≤ Model.card p.host.model := ht.trans hcardB.ge
  have hcI : P.D.t (σ + γ) ≤ Model.card (P.E.obj I) := ht.trans hcardI.ge
  have hmemI : K.Mem (P.E.obj I) := orderPresentation_obj_mem P.E I
  have hex : ∀ (β : Type u) (_ : #β ≤ γ) (qv : β → (P.E.obj I).carrier),
      ∃ φ : Language.Embedding K.τ p.host.model.carrier (P.E.obj I).carrier,
        K.Strong φ ∧ ∀ x, φ (incl (qv x)) = qv x :=
    fun β hβ qv => exists_paramFixing (hB := p.host.mem) hstrong (P.categorical hμ)
      hcardB hcardI hρinf ht (hβ.trans (by rw [add_comm]; exact le_self_add)) qv
  choose φ hφ hφp using hex
  have hpres : ∀ {β : Type u} (hβ : #β ≤ γ) (qv : β → (P.E.obj I).carrier)
      (hj : #(p.idx ⊕ β) ≤ σ + γ),
      P.D.same hj p.host.mem hmemI hcB hcI (Sum.elim d (fun x => incl (qv x)))
        (Sum.elim (fun a => φ β hβ qv (d a)) qv) := by
    intro β hβ qv hj
    refine P.D.of_strong hj p.host.mem hmemI hcB hcI _ _ (φ β hβ qv) hρinf (hφ β hβ qv) ?_
    rintro (a | x)
    · rfl
    · exact hφp β hβ qv x
  obtain ⟨Q, hQ⟩ := infra_69_pad_obstruction (E := P.E) (D := P.D) σ b β₀ hσ hb hσβ hbβ
    hidx hlab hcI
    (fun {β} hβ qv => Sum.elim (fun a => φ β hβ qv (d a)) qv)
    (fun {β} hβ qv hβ' => P.D.refl hβ' hmemI hcI qv)
    (fun {β β'} hβ hβ' qv ι hj => by
      have h1 : P.D.same hj p.host.mem hmemI hcB hcI
          (Sum.elim d (fun x => incl (qv (ι x))))
          (fun i => Sum.elim (fun a => φ β hβ qv (d a)) qv (Sum.map id ι i)) := by
        refine P.D.of_strong hj p.host.mem hmemI hcB hcI _ _ (φ β hβ qv) hρinf (hφ β hβ qv) ?_
        rintro (a | x)
        · rfl
        · exact hφp β hβ qv (ι x)
      exact P.D.trans hj hmemI p.host.mem hmemI hcI hcB hcI _ _ _
        (P.D.symm hj p.host.mem hmemI hcB hcI _ _ h1) (hpres hβ' (fun x => qv (ι x)) hj))
  refine ⟨Q, fun {β} ρ hρinf' hρτ qv hj => ?_⟩
  have hβ : #β ≤ β₀ := by
    refine le_trans ?_ (hρτ.trans (le_max_left _ b))
    refine le_trans ?_ hj
    rw [mk_sum, lift_id, lift_id, add_comm]
    exact le_self_add
  have hj0 : #(p.idx ⊕ β) ≤ σ + β₀ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_le_add hidx hβ
  have hJc0 : P.D.t (σ + γ) ≤ Model.card (P.E.obj Q.J) :=
    hcI.trans (mk_le_of_injective (P.E.map Q.f).injective)
  have h1 := SameNaturalDiagram.same hρinf (hQ hβ qv hj0) hJc0 hcI
    (orderPresentation_obj_mem P.E Q.J) hmemI
  simp only [realize_supportTermOf] at h1
  have hbig : Q.Lifts P.E P.D p.host.mem incl d (σ + γ)
      (hj0.trans (add_le_add_right (infra_69_pad_recursion_ge_start σ b β₀ _) σ)) qv := by
    intro hBc' hJc'
    exact P.D.trans (hj0.trans (add_le_add_right
        (infra_69_pad_recursion_ge_start σ b β₀ _) σ)) p.host.mem hmemI
      (orderPresentation_obj_mem P.E Q.J) hBc' hcI hJc' _ _ _
      (hpres (hβ.trans (infra_69_pad_recursion_ge_start σ b β₀ _)) qv _)
      (P.D.symm _ (orderPresentation_obj_mem P.E Q.J) hmemI hJc' hcI _ _ h1)
  have hle : ρ ≤ σ + γ := by
    calc ρ ≤ max σ τ := hρτ
      _ ≤ β₀ := le_max_left _ _
      _ ≤ σ + β₀ := by rw [add_comm]; exact le_self_add
      _ ≤ σ + γ := add_le_add_right (infra_69_pad_recursion_ge_start σ b β₀ _) σ
  have hls : ls K ≤ σ + γ := by
    calc ls K ≤ b := le_max_left _ _
      _ ≤ β₀ := hbβ
      _ ≤ γ := infra_69_pad_recursion_ge_start σ b β₀ _
      _ ≤ σ + γ := by rw [add_comm]; exact le_self_add
  exact hbig.relevel hρinf hρinf' le_rfl hle hls hcB hJc0 hj id

/-! ## Support copies on a linear order (English Lem 6.9, the anchor paragraphs)

`ChartSupport` is the old chart `I ↪o J` together with the supporting positions of a placed
tuple. The infras below are the order combinatorics of those positions. They do not use a
`Placement`. `infra_69_place_type` places `p` over the skeleton of a padded chart, correctly
for queries of size at most `τ`; these combinatorics do not read that placement. -/

open Function Set Classical

/-- A convex subset of a linear order: it contains every point between its members. -/
def IsConvexRegion {α : Type u} [LinearOrder α] (s : Set α) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c, a ≤ c → c ≤ b → c ∈ s

/-- Points lying between two members of `s`. -/
def convexHull {α : Type u} [LinearOrder α] (s : Set α) : Set α :=
  {c | ∃ a ∈ s, ∃ b ∈ s, a ≤ c ∧ c ≤ b}

theorem subset_convexHull {α : Type u} [LinearOrder α] (s : Set α) : s ⊆ convexHull s :=
  fun x hx => ⟨x, hx, x, hx, le_rfl, le_rfl⟩

theorem convexHull_convex {α : Type u} [LinearOrder α] (s : Set α) :
    IsConvexRegion (convexHull s) := by
  intro a ha b hb c hac hcb
  rcases ha with ⟨a1, ha1, -, -, ha1a, -⟩
  rcases hb with ⟨-, -, b2, hb2, -, hbb2⟩
  exact ⟨a1, ha1, b2, hb2, le_trans ha1a hac, le_trans hcb hbb2⟩

theorem convexHull_subset_of_convex {α : Type u} [LinearOrder α] {region s : Set α}
    (hconv : IsConvexRegion region) (hs : s ⊆ region) : convexHull s ⊆ region := by
  intro c hc
  rcases hc with ⟨a, ha, b, hb, hac, hcb⟩
  exact hconv a (hs ha) b (hs hb) c hac hcb

theorem convexHull_disjoint_of_lt {α : Type u} [LinearOrder α] {s t : Set α}
    (h : ∀ a ∈ s, ∀ b ∈ t, a < b) : Disjoint (convexHull s) (convexHull t) := by
  rw [Set.disjoint_left]
  intro z hzS hzT
  rcases hzS with ⟨-, -, b1, hb1, -, hzb1⟩
  rcases hzT with ⟨a2, ha2, -, -, ha2z, -⟩
  exact lt_irrefl z (lt_of_le_of_lt hzb1 (lt_of_lt_of_le (h b1 hb1 a2 ha2) ha2z))

/-- Supporting positions of one placed tuple over an old chart. -/
structure ChartSupport (I J : Type u) [LinearOrder I] [LinearOrder J] where
  /-- The old chart inside the placement order. -/
  old : I ↪o J
  /-- Positions used by the placed tuple. -/
  support : Set J

namespace ChartSupport

variable {I J : Type u} [LinearOrder I] [LinearOrder J]
  (C : ChartSupport I J)

/-- Supporting positions that already lie on the old chart. -/
def shared : Set J := C.support ∩ Set.range (⇑C.old)

/-- Supporting positions off the old chart. -/
def unshared : Set J := C.support \ Set.range (⇑C.old)

theorem unshared_subset_support : C.unshared ⊆ C.support := fun _ h => h.1

/-- The same strict cut over every old position. -/
def SameCut (x y : J) : Prop :=
  ∀ i : I, C.old i < x ↔ C.old i < y

theorem sameCut_refl (x : J) : C.SameCut x x := fun _ => Iff.rfl

theorem sameCut_symm {x y : J} (h : C.SameCut x y) : C.SameCut y x :=
  fun i => (h i).symm

theorem sameCut_trans {x y z : J} (hxy : C.SameCut x y) (hyz : C.SameCut y z) :
    C.SameCut x z :=
  fun i => (hxy i).trans (hyz i)

theorem exists_separator {x y : J} (h : ¬ C.SameCut x y) :
    ∃ i : I, (C.old i < x) ≠ (C.old i < y) := by
  by_contra h'
  push Not at h'
  exact h fun i => Iff.of_eq (h' i)

/-- Pairs of unshared positions that lie in different strict cuts. -/
def sepIndex : Type u :=
  {p : J × J // p.1 ∈ C.unshared ∧ p.2 ∈ C.unshared ∧ ¬ C.SameCut p.1 p.2}

/-- One old position separating a pair of distinct cuts. -/
noncomputable def sepAt (p : C.sepIndex) : I :=
  Classical.choose (C.exists_separator p.2.2.2)

theorem sepAt_spec (p : C.sepIndex) :
    (C.old (C.sepAt p) < p.1.1) ≠ (C.old (C.sepAt p) < p.1.2) :=
  Classical.choose_spec (C.exists_separator p.2.2.2)

/-- Images of the chosen separators. -/
noncomputable def sepImage : Set J :=
  Set.range fun p : C.sepIndex => C.old (C.sepAt p)

/-- Shared supports together with one separator for each pair of distinct cuts. -/
noncomputable def anchors : Set J := C.shared ∪ C.sepImage

theorem exists_old_index {a : J} (ha : a ∈ C.anchors) : ∃ i : I, C.old i = a := by
  rcases ha with hsh | hsep
  · exact hsh.2
  · rcases hsep with ⟨_p, rfl⟩
    exact ⟨C.sepAt _, rfl⟩

/-- Strict slot over the anchor set. -/
def SameSlot (x y : J) : Prop :=
  ∀ a ∈ C.anchors, a < x ↔ a < y

/-- Old indices of anchors strictly to the left of `x`. -/
def anchorLeft (x : J) : Set I :=
  {i | C.old i ∈ C.anchors ∧ C.old i < x}

/-- Old indices of anchors strictly to the right of `x`. -/
def anchorRight (x : J) : Set I :=
  {i | C.old i ∈ C.anchors ∧ x < C.old i}

/-- Old positions that compare with every anchor the way `x` does. -/
def slotCarrier (x : J) : Set I :=
  {i | ∀ a ∈ C.anchors, a < C.old i ↔ a < x}

/-- A point of `I` lying in the anchor slot of `x`. -/
structure InAnchorSlot (x : J) (z : I) : Prop where
  aboveLeft : ∀ a ∈ C.anchorLeft x, a < z
  belowRight : ∀ b ∈ C.anchorRight x, z < b

theorem anchorSide_card_le (x : J) :
    #(C.anchorLeft x) ≤ #C.anchors ∧ #(C.anchorRight x) ≤ #C.anchors := by
  refine ⟨mk_le_of_injective (f := fun a : C.anchorLeft x =>
      (⟨C.old a.1, a.2.1⟩ : C.anchors)) ?_,
    mk_le_of_injective (f := fun a : C.anchorRight x =>
      (⟨C.old a.1, a.2.1⟩ : C.anchors)) ?_⟩
  · intro a b h
    exact Subtype.ext (C.old.injective (congrArg Subtype.val h))
  · intro a b h
    exact Subtype.ext (C.old.injective (congrArg Subtype.val h))

theorem slot_of_inAnchor {x : J} (hx : x ∈ C.unshared) {z : I}
    (hz : C.InAnchorSlot x z) : z ∈ C.slotCarrier x := by
  intro a ha
  obtain ⟨i, hi⟩ := C.exists_old_index ha
  have hne : a ≠ x := by
    intro heq
    exact hx.2 ⟨i, hi.trans heq⟩
  rcases lt_trichotomy a x with hax | heq | hxa
  · have hiL : i ∈ C.anchorLeft x := ⟨by simpa [hi] using ha, by simpa [hi] using hax⟩
    have hbelow : a < C.old z := by
      simpa [hi] using (C.old.lt_iff_lt).mpr (hz.aboveLeft i hiL)
    exact iff_of_true hbelow hax
  · exact absurd heq hne
  · have hiR : i ∈ C.anchorRight x := ⟨by simpa [hi] using ha, by simpa [hi] using hxa⟩
    have hnot : ¬ a < C.old z := by
      have hzlt : C.old z < a := by
        simpa [hi] using (C.old.lt_iff_lt).mpr (hz.belowRight i hiR)
      exact not_lt_of_gt hzlt
    exact iff_of_false hnot (not_lt_of_gt hxa)

/-- The cut setoid of a set of positions, over the whole old order. -/
def cutSetoid (S : Set J) : Setoid S where
  r x y := C.SameCut x.1 y.1
  iseqv := ⟨fun x => C.sameCut_refl x.1, fun h => C.sameCut_symm h,
    fun h₁ h₂ => C.sameCut_trans h₁ h₂⟩

/-- Clusters of unshared supports: one class for each strict cut. -/
abbrev Cluster : Type u := Quotient (C.cutSetoid C.unshared)

/-- The class of an unshared supporting position. -/
def clusterMk (x : C.unshared) : C.Cluster :=
  Quotient.mk (C.cutSetoid C.unshared) x

variable {κIndex : Type u} [LinearOrder κIndex]

/-- Data of one point chosen in an anchor slot, strictly above the points already chosen. -/
structure RegionPointSpec (x : J) (i : κIndex) (prev : ∀ j : κIndex, j < i → I) (z : I) :
    Prop where
  slot : C.InAnchorSlot x z
  abovePrev : ∀ j, (hj : j < i) → prev j hj < z

theorem exists_regionPoint_step {η : Cardinal.{u}} (hη : ℵ₀ ≤ η)
    (hanchors : #C.anchors ≤ η) (hidx : #κIndex ≤ η)
    (hfill : OrderFillsCuts η I) (x : J) (i : κIndex)
    (prev : ∀ j : κIndex, j < i → I)
    (hprev : ∀ j (hj : j < i), C.InAnchorSlot x (prev j hj)) :
    ∃ z : I, C.RegionPointSpec x i prev z := by
  let prevFun : {j : κIndex // j < i} → I := fun j => prev j.1 j.2
  let L : Set I := C.anchorLeft x ∪ Set.range prevFun
  let R : Set I := C.anchorRight x
  have hL : #L ≤ η := by
    have hLeft : #(C.anchorLeft x) ≤ η := (C.anchorSide_card_le x).1.trans hanchors
    have hPrev : #(Set.range prevFun) ≤ η :=
      mk_range_le.trans ((mk_subtype_le (fun j : κIndex => j < i)).trans hidx)
    have hsum : #(C.anchorLeft x) + #(Set.range prevFun) ≤ η := by
      have hle := add_le_add hLeft hPrev
      simpa [add_eq_max hη, max_self] using hle
    exact (mk_union_le _ _).trans hsum
  have hR : #R ≤ η := (C.anchorSide_card_le x).2.trans hanchors
  have hLR : ∀ a ∈ L, ∀ b ∈ R, a < b := by
    intro a ha b hb
    rcases ha with ha | ha
    · exact (C.old.lt_iff_lt).mp (lt_trans ha.2 hb.2)
    · rcases ha with ⟨j, rfl⟩
      exact (hprev j.1 j.2).belowRight b hb
  obtain ⟨z, hzL, hzR⟩ := hfill L R hL hR hLR
  refine ⟨z, ?_, ?_⟩
  · refine ⟨fun a ha => hzL a (Or.inl ha), fun b hb => hzR b hb⟩
  · intro j hj
    exact hzL (prev j hj) (Or.inr ⟨⟨j, hj⟩, rfl⟩)

/-- The `i`th point of a `κ`-sequence in the anchor slot of `x`, chosen by cut filling. -/
noncomputable abbrev regionPoint {η : Cardinal.{u}} (hfill : OrderFillsCuts η I) (x : J)
    [WellFoundedLT κIndex] : κIndex → I :=
  WellFoundedLT.fix fun i prev =>
    if h : ∃ z : I, C.RegionPointSpec x i prev z then
      Classical.choose h
    else
      Classical.choice (orderFillsCuts_nonempty hfill)

theorem regionPoint_spec {η : Cardinal.{u}} (hη : ℵ₀ ≤ η)
    (hanchors : #C.anchors ≤ η) (hidx : #κIndex ≤ η)
    (hfill : OrderFillsCuts η I) (x : J)
    [WellFoundedLT κIndex] (i : κIndex) :
    C.RegionPointSpec x i (fun j _ => C.regionPoint hfill x j) (C.regionPoint hfill x i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hex : ∃ z : I, C.RegionPointSpec x i (fun j _ => C.regionPoint hfill x j) z :=
      C.exists_regionPoint_step hη hanchors hidx hfill x i
        (fun j hj => C.regionPoint hfill x j) (fun j hj => (ih j hj).slot)
    unfold regionPoint
    rw [WellFoundedLT.fix_eq]
    have hpick :
        (if h : ∃ z : I, C.RegionPointSpec x i (fun j _ => C.regionPoint hfill x j) z then
            Classical.choose h
          else Classical.choice (orderFillsCuts_nonempty hfill)) =
        Classical.choose hex :=
      dite_eq_left hex
    rw [hpick]
    exact Classical.choose_spec hex

/-- Unshared positions in the strict cut of `x`. -/
def clusterAt (x : J) : Set J :=
  {y | y ∈ C.unshared ∧ C.SameCut x y}

/-- Old indices of anchor positions. An abbreviation, so the subtype linear order is found. -/
noncomputable abbrev anchorIdx : Type u := {i : I // C.old i ∈ C.anchors}

/-- Anchors together with one unshared cluster, in the order induced from `J`. -/
def patternCarrier (x : J) : Set J := C.anchors ∪ C.clusterAt x

/-- The anchor indices, as an order embedding into the pattern carrier. -/
def anchorIncl (x : J) : C.anchorIdx ↪o ↥(C.patternCarrier x) :=
  OrderEmbedding.ofStrictMono (fun i => ⟨C.old i.1, Or.inl i.2⟩) fun a b hab =>
    Subtype.coe_lt_coe.mp
      ((C.old.lt_iff_lt).mpr (Subtype.coe_lt_coe.mpr hab))

/-- Cardinality of the anchor set. The infra wrapper is `infra_69_anchor_bound`. -/
theorem anchor_card_le {σ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hsup : #C.support ≤ σ) :
    #C.anchors ≤ σ + ℵ₀ := by
  have hshared : #C.shared ≤ σ :=
    (mk_le_mk_of_subset (fun _ hx => hx.1)).trans hsup
  have hidx : #C.sepIndex ≤ σ := by
    let f : C.sepIndex → C.support × C.support := fun p =>
      (⟨p.1.1, p.2.1.1⟩, ⟨p.1.2, p.2.2.1.1⟩)
    have hinj : Function.Injective f := by
      intro p q h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : C.support × C.support => (z.1 : J)) h
      · exact congrArg (fun z : C.support × C.support => (z.2 : J)) h
    have hprod : #(C.support × C.support) = #C.support * #C.support := by
      simp [mk_prod, lift_id]
    have hmul : #C.support * #C.support ≤ σ := by
      simpa [mul_eq_self hσ] using mul_le_mul' hsup hsup
    exact (mk_le_of_injective hinj).trans (by rw [hprod]; exact hmul)
  have himg : #C.sepImage ≤ σ := mk_range_le.trans hidx
  have hunion : #(C.shared ∪ C.sepImage : Set J) ≤ #C.shared + #C.sepImage :=
    mk_union_le _ _
  have hsum : #C.shared + #C.sepImage ≤ σ := by
    simpa [add_eq_max hσ, max_self] using add_le_add hshared himg
  have hanchors : #C.anchors ≤ σ := by
    simpa [ChartSupport.anchors] using hunion.trans hsum
  exact hanchors.trans (self_le_add_right σ ℵ₀)

theorem anchorIdx_card_le {σ κ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hκ : ℵ₀ ≤ κ)
    (hsup : #C.support ≤ σ) : #C.anchorIdx ≤ σ + κ := by
  have hinj : Function.Injective (fun i : C.anchorIdx => (⟨C.old i.1, i.2⟩ : C.anchors)) :=
    fun a b h => Subtype.ext (C.old.injective (congrArg Subtype.val h))
  have hpre : #C.anchorIdx ≤ #C.anchors := mk_le_of_injective hinj
  have hAnch : #C.anchors ≤ σ + ℵ₀ := C.anchor_card_le hσ hsup
  exact hpre.trans (hAnch.trans (add_le_add le_rfl hκ))

theorem clusterAt_subset_support (x : J) : C.clusterAt x ⊆ C.support :=
  fun _ h => C.unshared_subset_support h.1

theorem clusterAt_card_le {σ κ : Cardinal.{u}} (_hσ : ℵ₀ ≤ σ) (_hκ : ℵ₀ ≤ κ)
    (hsup : #C.support ≤ σ) (x : J) : #(C.clusterAt x) ≤ σ + κ :=
  (mk_le_mk_of_subset (C.clusterAt_subset_support x)).trans
    (hsup.trans (self_le_add_right σ κ))

theorem mem_range_anchorIncl {x : J} {z : ↥(C.patternCarrier x)} :
    z ∈ Set.range (⇑(C.anchorIncl x)) ↔ z.1 ∈ C.anchors := by
  constructor
  · rintro ⟨i, rfl⟩
    exact i.2
  · intro hz
    obtain ⟨i, hi⟩ := C.exists_old_index hz
    have hiMem : C.old i ∈ C.anchors := by simpa [hi] using hz
    refine ⟨⟨i, hiMem⟩, ?_⟩
    exact Subtype.ext hi

theorem patternAdded_subset_cluster {x : J} {z : ↥(C.patternCarrier x)}
    (hz : z ∉ Set.range (⇑(C.anchorIncl x))) : z.1 ∈ C.clusterAt x := by
  have hnot : z.1 ∉ C.anchors := fun ha => hz ((C.mem_range_anchorIncl).mpr ha)
  rcases z.2 with h | h
  · exact absurd h hnot
  · exact h

theorem patternAdded_card_le {σ κ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hκ : ℵ₀ ≤ κ)
    (hsup : #C.support ≤ σ) (x : J) :
    #(Set.diff Set.univ (Set.range (⇑(C.anchorIncl x)))) ≤ σ + κ := by
  let emb := C.anchorIncl x
  let f : ↥(Set.diff Set.univ (Set.range (⇑emb))) → C.clusterAt x := fun z =>
    ⟨z.1.1, C.patternAdded_subset_cluster z.2.2⟩
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : C.clusterAt x => (w : J)) h
  exact (mk_le_of_injective hinj).trans (C.clusterAt_card_le hσ hκ hsup x)

/-- The order pattern of one cluster over the anchors. Old and added parts have size at most
`σ + κ`. -/
def clusterPattern {σ κ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hκ : ℵ₀ ≤ κ)
    (hsup : #C.support ≤ σ) (x : J) :
    OrderPattern (σ + κ) C.anchorIdx ↥(C.patternCarrier x) where
  emb := C.anchorIncl x
  card_old := C.anchorIdx_card_le hσ hκ hsup
  cardAdded := C.patternAdded_card_le hσ hκ hsup x

theorem slotCarrier_convex (x : J) : IsConvexRegion (C.slotCarrier x) := by
  intro a ha b hb c hac hcb u hu
  by_cases hux : u < x
  · have hua : u < C.old a := (ha u hu).2 hux
    exact iff_of_true (lt_of_lt_of_le hua (C.old.monotone hac)) hux
  · have hnotb : ¬ u < C.old b := fun h => hux ((hb u hu).1 h)
    have hnotc : ¬ u < C.old c := fun h => hnotb (lt_of_lt_of_le h (C.old.monotone hcb))
    exact iff_of_false hnotc hux

end ChartSupport

/-- **Infra `infra_69_shared_supports`:** Keep every extra supporting position that belongs to
the old chart. -/
theorem infra_69_shared_supports {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) :
    (∀ x : J, x ∈ C.shared ↔ x ∈ C.support ∧ x ∈ Set.range (⇑C.old)) ∧
    C.shared ∪ C.unshared = C.support ∧
    Disjoint C.shared C.unshared := by
  refine ⟨fun x => by simp [ChartSupport.shared, Set.mem_inter_iff], ?_, ?_⟩
  · ext x
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · exact hx.1
    · intro hx
      by_cases h : x ∈ Set.range (⇑C.old)
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  · rw [Set.disjoint_iff]
    intro x hx
    exact hx.2.2 hx.1.2

/-- **Infra `infra_69_cut_clusters`:** Partition the other supporting positions into clusters
according to their strict cut over the entire old order. -/
theorem infra_69_cut_clusters {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) :
    Function.Surjective C.clusterMk ∧
    ∀ x y : C.unshared, C.clusterMk x = C.clusterMk y ↔ C.SameCut x.1 y.1 := by
  refine ⟨?_, ?_⟩
  · intro q
    obtain ⟨x, hx⟩ := Quotient.exists_rep q
    exact ⟨x, hx⟩
  · intro x y
    simp only [ChartSupport.clusterMk]
    exact
      ⟨fun h => Quotient.exact (s := C.cutSetoid C.unshared) h,
        fun h => Quotient.sound (s := C.cutSetoid C.unshared) h⟩

/-- **Infra `infra_69_separators`:** For every pair of distinct cuts choose an old position
separating them. The chosen position is an anchor. -/
theorem infra_69_separators {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) :
    ∀ x y : J, x ∈ C.unshared → y ∈ C.unshared → ¬ C.SameCut x y →
      ∃ i : I, C.old i ∈ C.anchors ∧ (C.old i < x) ≠ (C.old i < y) := by
  intro x y hx hy hcut
  let p : C.sepIndex := ⟨(x, y), hx, hy, hcut⟩
  refine ⟨C.sepAt p, ?_, C.sepAt_spec p⟩
  exact Or.inr ⟨p, rfl⟩

/-- **Infra `infra_69_include_shared`:** Include the shared supporting positions as well. -/
theorem infra_69_include_shared {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) :
    C.shared ⊆ C.anchors ∧ C.anchors = C.shared ∪ C.sepImage :=
  ⟨fun _ hx => Or.inl hx, rfl⟩

/-- **Infra `infra_69_anchor_bound`:** This gives a bounded anchor set of size at most
`σ + ℵ₀`. -/
theorem infra_69_anchor_bound {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {σ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hsup : #C.support ≤ σ) :
    #C.anchors ≤ σ + ℵ₀ :=
  C.anchor_card_le hσ hsup

/-- **Infra `infra_69_slot_assignment`:** Each unshared cluster belongs to a different strict
slot over the anchors. -/
theorem infra_69_slot_assignment {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {x y : J} (hx : x ∈ C.unshared) (hy : y ∈ C.unshared) :
    C.SameCut x y ↔ C.SameSlot x y := by
  constructor
  · intro hcut a ha
    obtain ⟨i, rfl⟩ := C.exists_old_index ha
    exact hcut i
  · intro hslot
    by_contra hcut
    let p : C.sepIndex := ⟨(x, y), hx, hy, hcut⟩
    have ha : C.old (C.sepAt p) ∈ C.anchors := Or.inr ⟨p, rfl⟩
    exact C.sepAt_spec p (propext (hslot _ ha))

/-- **Infra `infra_69_disjoint_regions`:** In each such anchor slot, choose `κ` pairwise
disjoint convex regions in the old order.

Each region is a singleton cut-filler of the slot. `η` is large enough for the anchors and
for `κ`, and `I` fills `η`-cuts. -/
theorem infra_69_disjoint_regions {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {η κ : Cardinal.{u}} (hη : ℵ₀ ≤ η) (hκle : κ ≤ η)
    (hanchors : #C.anchors ≤ η) (hfill : OrderFillsCuts η I)
    {x : J} (hx : x ∈ C.unshared) (κIndex : Type u) (hκ : #κIndex ≤ κ) :
    ∃ region : κIndex → Set I,
      (∀ i, region i ⊆ C.slotCarrier x) ∧
      (∀ i, IsConvexRegion (region i)) ∧
      (∀ i, (region i).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (region i) (region j)) := by
  obtain ⟨lo, wf⟩ := exists_wellFoundedLT κIndex
  letI : LinearOrder κIndex := lo
  haveI : WellFoundedLT κIndex := wf
  have hidx : #κIndex ≤ η := hκ.trans hκle
  let point : κIndex → I := C.regionPoint hfill x
  refine ⟨fun i => {point i}, ?_, ?_, ?_, ?_⟩
  · intro i z hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    exact C.slot_of_inAnchor hx (C.regionPoint_spec hη hanchors hidx hfill x i).slot
  · intro i a ha b hb c hac hcb
    simp only [Set.mem_singleton_iff] at ha hb
    subst ha
    subst hb
    have hc : c = point i := le_antisymm hcb hac
    subst hc
    exact Set.mem_singleton _
  · intro i
    exact ⟨point i, rfl⟩
  · intro i j hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact Set.disjoint_singleton.mpr (ne_of_lt
        ((C.regionPoint_spec hη hanchors hidx hfill x j).abovePrev i hlt))
    · exact absurd heq hij
    · exact Set.disjoint_singleton.mpr (ne_of_gt
        ((C.regionPoint_spec hη hanchors hidx hfill x i).abovePrev j hgt))

/-- **Infra `infra_69_richness_arity`:** The prescribed richness supplies these patterns; its
required arity is bounded in terms of `σ + κ`.

The pattern is one unshared cluster over the anchors. Both parts have cardinality at most
`σ + κ`. `OrderPatternRealized` is the richness hypothesis; on an order that fills cuts it is
`infra_55_pattern_realize`. -/
theorem infra_69_richness_arity {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {σ κ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hκ : ℵ₀ ≤ κ)
    (hsup : #C.support ≤ σ) (x : J) (_hx : x ∈ C.unshared) :
    #C.anchorIdx ≤ σ + κ ∧ #(C.clusterAt x) ≤ σ + κ ∧
    ∀ {Q : Type u} [LinearOrder Q], OrderPatternRealized (σ + κ) Q →
      ∀ f : C.anchorIdx ↪o Q,
        ∃ g : ↥(C.patternCarrier x) ↪o Q, ∀ a, g (C.anchorIncl x a) = f a := by
  refine ⟨C.anchorIdx_card_le hσ hκ hsup, C.clusterAt_card_le hσ hκ hsup x, ?_⟩
  intro Q _ hreal f
  exact hreal (C.clusterPattern hσ hκ hsup x) f

/-! ### Copies of one cluster (`infra_69_copy_cluster`)

The carrier is the lexicographic sum of the left anchors, one seed and one copy of the cluster
for each index, and the right anchors. `OrderPatternRealized` extends the embedding of the
anchors and the seeds. -/

namespace SupportCopy

inductive Pos (κIndex Cluster Left Right : Type u) where
  | left (a : Left)
  | seed (i : κIndex)
  | copy (i : κIndex) (y : Cluster)
  | right (a : Right)

inductive Old (κIndex Left Right : Type u) where
  | left (a : Left)
  | seed (i : κIndex)
  | right (a : Right)

section

variable {κIndex Cluster Left Right : Type u}
  [LinearOrder κIndex] [LinearOrder Cluster] [LinearOrder Left] [LinearOrder Right]

abbrev Code (κIndex Cluster Left Right : Type u) : Type u :=
  (Left ⊕ₗ (κIndex ×ₗ (PUnit.{u + 1} ⊕ₗ Cluster))) ⊕ₗ Right

abbrev OldCode (κIndex Left Right : Type u) := (Left ⊕ₗ κIndex) ⊕ₗ Right

def includeOld : Old κIndex Left Right → Pos κIndex Cluster Left Right
  | .left a => .left a
  | .seed i => .seed i
  | .right a => .right a

def encode : Pos κIndex Cluster Left Right → Code κIndex Cluster Left Right
  | .left a => toLex (Sum.inl (toLex (Sum.inl a)))
  | .seed i =>
      toLex (Sum.inl (toLex (Sum.inr (toLex (i, toLex (Sum.inl (PUnit.unit : PUnit.{u + 1})))))))
  | .copy i y =>
      toLex (Sum.inl (toLex (Sum.inr (toLex (i, toLex (Sum.inr y))))))
  | .right a => toLex (Sum.inr a)

/-- Recover a position from its lexicographic code. -/
def decode (c : Code κIndex Cluster Left Right) : Pos κIndex Cluster Left Right :=
  match ofLex c with
  | Sum.inl inner =>
      match ofLex inner with
      | Sum.inl a => .left a
      | Sum.inr mid =>
          match ofLex (ofLex mid).2 with
          | Sum.inl _ => .seed (ofLex mid).1
          | Sum.inr y => .copy (ofLex mid).1 y
  | Sum.inr b => .right b

theorem decode_encode (p : Pos κIndex Cluster Left Right) : decode (encode p) = p := by
  cases p <;> simp [decode, encode, ofLex_toLex]

theorem encode_injective :
    Function.Injective (encode : Pos κIndex Cluster Left Right → Code κIndex Cluster Left Right) :=
  fun a b h => by simpa [decode_encode] using congrArg decode h

/-- Anchors and seeds, with no cluster coordinate. The order on `Old` does not depend on `Cluster`. -/
def encodeOld : Old κIndex Left Right → OldCode κIndex Left Right
  | .left a => toLex (Sum.inl (toLex (Sum.inl a)))
  | .seed i => toLex (Sum.inl (toLex (Sum.inr i)))
  | .right a => toLex (Sum.inr a)

def decodeOld (c : OldCode κIndex Left Right) : Old κIndex Left Right :=
  match ofLex c with
  | Sum.inl inner =>
      match ofLex inner with
      | Sum.inl a => .left a
      | Sum.inr i => .seed i
  | Sum.inr b => .right b

theorem decodeOld_encode (o : Old κIndex Left Right) : decodeOld (encodeOld o) = o := by
  cases o <;> simp [decodeOld, encodeOld, ofLex_toLex]

theorem encodeOld_injective :
    Function.Injective (encodeOld : Old κIndex Left Right → OldCode κIndex Left Right) :=
  fun a b h => by simpa [decodeOld_encode] using congrArg decodeOld h

noncomputable instance : LinearOrder (Pos κIndex Cluster Left Right) :=
  LinearOrder.lift' (β := Code κIndex Cluster Left Right) encode encode_injective

noncomputable instance : LinearOrder (Old κIndex Left Right) :=
  LinearOrder.lift' encodeOld encodeOld_injective

theorem encode_left_lt_left {a b : Left} :
    encode (Pos.left a : Pos κIndex Cluster Left Right) <
      encode (Pos.left b : Pos κIndex Cluster Left Right) ↔ a < b := by
  simp only [encode]
  rw [Sum.Lex.inl_lt_inl_iff, Sum.Lex.inl_lt_inl_iff]

theorem encode_right_lt_right {a b : Right} :
    encode (Pos.right a : Pos κIndex Cluster Left Right) <
      encode (Pos.right b : Pos κIndex Cluster Left Right) ↔ a < b := by
  simp only [encode]
  rw [Sum.Lex.inr_lt_inr_iff]

theorem encode_seed_lt_seed {i j : κIndex} :
    encode (Pos.seed i : Pos κIndex Cluster Left Right) <
      encode (Pos.seed j : Pos κIndex Cluster Left Right) ↔ i < j := by
  simp only [encode]
  rw [Sum.Lex.inl_lt_inl_iff, Sum.Lex.inr_lt_inr_iff, Prod.Lex.toLex_lt_toLex]
  constructor
  · rintro (hij | ⟨-, hunit⟩)
    · exact hij
    · exact absurd (Sum.Lex.inl_lt_inl_iff.mp hunit) (lt_irrefl _)
  · intro hij
    exact Or.inl hij

theorem not_encode_seed_lt_left (i : κIndex) (a : Left) :
    ¬ encode (Pos.seed i : Pos κIndex Cluster Left Right) <
        encode (Pos.left a : Pos κIndex Cluster Left Right) := by
  intro h
  simp only [encode] at h
  rw [Sum.Lex.inl_lt_inl_iff] at h
  exact Sum.Lex.not_inr_lt_inl h

theorem not_encode_right_lt_left (a : Right) (b : Left) :
    ¬ encode (Pos.right a : Pos κIndex Cluster Left Right) <
        encode (Pos.left b : Pos κIndex Cluster Left Right) := by
  intro h
  simp only [encode] at h
  exact Sum.Lex.not_inr_lt_inl h

theorem not_encode_right_lt_seed (a : Right) (i : κIndex) :
    ¬ encode (Pos.right a : Pos κIndex Cluster Left Right) <
        encode (Pos.seed i : Pos κIndex Cluster Left Right) := by
  intro h
  simp only [encode] at h
  exact Sum.Lex.not_inr_lt_inl h

theorem encode_left_lt_copy (a : Left) (i : κIndex) (y : Cluster) :
    encode (Pos.left a : Pos κIndex Cluster Left Right) <
      encode (Pos.copy i y : Pos κIndex Cluster Left Right) := by
  simp only [encode]
  rw [Sum.Lex.inl_lt_inl_iff]
  exact Sum.Lex.inl_lt_inr _ _

theorem encode_copy_lt_right (i : κIndex) (y : Cluster) (b : Right) :
    encode (Pos.copy i y : Pos κIndex Cluster Left Right) <
      encode (Pos.right b : Pos κIndex Cluster Left Right) := by
  simp only [encode]
  exact Sum.Lex.inl_lt_inr _ _

theorem encode_copy_lt_copy {i j : κIndex} {y y' : Cluster} :
    encode (Pos.copy i y : Pos κIndex Cluster Left Right) <
      encode (Pos.copy j y' : Pos κIndex Cluster Left Right) ↔
        i < j ∨ (i = j ∧ y < y') := by
  simp only [encode]
  rw [Sum.Lex.inl_lt_inl_iff, Sum.Lex.inr_lt_inr_iff, Prod.Lex.toLex_lt_toLex,
    Sum.Lex.inr_lt_inr_iff]

theorem encode_left_lt_seed (a : Left) (i : κIndex) :
    encode (Pos.left a : Pos κIndex Cluster Left Right) <
      encode (Pos.seed i : Pos κIndex Cluster Left Right) := by
  simp only [encode]
  exact (Sum.Lex.inl_lt_inl_iff).2 (Sum.Lex.inl_lt_inr _ _)

theorem encode_left_lt_right (a : Left) (b : Right) :
    encode (Pos.left a : Pos κIndex Cluster Left Right) <
      encode (Pos.right b : Pos κIndex Cluster Left Right) := by
  simp only [encode]
  exact Sum.Lex.inl_lt_inr _ _

theorem encode_seed_lt_right (i : κIndex) (b : Right) :
    encode (Pos.seed i : Pos κIndex Cluster Left Right) <
      encode (Pos.right b : Pos κIndex Cluster Left Right) := by
  simp only [encode]
  exact Sum.Lex.inl_lt_inr _ _

theorem encodeOld_left_lt_left {a b : Left} :
    encodeOld (Old.left a : Old κIndex Left Right) <
      encodeOld (Old.left b : Old κIndex Left Right) ↔ a < b := by
  simp only [encodeOld]
  rw [Sum.Lex.inl_lt_inl_iff, Sum.Lex.inl_lt_inl_iff]

theorem encodeOld_right_lt_right {a b : Right} :
    encodeOld (Old.right a : Old κIndex Left Right) <
      encodeOld (Old.right b : Old κIndex Left Right) ↔ a < b := by
  simp only [encodeOld]
  rw [Sum.Lex.inr_lt_inr_iff]

theorem encodeOld_seed_lt_seed {i j : κIndex} :
    encodeOld (Old.seed i : Old κIndex Left Right) <
      encodeOld (Old.seed j : Old κIndex Left Right) ↔ i < j := by
  simp only [encodeOld]
  rw [Sum.Lex.inl_lt_inl_iff, Sum.Lex.inr_lt_inr_iff]

theorem encodeOld_not_seed_lt_left (i : κIndex) (a : Left) :
    ¬ encodeOld (Old.seed i : Old κIndex Left Right) <
        encodeOld (Old.left a : Old κIndex Left Right) := by
  intro h
  simp only [encodeOld] at h
  rw [Sum.Lex.inl_lt_inl_iff] at h
  exact Sum.Lex.not_inr_lt_inl h

theorem encodeOld_not_right_lt_left (a : Right) (b : Left) :
    ¬ encodeOld (Old.right a : Old κIndex Left Right) <
        encodeOld (Old.left b : Old κIndex Left Right) := by
  intro h
  simp only [encodeOld] at h
  exact Sum.Lex.not_inr_lt_inl h

theorem encodeOld_not_right_lt_seed (a : Right) (i : κIndex) :
    ¬ encodeOld (Old.right a : Old κIndex Left Right) <
        encodeOld (Old.seed i : Old κIndex Left Right) := by
  intro h
  simp only [encodeOld] at h
  exact Sum.Lex.not_inr_lt_inl h

theorem include_strict :
    StrictMono (includeOld : Old κIndex Left Right → Pos κIndex Cluster Left Right) := by
  intro a b hab
  cases a <;> cases b
  · exact encode_left_lt_left.2 (encodeOld_left_lt_left.1 hab)
  · exact encode_left_lt_seed _ _
  · exact encode_left_lt_right _ _
  · exact absurd hab (encodeOld_not_seed_lt_left _ _)
  · exact encode_seed_lt_seed.2 (encodeOld_seed_lt_seed.1 hab)
  · exact encode_seed_lt_right _ _
  · exact absurd hab (encodeOld_not_right_lt_left _ _)
  · exact absurd hab (encodeOld_not_right_lt_seed _ _)
  · exact encode_right_lt_right.2 (encodeOld_right_lt_right.1 hab)

noncomputable def includeEmb : Old κIndex Left Right ↪o Pos κIndex Cluster Left Right :=
  OrderEmbedding.ofStrictMono includeOld include_strict

theorem oldPoint_strictMono {ι : Type u} [LinearOrder ι] (point : Old κIndex Left Right → ι)
    (hLL : ∀ a b : Left, a < b → point (.left a) < point (.left b))
    (hLS : ∀ a i, point (.left a) < point (.seed i))
    (hLR : ∀ a b, point (.left a) < point (.right b))
    (hSS : ∀ i j, i < j → point (.seed i) < point (.seed j))
    (hSR : ∀ i b, point (.seed i) < point (.right b))
    (hRR : ∀ a b : Right, a < b → point (.right a) < point (.right b)) :
    StrictMono point := by
  intro a b hab
  cases a <;> cases b
  · exact hLL _ _ ((encodeOld_left_lt_left).1 hab)
  · exact hLS _ _
  · exact hLR _ _
  · exact absurd hab (encodeOld_not_seed_lt_left _ _)
  · exact hSS _ _ ((encodeOld_seed_lt_seed).1 hab)
  · exact hSR _ _
  · exact absurd hab (encodeOld_not_right_lt_left _ _)
  · exact absurd hab (encodeOld_not_right_lt_seed _ _)
  · exact hRR _ _ ((encodeOld_right_lt_right).1 hab)

def addedPair (z : {p : Pos κIndex Cluster Left Right // p ∉ Set.range includeOld}) :
    κIndex × Cluster :=
  match z with
  | ⟨.copy i y, _⟩ => (i, y)
  | ⟨.left a, h⟩ => False.elim (h ⟨.left a, rfl⟩)
  | ⟨.seed i, h⟩ => False.elim (h ⟨.seed i, rfl⟩)
  | ⟨.right a, h⟩ => False.elim (h ⟨.right a, rfl⟩)

theorem addedPair_eq (z : {p : Pos κIndex Cluster Left Right // p ∉ Set.range includeOld}) :
    z.1 = Pos.copy (addedPair z).1 (addedPair z).2 := by
  cases z with
  | mk p hp =>
    cases p with
    | copy _ _ => rfl
    | left a => exact False.elim (hp ⟨.left a, rfl⟩)
    | seed i => exact False.elim (hp ⟨.seed i, rfl⟩)
    | right a => exact False.elim (hp ⟨.right a, rfl⟩)

theorem patternAdded_card_le :
    #(Set.diff Set.univ (Set.range (⇑(includeEmb :
      Old κIndex Left Right ↪o Pos κIndex Cluster Left Right)))) ≤
      #κIndex * #Cluster := by
  let f : ↥(Set.diff Set.univ (Set.range (⇑(includeEmb :
      Old κIndex Left Right ↪o Pos κIndex Cluster Left Right)))) → κIndex × Cluster :=
    fun z => addedPair ⟨z.1, z.2.2⟩
  have hinj : Function.Injective f := by
    intro z₁ z₂ h
    apply Subtype.ext
    have h₁ := addedPair_eq ⟨z₁.1, z₁.2.2⟩
    have h₂ := addedPair_eq ⟨z₂.1, z₂.2.2⟩
    rw [h₁, h₂]
    exact congrArg (fun q : κIndex × Cluster => Pos.copy q.1 q.2) h
  have hprod : #(κIndex × Cluster) = #κIndex * #Cluster := by simp [mk_prod, lift_id]
  exact (mk_le_of_injective hinj).trans (le_of_eq hprod)

theorem cardOld_le : #(Old κIndex Left Right) ≤ #Left + (#κIndex + #Right) := by
  let f : Old κIndex Left Right → Left ⊕ (κIndex ⊕ Right)
    | .left a => Sum.inl a
    | .seed i => Sum.inr (Sum.inl i)
    | .right a => Sum.inr (Sum.inr a)
  have hinj : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp [f] at h <;> subst h <;> rfl
  refine (mk_le_of_injective hinj).trans ?_
  simp [mk_sum]

end

end SupportCopy

/-- The old index of a supporting position off the old chart. -/
def ChartSupport.asUnshared {I J : Type u} [LinearOrder I] [LinearOrder J]
    {C : ChartSupport I J} (s : C.support) (hs : s.1 ∉ Set.range (⇑C.old)) : C.unshared :=
  ⟨s.1, s.2, hs⟩

/-- That position, read in its own cut-cluster. -/
def ChartSupport.asCluster {I J : Type u} [LinearOrder I] [LinearOrder J]
    {C : ChartSupport I J} (s : C.support) (hs : s.1 ∉ Set.range (⇑C.old)) :
    ↥(C.clusterAt s.1) :=
  ⟨s.1, ⟨s.2, hs⟩, C.sameCut_refl s.1⟩

/-- **Infra `infra_69_copy_cluster`:** In the `i`th region, put a copy of the corresponding
cluster with its internal order.

`infra_69_disjoint_regions` supplies `κ` disjoint convex separators in the anchor slot.
`infra_69_richness_arity` bounds the cluster pattern by `σ + κ`. `OrderPatternRealized`,
which cut filling gives, embeds every index's copy of that cluster into the slot, on the
cut above the increasing `regionPoint` seeds. The landing region of each copy is the convex
hull of its image. -/
theorem infra_69_copy_cluster {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {σ κ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hκ : ℵ₀ ≤ κ)
    (hsup : #C.support ≤ σ) (hfill : OrderFillsCuts (σ + κ) I)
    {x : J} (hx : x ∈ C.unshared) (κIndex : Type u) (hκI : #κIndex ≤ κ) :
    ∃ (separator region : κIndex → Set I)
      (copy : κIndex → (↥(C.clusterAt x) ↪o I)),
      (∀ i, separator i ⊆ C.slotCarrier x) ∧
      (∀ i, IsConvexRegion (separator i)) ∧
      (∀ i, (separator i).Nonempty) ∧
      (∀ i j, i ≠ j → Disjoint (separator i) (separator j)) ∧
      (∀ i y, (copy i y : I) ∈ region i) ∧
      (∀ i, region i ⊆ C.slotCarrier x) ∧
      (∀ i, IsConvexRegion (region i)) ∧
      (∀ i j, i ≠ j → Disjoint (region i) (region j)) ∧
      (∀ i y (a : C.anchorIdx),
        (a.1 < copy i y ↔ C.old a.1 < x) ∧ (copy i y < a.1 ↔ x < C.old a.1)) := by
  classical
  obtain ⟨hAnch, hCl, _⟩ := infra_69_richness_arity C hσ hκ hsup x hx
  have hη : ℵ₀ ≤ σ + κ := hσ.trans (self_le_add_right σ κ)
  have hκle : κ ≤ σ + κ := by
    calc
      κ ≤ κ + σ := self_le_add_right κ σ
      _ = σ + κ := add_comm _ _
  have hanchors : #C.anchors ≤ σ + κ :=
    (infra_69_anchor_bound C hσ hsup).trans (add_le_add le_rfl hκ)
  have hidx : #κIndex ≤ σ + κ := hκI.trans hκle
  obtain ⟨lo, wf⟩ := exists_wellFoundedLT κIndex
  letI : LinearOrder κIndex := lo
  haveI : WellFoundedLT κIndex := wf
  obtain ⟨separator, hsepSlot, hsepConv, hsepNe, hsepDisj⟩ :=
    infra_69_disjoint_regions C hη hκle hanchors hfill hx κIndex hκI
  let p : κIndex → I := C.regionPoint hfill x
  have hp_spec := fun i => C.regionPoint_spec hη hanchors hidx hfill x i
  let Left := {a : C.anchorIdx // C.old a.1 < x}
  let Right := {a : C.anchorIdx // x < C.old a.1}
  let Cluster := ↥(C.clusterAt x)
  let oldPoint : SupportCopy.Old κIndex Left Right → I
    | .left a => a.1.1
    | .seed i => p i
    | .right b => b.1.1
  have hleft_p : ∀ a : Left, ∀ i, a.1.1 < p i := by
    intro a i
    exact (hp_spec i).slot.aboveLeft a.1.1 ⟨a.1.2, a.2⟩
  have hp_right : ∀ i, ∀ b : Right, p i < b.1.1 := by
    intro i b
    exact (hp_spec i).slot.belowRight b.1.1 ⟨b.1.2, b.2⟩
  have hleft_right : ∀ a : Left, ∀ b : Right, a.1.1 < b.1.1 := by
    intro a b
    exact (C.old.lt_iff_lt).1 (lt_trans a.2 b.2)
  have hp_mono : StrictMono p := fun i j hij => (hp_spec j).abovePrev i hij
  have hold : StrictMono oldPoint :=
    SupportCopy.oldPoint_strictMono oldPoint
      (fun a b h => Subtype.coe_lt_coe.mp (Subtype.coe_lt_coe.mp h))
      (fun a i => hleft_p a i)
      (fun a b => hleft_right a b)
      (fun i j hij => hp_mono hij)
      (fun i b => hp_right i b)
      (fun a b h => Subtype.coe_lt_coe.mp (Subtype.coe_lt_coe.mp h))
  let fEmb : SupportCopy.Old κIndex Left Right ↪o I :=
    OrderEmbedding.ofStrictMono oldPoint hold
  have hinjL : Function.Injective (fun a : Left => (a.1 : C.anchorIdx)) :=
    fun a b h => Subtype.ext h
  have hinjR : Function.Injective (fun a : Right => (a.1 : C.anchorIdx)) :=
    fun a b h => Subtype.ext h
  have hLcard : #Left ≤ σ + κ := (mk_le_of_injective hinjL).trans hAnch
  have hRcard : #Right ≤ σ + κ := (mk_le_of_injective hinjR).trans hAnch
  have hOld : #(SupportCopy.Old κIndex Left Right) ≤ σ + κ := by
    refine (SupportCopy.cardOld_le (κIndex := κIndex) (Left := Left) (Right := Right)).trans ?_
    have hSR : #κIndex + #Right ≤ σ + κ := by
      calc
        #κIndex + #Right ≤ (σ + κ) + (σ + κ) := add_le_add hidx hRcard
        _ = σ + κ := by rw [add_eq_max hη, max_self]
    calc
      #Left + (#κIndex + #Right) ≤ (σ + κ) + (σ + κ) := add_le_add hLcard hSR
      _ = σ + κ := by rw [add_eq_max hη, max_self]
  have hAdded :
      #(Set.diff Set.univ (Set.range (⇑(SupportCopy.includeEmb :
        SupportCopy.Old κIndex Left Right ↪o
          SupportCopy.Pos κIndex Cluster Left Right)))) ≤ σ + κ := by
    refine (SupportCopy.patternAdded_card_le (κIndex := κIndex) (Cluster := Cluster)
      (Left := Left) (Right := Right)).trans ?_
    have hmul : #κIndex * #Cluster ≤ κ * (σ + κ) := mul_le_mul' hκI hCl
    have hmax : κ * (σ + κ) ≤ max κ (σ + κ) := mul_le_max_of_aleph0_le_left hκ
    exact hmul.trans (hmax.trans (by rw [max_eq_right hκle]))
  let pat : OrderPattern (σ + κ) (SupportCopy.Old κIndex Left Right)
      (SupportCopy.Pos κIndex Cluster Left Right) :=
    { emb := SupportCopy.includeEmb
      card_old := hOld
      cardAdded := hAdded }
  have hreal : OrderPatternRealized (σ + κ) I :=
    orderPatternRealized_of_fillsCuts hη hfill
  obtain ⟨g, hg⟩ := hreal pat fEmb
  have hgo : ∀ o, g (SupportCopy.includeEmb o) = oldPoint o := by
    intro o
    simpa [pat, fEmb, OrderEmbedding.coe_ofStrictMono] using hg o
  let copyFun : κIndex → Cluster → I := fun i y => g (SupportCopy.Pos.copy i y)
  have hcopyMono : ∀ i, StrictMono (copyFun i) := by
    intro i y y' hy
    have hlt : (SupportCopy.Pos.copy i y : SupportCopy.Pos κIndex Cluster Left Right) <
        SupportCopy.Pos.copy i y' :=
      SupportCopy.encode_copy_lt_copy.mpr (Or.inr ⟨rfl, hy⟩)
    exact (g.lt_iff_lt).2 hlt
  let copy : κIndex → (Cluster ↪o I) := fun i =>
    OrderEmbedding.ofStrictMono (copyFun i) (hcopyMono i)
  have hbetween : ∀ i j, i < j → ∀ y z, copyFun i y < copyFun j z := by
    intro i j hij y z
    have hlt : (SupportCopy.Pos.copy i y : SupportCopy.Pos κIndex Cluster Left Right) <
        SupportCopy.Pos.copy j z :=
      SupportCopy.encode_copy_lt_copy.mpr (Or.inl hij)
    exact (g.lt_iff_lt).2 hlt
  have hanchor : ∀ i y (a : C.anchorIdx), a.1 < copyFun i y ↔ C.old a.1 < x := by
    intro i y a
    rcases lt_trichotomy (C.old a.1) x with hL | heq | hR
    · let al : Left := ⟨a, hL⟩
      have henc :
          (SupportCopy.includeEmb (SupportCopy.Old.left al) :
            SupportCopy.Pos κIndex Cluster Left Right) <
            SupportCopy.Pos.copy i y :=
        SupportCopy.encode_left_lt_copy al i y
      have hpt : oldPoint (SupportCopy.Old.left al) < copyFun i y := by
        have hlt : g (SupportCopy.includeEmb (SupportCopy.Old.left al)) < copyFun i y :=
          (g.lt_iff_lt).2 henc
        simpa [hgo (SupportCopy.Old.left al)] using hlt
      have hcoe : oldPoint (SupportCopy.Old.left al) = a.1 := rfl
      exact iff_of_true (by simpa [hcoe] using hpt) hL
    · exact absurd heq (fun h => hx.2 ⟨a.1, h⟩)
    · let ar : Right := ⟨a, hR⟩
      have henc : (SupportCopy.Pos.copy i y : SupportCopy.Pos κIndex Cluster Left Right) <
          SupportCopy.includeEmb (SupportCopy.Old.right ar) :=
        SupportCopy.encode_copy_lt_right i y ar
      have hpt : copyFun i y < oldPoint (SupportCopy.Old.right ar) := by
        have hlt : copyFun i y < g (SupportCopy.includeEmb (SupportCopy.Old.right ar)) :=
          (g.lt_iff_lt).2 henc
        simpa [hgo (SupportCopy.Old.right ar)] using hlt
      have hcoe : oldPoint (SupportCopy.Old.right ar) = a.1 := rfl
      exact iff_of_false (by
        have : copyFun i y < a.1 := by simpa [hcoe] using hpt
        exact not_lt_of_gt this) (not_lt_of_gt hR)
  have hanchorR : ∀ i y (a : C.anchorIdx), copyFun i y < a.1 ↔ x < C.old a.1 := by
    intro i y a
    rcases lt_trichotomy (C.old a.1) x with hL | heq | hR
    · have hlt : a.1 < copyFun i y := (hanchor i y a).mpr hL
      exact iff_of_false (not_lt_of_gt hlt) (not_lt_of_gt hL)
    · exact absurd heq (fun h => hx.2 ⟨a.1, h⟩)
    · let ar : Right := ⟨a, hR⟩
      have henc : (SupportCopy.Pos.copy i y : SupportCopy.Pos κIndex Cluster Left Right) <
          SupportCopy.includeEmb (SupportCopy.Old.right ar) :=
        SupportCopy.encode_copy_lt_right i y ar
      have hpt : copyFun i y < oldPoint (SupportCopy.Old.right ar) := by
        have hlt : copyFun i y < g (SupportCopy.includeEmb (SupportCopy.Old.right ar)) :=
          (g.lt_iff_lt).2 henc
        simpa [hgo (SupportCopy.Old.right ar)] using hlt
      have hcoe : oldPoint (SupportCopy.Old.right ar) = a.1 := rfl
      exact iff_of_true (by simpa [hcoe] using hpt) hR
  have hcopySlot : ∀ i y, copyFun i y ∈ C.slotCarrier x := by
    intro i y u hu
    obtain ⟨j, hj⟩ := C.exists_old_index hu
    have hjA : C.old j ∈ C.anchors := by simpa [hj] using hu
    have hcomp : C.old j < C.old (copyFun i y) ↔ j < copyFun i y := C.old.lt_iff_lt
    have hchain := hcomp.trans (hanchor i y ⟨j, hjA⟩)
    simpa [hj] using hchain
  let region : κIndex → Set I := fun i => convexHull (Set.range (copyFun i))
  have hregionSlot : ∀ i, region i ⊆ C.slotCarrier x := by
    intro i
    exact convexHull_subset_of_convex (C.slotCarrier_convex x)
      (fun z hz => by
        rcases hz with ⟨y, rfl⟩
        exact hcopySlot i y)
  have hdisjR : ∀ i j, i ≠ j → Disjoint (region i) (region j) := by
    intro i j hne
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exact convexHull_disjoint_of_lt fun a ha b hb => by
        rcases ha with ⟨y, rfl⟩
        rcases hb with ⟨z, rfl⟩
        exact hbetween i j hlt y z
    · exact absurd heq hne
    · exact (convexHull_disjoint_of_lt fun a ha b hb => by
        rcases ha with ⟨y, rfl⟩
        rcases hb with ⟨z, rfl⟩
        exact hbetween j i hgt y z).symm
  refine ⟨separator, region, copy, hsepSlot, hsepConv, hsepNe, hsepDisj, ?_, hregionSlot,
      fun i => convexHull_convex _, hdisjR, ?_⟩
  · intro i y
    exact subset_convexHull _ ⟨y, rfl⟩
  · intro i y a
    exact ⟨by simpa [copy, OrderEmbedding.coe_ofStrictMono] using hanchor i y a,
      by simpa [copy, OrderEmbedding.coe_ofStrictMono] using hanchorR i y a⟩

/-- **Infra `infra_69_interpret_copies`:** Use the original labels and the unchanged shared
positions to obtain `vᵢ ∈ A`.

Shared positions stay on their old indices. Each unshared position is replaced by its copy,
which is an index of the old chart, so every position of `vᵢ` lies on the chart of `A`.
Labels are the original ones. -/
theorem infra_69_interpret_copies
    {I J Lab : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) (label : C.support → Lab) {κIndex : Type u}
    (copy : ∀ x : C.unshared, κIndex → ↥(C.clusterAt x.1) ↪o I) :
    ∃ (position : κIndex → C.support → I) (label' : κIndex → C.support → Lab),
      (∀ i s, label' i s = label s) ∧
      (∀ i s, (hs : s.1 ∈ C.shared) → C.old (position i s) = s.1) ∧
      (∀ i s, (hu : s.1 ∉ Set.range (⇑C.old)) →
        position i s = copy (C.asUnshared s hu) i (C.asCluster s hu)) := by
  classical
  let position : κIndex → C.support → I := fun i s =>
    if h : ∃ j : I, C.old j = s.1 then
      Classical.choose h
    else
      copy
        (C.asUnshared s (by
          intro hr
          exact h (Set.mem_range.mp hr)))
        i
        (C.asCluster s (by
          intro hr
          exact h (Set.mem_range.mp hr)))
  refine ⟨position, fun _ s => label s, fun _ _ => rfl, ?_, ?_⟩
  · intro i s hs
    have hex : ∃ j : I, C.old j = s.1 := Set.mem_range.mp hs.2
    simp only [position]
    split
    · next h => exact Classical.choose_spec h
    · next h => exact absurd hex h
  · intro i s hu
    simp only [position]
    split
    · next h => exact absurd (Set.mem_range.mpr h) hu
    · rfl

/-- **Infra `infra_69_choose_supports`:** Choose a query `Z` and one finite support for each
of its elements. -/
theorem infra_69_choose_supports {J Z : Type u} (avail : Z → Set (Set J))
    (hfin : ∀ z s, s ∈ avail z → s.Finite) (hne : ∀ z, (avail z).Nonempty) :
    ∃ support : Z → Set J, ∀ z, support z ∈ avail z ∧ (support z).Finite := by
  classical
  exact ⟨fun z => Classical.choose (hne z),
    fun z => ⟨Classical.choose_spec (hne z), hfin z _ (Classical.choose_spec (hne z))⟩⟩

/-- **Infra `infra_69_whole_block_diff`:** If these supports avoid every region used for the
`i`th copies, then each copied cluster and the original cluster can differ relative to the
query only by passing whole blocks of parameter positions.

A query set disjoint from a convex region lies entirely to one side of any block inside that
region. An old-chart query cannot split the original cluster: a point of the old chart is not
an unshared cluster point, and the cluster is one strict cut. -/
theorem infra_69_whole_block_diff {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {x : J} (_hx : x ∈ C.unshared)
    {region block queryI : Set I} (hconv : IsConvexRegion region) (hblock : block ⊆ region)
    (havoidI : Disjoint queryI region) {queryJ : Set J}
    (hq : queryJ ⊆ Set.range (⇑C.old)) :
    (∀ q ∈ queryI, (∀ b ∈ block, b < q) ∨ (∀ b ∈ block, q < b)) ∧
    (∀ q ∈ queryJ, (∀ y ∈ C.clusterAt x, y < q) ∨ (∀ y ∈ C.clusterAt x, q < y)) := by
  refine ⟨?_, ?_⟩
  · intro q hqmem
    by_contra hbad
    rw [not_or] at hbad
    obtain ⟨b1, hb1⟩ := not_forall.mp hbad.1
    obtain ⟨b2, hb2⟩ := not_forall.mp hbad.2
    rw [not_imp] at hb1
    rw [not_imp] at hb2
    obtain ⟨hb1, h1⟩ := hb1
    obtain ⟨hb2, h2⟩ := hb2
    have hqreg : q ∈ region :=
      hconv b2 (hblock hb2) b1 (hblock hb1) q (le_of_not_gt h2) (le_of_not_gt h1)
    exact (Set.mem_empty_iff_false q).1 ((Set.disjoint_iff.mp havoidI) ⟨hqmem, hqreg⟩)
  · intro q hqmem
    obtain ⟨i, rfl⟩ := hq hqmem
    by_contra hbad
    rw [not_or] at hbad
    obtain ⟨y, hyimp⟩ := not_forall.mp hbad.1
    obtain ⟨z, hzimp⟩ := not_forall.mp hbad.2
    rw [not_imp] at hyimp
    rw [not_imp] at hzimp
    obtain ⟨hy, hynot⟩ := hyimp
    obtain ⟨hz, hznot⟩ := hzimp
    have hiy : C.old i ≤ y := le_of_not_gt hynot
    have hzi : z ≤ C.old i := le_of_not_gt hznot
    by_cases hqe : C.old i = y
    · exact hy.1.2 ⟨i, hqe⟩
    · by_cases hqz : C.old i = z
      · exact hz.1.2 ⟨i, hqz⟩
      · have hltz : z < C.old i := lt_of_le_of_ne hzi (Ne.symm hqz)
        have hlty : C.old i < y := lt_of_le_of_ne hiy hqe
        have hcut : C.SameCut y z := C.sameCut_trans (C.sameCut_symm hy.2) hz.2
        exact not_lt_of_gt hltz ((hcut i).1 hlty)

/-- **Infra `infra_69_no_internal_hits`:** There are no hits or separations inside a cluster.
A cluster point lies off the old chart, two points of one cluster determine the same strict
cut, and no old position lies strictly between them. -/
theorem infra_69_no_internal_hits {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {x : J} :
    (∀ y ∈ C.clusterAt x, y ∉ Set.range (⇑C.old)) ∧
    (∀ y ∈ C.clusterAt x, ∀ z ∈ C.clusterAt x, C.SameCut y z) ∧
    (∀ y ∈ C.clusterAt x, ∀ z ∈ C.clusterAt x, ∀ i : I,
      ¬ (y < C.old i ∧ C.old i < z)) := by
  refine ⟨fun y hy => hy.1.2, ?_, ?_⟩
  · intro y hy z hz
    exact C.sameCut_trans (C.sameCut_symm hy.2) hz.2
  · intro y hy z hz i ⟨hyl, hiz⟩
    have hcut : C.SameCut y z := C.sameCut_trans (C.sameCut_symm hy.2) hz.2
    exact not_lt_of_gt hyl ((hcut i).2 hiz)

namespace ChartSupport

variable {I J : Type u} [LinearOrder I] [LinearOrder J] (C : ChartSupport I J)

/-- One point of a cut-cluster. -/
noncomputable def clusterRepPoint (q : C.Cluster) : C.unshared :=
  Classical.choose (Quotient.exists_rep q)

theorem clusterRepPoint_spec (q : C.Cluster) : C.clusterMk (C.clusterRepPoint q) = q :=
  Classical.choose_spec (Quotient.exists_rep q)

/-- Its position in the placement order. -/
noncomputable def clusterRep (q : C.Cluster) : J := (C.clusterRepPoint q).1

theorem clusterRep_injective : Function.Injective C.clusterRep := by
  intro q₁ q₂ h
  have hs : C.clusterRepPoint q₁ = C.clusterRepPoint q₂ := Subtype.ext h
  rw [← C.clusterRepPoint_spec q₁, ← C.clusterRepPoint_spec q₂, hs]

noncomputable instance : LinearOrder C.Cluster :=
  LinearOrder.lift' C.clusterRep C.clusterRep_injective

theorem cluster_lt_iff {q₁ q₂ : C.Cluster} : q₁ < q₂ ↔ C.clusterRep q₁ < C.clusterRep q₂ :=
  Iff.rfl

/-- An anchor lies strictly between two unshared points of different cuts, with the left
point first. -/
theorem exists_anchor_between {y z : C.unshared} (hlt : y.1 < z.1)
    (hcut : ¬ C.SameCut y.1 z.1) :
    ∃ a : C.anchorIdx, y.1 < C.old a.1 ∧ C.old a.1 < z.1 := by
  let p : C.sepIndex := ⟨(y.1, z.1), y.2, z.2, hcut⟩
  have hspec := C.sepAt_spec p
  have ha : C.old (C.sepAt p) ∈ C.anchors := Or.inr ⟨p, rfl⟩
  let a : C.anchorIdx := ⟨C.sepAt p, ha⟩
  have hyne : y.1 ≠ C.old a.1 := fun h => y.2.2 ⟨a.1, h.symm⟩
  by_cases hy : C.old a.1 < y.1
  · have hnot : ¬ C.old a.1 < z.1 := by
      intro hz
      exact hspec (propext (iff_of_true hy hz))
    exact absurd (hy.trans (hlt.trans_le (le_of_not_gt hnot))) (lt_irrefl _)
  · have hy' : y.1 < C.old a.1 := lt_of_le_of_ne (le_of_not_gt hy) hyne
    have hz : C.old a.1 < z.1 := by
      by_contra hnot
      exact hspec (propext (iff_of_false hy hnot))
    exact ⟨a, hy', hz⟩

/-- Distinct cuts are separated by an anchor, so the left cut lies entirely left of the right. -/
theorem cluster_points_lt {y z : C.unshared} (hlt : y.1 < z.1)
    (hcut : C.clusterMk y ≠ C.clusterMk z) (y' z' : C.unshared)
    (hy : C.clusterMk y' = C.clusterMk y) (hz : C.clusterMk z' = C.clusterMk z) :
    y'.1 < z'.1 := by
  have hne : ¬ C.SameCut y.1 z.1 := fun hsame => hcut (Quotient.sound hsame)
  obtain ⟨a, hyl, hzr⟩ := C.exists_anchor_between hlt hne
  have hyS : C.SameCut y'.1 y.1 := Quotient.exact hy
  have hzS : C.SameCut z'.1 z.1 := Quotient.exact hz
  have hnoty : ¬ C.old a.1 < y.1 := not_lt_of_gt hyl
  have hnoty' : ¬ C.old a.1 < y'.1 := fun h => hnoty ((hyS a.1).mp h)
  have hy' : y'.1 < C.old a.1 := by
    exact lt_of_le_of_ne (le_of_not_gt hnoty') (fun h => y'.2.2 ⟨a.1, h.symm⟩)
  exact hy'.trans ((hzS a.1).mpr hzr)

theorem clusterMk_mono : Monotone C.clusterMk := by
  intro y z hle
  rcases lt_or_eq_of_le hle with hlt | heq
  · by_cases hs : C.clusterMk y = C.clusterMk z
    · exact le_of_eq hs
    · have hrep : C.clusterRep (C.clusterMk y) < C.clusterRep (C.clusterMk z) :=
        C.cluster_points_lt hlt hs
          (C.clusterRepPoint (C.clusterMk y)) (C.clusterRepPoint (C.clusterMk z))
          (C.clusterRepPoint_spec (C.clusterMk y)) (C.clusterRepPoint_spec (C.clusterMk z))
      exact (C.cluster_lt_iff.mpr hrep).le
  · exact le_of_eq (congrArg C.clusterMk heq)

theorem unshared_lt_of_cluster_lt {y z : C.unshared} (h : C.clusterMk y < C.clusterMk z) :
    y.1 < z.1 := by
  have hrep : C.clusterRep (C.clusterMk y) < C.clusterRep (C.clusterMk z) :=
    C.cluster_lt_iff.mp h
  exact C.cluster_points_lt
    (y := C.clusterRepPoint (C.clusterMk y)) (z := C.clusterRepPoint (C.clusterMk z)) hrep
    (fun heq => ne_of_lt h
      ((C.clusterRepPoint_spec _).symm.trans (heq.trans (C.clusterRepPoint_spec _))))
    y z (C.clusterRepPoint_spec _).symm (C.clusterRepPoint_spec _).symm

end ChartSupport

/-- One index of the off-hit copy: the unshared supports, their copies in disjoint convex
regions, and the parameter positions (the query, together with the anchors). -/
structure ChartOffHit (I J : Type u) [LinearOrder I] [LinearOrder J] where
  C : ChartSupport I J
  copy : C.unshared ↪o I
  /-- Both sides of the anchor comparison, as exported by `infra_69_copy_cluster`. -/
  hslot : ∀ (y : C.unshared) (a : C.anchorIdx),
    (a.1 < copy y ↔ C.old a.1 < y.1) ∧ (copy y < a.1 ↔ y.1 < C.old a.1)
  region : C.Cluster → Set I
  copy_mem : ∀ y, (copy y : I) ∈ region (C.clusterMk y)
  convex : ∀ q, IsConvexRegion (region q)
  disjoint_region : ∀ q q', q ≠ q' → Disjoint (region q) (region q')
  query : Set I
  query_off : ∀ q, Disjoint query (region q)
  nonempty_unshared : Nonempty C.unshared

namespace ChartOffHit

variable {I J : Type u} [LinearOrder I] [LinearOrder J] (H : ChartOffHit I J)

instance : Nonempty H.C.unshared := H.nonempty_unshared

/-- Query indices and anchor indices. These are the parameter positions of the interchange. -/
abbrev Parm : Type u := {i : I // i ∈ H.query ∨ H.C.old i ∈ H.C.anchors}

def embCl : H.C.unshared ↪o J :=
  OrderEmbedding.subtype (· ∈ H.C.unshared)

def embParm : H.Parm ↪o J :=
  (OrderEmbedding.subtype (fun i => i ∈ H.query ∨ H.C.old i ∈ H.C.anchors)).trans H.C.old

def embCopy : H.C.unshared ↪o J := H.copy.trans H.C.old

@[simp] theorem embCl_apply (c : H.C.unshared) : H.embCl c = c.1 := rfl

@[simp] theorem embParm_apply (p : H.Parm) : H.embParm p = H.C.old p.1 := rfl

@[simp] theorem embCopy_apply (c : H.C.unshared) : H.embCopy c = H.C.old (H.copy c) := rfl

theorem disjCl (c : H.C.unshared) (p : H.Parm) : H.embCl c ≠ H.embParm p := by
  intro h
  rw [embCl_apply, embParm_apply] at h
  exact c.2.2 ⟨p.1, h.symm⟩

theorem disjCopy (c : H.C.unshared) (p : H.Parm) : H.embCopy c ≠ H.embParm p := by
  intro h
  have hidx : H.copy c = p.1 := H.C.old.injective (by
    rw [← embCopy_apply, ← embParm_apply]; exact h)
  rcases p.2 with hq | ha
  · exact (Set.disjoint_left.mp (H.query_off (H.C.clusterMk c)) hq) (hidx ▸ H.copy_mem c)
  · let a : H.C.anchorIdx := ⟨p.1, ha⟩
    have hslot := H.hslot c a
    have hnotL : ¬ a.1 < H.copy c := by
      rw [← hidx]
      exact lt_irrefl _
    have hnotR : ¬ H.copy c < a.1 := by
      rw [hidx]
      exact lt_irrefl _
    have hnot1 : ¬ H.C.old a.1 < c.1 := fun hlt => hnotL (hslot.1.mpr hlt)
    have hnot2 : ¬ c.1 < H.C.old a.1 := fun hlt => hnotR (hslot.2.mpr hlt)
    have heq : c.1 = H.C.old a.1 := by
      rcases lt_trichotomy c.1 (H.C.old a.1) with hlt | heq | hgt
      · exact absurd hlt hnot2
      · exact heq
      · exact absurd hgt hnot1
    exact c.2.2 ⟨a.1, heq.symm⟩

theorem blockOrig {c₁ c₂ : H.C.unshared} (hs : H.C.clusterMk c₁ = H.C.clusterMk c₂)
    (p : H.Parm) :
    H.embParm p < H.embCl c₁ ↔ H.embParm p < H.embCl c₂ := by
  have hcut : H.C.SameCut c₁.1 c₂.1 := Quotient.exact hs
  simpa [embParm_apply, embCl_apply] using hcut p.1

theorem point_lt_anchor_iff (c : H.C.unshared) (p : H.Parm) (ha : H.C.old p.1 ∈ H.C.anchors) :
    c.1 < H.C.old p.1 ↔ ¬ H.C.old p.1 < c.1 := by
  constructor
  · exact fun h => not_lt_of_gt h
  · intro hnot
    rcases lt_trichotomy c.1 (H.C.old p.1) with hlt | heq | hgt
    · exact hlt
    · exact (c.2.2 ⟨p.1, heq.symm⟩).elim
    · exact absurd hgt hnot

theorem blockCopy {c₁ c₂ : H.C.unshared} (hs : H.C.clusterMk c₁ = H.C.clusterMk c₂)
    (p : H.Parm) :
    H.embParm p < H.embCopy c₁ ↔ H.embParm p < H.embCopy c₂ := by
  simp only [embParm_apply, embCopy_apply, H.C.old.lt_iff_lt]
  rcases p.2 with hq | ha
  · have hmem₁ : H.copy c₁ ∈ H.region (H.C.clusterMk c₁) := H.copy_mem c₁
    have hmem₂ : H.copy c₂ ∈ H.region (H.C.clusterMk c₁) := by
      simpa [hs] using H.copy_mem c₂
    constructor
    · intro hlt
      by_contra hnot
      rcases lt_or_eq_of_le (le_of_not_gt hnot) with h2 | heq
      · exact (Set.disjoint_left.mp (H.query_off (H.C.clusterMk c₁)) hq)
          (H.convex _ (H.copy c₂) hmem₂ (H.copy c₁) hmem₁ p.1 (le_of_lt h2) (le_of_lt hlt))
      · exact (Set.disjoint_left.mp (H.query_off (H.C.clusterMk c₁)) hq) (heq.symm ▸ hmem₂)
    · intro hlt
      by_contra hnot
      rcases lt_or_eq_of_le (le_of_not_gt hnot) with h1 | heq
      · exact (Set.disjoint_left.mp (H.query_off (H.C.clusterMk c₁)) hq)
          (H.convex _ (H.copy c₁) hmem₁ (H.copy c₂) hmem₂ p.1 (le_of_lt h1) (le_of_lt hlt))
      · exact (Set.disjoint_left.mp (H.query_off (H.C.clusterMk c₁)) hq) (heq.symm ▸ hmem₁)
  · let a : H.C.anchorIdx := ⟨p.1, ha⟩
    have hcut : H.C.SameCut c₁.1 c₂.1 := Quotient.exact hs
    have hside : c₁.1 < H.C.old p.1 ↔ c₂.1 < H.C.old p.1 := by
      rw [H.point_lt_anchor_iff c₁ p ha, H.point_lt_anchor_iff c₂ p ha, hcut p.1]
    have hflip (c : H.C.unshared) : H.C.old p.1 < c.1 ↔ ¬ c.1 < H.C.old p.1 := by
      constructor
      · exact fun h => not_lt_of_gt h
      · intro hnot
        rcases lt_trichotomy (H.C.old p.1) c.1 with hlt | heq | hgt
        · exact hlt
        · exact (c.2.2 ⟨p.1, heq⟩).elim
        · exact absurd hgt hnot
    have horig : H.C.old p.1 < c₁.1 ↔ H.C.old p.1 < c₂.1 :=
      (hflip c₁).trans (hside.not.trans (hflip c₂).symm)
    exact (H.hslot c₁ a).1.trans (horig.trans (H.hslot c₂ a).1.symm)

/-- A parameter that crosses one cluster lies on the same side of every other cluster in the
original order and in the copy. -/
theorem stable (c₁ c₂ : H.C.unshared) (p : H.Parm)
    (hcross : (H.embParm p < H.embCl c₁) ≠ (H.embParm p < H.embCopy c₁))
    (hne : H.C.clusterMk c₁ ≠ H.C.clusterMk c₂) :
    H.embParm p < H.embCl c₂ ↔ H.embParm p < H.embCopy c₂ := by
  have hcross' : (H.C.old p.1 < c₁.1) ≠ (p.1 < H.copy c₁) := by
    simpa [embParm_apply, embCl_apply, embCopy_apply, H.C.old.lt_iff_lt] using hcross
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hpts : c₁.1 < c₂.1 := H.C.unshared_lt_of_cluster_lt hlt
    obtain ⟨a, hleft, hright⟩ := H.C.exists_anchor_between hpts
      (fun hsame => ne_of_lt hlt (Quotient.sound hsame))
    have hcopyL : H.copy c₁ < a.1 := (H.hslot c₁ a).2.mpr hleft
    have hcopyR : a.1 < H.copy c₂ := (H.hslot c₂ a).1.mpr hright
    have hp : p.1 < a.1 := by
      by_contra hge
      have hle : a.1 ≤ p.1 := le_of_not_gt hge
      have hnotCopy : ¬ p.1 < H.copy c₁ := not_lt_of_gt (hcopyL.trans_le hle)
      have hnotOrig : ¬ H.C.old p.1 < c₁.1 :=
        not_lt_of_gt (hleft.trans_le ((H.C.old.le_iff_le).mpr hle))
      exact hcross' (propext (iff_of_false hnotOrig hnotCopy))
    have horig : H.C.old p.1 < c₂.1 := ((H.C.old.lt_iff_lt).mpr hp).trans hright
    have hcopy : p.1 < H.copy c₂ := hp.trans hcopyR
    simp only [embParm_apply, embCl_apply, embCopy_apply, H.C.old.lt_iff_lt]
    exact iff_of_true horig hcopy
  · have hpts : c₂.1 < c₁.1 := H.C.unshared_lt_of_cluster_lt hgt
    obtain ⟨a, hleft, hright⟩ := H.C.exists_anchor_between hpts
      (fun hsame => ne_of_lt hgt (Quotient.sound hsame))
    have hcopyL : H.copy c₂ < a.1 := (H.hslot c₂ a).2.mpr hleft
    have hcopyR : a.1 < H.copy c₁ := (H.hslot c₁ a).1.mpr hright
    have hp : a.1 < p.1 := by
      by_contra hge
      have hle : p.1 ≤ a.1 := le_of_not_gt hge
      have hcopyYes : p.1 < H.copy c₁ := lt_of_le_of_lt hle hcopyR
      have horigYes : H.C.old p.1 < c₁.1 :=
        lt_of_le_of_lt ((H.C.old.le_iff_le).mpr hle) hright
      exact hcross' (propext (iff_of_true horigYes hcopyYes))
    have hnotOrig : ¬ H.C.old p.1 < c₂.1 :=
      not_lt_of_gt (lt_trans hleft ((H.C.old.lt_iff_lt).mpr hp))
    have hnotCopy : ¬ p.1 < H.copy c₂ := not_lt_of_gt (lt_trans hcopyL hp)
    simp only [embParm_apply, embCl_apply, embCopy_apply, H.C.old.lt_iff_lt]
    exact iff_of_false hnotOrig hnotCopy

/-- The chart copy as one block interchange: each cut-cluster is a block, and the parameters
it passes are the other block of that region. -/
noncomputable def interchange : CopyInterchange H.C.unshared H.Parm J H.C.Cluster where
  embCl := H.embCl
  embCopy := H.embCopy
  embParm := H.embParm
  slot := H.C.clusterMk
  slot_mono := H.C.clusterMk_mono
  slot_reflect := fun h => H.C.unshared_lt_of_cluster_lt h
  disjCl := H.disjCl
  disjCopy := H.disjCopy
  blockOrig := H.blockOrig
  blockCopy := H.blockCopy
  stable := H.stable

end ChartOffHit

/-- **Infra `infra_69_lem61_off_hits`:** Their anchor slots are disjoint, so Lemma 6.1 gives
`D(vᵢ, Z) = p↾Z`.

The transposition sentence of that lemma is Lemma 4.6. An off-hit copy moves each cluster
across a whole block of parameter positions, the blocks of distinct slots are disjoint, and
the natural diagram is unchanged. The scheme identification `OffHitCopyDiagramEq` is
`infra_69_off_hit_diagramEq`: `lemma_6_1` only counts orbits. -/
theorem infra_69_lem61_off_hits
    [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K)
    {I J : Type u} [LinearOrder I] [LinearOrder J]
    (H : ChartOffHit I J)
    {α β : Type u} (σ : Cardinal.{u}) (hjoint : #(α ⊕ β) ≤ σ) (hσ : ℵ₀ ≤ σ)
    (t : α → SupportTerm E.lab E.arity (CopyInterchange.Src H.interchange))
    (s : β → SupportTerm E.lab E.arity (CopyInterchange.Src H.interchange))
    (ht : ∀ a k, (t a).pos k ∉ H.interchange.regions.second)
    (hs : ∀ b k, (s b).pos k ∉ H.interchange.regions.first) :
    SameNaturalDiagram K E D σ hjoint (Sum.elim t s)
      (Sum.elim (fun a => H.interchange.interchange.move (t a) (Or.inl (ht a)))
        (fun b => H.interchange.interchange.move (s b) (Or.inr (hs b)))) :=
  H.interchange.sameNaturalDiagram K E D σ hjoint hσ t s ht hs

/-- English (eventual.pdf §6.2): "Their anchor slots are disjoint, so Lemma 6.1 gives
`D(vᵢ, Z) = p↾Z`."

`lemma_6_1` counts orbits of `σ`-tuples and does not identify the two diagrams.
`infra_69_lem61_off_hits` is the transposition half (Lemma 4.6). On `SingleModelData`,
`ChartOffHit.readCopy` is the occurrence reading of the moved support, and
`infra_69_off_hit_diagramEq` transports `SameNaturalDiagram` to `DiagramEq`. -/
def OffHitCopyDiagramEq
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    (p : TupleOver K S W hμ base)
    {κIndex ι : Type u}
    (family : κIndex → p.idx → Occurrence K S (W.asSystem hμ base))
    (Z : ι → Occurrence K S (W.asSystem hμ base)) (i : κIndex) : Prop :=
  W.DiagramEq (X := p.host) (Y := base)
    (typeJoint (p := p) Z) (seqJoint (family i) Z)

/-- Every position of a term pushed along `dstEmb` lies on the old chart.
Clusters move by `copy`; parameters stay at their old indices. -/
theorem ChartOffHit.dstAlong_support_subset_old
    {I J : Type u} [LinearOrder I] [LinearOrder J]
    {lab : Type u} {arity : lab → ℕ}
    (H : ChartOffHit I J)
    (u : SupportTerm lab arity (CopyInterchange.Dst H.interchange)) :
    termSupport (SupportTerm.along H.interchange.dstEmb u) ⊆ Set.range (⇑H.C.old) := by
  intro x hx
  obtain ⟨k, rfl⟩ := hx
  change H.interchange.dstEmb (u.pos k) ∈ Set.range (⇑H.C.old)
  rw [CopyInterchange.dstEmb_apply]
  rcases (u.pos k) with ⟨v⟩
  cases v with
  | inl c =>
    exact ⟨H.copy c, (ChartOffHit.embCopy_apply H c).symm⟩
  | inr p =>
    exact ⟨p.1, (ChartOffHit.embParm_apply H p).symm⟩

/-- The moved support, read as a term over the old chart. -/
noncomputable def ChartOffHit.readCopy
    {I J : Type u} [LinearOrder I] [LinearOrder J]
    {lab : Type u} {arity : lab → ℕ}
    (H : ChartOffHit I J)
    (u : SupportTerm lab arity (CopyInterchange.Dst H.interchange)) :
    SupportTerm lab arity I :=
  (SupportTerm.along H.interchange.dstEmb u).pullback H.C.old
    (H.dstAlong_support_subset_old u)

theorem ChartOffHit.along_old_readCopy
    {I J : Type u} [LinearOrder I] [LinearOrder J]
    {lab : Type u} {arity : lab → ℕ}
    (H : ChartOffHit I J)
    (u : SupportTerm lab arity (CopyInterchange.Dst H.interchange)) :
    SupportTerm.along H.C.old (H.readCopy u) =
      SupportTerm.along H.interchange.dstEmb u :=
  SupportTerm.along_pullback H.C.old _
    (H.dstAlong_support_subset_old u)

/-- **Infra `infra_69_off_hit_diagramEq`:** On `SingleModelData`, an off-hit chart copy
satisfies `D(vᵢ, Z) = p↾Z`.

`Placement.Lifts` identifies `typeJoint Z` with the placed joint. `infra_69_lem61_off_hits`
keeps the natural diagram of that joint after the block interchange, and
`SameNaturalDiagram.same` is `D.same` of the realizations in `E(Q.J)`. `readCopy` pulls the
moved terms back along the old chart; the skeleton chart `e` is their occurrence reading in
the base. `diagramEq_iff_sameD` is `DiagramEq`. -/
theorem infra_69_off_hit_diagramEq
    (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (base : P.scheme.Object μ hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ base)
    (hνμ : p.ν = μ)
    {κIndex ι : Type u} (i : κIndex)
    (family : κIndex → p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ base))
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ base))
    {I : Type u} [LinearOrder I] [Nonempty I] (hI : #I = μ)
    (e : (P.E.obj I).carrier ≃[K.τ] base.model.carrier)
    (Q : Placement P.E.lab P.E.arity I p.idx)
    (H : ChartOffHit I Q.J)
    {ρ : Cardinal.{u}} (hρ : ℵ₀ ≤ ρ) (hρμ : ρ < μ)
    (hjoint : #(p.idx ⊕ ι) ≤ ρ)
    (q : ι → (P.E.obj I).carrier)
    (t : p.idx → SupportTerm P.E.lab P.E.arity (CopyInterchange.Src H.interchange))
    (s : ι → SupportTerm P.E.lab P.E.arity (CopyInterchange.Src H.interchange))
    (ht : ∀ a k, (t a).pos k ∉ H.interchange.regions.second)
    (hs : ∀ b k, (s b).pos k ∉ H.interchange.regions.first)
    (hplaced : ∀ c,
      SupportTerm.along H.interchange.srcEmb ((Sum.elim t s) c) =
        Q.joint (fun b => supportTermOf P.E (q b)) c)
    (hread : ∀ c, seqJoint (family i) Z c =
      base.occ (e (P.E.realize
        (H.readCopy (H.interchange.movedJoint t s ht hs c)))))
    (hpar : ∀ j, e (q j) = base.val (Z j))
    (incl : Language.Embedding K.τ (P.E.obj I).carrier p.host.model.carrier)
    (d : p.idx → p.host.model.carrier)
    (hincl : ∀ a, incl a = (p.incl.onVertex PUnit.unit) (e a))
    (hd : ∀ a, d a = p.host.val (p.val a))
    (hlifts : Q.Lifts P.E P.D p.host.mem incl d ρ hjoint q) :
    OffHitCopyDiagramEq (S := oneVertexShape) (W := P.scheme) p family Z i := by
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  let moved := H.interchange.movedJoint t s ht hs
  let xs : (p.idx ⊕ ι) → p.host.model.carrier :=
    fun c => p.host.val (typeJoint (p := p) Z c)
  let ys : (p.idx ⊕ ι) → base.model.carrier :=
    fun c => base.val (seqJoint (family i) Z c)
  let realizedCopy : (p.idx ⊕ ι) → (P.E.obj I).carrier :=
    fun c => P.E.realize (H.readCopy (moved c))
  let realizedJoint : (p.idx ⊕ ι) → (P.E.obj Q.J).carrier :=
    fun c => P.E.realize (Q.joint (fun b => supportTermOf P.E (q b)) c)
  let realizedMoved : (p.idx ⊕ ι) → (P.E.obj Q.J).carrier :=
    fun c => P.E.realize (SupportTerm.along H.interchange.dstEmb (moved c))
  have hcardI : Model.card (P.E.obj I) = μ := P.card_obj_eq hμ I hI
  have hcardHost : Model.card p.host.model = μ := by simpa [hνμ] using p.host.card
  have hcardBase : Model.card base.model = μ := base.card
  have htρ : P.D.t ρ ≤ μ := (P.t_lt hμ hρ hρμ).le
  have hBc : P.D.t ρ ≤ Model.card p.host.model := htρ.trans hcardHost.ge
  have hBasec : P.D.t ρ ≤ Model.card base.model := htρ.trans hcardBase.ge
  have hIc : P.D.t ρ ≤ Model.card (P.E.obj I) := htρ.trans hcardI.ge
  have hJc : P.D.t ρ ≤ Model.card (P.E.obj Q.J) :=
    hIc.trans (mk_le_of_injective (P.E.map Q.f).injective)
  have hxs : xs = Sum.elim d (fun b => incl (q b)) := by
    funext c
    cases c with
    | inl a =>
      simp [xs, typeJoint, hd]
    | inr j =>
      simp only [xs, typeJoint]
      have hunit : (Z j).1 = PUnit.unit := Subsingleton.elim _ _
      rw [hunit]
      change (p.incl.onVertex PUnit.unit) (Z j).2 = incl (q j)
      rw [hincl]
      apply congrArg (p.incl.onVertex PUnit.unit)
      rw [hpar j]
      rfl
  have hys : ∀ c, ys c = e (realizedCopy c) := by
    intro c
    change base.val (seqJoint (family i) Z c) =
      e (P.E.realize (H.readCopy (H.interchange.movedJoint t s ht hs c)))
    exact (congrArg base.val (hread c)).trans
      (SMObject.val_occ base
        (e (P.E.realize (H.readCopy (H.interchange.movedJoint t s ht hs c)))))
  have hMJ : K.Mem (P.E.obj Q.J) := orderPresentation_obj_mem P.E Q.J
  have hMI : K.Mem (P.E.obj I) := P.hE I
  have h1 := hlifts hBc hJc
  rw [← hxs] at h1
  have hplacedFun :
      (fun c => SupportTerm.along H.interchange.srcEmb ((Sum.elim t s) c)) =
        Q.joint (fun b => supportTermOf P.E (q b)) :=
    funext hplaced
  have hnat :=
    (infra_69_lem61_off_hits (E := P.E) (D := P.D) H ρ hjoint hρ t s ht hs).along
      hρ H.interchange.srcEmb H.interchange.dstEmb
  have hnat' : SameNaturalDiagram K P.E P.D ρ hjoint
      (Q.joint (fun b => supportTermOf P.E (q b)))
      (fun c => SupportTerm.along H.interchange.dstEmb (moved c)) := by
    simpa [hplacedFun, moved, CopyInterchange.movedJoint] using hnat
  have h2 := SameNaturalDiagram.same hρ hnat' hJc hJc hMJ hMJ
  have hmap : ∀ c, P.E.map H.C.old (realizedCopy c) = realizedMoved c := by
    intro c
    unfold realizedCopy realizedMoved
    rw [P.E.realize_along, ChartOffHit.along_old_readCopy]
  have h3 := P.D.of_strong hjoint hMI hMJ hIc hJc realizedCopy realizedMoved
    (P.E.map H.C.old) hρ (P.E.map_strong H.C.old) hmap
  have h4 := P.D.of_strong hjoint hMI base.mem hIc hBasec realizedCopy ys
    e.toEmbedding hρ (strong_of_equiv K e hMI) fun c => (hys c).symm
  have h23 := P.D.trans hjoint hMJ hMJ hMI hJc hJc hIc realizedJoint realizedMoved
    realizedCopy h2 (P.D.symm hjoint hMI hMJ hIc hJc realizedCopy realizedMoved h3)
  have h123 := P.D.trans hjoint p.host.mem hMJ hMI hBc hJc hIc xs realizedJoint
    realizedCopy h1 h23
  have hfin := P.D.trans hjoint p.host.mem hMI base.mem hBc hIc hBasec xs realizedCopy ys
    h123 h4
  let τ0 : Cardinal.{u} := max #(p.idx ⊕ ι) ℵ₀
  let σ' : Cardinal.{u} := max ρ (ls K)
  have hτ0inf : ℵ₀ ≤ τ0 := le_max_right _ _
  have hτ0ρ : τ0 ≤ ρ := max_le hjoint hρ
  have hσ'inf : ℵ₀ ≤ σ' := hρ.trans (le_max_left _ _)
  have hσ'μ : σ' < μ := max_lt hρμ (P.ls_lt hμ)
  have htσ' : P.D.t σ' ≤ μ := (P.t_lt hμ hσ'inf hσ'μ).le
  have hBc' : P.D.t σ' ≤ Model.card p.host.model := htσ'.trans hcardHost.ge
  have hBase' : P.D.t σ' ≤ Model.card base.model := htσ'.trans hcardBase.ge
  have hBcτ : P.D.t τ0 ≤ Model.card p.host.model := (P.D.mono _ _ hτ0ρ).trans hBc
  have hBaseτ : P.D.t τ0 ≤ Model.card base.model := (P.D.mono _ _ hτ0ρ).trans hBasec
  have hsameτ := P.D.same_relevel hjoint hρ hτ0inf (le_max_left ρ (ls K))
    (hτ0ρ.trans (le_max_left ρ (ls K))) (le_max_right ρ (ls K)) p.host.mem base.mem
    hBc hBasec hBc' hBase' hBcτ hBaseτ xs ys hfin (le_max_left _ _)
    (id : (p.idx ⊕ ι) → p.idx ⊕ ι)
  simp only [id] at hsameτ
  have hSame : P.D.SameD p.host.model base.model xs ys :=
    ⟨p.host.mem, base.mem, hBcτ, hBaseτ, hsameτ⟩
  have hαμ : #(p.idx ⊕ ι) < μ := hjoint.trans_lt hρμ
  have hαν : #(p.idx ⊕ ι) < p.ν := by simpa [hνμ] using hαμ
  have hDeq :=
    (SingleModelData.diagramEq_iff_sameD (hμ := p.hν) (hν := hμ) p.host base xs ys hαν
      hαμ).mpr hSame
  simpa [OffHitCopyDiagramEq, SingleModelData.scheme, xs, ys] using hDeq

/-- **Infra `infra_69_hit_bound`:** Every supporting position of `Z` belongs to at most one of
the regions, and therefore excludes at most one index `i`. -/
theorem infra_69_hit_bound {α ι : Type u} (region : ι → Set α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (region i) (region j)) :
    (∀ p i j, p ∈ region i → p ∈ region j → i = j) ∧
    (∀ p, #{i : ι // p ∈ region i} ≤ 1) := by
  have hunique : ∀ p i j, p ∈ region i → p ∈ region j → i = j := by
    intro p i j hi hj
    by_contra hne
    exact (Set.mem_empty_iff_false p).1 ((Set.disjoint_iff.mp (hdisj i j hne)) ⟨hi, hj⟩)
  refine ⟨hunique, fun p => ?_⟩
  exact le_one_iff_subsingleton.2
    ⟨fun a b => Subtype.ext (hunique p a.1 b.1 a.2 b.2)⟩

/-- **Infra `infra_69_finitary_exceptions`:** Finitarity of supports gives at most
`|Z| + ℵ₀` excluded indices. -/
theorem infra_69_finitary_exceptions {α ι Z : Type u} (region : ι → Set α)
    (hhit : ∀ p i j, p ∈ region i → p ∈ region j → i = j)
    (support : Z → Set α) (hfin : ∀ z, (support z).Finite) :
    #{i : ι // ∃ z : Z, ∃ p ∈ support z, p ∈ region i} ≤ #Z + ℵ₀ := by
  classical
  let hitSet : Z → Set ι := fun z => {i | ∃ p ∈ support z, p ∈ region i}
  have hcard : ∀ z, #(hitSet z) ≤ ℵ₀ := by
    intro z
    let f : {i : ι // i ∈ hitSet z} → ↥(support z) := fun i =>
      ⟨Classical.choose i.2, (Classical.choose_spec i.2).1⟩
    have hinj : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      have ha := Classical.choose_spec a.2
      have hb := Classical.choose_spec b.2
      have hpt : Classical.choose a.2 = Classical.choose b.2 := Subtype.ext_iff.mp h
      exact hhit _ a.1 b.1 (hpt ▸ ha.2) hb.2
    haveI : Finite (↥(support z)) := hfin z
    exact (mk_le_of_injective hinj).trans mk_le_aleph0
  have hunion : #(⋃ z, hitSet z) ≤ #Z * ℵ₀ := by
    calc
      #(⋃ z, hitSet z) ≤ sum fun z => #(hitSet z) := mk_iUnion_le_sum_mk
      _ ≤ #Z * ⨆ z, #(hitSet z) := sum_le_mk_mul_iSup _
      _ ≤ #Z * ℵ₀ := mul_le_mul' le_rfl (ciSup_le' hcard)
  have hmul : #Z * ℵ₀ ≤ #Z + ℵ₀ := by
    by_cases hZ : #Z = 0
    · rw [hZ, zero_mul]
      exact bot_le
    · rw [mul_comm, mul_eq_max_of_aleph0_le_left (le_refl ℵ₀) hZ, add_eq_max' (le_refl ℵ₀),
        max_comm]
  have hsub : #{i : ι // ∃ z : Z, ∃ p ∈ support z, p ∈ region i} ≤ #(⋃ z, hitSet z) := by
    refine mk_le_of_injective (f := fun i : {i : ι // ∃ z, ∃ p ∈ support z, p ∈ region i} =>
      (⟨i.1, ?_⟩ : ↥(⋃ z, hitSet z))) ?_
    · rcases i.2 with ⟨z, p, hp, hreg⟩
      exact Set.mem_iUnion.mpr ⟨z, ⟨p, hp, hreg⟩⟩
    · intro a b h
      exact Subtype.ext (congrArg (fun s : ↥(⋃ z, hitSet z) => (s : ι)) h)
  exact hsub.trans (hunion.trans hmul)

/-- **Infra `infra_69_subtuple_uniform`:** The same set of good indices works for every
subtuple of `v`. This is `ApproximationSequence.subtuple_uniform`: a bad index for a
subtuple is already bad for the full tuple, so the `|Z| + ℵ₀` bound carries over. -/
theorem infra_69_subtuple_uniform
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    (p : TupleOver K S W hμ base) (seq : ApproximationSequence p) :
    seq.HasSubtupleBound :=
  seq.subtuple_uniform

/-- **Infra `infra_69_uniformity_bounds`:** Only bounded support patterns, the fixed labels,
rich orders at bounded arities, and the compact-placement bounds were used.

The cardinals that the construction spends are determined by `b`, `σ`, `τ`, `κ`, and the
fixed scheme (`ls K`). The level and the type do not appear. -/
theorem infra_69_uniformity_bounds (b σ τ κ χ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) (hτ : ℵ₀ ≤ τ) (hκ : ℵ₀ ≤ κ)
    (hpow : χ ^ σ = χ) (hb : b + σ < χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) :
    σ + ℵ₀ ≤ σ + κ ∧
    σ + κ = max σ κ ∧
    (σ + κ) * (σ + κ) = σ + κ ∧
    (∀ z : Cardinal.{u}, z ≤ τ → z + ℵ₀ ≤ τ + ℵ₀) ∧
    χ ^ σ = χ ∧
    b + σ < χ ∧
    ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ ∧
    τ + κ = max τ κ := by
  refine ⟨add_le_add le_rfl hκ, add_eq_max hσ, ?_, ?_, hpow, hb, hχ, add_eq_max hτ⟩
  · rw [mul_eq_self (hσ.trans (self_le_add_right σ κ))]
  · intro z hz
    exact add_le_add hz le_rfl

/-! ## The κ-family (support copies, then the finitary hit set) -/

/-- The `κ` copies of one cut-cluster, chosen by `infra_69_copy_cluster`. -/
noncomputable def infra_69_copyHex
    {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {σ κ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hκ : ℵ₀ ≤ κ)
    (hsup : #C.support ≤ σ) (hfill : OrderFillsCuts (σ + κ) I)
    (κIndex : Type u) (hκI : #κIndex ≤ κ) (q : C.Cluster) :=
  infra_69_copy_cluster C hσ hκ hsup hfill (x := C.clusterRep q) (C.clusterRepPoint q).2
    κIndex hκI

noncomputable def infra_69_clusterRegion
    {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {σ κ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hκ : ℵ₀ ≤ κ)
    (hsup : #C.support ≤ σ) (hfill : OrderFillsCuts (σ + κ) I)
    (κIndex : Type u) (hκI : #κIndex ≤ κ) (q : C.Cluster) : κIndex → Set I :=
  Classical.choose (Classical.choose_spec
    (infra_69_copyHex C hσ hκ hsup hfill κIndex hκI q))

noncomputable def infra_69_clusterCopy
    {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {σ κ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hκ : ℵ₀ ≤ κ)
    (hsup : #C.support ≤ σ) (hfill : OrderFillsCuts (σ + κ) I)
    (κIndex : Type u) (hκI : #κIndex ≤ κ) (q : C.Cluster) :
    κIndex → (↥(C.clusterAt (C.clusterRep q)) ↪o I) :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (infra_69_copyHex C hσ hκ hsup hfill κIndex hκI q)))

theorem infra_69_clusterCopy_spec
    {I J : Type u} [LinearOrder I] [LinearOrder J]
    (C : ChartSupport I J) {σ κ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hκ : ℵ₀ ≤ κ)
    (hsup : #C.support ≤ σ) (hfill : OrderFillsCuts (σ + κ) I)
    (κIndex : Type u) (hκI : #κIndex ≤ κ) (q : C.Cluster) :
    (∀ i y, (infra_69_clusterCopy C hσ hκ hsup hfill κIndex hκI q i y : I) ∈
        infra_69_clusterRegion C hσ hκ hsup hfill κIndex hκI q i) ∧
    (∀ i, infra_69_clusterRegion C hσ hκ hsup hfill κIndex hκI q i ⊆
        C.slotCarrier (C.clusterRep q)) ∧
    (∀ i, IsConvexRegion (infra_69_clusterRegion C hσ hκ hsup hfill κIndex hκI q i)) ∧
    (∀ i j, i ≠ j → Disjoint (infra_69_clusterRegion C hσ hκ hsup hfill κIndex hκI q i)
        (infra_69_clusterRegion C hσ hκ hsup hfill κIndex hκI q j)) ∧
    (∀ i y (a : C.anchorIdx),
      (a.1 < infra_69_clusterCopy C hσ hκ hsup hfill κIndex hκI q i y ↔
          C.old a.1 < C.clusterRep q) ∧
      (infra_69_clusterCopy C hσ hκ hsup hfill κIndex hκI q i y < a.1 ↔
          C.clusterRep q < C.old a.1)) := by
  let hex := infra_69_copyHex C hσ hκ hsup hfill κIndex hκI q
  rcases Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hex)) with
    ⟨_, _, _, _, hmem, hslot, hconv, hdisj, hanchor⟩
  exact ⟨hmem, hslot, hconv, hdisj, hanchor⟩

/-- Package a family whose bad indices sit inside a finitary hit set of pairwise disjoint
regions. `infra_69_hit_bound` makes each position exclude at most one index, and
`infra_69_finitary_exceptions` bounds the union by `|Z| + ℵ₀`. -/
theorem infra_69_sequence_of_hits
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    (p : TupleOver K S W hμ base) (τ κ : Cardinal.{u})
    (κIndex : Type u) (hκ : #κIndex = κ)
    (family : κIndex → p.idx → Occurrence K S (W.asSystem hμ base))
    (hconcat : #(κIndex × p.idx) < μ)
    {α : Type u} (region : κIndex → Set α)
    (hdisj : ∀ i j, i ≠ j → Disjoint (region i) (region j))
    (supportOf : ∀ {ι : Type u},
      (ι → Occurrence K S (W.asSystem hμ base)) → ι → Set α)
    (hfin : ∀ {ι : Type u}
      (Z : ι → Occurrence K S (W.asSystem hμ base)) (z : ι), (supportOf Z z).Finite)
    (hgood : ∀ {ι : Type u}
      (Z : ι → Occurrence K S (W.asSystem hμ base)) (_hι : #ι ≤ τ) (i : κIndex),
      (∀ z, ∀ x ∈ supportOf Z z, x ∉ region i) →
      W.DiagramEq (X := p.host) (Y := base)
        (typeJoint (p := p) Z) (seqJoint (family i) Z)) :
    ∃ seq : ApproximationSequence p, seq.τ = τ ∧ #(seq.κIndex) = κ := by
  refine ⟨{
    τ := τ
    κIndex := κIndex
    family := family
    concat_bounded := hconcat
    few_exceptions := ?_ }, rfl, hκ⟩
  intro ι Z hι
  have hsub : ∀ i : κIndex,
      ¬ W.DiagramEq (X := p.host) (Y := base)
          (typeJoint (p := p) Z) (seqJoint (family i) Z) →
      ∃ z, ∃ x ∈ supportOf Z z, x ∈ region i := by
    intro i hbad
    by_contra hmiss
    exact hbad (hgood Z hι i (fun z x hx hreg => hmiss ⟨z, x, hx, hreg⟩))
  exact (mk_subtype_mono hsub).trans
    (infra_69_finitary_exceptions region (infra_69_hit_bound region hdisj).1
      (supportOf Z) (hfin Z))

/-- A placement whose support already lies on the old chart is its own copy: the pullback
along `Q.f` realizes `D(v, Z) = p ↾ Z` for every query that the placement lifts. -/
theorem infra_69_shared_diagramEq
    (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (base : P.scheme.Object μ hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ base)
    (hνμ : p.ν = μ)
    {I : Type u} [LinearOrder I] [Nonempty I] (hI : #I = μ)
    (e : (P.E.obj I).carrier ≃[K.τ] base.model.carrier)
    (incl : Language.Embedding K.τ (P.E.obj I).carrier p.host.model.carrier)
    (d : p.idx → p.host.model.carrier)
    (hincl : ∀ a, incl a = (p.incl.onVertex PUnit.unit) (e a))
    (hd : ∀ a, d a = p.host.val (p.val a))
    (Q : Placement P.E.lab P.E.arity I p.idx)
    (hshared : ∀ a, termSupport (Q.z a) ⊆ Set.range (⇑Q.f))
    (family : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ base))
    (hfam : ∀ a, family a =
      base.occ (e (P.E.realize ((Q.z a).pullback Q.f (hshared a)))))
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ base))
    {ρ : Cardinal.{u}} (hρ : ℵ₀ ≤ ρ) (hρμ : ρ < μ)
    (hjoint : #(p.idx ⊕ ι) ≤ ρ)
    (q : ι → (P.E.obj I).carrier)
    (hpar : ∀ j, e (q j) = base.val (Z j))
    (hlifts : Q.Lifts P.E P.D p.host.mem incl d ρ hjoint q) :
    P.scheme.DiagramEq (X := p.host) (Y := base)
      (typeJoint (p := p) Z) (seqJoint family Z) := by
  let xs : (p.idx ⊕ ι) → p.host.model.carrier :=
    fun c => p.host.val (typeJoint (p := p) Z c)
  let ys : (p.idx ⊕ ι) → base.model.carrier :=
    fun c => base.val (seqJoint family Z c)
  let realizedPull : (p.idx ⊕ ι) → (P.E.obj I).carrier := fun c =>
    match c with
    | Sum.inl a => P.E.realize ((Q.z a).pullback Q.f (hshared a))
    | Sum.inr b => q b
  let realizedJoint : (p.idx ⊕ ι) → (P.E.obj Q.J).carrier :=
    fun c => P.E.realize (Q.joint (fun b => supportTermOf P.E (q b)) c)
  have hcardI : Model.card (P.E.obj I) = μ := P.card_obj_eq hμ I hI
  have hcardHost : Model.card p.host.model = μ := by simpa [hνμ] using p.host.card
  have hcardBase : Model.card base.model = μ := base.card
  have htρ : P.D.t ρ ≤ μ := (P.t_lt hμ hρ hρμ).le
  have hBc : P.D.t ρ ≤ Model.card p.host.model := htρ.trans hcardHost.ge
  have hBasec : P.D.t ρ ≤ Model.card base.model := htρ.trans hcardBase.ge
  have hIc : P.D.t ρ ≤ Model.card (P.E.obj I) := htρ.trans hcardI.ge
  have hJc : P.D.t ρ ≤ Model.card (P.E.obj Q.J) :=
    hIc.trans (mk_le_of_injective (P.E.map Q.f).injective)
  have hxs : xs = Sum.elim d (fun b => incl (q b)) := by
    funext c
    cases c with
    | inl a =>
      simp [xs, typeJoint, hd]
    | inr j =>
      simp only [xs, typeJoint]
      have hunit : (Z j).1 = PUnit.unit := Subsingleton.elim _ _
      rw [hunit]
      change (p.incl.onVertex PUnit.unit) (Z j).2 = incl (q j)
      rw [hincl]
      apply congrArg (p.incl.onVertex PUnit.unit)
      rw [hpar j]
      rfl
  have hys : ∀ c, ys c = e (realizedPull c) := by
    intro c
    cases c with
    | inl a =>
      change base.val (family a) =
        e (P.E.realize ((Q.z a).pullback Q.f (hshared a)))
      rw [hfam a]
      exact SMObject.val_occ base _
    | inr j =>
      change base.val (Z j) = e (q j)
      exact (hpar j).symm
  have hmap : ∀ c, P.E.map Q.f (realizedPull c) = realizedJoint c := by
    intro c
    cases c with
    | inl a =>
      change P.E.map Q.f (P.E.realize ((Q.z a).pullback Q.f (hshared a))) =
        P.E.realize (Q.z a)
      rw [P.E.realize_along, SupportTerm.along_pullback]
    | inr b =>
      change P.E.map Q.f (q b) =
        P.E.realize (SupportTerm.along Q.f (supportTermOf P.E (q b)))
      conv_lhs => rw [← realize_supportTermOf P.E (q b)]
      rw [P.E.realize_along]
  have hMJ : K.Mem (P.E.obj Q.J) := orderPresentation_obj_mem P.E Q.J
  have hMI : K.Mem (P.E.obj I) := P.hE I
  have h1 := hlifts hBc hJc
  rw [← hxs] at h1
  have h3 := P.D.of_strong hjoint hMI hMJ hIc hJc realizedPull realizedJoint
    (P.E.map Q.f) hρ (P.E.map_strong Q.f) hmap
  have h4 := P.D.of_strong hjoint hMI base.mem hIc hBasec realizedPull ys
    e.toEmbedding hρ (strong_of_equiv K e hMI) fun c => (hys c).symm
  have h13 := P.D.trans hjoint p.host.mem hMJ hMI hBc hJc hIc xs realizedJoint
    realizedPull h1 (P.D.symm hjoint hMI hMJ hIc hJc realizedPull realizedJoint h3)
  have hfin := P.D.trans hjoint p.host.mem hMI base.mem hBc hIc hBasec xs realizedPull ys
    h13 h4
  let τ0 : Cardinal.{u} := max #(p.idx ⊕ ι) ℵ₀
  let σ' : Cardinal.{u} := max ρ (ls K)
  have hτ0inf : ℵ₀ ≤ τ0 := le_max_right _ _
  have hτ0ρ : τ0 ≤ ρ := max_le hjoint hρ
  have hσ'inf : ℵ₀ ≤ σ' := hρ.trans (le_max_left _ _)
  have hσ'μ : σ' < μ := max_lt hρμ (P.ls_lt hμ)
  have htσ' : P.D.t σ' ≤ μ := (P.t_lt hμ hσ'inf hσ'μ).le
  have hBc' : P.D.t σ' ≤ Model.card p.host.model := htσ'.trans hcardHost.ge
  have hBase' : P.D.t σ' ≤ Model.card base.model := htσ'.trans hcardBase.ge
  have hBcτ : P.D.t τ0 ≤ Model.card p.host.model := (P.D.mono _ _ hτ0ρ).trans hBc
  have hBaseτ : P.D.t τ0 ≤ Model.card base.model := (P.D.mono _ _ hτ0ρ).trans hBasec
  have hsameτ := P.D.same_relevel hjoint hρ hτ0inf (le_max_left ρ (ls K))
    (hτ0ρ.trans (le_max_left ρ (ls K))) (le_max_right ρ (ls K)) p.host.mem base.mem
    hBc hBasec hBc' hBase' hBcτ hBaseτ xs ys hfin (le_max_left _ _)
    (id : (p.idx ⊕ ι) → p.idx ⊕ ι)
  simp only [id] at hsameτ
  have hSame : P.D.SameD p.host.model base.model xs ys :=
    ⟨p.host.mem, base.mem, hBcτ, hBaseτ, hsameτ⟩
  have hαμ : #(p.idx ⊕ ι) < μ := hjoint.trans_lt hρμ
  have hαν : #(p.idx ⊕ ι) < p.ν := by simpa [hνμ] using hαμ
  have hDeq :=
    (SingleModelData.diagramEq_iff_sameD (hμ := p.hν) (hν := hμ) p.host base xs ys hαν
      hαμ).mpr hSame
  simpa [SingleModelData.scheme, xs, ys] using hDeq

/-- Build the support-copy sequence on a chart that already carries both the placement and
the room for the copies. `Q` lifts every joint of size at most `max σ τ`, and `I` fills cuts
of size `σ + κ`, so each unshared cluster can be copied into `κ` disjoint regions of `I`.
An index whose query supports miss those regions is off-hit, and
`infra_69_off_hit_diagramEq` gives `D(vᵢ, Z) = p ↾ Z`. The remaining indices are bounded by
`infra_69_finitary_exceptions`. When every support already lies on `I`, the pullback of `Q`
is the copy and there are no exceptions. -/
theorem infra_69_support_copy_sequence
    (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (base : P.scheme.Object μ hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ base)
    (hνμ : p.ν = μ)
    (σ τ κ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) (hσμ : σ < μ) (hidx : #p.idx ≤ σ)
    (hτ : ℵ₀ ≤ τ) (hτμ : τ < μ)
    (hκ : ℵ₀ ≤ κ) (hκμ : κ < μ)
    (hprod : κ * #p.idx < μ)
    {I : Type u} [LinearOrder I] [Nonempty I] (hI : #I = μ)
    (hfill : OrderFillsCuts (σ + κ) I)
    (e : (P.E.obj I).carrier ≃[K.τ] base.model.carrier)
    (incl : Language.Embedding K.τ (P.E.obj I).carrier p.host.model.carrier)
    (d : p.idx → p.host.model.carrier)
    (hincl : ∀ a, incl a = (p.incl.onVertex PUnit.unit) (e a))
    (hd : ∀ a, d a = p.host.val (p.val a))
    (Q : Placement P.E.lab P.E.arity I p.idx)
    (hlifts : ∀ {β : Type u} (ρ : Cardinal.{u}), ℵ₀ ≤ ρ → ρ ≤ max σ τ →
      ∀ (q : β → (P.E.obj I).carrier) (hj : #(p.idx ⊕ β) ≤ ρ),
        Q.Lifts P.E P.D p.host.mem incl d ρ hj q) :
    ∃ seq : ApproximationSequence p, seq.τ = τ ∧ #(seq.κIndex) = κ := by
  classical
  let C : ChartSupport I Q.J := { old := Q.f, support := tupleSupport Q.z }
  have hsup : #C.support ≤ σ := by
    calc #C.support ≤ max ℵ₀ σ := by simpa [C] using mk_tupleSupport_le hidx Q.z
      _ = σ := max_eq_right hσ
  let κIndex : Type u := (ord κ).ToType
  have hκcard : #κIndex = κ := Cardinal.mk_ord_toType κ
  have hκI : #κIndex ≤ κ := le_of_eq hκcard
  have hconcat : #(κIndex × p.idx) < μ := by
    rw [mk_prod, lift_id, lift_id, hκcard]
    exact hprod
  by_cases hne : Nonempty C.unshared
  · let spec (q : C.Cluster) :=
      infra_69_clusterCopy_spec C hσ hκ hsup hfill κIndex hκI q
    have hmem (q : C.Cluster) := (spec q).1
    have hsub (q : C.Cluster) := (spec q).2.1
    have hconv (q : C.Cluster) := (spec q).2.2.1
    have hdisjC (q : C.Cluster) := (spec q).2.2.2.1
    have hside (q : C.Cluster) := (spec q).2.2.2.2
    let ypt (y : C.unshared) : ↥(C.clusterAt (C.clusterRep (C.clusterMk y))) :=
      ⟨y.1, ⟨y.2, Quotient.exact (C.clusterRepPoint_spec (C.clusterMk y))⟩⟩
    let glue (i : κIndex) (y : C.unshared) : I :=
      infra_69_clusterCopy C hσ hκ hsup hfill κIndex hκI (C.clusterMk y) i (ypt y)
    have hsideY (i : κIndex) (y : C.unshared) (a : C.anchorIdx) :
        (a.1 < glue i y ↔ C.old a.1 < y.1) ∧ (glue i y < a.1 ↔ y.1 < C.old a.1) := by
      let q := C.clusterMk y
      have hs := hside q i (ypt y) a
      have hcut : C.SameCut (C.clusterRep q) y.1 := (ypt y).2.2
      have hL : C.old a.1 < C.clusterRep q ↔ C.old a.1 < y.1 := hcut a.1
      have hrne : C.clusterRep q ≠ C.old a.1 := by
        intro h
        exact (C.clusterRepPoint q).2.2 ⟨a.1, h.symm⟩
      have hyne : y.1 ≠ C.old a.1 := by
        intro h
        exact y.2.2 ⟨a.1, h.symm⟩
      have hRep : C.clusterRep q < C.old a.1 ↔ ¬ C.old a.1 < C.clusterRep q := by
        constructor
        · exact fun h => not_lt_of_gt h
        · intro hnot
          rcases lt_trichotomy (C.clusterRep q) (C.old a.1) with hlt | heq | hgt
          · exact hlt
          · exact absurd heq hrne
          · exact absurd hgt hnot
      have hPt : y.1 < C.old a.1 ↔ ¬ C.old a.1 < y.1 := by
        constructor
        · exact fun h => not_lt_of_gt h
        · intro hnot
          rcases lt_trichotomy y.1 (C.old a.1) with hlt | heq | hgt
          · exact hlt
          · exact absurd heq hyne
          · exact absurd hgt hnot
      refine ⟨?_, ?_⟩
      · have hglue : a.1 < glue i y ↔ C.old a.1 < C.clusterRep q := by
          simpa [glue, q] using hs.1
        exact hglue.trans hL
      · have hglue : glue i y < a.1 ↔ C.clusterRep q < C.old a.1 := by
          simpa [glue, q] using hs.2
        exact hglue.trans (hRep.trans (hL.not.trans hPt.symm))
    have hslots (q q' : C.Cluster) (hq : q ≠ q') :
        Disjoint (C.slotCarrier (C.clusterRep q)) (C.slotCarrier (C.clusterRep q')) := by
      suffices hlt : ∀ {q q' : C.Cluster}, q < q' →
          Disjoint (C.slotCarrier (C.clusterRep q)) (C.slotCarrier (C.clusterRep q')) by
        rcases lt_trichotomy q q' with hlt' | heq | hgt
        · exact hlt hlt'
        · exact absurd heq hq
        · exact (hlt hgt).symm
      intro q q' hlt
      let y := C.clusterRepPoint q
      let z := C.clusterRepPoint q'
      have hltJ : y.1 < z.1 := C.cluster_lt_iff.mp hlt
      have hcut : ¬ C.SameCut y.1 z.1 := by
        intro hs
        exact ne_of_lt hlt (by
          have hmk : C.clusterMk y = C.clusterMk z := Quotient.sound hs
          have hyq : C.clusterMk y = q := C.clusterRepPoint_spec q
          have hzq : C.clusterMk z = q' := C.clusterRepPoint_spec q'
          exact hyq.symm.trans (hmk.trans hzq))
      obtain ⟨a, hy, hz⟩ := C.exists_anchor_between hltJ hcut
      rw [Set.disjoint_left]
      intro i hiQ hiQ'
      have hb : C.old a.1 ∈ C.anchors := a.2
      have hnot : ¬ C.old a.1 < y.1 := not_lt_of_gt hy
      have hnoti : ¬ C.old a.1 < C.old i := (hiQ _ hb).not.mpr hnot
      have hzi : C.old a.1 < C.old i := (hiQ' _ hb).mpr hz
      exact not_lt_of_ge (le_of_not_gt hnoti) hzi
    have hglueMono (i : κIndex) : StrictMono (glue i) := by
      intro y z hyz
      by_cases hcut : C.clusterMk y = C.clusterMk z
      · have hS : C.SameCut (C.clusterRep (C.clusterMk y)) z.1 := by
          rw [hcut]
          exact (ypt z).2.2
        let zpt : ↥(C.clusterAt (C.clusterRep (C.clusterMk y))) := ⟨z.1, ⟨z.2, hS⟩⟩
        have hltp : ypt y < zpt := Subtype.coe_lt_coe.mp (Subtype.coe_lt_coe.mpr hyz)
        have himg :=
          (infra_69_clusterCopy C hσ hκ hsup hfill κIndex hκI (C.clusterMk y) i).strictMono hltp
        have hmemiff : ∀ x : Q.J,
            x ∈ C.clusterAt (C.clusterRep (C.clusterMk y)) ↔
            x ∈ C.clusterAt (C.clusterRep (C.clusterMk z)) := by
          intro x
          rw [hcut]
        have hpt : zpt ≍ ypt z := (Subtype.heq_iff_coe_eq hmemiff).mpr rfl
        have hfun := congr_arg_heq
          (fun q : C.Cluster =>
            (infra_69_clusterCopy C hσ hκ hsup hfill κIndex hκI q i :
              ↥(C.clusterAt (C.clusterRep q)) → I)) hcut
        have himgeq := congr_heq hfun hpt
        calc glue i y
            = (infra_69_clusterCopy C hσ hκ hsup hfill κIndex hκI (C.clusterMk y) i) (ypt y) := rfl
          _ < (infra_69_clusterCopy C hσ hκ hsup hfill κIndex hκI (C.clusterMk y) i) zpt := himg
          _ = (infra_69_clusterCopy C hσ hκ hsup hfill κIndex hκI (C.clusterMk z) i) (ypt z) :=
              himgeq
          _ = glue i z := rfl
      · have hmk : C.clusterMk y < C.clusterMk z :=
          lt_of_le_of_ne (C.clusterMk_mono hyz.le) hcut
        have hneCut : ¬ C.SameCut y.1 z.1 := fun hs => hcut (Quotient.sound hs)
        obtain ⟨a, hleft, hright⟩ :=
          C.exists_anchor_between (Subtype.coe_lt_coe.mpr hyz) hneCut
        exact ((hsideY i y a).2.mpr hleft).trans ((hsideY i z a).1.mpr hright)
    let glueEmb (i : κIndex) : C.unshared ↪o I :=
      OrderEmbedding.ofStrictMono (glue i) (hglueMono i)
    let toU (j : Q.J) (hj : j ∈ tupleSupport Q.z) (hn : ¬ ∃ t : I, C.old t = j) : C.unshared :=
      ⟨j, ⟨hj, by simpa [Set.mem_range] using hn⟩⟩
    let locPos (i : κIndex) (j : Q.J) (hj : j ∈ tupleSupport Q.z) : I :=
      if h : ∃ t : I, C.old t = j then Classical.choose h else glue i (toU j hj h)
    have hloc (i : κIndex) {j j' : Q.J} (hj : j ∈ tupleSupport Q.z) (hj' : j' ∈ tupleSupport Q.z)
        (hlt : j < j') : locPos i j hj < locPos i j' hj' := by
      by_cases h : ∃ t : I, C.old t = j
      · by_cases h' : ∃ t : I, C.old t = j'
        · have h1 := Classical.choose_spec h
          have h2 := Classical.choose_spec h'
          have : C.old (Classical.choose h) < C.old (Classical.choose h') := by
            rw [h1, h2]; exact hlt
          simpa [locPos, dif_pos h, dif_pos h'] using (C.old.lt_iff_lt).mp this
        · have h1 := Classical.choose_spec h
          have hsh : j ∈ C.shared := ⟨hj, ⟨Classical.choose h, h1⟩⟩
          have ha : C.old (Classical.choose h) ∈ C.anchors := by
            rw [h1]
            exact Set.mem_union_left C.sepImage hsh
          let a : C.anchorIdx := ⟨Classical.choose h, ha⟩
          have hlt' : C.old a.1 < (toU j' hj' h').1 := by
            have hpre : C.old (Classical.choose h) < j' := by simpa [h1] using hlt
            simpa [a, toU] using hpre
          have hcmp := (hsideY i (toU j' hj' h') a).1.mpr hlt'
          simpa [locPos, dif_pos h, dif_neg h', a] using hcmp
      · by_cases h' : ∃ t : I, C.old t = j'
        · have h2 := Classical.choose_spec h'
          have hsh : j' ∈ C.shared := ⟨hj', ⟨Classical.choose h', h2⟩⟩
          have ha : C.old (Classical.choose h') ∈ C.anchors := by
            rw [h2]
            exact Set.mem_union_left C.sepImage hsh
          let a : C.anchorIdx := ⟨Classical.choose h', ha⟩
          have hlt' : (toU j hj h).1 < C.old a.1 := by
            have hpre : j < C.old (Classical.choose h') := by simpa [h2] using hlt
            simpa [a, toU] using hpre
          have hcmp := (hsideY i (toU j hj h) a).2.mpr hlt'
          simpa [locPos, dif_neg h, dif_pos h', a] using hcmp
        · have hpts : toU j hj h < toU j' hj' h' := Subtype.coe_lt_coe.mp hlt
          simpa [locPos, dif_neg h, dif_neg h'] using hglueMono i hpts
    let copyTerm (i : κIndex) (a : p.idx) : SupportTerm P.E.lab P.E.arity I :=
      { label := (Q.z a).label
        pos := fun k => locPos i ((Q.z a).pos k)
          (termSupport_subset_tupleSupport Q.z a (Set.mem_range_self k))
        increasing := fun k k' hk =>
          hloc i
            (termSupport_subset_tupleSupport Q.z a (Set.mem_range_self k))
            (termSupport_subset_tupleSupport Q.z a (Set.mem_range_self k'))
            ((Q.z a).increasing hk) }
    let family (i : κIndex) (a : p.idx) : Occurrence K oneVertexShape (P.scheme.asSystem hμ base) :=
      base.occ (e (P.E.realize (copyTerm i a)))
    let hitRegion (i : κIndex) : Set I :=
      ⋃ q : C.Cluster, infra_69_clusterRegion C hσ hκ hsup hfill κIndex hκI q i
    have hdisjHit : ∀ i j, i ≠ j → Disjoint (hitRegion i) (hitRegion j) := by
      intro i j hneij
      rw [Set.disjoint_left]
      intro z hzi hzj
      rcases Set.mem_iUnion.mp hzi with ⟨q, hq⟩
      rcases Set.mem_iUnion.mp hzj with ⟨q', hq'⟩
      by_cases hqq : q = q'
      · subst hqq
        exact (Set.disjoint_left.mp (hdisjC q i j hneij) hq) hq'
      · exact (Set.disjoint_left.mp (hslots q q' hqq) (hsub q i hq)) (hsub q' j hq')
    exact @infra_69_sequence_of_hits K oneVertexShape P.scheme μ hμ base
      p τ κ κIndex hκcard family hconcat I hitRegion hdisjHit
      (fun {_} Z z => termSupport (supportTermOf P.E (e.symm (base.val (Z z)))))
      (fun {_} Z z =>
        Set.finite_range (supportTermOf P.E (e.symm (base.val (Z z)))).pos)
      (fun {ι} Z hι i hmiss => by
        let qv : _ → (P.E.obj I).carrier := fun j => e.symm (base.val (Z j))
        let querySet : Set I :=
          ⋃ j, termSupport (supportTermOf P.E (qv j))
        let H : ChartOffHit I Q.J := {
          C := C
          copy := glueEmb i
          hslot := fun y a => by
            simpa [glueEmb, OrderEmbedding.coe_ofStrictMono] using hsideY i y a
          region := fun q => infra_69_clusterRegion C hσ hκ hsup hfill κIndex hκI q i
          copy_mem := fun y => by
            simpa [glue, glueEmb, OrderEmbedding.coe_ofStrictMono] using
              hmem (C.clusterMk y) i (ypt y)
          convex := fun q => hconv q i
          disjoint_region := fun q q' hqq => by
            rw [Set.disjoint_left]
            intro x hx hx'
            exact (Set.disjoint_left.mp (hslots q q' hqq) (hsub q i hx)) (hsub q' i hx')
          query := querySet
          query_off := fun q => by
            rw [Set.disjoint_left]
            intro x hx hxR
            rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
            exact hmiss j x hj (Set.mem_iUnion.mpr ⟨q, hxR⟩)
          nonempty_unshared := hne }
        have hposMem (a : p.idx) (k : Fin (P.E.arity (Q.z a).label)) :
            (Q.z a).pos k ∈ tupleSupport Q.z :=
          termSupport_subset_tupleSupport Q.z a (Set.mem_range_self k)
        let parmOf (j : Q.J) (hj : j ∈ tupleSupport Q.z) (h : ∃ t : I, C.old t = j) : H.Parm :=
          ⟨Classical.choose h, Or.inr (by
            have hsh : j ∈ C.shared := ⟨hj, h⟩
            rw [Classical.choose_spec h]
            exact Set.mem_union_left C.sepImage hsh)⟩
        let posSrc (j : Q.J) (hj : j ∈ tupleSupport Q.z) :
            CopyInterchange.Src H.interchange :=
          if h : ∃ t : I, C.old t = j then ⟨Sum.inr (parmOf j hj h)⟩
          else ⟨Sum.inl (toU j hj h)⟩
        have hsrcEmb (j : Q.J) (hj : j ∈ tupleSupport Q.z) :
            H.interchange.srcEmb (posSrc j hj) = j := by
          by_cases h : ∃ t : I, C.old t = j
          · unfold posSrc
            rw [dif_pos h]
            simp only [CopyInterchange.srcEmb_apply, CopyInterchange.sumOrig_inr,
              ChartOffHit.embParm_apply]
            exact Classical.choose_spec h
          · unfold posSrc
            rw [dif_neg h]
            rfl
        let t (a : p.idx) :
            SupportTerm P.E.lab P.E.arity (CopyInterchange.Src H.interchange) :=
          { label := (Q.z a).label
            pos := fun k => posSrc ((Q.z a).pos k) (hposMem a k)
            increasing := fun k k' hk => by
              rw [← H.interchange.srcEmb.lt_iff_lt]
              rw [hsrcEmb _ (hposMem a k), hsrcEmb _ (hposMem a k')]
              exact (Q.z a).increasing hk }
        let s (b : ι) :
            SupportTerm P.E.lab P.E.arity (CopyInterchange.Src H.interchange) :=
          { label := (supportTermOf P.E (qv b)).label
            pos := fun k =>
              ⟨Sum.inr ⟨(supportTermOf P.E (qv b)).pos k,
                Or.inl (Set.mem_iUnion.mpr ⟨b, Set.mem_range_self k⟩)⟩⟩
            increasing := fun k k' hk => by
              simp only [CopyInterchange.src_lt_iff, CopyInterchange.sumOrig_inr,
                ChartOffHit.embParm_apply]
              exact (C.old.lt_iff_lt).mpr ((supportTermOf P.E (qv b)).increasing hk) }
        have hs : ∀ b k, (s b).pos k ∉ H.interchange.regions.first := by
          intro b k hf
          rcases hf with ⟨c, hc⟩
          simp only [s] at hc
          cases hc
        have ht : ∀ a k, (t a).pos k ∉ H.interchange.regions.second := by
          intro a k hsec
          rcases hsec with ⟨p, hpval, ⟨c, hcross⟩⟩
          by_cases hex : ∃ t0 : I, C.old t0 = (Q.z a).pos k
          · have hval : ((t a).pos k).val = Sum.inr (parmOf _ (hposMem a k) hex) := by
              simp [t, posSrc, dif_pos hex]
            rw [hval] at hpval
            injection hpval with hpeq
            have hp1 : p.1 = Classical.choose hex := by
              rw [← hpeq]
            have hsh : (Q.z a).pos k ∈ C.shared := ⟨hposMem a k, hex⟩
            have ha : C.old p.1 ∈ C.anchors := by
              rw [hp1, Classical.choose_spec hex]
              exact Set.mem_union_left C.sepImage hsh
            have hiff : H.interchange.leftOrig c p ↔ H.interchange.leftCopy c p := by
              change C.old p.1 < c.1 ↔ C.old p.1 < C.old (H.copy c)
              rw [C.old.lt_iff_lt]
              exact (H.hslot c ⟨p.1, ha⟩).1.symm
            exact hcross (propext hiff)
          · simp [t, posSrc, dif_neg hex] at hpval
        have hplaced : ∀ c,
            SupportTerm.along H.interchange.srcEmb ((Sum.elim t s) c) =
              Q.joint (fun b => supportTermOf P.E (qv b)) c := by
          intro c
          cases c with
          | inl a =>
            refine SupportTerm.ext_of_label_eq rfl fun k => ?_
            simp only [SupportTerm.along, Sum.elim_inl, t, Placement.joint]
            exact hsrcEmb _ (hposMem a k)
          | inr b =>
            refine SupportTerm.ext_of_label_eq rfl fun k => ?_
            simp only [SupportTerm.along, Sum.elim_inr, s, Placement.joint,
              CopyInterchange.srcEmb_apply, CopyInterchange.sumOrig_inr,
              ChartOffHit.embParm_apply]
            rfl
        have hread : ∀ c, seqJoint (family i) Z c =
            base.occ (e (P.E.realize
              (H.readCopy (H.interchange.movedJoint t s ht hs c)))) := by
          intro c
          cases c with
          | inl a =>
            have hterm : copyTerm i a =
                H.readCopy (H.interchange.movedJoint t s ht hs (Sum.inl a)) := by
              refine SupportTerm.ext_of_label_eq rfl fun k => ?_
              apply C.old.injective
              let u := H.interchange.movedJoint t s ht hs (Sum.inl a)
              have hEq : C.old ((H.readCopy u).pos k) =
                  H.interchange.dstEmb (u.pos k) :=
                Classical.choose_spec
                  (H.dstAlong_support_subset_old u (Set.mem_range_self k))
              suffices hL : C.old ((copyTerm i a).pos k) =
                  H.interchange.dstEmb (u.pos k) from hL.trans hEq.symm
              have hmove : u.pos k = H.interchange.srcDstEquiv ((t a).pos k) := rfl
              rw [hmove, CopyInterchange.dstEmb_apply, CopyInterchange.srcDstEquiv_val]
              by_cases hex : ∃ t0 : I, C.old t0 = (Q.z a).pos k
              · simp only [t, posSrc, copyTerm, locPos, dif_pos hex, parmOf,
                  CopyInterchange.sumCopy_inr, ChartOffHit.embParm_apply]
                rfl
              · simp only [t, posSrc, copyTerm, locPos, dif_neg hex, glue, glueEmb,
                  OrderEmbedding.coe_ofStrictMono, CopyInterchange.sumCopy_inl,
                  ChartOffHit.embCopy_apply]
                rfl
            simp [seqJoint, family, hterm]
            rfl
          | inr b =>
            have hterm : H.readCopy (H.interchange.movedJoint t s ht hs (Sum.inr b)) =
                supportTermOf P.E (qv b) := by
              refine SupportTerm.ext_of_label_eq rfl fun k => ?_
              apply C.old.injective
              let u := H.interchange.movedJoint t s ht hs (Sum.inr b)
              have hEq : C.old ((H.readCopy u).pos k) =
                  H.interchange.dstEmb (u.pos k) :=
                Classical.choose_spec
                  (H.dstAlong_support_subset_old u (Set.mem_range_self k))
              have hmove : u.pos k = H.interchange.srcDstEquiv ((s b).pos k) := rfl
              rw [hEq, hmove, CopyInterchange.dstEmb_apply, CopyInterchange.srcDstEquiv_val]
              apply congrArg (⇑C.old)
              apply congrArg (supportTermOf P.E (qv b)).pos
              exact (Fin.ext rfl).symm
            simp [seqJoint, hterm, realize_supportTermOf, qv, e.apply_symm_apply]
            exact (SMObject.occ_val base (Z b)).symm
        let ρ : Cardinal.{u} := max σ τ
        have hρ : ℵ₀ ≤ ρ := hσ.trans (le_max_left _ _)
        have hρμ : ρ < μ := max_lt hσμ hτμ
        have hjoint : #(p.idx ⊕ ι) ≤ ρ := by
          calc #(p.idx ⊕ ι) = #p.idx + #ι := by simp [mk_sum, lift_id]
            _ ≤ σ + τ := add_le_add hidx hι
            _ = max σ τ := add_eq_max hσ
        simpa [OffHitCopyDiagramEq] using
          infra_69_off_hit_diagramEq P hμ base p hνμ i family Z hI e Q H
            hρ hρμ hjoint qv t s ht hs hplaced hread
            (fun j => e.apply_symm_apply (base.val (Z j)))
            incl d hincl hd (hlifts ρ hρ le_rfl qv hjoint))
  · have hshared : ∀ a, termSupport (Q.z a) ⊆ Set.range (⇑Q.f) := by
      intro a x hx
      by_contra hnot
      exact hne ⟨⟨x, ⟨termSupport_subset_tupleSupport Q.z a hx, hnot⟩⟩⟩
    let pull (a : p.idx) : Occurrence K oneVertexShape (P.scheme.asSystem hμ base) :=
      base.occ (e (P.E.realize ((Q.z a).pullback Q.f (hshared a))))
    exact @infra_69_sequence_of_hits K oneVertexShape P.scheme μ hμ base
      p τ κ κIndex hκcard (fun _ a => pull a) hconcat I
      (fun _ => (∅ : Set I)) (fun _ _ _ => empty_disjoint _)
      (fun {_} _ _ => (∅ : Set I)) (fun {_} _ _ => Set.finite_empty)
      (fun {ι} Z hι _ _ => by
        let ρ : Cardinal.{u} := max σ τ
        have hρ : ℵ₀ ≤ ρ := hσ.trans (le_max_left _ _)
        have hρμ : ρ < μ := max_lt hσμ hτμ
        have hjoint : #(p.idx ⊕ ι) ≤ ρ := by
          calc #(p.idx ⊕ ι) = #p.idx + #ι := by simp [mk_sum, lift_id]
            _ ≤ σ + τ := add_le_add hidx hι
            _ = max σ τ := add_eq_max hσ
        let qv : ι → (P.E.obj I).carrier := fun j => e.symm (base.val (Z j))
        exact infra_69_shared_diagramEq P hμ base p hνμ hI e incl d hincl hd Q hshared
          pull (fun _ => rfl) Z hρ hρμ hjoint qv (fun j => e.apply_symm_apply _)
          (hlifts ρ hρ le_rfl qv hjoint))

/-- **Infra `infra_69_assemble`:** Package the support-copy family into an
`ApproximationSequence` (Def 6.8: `concat_bounded`, `few_exceptions`).

On `SingleModelData`, matching `infra_69_place_type` and `infra_69_off_hit_diagramEq`.
Present `A` on the padded chart (`infra_69_present_padded`: Lemmas 5.5 and 5.4, cut filling
at `σ + κ`). Read `p` across the chart equivalence. Place it by the padded clause
`infra_69_place_on_fills` — not by `infra_69_place_type`, whose skeleton does not fill cuts.
`infra_69_support_copy_sequence` is the `κ`-family (`concat_bounded`, `few_exceptions`).

A general `WorkingScheme` has no order presentation and no `Placement`. This statement is
the single-model chain. `TupleOver.InBase` and `ApproximationSequence.ofConstFamily` are
not used. The level must be closed under the `σ⁺` profile recursion; a `{D.t, g}`-closure
point need not be. -/
theorem infra_69_assemble
    (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (base : P.scheme.Object μ hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ base)
    (hνμ : p.ν = μ)
    (σ τ κ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) (hσμ : σ < μ) (hidx : #p.idx ≤ σ)
    (hτ : ℵ₀ ≤ τ) (hτμ : τ < μ)
    (hκ : ℵ₀ ≤ κ) (hκμ : κ < μ)
    (hprod : κ * #p.idx < μ)
    (hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ) :
    ∃ seq : ApproximationSequence p, seq.τ = τ ∧ #(seq.κIndex) = κ := by
  have hμSL : μ.IsStrongLimit := hμ.1.working.strongLimit
  have hη : ℵ₀ ≤ σ + κ := hσ.trans (self_le_add_right σ κ)
  have hημ : σ + κ < μ := add_lt_of_lt (P.aleph0_le hμ) hσμ hκμ
  obtain ⟨I, lo, neI, pad, hIcard, _, hfills, hex⟩ :=
    infra_69_present_padded (S := oneVertexShape) (W := P.scheme) (F := P.template)
      (hpres := P.hasPresentations) P.hasChainUnions hμ hμSL (η := σ + κ) hη hημ base
  letI : LinearOrder I := lo
  letI : Nonempty I := neI
  letI : IsPadded I := pad
  obtain ⟨_, _, hIA⟩ := hex
  obtain ⟨e⟩ := hIA PUnit.unit
  let incl : Language.Embedding K.τ (P.E.obj I).carrier p.host.model.carrier :=
    (p.incl.onVertex PUnit.unit).comp e.toEmbedding
  let d : p.idx → p.host.model.carrier := fun i => p.host.val (p.val i)
  have hstrong : K.Strong incl :=
    K.strong_trans e.toEmbedding (p.incl.onVertex PUnit.unit)
      (strong_of_equiv K e (P.hE I)) (p.incl.onVertex_strong PUnit.unit)
  obtain ⟨Q, hQ⟩ :=
    infra_69_place_on_fills P hμ base p hνμ hσ hσμ hidx hτ hτμ hIcard e incl d
      hstrong (fun _ => rfl) (fun _ => rfl) hclosed
  have hfill : OrderFillsCuts (σ + κ) I := hfills (σ + κ) le_rfl
  exact infra_69_support_copy_sequence P hμ base p hνμ σ τ κ hσ hσμ hidx hτ hτμ hκ hκμ
    hprod hIcard hfill e incl d (fun _ => rfl) (fun _ => rfl) Q hQ

/-- Deprecated mega-name: use `infra_69_assemble`. -/
abbrev support_copy_exception_and_assembly := @infra_69_assemble

/-! ## Main existence (English support-copy gloss) -/

/-- Uniform approximation sequences for `p = tp(v/A)` with `#p.idx ≤ σ` (English Lemma 6.9).

Hypotheses match Lemma 6.1 packaging. On `SingleModelData` the chain is
`infra_69_assemble`: padded chart, `infra_69_place_on_fills`, `infra_69_support_copy_sequence`.
A general `WorkingScheme` has no order presentation and no `Placement`, so it is not that
chain. `infra_69_place_type` places over a well-ordered skeleton and does not fill cuts.
`TupleOver.InBase` and `ApproximationSequence.ofConstFamily` are not a proof. -/
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
  /- `infra_69_assemble` is the single-model chain, and it needs
     `infra_69_pad_recursion_closed`. Nothing here identifies `W` with `P.scheme`, so the
     general existence stays open. Not a constant family. -/
  sorry

end
end AEC
