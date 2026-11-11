module

public import AEC.Section6.ApproximationSequence
public import AEC.Section6.ParameterOrbits
public import AEC.Section5.PackageClauses
public import AEC.Section5.Results
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Sum.Order

@[expose] public section

/-!
# Uniform approximation sequences (Lemma 6.9)

1:1 Lean gloss of the English support-copy proof (eventual.pdf §6.2; see also Lemma 5.5.md
equivalence clause).

English steps:

1. By the rich-order and padding constructions of Lemmas 5.5 and 5.4, present `A` on a padded
   chart (`exists_denseRichOrder`, `exists_richPaddedOrder`, `lemma_5_4`).
2. Lemma 6.5 / compact placement places `p = tp(v/A)` at query size `τ`
   on the well-ordered skeleton of the padded chart (`infra_69_place_type`).
3. Keep shared old-chart supports; partition other supports by cuts; anchors have size at most
   `σ + ℵ₀` (`ChartSupport`, the pure-order infras below).
4. In each anchor slot, choose `κ` pairwise disjoint convex regions and put a copy of the
   pattern; richness realizes the needed order patterns (English: Lemma 5.5 equivalence).
5. If supports avoid every region, Lemma 6.1 gives `D(vᵢ,Z) = p↾Z` for all but at most
   `|Z|+ℵ₀` indices; block interchange (Lemma 4.6) for the copy-region bookkeeping.
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
placement (`exists_placement_lifting`) at one `χ` with `τ ≤ χ < μ`, `χ ^ σ = χ`, and
`ℓ + σ < χ` does not need a tester. The resulting placement realizes every query of size at
most `τ`.

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
          ∀ {β : Type u} (ρ : Cardinal.{u}), ℵ₀ ≤ ρ → ρ ≤ τ →
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
  have hρχμ : σ + χ < μ := add_lt_of_lt hμinf hσμ hχμ
  have hρinf : ℵ₀ ≤ σ + χ := (hτ.trans hτχ.le).trans (self_le_add_left χ σ)
  have ht : P.D.t (σ + χ) ≤ μ := (P.t_lt hμ hρinf hρχμ).le
  obtain ⟨Q, hQ⟩ := exists_placement_lifting (hB := p.host.mem) (incl := incl) (d := d)
    hstrong (P.categorical hμ) hcardB hcardS hσ hidx hlsχ hpow ht
  refine ⟨s, hsNe, hsWF, hsμ, e, incl, d, hstrong, fun _ => rfl, fun _ => rfl, hcardB, Q, ?_⟩
  intro β ρ hρinf' hρτ q hj
  have hβχ : #β ≤ χ := by
    refine le_trans ?_ (hj.trans (hρτ.trans hτχ.le))
    rw [mk_sum, lift_id, lift_id]
    exact self_le_add_left _ _
  have hjχ : #(p.idx ⊕ β) ≤ σ + χ :=
    hj.trans (hρτ.trans (hτχ.le.trans (self_le_add_left χ σ)))
  have hls : ls K ≤ σ + χ :=
    (self_le_add_right (ls K) σ).trans (hlsχ.le.trans (self_le_add_left χ σ))
  have hBc : P.D.t (σ + χ) ≤ Model.card p.host.model := ht.trans hcardB.ge
  have hJc : P.D.t (σ + χ) ≤ Model.card (P.E.obj Q.J) :=
    (ht.trans hcardS.ge).trans (mk_le_of_injective (P.E.map Q.f).injective)
  exact (hQ hβχ q hjχ).relevel hρinf hρinf' le_rfl
    (hρτ.trans (hτχ.le.trans (self_le_add_left χ σ))) hls hBc hJc hj id

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
      (∀ i y (a : C.anchorIdx), a.1 < copy i y ↔ C.old a.1 < x) := by
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
    simpa [copy, OrderEmbedding.coe_ofStrictMono] using hanchor i y a

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

/-- **Infra `infra_69_lem61_off_hits`:** Their anchor slots are disjoint, so Lemma 6.1 gives
`D(vᵢ, Z) = p↾Z`.

Pinned. The order half is the disjointness of the anchor slots (`hoff`). Identifying the
off-hit copy with `p ↾ Z` is a `WorkingScheme.DiagramEq`, and the development does not supply
it. -/
theorem infra_69_lem61_off_hits
    [CategoricalUnbounded K]
    (hedge : ∀ i j, ¬ S.specified i j)
    (hcat : ∀ μ' ∈ W.eligible, Categorical K μ')
    (σ χ b : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) (hpow : χ ^ σ = χ) (hb : b + σ < χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ)
    (hiso : AssemblesStructIso W b)
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
    (p : TupleOver K S W hμ base)
    {I J : Type u} [LinearOrder I] [LinearOrder J] (C : ChartSupport I J)
    {κIndex ι : Type u} (region : κIndex → Set I)
    (hdisj : ∀ i j, i ≠ j → Disjoint (region i) (region j))
    (family : κIndex → p.idx → Occurrence K S (W.asSystem hμ base))
    (Z : ι → Occurrence K S (W.asSystem hμ base))
    (supportZ : ι → Set J) (i : κIndex)
    (hoff : ∀ z, Disjoint (supportZ z) (⇑C.old '' region i)) :
    W.DiagramEq (X := p.host) (Y := base)
      (typeJoint (p := p) Z) (seqJoint (family i) Z) := by
  /- English (eventual.pdf §6.2): "Their anchor slots are disjoint, so Lemma 6.1 gives
     `D(vᵢ, Z) = p↾Z`."
     Missing API:
     * `infra_69_place_type` places `p` over the well-ordered skeleton, for queries of size at
       most `τ` (`Placement.Lifts`). It does not produce a `WorkingScheme.DiagramEq`;
     * there is no reading of an order-support copy as an `Occurrence` list for which
       `WorkingScheme.DiagramEq` is `StableDiagram.same`;
     * `lemma_6_1` / `WorkingScheme.exists_parameter_orbit_reps` bounds the number of diagrams
       of `σ`-tuples over parameters, and does not identify `D(vᵢ, Z)` with `p ↾ Z`. -/
  sorry

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

/-- **Infra `infra_69_assemble`:** Package the support-copy family into an
`ApproximationSequence` (Def 6.8: `concat_bounded`, `few_exceptions`). -/
theorem infra_69_assemble
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
  /- English (eventual.pdf §6.2, Definition 6.8): package the support-copy family into an
     approximation sequence (`concat_bounded`, `few_exceptions`).
     Missing API:
     * `infra_69_place_type` places `p` over the skeleton for queries of size at most `τ`, and
       supplies no `Occurrence` family;
     * `infra_69_lem61_off_hits` is the missing `WorkingScheme.DiagramEq` for indices whose
       supports avoid the copy regions, which is what `few_exceptions` asks for.
     `infra_69_copy_cluster`, `infra_69_hit_bound`, `infra_69_finitary_exceptions`, and
     `infra_69_subtuple_uniform` do not produce the `Occurrence` family.
     `TupleOver.InBase` and `ApproximationSequence.ofConstFamily` are not used. -/
  sorry

/-- Deprecated mega-name: use `infra_69_assemble`. -/
abbrev support_copy_exception_and_assembly := @infra_69_assemble

/-! ## Main existence (English support-copy gloss) -/

/-- Uniform approximation sequences for `p = tp(v/A)` with `#p.idx ≤ σ` (English Lemma 6.9).

Hypotheses match Lemma 6.1 packaging. The proof follows the English paragraphs above; it is
pinned at `infra_69_assemble` (`infra_69_lem61_off_hits` is the missing `DiagramEq`).
On `SingleModelData`, `infra_69_place_type` places `p` over the skeleton at size `τ`.
Steps 1–2 invoke Lemmas 5.5 and 5.4. -/
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
    · obtain ⟨I, _loI, _neI, _padI, hIcard, _, _, _, _, _⟩ :=
        infra_69_present_padded F hpack hμ hμSL hτ hμτ base
      obtain ⟨_, _, _, _⟩ := infra_69_chart_iso F hpack hcat hμ I hIcard base
      trivial
    · -- Without `μ` a strong limit, English cites cut filling at `2^τ` only.
      trivial
  -- English step 2, on `SingleModelData`: `infra_69_place_type` places `p` over the
  -- well-ordered skeleton of the padded chart, for queries of size at most `τ`. This
  -- general-scheme existence has no `SingleModelData`, so the placement is not unpacked here.
  -- English steps 3–4: `ChartSupport` proves the anchor and pattern-arity infras. The copy
  -- family is still packaged by `infra_69_assemble`.
  have hη : aleph0 ≤ max τ σ := le_trans hτ (le_max_left τ σ)
  have hpattern : EnglishOrderPatternRealized (max τ σ) :=
    english_orderPattern_realized_over_old (max τ σ) hη
  exact infra_69_assemble F hedge hcat σ χ b τ κ hχ hiso p hχμ hpattern

end
end AEC
