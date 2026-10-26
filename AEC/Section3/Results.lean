module

public import AEC.Section3.FiniteSupportOrder
public import AEC.Section3.HausdorffOrder
public import AEC.Section3.CutBalance
public import AEC.Section3.HOrderBalance
public import AEC.Section3.OrderCharacter
public import AEC.Section3.InteriorNonprincipal
public import AEC.Section3.Balanced
public import AEC.Section3.OrderEqualityDiagram
public import AEC.Section3.Occupancy
public import AEC.Section3.AdditivelyIndecomposable
public import AEC.Section3.Reversal
public import AEC.Section3.Elimination
public import AEC.Section3.OrbitName
public import AEC.Section3.OrbitRecord
public import AEC.Section3.SameRecord
public import AEC.Section3.Segment
public import AEC.Section3.ShortOrbit
public import AEC.Section3.SupportClosure
public import AEC.Section3.IndecomposableSegment
public import AEC.Section3.UniformOrbitBound
public import AEC.Section3.Profile
public import AEC.Section3.Alignment
public import AEC.Section2.OrderPresentation
public import AEC.Section2.DirectedLimit
public import AEC.Section2.Results
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Exponential

@[expose] public section

namespace AEC
section

universe u v

set_option linter.unusedVariables false

open Cardinal Set FirstOrder

/-- **Lemma 3.2.** `H(δ)` is dense without endpoints and has cardinality `|δ|`. Its points have
character `cf(δ)` on both sides. All nonempty bounded open intervals have one order type, and
all left rays, respectively all right rays, have one order type. -/
theorem lemma_3_2 (δ : _root_.Ordinal.{u}) (hδ : Order.IsSuccLimit δ) :
    (∀ a b : HOrder δ, a < b → ∃ c : HOrder δ, a < c ∧ c < b) ∧
    (∀ a : HOrder δ, ∃ b : HOrder δ, b < a) ∧
    (∀ a : HOrder δ, ∃ c : HOrder δ, a < c) ∧
    Cardinal.lift.{u + 1} δ.card = #(HOrder δ) ∧
    (∀ a : HOrder δ,
      setCofinality (Iio a) = lift.{u + 1} (Ordinal.cof δ) ∧
      setCoinitiality (Ioi a) = lift.{u + 1} (Ordinal.cof δ)) ∧
    (∀ a b c d : HOrder δ, a < b → c < d →
      Nonempty (↥(Ioo a b) ≃o ↥(Ioo c d))) ∧
    (∀ a b : HOrder δ, Nonempty (↥(Iio a) ≃o ↥(Iio b))) ∧
    (∀ a b : HOrder δ,       Nonempty (↥(Ioi a) ≃o ↥(Ioi b))) := by
  refine ⟨HOrder.dense, HOrder.noBot, HOrder.noTop, HOrder.card_eq hδ, ?_,
    HOrder.interval, HOrder.leftRay, HOrder.rightRay⟩
  intro a
  exact ⟨HOrder.leftChar hδ a, HOrder.rightChar hδ a⟩

/-- **Lemma 3.3** (Balance of cuts). Every interior nonprincipal cut of `Γδ`, and every such
cut of `H(δ)`, is balanced. -/
theorem lemma_3_3 (δ : _root_.Ordinal.{u}) :
    (∀ c : Cut (Gamma δ), Cut.IsInteriorNonprincipal c → Cut.IsBalanced c) ∧
    (∀ c : Cut (HOrder δ), Cut.IsInteriorNonprincipal c → Cut.IsBalanced c) :=
  ⟨fun c hc => gamma_balanced c hc, fun c hc => horder_balanced c hc⟩

/-- **Lemma 3.4** (Segments approaching a small cut). In a dense endpoint-free linear order
whose points have one character `κ` on both sides, whose bounded open intervals have one order
type, and whose interior nonprincipal cuts are balanced, the segment types of an interior
nonprincipal cut of regular character `ε < κ` depend only on `ε` and the side. The
isomorphisms match the displayed endpoint. -/
theorem lemma_3_4 {L : Type u} [LinearOrder L]
    (dense : ∀ a b : L, a < b → ∃ c, a < c ∧ c < b)
    (noBot : ∀ a : L, ∃ b, b < a) (noTop : ∀ a : L, ∃ c, a < c)
    (κ : Cardinal.{u})
    (pointChar : ∀ a : L, setCofinality (Iio a) = κ ∧ setCoinitiality (Ioi a) = κ)
    (oneInterval : ∀ a b c d : L, a < b → c < d → Nonempty (↥(Ioo a b) ≃o ↥(Ioo c d)))
    (balanced : ∀ c : Cut L, Cut.IsInteriorNonprincipal c → Cut.IsBalanced c)
    (ε : Cardinal.{u}) (hε : aleph0 ≤ ε) (hreg : Cardinal.IsRegular ε) (hεlt : ε < κ)
    (c d : Cut L) (hc : Cut.IsInteriorNonprincipal c) (hd : Cut.IsInteriorNonprincipal d)
    (hcb : Cut.IsBalanced c) (hdb : Cut.IsBalanced d)
    (hchar : c.characters = (ε, ε) ∧ d.characters = (ε, ε))
    (p q : L) (hp : p ∈ c.lower) (hq : q ∈ d.lower)
    (p' q' : L) (hp' : p' ∈ c.upper) (hq' : q' ∈ d.upper) :
    Nonempty (↥{x : L | x ∈ c.lower ∧ p ≤ x} ≃o ↥{x : L | x ∈ d.lower ∧ q ≤ x}) ∧
    Nonempty (↥{x : L | x ∈ c.upper ∧ x ≤ p'} ≃o ↥{x : L | x ∈ d.upper ∧ x ≤ q'}) := by
  exact bothSegments_of_regular hε hreg hεlt L
    { dense := dense, noBot := noBot, noTop := noTop, pointChar := pointChar,
      oneInterval := oneInterval, balanced := balanced }
    c d hc hd hcb hdb hchar.1 hchar.2 p q hp hq p' q' hp' hq'

/-- **Theorem 3.5** (Short-sequence order orbits). Two sequences of length at most `θ` in
`H(δ)`, with `θ < cf(δ)`, lie in the same automorphism orbit if and only if they have the same
order/equality diagram and the same strict-slot occupancies. -/
theorem theorem_3_5 (δ : _root_.Ordinal.{u}) (θ : Cardinal.{u})
    (hδ : Order.IsSuccLimit δ) (hθ : aleph0 ≤ θ)
    (hcf : lift.{u + 1} θ < lift.{u + 1} (Ordinal.cof δ))
    {ι : Type (u + 1)} (hι : #ι ≤ lift.{u + 1} θ) (xs ys : ι → HOrder δ) :
    (SameOrderDiagram xs ys ∧ SameSlotOccupancy xs ys) ↔
      ∃ e : HOrder δ ≃o HOrder δ, ∀ i, e (xs i) = ys i :=
  horder_orbit_iff δ θ hδ hθ hcf hι xs ys

/-- **Lemma 3.6** (Uniform orbit bound). There is a fixed set `Rθ` of possible presentation
records, depending only on `ℓ` and `θ`, with `|Rθ| ≤ B(ℓ, θ) := 2^{2^{ℓ+θ}}`. For every
categoricity cardinal `κ ≥ max(ℓ, θ⁺)`, the set of automorphism orbits of `θ`-tuples in its
model has cardinality at most `B(ℓ, θ)`. This applies also when `κ` is singular. If `|δ| = κ`
and `cf(δ) > θ`, each realized record in `E(H(δ))` determines exactly one such model orbit. -/
theorem lemma_3_6 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) :
    ∃ (R : Type u) (decode : R → OrbitRecord E.lab E.arity),
      #R ≤ orbitRecordBound (ls K) θ ∧
      (∀ r, #(decode r).index ≤ θ ∧ #(decode r).slot ≤ θ) ∧
      (∀ rec : OrbitRecord E.lab E.arity, #rec.index ≤ θ → #rec.slot ≤ θ →
        ∃ r, OrbitRecord.Same rec (decode r)) ∧
      ∀ (κ : Cardinal.{u}), max (ls K) (Order.succ θ) ≤ κ → Categorical K κ →
        (∀ (M : Model K.τ) {ι : Type u}, K.Mem M → Model.card M = κ → #ι ≤ θ →
          ∃ code : (ι → M.carrier) → R,
            ∀ xs ys, code xs = code ys ↔ SameAutOrbit K M xs ys) ∧
        ∀ (δ : _root_.Ordinal.{u}), δ.card = κ → θ < Ordinal.cof δ →
          ∃ (I : Type u) (_ : LinearOrder I) (_ : Nonempty I) (e : HOrder δ ≃o I),
            Model.card (E.obj I) = κ ∧
            ∀ rec : OrbitRecord E.lab E.arity, OrbitRecordRealized (I := I) E rec →
              #rec.slot ≤ θ →
              ∀ (place₁ place₂ : rec.slot → I)
                (xs ys : rec.index → (E.obj I).carrier),
                RealizesOrbitRecord (I := I) E rec place₁ xs →
                RealizesOrbitRecord (I := I) E rec place₂ ys →
                SameAutOrbit K (E.obj I) xs ys := by
  classical
  let R := CanonicalRecord E.lab E.arity θ
  let decode : R → OrbitRecord E.lab E.arity := CanonicalRecord.toOrbitRecord
  have hell : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hlab : #E.lab ≤ ls K := by simpa [E.ell_eq] using E.lab_small
  refine ⟨R, decode,
    mk_canonicalRecord_le_orbitRecordBound (arity := E.arity) θ (ls K) hlab hθ hell,
    fun r => ⟨canonical_record_card_index r, canonical_record_card_slot r⟩,
    fun rec hidx hslt => canonical_record_covers rec hidx hslt, ?_⟩
  intro κ hκle hcat
  have hlsκ : ls K ≤ κ := le_trans (le_max_left _ _) hκle
  have hsuccκ : Order.succ θ ≤ κ := le_trans (le_max_right _ _) hκle
  have hκinf : aleph0 ≤ κ := le_trans hell hlsκ
  refine ⟨?coding, ?orbits⟩
  case coding =>
    intro M ι hM hMcard hι
    let δ := categoricityOrdinal κ θ
    have hδcard := categoricityOrdinal_card (κ := κ) (θ := θ) hκinf hsuccκ
    have hδlim := categoricityOrdinal_isSuccLimit (κ := κ) (θ := θ) hθ
    have hδcof := categoricityOrdinal_cof (κ := κ) (θ := θ) hθ
    have hθlt : θ < Ordinal.cof δ := by rw [hδcof]; exact Order.lt_succ θ
    obtain ⟨I, _, _, eISO, hIcard⟩ := horderSmallCopy hδlim hδcard
    have hImem := orderPresentation_obj_mem E I
    have hEcard := orderPresentation_obj_card E hIcard hlsκ hκinf
    obtain ⟨φ⟩ := hcat.unique_model M (E.obj I) hM hImem hMcard hEcard
    let s := autOrbitSetoid K (E.obj I) hImem ι
    have hQle : #(Quotient s) ≤ #R := by
      let f : Quotient s → R := fun q =>
        canonicalOfTuple E hθ hι (Quotient.out (s := s) q)
      refine mk_le_of_injective (f := f) ?_
      intro q1 q2 hf
      rw [← Quotient.out_eq (s := s) q1, ← Quotient.out_eq (s := s) q2]
      exact Quotient.sound (same_canonical_sameAutOrbit E δ θ hδlim hθ hθlt eISO hι
        (Quotient.out (s := s) q1) (Quotient.out (s := s) q2) hf)
    obtain ⟨inj⟩ := (Cardinal.le_def (Quotient s) R).mp hQle
    refine ⟨fun xs => inj ⟦φ ∘ xs⟧, fun xs ys => ?_⟩
    constructor
    · intro hcode
      exact (sameAutOrbit_congr K hM φ xs ys).mpr
        (Quotient.exact (inj.injective hcode))
    · intro horb
      exact congrArg inj
        (Quotient.sound ((sameAutOrbit_congr K hM φ xs ys).mp horb))
  case orbits =>
    intro δ hδcard hcf
    have hδlim : Order.IsSuccLimit δ :=
      Ordinal.one_lt_cof_iff.1 (lt_of_le_of_lt (one_le_aleph0.trans hθ) hcf)
    obtain ⟨I, linI, nonI, eISO, hIcard⟩ := horderSmallCopy hδlim hδcard
    refine ⟨I, linI, nonI, eISO,
      orderPresentation_obj_card E hIcard hlsκ hκinf, ?_⟩
    intro rec _hReal hslot place₁ place₂ xs ys h₁ h₂
    exact same_record_sameAutOrbit E δ θ hδlim hθ hcf eISO rec hslot
      place₁ place₂ xs ys h₁ h₂

/-- **Lemma 3.7** (Closure of ordinal supports). A set `S ⊆ β` of size at most `a` sits in a
bounded `T₀` of size at most `a` and cofinality greater than `θ`, such that every finite tuple
from `β` has the same order/equality diagram over any `≤ θ` parameters from `T₀` as some tuple
from `T₀`. -/
theorem lemma_3_7 (θ a : Cardinal.{u}) (β : _root_.Ordinal.{u})
    (hθ : aleph0 ≤ θ) (ha : Order.succ θ ≤ a) (hβ : a.ord < β) (hcof : a < Ordinal.cof β) :
    ∀ S : Set (Ordinal.ToType β), #S ≤ a →
      ∃ T0 : Set (Ordinal.ToType β), S ⊆ T0 ∧ #T0 ≤ a ∧
        (∀ {ι : Type u} (_hι : #ι ≤ θ) (p : ι → Ordinal.ToType β),
          (∀ i, p i ∈ T0) →
          ∀ {n : ℕ} (q : Fin n → Ordinal.ToType β),
            ∃ q' : Fin n → Ordinal.ToType β,
              (∀ i, q' i ∈ T0) ∧
              SameOrderDiagram (Sum.elim p q) (Sum.elim p q')) ∧
        (∃ b : Ordinal.ToType β, ∀ x ∈ T0, x ≤ b) ∧
        θ < setCofinality T0 := by
  intro S hS
  exact support_closure θ a hθ ha hcof S hS

/-- **Lemma 3.8** (Appending a long indecomposable segment). Extending the closed support `T₀`
by a terminal segment of additively indecomposable order type `δ` yields a set of order type
`δ` with the same finite-pattern matching property, and `H(δ)` computes the strict-slot
occupancies of its `≤ θ` sequences inside `H(β)`. The set `T₀` carries the finite-pattern
property produced by Lemma 3.7. -/
theorem lemma_3_8 (θ a : Cardinal.{u}) (β δ : _root_.Ordinal.{u})
    (hθ : aleph0 ≤ θ) (ha : Order.succ θ ≤ a) (hcofβ : a < Ordinal.cof β)
    (hβ : AdditivelyIndecomposable β) (hδ : AdditivelyIndecomposable δ) (hδlt : δ < β)
    (hcfδ : θ < Ordinal.cof δ)
    (T0 : Set (Ordinal.ToType β)) (hcard : #T0 ≤ a)
    (hpat : ∀ {ι : Type u} (_hι : #ι ≤ θ) (p : ι → Ordinal.ToType β),
      (∀ i, p i ∈ T0) →
      ∀ {n : ℕ} (q : Fin n → Ordinal.ToType β),
        ∃ q' : Fin n → Ordinal.ToType β,
          (∀ i, q' i ∈ T0) ∧ SameOrderDiagram (Sum.elim p q) (Sum.elim p q'))
    (hotp : ∃ e : ↥T0 ↪o Ordinal.ToType δ, ∃ b : Ordinal.ToType δ, ∀ x, e x < b) :
    ∃ T : Set (Ordinal.ToType β), T0 ⊆ T ∧
      Nonempty (↥T ≃o Ordinal.ToType δ) ∧
      (∀ {ι : Type u} (_hι : #ι ≤ θ) (p : ι → Ordinal.ToType β),
        (∀ i, p i ∈ T) →
        ∀ {n : ℕ} (q : Fin n → Ordinal.ToType β),
          ∃ q' : Fin n → Ordinal.ToType β,
            (∀ i, q' i ∈ T) ∧ SameOrderDiagram (Sum.elim p q) (Sum.elim p q')) ∧
      ∃ f : HOrder δ ↪o HOrder β,
        ∀ {ι : Type u} (hι : #ι ≤ θ) (xs : ι → HOrder δ) (lower upper : Set ι),
          Occupied (xs '' lower) (xs '' upper) ↔
            Occupied ((fun i => f (xs i)) '' lower) ((fun i => f (xs i)) '' upper) := by
  have haleph : aleph0 ≤ a := hθ.trans ((Order.lt_succ θ).le.trans ha)
  obtain ⟨α, _, hαδ, hT0lt⟩ := exists_segment_base haleph hcofβ hβ hδlt T0 hcard
  obtain ⟨T, hsub, ⟨e⟩, hmem⟩ := exists_extended_iso hδ α hαδ T0 hT0lt hotp
  have hpatT :
      ∀ {ι : Type u} (_hι : #ι ≤ θ) (p : ι → Ordinal.ToType β), (∀ i, p i ∈ T) →
        ∀ {n : ℕ} (q : Fin n → Ordinal.ToType β), ∃ q' : Fin n → Ordinal.ToType β,
          (∀ k, q' k ∈ T) ∧ SameOrderDiagram (Sum.elim p q) (Sum.elim p q') :=
    extended_pattern hθ hcfδ α hαδ T0 hT0lt hpat T hmem
  refine ⟨T, hsub, ⟨e⟩, hpatT, horderPush (segmentPosition e), ?_⟩
  intro ι hι xs lower upper
  exact extended_occupancy T hpatT e hθ hι xs lower upper

/-- **Proposition 3.9** (Alignment of model orbits). When a presentation of the model of size
`μ` and a cofinal family of presentations of the model of size `a` share one profile, every
set of size at most `a` in a copy of the large model sits in a strong submodel of size `a`
whose `θ`-tuple orbit names agree with the names computed in the large model. -/
theorem proposition_3_9 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ a μ : Cardinal.{u}) (N : OrbitNaming K θ)
    (hθ : aleph0 ≤ θ) (ha : max (ls K) (Order.succ θ) ≤ a) (hμ : a < μ)
    (hcatA : Categorical K a) (hcatμ : Categorical K μ)
    (P : CommonProfileSetup K E θ a μ N hθ) :
    ∀ (M : Model K.τ) (hM : K.Mem M), Model.card M = μ →
      ∀ S : Set M.carrier, #S ≤ a →
        ∃ (A : Model K.τ) (f : Language.Embedding K.τ A.carrier M.carrier) (hA : K.Mem A),
          K.Strong f ∧ Model.card A = a ∧
          (∀ x ∈ S, ∃ y, f y = x) ∧
          ∀ {ι : Type u} (hι : #ι ≤ θ) (xs : ι → A.carrier),
            N.name (M := A) (ι := ι) hA xs hι =
              N.name (M := M) (ι := ι) hM (fun i => f (xs i)) hι := by
  classical
  intro M hM hMcard S hS
  have hls : ls K ≤ a := (le_max_left _ _).trans ha
  have hsucc : Order.succ θ ≤ a := (le_max_right _ _).trans ha
  have haleph_a : aleph0 ≤ a := hθ.trans ((Order.lt_succ θ).le.trans hsucc)
  have hβlim : Order.IsSuccLimit P.β :=
    Ordinal.one_lt_cof_iff.1 (lt_of_le_of_lt (one_le_aleph0.trans haleph_a) P.β_cof_a)
  obtain ⟨I, _, _, eI, hIcard⟩ := horderSmallCopy hβlim P.β_card
  have hImem := orderPresentation_obj_mem E I
  have hlsμ : ls K ≤ μ := hls.trans hμ.le
  have hEμ := orderPresentation_obj_card E hIcard hlsμ (haleph_a.trans hμ.le)
  obtain ⟨φ⟩ := hcatμ.unique_model M (E.obj I) hM hImem hMcard hEμ
  let S' : Set (E.obj I).carrier := φ '' S
  have hS' : #S' ≤ a := (mk_image_le).trans hS
  let Sord := ordinalSupportOf E eI S'
  have hSord : #Sord ≤ a := ordinalSupportOf_card E eI haleph_a S' hS'
  have hμβ : μ.ord ≤ P.β := by
    have h := Cardinal.ord_card_le P.β
    rwa [P.β_card] at h
  have hβord : a.ord < P.β := (Cardinal.ord_lt_ord.mpr hμ).trans_le hμβ
  obtain ⟨T0, hSsub, hT0card, hpat, _, _⟩ :=
    lemma_3_7 θ a P.β hθ hsucc hβord P.β_cof_a Sord hSord
  obtain ⟨δ, hδmem, hotp, hδind, hδcard, hδcof⟩ :=
    exists_profile_delta (θ := θ) haleph_a P.Deltas P.deltas_spec P.deltas_cofinal T0 hT0card
  obtain ⟨eT0, bT0, hbT0⟩ := exists_otp_embedding (β := P.β) (δ := δ) T0 hotp
  have hδltβ : δ < P.β := by
    have hδlt : δ < (Order.succ a).ord := (P.deltas_spec δ hδmem).2.2.2
    have haμ : (Order.succ a).ord ≤ μ.ord :=
      Cardinal.ord_le_ord.mpr (Order.succ_le_of_lt hμ)
    exact hδlt.trans_le (haμ.trans hμβ)
  -- Expand Lemma 3.8 so the segment iso and Hausdorff push share one witness
  have haleph' : aleph0 ≤ a := haleph_a
  obtain ⟨α, _, hαδ, hT0lt⟩ :=
    exists_segment_base haleph' P.β_cof_a P.β_indecomposable hδltβ T0 hT0card
  obtain ⟨T, hT0sub, ⟨eT⟩, hmem⟩ :=
    exists_extended_iso hδind α hαδ T0 hT0lt ⟨eT0, bT0, hbT0⟩
  have hpatT :
      ∀ {ι : Type u} (_hι : #ι ≤ θ) (p : ι → P.β.ToType), (∀ i, p i ∈ T) →
        ∀ {n : ℕ} (q : Fin n → P.β.ToType), ∃ q' : Fin n → P.β.ToType,
          (∀ k, q' k ∈ T) ∧ SameOrderDiagram (Sum.elim p q) (Sum.elim p q') :=
    extended_pattern (θ := θ) (β := P.β) (δ := δ) hθ hδcof α hαδ T0 hT0lt hpat T hmem
  let φH : HOrder δ ↪o HOrder P.β := horderPush (segmentPosition eT)
  have hocc :
      ∀ {ι : Type u} (hι : #ι ≤ θ) (xs : ι → HOrder δ) (lower upper : Set ι),
        Occupied (xs '' lower) (xs '' upper) ↔
          Occupied ((fun i => φH (xs i)) '' lower) ((fun i => φH (xs i)) '' upper) := by
    intro ι hι xs lower upper
    simpa [φH] using extended_occupancy (θ := θ) T hpatT eT hθ hι xs lower upper
  have hδlim : Order.IsSuccLimit δ :=
    Ordinal.one_lt_cof_iff.1 (lt_of_le_of_lt (one_le_aleph0.trans hθ) hδcof)
  obtain ⟨J, _, _, eJ, hJcard⟩ := horderSmallCopy hδlim hδcard
  have hJmem := orderPresentation_obj_mem E J
  have hEa := orderPresentation_obj_card E hJcard hls haleph_a
  let embIJ := E.map (softPush eJ eI φH)
  have hembStrong : K.Strong embIJ := softPush_strong E eJ eI φH
  let f : Language.Embedding K.τ (E.obj J).carrier M.carrier :=
    φ.symm.toEmbedding.comp embIJ
  have hfStrong : K.Strong f :=
    K.transport_strong embIJ φ.symm hembStrong
  have hcontains : ∀ x ∈ S, ∃ y, f y = x := by
    intro x hx
    let x' := φ x
    have hx' : x' ∈ S' := Set.mem_image_of_mem φ hx
    let t := supportTermOf E x'
    have htreal := realize_supportTermOf E x'
    have hpos_in_T : ∀ k : Fin (E.arity t.label),
        ∀ i ∈ hSupport (eI.symm (t.pos k)),
          Ordinal.ToType.mk (asIio i) ∈ T := by
      intro k i hi
      have : Ordinal.ToType.mk (asIio i) ∈ Sord := by
        dsimp [Sord, ordinalSupportOf]
        refine Set.mem_biUnion hx' ?_
        refine Set.mem_biUnion (Set.mem_range_self k) ?_
        exact Set.mem_image_of_mem _ hi
      exact hT0sub (hSsub this)
    have hpos_range : ∀ k : Fin (E.arity t.label),
        eI.symm (t.pos k) ∈ Set.range φH := by
      intro k
      obtain ⟨w, hw⟩ := horder_supported_pull (segmentPosition eT) (eI.symm (t.pos k)) (by
        intro g hg i hi
        have him : i ∈ hSupport (eI.symm (t.pos k)) := by
          simp only [hSupport, Finset.mem_biUnion]
          exact ⟨g, hg, hi⟩
        exact segmentPosition_of_mem eT i (hpos_in_T k i him))
      exact ⟨w, hw⟩
    let posJ : Fin (E.arity t.label) → J := fun k =>
      eJ (Classical.choose (hpos_range k))
    have hinc : StrictMono posJ := by
      intro k₁ k₂ hk
      dsimp [posJ]
      refine (eJ.lt_iff_lt).mpr ?_
      have hw1 := Classical.choose_spec (hpos_range k₁)
      have hw2 := Classical.choose_spec (hpos_range k₂)
      exact (φH.lt_iff_lt).mp (by
        change φH _ < φH _
        rw [hw1, hw2]
        exact (eI.symm.lt_iff_lt).mpr (t.increasing hk))
    let y : (E.obj J).carrier := E.realize ⟨t.label, posJ, hinc⟩
    refine ⟨y, ?_⟩
    change φ.symm (embIJ y) = x
    have hy : embIJ y = x' := by
      dsimp [embIJ, y]
      rw [E.realize_map]
      have hterm : SupportTerm.mk t.label
          (softPush eJ eI φH ∘ posJ)
          ((softPush eJ eI φH).strictMono.comp hinc) = t := by
        refine SupportTerm.ext_of_label_eq rfl fun k => ?_
        change eI (φH (eJ.symm (eJ (Classical.choose (hpos_range k))))) = t.pos k
        rw [OrderIso.symm_apply_apply, Classical.choose_spec (hpos_range k),
          OrderIso.apply_symm_apply]
      simpa [hterm] using htreal
    simpa [hy, x'] using Equiv.symm_apply_apply φ x
  refine ⟨E.obj J, f, hJmem, hfStrong, hEa, hcontains, ?_⟩
  intro ι hι xs
  have hsmall := P.assign_small δ hδmem eJ hι xs
  have hreal := realizes_canonical_softPush E hθ eJ eI φH hocc hι xs
  have hlarge := P.assign_realizes_large eI hι (fun i => embIJ (xs i))
    (canonicalOfTuple E hθ hι xs)
    (fun s => softPush eJ eI φH (canonicalPlaceOfTuple E hθ hι xs s))
    (canonicalOfTupleIndexEquiv E hθ hι xs).symm
    hreal
  have hnames : N.name hJmem xs hι =
      N.name hImem (fun i => embIJ (xs i)) hι := by
    have : some (N.name hJmem xs hι) = some (N.name hImem (fun i => embIJ (xs i)) hι) := by
      rw [← hsmall, ← hlarge]
    exact Option.some.inj this
  have htoM := N.name_iso φ.symm hImem hM (fun i => embIJ (xs i)) hι
  exact hnames.trans (by simpa [f, Language.Embedding.comp_apply] using htoM)

/-- **Lemma 3.10.** The additively indecomposable ordinals `δ < κ⁺` with `|δ| = κ` and
`cf(δ) = τ` are cofinal in `κ⁺`, for infinite `κ` and infinite regular `τ ≤ κ`. -/
theorem lemma_3_10 (κ τ : Cardinal.{u}) (hκ : aleph0 ≤ κ) (hτ : aleph0 ≤ τ)
    (hreg : Cardinal.IsRegular τ) (hle : τ ≤ κ) :
    ∀ α : _root_.Ordinal.{u}, α < (Order.succ κ).ord →
      ∃ δ : _root_.Ordinal.{u}, α ≤ δ ∧ δ < (Order.succ κ).ord ∧
        AdditivelyIndecomposable δ ∧ δ.card = κ ∧ Ordinal.cof δ = τ := by
  intro α hα
  have hαcard : α.card ≤ κ := Cardinal.card_le_iff.mpr hα
  let ρ : _root_.Ordinal.{u} := α + κ.ord + τ.ord
  have hτlim : Order.IsSuccLimit τ.ord := Cardinal.isSuccLimit_ord hτ
  have hρlim : Order.IsSuccLimit ρ := Ordinal.isSuccLimit_add (α + κ.ord) hτlim
  have hρcard : ρ.card = κ := by
    have hsum : (α + κ.ord).card = κ := by
      rw [Ordinal.card_add, Cardinal.card_ord, add_comm, Cardinal.add_eq_max hκ,
        max_eq_left hαcard]
    rw [Ordinal.card_add, Cardinal.card_ord, hsum, Cardinal.add_eq_max hκ, max_eq_left hle]
  have hcofρ : Ordinal.cof ρ = τ := by
    rw [Ordinal.cof_add (α + κ.ord) hτlim.ne_bot, hreg.cof_ord]
  refine ⟨Ordinal.omega0 ^ ρ, ?_, ?_, ⟨Ordinal.isPrincipal_add_omega0_opow ρ⟩, ?_, ?_⟩
  · exact (le_self_add : α ≤ α + κ.ord).trans
      ((le_self_add : α + κ.ord ≤ α + κ.ord + τ.ord).trans
        (Ordinal.right_le_opow ρ Ordinal.one_lt_omega0))
  · apply Cardinal.card_le_iff.mp
    rw [Ordinal.card_omega0_opow hρlim.ne_bot, hρcard, max_eq_right hκ]
  · rw [Ordinal.card_omega0_opow hρlim.ne_bot, hρcard, max_eq_right hκ]
  · rw [Ordinal.cof_map_of_isNormal (Ordinal.isNormal_opow Ordinal.one_lt_omega0) hρlim, hcofρ]

/-- **Theorem 3.11** (Eventual reversal at categoricity cardinals). For each infinite cardinal
`θ` there is a bound `b_K(θ)` such that, at every categoricity cardinal `κ ≥ b_K(θ)`, every
strong self-embedding is inverted on every tuple of length at most `θ`.

Proof shape (text.md §3.5): if failing categoricity cardinals are bounded, apply
`isReversalThreshold_of_fails_bounded`. Otherwise the `P⁺`-sequence of failures, profile
pigeonhole, Proposition 3.9 alignment, the θ⁺-renaming kill, and `killed_copy_impossible`
yield a contradiction. -/
theorem theorem_3_11 (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) :
    ∃ b : Cardinal.{u}, IsReversalThreshold K θ b := by
  classical
  by_cases hB : ∃ B : Cardinal.{u}, ∀ κ, FailsReversal K θ κ → κ ≤ B
  · obtain ⟨B, hBound⟩ := hB
    exact ⟨Order.succ B, isReversalThreshold_of_fails_bounded K θ B hBound⟩
  · -- Unbounded failures: eliminate via profiles + Prop 3.9 renaming (text.md 180–202).
    push Not at hB
    have hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ := hB
    have : ArbitrarilyLarge K := arbitrarilyLarge_of_unbounded_fails K θ hUnb
    obtain ⟨E, _, _⟩ := @theorem_2_6 K this
    let N := elimOrbitNaming K E θ hθ
    -- Remaining (text.md 186–201): profile pigeonhole on `failingSequence` → a < μ with
    -- common cofinal profile and asymmetric NamedArrow p→r; CommonProfileSetup + Prop 3.9;
    -- θ⁺·a^θ renaming kill; killed_copy_impossible K θ a N ... .
    exact False.elim (by
      clear N
      sorry)

end
end AEC
