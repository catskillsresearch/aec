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
public import AEC.Section3.OrbitName
public import AEC.Section3.OrbitRecord
public import AEC.Section3.SameRecord
public import AEC.Section3.Segment
public import AEC.Section2.OrderPresentation
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace AEC
section

universe u v

set_option linter.unusedVariables false

open Cardinal Set FirstOrder

/-- Strict slots over a sequence are occupied in the same pattern. -/
def SameSlotOccupancy {ι α : Type v} [LinearOrder α] (xs ys : ι → α) : Prop :=
  ∀ (lower upper : Set ι),
    (∀ i ∈ lower, ∀ j ∈ upper, xs i < xs j) →
    (∀ i ∈ lower, ∀ j ∈ upper, ys i < ys j) →
    Occupied (xs '' lower) (xs '' upper) ↔ Occupied (ys '' lower) (ys '' upper)

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
      ∃ e : HOrder δ ≃o HOrder δ, ∀ i, e (xs i) = ys i := by
  sorry

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
              ∀ (place₁ place₂ : rec.slot → I)
                (xs ys : rec.index → (E.obj I).carrier),
                RealizesOrbitRecord (I := I) E rec place₁ xs →
                RealizesOrbitRecord (I := I) E rec place₂ ys →
                SameAutOrbit K (E.obj I) xs ys := by
  sorry

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
  sorry

/-- **Lemma 3.8** (Appending a long indecomposable segment). Extending the closed support `T₀`
by a terminal segment of additively indecomposable order type `δ` yields a set of order type
`δ` with the same finite-pattern matching property, and `H(δ)` computes the strict-slot
occupancies of its `≤ θ` sequences inside `H(β)`. -/
theorem lemma_3_8 (θ a : Cardinal.{u}) (β δ : _root_.Ordinal.{u})
    (hθ : aleph0 ≤ θ) (ha : Order.succ θ ≤ a) (hcofβ : a < Ordinal.cof β)
    (hβ : AdditivelyIndecomposable β) (hδ : AdditivelyIndecomposable δ) (hδlt : δ < β)
    (hcfδ : θ < Ordinal.cof δ)
    (T0 : Set (Ordinal.ToType β)) (hcard : #T0 ≤ a)
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
  sorry

/-- **Proposition 3.9** (Alignment of model orbits). When a presentation of the model of size
`μ` and a cofinal family of presentations of the model of size `a` share one profile, every
set of size at most `a` in a copy of the large model sits in a strong submodel of size `a`
whose `θ`-tuple orbit names agree with the names computed in the large model. -/
theorem proposition_3_9 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ a μ : Cardinal.{u}) (N : OrbitNaming K θ)
    (hθ : aleph0 ≤ θ) (ha : max (ls K) (Order.succ θ) ≤ a) (hμ : a < μ)
    (hcatA : Categorical K a) (hcatμ : Categorical K μ) :
    ∀ (M : Model K.τ) (hM : K.Mem M), Model.card M = μ →
      ∀ S : Set M.carrier, #S ≤ a →
        ∃ (A : Model K.τ) (f : Language.Embedding K.τ A.carrier M.carrier) (hA : K.Mem A),
          K.Strong f ∧ Model.card A = a ∧
          (∀ x ∈ S, ∃ y, f y = x) ∧
          ∀ {ι : Type u} (hι : #ι ≤ θ) (xs : ι → A.carrier),
            N.name (M := A) (ι := ι) hA xs hι =
              N.name (M := M) (ι := ι) hM (fun i => f (xs i)) hι := by
  sorry

/-- **Lemma 3.10.** The additively indecomposable ordinals `δ < κ⁺` with `|δ| = κ` and
`cf(δ) = τ` are cofinal in `κ⁺`, for infinite `κ` and infinite regular `τ ≤ κ`. -/
theorem lemma_3_10 (κ τ : Cardinal.{u}) (hκ : aleph0 ≤ κ) (hτ : aleph0 ≤ τ)
    (hreg : Cardinal.IsRegular τ) (hle : τ ≤ κ) :
    ∀ α : _root_.Ordinal.{u}, α < (Order.succ κ).ord →
      ∃ δ : _root_.Ordinal.{u}, α ≤ δ ∧ δ < (Order.succ κ).ord ∧
        AdditivelyIndecomposable δ ∧ δ.card = κ ∧ Ordinal.cof δ = τ := by
  sorry

/-- **Theorem 3.11** (Eventual reversal at categoricity cardinals). For each infinite cardinal
`θ` there is a bound `b_K(θ)` such that, at every categoricity cardinal `κ ≥ b_K(θ)`, every
strong self-embedding is inverted on every tuple of length at most `θ`. -/
theorem theorem_3_11 (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) :
    ∃ b : Cardinal.{u}, IsReversalThreshold K θ b := by
  sorry

end
end AEC
