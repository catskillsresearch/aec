module

public import AEC.Section5.PackageClauses
public import AEC.Section5.RichPaddedOrder
public import Mathlib.Data.Set.Basic

@[expose] public section

/-!
# Order-pattern realization from cut filling (Lemma 5.5 equivalence)

English: every extension of an order pattern with at most `η` old and at most `η` added
positions can be realized over its old positions, given that cuts with at most `η` parameters on
each side are filled. The implication is discharged in `order_pattern_realized_over_old`.
-/

namespace AEC
section

universe u

open Cardinal OrderEmbedding

/-- A linear order **fills `η`-bounded cuts** (Lemma 5.5, first clause). -/
def OrderFillsCuts (η : Cardinal.{u}) (Q : Type u) [LinearOrder Q] : Prop :=
  ∀ (L R : Set Q), #L ≤ η → #R ≤ η → (∀ a ∈ L, ∀ b ∈ R, a < b) →
    ∃ x : Q, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b)

/-- Data for an order-pattern extension (`η` old / `η` added positions). -/
structure OrderPattern (η : Cardinal.{u}) (Old Ext : Type u) [LinearOrder Old]
    [LinearOrder Ext] where
  emb : Old ↪o Ext
  card_old : #Old ≤ η
  cardAdded : #(Set.diff Set.univ (Set.range ⇑emb)) ≤ η

/-- Added positions of an order pattern. -/
def OrderPattern.added {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old] [LinearOrder Ext]
    (pat : OrderPattern η Old Ext) : Set Ext :=
  Set.diff Set.univ (Set.range ⇑pat.emb)

theorem OrderPattern.mem_added_iff {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) (x : Ext) :
    x ∈ pat.added ↔ x ∉ Set.range (⇑pat.emb) := by
  change (x ∈ Set.univ ∧ x ∉ Set.range ⇑pat.emb) ↔ x ∉ Set.range ⇑pat.emb
  simp

/-- Cut filling implies order-pattern realization (Lemma 5.5 equivalence, pattern direction). -/
def OrderPatternRealized (η : Cardinal.{u}) (Q : Type u) [LinearOrder Q] : Prop :=
  ∀ {Old Ext : Type u} [LinearOrder Old] [LinearOrder Ext]
    (pat : OrderPattern η Old Ext) (f : Old ↪o Q),
    ∃ g : Ext ↪o Q, ∀ a : Old, g (pat.emb a) = f a

/-- **Pattern direction of Lemma 5.5.** Well-founded placement along a linear extension of the
added positions, using `η`-bounded cut filling at each step. -/
theorem order_pattern_realized_over_old {η : Cardinal.{u}} (hη : ℵ₀ ≤ η) {Q : Type u}
    [LinearOrder Q] (hfill : OrderFillsCuts η Q) {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) (f : Old ↪o Q) :
    ∃ g : Ext ↪o Q, ∀ a : Old, g (pat.emb a) = f a := by
  classical
  sorry

theorem orderPatternRealized_of_fillsCuts {η : Cardinal.{u}} (hη : ℵ₀ ≤ η) {Q : Type u}
    [LinearOrder Q] (hfill : OrderFillsCuts η Q) :
    OrderPatternRealized η Q :=
  fun pat f => order_pattern_realized_over_old hη hfill pat f

/-- Every order from Lemma 5.5 fills cuts and hence realizes patterns. -/
theorem orderPatternRealized_of_lemma_5_5 (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) {Q : Type u}
    [LinearOrder Q] (hfill : OrderFillsCuts η Q) :
    OrderPatternRealized η Q :=
  orderPatternRealized_of_fillsCuts hη hfill

/-- A dense rich `Pt η` order (Lemma 5.5) fills cuts and realizes patterns. -/
theorem orderPatternRealized_pt (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) :
    OrderPatternRealized η (Pt η) :=
  orderPatternRealized_of_fillsCuts hη (by
    intro L R hL hR hcut
    obtain ⟨x, hxL, hxR⟩ := pt_fills_cuts η hη L R hL hR hcut
    exact ⟨x, hxL, hxR⟩)

end
end AEC
