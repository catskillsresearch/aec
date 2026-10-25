module

public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

namespace AEC
section

universe u

/-- **Definition 6.2.** A natural parameter layout: finitely many slots, a finite ordered set of
colors, and the monotonicity property that increasing the ordinal lengths of the unfrozen slots
embeds the layout and preserves the designated parameter terms. -/
structure NaturalParameterLayout where
  Slot : Type u
  slotFinite : Finite Slot
  Color : Type u
  colorFinite : Finite Color
  colorOrder : LinearOrder Color
  frozen : Set Slot
  /-- A lengthening preserves the designated parameter terms. -/
  embeds : (Slot → _root_.Ordinal.{u}) → (Slot → _root_.Ordinal.{u}) → Prop
  mono : ∀ len len' : Slot → _root_.Ordinal.{u},
    (∀ s, s ∈ frozen → len s = len' s) →
    (∀ s, s ∉ frozen → len s ≤ len' s) →
    embeds len len'

end
end AEC
