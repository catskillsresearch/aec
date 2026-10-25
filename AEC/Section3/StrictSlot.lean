module

public import Mathlib.Order.Basic

@[expose] public section

namespace AEC
section

universe u


/-- The strict slot of a cut `(A⁻, A⁺)` of a subset of `L`:
`{x ∈ L \ A : A⁻ < x < A⁺}`. -/
def strictSlot {α : Type u} [LinearOrder α] (lower upper : Set α) : Set α :=
  {x | x ∉ lower ∧ x ∉ upper ∧ (∀ a ∈ lower, a < x) ∧ (∀ b ∈ upper, x < b)}

end
end AEC
