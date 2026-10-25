module

public import AEC.Section3.Cut

@[expose] public section

namespace AEC
section

universe u

/-- An interior nonprincipal cut has both sides nonempty, no greatest lower point,
and no least upper point. -/
class Cut.IsInteriorNonprincipal {α : Type u} [LinearOrder α] (c : Cut α) : Prop where
  lower_nonempty : c.lower.Nonempty
  upper_nonempty : c.upper.Nonempty
  lower_no_greatest : ∀ a ∈ c.lower, ∃ b ∈ c.lower, a < b
  upper_no_least : ∀ b ∈ c.upper, ∃ a ∈ c.upper, a < b

end
end AEC
