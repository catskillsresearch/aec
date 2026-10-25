module

public import AEC.Section5.StrictClosure
public import AEC.Section5.EligibleLevel

@[expose] public section

namespace AEC
section

universe u


open Cardinal

/-- A closure point in the sense of the construction after Proposition 4.3:
a strong limit of countable cofinality, strictly closed under each listed bound. -/
class IsClosurePoint (bounds : Set (Cardinal.{u} → Cardinal.{u})) (μ : Cardinal.{u}) : Prop where
  working : IsWorkingLevel μ
  closed : ∀ u ∈ bounds, StrictlyClosed u μ

end
end AEC
