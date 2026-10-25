module

public import AEC.Section5.EligibleLevel
public import Mathlib.Order.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- A class of cardinals is closed under strictly increasing countable suprema. -/
class CountablySupClosed (T : Set Cardinal.{u}) : Prop where
  sup : ∀ f : ℕ → Cardinal.{u}, (∀ n, f n ∈ T) → StrictMono f → sSup (Set.range f) ∈ T

/-- **Convention 5.3.** The input eligible class `S` contains a fixed definable unbounded
subclass `T` closed under suprema of strictly increasing countable sequences. -/
def EligibleSubclass (S T : Set Cardinal.{u}) : Prop :=
  T ⊆ S ∧ (∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ T) ∧ CountablySupClosed T

end
end AEC
