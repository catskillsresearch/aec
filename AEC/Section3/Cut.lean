module

public import Mathlib.Data.Set.Lattice

@[expose] public section

namespace AEC
section

universe u

/-- A cut of a linear order `L` is a partition `(L⁻, L⁺)` with `L⁻ < L⁺`. -/
structure Cut (α : Type u) [LinearOrder α] where
  lower : Set α
  upper : Set α
  union_eq : lower ∪ upper = Set.univ
  disjoint : Disjoint lower upper
  ordered : ∀ a ∈ lower, ∀ b ∈ upper, a < b

end
end AEC
