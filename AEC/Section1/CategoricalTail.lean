module

public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- A tail of cardinals is every cardinal above a fixed bound.
`K` is categorical on a tail when there is `μ` such that `K` is categorical
in every `κ ≥ μ`. -/
class CategoricalOnTail (K : AbstractElementaryClass.{u}) : Prop where
  tail : ∃ μ : Cardinal.{u}, ∀ κ : Cardinal.{u}, μ ≤ κ → Categorical K κ

end
end AEC
