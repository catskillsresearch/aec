module

public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- Categoricity in unboundedly many cardinals: above every cardinal there is a
larger categoricity cardinal. -/
class CategoricalUnbounded (K : AbstractElementaryClass.{u}) : Prop where
  unbounded : ∀ κ : Cardinal.{u}, ∃ μ : Cardinal.{u}, κ ≤ μ ∧ Categorical K μ

end
end AEC
