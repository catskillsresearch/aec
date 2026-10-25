module

public import AEC.Section1.AbstractElementaryClass

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- `K` has arbitrarily large models: above every cardinal there is a larger model. -/
class ArbitrarilyLarge (K : AbstractElementaryClass.{u}) : Prop where
  large : ∀ κ : Cardinal.{u}, ∃ M : Model K.τ, K.Mem M ∧ κ ≤ Model.card M

end
end AEC
