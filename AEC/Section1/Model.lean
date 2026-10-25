module

public import AEC.Section1.Language

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- A `τ`-structure. The paper writes `|M|` for the universe of `M`. -/
structure Model (τ : Tau.{u}) where
  carrier : Type u
  str : τ.Structure carrier

instance (τ : Tau.{u}) (M : Model τ) : τ.Structure M.carrier := M.str

namespace Model

variable {τ : Tau.{u}}

/-- The universe `|M|`. -/
def underlying (M : Model τ) : Type u := M.carrier

/-- The cardinality `‖M‖`. -/
def card (M : Model τ) : Cardinal.{u} := #M.carrier

end Model

end
end AEC
