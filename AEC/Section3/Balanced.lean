module

public import AEC.Section3.InteriorNonprincipal
public import AEC.Section3.OrderCharacter

@[expose] public section

namespace AEC
section

universe u


open Cardinal

/-- A cut is balanced when its two characters agree: `cf(L⁻) = ci(L⁺)`. -/
class Cut.IsBalanced {α : Type u} [LinearOrder α] (c : Cut α) : Prop where
  characters : setCofinality c.lower = setCoinitiality c.upper

end
end AEC
