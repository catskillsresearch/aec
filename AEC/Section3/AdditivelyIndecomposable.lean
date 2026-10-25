module

public import Mathlib.SetTheory.Ordinal.Principal

@[expose] public section

namespace AEC
section

universe u


/-- An ordinal is additively indecomposable when it is principal for addition.
The paper uses this for the ordinals `δ` in Lemmas 3.8 and 3.10. -/
class AdditivelyIndecomposable (δ : _root_.Ordinal.{u}) : Prop where
  principal : _root_.Ordinal.IsPrincipal (· + ·) δ

end
end AEC
