module

public import AEC.Section1.AbstractElementaryClass

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A strong map is an isomorphism onto a strong substructure of its codomain.
Here that is a `τ`-embedding `f` with `K.Strong f`. -/
abbrev StrongMap (K : AbstractElementaryClass.{u}) (M N : Model K.τ) :=
  {f : Language.Embedding K.τ M.carrier N.carrier // K.Strong f}

end
end AEC
