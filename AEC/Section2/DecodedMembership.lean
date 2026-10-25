module

public import AEC.Section2.CodedPresentation

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- Membership recovered from a small code: `M` is isomorphic to a direct limit of a
nonempty directed family of allowed small models whose transition pairs are allowed. -/
def DecodedMem {τ : Tau.{u}} {lam : Cardinal.{u}} (c : SmallCode τ lam) (M : Model τ) : Prop :=
  ∃ P : CodedPresentation c, ∃ U : DirectLimit P.system,
    Nonempty (U.obj.carrier ≃[τ] M.carrier)

end
end AEC
