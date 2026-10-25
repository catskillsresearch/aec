module

public import AEC.Section2.CodedInclusion

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- The strong relation recovered from a small code. `f : M → N` is decoded-strong when
it is the direct-limit map of a directed subfamily, up to the identifications of the
two limits with `M` and `N`. -/
def DecodedStrong {τ : Tau.{u}} {lam : Cardinal.{u}} (c : SmallCode τ lam)
    {M N : Model τ} (f : Language.Embedding τ M.carrier N.carrier) : Prop :=
  ∃ I : CodedInclusion c,
    ∃ eM : I.smallLimit.obj.carrier ≃[τ] M.carrier,
      ∃ eN : I.bigLimit.obj.carrier ≃[τ] N.carrier,
        eN.toEmbedding.comp I.induced = f.comp eM.toEmbedding

end
end AEC
