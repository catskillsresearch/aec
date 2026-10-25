module

public import AEC.Section2.SmallModel

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A small pair `M ⊆ N`: two small ordinal structures and a `τ`-embedding of the
smaller into the larger. The paper records the pair by the large structure together
with the distinguished subset that is the domain of the small one. -/
structure SmallPair (τ : Tau.{u}) (lam : Cardinal.{u}) where
  big : SmallModel τ lam
  small : SmallModel τ lam
  incl : Language.Embedding τ (↥small.domain) (↥big.domain)

end
end AEC
