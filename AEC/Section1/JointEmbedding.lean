module

public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- Joint embedding: any two models of `K` embed strongly into a common model. -/
class HasJointEmbedding (K : AbstractElementaryClass.{u}) : Prop where
  common : ∀ M N : Model K.τ, K.Mem M → K.Mem N →
    ∃ P : Model K.τ, ∃ f : Language.Embedding K.τ M.carrier P.carrier,
      ∃ g : Language.Embedding K.τ N.carrier P.carrier,
        K.Mem P ∧ K.Strong f ∧ K.Strong g

end
end AEC
