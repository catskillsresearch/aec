module

public import AEC.Section1.AbstractElementaryClass

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- `K` has no maximal model: every model is the source of a non-surjective strong map. -/
class NoMaximalModel (K : AbstractElementaryClass.{u}) : Prop where
  extends_strictly : ∀ M : Model K.τ, K.Mem M →
    ∃ N : Model K.τ, ∃ f : Language.Embedding K.τ M.carrier N.carrier,
      K.Mem N ∧ K.Strong f ∧ ¬ Function.Surjective f

end
end AEC
