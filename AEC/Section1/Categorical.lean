module

public import AEC.Section1.Model
public import AEC.Section1.AbstractElementaryClass

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- `K` is categorical in `κ` when it has a model of cardinality `κ` and any two
models of that cardinality are isomorphic. -/
class Categorical (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u}) : Prop where
  exists_model : ∃ M : Model K.τ, K.Mem M ∧ Model.card M = κ
  unique_model : ∀ M N : Model K.τ, K.Mem M → K.Mem N →
    Model.card M = κ → Model.card N = κ → Nonempty (M.carrier ≃[K.τ] N.carrier)

end
end AEC
