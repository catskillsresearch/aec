module

public import AEC.Section10.MinimalData

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- **Proposition 10.6.** A pointed model is a model with a distinguished strong copy of `M₀`
whose enumeration has the fixed diagram `Δ`. -/
structure PointedModel (K : AbstractElementaryClass.{u}) (D : MinimalData K) where
  M : Model K.τ
  copy : Language.Embedding K.τ D.M0.carrier M.carrier
  copy_strong : K.Strong copy
  hasDiagram : D.Delta M copy

end
end AEC
