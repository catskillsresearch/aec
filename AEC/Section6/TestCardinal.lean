module

public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- Equation (1). For a testing function `g` and the fixed label bound `b`,
`c(σ, τ) = 2^{g(σ) + b + σ + τ}`. -/
noncomputable def testPair (b : Cardinal.{u}) (g : Cardinal.{u} → Cardinal.{u})
    (σ τ : Cardinal.{u}) : Cardinal.{u} :=
  (2 : Cardinal.{u}) ^ (g σ + b + σ + τ)

/-- `c(σ) = c(σ, ℵ₀)`. -/
noncomputable def testCardinal (b : Cardinal.{u}) (g : Cardinal.{u} → Cardinal.{u})
    (σ : Cardinal.{u}) : Cardinal.{u} :=
  testPair b g σ aleph0

end
end AEC
