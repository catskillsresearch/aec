module

public import AEC.Section6.NaturalParameterLayout
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- **Proposition 6.3.** A testing function for one fixed natural layout: a monotone cardinal
function `g` with `g(σ) ≥ σ`. Two placed comparisons of tuples of length at most `σ` agree if
and only if they agree on parameter queries of size at most `g(σ)`. -/
structure TestingFunction (_layout : NaturalParameterLayout.{u}) where
  g : Cardinal.{u} → Cardinal.{u}
  mono : ∀ ⦃σ τ : Cardinal.{u}⦄, σ ≤ τ → g σ ≤ g τ
  ge_self : ∀ σ : Cardinal.{u}, σ ≤ g σ

end
end AEC
