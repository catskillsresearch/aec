module

public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- The categoricity spectrum of `K` is the class of cardinals in which `K` is categorical. -/
def categoricitySpectrum (K : AbstractElementaryClass.{u}) : Set Cardinal.{u} :=
  {κ | Categorical K κ}

/-- The spectrum is bounded when only boundedly many cardinals lie in it. -/
class SpectrumBounded (K : AbstractElementaryClass.{u}) : Prop where
  bound : ∃ κ : Cardinal.{u}, ∀ μ ∈ categoricitySpectrum K, μ ≤ κ

end
end AEC
