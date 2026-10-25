module

public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- Advance notation of §5.2. For a class `A` of cardinals,
`Lim(A) = {μ : sup(A ∩ μ) = μ > 0}`. -/
def Lim (A : Set Cardinal.{u}) : Set Cardinal.{u} :=
  {μ | sSup (A ∩ Set.Iio μ) = μ ∧ 0 < μ}

end
end AEC
