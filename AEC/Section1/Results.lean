module

public import AEC.Section1.UniformThreshold
public import AEC.Section1.CategoricalTail
public import AEC.Section1.UnboundedCategoricity

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open Cardinal

/-- **Theorem 1.2** (Uniform eventual categoricity). For every infinite cardinal `lam` there is
a cardinal `μ(lam) ≥ lam` such that, for every AEC `K` with `LS(K) ≤ lam`, categoricity at
one cardinal `≥ μ(lam)` implies categoricity at every cardinal `≥ μ(lam)`. -/
theorem theorem_1_2 : ∃ μ : Cardinal.{u} → Cardinal.{u}, IsUniformThreshold μ := by
  sorry

/-- **Theorem 1.3** (The qualitative form). An AEC categorical in unboundedly many cardinals
is categorical on a tail of the cardinals. -/
theorem theorem_1_3 (K : AbstractElementaryClass.{u}) :
    CategoricalUnbounded K → CategoricalOnTail K := by
  sorry

end
end AEC
