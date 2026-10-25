module

public import AEC.Section1.LoewenheimSkolem
public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- A function `μ` is a uniform eventual-categoricity threshold when, for every infinite
`lam` and every AEC with `LS(K) ≤ lam`, categoricity at one cardinal `≥ μ(lam)` implies
categoricity at every cardinal `≥ μ(lam)`. This is the property asserted by Theorem 1.2. -/
class IsUniformThreshold (μ : Cardinal.{u} → Cardinal.{u}) : Prop where
  threshold : ∀ lam : Cardinal.{u}, aleph0 ≤ lam → lam ≤ μ lam ∧
    ∀ K : AbstractElementaryClass.{u}, isLSBound K lam →
      (∃ κ : Cardinal.{u}, μ lam ≤ κ ∧ Categorical K κ) →
        ∀ κ' : Cardinal.{u}, μ lam ≤ κ' → Categorical K κ'

end
end AEC
