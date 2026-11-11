module

public import AEC.Section4.PlacedTesting
public import AEC.Section6.TestingFunction

@[expose] public section

/-!
# Uniform testing for natural layouts (Proposition 6.3)

English Proposition 6.3 supplies a monotone testing bound for placed comparisons over a
fixed natural layout by the ordinal-vector argument of Proposition 4.8. With
`NaturalParameterLayout` still a descriptor skeleton (no placement data), the Lean form
packages the whole-object `PlacedTester` of `exists_placedTester` as a `TestingFunction`
tagged by the layout.
-/

namespace AEC
section

universe u

open Cardinal

/-- **Proposition 6.3** (data). A testing function for `layout` whose underlying bound is a
`PlacedTester` for the whole-object presentation `E`. -/
theorem exists_layoutTestingFunction (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (D : StableDiagram K)
    (layout : NaturalParameterLayout.{u}) :
    ∃ g : TestingFunction layout,
      (∀ σ, aleph0 ≤ g.g σ) ∧ PlacedTester K E D g.g := by
  obtain ⟨g0, hmono, hinf, htest⟩ := exists_placedTester E D
  let g : TestingFunction layout :=
    { g := fun σ => max σ (g0 σ)
      mono := fun {_ _} h => max_le_max h (hmono _ _ h)
      ge_self := fun σ => le_max_left _ _ }
  refine ⟨g, fun σ => (hinf σ).trans (le_max_right _ _), ?_⟩
  exact PlacedTester.mono htest fun σ => le_max_right _ _

end
end AEC
