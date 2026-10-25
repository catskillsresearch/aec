module

public import AEC.Section1.Model

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A countable fragment of an infinitary extension of `τ`, as used for sentences of
`L_{ω₁,ω}`. Formulas are indexed by finite free-variable arity. Mathlib's finitary
`Formula` is not used: `L_{ω₁,ω}` allows countable conjunctions and disjunctions. -/
structure InfinitaryFragment (τ : Tau.{u}) where
  Formula : ℕ → Type u
  countable : ∀ n, Countable (Formula n)
  realize : ∀ {n} {M : Type u} [τ.Structure M], Formula n → (Fin n → M) → Prop

end
end AEC
