module

public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace AEC
section

universe u

/-- `x` independently extends `S` when it lies outside `S` and `S ∪ {x}` is independent. -/
def IndependentlyExtends {α : Type u} (indep : Set α → Prop) (x : α) (S : Set α) : Prop :=
  x ∉ S ∧ indep (insert x S)

/-- `S` is a maximal independent subset of `F`. -/
def MaximallyIndependent {α : Type u} (indep : Set α → Prop) (F S : Set α) : Prop :=
  S ⊆ F ∧ indep S ∧ ∀ y ∈ F, ¬ IndependentlyExtends indep y S

/-- **Theorem 10.5.** For finite `F`, `x ∈ cl(F)` when `x` does not independently extend some
maximal independent subset of `F`. -/
def InFiniteClosure {α : Type u} (indep : Set α → Prop) (F : Set α) (x : α) : Prop :=
  ∃ S : Set α, MaximallyIndependent indep F S ∧ ¬ IndependentlyExtends indep x S

/-- Closure of an arbitrary set is the union of the closures of its finite subsets. -/
def InClosure {α : Type u} (indep : Set α → Prop) (A : Set α) (x : α) : Prop :=
  ∃ F : Set α, F ⊆ A ∧ F.Finite ∧ InFiniteClosure indep F x

end
end AEC
