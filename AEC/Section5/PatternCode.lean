module

public import AEC.Section2.SupportTerm
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- `P_F(σ)`. A pattern of arity at most `σ`: an indexed list of labels, each with a finite
increasing support, on a support universe of cardinality at most `σ`. -/
structure PatternCode (lab : Type u) (arity : lab → ℕ) (σ : Cardinal.{u}) where
  support : Type u
  supportOrder : LinearOrder support
  supportCard : #support ≤ σ
  index : Type u
  indexCard : #index ≤ σ
  term : index → (letI := supportOrder; SupportTerm lab arity support)

end
end AEC
