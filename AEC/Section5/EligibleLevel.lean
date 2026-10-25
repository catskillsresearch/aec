module

public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

namespace AEC
section

universe u


open Cardinal

/-- An eligible level is an infinite cardinal at which the construction under
consideration has been established. The working levels used after the preliminary
arguments are strong limits of countable cofinality. -/
class IsWorkingLevel (μ : Cardinal.{u}) : Prop where
  infinite : aleph0 ≤ μ
  strongLimit : μ.IsStrongLimit
  countableCof : Ordinal.cof μ.ord = aleph0

/-- A class of eligible levels: a class of infinite cardinals. -/
class Eligible (S : Set Cardinal.{u}) : Prop where
  infinite : ∀ μ ∈ S, aleph0 ≤ μ

end
end AEC
