module

public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u


open Cardinal

/-- A list indexed by `ι` is bounded at a level `μ` when its cardinality is strictly
less than `μ`. -/
def BoundedAt (μ : Cardinal.{u}) (ι : Type u) : Prop :=
  #ι < μ

end
end AEC
