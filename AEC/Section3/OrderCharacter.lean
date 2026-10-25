module

public import AEC.Section3.Cut
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- The cofinality of a subset: the least cardinality of a cofinal subset. -/
noncomputable def setCofinality {α : Type u} [LinearOrder α] (s : Set α) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | ∃ t : Set α, t ⊆ s ∧ #t = κ ∧ ∀ x ∈ s, ∃ y ∈ t, x ≤ y}

/-- The coinitiality of a subset: the cofinality of the reversed order. -/
noncomputable def setCoinitiality {α : Type u} [LinearOrder α] (s : Set α) : Cardinal.{u} :=
  setCofinality (α := αᵒᵈ) (OrderDual.toDual '' s)

/-- The two characters of a cut are `cf(L⁻)` and `ci(L⁺)`. -/
noncomputable def Cut.characters {α : Type u} [LinearOrder α] (c : Cut α) :
    Cardinal.{u} × Cardinal.{u} :=
  (setCofinality c.lower, setCoinitiality c.upper)

end
end AEC
