module

public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

/-- The fixed menu of assertions a descriptor may request. Proposition 13.1. -/
inductive AdequacyItem
  | presentation
  | orbit
  | chainUnion
  | rootPrescription
  | boundary
  | geometric
  | naturalLayout

/-- A descriptor records which menu items it requires. -/
structure SchemeDescriptor where
  items : List AdequacyItem

/-- The single formula $\mathrm{Adeq}(d, \mu)$: the cardinal meets every assertion the descriptor
requests. The interpretation of each menu item is supplied with the descriptor. -/
structure Adequacy where
  holds : AdequacyItem → Cardinal.{u} → Prop

def Adeq (A : Adequacy) (d : SchemeDescriptor) (μ : Cardinal.{u}) : Prop :=
  ∀ item ∈ d.items, A.holds item μ

end
end AEC
