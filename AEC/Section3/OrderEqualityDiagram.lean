module

public import Mathlib.Order.Basic

@[expose] public section

namespace AEC
section

universe u


/-- Two indexed sequences have the same order/equality diagram when equality and
strict order agree on every pair of indices. -/
def SameOrderDiagram {ι α β : Type u} [LinearOrder α] [LinearOrder β]
    (xs : ι → α) (ys : ι → β) : Prop :=
  (∀ i j, xs i = xs j ↔ ys i = ys j) ∧ (∀ i j, xs i < xs j ↔ ys i < ys j)

end
end AEC
