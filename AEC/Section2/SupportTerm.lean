module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Fin.Basic

@[expose] public section

namespace AEC
section

universe u

/-- A term in an order presentation: one label of positive finite arity, applied to a
strictly increasing finite list of positions from the index order. -/
structure SupportTerm (lab : Type u) (arity : lab → ℕ) (I : Type u) [LinearOrder I] where
  label : lab
  pos : Fin (arity label) → I
  increasing : StrictMono pos

end
end AEC
