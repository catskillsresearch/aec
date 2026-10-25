module

public import AEC.Section2.SupportTerm
public import AEC.Section3.Cut

@[expose] public section

namespace AEC
section

universe u

/-- A presentation record of a tuple in an order presentation, as in Section 3.2.
It retains the labels, the order and equality diagram of the flattened argument
positions, and the occupancy of every cut of those positions. -/
structure PresentationRecord (lab : Type u) (arity : lab → ℕ) (flat : Type u)
    [LinearOrder flat] where
  index : Type u
  label : index → lab
  arg : ∀ i, Fin (arity (label i)) → flat
  arg_mono : ∀ i, StrictMono (arg i)
  occupied : Cut flat → Prop

end
end AEC
