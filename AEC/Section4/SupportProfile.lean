module

public import AEC.Section2.SupportTerm

@[expose] public section

namespace AEC
section

universe u

/-- A support profile of a new tuple over a parameter set, as used in Proposition 4.9.
It records the labels of the new tuple, a formal linear order on its support, and the
comparison of each new position with each old supporting position. -/
structure SupportProfile (lab : Type u) (arity : lab → ℕ) (old : Type u) [LinearOrder old] where
  index : Type u
  label : index → lab
  support : Type u
  supportOrder : LinearOrder support
  arg : ∀ i, Fin (arity (label i)) → support
  arg_mono : ∀ i, haveI := supportOrder; StrictMono (arg i)
  compare : support → old → Ordering

end
end AEC
