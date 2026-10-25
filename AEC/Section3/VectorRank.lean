module

public import AEC.Section3.FiniteSupportOrder

@[expose] public section

namespace AEC
section

universe u

open Finsupp

/-- The rank of a nonzero finite-support vector: its greatest support coordinate. -/
noncomputable def vectorRank {δ : _root_.Ordinal.{u}} (f : Gamma δ) (hf : ofColex f ≠ 0) :
    OrdIndex δ :=
  (ofColex f).support.max' (by
    rw [support_nonempty_iff]
    exact hf)

end
end AEC
