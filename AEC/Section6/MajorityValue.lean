module

public import AEC.Section6.ApproximationSequence

@[expose] public section

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}
  {p : TupleOver K S W hμ base}

/-- **Definition 6.8.** A diagram is the majority value of an approximation sequence on `Z`
when it disagrees with the sequence on at most `|Z| + ℵ₀` indices. Whenever the index is
longer than that, the value is unique. -/
def IsMajorityValue (A : ApproximationSequence p) {ι : Type u}
    (Z : ι → Occurrence K S (W.asSystem hμ base))
    {ν : Cardinal.{u}} (hν : ν ∈ W.eligible) (repr : W.Object ν hν)
    (xs : p.idx ⊕ ι → Occurrence K S (W.asSystem hν repr)) : Prop :=
  # {i : A.κIndex // ¬ W.DiagramEq (X := base) (Y := repr)
      (seqJoint (A.family i) Z) xs} ≤ #ι + aleph0

end
end AEC
