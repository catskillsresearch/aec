module

public import AEC.Section7.RelativeIsolation

@[expose] public section

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible}

/-- View a list of occurrences in `Y` as a tuple over `X` along an arrow `X → Y`. -/
def asTuple {X Y : W.Object μ hμ}
    (incl : SystemArrow K S (W.asSystem hμ X) (W.asSystem hμ Y))
    (hincl : W.permitted (X := X) (Y := Y) incl) {idx : Type u}
    (val : idx → Occurrence K S (W.asSystem hμ Y)) : TupleOver K S W hμ X where
  ν := μ
  hν := hμ
  host := Y
  incl := incl
  incl_arrow := hincl
  idx := idx
  val := val

/-- **Definition 7.4.** `Y` is all-dominated over `X + b` when, for every bounded tuple `c`
from `Y`, `tp(b, c/X)` is isolated relative to `b`. -/
def AllDominated {X Y : W.Object μ hμ}
    (incl : SystemArrow K S (W.asSystem hμ X) (W.asSystem hμ Y))
    (hincl : W.permitted (X := X) (Y := Y) incl) (bIdx : Type u)
    (b : bIdx → Occurrence K S (W.asSystem hμ Y)) : Prop :=
  ∀ (cIdx : Type u) (c : cIdx → Occurrence K S (W.asSystem hμ Y)),
    #cIdx < μ →
    IsRelativelyIsolated (uIdx := bIdx) (cIdx := cIdx)
      (asTuple incl hincl (seqJoint b c)) (Equiv.refl (bIdx ⊕ cIdx))

end
end AEC
