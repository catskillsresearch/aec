module

public import AEC.Section11.GeometricSystem

@[expose] public section

namespace AEC
section

universe u

/-- A coordinate in a designated vertex. -/
structure Coordinate {K : AbstractElementaryClass.{u}} {n : ℕ} {L : Set (Finset (Fin n))}
    (Y : GeometricSystem K n L) where
  label : Finset (Fin n)
  active : label ∈ L
  val : (Y.vertex label).carrier

/-- **Definition 11.8.** A list of coordinates is jointly fresh over `X` when it is a sublist of
the complementary pieces of some extension of the pieces of `X`. The sets `C_s` are those
complementary pieces. -/
def JointlyFresh {K : AbstractElementaryClass.{u}} {n : ℕ} {L : Set (Finset (Fin n))}
    {X Y : GeometricSystem K n L} (f : GeometricArrow K X Y)
    (coords : List (Coordinate Y)) : Prop :=
  ∃ extra : ∀ s (_hs : s ∈ L), Set (Y.vertex s).carrier,
    (∀ s hs, Disjoint (f.onVertex s '' X.piece s hs) (extra s hs)) ∧
    (∀ s hs, f.onVertex s '' X.piece s hs ∪ extra s hs = Y.piece s hs) ∧
    ∀ c ∈ coords, c.val ∈ extra c.label c.active

end
end AEC
