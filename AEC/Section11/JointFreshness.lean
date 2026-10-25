module

public import AEC.Section11.GeometricSystem

@[expose] public section

namespace AEC
section

universe u v

open Cardinal

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

/-- Transport an element along an equality of vertex labels. -/
def castCarrier {K : AbstractElementaryClass.{u}} {n : ℕ} {L : Set (Finset (Fin n))}
    {Y : GeometricSystem K n L} {s t : Finset (Fin n)} (h : s = t)
    (x : (Y.vertex s).carrier) : (Y.vertex t).carrier :=
  (congrArg (fun u => (Y.vertex u).carrier) h) ▸ x

/-- **Definition 11.8** for an index of any cardinality. A `List` is finite, while a bounded
fresh list in the claims may have any size below the level. The entries lie in the
complementary pieces of some extension of the pieces of `X`. -/
def JointlyFreshIndexed {K : AbstractElementaryClass.{u}} {n : ℕ}
    {L : Set (Finset (Fin n))} {X Y : GeometricSystem K n L}
    (f : GeometricArrow K X Y) {ι : Type v} (label : ι → Finset (Fin n))
    (active : ∀ i, label i ∈ L) (val : ∀ i, (Y.vertex (label i)).carrier) : Prop :=
  ∃ extra : ∀ s (_hs : s ∈ L), Set (Y.vertex s).carrier,
    (∀ s hs, Disjoint (f.onVertex s '' X.piece s hs) (extra s hs)) ∧
    (∀ s hs, f.onVertex s '' X.piece s hs ∪ extra s hs = Y.piece s hs) ∧
    ∀ i, val i ∈ extra (label i) (active i)

/-- The indexed coordinates are exactly the complementary pieces of `X → Y`. -/
def EnumeratesComplements {K : AbstractElementaryClass.{u}} {n : ℕ}
    {L : Set (Finset (Fin n))} {X Y : GeometricSystem K n L}
    (f : GeometricArrow K X Y) {ι : Type v} (label : ι → Finset (Fin n))
    (active : ∀ i, label i ∈ L) (val : ∀ i, (Y.vertex (label i)).carrier) : Prop :=
  ∃ extra : ∀ s (_hs : s ∈ L), Set (Y.vertex s).carrier,
    (∀ s hs, Disjoint (f.onVertex s '' X.piece s hs) (extra s hs)) ∧
    (∀ s hs, f.onVertex s '' X.piece s hs ∪ extra s hs = Y.piece s hs) ∧
    (∀ i, val i ∈ extra (label i) (active i)) ∧
    ∀ s hs (x : (Y.vertex s).carrier), x ∈ extra s hs →
      ∃ i, ∃ h : label i = s, x = castCarrier h (val i)

/-- `X → Y` factors as `X → U → Y`. -/
def FactorsThrough {K : AbstractElementaryClass.{u}} {n : ℕ} {L : Set (Finset (Fin n))}
    {X Y U : GeometricSystem K n L} (f : GeometricArrow K X Y)
    (xu : GeometricArrow K X U) (uy : GeometricArrow K U Y) : Prop :=
  ∀ t, (uy.onVertex t).comp (xu.onVertex t) = f.onVertex t

/-- Each entry of `d` lies in the image of `U → Y`. -/
def CoordinatesInImage {K : AbstractElementaryClass.{u}} {n : ℕ} {L : Set (Finset (Fin n))}
    {U Y : GeometricSystem K n L} (h : GeometricArrow K U Y) {ι : Type u}
    (d : ι → Σ t : Finset (Fin n), (Y.vertex t).carrier) : Prop :=
  ∀ i, ∃ x : (U.vertex (d i).1).carrier, h.onVertex (d i).1 x = (d i).2

/-- `extra` is a complementary-piece partition of the active pieces of `Y` over `X`. -/
def IsPieceExtension {K : AbstractElementaryClass.{u}} {n : ℕ} {L : Set (Finset (Fin n))}
    {X Y : GeometricSystem K n L} (f : GeometricArrow K X Y)
    (extra : ∀ s, s ∈ L → Set (Y.vertex s).carrier) : Prop :=
  ∀ s (hs : s ∈ L),
    Disjoint (f.onVertex s '' X.piece s hs) (extra s hs) ∧
    f.onVertex s '' X.piece s hs ∪ extra s hs = Y.piece s hs

/-- The total number of elements in the complementary pieces. -/
def complementTotal {K : AbstractElementaryClass.{u}} {n : ℕ} {L : Set (Finset (Fin n))}
    {Y : GeometricSystem K n L}
    (extra : ∀ s, s ∈ L → Set (Y.vertex s).carrier) : Cardinal.{u} :=
  Cardinal.lift #(Σ s : {s : Finset (Fin n) // s ∈ L}, ↥(extra s.1 s.2))

/-- Two finite labeled tuples have the same type over `X` when a pair of arrows into a
common system identifies them and commutes with the inclusions of `X`. -/
def SameGeometricType {K : AbstractElementaryClass.{u}} {n : ℕ} {L : Set (Finset (Fin n))}
    {k : ℕ} {X Y0 Y1 : GeometricSystem K n L} (f0 : GeometricArrow K X Y0)
    (f1 : GeometricArrow K X Y1) (labs : Fin k → Finset (Fin n))
    (b0 : ∀ i, (Y0.vertex (labs i)).carrier)
    (b1 : ∀ i, (Y1.vertex (labs i)).carrier) : Prop :=
  ∃ (Z : GeometricSystem K n L) (g0 : GeometricArrow K Y0 Z) (g1 : GeometricArrow K Y1 Z),
    (∀ t, (g0.onVertex t).comp (f0.onVertex t) = (g1.onVertex t).comp (f1.onVertex t)) ∧
    ∀ i, g0.onVertex (labs i) (b0 i) = g1.onVertex (labs i) (b1 i)

end
end AEC
