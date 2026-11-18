module

public import AEC.Section11.JointFreshness

@[expose] public section

/-!
# Re-piecing a geometric system (statement audit helper)

`GeometricSystem.repiece Y P` keeps every vertex, map and independence predicate of `Y` and
replaces the pieces by `P`. The identity is an arrow `Y.repiece P → Y` when `P ⊆ Y.piece`, and
an arrow `f : X → Y` factors through `Y.repiece (f '' X.piece)` with no complementary pieces.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}} {n : ℕ} {L : Set (Finset (Fin n))}

/-- `Y` with its pieces replaced by `P`. -/
def GeometricSystem.repiece (Y : GeometricSystem K n L)
    (P : ∀ s, s ∈ L → Set (Y.vertex s).carrier) : GeometricSystem K n L where
  admissible := Y.admissible
  level := Y.level
  vertex := Y.vertex
  inK := Y.inK
  le := Y.le
  le_strong := Y.le_strong
  le_refl := Y.le_refl
  le_trans := Y.le_trans
  indep := Y.indep
  inP t := {x | InClosure (Y.indep t)
    {y | ∃ s, ∃ hs : s ∈ L, ∃ hst : s ⊆ t, ∃ z, z ∈ P s hs ∧ Y.le hst z = y} x}
  piece := P
  pieceRank s hs := #(P s hs)
  piece_card _ _ := rfl
  span _ := rfl

/-- `f : X → Y` as an arrow into `Y` re-pieced by the image of `X`'s pieces. -/
def GeometricArrow.toRepiece {X Y : GeometricSystem K n L} (f : GeometricArrow K X Y) :
    GeometricArrow K X (Y.repiece fun s hs => f.onVertex s '' X.piece s hs) where
  onVertex := f.onVertex
  onVertex_strong := f.onVertex_strong
  comm := f.comm
  extends_piece _ _ := subset_rfl
  indep_image := f.indep_image

/-- The identity from a re-piecing with smaller pieces. -/
def GeometricSystem.repieceOut (Y : GeometricSystem K n L)
    (P : ∀ s, s ∈ L → Set (Y.vertex s).carrier) (hP : ∀ s hs, P s hs ⊆ Y.piece s hs) :
    GeometricArrow K (Y.repiece P) Y where
  onVertex t := Language.Embedding.refl K.τ (Y.vertex t).carrier
  onVertex_strong t := K.strong_refl _ (Y.inK t)
  comm _ := by ext; rfl
  extends_piece s hs := by
    rintro _ ⟨z, hz, rfl⟩
    exact hP s hs hz
  indep_image t S := iff_of_eq (congrArg (Y.indep t) (Set.image_id S).symm)

end
end AEC
