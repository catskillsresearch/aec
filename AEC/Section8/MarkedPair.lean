module

public import AEC.Section8.StationaryPrescription
public import AEC.Section7.AllDominated

@[expose] public section

namespace AEC
section

universe u

/-- **Definition 8.1.** An object of the marked scheme `C_b` at level `μ` is a triple `(X, Y, b)`
with `b` realizing the prescribed type and `Y` all-dominated over `X + b`. -/
structure MarkedPair (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (W : WorkingScheme K S) (P : StationaryPrescription K S W) where
  μ : Cardinal.{u}
  hμ : μ ∈ W.eligible
  X : W.Object μ hμ
  Y : W.Object μ hμ
  incl : SystemArrow K S (W.asSystem hμ X) (W.asSystem hμ Y)
  incl_arrow : W.permitted (X := X) (Y := Y) incl
  bIdx : Type u
  b : bIdx → Occurrence K S (W.asSystem hμ Y)
  /-- The realizing identification of the mark's list positions with the prescribed tuple's
  coordinates, kept as data (cycle 97 ruling) so that marks of different pairs can be matched by
  position. -/
  realEq : bIdx ≃ (P.assign hμ X).idx
  realizes : SameGaloisType (asTuple incl incl_arrow b) (P.assign hμ X) realEq (Equiv.refl _)
  dominated : AllDominated incl incl_arrow bIdx b

/-- An arrow of marked pairs is a commuting pair of arrows carrying the mark to the mark.
English (Definition 8.1): "An arrow is a commuting pair of componentwise strong embeddings taking
the mark to the mark." The mark is a tuple, so the arrow carries it entrywise: `markMap` matches
the list positions (cycle 95; it was setwise `∀ i, ∃ j`, which is weaker than the English when
mark values repeat). -/
structure MarkedArrow (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (W : WorkingScheme K S) (P : StationaryPrescription K S W)
    (M N : MarkedPair K S W P) where
  onX : SystemArrow K S (W.asSystem M.hμ M.X) (W.asSystem N.hμ N.X)
  onY : SystemArrow K S (W.asSystem M.hμ M.Y) (W.asSystem N.hμ N.Y)
  onX_arrow : W.permitted (X := M.X) (Y := N.X) onX
  onY_arrow : W.permitted (X := M.Y) (Y := N.Y) onY
  comm : SystemArrow.comp M.incl onY = SystemArrow.comp onX N.incl
  markMap : M.bIdx ≃ N.bIdx
  preserves_mark : ∀ i,
    (⟨(M.b i).1, onY.onVertex (M.b i).1 (M.b i).2⟩ :
      Occurrence K S (W.asSystem N.hμ N.Y)) = N.b (markMap i)

end
end AEC
