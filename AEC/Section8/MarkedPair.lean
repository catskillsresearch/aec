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
  realizes : ∃ e : bIdx ≃ (P.assign hμ X).idx,
    SameGaloisType (asTuple incl incl_arrow b) (P.assign hμ X) e (Equiv.refl _)
  dominated : AllDominated incl incl_arrow bIdx b

/-- An arrow of marked pairs is a commuting pair of arrows carrying the mark to the mark. -/
structure MarkedArrow (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (W : WorkingScheme K S) (P : StationaryPrescription K S W)
    (M N : MarkedPair K S W P) where
  onX : SystemArrow K S (W.asSystem M.hμ M.X) (W.asSystem N.hμ N.X)
  onY : SystemArrow K S (W.asSystem M.hμ M.Y) (W.asSystem N.hμ N.Y)
  onX_arrow : W.permitted (X := M.X) (Y := N.X) onX
  onY_arrow : W.permitted (X := M.Y) (Y := N.Y) onY
  comm : SystemArrow.comp M.incl onY = SystemArrow.comp onX N.incl
  preserves_mark : ∀ i,
    ∃ j, (⟨(M.b i).1, onY.onVertex (M.b i).1 (M.b i).2⟩ :
      Occurrence K S (W.asSystem N.hμ N.Y)) = N.b j

end
end AEC
