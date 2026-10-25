module

public import AEC.Section6.TupleOver

@[expose] public section

namespace AEC
section

universe u

/-- An amalgam of two arrows out of one base. **Theorem 6.6** says that at sufficiently closed
levels such an amalgam identifying two bounded tuples exists exactly when their `D`-diagrams
agree on all parameter queries of size at most `g` of the tuple length. -/
structure SchemeAmalgam (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (W : WorkingScheme K S) where
  μ : Cardinal.{u}
  hμ : μ ∈ W.eligible
  base : W.Object μ hμ
  left : W.Object μ hμ
  right : W.Object μ hμ
  top : W.Object μ hμ
  toLeft : SystemArrow K S (W.asSystem hμ base) (W.asSystem hμ left)
  toRight : SystemArrow K S (W.asSystem hμ base) (W.asSystem hμ right)
  fromLeft : SystemArrow K S (W.asSystem hμ left) (W.asSystem hμ top)
  fromRight : SystemArrow K S (W.asSystem hμ right) (W.asSystem hμ top)
  toLeft_arrow : W.permitted (X := base) (Y := left) toLeft
  toRight_arrow : W.permitted (X := base) (Y := right) toRight
  fromLeft_arrow : W.permitted (X := left) (Y := top) fromLeft
  fromRight_arrow : W.permitted (X := right) (Y := top) fromRight
  comm : ∀ v, (fromLeft.onVertex v).comp (toLeft.onVertex v) =
    (fromRight.onVertex v).comp (toRight.onVertex v)

/-- The amalgam identifies two equally indexed tuples. -/
def SchemeAmalgam.Identifies {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    {W : WorkingScheme K S} (A : SchemeAmalgam K S W) {idx : Type u}
    (v0 : idx → Occurrence K S (W.asSystem A.hμ A.left))
    (v1 : idx → Occurrence K S (W.asSystem A.hμ A.right)) : Prop :=
  ∀ i,
    (⟨(v0 i).1, A.fromLeft.onVertex (v0 i).1 (v0 i).2⟩ :
      Occurrence K S (W.asSystem A.hμ A.top)) =
    ⟨(v1 i).1, A.fromRight.onVertex (v1 i).1 (v1 i).2⟩

end
end AEC
