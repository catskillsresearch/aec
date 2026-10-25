module

public import AEC.Section5.WorkingScheme

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- **Corollary 6.16.** Arrows `rᵢ : B → A`, indexed by the level, such that each `a ∈ A` is
fixed for all but finitely many indices. The maps are not required to fix all of `A` at once. -/
structure ApproximateRetraction (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (W : WorkingScheme K S) {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible)
    (A B : W.Object μ hμ)
    (incl : SystemArrow K S (W.asSystem hμ A) (W.asSystem hμ B)) where
  index : Type u
  index_card : #index = μ
  retr : index → SystemArrow K S (W.asSystem hμ B) (W.asSystem hμ A)
  retr_arrow : ∀ i, W.permitted (X := B) (Y := A) (retr i)
  almost_id : ∀ a : Occurrence K S (W.asSystem hμ A),
    Finite {i : index //
      (retr i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2}

end
end AEC
