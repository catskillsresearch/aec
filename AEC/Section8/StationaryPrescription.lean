module

public import AEC.Section6.FreeExtension

@[expose] public section

namespace AEC
section

universe u

/-- **Definition 8.1.** A stationary finite prescription assigns to every object the type of one
finite tuple, so that the assignment along any arrow, including a mixed-level arrow, is the free
extension. -/
structure StationaryPrescription (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (W : WorkingScheme K S) where
  n : ℕ
  assign : ∀ {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (X : W.Object μ hμ),
    TupleOver K S W hμ X
  arity : ∀ {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (X : W.Object μ hμ),
    (assign hμ X).idx ≃ Fin n
  along : ∀ {μ ν : Cardinal.{u}} {hμ : μ ∈ W.eligible} {hν : ν ∈ W.eligible}
    {X : W.Object μ hμ} {Y : W.Object ν hν}
    (f : SystemArrow K S (W.asSystem hμ X) (W.asSystem hν Y))
    (hf : W.permitted (X := X) (Y := Y) f),
    ∃ e : (assign hμ X).idx ≃ (assign hν Y).idx,
      IsFreeLift (assign hμ X) (assign hν Y) f hf e

end
end AEC
