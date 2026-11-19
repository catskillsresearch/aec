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

/-- **Definition 8.1, "commutes with isomorphisms"** (cycle 95; a hypothesis predicate on the
prescription, not a field). English: "A stationary finite prescription for C assigns to every
object X a type pX of a finite tuple, with specified component sorts. The assignment commutes with
isomorphisms, and, for every arrow X → X′, including an arrow between eligible levels, pX′ is the
free extension of pX, after identifying the base by that arrow." For a structural isomorphism
`e : X ≅ X′` (a vertexwise bijective permitted arrow at one level), `p_{X′}` read back along `e`
has the type of `p_X`, position by position: `p_X` is the type of a finite tuple with specified
component sorts, so the coordinates are matched through `arity` (cycle 96; previously an arbitrary
permutation `κ` of the coordinates was allowed, which is weaker than the English when entries of
the prescribed tuple are interchangeable). -/
def StationaryPrescription.CommutesWithIso {K : AbstractElementaryClass.{u}}
    {S : SystemShape.{u}} {W : WorkingScheme K S} (Pr : StationaryPrescription K S W) : Prop :=
  ∀ {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} (X X' : W.Object μ hμ)
    (e : SystemArrow K S (W.asSystem hμ X) (W.asSystem hμ X'))
    (he : W.permitted (X := X) (Y := X') e),
    (∀ v, Function.Bijective (e.onVertex v)) →
    SameGaloisType (Pr.assign hμ X) ((Pr.assign hμ X').restrict e he)
      ((Pr.arity hμ X).trans (Pr.arity hμ X').symm) (Equiv.refl _)

end
end AEC
