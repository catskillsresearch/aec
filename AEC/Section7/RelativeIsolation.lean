module

public import AEC.Section6.ApproximationSequence

@[expose] public section

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}

/-- Reindex a joint list along an identification of the tuple coordinates. -/
def alignJoint {idx idx' ι : Type u} {X : SystemObject K S} (e : idx ≃ idx')
    (xs : idx ⊕ ι → Occurrence K S X) : idx' ⊕ ι → Occurrence K S X
  | Sum.inl i => xs (Sum.inl (e.symm i))
  | Sum.inr j => xs (Sum.inr j)

/-- The marginal of a concatenated tuple on the first summand. -/
def TupleOver.marginal {uIdx cIdx : Type u} (q : TupleOver K S W hμ base)
    (e : q.idx ≃ uIdx ⊕ cIdx) : TupleOver K S W hμ base where
  ν := q.ν
  hν := q.hν
  host := q.host
  incl := q.incl
  incl_arrow := q.incl_arrow
  idx := uIdx
  val i := q.val (e.symm (Sum.inl i))

/-- **Definition 7.1.** `q = tp(u, c/A)` is isolated relative to `u` when some bounded
`Z ⊆ A` isolates it: any `q'` with the same marginal on `u` and the same diagram over `Z`
equals `q`. The set `Z` is an isolating fragment. -/
def IsRelativelyIsolated (q : TupleOver K S W hμ base) {uIdx cIdx : Type u}
    (e : q.idx ≃ uIdx ⊕ cIdx) : Prop :=
  ∃ (ι : Type u) (Z : ι → Occurrence K S (W.asSystem hμ base)),
    #ι < μ ∧
    ∀ (q' : TupleOver K S W hμ base) (e' : q'.idx ≃ uIdx ⊕ cIdx),
      SameGaloisType (q.marginal e) (q'.marginal e') (Equiv.refl uIdx) (Equiv.refl uIdx) →
      W.DiagramEq (X := q.host) (Y := q'.host)
        (alignJoint e (typeJoint (p := q) Z)) (alignJoint e' (typeJoint (p := q') Z)) →
      SameGaloisType q q' e e'

/-- A parameter enumeration witnessing relative isolation. -/
def IsIsolatingFragment (q : TupleOver K S W hμ base) {uIdx cIdx : Type u}
    (e : q.idx ≃ uIdx ⊕ cIdx) {ι : Type u}
    (Z : ι → Occurrence K S (W.asSystem hμ base)) : Prop :=
  #ι < μ ∧
    ∀ (q' : TupleOver K S W hμ base) (e' : q'.idx ≃ uIdx ⊕ cIdx),
      SameGaloisType (q.marginal e) (q'.marginal e') (Equiv.refl uIdx) (Equiv.refl uIdx) →
      W.DiagramEq (X := q.host) (Y := q'.host)
        (alignJoint e (typeJoint (p := q) Z)) (alignJoint e' (typeJoint (p := q') Z)) →
      SameGaloisType q q' e e'

end
end AEC
