module

public import AEC.Section6.FreeExtension

@[expose] public section

namespace AEC
section

universe u

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible}

/-- A chain of same-level objects, with maps from a first stage and into a union. -/
structure ContinuousChain (W : WorkingScheme K S) {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) where
  index : Type u
  zero : index
  obj : index → W.Object μ hμ
  fromZero : (i : index) →
    SystemArrow K S (W.asSystem hμ (obj zero)) (W.asSystem hμ (obj i))
  fromZero_arrow : ∀ i, W.permitted (X := obj zero) (Y := obj i) (fromZero i)
  unionObj : W.Object μ hμ
  toUnion : (i : index) →
    SystemArrow K S (W.asSystem hμ (obj i)) (W.asSystem hμ unionObj)
  toUnion_arrow : ∀ i, W.permitted (X := obj i) (Y := unionObj) (toUnion i)

/-- **Definition 7.7.** A bounded marginal type `p` satisfies the continuity condition when,
at a level to which it has been freely lifted, a realization that is free from the first stage
of a chain at every stage is free from that first stage over the union. -/
def SatisfiesContinuity {A : W.Object μ hμ} (p : TupleOver K S W hμ A) : Prop :=
  ∀ (C : ContinuousChain W hμ)
    (f : SystemArrow K S (W.asSystem hμ A) (W.asSystem hμ (C.obj C.zero)))
    (hf : W.permitted (X := A) (Y := C.obj C.zero) f)
    (b : TupleOver K S W hμ C.unionObj),
    (∃ e : p.idx ≃ (b.restrict (C.toUnion C.zero) (C.toUnion_arrow C.zero)).idx,
      IsFreeLift p (b.restrict (C.toUnion C.zero) (C.toUnion_arrow C.zero)) f hf e) →
    (∀ i, IsFreeFrom (C.fromZero i) (C.fromZero_arrow i)
      (b.restrict (C.toUnion i) (C.toUnion_arrow i))) →
    IsFreeFrom (C.toUnion C.zero) (C.toUnion_arrow C.zero) b

end
end AEC
