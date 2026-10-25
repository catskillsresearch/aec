module

public import AEC.Section2.CodedPresentation

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A decoded strong inclusion: a coded presentation of the large model, a directed
subfamily presenting the small model, and the direct-limit embedding between them. -/
structure CodedInclusion {τ : Tau.{u}} {lam : Cardinal.{u}} (c : SmallCode τ lam) where
  big : CodedPresentation c
  small : CodedPresentation c
  bigLimit : DirectLimit big.system
  smallLimit : DirectLimit small.system
  embedIndex : small.system.ι → big.system.ι
  embedIndex_rel : ∀ {i j} (_hij : small.system.rel i j),
    big.system.rel (embedIndex i) (embedIndex j)
  /-- The stage embedding of the `i`-th small model into its image in the large system. -/
  stage : ∀ i, Language.Embedding τ (small.system.obj i).carrier
    (big.system.obj (embedIndex i)).carrier
  subpair : ∀ i, ∃ p : SmallPair τ lam, p ∈ c.pair ∧ p.small = small.rep i ∧
    p.big = big.rep (embedIndex i)
  induced : Language.Embedding τ smallLimit.obj.carrier bigLimit.obj.carrier
  induced_comm : ∀ i,
    induced.comp (smallLimit.canon i) =
      (bigLimit.canon (embedIndex i)).comp (stage i)

end
end AEC
