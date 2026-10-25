module

public import AEC.Section7.AllDominated
public import AEC.Section6.FreeExtension

@[expose] public section

namespace AEC
section

universe u

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {A : W.Object μ hμ}

/-- **Definition 7.10.** A witnessing chain for marks `bᵢ` has `bᵢ` in the successor of stage
`i`, with `tp(bᵢ/Mᵢ)` the free lift of `tp(bᵢ/A)`. -/
structure WitnessingChain (W : WorkingScheme K S) {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible)
    (A : W.Object μ hμ) where
  δ : Type u
  obj : δ → W.Object μ hμ
  into : (i : δ) → SystemArrow K S (W.asSystem hμ A) (W.asSystem hμ (obj i))
  into_arrow : ∀ i, W.permitted (X := A) (Y := obj i) (into i)
  next : δ → δ
  step : (i : δ) →
    SystemArrow K S (W.asSystem hμ (obj i)) (W.asSystem hμ (obj (next i)))
  step_arrow : ∀ i, W.permitted (X := obj i) (Y := obj (next i)) (step i)
  markIdx : δ → Type u
  mark : (i : δ) → markIdx i → Occurrence K S (W.asSystem hμ (obj (next i)))
  finite_mark : ∀ i, Finite (markIdx i)
  free : ∀ i, IsFreeFrom (into i) (into_arrow i)
    (asTuple (step i) (step_arrow i) (mark i))

/-- The chain is an all-dominated-increment chain when each successor is all-dominated over
the preceding stage plus the new mark. -/
def AllDominatedIncrement (C : WitnessingChain W hμ A) : Prop :=
  ∀ i, AllDominated (C.step i) (C.step_arrow i) (C.markIdx i) (C.mark i)

end
end AEC
