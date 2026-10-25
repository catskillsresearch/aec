module

public import AEC.Section1.AbstractElementaryClass

@[expose] public section

namespace AEC
section

universe u


open FirstOrder

/-- The orbit arrow `p → r` of Section 3.3: some strong self-map of `M` carries the
tuple `xs` onto the tuple `ys`. -/
def OrbitArrow (K : AbstractElementaryClass.{u}) (M : Model K.τ) {ι : Type u}
    (xs ys : ι → M.carrier) : Prop :=
  ∃ f : Language.Embedding K.τ M.carrier M.carrier,
    K.Strong f ∧ ∀ i, f (xs i) = ys i

end
end AEC
