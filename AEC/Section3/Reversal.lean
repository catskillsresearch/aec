module

public import AEC.Section3.OrbitArrow
public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u


open FirstOrder Cardinal

/-- Reversal at a categoricity cardinal `κ` for tuples of length at most `θ`:
every strong self-map is inverted on every such tuple.
`b_K(θ)` in Theorem 3.11 is a cardinal past which this holds at every categoricity cardinal. -/
def Reverses (K : AbstractElementaryClass.{u}) (theta κ : Cardinal.{u}) : Prop :=
  Categorical K κ ∧
    ∀ (M : Model K.τ) (f : Language.Embedding K.τ M.carrier M.carrier) {ι : Type u}
      (xs : ι → M.carrier),
      K.Mem M → Model.card M = κ → K.Strong f → #ι ≤ theta →
        ∃ g : Language.Embedding K.τ M.carrier M.carrier,
          K.Strong g ∧ ∀ i, g (f (xs i)) = xs i

/-- `b` is a reversal threshold for length `θ` when every categoricity cardinal `≥ b` reverses. -/
def IsReversalThreshold (K : AbstractElementaryClass.{u}) (theta b : Cardinal.{u}) : Prop :=
  ∀ κ, b ≤ κ → Categorical K κ → Reverses K theta κ

end
end AEC
