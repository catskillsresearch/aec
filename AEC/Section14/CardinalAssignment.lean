module

public import AEC.Section11.LargestActiveLabel
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- **Definition 14.1.** A cardinal assignment on an allowed family `L` is a family `(κ_s)` with
`γ ≤ κ_s ≤ κ_t` whenever `s ⊆ t`. -/
structure CardinalAssignment (n : ℕ) (L : Set (Finset (Fin n))) (γ : Cardinal.{u}) where
  kappa : Finset (Fin n) → Cardinal.{u}
  lower : ∀ s, s ∈ L → γ ≤ kappa s
  mono : ∀ s t, s ∈ L → t ∈ L → s ⊆ t → kappa s ≤ kappa t

/-- Equation (16). The piece rank of `P(X_t)` is `κ_{a_L(t)}`, the cardinal assigned to the
largest active label contained in `t`. -/
def IsPieceRank {n : ℕ} {L : Set (Finset (Fin n))} {γ : Cardinal.{u}}
    (A : CardinalAssignment n L γ) (t : Finset (Fin n)) (ρ : Cardinal.{u}) : Prop :=
  ∃ u, IsLargestActive L t u ∧ ρ = A.kappa u

end
end AEC
