module

public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- `ρ` is large enough that every coloring of the `k`-element subsets of a type of
cardinality at least `ρ`, with `#ξ` colors, has a homogeneous subset of cardinality `ν`.
This is the relation defining `Rₖ(ξ, ν)` in Lemma 2.5. -/
def IsErdosRadoBound (k : ℕ) (ξ ν ρ : Cardinal.{u}) : Prop :=
  ∀ (α : Type u) (_hα : ρ ≤ #α) (c : {s : Finset α // s.card = k} → ξ.ord.ToType),
    ∃ t : Set α, ν ≤ #t ∧
      ∃ color : ξ.ord.ToType, ∀ s : Finset α, ∀ hs : s.card = k,
        (∀ x ∈ s, x ∈ t) → c ⟨s, hs⟩ = color

/-- The recursive cardinal written in the proof of Lemma 2.5:
`R₁(ξ, ν)` exceeds `ξ · ν`, and `R_{k+1}(ξ, ν) = (ξ ^ Rₖ(ξ, ν))⁺`. -/
noncomputable def recursivePartitionBound : ℕ → Cardinal.{u} → Cardinal.{u} → Cardinal.{u}
  | 0, _, _ => 0
  | 1, ξ, ν => Order.succ (ξ * ν)
  | k + 2, ξ, ν => Order.succ (ξ ^ recursivePartitionBound (k + 1) ξ ν)

end
end AEC
