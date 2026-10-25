module

public import AEC.Section11.GeometricSystem
public import AEC.Section11.LargestActiveLabel
public import AEC.Section11.JointFreshness
public import AEC.Section5.Results

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Lemma 11.2** (Combinatorics of shapes). An admissible family contains `∅`, is closed
under unions, and every set of axes has a largest active subset. In a geometric system an
inactive vertex equals the vertex of that largest active subset. -/
theorem lemma_11_2 {n : ℕ} {L : Set (Finset (Fin n))} (hL : Admissible n L) :
    (∃ e : Finset (Fin n), e ∈ L ∧ e = ∅) ∧
    (∀ s t, s ∈ L → t ∈ L → s ∪ t ∈ L) ∧
    (∀ t : Finset (Fin n), ∃ u, IsLargestActive L t u) ∧
    ∀ (K : AbstractElementaryClass.{u}) (X : GeometricSystem K n L) (t : Finset (Fin n))
      (u : Finset (Fin n)),
      IsLargestActive L t u → ¬ t ∈ L →
      ∃ h : u ⊆ t, Function.Bijective (X.le h) := by
  refine ⟨⟨∅, hL.empty_mem, rfl⟩, fun s t hs ht => hL.union_mem hs ht, hL.exists_largest, ?_⟩
  intro K X t u hu ht
  sorry

/-- **Lemma 11.4** (Replacement and extension of relative bases). Any choice of bases of the
active pieces over the relative spans is a witnessing partition, and an arrow extends a
witnessing partition of its domain to one of its codomain. -/
theorem lemma_11_4 (K : AbstractElementaryClass.{u}) {n : ℕ} {L : Set (Finset (Fin n))}
    (X Y : GeometricSystem K n L) (f : GeometricArrow K X Y) :
    (∀ s (hs : s ∈ L), f.onVertex s '' X.piece s hs ⊆ Y.piece s hs) ∧
    ∀ t, f.onVertex t '' RelativeSpan K X t ⊆ RelativeSpan K Y t := by
  sorry

/-- **Lemma 11.5** (Structural properties and the last-axis description). Geometric arrows
compose, and restriction to a subset of the axes preserves systems and arrows. -/
theorem lemma_11_5 (K : AbstractElementaryClass.{u}) {n : ℕ} {L : Set (Finset (Fin n))}
    (X Y Z : GeometricSystem K n L) (f : GeometricArrow K X Y) (g : GeometricArrow K Y Z) :
    ∃ h : GeometricArrow K X Z,
      ∀ t, h.onVertex t = (g.onVertex t).comp (f.onVertex t) := by
  sorry

/-- **Proposition 11.6** (Tiled presentations). For an admissible shape and every sufficiently
large `μ`, there is a geometric system of level `μ` in which every active piece has
cardinality `μ`. -/
theorem proposition_11_6 (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (hL : Admissible n L) (μ : Cardinal.{u})
    (hμ : aleph0 ≤ μ) :
    ∃ X : GeometricSystem K n L, X.level = μ ∧
      ∀ s (hs : s ∈ L), #(X.piece s hs) = μ := by
  sorry

/-- **Proposition 11.7** (Conditional working package). If the geometric systems of one
admissible shape are categorical on an unbounded countably closed class of eligible levels,
a further subclass carries the working package. -/
theorem proposition_11_7 (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (hL : Admissible n L)
    (S : SystemShape.{u}) (W : WorkingScheme K S) (T : Set Cardinal.{u})
    (hT : EligibleSubclass W.eligible T) :
    ∃ W' : WorkingScheme K S, IsWorkingPackage W' ∧ EligibleSubclass T W'.eligible := by
  sorry

/-- **Theorem 11.9** (Classification with prescribed basis maps). At sufficiently closed
uniform levels, bijections of the nonroot pieces of two systems of the same shape extend to
a system isomorphism. In particular the shape is categorical at those levels. -/
theorem theorem_11_9 (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (hL : Admissible n L) :
    ∃ μ0 : Cardinal.{u}, ∀ μ, μ0 ≤ μ →
      ∀ X Y : GeometricSystem K n L, X.level = μ → Y.level = μ →
        (∀ s (hs : s ∈ L), ∃ e : X.piece s hs ≃ Y.piece s hs, True) →
        ∃ f : GeometricArrow K X Y, ∀ t, Function.Bijective (f.onVertex t) := by
  sorry

end
end AEC
