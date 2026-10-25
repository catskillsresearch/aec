module

public import AEC.Section14.CardinalAssignment
public import AEC.Section12.PrescribedBoundaryIso
public import AEC.Section10.PointedModel
public import AEC.Section1.UnboundedCategoricity
public import AEC.Section1.CategoricalTail

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Lemma 14.2** (Choosing subcubes with prescribed supports). Two systems with the same
cardinal assignment have subsystems whose active pieces of maximum rank have any prescribed
intermediate cardinality, and whose proper faces are matched by the given boundary maps. -/
theorem lemma_14_2 (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (γ χ : Cardinal.{u})
    (A : CardinalAssignment n L γ) (hχ : γ ≤ χ) (hL : ∀ s, s ∈ L → A.kappa s = χ) :
    ∃ X Y : GeometricSystem K n L, ∃ _h : PrescribedBoundaryIso K X Y,
      X.level = χ ∧ Y.level = χ ∧
      ∀ s (hs : s ∈ L), #(X.piece s hs) = A.kappa s ∧ #(Y.piece s hs) = A.kappa s := by
  sorry

/-- **Theorem 14.3** (Exact lifting at every larger cardinal). For every finite allowed shape
and every monotone assignment of cardinals at least `γ`, a prescribed boundary isomorphism
between two systems with that assignment extends to an isomorphism of their tops. -/
theorem theorem_14_3 (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (γ : Cardinal.{u})
    (A : CardinalAssignment n L γ)
    (X Y : GeometricSystem K n L) (h : PrescribedBoundaryIso K X Y) :
    ∃ e : (X.vertex Finset.univ).carrier ≃[K.τ] (Y.vertex Finset.univ).carrier,
      K.Strong e.toEmbedding := by
  sorry

/-- **Corollary 14.4** (Pointed categoricity on a tail). Above a threshold `γ`, any two models
of a given cardinality that carry the fixed point pattern are pointedly isomorphic. -/
theorem corollary_14_4 (K : AbstractElementaryClass.{u}) (D : MinimalData K) :
    ∃ γ : Cardinal.{u}, ∀ κ, γ ≤ κ →
      ∀ M N : PointedModel K D, Model.card M.M = κ → Model.card N.M = κ →
        ∃ e : M.M.carrier ≃[K.τ] N.M.carrier,
          K.Strong e.toEmbedding ∧ e.toEmbedding.comp M.copy = N.copy := by
  sorry

/-- **Theorem 14.5** (Categoricity on a tail). An AEC categorical in unboundedly many cardinals
is categorical in every cardinal above some threshold, including existence of a model at each
such cardinal. -/
theorem theorem_14_5 (K : AbstractElementaryClass.{u}) :
    CategoricalUnbounded K → CategoricalOnTail K := by
  sorry

end
end AEC
