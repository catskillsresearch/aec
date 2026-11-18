module

public import AEC.Section14.CardinalAssignment
public import AEC.Section12.PrescribedBoundaryIso
public import AEC.Section10.PointedModel
public import AEC.Section1.UnboundedCategoricity
public import AEC.Section1.CategoricalTail
public import AEC.Section12.Results

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Lemma 14.2** (Choosing subcubes with prescribed supports). Suppose two systems `X⁻` and
`X⁺` have the same cardinal assignment, and prescribed isomorphisms `hₜ` on their proper
faces. Suppose their top is active and put `κ = max κₛ` and `Q = {s ∈ L : κₛ = κ}`. One can
choose witnessing global basis partitions `(Hₛ⁻)` and `(Hₛ⁺)` such that `hₛ[Hₛ⁻] = Hₛ⁺` for
`s ∈ L` proper. Fix such partitions. Let `χ` be a cardinal with `γ ≤ χ < κ` which bounds all
`κₛ < κ`. Given at most `χ` requested elements in the finitely many vertices on both sides,
there are subsystems `U±` inside `X±` whose requested elements lie in the indicated vertices,
whose vertices of size `< κ` are retained in full, whose pieces equal `Hₛ` off `Q` and have
size `χ` on `Q`, and which satisfy `hₜ[Uₜ⁻] = Uₜ⁺` on every proper face. Old subsystems of
size at most `χ` whose pieces lie in these partitions can be included among the requests, and
then each `s ∈ Q` gains exactly `χ` fresh basis coordinates. The inclusions are system arrows.

**Statement (restated, grokbot_01, open):** all systems, the boundary isomorphism and all arrows
are pointed for the minimal type `D` (standing hypotheses added), and the chosen partitions
`HX`, `HY` are witnessing (they span `P` at every vertex). Without pointedness the subsystems
could be re-pieced copies of `X`, `Y` (a degenerate route via `GeometricSystem.repiece`). -/
theorem lemma_14_2 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms) {n : ℕ}
    {L : Set (Finset (Fin n))} (γ χ κ : Cardinal.{u})
    (A : CardinalAssignment n L γ)
    (X Y : GeometricSystem K n L) (PX : X.IsPointed D) (PY : Y.IsPointed D)
    (h : PrescribedBoundaryIso K X Y) (hpt : h.IsPointed PX PY)
    (hassign : ∀ s (hs : s ∈ L),
      X.pieceRank s hs = A.kappa s ∧ Y.pieceRank s hs = A.kappa s)
    (htop : Finset.univ ∈ L) (hχ : γ ≤ χ) (hχκ : χ < κ)
    (hmax : ∀ s, s ∈ L → A.kappa s ≤ κ) (hreach : ∃ s, s ∈ L ∧ A.kappa s = κ)
    (hsmall : ∀ s, s ∈ L → A.kappa s < κ → A.kappa s ≤ χ)
    (reqX : ∀ t : Finset (Fin n), Set (X.vertex t).carrier)
    (reqY : ∀ t : Finset (Fin n), Set (Y.vertex t).carrier)
    (hreqX : #(Σ t, {x // x ∈ reqX t}) ≤ χ)
    (hreqY : #(Σ t, {x // x ∈ reqY t}) ≤ χ) :
    ∃ (HX : ∀ s, s ∈ L → Set (X.vertex s).carrier)
      (HY : ∀ s, s ∈ L → Set (Y.vertex s).carrier),
      (∀ s (hs : s ∈ L), #(HX s hs) = A.kappa s ∧ #(HY s hs) = A.kappa s) ∧
      (∀ t, X.inP t = {x | InClosure (X.indep t)
        {y | ∃ s, ∃ hs : s ∈ L, ∃ hst : s ⊆ t, ∃ z, z ∈ HX s hs ∧ X.le hst z = y} x}) ∧
      (∀ t, Y.inP t = {x | InClosure (Y.indep t)
        {y | ∃ s, ∃ hs : s ∈ L, ∃ hst : s ⊆ t, ∃ z, z ∈ HY s hs ∧ Y.le hst z = y} x}) ∧
      (∀ s (hs : s ∈ L) (ht : s ≠ Finset.univ),
        (h.onFace s ht).toEmbedding '' HX s hs = HY s hs) ∧
      ∃ (UX UY : GeometricSystem K n L) (PUX : UX.IsPointed D) (PUY : UY.IsPointed D)
        (intoX : GeometricArrow K UX X) (intoY : GeometricArrow K UY Y),
        intoX.IsPointed PUX PX ∧ intoY.IsPointed PUY PY ∧
        (∀ t, Function.Injective (intoX.onVertex t)) ∧
        (∀ t, Function.Injective (intoY.onVertex t)) ∧
        (∀ t x, x ∈ reqX t → ∃ y, intoX.onVertex t y = x) ∧
        (∀ t y, y ∈ reqY t → ∃ z, intoY.onVertex t z = y) ∧
        (∀ t, Model.card (X.vertex t) < κ → Function.Surjective (intoX.onVertex t)) ∧
        (∀ t, Model.card (Y.vertex t) < κ → Function.Surjective (intoY.onVertex t)) ∧
        (∀ s (hs : s ∈ L),
          intoX.onVertex s '' UX.piece s hs ⊆ HX s hs ∧
          intoY.onVertex s '' UY.piece s hs ⊆ HY s hs ∧
          (A.kappa s < κ →
            intoX.onVertex s '' UX.piece s hs = HX s hs ∧
            intoY.onVertex s '' UY.piece s hs = HY s hs) ∧
          (A.kappa s = κ → #(UX.piece s hs) = χ ∧ #(UY.piece s hs) = χ)) ∧
        (∀ s (ht : s ≠ Finset.univ),
          (h.onFace s ht).toEmbedding '' Set.range (intoX.onVertex s) =
            Set.range (intoY.onVertex s)) ∧
        ∀ (OldX OldY : GeometricSystem K n L) (POX : OldX.IsPointed D) (POY : OldY.IsPointed D)
          (oldX : GeometricArrow K OldX X) (oldY : GeometricArrow K OldY Y),
          oldX.IsPointed POX PX → oldY.IsPointed POY PY →
          (∀ t, Model.card (OldX.vertex t) ≤ χ) →
          (∀ t, Model.card (OldY.vertex t) ≤ χ) →
          (∀ s (hs : s ∈ L), oldX.onVertex s '' OldX.piece s hs ⊆ HX s hs) →
          (∀ s (hs : s ∈ L), oldY.onVertex s '' OldY.piece s hs ⊆ HY s hs) →
          (∀ t x, x ∈ Set.range (oldX.onVertex t) → x ∈ reqX t) →
          (∀ t y, y ∈ Set.range (oldY.onVertex t) → y ∈ reqY t) →
          ∃ (keepX : GeometricArrow K OldX UX) (keepY : GeometricArrow K OldY UY),
            keepX.IsPointed POX PUX ∧ keepY.IsPointed POY PUY ∧
            (∀ t, (intoX.onVertex t).comp (keepX.onVertex t) = oldX.onVertex t) ∧
            (∀ t, (intoY.onVertex t).comp (keepY.onVertex t) = oldY.onVertex t) ∧
            ∀ s (hs : s ∈ L), A.kappa s = κ →
              ∃ freshX : Set (X.vertex s).carrier, ∃ freshY : Set (Y.vertex s).carrier,
                #freshX = χ ∧ #freshY = χ ∧
                freshX ⊆ intoX.onVertex s '' UX.piece s hs ∧
                freshY ⊆ intoY.onVertex s '' UY.piece s hs ∧
                (∀ a ∈ freshX, ∀ b, oldX.onVertex s b ≠ a) ∧
                (∀ a ∈ freshY, ∀ b, oldY.onVertex s b ≠ a) := by
  sorry

/-- **Theorem 14.3** (Exact lifting at every larger cardinal). For every finite allowed shape
and every monotone assignment `(κ_s : s ∈ L)` of cardinals at least `γ`, any prescribed boundary
isomorphism between two systems with that assignment extends to an isomorphism of their tops.

**Statement (restated, honest form, open):** `γ` is the threshold produced by the construction
(existential), the systems are pointed for `D` and *have* the assignment
(`pieceRank s = A.kappa s`), the boundary isomorphism is pointed, and the top isomorphism is
pointed and extends `h` on every proper face. The former statement did not link `A` to `X`, `Y`
and was false for arbitrary systems (`AEC.Audit.theorem_14_3_arbitrary_false`). -/
theorem theorem_14_3 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms) :
    ∃ γ : Cardinal.{u}, aleph0 ≤ γ ∧
      ∀ {n : ℕ} {L : Set (Finset (Fin n))}, Admissible n L →
      ∀ (A : CardinalAssignment n L γ)
        (X Y : GeometricSystem K n L) (PX : X.IsPointed D) (PY : Y.IsPointed D),
        (∀ s (hs : s ∈ L), X.pieceRank s hs = A.kappa s ∧ Y.pieceRank s hs = A.kappa s) →
        ∀ h : PrescribedBoundaryIso K X Y, h.IsPointed PX PY →
          ∃ e : (X.vertex Finset.univ).carrier ≃[K.τ] (Y.vertex Finset.univ).carrier,
            K.Strong e.toEmbedding ∧
            (∀ a, e (PX.copy Finset.univ a) = PY.copy Finset.univ a) ∧
            ∀ (s : Finset (Fin n)) (hs : s ≠ Finset.univ) (x : (X.vertex s).carrier),
              e (X.le (Finset.subset_univ s) x) =
                Y.le (Finset.subset_univ s) (h.onFace s hs x) := by
  sorry

/-- **Corollary 14.4** (Pointed categoricity on a tail). Above a threshold `γ`, any two models
of a given cardinality that carry the fixed point pattern are pointedly isomorphic.

**Statement change:** now assumes the paper's standing hypothesis `CategoricalUnbounded K`.
The unconditional form is false (`AEC.Audit.Pred.corollary_14_4_unconditional_false`: sets with
a unary predicate, which are categorical in no infinite cardinal). grokbot_01: the product clauses
`D.ProductAxioms` of Definition 10.3 are now explicit. -/
theorem corollary_14_4 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms) :
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
