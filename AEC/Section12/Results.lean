module

public import AEC.Section12.PrescribedBoundaryIso
public import AEC.Section2.OrderPresentation
public import AEC.Section4.NaturalDiagram
public import AEC.Section11.PointedSystem
public import AEC.Section1.UnboundedCategoricity

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- A prescribed boundary isomorphism of pointed systems preserves the copies of `M₀`. -/
def PrescribedBoundaryIso.IsPointed {K : AbstractElementaryClass.{u}} {D : MinimalData K}
    {n : ℕ} {L : Set (Finset (Fin n))} {X Y : GeometricSystem K n L}
    (PX : X.IsPointed D) (PY : Y.IsPointed D) (h : PrescribedBoundaryIso K X Y) : Prop :=
  ∀ (s : Finset (Fin n)) (hs : s ≠ Finset.univ) (a : D.M0.carrier),
    h.onFace s hs (PX.copy s a) = PY.copy s a

/-- Exact geometric boundary lifting (the conclusion of Theorem 12.2) for pointed systems of one
shape at level `μ`: every pointed prescribed boundary isomorphism extends to a pointed
isomorphism of all vertices commuting with the inclusions. -/
def ExactBoundaryLiftingAt {K : AbstractElementaryClass.{u}} (D : MinimalData K) (n : ℕ)
    (L : Set (Finset (Fin n))) (μ : Cardinal.{u}) : Prop :=
  ∀ (X Y : GeometricSystem K n L) (PX : X.IsPointed D) (PY : Y.IsPointed D),
    X.UniformAt μ → Y.UniformAt μ →
    ∀ h : PrescribedBoundaryIso K X Y, h.IsPointed PX PY →
      ∃ e : ∀ t, (X.vertex t).carrier ≃[K.τ] (Y.vertex t).carrier,
        (∀ t, K.Strong (e t).toEmbedding) ∧
        (∀ t a, e t (PX.copy t a) = PY.copy t a) ∧
        (∀ (s : Finset (Fin n)) (hs : s ≠ Finset.univ) (x : (X.vertex s).carrier),
          e s x = h.onFace s hs x) ∧
        ∀ (s t : Finset (Fin n)) (hst : s ⊆ t) (x : (X.vertex s).carrier),
          e t (X.le hst x) = Y.le hst (e s x)

/-- **Theorem 12.2** (Exact geometric boundary lifting). For every finite allowed shape, at all
sufficiently closed uniform levels, every prescribed boundary isomorphism between two systems of
that shape extends to a pointed isomorphism of their tops; the top isomorphism with its
prescribed restrictions is an isomorphism of the systems.

**Statement (restated, honest form, open):** systems are pointed geometric systems of the
minimal type `D` (standing hypotheses added), the boundary isomorphism is pointed, levels range
over an unbounded class `T` of uniform levels, and the conclusion is `ExactBoundaryLiftingAt`
(a pointed system isomorphism agreeing with `h`). The former statement for arbitrary systems was
false (`AEC.Audit.theorem_12_2_arbitrary_false`). -/
theorem theorem_12_2 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms) {n : ℕ}
    {L : Set (Finset (Fin n))} (hL : Admissible n L) :
    ∃ T : Set Cardinal.{u}, (∀ κ, ∃ μ, κ ≤ μ ∧ μ ∈ T) ∧
      ∀ μ ∈ T, ExactBoundaryLiftingAt D n L μ := by
  sorry

/-- **Lemma 12.3** (Joint boundary comparisons). Assume exact geometric boundary lifting for all
allowed shapes on fewer than `n` axes. At a sufficiently closed uniform level, a prescribed
boundary isomorphism between two `n`-axis systems preserves the bounded `K`-diagram of every
occurrence-tagged boundary list, computed in the top models.

**Statement (restated, honest form, open):** systems are pointed for `D`, `h` is pointed, the
level is in an unbounded class `T`, and the inductive hypothesis (exact lifting on fewer axes,
`ExactBoundaryLiftingAt`) is explicit. The former statement about arbitrary systems was false
(`AEC.Audit.lemma_12_3_false`: faces disjoint in one top, identified in the other). -/
theorem lemma_12_3 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms) (SD : StableDiagram K) {n : ℕ}
    {L : Set (Finset (Fin n))} (hL : Admissible n L) :
    ∃ T : Set Cardinal.{u}, (∀ κ, ∃ μ, κ ≤ μ ∧ μ ∈ T) ∧
      ∀ μ ∈ T, (∀ m < n, ∀ L' : Set (Finset (Fin m)), Admissible m L' →
          ExactBoundaryLiftingAt D m L' μ) →
      ∀ (X Y : GeometricSystem K n L) (PX : X.IsPointed D) (PY : Y.IsPointed D),
        X.UniformAt μ → Y.UniformAt μ →
        ∀ h : PrescribedBoundaryIso K X Y, h.IsPointed PX PY →
        ∀ {α : Type u} (occ : α → Σ s : {s : Finset (Fin n) // s ≠ Finset.univ},
            (X.vertex s.1).carrier),
          #α < μ →
          ∀ (σ : Cardinal.{u}) (hσ : #α ≤ σ)
            (hX : SD.t σ ≤ Model.card (X.vertex Finset.univ))
            (hY : SD.t σ ≤ Model.card (Y.vertex Finset.univ)),
            SD.same hσ (X.inK Finset.univ) (Y.inK Finset.univ) hX hY
              (fun i => X.le (Finset.subset_univ _) (occ i).2)
              (fun i => Y.le (Finset.subset_univ _) (h.onFace (occ i).1.1 (occ i).1.2 (occ i).2)) := by
  sorry

/-- **Lemma 12.5** (Testing on rationally tiled parameter orders). There is a monotone bound
`g(σ, τ)` such that two placements of tuples of length at most `σ` in order enlargements of `J`,
with a fixed tuple `c` of length at most `τ`, have the same comparison over the parameter layout
together with `c` once they agree on every parameter query of size at most `g(σ, τ)`.

**Statement (restated, honest form, open):** the candidates `t`, `s` now live in an order
enlargement `incl : I ↪o Istar` (as in the English; with candidates inside `E(I)` the query could
contain the candidates themselves), queries and `c` come from `E(I)`, and the conclusion is the
whole comparison over the layout: agreement on *every* bounded query (the former conclusion only
compared `(t, c)` with `(s, c)`). The query type is quantified inside the hypothesis (the
original form was false, `AEC.Audit.lemma_12_5_original_false`).
**Caveat:** the layout is all of `E(I)` for an arbitrary order `I`, which generalizes the
English rationally tiled layouts `J₀ + Σ Hᵢ × ℚ`; if this is too strong it must be specialized to
tiled orders. `StableDiagram` has no restriction / arity-monotonicity clauses, which the proof
will need (Proposition 4.2 natural-diagram calculus). -/
theorem lemma_12_5 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) :
    ∃ g : Cardinal.{u} → Cardinal.{u} → Cardinal.{u},
      (∀ σ τ σ' τ', σ ≤ σ' → τ ≤ τ' → g σ τ ≤ g σ' τ') ∧
      ∀ {I Istar : Type u} [LinearOrder I] [Nonempty I] [LinearOrder Istar] [Nonempty Istar]
        (incl : I ↪o Istar) {α β : Type u}
        (σ τ : Cardinal.{u}) (hσ : #α ≤ σ) (hτ : #β ≤ τ)
        (t s : α → SupportTerm E.lab E.arity Istar) (c : β → SupportTerm E.lab E.arity I),
        (∀ (ι : Type u) (q : ι → SupportTerm E.lab E.arity I) (hq : #ι ≤ g σ τ)
            (hquery : #((α ⊕ β) ⊕ ι) ≤ σ + τ + g σ τ),
          SameNaturalDiagram K E D (σ + τ + g σ τ) hquery
            (Sum.elim (Sum.elim t (fun b => SupportTerm.along incl (c b)))
              (fun i => SupportTerm.along incl (q i)))
            (Sum.elim (Sum.elim s (fun b => SupportTerm.along incl (c b)))
              (fun i => SupportTerm.along incl (q i)))) →
        ∀ (κ : Cardinal.{u}) (ι : Type u) (q : ι → SupportTerm E.lab E.arity I)
          (hquery : #((α ⊕ β) ⊕ ι) ≤ σ + τ + κ),
          SameNaturalDiagram K E D (σ + τ + κ) hquery
            (Sum.elim (Sum.elim t (fun b => SupportTerm.along incl (c b)))
              (fun i => SupportTerm.along incl (q i)))
            (Sum.elim (Sum.elim s (fun b => SupportTerm.along incl (c b)))
              (fun i => SupportTerm.along incl (q i))) := by
  sorry

/-- **Lemma 12.6** (Realization using an unoccupied strip). Let `E(J)` be a pointed presentation
of cardinality `μ` at a sufficiently closed uniform level, `V ⊆ J` a convex substrip of
cardinality `μ`, and `B ⊆ E(J)` a parameter layout represented by positions in `J \ V`. If a
bounded tuple `z*` of `E(J*)`, `J ⊆ J*`, has a placed comparison over `B`, a tuple `z` of `E(J)`
has the same comparison over every bounded list from `B`, retaining specified old entries whose
representations avoid `V`.

**Statement (restated, honest form, open):** the unoccupied convex strip `V` (`OrdConnected`,
`#V = #J = μ`, `μ` in an unbounded class `T` of levels) is restored; the conclusion is the
comparison over every bounded list `q` of terms with positions in `J \ V` (the layout `B`); old
entries must have representations avoiding `V`. The former statement had no strip (false:
`AEC.Audit.lemma_12_6_false`, `J` a point). The pointedness of `E` is not represented. -/
theorem lemma_12_6 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) :
    ∃ T : Set Cardinal.{u}, (∀ κ, ∃ μ, κ ≤ μ ∧ μ ∈ T) ∧
      ∀ μ ∈ T, ∀ {J Jstar : Type u} [LinearOrder J] [LinearOrder Jstar]
        [Nonempty J] [Nonempty Jstar] (incl : J ↪o Jstar) (V : Set J),
        #J = μ → V.OrdConnected → #V = μ →
        ∀ {α : Type u} (σ : Cardinal.{u}), #α ≤ σ → σ < μ →
        ∀ (zStar : α → SupportTerm E.lab E.arity Jstar) (old : Set α),
          (∀ i ∈ old, ∃ t : SupportTerm E.lab E.arity J, (∀ a, t.pos a ∉ V) ∧
            zStar i = SupportTerm.along incl t) →
          ∃ z : α → SupportTerm E.lab E.arity J,
            (∀ i ∈ old, zStar i = SupportTerm.along incl (z i)) ∧
            ∀ {ι : Type u} (q : ι → SupportTerm E.lab E.arity J), (∀ k a, (q k).pos a ∉ V) →
              ∀ (κ : Cardinal.{u}) (hq : #(α ⊕ ι) ≤ κ), κ < μ →
                SameNaturalDiagram K E D κ hq
                  (Sum.elim z q) (Sum.elim zStar (fun k => SupportTerm.along incl (q k))) := by
  sorry

end
end AEC
