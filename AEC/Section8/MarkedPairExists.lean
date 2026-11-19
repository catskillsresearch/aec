module

public import AEC.Section8.MarkedPair
public import AEC.Section7.RetractionPair

@[expose] public section

/-!
# Lemma 8.2, first clause for the Prop 5.6 scheme (`infra_82_marked_pair_exists`, cycle 94)

English (Lemma 8.2): "On a further tail of eligible levels, every object sits in a marked pair".
For `SingleModelData` (the scheme of Proposition 5.6) and any stationary prescription (whose marks
are finite, `arity : idx ≃ Fin n`), on the tail `infra_78_closedTail P ∩ infra_615_closed P`
every object `X` is the base of a marked pair `X ≤ Y` (with `e = id`): Theorem 7.9 at the level
(`infra_79_existence_at`) gives an all-dominated realization of the prescribed mark.
-/

universe u

open Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Lemma 8.2 (1) for the Prop 5.6 scheme (proved, cycle 94).** Every object at a level of the
Theorem 7.9 tail sits in a marked pair (identity base isomorphism). -/
theorem infra_82_marked_pair_exists (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ T, ∃ hT : Tail P.scheme.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : P.scheme.Object μ (Tail.mem hT hμ)),
        ∃ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ = μ ∧
          ∃ e : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ M.X),
            P.scheme.permitted (X := X) (Y := M.X) e ∧ ∀ v, Function.Bijective (e.onVertex v) := by
  classical
  have htail := infra_79_tail P
  have hT : Tail P.eligible (infra_78_closedTail P ∩ infra_615_closed P) :=
    ⟨fun μ hμ => hμ.1.1, fun κ => by
      obtain ⟨μ, hκμ, h1, h2⟩ := htail κ
      exact ⟨μ, hκμ, h1, h2⟩⟩
  refine ⟨_, hT, fun μ hμ X => ?_⟩
  have hfin : Finite (Pr.assign (Tail.mem hT hμ) X).idx :=
    Finite.of_equiv _ (Pr.arity (Tail.mem hT hμ) X).symm
  obtain ⟨Y, f, hf, b, hAll, hS⟩ :=
    infra_79_existence_at P ⟨htail, infra_79_retraction_pair P⟩ hμ X
      (Pr.assign (Tail.mem hT hμ) X) hfin
  refine ⟨⟨μ, Tail.mem hT hμ, X, Y, f, hf, _, b, ⟨Equiv.refl _, hS.symm⟩, hAll⟩, rfl,
    SystemArrow.refl _, trivial, fun v => ?_⟩
  exact Function.bijective_id

end AEC
