module

public import AEC.Section6.FreeExtension
public import AEC.Section6.TupleOver
public import AEC.Section6.UniformApproximations

@[expose] public section

/-!
# Theorem 6.10 (Stationary free extension) — English gloss

English clauses (from `FreeExtension.md`):

1. **Existence.** At a sufficiently closed level, every type `p = tp(v/A)` with `|v| ≤ σ` has a
   specified actual free lift `p_B` over `B` extending `p` along `A → B`.
2. **Approximation transport.** At bounded query and testing cost at the level of `A`, the free
   lift is computed by transporting sufficiently long approximation sequences in `A`.
3. **Scope.** At one level this includes every bounded query size; in mixed-level use, costs must
   stay below the level of `A`. (Corollary 6.7 enters for independence of section in the English
   proof of clause 3.)
4. **Definition.** An actual type over `B` is *free from* `A` when it is that free lift of its
   restriction to `A` (`IsFreeFrom` in `FreeExtension.lean`).

Proof plan (eventual.pdf §6.2): Lemma 6.9 supplies long uniform approximation sequences on
`SingleModelData`. A general scheme still needs `infra_69_diagram_transport`. Majority
values determine the free extension (`IsFreeLift` / `IsMajorityValue`). The free-lift
argument is not part of the Lemma 6.9 transfer.
-/

namespace AEC
section

universe u

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}

/-- English clause 1: existence of a free lift along a permitted arrow (pinned on Lemma 6.9). -/
theorem stationary_free_extension_exists
    [CategoricalUnbounded K] (F : TermTemplate K S) [hpres : HasPresentations W F]
    [hpack : HasChainUnions W]
    (hedge : ∀ i j, ¬ S.specified i j)
    (hcat : ∀ μ' ∈ W.eligible, Categorical K μ')
    (σ χ b τ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hσ' : aleph0 ≤ τ)
    (hpow : χ ^ σ = χ) (hb : b + σ < χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ)
    (hiso : AssemblesStructIso W b)
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {A B : W.Object μ hμ}
    (f : SystemArrow K S (W.asSystem hμ A) (W.asSystem hμ B))
    (hf : W.permitted (X := A) (Y := B) f)
    (p : TupleOver K S W hμ A) :
    ∃ q : TupleOver K S W hμ B, ∃ e : p.idx ≃ q.idx, IsFreeLift p q f hf e := by
  sorry

/-! Clauses 2–4 are packaged in `IsFreeLift` / `IsFreeFrom` (`FreeExtension.lean`); this file
records the English dependency on Lemma 6.9 via `exists_approximationSequence`. -/

end
end AEC
