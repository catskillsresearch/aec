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

**Statement repair.** Same packaging as Lemma 6.9: the construction runs in `SingleModelData`
(Prop 5.6). Cross-scheme transfer of approximation sequences is not used.

**Pinned.** The free-lift argument (majority values, saturation over the sequence, placement of
majority answers in a chart of `B`) stays open. Lemma 6.9 supplies the sequences.
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- English clause 1: existence of a free lift along a permitted arrow of `P.scheme`.
Pinned on the majority / saturation construction, not on diagram transport. -/
theorem stationary_free_extension_exists
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hidx : #p.idx ≤ σ) (hidxμ : #p.idx < μ) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B, ∃ e : p.idx ≃ q.idx,
      IsFreeLift p q f hf e := by
  /- Majority transport of a Lemma 6.9 approximation sequence; saturation moves queries into
     `A` over the sequence; majority answers place in a chart of `B`. Not diagram transport. -/
  sorry

/-! Clauses 2–4 are packaged in `IsFreeLift` / `IsFreeFrom` (`FreeExtension.lean`). -/

end
end AEC
