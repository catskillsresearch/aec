module

public import AEC.Section7.TiedLocalCharacter

@[expose] public section

/-!
# Lemma 6.11 (average criterion for descent, tied form)

English Lemma 6.11 for `A → B` at eligible sizes `ν ≤ μ`, with "free lift" read as tied
freeness (`IsTiedFreeMixed`, which for `ν = μ` is `IsTiedFree`). It lives here, not in
`AEC/Section6/Results.lean`, because its proof uses the Section 7 tied infrastructure, which
imports `AEC.Section6.Results`.

The same-level case `ν = μ` is proved (`infra_611_tied`). The mixed case `ν < μ` is the open
sub-tip `infra_611_tied_mixed` (needs a mixed testing reduction / tied free lift from level `ν`
to `μ` at all query sizes below `ν`).
-/

namespace AEC
section

universe u

open Cardinal

/-- **Lemma 6.11** (An average criterion for descent). Let `A → B` have eligible sizes
`ν ≤ μ`, and let `q = tp(d/B)` with `|d| ≤ σ < ν`. Choose `χ ≥ c(σ)` below `ν`. Suppose a
bounded sequence `I = (d_i : i < κ)` in `A`, with `χ + ℵ₀ < κ < ν`, has majority value `q ↾ Z`
on every query `Z ⊆ B` of size at most `χ`, with at most `|Z| + ℵ₀` exceptions (the diagram of
`f(d_i) ⌢ Z` computed in `B`). Then `q` is the free lift of its restriction to `A`: tied freeness
`IsTiedFreeMixed f (q ↾ A) q`.

Packaging as Theorem 6.10: a tail of sufficiently closed levels (both `ν` and `μ` in it),
`c(σ) = testCardinal (max LS(K) ℵ₀) g σ`.

**Status:** `ν = μ` proved (`infra_611_tied`); `ν < μ` is `sorry`, tracked as the open
sub-tip `infra_611_tied_mixed`. -/
theorem lemma_6_11 {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ ν μ (hν : ν ∈ T) (hμ : μ ∈ T), ν ≤ μ →
      ∀ (A : P.scheme.Object ν (Tail.mem hT hν)) (B : P.scheme.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
        (hf : P.scheme.permitted (X := A) (Y := B) f)
        (q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
        {κI : Type u} (I : κI → q.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ A))
        (χ : Cardinal.{u}),
        q.ν = μ → #q.idx ≤ σ →
        testCardinal (max (ls K) ℵ₀) P.g σ ≤ χ → χ < ν →
        χ + ℵ₀ < #κI → #κI < ν →
        (∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem _ B)),
          #ι ≤ χ →
          #{i : κI // ¬ P.scheme.DiagramEq (X := q.host) (Y := B)
            (typeJoint (p := q) Z) (seqJoint (fun j => pushOcc f (I i j)) Z)} ≤ #ι + ℵ₀) →
        IsTiedFreeMixed f (q.restrict f hf) q (Equiv.refl _) := by
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun ν μ hν hμ hνμ A B f hf q κI I χ hqν hidx hχ hχν hκ hκν hmaj => ?_⟩
  rcases eq_or_lt_of_le hνμ with heq | hlt
  · subst heq
    exact infra_611_tied P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 f hf q hqν hidx I χ
      ((infra_611_test_le_testCardinal P σ).trans hχ) hχν hκ hκν hmaj
  · -- mixed levels `ν < μ`: open sub-tip `infra_611_tied_mixed`
    sorry

end
end AEC
