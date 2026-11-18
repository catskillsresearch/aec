module

public import AEC.Section7.TiedLocalCharacter

@[expose] public section

/-!
# Proposition 6.13 (tied form)

English Proposition 6.13 with "free" read as the free lift of Theorem 6.10, i.e. tied freeness
`IsTiedFree` of `p` from its restriction (the untied `IsFreeFrom` is vacuous,
`AEC/Audit/FreeFromVacuous.lean`). It lives here, not in `AEC/Section6/Results.lean`, because
its proof uses the Section 7 tied infrastructure, which imports `AEC.Section6.Results`.
-/

namespace AEC
section

universe u

open Cardinal

/-- **Proposition 6.13** (Local character and continuity). Let `(A_i : i < δ)` be an increasing
chain of objects at one eligible level `μ` with union `A` of size `μ`, `δ` a nonzero limit
ordinal. If `p = tp(v/A)` and `|v| < cf(δ)`, then `p` is free from some `A_i`. If, in addition,
every restriction `tp(v/A_i)` is free from a fixed base `X ≤ A_0`, then `p` is free from `X`.

"Free from `A_i`" is `IsTiedFree (A_i → A) (p ↾ A_i) p`: on every long approximation sequence
of `p ↾ A_i` and every bounded query of `A` with a sequence-move, `p` answers with the type of
`p ↾ A_i` (Theorem 6.10's free lift). Same packaging as Theorem 6.10: a tail of
recursion-closed levels `μ ≥ σ⁺`, tuples of size `≤ σ`, and the chain is `SameLevelChain`
(the finite-`v` case is covered since `cf δ ≥ ℵ₀`). Proof: `infra_78_tied_local` (stage-trapped
Lemma 6.9 code at the testing arity plus the testing reduction `infra_78_tiedFree_of_upTo`) and
`infra_78_tied_continuity` (transitivity `infra_78_tiedFree_trans` along the cocone). -/
theorem proposition_6_13 {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (C : SameLevelChain P (Tail.mem hT hμ))
        (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) C.unionObj),
        p.ν = μ → #p.idx ≤ σ → #p.idx < C.δ.cof →
        (∃ (i : Ordinal.{u}) (hi : i < C.δ),
          IsTiedFree (C.toUnion i hi)
            (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) p (Equiv.refl _)) ∧
        (∀ (X : P.scheme.Object μ (Tail.mem hT hμ))
          (g : SystemArrow K oneVertexShape
            (P.scheme.asSystem _ X)
            (P.scheme.asSystem _ (C.obj 0 C.hlim.1)))
          (hg : P.scheme.permitted (X := X) (Y := C.obj 0 C.hlim.1) g),
          (∀ (i : Ordinal.{u}) (hi : i < C.δ),
            IsTiedFree
              (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
              ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
                (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
                (P.scheme.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hg
                  (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
              (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)) →
          IsTiedFree (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
            (p.restrict (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
              (P.scheme.comp g (C.toUnion 0 C.hlim.1) hg (C.toUnion_arrow 0 C.hlim.1)))
            p (Equiv.refl _)) := by
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun μ hμ C p hνμ hidx hcof =>
    ⟨infra_78_tied_local P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 C p hνμ hidx hcof,
      fun X g hg hAll =>
        infra_78_tied_continuity P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 C p hνμ hidx hcof
          X g hg hAll⟩⟩

end
end AEC
