module

public import AEC.Section6.Results
public import AEC.Section7.ContinuityCondition

@[expose] public section

/-!
# Proposition 7.8 — finite-mark continuity (infra)

English Proposition 7.8 existence needs Prop 7.3’s demoted uniform fragment bound and
Lemma 7.6’s demoted mixed / arbitrary-fragment descent, plus a Fodor / `ρ^λ` matrix. Those
are out of scope for this tip.

What ships here is Definition 7.7 for **finite** marks on a `SameLevelChain`: local character
and continuity of freeness along the chain, via Proposition 6.13. Full `SatisfiesContinuity`
on a bare `WorkingScheme` / `ContinuousChain` stays deferred.
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- Tail used for finite-mark continuity (same shape as Prop 6.13 / Lem 7.2). -/
def infra_78_tailSet (P : SingleModelData K) (σ : Cardinal.{u}) : Set Cardinal.{u} :=
  {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}

theorem infra_78_tail (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    Tail P.eligible (infra_78_tailSet P σ) := by
  refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
  obtain ⟨μ, hle, hμ, hrec⟩ :=
    (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
  exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩

/-- Finite `#p.idx` is strictly below the cofinality of any eligible-level chain. -/
theorem infra_78_finite_lt_cof
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    (C : SameLevelChain P hμ) {idx : Type u} (hFin : Finite idx) :
    #idx < C.δ.cof := by
  have hlt : #idx < ℵ₀ := mk_lt_aleph0_iff.2 hFin
  exact hlt.trans_le (SameLevelChain.cof_aleph0 C)

/-- **Definition 7.7 for finite marks** (Prop 6.13 packaging). On a recursion-closed level,
a finite tuple over the union of a `SameLevelChain` is free from some stage, and if every
stage restriction is free from a fixed base through the zero stage, the union is free from
that base. -/
theorem infra_78_finite_continuity (P : SingleModelData K) (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (C : SameLevelChain P (Tail.mem hT hμ))
        (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) C.unionObj),
        p.ν = μ → Finite p.idx → #p.idx ≤ σ →
        (∃ (i : Ordinal.{u}) (hi : i < C.δ),
          IsFreeFrom (C.toUnion i hi) (C.toUnion_arrow i hi) p) ∧
        (∀ (X : P.scheme.Object μ (Tail.mem hT hμ))
          (g : SystemArrow K oneVertexShape
            (P.scheme.asSystem _ X)
            (P.scheme.asSystem _ (C.obj 0 C.hlim.1)))
          (hg : P.scheme.permitted (X := X) (Y := C.obj 0 C.hlim.1) g),
          (∀ (i : Ordinal.{u}) (hi : i < C.δ),
            IsFreeFrom
              (SystemArrow.comp g
                (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
              (P.scheme.comp g
                (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hg
                (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
              (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi))) →
          IsFreeFrom
            (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
            (P.scheme.comp g (C.toUnion 0 C.hlim.1) hg (C.toUnion_arrow 0 C.hlim.1))
            p) := by
  refine ⟨infra_78_tailSet P σ, infra_78_tail P σ hσ, ?_⟩
  intro μ hμ C p hqν hFin hidx
  have hμel : μ ∈ P.eligible := hμ.1.1
  have hrec : μ ∈ recursionClosedLevels P σ := hμ.1
  have hσSucc : Order.succ σ ≤ μ := hμ.2
  have hcof : #p.idx < C.δ.cof := infra_78_finite_lt_cof C hFin
  refine ⟨infra_613_local P σ hσ hμel hrec hσSucc C p hqν hidx hcof, ?_⟩
  intro X g hg hAll
  exact infra_613_continuity P σ hσ hμel hrec hσSucc C p hqν hidx hcof X g hg hAll

end
end AEC
