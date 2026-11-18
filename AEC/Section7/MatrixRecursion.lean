module

public import AEC.Section7.LimitStep

@[expose] public section

/-!
# The `ρ⁺` recursion of Proposition 7.8 (`infra_78_matrix_recursion`, split cycle 48)

`infra_78_recursion_succ_stage` is the successor stage in pair form: from the current pair
`X → Y`, the base `X₀ → X`, the mark `b` with invariant (5) and a family of candidate lists, it
produces the next pair with permitted steps and a commuting square, invariant (5) for the moved
mark, and either all candidates isolated (identity step) or a failing candidate with a nonfree
extension. The transfinite plumbing (`infra_78_recursion_plumbing`) and the verification of the
required outputs (`infra_78_recursion_outputs`) are tracked on the board.
-/

universe u

open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}

section SuccStage
variable (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
  {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ)

/-- **Successor stage of the Prop 7.8 recursion, pair form** (`infra_78_recursion_succ_stage`).
Given the stage-`i` pair `pair : X → Y` at a level `μ` of the Prop 7.3 tail, the base
`g0 : X₀ → X`, the mark `b` in `Y` with invariant (5), and a family of candidate lists `d_l` in
`Y` with `|b| + |d_l| ≤ σ`, there is a next pair `pair' : X' → Y'` with permitted steps and a
commuting square, invariant (5) for the moved mark at `X'` along `stepX ∘ g0`, and: either every
candidate list is isolated relative to `b`, or some candidate `d_l` is failing and
`tp(b, d_l / X')` is not tied free over `X` (nonfree extension, Prop 7.3 + type-identifying
amalgamation, `infra_78_matrix_successor_step`'s construction). In the first case the step is
the identity. -/
theorem infra_78_recursion_succ_stage
    {X X0 Y : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)}
    (pair : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y))
    (g0 : SystemArrow K oneVertexShape (P.scheme.asSystem _ X0) (P.scheme.asSystem _ X))
    {uIdx cIdx L : Type u}
    (b : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y))
    (d : L → cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y))
    (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (h5 : IsTiedFree g0 ((infra_78_markTuple pair b).restrict g0 trivial)
      (infra_78_markTuple pair b) (Equiv.refl _)) :
    ∃ (X' Y' : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
      (stepX : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ X'))
      (stepY : SystemArrow K oneVertexShape (P.scheme.asSystem _ Y) (P.scheme.asSystem _ Y'))
      (pair' : SystemArrow K oneVertexShape (P.scheme.asSystem _ X') (P.scheme.asSystem _ Y')),
      SystemArrow.comp pair stepY = SystemArrow.comp stepX pair' ∧
      IsTiedFree (SystemArrow.comp g0 stepX)
        ((infra_78_markTuple pair' (fun k => pushOcc stepY (b k))).restrict
          (SystemArrow.comp g0 stepX) trivial)
        (infra_78_markTuple pair' (fun k => pushOcc stepY (b k))) (Equiv.refl _) ∧
      ((∀ l, IsRelativelyIsolated (infra_78_markTuple pair (Sum.elim b (d l)))
          (Equiv.refl (uIdx ⊕ cIdx))) ∨
       ∃ l, ¬ IsRelativelyIsolated (infra_78_markTuple pair (Sum.elim b (d l)))
          (Equiv.refl (uIdx ⊕ cIdx)) ∧
        ¬ IsTiedFree stepX
          ((infra_78_markTuple pair' (fun k => pushOcc stepY (Sum.elim b (d l) k))).restrict
            stepX trivial)
          (infra_78_markTuple pair' (fun k => pushOcc stepY (Sum.elim b (d l) k)))
          (Equiv.refl _)) := by
  classical
  by_cases hall : ∀ l, IsRelativelyIsolated (infra_78_markTuple pair (Sum.elim b (d l)))
      (Equiv.refl (uIdx ⊕ cIdx))
  · refine ⟨X, Y, SystemArrow.refl _, SystemArrow.refl _, pair, ?_, ?_, Or.inl hall⟩
    · apply SystemArrow.ext; intro v; rfl
    · exact h5
  push Not at hall
  obtain ⟨l, hl⟩ := hall
  set q := infra_78_markTuple pair (Sum.elim b (d l)) with hqdef
  let e : q.idx ≃ uIdx ⊕ cIdx := Equiv.refl _
  have hqν : q.ν = μ := rfl
  have hσμ : σ < μ :=
    (Order.lt_succ_iff.2 (le_max_left σ (infra_73_h P σ))).trans_le hμT.2
  have hqlt : #q.idx < μ := hidx.trans_lt hσμ
  have hult : #uIdx < μ :=
    (Cardinal.mk_le_of_injective (f := fun u => (Sum.inl u : uIdx ⊕ cIdx))
      Sum.inl_injective).trans_lt hqlt
  obtain ⟨B, fB, hfB, qB, eB, hqBν, hS, hmarg, hnf⟩ :=
    infra_78_nonfree_extension_tied P σ hσ hμT q e hqν hidx hl
  obtain ⟨top, f1, f2, hf1, hf2, hcomm, hvals⟩ :=
    infra_78_same_level_type_amalgam q (qB.restrict fB hfB) eB (Equiv.refl _) hqν hqBν hS
  let pair' : SystemArrow K oneVertexShape (P.scheme.asSystem _ B) (P.scheme.asSystem _ top) :=
    SystemArrow.comp qB.incl f2
  let q' := infra_78_markTuple pair' (fun k => pushOcc f1 (q.val k))
  have hsq : ∀ v x, f1.onVertex v (q.incl.onVertex v x) =
      q'.incl.onVertex v (fB.onVertex v x) := fun v x => congrFun (congrArg DFunLike.coe
        (hcomm v)) x
  have hg0 : P.scheme.permitted (X := X0) (Y := X) g0 := trivial
  have hinv : IsTiedFree g0 ((q.marginal e).restrict g0 hg0) (q.marginal e) (Equiv.refl _) := h5
  have hR1 : infra_78_HostRel q (q'.restrict fB hfB) f1 (Equiv.refl _) :=
    ⟨hsq, fun k => rfl⟩
  have hRm : infra_78_HostRel (q.marginal e) ((q'.marginal e).restrict fB hfB) f1
      (Equiv.refl _) := ⟨hsq, fun k => rfl⟩
  have hR2 : infra_78_HostRel qB q' f2 eB.symm := by
    refine ⟨fun v x => rfl, fun i => ?_⟩
    have := hvals i
    exact this
  have hR2m : infra_78_HostRel (qB.marginal (eB.symm.trans e)) (q'.marginal e) f2
      (Equiv.refl _) := by
    refine ⟨fun v x => rfl, fun k => ?_⟩
    have := hvals (eB (e.symm (Sum.inl k)))
    rw [Equiv.symm_apply_apply] at this
    exact this
  have hmargq' : IsTiedFree fB ((q'.marginal e).restrict fB hfB) (q'.marginal e)
      (Equiv.refl _) := by
    have h3 := (infra_78_tiedFree_host_target fB (q.marginal e) hf2 hR2m hqBν rfl hult
      (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 hmarg
    exact infra_78_tiedFree_host_source fB hf1 hRm hqν rfl hult (q'.marginal e) _ _
      (fun _ => rfl) h3
  have h5' : IsTiedFree (SystemArrow.comp g0 fB)
      ((q'.marginal e).restrict (SystemArrow.comp g0 fB) (P.scheme.comp g0 fB hg0 hfB))
      (q'.marginal e) (Equiv.refl _) := by
    refine infra_78_tiedFree_trans g0 hg0 fB hfB (q'.marginal e) ?_ hmargq'
    have h3 := (infra_78_tiedFree_host_target g0 ((q.marginal e).restrict g0 hg0) hf1 hRm
      hqν rfl hult (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 hinv
    have hR' : infra_78_HostRel ((q.marginal e).restrict g0 hg0)
        (((q'.marginal e).restrict fB hfB).restrict g0 hg0) f1 (Equiv.refl _) :=
      ⟨fun v x => hsq v (g0.onVertex v x), fun k => rfl⟩
    exact infra_78_tiedFree_host_source g0 hf1 hR' hqν rfl hult _ _ _ (fun _ => rfl) h3
  have hnf' : ¬ IsTiedFree fB (q'.restrict fB hfB) q' (Equiv.refl _) := by
    intro H
    have h1 := infra_78_tiedFree_host_source' fB hf1 hR1 hqν rfl hqlt q' _ (Equiv.refl _)
      (fun _ => rfl) H
    have h2 := (infra_78_tiedFree_host_target fB q hf2 hR2 hqBν rfl hqlt eB (Equiv.refl _)
      (fun k => (eB.symm_apply_apply k).symm)).2 h1
    exact hnf h2
  refine ⟨B, top, fB, f1, pair', ?_, h5', Or.inr ⟨l, hl, hnf'⟩⟩
  apply SystemArrow.ext
  intro v
  exact hcomm v

end SuccStage
end AEC
