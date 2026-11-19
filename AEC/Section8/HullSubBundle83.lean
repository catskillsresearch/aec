module

public import AEC.Section8.HullSub83
public import AEC.Section8.PairChain83

/-!
# Lemma 8.3: bundled hull pieces in a sublanguage (the sort chain via `subPiecesHom`)

For bundled samples in `L` and a sublanguage `ψ : L₀ →ᴸ L` (over `φ₀ : K.τ →ᴸ L₀`): the
`L₀`-hulls of selected sort coordinates `σ` form finite pieces of `K`; nested selections give
strong natural maps between them, and the `L₀`-hulls include strongly and naturally into the
`L`-hulls.  This is the sort chain `X_H → Y_H` (sublanguage) `→ L_H` (full language).
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {K : AbstractElementaryClass.{u}} {L₀ L : Language.{u, u}} (ψ : L₀ →ᴸ L)

/-- Equal `L`-types give equal `L₀`-types in the reducts (any variable type). -/
theorem tpCode_reduct' {M N : Type u} [L.Structure M] [L.Structure N] {ι : Type}
    {v : ι → M} {w : ι → N} (h : tpCode (L := L) v = tpCode w) :
    @tpCode L₀ M (ψ.reduct M) ι v = @tpCode L₀ N (ψ.reduct N) ι w := by
  letI := ψ.reduct M
  letI := ψ.reduct N
  ext θ
  have := congrArg (fun c : Set (L.Formula ι) => ψ.onFormula θ ∈ c) h
  simp only [tpCode, Set.mem_setOf_eq, LHom.realize_onFormula] at this
  exact Iff.of_eq this

theorem subToHull_hullMap' {M N : Type u} [L.Structure M] [L.Structure N] {ι ι' : Type}
    {v' : ι' → N} {v : ι → M} (g : ι' → ι)
    (h : tpCode (L := L) v' = tpCode (v ∘ g)) (x : subHull ψ v') :
    subToHull ψ v (@hullMap L₀ M N (ψ.reduct M) (ψ.reduct N) ι ι' v' v g (tpCode_reduct' ψ h) x) =
      hullMap g h (subToHull ψ v' x) := by
  induction x using Quotient.ind with
  | _ t =>
    exact congrArg (Quotient.mk _) (onTerm_relabel ψ g t)

variable (φ₀ : K.τ →ᴸ L₀)

section SubLangBundle

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
  {c : (m : ℕ) → 0 < m → TpColorB L r m}
  (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpResB r f (c m hm))
  {r₁ : ℕ} (σ : Fin r₁ → Fin r) [NeZero r] [NeZero r₁]

include hcoh in
/-- **Sublanguage bundled pieces**: the `L₀`-hulls of the `σ`-coordinates of the witnesses. -/
noncomputable def subLangPieces (hP₀ : SubHullStrong ψ φ₀ P) : EM83.FinPieces K where
  obj k := subHullModel ψ φ₀ ((witB hc k).v ∘ Prod.map id σ)
  mem k := K.strong_mem_dom _ (hP₀ _ (witB hc k).mem ((witB hc k).v ∘ Prod.map id σ))
  map e := @redEmb K L₀ φ₀ _ _ (@hullStructure L₀ _ (ψ.reduct _) _ _)
    (@hullStructure L₀ _ (ψ.reduct _) _ _)
    (@hullMapEmb L₀ _ _ (ψ.reduct _) (ψ.reduct _) _ _ _ _ (Prod.map e id)
      (tpCode_reduct' ψ (subBundle_tp hc hcoh σ e)))
  map_refl k := by
    ext x
    exact @hullMap_id L₀ _ (ψ.reduct _) _ _
      (tpCode_reduct' ψ (subBundle_tp hc hcoh σ (k := k) (l := k) idEmb)) x
  map_trans e f := by
    ext x
    exact (@hullMap_comp L₀ _ _ (ψ.reduct _) (ψ.reduct _) _ _ _ (ψ.reduct _) _ _ _ _
      (Prod.map e id) (Prod.map f id) (tpCode_reduct' ψ (subBundle_tp hc hcoh σ e))
      (tpCode_reduct' ψ (subBundle_tp hc hcoh σ f))
      (tpCode_reduct' ψ (subBundle_tp hc hcoh σ (e.trans f))) x).symm
  strong e := @hullMap_strong K L₀ φ₀ (reductClass ψ P) (hullStrong_reductClass ψ φ₀ hP₀)
    _ _ (ψ.reduct _) (ψ.reduct _) ⟨_, (witB hc _).mem, rfl⟩ ⟨_, (witB hc _).mem, rfl⟩
    _ _ _ _ _ _ _ _ (Prod.map e id) (tpCode_reduct' ψ (subBundle_tp hc hcoh σ e))

include hcoh in
/-- **Sublanguage-to-language inclusion** of the `σ`-pieces (`Y_H` in `L₀` into its `L`-hull):
strong and natural. -/
noncomputable def subLangHom (hP₀ : SubHullStrong ψ φ₀ P) (hP : HullStrong (ψ.comp φ₀) P) :
    EM83.PiecesHom (subLangPieces ψ φ₀ hc hcoh σ hP₀)
      (subBundlePieces hc hcoh σ (ψ.comp φ₀) hP) where
  app k := subHullIncl ψ φ₀ ((witB hc k).v ∘ Prod.map id σ)
  strong k := subHullIncl_strong ψ φ₀ _ (hP _ (witB hc k).mem _) (hP₀ _ (witB hc k).mem _)
  natural e := by
    ext x
    exact subToHull_hullMap' ψ (Prod.map e id) (subBundle_tp hc hcoh σ e) x

variable {r₀ : ℕ} (τ : Fin r₀ → Fin r₁) [NeZero r₀]

include hcoh in
/-- **Nested sublanguage pieces** `X_H → Y_H` (both in `L₀`): strong and natural. -/
noncomputable def subLangSubHom (hP₀ : SubHullStrong ψ φ₀ P) :
    EM83.PiecesHom (subLangPieces ψ φ₀ hc hcoh (σ ∘ τ) hP₀) (subLangPieces ψ φ₀ hc hcoh σ hP₀) where
  app k := @redEmb K L₀ φ₀ _ _ (@hullStructure L₀ _ (ψ.reduct _) _ _)
    (@hullStructure L₀ _ (ψ.reduct _) _ _)
    (@hullMapEmb L₀ _ _ (ψ.reduct _) (ψ.reduct _) _ _ ((witB hc k).v ∘ Prod.map id (σ ∘ τ))
      ((witB hc k).v ∘ Prod.map id σ) (Prod.map id τ) rfl)
  strong k := @hullMap_strong K L₀ φ₀ (reductClass ψ P) (hullStrong_reductClass ψ φ₀ hP₀)
    _ _ (ψ.reduct _) (ψ.reduct _) ⟨_, (witB hc k).mem, rfl⟩ ⟨_, (witB hc k).mem, rfl⟩
    _ _ _ _ _ _ _ _ (Prod.map id τ) rfl
  natural {k l} e := by
    ext x
    exact (@hullMap_comp L₀ _ _ (ψ.reduct _) (ψ.reduct _) _ _ _ (ψ.reduct _) _ _ _ _
        (Prod.map e id) (Prod.map id τ) (tpCode_reduct' ψ (subBundle_tp hc hcoh (σ ∘ τ) e)) rfl
        (tpCode_reduct' ψ (subBundle_tp hc hcoh (σ ∘ τ) e)) x).trans
      (@hullMap_comp L₀ _ _ (ψ.reduct _) (ψ.reduct _) _ _ _ (ψ.reduct _) _ _ _ _
        (Prod.map id τ) (Prod.map e id) rfl (tpCode_reduct' ψ (subBundle_tp hc hcoh σ e))
        (tpCode_reduct' ψ (subBundle_tp hc hcoh (σ ∘ τ) e)) x).symm

include hcoh in
/-- **The sort chain via the sublanguage**: `X_H → Y_H` in `L₀`, then `Y_H → L_H` (into the
`L`-hull of `σ`, then into the full `L`-hull). -/
noncomputable def subLangChain (hP₀ : SubHullStrong ψ φ₀ P) (hP : HullStrong (ψ.comp φ₀) P) :
    EM83.PiecesHom (subLangPieces ψ φ₀ hc hcoh σ hP₀)
      (tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := ψ.comp φ₀) hP) :=
  (subBundleHom hc hcoh σ (ψ.comp φ₀) hP).comp (subLangHom ψ φ₀ hc hcoh σ hP₀ hP)

end SubLangBundle

end Hull83
end AEC
