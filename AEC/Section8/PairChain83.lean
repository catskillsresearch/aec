module

public import AEC.Section8.HullBundle83

/-!
# Lemma 8.3: the sort chain `X → Y → L` of bundled pieces

For nested selections of sort coordinates `σ ∘ τ` (the `X`-sorts) inside `σ` (the `Y`-sorts)
inside all sorts (`L`), the sub-bundle hull pieces form a chain of strong natural piece maps
`X → Y → L` (`infra_83_pair_pieces`, generic sort chain).
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {K : AbstractElementaryClass.{u}} {L : Language.{u, u}}

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
  {c : (m : ℕ) → 0 < m → TpColorB L r m}
  (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpResB r f (c m hm))
  {r₁ r₀ : ℕ} (σ : Fin r₁ → Fin r) (τ : Fin r₀ → Fin r₁) (φ : K.τ →ᴸ L)
  [NeZero r] [NeZero r₁] [NeZero r₀]

include hcoh in
/-- **Nested sub-bundle inclusion** `X → Y`: from the hulls of the `σ ∘ τ` coordinates to the
hulls of the `σ` coordinates; strong and natural. -/
noncomputable def subSubBundleHom (hP : HullStrong φ P) :
    EM83.PiecesHom (subBundlePieces hc hcoh (σ ∘ τ) φ hP) (subBundlePieces hc hcoh σ φ hP) where
  app k := redEmb φ (hullMapEmb (v := (witB hc k).v ∘ Prod.map id σ)
    (v' := (witB hc k).v ∘ Prod.map id (σ ∘ τ)) (Prod.map id τ) rfl)
  strong k := hullMap_strong hP (witB hc k).mem (witB hc k).mem _ rfl
  natural {k l} e := by
    ext x
    exact (hullMap_comp (Prod.map e id) (Prod.map id τ) (subBundle_tp hc hcoh (σ ∘ τ) e) rfl
        (subBundle_tp hc hcoh (σ ∘ τ) e)
        (show Hull (L := L) ((witB hc k).v ∘ Prod.map id (σ ∘ τ)) from x)).trans
      (hullMap_comp (Prod.map id τ) (Prod.map e id) rfl (subBundle_tp hc hcoh σ e)
        (subBundle_tp hc hcoh (σ ∘ τ) e)
        (show Hull (L := L) ((witB hc k).v ∘ Prod.map id (σ ∘ τ)) from x)).symm

include hcoh in
/-- **The sort chain `X → Y → L`**: the composite of the nested sub-bundle inclusions, a strong
natural transformation of piece functors. -/
noncomputable def pairChainHom (hP : HullStrong φ P) :
    EM83.PiecesHom (subBundlePieces hc hcoh (σ ∘ τ) φ hP)
      (tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP) :=
  (subBundleHom hc hcoh σ φ hP).comp (subSubBundleHom hc hcoh σ τ φ hP)

/-- The induced template maps compose along the chain: `F_X(I) → F_Y(I) → F_L(I)`. -/
theorem pairChain_limMap (hP : HullStrong φ P) (I : Type u) [LinearOrder I] [Nonempty I] :
    (pairChainHom hc hcoh σ τ φ hP).limMap I =
      ((subBundleHom hc hcoh σ φ hP).limMap I).comp
        ((subSubBundleHom hc hcoh σ τ φ hP).limMap I) :=
  EM83.PiecesHom.limMap_comp _ _ I

end Hull83
end AEC
