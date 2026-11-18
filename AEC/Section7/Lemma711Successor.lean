module

public import AEC.Section7.Lemma711Induction

/-!
# Lemma 7.11, successor step (tied)

At a successor stage `j` (`i ⋖ j`) the paper argues: by induction `tp(x/Mᵢ)` is free from `A`;
`x` and `bᵢ` have product over `Mᵢ` (induction applied to `(x, bᵢ)` and free base change of the
products over `A`); `M_{i+1}` is all-dominated over `Mᵢ + bᵢ`, so Proposition 7.5(3) makes
`tp(x/M_{i+1})` free from `Mᵢ`; transitivity gives freeness from `A`.

`infra_711_successor_of_product` proves the step from the product over `Mᵢ`
(`infra_711_succ_product_statement`, open tip `infra_711_succ_product`), using the proved level
form of 7.5(3) (`infra_75_product_free_level`) and tied transitivity (`infra_78_tiedFree_trans`).
-/

@[expose] public section

namespace AEC
noncomputable section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- **Lemma 7.11 successor: the product over `Mᵢ` (statement; open tip
`infra_711_succ_product`).** Under the induction claim at `i`, a finite `x` in the actual coupling
with tied products with every finite selection of marks below `j = i + 1` has, over `Mᵢ`, the tied
product of `tp(x/Mᵢ)` with `tp(bᵢ/Mᵢ)` (`bᵢ` read in `M_j`, hosted with `x`). -/
def infra_711_succ_product_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ] (C : TiedListWitnessingChain L), C.AllDominatedIncrement →
      ∀ (i0 : L.δ) (j : WithTop L.δ) (h : (i0 : WithTop L.δ) ⋖ j),
        C.Claim (i0 : WithTop L.δ) →
        ∀ x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤), Finite x.idx → x.ν = μ →
          C.prodBelow x j →
          IsProductTied
            ((x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)).restrict
              (C.step h.le) (C.step_arrow h.le))
            (infra_75_markOver (C.step h.le) (C.step_arrow h.le)
              (x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)) (C.mark i0 j h.lt))
            (infra_75_jointOver (C.step h.le) (C.step_arrow h.le)
              (x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)) (C.mark i0 j h.lt))
            (Equiv.refl _)

/-- **Lemma 7.11 successor step from the product over `Mᵢ` (proved).** -/
theorem infra_711_successor_of_product (P : SingleModelData K)
    (hS : infra_711_succ_product_statement P) : infra_711_successor_statement P := by
  intro μ hμ h0 h1 hw1 hw2 A L _ _ C hinc i j hij hCi
  induction i using WithTop.recTopCoe with
  | top => exact absurd hij.lt (not_top_lt)
  | coe i0 =>
  intro x hfin hxν hprod
  have : Finite x.idx := hfin
  let xj := x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)
  have hP := hS hμ h0 h1 hw1 hw2 A L C hinc i0 j hij hCi x hfin hxν hprod
  have hb : #(L.indexAt i0) ≤ ℵ₀ := by
    have := L.finite_each i0
    exact Cardinal.mk_le_aleph0
  have hx : #xj.idx ≤ ℵ₀ := by
    have : Finite xj.idx := hfin
    exact Cardinal.mk_le_aleph0
  have h75 := infra_75_product_free_level P ℵ₀ le_rfl hμ h0 h1 hw1 hw2 (C.stage i0) (C.stage j)
    (C.step hij.le) (C.step_arrow _) (L.indexAt i0) (C.mark i0 j hij.lt) hb (hinc i0 j hij)
    xj hxν hx hP
  have IH := hCi x hfin hxν (C.prodBelow_mono hij.le hprod)
  have hXA : IsTiedFree (C.into (i0 : WithTop L.δ))
      ((xj.restrict (C.step hij.le) (C.step_arrow _)).restrict (C.into _) (C.into_arrow _))
      (xj.restrict (C.step hij.le) (C.step_arrow _)) (Equiv.refl _) := by
    refine infra_711_tiedFree_transport ?_ rfl (C.into_arrow _) (C.into_arrow _) IH
    refine (infra_711_restrict_restrict x _ _ _ _ _ _ ?_).symm
    apply SystemArrow.ext; intro v; exact C.step_comp _ _ v
  have htr := infra_78_tiedFree_trans (C.into (i0 : WithTop L.δ)) (C.into_arrow _)
    (C.step hij.le) (C.step_arrow _) xj hXA h75
  refine infra_711_tiedFree_transport rfl ?_ _ (C.into_arrow j) htr
  apply SystemArrow.ext; intro v; exact C.into_step _ v

end
end AEC
