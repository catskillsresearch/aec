module

public import AEC.Section8.TiedAlong

@[expose] public section

/-!
# Lemma 8.2(5) for P.scheme: comparisons from a small level to a larger level

Cycle 98. Inputs for the preservation direction of Lemma 8.2(5) ("comparisons preserved and
reflected from a common small level to a common larger level"): composition of marked arrows, and
transport of the mark type between two pairs at the larger level along a base isomorphism.
-/

namespace AEC
section

universe u
open Cardinal Classical FirstOrder Function
variable {K : AbstractElementaryClass.{u}}

/-- Composition of marked arrows (P.scheme). -/
noncomputable def infra_82_markedComp {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {M₁ M₂ N : MarkedPair K oneVertexShape P.scheme Pr}
    (α : MarkedArrow K oneVertexShape P.scheme Pr M₁ M₂)
    (f : MarkedArrow K oneVertexShape P.scheme Pr M₂ N) :
    MarkedArrow K oneVertexShape P.scheme Pr M₁ N where
  onX := SystemArrow.comp α.onX f.onX
  onY := SystemArrow.comp α.onY f.onY
  onX_arrow := trivial
  onY_arrow := trivial
  comm := by
    rw [← SystemArrow.comp_assoc, α.comm, SystemArrow.comp_assoc, f.comm,
      ← SystemArrow.comp_assoc]
  markMap := α.markMap.trans f.markMap
  preserves_mark i := by
    have h1' : α.onY.mapOcc (M₁.b i) = M₂.b (α.markMap i) := α.preserves_mark i
    have h2' : f.onY.mapOcc (M₂.b (α.markMap i)) = N.b (f.markMap (α.markMap i)) :=
      f.preserves_mark (α.markMap i)
    exact (congrArg f.onY.mapOcc h1').trans h2'

set_option maxHeartbeats 1600000 in
/-- **Mark transport between two pairs at a larger level (P.scheme; toward 8.2(5)).** Marked
arrows `f₁ : M₁ → N₁`, `f₂ : M₂ → N₂` and `α : M₁ → M₂`, the `M`s at one level and the `N`s at one
larger level, both recursion closed at `ℵ₀`, and a structural isomorphism `e : N₁.X ≅ N₂.X`:
the image of `M₁`'s mark in `N₁` along `f₁` and the image of `M₁`'s mark in `N₂` along `f₂ ∘ α`,
read back along `e`, have the same type over `N₁.X`, position by position. -/
theorem infra_82_mark_transport_cross_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme} (hiso : Pr.CommutesWithIso)
    (hTA : Pr.TiedAlong) {M₁ M₂ N₁ N₂ : MarkedPair K oneVertexShape P.scheme Pr}
    (f₁ : MarkedArrow K oneVertexShape P.scheme Pr M₁ N₁)
    (f₂ : MarkedArrow K oneVertexShape P.scheme Pr M₂ N₂)
    (α : MarkedArrow K oneVertexShape P.scheme Pr M₁ M₂) (hN : N₁.μ = N₂.μ)
    (hlev : M₁.μ ≤ N₁.μ) (hMrec : M₁.μ ∈ recursionClosedLevels P ℵ₀)
    (hNrec : N₁.μ ∈ recursionClosedLevels P ℵ₀)
    (e : SystemArrow K oneVertexShape (P.scheme.asSystem N₁.hμ N₁.X)
      (P.scheme.asSystem N₂.hμ N₂.X))
    (hbij : ∀ v, Function.Bijective (e.onVertex v)) :
    SameGaloisType (infra_82_markImage f₁)
      ((infra_82_markImage (infra_82_markedComp α f₂)).restrict e trivial)
      (Equiv.refl _) (Equiv.refl _) := by
  classical
  have hlev₂ : M₁.μ ≤ N₂.μ := hN ▸ hlev
  have hNrec₂ : N₂.μ ∈ recursionClosedLevels P ℵ₀ := hN ▸ hNrec
  have B1 := infra_82_mark_positional_mixed hTA f₁ hlev hMrec hNrec
  have Bg := infra_82_mark_positional_mixed hTA (infra_82_markedComp α f₂) hlev₂ hMrec hNrec₂
  have Bg' := infra_82_sgt_restrict e trivial Bg
  have I := infra_82_mark_type_iso_single hiso N₁ N₂ hN e hbij
  have hμ0 : ℵ₀ < N₁.μ := P.aleph0_lt N₁.hμ
  have hfinB : Finite M₁.bIdx :=
    Finite.of_equiv _ (M₁.realEq.trans (Pr.arity M₁.hμ M₁.X)).symm
  have hfinN : Finite N₁.bIdx :=
    Finite.of_equiv _ (N₁.realEq.trans (Pr.arity N₁.hμ N₁.X)).symm
  have hidx1 : #(infra_82_markImage f₁).idx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite M₁.bIdx).le
  have s1 := infra_612_galois_trans_last_base (infra_73_sgt_uncommon B1)
    (SameGaloisType.swap_refl I) ℵ₀ le_rfl hμ0 hidx1 hN.symm
  have s2 := infra_612_galois_trans_last_base s1
    (SameGaloisType.swap_refl (infra_73_sgt_uncommon (SameGaloisType.symm Bg')))
    ℵ₀ le_rfl hμ0 hidx1 hN.symm
  have hE : ((((Equiv.refl M₁.bIdx).symm.trans
      ((M₁.realEq.trans ((Pr.arity M₁.hμ M₁.X).trans (Pr.arity N₁.hμ N₁.X).symm)).trans
        N₁.realEq.symm).symm.symm).trans
      (N₁.realEq.trans (((Pr.arity N₁.hμ N₁.X).trans (Pr.arity N₂.hμ N₂.X).symm).trans
        N₂.realEq.symm)).symm.symm).trans
      ((((M₁.realEq.trans ((Pr.arity M₁.hμ M₁.X).trans (Pr.arity N₂.hμ N₂.X).symm)).trans
        N₂.realEq.symm).symm.trans (Equiv.refl M₁.bIdx).symm.symm).symm).symm) =
      Equiv.refl M₁.bIdx := by
    ext k
    simp
  exact cast (congrArg (fun E => SameGaloisType (infra_82_markImage f₁)
    ((infra_82_markImage (infra_82_markedComp α f₂)).restrict e trivial) E
      (Equiv.refl _)) hE) s2

end
end AEC
