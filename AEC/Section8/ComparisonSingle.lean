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

set_option maxHeartbeats 6400000 in
/-- **Lemma 8.2(5) for P.scheme, preservation direction (proved).** English: "comparisons
preserved and reflected from a common small level to a common larger level". For a stationary
prescription satisfying Definition 8.1 (commutes with isomorphisms; tied free extension along
arrows), on the tail `infra_615_closed`: marked arrows `f₁ : M₁ → N₁`, `f₂ : M₂ → N₂` (the `M`s
at one level, the `N`s at one larger level) carry bounded lists in the same pair orbit
(marks matched along `σ`) to lists in the same pair orbit (marks matched along
`f₁.markMap⁻¹ ∘ σ ∘ f₂.markMap`). Proof as for clause (4): bounded diagram homogeneity across the
two pairs, mark transport (`infra_82_mark_transport_cross_single`), mixed over-`B` isolation
(`infra_72_mixed_level_closed`; the `N` level is recursion closed on this tail), and the pair
isomorphism test (clause 3). -/
theorem infra_82_comparison_preservation_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) (hiso : Pr.CommutesWithIso)
    (hTA : Pr.TiedAlong) :
    ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∀ (M₁ M₂ N₁ N₂ : MarkedPair K oneVertexShape P.scheme Pr)
        (f₁ : MarkedArrow K oneVertexShape P.scheme Pr M₁ N₁)
        (f₂ : MarkedArrow K oneVertexShape P.scheme Pr M₂ N₂),
        M₁.μ ∈ T → M₁.μ = M₂.μ → N₁.μ ∈ T → N₁.μ = N₂.μ → M₁.μ < N₁.μ →
        ∀ {ι : Type u} (t₁ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M₁.hμ M₁.Y))
          (t₂ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M₂.hμ M₂.Y)), #ι < M₁.μ →
          ∀ σ : M₁.bIdx ≃ M₂.bIdx,
          PairOrbitEq M₁ M₂ σ t₁ t₂ →
            PairOrbitEq N₁ N₂ (f₁.markMap.symm.trans (σ.trans f₂.markMap))
              (fun i => f₁.onY.mapOcc (t₁ i)) (fun i => f₂.onY.mapOcc (t₂ i)) := by
  classical
  refine ⟨infra_615_closed P, infra_615_tail P,
    fun M₁ M₂ N₁ N₂ f₁ f₂ hM hMM hNT hNN hlt ι t₁ t₂ hι σ hO => ?_⟩
  obtain ⟨α, hασ, -, -, hαt⟩ := hO
  subst hασ
  obtain ⟨γ, Z, hγ, HZ⟩ := M₁.dominated ι t₁ hι
  have hγ₂ : #γ < M₂.μ := hMM ▸ hγ
  have hγN : #γ < N₁.μ := hγ.trans hlt
  obtain ⟨e, hbij, he⟩ := infra_82_base_homogeneity_cross_single hNN f₁ f₂ α Z hγ hγ₂ hγN
  have hfinB : Finite M₁.bIdx :=
    Finite.of_equiv _ (M₁.realEq.trans (Pr.arity M₁.hμ M₁.X)).symm
  have hμ0 : ℵ₀ < M₁.μ := P.aleph0_lt M₁.hμ
  have hBlt : #M₁.bIdx < M₁.μ := (Cardinal.lt_aleph0_of_finite M₁.bIdx).trans hμ0
  have hbι : #(M₁.bIdx ⊕ ι) < M₁.μ := by
    simp only [mk_sum, lift_id]
    exact add_lt_of_lt (P.aleph0_le M₁.hμ) hBlt hι
  have hbιγ : #((M₁.bIdx ⊕ ι) ⊕ γ) < M₁.μ := by
    simp only [mk_sum, lift_id] at hbι ⊢
    exact add_lt_of_lt (P.aleph0_le M₁.hμ) hbι hγ
  have hD := infra_82_orbit_diagram_cross_single f₁ f₂ α t₁ t₂ hαt Z hbιγ (hMM ▸ hbιγ)
    (hbιγ.trans hlt) (hNN ▸ hbιγ.trans hlt)
  have hExt := infra_82_marked_arrow_ext_single f₁ t₁
  have hMrec0 : M₁.μ ∈ recursionClosedLevels P ℵ₀ :=
    ⟨hM.1, fun β₀ hβ => hM.2 ℵ₀ le_rfl hμ0 β₀ hβ⟩
  have hNrec0 : N₁.μ ∈ recursionClosedLevels P ℵ₀ :=
    ⟨hNT.1, fun β₀ hβ => hNT.2 ℵ₀ le_rfl (hμ0.trans hlt) β₀ hβ⟩
  have hMk := infra_82_mark_transport_cross_single hiso hTA f₁ f₂ α hNN hlt.le hMrec0 hNrec0 e
    hbij
  have hTied := infra_82_mark_tied_along_mixed hTA f₁ hlt.le
  have hιN : #ι < N₁.μ := hι.trans hlt
  let κ : Cardinal.{u} := max (#(M₁.bIdx ⊕ ι)) ℵ₀
  have hκ : ℵ₀ ≤ κ := le_max_right _ _
  have hκμ : κ < M₁.μ := max_lt hbι hμ0
  have hrec : M₁.μ ∈ recursionClosedLevels P κ :=
    ⟨hM.1, fun β₀ hβ => hM.2 κ hκ hκμ β₀ hβ⟩
  have hrecN : N₁.μ ∈ recursionClosedLevels P κ :=
    ⟨hNT.1, fun β₀ hβ => hNT.2 κ hκ (hκμ.trans hlt) β₀ hβ⟩
  have hκSucc : Order.succ κ ≤ M₁.μ := Order.succ_le_of_lt hκμ
  have hidx : #(M₁.bIdx ⊕ ι) ≤ κ := le_max_left _ _
  -- the pair-isomorphism test at the `N`s
  refine (fun H => ?_) (infra_82_pointed_all P Pr N₁ N₂ e hbij trivial
    (f₁.markMap.symm.trans (α.markMap.trans f₂.markMap))
    (fun i => f₁.onY.mapOcc (t₁ i)) (fun i => f₂.onY.mapOcc (t₂ i)) hιN)
  suffices hG : ∃ (ρ : Cardinal.{u}) (hρ : ρ ∈ P.scheme.eligible) (top : P.scheme.Object ρ hρ)
      (g1 : SystemArrow K oneVertexShape (P.scheme.asSystem N₁.hμ N₁.Y)
        (P.scheme.asSystem hρ top))
      (g2 : SystemArrow K oneVertexShape (P.scheme.asSystem N₂.hμ N₂.Y)
        (P.scheme.asSystem hρ top)),
      (∀ v, (g1.onVertex v).comp (N₁.incl.onVertex v) =
        (g2.onVertex v).comp ((SystemArrow.comp e N₂.incl).onVertex v)) ∧
      (∀ k, g1.mapOcc (N₁.b (f₁.markMap k)) = g2.mapOcc (N₂.b (f₂.markMap (α.markMap k)))) ∧
      (∀ i, g1.mapOcc (f₁.onY.mapOcc (t₁ i)) = g2.mapOcc (f₂.onY.mapOcc (t₂ i))) by
    obtain ⟨ρ, hρ, top, g1, g2, hc, hvb, hvt⟩ := hG
    have hbase : ∀ i (x : Occurrence K oneVertexShape (P.scheme.asSystem N₁.hμ N₁.X)),
        f₁.onY.mapOcc (t₁ i) = N₁.incl.mapOcc x →
          f₂.onY.mapOcc (t₂ i) = N₂.incl.mapOcc (e.mapOcc x) := by
      intro i x hx
      apply infra_82_mapOcc_injective g2
      rw [← hvt i, hx]
      exact congrArg (Sigma.mk x.1) (DFunLike.congr_fun (hc x.1) x.2)
    have hsgt : SameGaloisType
        (asTuple N₁.incl N₁.incl_arrow (Sum.elim (fun i => f₁.onY.mapOcc (t₁ i)) N₁.b))
        (markedJointOver N₁ N₂ e trivial (f₁.markMap.symm.trans (α.markMap.trans f₂.markMap))
          (fun i => f₂.onY.mapOcc (t₂ i)))
        (Equiv.refl _) (Equiv.refl _) := by
      refine ⟨ρ, hρ, top, g1, g2, trivial, trivial, hc, fun i => ?_⟩
      rcases i with i | j
      · exact hvt i
      · have h := hvb (f₁.markMap.symm j)
        rw [Equiv.apply_symm_apply] at h
        exact h
    obtain ⟨arr, hX, hσ', hY, hmap⟩ := H.mpr ⟨hbase, hsgt⟩
    exact ⟨arr, hσ', fun v => by rw [hX]; exact hbij v, hY, hmap⟩
  -- mixed over-`B` isolation
  have hW := infra_72_mixed_level_closed P κ hκ M₁.hμ N₁.hμ hlt.le hrec hκSucc hrecN f₁.onX
    trivial (asTuple M₁.incl M₁.incl_arrow (seqJoint M₁.b t₁))
    (asTuple N₁.incl N₁.incl_arrow (seqJoint N₁.b (fun i => f₁.onY.mapOcc (t₁ i))))
    (Equiv.sumCongr f₁.markMap (Equiv.refl ι)) (Equiv.refl _) rfl rfl hidx hbι Z ⟨hγ, HZ⟩
    hExt hTied
  let q' : TupleOver K oneVertexShape P.scheme N₁.hμ N₁.X :=
    ⟨N₂.μ, N₂.hμ, N₂.Y, SystemArrow.comp e N₂.incl, trivial, M₁.bIdx ⊕ ι,
      seqJoint (fun k => N₂.b (f₂.markMap (α.markMap k))) (fun i => f₂.onY.mapOcc (t₂ i))⟩
  have hmarg : SameGaloisType
      ((asTuple N₁.incl N₁.incl_arrow (seqJoint N₁.b (fun i => f₁.onY.mapOcc (t₁ i)))).marginal
        ((Equiv.sumCongr f₁.markMap (Equiv.refl ι)).symm.trans (Equiv.refl _)))
      (q'.marginal (Equiv.refl _)) (Equiv.refl _) (Equiv.refl _) := by
    rcases hMk with ⟨ρ, hρ, top, g1, g2, h1, h2, hc, hv⟩
    exact ⟨ρ, hρ, top, g1, g2, h1, h2, hc, fun k => hv k⟩
  have hdiag : P.scheme.DiagramEq (X := N₁.Y) (Y := q'.host)
      (alignJoint ((Equiv.sumCongr f₁.markMap (Equiv.refl ι)).symm.trans (Equiv.refl _))
        (typeJoint (p := asTuple N₁.incl N₁.incl_arrow
          (seqJoint N₁.b (fun i => f₁.onY.mapOcc (t₁ i)))) (pushParams f₁.onX Z)))
      (alignJoint (Equiv.refl _) (typeJoint (p := q') (pushParams f₁.onX Z))) := by
    refine infra_73_diagramEq_of_eq hD ?_ ?_
    · intro x; rcases x with (k | i) | j <;> rfl
    · intro x
      rcases x with (k | i) | j
      · rfl
      · rfl
      · exact (congrArg N₂.incl.mapOcc (he j)).symm
  obtain ⟨ρ, hρ, top, g1, g2, -, -, hc, hv⟩ := hW.2 q' _ hNN.symm hmarg hdiag
  exact ⟨ρ, hρ, top, g1, g2, hc, fun k => hv (Sum.inl k), fun i => hv (Sum.inr i)⟩

end
end AEC
