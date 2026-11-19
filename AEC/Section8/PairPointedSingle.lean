module

public import AEC.Section8.PairIsoSingle
public import AEC.Section8.Results

@[expose] public section

/-!
# Lemma 8.2, clause (3), for the Prop 5.6 scheme (`infra_82_pointed_single`, cycle 95)

English (Lemma 8.2): "More precisely, for bounded tuples t and t′ in the respective pair
structures, such an extension can take t to t′ if and only if e takes the indicated base entries
to their counterparts and transports tp(t,b/X) to tp(t′,b′/X′)." Marks are matched by list
position (`MarkedArrow.markMap = σ`). One tail serves every length below the level: the iso
clause of Proposition 7.5 (`infra_75_iso`) holds at every eligible level for any tuple of length
below it, after all-domination is extended to `X + (t, b)` (`infra_82_allDominated_absorb`).
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- Relative isolation of `b` over `(t, c)` gives relative isolation of `(t, b)` over `c`. -/
theorem infra_82_isolated_absorb {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    {ι β γ : Type u} (t : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (c : γ → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (h : IsRelativelyIsolated (uIdx := β) (cIdx := ι ⊕ γ)
      (asTuple incl trivial (seqJoint b (seqJoint t c))) (Equiv.refl (β ⊕ (ι ⊕ γ)))) :
    IsRelativelyIsolated (uIdx := ι ⊕ β) (cIdx := γ)
      (asTuple incl trivial (seqJoint (Sum.elim t b) c)) (Equiv.refl ((ι ⊕ β) ⊕ γ)) := by
  obtain ⟨ι0, Z, hι, H⟩ := h
  refine ⟨ι0, Z, hι, fun q' e' hν hm hd => ?_⟩
  let A : (ι ⊕ β) ⊕ γ ≃ β ⊕ (ι ⊕ γ) :=
    (Equiv.sumCongr (Equiv.sumComm ι β) (Equiv.refl γ)).trans (Equiv.sumAssoc β ι γ)
  have hA1 : ∀ j, A.symm (Sum.inl j) = Sum.inl (Sum.inr j) := fun j => rfl
  have hm' : SameGaloisType
      ((asTuple incl trivial (seqJoint b (seqJoint t c))).marginal (Equiv.refl _))
      (q'.marginal (e'.trans A)) (Equiv.refl β) (Equiv.refl β) := by
    rcases hm with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun j => ?_⟩
    exact hv (Sum.inr j)
  have hd' : P.scheme.DiagramEq (X := Y) (Y := q'.host)
      (alignJoint (Equiv.refl _)
        (typeJoint (p := asTuple incl trivial (seqJoint b (seqJoint t c))) Z))
      (alignJoint (e'.trans A) (typeJoint (p := q') Z)) := by
    have hX := (P.scheme.diagram_reindex _ _ (Equiv.sumCongr A (Equiv.refl ι0)) _ _).1 hd
    have e1 : (fun x => alignJoint (Equiv.refl ((ι ⊕ β) ⊕ γ))
        (typeJoint (p := asTuple incl trivial (seqJoint (Sum.elim t b) c)) Z)
        ((Equiv.sumCongr A (Equiv.refl ι0)).symm x)) =
        alignJoint (Equiv.refl _)
          (typeJoint (p := asTuple incl trivial (seqJoint b (seqJoint t c))) Z) := by
      funext x
      rcases x with (j | (k | k)) | i <;> rfl
    have e2 : (fun x => alignJoint e' (typeJoint (p := q') Z)
        ((Equiv.sumCongr A (Equiv.refl ι0)).symm x)) =
        alignJoint (e'.trans A) (typeJoint (p := q') Z) := by
      funext x
      rcases x with (j | (k | k)) | i <;> rfl
    have key : ∀ {α : Type u} (xs xs' : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
        (ys ys' : α → Occurrence K oneVertexShape (P.scheme.asSystem q'.hν q'.host)),
        xs = xs' → ys = ys' →
        P.scheme.DiagramEq (X := Y) (Y := q'.host) xs ys →
        P.scheme.DiagramEq (X := Y) (Y := q'.host) xs' ys' := by
      intro _ _ _ _ _ h1 h2 h; subst h1 h2; exact h
    exact key _ _ _ _ e1 e2 hX
  have H2 := H q' (e'.trans A) hν hm' hd'
  rcases H2 with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun j => ?_⟩
  have hs2 : ∀ j, (e'.trans A).symm (A j) = e'.symm j := fun j => by
    rw [Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  have h1 := hv (A j)
  erw [hs2] at h1
  rcases j with (k | k) | k <;> exact h1

/-- All-domination over `X + b` gives all-domination over `X + (t, b)` for a bounded `t`. -/
theorem infra_82_allDominated_absorb {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    {ι β : Type u} (t : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (hdom : AllDominated incl trivial β b) (hι : #ι < μ) :
    AllDominated incl trivial (ι ⊕ β) (Sum.elim t b) := fun γ c hc =>
  infra_82_isolated_absorb incl t b c
    (hdom (ι ⊕ γ) (seqJoint t c) (infra_75_sum_lt (P.aleph0_le hμ) hι hc))

/-- **Lemma 8.2, clause (3) (pointed form), for the Prop 5.6 scheme.** On the Theorem 7.9 tail
(the tail of `infra_82_marked_pair_exists`), for a bijective base arrow `e`, a list-position
matching `σ` of the marks, and tuples `t`, `t′` of any length below the level: some isomorphism of
the marked pairs over `e` matching the marks along `σ` takes `t` to `t′` iff `e` matches the base
entries and transports `tp(t, b/X)` to `tp(t′, b′/X′)`. The length bound is uniform: every
`#ι < μ` on one tail (Proposition 7.5(2) at the level, `infra_75_iso`, needs no closure in the
tuple length). -/
theorem infra_82_pointed_all (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
      ∀ (M N : MarkedPair K oneVertexShape P.scheme Pr)
        (e : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.X)
          (P.scheme.asSystem N.hμ N.X)),
        (∀ v, Function.Bijective (e.onVertex v)) →
        ∀ (he : P.scheme.permitted (X := M.X) (Y := N.X) e) (σ : M.bIdx ≃ N.bIdx)
          {ι : Type u} (t : ι → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y))
          (t' : ι → Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y)), #ι < M.μ →
          ((∃ arr : MarkedArrow K oneVertexShape P.scheme Pr M N, arr.onX = e ∧
              arr.markMap = σ ∧ (∀ v, Function.Bijective (arr.onY.onVertex v)) ∧
              ∀ i, arr.onY.mapOcc (t i) = t' i) ↔
            ((∀ i (x : Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.X)),
                t i = M.incl.mapOcc x → t' i = N.incl.mapOcc (e.mapOcc x)) ∧
              SameGaloisType (asTuple M.incl M.incl_arrow (Sum.elim t M.b))
                (markedJointOver M N e he σ t') (Equiv.refl _) (Equiv.refl _))) := by
  classical
  intro M N e hbij he σ ι t t' hι
  refine ⟨?_, ?_⟩
  · rintro ⟨arr, hX, hσ, -, hmap⟩
    subst hX hσ
    have hcomm : ∀ v x, arr.onY.onVertex v (M.incl.onVertex v x) =
        N.incl.onVertex v (arr.onX.onVertex v x) := fun v x =>
      congrArg (fun f => SystemArrow.onVertex f v x) arr.comm
    refine ⟨fun i x hx => ?_, ?_⟩
    · rw [← hmap i, hx]
      exact congrArg (Sigma.mk x.1) (hcomm x.1 x.2)
    · refine ⟨N.μ, N.hμ, N.Y, arr.onY, SystemArrow.refl _, trivial, trivial, fun v => ?_,
        fun i => ?_⟩
      · apply FirstOrder.Language.Embedding.ext
        intro x
        exact hcomm v x
      · rcases i with i | j
        · exact hmap i
        · exact arr.preserves_mark j
  · rintro ⟨-, hGal⟩
    have hlev : M.μ = N.μ := by
      have h1 : #M.X.model.carrier = M.μ := M.X.card
      have h2 : #N.X.model.carrier = N.μ := N.X.card
      rw [← h1, ← h2]
      exact Cardinal.mk_congr (Equiv.ofBijective _ (hbij PUnit.unit))
    obtain ⟨μ, hμ, X, Y, incl, hincl, bIdx, b, hreal, hdom⟩ := M
    obtain ⟨μ', hμ', X', Y', incl', hincl', bIdx', b', hreal', hdom'⟩ := N
    simp only at hlev e he hbij σ t t' hι hGal ⊢
    subst hlev
    have hg : P.scheme.permitted (X := X) (Y := Y') (SystemArrow.comp e incl') :=
      P.scheme.comp e incl' he hincl'
    obtain ⟨g, heg, hge⟩ := infra_82_inverse_arrow e hbij
    have hAll : AllDominated incl hincl (ι ⊕ bIdx) (Sum.elim t b) :=
      infra_82_allDominated_absorb incl t b hdom hι
    have hAll₂ : AllDominated (SystemArrow.comp e incl') hg (ι ⊕ bIdx)
        (Sum.elim t' (fun j => b' (σ j))) := by
      have d1 := infra_82_allDominated_absorb incl' t' b' hdom' hι
      intro γ c hc
      have h1 := infra_82_isolated_reindex_mark incl' (Equiv.sumCongr (Equiv.refl ι) σ)
        (Sum.elim t' b') c (d1 γ c hc)
      have hf : (fun a => Sum.elim t' b' (Equiv.sumCongr (Equiv.refl ι) σ a)) =
          Sum.elim t' (fun j => b' (σ j)) := by
        funext a; rcases a with a | a <;> rfl
      rw [hf] at h1
      exact infra_82_isolated_base_iso e g heg hge _ _ h1
    have hBlt : #(ι ⊕ bIdx) < μ := by
      have hfinB : Finite bIdx := by
        obtain ⟨eM, -⟩ := hreal
        exact Finite.of_equiv _ (eM.trans (Pr.arity hμ X)).symm
      exact infra_75_sum_lt (P.aleph0_le hμ) hι
        ((Cardinal.lt_aleph0_of_finite _).trans_le (P.aleph0_le hμ))
    obtain ⟨φ, hφ, hcomp, hv⟩ := infra_75_iso hμ X Y Y' incl hincl
      (SystemArrow.comp e incl') hg (Sum.elim t b) (Sum.elim t' (fun j => b' (σ j))) hBlt
      hAll hAll₂ hGal
    have hocc : ∀ (o1 : Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
        (o2 : Occurrence K oneVertexShape (P.scheme.asSystem hμ Y')),
        φ.onVertex o1.1 o1.2 = o2.2 →
        (⟨o1.1, φ.onVertex o1.1 o1.2⟩ : Occurrence K oneVertexShape
          (P.scheme.asSystem hμ Y')) = o2 := by
      intro o1 o2
      obtain ⟨⟨⟩, x1⟩ := o1
      obtain ⟨⟨⟩, x2⟩ := o2
      intro h1
      exact congrArg (Sigma.mk PUnit.unit) h1
    refine ⟨⟨e, φ, he, trivial, hcomp, σ, fun j => hocc _ _ (hv (Sum.inr j))⟩, rfl, rfl,
      P.scheme.isStructIso_bijective _ _ φ hφ, fun i => hocc _ _ (hv (Sum.inl i))⟩

/-- **Lemma 8.2, clause (3) (pointed form), for the Prop 5.6 scheme** on the Theorem 7.9 tail
(`infra_82_pointed_all` holds at every level). -/
theorem infra_82_pointed_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∀ (M N : MarkedPair K oneVertexShape P.scheme Pr)
        (e : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.X)
          (P.scheme.asSystem N.hμ N.X)),
        M.μ ∈ T → N.μ ∈ T →
        (∀ v, Function.Bijective (e.onVertex v)) →
        ∀ (he : P.scheme.permitted (X := M.X) (Y := N.X) e) (σ : M.bIdx ≃ N.bIdx)
          {ι : Type u} (t : ι → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y))
          (t' : ι → Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y)), #ι < M.μ →
          ((∃ arr : MarkedArrow K oneVertexShape P.scheme Pr M N, arr.onX = e ∧
              arr.markMap = σ ∧ (∀ v, Function.Bijective (arr.onY.onVertex v)) ∧
              ∀ i, arr.onY.mapOcc (t i) = t' i) ↔
            ((∀ i (x : Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.X)),
                t i = M.incl.mapOcc x → t' i = N.incl.mapOcc (e.mapOcc x)) ∧
              SameGaloisType (asTuple M.incl M.incl_arrow (Sum.elim t M.b))
                (markedJointOver M N e he σ t') (Equiv.refl _) (Equiv.refl _))) := by
  obtain ⟨T, hT, -⟩ := infra_82_marked_pair_exists P Pr
  exact ⟨T, hT, fun M N e _ _ hbij he σ ι t t' hι =>
    infra_82_pointed_all P Pr M N e hbij he σ t t' hι⟩

end AEC
