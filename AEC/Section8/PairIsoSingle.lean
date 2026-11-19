module

public import AEC.Section8.MarkedPairExists
public import AEC.Section7.Results

@[expose] public section

/-!
# Lemma 8.2, clause (2), for the Prop 5.6 scheme (`infra_82_iso_single`, cycle 95)

English (Lemma 8.2): "An isomorphism e : X ≅ X′ extends to an isomorphism (X, Y, b) ≅ (X′, Y′, b′)."
For `SingleModelData`: a bijective base arrow has an inverse arrow (`infra_82_inverse_arrow`,
via AEC coherence); all-domination transfers along the base isomorphism and the mark
reindexing (`infra_82_isolated_base_iso`, `infra_82_isolated_reindex_mark`, both two-sided, no
one-way diagram restriction converse); Proposition 7.5(2) then gives the structural isomorphism.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

theorem infra_82_systemArrow_ext {S : SystemShape.{u}} {X Y : SystemObject K S}
    {f1 f2 : SystemArrow K S X Y} (h : ∀ v x, f1.onVertex v x = f2.onVertex v x) : f1 = f2 := by
  obtain ⟨o1, s1, c1⟩ := f1
  obtain ⟨o2, s2, c2⟩ := f2
  have : o1 = o2 := funext fun v => FirstOrder.Language.Embedding.ext fun x => h v x
  subst this
  rfl

theorem infra_82_restrict_incl_eq {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}
    {q1 q2 : TupleOver K oneVertexShape P.scheme hμ A} (hν : q1.ν = q2.ν)
    (hhost : HEq q1.host q2.host) (hincl : HEq q1.incl q2.incl) (hidx : q1.idx = q2.idx)
    (hval : HEq q1.val q2.val) : q1 = q2 := by
  obtain ⟨ν1, h1, H1, i1, a1, x1, v1⟩ := q1
  obtain ⟨ν2, h2, H2, i2, a2, x2, v2⟩ := q2
  simp only at hν hhost hincl hidx hval
  subst hν hidx
  cases hhost; cases hincl; cases hval
  rfl


/-- Relative isolation transfers along a base isomorphism (two-sided inverse `g`). -/
theorem infra_82_isolated_base_iso {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A B : P.scheme.Object μ hμ}
    (e : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ B) (P.scheme.asSystem hμ A))
    (heg : ∀ v x, e.onVertex v (g.onVertex v x) = x)
    (hge : ∀ v x, g.onVertex v (e.onVertex v x) = x)
    (q₀ : TupleOver K oneVertexShape P.scheme hμ B) {uIdx cIdx : Type u}
    (eq : q₀.idx ≃ uIdx ⊕ cIdx) (h : IsRelativelyIsolated q₀ eq) :
    IsRelativelyIsolated (q₀.restrict e trivial) eq := by
  obtain ⟨ι, Z, hι, H⟩ := h
  refine ⟨ι, fun i => g.mapOcc (Z i), hι, fun q' e' hν hmarg hdiag => ?_⟩
  have h1 : SameGaloisType (q₀.marginal eq) ((q'.restrict g trivial).marginal e')
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
    rcases infra_82_sameGalois_restrict g trivial hmarg with
      ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, fun v => ?_, hv⟩
    apply FirstOrder.Language.Embedding.ext
    intro y
    have := congrArg (fun φ => φ y) (hc v)
    simp only [FirstOrder.Language.Embedding.comp_apply] at this ⊢
    refine Eq.trans ?_ this
    show f1.onVertex v (q₀.incl.onVertex v y) =
      f1.onVertex v (q₀.incl.onVertex v (e.onVertex v (g.onVertex v y)))
    rw [heg]
  have hJ : typeJoint (p := q₀.restrict e trivial) (fun i => g.mapOcc (Z i)) =
      typeJoint (p := q₀) Z := by
    funext k
    rcases k with i | j
    · rfl
    · show (⟨(Z j).1, q₀.incl.onVertex (Z j).1 (e.onVertex (Z j).1 (g.onVertex (Z j).1 (Z j).2))⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem q₀.hν q₀.host)) = _
      rw [heg]
      rfl
  have h2 : P.scheme.DiagramEq (X := q₀.host) (Y := (q'.restrict g trivial).host)
      (alignJoint eq (typeJoint (p := q₀) Z))
      (alignJoint e' (typeJoint (p := q'.restrict g trivial) Z)) := by
    rw [← hJ]
    exact hdiag
  have h3 := infra_82_sameGalois_restrict e trivial (H (q'.restrict g trivial) e' hν h1 h2)
  rcases h3 with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, fun v => ?_, hv⟩
  apply FirstOrder.Language.Embedding.ext
  intro y
  have := congrArg (fun φ => φ y) (hc v)
  simp only [FirstOrder.Language.Embedding.comp_apply] at this ⊢
  refine this.trans ?_
  show f2.onVertex v (q'.incl.onVertex v (g.onVertex v (e.onVertex v y))) =
    f2.onVertex v (q'.incl.onVertex v y)
  rw [hge]


/-- Relative isolation of `(b, c)` transfers to the reindexed mark `(b ∘ τ, c)`. -/
theorem infra_82_isolated_reindex_mark {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    {α β γ : Type u} (τ : α ≃ β) (b : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (c : γ → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (h : IsRelativelyIsolated (uIdx := β) (cIdx := γ) (asTuple incl trivial (seqJoint b c))
      (Equiv.refl (β ⊕ γ))) :
    IsRelativelyIsolated (uIdx := α) (cIdx := γ)
      (asTuple incl trivial (seqJoint (fun a => b (τ a)) c)) (Equiv.refl (α ⊕ γ)) := by
  obtain ⟨ι, Z, hι, H⟩ := h
  refine ⟨ι, Z, hι, fun q' e' hν hm hd => ?_⟩
  have hm' : SameGaloisType ((asTuple incl trivial (seqJoint b c)).marginal (Equiv.refl _))
      (q'.marginal (e'.trans (Equiv.sumCongr τ (Equiv.refl γ)))) (Equiv.refl β) (Equiv.refl β) := by
    rcases hm with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun j => ?_⟩
    obtain ⟨a, rfl⟩ := τ.surjective j
    have h1 := hv a
    have hs : (Equiv.sumCongr τ (Equiv.refl γ)).symm (Sum.inl (τ a)) = Sum.inl a := by
      simp [Equiv.sumCongr_symm]
    show (⟨(b (τ a)).1, f1.onVertex _ (b (τ a)).2⟩ : Occurrence K oneVertexShape _) =
      ⟨(q'.val (e'.symm ((Equiv.sumCongr τ (Equiv.refl γ)).symm (Sum.inl (τ a))))).1,
        f2.onVertex _ (q'.val (e'.symm ((Equiv.sumCongr τ (Equiv.refl γ)).symm (Sum.inl (τ a))))).2⟩
    rw [hs]
    exact h1
  have hd' : P.scheme.DiagramEq (X := Y) (Y := q'.host)
      (alignJoint (Equiv.refl _) (typeJoint (p := asTuple incl trivial (seqJoint b c)) Z))
      (alignJoint (e'.trans (Equiv.sumCongr τ (Equiv.refl γ))) (typeJoint (p := q') Z)) := by
    have hX := (P.scheme.diagram_reindex _ _
      (Equiv.sumCongr (Equiv.sumCongr τ (Equiv.refl γ)) (Equiv.refl ι)) _ _).1 hd
    have e1 : (fun x => alignJoint (Equiv.refl (α ⊕ γ))
        (typeJoint (p := asTuple incl trivial (seqJoint (fun a => b (τ a)) c)) Z)
        ((Equiv.sumCongr (Equiv.sumCongr τ (Equiv.refl γ)) (Equiv.refl ι)).symm x)) =
        alignJoint (Equiv.refl _) (typeJoint (p := asTuple incl trivial (seqJoint b c)) Z) := by
      funext x
      rcases x with (j | k) | i
      · simp [alignJoint, typeJoint, asTuple, seqJoint, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl]; rfl
      · simp [alignJoint, typeJoint, asTuple, seqJoint, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl]; rfl
      · simp [alignJoint, typeJoint, asTuple, seqJoint, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl]; rfl
    have e2 : (fun x => alignJoint e' (typeJoint (p := q') Z)
        ((Equiv.sumCongr (Equiv.sumCongr τ (Equiv.refl γ)) (Equiv.refl ι)).symm x)) =
        alignJoint (e'.trans (Equiv.sumCongr τ (Equiv.refl γ))) (typeJoint (p := q') Z) := by
      funext x
      rcases x with (j | k) | i
      · simp [alignJoint, typeJoint, Equiv.sumCongr_symm, Equiv.sumCongr_apply]
      · simp [alignJoint, typeJoint, Equiv.sumCongr_symm, Equiv.sumCongr_apply]
      · simp [alignJoint, typeJoint, Equiv.sumCongr_symm, Equiv.sumCongr_apply]
    have key : ∀ {α : Type u} (xs xs' : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
        (ys ys' : α → Occurrence K oneVertexShape (P.scheme.asSystem q'.hν q'.host)),
        xs = xs' → ys = ys' →
        P.scheme.DiagramEq (X := Y) (Y := q'.host) xs ys →
        P.scheme.DiagramEq (X := Y) (Y := q'.host) xs' ys' := by
      intro _ _ _ _ _ h1 h2 h; subst h1 h2; exact h
    exact key _ _ _ _ e1 e2 hX
  have H2 := H q' (e'.trans (Equiv.sumCongr τ (Equiv.refl γ))) hν hm' hd'
  rcases H2 with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun j => ?_⟩
  have hs : ∀ j, (Equiv.sumCongr τ (Equiv.refl γ)).symm ((Equiv.sumCongr τ (Equiv.refl γ)) j) = j :=
    fun j => Equiv.symm_apply_apply _ j
  have hs2 : ∀ j, (e'.trans (Equiv.sumCongr τ (Equiv.refl γ))).symm
      ((Equiv.sumCongr τ (Equiv.refl γ)) j) = e'.symm j := fun j => by
    rw [Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  have h1 := hv ((Equiv.sumCongr τ (Equiv.refl γ)) j)
  rcases j with a | k
  · show (⟨(b (τ a)).1, f1.onVertex _ (b (τ a)).2⟩ : Occurrence K oneVertexShape _) =
      ⟨(q'.val (e'.symm (Sum.inl a))).1, f2.onVertex _ (q'.val (e'.symm (Sum.inl a))).2⟩
    have h2 := h1
    erw [hs2] at h2
    exact h2
  · show (⟨(c k).1, f1.onVertex _ (c k).2⟩ : Occurrence K oneVertexShape _) =
      ⟨(q'.val (e'.symm (Sum.inr k))).1, f2.onVertex _ (q'.val (e'.symm (Sum.inr k))).2⟩
    have h2 := h1
    erw [hs2] at h2
    exact h2


/-- A vertexwise bijective arrow of one-vertex systems has a two-sided inverse arrow. -/
theorem infra_82_inverse_arrow {X Y : SystemObject K oneVertexShape}
    (e : SystemArrow K oneVertexShape X Y) (hbij : ∀ v, Function.Bijective (e.onVertex v)) :
    ∃ g : SystemArrow K oneVertexShape Y X,
      (∀ v x, e.onVertex v (g.onVertex v x) = x) ∧ (∀ v x, g.onVertex v (e.onVertex v x) = x) := by
  classical
  let E : ∀ v, (X.obj v).carrier ≃[K.τ] (Y.obj v).carrier := fun v =>
    { toEquiv := Equiv.ofBijective _ (hbij v)
      map_fun' := fun φ x => (e.onVertex v).map_fun φ x
      map_rel' := fun r x => (e.onVertex v).map_rel r x }
  have hEg : ∀ v, (e.onVertex v).comp (E v).symm.toEmbedding =
      FirstOrder.Language.Embedding.refl K.τ (Y.obj v).carrier := fun v => by
    ext y
    exact (E v).apply_symm_apply y
  refine ⟨⟨fun v => (E v).symm.toEmbedding, fun v => K.coherence _ _ (e.onVertex v)
    (K.strong_refl _ (Y.inK v)) (e.onVertex_strong v) (hEg v), fun h => h.elim⟩,
    fun v x => (E v).apply_symm_apply x, fun v x => (E v).symm_apply_apply x⟩


/-- **Lemma 8.2, clause (2), for the Prop 5.6 scheme.** On the Proposition 7.5 tail, a bijective
base arrow `e : M.X → N.X` extends to an isomorphism of marked pairs (`onX = e`, `onY` vertexwise
bijective). -/
theorem infra_82_iso_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∀ (M N : MarkedPair K oneVertexShape P.scheme Pr)
        (e : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.X)
          (P.scheme.asSystem N.hμ N.X)),
        M.μ ∈ T → N.μ ∈ T →
        (∀ v, Function.Bijective (e.onVertex v)) →
        P.scheme.permitted (X := M.X) (Y := N.X) e →
        ∃ arr : MarkedArrow K oneVertexShape P.scheme Pr M N, arr.onX = e ∧
          ∀ v, Function.Bijective (arr.onY.onVertex v) := by
  classical
  obtain ⟨T, hT, H⟩ := proposition_7_5 P ℵ₀ le_rfl
  refine ⟨T, hT, fun M N e hMT _ hbij he => ?_⟩
  have hlev : M.μ = N.μ := by
    have h1 : #M.X.model.carrier = M.μ := M.X.card
    have h2 : #N.X.model.carrier = N.μ := N.X.card
    rw [← h1, ← h2]
    exact Cardinal.mk_congr (Equiv.ofBijective _ (hbij PUnit.unit))
  obtain ⟨μ, hμ, X, Y, incl, hincl, bIdx, b, eM, hM, hdom⟩ := M
  obtain ⟨μ', hμ', X', Y', incl', hincl', bIdx', b', eN, hN, hdom'⟩ := N
  simp only at hlev e he hbij hMT ⊢
  subst hlev
  obtain ⟨e0, hFL, -⟩ := Pr.along e he
  have hN' := infra_82_sameGalois_restrict e he hN
  have hlt : ℵ₀ < μ := P.aleph0_lt hμ
  have hfinX : Finite (Pr.assign hμ X).idx := Finite.of_equiv _ (Pr.arity hμ X).symm
  have hidxX : #(Pr.assign hμ X).idx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite _).le
  have S1 := infra_612_galois_trans_last_base (t1 := Pr.assign hμ X)
    (t2 := (Pr.assign hμ X').restrict e he)
    (t3 := (asTuple incl' hincl' b').restrict e he) (e12 := e0) (e32 := eN)
    hFL hN'.symm ℵ₀ le_rfl hlt hidxX rfl
  have hfinB : Finite bIdx := Finite.of_equiv _ (eM.trans (Pr.arity hμ X)).symm
  have hidxB : #bIdx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite _).le
  have S2 := infra_612_galois_trans_last_base (t1 := asTuple incl hincl b)
    (t2 := Pr.assign hμ X) (t3 := (asTuple incl' hincl' b').restrict e he) (e12 := eM)
    hM (SameGaloisType.swap_refl S1) ℵ₀ le_rfl hlt hidxB rfl
  set τ : bIdx ≃ bIdx' := eM.trans (e0.trans eN.symm).symm.symm with hτ
  have hg : P.scheme.permitted (X := X) (Y := Y') (SystemArrow.comp e incl') :=
    P.scheme.comp e incl' he hincl'
  have hGal : SameGaloisType (asTuple incl hincl b)
      (asTuple (SystemArrow.comp e incl') hg (fun j => b' (τ j))) (Equiv.refl _)
      (Equiv.refl _) := by
    rcases S2 with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, fun j => ?_⟩
    have := hval (τ j)
    erw [τ.symm_apply_apply j] at this
    exact this
  obtain ⟨g, heg, hge⟩ := infra_82_inverse_arrow e hbij
  have hdom2 : AllDominated (SystemArrow.comp e incl') hg bIdx (fun j => b' (τ j)) :=
    fun cIdx c hc => infra_82_isolated_base_iso e g heg hge _ _
      (infra_82_isolated_reindex_mark incl' τ b' c (hdom' cIdx c hc))
  have hBlt : #bIdx < μ := lt_of_le_of_lt hidxB hlt
  obtain ⟨φ, hφ, hcomp, hv⟩ :=
    (H μ hMT X Y incl hincl b hidxB hBlt hdom).2 Y' (SystemArrow.comp e incl') hg
      (fun j => b' (τ j)) hdom2 hGal
  refine ⟨⟨e, φ, he, trivial, hcomp, τ, fun i => ?_⟩, rfl,
    P.scheme.isStructIso_bijective _ _ φ hφ⟩
  show (⟨(b i).1, φ.onVertex (b i).1 (b i).2⟩ : Occurrence K oneVertexShape
    (P.scheme.asSystem hμ Y')) = b' (τ i)
  have h1 : φ.onVertex (b i).1 (b i).2 = (b' (τ i)).2 := hv i
  revert h1
  generalize b i = o1
  generalize b' (τ i) = o2
  obtain ⟨⟨⟩, x1⟩ := o1
  obtain ⟨⟨⟩, x2⟩ := o2
  intro h1
  exact congrArg (Sigma.mk PUnit.unit) h1

/-- **Lemma 8.2, clause (2), for the Prop 5.6 scheme, at every level.** On the Proposition 7.5 tail, a bijective
base arrow `e : M.X → N.X` extends to an isomorphism of marked pairs (`onX = e`, `onY` vertexwise
bijective). -/
theorem infra_82_iso_any (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
      ∀ (M N : MarkedPair K oneVertexShape P.scheme Pr)
        (e : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.X)
          (P.scheme.asSystem N.hμ N.X)),
        (∀ v, Function.Bijective (e.onVertex v)) →
        P.scheme.permitted (X := M.X) (Y := N.X) e →
        ∃ arr : MarkedArrow K oneVertexShape P.scheme Pr M N, arr.onX = e ∧
          ∀ v, Function.Bijective (arr.onY.onVertex v) := by
  classical
  intro M N e hbij he
  have hlev : M.μ = N.μ := by
    have h1 : #M.X.model.carrier = M.μ := M.X.card
    have h2 : #N.X.model.carrier = N.μ := N.X.card
    rw [← h1, ← h2]
    exact Cardinal.mk_congr (Equiv.ofBijective _ (hbij PUnit.unit))
  obtain ⟨μ, hμ, X, Y, incl, hincl, bIdx, b, eM, hM, hdom⟩ := M
  obtain ⟨μ', hμ', X', Y', incl', hincl', bIdx', b', eN, hN, hdom'⟩ := N
  simp only at hlev e he hbij ⊢
  subst hlev
  obtain ⟨e0, hFL, -⟩ := Pr.along e he
  have hN' := infra_82_sameGalois_restrict e he hN
  have hlt : ℵ₀ < μ := P.aleph0_lt hμ
  have hfinX : Finite (Pr.assign hμ X).idx := Finite.of_equiv _ (Pr.arity hμ X).symm
  have hidxX : #(Pr.assign hμ X).idx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite _).le
  have S1 := infra_612_galois_trans_last_base (t1 := Pr.assign hμ X)
    (t2 := (Pr.assign hμ X').restrict e he)
    (t3 := (asTuple incl' hincl' b').restrict e he) (e12 := e0) (e32 := eN)
    hFL hN'.symm ℵ₀ le_rfl hlt hidxX rfl
  have hfinB : Finite bIdx := Finite.of_equiv _ (eM.trans (Pr.arity hμ X)).symm
  have hidxB : #bIdx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite _).le
  have S2 := infra_612_galois_trans_last_base (t1 := asTuple incl hincl b)
    (t2 := Pr.assign hμ X) (t3 := (asTuple incl' hincl' b').restrict e he) (e12 := eM)
    hM (SameGaloisType.swap_refl S1) ℵ₀ le_rfl hlt hidxB rfl
  set τ : bIdx ≃ bIdx' := eM.trans (e0.trans eN.symm).symm.symm with hτ
  have hg : P.scheme.permitted (X := X) (Y := Y') (SystemArrow.comp e incl') :=
    P.scheme.comp e incl' he hincl'
  have hGal : SameGaloisType (asTuple incl hincl b)
      (asTuple (SystemArrow.comp e incl') hg (fun j => b' (τ j))) (Equiv.refl _)
      (Equiv.refl _) := by
    rcases S2 with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, fun j => ?_⟩
    have := hval (τ j)
    erw [τ.symm_apply_apply j] at this
    exact this
  obtain ⟨g, heg, hge⟩ := infra_82_inverse_arrow e hbij
  have hdom2 : AllDominated (SystemArrow.comp e incl') hg bIdx (fun j => b' (τ j)) :=
    fun cIdx c hc => infra_82_isolated_base_iso e g heg hge _ _
      (infra_82_isolated_reindex_mark incl' τ b' c (hdom' cIdx c hc))
  have hBlt : #bIdx < μ := lt_of_le_of_lt hidxB hlt
  obtain ⟨φ, hφ, hcomp, hv⟩ :=
    infra_75_iso hμ X Y Y' incl hincl (SystemArrow.comp e incl') hg b (fun j => b' (τ j)) hBlt
      hdom hdom2 hGal
  refine ⟨⟨e, φ, he, trivial, hcomp, τ, fun i => ?_⟩, rfl,
    P.scheme.isStructIso_bijective _ _ φ hφ⟩
  show (⟨(b i).1, φ.onVertex (b i).1 (b i).2⟩ : Occurrence K oneVertexShape
    (P.scheme.asSystem hμ Y')) = b' (τ i)
  have h1 : φ.onVertex (b i).1 (b i).2 = (b' (τ i)).2 := hv i
  revert h1
  generalize b i = o1
  generalize b' (τ i) = o2
  obtain ⟨⟨⟩, x1⟩ := o1
  obtain ⟨⟨⟩, x2⟩ := o2
  intro h1
  exact congrArg (Sigma.mk PUnit.unit) h1

end AEC
