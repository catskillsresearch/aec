module

public import AEC.Section8.PairPointedSingle

@[expose] public section

/-!
# Lemma 8.2, clause (4), for the Prop 5.6 scheme: reduction pieces (cycle 96)

English (Lemma 8.2): "Same-level arrows preserve bounded pair orbits." Pair orbits are pair
isomorphism orbits (Section 8.4: "Define comparison of bounded term patterns by their pair
isomorphism orbits at any eligible level"). The proof (paper lines 3010–3018) produces a base
automorphism matching bounded approximation lists "by bounded diagram homogeneity in C" and then
applies the pair isomorphism test (clause 3). This file proves the reduction: an automorphism of
the base that keeps the prescribed type of the mark (positionwise) and matches the diagram of a
bounded isolating fragment extends to a pair automorphism taking `s` to `s′`
(`infra_82_orbit_criterion_single`). Bounded diagram homogeneity for `P.scheme` is the
`diagram_iso` field (Definition 5.2(3): "At each level, two bounded lists have the same diagram
if and only if a structural isomorphism between their objects takes one list to the other").
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Lemma 8.2(4) reduction for the Prop 5.6 scheme.** On the clause-(3) tail, for a marked pair
`N` and a bounded tuple `s` of `N.Y`, there is a bounded isolating fragment `Z` of the base such
that every automorphism `e` of the base that (a) matches the base entries of `s` with those of
`s′`, (b) keeps the prescribed type of the mark positionwise, and (c) carries the diagram of
`(b, s, Z)` to that of `(b, s′, e Z)`, extends to a pair automorphism (marks fixed positionwise)
taking `s` to `s′`. -/
theorem infra_82_orbit_criterion_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∀ (N : MarkedPair K oneVertexShape P.scheme Pr), N.μ ∈ T →
      ∀ {ι : Type u} (s : ι → Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y)),
        #ι < N.μ →
        ∃ (γ : Type u) (Z : γ → Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.X)),
          #γ < N.μ ∧
          ∀ (e : SystemArrow K oneVertexShape (P.scheme.asSystem N.hμ N.X)
              (P.scheme.asSystem N.hμ N.X))
            (_he : P.scheme.permitted (X := N.X) (Y := N.X) e),
            (∀ v, Function.Bijective (e.onVertex v)) →
            ∀ s' : ι → Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y),
            (∀ i (x : Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.X)),
                s i = N.incl.mapOcc x → s' i = N.incl.mapOcc (e.mapOcc x)) →
            SameGaloisType (asTuple N.incl N.incl_arrow N.b)
              (⟨N.μ, N.hμ, N.Y, SystemArrow.comp e N.incl, trivial, N.bIdx, N.b⟩ :
                TupleOver K oneVertexShape P.scheme N.hμ N.X) (Equiv.refl _) (Equiv.refl _) →
            P.scheme.DiagramEq (X := N.Y) (Y := N.Y)
              (seqJoint (seqJoint N.b s) (fun j => N.incl.mapOcc (Z j)))
              (seqJoint (seqJoint N.b s') (fun j => N.incl.mapOcc (e.mapOcc (Z j)))) →
            ∃ arr : MarkedArrow K oneVertexShape P.scheme Pr N N, arr.onX = e ∧
              arr.markMap = Equiv.refl _ ∧ (∀ v, Function.Bijective (arr.onY.onVertex v)) ∧
              ∀ i, arr.onY.mapOcc (s i) = s' i := by
  obtain ⟨T, hT, H3⟩ := infra_82_pointed_single P Pr
  refine ⟨T, hT, fun N hN ι s hι => ?_⟩
  obtain ⟨γ, Z, hγ, HZ⟩ := N.dominated ι s hι
  refine ⟨γ, Z, hγ, fun e he hbij s' hbase hb hd => ?_⟩
  let q' : TupleOver K oneVertexShape P.scheme N.hμ N.X :=
    ⟨N.μ, N.hμ, N.Y, SystemArrow.comp e N.incl, trivial, N.bIdx ⊕ ι, seqJoint N.b s'⟩
  have hd' : P.scheme.DiagramEq (X := N.Y) (Y := q'.host)
      (alignJoint (Equiv.refl _)
        (typeJoint (p := asTuple N.incl N.incl_arrow (seqJoint N.b s)) Z))
      (alignJoint (Equiv.refl _) (typeJoint (p := q') Z)) := by
    have key : ∀ {α : Type u} (xs xs' ys ys' : α → Occurrence K oneVertexShape
        (P.scheme.asSystem N.hμ N.Y)), xs = xs' → ys = ys' →
        P.scheme.DiagramEq (X := N.Y) (Y := N.Y) xs ys →
        P.scheme.DiagramEq (X := N.Y) (Y := N.Y) xs' ys' := by
      intro _ _ _ _ _ h1 h2 h; subst h1 h2; exact h
    refine key _ _ _ _ ?_ ?_ hd
    · funext x; rcases x with (j | j) | j <;> rfl
    · funext x; rcases x with (j | j) | j <;> rfl
  have hm : SameGaloisType
      ((asTuple N.incl N.incl_arrow (seqJoint N.b s)).marginal (Equiv.refl _))
      (q'.marginal (Equiv.refl _)) (Equiv.refl _) (Equiv.refl _) := by
    rcases hb with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
    exact ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun j => hv j⟩
  have hG := HZ q' (Equiv.refl _) rfl hm hd'
  refine (H3 N N e hN hN hbij he (Equiv.refl _) s s' hι).mpr ⟨hbase, ?_⟩
  rcases hG with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun i => ?_⟩
  rcases i with i | j
  · exact hv (Sum.inr i)
  · exact hv (Sum.inl j)

/-- **Base automorphisms keep the mark's type (P.scheme).** If the prescription commutes with
isomorphisms (Definition 8.1), every structural automorphism `e` of the base of a marked pair keeps
`tp(b/X)` position by position. This is hypothesis (b) of `infra_82_orbit_criterion_single`. -/
theorem infra_82_mark_type_auto_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme} (hiso : Pr.CommutesWithIso)
    (N : MarkedPair K oneVertexShape P.scheme Pr)
    (e : SystemArrow K oneVertexShape (P.scheme.asSystem N.hμ N.X) (P.scheme.asSystem N.hμ N.X))
    (hbij : ∀ v, Function.Bijective (e.onVertex v)) :
    SameGaloisType (asTuple N.incl N.incl_arrow N.b)
      (⟨N.μ, N.hμ, N.Y, SystemArrow.comp e N.incl, trivial, N.bIdx, N.b⟩ :
        TupleOver K oneVertexShape P.scheme N.hμ N.X) (Equiv.refl _) (Equiv.refl _) := by
  obtain ⟨eb, hR⟩ := N.realizes
  have hk := hiso N.X N.X e trivial hbij
  have hκ : (Pr.arity N.hμ N.X).trans (Pr.arity N.hμ N.X).symm = Equiv.refl _ := by
    ext i; simp
  rw [hκ] at hk
  -- restrict the realization along `e`
  have hRe : SameGaloisType
      ((asTuple N.incl N.incl_arrow N.b).restrict e trivial)
      ((Pr.assign N.hμ N.X).restrict e trivial) eb (Equiv.refl _) := by
    rcases hR with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, fun v => ?_, hv⟩
    change (f1.onVertex v).comp ((N.incl.onVertex v).comp (e.onVertex v)) =
      (f2.onVertex v).comp (((Pr.assign N.hμ N.X).incl.onVertex v).comp (e.onVertex v))
    have h := congrArg (fun g => FirstOrder.Language.Embedding.comp g (e.onVertex v)) (hc v)
    simp only [FirstOrder.Language.Embedding.comp_assoc] at h ⊢
    exact h
  have hμ0 : ℵ₀ < N.μ := P.aleph0_lt N.hμ
  have hfinA : Finite (Pr.assign N.hμ N.X).idx := Finite.of_equiv _ (Pr.arity N.hμ N.X).symm
  have hfinB : Finite N.bIdx := Finite.of_equiv _ eb.symm
  have hA : #(Pr.assign N.hμ N.X).idx ≤ ℵ₀ :=
    (Cardinal.lt_aleph0_of_finite (Pr.assign N.hμ N.X).idx).le
  have hB : #N.bIdx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite N.bIdx).le
  -- assign → assign∘e → (b over X via e)
  have h24 := infra_612_galois_trans_last_base hk hRe.symm ℵ₀ le_rfl hμ0 hA rfl
  have h24' := SameGaloisType.swap_refl h24
  have h14 := infra_612_galois_trans_last_base hR h24' ℵ₀ le_rfl hμ0 hB rfl
  rcases h14 with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun i => ?_⟩
  have h := hv i
  have hidx : ∀ j : N.bIdx,
      (eb.trans ((Equiv.refl (Pr.assign N.hμ N.X).idx).trans eb.symm).symm.symm).symm j = j :=
    fun j => by simp
  erw [hidx i] at h
  exact h

/-- **Bounded diagram homogeneity in the base (P.scheme).** For a same-level marked arrow
`f : M → N` and a pair automorphism `α` of `M`, every bounded list `Z` of `M.X` gives an
automorphism `e` of `N.X` with `e (f Z) = f (α Z)`. English (Definition 5.2(3)): "At each level,
two bounded lists have the same diagram if and only if a structural isomorphism between their
objects takes one list to the other" (`diagram_iso`); the two lists have the same diagram by
preservation under the arrows `f.onX` and `α.onX` (`diagram_preserved`). -/
theorem infra_82_base_homogeneity_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    (M N : MarkedPair K oneVertexShape P.scheme Pr) (hlev : M.μ = N.μ)
    (f : MarkedArrow K oneVertexShape P.scheme Pr M N)
    (α : MarkedArrow K oneVertexShape P.scheme Pr M M)
    {γ : Type u} (Z : γ → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.X))
    (hγ : #γ < M.μ) :
    ∃ e : SystemArrow K oneVertexShape (P.scheme.asSystem N.hμ N.X)
        (P.scheme.asSystem N.hμ N.X),
      (∀ v, Function.Bijective (e.onVertex v)) ∧
      ∀ j, e.mapOcc (f.onX.mapOcc (Z j)) = f.onX.mapOcc (α.onX.mapOcc (Z j)) := by
  have hγN : #γ < N.μ := hlev ▸ hγ
  have d1 := P.scheme.diagram_preserved M.X N.X f.onX trivial Z hγ hγN
  have d2 := P.scheme.diagram_preserved M.X M.X α.onX trivial Z hγ hγ
  have d3 := P.scheme.diagram_preserved M.X N.X f.onX trivial
    (fun j => α.onX.mapOcc (Z j)) hγ hγN
  have d := P.scheme.diagram_trans _ _ _ _ _ _
    (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d1) d2) d3
  obtain ⟨g, hg, hmap⟩ := (P.scheme.diagram_iso N.X N.X
    (fun j => f.onX.mapOcc (Z j)) (fun j => f.onX.mapOcc (α.onX.mapOcc (Z j))) hγN).mp d
  exact ⟨g, hg, fun j => (hmap j).symm⟩

/-- **A marked arrow extends the joint type of marks and a tuple (P.scheme).** For a marked arrow
`f : M → N` and a tuple `t` of `M.Y`, `tp(b, t/M.X)` is the restriction along `f.onX` of
`tp(b′, f t/N.X)`, the marks matched by `f.markMap`. This is the extension hypothesis of the
over-`B` isolation of Lemma 7.2 (`infra_72_over_B_isolation`). -/
theorem infra_82_marked_arrow_ext_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {M N : MarkedPair K oneVertexShape P.scheme Pr}
    (f : MarkedArrow K oneVertexShape P.scheme Pr M N) {ι : Type u}
    (t : ι → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y)) :
    SameGaloisType (asTuple M.incl M.incl_arrow (seqJoint M.b t))
      ((asTuple N.incl N.incl_arrow (seqJoint N.b (fun i => f.onY.mapOcc (t i)))).restrict
        f.onX trivial)
      (Equiv.sumCongr f.markMap (Equiv.refl ι)) (Equiv.refl _) := by
  refine ⟨N.μ, N.hμ, N.Y, f.onY, SystemArrow.refl _, trivial, trivial, fun v => ?_, fun i => ?_⟩
  · have h := congrArg (fun g => SystemArrow.onVertex g v) f.comm
    change (f.onY.onVertex v).comp (M.incl.onVertex v) =
      (Language.Embedding.refl K.τ _).comp ((N.incl.onVertex v).comp (f.onX.onVertex v))
    rw [Language.Embedding.refl_comp]
    exact h
  · rcases i with j | i
    · have h := f.preserves_mark (f.markMap.symm j)
      rw [Equiv.apply_symm_apply] at h
      change (⟨(M.b (f.markMap.symm j)).1,
        f.onY.onVertex (M.b (f.markMap.symm j)).1 (M.b (f.markMap.symm j)).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y)) =
        ⟨(N.b j).1, (Language.Embedding.refl K.τ _) (N.b j).2⟩
      rw [h]
      rfl
    · rfl

/-- **Diagram transport for Lemma 8.2(4) (P.scheme).** For a same-level marked arrow `f : M → N`,
a pair automorphism `α` of `M` fixing the marks positionwise and taking `t₁` to `t₂`, and a list
`Z` of `M.X`, the lists `(b′, f t₁, f Z)` and `(b′, f t₂, f (α Z))` of `N.Y` have the same diagram
(both are images of one list of `M.Y` under arrows; `diagram_preserved`). -/
theorem infra_82_orbit_diagram_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {M N : MarkedPair K oneVertexShape P.scheme Pr} (hlev : M.μ = N.μ)
    (f : MarkedArrow K oneVertexShape P.scheme Pr M N)
    (α : MarkedArrow K oneVertexShape P.scheme Pr M M) (hαb : α.markMap = Equiv.refl _)
    {ι γ : Type u} (t₁ t₂ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y))
    (hα : ∀ i, α.onY.mapOcc (t₁ i) = t₂ i)
    (Z : γ → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.X))
    (hb : #((N.bIdx ⊕ ι) ⊕ γ) < M.μ) :
    P.scheme.DiagramEq (X := N.Y) (Y := N.Y)
      (seqJoint (seqJoint N.b (fun i => f.onY.mapOcc (t₁ i)))
        (fun j => N.incl.mapOcc (f.onX.mapOcc (Z j))))
      (seqJoint (seqJoint N.b (fun i => f.onY.mapOcc (t₂ i)))
        (fun j => N.incl.mapOcc (f.onX.mapOcc (α.onX.mapOcc (Z j))))) := by
  have hbN : #((N.bIdx ⊕ ι) ⊕ γ) < N.μ := hlev ▸ hb
  have hcommf : ∀ x : Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.X),
      f.onY.mapOcc (M.incl.mapOcc x) = N.incl.mapOcc (f.onX.mapOcc x) := fun x =>
    congrArg (Sigma.mk x.1) (congrArg (fun g => SystemArrow.onVertex g x.1 x.2) f.comm)
  have hcommα : ∀ x : Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.X),
      α.onY.mapOcc (M.incl.mapOcc x) = M.incl.mapOcc (α.onX.mapOcc x) := fun x =>
    congrArg (Sigma.mk x.1) (congrArg (fun g => SystemArrow.onVertex g x.1 x.2) α.comm)
  have hmarkf : ∀ j, f.onY.mapOcc (M.b (f.markMap.symm j)) = N.b j := fun j => by
    have h := f.preserves_mark (f.markMap.symm j)
    rw [Equiv.apply_symm_apply] at h
    exact h
  have hmarkα : ∀ k, α.onY.mapOcc (M.b k) = M.b k := fun k => by
    have h := α.preserves_mark k
    rw [hαb] at h
    exact h
  let L : (N.bIdx ⊕ ι) ⊕ γ → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y) :=
    seqJoint (seqJoint (fun j => M.b (f.markMap.symm j)) t₁) (fun j => M.incl.mapOcc (Z j))
  let L' : (N.bIdx ⊕ ι) ⊕ γ → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y) :=
    seqJoint (seqJoint (fun j => M.b (f.markMap.symm j)) t₂)
      (fun j => M.incl.mapOcc (α.onX.mapOcc (Z j)))
  have d1 := P.scheme.diagram_preserved M.Y N.Y f.onY trivial L hb hbN
  have d2 := P.scheme.diagram_preserved M.Y M.Y α.onY trivial L hb hb
  have d3 := P.scheme.diagram_preserved M.Y N.Y f.onY trivial L' hb hbN
  have e1 : (fun x => (⟨(L x).1, f.onY.onVertex (L x).1 (L x).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y))) =
      seqJoint (seqJoint N.b (fun i => f.onY.mapOcc (t₁ i)))
        (fun j => N.incl.mapOcc (f.onX.mapOcc (Z j))) := by
    funext x
    rcases x with (j | i) | j
    · exact hmarkf j
    · rfl
    · exact hcommf (Z j)
  have e2 : (fun x => (⟨(L x).1, α.onY.onVertex (L x).1 (L x).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y))) = L' := by
    funext x
    rcases x with (j | i) | j
    · exact hmarkα _
    · exact hα i
    · exact hcommα (Z j)
  have e3 : (fun x => (⟨(L' x).1, f.onY.onVertex (L' x).1 (L' x).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y))) =
      seqJoint (seqJoint N.b (fun i => f.onY.mapOcc (t₂ i)))
        (fun j => N.incl.mapOcc (f.onX.mapOcc (α.onX.mapOcc (Z j)))) := by
    funext x
    rcases x with (j | i) | j
    · exact hmarkf j
    · rfl
    · exact hcommf _
  rw [e1] at d1
  rw [e2] at d2
  rw [e3] at d3
  exact P.scheme.diagram_trans _ _ _ _ _ _
    (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d1) d2) d3

end AEC
