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
  have hR := N.realizes
  generalize N.realEq = eb at hR
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
    (hb : #((M.bIdx ⊕ ι) ⊕ γ) < M.μ) :
    P.scheme.DiagramEq (X := N.Y) (Y := N.Y)
      (seqJoint (seqJoint (fun k => N.b (f.markMap k)) (fun i => f.onY.mapOcc (t₁ i)))
        (fun j => N.incl.mapOcc (f.onX.mapOcc (Z j))))
      (seqJoint (seqJoint (fun k => N.b (f.markMap k)) (fun i => f.onY.mapOcc (t₂ i)))
        (fun j => N.incl.mapOcc (f.onX.mapOcc (α.onX.mapOcc (Z j))))) := by
  have hbN : #((M.bIdx ⊕ ι) ⊕ γ) < N.μ := hlev ▸ hb
  have hcommf : ∀ x : Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.X),
      f.onY.mapOcc (M.incl.mapOcc x) = N.incl.mapOcc (f.onX.mapOcc x) := fun x =>
    congrArg (Sigma.mk x.1) (congrArg (fun g => SystemArrow.onVertex g x.1 x.2) f.comm)
  have hcommα : ∀ x : Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.X),
      α.onY.mapOcc (M.incl.mapOcc x) = M.incl.mapOcc (α.onX.mapOcc x) := fun x =>
    congrArg (Sigma.mk x.1) (congrArg (fun g => SystemArrow.onVertex g x.1 x.2) α.comm)
  have hmarkf : ∀ k, f.onY.mapOcc (M.b k) = N.b (f.markMap k) := fun k => f.preserves_mark k
  have hmarkα : ∀ k, α.onY.mapOcc (M.b k) = M.b k := fun k => by
    have h := α.preserves_mark k
    rw [hαb] at h
    exact h
  let L : (M.bIdx ⊕ ι) ⊕ γ → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y) :=
    seqJoint (seqJoint M.b t₁) (fun j => M.incl.mapOcc (Z j))
  let L' : (M.bIdx ⊕ ι) ⊕ γ → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y) :=
    seqJoint (seqJoint M.b t₂)
      (fun j => M.incl.mapOcc (α.onX.mapOcc (Z j)))
  have d1 := P.scheme.diagram_preserved M.Y N.Y f.onY trivial L hb hbN
  have d2 := P.scheme.diagram_preserved M.Y M.Y α.onY trivial L hb hb
  have d3 := P.scheme.diagram_preserved M.Y N.Y f.onY trivial L' hb hbN
  have e1 : (fun x => (⟨(L x).1, f.onY.onVertex (L x).1 (L x).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y))) =
      seqJoint (seqJoint (fun k => N.b (f.markMap k)) (fun i => f.onY.mapOcc (t₁ i)))
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
      seqJoint (seqJoint (fun k => N.b (f.markMap k)) (fun i => f.onY.mapOcc (t₂ i)))
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

/-- Arrows of one-vertex systems are injective on occurrences. -/
theorem infra_82_mapOcc_injective {X Y : SystemObject K oneVertexShape}
    (g : SystemArrow K oneVertexShape X Y) {x y : Occurrence K oneVertexShape X}
    (h : g.mapOcc x = g.mapOcc y) : x = y := by
  obtain ⟨⟨⟩, a⟩ := x
  obtain ⟨⟨⟩, b⟩ := y
  have h2 := eq_of_heq (Sigma.mk.inj h).2
  have h3 : a = b := (g.onVertex PUnit.unit).injective h2
  subst h3
  rfl

/-- **Lemma 8.2(4) for P.scheme, given tied freeness of the mark along the arrow.** On the
tail `infra_615_closed` (closed for the profile recursion at every smaller size), a same-level
marked arrow `f : M → N` along which `tp(b′/N.X)` (read in `M`'s mark positions through
`f.markMap`) is the tied free extension of `tp(b/M.X)` preserves bounded pair orbits. English
(Lemma 8.2 proof): the joint type over the larger base is the free extension (Lemma 7.2, over-`B`
isolation by the pushed fragment, `infra_72_over_B_isolation`); "An isomorphism of the two bases
matching these lists exists by bounded diagram homogeneity in C"
(`infra_82_base_homogeneity_single`); then the pair isomorphism test (clause 3). -/
theorem infra_82_orbit_preservation_of_tied_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) (hiso : Pr.CommutesWithIso) :
    ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∀ (M N : MarkedPair K oneVertexShape P.scheme Pr)
        (f : MarkedArrow K oneVertexShape P.scheme Pr M N),
        M.μ ∈ T → M.μ = N.μ →
        IsTiedFreeMixed f.onX (asTuple M.incl M.incl_arrow M.b)
          (⟨N.μ, N.hμ, N.Y, N.incl, trivial, M.bIdx, fun k => N.b (f.markMap k)⟩ :
            TupleOver K oneVertexShape P.scheme N.hμ N.X) (Equiv.refl _) →
        ∀ {ι : Type u} (t₁ t₂ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y)),
          #ι < M.μ →
          PairOrbitEq M M (Equiv.refl _) t₁ t₂ →
          PairOrbitEq N N (Equiv.refl _) (fun i => f.onY.mapOcc (t₁ i))
            (fun i => f.onY.mapOcc (t₂ i)) := by
  classical
  refine ⟨infra_615_closed P, infra_615_tail P,
    fun M N f hM hlev hTied ι t₁ t₂ hι hO => ?_⟩
  obtain ⟨α, hαb, -, -, hαt⟩ := hO
  obtain ⟨γ, Z, hγ, HZ⟩ := M.dominated ι t₁ hι
  obtain ⟨e, hbij, he⟩ := infra_82_base_homogeneity_single M N hlev f α Z hγ
  -- sizes
  obtain ⟨eb, -⟩ : ∃ e, _ := (⟨M.realEq, M.realizes⟩ : ∃ e, _)
  have hfinB : Finite M.bIdx :=
    Finite.of_equiv _ (eb.trans (Pr.arity M.hμ M.X)).symm
  have hμ0 : ℵ₀ < M.μ := P.aleph0_lt M.hμ
  have hBlt : #M.bIdx < M.μ := (Cardinal.lt_aleph0_of_finite M.bIdx).trans hμ0
  have hbι : #(M.bIdx ⊕ ι) < M.μ := by
    simp only [mk_sum, lift_id]
    exact add_lt_of_lt (P.aleph0_le M.hμ) hBlt hι
  have hbιγ : #((M.bIdx ⊕ ι) ⊕ γ) < M.μ := by
    simp only [mk_sum, lift_id] at hbι ⊢
    exact add_lt_of_lt (P.aleph0_le M.hμ) hbι hγ
  have hD := infra_82_orbit_diagram_single hlev f α hαb t₁ t₂ hαt Z hbιγ
  have hExt := infra_82_marked_arrow_ext_single f t₁
  have hMk := infra_82_mark_type_auto_single hiso N e hbij
  have hιN : #ι < N.μ := hlev ▸ hι
  let σ : Cardinal.{u} := max (#(M.bIdx ⊕ ι)) ℵ₀
  have hσ : ℵ₀ ≤ σ := le_max_right _ _
  have hσμ : σ < M.μ := max_lt hbι hμ0
  have hrec : M.μ ∈ recursionClosedLevels P σ :=
    ⟨hM.1, fun β₀ hβ => hM.2 σ hσ hσμ β₀ hβ⟩
  have hσSucc : Order.succ σ ≤ M.μ := Order.succ_le_of_lt hσμ
  have hidx : #(M.bIdx ⊕ ι) ≤ σ := le_max_left _ _
  -- the pair-isomorphism test at `N`
  refine (fun H => ?_) (infra_82_pointed_all P Pr N N e hbij trivial (Equiv.refl _)
    (fun i => f.onY.mapOcc (t₁ i)) (fun i => f.onY.mapOcc (t₂ i)) hιN)
  suffices hG : ∃ (ρ : Cardinal.{u}) (hρ : ρ ∈ P.scheme.eligible) (top : P.scheme.Object ρ hρ)
      (g1 g2 : SystemArrow K oneVertexShape (P.scheme.asSystem N.hμ N.Y)
        (P.scheme.asSystem hρ top)),
      (∀ v, (g1.onVertex v).comp (N.incl.onVertex v) =
        (g2.onVertex v).comp ((SystemArrow.comp e N.incl).onVertex v)) ∧
      (∀ k, g1.mapOcc (N.b (f.markMap k)) = g2.mapOcc (N.b (f.markMap k))) ∧
      (∀ i, g1.mapOcc (f.onY.mapOcc (t₁ i)) = g2.mapOcc (f.onY.mapOcc (t₂ i))) by
    obtain ⟨ρ, hρ, top, g1, g2, hc, hvb, hvt⟩ := hG
    have hbase : ∀ i (x : Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.X)),
        f.onY.mapOcc (t₁ i) = N.incl.mapOcc x →
          f.onY.mapOcc (t₂ i) = N.incl.mapOcc (e.mapOcc x) := by
      intro i x hx
      apply infra_82_mapOcc_injective g2
      rw [← hvt i, hx]
      exact congrArg (Sigma.mk x.1) (DFunLike.congr_fun (hc x.1) x.2)
    have hsgt : SameGaloisType
        (asTuple N.incl N.incl_arrow (Sum.elim (fun i => f.onY.mapOcc (t₁ i)) N.b))
        (markedJointOver N N e trivial (Equiv.refl _) (fun i => f.onY.mapOcc (t₂ i)))
        (Equiv.refl _) (Equiv.refl _) := by
      refine ⟨ρ, hρ, top, g1, g2, trivial, trivial, hc, fun i => ?_⟩
      rcases i with i | j
      · exact hvt i
      · have h := hvb (f.markMap.symm j)
        rw [Equiv.apply_symm_apply] at h
        exact h
    obtain ⟨arr, hX, hσ', hY, hmap⟩ := H.mpr ⟨hbase, hsgt⟩
    exact ⟨arr, hσ', fun v => by rw [hX]; exact hbij v, hY, hmap⟩
  -- over-`B` isolation at the common level
  obtain ⟨μM, hμM, XM, YM, inclM, hinclM, bIM, bM, erM, hrM, hdM⟩ := M
  obtain ⟨μN, hμN, XN, YN, inclN, hinclN, bIN, bN, erN, hrN, hdN⟩ := N
  change μM = μN at hlev
  subst hlev
  have hW := infra_72_over_B_isolation P σ hσ hμM hrec hσSucc f.onX trivial
    (asTuple inclM hinclM (seqJoint bM t₁))
    (asTuple inclN hinclN (seqJoint bN (fun i => f.onY.mapOcc (t₁ i))))
    (Equiv.sumCongr f.markMap (Equiv.refl ι)) (Equiv.refl _) rfl rfl hidx hbι Z ⟨hγ, HZ⟩ hExt hTied
  let q' : TupleOver K oneVertexShape P.scheme hμN XN :=
    ⟨μM, hμN, YN, SystemArrow.comp e inclN, trivial, bIN ⊕ ι,
      seqJoint bN (fun i => f.onY.mapOcc (t₂ i))⟩
  have hmarg : SameGaloisType
      ((asTuple inclN hinclN (seqJoint bN (fun i => f.onY.mapOcc (t₁ i)))).marginal
        ((Equiv.sumCongr f.markMap (Equiv.refl ι)).symm.trans (Equiv.refl _)))
      (q'.marginal ((Equiv.sumCongr f.markMap (Equiv.refl ι)).symm.trans (Equiv.refl _)))
      (Equiv.refl _) (Equiv.refl _) := by
    rcases hMk with ⟨ρ, hρ, top, g1, g2, h1, h2, hc, hv⟩
    exact ⟨ρ, hρ, top, g1, g2, h1, h2, hc, fun k => hv (f.markMap k)⟩
  have hdiag : P.scheme.DiagramEq (X := YN) (Y := q'.host)
      (alignJoint ((Equiv.sumCongr f.markMap (Equiv.refl ι)).symm.trans (Equiv.refl _))
        (typeJoint (p := asTuple inclN hinclN (seqJoint bN (fun i => f.onY.mapOcc (t₁ i))))
          (pushParams f.onX Z)))
      (alignJoint ((Equiv.sumCongr f.markMap (Equiv.refl ι)).symm.trans (Equiv.refl _))
        (typeJoint (p := q') (pushParams f.onX Z))) := by
    have key : ∀ {α : Type u} (xs xs' ys ys' : α → Occurrence K oneVertexShape
        (P.scheme.asSystem hμN YN)), xs = xs' → ys = ys' →
        P.scheme.DiagramEq (X := YN) (Y := YN) xs ys →
        P.scheme.DiagramEq (X := YN) (Y := YN) xs' ys' := by
      intro _ _ _ _ _ h1 h2 h; subst h1 h2; exact h
    refine key _ _ _ _ ?_ ?_ hD
    · funext x; rcases x with (k | i) | j <;> rfl
    · funext x
      rcases x with (k | i) | j
      · rfl
      · rfl
      · exact (congrArg inclN.mapOcc (he j)).symm
  obtain ⟨ρ, hρ, top, g1, g2, -, -, hc, hv⟩ := hW.2 q' _ rfl hmarg hdiag
  exact ⟨ρ, hρ, top, g1, g2, hc, fun k => hv (Sum.inl k), fun i => hv (Sum.inr i)⟩

/-- **Bounded diagram homogeneity between two bases (P.scheme; toward Lemma 8.2(5)).** For marked
arrows `f₁ : M₁ → N₁`, `f₂ : M₂ → N₂` (any levels, `N₁`, `N₂` at one level) and a marked arrow
`α : M₁ → M₂`, every list `Z` of `M₁.X` bounded at the levels gives a structural isomorphism
`e : N₁.X ≅ N₂.X` with `e (f₁ Z) = f₂ (α Z)` (`diagram_preserved` across levels, then
`diagram_iso` at the level of the `N`s). -/
theorem infra_82_base_homogeneity_cross_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {M₁ M₂ N₁ N₂ : MarkedPair K oneVertexShape P.scheme Pr} (hN : N₁.μ = N₂.μ)
    (f₁ : MarkedArrow K oneVertexShape P.scheme Pr M₁ N₁)
    (f₂ : MarkedArrow K oneVertexShape P.scheme Pr M₂ N₂)
    (α : MarkedArrow K oneVertexShape P.scheme Pr M₁ M₂)
    {γ : Type u} (Z : γ → Occurrence K oneVertexShape (P.scheme.asSystem M₁.hμ M₁.X))
    (hγ₁ : #γ < M₁.μ) (hγ₂ : #γ < M₂.μ) (hγN : #γ < N₁.μ) :
    ∃ e : SystemArrow K oneVertexShape (P.scheme.asSystem N₁.hμ N₁.X)
        (P.scheme.asSystem N₂.hμ N₂.X),
      (∀ v, Function.Bijective (e.onVertex v)) ∧
      ∀ j, e.mapOcc (f₁.onX.mapOcc (Z j)) = f₂.onX.mapOcc (α.onX.mapOcc (Z j)) := by
  have hγN₂ : #γ < N₂.μ := hN ▸ hγN
  have d1 := P.scheme.diagram_preserved M₁.X N₁.X f₁.onX trivial Z hγ₁ hγN
  have d2 := P.scheme.diagram_preserved M₁.X M₂.X α.onX trivial Z hγ₁ hγ₂
  have d3 := P.scheme.diagram_preserved M₂.X N₂.X f₂.onX trivial
    (fun j => α.onX.mapOcc (Z j)) hγ₂ hγN₂
  have d := P.scheme.diagram_trans _ _ _ _ _ _
    (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d1) d2) d3
  obtain ⟨μ₁, hμ₁, X₁, Y₁, i₁, hi₁, bI₁, b₁, er₁, r₁, d₁⟩ := N₁
  obtain ⟨μ₂, hμ₂, X₂, Y₂, i₂, hi₂, bI₂, b₂, er₂, r₂, d₂'⟩ := N₂
  change μ₁ = μ₂ at hN
  subst hN
  obtain ⟨g, hg, hmap⟩ := (P.scheme.diagram_iso X₁ X₂
    (fun j => f₁.onX.mapOcc (Z j)) (fun j => f₂.onX.mapOcc (α.onX.mapOcc (Z j))) hγN).mp d
  exact ⟨g, hg, fun j => (hmap j).symm⟩

/-- **Diagram transport between two pairs (P.scheme; toward Lemma 8.2(5)).** For marked arrows
`f₁ : M₁ → N₁`, `f₂ : M₂ → N₂` and `α : M₁ → M₂` taking `t₁` to `t₂`, and a list `Z` of `M₁.X`,
the lists `(b₁′ ∘ f₁.markMap, f₁ t₁, f₁ Z)` of `N₁.Y` and
`(b₂′ ∘ f₂.markMap ∘ α.markMap, f₂ t₂, f₂ (α Z))` of `N₂.Y` have the same diagram. -/
theorem infra_82_orbit_diagram_cross_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {M₁ M₂ N₁ N₂ : MarkedPair K oneVertexShape P.scheme Pr}
    (f₁ : MarkedArrow K oneVertexShape P.scheme Pr M₁ N₁)
    (f₂ : MarkedArrow K oneVertexShape P.scheme Pr M₂ N₂)
    (α : MarkedArrow K oneVertexShape P.scheme Pr M₁ M₂)
    {ι γ : Type u} (t₁ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M₁.hμ M₁.Y))
    (t₂ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M₂.hμ M₂.Y))
    (hα : ∀ i, α.onY.mapOcc (t₁ i) = t₂ i)
    (Z : γ → Occurrence K oneVertexShape (P.scheme.asSystem M₁.hμ M₁.X))
    (hb₁ : #((M₁.bIdx ⊕ ι) ⊕ γ) < M₁.μ) (hb₂ : #((M₁.bIdx ⊕ ι) ⊕ γ) < M₂.μ)
    (hbN₁ : #((M₁.bIdx ⊕ ι) ⊕ γ) < N₁.μ) (hbN₂ : #((M₁.bIdx ⊕ ι) ⊕ γ) < N₂.μ) :
    P.scheme.DiagramEq (X := N₁.Y) (Y := N₂.Y)
      (seqJoint (seqJoint (fun k => N₁.b (f₁.markMap k)) (fun i => f₁.onY.mapOcc (t₁ i)))
        (fun j => N₁.incl.mapOcc (f₁.onX.mapOcc (Z j))))
      (seqJoint (seqJoint (fun k => N₂.b (f₂.markMap (α.markMap k)))
          (fun i => f₂.onY.mapOcc (t₂ i)))
        (fun j => N₂.incl.mapOcc (f₂.onX.mapOcc (α.onX.mapOcc (Z j))))) := by
  have hcomm : ∀ {A B : MarkedPair K oneVertexShape P.scheme Pr}
      (g : MarkedArrow K oneVertexShape P.scheme Pr A B)
      (x : Occurrence K oneVertexShape (P.scheme.asSystem A.hμ A.X)),
      g.onY.mapOcc (A.incl.mapOcc x) = B.incl.mapOcc (g.onX.mapOcc x) := fun g x =>
    congrArg (Sigma.mk x.1) (congrArg (fun h => SystemArrow.onVertex h x.1 x.2) g.comm)
  let L : (M₁.bIdx ⊕ ι) ⊕ γ → Occurrence K oneVertexShape (P.scheme.asSystem M₁.hμ M₁.Y) :=
    seqJoint (seqJoint M₁.b t₁) (fun j => M₁.incl.mapOcc (Z j))
  let L' : (M₁.bIdx ⊕ ι) ⊕ γ → Occurrence K oneVertexShape (P.scheme.asSystem M₂.hμ M₂.Y) :=
    seqJoint (seqJoint (fun k => M₂.b (α.markMap k)) t₂)
      (fun j => M₂.incl.mapOcc (α.onX.mapOcc (Z j)))
  have d1 := P.scheme.diagram_preserved M₁.Y N₁.Y f₁.onY trivial L hb₁ hbN₁
  have d2 := P.scheme.diagram_preserved M₁.Y M₂.Y α.onY trivial L hb₁ hb₂
  have d3 := P.scheme.diagram_preserved M₂.Y N₂.Y f₂.onY trivial L' hb₂ hbN₂
  have e1 : (fun x => (⟨(L x).1, f₁.onY.onVertex (L x).1 (L x).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem N₁.hμ N₁.Y))) =
      seqJoint (seqJoint (fun k => N₁.b (f₁.markMap k)) (fun i => f₁.onY.mapOcc (t₁ i)))
        (fun j => N₁.incl.mapOcc (f₁.onX.mapOcc (Z j))) := by
    funext x
    rcases x with (k | i) | j
    · exact f₁.preserves_mark k
    · rfl
    · exact hcomm f₁ (Z j)
  have e2 : (fun x => (⟨(L x).1, α.onY.onVertex (L x).1 (L x).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem M₂.hμ M₂.Y))) = L' := by
    funext x
    rcases x with (k | i) | j
    · exact α.preserves_mark k
    · exact hα i
    · exact hcomm α (Z j)
  have e3 : (fun x => (⟨(L' x).1, f₂.onY.onVertex (L' x).1 (L' x).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem N₂.hμ N₂.Y))) =
      seqJoint (seqJoint (fun k => N₂.b (f₂.markMap (α.markMap k)))
          (fun i => f₂.onY.mapOcc (t₂ i)))
        (fun j => N₂.incl.mapOcc (f₂.onX.mapOcc (α.onX.mapOcc (Z j)))) := by
    funext x
    rcases x with (k | i) | j
    · exact f₂.preserves_mark _
    · rfl
    · exact hcomm f₂ _
  rw [e1] at d1
  rw [e2] at d2
  rw [e3] at d3
  exact P.scheme.diagram_trans _ _ _ _ _ _
    (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d1) d2) d3

/-- **Structural isomorphisms of bases carry the mark's type (P.scheme; toward Lemma 8.2(5)).**
If the prescription commutes with isomorphisms, a structural isomorphism `e : N₁.X ≅ N₂.X` of the
bases of two marked pairs at one level carries `tp(b₁/N₁.X)` to `tp(b₂/N₂.X)`, the marks matched
by list position through the realizations (`realEq`, data since cycle 97) and `arity`. -/
theorem infra_82_mark_type_iso_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme} (hiso : Pr.CommutesWithIso)
    (N₁ N₂ : MarkedPair K oneVertexShape P.scheme Pr) (hN : N₁.μ = N₂.μ)
    (e : SystemArrow K oneVertexShape (P.scheme.asSystem N₁.hμ N₁.X)
      (P.scheme.asSystem N₂.hμ N₂.X))
    (hbij : ∀ v, Function.Bijective (e.onVertex v)) :
    SameGaloisType (asTuple N₁.incl N₁.incl_arrow N₁.b)
      ((asTuple N₂.incl N₂.incl_arrow N₂.b).restrict e trivial)
      (N₁.realEq.trans (((Pr.arity N₁.hμ N₁.X).trans (Pr.arity N₂.hμ N₂.X).symm).trans
        N₂.realEq.symm)) (Equiv.refl _) := by
  obtain ⟨μ₁, hμ₁, X₁, Y₁, i₁, hi₁, bI₁, b₁, er₁, r₁, d₁⟩ := N₁
  obtain ⟨μ₂, hμ₂, X₂, Y₂, i₂, hi₂, bI₂, b₂, er₂, r₂, d₂⟩ := N₂
  change μ₁ = μ₂ at hN
  subst hN
  have hR₁ := r₁
  have hR₂ := r₂
  have hk := hiso X₁ X₂ e trivial hbij
  have hR₂e : SameGaloisType ((asTuple i₂ hi₂ b₂).restrict e trivial)
      ((Pr.assign hμ₁ X₂).restrict e trivial) er₂ (Equiv.refl _) := by
    rcases hR₂ with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, fun v => ?_, hv⟩
    change (f1.onVertex v).comp ((i₂.onVertex v).comp (e.onVertex v)) =
      (f2.onVertex v).comp (((Pr.assign hμ₁ X₂).incl.onVertex v).comp (e.onVertex v))
    have h := congrArg (fun g => FirstOrder.Language.Embedding.comp g (e.onVertex v)) (hc v)
    simp only [FirstOrder.Language.Embedding.comp_assoc] at h ⊢
    exact h
  have hμ0 : ℵ₀ < μ₁ := P.aleph0_lt hμ₁
  have hfinA : Finite (Pr.assign hμ₁ X₁).idx := Finite.of_equiv _ (Pr.arity hμ₁ X₁).symm
  have hfinB : Finite bI₁ := Finite.of_equiv _ er₁.symm
  have hA : #(Pr.assign hμ₁ X₁).idx ≤ ℵ₀ :=
    (Cardinal.lt_aleph0_of_finite (Pr.assign hμ₁ X₁).idx).le
  have hB : #bI₁ ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite bI₁).le
  have h24 := infra_612_galois_trans_last_base hk hR₂e.symm ℵ₀ le_rfl hμ0 hA rfl
  have h24' := SameGaloisType.swap_refl h24
  have hfin := infra_612_galois_trans_last_base hR₁ h24' ℵ₀ le_rfl hμ0 hB rfl
  rw [Equiv.symm_symm] at hfin
  exact hfin

end AEC
