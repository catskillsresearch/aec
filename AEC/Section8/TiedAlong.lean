module

public import AEC.Section8.PairOrbitSingle
public import AEC.Section7.Lemma72Mixed

@[expose] public section

/-!
# Definition 8.1 with tied freeness (P.scheme)

Cycle 97 ruling (Lars may override): in Definition 8.1, "for every arrow `X → X′` ... `p_{X′}` is
the free extension of `p_X`" is the tied notion (`IsTiedFree` / `IsTiedFreeMixed`), as in
Sections 6–7. The structure field `StationaryPrescription.along` is stated for a general working
scheme, where Lean has only the untied `IsFreeLift` (the tied notion exists only for
`SingleModelData`; generalizing it is `infra_8_general_calculus`, untouched). For `P.scheme` the
Definition 8.1 freeness is therefore the predicate `StationaryPrescription.TiedAlong`, positional
through `arity` like `CommutesWithIso`: along every permitted arrow (including a mixed-level
one) `p_{X′}` read back is `p_X` coordinate by coordinate, and `p_{X′}` is a tied free extension
of `p_X` with that matching.
-/

namespace AEC
section

universe u
open Cardinal Classical FirstOrder Function
variable {K : AbstractElementaryClass.{u}}

/-- **Definition 8.1, tied free extension along arrows (P.scheme).** -/
def StationaryPrescription.TiedAlong {P : SingleModelData K}
    (Pr : StationaryPrescription K oneVertexShape P.scheme) : Prop :=
  ∀ {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (X : P.scheme.Object ν hν) (Y : P.scheme.Object μ hμ)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f),
    SameGaloisType (Pr.assign hν X) ((Pr.assign hμ Y).restrict f hf)
      ((Pr.arity hν X).trans (Pr.arity hμ Y).symm) (Equiv.refl _) ∧
    IsTiedFreeMixed f (Pr.assign hν X) (Pr.assign hμ Y)
      ((Pr.arity hν X).trans (Pr.arity hμ Y).symm)

/-- **Mixed tied freeness under a reindexed change of the base tuple (proved).** If `p'` and
`p` (both over `A`) answer every query bounded below the level of `A` alike, `p'` read through
`ε : p'.idx ≃ p.idx`, then a mixed tied-free extension of `p` is one of `p'`, matched through `ε`. -/
theorem infra_82_tiedFreeMixed_base_equiv
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (p p' : TupleOver K oneVertexShape P.scheme hν A) (ε : p'.idx ≃ p.idx)
    (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx)
    (hD : ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      #ι < ν → P.scheme.DiagramEq (X := p'.host) (Y := p.host)
        (typeJoint (p := p') Z) (fun t => typeJoint (p := p) Z (Sum.map ε id t)))
    (hT : IsTiedFreeMixed f p qB eB) :
    IsTiedFreeMixed f p' qB (ε.trans eB) := by
  intro seq' ι Z Z0 hlong hι hιν hmv
  let seq : ApproximationSequence p :=
    { τ := #ι
      κIndex := seq'.κIndex
      family := fun i k => seq'.family i (ε.symm k)
      concat_bounded := by
        rw [← Cardinal.mk_congr (Equiv.prodCongr (Equiv.refl _) ε)]
        exact seq'.concat_bounded
      few_exceptions := fun {ι'} Z' h' => by
        have h0 := seq'.few_exceptions Z' (h'.trans hι)
        refine le_trans (Cardinal.mk_le_of_injective (f := fun s => (⟨s.1, ?_⟩ :
          {i : seq'.κIndex // ¬ P.scheme.DiagramEq (X := p'.host) (Y := A)
            (typeJoint (p := p') Z') (seqJoint (seq'.family i) Z')})) ?_) h0
        · intro hc
          apply s.2
          have d := hD Z' (h'.trans_lt hιν)
          have d1 := infra_73_scheme_comp (P.scheme.diagram_trans _ _ _ _ _ _
            (P.scheme.diagram_symm _ _ _ _ d) hc) (Sum.map ε.symm id)
          exact infra_73_diagramEq_of_eq d1
            (fun t => by cases t <;> simp [typeJoint])
            (fun t => by cases t <;> rfl)
        · intro s1 s2 h
          have h2 := congrArg Subtype.val h
          exact Subtype.ext h2 }
  have hlong' : seq.τ + ℵ₀ < #seq.κIndex :=
    show #ι + ℵ₀ < #seq'.κIndex from (add_le_add hι le_rfl).trans_lt hlong
  have hmv' : infra_78_isMoveMixed f seq Z Z0 := by
    intro i
    have h := infra_73_scheme_comp (hmv i) (Sum.map ε.symm id)
    exact infra_73_diagramEq_of_eq h (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  have T := hT seq Z Z0 hlong' le_rfl hιν hmv'
  have T' := infra_73_scheme_comp T (Sum.map ε id)
  have d := hD Z0 hιν
  have d' := P.scheme.diagram_trans _ _ _ _ _ _ d T'
  exact infra_73_diagramEq_of_eq d' (fun _ => rfl) (fun t => by cases t <;> rfl)

/-- A tuple over an object of level `μ` is hosted at a level at least `μ`. -/
theorem infra_82_host_level_ge {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} (t : TupleOver K oneVertexShape P.scheme hμ A) : μ ≤ t.ν := by
  have a := P.scheme.vertex_card hμ A PUnit.unit
  have b := P.scheme.vertex_card t.hν t.host PUnit.unit
  exact a.symm.le.trans
    ((Cardinal.mk_le_of_injective (t.incl.onVertex PUnit.unit).injective).trans b.le)

/-- Restricting both sides of a Galois-type equality along one permitted arrow. -/
theorem infra_82_sgt_restrict {P : SingleModelData K} {ν μ : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hg : P.scheme.permitted (X := A) (Y := B) g)
    {t1 t2 : TupleOver K oneVertexShape P.scheme hμ B} {ι : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι} (h : SameGaloisType t1 t2 e1 e2) :
    SameGaloisType (t1.restrict g hg) (t2.restrict g hg) e1 e2 := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, fun v => ?_, hv⟩
  change (f1.onVertex v).comp ((t1.incl.onVertex v).comp (g.onVertex v)) =
    (f2.onVertex v).comp ((t2.incl.onVertex v).comp (g.onVertex v))
  have h := congrArg (fun k => FirstOrder.Language.Embedding.comp k (g.onVertex v)) (hc v)
  simp only [FirstOrder.Language.Embedding.comp_assoc] at h ⊢
  exact h

/-- The image of a pair's mark along a marked arrow, as a tuple over the target base, indexed by
the source mark's positions. -/
abbrev infra_82_markImage {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {M N : MarkedPair K oneVertexShape P.scheme Pr}
    (f : MarkedArrow K oneVertexShape P.scheme Pr M N) :
    TupleOver K oneVertexShape P.scheme N.hμ N.X :=
  ⟨N.μ, N.hμ, N.Y, N.incl, trivial, M.bIdx, fun k => N.b (f.markMap k)⟩

/-- The source mark has the type, over the source base, of its image read back along the arrow. -/
theorem infra_82_mark_ext_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {M N : MarkedPair K oneVertexShape P.scheme Pr}
    (f : MarkedArrow K oneVertexShape P.scheme Pr M N) :
    SameGaloisType (asTuple M.incl M.incl_arrow M.b)
      ((infra_82_markImage f).restrict f.onX trivial) (Equiv.refl _) (Equiv.refl _) := by
  refine ⟨N.μ, N.hμ, N.Y, f.onY, SystemArrow.refl _, trivial, trivial, fun v => ?_, fun i => ?_⟩
  · have h := congrArg (fun g => SystemArrow.onVertex g v) f.comm
    change (f.onY.onVertex v).comp (M.incl.onVertex v) =
      (Language.Embedding.refl K.τ _).comp ((N.incl.onVertex v).comp (f.onX.onVertex v))
    rw [Language.Embedding.refl_comp]
    exact h
  · have h := f.preserves_mark i
    change (⟨(M.b i).1, f.onY.onVertex (M.b i).1 (M.b i).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y)) =
      ⟨(N.b (f.markMap i)).1, (Language.Embedding.refl K.τ _) (N.b (f.markMap i)).2⟩
    rw [h]
    rfl

/-- The target pair's mark, read through `markMap`, realizes the target prescription. -/
theorem infra_82_markImage_realizes {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {M N : MarkedPair K oneVertexShape P.scheme Pr}
    (f : MarkedArrow K oneVertexShape P.scheme Pr M N) :
    SameGaloisType (infra_82_markImage f) (Pr.assign N.hμ N.X)
      (f.markMap.trans N.realEq) (Equiv.refl _) := by
  rcases N.realizes with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun i => ?_⟩
  have h := hv i
  have hk : (infra_82_markImage f).val ((f.markMap.trans N.realEq).symm i) =
      N.b (N.realEq.symm i) := by
    simp [infra_82_markImage]
  rw [hk]
  exact h

/-- A Galois-type equality `tp(p′) = tp(p)` through `ε` read as equal answers on every bounded
query, `p` reindexed by `ε`. -/
theorem infra_82_diag_of_sgt_equiv {P : SingleModelData K} {ν : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {A : P.scheme.Object ν hν}
    {p' p : TupleOver K oneVertexShape P.scheme hν A} {ε : p'.idx ≃ p.idx}
    (h : SameGaloisType p' p ε (Equiv.refl _)) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (h1 : #(p.idx ⊕ ι) < p'.ν) (h2 : #(p.idx ⊕ ι) < p.ν) :
    P.scheme.DiagramEq (X := p'.host) (Y := p.host)
      (typeJoint (p := p') Z) (fun t => typeJoint (p := p) Z (Sum.map ε id t)) := by
  have d := infra_78_diagramEq_of_sameGalois h Z h1 h2
  have d1 := infra_73_scheme_comp d (Sum.map ε id)
  exact infra_73_diagramEq_of_eq d1
    (fun t => by cases t <;> simp [alignJoint, typeJoint])
    (fun t => by cases t <;> rfl)

set_option maxHeartbeats 1600000 in
/-- **Tied freeness of the mark along marked arrows (P.scheme; input to Lemma 8.2(4)).** Under the
Definition 8.1 tied free extension along arrows (`TiedAlong`), for a same-level marked arrow
`f : M → N`, the image of the mark of `M` (read through `markMap`) is a tied free extension over
`N.X` of the mark of `M` over `M.X`, positions matched by the identity. -/
theorem infra_82_mark_tied_along_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme} (hTA : Pr.TiedAlong)
    {M N : MarkedPair K oneVertexShape P.scheme Pr}
    (f : MarkedArrow K oneVertexShape P.scheme Pr M N) (hlev : M.μ = N.μ) :
    IsTiedFreeMixed f.onX (asTuple M.incl M.incl_arrow M.b) (infra_82_markImage f)
      (Equiv.refl _) := by
  classical
  obtain ⟨h1, h2⟩ := hTA M.X N.X f.onX f.onX_arrow
  have hμ0 : ℵ₀ < M.μ := P.aleph0_lt M.hμ
  have hfinM : Finite (Pr.assign M.hμ M.X).idx := Finite.of_equiv _ (Pr.arity M.hμ M.X).symm
  have hA : #(Pr.assign M.hμ M.X).idx ≤ ℵ₀ :=
    (Cardinal.lt_aleph0_of_finite (Pr.assign M.hμ M.X).idx).le
  have hfinB : Finite M.bIdx := Finite.of_equiv _ (M.realEq.trans (Pr.arity M.hμ M.X)).symm
  have hii := infra_82_sgt_restrict f.onX f.onX_arrow (infra_82_markImage_realizes f)
  have s1 := infra_612_galois_trans_last_base h1 (SameGaloisType.symm hii) ℵ₀ le_rfl hμ0 hA
    hlev.symm
  have hi := infra_82_mark_ext_single f
  have s2 := infra_612_galois_trans_last_base s1 (SameGaloisType.symm hi) ℵ₀ le_rfl hμ0 hA rfl
  have s3 := infra_73_sgt_uncommon (SameGaloisType.symm s2)
  have hB := infra_82_tiedFreeMixed_base_equiv f.onX _ _ _ _ _ (fun {ι} Z hι => by
      have hs : #((Pr.assign M.hμ M.X).idx ⊕ ι) < M.μ := by
        rw [mk_sum, lift_id, lift_id]
        exact add_lt_of_lt (P.aleph0_le M.hμ) (hA.trans_lt hμ0) hι
      exact infra_82_diag_of_sgt_equiv s3 Z hs (hs.trans_le (infra_82_host_level_ge _))) h2
  have hR := infra_73_sgt_uncommon (SameGaloisType.symm (infra_82_markImage_realizes f))
  have hT : IsTiedFreeMixed f.onX (asTuple M.incl M.incl_arrow M.b) (Pr.assign N.hμ N.X)
      ((Equiv.refl M.bIdx).trans
        ((Equiv.refl _).trans (f.markMap.trans N.realEq).symm).symm) := by
    have hE : (Equiv.refl M.bIdx).trans
        ((Equiv.refl _).trans (f.markMap.trans N.realEq).symm).symm =
        ((Equiv.refl _).trans ((((Pr.arity M.hμ M.X).trans (Pr.arity N.hμ N.X).symm).trans
          (f.markMap.trans N.realEq).symm).trans (Equiv.refl _).symm).symm).trans
          ((Pr.arity M.hμ M.X).trans (Pr.arity N.hμ N.X).symm) := by
      ext k
      simp
    rw [hE]
    exact hB
  have hfin : #M.bIdx < M.μ := (Cardinal.lt_aleph0_of_finite M.bIdx).trans hμ0
  have hres := infra_72_tiedFreeMixed_of_sameGalois hlev.le f.onX
    (asTuple M.incl M.incl_arrow M.b) (Pr.assign N.hμ N.X) (infra_82_markImage f)
    (Equiv.refl M.bIdx) (Equiv.refl M.bIdx)
    ((Equiv.refl _).trans (f.markMap.trans N.realEq).symm)
    (infra_82_host_level_ge _) le_rfl hfin hT hR
  exact hres

/-- **Lemma 8.2(4) for P.scheme (proved).** English: "Same-level arrows preserve bounded pair
orbits." For a stationary prescription satisfying Definition 8.1 (commutes with isomorphisms;
tied free extension along arrows), on a tail of levels, every same-level marked arrow `f : M → N`
carries bounded lists with the same pair orbit in `M` to lists with the same pair orbit in `N`. -/
theorem infra_82_orbit_preservation_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) (hiso : Pr.CommutesWithIso)
    (hTA : Pr.TiedAlong) :
    ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∀ (M N : MarkedPair K oneVertexShape P.scheme Pr)
        (f : MarkedArrow K oneVertexShape P.scheme Pr M N),
        M.μ ∈ T → M.μ = N.μ →
        ∀ {ι : Type u} (t₁ t₂ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y)),
          #ι < M.μ →
          PairOrbitEq M M (Equiv.refl _) t₁ t₂ →
          PairOrbitEq N N (Equiv.refl _) (fun i => f.onY.mapOcc (t₁ i))
            (fun i => f.onY.mapOcc (t₂ i)) := by
  obtain ⟨T, hT, H⟩ := infra_82_orbit_preservation_of_tied_single P Pr hiso
  exact ⟨T, hT, fun M N f hM hlev => H M N f hM hlev
    (infra_82_mark_tied_along_single hTA f hlev)⟩

end
end AEC
