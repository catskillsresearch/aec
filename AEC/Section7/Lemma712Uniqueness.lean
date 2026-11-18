module

public import AEC.Section7.Lemma712Products

/-!
# Lemma 7.12 (2): uniqueness (cycle 88)

* `infra_712_trans_level`: Galois transitivity when all three hosts are at the level, for any
  index size (two level-`μ` type-identifying amalgams, then Theorem 4.11(1) amalgamation over the
  middle host).
* `TiedListWitnessingChain.marksWhole`: the chain's marks in its last stage; same type as the
  whole list via `C.top`.
* `lemma_7_12_of_marks`: the full paper statement `lemma_7_12` from `infra_712u_marks_statement`
  (the two chains' marks have the same type), on the tail `infra_712_levels P`.
-/

@[expose] public section

namespace AEC
noncomputable section
open Cardinal FirstOrder
variable {K : AbstractElementaryClass.{u}}
/-- **Galois transitivity with all three hosts at the level (proved, cycle 88).** Any size of
index: two level-`μ` type-identifying amalgams (`infra_78_same_level_type_amalgam`) are
amalgamated over the middle host by Theorem 4.11(1) (`ClosedLevel.amalgamation`). -/
theorem infra_712_trans_level (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (h0 : μ ∈ recursionClosedLevels P ℵ₀) {A : P.scheme.Object μ hμ}
    {t1 t2 t3 : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    (e1 : t1.idx ≃ ι) (e2 : t2.idx ≃ ι) (e3 : t3.idx ≃ ι)
    (h1 : t1.ν = μ) (h2 : t2.ν = μ) (h3 : t3.ν = μ)
    (h12 : SameGaloisType t1 t2 e1 e2) (h23 : SameGaloisType t2 t3 e2 e3) :
    SameGaloisType t1 t3 e1 e3 := by
  classical
  have : CategoricalUnbounded K := P.D.categoricalUnbounded
  have hL := infra_610_closed_level P ℵ₀ le_rfl hμ h0
  obtain ⟨T, f1, f2, -, -, hc12, hv12⟩ := infra_78_same_level_type_amalgam t1 t2 e1 e2 h1 h2 h12
  obtain ⟨U, g2, g3, -, -, hc23, hv23⟩ := infra_78_same_level_type_amalgam t2 t3 e2 e3 h2 h3 h23
  have hc2 : Model.card t2.host.model = μ := by simpa [h2] using t2.host.card
  obtain ⟨M, k1, k2, hM, hk1, hk2, hcM, hbase⟩ :=
    ClosedLevel.amalgamation hL t2.host.model T.model U.model (f2.onVertex PUnit.unit)
      (g2.onVertex PUnit.unit) t2.host.mem T.mem U.mem (f2.onVertex_strong _)
      (g2.onVertex_strong _) hc2 T.card U.card
  let top : SMObject K μ := SMObject.ofModel M hM hcM
  let φ : M.carrier ≃[K.τ] top.model.carrier := SMObject.ofModelEquiv M hM hcM
  have hφ : K.Strong φ.toEmbedding := strong_of_equiv K φ hM
  let a1 : SystemArrow K oneVertexShape (P.scheme.asSystem hμ T) (P.scheme.asSystem hμ top) :=
    oneVertexArrow (φ.toEmbedding.comp k1) (K.strong_trans _ _ hk1 hφ)
  let a2 : SystemArrow K oneVertexShape (P.scheme.asSystem hμ U) (P.scheme.asSystem hμ top) :=
    oneVertexArrow (φ.toEmbedding.comp k2) (K.strong_trans _ _ hk2 hφ)
  have hmid : ∀ y, a1.onVertex PUnit.unit (f2.onVertex PUnit.unit y) =
      a2.onVertex PUnit.unit (g2.onVertex PUnit.unit y) := fun y => congrArg φ (hbase y)
  refine ⟨μ, hμ, top, f1.comp a1, g3.comp a2, trivial, trivial, fun v => ?_, fun i => ?_⟩
  · have hv : v = PUnit.unit := Subsingleton.elim _ _
    subst hv
    refine DFunLike.ext _ _ fun x => ?_
    show a1.onVertex _ (f1.onVertex _ (t1.incl.onVertex _ x)) =
      a2.onVertex _ (g3.onVertex _ (t3.incl.onVertex _ x))
    have q1 : f1.onVertex PUnit.unit (t1.incl.onVertex PUnit.unit x) =
        f2.onVertex PUnit.unit (t2.incl.onVertex PUnit.unit x) := DFunLike.congr_fun (hc12 PUnit.unit) x
    have q3 : g2.onVertex PUnit.unit (t2.incl.onVertex PUnit.unit x) =
        g3.onVertex PUnit.unit (t3.incl.onVertex PUnit.unit x) := DFunLike.congr_fun (hc23 PUnit.unit) x
    exact (congrArg (a1.onVertex PUnit.unit) q1).trans
      ((hmid _).trans (congrArg (a2.onVertex PUnit.unit) q3))
  · have E1 := congrArg (fun o : Occurrence K oneVertexShape (P.scheme.asSystem hμ T) =>
      (⟨o.1, a1.onVertex o.1 o.2⟩ : Occurrence K oneVertexShape (P.scheme.asSystem hμ top)))
      (hv12 i)
    have E3 := congrArg (fun o : Occurrence K oneVertexShape (P.scheme.asSystem hμ U) =>
      (⟨o.1, a2.onVertex o.1 o.2⟩ : Occurrence K oneVertexShape (P.scheme.asSystem hμ top)))
      (hv23 i)
    refine E1.trans (Eq.trans ?_ E3)
    simp only
    generalize t2.val (e2.symm i) = o
    obtain ⟨⟨⟩, y⟩ := o
    exact Sigma.ext rfl (heq_of_eq (hmid y))

/-- The whole list of marks of a witnessing chain, in its last stage, over `A`. -/
def TiedListWitnessingChain.marksWhole {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ} {L : TupleList P.scheme hμ A}
    [LinearOrder L.δ] (C : TiedListWitnessingChain L) : TupleOver K oneVertexShape P.scheme hμ A where
  ν := μ
  hν := hμ
  host := C.stage ⊤
  incl := C.into ⊤
  incl_arrow := C.into_arrow ⊤
  idx := Σ i, L.indexAt i
  val := fun p => C.mark p.1 ⊤ (WithTop.coe_lt_top p.1) p.2

/-- The chain's marks have the type of the whole list (one amalgam: `C.top`). -/
theorem TiedListWitnessingChain.marksWhole_sameGalois {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ} {L : TupleList P.scheme hμ A}
    [LinearOrder L.δ] (C : TiedListWitnessingChain L) :
    SameGaloisType C.marksWhole L.whole (Equiv.refl _) (Equiv.refl _) :=
  ⟨μ, hμ, C.top, C.toTop, C.listToTop, C.toTop_arrow, C.listToTop_arrow, C.comm_A,
    fun p => C.mark_spec p.1 p.2⟩

/-- **7.12(2), uniqueness of the marks (statement; open tip `infra_712u_marks`).** At a 7.12
level, two witnessing chains of lists with the same successive marginal types over `A` have
marks of the same type over `A` (English proof: common objects `N_i` receiving both chains). -/
def infra_712u_marks_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_712_levels P →
    ∀ (A : P.scheme.Object μ hμ) (L L' : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ] [LinearOrder L'.δ] [WellFoundedLT L'.δ]
      (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i)),
      #(Σ i, L.indexAt i) ≤ μ → #(Σ i, L'.indexAt i) ≤ μ →
      ∀ (C : TiedListWitnessingChain L) (C' : TiedListWitnessingChain L'),
      (∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) →
      SameGaloisType C.marksWhole C'.marksWhole (Equiv.sigmaCongr e.toEquiv ei) (Equiv.refl _)

/-- **Lemma 7.12 from the marks statement (proved glue, cycle 88).** Clause (1) by
`lemma_7_12_existence`; clause (2) by `infra_712_trans_level` through the chains' marks. -/
theorem lemma_7_12_of_marks (P : SingleModelData K) (hm : infra_712u_marks_statement P) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ)),
        (∀ (L : TupleList P.scheme (Tail.mem hT hμ) A) [LinearOrder L.δ] [WellFoundedLT L.δ],
          #L.δ ≤ μ → ProductIndependentTied L →
          ∃ C : TiedListWitnessingChain L, C.AllDominatedIncrement) ∧
        (∀ (L L' : TupleList P.scheme (Tail.mem hT hμ) A) [LinearOrder L.δ] [WellFoundedLT L.δ]
            [LinearOrder L'.δ] [WellFoundedLT L'.δ]
            (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i)),
          #(Σ i, L.indexAt i) ≤ μ → #(Σ i, L'.indexAt i) ≤ μ →
          Nonempty (TiedListWitnessingChain L) → Nonempty (TiedListWitnessingChain L') →
          (∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) →
          SameGaloisType L.whole L'.whole
            (Equiv.sigmaCongr e.toEquiv ei) (Equiv.refl _)) := by
  refine ⟨infra_712_levels P, infra_712_levels_tail P, fun μ hμ A => ⟨?_, ?_⟩⟩
  · obtain ⟨ht, hc, hw⟩ := hμ
    have hw0 : ℵ₀ ≤ infra_75_wide P ℵ₀ := le_self_add
    have h0lt : ℵ₀ < μ := hw0.trans_lt hw
    exact lemma_7_12_existence P _ ht hc (infra_712_recursionClosed_of_615 hc le_rfl h0lt)
      (Order.succ_le_of_lt h0lt) (infra_712_recursionClosed_of_615 hc hw0 hw)
      (Order.succ_le_of_lt hw) A
  · intro L L' _ _ _ _ e ei hs hs' ⟨C⟩ ⟨C'⟩ hm1
    have h0 : μ ∈ recursionClosedLevels P ℵ₀ :=
      infra_712_recursionClosed_of_615 hμ.2.1 le_rfl (le_self_add.trans_lt hμ.2.2)
    have hM := hm _ hμ A L L' e ei hs hs' C C' hm1
    have hA := infra_612_sameGalois_trans_equiv C.marksWhole_sameGalois.symm
      (Equiv.sigmaCongr e.toEquiv ei)
    have hA' : SameGaloisType L.whole C.marksWhole (Equiv.sigmaCongr e.toEquiv ei)
        (Equiv.sigmaCongr e.toEquiv ei) := hA
    have h1 := infra_712_trans_level P _ h0 _ _ _ rfl rfl rfl hA' hM
    exact infra_712_trans_level P _ h0 _ _ _ rfl rfl rfl h1 C'.marksWhole_sameGalois

/-- **Restriction of tied freeness, general base tuple (proved, cycle 88).** If `q` over `B` is
tied free along `X → A → B` from `p`, its restriction to `A` is tied free along `X → A` from `p`
(the proof of `infra_78_tiedFree_restrict`, any base tuple and coordinate map). -/
theorem infra_712u_tiedFree_restrict
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ X)
    (q : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ q.idx)
    (h : IsTiedFree (SystemArrow.comp g f) p q eB) :
    IsTiedFree g p (q.restrict f hf) eB := by
  intro seq ι Z Z0 hκ hι hιμ hmove
  have hidx : #p.idx < μ := infra_78_idx_lt_of_seq (q := p) seq hκ
  have hsum : #(p.idx ⊕ ι) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hidx hιμ
  let fZ : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) := fun b => pushOcc f (Z b)
  have hmove' : infra_73_isMove (SystemArrow.comp g f) seq fZ Z0 := by
    intro i
    have h1 := hmove i
    let ys := seqJoint
      (fun j => (⟨(seq.family i j).1, g.onVertex (seq.family i j).1 (seq.family i j).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ A))) Z
    have h2 := P.scheme.diagram_preserved A B f hf ys hsum hsum
    have hpush : (fun t => (⟨(ys t).1, f.onVertex (ys t).1 (ys t).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) =
        seqJoint (fun j => (⟨(seq.family i j).1,
          (SystemArrow.comp g f).onVertex (seq.family i j).1 (seq.family i j).2⟩ :
            Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) fZ := by
      funext t
      cases t <;> rfl
    rw [hpush] at h2
    exact P.scheme.diagram_trans _ _ _ _ _ _ h1 h2
  exact h seq fZ Z0 hκ hι hιμ hmove'

theorem infra_712u_sg_congr_right {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    {f : t1.idx ≃ ι} {g g' : t2.idx ≃ ι} (h : SameGaloisType t1 t2 f g)
    (hg : ∀ x, g x = g' x) : SameGaloisType t1 t2 f g' := Equiv.ext hg ▸ h

/-- **7.12(2) successor comparison (proved, cycle 88).** A finite `q` over `M`, tied free
along `a : A → M` from its marginal, and a tied free extension `r` of the same marginal over
`N ⊇ M` (along `a ≫ g`) have the same type over `M`: `r ↾ M` is tied free over `M`
(`infra_712u_tiedFree_restrict`), and tied free extensions are unique
(`infra_73_tied_unique`). With `infra_78_same_level_type_amalgam` this is the amalgamation
step "identify `bᵢ` with `c`" of the English proof. -/
theorem infra_712u_step (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
    {A M N : P.scheme.Object μ hμ}
    (a : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ M))
    (ha : P.scheme.permitted (X := A) (Y := M) a)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ M) (P.scheme.asSystem hμ N))
    (hg : P.scheme.permitted (X := M) (Y := N) g)
    (q : TupleOver K oneVertexShape P.scheme hμ M) (hqν : q.ν = μ) (hfin : Finite q.idx)
    (hq : IsTiedFree a (q.restrict a ha) q (Equiv.refl _))
    (r : TupleOver K oneVertexShape P.scheme hμ N) (hrν : r.ν = μ) (er : q.idx ≃ r.idx)
    (hr : IsTiedFree (SystemArrow.comp a g) (q.restrict a ha) r er) :
    SameGaloisType q (r.restrict g hg) er (Equiv.refl _) := by
  have hrM := infra_712u_tiedFree_restrict a g hg (q.restrict a ha) r er hr
  have H := infra_73_tied_unique P ℵ₀ le_rfl hμ h0 h1 a ha (q.restrict a ha) hqν
    (Cardinal.lt_aleph0_of_finite q.idx).le q (r.restrict g hg) (Equiv.refl _) er hqν hrν hq hrM
  have H2 := infra_612_sameGalois_trans_equiv H er
  exact infra_712u_sg_congr_right (infra_712_sg_congr_left H2 (fun _ => rfl))
    (fun x => er.apply_symm_apply x)

/-- **Tied freeness depends on the base tuple only through its Galois type (proved, cycle 88).**
Finite base tuples at the level. -/
theorem infra_712u_tiedFree_base_sameGalois {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (p p' : TupleOver K oneVertexShape P.scheme hμ A) (hν : p.ν = μ) (hν' : p'.ν = μ)
    (hfin : Finite p.idx) (e : p'.idx ≃ p.idx)
    (hS : SameGaloisType p' p e (Equiv.refl _))
    (r : TupleOver K oneVertexShape P.scheme hμ B) (er : p.idx ≃ r.idx)
    (hT : IsTiedFree f p r er) : IsTiedFree f p' r (e.trans er) := by
  have hM : IsTiedFreeMixed f p r er := hT
  have H := infra_711_tiedFree_base_equiv f p p' e r er (fun {β} Z hβ => by
    have D := infra_72_diagramEq_of_sameGalois hS Z hν' hν
      ((Cardinal.lt_aleph0_of_finite p.idx).trans_le (P.aleph0_le hμ)) hβ
    refine infra_612_dEq_comp D (Sum.map e id) ?_ ?_
    · rintro (k | j)
      · show _ = typeJoint (p := p') Z (Sum.inl (e.symm (e k)))
        rw [Equiv.symm_apply_apply]
      · rfl
    · rintro (k | j) <;> rfl) hM
  exact H

/-- **7.12(2) successor of the common objects (proved, cycle 88).** Old stages `M`, `M'` mapped
into a common `N` compatibly over `A`; next marks `q` over `M`, `q'` over `M'` tied free from
marginals of the same type. Then there is a level-`μ` `N₁ ⊇ N` receiving both new stages over
the old ones and identifying the marks: the common tied free lift `c` over `N`
(`infra_610_tied_free_lift`), `infra_712u_step` on both sides, two type-identifying amalgams
(`infra_78_same_level_type_amalgam`) merged over `c`'s host by Theorem 4.11(1). -/
theorem infra_712u_succ (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
    {A M M' N : P.scheme.Object μ hμ}
    (a : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ M))
    (a' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ M'))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ M) (P.scheme.asSystem hμ N))
    (g' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ M') (P.scheme.asSystem hμ N))
    (hcomm : SystemArrow.comp a g = SystemArrow.comp a' g')
    (q : TupleOver K oneVertexShape P.scheme hμ M) (q' : TupleOver K oneVertexShape P.scheme hμ M')
    (hqν : q.ν = μ) (hqν' : q'.ν = μ) (hfin : Finite q.idx)
    (hq : IsTiedFree a (q.restrict a trivial) q (Equiv.refl _))
    (hq' : IsTiedFree a' (q'.restrict a' trivial) q' (Equiv.refl _))
    (e : q'.idx ≃ q.idx)
    (hS : SameGaloisType (q'.restrict a' trivial) (q.restrict a trivial) e (Equiv.refl _)) :
    ∃ (N₁ : P.scheme.Object μ hμ)
      (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ N) (P.scheme.asSystem hμ N₁))
      (k : SystemArrow K oneVertexShape (P.scheme.asSystem q.hν q.host) (P.scheme.asSystem hμ N₁))
      (k' : SystemArrow K oneVertexShape (P.scheme.asSystem q'.hν q'.host)
        (P.scheme.asSystem hμ N₁)),
      (∀ v, (k.onVertex v).comp (q.incl.onVertex v) = (h.onVertex v).comp (g.onVertex v)) ∧
      (∀ v, (k'.onVertex v).comp (q'.incl.onVertex v) = (h.onVertex v).comp (g'.onVertex v)) ∧
      ∀ x : q.idx, (⟨(q.val x).1, k.onVertex _ (q.val x).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ N₁)) =
        ⟨(q'.val (e.symm x)).1, k'.onVertex _ (q'.val (e.symm x)).2⟩ := by
  classical
  have : CategoricalUnbounded K := P.D.categoricalUnbounded
  have hL := infra_610_closed_level P ℵ₀ le_rfl hμ h0
  obtain ⟨r, er, hrν, -, hr⟩ := infra_610_tied_free_lift P ℵ₀ le_rfl hμ h0 h1
    (SystemArrow.comp a g) trivial (q.restrict a trivial) hqν (Cardinal.lt_aleph0_of_finite q.idx).le
  have S1 := infra_712u_step P hμ h0 h1 a trivial g trivial q hqν hfin hq r hrν er hr
  have hr' : IsTiedFree (SystemArrow.comp a' g') (q'.restrict a' trivial) r (e.trans er) := by
    rw [← hcomm]
    exact infra_712u_tiedFree_base_sameGalois _ (q.restrict a trivial) (q'.restrict a' trivial)
      hqν hqν' hfin e hS r er hr
  have hfin' : Finite q'.idx := Finite.of_equiv _ e.symm
  have S2 := infra_712u_step P hμ h0 h1 a' trivial g' trivial q' hqν' hfin' hq' r hrν _ hr'
  obtain ⟨T1, f1, f2, -, -, hc1, hv1⟩ := infra_78_same_level_type_amalgam q (r.restrict g trivial)
    er (Equiv.refl _) hqν hrν S1
  obtain ⟨T2, f1', f2', -, -, hc2, hv2⟩ := infra_78_same_level_type_amalgam q'
    (r.restrict g' trivial) (e.trans er) (Equiv.refl _) hqν' hrν S2
  have hcr : Model.card r.host.model = μ := by simpa [hrν] using r.host.card
  obtain ⟨M0, k1, k2, hM, hk1, hk2, hcM, hbase⟩ :=
    ClosedLevel.amalgamation hL r.host.model T1.model T2.model (f2.onVertex PUnit.unit)
      (f2'.onVertex PUnit.unit) r.host.mem T1.mem T2.mem (f2.onVertex_strong _)
      (f2'.onVertex_strong _) hcr T1.card T2.card
  let top : SMObject K μ := SMObject.ofModel M0 hM hcM
  let φ : M0.carrier ≃[K.τ] top.model.carrier := SMObject.ofModelEquiv M0 hM hcM
  have hφ : K.Strong φ.toEmbedding := strong_of_equiv K φ hM
  let b1 : SystemArrow K oneVertexShape (P.scheme.asSystem hμ T1) (P.scheme.asSystem hμ top) :=
    oneVertexArrow (φ.toEmbedding.comp k1) (K.strong_trans _ _ hk1 hφ)
  let b2 : SystemArrow K oneVertexShape (P.scheme.asSystem hμ T2) (P.scheme.asSystem hμ top) :=
    oneVertexArrow (φ.toEmbedding.comp k2) (K.strong_trans _ _ hk2 hφ)
  have hmid : ∀ y, b1.onVertex PUnit.unit (f2.onVertex PUnit.unit y) =
      b2.onVertex PUnit.unit (f2'.onVertex PUnit.unit y) := fun y => congrArg φ (hbase y)
  refine ⟨top, SystemArrow.comp r.incl (SystemArrow.comp f2 b1), SystemArrow.comp f1 b1,
    SystemArrow.comp f1' b2, fun v => ?_, fun v => ?_, fun x => ?_⟩
  · have hv : v = PUnit.unit := Subsingleton.elim _ _
    subst hv
    refine DFunLike.ext _ _ fun y => ?_
    have q1 : f1.onVertex PUnit.unit (q.incl.onVertex PUnit.unit y) =
        f2.onVertex PUnit.unit (r.incl.onVertex PUnit.unit (g.onVertex PUnit.unit y)) :=
      DFunLike.congr_fun (hc1 PUnit.unit) y
    exact congrArg (b1.onVertex PUnit.unit) q1
  · have hv : v = PUnit.unit := Subsingleton.elim _ _
    subst hv
    refine DFunLike.ext _ _ fun y => ?_
    have q2 : f1'.onVertex PUnit.unit (q'.incl.onVertex PUnit.unit y) =
        f2'.onVertex PUnit.unit (r.incl.onVertex PUnit.unit (g'.onVertex PUnit.unit y)) :=
      DFunLike.congr_fun (hc2 PUnit.unit) y
    exact (congrArg (b2.onVertex PUnit.unit) q2).trans (hmid _).symm
  · let Φ1 : q.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ top) := fun y =>
      ⟨(q.val y).1, (SystemArrow.comp f1 b1).onVertex _ (q.val y).2⟩
    let Φ2 : q'.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ top) := fun y =>
      ⟨(q'.val y).1, (SystemArrow.comp f1' b2).onVertex _ (q'.val y).2⟩
    let Ψ1 : r.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ top) := fun i =>
      ⟨(r.val i).1, b1.onVertex _ (f2.onVertex _ (r.val i).2)⟩
    let Ψ2 : r.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ top) := fun i =>
      ⟨(r.val i).1, b2.onVertex _ (f2'.onVertex _ (r.val i).2)⟩
    have E1 : ∀ i, Φ1 (er.symm i) = Ψ1 i := fun i =>
      congrArg (fun o : Occurrence K oneVertexShape (P.scheme.asSystem hμ T1) =>
        (⟨o.1, b1.onVertex o.1 o.2⟩ : Occurrence K oneVertexShape (P.scheme.asSystem hμ top)))
        (hv1 i)
    have E2 : ∀ i, Φ2 ((e.trans er).symm i) = Ψ2 i := fun i =>
      congrArg (fun o : Occurrence K oneVertexShape (P.scheme.asSystem hμ T2) =>
        (⟨o.1, b2.onVertex o.1 o.2⟩ : Occurrence K oneVertexShape (P.scheme.asSystem hμ top)))
        (hv2 i)
    have hmid' : ∀ i, Ψ1 i = Ψ2 i := by
      intro i
      show (⟨(r.val i).1, _⟩ : Occurrence K oneVertexShape (P.scheme.asSystem hμ top)) = ⟨_, _⟩
      generalize r.val i = o
      obtain ⟨⟨⟩, y⟩ := o
      exact Sigma.ext rfl (heq_of_eq (hmid y))
    have i2 : (e.trans er).symm (er x) = e.symm x := congrArg e.symm (er.symm_apply_apply x)
    show Φ1 x = Φ2 (e.symm x)
    calc Φ1 x = Φ1 (er.symm (er x)) := congrArg Φ1 (er.symm_apply_apply x).symm
      _ = Ψ1 (er x) := E1 _
      _ = Ψ2 (er x) := hmid' _
      _ = Φ2 ((e.trans er).symm (er x)) := (E2 _).symm
      _ = Φ2 (e.symm x) := congrArg Φ2 i2

/-- **Arrows out of a continuous stage (proved, cycle 88).** If `M` is covered by a directed
family `X a → M` (continuity of a chain at a limit), a compatible family `X a → Z` factors
through `M`: the directed union `U` (`infra_78_chain_union_kappa`) maps bijectively onto `M`,
so its universal arrow composes with the inverse (`infra_78_struct_inverse`). -/
theorem infra_712u_factor_continuous {P : SingleModelData K} {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (hι : #ι ≤ μ) (X : ι → P.scheme.Object μ hμ)
    (st : ∀ {a b : ι}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hμ (X a)) (P.scheme.asSystem hμ (X b)))
    (hrefl : ∀ a, st (le_refl a) = SystemArrow.refl _)
    (htrans : ∀ {a b c : ι} (h₁ : a ≤ b) (h₂ : b ≤ c),
      st (h₁.trans h₂) = SystemArrow.comp (st h₁) (st h₂))
    (M : P.scheme.Object μ hμ)
    (s : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hμ (X a)) (P.scheme.asSystem hμ M))
    (hs : ∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (st h) (s b) = s a)
    (hcov : ∀ x : ((P.scheme.asSystem hμ M).obj PUnit.unit).carrier,
      ∃ a y, (s a).onVertex PUnit.unit y = x)
    {Z : P.scheme.Object μ hμ}
    (g : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hμ (X a)) (P.scheme.asSystem hμ Z))
    (hg : ∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (st h) (g b) = g a) :
    ∃ f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ M) (P.scheme.asSystem hμ Z),
      ∀ a (y : ((P.scheme.asSystem hμ (X a)).obj PUnit.unit).carrier),
        f.onVertex PUnit.unit ((s a).onVertex PUnit.unit y) = (g a).onVertex PUnit.unit y := by
  classical
  obtain ⟨U, leg, -, hleg, -, huniv, -⟩ := infra_78_chain_union_kappa hμ hι X st hrefl htrans
  obtain ⟨u, -, hu⟩ := huniv M s (fun h => hs h)
  obtain ⟨w, -, hw⟩ := huniv Z g (fun h => hg h)
  have hbij : P.scheme.IsStructIso (X := U) (Y := M) u := by
    intro v
    have hv : v = PUnit.unit := Subsingleton.elim _ _
    subst hv
    refine ⟨(u.onVertex PUnit.unit).injective, fun x => ?_⟩
    obtain ⟨a, y, rfl⟩ := hcov x
    refine ⟨(leg a).onVertex PUnit.unit y, ?_⟩
    rw [← hu a]
    rfl
  obtain ⟨ψ, hφψ, hψφ⟩ := infra_78_struct_inverse u hbij
  refine ⟨SystemArrow.comp ψ w, fun a y => ?_⟩
  show w.onVertex PUnit.unit (ψ.onVertex PUnit.unit ((s a).onVertex PUnit.unit y)) = _
  rw [← hu a, ← hw a]
  show w.onVertex PUnit.unit (ψ.onVertex PUnit.unit (u.onVertex PUnit.unit
    ((leg a).onVertex PUnit.unit y))) = _
  rw [hψφ]
  rfl

/-- **7.12(2), the marks (open tip `infra_712u_marks`).** -/
theorem infra_712u_marks (P : SingleModelData K) : infra_712u_marks_statement P := by
  sorry

end
end AEC
