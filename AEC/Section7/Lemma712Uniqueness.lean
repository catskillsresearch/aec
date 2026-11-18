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
      (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i)), (∀ i, #(L.indexAt i) < μ) →
      #(Σ i, L.indexAt i) ≤ μ → #(Σ i, L'.indexAt i) ≤ μ →
      ∀ (C : TiedListWitnessingChain L) (C' : TiedListWitnessingChain L'),
      (∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) →
      SameGaloisType C.marksWhole C'.marksWhole (Equiv.sigmaCongr e.toEquiv ei) (Equiv.refl _)

/-- **Lemma 7.12 from the marks statement (proved glue, cycle 88).** Clause (1) by
`lemma_7_12_existence`; clause (2) by `infra_712_trans_level` through the chains' marks. -/
theorem lemma_7_12_of_marks (P : SingleModelData K) (hm : infra_712u_marks_statement P) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ)),
        (∀ (L : TupleList P.scheme (Tail.mem hT hμ) A) [LinearOrder L.δ] [L.FiniteEach] [WellFoundedLT L.δ],
          #L.δ ≤ μ → ProductIndependentTied L →
          ∃ C : TiedListWitnessingChain L, C.AllDominatedIncrement) ∧
        (∀ (L L' : TupleList P.scheme (Tail.mem hT hμ) A) [LinearOrder L.δ] [L.FiniteEach] [WellFoundedLT L.δ]
            [LinearOrder L'.δ] [L'.FiniteEach] [WellFoundedLT L'.δ]
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
  · intro L L' _ _ _ _ _ _ e ei hs hs' ⟨C⟩ ⟨C'⟩ hm1
    have h0 : μ ∈ recursionClosedLevels P ℵ₀ :=
      infra_712_recursionClosed_of_615 hμ.2.1 le_rfl (le_self_add.trans_lt hμ.2.2)
    have hb : ∀ i, #(L.indexAt i) < μ := fun i => haveI := L.finite_each i
      (Cardinal.lt_aleph0_of_finite _).trans_le ((le_self_add : ℵ₀ ≤ infra_75_wide P ℵ₀).trans hμ.2.2.le)
    have hM := hm _ hμ A L L' e ei hb hs hs' C C' hm1
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
    (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (h0 : μ ∈ recursionClosedLevels P σ) (h1 : Order.succ σ ≤ μ)
    {A M N : P.scheme.Object μ hμ}
    (a : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ M))
    (ha : P.scheme.permitted (X := A) (Y := M) a)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ M) (P.scheme.asSystem hμ N))
    (hg : P.scheme.permitted (X := M) (Y := N) g)
    (q : TupleOver K oneVertexShape P.scheme hμ M) (hqν : q.ν = μ) (hidx : #q.idx ≤ σ)
    (hq : IsTiedFree a (q.restrict a ha) q (Equiv.refl _))
    (r : TupleOver K oneVertexShape P.scheme hμ N) (hrν : r.ν = μ) (er : q.idx ≃ r.idx)
    (hr : IsTiedFree (SystemArrow.comp a g) (q.restrict a ha) r er) :
    SameGaloisType q (r.restrict g hg) er (Equiv.refl _) := by
  have hrM := infra_712u_tiedFree_restrict a g hg (q.restrict a ha) r er hr
  have H := infra_73_tied_unique P σ hσ hμ h0 h1 a ha (q.restrict a ha) hqν
    hidx q (r.restrict g hg) (Equiv.refl _) er hqν hrν hq hrM
  have H2 := infra_612_sameGalois_trans_equiv H er
  exact infra_712u_sg_congr_right (infra_712_sg_congr_left H2 (fun _ => rfl))
    (fun x => er.apply_symm_apply x)

/-- **Tied freeness depends on the base tuple only through its Galois type (proved, cycle 88).**
Finite base tuples at the level. -/
theorem infra_712u_tiedFree_base_sameGalois {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (p p' : TupleOver K oneVertexShape P.scheme hμ A) (hν : p.ν = μ) (hν' : p'.ν = μ)
    (hlt : #p.idx < μ) (e : p'.idx ≃ p.idx)
    (hS : SameGaloisType p' p e (Equiv.refl _))
    (r : TupleOver K oneVertexShape P.scheme hμ B) (er : p.idx ≃ r.idx)
    (hT : IsTiedFree f p r er) : IsTiedFree f p' r (e.trans er) := by
  have hM : IsTiedFreeMixed f p r er := hT
  have H := infra_711_tiedFree_base_equiv f p p' e r er (fun {β} Z hβ => by
    have D := infra_72_diagramEq_of_sameGalois hS Z hν' hν hlt hβ
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
    (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (h0 : μ ∈ recursionClosedLevels P σ) (h1 : Order.succ σ ≤ μ)
    {A M M' N : P.scheme.Object μ hμ}
    (a : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ M))
    (a' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ M'))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ M) (P.scheme.asSystem hμ N))
    (g' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ M') (P.scheme.asSystem hμ N))
    (hcomm : SystemArrow.comp a g = SystemArrow.comp a' g')
    (q : TupleOver K oneVertexShape P.scheme hμ M) (q' : TupleOver K oneVertexShape P.scheme hμ M')
    (hqν : q.ν = μ) (hqν' : q'.ν = μ) (hidx : #q.idx ≤ σ)
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
  have hL := infra_610_closed_level P σ hσ hμ h0
  have hσμ : σ < μ := (Order.lt_succ_of_not_isMax (not_isMax σ)).trans_le h1
  obtain ⟨r, er, hrν, -, hr⟩ := infra_610_tied_free_lift P σ hσ hμ h0 h1
    (SystemArrow.comp a g) trivial (q.restrict a trivial) hqν hidx
  have S1 := infra_712u_step P hμ σ hσ h0 h1 a trivial g trivial q hqν hidx hq r hrν er hr
  have hr' : IsTiedFree (SystemArrow.comp a' g') (q'.restrict a' trivial) r (e.trans er) := by
    rw [← hcomm]
    exact infra_712u_tiedFree_base_sameGalois _ (q.restrict a trivial) (q'.restrict a' trivial)
      hqν hqν' (hidx.trans_lt hσμ) e hS r er hr
  have hidx' : #q'.idx ≤ σ := (Cardinal.mk_congr e).le.trans hidx
  have S2 := infra_712u_step P hμ σ hσ h0 h1 a' trivial g' trivial q' hqν' hidx' hq' r hrν _ hr'
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

section ChainSide
variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
  {A : P.scheme.Object μ hμ} {L : TupleList P.scheme hμ A} [LinearOrder L.δ]

/-- A witnessing chain forgets to a pre-chain. -/
def TiedListWitnessingChain.toPre (C : TiedListWitnessingChain L) : TiedListPreChain L :=
  { C with }

theorem TiedListWitnessingChain.toPre_free (C : TiedListWitnessingChain L) (k : L.δ) :
    C.toPre.FreeAt k := C.free k

/-- **A bounded chain mark's freeness at any later stage (proved, cycle 90).** -/
theorem TiedListWitnessingChain.free_at_of_lt (C : TiedListWitnessingChain L) (k : L.δ)
    (hb : #(L.indexAt k) < μ) (j : WithTop L.δ) (hj : (k : WithTop L.δ) < j) :
    IsTiedFree (C.into (k : WithTop L.δ))
      ((asTuple (C.step hj.le) (C.step_arrow _) (C.mark k j hj)).restrict
        (C.into (k : WithTop L.δ)) (C.into_arrow _))
      (asTuple (C.step hj.le) (C.step_arrow _) (C.mark k j hj)) (Equiv.refl _) :=
  C.toPre.free_pull_of_lt k hb (C.toPre_free k) j hj

/-- **A chain mark's freeness at any later stage (proved, cycle 88).** -/
theorem TiedListWitnessingChain.free_at [L.FiniteEach] (C : TiedListWitnessingChain L) (k : L.δ)
    (j : WithTop L.δ) (hj : (k : WithTop L.δ) < j) :
    IsTiedFree (C.into (k : WithTop L.δ))
      ((asTuple (C.step hj.le) (C.step_arrow _) (C.mark k j hj)).restrict
        (C.into (k : WithTop L.δ)) (C.into_arrow _))
      (asTuple (C.step hj.le) (C.step_arrow _) (C.mark k j hj)) (Equiv.refl _) :=
  C.toPre.free_pull k (C.toPre_free k) j hj

/-- **A chain mark's marginal over `A` is the list entry's type (proved, cycle 88).** One
amalgam: `C.top`. -/
theorem TiedListWitnessingChain.marginal_sameGalois (C : TiedListWitnessingChain L) (k : L.δ)
    (j : WithTop L.δ) (hj : (k : WithTop L.δ) < j) :
    SameGaloisType ((asTuple (C.step hj.le) (C.step_arrow _) (C.mark k j hj)).restrict
        (C.into (k : WithTop L.δ)) (C.into_arrow _)) (L.one k) (Equiv.refl _) (Equiv.refl _) := by
  refine ⟨μ, hμ, C.top, SystemArrow.comp (C.step (le_top : j ≤ ⊤)) C.toTop, C.listToTop,
    P.scheme.comp _ _ (C.step_arrow _) C.toTop_arrow, C.listToTop_arrow, fun v => ?_, fun a => ?_⟩
  · refine DFunLike.ext _ _ fun x => ?_
    have e1 := DFunLike.congr_fun (C.step_comp hj.le (le_top : j ≤ ⊤) v)
      ((C.into (k : WithTop L.δ)).onVertex v x)
    have e2 := DFunLike.congr_fun (C.into_step (le_top : (k : WithTop L.δ) ≤ ⊤) v) x
    have e3 := DFunLike.congr_fun (C.comm_A v) x
    exact (congrArg (C.toTop.onVertex v) e1).trans
      ((congrArg (C.toTop.onVertex v) e2).trans e3)
  · have h1 := C.mark_step k hj (le_top : j ≤ ⊤) a
    have h2 := C.mark_spec k a
    exact (congrArg C.toTop.mapOcc h1).trans h2

/-- **7.12(2) successor of the common objects, chain form (proved, cycle 88).** For two
witnessing chains with the same successive marginals over `A`, stages `M_j`, `M'_{e j}` mapped
compatibly over `A` into a common `N` extend to a common `N₁` receiving the next stages `M_{j₁}`,
`M'_{j₁'}` and identifying the marks `b_j`, `b'_{e j}` (`infra_712u_succ`). -/
theorem infra_712b_chain_succ (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (h0 : μ ∈ recursionClosedLevels P σ) (h1 : Order.succ σ ≤ μ) (h0' : μ ∈ recursionClosedLevels P ℵ₀)
    {A : P.scheme.Object μ hμ} {L L' : TupleList P.scheme hμ A} [LinearOrder L.δ]
    [LinearOrder L'.δ] (C : TiedListWitnessingChain L) (C' : TiedListWitnessingChain L')
    (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i))
    (hm : ∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _))
    (j : L.δ) (j₁ : WithTop L.δ) (hj : (j : WithTop L.δ) < j₁)
    (j₁' : WithTop L'.δ) (hj' : ((e j : L'.δ) : WithTop L'.δ) < j₁') (hidx : #(L.indexAt j) ≤ σ)
    {N : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C.stage j))
      (P.scheme.asSystem hμ N))
    (g' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C'.stage (e j)))
      (P.scheme.asSystem hμ N))
    (hcomm : SystemArrow.comp (C.into j) g = SystemArrow.comp (C'.into (e j)) g') :
    ∃ (N₁ : P.scheme.Object μ hμ)
      (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ N) (P.scheme.asSystem hμ N₁))
      (k : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C.stage j₁))
        (P.scheme.asSystem hμ N₁))
      (k' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C'.stage j₁'))
        (P.scheme.asSystem hμ N₁)),
      (∀ v, (k.onVertex v).comp ((C.step hj.le).onVertex v) = (h.onVertex v).comp (g.onVertex v)) ∧
      (∀ v, (k'.onVertex v).comp ((C'.step hj'.le).onVertex v) =
        (h.onVertex v).comp (g'.onVertex v)) ∧
      ∀ a : L.indexAt j, (⟨(C.mark j j₁ hj a).1, k.onVertex _ (C.mark j j₁ hj a).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ N₁)) =
        ⟨(C'.mark (e j) j₁' hj' (ei j a)).1, k'.onVertex _ (C'.mark (e j) j₁' hj' (ei j a)).2⟩ := by
  have hσμ : σ < μ := (Order.lt_succ_of_not_isMax (not_isMax σ)).trans_le h1
  have hb : #(L.indexAt j) < μ := hidx.trans_lt hσμ
  have hb' : #(L'.indexAt (e j)) < μ := (Cardinal.mk_congr (ei j)).symm.le.trans_lt hb
  let q := asTuple (C.step hj.le) (C.step_arrow _) (C.mark j j₁ hj)
  let q' := asTuple (C'.step hj'.le) (C'.step_arrow _) (C'.mark (e j) j₁' hj')
  let qr := q.restrict (C.into (j : WithTop L.δ)) (C.into_arrow _)
  let q'r := q'.restrict (C'.into ((e j : L'.δ) : WithTop L'.δ)) (C'.into_arrow _)
  have M1 : SameGaloisType qr (L.one j) (Equiv.refl _) (Equiv.refl _) :=
    C.marginal_sameGalois j j₁ hj
  have M2 : SameGaloisType q'r (L'.one (e j)) (Equiv.refl _) (Equiv.refl _) :=
    C'.marginal_sameGalois (e j) j₁' hj'
  have H23 : SameGaloisType (L'.one (e j)) (L.one j) (Equiv.refl _) (ei j) := (hm j).symm
  have T1 : SameGaloisType q'r (L.one j) (Equiv.refl _) (ei j) :=
    infra_712_trans_level P hμ h0' (t1 := q'r) (t2 := L'.one (e j)) (t3 := L.one j)
      (Equiv.refl _) (Equiv.refl _) (ei j) rfl rfl rfl M2 H23
  have H34 : SameGaloisType (L.one j) qr (ei j) (ei j) :=
    infra_612_sameGalois_trans_equiv M1.symm (ei j)
  have T2 : SameGaloisType q'r qr (Equiv.refl _) (ei j) :=
    infra_712_trans_level P hμ h0' (t1 := q'r) (t2 := L.one j) (t3 := qr)
      (Equiv.refl _) (ei j) (ei j) rfl rfl rfl T1 H34
  have hS : SameGaloisType q'r qr (ei j).symm (Equiv.refl _) :=
    infra_712u_sg_congr_right (infra_612_sameGalois_trans_equiv T2 (ei j).symm)
      (fun x => (ei j).symm_apply_apply x)
  obtain ⟨N₁, h, k, k', H1, H2, H3⟩ := infra_712u_succ P hμ σ hσ h0 h1 (C.into (j : WithTop L.δ))
    (C'.into ((e j : L'.δ) : WithTop L'.δ)) g g' hcomm q q' rfl rfl hidx
    (C.free_at_of_lt j hb j₁ hj) (C'.free_at_of_lt (e j) hb' j₁' hj') (ei j).symm hS
  exact ⟨N₁, h, k, k', H1, H2, fun a => H3 a⟩

/-- **7.12(2) successor, finite entries (proved, cycle 88; corollary of `infra_712b_chain_succ`).** -/
theorem infra_712u_chain_succ (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
    {A : P.scheme.Object μ hμ} {L L' : TupleList P.scheme hμ A} [LinearOrder L.δ] [L.FiniteEach]
    [LinearOrder L'.δ] (C : TiedListWitnessingChain L) (C' : TiedListWitnessingChain L')
    (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i))
    (hm : ∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _))
    (j : L.δ) (j₁ : WithTop L.δ) (hj : (j : WithTop L.δ) < j₁)
    (j₁' : WithTop L'.δ) (hj' : ((e j : L'.δ) : WithTop L'.δ) < j₁')
    {N : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C.stage j))
      (P.scheme.asSystem hμ N))
    (g' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C'.stage (e j)))
      (P.scheme.asSystem hμ N))
    (hcomm : SystemArrow.comp (C.into j) g = SystemArrow.comp (C'.into (e j)) g') :
    ∃ (N₁ : P.scheme.Object μ hμ)
      (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ N) (P.scheme.asSystem hμ N₁))
      (k : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C.stage j₁))
        (P.scheme.asSystem hμ N₁))
      (k' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C'.stage j₁'))
        (P.scheme.asSystem hμ N₁)),
      (∀ v, (k.onVertex v).comp ((C.step hj.le).onVertex v) = (h.onVertex v).comp (g.onVertex v)) ∧
      (∀ v, (k'.onVertex v).comp ((C'.step hj'.le).onVertex v) =
        (h.onVertex v).comp (g'.onVertex v)) ∧
      ∀ a : L.indexAt j, (⟨(C.mark j j₁ hj a).1, k.onVertex _ (C.mark j j₁ hj a).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ N₁)) =
        ⟨(C'.mark (e j) j₁' hj' (ei j a)).1, k'.onVertex _ (C'.mark (e j) j₁' hj' (ei j a)).2⟩ :=
  infra_712b_chain_succ P hμ ℵ₀ le_rfl h0 h1 h0 C C' e ei hm j j₁ hj j₁' hj'
    (haveI := L.finite_each j; (Cardinal.lt_aleph0_of_finite _).le) g g' hcomm

end ChainSide

/-- **7.12(2), the common object (statement; open tip `infra_712u_common`).** Two witnessing
chains with the same successive marginals have a common level-`μ` object receiving both last
stages compatibly over `A` and identifying corresponding marks (English: the final `N_δ`). -/
def infra_712u_common_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_712_levels P →
    ∀ (A : P.scheme.Object μ hμ) (L L' : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ] [LinearOrder L'.δ] [WellFoundedLT L'.δ]
      (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i)), (∀ i, #(L.indexAt i) < μ) →
      #(Σ i, L.indexAt i) ≤ μ → #(Σ i, L'.indexAt i) ≤ μ →
      ∀ (C : TiedListWitnessingChain L) (C' : TiedListWitnessingChain L'),
      (∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) →
      ∃ (N : P.scheme.Object μ hμ)
        (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C.stage ⊤))
          (P.scheme.asSystem hμ N))
        (g' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C'.stage ⊤))
          (P.scheme.asSystem hμ N)),
        (∀ v, (g.onVertex v).comp ((C.into ⊤).onVertex v) =
          (g'.onVertex v).comp ((C'.into ⊤).onVertex v)) ∧
        ∀ (i : L.δ) (a : L.indexAt i),
          g.mapOcc (C.mark i ⊤ (WithTop.coe_lt_top i) a) =
            g'.mapOcc (C'.mark (e i) ⊤ (WithTop.coe_lt_top (e i)) (ei i a))

/-- **7.12(2) marks from the common object (proved glue, cycle 88).** -/
theorem infra_712u_marks_of_common (P : SingleModelData K)
    (hc : infra_712u_common_statement P) : infra_712u_marks_statement P := by
  intro μ hμ hl A L L' _ _ _ _ e ei hb hs hs' C C' hm
  obtain ⟨N, g, g', hA, hmk⟩ := hc hμ hl A L L' e ei hb hs hs' C C' hm
  let σ := Equiv.sigmaCongr e.toEquiv ei
  let Φ1 : (Σ i, L.indexAt i) → Occurrence K oneVertexShape (P.scheme.asSystem hμ N) :=
    fun q => g.mapOcc (C.mark q.1 ⊤ (WithTop.coe_lt_top q.1) q.2)
  let Φ2 : (Σ i, L'.indexAt i) → Occurrence K oneVertexShape (P.scheme.asSystem hμ N) :=
    fun q => g'.mapOcc (C'.mark q.1 ⊤ (WithTop.coe_lt_top q.1) q.2)
  refine ⟨μ, hμ, N, g, g', trivial, trivial, hA, fun p => ?_⟩
  obtain ⟨q, rfl⟩ := σ.surjective p
  show Φ1 (σ.symm (σ q)) = Φ2 (σ q)
  exact (congrArg Φ1 (σ.symm_apply_apply q)).trans (hmk q.1 q.2)

/-- **7.12(2) base of the common objects (proved, cycle 88).** The first stage of a witnessing
chain is `A` itself (`first`), so it maps back onto `A` inverting `into`. -/
theorem infra_712u_base {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {L : TupleList P.scheme hμ A} [LinearOrder L.δ]
    (C : TiedListWitnessingChain L) (k : WithTop L.δ) (hk : ∀ j, k ≤ j) :
    ∃ r : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C.stage k)) (P.scheme.asSystem hμ A),
      (∀ x, r.onVertex PUnit.unit ((C.into k).onVertex PUnit.unit x) = x) ∧
      (∀ y, (C.into k).onVertex PUnit.unit (r.onVertex PUnit.unit y) = y) := by
  obtain ⟨ψ, h1, h2⟩ := infra_78_struct_inverse (C.into k) (fun v => C.first k hk v)
  exact ⟨ψ, h2, h1⟩

end
end AEC
