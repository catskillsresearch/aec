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

/-- **7.12(2), the marks (open tip `infra_712u_marks`).** -/
theorem infra_712u_marks (P : SingleModelData K) : infra_712u_marks_statement P := by
  sorry

end
end AEC
