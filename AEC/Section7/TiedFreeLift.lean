module

public import AEC.Section7.IsolationBound

@[expose] public section

/-!
# Tied free lift (English Theorem 6.10, tied form)

English §6.2: "In a well-ordered chart of `B` prescribe the majority answers on every query of
size at most `τ` … Lemma 6.4 gives a placement realizing all of them in an order enlargement of
`B`. This is an actual tuple in an extension object." The untied `IsFreeLift` of
`stationary_free_extension_exists` pulls each prescription back into `B` separately. Here the
Proposition 4.9 placement `z ∈ E(J)` is kept: a strong hull `N ⊇ E(I) ∪ z` of size `μ` is the
host of `qB`, and every bounded query `Z` of `B` is answered by the majority prescription.

* `infra_610_isMove_of_iso`: one structural isomorphism agreeing with `f` on a sequence and
  carrying `Z'` onto `Z` makes `Z'` a sequence-move of `Z`.
* `infra_610_tied_of_majority`: majority answers on one long sequence give the tied answer on
  every move along every long sequence (move `Z` over both sequences at once).
* `infra_610_tied_placement`: the Prop 4.9 placement as a `TupleOver` over `B` with majority
  answers at the chart arity.
* `infra_610_tied_free_lift`: existence of a tied free extension at every query size, by
  comparing placements at two arities on the test size (Theorem 6.6, `infra_73_differing_test`).
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-- A structural isomorphism `ψ` agreeing with `f` on every copy of `seq` and carrying `Z'`
onto `Z` makes `Z'` a sequence-move of `Z`. -/
theorem infra_610_isMove_of_iso
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f ψ : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hψ : P.scheme.permitted (X := A) (Y := B) ψ)
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hidxμ : #q.idx < μ) (hιμ : #ι < μ)
    (hfam : ∀ i j, (⟨(seq.family i j).1, ψ.onVertex _ (seq.family i j).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) =
      ⟨(seq.family i j).1, f.onVertex _ (seq.family i j).2⟩)
    (hZ : ∀ k, Z k = ⟨(Z' k).1, ψ.onVertex (Z' k).1 (Z' k).2⟩) :
    infra_73_isMove f seq Z Z' := by
  intro i
  have hcard : #(q.idx ⊕ ι) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hidxμ hιμ
  have h := P.scheme.diagram_preserved A B ψ hψ (seqJoint (seq.family i) Z') hcard hcard
  refine infra_73_diagramEq_of_eq h (fun _ => rfl) ?_
  intro t
  cases t with
  | inl j => exact hfam i j
  | inr k => exact (hZ k).symm

/-- One query is a common sequence-move over two approximation sequences. -/
theorem infra_610_common_move
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq seq' : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hidxμ : #q.idx < μ) (hιμ : #ι < μ) :
    ∃ Z1 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
      infra_73_isMove f seq Z Z1 ∧ infra_73_isMove f seq' Z Z1 := by
  classical
  let xs : (seq.κIndex × q.idx) ⊕ (seq'.κIndex × q.idx) →
      Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    Sum.elim (fun ij => seq.family ij.1 ij.2) (fun ij => seq'.family ij.1 ij.2)
  have hxs : #((seq.κIndex × q.idx) ⊕ (seq'.κIndex × q.idx)) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) seq.concat_bounded seq'.concat_bounded
  obtain ⟨Z1, ψ, hψiso, hψxs, hψZ⟩ := infra_73_move_iso f hf xs Z hxs hιμ
  have hψ : P.scheme.permitted (X := A) (Y := B) ψ := P.scheme.structural_iso A B ψ hψiso
  refine ⟨Z1, ?_, ?_⟩
  · exact infra_610_isMove_of_iso f ψ hψ seq Z Z1 hidxμ hιμ
      (fun i j => hψxs (Sum.inl (i, j))) hψZ
  · exact infra_610_isMove_of_iso f ψ hψ seq' Z Z1 hidxμ hιμ
      (fun i j => hψxs (Sum.inr (i, j))) hψZ

/-- A majority value of a long sequence on a move of `Z` is the type of `q` on that move. -/
theorem infra_610_type_eq_majority
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q) {ι : Type u}
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {R : P.scheme.Object ν hν}
    (xs : q.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν R))
    (hmaj : IsMajorityValue seq Z0 hν R xs)
    (hι : #ι ≤ seq.τ) (hκ : #ι + ℵ₀ < #(seq.κIndex)) :
    P.scheme.DiagramEq (X := q.host) (Y := R) (typeJoint (p := q) Z0) xs := by
  classical
  let Exc0 : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := q.host)
      (seqJoint (seq.family i) Z0) (typeJoint (p := q) Z0)}
  let Exc1 : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := R) (seqJoint (seq.family i) Z0) xs}
  have hExc0 : #Exc0 ≤ #ι + ℵ₀ := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := q.host)
          (seqJoint (seq.family i) Z0) (typeJoint (p := q) Z0)} ≤ _
    exact infra_610_majority_eq_type seq Z0 hι
  have hExc1 : #Exc1 ≤ #ι + ℵ₀ := hmaj
  have hinf : ℵ₀ ≤ #(seq.κIndex) :=
    (le_add_self (a := ℵ₀) (b := #ι)).trans (le_of_lt hκ)
  have hex : ∃ i : seq.κIndex, i ∉ Exc0 ∧ i ∉ Exc1 := by
    by_contra h
    have hall : (Set.univ : Set seq.κIndex) ⊆ Exc0 ∪ Exc1 := by
      intro i _
      by_cases hi : i ∈ Exc0 ∪ Exc1
      · exact hi
      · exact False.elim (h ⟨i, by
          simp only [Set.mem_union, not_or] at hi
          exact hi⟩)
    have hle : #(seq.κIndex) ≤ (#ι + ℵ₀) + (#ι + ℵ₀) := by
      have huni : #(Set.univ : Set seq.κIndex) = #(seq.κIndex) := mk_univ
      rw [← huni]
      exact (mk_le_mk_of_subset hall).trans
        ((mk_union_le _ _).trans (add_le_add hExc0 hExc1))
    exact (not_le_of_gt (add_lt_of_lt hinf hκ hκ)) hle
  obtain ⟨i, hi0, hi1⟩ := hex
  have h0 : P.scheme.DiagramEq (X := A) (Y := q.host)
      (seqJoint (seq.family i) Z0) (typeJoint (p := q) Z0) := by
    simpa [Exc0] using hi0
  have h1 : P.scheme.DiagramEq (X := A) (Y := R) (seqJoint (seq.family i) Z0) xs := by
    simpa [Exc1] using hi1
  exact P.scheme.diagram_trans q.host A R _ _ _ (P.scheme.diagram_symm A q.host _ _ h0) h1

/-- **Majority answers are tied.** If `qB` answers every query of size at most `χ` by a
majority value of one long sequence on a move, then on every sequence-move along any long
sequence its answer is the type of `p`. The query is moved over both sequences at once
(`infra_610_common_move`); on that move both majorities compute `p` (English §6.2, “If `I′`
is another sufficiently long approximation sequence, move `Z` into `A` over `I ∪ I′`”). -/
theorem infra_610_tied_of_majority
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx)
    (hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (hlong : seq.τ + ℵ₀ < #(seq.κIndex))
    (χ : Cardinal.{u}) (hχ : χ ≤ seq.τ)
    (hmaj : ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ χ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        infra_73_isMove f seq Z Z0 ∧
        IsMajorityValue seq Z0 qB.hν qB.host (infra_612_anchored eB qB.incl qB.val Z))
    (seq' : ApproximationSequence p) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hlong' : seq'.τ + ℵ₀ < #(seq'.κIndex))
    (hι' : #ι ≤ seq'.τ) (hιχ : #ι ≤ χ) (hιμ : #ι < μ)
    (hmv : infra_73_isMove f seq' Z Z0') :
    P.scheme.DiagramEq (X := p.host) (Y := qB.host)
      (typeJoint (p := p) Z0') (infra_612_anchored eB qB.incl qB.val Z) := by
  obtain ⟨Z0, hmv0, hmaj0⟩ := hmaj Z hιχ
  have hι : #ι ≤ seq.τ := hιχ.trans hχ
  have hκ : #ι + ℵ₀ < #(seq.κIndex) := (add_le_add hι le_rfl).trans_lt hlong
  have hκ' : #ι + ℵ₀ < #(seq'.κIndex) := (add_le_add hι' le_rfl).trans_lt hlong'
  have hans := infra_610_type_eq_majority seq Z0 _ hmaj0 hι hκ
  obtain ⟨Z1, hmv1, hmv1'⟩ := infra_610_common_move f hf seq seq' Z hidxμ hιμ
  have h01 := infra_73_moves_agree f seq Z Z0 Z1 hmv0 hmv1 hι hκ
  have h01' := infra_73_moves_agree f seq' Z Z0' Z1 hmv hmv1' hι' hκ'
  exact P.scheme.diagram_trans p.host p.host qB.host _ _ _ h01'
    (P.scheme.diagram_trans p.host p.host qB.host _ _ _
      (P.scheme.diagram_symm p.host p.host _ _ h01) hans)

set_option maxHeartbeats 3200000 in
/-- **Tied placement (English §6.2, “an actual tuple in an extension object”).** The
Proposition 4.9 placement `z ∈ E(J)` of the chart prescriptions, in a strong hull `N` of
`E(I) ∪ z` of size `μ`, is a tuple over `B` whose answer on every query `Z` of size at most the
chart arity is the majority prescription on a move of `Z`. -/
theorem infra_610_tied_placement
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible) (hσμ : σ < μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A) (hidx : #p.idx ≤ σ)
    (seq : ApproximationSequence p)
    (data : Infra610ChartSupport (hμ := hμ) P σ f hf p seq) :
    ∃ (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx), qB.ν = μ ∧
      ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #ι ≤ seq.τ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
          infra_73_isMove f seq Z Z0 ∧
          IsMajorityValue seq Z0 qB.hν qB.host (infra_612_anchored eB qB.incl qB.val Z) := by
  classical
  letI := data.linOrder
  letI := data.nonempty
  haveI := data.wf
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  obtain ⟨J, linJ, nonJ, fIJ, z, hJ, hPlace⟩ :=
    @proposition_4_9 K _ P.E P.D data.I data.linOrder data.nonempty data.wf
      p.idx σ data.χ hσ hidx data.hχls data.hpow data.hImem data.qPres data.hnat data.hcoh
  letI := linJ
  letI := nonJ
  obtain ⟨N, i, j, zN, hN, hcN, hi, hj, hij, hiz⟩ :=
    infra_610_placement_mu_hull hσ data hidx hσμ (P.E.map fIJ) (P.E.map_strong fIJ) z hJ
  let top : SMObject K μ := SMObject.ofModel N hN hcN
  let φ : N.carrier ≃[K.τ] top.model.carrier := SMObject.ofModelEquiv N hN hcN
  have hφ : K.Strong φ.toEmbedding := strong_of_equiv K φ hN
  have hsB : K.Strong data.eB.symm.toEmbedding := strong_of_equiv K data.eB.symm B.mem
  have hsE : K.Strong data.eB.toEmbedding := strong_of_equiv K data.eB data.hImem
  let embB : Language.Embedding K.τ B.model.carrier top.model.carrier :=
    φ.toEmbedding.comp (j.comp data.eB.symm.toEmbedding)
  have hembB : K.Strong embB := K.strong_trans _ _ (K.strong_trans _ _ hsB hj) hφ
  let qB : TupleOver K oneVertexShape P.scheme hμ B :=
    { ν := μ
      hν := hμ
      host := top
      incl := oneVertexArrow embB hembB
      incl_arrow := trivial
      idx := p.idx
      val := fun a => top.occ (φ (zN a)) }
  refine ⟨qB, Equiv.refl p.idx, rfl, ?_⟩
  intro ι Z hι
  have hιχ : #ι ≤ data.χ := by rw [data.hχτ]; exact hι
  let params : ι → (P.E.obj data.I).carrier := fun k => data.eB.symm (B.val (Z k))
  obtain ⟨Z0, hmove, hmaj⟩ := data.hmajPres hιχ params
  have hZ : (fun b => B.occ (data.eB (params b))) = Z := by
    funext b
    change B.occ (data.eB (data.eB.symm (B.val (Z b)))) = Z b
    rw [show data.eB (data.eB.symm (B.val (Z b))) = B.val (Z b) from
      data.eB.apply_symm_apply _]
    exact SMObject.occ_val B (Z b)
  refine ⟨Z0, ?_, ?_⟩
  · intro k
    have h := hmove k
    rwa [hZ] at h
  -- cardinal bookkeeping
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ
  have hχμ : data.χ < μ := data.hχμ
  have hιμ : #ι < μ := hιχ.trans_lt hχμ
  have hidxμ : #p.idx < μ := hidx.trans_lt hσμ
  have hα : #(p.idx ⊕ ι) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt hμinf hidxμ hιμ
  let ρ : Cardinal.{u} := σ + data.χ
  have hρinf : ℵ₀ ≤ ρ := hσ.trans (self_le_add_right σ data.χ)
  have hρμ : ρ < μ := add_lt_of_lt hμinf hσμ hχμ
  have hjoint : #(p.idx ⊕ ι) ≤ ρ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_le_add hidx hιχ
  have hls : ls K ≤ ρ := by
    have h1 : ls K ≤ ls K + σ := le_self_add
    have h2 : ls K + σ < data.χ := data.hχls
    exact h1.trans (h2.le.trans le_add_self)
  have hIc : Model.card (P.E.obj data.I) = μ :=
    SingleModelData.card_obj_eq (P := P) hμ data.I data.hIcard
  have htρ : P.D.t ρ < μ := P.t_lt hμ hρinf hρμ
  have hcI : P.D.t ρ ≤ Model.card (P.E.obj data.I) := htρ.le.trans hIc.ge
  have hcJ : P.D.t ρ ≤ Model.card (P.E.obj J) :=
    hcI.trans (mk_le_of_injective (P.E.map fIJ).injective)
  have hcN : P.D.t ρ ≤ Model.card N := htρ.le.trans hcN.ge
  have hcT : P.D.t ρ ≤ Model.card top.model := htρ.le.trans top.card.ge
  have hcB : P.D.t ρ ≤ Model.card B.model := htρ.le.trans B.card.ge
  let LN : p.idx ⊕ ι → N.carrier := Sum.elim zN (fun k => j (params k))
  let LJ : p.idx ⊕ ι → (P.E.obj J).carrier :=
    Sum.elim z (fun k => P.E.map fIJ (params k))
  let LQ : p.idx ⊕ ι → (P.E.obj data.I).carrier := data.qPres hιχ params
  let LB : p.idx ⊕ ι → B.model.carrier := fun t => data.eB (LQ t)
  let LT : p.idx ⊕ ι → top.model.carrier := fun t => φ (LN t)
  have s1 : P.D.same hjoint hN top.mem hcN hcT LN LT :=
    P.D.of_strong hjoint hN top.mem hcN hcT LN LT φ.toEmbedding hρinf hφ (fun _ => rfl)
  have s2 : P.D.same hjoint hN hJ hcN hcJ LN LJ := by
    refine P.D.of_strong hjoint hN hJ hcN hcJ LN LJ i hρinf hi ?_
    intro t
    cases t with
    | inl a => exact hiz a
    | inr k => exact hij (params k)
  have s3 := hPlace hιχ params hjoint hcI hcJ
  have s4 : P.D.same hjoint data.hImem hJ hcI hcJ LQ
      (Sum.elim (fun a => P.E.map fIJ (LQ (Sum.inl a)))
        (fun b => P.E.map fIJ (LQ (Sum.inr b)))) := by
    refine P.D.of_strong hjoint data.hImem hJ hcI hcJ _ _ (P.E.map fIJ) hρinf
      (P.E.map_strong fIJ) ?_
    intro t
    cases t <;> rfl
  have s5 : P.D.same hjoint data.hImem B.mem hcI hcB LQ LB :=
    P.D.of_strong hjoint data.hImem B.mem hcI hcB LQ LB data.eB.toEmbedding hρinf hsE
      (fun _ => rfl)
  have sNI : P.D.same hjoint hN data.hImem hcN hcI LN LQ :=
    P.D.trans hjoint hN hJ data.hImem hcN hcJ hcI _ _ _ s2
      (P.D.trans hjoint hJ hJ data.hImem hcJ hcJ hcI _ _ _ s3
        (P.D.symm hjoint data.hImem hJ hcI hcJ _ _ s4))
  have sNB : P.D.same hjoint hN B.mem hcN hcB LN LB :=
    P.D.trans hjoint hN data.hImem B.mem hcN hcI hcB _ _ _ sNI s5
  have sBT : P.D.same hjoint B.mem top.mem hcB hcT LB LT :=
    P.D.trans hjoint B.mem hN top.mem hcB hcN hcT _ _ _
      (P.D.symm hjoint hN B.mem hcN hcB _ _ sNB) s1
  -- relevel to the canonical bound
  have hmaxμ : max #(p.idx ⊕ ι) ℵ₀ < μ := max_lt hα (P.aleph0_lt hμ)
  have htm : P.D.t (max #(p.idx ⊕ ι) ℵ₀) < μ := P.t_lt hμ (le_max_right _ _) hmaxμ
  have hcBm : P.D.t (max #(p.idx ⊕ ι) ℵ₀) ≤ Model.card B.model := htm.le.trans B.card.ge
  have hcTm : P.D.t (max #(p.idx ⊕ ι) ℵ₀) ≤ Model.card top.model :=
    htm.le.trans top.card.ge
  have sBTm := P.D.same_relevel (σ := ρ) (τ := max #(p.idx ⊕ ι) ℵ₀) (σ' := ρ)
    hjoint hρinf (le_max_right _ _) le_rfl (max_le hjoint hρinf) hls B.mem top.mem
    hcB hcT hcB hcT hcBm hcTm LB LT sBT (le_max_left _ _) id
  have hSameD : P.D.SameD B.model top.model LB LT := ⟨B.mem, top.mem, hcBm, hcTm, sBTm⟩
  have hD : P.scheme.DiagramEq (X := B) (Y := top)
      (fun t => B.occ (data.eB (data.qPres hιχ params t)))
      (infra_612_anchored (Equiv.refl p.idx) qB.incl qB.val Z) := by
    have hEq : P.scheme.DiagramEq (X := B) (Y := top) (fun t => B.occ (LB t))
        (fun t => top.occ (LT t)) :=
      (SingleModelData.diagramEq_iff_sameD (P := P) (α := p.idx ⊕ ι) hμ hμ B top
        LB LT hα hα).mpr hSameD
    refine infra_73_diagramEq_of_eq hEq (fun _ => rfl) ?_
    intro t
    cases t with
    | inl a => rfl
    | inr k => rfl
  change # {i : seq.κIndex //
      ¬ P.scheme.DiagramEq (X := A) (Y := top) (seqJoint (seq.family i) Z0)
        (infra_612_anchored (Equiv.refl p.idx) qB.incl qB.val Z)} ≤ _
  have hmono : ∀ i : seq.κIndex,
      ¬ P.scheme.DiagramEq (X := A) (Y := top) (seqJoint (seq.family i) Z0)
        (infra_612_anchored (Equiv.refl p.idx) qB.incl qB.val Z) →
      ¬ P.scheme.DiagramEq (X := A) (Y := B) (seqJoint (seq.family i) Z0)
        (fun t => B.occ (data.eB (data.qPres hιχ params t))) := by
    intro i hbad hgood
    exact hbad (P.scheme.diagram_trans A B top _ _ _ hgood hD)
  exact (mk_subtype_mono hmono).trans hmaj

set_option maxHeartbeats 1600000 in
/-- A tied placement whose chart arity is at least a prescribed `λ < μ` (English: “For a larger
desired bounded query size `τ′`, repeat with a power closed bound at least `c(σ, τ′)`”). -/
theorem infra_610_tied_at
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (lam : Cardinal.{u}) (hlam : lam < μ) :
    ∃ (seq : ApproximationSequence p) (qB : TupleOver K oneVertexShape P.scheme hμ B)
      (eB : p.idx ≃ qB.idx), qB.ν = μ ∧ lam ≤ seq.τ ∧ P.g σ + ls K ≤ seq.τ ∧
      seq.τ + ℵ₀ < #(seq.κIndex) ∧
      ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #ι ≤ seq.τ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
          infra_73_isMove f seq Z Z0 ∧
          IsMajorityValue seq Z0 qB.hν qB.host (infra_612_anchored eB qB.incl qB.val Z) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let τ0 : Cardinal.{u} := testCardinal b P.g σ
  have hτ0 : ℵ₀ ≤ τ0 := by
    change ℵ₀ ≤ (2 : Cardinal.{u}) ^ (P.g σ + b + σ + aleph0)
    exact le_trans (cantor aleph0).le
      (power_le_power_left two_ne_zero
        (le_add_self : aleph0 ≤ (P.g σ + b + σ) + aleph0))
  have hexp0 : P.g σ + b + σ + aleph0 < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    have hb : b < μ := max_lt (P.ls_lt hμ) (P.aleph0_lt hμ)
    have h1 : P.g σ + b < μ := add_lt_of_lt (P.aleph0_le hμ) hg hb
    have h2 : P.g σ + b + σ < μ := add_lt_of_lt (P.aleph0_le hμ) h1 hσlt
    exact add_lt_of_lt (P.aleph0_le hμ) h2 (P.aleph0_lt hμ)
  have hτ0μ : τ0 < μ :=
    hμ.1.working.strongLimit.isStrongPrelimit hexp0
  obtain ⟨χ, hχls, hχμ, hpow, hτ0χ', htestχ⟩ :=
    infra_610_choose_chi P σ hσ hμ hσlt (max τ0 lam) (max_lt hτ0μ hlam)
  have hτ0χ : τ0 ≤ χ := (le_max_left _ _).trans hτ0χ'
  have hlamχ : lam ≤ χ := (le_max_right _ _).trans hτ0χ'
  let τ : Cardinal.{u} := χ
  let κ : Cardinal.{u} := Order.succ τ
  have hτ : ℵ₀ ≤ τ := hτ0.trans hτ0χ
  have hτμ : τ < μ := hχμ
  have hκ : ℵ₀ ≤ κ := hτ.trans (Order.le_succ _)
  have hκμ : κ < μ :=
    (Order.succ_le_of_lt (cantor τ)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hτμ)
  have hprod : κ * #p.idx < μ := by
    have hmul : κ * #p.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    have hκσ : κ * σ = κ := by
      refine mul_eq_left hκ ?_ (aleph0_pos.trans_le hσ).ne'
      have hστ : σ < τ :=
        (lt_of_lt_of_le (cantor σ)
          (power_le_power_left two_ne_zero
            (le_trans (le_add_self : σ ≤ (P.g σ + b) + σ)
              (le_self_add : (P.g σ + b) + σ ≤ ((P.g σ + b) + σ) + aleph0)))).trans_le hτ0χ
      exact hστ.le.trans (Order.le_succ _)
    exact hmul.trans_lt (by rw [hκσ]; exact hκμ)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ := by
    have hβ : max (max σ τ) (max (ls K) ℵ₀) < μ :=
      max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
    exact hrec.2 _ hβ
  obtain ⟨seq, hseqτ, hseqκ⟩ :=
    P.exists_approximationSequence hμ A p hνμ σ τ κ hσ hσlt hidx hτ hτμ hκ hκμ hprod hclosed
  have hseqτμ : seq.τ < μ := hseqτ ▸ hτμ
  have hκIndex : seq.τ + aleph0 < #seq.κIndex := by
    rw [hseqκ, hseqτ, add_eq_left hτ hτ]
    exact Order.lt_succ τ
  have hχls' : ls K + σ < seq.τ := hseqτ ▸ hχls
  have hpow' : seq.τ ^ σ = seq.τ := by rw [hseqτ]; exact hpow
  have htestχ' : P.g σ + ls K ≤ seq.τ := hseqτ ▸ htestχ
  obtain ⟨data⟩ :=
    infra_610_chart_support P σ hσ hμ hσμ f hf p hidx seq hseqτμ hκIndex hχls' hpow' htestχ'
  obtain ⟨qB, eB, hqν, hmaj⟩ := infra_610_tied_placement P σ hσ hμ hσlt f hf p hidx seq data
  exact ⟨seq, qB, eB, hqν, hseqτ ▸ hlamχ, htestχ', hκIndex, hmaj⟩

set_option maxHeartbeats 3200000 in
/-- **Tied free lift (English Theorem 6.10, existence of `p_B`).** At a recursion-closed level,
`p` over `A` has an extension `qB` over `B` along `f` whose answer on every bounded query of `B`
is the free evaluation: on any sequence-move along any long approximation sequence it is the
type of `p` (`IsTiedFree`).

The chart placement of `infra_610_tied_placement` at the test arity is the witness. A query of
larger size `λ` is answered by a placement at arity `≥ λ` (`infra_610_tied_at`); the two
placements agree on all tests (`infra_73_tied_move`, `infra_610_tied_of_majority`), so
Theorem 6.6 (`infra_73_differing_test`) gives one Galois type over `B`, which carries the
answer back (`infra_72_diagramEq_of_sameGalois`). The restriction to `A` is `p` by the same
testing criterion, using the trivial move `f Y` of `Y`. -/
theorem infra_610_tied_free_lift
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) :
    ∃ (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx), qB.ν = μ ∧
      SameGaloisType p (qB.restrict f hf) eB (Equiv.refl qB.idx) ∧ IsTiedFree f p qB eB := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hidxμ : #p.idx < μ := hidx.trans_lt hσlt
  -- placements answer every bounded query they cover by the type of `p`
  have hanswer : ∀ (seqX : ApproximationSequence p) (qX : TupleOver K oneVertexShape P.scheme hμ B)
      (eX : p.idx ≃ qX.idx), seqX.τ + ℵ₀ < #(seqX.κIndex) →
      (∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #ι ≤ seqX.τ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
          infra_73_isMove f seqX Z Z0 ∧
          IsMajorityValue seqX Z0 qX.hν qX.host (infra_612_anchored eX qX.incl qX.val Z)) →
      ∀ (seq' : ApproximationSequence p) {ι : Type u}
        (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
        (Z0' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
        seq'.τ + ℵ₀ < #(seq'.κIndex) → #ι ≤ seq'.τ → #ι ≤ seqX.τ → #ι < μ →
        infra_73_isMove f seq' Z Z0' →
        P.scheme.DiagramEq (X := p.host) (Y := qX.host)
          (typeJoint (p := p) Z0') (infra_612_anchored eX qX.incl qX.val Z) := by
    intro seqX qX eX hlongX hmajX seq' ι Z Z0' hlong' hι' hιX hιμ hmv
    exact infra_610_tied_of_majority f hf p qX eX hidxμ seqX hlongX seqX.τ le_rfl
      (fun Z hZ => hmajX Z hZ) seq' Z Z0' hlong' hι' hιX hιμ hmv
  -- two placements covering the test size have one Galois type over `B`
  have hsame : ∀ (seq1 seq2 : ApproximationSequence p)
      (q1 q2 : TupleOver K oneVertexShape P.scheme hμ B) (e1 : p.idx ≃ q1.idx)
      (e2 : p.idx ≃ q2.idx), q1.ν = μ → q2.ν = μ →
      P.g σ + ls K ≤ seq1.τ → P.g σ + ls K ≤ seq2.τ →
      seq1.τ + ℵ₀ < #(seq1.κIndex) → seq2.τ + ℵ₀ < #(seq2.κIndex) →
      (∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #ι ≤ seq1.τ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
          infra_73_isMove f seq1 Z Z0 ∧
          IsMajorityValue seq1 Z0 q1.hν q1.host (infra_612_anchored e1 q1.incl q1.val Z)) →
      (∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #ι ≤ seq2.τ → ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
          infra_73_isMove f seq2 Z Z0 ∧
          IsMajorityValue seq2 Z0 q2.hν q2.host (infra_612_anchored e2 q2.incl q2.val Z)) →
      SameGaloisType q1 q2 e1.symm e2.symm := by
    intro seq1 seq2 q1 q2 e1 e2 h1ν h2ν ht1 ht2 hl1 hl2 hm1 hm2
    have hidx1 : #q1.idx ≤ σ := by rw [← Cardinal.mk_congr e1]; exact hidx
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ :=
      infra_73_differing_test P σ hσ hμ hrec hσμ q1 q2 e1.symm e2.symm h1ν h2ν
        hidx1 (hidx1.trans_lt hσlt) hneq
    apply hnot
    obtain ⟨seq, Y0, hlong, hβτ, hβμ, hmv⟩ :=
      infra_73_tied_move P σ hσ hμ hrec hσμ f hf p hνμ hidx Y hβ
    have d1 := hanswer seq1 q1 e1 hl1 hm1 seq Y Y0 hlong hβτ (hβ.trans ht1) hβμ hmv
    have d2 := hanswer seq2 q2 e2 hl2 hm2 seq Y Y0 hlong hβτ (hβ.trans ht2) hβμ hmv
    have d := P.scheme.diagram_trans q1.host p.host q2.host _ _ _
      (P.scheme.diagram_symm p.host q1.host _ _ d1) d2
    exact infra_73_diagramEq_of_eq d (fun t => by cases t <;> rfl)
      (fun t => by cases t <;> rfl)
  obtain ⟨seqA, qA, eA, hAν, -, htA, hlA, hmA⟩ :=
    infra_610_tied_at P σ hσ hμ hrec hσμ f hf p hνμ hidx 0
      (aleph0_pos.trans (P.aleph0_lt hμ))
  have hTied : IsTiedFree f p qA eA := by
    intro seq' ι Z Z0' hlong' hι' hιμ hmv
    obtain ⟨seqL, qL, eL, hLν, hιL, htL, hlL, hmL⟩ :=
      infra_610_tied_at P σ hσ hμ hrec hσμ f hf p hνμ hidx #ι hιμ
    have dL := hanswer seqL qL eL hlL hmL seq' Z Z0' hlong' hι' hιL hιμ hmv
    have hS := hsame seqA seqL qA qL eA eL hAν hLν htA htL hlA hlL hmA hmL
    have dAL := infra_72_diagramEq_of_sameGalois (P := P) hS Z hAν hLν hidxμ hιμ
    have dAL' : P.scheme.DiagramEq (X := qA.host) (Y := qL.host)
        (infra_612_anchored eA qA.incl qA.val Z) (infra_612_anchored eL qL.incl qL.val Z) :=
      infra_73_diagramEq_of_eq dAL (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    exact P.scheme.diagram_trans p.host qL.host qA.host _ _ _ dL
      (P.scheme.diagram_symm qA.host qL.host _ _ dAL')
  refine ⟨qA, eA, hAν, ?_, hTied⟩
  -- the restriction to `A` is `p`
  have hidxA : #p.idx ≤ σ := hidx
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ :=
    infra_73_differing_test P σ hσ hμ hrec hσμ p (qA.restrict f hf) eA
      (Equiv.refl qA.idx) hνμ hAν hidxA hidxμ hneq
  apply hnot
  have hβμ : #β < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    exact hβ.trans_lt (add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ))
  have hmvY : infra_73_isMove f seqA (pushParams f Y) Y :=
    infra_610_isMove_of_iso f f hf seqA (pushParams f Y) Y hidxμ hβμ
      (fun _ _ => rfl) (fun _ => rfl)
  have d := hTied seqA (pushParams f Y) Y hlA (hβ.trans htA) hβμ hmvY
  have d' := (P.scheme.diagram_reindex p.host qA.host
    (Equiv.sumCongr eA (Equiv.refl β)) _ _).mp d
  refine infra_73_diagramEq_of_eq d' ?_ ?_
  · intro t
    cases t with
    | inl k => rfl
    | inr b => rfl
  · intro t
    cases t with
    | inl k =>
      simp only [Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inl, infra_612_anchored,
        alignJoint, typeJoint, Equiv.apply_symm_apply, Equiv.refl_symm]
      rfl
    | inr b => rfl

end
end
end AEC
