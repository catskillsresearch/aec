module

public import AEC.Section7.BlockRestriction
public import AEC.Section7.DescentIsolation

@[expose] public section

/-!
# Lemma 7.6 — descent of relative isolation along a tied-free lift

English Lemma 7.6 for an arbitrary isolating fragment `W ⊆ B` (same level). The free lift is
the English free evaluation `IsTiedFree`. The tied answer of `q_B` on a list `w` from `B` is
the answer of `q_A` on the members `w_k` of an approximation list of `tp(w/A)` inside `A`,
off a bounded exception set (`infra_76_tied_majority`): each good `w_k` is a sequence-move of
`w`, and moves are answered alike. The fragment of `q_A` is the union of the `w_k`.
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-- The list `Y` from `B` as a tuple over `A` (host `B`, inclusion `f`). -/
def infra_76_listTuple
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) :
    TupleOver K oneVertexShape P.scheme hμ A where
  ν := μ
  hν := hμ
  host := B
  incl := f
  incl_arrow := hf
  idx := β
  val := Y

set_option maxHeartbeats 1600000 in
/-- **Symmetry of the tied answer.** If `q_B` is a tied-free lift of `q_A` and `S` is an
approximation list of `tp(Y/A)` long enough to query a whole approximation family of `q_A`,
then off a set of at most `h(σ)` indices `k`, `q_B` answers `Y` as `q_A` answers `S_k`. -/
theorem infra_76_tied_majority
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible) (hμT : μ ∈ infra_73_tailSet P σ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (qA : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : qA.idx ≃ qB.idx) (hqAν : qA.ν = μ) (hidx : #qA.idx ≤ σ)
    (hT : IsTiedFree f qA qB eB)
    {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hβ : #β ≤ σ)
    (S : ApproximationSequence (infra_76_listTuple f hf Y))
    (hS : infra_73_h P σ ≤ S.τ) :
    ∃ E : Set S.κIndex, #E ≤ infra_73_h P σ ∧
      ∀ k, k ∉ E →
        P.scheme.DiagramEq (X := qA.host) (Y := qB.host)
          (typeJoint (p := qA) (S.family k))
          (infra_612_anchored eB qB.incl qB.val Y) := by
  classical
  have hσSucc : Order.succ σ ≤ μ := infra_73_tail_succ hμT
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hhμ : infra_73_h P σ < μ := infra_73_h_lt hμ hμT
  have hβμ : #β < μ := hβ.trans_lt hσlt
  obtain ⟨seq, hτeq, hκ, -, hlong⟩ := infra_73_sequence P σ hσ hμ hμT qA hqAν hidx
  have hβτ : #β ≤ seq.τ := hβ.trans (hτeq ▸ le_max_left _ _)
  have hhinf : ℵ₀ ≤ infra_73_h P σ :=
    hσ.trans ((le_max_left σ (infra_73_chi P σ)).trans (Order.le_succ _))
  have hβκ : #β + ℵ₀ < #(seq.κIndex) := by
    rw [hκ]
    have h1 : #β + ℵ₀ ≤ max σ (infra_73_chi P σ) :=
      (add_le_add (hβ.trans (le_max_left _ _)) (hσ.trans (le_max_left _ _))).trans
        (add_eq_self (hσ.trans (le_max_left _ _))).le
    exact h1.trans_lt (Order.lt_succ_of_not_isMax (not_isMax _))
  let FAM : seq.κIndex × qA.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun x => seq.family x.1 x.2
  have hFAM : #(seq.κIndex × qA.idx) ≤ infra_73_h P σ := infra_73_family_card seq hσ hidx hκ
  -- a move of `Y` over the family
  obtain ⟨Y0, ψ, hψiso, hψxs, hψY⟩ :=
    infra_73_move_iso f hf FAM Y (hFAM.trans_lt hhμ) hβμ
  have hψ : P.scheme.permitted (X := A) (Y := B) ψ := P.scheme.structural_iso A B ψ hψiso
  have hmove0 : infra_73_isMove f seq Y Y0 := by
    intro i
    have hcard : #(qA.idx ⊕ β) < μ := by
      rw [mk_sum, lift_id, lift_id]
      exact add_lt_of_lt (P.aleph0_le hμ) (hidx.trans_lt hσlt) hβμ
    have h := P.scheme.diagram_preserved A B ψ hψ (seqJoint (seq.family i) Y0) hcard hcard
    have heq : (fun t => (⟨(seqJoint (seq.family i) Y0 t).1,
          ψ.onVertex _ (seqJoint (seq.family i) Y0 t).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) =
        seqJoint (fun j => ⟨(seq.family i j).1, f.onVertex _ (seq.family i j).2⟩) Y := by
      funext t
      cases t with
      | inl j => exact hψxs (i, j)
      | inr k => exact (hψY k).symm
    rw [heq] at h
    exact h
  have hans := hT seq Y Y0 hlong hβτ hβμ hmove0
  -- exceptions of `S` on the family query
  let E : Set S.κIndex := {k | ¬ P.scheme.DiagramEq (X := B) (Y := A)
    (typeJoint (p := infra_76_listTuple f hf Y) FAM) (seqJoint (S.family k) FAM)}
  have hE : #E ≤ infra_73_h P σ :=
    (S.few_exceptions FAM (hFAM.trans hS)).trans
      ((add_le_add hFAM hhinf).trans (add_eq_self hhinf).le)
  refine ⟨E, hE, fun k hk => ?_⟩
  have hk : P.scheme.DiagramEq (X := B) (Y := A)
      (typeJoint (p := infra_76_listTuple f hf Y) FAM) (seqJoint (S.family k) FAM) :=
    not_not.mp hk
  have hmove1 : infra_73_isMove f seq Y (S.family k) := by
    intro i
    let ι : qA.idx ⊕ β → β ⊕ (seq.κIndex × qA.idx) := fun t =>
      match t with
      | Sum.inl a => Sum.inr (i, a)
      | Sum.inr b => Sum.inl b
    have h := infra_73_scheme_comp hk ι
    have h' := P.scheme.diagram_symm B A _ _ h
    exact infra_73_diagramEq_of_eq h' (fun t => by cases t <;> rfl)
      (fun t => by cases t <;> rfl)
  have hagree := infra_73_moves_agree f seq Y Y0 (S.family k) hmove0 hmove1 hβτ hβκ
  exact P.scheme.diagram_trans qA.host qA.host qB.host _ _ _
    (P.scheme.diagram_symm qA.host qA.host _ _ hagree) hans

/-! ## Tails for a larger arity -/

theorem infra_76_pad_recursion_mono_sigma {σ σ' b a : Cardinal.{u}} (hσ : σ ≤ σ')
    (i : Ordinal.{u}) :
    infra_69_pad_recursion σ b a i ≤ infra_69_pad_recursion σ' b a i := by
  refine WellFounded.induction
    (C := fun i => infra_69_pad_recursion σ b a i ≤ infra_69_pad_recursion σ' b a i)
    wellFounded_lt i ?_
  intro i ih
  by_cases h0 : i = 0
  · rw [h0, infra_69_pad_recursion_zero, infra_69_pad_recursion_zero]
  · by_cases hsuc : ∃ j, i = Order.succ j
    · obtain ⟨j, hj⟩ := hsuc
      have hlt : j < i := by rw [hj]; exact Order.lt_succ j
      rw [hj, infra_69_pad_recursion_succ, infra_69_pad_recursion_succ]
      exact add_le_add (add_le_add
        (power_le_power_left two_ne_zero (ih j hlt)) hσ) le_rfl
    · rw [infra_69_pad_recursion_limit h0 (fun j hj => hsuc ⟨j, hj⟩),
        infra_69_pad_recursion_limit h0 (fun j hj => hsuc ⟨j, hj⟩)]
      haveI : Nonempty (Set.Iio i) := ⟨⟨0,
        lt_of_le_of_ne (bot_le : (0 : Ordinal.{u}) ≤ i) (Ne.symm h0)⟩⟩
      exact ciSup_le fun t => (ih t.1 t.2).trans
        (le_ciSup (f := fun t : Set.Iio i => infra_69_pad_recursion σ' b a t.1)
          bddAbove_of_small t)

theorem infra_76_rec_mono {P : SingleModelData K} {σ σ' μ : Cardinal.{u}} (hσ : σ ≤ σ')
    (h : μ ∈ recursionClosedLevels P σ') : μ ∈ recursionClosedLevels P σ := by
  refine ⟨h.1, fun β₀ hβ₀ => ?_⟩
  have h' := h.2 β₀ hβ₀
  unfold infra_69_pad_recursion_closed at h' ⊢
  refine lt_of_le_of_lt ?_ h'
  exact (infra_69_pad_recursion_mono σ _ β₀
    (Cardinal.ord_le_ord.mpr (Order.succ_le_succ hσ))).trans
    (infra_76_pad_recursion_mono_sigma hσ _)

theorem infra_76_lt_h (P : SingleModelData K) (σ : Cardinal.{u}) : σ < infra_73_h P σ :=
  (le_max_left σ (infra_73_chi P σ)).trans_lt (Order.lt_succ_of_not_isMax (not_isMax _))

/-- A level in the `σ'`-tail is in the `σ`-tail when `h(σ) ≤ σ'`. -/
theorem infra_76_tail_mono {P : SingleModelData K} {σ σ' μ : Cardinal.{u}}
    (hh : infra_73_h P σ ≤ σ') (h : μ ∈ infra_73_tailSet P σ') : μ ∈ infra_73_tailSet P σ := by
  have hσ : σ ≤ σ' := (infra_76_lt_h P σ).le.trans hh
  refine ⟨infra_76_rec_mono hσ h.1, ?_⟩
  exact (Order.succ_le_succ (max_le (hσ.trans (le_max_left _ _))
    (hh.trans (le_max_left _ _)))).trans h.2

/-- The arity bound of the descent: `h(h(σ))`. -/
def infra_76_sigma2 (P : SingleModelData K) (σ : Cardinal.{u}) : Cardinal.{u} :=
  infra_73_h P (infra_73_h P σ)

/-! ## The descent -/

theorem infra_76_two_good {κ : Type u} (E1 E2 : Set κ) {c : Cardinal.{u}} (hc : ℵ₀ ≤ c)
    (h1 : #E1 ≤ c) (h2 : #E2 ≤ c) (hκ : c < #κ) : ∃ k, k ∉ E1 ∧ k ∉ E2 := by
  by_contra hno
  push_neg at hno
  have hU : E1 ∪ E2 = Set.univ := Set.eq_univ_of_forall fun k => by
    by_cases hk : k ∈ E1
    · exact Or.inl hk
    · exact Or.inr (hno k hk)
  have hle : #κ ≤ c := by
    rw [← mk_univ, ← hU]
    exact (mk_union_le E1 E2).trans ((add_le_add h1 h2).trans (add_eq_self hc).le)
  exact absurd hκ (not_lt_of_ge hle)

set_option maxHeartbeats 3200000 in
/-- **English Lemma 7.6 (same level, tied-free lift).** If `q_B` is a tied-free lift of
`q_A` along `f` and `q_B` is isolated relative to `u`, then `q_A` is isolated relative to `u`.
The fragment is the union of an approximation list of `tp(W/A)` for an isolating fragment `W`
of `q_B` of size at most `h(σ)` (Proposition 7.3). -/
theorem infra_76_tied_descent
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P (infra_76_sigma2 P σ))
    {A B : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ)
      (infra_76_tail_mono (le_trans (infra_76_lt_h P _).le le_rfl) hμT))}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (qA : TupleOver K oneVertexShape P.scheme _ A)
    (qB : TupleOver K oneVertexShape P.scheme _ B)
    (e : qA.idx ≃ qB.idx) {uIdx cIdx : Type u} (eA : qA.idx ≃ uIdx ⊕ cIdx)
    (hqAν : qA.ν = μ) (hqBν : qB.ν = μ) (hidx : #qA.idx ≤ σ)
    (hExt : SameGaloisType qA (qB.restrict f hf) e (Equiv.refl qB.idx))
    (hT : IsTiedFree f qA qB e)
    (hIso : IsRelativelyIsolated qB (e.symm.trans eA)) :
    IsRelativelyIsolated qA eA := by
  classical
  let σ1 : Cardinal.{u} := infra_73_h P σ
  let σ2 : Cardinal.{u} := infra_76_sigma2 P σ
  have hσ1 : ℵ₀ ≤ σ1 := hσ.trans (infra_76_lt_h P σ).le
  have hσ2 : ℵ₀ ≤ σ2 := hσ1.trans (infra_76_lt_h P σ1).le
  have hσσ1 : σ ≤ σ1 := (infra_76_lt_h P σ).le
  have hσ1σ2 : σ1 ≤ σ2 := (infra_76_lt_h P σ1).le
  have hT0 : μ ∈ infra_73_tailSet P σ := infra_76_tail_mono (le_trans hσ1σ2 le_rfl) hμT
  have hT1 : μ ∈ infra_73_tailSet P σ1 := infra_76_tail_mono le_rfl hμT
  have hμ : μ ∈ P.eligible := Tail.mem (infra_73_tail P σ hσ) hT0
  have hrec : μ ∈ recursionClosedLevels P σ := infra_73_tail_rec hT0
  have hσSucc : Order.succ σ ≤ μ := infra_73_tail_succ hT0
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #qA.idx < μ := hidx.trans_lt hσlt
  have hidxB : #qB.idx ≤ σ := by rw [← Cardinal.mk_congr e]; exact hidx
  let eb : qB.idx ≃ uIdx ⊕ cIdx := e.symm.trans eA
  -- Proposition 7.3: a fragment of size at most `h(σ)`
  obtain ⟨ιW, W, hιW, hWiso⟩ := infra_73_uniform_of_block P σ hσ
    (infra_73_block_restriction P σ hσ) hT0 qB eb hqBν hidxB (hidxB.trans_lt hσlt) hIso
  -- an approximation list of `tp(W/A)`
  have hιW2 : #ιW ≤ σ2 := hιW.trans hσ1σ2
  obtain ⟨S, hSτ, hSκ, -, -⟩ := infra_73_sequence P σ2 hσ2 hμ hμT
    (infra_76_listTuple f hf W) rfl hιW2
  have hS : infra_73_h P σ1 ≤ S.τ := hSτ ▸ le_max_left _ _
  have hSbig : σ2 < #S.κIndex := hSκ ▸ infra_76_lt_h P σ2
  let Z : S.κIndex × ιW → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun x => S.family x.1 x.2
  refine ⟨S.κIndex × ιW, Z, S.concat_bounded, ?_⟩
  intro qA' e' hqA'ν hMarg hDE
  have hidx' : #qA'.idx ≤ σ := by rw [← Cardinal.mk_congr (eA.trans e'.symm)]; exact hidx
  obtain ⟨qB', eB', hB'ν, hExt', hT'⟩ :=
    infra_610_tied_free_lift P σ hσ hμ hrec hσSucc f hf qA' hqA'ν hidx'
  let e'' : qB'.idx ≃ uIdx ⊕ cIdx := eB'.symm.trans e'
  -- the fragment `W`: both lifts answer it as their bases answer a good `w_k`
  obtain ⟨E1, hE1, hgood1⟩ := infra_76_tied_majority P σ1 hσ1 hμ hT1 f hf qA qB e hqAν
    (hidx.trans hσσ1) hT W hιW S hS
  obtain ⟨E2, hE2, hgood2⟩ := infra_76_tied_majority P σ1 hσ1 hμ hT1 f hf qA' qB' eB' hqA'ν
    (hidx'.trans hσσ1) hT' W hιW S hS
  obtain ⟨k, hk1, hk2⟩ := infra_76_two_good E1 E2 hσ2 hE1 hE2 hSbig
  have d1 := infra_73_diagramEq_of_eq (infra_73_scheme_comp (hgood1 k hk1) (Sum.map eA.symm id))
    (xs' := alignJoint eA (typeJoint (p := qA) (S.family k)))
    (ys' := alignJoint eb (typeJoint (p := qB) W))
    (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  have d2 := infra_73_diagramEq_of_eq (infra_73_scheme_comp (hgood2 k hk2) (Sum.map e'.symm id))
    (xs' := alignJoint e' (typeJoint (p := qA') (S.family k)))
    (ys' := alignJoint e'' (typeJoint (p := qB') W))
    (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  have dk := infra_73_diagramEq_of_eq
    (infra_73_scheme_comp hDE (Sum.map id (fun b : ιW => (k, b))))
    (xs' := alignJoint eA (typeJoint (p := qA) (S.family k)))
    (ys' := alignJoint e' (typeJoint (p := qA') (S.family k)))
    (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  have hPush : P.scheme.DiagramEq (X := qB.host) (Y := qB'.host)
      (alignJoint eb (typeJoint (p := qB) W)) (alignJoint e'' (typeJoint (p := qB') W)) :=
    P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d1)
      (P.scheme.diagram_trans _ _ _ _ _ _ dk d2)
  -- the `u`-marginals of the two lifts agree
  have hidxu : #uIdx ≤ σ := by
    have heq : #qA.idx = #(uIdx ⊕ cIdx) := Cardinal.mk_congr eA
    have hle : #uIdx ≤ #qA.idx := by
      rw [heq, mk_sum, lift_id]
      exact le_self_add
    exact hle.trans hidx
  have hMargB : SameGaloisType (qB.marginal eb) (qB'.marginal e'')
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ := infra_73_differing_test P σ hσ hμ hrec hσSucc
      (qB.marginal eb) (qB'.marginal e'') (Equiv.refl uIdx) (Equiv.refl uIdx) hqBν hB'ν
      hidxu (hidxu.trans_lt hσlt) hneq
    apply hnot
    have hβ1 : #β ≤ σ1 := by
      refine hβ.trans (le_trans ?_ (le_max_right σ (infra_73_chi P σ))) |>.trans
        (Order.le_succ _)
      exact (add_le_add le_rfl (le_max_left _ _)).trans (le_max_right _ _)
    have hβμ : #β < μ := hβ1.trans_lt ((infra_76_lt_h P σ1).trans (infra_73_h_lt hμ hT1))
    obtain ⟨SY, hSYτ, hSYκ, -, -⟩ := infra_73_sequence P σ2 hσ2 hμ hμT
      (infra_76_listTuple f hf Y) rfl (hβ1.trans hσ1σ2)
    have hSY : infra_73_h P σ1 ≤ SY.τ := hSYτ ▸ le_max_left _ _
    have hSYbig : σ2 < #SY.κIndex := hSYκ ▸ infra_76_lt_h P σ2
    obtain ⟨F1, hF1, hg1⟩ := infra_76_tied_majority P σ1 hσ1 hμ hT1 f hf qA qB e hqAν
      (hidx.trans hσσ1) hT Y hβ1 SY hSY
    obtain ⟨F2, hF2, hg2⟩ := infra_76_tied_majority P σ1 hσ1 hμ hT1 f hf qA' qB' eB' hqA'ν
      (hidx'.trans hσσ1) hT' Y hβ1 SY hSY
    obtain ⟨j, hj1, hj2⟩ := infra_76_two_good F1 F2 hσ2 hF1 hF2 hSYbig
    have m1 := infra_73_diagramEq_of_eq
      (infra_73_scheme_comp (hg1 j hj1) (Sum.map (fun a => eA.symm (Sum.inl a)) id))
      (xs' := alignJoint (Equiv.refl uIdx) (typeJoint (p := qA.marginal eA) (SY.family j)))
      (ys' := alignJoint (Equiv.refl uIdx) (typeJoint (p := qB.marginal eb) Y))
      (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    have m2 := infra_73_diagramEq_of_eq
      (infra_73_scheme_comp (hg2 j hj2) (Sum.map (fun a => e'.symm (Sum.inl a)) id))
      (xs' := alignJoint (Equiv.refl uIdx) (typeJoint (p := qA'.marginal e') (SY.family j)))
      (ys' := alignJoint (Equiv.refl uIdx) (typeJoint (p := qB'.marginal e'') Y))
      (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    have mA := infra_72_diagramEq_of_sameGalois (P := P) hMarg (SY.family j) hqAν hqA'ν
      (hidxu.trans_lt hσlt) hβμ
    exact P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ m1)
      (P.scheme.diagram_trans _ _ _ _ _ _ mA m2)
  -- isolation of `q_B` and restriction to `A`
  have hSGTb := hWiso.2 qB' e'' hB'ν hMargB hPush
  have hRes : SameGaloisType (qB.restrict f hf) (qB'.restrict f hf) eb e'' := by
    rcases hSGTb with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, ?_, ?_⟩
    · intro v
      ext x
      simp only [TupleOver.restrict, SystemArrow.comp, Language.Embedding.comp_apply]
      exact DFunLike.congr_fun (hcomm v) (f.onVertex v x)
    · intro j
      exact hval j
  have hResRefl : SameGaloisType (qB.restrict f hf) (qB'.restrict f hf)
      (Equiv.refl qB.idx) (e''.trans eb.symm) := by
    rcases hRes with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
    intro i
    have hv := hval (eb i)
    have h1 : eb.symm (eb i) = i := Equiv.symm_apply_apply _ _
    have h2 : (e''.trans eb.symm).symm i = e''.symm (eb i) := rfl
    have hv' := h1 ▸ hv
    exact h2 ▸ hv'
  have hMid := SameGaloisType.trans_via (P := P) hExt hResRefl σ hσ hσlt hidx hrec hqAν
    (by simpa [TupleOver.restrict] using hqBν) (by simpa [TupleOver.restrict] using hB'ν)
  have hBack : SameGaloisType (qB'.restrict f hf) qA' (Equiv.refl _) eB' :=
    SameGaloisType.symm hExt'
  have hJoin := SameGaloisType.trans_via (P := P) hMid hBack σ hσ hσlt hidx hrec hqAν
    (by simpa [TupleOver.restrict] using hB'ν) hqA'ν
  have hEqv : (e.trans (e''.trans eb.symm).symm).trans eB'.symm = eA.trans e'.symm := by
    ext j
    simp [e'', eb, Equiv.symm_trans_apply, Equiv.trans_apply]
  rcases hEqv ▸ hJoin with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro k
  have hv := hval (e'.symm k)
  have hL : eA.symm (e' (e'.symm k)) = eA.symm k :=
    congrArg eA.symm (Equiv.apply_symm_apply e' k)
  have hR : (Equiv.refl qA'.idx).symm (e'.symm k) = e'.symm k := rfl
  exact hR ▸ hL ▸ hv

/-- **Lemma 7.6 (English form).** At sufficiently closed levels, relative isolation descends
along a tied-free lift, for an arbitrary isolating fragment of the lift. -/
theorem lemma_7_6_tied (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B : P.scheme.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
        (hf : P.scheme.permitted (X := A) (Y := B) f)
        (qA : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
        (qB : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
        (e : qA.idx ≃ qB.idx) {uIdx cIdx : Type u} (eA : qA.idx ≃ uIdx ⊕ cIdx),
        qA.ν = μ → qB.ν = μ → #qA.idx ≤ σ →
        SameGaloisType qA (qB.restrict f hf) e (Equiv.refl qB.idx) →
        IsTiedFree f qA qB e →
        IsRelativelyIsolated qB (e.symm.trans eA) →
        IsRelativelyIsolated qA eA :=
  ⟨infra_73_tailSet P (infra_76_sigma2 P σ),
    infra_73_tail P _ ((hσ.trans (infra_76_lt_h P σ).le).trans (infra_76_lt_h P _).le),
    fun _ hμ _ _ f hf qA qB e _ _ eA hqA hqB hidx hExt hT hIso =>
      infra_76_tied_descent P σ hσ hμ f hf qA qB e eA hqA hqB hidx hExt hT hIso⟩

end
end
end AEC
