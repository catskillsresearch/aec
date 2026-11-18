module

public import AEC.Section7.MixedTiedLift
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-!
# Mixed-level Lemma 7.6 descent and Proposition 7.8 matrix data

Split from `MixedLevel.lean` (grokbot_02) so that the descent can use the proved mixed tied
free lift of `MixedTiedLift.lean`.
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 3200000 in
/-- **Mixed-level Lemma 7.6 descent (proved modulo `infra_78_tied_free_lift_mixed`).** Port of
`infra_76_tied_descent` with `A` at level `ν ≤ μ` and `B` at level `μ`: the same-level structural
isomorphism, approximation sequences and Galois-type transitivity are replaced by
`infra_78_move_mixed`, `infra_78_sequence_mixed` and a diagram-level chain
(`infra_78_diagramEq_of_sameGalois`, `infra_78_sameGalois_of_diagramEq`). The only open input is
the mixed tied free lift of the competitor `q_A'`. -/
theorem infra_78_tied_descent_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible)
    (hνT : ν ∈ infra_73_tailSet P (infra_76_sigma2 P σ))
    (hμT : μ ∈ infra_73_tailSet P σ) (hνμ : ν ≤ μ)
    {A : P.scheme.Object ν hν}
    {B : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (qA : TupleOver K oneVertexShape P.scheme _ A)
    (qB : TupleOver K oneVertexShape P.scheme _ B)
    (e : qA.idx ≃ qB.idx) {uIdx cIdx : Type u} (eA : qA.idx ≃ uIdx ⊕ cIdx)
    (hqAν : qA.ν = ν) (hqBν : qB.ν = μ) (hidx : #qA.idx ≤ σ)
    (hExt : SameGaloisType qA (qB.restrict f hf) e (Equiv.refl qB.idx))
    (hT : IsTiedFreeMixed f qA qB e)
    (hIso : IsRelativelyIsolated qB (e.symm.trans eA)) :
    IsRelativelyIsolated qA eA := by
  classical
  let σ1 : Cardinal.{u} := infra_73_h P σ
  let σ2 : Cardinal.{u} := infra_76_sigma2 P σ
  have hσ1 : ℵ₀ ≤ σ1 := hσ.trans (infra_76_lt_h P σ).le
  have hσ2 : ℵ₀ ≤ σ2 := hσ1.trans (infra_76_lt_h P σ1).le
  have hσσ1 : σ ≤ σ1 := (infra_76_lt_h P σ).le
  have hσ1σ2 : σ1 ≤ σ2 := (infra_76_lt_h P σ1).le
  have hT0 : ν ∈ infra_73_tailSet P σ := infra_76_tail_mono (le_trans hσ1σ2 le_rfl) hνT
  have hT1 : ν ∈ infra_73_tailSet P σ1 := infra_76_tail_mono le_rfl hνT
  have hμ : μ ∈ P.eligible := Tail.mem (infra_73_tail P σ hσ) hμT
  have hrec : ν ∈ recursionClosedLevels P σ := infra_73_tail_rec hT0
  have hrecμ : μ ∈ recursionClosedLevels P σ := infra_73_tail_rec hμT
  have hσSucc : Order.succ σ ≤ ν := infra_73_tail_succ hT0
  have hσSuccμ : Order.succ σ ≤ μ := infra_73_tail_succ hμT
  have hσlt : σ < ν := (Order.lt_succ σ).trans_le hσSucc
  have hσltμ : σ < μ := (Order.lt_succ σ).trans_le hσSuccμ
  have hidxμ : #qA.idx < ν := hidx.trans_lt hσlt
  have hidxB : #qB.idx ≤ σ := by rw [← Cardinal.mk_congr e]; exact hidx
  let eb : qB.idx ≃ uIdx ⊕ cIdx := e.symm.trans eA
  -- Proposition 7.3: a fragment of size at most `h(σ)`
  obtain ⟨ιW, W, hιW, hWiso⟩ := infra_73_uniform_of_block P σ hσ
    (infra_73_block_restriction P σ hσ) hμT qB eb hqBν hidxB (hidxB.trans_lt hσltμ) hIso
  -- an approximation list of `tp(W/A)`
  have hιW2 : #ιW ≤ σ2 := hιW.trans hσ1σ2
  obtain ⟨S, hSτ, hSκ, -, -⟩ := infra_78_sequence_mixed P σ2 hσ2 hν hνT
    (infra_78_listTupleMixed f hf W) hιW2
  have hS : infra_73_h P σ1 ≤ S.τ := hSτ ▸ le_max_left _ _
  have hSbig : σ2 < #S.κIndex := hSκ ▸ infra_76_lt_h P σ2
  let Z : S.κIndex × ιW → Occurrence K oneVertexShape (P.scheme.asSystem hν A) :=
    fun x => S.family x.1 x.2
  refine ⟨S.κIndex × ιW, Z, S.concat_bounded, ?_⟩
  intro qA' e' hqA'ν hMarg hDE
  have hidx' : #qA'.idx ≤ σ := by rw [← Cardinal.mk_congr (eA.trans e'.symm)]; exact hidx
  obtain ⟨qB', eB', hB'ν, hExt', hT'⟩ :=
    infra_78_tied_free_lift_mixed P σ hσ hν hrec hσSucc hμ hrecμ hνμ f hf qA' hqA'ν hidx'
  let e'' : qB'.idx ≃ uIdx ⊕ cIdx := eB'.symm.trans e'
  -- the fragment `W`: both lifts answer it as their bases answer a good `w_k`
  obtain ⟨E1, hE1, hgood1⟩ := infra_78_tied_majority_mixed P σ1 hσ1 hν hT1 hμ hνμ f hf qA qB e hqAν
    (hidx.trans hσσ1) hT W hιW S hS
  obtain ⟨E2, hE2, hgood2⟩ := infra_78_tied_majority_mixed P σ1 hσ1 hν hT1 hμ hνμ f hf qA' qB' eB' hqA'ν
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
    obtain ⟨β, Y, hβ, hnot⟩ := infra_73_differing_test P σ hσ hμ hrecμ hσSuccμ
      (qB.marginal eb) (qB'.marginal e'') (Equiv.refl uIdx) (Equiv.refl uIdx) hqBν hB'ν
      hidxu (hidxu.trans_lt hσltμ) hneq
    apply hnot
    have hβ1 : #β ≤ σ1 := by
      refine hβ.trans (le_trans ?_ (le_max_right σ (infra_73_chi P σ))) |>.trans
        (Order.le_succ _)
      exact (add_le_add le_rfl (le_max_left _ _)).trans (le_max_right _ _)
    have hβμ : #β < ν := hβ1.trans_lt ((infra_76_lt_h P σ1).trans (infra_73_h_lt hν hT1))
    obtain ⟨SY, hSYτ, hSYκ, -, -⟩ := infra_78_sequence_mixed P σ2 hσ2 hν hνT
      (infra_78_listTupleMixed f hf Y) (hβ1.trans hσ1σ2)
    have hSY : infra_73_h P σ1 ≤ SY.τ := hSYτ ▸ le_max_left _ _
    have hSYbig : σ2 < #SY.κIndex := hSYκ ▸ infra_76_lt_h P σ2
    obtain ⟨F1, hF1, hg1⟩ := infra_78_tied_majority_mixed P σ1 hσ1 hν hT1 hμ hνμ f hf qA qB e hqAν
      (hidx.trans hσσ1) hT Y hβ1 SY hSY
    obtain ⟨F2, hF2, hg2⟩ := infra_78_tied_majority_mixed P σ1 hσ1 hν hT1 hμ hνμ f hf qA' qB' eB' hqA'ν
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
      simp only [TupleOver.restrict, SystemArrow.comp]
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
  -- chain of diagrams through the two restrictions (no same-level transitivity needed)
  let E' : qB'.idx ≃ qB.idx := e''.trans eb.symm
  let G : qA'.idx ≃ qB.idx := eB'.trans E'
  have hgσ : P.g σ + ls K < ν :=
    (le_trans (add_le_add le_rfl (le_max_left _ _)) (le_max_right _ _) |>.trans
      (le_max_right σ (infra_73_chi P σ))).trans_lt
      ((Order.lt_succ_of_not_isMax (not_isMax _)).trans (infra_73_h_lt hν hT0))
  have hbd : ∀ {ι β : Type u}, #ι ≤ σ → #β ≤ P.g σ + ls K → #(ι ⊕ β) < ν := by
    intro ι β hι hβ
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hν) (hι.trans_lt hσlt) (hβ.trans_lt hgσ)
  have hRν : (qB.restrict f hf).ν = μ := by simpa [TupleOver.restrict] using hqBν
  have hR'ν : (qB'.restrict f hf).ν = μ := by simpa [TupleOver.restrict] using hB'ν
  have hSGT : SameGaloisType qA qA' (e.trans G.symm) (Equiv.refl qA'.idx) := by
    refine infra_78_sameGalois_of_diagramEq P σ hσ hν hrec hσlt qA qA' (e.trans G.symm)
      hidx hqAν hqA'ν ?_
    intro β Z hβ
    have b1 := hbd (ι := qB.idx) (β := β) hidxB hβ
    have b1μ : #(qB.idx ⊕ β) < μ := b1.trans_le hνμ
    have d1 := infra_78_diagramEq_of_sameGalois hExt Z (by rw [hqAν]; exact b1) (by rw [hRν]; exact b1μ)
    have d2 := infra_78_diagramEq_of_sameGalois hResRefl Z (by rw [hRν]; exact b1μ)
      (by rw [hR'ν]; exact b1μ)
    have d3 := P.scheme.diagram_symm _ _ _ _ (hExt' Z (hβ.trans_lt hgσ))
    have d3' := infra_73_diagramEq_of_eq (infra_73_scheme_comp d3 (Sum.map G.symm id))
      (xs' := alignJoint E' (typeJoint (p := qB'.restrict f hf) Z))
      (ys' := alignJoint G (typeJoint (p := qA') Z))
      (fun t => by cases t <;> simp [alignJoint, typeJoint, G]) (fun t => by cases t <;> rfl)
    have d := P.scheme.diagram_trans _ _ _ _ _ _ d1 (P.scheme.diagram_trans _ _ _ _ _ _ d2 d3')
    exact infra_73_diagramEq_of_eq (infra_73_scheme_comp d (Sum.map G id))
      (fun t => by cases t <;> simp [alignJoint, typeJoint])
      (fun t => by cases t <;> simp [alignJoint, typeJoint])
  have hEqv : e.trans G.symm = eA.trans e'.symm := by
    ext j
    simp [G, E', e'', eb, Equiv.trans_apply]
  rcases hEqv ▸ hSGT with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro k
  have hv := hval (e'.symm k)
  have hL : eA.symm (e' (e'.symm k)) = eA.symm k :=
    congrArg eA.symm (Equiv.apply_symm_apply e' k)
  have hR : (Equiv.refl qA'.idx).symm (e'.symm k) = e'.symm k := rfl
  exact hR ▸ hL ▸ hv

/-- **Mixed-level Lemma 7.6 (proved modulo `infra_78_tied_free_lift_mixed`).** Relative
isolation descends along a mixed-level tied-free lift (`A` at level `ν ≤ μ`, `B` at level `μ`).
Mirror of `lemma_7_6_tied`, via `infra_78_tied_descent_mixed`. -/
theorem infra_78_lemma_7_6_mixed (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ ν (hν : ν ∈ T) μ (hμ : μ ∈ T) (A : P.scheme.Object ν (Tail.mem hT hν))
        (B : P.scheme.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
        (hf : P.scheme.permitted (X := A) (Y := B) f)
        (qA : TupleOver K oneVertexShape P.scheme (Tail.mem hT hν) A)
        (qB : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
        (e : qA.idx ≃ qB.idx) {uIdx cIdx : Type u} (eA : qA.idx ≃ uIdx ⊕ cIdx),
        ν ≤ μ → qA.ν = ν → qB.ν = μ → #qA.idx ≤ σ →
        SameGaloisType qA (qB.restrict f hf) e (Equiv.refl qB.idx) →
        IsTiedFreeMixed f qA qB e →
        IsRelativelyIsolated qB (e.symm.trans eA) →
        IsRelativelyIsolated qA eA :=
  ⟨infra_73_tailSet P (infra_76_sigma2 P σ),
    infra_73_tail P _ ((hσ.trans (infra_76_lt_h P σ).le).trans (infra_76_lt_h P _).le),
    fun _ hν _ hμ _ _ f hf qA qB e _ _ eA hνμ hqA hqB hidx hExt hT hIso =>
      infra_78_tied_descent_mixed P σ hσ _ hν
        (infra_76_tail_mono (infra_76_lt_h P (infra_73_h P σ)).le hμ)
        hνμ f hf qA qB e eA hqA hqB hidx hExt hT hIso⟩

/-- The well-order of length `ρ⁺` is a regular-cardinal order. -/
theorem infra_78_succ_isRegularCardinalOrder (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ) :
    IsRegularCardinalOrder (Order.succ ρ).ord.ToType :=
  ⟨by rw [Ordinal.type_toType, Ordinal.cof_toType, (Cardinal.isRegular_succ hρ).cof_ord]⟩

theorem infra_78_succ_cof_ne (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ) :
    Order.cof (Order.succ ρ).ord.ToType ≠ ℵ₀ := by
  rw [Ordinal.cof_toType, (Cardinal.isRegular_succ hρ).cof_ord]
  exact ((Order.lt_succ_of_not_isMax (not_isMax ρ)).trans_le' hρ).ne'

/-- **Pressing down on `ρ⁺` (Fodor; proved, from Mathlib).** A regressive function on a
stationary subset of `ρ⁺` is constant on a stationary subset. Used for the `ρ⁺`-matrix of
Proposition 7.8. -/
theorem infra_78_fodor (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ)
    {s : Set (Order.succ ρ).ord.ToType} (hs : IsStationary s)
    {g : (Order.succ ρ).ord.ToType → (Order.succ ρ).ord.ToType} (hg : ∀ x ∈ s, g x < x) :
    ∃ a, IsStationary (s ∩ g ⁻¹' {a}) :=
  haveI := infra_78_succ_isRegularCardinalOrder ρ hρ
  exists_isStationary_preimage_singleton (infra_78_succ_cof_ne ρ hρ) hs hg

/-- **High-cofinality stages are stationary (Prop 7.8 proof, proved).** For infinite `λ < ρ`,
the stages `i < ρ⁺` with `cf(i) > λ` form a stationary subset of `ρ⁺`: in any club take the
`λ⁺`-th point of its normal enumeration, whose cofinality is `λ⁺`. -/
theorem infra_78_stationary_high_cof (ρ l : Cardinal.{u}) (hl : ℵ₀ ≤ l) (hlρ : l < ρ) :
    IsStationary {x : (Order.succ ρ).ord.ToType | l < Order.cof (Set.Iio x)} := by
  have hρ : ℵ₀ ≤ ρ := hl.trans hlρ.le
  haveI := infra_78_succ_isRegularCardinalOrder ρ hρ
  intro C hC
  have he := hC.isNormal_enum
  set e := Subtype.val ∘ Order.enum C hC.isCofinal with he_def
  have hlt : (Order.succ l).ord < Ordinal.type (α := (Order.succ ρ).ord.ToType) (· < ·) := by
    rw [Ordinal.type_toType, Cardinal.ord_lt_ord]
    exact Order.succ_lt_succ_iff.2 hlρ
  set y : (Order.succ ρ).ord.ToType := Ordinal.enum (α := (Order.succ ρ).ord.ToType) (· < ·)
    ⟨(Order.succ l).ord, hlt⟩ with hy_def
  have hcy : Order.cof (Set.Iio y) = Order.succ l := by
    rw [Order.cof_Iio, hy_def, Ordinal.typein_enum, (Cardinal.isRegular_succ hl).cof_ord]
  have hone : (1 : Cardinal) < Order.succ l :=
    (Order.lt_succ_of_not_isMax (not_isMax l)).trans_le' (one_le_aleph0.trans hl)
  have hyl : Order.IsSuccLimit y := by
    refine ⟨fun hmin => ?_, fun b hb => ?_⟩
    · have : IsEmpty (Set.Iio y) := ⟨fun z => hmin.not_lt z.2⟩
      have h0 := Order.cof_le_cardinalMk (α := Set.Iio y)
      rw [Cardinal.mk_eq_zero, hcy] at h0
      exact absurd h0 (not_le.2 (hone.trans_le' zero_le_one))
    · have : Nonempty (Set.Iio y) := ⟨⟨b, hb.lt⟩⟩
      have h1 : Order.cof (Set.Iio y) ≤ 1 :=
        Order.cof_le_one_iff.2 ⟨⟨b, hb.lt⟩, fun z => hb.le_of_lt z.2⟩
      rw [hcy] at h1
      exact absurd h1 (not_le.2 hone)
  refine ⟨e y, ?_, (Order.enum C hC.isCofinal y).2⟩
  show l < Order.cof (Set.Iio (e y))
  let f : Set.Iio y → Set.Iio (e y) := fun z => ⟨e z, he.strictMono z.2⟩
  have hf : StrictMono f := fun _ _ h => he.strictMono h
  have hf' : IsCofinal (Set.range f) := by
    intro t
    obtain ⟨a, ha, hta⟩ := (he.lt_iff_exists_lt hyl).1 t.2
    exact ⟨f ⟨a, ha⟩, ⟨_, rfl⟩, hta.le⟩
  have := Order.lift_cof_congr_of_strictMono hf hf'
  simp only [Cardinal.lift_id] at this
  rw [← this, hcy]
  exact Order.lt_succ_of_not_isMax (not_isMax l)

/-- **Small sets of a continuous chain appear early (Prop 7.8 proof, proved).** If `S` is an
increasing chain of sets which is continuous at `i` (`S i ⊆ ⋃_{j<i} S j`) and `d ⊆ S i` has size
at most `λ < cf(i)`, then `d ⊆ S j` for some `j < i`. -/
theorem infra_78_bounded_in_earlier_stage {α : Type u} [LinearOrder α] [WellFoundedLT α]
    {E : Type u} (S : α → Set E) (hS : Monotone S) {i : α} (hi : S i ⊆ ⋃ j ∈ Set.Iio i, S j)
    {d : Set E} (hd : d ⊆ S i) {l : Cardinal.{u}} (hdl : #d ≤ l)
    (hcof : l < Order.cof (Set.Iio i)) :
    ∃ j < i, d ⊆ S j := by
  have H : ∀ e : d, ∃ j : Set.Iio i, e.1 ∈ S j := by
    intro e
    have := hi (hd e.2)
    simp only [Set.mem_iUnion, Set.mem_Iio] at this
    obtain ⟨j, hj, he⟩ := this
    exact ⟨⟨j, hj⟩, he⟩
  choose g hg using H
  have hnc : ¬ IsCofinal (Set.range g) := fun hc =>
    (Order.cof_le hc).not_gt ((Cardinal.mk_range_le.trans hdl).trans_lt hcof)
  rw [IsCofinal] at hnc
  push Not at hnc
  obtain ⟨j, hj⟩ := hnc
  refine ⟨j.1, j.2, fun e he => hS ?_ (hg ⟨e, he⟩)⟩
  exact (le_of_lt (hj _ ⟨⟨e, he⟩, rfl⟩) : (g ⟨e, he⟩ : α) ≤ j.1)

/-- **One fixed failing list on a stationary set (Prop 7.8 proof, proved).** Suppose at every
stage `i` of a stationary `T ⊆ ρ⁺` a list `d i` is chosen which already lies in an earlier stage
`j < i` (`inS j (d i)`), and each stage has at most `ρ` lists. Then Fodor's pressing-down lemma
fixes the stage and a partition into `ρ < ρ⁺` pieces fixes the list: one `d₀` (lying in one
stage `j`) equals `d i` stationarily often. -/
theorem infra_78_stationary_fixed_list (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ) {L : Type u}
    (inS : (Order.succ ρ).ord.ToType → L → Prop)
    (hcount : ∀ j, #{x : L // inS j x} ≤ ρ)
    {T : Set (Order.succ ρ).ord.ToType} (hT : IsStationary T)
    (d : (Order.succ ρ).ord.ToType → L) (hd : ∀ i ∈ T, ∃ j < i, inS j (d i)) :
    ∃ j d₀, inS j d₀ ∧ IsStationary (T ∩ {i | d i = d₀}) := by
  have hcof : Order.cof (Order.succ ρ).ord.ToType = Order.succ ρ := by
    rw [Ordinal.cof_toType, (Cardinal.isRegular_succ hρ).cof_ord]
  have hne := infra_78_succ_cof_ne ρ hρ
  let g : (Order.succ ρ).ord.ToType → (Order.succ ρ).ord.ToType := fun i =>
    if h : i ∈ T then Classical.choose (hd i h) else i
  have hgT : ∀ i (hi : i ∈ T), g i = Classical.choose (hd i hi) := fun i hi => by
    simp only [g, hi, ↓reduceDIte]
  have hg : ∀ i ∈ T, g i < i := fun i hi => by
    rw [hgT i hi]; exact (Classical.choose_spec (hd i hi)).1
  obtain ⟨j, hj⟩ := infra_78_fodor ρ hρ hT hg
  have hsub : T ∩ g ⁻¹' {j} ⊆ ⋃ x : {x : L // inS j x}, T ∩ {i | d i = x.1} := by
    rintro i ⟨hiT, hij⟩
    have hij' : g i = j := hij
    have : inS j (d i) := by
      have := (Classical.choose_spec (hd i hiT)).2
      rwa [← hgT i hiT, hij'] at this
    exact Set.mem_iUnion.2 ⟨⟨d i, this⟩, hiT, rfl⟩
  obtain ⟨x, hx⟩ := (isStationary_iUnion_iff hne (by
    simp only [Cardinal.lift_id]; rw [hcof]
    exact (hcount j).trans_lt (Order.lt_succ_of_not_isMax (not_isMax ρ)))).1 (hj.mono hsub)
  exact ⟨j, x.1, x.2, hx⟩

/-! ### Bookkeeping closure (Prop 7.8, "close the sets under these operations for `λ⁺` steps")

`infra_78_closureStage` iterates a closure operation `F` (sending each small parameter set to
the at most `ρ` points it requests: mixed Löwenheim–Skolem pairs, Lemma 6.9 copies) along a
well-order; `infra_78_cardinal_closure` runs it for `λ⁺` steps. Base and top bookkeeping sets
`R ⊆ S` are handled at once by taking `E` to be a sum of the two carriers. -/

noncomputable def infra_78_closureStage {E : Type u} {W : Type u} [LinearOrder W] [WellFoundedLT W]
    (R₀ : Set E) (ℓ : Cardinal.{u}) (F : Set E → Set E) : W → Set E :=
  (wellFounded_lt (α := W)).fix (fun i rec => R₀ ∪ ⋃ j : Set.Iio i, (rec j.1 j.2 ∪
    ⋃ s : {s : Set E // s ⊆ rec j.1 j.2 ∧ #s ≤ ℓ}, F s.1))

theorem infra_78_closureStage_eq {E W : Type u} [LinearOrder W] [WellFoundedLT W]
    (R₀ : Set E) (ℓ : Cardinal.{u}) (F : Set E → Set E) (i : W) :
    infra_78_closureStage R₀ ℓ F i = R₀ ∪ ⋃ j : Set.Iio i, (infra_78_closureStage R₀ ℓ F j.1 ∪
      ⋃ s : {s : Set E // s ⊆ infra_78_closureStage R₀ ℓ F j.1 ∧ #s ≤ ℓ}, F s.1) := by
  unfold infra_78_closureStage
  rw [WellFounded.fix_eq]

theorem infra_78_small_subsets_card {E : Type u} (A : Set E) {ℓ ρ : Cardinal.{u}}
    (hρ : ℵ₀ ≤ ρ) (hpow : ρ ^ ℓ = ρ) (hA : #A ≤ ρ) :
    #{s : Set E // s ⊆ A ∧ #s ≤ ℓ} ≤ ρ := by
  classical
  have hinj : Function.Injective (fun s : {s : Set E // s ⊆ A ∧ #s ≤ ℓ} =>
      (⟨Subtype.val ⁻¹' s.1, (Cardinal.mk_preimage_of_injective _ _ Subtype.val_injective).trans
        s.2.2⟩ : {t : Set A // #t ≤ ℓ})) := by
    intro t1 t2 hE
    obtain ⟨s1, h1, k1⟩ := t1
    obtain ⟨s2, h2, k2⟩ := t2
    have heq' : (Subtype.val ⁻¹' s1 : Set A) = Subtype.val ⁻¹' s2 := congrArg Subtype.val hE
    apply Subtype.ext
    ext x
    constructor
    · intro hx
      have : (⟨x, h1 hx⟩ : A) ∈ (Subtype.val ⁻¹' s2 : Set A) := heq' ▸ hx
      exact this
    · intro hx
      have : (⟨x, h2 hx⟩ : A) ∈ (Subtype.val ⁻¹' s1 : Set A) := heq'.symm ▸ hx
      exact this
  refine (Cardinal.mk_le_of_injective hinj).trans ((Cardinal.mk_bounded_set_le A ℓ).trans ?_)
  calc max #A ℵ₀ ^ ℓ ≤ ρ ^ ℓ := Cardinal.power_le_power_right (max_le hA hρ)
    _ = ρ := hpow

/-- **Cardinal closure for `λ⁺` steps (proved).** If `ℵ₀ ≤ λ < ρ = ρ^λ` and every set of size
at most `λ` requests at most `ρ` points, then every `R₀` of size at most `ρ` lies in a set `R` of
size at most `ρ` closed under the requests: `F s ⊆ R` for every `s ⊆ R` with `#s ≤ λ`
(regularity of `λ⁺` puts each small `s` inside an earlier stage). -/
theorem infra_78_cardinal_closure {E : Type u} (R₀ : Set E) {ℓ ρ : Cardinal.{u}}
    (hℓ : ℵ₀ ≤ ℓ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ) (F : Set E → Set E)
    (hF : ∀ s : Set E, #s ≤ ℓ → #(F s) ≤ ρ) (hR₀ : #R₀ ≤ ρ) :
    ∃ R : Set E, R₀ ⊆ R ∧ #R ≤ ρ ∧ ∀ s ⊆ R, #s ≤ ℓ → F s ⊆ R := by
  classical
  let W : Type u := (Order.succ ℓ).ord.ToType
  have hρ : ℵ₀ ≤ ρ := hℓ.trans hℓρ.le
  have hW : #W = Order.succ ℓ := mk_ord_toType _
  have hWρ : #W ≤ ρ := hW.le.trans (Order.succ_le_of_lt hℓρ)
  have hcof : Order.cof W = Order.succ ℓ := by
    rw [Ordinal.cof_toType, (Cardinal.isRegular_succ hℓ).cof_ord]
  have hbound : ∀ T : Set W, #T ≤ ℓ → ∃ a : W, ∀ b ∈ T, b < a := by
    intro T hT
    have hnc : ¬ IsCofinal T := fun hc =>
      (Order.cof_le hc).not_gt (by rw [hcof]; exact hT.trans_lt (Order.lt_succ_of_not_isMax (not_isMax ℓ)))
    rw [IsCofinal] at hnc
    push Not at hnc
    exact hnc
  have hU : ∀ {ι : Type u} (f : ι → Set E), #ι ≤ ρ → (∀ i, #(f i) ≤ ρ) → #(⋃ i, f i) ≤ ρ :=
    fun f hι hf => (mk_iUnion_le f).trans ((mul_le_mul' hι (ciSup_le' hf)).trans
      (mul_eq_self hρ).le)
  have h2 : ∀ (A B : Set E), #A ≤ ρ → #B ≤ ρ → #(A ∪ B : Set E) ≤ ρ := fun A B hA hB =>
    (mk_union_le A B).trans ((add_le_add hA hB).trans (add_eq_self hρ).le)
  let st : W → Set E := infra_78_closureStage R₀ ℓ F
  have hst : ∀ i, #(st i) ≤ ρ := by
    intro i
    refine (wellFounded_lt (α := W)).induction (C := fun i => #(st i) ≤ ρ) i ?_
    intro i ih
    change #(infra_78_closureStage R₀ ℓ F i) ≤ ρ
    rw [infra_78_closureStage_eq]
    refine h2 _ _ hR₀ (hU _ ((mk_set_le _).trans hWρ) fun j => h2 _ _ (ih j.1 j.2) ?_)
    exact hU _ (infra_78_small_subsets_card _ hρ hpow (ih j.1 j.2)) fun s => hF _ s.2.2
  have hmono : ∀ {j i : W}, j < i → st j ⊆ st i := by
    intro j i hji x hx
    change x ∈ infra_78_closureStage R₀ ℓ F i
    rw [infra_78_closureStage_eq]
    exact Or.inr (Set.mem_iUnion.2 ⟨⟨j, hji⟩, Or.inl hx⟩)
  have hnew : ∀ {j i : W} (hji : j < i) (s : Set E), s ⊆ st j → #s ≤ ℓ → F s ⊆ st i := by
    intro j i hji s hs hsl x hx
    change x ∈ infra_78_closureStage R₀ ℓ F i
    rw [infra_78_closureStage_eq]
    exact Or.inr (Set.mem_iUnion.2 ⟨⟨j, hji⟩, Or.inr (Set.mem_iUnion.2 ⟨⟨s, hs, hsl⟩, hx⟩)⟩)
  have hR0st : ∀ i, R₀ ⊆ st i := by
    intro i x hx
    change x ∈ infra_78_closureStage R₀ ℓ F i
    rw [infra_78_closureStage_eq]
    exact Or.inl hx
  have hne : Nonempty W := by
    rw [← Cardinal.mk_ne_zero_iff, hW]; exact (zero_le.trans_lt (Order.lt_succ_of_not_isMax (not_isMax ℓ))).ne'
  obtain ⟨i0⟩ := hne
  refine ⟨⋃ i, st i, fun x hx => Set.mem_iUnion.2 ⟨i0, hR0st i0 hx⟩,
    hU _ hWρ hst, ?_⟩
  intro s hs hsl
  have hmem : ∀ x : s, ∃ i, x.1 ∈ st i := fun x => Set.mem_iUnion.1 (hs x.2)
  choose g hg using hmem
  obtain ⟨a, ha⟩ := hbound (Set.range g) (Cardinal.mk_range_le.trans hsl)
  obtain ⟨k, hk⟩ := hbound {a} (by rw [Cardinal.mk_singleton]; exact one_le_aleph0.trans hℓ)
  have hsa : s ⊆ st a := fun x hx => hmono (ha _ ⟨⟨x, hx⟩, rfl⟩) (hg ⟨x, hx⟩)
  exact (hnew (hk a rfl) s hsa hsl).trans (Set.subset_iUnion st k)

section Bookkeeping
open Classical

/-- Closure of `S` under `F` (via `infra_78_cardinal_closure`), or `S` if the hypotheses fail. -/
noncomputable def infra_78_bkClose {E : Type u} (ℓ ρ : Cardinal.{u}) (F : Set E → Set E)
    (S : Set E) : Set E :=
  if h : ℵ₀ ≤ ℓ ∧ ℓ < ρ ∧ ρ ^ ℓ = ρ ∧ (∀ s : Set E, #s ≤ ℓ → #(F s) ≤ ρ) ∧ #S ≤ ρ then
    Classical.choose (infra_78_cardinal_closure S h.1 h.2.1 h.2.2.1 F h.2.2.2.1 h.2.2.2.2)
  else S

theorem infra_78_bkClose_spec {E : Type u} {ℓ ρ : Cardinal.{u}} {F : Set E → Set E}
    {S : Set E} (hℓ : ℵ₀ ≤ ℓ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    (hF : ∀ s : Set E, #s ≤ ℓ → #(F s) ≤ ρ) (hS : #S ≤ ρ) :
    S ⊆ infra_78_bkClose ℓ ρ F S ∧ #(infra_78_bkClose ℓ ρ F S) ≤ ρ ∧
      ∀ s ⊆ infra_78_bkClose ℓ ρ F S, #s ≤ ℓ → F s ⊆ infra_78_bkClose ℓ ρ F S := by
  have h : ℵ₀ ≤ ℓ ∧ ℓ < ρ ∧ ρ ^ ℓ = ρ ∧ (∀ s : Set E, #s ≤ ℓ → #(F s) ≤ ρ) ∧ #S ≤ ρ :=
    ⟨hℓ, hℓρ, hpow, hF, hS⟩
  unfold infra_78_bkClose
  split_ifs
  exact Classical.choose_spec (infra_78_cardinal_closure S h.1 h.2.1 h.2.2.1 F h.2.2.2.1 h.2.2.2.2)

/-- Stages of the bookkeeping sets along a directed system of carriers. -/
noncomputable def infra_78_bkStage {W : Type u} [LinearOrder W] [WellFoundedLT W]
    (C : W → Type u) (step : ∀ {j i : W}, j < i → C j → C i)
    (F : ∀ i, Set (C i) → Set (C i)) (seed : ∀ i, Set (C i)) (ℓ ρ : Cardinal.{u}) :
    ∀ i, Set (C i) :=
  (wellFounded_lt (α := W)).fix (C := fun i => Set (C i)) (fun i rec =>
    if Order.IsSuccLimit i then ⋃ j : Set.Iio i, step j.2 '' rec j.1 j.2
    else infra_78_bkClose ℓ ρ (F i) (seed i ∪ ⋃ j : Set.Iio i, step j.2 '' rec j.1 j.2))

theorem infra_78_bkStage_eq {W : Type u} [LinearOrder W] [WellFoundedLT W]
    (C : W → Type u) (step : ∀ {j i : W}, j < i → C j → C i)
    (F : ∀ i, Set (C i) → Set (C i)) (seed : ∀ i, Set (C i)) (ℓ ρ : Cardinal.{u}) (i : W) :
    infra_78_bkStage C step F seed ℓ ρ i =
      if Order.IsSuccLimit i then
        ⋃ j : Set.Iio i, step j.2 '' infra_78_bkStage C step F seed ℓ ρ j.1
      else infra_78_bkClose ℓ ρ (F i)
        (seed i ∪ ⋃ j : Set.Iio i, step j.2 '' infra_78_bkStage C step F seed ℓ ρ j.1) := by
  unfold infra_78_bkStage
  rw [WellFounded.fix_eq]

/-- **Bookkeeping sets along a directed system (Prop 7.8, successor/limit construction; proved).**
Along a well-order `W` whose initial segments have size at most `ρ` (e.g. `ρ⁺`), with carriers
`C i` and forward maps `step : C j → C i` (`j < i`), closure requests `F i` of size at most `ρ` per
set of size at most `λ`, and seeds of size at most `ρ`, there are sets `R i ⊆ C i` with
`#R i ≤ ρ`, increasing (`step '' R j ⊆ R i`), continuous at limits (`R i = ⋃_{j<i} step '' R j`),
and at non-limit stages containing the seed and closed under `F i` (`infra_78_cardinal_closure`
for `λ⁺` steps). For Prop 7.8, `C i` is the sum of the carriers of `X_i` and `Y_i`. -/
theorem infra_78_bookkeeping_sets_abstract {W : Type u} [LinearOrder W] [WellFoundedLT W]
    (C : W → Type u) (step : ∀ {j i : W}, j < i → C j → C i)
    (F : ∀ i, Set (C i) → Set (C i)) (seed : ∀ i, Set (C i)) {ℓ ρ : Cardinal.{u}}
    (hℓ : ℵ₀ ≤ ℓ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    (hF : ∀ i (s : Set (C i)), #s ≤ ℓ → #(F i s) ≤ ρ) (hseed : ∀ i, #(seed i) ≤ ρ)
    (hW : ∀ i : W, #(Set.Iio i) ≤ ρ) :
    ∃ R : ∀ i, Set (C i),
      (∀ i, #(R i) ≤ ρ) ∧
      (∀ {j i : W} (h : j < i), step h '' R j ⊆ R i) ∧
      (∀ i, Order.IsSuccLimit i → R i = ⋃ j : Set.Iio i, step j.2 '' R j.1) ∧
      (∀ i, ¬ Order.IsSuccLimit i →
        seed i ⊆ R i ∧ ∀ s ⊆ R i, #s ≤ ℓ → F i s ⊆ R i) := by
  have hρ : ℵ₀ ≤ ρ := hℓ.trans hℓρ.le
  let R := infra_78_bkStage C step F seed ℓ ρ
  have hU : ∀ {ι : Type u} {E : Type u} (f : ι → Set E), #ι ≤ ρ → (∀ i, #(f i) ≤ ρ) →
      #(⋃ i, f i) ≤ ρ :=
    fun f hι hf => (mk_iUnion_le f).trans ((mul_le_mul' hι (ciSup_le' hf)).trans
      (mul_eq_self hρ).le)
  have hcard : ∀ i, #(R i) ≤ ρ := by
    intro i
    refine (wellFounded_lt (α := W)).induction (C := fun i => #(R i) ≤ ρ) i ?_
    intro i ih
    have hun : #(⋃ j : Set.Iio i, step j.2 '' R j.1) ≤ ρ :=
      hU _ (hW i) fun j => Cardinal.mk_image_le.trans (ih j.1 j.2)
    change #(infra_78_bkStage C step F seed ℓ ρ i) ≤ ρ
    rw [infra_78_bkStage_eq]
    split_ifs with hlim
    · exact hun
    · exact (infra_78_bkClose_spec hℓ hℓρ hpow (hF i)
        ((mk_union_le _ _).trans ((add_le_add (hseed i) hun).trans (add_eq_self hρ).le))).2.1
  have hbase : ∀ i, ¬ Order.IsSuccLimit i →
      seed i ∪ (⋃ j : Set.Iio i, step j.2 '' R j.1) ⊆ R i ∧
        ∀ s ⊆ R i, #s ≤ ℓ → F i s ⊆ R i := by
    intro i hlim
    have hun : #(⋃ j : Set.Iio i, step j.2 '' R j.1) ≤ ρ :=
      hU _ (hW i) fun j => Cardinal.mk_image_le.trans (hcard j.1)
    have hspec := infra_78_bkClose_spec hℓ hℓρ hpow (hF i)
      ((mk_union_le _ _).trans ((add_le_add (hseed i) hun).trans (add_eq_self hρ).le))
    have hRi : R i = infra_78_bkClose ℓ ρ (F i) (seed i ∪ ⋃ j : Set.Iio i, step j.2 '' R j.1) := by
      change infra_78_bkStage C step F seed ℓ ρ i = _
      rw [infra_78_bkStage_eq]
      split_ifs
      rfl
    rw [hRi]
    exact ⟨hspec.1, hspec.2.2⟩
  have hlimEq : ∀ i, Order.IsSuccLimit i → R i = ⋃ j : Set.Iio i, step j.2 '' R j.1 := by
    intro i hlim
    change infra_78_bkStage C step F seed ℓ ρ i = _
    rw [infra_78_bkStage_eq]
    split_ifs
    rfl
  refine ⟨R, hcard, ?_, hlimEq, fun i hlim => ⟨fun x hx => (hbase i hlim).1 (Or.inl hx),
    (hbase i hlim).2⟩⟩
  intro j i h x hx
  have hmem : x ∈ ⋃ j' : Set.Iio i, step j'.2 '' R j'.1 :=
    Set.mem_iUnion.2 ⟨⟨j, h⟩, hx⟩
  by_cases hlim : Order.IsSuccLimit i
  · rw [hlimEq i hlim]; exact hmem
  · exact (hbase i hlim).1 (Or.inr hmem)

/-- The `ρ⁺` instance of `infra_78_bookkeeping_sets_abstract` (initial segments of
`(succ ρ).ord.ToType` have size at most `ρ`). -/
theorem infra_78_bookkeeping_sets_succ {ρ ℓ : Cardinal.{u}}
    (C : (Order.succ ρ).ord.ToType → Type u)
    (step : ∀ {j i : (Order.succ ρ).ord.ToType}, j < i → C j → C i)
    (F : ∀ i, Set (C i) → Set (C i)) (seed : ∀ i, Set (C i))
    (hℓ : ℵ₀ ≤ ℓ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    (hF : ∀ i (s : Set (C i)), #s ≤ ℓ → #(F i s) ≤ ρ) (hseed : ∀ i, #(seed i) ≤ ρ) :
    ∃ R : ∀ i, Set (C i),
      (∀ i, #(R i) ≤ ρ) ∧
      (∀ {j i} (h : j < i), step h '' R j ⊆ R i) ∧
      (∀ i, Order.IsSuccLimit i → R i = ⋃ j : Set.Iio i, step j.2 '' R j.1) ∧
      (∀ i, ¬ Order.IsSuccLimit i →
        seed i ⊆ R i ∧ ∀ s ⊆ R i, #s ≤ ℓ → F i s ⊆ R i) := by
  refine infra_78_bookkeeping_sets_abstract C step F seed hℓ hℓρ hpow hF hseed ?_
  intro i
  have h := Cardinal.mk_Iio_lt i (by rw [mk_ord_toType, Ordinal.type_toType])
  rw [mk_ord_toType] at h
  exact Order.lt_succ_iff.1 h

end Bookkeeping

/-- **The `ρ⁺` matrix (data of Proposition 7.8's proof).** An increasing `ρ⁺`-chain of
pairs `X_i ≤ Y_i` at one level `κ`, with permitted inclusions commuting with the pair arrows (continuity at limits, Def 7.7, is not
encoded here). -/
structure Infra78Matrix (P : SingleModelData K) (ρ : Cardinal.{u}) {κ : Cardinal.{u}}
    (hκ : κ ∈ P.eligible) where
  X : (Order.succ ρ).ord.ToType → P.scheme.Object κ hκ
  Y : (Order.succ ρ).ord.ToType → P.scheme.Object κ hκ
  pair : ∀ i, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X i)) (P.scheme.asSystem hκ (Y i))
  pair_permitted : ∀ i, P.scheme.permitted (X := X i) (Y := Y i) (pair i)
  stepX : ∀ {i j}, i ≤ j →
    SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X i)) (P.scheme.asSystem hκ (X j))
  stepY : ∀ {i j}, i ≤ j →
    SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y i)) (P.scheme.asSystem hκ (Y j))
  stepX_permitted : ∀ {i j} (h : i ≤ j), P.scheme.permitted (X := X i) (Y := X j) (stepX h)
  stepY_permitted : ∀ {i j} (h : i ≤ j), P.scheme.permitted (X := Y i) (Y := Y j) (stepY h)
  comm : ∀ {i j} (h : i ≤ j),
    SystemArrow.comp (pair i) (stepY h) = SystemArrow.comp (stepX h) (pair j)

end
end AEC

