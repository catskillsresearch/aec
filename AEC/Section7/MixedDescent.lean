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

