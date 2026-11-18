module

public import AEC.Section7.SeedStage

@[expose] public section

/-!
# Prop 7.8 for `p` realized at the level of `X` (`infra_78_assembly_glue`)

`infra_78_matrix_assembly_level`: the `proposition_7_8` conclusion on the tail
`infra_78_closedTail P` for every finite-tuple `p` over `X` realized at the level `λ` of `X`.
Glue of: `infra_78_assembly_levels` (`ρ = 2^λ`, matrix level `κ > ρ⁺`, `σ = λ`, `σd = θ`),
`infra_78_seed_stage` (seed `X → X_0`, `Y_0`, `b`, `I_p`, seeds `ι0(I_p) ∪ b`),
`infra_78_isolation_over_A` (isolated stage `i`, level-`λ` pair `A ≤ U` inside `X_i ≤ Y_i`
containing `I_p` and `b`), `infra_78_stage_transport` + `infra_78_tiedFreeMixed_trans` (the
stage-`i` mark is tied free over `X` along `ι0 ≫ g_i`), `infra_78_seq_diagram_transfer` (`I_p`
as a sequence for the stage mark), `infra_78_marginal_identify_level` (`φ : X ≅ A`,
`tp(bU/X) = p`) and `infra_78_iso_rename_asTuple` (isolation renamed along `φ`).
-/

universe u

open Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 1600000 in
/-- **`infra_78_matrix_assembly_level` (proved).** -/
theorem infra_78_matrix_assembly_level (P : SingleModelData K) :
    infra_78_matrix_assembly_level_statement P := by
  classical
  intro μ hμ X p θ hfin hpν hθ hθμ
  haveI : Finite p.idx := hfin
  have hel : μ ∈ P.eligible := Tail.mem (infra_78_closedTail_tail P) hμ
  have hμInf : ℵ₀ ≤ μ := P.aleph0_le hel
  obtain ⟨ρ, κ, hlρ, hpow, hρκ, hlκ, hκT, hκTθ, hlT2, hθsucc⟩ :=
    infra_78_assembly_levels P hμ hθ hθμ
  have hκel : κ ∈ P.eligible := Tail.mem (infra_73_tail P μ hμInf) hκT
  have hrecμθ : μ ∈ recursionClosedLevels P θ := (hμ.2.1 θ hθ hθμ).1
  have hrecκθ : κ ∈ recursionClosedLevels P θ := hκTθ.1
  have hpfin : #p.idx < ℵ₀ := Cardinal.mk_lt_aleph0
  have hidxθ : #p.idx ≤ θ := hpfin.le.trans hθ
  have hidxμ : #p.idx < μ := hpfin.trans_le hμInf
  have hidxρ : #p.idx ≤ ρ := hidxμ.le.trans hlρ.le
  obtain ⟨X0, Y0, ι0, p0, hp0, b0, seq, ⟨-, htest, hlong, hτν⟩, hD, hT, hIcard, hS⟩ :=
    infra_78_seed_stage P θ hθ (hν := hel) hrecμθ hθsucc hκel hrecκθ hlκ X p hpν hidxθ θ hθμ
      ρ hel hlκ hlρ hpow hlρ.le hidxρ
  have hne : Nonempty κ.ord.ToType := by
    rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_ord_toType]
    exact (aleph0_pos.trans_le (P.aleph0_le hκel)).ne'
  obtain ⟨y⟩ := hne
  obtain ⟨hg0, h5seed, hsub, h0, hclosed, hS0⟩ := hS y
  set I := infra_78_anchorImage ι0 seq with hIdef
  set s0 := infra_78_seedStage ρ hel X0 Y0 p0 hp0 id b0 (infra_78_seedSet I b0 y) with hs0def
  have hc : #θ.ord.ToType ≤ μ := by rw [Cardinal.mk_ord_toType]; exact hθμ.le
  have hidx : #(p.idx ⊕ θ.ord.ToType) ≤ μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact (add_le_add hidxμ.le hc).trans (add_eq_self hμInf).le
  have hcof : ∀ δ : (Order.succ ρ).ord.ToType, Order.IsSuccLimit δ →
      #p.idx < (Ordinal.ToType.toOrd δ).1.cof := fun δ hδ => infra_78_finite_lt_stage_cof δ hδ
  obtain ⟨i, -, hiso⟩ := infra_78_isolation_over_A P μ hμInf hκT (uIdx := p.idx)
    (cIdx := θ.ord.ToType) hρκ X0 hel s0 s0.e hidx hcof hlρ hpow hc h5seed hS0 h0 hclosed hlκ
    le_rfl hθ hθsucc hidxθ (Cardinal.mk_ord_toType θ).ge θ hθ le_rfl hlT2 hκTθ
  obtain ⟨i0, -, hi0⟩ := (wellFounded_lt (α := (Order.succ ρ).ord.ToType)).has_min Set.univ
    ⟨i, trivial⟩
  have hm : IsMin i0 := fun b _ => not_lt.1 (hi0 b trivial)
  have hii : i0 ≤ i := not_lt.1 (hi0 i trivial)
  have hmin0 : infra_78_rcObj X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i0 = s0 :=
    infra_78_pairMatrix_min s0 _ _ hm
  obtain ⟨hg, h5i⟩ := infra_78_rc_inv5_all P μ hμInf hκT hρκ X0 hel
    (infra_78_candS θ.ord.ToType) s0 s0.e hidx hcof h5seed i
  obtain ⟨hgx, hbu, F1, F2⟩ := infra_78_stage_transport hρκ X0 hel
    (infra_78_candS θ.ord.ToType) s0 s0.e ι0 rfl hidxμ hlκ hT hm i (infra_78_toArr hg)
    (fun x => infra_78_toArr_apply hg x)
  have hfwd := infra_78_rc_forward hρκ X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i0 i hii
  have hR0 : ∀ z, z ∈ infra_78_seedSet I b0 y →
      z ∈ (infra_78_rcObj X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i0).e.R := by
    intro z hz; rw [hmin0]; exact hsub hz
  let s₀ : Set (κ.ord.ToType ⊕ κ.ord.ToType) :=
    Sum.inl '' ((infra_78_rcMap X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i0 i).1 '' I) ∪
      Sum.inr '' Set.range (infra_78_rcObj X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i).e.b
  have hs₀R : s₀ ⊆ infra_78_rcSets hρκ X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i := by
    rintro z (⟨_, ⟨x, hx, rfl⟩, rfl⟩ | ⟨_, ⟨u, rfl⟩, rfl⟩)
    · exact hfwd ⟨Sum.inl x, hR0 _ (Or.inl ⟨x, hx, rfl⟩), rfl⟩
    · rw [hbu u]
      exact hfwd ⟨Sum.inr (b0 u), hR0 _ (Or.inr ⟨b0 u, Set.mem_insert_of_mem _ ⟨u, rfl⟩, rfl⟩),
        rfl⟩
  have hs₀card : #s₀ ≤ μ := by
    refine (Cardinal.mk_union_le _ _).trans ?_
    refine (add_le_add (Cardinal.mk_image_le.trans (Cardinal.mk_image_le.trans hIcard.le))
      (Cardinal.mk_image_le.trans (Cardinal.mk_range_le.trans hidxμ.le))).trans ?_
    exact (add_eq_self hμInf).le
  obtain ⟨A, U, jA, jU, gu, bU, hsq, hcov, -, -, hbY, hisoU⟩ :=
    hiso s₀ hs₀R hs₀card (fun k => Or.inr ⟨_, ⟨k, rfl⟩, rfl⟩)
  let q := infra_78_markTuple
    (infra_78_toArr (infra_78_rcObj X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i).hp)
    (infra_78_stageMark (infra_78_rcObj X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i))
  let ι := SystemArrow.comp ι0 (infra_78_toArr hg)
  have hTq : IsTiedFreeMixed ι (q.restrict ι trivial) q (Equiv.refl _) :=
    infra_78_tiedFreeMixed_trans ι0 trivial (infra_78_toArr hg) trivial q hlκ F1 h5i
  have hseedDE : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hel X)),
      #β < μ →
      P.scheme.DiagramEq (X := p.host) (Y := q.host)
        (alignJoint (Equiv.refl _) (typeJoint (p := p) Z)) (typeJoint (p := q.restrict ι trivial) Z) := by
    intro β Z hβ
    have h := P.scheme.diagram_trans _ _ _ _ _ _ (hD Z hβ) (F2 Z hβ)
    refine infra_73_diagramEq_of_eq h ?_ ?_
    · rintro (u | x) <;> rfl
    · rintro (u | x) <;> rfl
  let seqq : ApproximationSequence (q.restrict ι trivial) :=
    infra_78_seq_diagram_transfer (t2 := q.restrict ι trivial) (Equiv.refl p.idx) seq
      (fun Z hZ => by
        refine infra_73_diagramEq_of_eq (hseedDE Z (hZ.trans_lt hτν)) ?_ ?_
        · rintro (u | x) <;> rfl
        · rintro (u | x) <;> rfl)
  have hanch : ∀ a k, ∃ y, jA.onVertex PUnit.unit y =
      ι.onVertex PUnit.unit (seqq.family a k).2 := by
    intro a k
    have hmemI : ι0.onVertex PUnit.unit (seq.family a k).2 ∈ I :=
      ⟨(seq.family a k).2, ⟨(a, k), rfl⟩, rfl⟩
    have hval : ι.onVertex PUnit.unit (seqq.family a k).2 =
        (infra_78_rcMap X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i0 i).1
          (ι0.onVertex PUnit.unit (seq.family a k).2) := by
      show (infra_78_toArr hg).onVertex PUnit.unit (ι0.onVertex PUnit.unit (seq.family a k).2) = _
      rw [infra_78_toArr_apply hg]; exact hgx _
    rw [hval]
    rcases hcov (Or.inl ⟨_, ⟨_, hmemI, rfl⟩, rfl⟩) with ⟨_, ⟨y', hy⟩, he⟩ | ⟨_, -, he⟩
    · exact ⟨y', hy.trans (Sum.inl_injective he)⟩
    · exact (Sum.inr_ne_inl he).elim
  have hsq' : ∀ x, jU.onVertex PUnit.unit (gu.onVertex PUnit.unit x) =
      q.incl.onVertex PUnit.unit (jA.onVertex PUnit.unit x) := fun x =>
    congrArg (fun f => f.onVertex PUnit.unit x) hsq
  have hbU : ∀ k, q.val k = ⟨(bU k).1, jU.onVertex (bU k).1 (bU k).2⟩ := fun k => by
    show (⟨PUnit.unit, _⟩ : Occurrence K oneVertexShape _) =
      ⟨PUnit.unit, jU.onVertex PUnit.unit (bU k).2⟩
    rw [hbY k]
  obtain ⟨φ, hφ, -, hGal⟩ := infra_78_marginal_identify_level P θ hθ hel (hμ := hκel) hrecμθ
    hθμ hlκ (A := A) (U := U) p hpν hidxθ ι trivial q hlκ (Equiv.refl _) hseedDE hTq seqq
    htest hlong jA hanch gu jU hsq' bU hbU
  refine ⟨U, SystemArrow.comp φ gu, trivial, bU, hGal, ?_⟩
  intro cIdx c hc
  exact infra_78_iso_rename_asTuple φ hφ gu bU c (hisoU cIdx hc c)

end AEC
