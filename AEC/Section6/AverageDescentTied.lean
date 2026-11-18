module

public import AEC.Section7.TiedLocalCharacter

@[expose] public section

/-!
# Lemma 6.11 (average criterion for descent, tied form)

English Lemma 6.11 for `A → B` at eligible sizes `ν ≤ μ`, with "free lift" read as tied
freeness (`IsTiedFreeMixed`, which for `ν = μ` is `IsTiedFree`). It lives here, not in
`AEC/Section6/Results.lean`, because its proof uses the Section 7 tied infrastructure, which
imports `AEC.Section6.Results`.

Both cases are proved: `ν = μ` (`infra_611_tied`) and `ν < μ` (`infra_611_tied_mixed`, via a
level-`ν` realization of `q ↾ A`, its mixed tied free lift to `B`, and Theorem 6.6 at `μ`).
-/

namespace AEC
section

universe u

open Cardinal

section MixedAux

variable {K : AbstractElementaryClass.{u}}

/-- The level of the base is at most the level of any host over it. -/
theorem infra_611_le_nu {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} (t : TupleOver K oneVertexShape P.scheme hμ A) : μ ≤ t.ν := by
  have a := P.scheme.vertex_card hμ A PUnit.unit
  have b := P.scheme.vertex_card t.hν t.host PUnit.unit
  exact a.symm.le.trans
    ((Cardinal.mk_le_of_injective (t.incl.onVertex PUnit.unit).injective).trans b.le)

/-- Precompose a diagram equality with any reindexing, with pointwise identifications. -/
theorem infra_611_dEq_comp {P : SingleModelData K} {μ ν : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {X : P.scheme.Object μ hμ} {Y : P.scheme.Object ν hν} {α γ : Type u}
    {xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ X)}
    {ys : α → Occurrence K oneVertexShape (P.scheme.asSystem hν Y)}
    (h : P.scheme.DiagramEq (X := X) (Y := Y) xs ys) (ι : γ → α)
    {xs' : γ → Occurrence K oneVertexShape (P.scheme.asSystem hμ X)}
    {ys' : γ → Occurrence K oneVertexShape (P.scheme.asSystem hν Y)}
    (hx : ∀ c, xs' c = xs (ι c)) (hy : ∀ c, ys' c = ys (ι c)) :
    P.scheme.DiagramEq (X := X) (Y := Y) xs' ys' :=
  infra_73_diagramEq_of_eq (infra_73_scheme_comp h ι) (fun c => (hx c).symm)
    (fun c => (hy c).symm)

/-- Transport an approximation sequence across one Galois type over `A` (hosts at any levels),
at any smaller length bound `τ' < ν`. -/
noncomputable def infra_611_seqTransport {P : SingleModelData K} {ν : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {A : P.scheme.Object ν hν}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hν A} (e' : t2.idx ≃ t1.idx)
    (h : SameGaloisType t1 t2 (Equiv.refl t1.idx) e') (seq : ApproximationSequence t1)
    (τ' : Cardinal.{u}) (hτle : τ' ≤ seq.τ) (hτ' : τ' < ν) (hidx : #t1.idx < ν) :
    ApproximationSequence t2 where
  τ := τ'
  κIndex := seq.κIndex
  family i k := seq.family i (e' k)
  concat_bounded := by
    rw [Cardinal.mk_congr (Equiv.prodCongr (Equiv.refl seq.κIndex) e')]
    exact seq.concat_bounded
  few_exceptions := fun {β} W hW => by
    refine le_trans ?_ (seq.few_exceptions W (hW.trans hτle))
    refine Cardinal.mk_le_of_injective (f := fun j => ⟨j.1, fun hgood => j.2 ?_⟩) (by
      intro j₁ j₂ hj
      apply Subtype.ext
      have := congrArg Subtype.val hj
      exact this)
    have hb : #(t1.idx ⊕ β) < ν := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.add_lt_of_lt (P.aleph0_le hν) hidx (hW.trans_lt hτ')
    have D := infra_78_diagramEq_of_sameGalois h W (hb.trans_le (infra_611_le_nu t1))
      (hb.trans_le (infra_611_le_nu t2))
    have hgood' : P.scheme.DiagramEq (X := t1.host) (Y := A)
        (alignJoint (Equiv.refl t1.idx) (typeJoint (p := t1) W)) (seqJoint (seq.family j.1) W) :=
      infra_611_dEq_comp hgood id (fun c => by cases c <;> rfl) (fun _ => rfl)
    have X := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ D) hgood'
    refine infra_611_dEq_comp X (Sum.map e' id) ?_ (fun c => by cases c <;> rfl)
    rintro (k | d)
    · show _ = typeJoint (p := t2) W (Sum.inl (e'.symm (e' k)))
      rw [Equiv.symm_apply_apply]
    · rfl

set_option maxHeartbeats 3200000 in
/-- **Average criterion, mixed levels (`infra_611_tied_mixed`, English Lemma 6.11 for
`ν < μ`; proved).** Recursion-closed levels `σ⁺ ≤ ν ≤ μ`, `f : A → B` from level `ν` to level
`μ`, `q` over `B` realized at `μ` with `|q| ≤ σ`, and `I = (d_i : i ∈ κ)` in `A` with
`χ + ℵ₀ < κ < ν`, `g(σ) + LS(K) ≤ χ < ν`, such that for every query `Z ⊆ B` of size `≤ χ` all
but `|Z| + ℵ₀` of the `f(d_i) ⌢ Z` have the diagram of `q ↾ Z` (computed in `B`). Then `q` is
tied free from `A` across levels: `IsTiedFreeMixed f (q ↾ A) q`.

Proof: `I` is an approximation sequence of `q ↾ A` at size `χ`; common mixed moves with `I`
give tied freeness on queries of size `≤ χ`. For all bounded queries: realize `q ↾ A` at level
`ν` (`infra_78_same_level_realization`, a Galois-type copy `p'`), take the mixed tied free lift
`qB` of `p'` to `B` (`infra_78_tied_free_lift_mixed`; only its tied-freeness clause is used),
transport approximation sequences of `q ↾ A` to `p'` (`infra_611_seqTransport`), and identify
`qB` with `q` over `B` by Theorem 6.6 at `μ` (`infra_73_differing_test`), the tests of size
`≤ g(σ) + LS(K) ≤ χ` being answered alike through a move over `I`. -/
theorem infra_611_tied_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible)
    (hrecν : ν ∈ recursionClosedLevels P σ) (hσν : Order.succ σ ≤ ν)
    (hμ : μ ∈ P.eligible) (hrecμ : μ ∈ recursionClosedLevels P σ) (hνμ : ν ≤ μ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ)
    {κI : Type u} (I : κI → q.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (χ : Cardinal.{u}) (hχ : P.g σ + ls K ≤ χ) (hχν : χ < ν)
    (hκ : χ + ℵ₀ < #κI) (hκν : #κI < ν)
    (hmaj : ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ χ →
      #{i : κI // ¬ P.scheme.DiagramEq (X := q.host) (Y := B)
        (typeJoint (p := q) Z) (seqJoint (fun j => pushOcc f (I i j)) Z)} ≤ #ι + ℵ₀) :
    IsTiedFreeMixed f (q.restrict f hf) q (Equiv.refl _) := by
  classical
  have hσltν : σ < ν := (Order.lt_succ σ).trans_le hσν
  have hσμ : Order.succ σ ≤ μ := hσν.trans hνμ
  have hσltμ : σ < μ := hσltν.trans_le hνμ
  have hidxν : #q.idx < ν := hidx.trans_lt hσltν
  have hcb : #(κI × q.idx) < ν := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.mul_lt_of_lt (P.aleph0_le hν) hκν hidxν
  -- `I` is an approximation sequence for `q ↾ A` at size `χ`.
  let seqI : ApproximationSequence (q.restrict f hf) :=
    { τ := χ
      κIndex := κI
      family := I
      concat_bounded := hcb
      few_exceptions := fun {β} W hW => by
        have hβν : #β < ν := hW.trans_lt hχν
        have hsum : #(q.idx ⊕ β) < ν := by
          rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
          exact Cardinal.add_lt_of_lt (P.aleph0_le hν) hidxν hβν
        let fW : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
          fun b => pushOcc f (W b)
        refine le_trans ?_ (hmaj fW hW)
        refine Cardinal.mk_le_of_injective (f := fun j => ⟨j.1, fun hgood => j.2 ?_⟩)
          (by
            intro j₁ j₂ hj
            apply Subtype.ext
            have := congrArg Subtype.val hj
            exact this)
        have h2 := P.scheme.diagram_preserved A B f hf (seqJoint (I j.1) W) hsum
          (hsum.trans_le hνμ)
        have hpush : (fun t => (⟨(seqJoint (I j.1) W t).1,
            f.onVertex (seqJoint (I j.1) W t).1 (seqJoint (I j.1) W t).2⟩ :
              Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) =
            seqJoint (fun k => pushOcc f (I j.1 k)) fW := by
          funext t
          cases t <;> rfl
        rw [hpush] at h2
        have e1 := P.scheme.diagram_trans _ _ _ _ _ _ hgood
          (P.scheme.diagram_symm _ _ _ _ h2)
        exact infra_73_diagramEq_of_eq e1 (fun t => by cases t <;> rfl) (fun _ => rfl) }
  -- tied freeness at query sizes `≤ χ` (common moves with `I`)
  have hup : ∀ (seq : ApproximationSequence (q.restrict f hf)) {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
      (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      seq.τ + ℵ₀ < #seq.κIndex → #ι ≤ seq.τ → #ι < ν → #ι ≤ χ →
      infra_78_isMoveMixed f seq Z Z0 →
      P.scheme.DiagramEq (X := q.host) (Y := q.host)
        (typeJoint (p := q.restrict f hf) Z0) (typeJoint (p := q) Z) := by
    intro seq ι Z Z0 hlong hιτ hιν hιχ hmove
    obtain ⟨Z1, hZ1a, hZ1b⟩ := infra_78_common_move_mixed f hf hνμ seq seqI Z hιν
    have hcι : ℵ₀ ≤ #ι + ℵ₀ := le_add_self
    obtain ⟨i, hi1, hi2⟩ := infra_78_exists_outside_two
      {i | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
        (typeJoint (p := q.restrict f hf) Z0) (seqJoint (seq.family i) Z0)}
      {i | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
        (typeJoint (p := q.restrict f hf) Z1) (seqJoint (seq.family i) Z1)}
      hcι (seq.few_exceptions Z0 hιτ) (seq.few_exceptions Z1 hιτ)
      ((add_le_add hιτ le_rfl).trans_lt hlong)
    simp only [Set.mem_ofPred_eq, not_not] at hi1 hi2
    have E1 := P.scheme.diagram_trans _ _ _ _ _ _
      (P.scheme.diagram_trans _ _ _ _ _ _
        (P.scheme.diagram_trans _ _ _ _ _ _ hi1 (hmove i))
        (P.scheme.diagram_symm _ _ _ _ (hZ1a i)))
      (P.scheme.diagram_symm _ _ _ _ hi2)
    obtain ⟨j, hj1, hj2⟩ := infra_78_exists_outside_two
      {j | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
        (typeJoint (p := q.restrict f hf) Z1) (seqJoint (seqI.family j) Z1)}
      {j | ¬ P.scheme.DiagramEq (X := q.host) (Y := B)
        (typeJoint (p := q) Z) (seqJoint (fun k => pushOcc f (I j k)) Z)}
      hcι (seqI.few_exceptions Z1 hιχ) (hmaj Z hιχ)
      ((add_le_add hιχ le_rfl).trans_lt hκ)
    simp only [Set.mem_ofPred_eq, not_not] at hj1 hj2
    have E2 := P.scheme.diagram_trans _ _ _ _ _ _
      (P.scheme.diagram_trans _ _ _ _ _ _ hj1 (hZ1b j)) (P.scheme.diagram_symm _ _ _ _ hj2)
    exact P.scheme.diagram_trans _ _ _ _ _ _ E1 E2
  -- a level-`ν` realization `p'` of `q ↾ A` and its mixed tied free lift `qB` to `B`
  obtain ⟨p', e', hp'ν, hS⟩ := infra_78_same_level_realization (q.restrict f hf) hidxν
  have hidx' : #p'.idx ≤ σ := by rw [Cardinal.mk_congr e']; exact hidx
  obtain ⟨qB, eB, hBν, -, hTB⟩ :=
    infra_78_tied_free_lift_mixed P σ hσ hν hrecν hσν hμ hrecμ hνμ f hf p' hp'ν hidx'
  have hidxB : #qB.idx ≤ σ := by rw [← Cardinal.mk_congr eB]; exact hidx'
  -- every sequence of `q ↾ A` with a move: `q ↾ A` answers as `qB`
  have key : ∀ (seq : ApproximationSequence (q.restrict f hf)) {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
      (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      seq.τ + ℵ₀ < #seq.κIndex → #ι ≤ seq.τ → #ι < ν →
      infra_78_isMoveMixed f seq Z Z0 →
      P.scheme.DiagramEq (X := q.host) (Y := qB.host)
        (typeJoint (p := q.restrict f hf) Z0)
        (fun c => infra_612_anchored eB qB.incl qB.val Z (Sum.map e'.symm id c)) := by
    intro seq ι Z Z0 hlong hιτ hιν hmv
    let seq2 := infra_611_seqTransport e' hS seq #ι hιτ hιν hidxν
    have hlong2 : seq2.τ + ℵ₀ < #seq2.κIndex := (add_le_add hιτ le_rfl).trans_lt hlong
    have hmv2 : infra_78_isMoveMixed f seq2 Z Z0 := fun i =>
      infra_611_dEq_comp (hmv i) (Sum.map e' id) (fun c => by cases c <;> rfl)
        (fun c => by cases c <;> rfl)
    have dL := hTB seq2 Z Z0 hlong2 le_rfl hιν hmv2
    have hb : #(q.idx ⊕ ι) < ν := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.add_lt_of_lt (P.aleph0_le hν) hidxν hιν
    have D0 := infra_78_diagramEq_of_sameGalois hS Z0 (hb.trans_le (infra_611_le_nu _))
      (hb.trans_le (infra_611_le_nu _))
    have D0' := infra_611_dEq_comp D0 id
      (xs' := typeJoint (p := q.restrict f hf) Z0) (fun c => by cases c <;> rfl) (fun _ => rfl)
    have dL' := infra_611_dEq_comp dL (Sum.map e'.symm id)
      (xs' := alignJoint e' (typeJoint (p := p') Z0))
      (ys' := fun c => infra_612_anchored eB qB.incl qB.val Z (Sum.map e'.symm id c))
      (fun c => by cases c <;> rfl) (fun _ => rfl)
    exact P.scheme.diagram_trans _ _ _ _ _ _ D0' dL'
  -- `qB` and `q` have one Galois type over `B` (Theorem 6.6 at `μ`)
  have hSq : SameGaloisType qB q (eB.symm.trans e') (Equiv.refl q.idx) := by
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ :=
      infra_73_differing_test P σ hσ hμ hrecμ hσμ qB q (eB.symm.trans e') (Equiv.refl _)
        hBν hqν hidxB (hidxB.trans_lt hσltμ) hneq
    apply hnot
    have hβχ : #β ≤ χ := hβ.trans hχ
    have hβν : #β < ν := hβχ.trans_lt hχν
    obtain ⟨Y0, hY0⟩ := infra_78_move_query_mixed f hf hνμ seqI Y hβν
    have K1 := key seqI Y Y0 hκ hβχ hβν hY0
    have U := hup seqI Y Y0 hκ hβχ hβν hβχ hY0
    have R := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ K1) U
    exact infra_611_dEq_comp R id (fun c => by cases c <;> rfl) (fun c => by cases c <;> rfl)
  intro seq' ι Z Z0' hlong' hι' hιν hmv
  have K2 := key seq' Z Z0' hlong' hι' hιν hmv
  have hb : #(q.idx ⊕ ι) < ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hν) hidxν hιν
  have dS := infra_78_diagramEq_of_sameGalois hSq Z
    ((hb.trans_le hνμ).trans_le (infra_611_le_nu _)) ((hb.trans_le hνμ).trans_le (infra_611_le_nu _))
  have dS' := infra_611_dEq_comp dS id
    (xs' := fun c => infra_612_anchored eB qB.incl qB.val Z (Sum.map e'.symm id c))
    (ys' := infra_612_anchored (Equiv.refl q.idx) q.incl q.val Z)
    (fun c => by cases c <;> rfl) (fun c => by cases c <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ K2 dS'

end MixedAux

/-- **Lemma 6.11** (An average criterion for descent). Let `A → B` have eligible sizes
`ν ≤ μ`, and let `q = tp(d/B)` with `|d| ≤ σ < ν`. Choose `χ ≥ c(σ)` below `ν`. Suppose a
bounded sequence `I = (d_i : i < κ)` in `A`, with `χ + ℵ₀ < κ < ν`, has majority value `q ↾ Z`
on every query `Z ⊆ B` of size at most `χ`, with at most `|Z| + ℵ₀` exceptions (the diagram of
`f(d_i) ⌢ Z` computed in `B`). Then `q` is the free lift of its restriction to `A`: tied freeness
`IsTiedFreeMixed f (q ↾ A) q`.

Packaging as Theorem 6.10: a tail of sufficiently closed levels (both `ν` and `μ` in it),
`c(σ) = testCardinal (max LS(K) ℵ₀) g σ`.

**Status:** proved: `ν = μ` by `infra_611_tied`, `ν < μ` by `infra_611_tied_mixed`. -/
theorem lemma_6_11 {K : AbstractElementaryClass.{u}}
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ ν μ (hν : ν ∈ T) (hμ : μ ∈ T), ν ≤ μ →
      ∀ (A : P.scheme.Object ν (Tail.mem hT hν)) (B : P.scheme.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
        (hf : P.scheme.permitted (X := A) (Y := B) f)
        (q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
        {κI : Type u} (I : κI → q.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ A))
        (χ : Cardinal.{u}),
        q.ν = μ → #q.idx ≤ σ →
        testCardinal (max (ls K) ℵ₀) P.g σ ≤ χ → χ < ν →
        χ + ℵ₀ < #κI → #κI < ν →
        (∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem _ B)),
          #ι ≤ χ →
          #{i : κI // ¬ P.scheme.DiagramEq (X := q.host) (Y := B)
            (typeJoint (p := q) Z) (seqJoint (fun j => pushOcc f (I i j)) Z)} ≤ #ι + ℵ₀) →
        IsTiedFreeMixed f (q.restrict f hf) q (Equiv.refl _) := by
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun ν μ hν hμ hνμ A B f hf q κI I χ hqν hidx hχ hχν hκ hκν hmaj => ?_⟩
  rcases eq_or_lt_of_le hνμ with heq | hlt
  · subst heq
    exact infra_611_tied P σ hσ (Tail.mem hT hμ) hμ.1 hμ.2 f hf q hqν hidx I χ
      ((infra_611_test_le_testCardinal P σ).trans hχ) hχν hκ hκν hmaj
  · -- mixed levels `ν < μ`
    exact infra_611_tied_mixed P σ hσ (Tail.mem hT hν) hν.1 hν.2 (Tail.mem hT hμ) hμ.1 hνμ f hf
      q hqν hidx I χ ((infra_611_test_le_testCardinal P σ).trans hχ) hχν hκ hκν hmaj

end
end AEC
