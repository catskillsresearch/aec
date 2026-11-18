module

public import AEC.Section7.MixedDescent

@[expose] public section

/-!
# Tied local character (`infra_78_tied_local_character`)

The untied `IsFreeFrom` is vacuous (`AEC/Audit/FreeFromVacuous.lean`), so Prop 6.13 and the
local-character contradiction of Prop 7.8 are run on tied freeness `IsTiedFree`.

* (c) `infra_78_tiedFree_restrict` (**proved**): tied freeness along `X → A → B` restricts to
  tied freeness along `X → A` of the restriction to `A`.
* (b) `infra_78_tiedFree_base_mono` (**proved**): tied freeness along `X → A → B` gives tied
  freeness along `A → B` (Theorem 6.10 uniqueness of the free evaluation, via a common move).
* (a) bounded form `infra_78_tied_local_bounded` (**proved**): for each query bound
  `τ₀ < μ` some stage is tied-free up to queries of size `τ₀` (`IsTiedFreeUpTo`).
* testing reduction `infra_78_tiedFree_of_upTo` (**proved**): tied freeness up to the testing
  arity `g(σ) + LS(K)` is full tied freeness (tied free lift + Theorem 6.6).
* (a) `infra_78_tied_local` (**proved**): one stage is tied-free on every bounded query.
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- The tuple coordinates of an approximation sequence are below the level. -/
theorem infra_78_idx_lt_of_seq
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q) (hκ : seq.τ + ℵ₀ < #seq.κIndex) :
    #q.idx < μ := by
  have hne : Nonempty seq.κIndex := by
    rw [← Cardinal.mk_ne_zero_iff]
    exact (bot_le.trans_lt hκ).ne'
  obtain ⟨k⟩ := hne
  have hle : #q.idx ≤ #(seq.κIndex × q.idx) := by
    rw [← Cardinal.lift_id #q.idx, ← Cardinal.lift_id #(seq.κIndex × q.idx)]
    exact Cardinal.lift_mk_le'.2 ⟨⟨fun j => (k, j), fun a b h => (Prod.mk.inj h).2⟩⟩
  exact hle.trans_lt seq.concat_bounded

/-- **(c) Restriction of tied freeness (proved).** If `q` over `B` is tied free along
`X → A → B` from its restriction to `X`, then its restriction to `A` is tied free along
`X → A` from the same restriction to `X`. A move `Z ↦ Z₀` along `g` pushes along `f` to a
move along `g ≫ f` (`diagram_preserved` for the strong arrow `f`), and the anchored joint of
`q ↾ A` on `Z` is literally the anchored joint of `q` on `f(Z)`. -/
theorem infra_78_tiedFree_restrict
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := X) (Y := A) g)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (h : IsTiedFree (SystemArrow.comp g f)
      (q.restrict (SystemArrow.comp g f) (P.scheme.comp g f hg hf)) q (Equiv.refl _)) :
    IsTiedFree g ((q.restrict f hf).restrict g hg) (q.restrict f hf) (Equiv.refl _) := by
  intro seq ι Z Z0 hκ hι hιμ hmove
  have hidx : #q.idx < μ :=
    infra_78_idx_lt_of_seq (q := (q.restrict f hf).restrict g hg) seq hκ
  have hsum : #(q.idx ⊕ ι) < μ := by
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
  have hres := h seq fZ Z0 hκ hι hιμ hmove'
  exact hres

/-- The anchored joint along the identity is the type joint. -/
theorem infra_78_anchored_refl
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {base : P.scheme.Object μ hμ} (p : TupleOver K oneVertexShape P.scheme hμ base)
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ base)) :
    infra_612_anchored (Equiv.refl p.idx) p.incl p.val Z = typeJoint (p := p) Z := by
  funext t
  cases t <;> rfl

/-- Two sets of size at most an infinite `c < #κ` do not cover `κ`. -/
theorem infra_78_exists_outside_two {κ : Type u} (S T : Set κ) {c : Cardinal.{u}}
    (hc : ℵ₀ ≤ c) (hS : #S ≤ c) (hT : #T ≤ c) (hlt : c < #κ) :
    ∃ i, i ∉ S ∧ i ∉ T := by
  by_contra hcon
  push Not at hcon
  have hcov : (Set.univ : Set κ) ⊆ S ∪ T := fun i _ => by
    by_cases hi : i ∈ S
    · exact Or.inl hi
    · exact Or.inr (hcon i hi)
  have h1 : #κ ≤ c := by
    calc #κ = #(Set.univ : Set κ) := Cardinal.mk_univ.symm
      _ ≤ #(S ∪ T : Set κ) := Cardinal.mk_le_mk_of_subset hcov
      _ ≤ #S + #T := Cardinal.mk_union_le S T
      _ ≤ c + c := add_le_add hS hT
      _ = c := Cardinal.add_eq_self hc
  exact absurd hlt (not_lt.2 h1)

/-- Lemma 6.9 at a recursion-closed level, with query size at least a prescribed `t < μ`. -/
theorem infra_78_exists_seq_ge
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {base : P.scheme.Object μ hμ} (p : TupleOver K oneVertexShape P.scheme hμ base)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) {t : Cardinal.{u}} (ht : t < μ) :
    ∃ seq : ApproximationSequence p, t ≤ seq.τ ∧ seq.τ < μ ∧ seq.τ + ℵ₀ < #seq.κIndex := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #p.idx < μ := hidx.trans_lt hσlt
  let τ : Cardinal.{u} := max t ℵ₀
  have hτ : ℵ₀ ≤ τ := le_max_right _ _
  have hτμ : τ < μ := max_lt ht (P.aleph0_lt hμ)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ := by
    apply hrec.2
    exact max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
  let ρ : Cardinal.{u} := max τ #p.idx
  have hρinf : ℵ₀ ≤ ρ := hτ.trans (le_max_left _ _)
  have hρμ : ρ < μ := max_lt hτμ hidxμ
  let κ : Cardinal.{u} := Order.succ ρ
  have hκinf : ℵ₀ ≤ κ := hρinf.trans (Order.le_succ _)
  have hκμ : κ < μ :=
    (Order.succ_le_of_lt (cantor ρ)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hρμ)
  have hprodκ : κ * #p.idx < μ := by
    have hmul : κ * #p.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    rcases le_total σ κ with hσκ | hκσ
    · have heq : κ * σ = κ :=
        mul_eq_left hκinf hσκ (aleph0_pos.trans_le hσ).ne'
      rw [heq] at hmul
      exact hmul.trans_lt hκμ
    · have heq : κ * σ = σ := by
        rw [mul_comm]
        exact mul_eq_left hσ hκσ (aleph0_pos.trans_le hκinf).ne'
      rw [heq] at hmul
      exact hmul.trans_lt hσlt
  obtain ⟨seq, hseqτ, hseqκ⟩ :=
    P.exists_approximationSequence hμ base p hνμ σ τ κ hσ hσlt hidx hτ hτμ hκinf hκμ
      hprodκ hclosed
  refine ⟨seq, ?_, ?_, ?_⟩
  · rw [hseqτ]; exact le_max_left _ _
  · rw [hseqτ]; exact hτμ
  · rw [hseqτ, hseqκ, add_eq_left hτ hτ]
    exact (le_max_left _ _).trans_lt (Order.lt_succ ρ)

/-- **(b) Base monotonicity of tied freeness (proved).** At a recursion-closed level, if `q`
over `B` is tied free along `X → A → B` from its restriction to `X`, then it is tied free along
`A → B` from its restriction to `A`.

English: the free evaluation does not depend on the approximation sequence (Theorem 6.10).
Given any sequence `a` for `q ↾ A` with a move `Z ↦ Z₀`, take a Lemma 6.9 sequence `x` for
`q ↾ X`; by (c) its image `g(x)` is an approximation sequence for `q ↾ A`. A common move
`Z₁` of `Z` over `a` and `g(x)` (saturation) compares both majorities with `q ↾ A` on `Z₁`,
and the hypothesis (applied to `x` and a move of `Z` along `g ≫ f`) identifies the `g(x)`
majority with `q` on `Z`. -/
theorem infra_78_tiedFree_base_mono
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {X A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := X) (Y := A) g)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hνμ : q.ν = μ) (hidx : #q.idx ≤ σ)
    (h : IsTiedFree (SystemArrow.comp g f)
      (q.restrict (SystemArrow.comp g f) (P.scheme.comp g f hg hf)) q (Equiv.refl _)) :
    IsTiedFree f (q.restrict f hf) q (Equiv.refl _) := by
  classical
  have hc := infra_78_tiedFree_restrict g hg f hf q h
  intro seq ι Z Z0 hκ hι hιμ hmove
  obtain ⟨sX, hτlo, hτμ, hκX⟩ :=
    infra_78_exists_seq_ge P σ hσ hμ hrec hσSucc ((q.restrict f hf).restrict g hg) hνμ hidx
      hιμ
  -- `g(x)` is an approximation sequence for `q ↾ A`.
  let b : ApproximationSequence (q.restrict f hf) :=
    { τ := sX.τ
      κIndex := sX.κIndex
      family := fun j k => pushOcc g (sX.family j k)
      concat_bounded := sX.concat_bounded
      few_exceptions := fun {β} W hW => by
        obtain ⟨W0, hW0⟩ := infra_610_move_query g hg sX W hW (hW.trans_lt hτμ)
        have ht := hc sX W W0 hκX hW (hW.trans_lt hτμ) hW0
        refine le_trans ?_ (sX.few_exceptions W0 hW)
        refine Cardinal.mk_le_of_injective (f := fun j => ⟨j.1, fun hgood => j.2 ?_⟩)
          (by
            intro j₁ j₂ hj
            apply Subtype.ext
            have := congrArg Subtype.val hj
            exact this)
        have e1 := P.scheme.diagram_symm _ _ _ _ ht
        have e2 := P.scheme.diagram_trans _ _ _ _ _ _ e1 hgood
        have e3 := P.scheme.diagram_trans _ _ _ _ _ _ e2 (hW0 j.1)
        erw [infra_78_anchored_refl (q.restrict f hf) W] at e3
        exact e3 }
  have hιX : #ι ≤ sX.τ := hτlo
  obtain ⟨Z1, hZ1a, hZ1b⟩ := infra_78_common_move_mixed f hf le_rfl seq b Z hιμ
  obtain ⟨Z0', hZ0'⟩ :=
    infra_610_move_query (SystemArrow.comp g f) (P.scheme.comp g f hg hf) sX Z hιX hιμ
  have hq := h sX Z Z0' hκX hιX hιμ hZ0'
  have hcι : ℵ₀ ≤ #ι + ℵ₀ := le_add_self
  -- Compare `q ↾ A` on `Z₀` and on `Z₁` through `seq`.
  obtain ⟨i, hi1, hi2⟩ := infra_78_exists_outside_two
    {i | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q.restrict f hf) Z0) (seqJoint (seq.family i) Z0)}
    {i | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q.restrict f hf) Z1) (seqJoint (seq.family i) Z1)}
    hcι (seq.few_exceptions Z0 hι) (seq.few_exceptions Z1 hι)
    ((add_le_add hι le_rfl).trans_lt hκ)
  simp only [Set.mem_ofPred_eq, not_not] at hi1 hi2
  have E1 : P.scheme.DiagramEq (X := q.host) (Y := q.host)
      (typeJoint (p := q.restrict f hf) Z0) (typeJoint (p := q.restrict f hf) Z1) := by
    have a1 := P.scheme.diagram_trans _ _ _ _ _ _ hi1 (hmove i)
    have a2 := P.scheme.diagram_trans _ _ _ _ _ _ a1 (P.scheme.diagram_symm _ _ _ _ (hZ1a i))
    exact P.scheme.diagram_trans _ _ _ _ _ _ a2 (P.scheme.diagram_symm _ _ _ _ hi2)
  -- Compare `q ↾ A` on `Z₁` with `q` on `Z` through `g(x)` and `x`.
  obtain ⟨j, hj1, hj2⟩ := infra_78_exists_outside_two
    {j | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q.restrict f hf) Z1) (seqJoint (b.family j) Z1)}
    {j | ¬ P.scheme.DiagramEq (X := q.host) (Y := X)
      (typeJoint (p := (q.restrict f hf).restrict g hg) Z0') (seqJoint (sX.family j) Z0')}
    hcι (b.few_exceptions Z1 hιX) (sX.few_exceptions Z0' hιX)
    ((add_le_add hιX le_rfl).trans_lt hκX)
  simp only [Set.mem_ofPred_eq, not_not] at hj1 hj2
  have E2 : P.scheme.DiagramEq (X := q.host) (Y := q.host)
      (typeJoint (p := q.restrict f hf) Z1)
      (infra_612_anchored (Equiv.refl q.idx) q.incl q.val Z) := by
    have b1 := P.scheme.diagram_trans _ _ _ _ _ _ hj1 (hZ1b j)
    have b2 := P.scheme.diagram_trans _ _ _ _ _ _ b1 (P.scheme.diagram_symm _ _ _ _ (hZ0' j))
    have b3 := P.scheme.diagram_trans _ _ _ _ _ _ b2 (P.scheme.diagram_symm _ _ _ _ hj2)
    exact P.scheme.diagram_trans _ _ _ _ _ _ b3 hq
  exact P.scheme.diagram_trans _ _ _ _ _ _ E1 E2

/-- Tied freeness for queries of size at most `τ₀` (the bounded-arity form of `IsTiedFree`). -/
def IsTiedFreeUpTo
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx) (τ₀ : Cardinal.{u}) : Prop :=
  ∀ (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
    seq.τ + ℵ₀ < #(seq.κIndex) →
    #ι ≤ seq.τ → #ι < μ → #ι ≤ τ₀ →
    infra_73_isMove f seq Z Z0 →
    P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (typeJoint (p := q) Z0)
      (infra_612_anchored eB qB.incl qB.val Z)

theorem IsTiedFree.upTo
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    {f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)}
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    {qB : TupleOver K oneVertexShape P.scheme hμ B}
    {eB : q.idx ≃ qB.idx} (h : IsTiedFree f q qB eB) (τ₀ : Cardinal.{u}) :
    IsTiedFreeUpTo f q qB eB τ₀ :=
  fun seq _ Z Z0 hκ hι hιμ _ hmove => h seq Z Z0 hκ hι hιμ hmove

/-- A Lemma 6.9 sequence over the union of a chain, at query size `τ₀`, with a regular
length placed on one side of `cf(δ)` (the hypotheses of `infra_613_trap_in_stage`). -/
theorem infra_78_exists_trappable_seq
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    (C : SameLevelChain P hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ C.unionObj)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ)
    {τ₀ : Cardinal.{u}} (hτ₀ : ℵ₀ ≤ τ₀) (hτ₀μ : τ₀ < μ) :
    ∃ seq : ApproximationSequence p, seq.τ = τ₀ ∧
      #seq.κIndex * #p.idx < μ ∧ seq.τ + aleph0 < #seq.κIndex ∧
      #seq.κIndex < μ ∧ (#seq.κIndex).IsRegular ∧
      (#seq.κIndex < C.δ.cof ∨ C.δ.cof < #seq.κIndex) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #p.idx < μ := hidx.trans_lt hσlt
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) aleph0)
      (max (max σ τ₀) (max (ls K) aleph0)) μ := by
    apply hrec.2
    exact max_lt (max_lt hσlt hτ₀μ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
  have hκex : ∃ κ : Cardinal.{u}, aleph0 ≤ κ ∧ κ < μ ∧ κ.IsRegular ∧
      κ * #p.idx < μ ∧ τ₀ + aleph0 < κ ∧ (κ < C.δ.cof ∨ C.δ.cof < κ) := by
    let ρ : Cardinal.{u} := if C.δ.cof < μ then max τ₀ (max #p.idx C.δ.cof)
      else max τ₀ #p.idx
    have hρinf : aleph0 ≤ ρ := by
      simp only [ρ]; split_ifs <;> exact hτ₀.trans (le_max_left _ _)
    have hρμ : ρ < μ := by
      simp only [ρ]; split_ifs with h
      · exact max_lt hτ₀μ (max_lt hidxμ h)
      · exact max_lt hτ₀μ hidxμ
    have hτρ : τ₀ ≤ ρ := by simp only [ρ]; split_ifs <;> exact le_max_left _ _
    let κ : Cardinal.{u} := Order.succ ρ
    have hκinf : aleph0 ≤ κ := hρinf.trans (Order.le_succ _)
    have hκμ : κ < μ :=
      (Order.succ_le_of_lt (cantor ρ)).trans_lt
        (hμ.1.working.strongLimit.isStrongPrelimit hρμ)
    have hprodκ : κ * #p.idx < μ := by
      have hmul : κ * #p.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
      rcases le_total σ κ with hσκ | hκσ
      · have heq : κ * σ = κ :=
          mul_eq_left hκinf hσκ (aleph0_pos.trans_le hσ).ne'
        rw [heq] at hmul
        exact hmul.trans_lt hκμ
      · have heq : κ * σ = σ := by
          rw [mul_comm]
          exact mul_eq_left hσ hκσ (aleph0_pos.trans_le hκinf).ne'
        rw [heq] at hmul
        exact hmul.trans_lt hσlt
    have hlenκ : τ₀ + aleph0 < κ := by
      rw [add_eq_left hτ₀ hτ₀]
      exact hτρ.trans_lt (Order.lt_succ ρ)
    have hside : κ < C.δ.cof ∨ C.δ.cof < κ := by
      by_cases hcf : C.δ.cof < μ
      · right
        have : C.δ.cof ≤ ρ := by
          simp only [ρ, hcf, ↓reduceIte]
          exact (le_max_right #p.idx C.δ.cof).trans (le_max_right τ₀ _)
        exact this.trans_lt (Order.lt_succ ρ)
      · left
        exact hκμ.trans_le (le_of_not_gt hcf)
    exact ⟨κ, hκinf, hκμ, isRegular_succ hρinf, hprodκ, hlenκ, hside⟩
  obtain ⟨κ, hκinf, hκμ, hregκ, hprodκ, hlenκ, hsideκ⟩ := hκex
  obtain ⟨seq, hseqτ, hseqκ⟩ :=
    P.exists_approximationSequence hμ C.unionObj p hνμ σ τ₀ κ hσ hσlt hidx hτ₀ hτ₀μ
      hκinf hκμ hprodκ hclosed
  refine ⟨seq, hseqτ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hseqκ]; exact hprodκ
  · rw [hseqτ, hseqκ]; exact hlenκ
  · rw [hseqκ]; exact hκμ
  · rw [hseqκ]; exact hregκ
  · rw [hseqκ]; exact hsideκ

/-- **(a) Tied local character at a bounded arity (proved).** At a recursion-closed level,
for a same-level chain `C` and a small tuple `p` over its union (`#p.idx < cf δ`), for every
query bound `ℵ₀ ≤ τ₀ < μ` some stage `A_i` has `p` tied free from `p ↾ A_i` on all queries of
size at most `τ₀`. A Lemma 6.9 code at arity `τ₀` is trapped in a stage
(`infra_613_trap_in_stage`); any approximation sequence of `p ↾ A_i` with a move is compared
with the trapped code through a common move, and the trapped code's majority over the union is
`p` itself. -/
theorem infra_78_tied_local_bounded
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    (C : SameLevelChain P hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ C.unionObj)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hcof : #p.idx < C.δ.cof)
    {τ₀ : Cardinal.{u}} (hτ₀ : ℵ₀ ≤ τ₀) (hτ₀μ : τ₀ < μ) :
    ∃ i : Ordinal.{u}, ∃ hi : i < C.δ,
      IsTiedFreeUpTo (C.toUnion i hi)
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) p (Equiv.refl _) τ₀ := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #p.idx < μ := hidx.trans_lt hσlt
  obtain ⟨seq, hseqτ, hprod, hlen, hκμ, hreg, hside⟩ :=
    infra_78_exists_trappable_seq P σ hσ hμ hrec hσSucc C p hνμ hidx hτ₀ hτ₀μ
  obtain ⟨i, hi, seq', emb, hτeq, hlen', _, hpush⟩ :=
    infra_613_trap_in_stage C p seq hcof hidxμ (hseqτ ▸ hτ₀μ) hprod hlen hκμ hreg hside
  refine ⟨i, hi, ?_⟩
  intro seqA ι Z Z0 hκA hιA hιμ hι0 hmove
  have hι' : #ι ≤ seq'.τ := by rw [hτeq, hseqτ]; exact hι0
  have hιs : #ι ≤ seq.τ := by rw [hseqτ]; exact hι0
  obtain ⟨Z1, hZ1a, hZ1b⟩ :=
    infra_78_common_move_mixed (C.toUnion i hi) (C.toUnion_arrow i hi) le_rfl seqA seq' Z hιμ
  have hcι : ℵ₀ ≤ #ι + ℵ₀ := le_add_self
  obtain ⟨a, ha1, ha2⟩ := infra_78_exists_outside_two
    {a | ¬ P.scheme.DiagramEq (X := p.host) (Y := C.obj i hi)
      (typeJoint (p := p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) Z0)
      (seqJoint (seqA.family a) Z0)}
    {a | ¬ P.scheme.DiagramEq (X := p.host) (Y := C.obj i hi)
      (typeJoint (p := p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) Z1)
      (seqJoint (seqA.family a) Z1)}
    hcι (seqA.few_exceptions Z0 hιA) (seqA.few_exceptions Z1 hιA)
    ((add_le_add hιA le_rfl).trans_lt hκA)
  simp only [Set.mem_ofPred_eq, not_not] at ha1 ha2
  have E1 := P.scheme.diagram_trans _ _ _ _ _ _
    (P.scheme.diagram_trans _ _ _ _ _ _
      (P.scheme.diagram_trans _ _ _ _ _ _ ha1 (hmove a))
      (P.scheme.diagram_symm _ _ _ _ (hZ1a a)))
    (P.scheme.diagram_symm _ _ _ _ ha2)
  have hexc : #{s : seq'.κIndex // ¬ P.scheme.DiagramEq (X := p.host) (Y := C.unionObj)
      (typeJoint (p := p) Z) (seqJoint (seq.family (emb s)) Z)} ≤ #ι + ℵ₀ := by
    refine le_trans ?_ (seq.few_exceptions Z hιs)
    refine Cardinal.mk_le_of_injective (f := fun s => ⟨emb s.1, s.2⟩) ?_
    intro s₁ s₂ hs
    apply Subtype.ext
    have := congrArg Subtype.val hs
    exact emb.injective this
  obtain ⟨s, hs1, hs2⟩ := infra_78_exists_outside_two
    {s | ¬ P.scheme.DiagramEq (X := p.host) (Y := C.obj i hi)
      (typeJoint (p := p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) Z1)
      (seqJoint (seq'.family s) Z1)}
    {s | ¬ P.scheme.DiagramEq (X := p.host) (Y := C.unionObj)
      (typeJoint (p := p) Z) (seqJoint (seq.family (emb s)) Z)}
    hcι (seq'.few_exceptions Z1 hι') hexc
    ((add_le_add (hιs) le_rfl).trans_lt hlen')
  simp only [Set.mem_ofPred_eq, not_not] at hs1 hs2
  have hfam : (fun j => (⟨(seq'.family s j).1,
      (C.toUnion i hi).onVertex (seq'.family s j).1 (seq'.family s j).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ C.unionObj))) =
      seq.family (emb s) := funext fun j => hpush s j
  have hmv := hZ1b s
  rw [hfam] at hmv
  have E2 := P.scheme.diagram_trans _ _ _ _ _ _
    (P.scheme.diagram_trans _ _ _ _ _ _ hs1 hmv) (P.scheme.diagram_symm _ _ _ _ hs2)
  have E := P.scheme.diagram_trans _ _ _ _ _ _ E1 E2
  erw [infra_78_anchored_refl p Z]
  exact E

set_option maxHeartbeats 1600000 in
/-- **Testing reduction (`infra_78_tied_testing_reduction`).** At a recursion-closed level, a
small tuple `q` over `B` that is tied-free from `A` on every query up to the testing arity
`g(σ) + LS(K)` is tied-free on every bounded query (English Theorem 6.10: the free lift is
computed at every bounded query size, and Theorem 6.6 testing identifies it).

Proof: let `qB` be the tied free lift of `q ↾ A` (`infra_610_tied_free_lift`). On every test of
size `≤ g(σ) + LS(K)` the tied moves (`infra_73_tied_move`) give both `q` and `qB` the type of
`q ↾ A`, so Theorem 6.6 (`infra_73_differing_test`) makes them one Galois type over `B`; the
answer of `qB` on any larger query is carried to `q` (`infra_72_diagramEq_of_sameGalois`). -/
theorem infra_78_tiedFree_of_upTo
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ)
    (hup : IsTiedFreeUpTo f (q.restrict f hf) q (Equiv.refl _) (P.g σ + ls K)) :
    IsTiedFree f (q.restrict f hf) q (Equiv.refl _) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hidxμ : #q.idx < μ := hidx.trans_lt hσlt
  obtain ⟨qB, eB, hBν, -, hTB⟩ :=
    infra_610_tied_free_lift P σ hσ hμ hrec hσμ f hf (q.restrict f hf) hqν hidx
  have hidxB : #qB.idx ≤ σ := by rw [← Cardinal.mk_congr eB]; exact hidx
  have hS : SameGaloisType qB q eB.symm (Equiv.refl q.idx).symm := by
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ :=
      infra_73_differing_test P σ hσ hμ hrec hσμ qB q eB.symm (Equiv.refl q.idx).symm hBν hqν
        hidxB (hidxB.trans_lt hσlt) hneq
    apply hnot
    obtain ⟨seq, Y0, hlong, hβτ, hβμ, hmv⟩ :=
      infra_73_tied_move P σ hσ hμ hrec hσμ f hf (q.restrict f hf) hqν hidx Y hβ
    have d1 := hTB seq Y Y0 hlong hβτ hβμ hmv
    have d2 := hup seq Y Y0 hlong hβτ hβμ hβ hmv
    have d := P.scheme.diagram_trans qB.host q.host q.host _ _ _
      (P.scheme.diagram_symm q.host qB.host _ _ d1) d2
    exact infra_73_diagramEq_of_eq d (fun t => by cases t <;> rfl)
      (fun t => by cases t <;> rfl)
  intro seq' ι Z Z0' hlong' hι' hιμ hmv
  have dL := hTB seq' Z Z0' hlong' hι' hιμ hmv
  have dS := infra_72_diagramEq_of_sameGalois (P := P) hS Z hBν hqν hidxμ hιμ
  have dS' : P.scheme.DiagramEq (X := qB.host) (Y := q.host)
      (infra_612_anchored eB qB.incl qB.val Z)
      (infra_612_anchored (Equiv.refl q.idx) q.incl q.val Z) :=
    infra_73_diagramEq_of_eq dS (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  exact P.scheme.diagram_trans q.host qB.host q.host _ _ _ dL dS'

/-- **Tied local character (part (a) of `infra_78_tied_local_character`, English Prop 6.13
first clause in the tied form).** At a recursion-closed level, a small tuple over the union of
a same-level chain with `|v| < cf δ` is tied-free from some stage, on every bounded query.
The bounded form at the testing arity (`infra_78_tied_local_bounded`) plus the testing
reduction (`infra_78_tiedFree_of_upTo`). -/
theorem infra_78_tied_local
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    (C : SameLevelChain P hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ C.unionObj)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hcof : #p.idx < C.δ.cof) :
    ∃ i : Ordinal.{u}, ∃ hi : i < C.δ,
      IsTiedFree (C.toUnion i hi)
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) p (Equiv.refl _) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hg : P.g σ < μ :=
    (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
  have hτ₀μ : P.g σ + ls K < μ := add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ)
  have hτ₀ : ℵ₀ ≤ P.g σ + ls K := (isLSBound_ls K).1.trans le_add_self
  obtain ⟨i, hi, hup⟩ :=
    infra_78_tied_local_bounded P σ hσ hμ hrec hσSucc C p hνμ hidx hcof hτ₀ hτ₀μ
  exact ⟨i, hi, infra_78_tiedFree_of_upTo P σ hσ hμ hrec hσSucc (C.toUnion i hi)
    (C.toUnion_arrow i hi) p hνμ hidx hup⟩

end
end AEC
