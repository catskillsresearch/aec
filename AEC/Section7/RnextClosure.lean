module

public import AEC.Section7.MatrixOperators
public import AEC.Section7.Bookkeeping

@[expose] public section

/-!
# The concrete bookkeeping update `Rnext` of the Prop 7.8 recursion (grokbot cycle 53)

`infra_78_rnext_closure`. The paper (Prop 7.8 proof): at successor stages close the bookkeeping
set under the closure requirements, and "if new elements are added later, repeat these successor
closures". Requirement 2 at stage `k` concerns types over `X_k`, so the closure is taken with
respect to the *new* pair `X_k → Y_k` (this is why `Rnext` sees the new stage's pair).

* `infra_78_PairClosed`: the pair-local closure properties of `infra_78_pair_bookkeeping_close`.
* `infra_78_closeR`: a chosen closed superset (via `infra_78_pair_bookkeeping_close`);
  `infra_78_rcl`: the update `Rnext s X' Y' p' st = closeR (image of R_s along st)`.
* `infra_78_seedStage`: the seed stage with `R_0 = closeR (seeds)`; it is closed
  (`infra_78_seedStage_closed`), and `S_0 ≠ ∅` once a seed lies on the `Y`-side
  (`infra_78_seedStage_S_nonempty`).
* Matrix properties (`infra_78_rcObj`, `infra_78_rcMap`): sizes `≤ ρ` (`infra_78_rc_card`),
  forward closure (`infra_78_rc_forward`), continuity (`infra_78_rc_limit`), pair closure
  (`infra_78_rc_pair`), `S_k ≠ ∅` at every stage (`infra_78_rc_S_nonempty`), supply at
  non-limit stages (`infra_78_rc_supply`).
* `infra_78_rnext_closure`: all bookkeeping outputs in the `infra_78_bkStep` form, including
  closure requirements 1 and 2 at non-limit stages and stages of cofinality `> λ` (via
  `infra_78_bookkeeping_req1_high_cof` / `_req2_high_cof`). Its only non-construction hypothesis
  is invariant (5) at every stage, tracked as `infra_78_recursion_outputs`.
-/

universe u
open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}

section CloseR
variable {P : SingleModelData K} {κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

/-- The pair-local closure properties (size, pair closure, requirement 1, requirement 2) of a
bookkeeping set `T'` for the pair `f : X → Y` (the conclusion of
`infra_78_pair_bookkeeping_close`). -/
def infra_78_PairClosed (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    {X Y : P.scheme.Object κ hκ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (T' : Set (X.model.carrier ⊕ Y.model.carrier)) : Prop :=
  #T' ≤ ρ ∧
  (∀ x, (Sum.inl x : X.model.carrier ⊕ Y.model.carrier) ∈ T' →
    (Sum.inr (f.onVertex PUnit.unit x) : X.model.carrier ⊕ Y.model.carrier) ∈ T') ∧
  (∀ s ⊆ T', #s ≤ ℓ →
    ∃ (A V : P.scheme.Object ℓ hℓel)
      (iA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hκ X))
      (iV : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel V) (P.scheme.asSystem hκ Y))
      (g : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A)
        (P.scheme.asSystem hℓel V)),
      P.scheme.permitted (X := A) (Y := X) iA ∧
      P.scheme.permitted (X := V) (Y := Y) iV ∧
      P.scheme.permitted (X := A) (Y := V) g ∧
      (∀ v, (iV.onVertex v).comp (g.onVertex v) = (f.onVertex v).comp (iA.onVertex v)) ∧
      Sum.inl ⁻¹' s ⊆ Set.range (iA.onVertex PUnit.unit) ∧
      Sum.inr ⁻¹' s ⊆ Set.range (iV.onVertex PUnit.unit) ∧
      Sum.inl '' Set.range (iA.onVertex PUnit.unit) ⊆ T' ∧
      Sum.inr '' Set.range (iV.onVertex PUnit.unit) ⊆ T') ∧
  (∀ σ : Cardinal.{u}, ℵ₀ ≤ σ → κ ∈ recursionClosedLevels P σ → Order.succ σ ≤ κ → ℓ < κ →
    ∀ s ⊆ T', #s ≤ ℓ → #(Sum.inr ⁻¹' s : Set Y.model.carrier) ≤ σ →
    ∃ seq : ApproximationSequence (infra_78_pairTuple f hf s), seq.τ = ℓ ∧
      ℓ + ℵ₀ < #seq.κIndex ∧
      ∀ a b, (Sum.inl (X.val (seq.family a b)) : X.model.carrier ⊕ Y.model.carrier) ∈ T')

open Classical in
/-- **Closure of a bookkeeping set for the pair `p : X → Y`**: a chosen closed superset of `T`
(`infra_78_pair_bookkeeping_close`), or `T` itself if none exists. -/
noncomputable def infra_78_closeR (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (X Y : P.scheme.Object κ hκ) (p : κ.ord.ToType → κ.ord.ToType)
    (T : Set (κ.ord.ToType ⊕ κ.ord.ToType)) : Set (κ.ord.ToType ⊕ κ.ord.ToType) :=
  if h : ∃ hp : infra_78_IsArr X Y p, ∃ T' : Set (X.model.carrier ⊕ Y.model.carrier),
      T ⊆ T' ∧ infra_78_PairClosed ρ hℓel (infra_78_toArr hp) trivial T' then
    Classical.choose (Classical.choose_spec h)
  else T

theorem infra_78_closeR_card (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (X Y : P.scheme.Object κ hκ) (p : κ.ord.ToType → κ.ord.ToType)
    {T : Set (κ.ord.ToType ⊕ κ.ord.ToType)} (hT : #T ≤ ρ) :
    #(infra_78_closeR ρ hℓel X Y p T) ≤ ρ := by
  unfold infra_78_closeR
  split_ifs with h
  · exact (Classical.choose_spec (Classical.choose_spec h)).2.1
  · exact hT

theorem infra_78_closeR_subset (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (X Y : P.scheme.Object κ hκ) (p : κ.ord.ToType → κ.ord.ToType)
    (T : Set (κ.ord.ToType ⊕ κ.ord.ToType)) : T ⊆ infra_78_closeR ρ hℓel X Y p T := by
  unfold infra_78_closeR
  split_ifs with h
  · exact (Classical.choose_spec (Classical.choose_spec h)).1
  · exact le_rfl

/-- **The closure is closed** for the pair, whenever `|T| ≤ ρ`, `λ ≤ κ`, `λ < ρ`, `ρ^λ = ρ`. -/
theorem infra_78_closeR_spec {ρ ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (hℓκ : ℓ ≤ κ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    {X Y : P.scheme.Object κ hκ} {p : κ.ord.ToType → κ.ord.ToType} (hp : infra_78_IsArr X Y p)
    {T : Set (κ.ord.ToType ⊕ κ.ord.ToType)} (hT : #T ≤ ρ) :
    infra_78_PairClosed ρ hℓel (infra_78_toArr hp) trivial (infra_78_closeR ρ hℓel X Y p T) := by
  have hex : ∃ hp : infra_78_IsArr X Y p, ∃ T' : Set (X.model.carrier ⊕ Y.model.carrier),
      T ⊆ T' ∧ infra_78_PairClosed ρ hℓel (infra_78_toArr hp) trivial T' :=
    ⟨hp, infra_78_pair_bookkeeping_close (infra_78_toArr hp) trivial hℓel hℓκ hℓρ hpow T hT⟩
  unfold infra_78_closeR
  rw [dif_pos hex]
  exact (Classical.choose_spec (Classical.choose_spec hex)).2

variable {uIdx : Type u}

/-- **The concrete bookkeeping update** (`Rnext`): the image of the old set along the step,
closed for the new pair `p' : X' → Y'` ("repeat these successor closures"). -/
noncomputable def infra_78_rcl (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (s : Infra78Stage P hκ (Infra78MarkData κ uIdx)) (X' Y' : P.scheme.Object κ hκ)
    (p' : κ.ord.ToType → κ.ord.ToType) (st : Infra78Step κ) :
    Set (κ.ord.ToType ⊕ κ.ord.ToType) :=
  infra_78_closeR ρ hℓel X' Y' p' (Sum.map st.1 st.2 '' s.e.R)

/-- **The seed stage**: pair `p0 : X0 → Y0`, base `g0`, mark `b0`, and bookkeeping set the
closure of the seeds (e.g. `I_p`, the coordinates of `b`). -/
noncomputable def infra_78_seedStage (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (X0 Y0 : P.scheme.Object κ hκ) (p0 : κ.ord.ToType → κ.ord.ToType)
    (hp0 : infra_78_IsArr X0 Y0 p0) (g0 : κ.ord.ToType → κ.ord.ToType)
    (b0 : uIdx → κ.ord.ToType) (seeds : Set (κ.ord.ToType ⊕ κ.ord.ToType)) :
    Infra78Stage P hκ (Infra78MarkData κ uIdx) :=
  ⟨X0, Y0, p0, hp0, ⟨g0, b0, infra_78_closeR ρ hℓel X0 Y0 p0 seeds⟩⟩

end CloseR

section RclMatrix
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible} {uIdx cIdx L : Type u}
variable (hρκ : Order.succ ρ < κ) (Xb : P.scheme.Object κ hκ) {ℓ : Cardinal.{u}}
  (hℓel : ℓ ∈ P.eligible)
  (cand : (Order.succ ρ).ord.ToType → Infra78Stage P hκ (Infra78MarkData κ uIdx) →
    L → cIdx → κ.ord.ToType)
  (s0 : Infra78Stage P hκ (Infra78MarkData κ uIdx)) (e0 : Infra78MarkData κ uIdx)

/-- Stage `k` of the recursion matrix with the concrete update `infra_78_rcl`. -/
noncomputable abbrev infra_78_rcObj (k : (Order.succ ρ).ord.ToType) :
    Infra78Stage P hκ (Infra78MarkData κ uIdx) :=
  infra_78_pcObj s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand) (infra_78_limMarkE e0) k

/-- Plain step `i → k` of the recursion matrix with the concrete update. -/
noncomputable abbrev infra_78_rcMap (i k : (Order.succ ρ).ord.ToType) : Infra78Step κ :=
  infra_78_pcMap s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand) (infra_78_limMarkE e0) i k

include hρκ in
/-- Successor stages: the set is the closure (for the new pair) of the image of the previous set,
or (identity fallback) the stage and set are unchanged. -/
theorem infra_78_rc_succ_cases {β k : (Order.succ ρ).ord.ToType} (hβ : β ⋖ k) :
    (infra_78_rcObj Xb hℓel cand s0 e0 k).e.R =
      infra_78_closeR ρ hℓel (infra_78_rcObj Xb hℓel cand s0 e0 k).X
        (infra_78_rcObj Xb hℓel cand s0 e0 k).Y (infra_78_rcObj Xb hℓel cand s0 e0 k).p
        (Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 β k).1 (infra_78_rcMap Xb hℓel cand s0 e0 β k).2 ''
          (infra_78_rcObj Xb hℓel cand s0 e0 β).e.R) ∨
    (infra_78_rcObj Xb hℓel cand s0 e0 k = infra_78_rcObj Xb hℓel cand s0 e0 β ∧
      infra_78_rcMap Xb hℓel cand s0 e0 β k = infra_78_stepId) := by
  obtain ⟨hck, hmk⟩ := infra_78_pairMatrix_succ hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) (infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand) hβ
  have hck' : infra_78_rcObj Xb hℓel cand s0 e0 k =
      (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand β (infra_78_rcObj Xb hℓel cand s0 e0 β)).1 := hck
  have hmk' : infra_78_rcMap Xb hℓel cand s0 e0 β k =
      (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand β (infra_78_rcObj Xb hℓel cand s0 e0 β)).2 := hmk
  rw [hck', hmk']
  by_cases h : ∃ out, infra_78_SuccSpec Xb (infra_78_rcl ρ hℓel)
      (cand β (infra_78_rcObj Xb hℓel cand s0 e0 β)) (infra_78_rcObj Xb hℓel cand s0 e0 β) out
  · obtain ⟨-, -, -, -, -, hR, -⟩ := infra_78_succOp_spec Xb (infra_78_rcl ρ hℓel) cand β _ h
    exact Or.inl hR
  · refine Or.inr ?_
    unfold infra_78_succOp
    rw [dif_neg h]
    exact ⟨rfl, rfl⟩

include hρκ in
/-- Limit stages: the set is the union of the images of the earlier sets along the legs. -/
theorem infra_78_rc_limit {k : (Order.succ ρ).ord.ToType} (hk : Order.IsSuccLimit k) :
    (infra_78_rcObj Xb hℓel cand s0 e0 k).e.R =
      ⋃ j : Set.Iio k, Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 j.1 k).1
        (infra_78_rcMap Xb hℓel cand s0 e0 j.1 k).2 '' (infra_78_rcObj Xb hℓel cand s0 e0 j.1).e.R := by
  have hL := (infra_78_pairMatrix_limit hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) (infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand) hk).2.2.1
  have hne : Nonempty (Set.Iio k) := by
    obtain ⟨b, hb⟩ := not_isMin_iff.1 hk.not_isMin
    exact ⟨⟨b, hb⟩⟩
  simp only [infra_78_limMarkE, dif_pos hne] at hL
  exact congrArg Infra78MarkData.R hL

/-- Case split for stages of a well order: least, successor, or limit. -/
theorem infra_78_stage_trichotomy (k : (Order.succ ρ).ord.ToType) :
    IsMin k ∨ (∃ β, β ⋖ k) ∨ Order.IsSuccLimit k := by
  by_cases hmin : IsMin k
  · exact Or.inl hmin
  by_cases hs : ∃ β, β ⋖ k
  · exact Or.inr (Or.inl hs)
  exact Or.inr (Or.inr ⟨hmin, fun b hb => hs ⟨b, hb⟩⟩)

theorem infra_78_Iio_card_le (k : (Order.succ ρ).ord.ToType) : #(Set.Iio k) ≤ ρ := by
  have h := Cardinal.mk_Iio_lt k (by rw [mk_ord_toType, Ordinal.type_toType])
  rw [mk_ord_toType] at h
  exact Order.lt_succ_iff.1 h

include hρκ in
/-- **Size**: every bookkeeping set has size `≤ ρ` if the seed set does. -/
theorem infra_78_rc_card (hρ : ℵ₀ ≤ ρ) (h0 : #s0.e.R ≤ ρ) (k : (Order.succ ρ).ord.ToType) :
    #(infra_78_rcObj Xb hℓel cand s0 e0 k).e.R ≤ ρ := by
  induction k using WellFoundedLT.induction with
  | _ k IH =>
  rcases infra_78_stage_trichotomy k with hmin | ⟨β, hβ⟩ | hk
  · have h : infra_78_rcObj Xb hℓel cand s0 e0 k = s0 := infra_78_pairMatrix_min s0 _ _ hmin
    rw [h]; exact h0
  · rcases infra_78_rc_succ_cases hρκ Xb hℓel cand s0 e0 hβ with hR | ⟨hc, -⟩
    · rw [hR]
      exact infra_78_closeR_card ρ hℓel _ _ _ (Cardinal.mk_image_le.trans (IH β hβ.lt))
    · rw [hc]; exact IH β hβ.lt
  · rw [infra_78_rc_limit hρκ Xb hℓel cand s0 e0 hk]
    have hU := mk_iUnion_le (fun j : Set.Iio k =>
      Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 j.1 k).1 (infra_78_rcMap Xb hℓel cand s0 e0 j.1 k).2 ''
        (infra_78_rcObj Xb hℓel cand s0 e0 j.1).e.R)
    have hS : (⨆ j : Set.Iio k, #(Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 j.1 k).1
        (infra_78_rcMap Xb hℓel cand s0 e0 j.1 k).2 ''
        (infra_78_rcObj Xb hℓel cand s0 e0 j.1).e.R)) ≤ ρ :=
      ciSup_le' fun j => Cardinal.mk_image_le.trans (IH j.1 j.2)
    exact hU.trans ((mul_le_mul' (infra_78_Iio_card_le k) hS).trans (mul_eq_self hρ).le)

include hρκ in
/-- **Forward closure**: the image of the set at stage `i` lies in the set at stage `k ≥ i`. -/
theorem infra_78_rc_forward (i k : (Order.succ ρ).ord.ToType) (hik : i ≤ k) :
    Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 i k).1 (infra_78_rcMap Xb hℓel cand s0 e0 i k).2 ''
      (infra_78_rcObj Xb hℓel cand s0 e0 i).e.R ⊆ (infra_78_rcObj Xb hℓel cand s0 e0 k).e.R := by
  have hsop := infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand
  obtain ⟨-, hI, hC⟩ := infra_78_pairChain_laws hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) hsop
  induction k using WellFoundedLT.induction generalizing i with
  | _ k IH =>
  rcases hik.lt_or_eq with hik | rfl
  swap
  · have h := hI i
    change infra_78_rcMap Xb hℓel cand s0 e0 i i = infra_78_stepId at h
    rw [h]
    show Sum.map id id '' _ ⊆ _
    rw [Sum.map_id_id, Set.image_id]
  rcases infra_78_stage_trichotomy k with hmin | ⟨β, hβ⟩ | hk
  · exact absurd hik (not_lt.2 (hmin hik.le))
  · have hiβ : i ≤ β := hβ.le_of_lt hik
    have hcomp := hC i β k hiβ hβ.le
    change infra_78_rcMap Xb hℓel cand s0 e0 i k = infra_78_stepComp
      (infra_78_rcMap Xb hℓel cand s0 e0 i β) (infra_78_rcMap Xb hℓel cand s0 e0 β k) at hcomp
    rw [hcomp]
    show Sum.map ((infra_78_rcMap Xb hℓel cand s0 e0 β k).1 ∘ (infra_78_rcMap Xb hℓel cand s0 e0 i β).1)
      ((infra_78_rcMap Xb hℓel cand s0 e0 β k).2 ∘ (infra_78_rcMap Xb hℓel cand s0 e0 i β).2) '' _ ⊆ _
    rw [← Sum.map_comp_map, Set.image_comp]
    refine (Set.image_mono (IH β hβ.lt i hiβ)).trans ?_
    rcases infra_78_rc_succ_cases hρκ Xb hℓel cand s0 e0 hβ with hR | ⟨hc, hm⟩
    · rw [hR]; exact infra_78_closeR_subset ρ hℓel _ _ _ _
    · rw [hm, hc]
      show Sum.map id id '' _ ⊆ _
      rw [Sum.map_id_id, Set.image_id]
  · rw [infra_78_rc_limit hρκ Xb hℓel cand s0 e0 hk]
    exact Set.subset_iUnion_of_subset (⟨i, hik⟩ : Set.Iio k) le_rfl

include hρκ in
/-- **Pair closure at every stage**: `x ∈ R_k` on the `X`-side gives `p_k x ∈ R_k`. -/
theorem infra_78_rc_pair (hℓκ : ℓ ≤ κ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ) (hρ : ℵ₀ ≤ ρ)
    (h0 : #s0.e.R ≤ ρ) (h0p : ∀ x, (Sum.inl x : κ.ord.ToType ⊕ κ.ord.ToType) ∈ s0.e.R →
      (Sum.inr (s0.p x) : κ.ord.ToType ⊕ κ.ord.ToType) ∈ s0.e.R)
    (k : (Order.succ ρ).ord.ToType) (x : κ.ord.ToType)
    (hx : (Sum.inl x : κ.ord.ToType ⊕ κ.ord.ToType) ∈ (infra_78_rcObj Xb hℓel cand s0 e0 k).e.R) :
    (Sum.inr ((infra_78_rcObj Xb hℓel cand s0 e0 k).p x) : κ.ord.ToType ⊕ κ.ord.ToType) ∈
      (infra_78_rcObj Xb hℓel cand s0 e0 k).e.R := by
  have hsop := infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand
  obtain ⟨hA, -, -⟩ := infra_78_pairChain_laws hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) hsop
  induction k using WellFoundedLT.induction generalizing x with
  | _ k IH =>
  rcases infra_78_stage_trichotomy k with hmin | ⟨β, hβ⟩ | hk
  · have h : infra_78_rcObj Xb hℓel cand s0 e0 k = s0 := infra_78_pairMatrix_min s0 _ _ hmin
    rw [h] at hx ⊢; exact h0p x hx
  · rcases infra_78_rc_succ_cases hρκ Xb hℓel cand s0 e0 hβ with hR | ⟨hc, -⟩
    · have hT : #(Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 β k).1
          (infra_78_rcMap Xb hℓel cand s0 e0 β k).2 '' (infra_78_rcObj Xb hℓel cand s0 e0 β).e.R) ≤ ρ :=
        Cardinal.mk_image_le.trans (infra_78_rc_card hρκ Xb hℓel cand s0 e0 hρ h0 β)
      have hPC := infra_78_closeR_spec hℓel hℓκ hℓρ hpow
        (infra_78_rcObj Xb hℓel cand s0 e0 k).hp hT
      rw [← hR] at hPC
      have := hPC.2.1 x hx
      have e : ((infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 k).hp).onVertex PUnit.unit x :
          κ.ord.ToType) = (infra_78_rcObj Xb hℓel cand s0 e0 k).p x := infra_78_toArr_apply _ x
      exact e ▸ this
    · rw [hc] at hx ⊢; exact IH β hβ.lt x hx
  · rw [infra_78_rc_limit hρκ Xb hℓel cand s0 e0 hk] at hx ⊢
    obtain ⟨_, ⟨j, rfl⟩, z, hz, hzx⟩ := hx
    rcases z with x' | y'
    · have hxx : (infra_78_rcMap Xb hℓel cand s0 e0 j.1 k).1 x' = x := Sum.inl_injective hzx
      have hsq := congrFun (hA j.1 k j.2.le).2.2 x'
      refine Set.mem_iUnion.2 ⟨j, Sum.inr ((infra_78_rcObj Xb hℓel cand s0 e0 j.1).p x'),
        IH j.1 j.2 x' hz, ?_⟩
      show Sum.inr ((infra_78_rcMap Xb hℓel cand s0 e0 j.1 k).2
        ((infra_78_rcObj Xb hℓel cand s0 e0 j.1).p x')) = _
      rw [← hxx]
      exact congrArg Sum.inr hsq.symm
    · exact absurd hzx Sum.inr_ne_inl

include hρκ in
/-- **`S_k` nonempty at every stage** (the seeding obligation): if the seed set has a point on
the `Y`-side, so does every bookkeeping set (forward closure from the least stage). -/
theorem infra_78_rc_S_nonempty (h0 : ∃ y, (Sum.inr y : κ.ord.ToType ⊕ κ.ord.ToType) ∈ s0.e.R)
    (k : (Order.succ ρ).ord.ToType) :
    ∃ y, y ∈ infra_78_Spart (infra_78_rcObj Xb hℓel cand s0 e0 k) := by
  obtain ⟨i0, -, hi0⟩ := (wellFounded_lt (α := (Order.succ ρ).ord.ToType)).has_min Set.univ
    ⟨k, trivial⟩
  have hmin : IsMin i0 := fun b _ => not_lt.1 (hi0 b trivial)
  have hi0k : i0 ≤ k := not_lt.1 (hi0 k trivial)
  have h : infra_78_rcObj Xb hℓel cand s0 e0 i0 = s0 := infra_78_pairMatrix_min s0 _ _ hmin
  obtain ⟨y, hy⟩ := h0
  have hy' : (Sum.inr y : κ.ord.ToType ⊕ κ.ord.ToType) ∈
      (infra_78_rcObj Xb hℓel cand s0 e0 i0).e.R := by rw [h]; exact hy
  exact ⟨_, infra_78_rc_forward hρκ Xb hℓel cand s0 e0 i0 k hi0k ⟨_, hy', rfl⟩⟩

/-- The recursion matrix (as an `Infra78Matrix`) with the concrete update. -/
noncomputable abbrev infra_78_rcMatrix : Infra78Matrix P ρ hκ :=
  infra_78_pairMatrix hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand) (infra_78_limMarkE e0)
    (infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand)

/-- Its bookkeeping sets `R_i`, on the carriers of the matrix. -/
noncomputable abbrev infra_78_rcSets (i : (Order.succ ρ).ord.ToType) :
    Set (infra_78_bkCarrier (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) i) :=
  (infra_78_rcObj Xb hℓel cand s0 e0 i).e.R

theorem infra_78_rc_bkStep {j i : (Order.succ ρ).ord.ToType} (h : j < i)
    (z : infra_78_bkCarrier (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) j) :
    infra_78_bkStep (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) h z =
      Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 j i).1 (infra_78_rcMap Xb hℓel cand s0 e0 j i).2 z := by
  rcases z with x | y
  · exact congrArg Sum.inl (infra_78_pairMatrix_stepX_apply hρκ s0 _ _ _ h.le x)
  · exact congrArg Sum.inr (infra_78_pairMatrix_stepY_apply hρκ s0 _ _ _ h.le y)

theorem infra_78_rc_bkImage {j i : (Order.succ ρ).ord.ToType} (h : j < i) :
    infra_78_bkStep (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) h ''
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 j =
      Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 j i).1 (infra_78_rcMap Xb hℓel cand s0 e0 j i).2 ''
        (infra_78_rcObj Xb hℓel cand s0 e0 j).e.R :=
  Set.image_congr fun z _ => infra_78_rc_bkStep hρκ Xb hℓel cand s0 e0 h z

/-- Forward closure in the `infra_78_bkStep` form consumed by the bookkeeping lemmas. -/
theorem infra_78_rc_bkMono {j i : (Order.succ ρ).ord.ToType} (h : j < i) :
    infra_78_bkStep (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) h ''
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 j ⊆ infra_78_rcSets hρκ Xb hℓel cand s0 e0 i := by
  rw [infra_78_rc_bkImage]
  exact infra_78_rc_forward hρκ Xb hℓel cand s0 e0 j i h.le

/-- Continuity of the bookkeeping sets at limits, in `infra_78_bkStep` form. -/
theorem infra_78_rc_bkLim (i : (Order.succ ρ).ord.ToType) (hi : Order.IsSuccLimit i) :
    infra_78_rcSets hρκ Xb hℓel cand s0 e0 i =
      ⋃ j : Set.Iio i, infra_78_bkStep (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) j.2 ''
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 j.1 := by
  rw [infra_78_rcSets, infra_78_rc_limit hρκ Xb hℓel cand s0 e0 hi]
  exact Set.iUnion_congr fun j =>
    (infra_78_rc_bkImage hρκ Xb hℓel cand s0 e0 (j.2 : j.1 < i)).symm

end RclMatrix

section Seed
variable {P : SingleModelData K} {κ : Cardinal.{u}} {hκ : κ ∈ P.eligible} {uIdx : Type u}
  (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
  (X0 Y0 : P.scheme.Object κ hκ) (p0 : κ.ord.ToType → κ.ord.ToType)
  (hp0 : infra_78_IsArr X0 Y0 p0) (g0 : κ.ord.ToType → κ.ord.ToType)
  (b0 : uIdx → κ.ord.ToType) (seeds : Set (κ.ord.ToType ⊕ κ.ord.ToType))

theorem infra_78_seedStage_seeds :
    seeds ⊆ (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 g0 b0 seeds).e.R :=
  infra_78_closeR_subset ρ hℓel X0 Y0 p0 seeds

theorem infra_78_seedStage_card (hs : #seeds ≤ ρ) :
    #(infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 g0 b0 seeds).e.R ≤ ρ :=
  infra_78_closeR_card ρ hℓel X0 Y0 p0 hs

/-- **The seed stage is closed** (supply at the least stage). -/
theorem infra_78_seedStage_closed (hℓκ : ℓ ≤ κ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    (hs : #seeds ≤ ρ) :
    infra_78_PairClosed ρ hℓel (infra_78_toArr (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 g0 b0 seeds).hp)
      trivial (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 g0 b0 seeds).e.R :=
  infra_78_closeR_spec hℓel hℓκ hℓρ hpow hp0 hs

/-- Pair closure of the seed stage in plain form. -/
theorem infra_78_seedStage_pair (hℓκ : ℓ ≤ κ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    (hs : #seeds ≤ ρ) (x : κ.ord.ToType)
    (hx : (Sum.inl x : κ.ord.ToType ⊕ κ.ord.ToType) ∈
      (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 g0 b0 seeds).e.R) :
    (Sum.inr (p0 x) : κ.ord.ToType ⊕ κ.ord.ToType) ∈
      (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 g0 b0 seeds).e.R := by
  have := (infra_78_seedStage_closed ρ hℓel X0 Y0 p0 hp0 g0 b0 seeds hℓκ hℓρ hpow hs).2.1 x hx
  have e : ((infra_78_toArr hp0).onVertex PUnit.unit x : κ.ord.ToType) = p0 x :=
    infra_78_toArr_apply hp0 x
  exact e ▸ this

/-- **Seeding `S_0 ≠ ∅`**: a seed on the `Y`-side (e.g. a coordinate of `b`) lies in `R_0`. -/
theorem infra_78_seedStage_S_nonempty {y : κ.ord.ToType}
    (hy : (Sum.inr y : κ.ord.ToType ⊕ κ.ord.ToType) ∈ seeds) :
    ∃ y, (Sum.inr y : κ.ord.ToType ⊕ κ.ord.ToType) ∈
      (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 g0 b0 seeds).e.R :=
  ⟨y, infra_78_seedStage_seeds ρ hℓel X0 Y0 p0 hp0 g0 b0 seeds hy⟩

end Seed

section Supply
variable (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
  {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ) {uIdx cIdx L : Type u}
  {ρ : Cardinal.{u}} (hρκ : Order.succ ρ < μ)
  (Xb : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)) {ℓ : Cardinal.{u}}
  (hℓel : ℓ ∈ P.eligible)
  (cand : (Order.succ ρ).ord.ToType →
    Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx) →
    L → cIdx → μ.ord.ToType)
  (s0 : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
  (e0 : Infra78MarkData μ uIdx)

include hρκ in
/-- **Supply at non-limit stages**: when invariant (5) holds at every stage (so the successor
operator never falls back) and the seed stage is closed, every non-limit stage's bookkeeping set
is closed for that stage's own pair. -/
theorem infra_78_rc_supply (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (h5 : ∀ β, infra_78_StageInv5 Xb (infra_78_rcObj Xb hℓel cand s0 e0 β))
    (hℓκ : ℓ ≤ μ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ) (hρ : ℵ₀ ≤ ρ) (h0 : #s0.e.R ≤ ρ)
    (hseed : infra_78_PairClosed ρ hℓel (infra_78_toArr s0.hp) trivial s0.e.R)
    (i : (Order.succ ρ).ord.ToType) (hi : ¬ Order.IsSuccLimit i) :
    infra_78_PairClosed ρ hℓel (infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 i).hp) trivial
      (infra_78_rcObj Xb hℓel cand s0 e0 i).e.R := by
  rcases infra_78_stage_trichotomy i with hmin | ⟨β, hβ⟩ | hk
  · have h : infra_78_rcObj Xb hℓel cand s0 e0 i = s0 := infra_78_pairMatrix_min s0 _ _ hmin
    rw [h]; exact hseed
  · obtain ⟨-, -, -, -, -, hR, -⟩ := infra_78_opMatrix_succ P σ hσ hμT hρκ Xb (infra_78_rcl ρ hℓel)
      cand hidx s0 (infra_78_limMarkE e0) hβ (h5 β)
    have hT : #(Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 β i).1
        (infra_78_rcMap Xb hℓel cand s0 e0 β i).2 '' (infra_78_rcObj Xb hℓel cand s0 e0 β).e.R) ≤ ρ :=
      Cardinal.mk_image_le.trans (infra_78_rc_card hρκ Xb hℓel cand s0 e0 hρ h0 β)
    have hPC := infra_78_closeR_spec hℓel hℓκ hℓρ hpow
      (infra_78_rcObj Xb hℓel cand s0 e0 i).hp hT
    have hR' : (infra_78_rcObj Xb hℓel cand s0 e0 i).e.R =
        infra_78_closeR ρ hℓel (infra_78_rcObj Xb hℓel cand s0 e0 i).X
          (infra_78_rcObj Xb hℓel cand s0 e0 i).Y (infra_78_rcObj Xb hℓel cand s0 e0 i).p
          (Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 β i).1 (infra_78_rcMap Xb hℓel cand s0 e0 β i).2 ''
            (infra_78_rcObj Xb hℓel cand s0 e0 β).e.R) := hR
    rw [hR']; exact hPC
  · exact absurd hk hi

include hρκ in
/-- **`infra_78_rnext_closure`: the bookkeeping outputs of the recursion matrix** built with the
concrete update `infra_78_rcl` from a closed seed stage, under invariant (5) at every stage
(tracked: `infra_78_recursion_outputs`): sizes `≤ ρ`, forward closure and continuity (in the
`infra_78_bkStep` form), pair closure, `S_i ≠ ∅` at every stage, and closure requirements 1 and 2
at every non-limit stage and every stage of cofinality `> λ`. -/
theorem infra_78_rnext_closure (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (h5 : ∀ β, infra_78_StageInv5 Xb (infra_78_rcObj Xb hℓel cand s0 e0 β))
    (hℓκ : ℓ ≤ μ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ) (h0 : #s0.e.R ≤ ρ)
    (hseed : infra_78_PairClosed ρ hℓel (infra_78_toArr s0.hp) trivial s0.e.R)
    (hS0 : ∃ y, (Sum.inr y : μ.ord.ToType ⊕ μ.ord.ToType) ∈ s0.e.R) :
    (∀ i, #(infra_78_rcSets hρκ Xb hℓel cand s0 e0 i) ≤ ρ) ∧
    (∀ {j i} (h : j < i), infra_78_bkStep (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) h ''
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 j ⊆ infra_78_rcSets hρκ Xb hℓel cand s0 e0 i) ∧
    (∀ i, Order.IsSuccLimit i → infra_78_rcSets hρκ Xb hℓel cand s0 e0 i =
      ⋃ j : Set.Iio i, infra_78_bkStep (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) j.2 ''
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 j.1) ∧
    (∀ i x, (Sum.inl x : infra_78_bkCarrier (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) i) ∈
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 i →
      (Sum.inr (((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).pair i).onVertex PUnit.unit x) :
        infra_78_bkCarrier (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) i) ∈
        infra_78_rcSets hρκ Xb hℓel cand s0 e0 i) ∧
    (∀ i, ∃ y, y ∈ infra_78_Spart (infra_78_rcObj Xb hℓel cand s0 e0 i)) ∧
    (∀ i, (¬ Order.IsSuccLimit i ∨ ℓ < Order.cof (Set.Iio i)) →
      ∀ s ⊆ infra_78_rcSets hρκ Xb hℓel cand s0 e0 i, #s ≤ ℓ →
      infra_78_bkReq1 (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) hℓel i s
        (infra_78_rcSets hρκ Xb hℓel cand s0 e0 i)) ∧
    (∀ σ' : Cardinal.{u}, ℵ₀ ≤ σ' → μ ∈ recursionClosedLevels P σ' → Order.succ σ' ≤ μ → ℓ < μ →
      ∀ i, (¬ Order.IsSuccLimit i ∨ ℓ < Order.cof (Set.Iio i)) →
      ∀ s ⊆ infra_78_rcSets hρκ Xb hℓel cand s0 e0 i, #s ≤ ℓ →
      #(Sum.inr ⁻¹' s : Set ((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).Y i).model.carrier) ≤ σ' →
      ∃ seq : ApproximationSequence
          (infra_78_bkTuple (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) i s), seq.τ = ℓ ∧
        ℓ + ℵ₀ < #seq.κIndex ∧
        ∀ a b, (Sum.inl (((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).X i).val (seq.family a b)) :
          infra_78_bkCarrier (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) i) ∈
          infra_78_rcSets hρκ Xb hℓel cand s0 e0 i) := by
  have hℓ : ℵ₀ ≤ ℓ := P.aleph0_le hℓel
  have hρ : ℵ₀ ≤ ρ := hℓ.trans hℓρ.le
  have hsupp := infra_78_rc_supply P σ hσ hμT hρκ Xb hℓel cand s0 e0 hidx h5 hℓκ hℓρ hpow hρ h0 hseed
  have hM := infra_78_pairMatrix_compLaw hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) (infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand)
  have hC := infra_78_pairMatrix_contAtLimits hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) (infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand)
  have hmono := fun {j i : (Order.succ ρ).ord.ToType} (h : j < i) =>
    infra_78_rc_bkMono hρκ Xb hℓel cand s0 e0 h
  have hlim := infra_78_rc_bkLim hρκ Xb hℓel cand s0 e0
  refine ⟨fun i => infra_78_rc_card hρκ Xb hℓel cand s0 e0 hρ h0 i, hmono, hlim, ?_,
    fun i => infra_78_rc_S_nonempty hρκ Xb hℓel cand s0 e0 hS0 i, ?_, ?_⟩
  · intro i x hx
    have h0p : ∀ x, (Sum.inl x : μ.ord.ToType ⊕ μ.ord.ToType) ∈ s0.e.R →
        (Sum.inr (s0.p x) : μ.ord.ToType ⊕ μ.ord.ToType) ∈ s0.e.R := fun x hx => by
      have := hseed.2.1 x hx
      have e : ((infra_78_toArr s0.hp).onVertex PUnit.unit x : μ.ord.ToType) = s0.p x :=
        infra_78_toArr_apply s0.hp x
      exact e ▸ this
    have := infra_78_rc_pair hρκ Xb hℓel cand s0 e0 hℓκ hℓρ hpow hρ h0 h0p i x hx
    have e : (((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).pair i).onVertex PUnit.unit x :
        μ.ord.ToType) = (infra_78_rcObj Xb hℓel cand s0 e0 i).p x :=
      infra_78_pairMatrix_pair_apply hρκ s0 _ _ _ i x
    exact e ▸ this
  · intro i hi s hs hsl
    rcases hi with hnl | hcof
    · exact (hsupp i hnl).2.2.1 s hs hsl
    · exact infra_78_bookkeeping_req1_high_cof _ hM hℓel _ hmono hlim
        (fun i hi s hs hsl => (hsupp i hi).2.2.1 s hs hsl) i hcof s hs hsl
  · intro σ' hσ' hrec hσS hℓμ i hi s hs hsl hσs
    rcases hi with hnl | hcof
    · exact (hsupp i hnl).2.2.2 σ' hσ' hrec hσS hℓμ s hs hsl hσs
    · exact infra_78_bookkeeping_req2_high_cof _ hM hC hℓ hℓμ σ' hσ' hrec hσS _ hmono hlim
        (fun i hi s hs hsl hσs => (hsupp i hi).2.2.2 σ' hσ' hrec hσS hℓμ s hs hsl hσs)
        i hcof s hs hsl hσs

end Supply
end AEC
