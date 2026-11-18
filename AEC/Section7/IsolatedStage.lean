module

public import AEC.Section7.RecursionOutputs

@[expose] public section

/-!
# Prop 7.8: an isolated stage of the recursion matrix (`infra_78_isolated_stage`)

Paper (Prop 7.8 proof): suppose every stage `i` with `cf(i) > λ` has a failing list `d_i ⊆ S_i`.
By continuity `d_i ⊆ S_{j(i)}` for some `j(i) < i`; Fodor and `ρ^λ = ρ` fix `j` and the list
`d` on a stationary set; local character in the union of the whole `ρ⁺`-chain makes `(b, d)`
free from some stage on, contradicting the nonfree extensions at the stationary set.

Cycle 55: `infra_78_isolated_stage_core` (lists indexed by the fixed `cIdx`). Cycle 56:
`infra_78_isolated_stage` for every list of length `≤ θ = |cIdx|` (incl. the empty list) at the
same stage: pad with a point `p_i(x_i) ∈ S_i` (`infra_78_rc_padPoint`, seeded by
`infra_78_padSeed_of_closed`) and project back (`infra_78_isolated_of_pad`: the competitor is
padded with the same base point, which joins the fragment; only injective reindexing of
diagrams, via `WorkingScheme.diagramEq_precomp`).
-/

universe u

open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}

section FullChain
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

theorem infra_78_full_ord_limit (hρ : ℵ₀ ≤ ρ) :
    (0 : Ordinal.{u}) < (Order.succ ρ).ord ∧ Order.IsSuccLimit (Order.succ ρ).ord := by
  have h := Cardinal.isSuccLimit_ord (hρ.trans (Order.le_succ ρ))
  exact ⟨by simp, h⟩

/-- The whole `ρ⁺`-chain of `X`-stages of a matrix as a `SameLevelChain` over a covering
cocone. -/
noncomputable def infra_78_fullChain (hρ : ℵ₀ ≤ ρ) (M : Infra78Matrix P ρ hκ) (hM : M.CompLaw)
    (U : P.scheme.Object κ hκ)
    (l : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (M.X j)) (P.scheme.asSystem hκ U))
    (hl : ∀ {a b : (Order.succ ρ).ord.ToType} (h : a ≤ b), SystemArrow.comp (M.stepX h) (l b) = l a)
    (hcov : ∀ x : U.model.carrier, ∃ j y, (l j).onVertex PUnit.unit y = x) :
    SameLevelChain P hκ where
  δ := (Order.succ ρ).ord
  hlim := infra_78_full_ord_limit hρ
  obj α hα := M.X (Ordinal.ToType.mk ⟨α, hα⟩)
  le hα hβ h := M.stepX (Ordinal.ToType.mk.le_iff_le.2
    (show (⟨_, hα⟩ : Set.Iio (Order.succ ρ).ord) ≤ ⟨_, hβ⟩ from h))
  le_arrow _ _ _ := trivial
  le_comp _ _ _ _ _ := (hM.1 _ _).symm
  unionObj := U
  toUnion α hα := l _
  toUnion_arrow _ _ := trivial
  toUnion_comp _ _ _ := hl _
  joint x := by
    obtain ⟨j, y, hy⟩ := hcov x.2
    obtain ⟨⟨α, hα⟩, rfl⟩ := Ordinal.ToType.mk.surjective j
    exact ⟨α, hα, ⟨PUnit.unit, y⟩, by
      show (⟨PUnit.unit, _⟩ : Σ _ : PUnit, _) = x
      rw [hy]
      rfl⟩

/-- **Eventual freeness along the whole matrix** (local character in the `ρ⁺`-union). A list `v`
in `Y_j` of size `≤ σ` and `≤ ρ`, moved to `Y_k`, is tied free over `X_i → X_k` for all
`j* ≤ i ≤ k` (some `j*`). -/
theorem infra_78_matrix_eventually_free (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (hrec : κ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ κ)
    (hρ : ℵ₀ ≤ ρ) (hρκ : Order.succ ρ < κ) (M : Infra78Matrix P ρ hκ) (hI : M.IdLaw)
    (hM : M.CompLaw) (j : (Order.succ ρ).ord.ToType) {I : Type u}
    (v : I → Occurrence K oneVertexShape (P.scheme.asSystem hκ (M.Y j)))
    (hidx : #I ≤ σ) (hIρ : #I ≤ ρ) :
    ∃ jstar : (Order.succ ρ).ord.ToType, ∀ (i k : (Order.succ ρ).ord.ToType) (hji : j ≤ i),
      jstar ≤ i → ∀ hik : i ≤ k,
      IsTiedFree (M.stepX hik)
        ((infra_78_markTuple (M.pair k) (fun x => pushOcc (M.stepY (hji.trans hik)) (v x))).restrict
          (M.stepX hik) trivial)
        (infra_78_markTuple (M.pair k) (fun x => pushOcc (M.stepY (hji.trans hik)) (v x)))
        (Equiv.refl _) := by
  classical
  have hι : #(Order.succ ρ).ord.ToType ≤ κ := by rw [Cardinal.mk_ord_toType]; exact hρκ.le
  have : Nonempty (Order.succ ρ).ord.ToType := ⟨j⟩
  obtain ⟨Xδ, Yδ, lX, lY, pδ, -, -, -, hcX, hcY, hsq, hcovX, -⟩ :=
    infra_78_limit_pair_gen hι M.X M.Y M.pair M.stepX M.stepY hI.1 hI.2 hM.1 hM.2 M.comm
  let C := infra_78_fullChain hρ M hM Xδ lX hcX hcovX
  let p : TupleOver K oneVertexShape P.scheme hκ C.unionObj :=
    infra_78_markTuple pδ (fun x => pushOcc (lY j) (v x))
  have hcofC : #p.idx < C.δ.cof := by
    show #I < (Order.succ ρ).ord.cof
    rw [(Cardinal.isRegular_succ hρ).cof_ord]
    exact Order.lt_succ_of_le hIρ
  obtain ⟨jo, hjo, H⟩ := infra_78_fixed_list_eventually_free P σ hσ hκ hrec hσSucc C p rfl hidx hcofC
  refine ⟨Ordinal.ToType.mk ⟨jo, hjo⟩, ?_⟩
  intro i k hji hsi hik
  obtain ⟨⟨io, hio⟩, rfl⟩ := Ordinal.ToType.mk.surjective i
  obtain ⟨⟨ko, hko⟩, rfl⟩ := Ordinal.ToType.mk.surjective k
  have hjoi : jo ≤ io := Ordinal.ToType.mk.le_iff_le.1 hsi
  have hiok : io ≤ ko := Ordinal.ToType.mk.le_iff_le.1 hik
  have hF := H io ko hio hko hjoi hiok
  have hqκ : #I < κ := hidx.trans_lt (Order.succ_le_iff.1 hσSucc)
  set kk := Ordinal.ToType.mk (⟨ko, hko⟩ : Set.Iio (Order.succ ρ).ord) with hkk
  set ii := Ordinal.ToType.mk (⟨io, hio⟩ : Set.Iio (Order.succ ρ).ord) with hii
  let tk := infra_78_markTuple (M.pair kk) (fun x => pushOcc (M.stepY (hji.trans hik)) (v x))
  have hsqx : ∀ (x : (M.X kk).model.carrier),
      (lY kk).onVertex PUnit.unit ((M.pair kk).onVertex PUnit.unit x) =
        pδ.onVertex PUnit.unit ((lX kk).onVertex PUnit.unit x) := fun x =>
    DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hsq kk)) x
  have hval : ∀ x, pushOcc (lY j) (v x) = pushOcc (lY kk) (pushOcc (M.stepY (hji.trans hik)) (v x)) := by
    intro x
    rw [← pushOcc_comp, hcY]
  have hR : infra_78_HostRel tk (p.restrict (C.toUnion ko hko) (C.toUnion_arrow ko hko)) (lY kk)
      (Equiv.refl _) :=
    ⟨fun v x => by cases v; exact hsqx x, fun x => hval x⟩
  have hR' : infra_78_HostRel (tk.restrict (M.stepX hik) trivial)
      ((p.restrict (C.toUnion ko hko) (C.toUnion_arrow ko hko)).restrict (M.stepX hik) trivial)
      (lY kk) (Equiv.refl _) :=
    ⟨fun v x => by cases v; exact hsqx _, fun x => hval x⟩
  have h1 := (infra_78_tiedFree_host_target (M.stepX hik)
    ((p.restrict (C.toUnion ko hko) (C.toUnion_arrow ko hko)).restrict (M.stepX hik) trivial)
    trivial hR rfl rfl hqκ (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).2 hF
  exact infra_78_tiedFree_host_source' (M.stepX hik) trivial hR' rfl rfl hqκ tk
    (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) h1

end FullChain

section StageFacts
variable {ρ : Cardinal.{u}}

/-- A stage `i < ρ⁺` with `cf(i) > λ ≥ ℵ₀` is a limit stage. -/
theorem infra_78_highcof_limit {ℓ : Cardinal.{u}} (hℓ : ℵ₀ ≤ ℓ) {i : (Order.succ ρ).ord.ToType}
    (h : ℓ < Order.cof (Set.Iio i)) : Order.IsSuccLimit i := by
  have hone : (1 : Cardinal) < Order.cof (Set.Iio i) := (one_lt_aleph0.trans_le hℓ).trans h
  refine ⟨fun hmin => ?_, fun b hb => ?_⟩
  · have : IsEmpty (Set.Iio i) := ⟨fun z => hmin.not_lt z.2⟩
    have h0 := Order.cof_le_cardinalMk (α := Set.Iio i)
    rw [Cardinal.mk_eq_zero] at h0
    exact absurd h0 (not_le.2 (hone.trans_le' zero_le_one))
  · have : Nonempty (Set.Iio i) := ⟨⟨b, hb.lt⟩⟩
    have h1 : Order.cof (Set.Iio i) ≤ 1 :=
      Order.cof_le_one_iff.2 ⟨⟨b, hb.lt⟩, fun z => hb.le_of_lt z.2⟩
    exact absurd h1 (not_le.2 hone)

/-- No stage of `ρ⁺` (`ρ` infinite) is maximal. -/
theorem infra_78_stage_not_isMax (hρ : ℵ₀ ≤ ρ) (i : (Order.succ ρ).ord.ToType) : ¬ IsMax i := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := Ordinal.ToType.mk.surjective i
  have hs : Order.succ a < (Order.succ ρ).ord :=
    (Cardinal.isSuccLimit_ord (hρ.trans (Order.le_succ ρ))).succ_lt ha
  intro hmax
  have h := hmax (Ordinal.ToType.mk.le_iff_le.2
    (show (⟨a, ha⟩ : Set.Iio (Order.succ ρ).ord) ≤ ⟨Order.succ a, hs⟩ from Order.le_succ a))
  have h' : Order.succ a ≤ a := Ordinal.ToType.mk.le_iff_le.1 h
  exact absurd h' (not_le.2 (Order.lt_succ_of_not_isMax (not_isMax a)))

/-- Stationary subsets of `ρ⁺` are unbounded. -/
theorem infra_78_stationary_unbounded {T : Set (Order.succ ρ).ord.ToType} (hT : IsStationary T)
    (a : (Order.succ ρ).ord.ToType) : ∃ i ∈ T, a ≤ i := by
  have hclub : IsClub (Set.Ici a) := by
    refine ⟨fun d hd hne _ x hx => ?_, fun x => ⟨max x a, show a ≤ max x a from le_max_right _ _, le_max_left _ _⟩⟩
    obtain ⟨y, hy⟩ := hne
    exact (hd hy).trans (hx.1 hy)
  obtain ⟨i, hi, hai⟩ := hT hclub
  exact ⟨i, hi, hai⟩

/-- Stage cardinals: a mark shorter than the cofinality of a stage has size `≤ ρ`. -/
theorem infra_78_lt_stage_cof_le {I : Type u} (δ : (Order.succ ρ).ord.ToType)
    (h : #I < (Ordinal.ToType.toOrd δ).1.cof) : #I ≤ ρ := by
  have h1 := h.le.trans (Ordinal.cof_le_card _)
  have h2 : (Ordinal.ToType.toOrd δ).1.card < Order.succ ρ := Cardinal.lt_ord.1 (Ordinal.ToType.toOrd δ).2
  exact Order.lt_succ_iff.1 (h1.trans_lt h2)

end StageFacts

section RcPullback
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible} {uIdx cIdx L : Type u}
variable (hρκ : Order.succ ρ < κ) (Xb : P.scheme.Object κ hκ) {ℓ : Cardinal.{u}}
  (hℓel : ℓ ∈ P.eligible)
  (cand : (Order.succ ρ).ord.ToType → Infra78Stage P hκ (Infra78MarkData κ uIdx) →
    L → cIdx → κ.ord.ToType)
  (s0 : Infra78Stage P hκ (Infra78MarkData κ uIdx)) (e0 : Infra78MarkData κ uIdx)

include hρκ in
/-- Composition of the plain `Y`-maps of the recursion matrix. -/
theorem infra_78_rc_map2_comp {a b c : (Order.succ ρ).ord.ToType} (h₁ : a ≤ b) (h₂ : b ≤ c)
    (w : κ.ord.ToType) :
    (infra_78_rcMap Xb hℓel cand s0 e0 a c).2 w =
      (infra_78_rcMap Xb hℓel cand s0 e0 b c).2 ((infra_78_rcMap Xb hℓel cand s0 e0 a b).2 w) := by
  obtain ⟨-, -, hC⟩ := infra_78_pairChain_laws hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) (infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand)
  exact congrFun (congrArg Prod.snd (hC a b c h₁ h₂)) w

include hρκ in
/-- **Continuity pull-back (paper: `d_i ⊆ S_{j(i)}`).** At a stage `i` with `cf(i) > λ`, a list of
length `≤ λ` from `S_i` is the image of a list from `S_j` for some `j < i`. -/
theorem infra_78_rc_pullback (hℓ : ℵ₀ ≤ ℓ) {i : (Order.succ ρ).ord.ToType}
    (hi : ℓ < Order.cof (Set.Iio i)) (hc : #cIdx ≤ ℓ) (d : cIdx → κ.ord.ToType)
    (hd : Set.range d ⊆ infra_78_Spart (infra_78_rcObj Xb hℓel cand s0 e0 i)) :
    ∃ j < i, ∃ d' : cIdx → κ.ord.ToType,
      Set.range d' ⊆ infra_78_Spart (infra_78_rcObj Xb hℓel cand s0 e0 j) ∧
      ∀ x, d x = (infra_78_rcMap Xb hℓel cand s0 e0 j i).2 (d' x) := by
  classical
  have hlim := infra_78_highcof_limit hℓ hi
  let S : (Order.succ ρ).ord.ToType → Set (κ.ord.ToType ⊕ κ.ord.ToType) := fun j' =>
    {e | ∃ j0, j0 ≤ j' ∧ j0 < i ∧ e ∈ Sum.map (infra_78_rcMap Xb hℓel cand s0 e0 j0 i).1
      (infra_78_rcMap Xb hℓel cand s0 e0 j0 i).2 '' (infra_78_rcObj Xb hℓel cand s0 e0 j0).e.R}
  have hS : Monotone S := fun a b hab e ⟨j0, h1, h2, h3⟩ => ⟨j0, h1.trans hab, h2, h3⟩
  have hSi : S i ⊆ ⋃ j ∈ Set.Iio i, S j := fun e ⟨j0, _, h2, h3⟩ =>
    Set.mem_biUnion h2 ⟨j0, le_rfl, h2, h3⟩
  have hdS : Sum.inr '' Set.range d ⊆ S i := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hx : Sum.inr (d x) ∈ (infra_78_rcObj Xb hℓel cand s0 e0 i).e.R := hd ⟨x, rfl⟩
    rw [infra_78_rc_limit hρκ Xb hℓel cand s0 e0 hlim] at hx
    obtain ⟨j0, hj0⟩ := Set.mem_iUnion.1 hx
    exact ⟨j0.1, j0.2.le, j0.2, hj0⟩
  have hcard : #(Sum.inr '' Set.range d : Set (κ.ord.ToType ⊕ κ.ord.ToType)) ≤ ℓ :=
    Cardinal.mk_image_le.trans (Cardinal.mk_range_le.trans hc)
  obtain ⟨j, hj, hdj⟩ := infra_78_bounded_in_earlier_stage S hS hSi hdS hcard hi
  have H : ∀ x, ∃ y, Sum.inr y ∈ (infra_78_rcObj Xb hℓel cand s0 e0 j).e.R ∧
      d x = (infra_78_rcMap Xb hℓel cand s0 e0 j i).2 y := by
    intro x
    obtain ⟨j0, h1, h2, z, hz, hzx⟩ := hdj ⟨d x, ⟨x, rfl⟩, rfl⟩
    rcases z with z | y
    · exact absurd hzx (by simp)
    · have hy : d x = (infra_78_rcMap Xb hℓel cand s0 e0 j0 i).2 y := by
        simpa using hzx.symm
      refine ⟨(infra_78_rcMap Xb hℓel cand s0 e0 j0 j).2 y,
        infra_78_rc_forward hρκ Xb hℓel cand s0 e0 j0 j h1 ⟨Sum.inr y, hz, rfl⟩, ?_⟩
      rw [hy, infra_78_rc_map2_comp hρκ Xb hℓel cand s0 e0 h1 hj.le]
  choose d' hd'S hd'eq using H
  exact ⟨j, hj, d', by rintro _ ⟨x, rfl⟩; exact hd'S x, hd'eq⟩

include hρκ in
/-- **A padding point at every stage**: if the seed set contains `p_0(x)` on the `Y`-side for some
`x ∈ X_0`, then every `S_k` contains `p_k(x_k)` for some `x_k ∈ X_k` (forward closure and the
commuting squares). -/
theorem infra_78_rc_padPoint (h0 : ∃ x, (Sum.inr (s0.p x) : κ.ord.ToType ⊕ κ.ord.ToType) ∈ s0.e.R)
    (k : (Order.succ ρ).ord.ToType) :
    ∃ x, (infra_78_rcObj Xb hℓel cand s0 e0 k).p x ∈
      infra_78_Spart (infra_78_rcObj Xb hℓel cand s0 e0 k) := by
  have hsop := infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand
  obtain ⟨hA, -, -⟩ := infra_78_pairChain_laws hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) hsop
  obtain ⟨i0, -, hi0⟩ := (wellFounded_lt (α := (Order.succ ρ).ord.ToType)).has_min Set.univ
    ⟨k, trivial⟩
  have hmin : IsMin i0 := fun b _ => not_lt.1 (hi0 b trivial)
  have hi0k : i0 ≤ k := not_lt.1 (hi0 k trivial)
  have h : infra_78_rcObj Xb hℓel cand s0 e0 i0 = s0 := infra_78_pairMatrix_min s0 _ _ hmin
  obtain ⟨x, hx⟩ := h0
  have hx' : (Sum.inr ((infra_78_rcObj Xb hℓel cand s0 e0 i0).p x) : κ.ord.ToType ⊕ κ.ord.ToType) ∈
      (infra_78_rcObj Xb hℓel cand s0 e0 i0).e.R := by rw [h]; exact hx
  have hf := infra_78_rc_forward hρκ Xb hℓel cand s0 e0 i0 k hi0k ⟨_, hx', rfl⟩
  have hsq := congrFun (hA i0 k hi0k).2.2 x
  refine ⟨(infra_78_rcMap Xb hℓel cand s0 e0 i0 k).1 x, ?_⟩
  show (Sum.inr ((infra_78_rcObj Xb hℓel cand s0 e0 k).p _) : κ.ord.ToType ⊕ κ.ord.ToType) ∈
    (infra_78_rcObj Xb hℓel cand s0 e0 k).e.R
  have e : (infra_78_rcObj Xb hℓel cand s0 e0 k).p ((infra_78_rcMap Xb hℓel cand s0 e0 i0 k).1 x) =
      (infra_78_rcMap Xb hℓel cand s0 e0 i0 k).2 ((infra_78_rcObj Xb hℓel cand s0 e0 i0).p x) := hsq
  rw [e]; exact hf

end RcPullback

section Core
variable (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
  {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ) {uIdx cIdx : Type u}
  {ρ : Cardinal.{u}} (hρκ : Order.succ ρ < μ)
  (Xb : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)) {ℓ : Cardinal.{u}}
  (hℓel : ℓ ∈ P.eligible)

include hρκ in
/-- **`infra_78_isolated_stage_core`** (Prop 7.8 proof, the Fodor argument). In the recursion
matrix with candidate lists from `S_i` (`infra_78_candS`), lists of length `|cIdx| ≤ λ`
(`λ < ρ` eligible, so `ℵ₀ ≤ λ`; `ρ^λ = ρ`), seed with invariant (5), nonempty `S`-part and `|R_0| ≤ ρ`, some
stage `i` with `cf(i) > λ` has every list `d : cIdx → S_i` relatively isolated (with the mark
`b_i` prepended). Proof: otherwise each such stage has a failing list with a nonfree extension
(`infra_78_rc_failing_list`); continuity pulls it back to some `S_{j(i)}`, `j(i) < i`
(`infra_78_rc_pullback`); Fodor with `ρ^λ = ρ` fixes `j` and the list on a stationary set
(`infra_78_stationary_fixed_list`); local character in the `ρ⁺`-union makes the fixed list free
from some stage on (`infra_78_matrix_eventually_free`), a contradiction at a stationary stage. -/
theorem infra_78_isolated_stage_core (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (hcof : ∀ δ : (Order.succ ρ).ord.ToType, Order.IsSuccLimit δ →
      #uIdx < (Ordinal.ToType.toOrd δ).1.cof)
    (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ) (hc : #cIdx ≤ ℓ)
    (s0 : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
    (e0 : Infra78MarkData μ uIdx) (h5seed : infra_78_StageInv5 Xb s0)
    (hS0 : ∃ y, (Sum.inr y : μ.ord.ToType ⊕ μ.ord.ToType) ∈ s0.e.R) (h0 : #s0.e.R ≤ ρ) :
    ∃ i : (Order.succ ρ).ord.ToType, ℓ < Order.cof (Set.Iio i) ∧
      ∀ d : cIdx → μ.ord.ToType,
        Set.range d ⊆ infra_78_Spart (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i) →
        IsRelativelyIsolated (infra_78_markTuple
          (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).hp)
          (Sum.elim (infra_78_stageMark (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i))
            (fun x => ⟨PUnit.unit, d x⟩)))
          (Equiv.refl (uIdx ⊕ cIdx)) := by
  classical
  have hℓ : ℵ₀ ≤ ℓ := P.aleph0_le hℓel
  have hρ : ℵ₀ ≤ ρ := hℓ.trans hℓρ.le
  have hTst := infra_78_stationary_high_cof ρ ℓ hℓ hℓρ
  set T := {x : (Order.succ ρ).ord.ToType | ℓ < Order.cof (Set.Iio x)} with hT
  by_contra hne
  have hfail : ∀ i ∈ T, ∃ d : cIdx → μ.ord.ToType,
      Set.range d ⊆ infra_78_Spart (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i) ∧
      ∃ hX : infra_78_IsArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).X
          (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).X
          (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 i (Order.succ i)).1,
        ¬ IsTiedFree (infra_78_toArr hX)
          ((infra_78_markTuple (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).hp)
            (fun x => (⟨PUnit.unit, (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 i (Order.succ i)).2
              (Sum.elim (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).e.b d x)⟩ :
              Occurrence K oneVertexShape (P.scheme.asSystem _
                (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).Y)))).restrict
            (infra_78_toArr hX) trivial)
          (infra_78_markTuple (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).hp)
            (fun x => (⟨PUnit.unit, (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 i (Order.succ i)).2
              (Sum.elim (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).e.b d x)⟩ :
              Occurrence K oneVertexShape (P.scheme.asSystem _
                (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).Y))))
          (Equiv.refl _) := by
    intro i hi
    have hcov : i ⋖ Order.succ i := Order.covBy_succ_of_not_isMax (infra_78_stage_not_isMax hρ i)
    obtain ⟨hX, hA | ⟨d, hdS, -, hnf⟩⟩ := infra_78_rc_failing_list P σ hσ hμT hρκ Xb hℓel hidx hcof
      s0 e0 h5seed hS0 hcov
    · exact absurd ⟨i, hi, hA⟩ hne
    · exact ⟨d, hdS, hX, hnf⟩
  have hsop := infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) (infra_78_candS (ι := (Order.succ ρ).ord.ToType) (κ := μ) (uIdx := uIdx) (P := P) (hκ := Tail.mem (infra_73_tail P σ hσ) hμT) cIdx)
  -- pull back each failing list to an earlier stage
  have hpb : ∀ i ∈ T, ∃ jd : (Order.succ ρ).ord.ToType × (cIdx → μ.ord.ToType), jd.1 < i ∧
      Set.range jd.2 ⊆ infra_78_Spart (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 jd.1) ∧
      ∃ d : cIdx → μ.ord.ToType,
      (∀ x, d x = (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 jd.1 i).2 (jd.2 x)) ∧
      ∃ hX : infra_78_IsArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).X
          (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).X
          (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 i (Order.succ i)).1,
        ¬ IsTiedFree (infra_78_toArr hX)
          ((infra_78_markTuple (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).hp)
            (fun x => (⟨PUnit.unit, (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 i (Order.succ i)).2
              (Sum.elim (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).e.b d x)⟩ :
              Occurrence K oneVertexShape (P.scheme.asSystem _
                (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).Y)))).restrict
            (infra_78_toArr hX) trivial)
          (infra_78_markTuple (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).hp)
            (fun x => (⟨PUnit.unit, (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 i (Order.succ i)).2
              (Sum.elim (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).e.b d x)⟩ :
              Occurrence K oneVertexShape (P.scheme.asSystem _
                (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).Y))))
          (Equiv.refl _) := by
    intro i hi
    obtain ⟨d, hdS, hX, hnf⟩ := hfail i hi
    obtain ⟨j, hj, d', hd'S, hd'⟩ := infra_78_rc_pullback hρκ Xb hℓel (infra_78_candS cIdx) s0 e0
      hℓ hi hc d hdS
    exact ⟨(j, d'), hj, hd'S, d, hd', hX, hnf⟩
  obtain ⟨i0, hi0⟩ := hTst.nonempty
  have : Nonempty ((Order.succ ρ).ord.ToType × (cIdx → μ.ord.ToType)) :=
    ⟨(i0, fun _ => hS0.choose)⟩
  choose! F hF using hpb
  have hρ0 : ρ ≠ 0 := (aleph0_pos.trans_le hρ).ne'
  have hcount : ∀ j, #{x : (Order.succ ρ).ord.ToType × (cIdx → μ.ord.ToType) //
      x.1 = j ∧ Set.range x.2 ⊆ infra_78_Spart (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 j)} ≤ ρ := by
    intro j
    have hSp : #(infra_78_Spart (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 j)) ≤ ρ :=
      (Cardinal.mk_preimage_of_injective Sum.inr _ Sum.inr_injective).trans
        (infra_78_rc_card hρκ Xb hℓel (infra_78_candS cIdx) s0 e0 hρ h0 j)
    refine (Cardinal.mk_le_of_injective (f := fun x => (⟨x.1.2, x.2.2⟩ :
      {d : cIdx → μ.ord.ToType // Set.range d ⊆
        infra_78_Spart (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 j)})) ?_).trans
      (infra_78_Slists_card _ hρ0 hSp hc hpow)
    intro x y h
    exact Subtype.ext (Prod.ext (x.2.1.trans y.2.1.symm) (congrArg Subtype.val h))
  obtain ⟨j, ⟨j', dl⟩, ⟨hj', hdlS⟩, hst⟩ := infra_78_stationary_fixed_list ρ hρ
    (fun j x => x.1 = j ∧ Set.range x.2 ⊆
      infra_78_Spart (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 j)) hcount hTst F
    (fun i hi => ⟨(F i).1, (hF i hi).1, rfl, (hF i hi).2.1⟩)
  dsimp only at hj'
  subst hj'
  have hu : #uIdx ≤ ρ := infra_78_lt_stage_cof_le i0 (hcof i0 (infra_78_highcof_limit hℓ hi0))
  have hIρ : #(uIdx ⊕ cIdx) ≤ ρ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le hρ hu (hc.trans hℓρ.le)
  have hI := infra_78_pairMatrix_idLaw hρκ s0
    (infra_78_succOp Xb (infra_78_rcl ρ hℓel) (infra_78_candS cIdx)) (infra_78_limMarkE e0) hsop
  have hM := infra_78_pairMatrix_compLaw hρκ s0
    (infra_78_succOp Xb (infra_78_rcl ρ hℓel) (infra_78_candS cIdx)) (infra_78_limMarkE e0) hsop
  obtain ⟨jstar, Hfree⟩ := infra_78_matrix_eventually_free σ hσ hμT.1 (infra_73_tail_succ hμT) hρ
    hρκ (infra_78_rcMatrix hρκ Xb hℓel (infra_78_candS cIdx) s0 e0) hI hM j'
    (Sum.elim (infra_78_stageMark (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 j'))
      (fun x => ⟨PUnit.unit, dl x⟩)) hidx hIρ
  obtain ⟨i, ⟨hiT, hFi⟩, hai⟩ := infra_78_stationary_unbounded hst (max j' jstar)
  obtain ⟨-, -, d, hdeq, hX, hnf⟩ := hF i hiT
  rw [hFi] at hdeq
  have hji : j' ≤ i := le_of_max_le_left hai
  have hsi : jstar ≤ i := le_of_max_le_right hai
  have hik : i ≤ Order.succ i := Order.le_succ i
  have hfree := Hfree i (Order.succ i) hji hsi hik
  have hcoh := (infra_78_opMatrix_coherent hρκ Xb (infra_78_rcl ρ hℓel) (infra_78_candS cIdx) s0 e0
    j' i hji).2
  have hval : (fun x => pushOcc ((infra_78_rcMatrix hρκ Xb hℓel (infra_78_candS cIdx) s0 e0).stepY
      (hji.trans hik)) (Sum.elim (infra_78_stageMark (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 j'))
        (fun x => ⟨PUnit.unit, dl x⟩) x)) =
      (fun x => (⟨PUnit.unit, (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 i (Order.succ i)).2
        (Sum.elim (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).e.b d x)⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem _
          (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).Y))) := by
    funext x
    have hY : ∀ w, ((infra_78_rcMatrix hρκ Xb hℓel (infra_78_candS cIdx) s0 e0).stepY
        (hji.trans hik)).onVertex PUnit.unit w =
        (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 j' (Order.succ i)).2 w := fun w =>
      infra_78_pairMatrix_stepY_apply hρκ s0 _ _ hsop _ w
    have hw : Sum.elim (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).e.b d x =
        (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 j' i).2
          (Sum.elim (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 j').e.b dl x) := by
      rcases x with u | x
      · exact congrFun hcoh u
      · exact hdeq x
    have e : ((infra_78_rcMatrix hρκ Xb hℓel (infra_78_candS cIdx) s0 e0).stepY
        (hji.trans hik)).onVertex PUnit.unit
          (Sum.elim (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 j').e.b dl x) =
        (infra_78_rcMap Xb hℓel (infra_78_candS cIdx) s0 e0 i (Order.succ i)).2
          (Sum.elim (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).e.b d x) :=
      (hY _).trans ((infra_78_rc_map2_comp hρκ Xb hℓel (infra_78_candS cIdx) s0 e0 hji hik _).trans
        (congrArg _ hw.symm))
    rcases x with u | x
    · exact congrArg (fun y => (⟨PUnit.unit, y⟩ : Occurrence K oneVertexShape (P.scheme.asSystem _
        (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).Y))) e
    · exact congrArg (fun y => (⟨PUnit.unit, y⟩ : Occurrence K oneVertexShape (P.scheme.asSystem _
        (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 (Order.succ i)).Y))) e
  rw [hval] at hfree
  exact hnf hfree

end Core

section Padding
variable {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}

/-- Padding a tuple `(u, c)` (coordinates `uIdx ⊕ J`) to `(u, d)` with coordinates `uIdx ⊕ cIdx`,
`cIdx ≃ J ⊕ Kp`: the `J`-part is `c`, the `Kp`-part is the image of a fixed base point `w`. -/
def infra_78_padTuple (q : TupleOver K S W hμ base) {uIdx J cIdx Kp : Type u}
    (e : q.idx ≃ uIdx ⊕ J) (eK : cIdx ≃ J ⊕ Kp) (w : Occurrence K S (W.asSystem hμ base)) :
    TupleOver K S W hμ base where
  ν := q.ν
  hν := q.hν
  host := q.host
  incl := q.incl
  incl_arrow := q.incl_arrow
  idx := uIdx ⊕ cIdx
  val := Sum.elim (fun u => q.val (e.symm (Sum.inl u)))
    (fun k => Sum.elim (fun j => q.val (e.symm (Sum.inr j)))
      (fun _ => (⟨w.1, q.incl.onVertex w.1 w.2⟩ : Occurrence K S (W.asSystem q.hν q.host))) (eK k))

/-- The coordinate map of the padding: `(uIdx ⊕ cIdx) ⊕ ι → (uIdx ⊕ J) ⊕ (ι ⊕ Kp)`; padding
coordinates go to the extra fragment coordinates. Injective. -/
def infra_78_padMap {uIdx J cIdx Kp ι : Type u} (eK : cIdx ≃ J ⊕ Kp) :
    (uIdx ⊕ cIdx) ⊕ ι → (uIdx ⊕ J) ⊕ (ι ⊕ Kp)
  | Sum.inl (Sum.inl u) => Sum.inl (Sum.inl u)
  | Sum.inl (Sum.inr k) => Sum.elim (fun j => Sum.inl (Sum.inr j)) (fun kk => Sum.inr (Sum.inr kk)) (eK k)
  | Sum.inr z => Sum.inr (Sum.inl z)

theorem infra_78_padMap_injective {uIdx J cIdx Kp ι : Type u} (eK : cIdx ≃ J ⊕ Kp) :
    Function.Injective (infra_78_padMap (uIdx := uIdx) (ι := ι) eK) := by
  let g : (uIdx ⊕ J) ⊕ (ι ⊕ Kp) → (uIdx ⊕ cIdx) ⊕ ι
    | Sum.inl (Sum.inl u) => Sum.inl (Sum.inl u)
    | Sum.inl (Sum.inr j) => Sum.inl (Sum.inr (eK.symm (Sum.inl j)))
    | Sum.inr (Sum.inl z) => Sum.inr z
    | Sum.inr (Sum.inr kk) => Sum.inl (Sum.inr (eK.symm (Sum.inr kk)))
  refine Function.LeftInverse.injective (g := g) ?_
  intro a
  rcases a with (u | k) | z
  · rfl
  · show g (Sum.elim _ _ (eK k)) = _
    rcases hk : eK k with j | kk
    · show Sum.inl (Sum.inr (eK.symm (Sum.inl j))) = _
      rw [← hk, Equiv.symm_apply_apply]
    · show Sum.inl (Sum.inr (eK.symm (Sum.inr kk))) = _
      rw [← hk, Equiv.symm_apply_apply]
  · rfl

/-- **Isolation of a shorter list from isolation of its padding** (no non-injective diagram
reindexing). If the padded tuple `(u, d)` is relatively isolated over `u` (fragment `Z`), then
`(u, c)` is, with fragment `Z` plus `|Kp|` copies of the padding point `w`: a competitor `(u', c')`
pads to `(u', d')` with the same point; the diagram hypothesis transfers along the injective
coordinate map `infra_78_padMap` (`WorkingScheme.diagramEq_precomp`: `diagram_reindex` +
forward `diagram_restrict`), and the Galois-type conclusion restricts to the `J`-coordinates. -/
theorem infra_78_isolated_of_pad (q : TupleOver K S W hμ base) {uIdx J cIdx Kp : Type u}
    (e : q.idx ≃ uIdx ⊕ J) (eK : cIdx ≃ J ⊕ Kp) (w : Occurrence K S (W.asSystem hμ base))
    (hμ0 : ℵ₀ ≤ μ) (hKp : #Kp < μ)
    (h : IsRelativelyIsolated (infra_78_padTuple q e eK w) (Equiv.refl (uIdx ⊕ cIdx))) :
    IsRelativelyIsolated q e := by
  obtain ⟨ι, Z, hι, H⟩ := h
  refine ⟨ι ⊕ Kp, Sum.elim Z (fun _ => w), ?_, ?_⟩
  · rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hμ0 hι hKp
  intro q' e' hν' hmarg hdiag
  have hp := WorkingScheme.diagramEq_precomp q.host q'.host _ _ (infra_78_padMap (ι := ι) eK)
    (infra_78_padMap_injective eK) hdiag
  have e1 : alignJoint (Equiv.refl (uIdx ⊕ cIdx)) (typeJoint (p := infra_78_padTuple q e eK w) Z) =
      fun t => alignJoint e (typeJoint (p := q) (Sum.elim Z fun _ => w)) (infra_78_padMap eK t) := by
    funext t
    rcases t with (u | k) | z
    · rfl
    · show _ = alignJoint e (typeJoint (p := q) (Sum.elim Z fun _ => w)) (Sum.elim _ _ (eK k))
      show Sum.elim _ _ (eK k) = _
      rcases eK k with j | kk <;> rfl
    · rfl
  have e2 : alignJoint (Equiv.refl (uIdx ⊕ cIdx)) (typeJoint (p := infra_78_padTuple q' e' eK w) Z) =
      fun t => alignJoint e' (typeJoint (p := q') (Sum.elim Z fun _ => w)) (infra_78_padMap eK t) := by
    funext t
    rcases t with (u | k) | z
    · rfl
    · show _ = alignJoint e' (typeJoint (p := q') (Sum.elim Z fun _ => w)) (Sum.elim _ _ (eK k))
      show Sum.elim _ _ (eK k) = _
      rcases eK k with j | kk <;> rfl
    · rfl
  have hd : W.DiagramEq (X := (infra_78_padTuple q e eK w).host)
      (Y := (infra_78_padTuple q' e' eK w).host)
      (alignJoint (Equiv.refl (uIdx ⊕ cIdx)) (typeJoint (p := infra_78_padTuple q e eK w) Z))
      (alignJoint (Equiv.refl (uIdx ⊕ cIdx)) (typeJoint (p := infra_78_padTuple q' e' eK w) Z)) := by
    rw [e1, e2]; exact hp
  have h1 := H (infra_78_padTuple q' e' eK w) (Equiv.refl _) hν' hmarg hd
  obtain ⟨ρ, hρ, top, f1, f2, hf1, hf2, hinc, hval⟩ := h1
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hinc, fun i => ?_⟩
  rcases i with u | j
  · exact hval (Sum.inl u)
  · obtain ⟨k, hk⟩ : ∃ k, eK k = Sum.inl j := ⟨_, eK.apply_symm_apply _⟩
    have h1 : (infra_78_padTuple q e eK w).val (Sum.inr k) = q.val (e.symm (Sum.inr j)) := by
      show Sum.elim _ _ (eK k) = _
      rw [hk]; rfl
    have h2 : (infra_78_padTuple q' e' eK w).val (Sum.inr k) = q'.val (e'.symm (Sum.inr j)) := by
      show Sum.elim _ _ (eK k) = _
      rw [hk]; rfl
    have := hval (Sum.inr k)
    change (⟨((infra_78_padTuple q e eK w).val (Sum.inr k)).1,
        f1.onVertex ((infra_78_padTuple q e eK w).val (Sum.inr k)).1
          ((infra_78_padTuple q e eK w).val (Sum.inr k)).2⟩ : Occurrence K S (W.asSystem hρ top)) =
      ⟨((infra_78_padTuple q' e' eK w).val (Sum.inr k)).1,
        f2.onVertex ((infra_78_padTuple q' e' eK w).val (Sum.inr k)).1
          ((infra_78_padTuple q' e' eK w).val (Sum.inr k)).2⟩ at this
    rw [h1, h2] at this
    exact this

end Padding

section PadSeed
variable {P : SingleModelData K} {κ : Cardinal.{u}} {hκ : κ ∈ P.eligible} {uIdx : Type u}

/-- A closed seed set (`infra_78_PairClosed`, as produced by `infra_78_seedStage_closed`) contains
a padding point `p_0(x)`: requirement 1 for the empty set gives a level-`λ` subobject inside the
`X`-part, and pair closure moves one of its points to the `Y`-side. -/
theorem infra_78_padSeed_of_closed (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (s0 : Infra78Stage P hκ (Infra78MarkData κ uIdx))
    (hseed : infra_78_PairClosed ρ hℓel (infra_78_toArr s0.hp) trivial s0.e.R) :
    ∃ x, (Sum.inr (s0.p x) : κ.ord.ToType ⊕ κ.ord.ToType) ∈ s0.e.R := by
  obtain ⟨A, V, iA, iV, g, -, -, -, -, -, -, hA, -⟩ :=
    hseed.2.2.1 ∅ (Set.empty_subset _) (by simp)
  have hne : Nonempty ℓ.ord.ToType :=
    Cardinal.nonempty_ord_toType (aleph0_pos.trans_le (P.aleph0_le hℓel)).ne'
  let a : A.model.carrier := hne.some
  have hx : (Sum.inl (iA.onVertex PUnit.unit a) : κ.ord.ToType ⊕ κ.ord.ToType) ∈ s0.e.R :=
    hA ⟨_, ⟨a, rfl⟩, rfl⟩
  have h := hseed.2.1 _ hx
  exact ⟨_, (infra_78_toArr_apply s0.hp _) ▸ h⟩

end PadSeed

section Full
variable (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
  {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ) {uIdx cIdx : Type u}
  {ρ : Cardinal.{u}} (hρκ : Order.succ ρ < μ)
  (Xb : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)) {ℓ : Cardinal.{u}}
  (hℓel : ℓ ∈ P.eligible)

include hρκ in
/-- **`infra_78_isolated_stage`** (Prop 7.8 proof: "some stage `i` with `cf(i) > λ` at which every
list of length `≤ θ` from `S_i` is isolated relative to `b`"), with `θ = |cIdx| ≤ λ`. In the
recursion matrix with `S`-part candidates indexed by `cIdx`, under the hypotheses of
`infra_78_isolated_stage_core` and a padding point in the seed set (`p_0(x) ∈ S_0`, supplied by
any closed seed via `infra_78_padSeed_of_closed`), there is a stage `i` with `λ < cf(i)` such that
for EVERY index type `J` with `|J| ≤ θ` (including `J = ∅`) and every `c : J → S_i`, the tuple
`(b_i, c)` is relatively isolated over `b_i`. Shorter lists are padded with a point `p_i(x_i) ∈ S_i`
and projected back (`infra_78_isolated_of_pad`, injective reindexing only). -/
theorem infra_78_isolated_stage (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (hcof : ∀ δ : (Order.succ ρ).ord.ToType, Order.IsSuccLimit δ →
      #uIdx < (Ordinal.ToType.toOrd δ).1.cof)
    (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ) (hc : #cIdx ≤ ℓ)
    (s0 : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
    (e0 : Infra78MarkData μ uIdx) (h5seed : infra_78_StageInv5 Xb s0)
    (hS0 : ∃ y, (Sum.inr y : μ.ord.ToType ⊕ μ.ord.ToType) ∈ s0.e.R) (h0 : #s0.e.R ≤ ρ)
    (hpad : ∃ x, (Sum.inr (s0.p x) : μ.ord.ToType ⊕ μ.ord.ToType) ∈ s0.e.R) :
    ∃ i : (Order.succ ρ).ord.ToType, ℓ < Order.cof (Set.Iio i) ∧
      ∀ (J : Type u), #J ≤ #cIdx → ∀ c : J → μ.ord.ToType,
        Set.range c ⊆ infra_78_Spart (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i) →
        IsRelativelyIsolated (infra_78_markTuple
          (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).hp)
          (Sum.elim (infra_78_stageMark (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i))
            (fun x => ⟨PUnit.unit, c x⟩)))
          (Equiv.refl (uIdx ⊕ J)) := by
  classical
  obtain ⟨i, hi, hiso⟩ := infra_78_isolated_stage_core P σ hσ hμT hρκ Xb hℓel hidx hcof hℓρ hpow hc
    s0 e0 h5seed hS0 h0
  refine ⟨i, hi, fun J hJ c hcS => ?_⟩
  obtain ⟨sJ⟩ := (Cardinal.le_def J cIdx).1 hJ
  obtain ⟨x0, hx0⟩ := infra_78_rc_padPoint hρκ Xb hℓel (infra_78_candS cIdx) s0 e0 hpad i
  let eK : cIdx ≃ J ⊕ ↥(Set.range sJ)ᶜ :=
    (Equiv.Set.sumCompl (Set.range sJ)).symm.trans
      (Equiv.sumCongr (Equiv.ofInjective sJ sJ.injective).symm (Equiv.refl _))
  let d : cIdx → μ.ord.ToType := fun k =>
    Sum.elim c (fun _ => (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).p x0) (eK k)
  have hd : Set.range d ⊆ infra_78_Spart (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i) := by
    rintro _ ⟨k, rfl⟩
    show Sum.elim c _ (eK k) ∈ _
    rcases eK k with j | kk
    · exact hcS ⟨j, rfl⟩
    · exact hx0
  have h := hiso d hd
  have hV : (infra_78_padTuple (infra_78_markTuple
      (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).hp)
      (Sum.elim (infra_78_stageMark (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i))
        (fun x => ⟨PUnit.unit, c x⟩))) (Equiv.refl (uIdx ⊕ J)) eK ⟨PUnit.unit, x0⟩).val =
      Sum.elim (infra_78_stageMark (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i))
          (fun x => ⟨PUnit.unit, d x⟩) := by
    funext t
    rcases t with u | k
    · rfl
    · show Sum.elim _ _ (eK k) = (⟨PUnit.unit, Sum.elim c
          (fun _ => (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).p x0) (eK k)⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem (Tail.mem (infra_73_tail P σ hσ) hμT)
            (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).Y))
      rcases eK k with j | kk
      · rfl
      · exact congrArg (fun y => (⟨PUnit.unit, y⟩ : Occurrence K oneVertexShape
          (P.scheme.asSystem (Tail.mem (infra_73_tail P σ hσ) hμT)
            (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).Y)))
          (infra_78_toArr_apply (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).hp x0)
  have h' : IsRelativelyIsolated (infra_78_markTuple
      (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).hp)
      (infra_78_padTuple (infra_78_markTuple
        (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).hp)
        (Sum.elim (infra_78_stageMark (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i))
          (fun x => ⟨PUnit.unit, c x⟩))) (Equiv.refl (uIdx ⊕ J)) eK ⟨PUnit.unit, x0⟩).val)
      (Equiv.refl (uIdx ⊕ cIdx)) := by
    rw [hV]; exact h
  have hμ0 : ℵ₀ ≤ μ := P.aleph0_le (Tail.mem (infra_73_tail P σ hσ) hμT)
  have hKp : #(↥(Set.range sJ)ᶜ) < μ :=
    (Cardinal.mk_subtype_le _).trans_lt (hc.trans_lt (hℓρ.trans
      ((Order.lt_succ_of_not_isMax (not_isMax ρ)).trans hρκ)))
  exact infra_78_isolated_of_pad (infra_78_markTuple
      (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).hp)
      (Sum.elim (infra_78_stageMark (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i))
        (fun x => ⟨PUnit.unit, c x⟩))) (Equiv.refl _) eK
    (⟨PUnit.unit, x0⟩ : Occurrence K oneVertexShape (P.scheme.asSystem
      (Tail.mem (infra_73_tail P σ hσ) hμT) (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).X))
    hμ0 hKp h'

end Full
end AEC
