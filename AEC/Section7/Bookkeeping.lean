module

public import AEC.Section7.TiedLocalCharacter
public import AEC.Section6.ProductTied

@[expose] public section

/-!
# Bookkeeping sets of Proposition 7.8 (`infra_78_bookkeeping_sets_instantiate`)

Instantiates the abstract `ρ⁺`-bookkeeping recursion (`infra_78_bookkeeping_sets_succ`) on a
given `ρ⁺` matrix `Infra78Matrix`: the carrier at stage `i` is `|X_i| ⊕ |Y_i|`, and every
small parameter set requests (0) its pair images, (1) a level-`λ` pair `A ≤ V` covering it
(`infra_78_mixed_ls_pair`, closure requirement 1) and (2) the copies of a Lemma 6.9
approximation sequence of length `λ` for its top points (`infra_78_code_copies_bounded`,
closure requirement 2). Each request adds at most `ρ` points (`infra_78_bkRequests_card`).

The instantiation uses only the commutation law of the matrix (pair closure at limit stages).
Requirement 1 at stages of cofinality `> λ` (`infra_78_bookkeeping_req1_high_cof`) takes the
composition law `Infra78Matrix.CompLaw` as an explicit hypothesis; requirement 2 at such stages
(`infra_78_bookkeeping_req2_high_cof`) also takes continuity at limits
`Infra78Matrix.ContAtLimits` (local character on the stage chain `infra_78_stageChain`). Both are
tracked obligations of `infra_78_matrix_construction`, not hidden assumptions. The combined
statement is `infra_78_bookkeeping_assembly`.

Stage-local form (`infra_78_pair_bookkeeping_close`): for a single pair `X → Y` and any `T` of
size `≤ ρ`, a closed `T' ⊇ T` of size `≤ ρ`; it depends only on the current pair, so the
bookkeeping can be interleaved with the matrix recursion (`infra_78_matrix_recursion`).
-/

universe u

open Cardinal Classical

namespace AEC
variable {K : AbstractElementaryClass.{u}}

/-- A chosen witness set of size at most `ρ` for `Q`, or `∅`. -/
noncomputable def infra_78_pick {E : Type u} (ρ : Cardinal.{u}) (Q : Set E → Prop) : Set E :=
  if h : ∃ T : Set E, #T ≤ ρ ∧ Q T then Classical.choose h else ∅

theorem infra_78_pick_card {E : Type u} (ρ : Cardinal.{u}) (Q : Set E → Prop) :
    #(infra_78_pick ρ Q) ≤ ρ := by
  unfold infra_78_pick
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · simp

theorem infra_78_pick_spec {E : Type u} {ρ : Cardinal.{u}} {Q : Set E → Prop}
    (h : ∃ T : Set E, #T ≤ ρ ∧ Q T) : Q (infra_78_pick ρ Q) := by
  unfold infra_78_pick
  split_ifs
  exact (Classical.choose_spec h).2

section
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}
  (M : Infra78Matrix P ρ hκ)

/-- Bookkeeping carrier at stage `i`: base points (left) and top points (right). -/
abbrev infra_78_bkCarrier (i : (Order.succ ρ).ord.ToType) : Type u :=
  (M.X i).model.carrier ⊕ (M.Y i).model.carrier

/-- Forward map of bookkeeping carriers. -/
def infra_78_bkStep {j i : (Order.succ ρ).ord.ToType} (h : j < i) :
    infra_78_bkCarrier M j → infra_78_bkCarrier M i :=
  Sum.map ((M.stepX h.le).onVertex PUnit.unit) ((M.stepY h.le).onVertex PUnit.unit)

/-- The tuple of top points of `s` over the base `X_i` (realized in `Y_i`). -/
def infra_78_bkTuple (i : (Order.succ ρ).ord.ToType) (s : Set (infra_78_bkCarrier M i)) :
    TupleOver K oneVertexShape P.scheme hκ (M.X i) :=
  ⟨κ, hκ, M.Y i, M.pair i, M.pair_permitted i, (Sum.inr ⁻¹' s : Set _),
    fun k => (M.Y i).occ k.1⟩

/-- Closure requirement 1 request: a level-`ℓ` pair over the small parameter set `s`. -/
def infra_78_bkLsReq {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible) (i : (Order.succ ρ).ord.ToType)
    (s T : Set (infra_78_bkCarrier M i)) : Prop :=
  ∃ (A V : P.scheme.Object ℓ hℓel)
    (iA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hκ (M.X i)))
    (iV : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel V) (P.scheme.asSystem hκ (M.Y i)))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hℓel V)),
    P.scheme.permitted (X := A) (Y := M.X i) iA ∧
    P.scheme.permitted (X := V) (Y := M.Y i) iV ∧
    P.scheme.permitted (X := A) (Y := V) g ∧
    (∀ v, (iV.onVertex v).comp (g.onVertex v) = ((M.pair i).onVertex v).comp (iA.onVertex v)) ∧
    Sum.inl ⁻¹' s ⊆ Set.range (iA.onVertex PUnit.unit) ∧
    Sum.inr ⁻¹' s ⊆ Set.range (iV.onVertex PUnit.unit) ∧
    T = Sum.inl '' Set.range (iA.onVertex PUnit.unit) ∪
      Sum.inr '' Set.range (iV.onVertex PUnit.unit)

/-- Closure requirement 2 request: the copies of a Lemma 6.9 sequence of length `ℓ`. -/
def infra_78_bkCopyReq (ℓ : Cardinal.{u}) (i : (Order.succ ρ).ord.ToType)
    (s T : Set (infra_78_bkCarrier M i)) : Prop :=
  ∃ seq : ApproximationSequence (infra_78_bkTuple M i s), seq.τ = ℓ ∧
    ℓ + ℵ₀ < #seq.κIndex ∧ T = Set.range (fun ab : seq.κIndex × (infra_78_bkTuple M i s).idx =>
      (Sum.inl ((M.X i).val (seq.family ab.1 ab.2)) : infra_78_bkCarrier M i))

/-- All requests of a small parameter set: pair images, a level-`ℓ` pair, Lemma 6.9 copies. -/
noncomputable def infra_78_bkRequests {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (i : (Order.succ ρ).ord.ToType) (s : Set (infra_78_bkCarrier M i)) :
    Set (infra_78_bkCarrier M i) :=
  (Sum.inr '' ((M.pair i).onVertex PUnit.unit '' (Sum.inl ⁻¹' s))) ∪
    infra_78_pick ρ (infra_78_bkLsReq M hℓel i s) ∪ infra_78_pick ρ (infra_78_bkCopyReq M ℓ i s)

theorem infra_78_bkRequests_card {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible) (hℓρ : ℓ < ρ)
    (hρ : ℵ₀ ≤ ρ) (i : (Order.succ ρ).ord.ToType) (s : Set (infra_78_bkCarrier M i))
    (hs : #s ≤ ℓ) : #(infra_78_bkRequests M hℓel i s) ≤ ρ := by
  have h1 : #(Sum.inr '' ((M.pair i).onVertex PUnit.unit '' (Sum.inl ⁻¹' s)) :
      Set (infra_78_bkCarrier M i)) ≤ ρ :=
    Cardinal.mk_image_le.trans (Cardinal.mk_image_le.trans
      ((Cardinal.mk_preimage_of_injective _ _ Sum.inl_injective).trans (hs.trans hℓρ.le)))
  refine (mk_union_le _ _).trans ?_
  refine (add_le_add ((mk_union_le _ _).trans (add_le_add h1 (infra_78_pick_card _ _)))
    (infra_78_pick_card _ _)).trans ?_
  rw [add_eq_self hρ, add_eq_self hρ]

/-- Forward maps preserve the left/right summands and commute with the pair arrows. -/
theorem infra_78_bkStep_pair {j i : (Order.succ ρ).ord.ToType} (h : j < i)
    (x : (M.X j).model.carrier) :
    (M.stepY h.le).onVertex PUnit.unit ((M.pair j).onVertex PUnit.unit x) =
      (M.pair i).onVertex PUnit.unit ((M.stepX h.le).onVertex PUnit.unit x) := by
  have := congrArg (fun a => a.onVertex PUnit.unit x) (M.comm h.le)
  exact this

/-- **Bookkeeping sets for a given `ρ⁺` matrix (Prop 7.8 proof, instantiation).** -/
theorem infra_78_bookkeeping_sets_instantiate {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (hℓκ : ℓ ≤ κ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    (seed : ∀ i, Set (infra_78_bkCarrier M i)) (hseed : ∀ i, #(seed i) ≤ ρ) :
    ∃ R : ∀ i, Set (infra_78_bkCarrier M i),
      (∀ i, #(R i) ≤ ρ) ∧
      (∀ {j i} (h : j < i), infra_78_bkStep M h '' R j ⊆ R i) ∧
      (∀ i, Order.IsSuccLimit i → R i = ⋃ j : Set.Iio i, infra_78_bkStep M j.2 '' R j.1) ∧
      (∀ i, ¬ Order.IsSuccLimit i → seed i ⊆ R i) ∧
      (∀ i x, (Sum.inl x : infra_78_bkCarrier M i) ∈ R i →
        (Sum.inr ((M.pair i).onVertex PUnit.unit x) : infra_78_bkCarrier M i) ∈ R i) ∧
      (∀ i, ¬ Order.IsSuccLimit i → ∀ s ⊆ R i, #s ≤ ℓ →
        ∃ (A V : P.scheme.Object ℓ hℓel)
          (iA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A)
            (P.scheme.asSystem hκ (M.X i)))
          (iV : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel V)
            (P.scheme.asSystem hκ (M.Y i)))
          (g : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A)
            (P.scheme.asSystem hℓel V)),
          P.scheme.permitted (X := A) (Y := M.X i) iA ∧
          P.scheme.permitted (X := V) (Y := M.Y i) iV ∧
          P.scheme.permitted (X := A) (Y := V) g ∧
          (∀ v, (iV.onVertex v).comp (g.onVertex v) =
            ((M.pair i).onVertex v).comp (iA.onVertex v)) ∧
          Sum.inl ⁻¹' s ⊆ Set.range (iA.onVertex PUnit.unit) ∧
          Sum.inr ⁻¹' s ⊆ Set.range (iV.onVertex PUnit.unit) ∧
          Sum.inl '' Set.range (iA.onVertex PUnit.unit) ⊆ R i ∧
          Sum.inr '' Set.range (iV.onVertex PUnit.unit) ⊆ R i) ∧
      (∀ i, ¬ Order.IsSuccLimit i → ∀ σ : Cardinal.{u}, ℵ₀ ≤ σ →
          κ ∈ recursionClosedLevels P σ → Order.succ σ ≤ κ → ℓ < κ →
          ∀ s ⊆ R i, #s ≤ ℓ → #(Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) ≤ σ →
          ∃ seq : ApproximationSequence (infra_78_bkTuple M i s), seq.τ = ℓ ∧
            ℓ + ℵ₀ < #seq.κIndex ∧ ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ R i) := by
  have hℓ : ℵ₀ ≤ ℓ := P.aleph0_le hℓel
  have hρ : ℵ₀ ≤ ρ := hℓ.trans hℓρ.le
  obtain ⟨R, hcard, hmono, hlim, hsucc⟩ := infra_78_bookkeeping_sets_succ
    (infra_78_bkCarrier M) (fun h => infra_78_bkStep M h) (infra_78_bkRequests M hℓel) seed
    hℓ hℓρ hpow (fun i s hs => infra_78_bkRequests_card M hℓel hℓρ hρ i s hs) hseed
  have hreq : ∀ i, ¬ Order.IsSuccLimit i → ∀ s ⊆ R i, #s ≤ ℓ →
      infra_78_bkRequests M hℓel i s ⊆ R i := fun i hi => (hsucc i hi).2
  -- pair closure at every stage, by well-founded induction
  have hpair : ∀ i x, (Sum.inl x : infra_78_bkCarrier M i) ∈ R i →
      (Sum.inr ((M.pair i).onVertex PUnit.unit x) : infra_78_bkCarrier M i) ∈ R i := by
    intro i
    induction i using WellFoundedLT.induction with
    | _ i IH =>
      intro x hx
      by_cases hi : Order.IsSuccLimit i
      · rw [hlim i hi] at hx
        obtain ⟨⟨j, hj⟩, z, hz, hzx⟩ := Set.mem_iUnion.1 hx
        rcases z with x' | y'
        · have hzx' : (M.stepX (le_of_lt hj)).onVertex PUnit.unit x' = x := Sum.inl_injective hzx
          subst hzx'
          have h1 := IH j hj x' hz
          have h2 := hmono hj ⟨_, h1, rfl⟩
          rw [← infra_78_bkStep_pair M hj]
          exact h2
        · exact (Sum.inr_ne_inl hzx).elim
      · have hs : ({Sum.inl x} : Set (infra_78_bkCarrier M i)) ⊆ R i :=
          Set.singleton_subset_iff.2 hx
        have hsl : #({Sum.inl x} : Set (infra_78_bkCarrier M i)) ≤ ℓ := by
          rw [Cardinal.mk_singleton]; exact one_le_aleph0.trans hℓ
        apply hreq i hi _ hs hsl
        left; left
        exact ⟨_, ⟨x, Set.mem_singleton _, rfl⟩, rfl⟩
  refine ⟨R, hcard, hmono, hlim, fun i hi => (hsucc i hi).1, hpair, ?_, ?_⟩
  · intro i hi s hs hsl
    have hS : #(Sum.inl ⁻¹' s : Set (M.X i).model.carrier) ≤ ℓ :=
      (Cardinal.mk_preimage_of_injective _ _ Sum.inl_injective).trans hsl
    have hT : #(Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) ≤ ℓ :=
      (Cardinal.mk_preimage_of_injective _ _ Sum.inr_injective).trans hsl
    have hex : ∃ T : Set (infra_78_bkCarrier M i), #T ≤ ρ ∧ infra_78_bkLsReq M hℓel i s T := by
      obtain ⟨A, V, iA, iV, g, h1, h2, h3, h4, h5, h6⟩ :=
        infra_78_mixed_ls_pair hℓel hκ hℓκ (M.pair i) _ _ hS hT
      refine ⟨_, ?_, A, V, iA, iV, g, h1, h2, h3, h4, h5, h6, rfl⟩
      refine (mk_union_le _ _).trans ?_
      have eA : #(Set.range (iA.onVertex PUnit.unit)) ≤ ℓ :=
        Cardinal.mk_range_le.trans (le_of_eq A.card)
      have eV : #(Set.range (iV.onVertex PUnit.unit)) ≤ ℓ :=
        Cardinal.mk_range_le.trans (le_of_eq V.card)
      refine (add_le_add (Cardinal.mk_image_le.trans eA) (Cardinal.mk_image_le.trans eV)).trans ?_
      rw [add_eq_self hℓ]; exact hℓρ.le
    obtain ⟨A, V, iA, iV, g, h1, h2, h3, h4, h5, h6, hT⟩ := infra_78_pick_spec hex
    have hsub : infra_78_pick ρ (infra_78_bkLsReq M hℓel i s) ⊆ R i := fun z hz =>
      hreq i hi s hs hsl (Or.inl (Or.inr hz))
    rw [hT] at hsub
    exact ⟨A, V, iA, iV, g, h1, h2, h3, h4, h5, h6,
      fun z hz => hsub (Or.inl hz), fun z hz => hsub (Or.inr hz)⟩
  · intro i hi σ hσ hrec hσSucc hℓκ' s hs hsl hσs
    have hidxℓ : #(infra_78_bkTuple M i s).idx ≤ ℓ :=
      (Cardinal.mk_preimage_of_injective _ _ Sum.inr_injective).trans hsl
    have hex : ∃ T : Set (infra_78_bkCarrier M i), #T ≤ ρ ∧ infra_78_bkCopyReq M ℓ i s T := by
      obtain ⟨seq, hτ, hκI, hprod⟩ := infra_78_code_copies_bounded P σ hσ hκ hrec hσSucc
        (infra_78_bkTuple M i s) rfl hσs hℓ hℓκ' hidxℓ
      refine ⟨_, Cardinal.mk_range_le.trans (hprod.trans (Order.succ_le_of_lt hℓρ)), seq, hτ,
        ?_, rfl⟩
      rw [hκI, Cardinal.add_eq_left hℓ hℓ]
      exact Order.lt_succ_of_not_isMax (not_isMax ℓ)
    obtain ⟨seq, hτ, hlen, hT⟩ := infra_78_pick_spec hex
    have hsub : infra_78_pick ρ (infra_78_bkCopyReq M ℓ i s) ⊆ R i := fun z hz =>
      hreq i hi s hs hsl (Or.inr hz)
    rw [hT] at hsub
    exact ⟨seq, hτ, hlen, fun a b => hsub ⟨(a, b), rfl⟩⟩

end
section
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}
  (M : Infra78Matrix P ρ hκ)

/-- The composition law of a `ρ⁺` matrix (an obligation of `infra_78_matrix_construction`). -/
def Infra78Matrix.CompLaw : Prop :=
  (∀ {a b c : (Order.succ ρ).ord.ToType} (h₁ : a ≤ b) (h₂ : b ≤ c),
    M.stepX (h₁.trans h₂) = SystemArrow.comp (M.stepX h₁) (M.stepX h₂)) ∧
  (∀ {a b c : (Order.succ ρ).ord.ToType} (h₁ : a ≤ b) (h₂ : b ≤ c),
    M.stepY (h₁.trans h₂) = SystemArrow.comp (M.stepY h₁) (M.stepY h₂))

theorem infra_78_bkStep_trans (hM : M.CompLaw) {a b c : (Order.succ ρ).ord.ToType}
    (h₁ : a < b) (h₂ : b < c) (z : infra_78_bkCarrier M a) :
    infra_78_bkStep M (h₁.trans h₂) z = infra_78_bkStep M h₂ (infra_78_bkStep M h₁ z) := by
  rcases z with x | y
  · exact congrArg Sum.inl (congrArg (fun f => f.onVertex PUnit.unit x) (hM.1 h₁.le h₂.le))
  · exact congrArg Sum.inr (congrArg (fun f => f.onVertex PUnit.unit y) (hM.2 h₁.le h₂.le))

/-- Closure requirement 1 for a small `s` inside the bookkeeping set `T` at stage `i`. -/
def infra_78_bkReq1 {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible) (i : (Order.succ ρ).ord.ToType)
    (s T : Set (infra_78_bkCarrier M i)) : Prop :=
  ∃ (A V : P.scheme.Object ℓ hℓel)
    (iA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hκ (M.X i)))
    (iV : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel V) (P.scheme.asSystem hκ (M.Y i)))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hℓel V)),
    P.scheme.permitted (X := A) (Y := M.X i) iA ∧
    P.scheme.permitted (X := V) (Y := M.Y i) iV ∧
    P.scheme.permitted (X := A) (Y := V) g ∧
    (∀ v, (iV.onVertex v).comp (g.onVertex v) = ((M.pair i).onVertex v).comp (iA.onVertex v)) ∧
    Sum.inl ⁻¹' s ⊆ Set.range (iA.onVertex PUnit.unit) ∧
    Sum.inr ⁻¹' s ⊆ Set.range (iV.onVertex PUnit.unit) ∧
    Sum.inl '' Set.range (iA.onVertex PUnit.unit) ⊆ T ∧
    Sum.inr '' Set.range (iV.onVertex PUnit.unit) ⊆ T

/-- **Closure requirement 1 at stages of cofinality `> λ` (Prop 7.8 proof).** Given bookkeeping
sets that are forward-closed, continuous at limits and satisfy requirement 1 at non-limit stages
(as produced by `infra_78_bookkeeping_sets_instantiate`), and the matrix composition law,
requirement 1 holds at every stage `i` with `cf(i) > λ`. -/
theorem infra_78_bookkeeping_req1_high_cof (hM : M.CompLaw) {ℓ : Cardinal.{u}}
    (hℓel : ℓ ∈ P.eligible) (R : ∀ i, Set (infra_78_bkCarrier M i))
    (hmono : ∀ {j i} (h : j < i), infra_78_bkStep M h '' R j ⊆ R i)
    (hlim : ∀ i, Order.IsSuccLimit i → R i = ⋃ j : Set.Iio i, infra_78_bkStep M j.2 '' R j.1)
    (hsupp : ∀ i, ¬ Order.IsSuccLimit i → ∀ s ⊆ R i, #s ≤ ℓ → infra_78_bkReq1 M hℓel i s (R i))
    (i : (Order.succ ρ).ord.ToType) (hcof : ℓ < Order.cof (Set.Iio i))
    (s : Set (infra_78_bkCarrier M i)) (hs : s ⊆ R i) (hsl : #s ≤ ℓ) :
    infra_78_bkReq1 M hℓel i s (R i) := by
  by_cases hi : Order.IsSuccLimit i
  swap
  · exact hsupp i hi s hs hsl
  -- stage family seen from `i`
  let S : (Order.succ ρ).ord.ToType → Set (infra_78_bkCarrier M i) := fun j =>
    if h : j < i then infra_78_bkStep M h '' R j else if j = i then R i else Set.univ
  have hSlt : ∀ j (h : j < i), S j = infra_78_bkStep M h '' R j := fun j h => by
    simp only [S, h, ↓reduceDIte]
  have hSi' : S i = R i := by simp only [S, lt_irrefl, ↓reduceDIte, ↓reduceIte]
  have hSgt : ∀ j, i < j → S j = Set.univ := fun j h => by
    simp only [S, not_lt.2 h.le, h.ne', ↓reduceDIte, ↓reduceIte]
  have hSmono : Monotone S := by
    intro a b hab
    rcases lt_trichotomy b i with hb | hb | hb
    · have ha := lt_of_le_of_lt hab hb
      rw [hSlt a ha, hSlt b hb]
      rcases hab.lt_or_eq with hab' | hab'
      · rintro _ ⟨z, hz, rfl⟩
        refine ⟨infra_78_bkStep M hab' z, hmono hab' ⟨z, hz, rfl⟩, ?_⟩
        exact (infra_78_bkStep_trans M hM hab' hb z).symm
      · subst hab'; exact le_rfl
    · subst hb
      rw [hSi']
      rcases hab.lt_or_eq with ha | ha
      · rw [hSlt a ha]; exact hmono ha
      · subst ha; rw [hSi']
    · rw [hSgt b hb]; exact Set.subset_univ _
  have hSi : S i ⊆ ⋃ j ∈ Set.Iio i, S j := by
    rw [hSi', hlim i hi]
    intro x hx
    obtain ⟨⟨j, hj⟩, hx⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_biUnion hj (by rw [hSlt j hj]; exact hx)
  have hsS : s ⊆ S i := by rw [hSi']; exact hs
  obtain ⟨j, hj, hsj⟩ := infra_78_bounded_in_earlier_stage S hSmono hSi hsS hsl hcof
  rw [hSlt j hj] at hsj
  -- move to the non-limit stage `k = succ j < i`
  set k := Order.succ j with hkdef
  have hjk : j < k := Order.lt_succ_of_not_isMax hj.not_isMax
  have hki : k < i := (Order.IsSuccLimit.succ_lt_iff hi).mpr hj
  have hk : ¬ Order.IsSuccLimit k := fun hl =>
    hl.isSuccPrelimit j (Order.covBy_succ_of_not_isMax hj.not_isMax)
  have hsk : s ⊆ infra_78_bkStep M hki '' R k := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hsj hx
    exact ⟨infra_78_bkStep M hjk z, hmono hjk ⟨z, hz, rfl⟩,
      (infra_78_bkStep_trans M hM hjk hki z).symm⟩
  -- a small preimage inside `R k`
  have hpre : ∀ x : s, ∃ z ∈ R k, infra_78_bkStep M hki z = x.1 := fun x => hsk x.2
  choose pre hpreR hpreEq using hpre
  set s' : Set (infra_78_bkCarrier M k) := Set.range pre
  have hs'R : s' ⊆ R k := by rintro _ ⟨x, rfl⟩; exact hpreR x
  have hs'l : #s' ≤ ℓ := Cardinal.mk_range_le.trans hsl
  obtain ⟨A, V, iA, iV, g, -, -, -, hcomm, hcovA, hcovV, hinA, hinV⟩ := hsupp k hk s' hs'R hs'l
  refine ⟨A, V, SystemArrow.comp iA (M.stepX hki.le), SystemArrow.comp iV (M.stepY hki.le), g,
    trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    ext a
    have h1 : (iV.onVertex v) (g.onVertex v a) = ((M.pair k).onVertex v) (iA.onVertex v a) :=
      congrArg (fun e => e a) (hcomm v)
    have h2 := congrArg (fun f => f.onVertex v ((iA.onVertex v) a)) (M.comm hki.le)
    change (M.stepY hki.le).onVertex v ((iV.onVertex v) (g.onVertex v a)) =
      (M.pair i).onVertex v ((M.stepX hki.le).onVertex v (iA.onVertex v a))
    rw [h1]; exact h2
  · intro x hx
    have hw := hpreEq ⟨_, hx⟩
    have hwR := hpreR ⟨_, hx⟩
    rcases hpw : pre ⟨_, hx⟩ with y | y
    · rw [hpw] at hw
      have hy : y ∈ Sum.inl ⁻¹' s' := by
        show Sum.inl y ∈ s'; rw [← hpw]; exact ⟨_, rfl⟩
      obtain ⟨a, rfl⟩ := hcovA hy
      exact ⟨a, Sum.inl_injective hw⟩
    · rw [hpw] at hw; exact (Sum.inr_ne_inl hw).elim
  · intro x hx
    rcases hpw : pre ⟨_, hx⟩ with y | y
    · have hw := hpreEq ⟨_, hx⟩; rw [hpw] at hw; exact (Sum.inl_ne_inr hw).elim
    · have hw := hpreEq ⟨_, hx⟩
      rw [hpw] at hw
      have hy : y ∈ Sum.inr ⁻¹' s' := by
        show Sum.inr y ∈ s'; rw [← hpw]; exact ⟨_, rfl⟩
      obtain ⟨a, rfl⟩ := hcovV hy
      exact ⟨a, Sum.inr_injective hw⟩
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hmono hki ⟨_, hinA ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hmono hki ⟨_, hinV ⟨_, ⟨a, rfl⟩, rfl⟩, rfl⟩

/-- Bookkeeping sets with requirement 1 at every stage of cofinality `> λ` (combining
`infra_78_bookkeeping_sets_instantiate` with `infra_78_bookkeeping_req1_high_cof`). -/
theorem infra_78_bookkeeping_sets_req1 (hM : M.CompLaw) {ℓ : Cardinal.{u}}
    (hℓel : ℓ ∈ P.eligible) (hℓκ : ℓ ≤ κ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    (seed : ∀ i, Set (infra_78_bkCarrier M i)) (hseed : ∀ i, #(seed i) ≤ ρ) :
    ∃ R : ∀ i, Set (infra_78_bkCarrier M i),
      (∀ i, #(R i) ≤ ρ) ∧
      (∀ {j i} (h : j < i), infra_78_bkStep M h '' R j ⊆ R i) ∧
      (∀ i, Order.IsSuccLimit i → R i = ⋃ j : Set.Iio i, infra_78_bkStep M j.2 '' R j.1) ∧
      (∀ i, ¬ Order.IsSuccLimit i → seed i ⊆ R i) ∧
      (∀ i x, (Sum.inl x : infra_78_bkCarrier M i) ∈ R i →
        (Sum.inr ((M.pair i).onVertex PUnit.unit x) : infra_78_bkCarrier M i) ∈ R i) ∧
      (∀ i, (¬ Order.IsSuccLimit i ∨ ℓ < Order.cof (Set.Iio i)) → ∀ s ⊆ R i, #s ≤ ℓ →
        infra_78_bkReq1 M hℓel i s (R i)) := by
  obtain ⟨R, hcard, hmono, hlim, hseedR, hpair, hsupp, -⟩ :=
    infra_78_bookkeeping_sets_instantiate M hℓel hℓκ hℓρ hpow seed hseed
  refine ⟨R, hcard, hmono, hlim, hseedR, hpair, ?_⟩
  rintro i (hi | hcof) s hs hsl
  · exact hsupp i hi s hs hsl
  · exact infra_78_bookkeeping_req1_high_cof M hM hℓel R hmono hlim hsupp i hcof s hs hsl

end

/-- **Approximation sequences transfer along a host arrow.** If `h : host₁ → host₂` is
permitted, commutes with the inclusions of the common base, and carries the tuple of `p₁` to
that of `p₂` (along `e`), every approximation sequence of `p₁` (with bounded joints) is one of
`p₂`, with the same test size, index and copies. -/
noncomputable def infra_78_seq_host_transfer {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {B : P.scheme.Object μ hμ}
    (p₁ p₂ : TupleOver K oneVertexShape P.scheme hμ B)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem p₁.hν p₁.host)
      (P.scheme.asSystem p₂.hν p₂.host))
    (hh : P.scheme.permitted (X := p₁.host) (Y := p₂.host) h) (e : p₁.idx ≃ p₂.idx)
    (hincl : ∀ x, h.onVertex PUnit.unit (p₁.incl.onVertex PUnit.unit x) =
      p₂.incl.onVertex PUnit.unit x)
    (hval : ∀ k, p₂.val (e k) = ⟨(p₁.val k).1, h.onVertex (p₁.val k).1 (p₁.val k).2⟩)
    (s : ApproximationSequence p₁) (hb₁ : #p₁.idx + s.τ < p₁.ν) (hb₂ : #p₁.idx + s.τ < p₂.ν) :
    ApproximationSequence p₂ where
  τ := s.τ
  κIndex := s.κIndex
  family := fun j k => s.family j (e.symm k)
  concat_bounded := by
    rw [← Cardinal.mk_congr (Equiv.prodCongr (Equiv.refl s.κIndex) e)]
    exact s.concat_bounded
  few_exceptions := fun {ι} Z hZ => by
    classical
    refine le_trans ?_ (s.few_exceptions Z hZ)
    refine Cardinal.mk_le_of_injective (f := fun j => ⟨j.1, fun hgood => j.2 ?_⟩)
      (by
        intro j₁ j₂ hj
        apply Subtype.ext
        have := congrArg Subtype.val hj
        exact this)
    have hcard : #(p₁.idx ⊕ ι) < p₁.ν ∧ #(p₁.idx ⊕ ι) < p₂.ν := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      have : #p₁.idx + #ι ≤ #p₁.idx + s.τ := add_le_add le_rfl hZ
      exact ⟨this.trans_lt hb₁, this.trans_lt hb₂⟩
    have hpres := P.scheme.diagram_preserved p₁.host p₂.host h hh
      (typeJoint (p := p₁) Z) hcard.1 hcard.2
    have e3 := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ hpres) hgood
    refine infra_612_dEq_transport e3 (Equiv.sumCongr e.symm (Equiv.refl ι)) ?_ ?_
    · rintro (k | c)
      · show p₂.val k = _
        have := hval (e.symm k)
        rw [Equiv.apply_symm_apply] at this
        exact this
      · show (⟨(Z c).1, p₂.incl.onVertex (Z c).1 (Z c).2⟩ :
            Occurrence K oneVertexShape (P.scheme.asSystem p₂.hν p₂.host)) = _
        exact (congrArg (fun y => (⟨(Z c).1, y⟩ :
            Occurrence K oneVertexShape (P.scheme.asSystem p₂.hν p₂.host)))
          (hincl (Z c).2)).symm
    · rintro (k | c) <;> rfl

section
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}
  (M : Infra78Matrix P ρ hκ)

/-- Continuity of a `ρ⁺` matrix at limits (Def 7.7 continuous pairs; an obligation of
`infra_78_matrix_construction`): at a limit stage every element of `X_i` and of `Y_i` comes
from an earlier stage. -/
def Infra78Matrix.ContAtLimits : Prop :=
  (∀ i : (Order.succ ρ).ord.ToType, Order.IsSuccLimit i → ∀ x : (M.X i).model.carrier,
    ∃ j, ∃ h : j < i, ∃ y, (M.stepX h.le).onVertex PUnit.unit y = x) ∧
  (∀ i : (Order.succ ρ).ord.ToType, Order.IsSuccLimit i → ∀ x : (M.Y i).model.carrier,
    ∃ j, ∃ h : j < i, ∃ y, (M.stepY h.le).onVertex PUnit.unit y = x)

/-- The stage of the matrix with ordinal index `α` below the ordinal of `i`. -/
noncomputable def infra_78_stg (i : (Order.succ ρ).ord.ToType) (α : Ordinal.{u})
    (hα : α < (Ordinal.ToType.toOrd i).1) : (Order.succ ρ).ord.ToType :=
  Ordinal.ToType.mk ⟨α, hα.trans (Ordinal.ToType.toOrd i).2⟩

theorem infra_78_stg_lt (i : (Order.succ ρ).ord.ToType) (α : Ordinal.{u})
    (hα : α < (Ordinal.ToType.toOrd i).1) : infra_78_stg (ρ := ρ) i α hα < i := by
  have : Ordinal.ToType.mk (Ordinal.ToType.toOrd i) = i := Ordinal.ToType.mk.apply_symm_apply i
  conv_rhs => rw [← this]
  exact Ordinal.ToType.mk.lt_iff_lt.2 hα

theorem infra_78_stg_mono (i : (Order.succ ρ).ord.ToType) {α β : Ordinal.{u}}
    (hα : α < (Ordinal.ToType.toOrd i).1) (hβ : β < (Ordinal.ToType.toOrd i).1) (h : α ≤ β) :
    infra_78_stg (ρ := ρ) i α hα ≤ infra_78_stg i β hβ :=
  Ordinal.ToType.mk.le_iff_le.2 h

theorem infra_78_stg_surj (i j : (Order.succ ρ).ord.ToType) (hj : j < i) :
    ∃ α, ∃ hα : α < (Ordinal.ToType.toOrd i).1, infra_78_stg (ρ := ρ) i α hα = j :=
  ⟨(Ordinal.ToType.toOrd j).1, Ordinal.ToType.mk.symm.lt_iff_lt.2 hj,
    Ordinal.ToType.mk.apply_symm_apply j⟩

theorem infra_78_stg_ord_limit (i : (Order.succ ρ).ord.ToType) (hi : Order.IsSuccLimit i) :
    (0 : Ordinal.{u}) < (Ordinal.ToType.toOrd i).1 ∧
      Order.IsSuccLimit (Ordinal.ToType.toOrd i).1 := by
  have hne : (Ordinal.ToType.toOrd i).1 ≠ 0 := by
    intro h0
    apply hi.not_isMin
    intro j _
    have : (Ordinal.ToType.toOrd i) ≤ Ordinal.ToType.toOrd j := by
      show (Ordinal.ToType.toOrd i).1 ≤ (Ordinal.ToType.toOrd j).1
      rw [h0]; exact zero_le
    exact Ordinal.ToType.mk.symm.le_iff_le.1 this
  refine ⟨pos_iff_ne_zero.2 hne, ?_⟩
  rw [Order.isSuccLimit_iff]
  refine ⟨fun hm => hne (hm.eq_bot), ?_⟩
  intro b hb
  have hbδ : b < (Ordinal.ToType.toOrd i).1 := hb.lt
  apply hi.isSuccPrelimit (infra_78_stg i b hbδ)
  refine ⟨infra_78_stg_lt i b hbδ, fun c hbc hci => ?_⟩
  have h1 : b < (Ordinal.ToType.toOrd c).1 := by
    have := Ordinal.ToType.mk.symm.lt_iff_lt.2 hbc
    simp only [infra_78_stg, OrderIso.symm_apply_apply] at this
    exact this
  have h2 : (Ordinal.ToType.toOrd c).1 < (Ordinal.ToType.toOrd i).1 :=
    Ordinal.ToType.mk.symm.lt_iff_lt.2 hci
  exact hb.2 h1 h2

/-- The stages below a limit `i` as a `SameLevelChain` with union `X_i` (needs the composition
law and continuity at limits). -/
noncomputable def infra_78_stageChain (hM : M.CompLaw) (hC : M.ContAtLimits)
    (i : (Order.succ ρ).ord.ToType) (hi : Order.IsSuccLimit i) : SameLevelChain P hκ where
  δ := (Ordinal.ToType.toOrd i).1
  hlim := infra_78_stg_ord_limit i hi
  obj α hα := M.X (infra_78_stg i α hα)
  le hα hβ h := M.stepX (infra_78_stg_mono i hα hβ h)
  le_arrow _ _ _ := trivial
  le_comp hα hβ hγ h₁ h₂ := (hM.1 _ _).symm
  unionObj := M.X i
  toUnion α hα := M.stepX (infra_78_stg_lt i α hα).le
  toUnion_arrow _ _ := trivial
  toUnion_comp hα hβ h := (hM.1 _ _).symm
  joint x := by
    obtain ⟨j, hj, y, hy⟩ := hC.1 i hi x.2
    obtain ⟨α, hα, rfl⟩ := infra_78_stg_surj i j hj
    exact ⟨α, hα, ⟨PUnit.unit, y⟩, by
      show (⟨PUnit.unit, _⟩ : Σ _ : PUnit, _) = x
      rw [hy]
      rfl⟩

theorem infra_78_stageChain_cof (hM : M.CompLaw) (hC : M.ContAtLimits)
    (i : (Order.succ ρ).ord.ToType) (hi : Order.IsSuccLimit i) :
    (infra_78_stageChain M hM hC i hi).δ.cof = Order.cof (Set.Iio i) := by
  show (Ordinal.ToType.toOrd i).1.cof = _
  let f : Set.Iio i → Set.Iio (Ordinal.ToType.toOrd i).1 := fun j =>
    ⟨(Ordinal.ToType.toOrd j.1).1, Ordinal.ToType.mk.symm.lt_iff_lt.2 j.2⟩
  have hf : StrictMono f := fun a b hab => by
    show (Ordinal.ToType.toOrd a.1).1 < (Ordinal.ToType.toOrd b.1).1
    exact Ordinal.ToType.mk.symm.lt_iff_lt.2 hab
  have hfs : Function.Surjective f := by
    intro α
    refine ⟨⟨infra_78_stg i α.1 α.2, infra_78_stg_lt i α.1 α.2⟩, ?_⟩
    apply Subtype.ext
    show (Ordinal.ToType.mk.symm (Ordinal.ToType.mk _)).1 = α.1
    rw [OrderIso.symm_apply_apply]
  have e := (hf.orderIsoOfSurjective f hfs).trans Ordinal.ToType.mk
  rw [OrderIso.cof_congr e, Ordinal.cof_toType]

/-- Pull a small subset of `R_i` at a limit of cofinality `> λ` back to a non-limit stage
`k` above a given `j₀ < i` (composition law). -/
theorem infra_78_bk_pull (hM : M.CompLaw) {ℓ : Cardinal.{u}} (R : ∀ i, Set (infra_78_bkCarrier M i))
    (hmono : ∀ {j i} (h : j < i), infra_78_bkStep M h '' R j ⊆ R i)
    (hlim : ∀ i, Order.IsSuccLimit i → R i = ⋃ j : Set.Iio i, infra_78_bkStep M j.2 '' R j.1)
    (i : (Order.succ ρ).ord.ToType) (hi : Order.IsSuccLimit i) (hcof : ℓ < Order.cof (Set.Iio i))
    (s : Set (infra_78_bkCarrier M i)) (hs : s ⊆ R i) (hsl : #s ≤ ℓ)
    (j₀ : (Order.succ ρ).ord.ToType) (hj₀ : j₀ < i) :
    ∃ k, ∃ hk : k < i, j₀ < k ∧ ¬ Order.IsSuccLimit k ∧
      ∃ s' ⊆ R k, #s' ≤ ℓ ∧ infra_78_bkStep M hk '' s' = s := by
  classical
  let S : (Order.succ ρ).ord.ToType → Set (infra_78_bkCarrier M i) := fun j =>
    if h : j < i then infra_78_bkStep M h '' R j else if j = i then R i else Set.univ
  have hSlt : ∀ j (h : j < i), S j = infra_78_bkStep M h '' R j := fun j h => by
    simp only [S, h, ↓reduceDIte]
  have hSi' : S i = R i := by simp only [S, lt_irrefl, ↓reduceDIte, ↓reduceIte]
  have hSgt : ∀ j, i < j → S j = Set.univ := fun j h => by
    simp only [S, not_lt.2 h.le, h.ne', ↓reduceDIte, ↓reduceIte]
  have hSmono : Monotone S := by
    intro a b hab
    rcases lt_trichotomy b i with hb | hb | hb
    · have ha := lt_of_le_of_lt hab hb
      rw [hSlt a ha, hSlt b hb]
      rcases hab.lt_or_eq with hab' | hab'
      · rintro _ ⟨z, hz, rfl⟩
        refine ⟨infra_78_bkStep M hab' z, hmono hab' ⟨z, hz, rfl⟩, ?_⟩
        exact (infra_78_bkStep_trans M hM hab' hb z).symm
      · subst hab'; exact le_rfl
    · subst hb
      rw [hSi']
      rcases hab.lt_or_eq with ha | ha
      · rw [hSlt a ha]; exact hmono ha
      · subst ha; rw [hSi']
    · rw [hSgt b hb]; exact Set.subset_univ _
  have hSi : S i ⊆ ⋃ j ∈ Set.Iio i, S j := by
    rw [hSi', hlim i hi]
    intro x hx
    obtain ⟨⟨j, hj⟩, hx⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_biUnion hj (by rw [hSlt j hj]; exact hx)
  have hsS : s ⊆ S i := by rw [hSi']; exact hs
  obtain ⟨j₁, hj₁, hsj⟩ := infra_78_bounded_in_earlier_stage S hSmono hSi hsS hsl hcof
  rw [hSlt j₁ hj₁] at hsj
  set m := max j₀ j₁ with hmdef
  have hmi : m < i := max_lt hj₀ hj₁
  set k := Order.succ m with hkdef
  have hmk : m < k := Order.lt_succ_of_not_isMax hmi.not_isMax
  have hki : k < i := (Order.IsSuccLimit.succ_lt_iff hi).mpr hmi
  have hk : ¬ Order.IsSuccLimit k := fun hl =>
    hl.isSuccPrelimit m (Order.covBy_succ_of_not_isMax hmi.not_isMax)
  have hj₁k : j₁ < k := lt_of_le_of_lt (le_max_right _ _) hmk
  have hsk : s ⊆ infra_78_bkStep M hki '' R k := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hsj hx
    exact ⟨infra_78_bkStep M hj₁k z, hmono hj₁k ⟨z, hz, rfl⟩,
      (infra_78_bkStep_trans M hM hj₁k hki z).symm⟩
  have hpre : ∀ x : s, ∃ z ∈ R k, infra_78_bkStep M hki z = x.1 := fun x => hsk x.2
  choose pre hpreR hpreEq using hpre
  refine ⟨k, hki, lt_of_le_of_lt (le_max_left _ _) hmk, hk, Set.range pre, ?_,
    Cardinal.mk_range_le.trans hsl, ?_⟩
  · rintro _ ⟨x, rfl⟩; exact hpreR x
  · ext x
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩; rw [hpreEq y]; exact y.2
    · intro hx; exact ⟨pre ⟨x, hx⟩, ⟨_, rfl⟩, hpreEq _⟩

/-- **Closure requirement 2 at stages of cofinality `> λ` (Prop 7.8 proof).** For a `ρ⁺`
matrix with the composition law and continuity at limits (obligations of
`infra_78_matrix_construction`) and bookkeeping sets `R` that are forward-closed, continuous,
and satisfy requirement 2 at non-limit stages (`infra_78_bookkeeping_sets_instantiate`):
at every stage `i` with `cf(i) > λ`, every `≤ λ` top list `d ⊆ S_i` has a Lemma 6.9
approximation sequence of length `λ` over `X_i` (exception estimate `|Z| + ℵ₀` on all tests of
size `≤ λ`) whose copies lie in `R_i`. Local character (`infra_78_tied_local` on the stage chain
below `i`) makes the type free from an earlier stage; copies supplied at an intervening
successor stage are transferred to the image tuple (`infra_78_seq_host_transfer`) and persist
over `X_i` (`infra_78_copies_persist_at_limits`). -/
theorem infra_78_bookkeeping_req2_high_cof (hM : M.CompLaw) (hC : M.ContAtLimits)
    {ℓ : Cardinal.{u}} (hℓ : ℵ₀ ≤ ℓ) (hℓκ : ℓ < κ) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (hrec : κ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ κ)
    (R : ∀ i, Set (infra_78_bkCarrier M i))
    (hmono : ∀ {j i} (h : j < i), infra_78_bkStep M h '' R j ⊆ R i)
    (hlim : ∀ i, Order.IsSuccLimit i → R i = ⋃ j : Set.Iio i, infra_78_bkStep M j.2 '' R j.1)
    (hsupp : ∀ i, ¬ Order.IsSuccLimit i → ∀ s ⊆ R i, #s ≤ ℓ →
      #(Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) ≤ σ →
      ∃ seq : ApproximationSequence (infra_78_bkTuple M i s), seq.τ = ℓ ∧
        ℓ + ℵ₀ < #seq.κIndex ∧
        ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ R i)
    (i : (Order.succ ρ).ord.ToType) (hcof : ℓ < Order.cof (Set.Iio i))
    (s : Set (infra_78_bkCarrier M i)) (hs : s ⊆ R i) (hsl : #s ≤ ℓ)
    (hσs : #(Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) ≤ σ) :
    ∃ seq : ApproximationSequence (infra_78_bkTuple M i s), seq.τ = ℓ ∧
      ℓ + ℵ₀ < #seq.κIndex ∧
      ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ R i := by
  classical
  by_cases hi : Order.IsSuccLimit i
  swap
  · exact hsupp i hi s hs hsl hσs
  set q := infra_78_bkTuple M i s with hqdef
  have hidxℓ : #q.idx ≤ ℓ := (Cardinal.mk_preimage_of_injective _ _ Sum.inr_injective).trans hsl
  -- local character on the stage chain below `i`
  let C := infra_78_stageChain M hM hC i hi
  obtain ⟨α₀, hα₀, hF⟩ := infra_78_tied_local P σ hσ hκ hrec hσSucc C q rfl hσs
    (by
      show #q.idx < (infra_78_stageChain M hM hC i hi).δ.cof
      rw [infra_78_stageChain_cof]; exact hidxℓ.trans_lt hcof)
  set j₀ := infra_78_stg i α₀ hα₀ with hj₀def
  have hj₀ : j₀ < i := infra_78_stg_lt i α₀ hα₀
  -- an intervening non-limit stage holding a preimage of `s`
  obtain ⟨k, hk, hj₀k, hknl, s', hs'R, hs'l, hs'eq⟩ :=
    infra_78_bk_pull M hM R hmono hlim i hi hcof s hs hsl j₀ hj₀
  -- the top points of `s'` correspond to those of `s`
  have hmemY : ∀ y : (Sum.inr ⁻¹' s' : Set (M.Y k).model.carrier),
      (M.stepY hk.le).onVertex PUnit.unit y.1 ∈ (Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) := by
    intro y
    rw [← hs'eq]
    exact ⟨Sum.inr y.1, y.2, rfl⟩
  let eF : (Sum.inr ⁻¹' s' : Set (M.Y k).model.carrier) →
      (Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) := fun y => ⟨_, hmemY y⟩
  have heF : Function.Bijective eF := by
    constructor
    · intro y₁ y₂ h
      apply Subtype.ext
      exact ((M.stepY hk.le).onVertex PUnit.unit).injective (congrArg Subtype.val h)
    · rintro ⟨xv, hxv⟩
      have hx : (Sum.inr xv : infra_78_bkCarrier M i) ∈ s := hxv
      rw [← hs'eq] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      rcases z with z | z
      · exact (Sum.inl_ne_inr hzx).elim
      · exact ⟨⟨z, hz⟩, Subtype.ext (Sum.inr_injective hzx)⟩
  let e := Equiv.ofBijective eF heF
  have hσs' : #(Sum.inr ⁻¹' s' : Set (M.Y k).model.carrier) ≤ σ :=
    (Cardinal.mk_congr e).le.trans hσs
  obtain ⟨sk, hτk, hlenk, hink⟩ := hsupp k hknl s' hs'R hs'l hσs'
  have hidx' : #(infra_78_bkTuple M k s').idx ≤ ℓ :=
    (Cardinal.mk_preimage_of_injective _ _ Sum.inr_injective).trans hs'l
  have hb : #(infra_78_bkTuple M k s').idx + sk.τ < κ := by
    rw [hτk]
    exact (add_le_add hidx' le_rfl).trans_lt (by rw [Cardinal.add_eq_self hℓ]; exact hℓκ)
  let s2 := infra_78_seq_host_transfer (infra_78_bkTuple M k s')
    (q.restrict (M.stepX hk.le) trivial) (M.stepY hk.le) trivial e
    (fun x => infra_78_bkStep_pair M hk x) (fun _ => rfl) sk hb hb
  have hfree := infra_78_tiedFree_congr_arrow (P := P) (A := M.X j₀) (B := M.X i)
    (f := M.stepX (infra_78_stg_lt i α₀ hα₀).le)
    (f' := SystemArrow.comp (M.stepX hj₀k.le) (M.stepX hk.le)) trivial trivial q
    (hM.1 hj₀k.le hk.le) hF
  have hs2 : s2.τ + ℵ₀ < #s2.κIndex := by
    show sk.τ + ℵ₀ < #sk.κIndex
    rw [hτk]; exact hlenk
  have hs2μ : s2.τ < κ := by show sk.τ < κ; rw [hτk]; exact hℓκ
  obtain ⟨seq, hτ, e', hfam⟩ := infra_78_copies_persist_at_limits P σ hσ hκ hrec hσSucc
    (M.stepX hj₀k.le) trivial (M.stepX hk.le) trivial q rfl hσs hfree s2 hs2 hs2μ
  refine ⟨seq, hτ.trans hτk, ?_, ?_⟩
  · rw [Cardinal.mk_congr e']; exact hlenk
  · intro a b
    rw [hfam a b]
    exact hmono hk ⟨_, hink (e' a) (e.symm b), rfl⟩

/-- **Bookkeeping assembly (Prop 7.8 proof).** On a `ρ⁺` matrix with the composition law and
continuity at limits (obligations of `infra_78_matrix_construction`), for `ℵ₀ ≤ λ < ρ = ρ^λ`,
`λ < κ` with `κ` recursion-closed at some `σ ≥ λ`, and seeds of size `≤ ρ`: there are increasing
continuous bookkeeping sets `R_i ⊆ X_i`, `S_i ⊆ Y_i` (one set in `X_i ⊕ Y_i`), `R_i ⊆ S_i`
along the pair, of size `≤ ρ`, containing the seeds at non-limit stages, satisfying closure
requirements 1 and 2 at every non-limit stage and every stage of cofinality `> λ`. -/
theorem infra_78_bookkeeping_assembly (hM : M.CompLaw) (hC : M.ContAtLimits)
    {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible) (hℓκ : ℓ < κ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    (σ : Cardinal.{u}) (hℓσ : ℓ ≤ σ) (hrec : κ ∈ recursionClosedLevels P σ)
    (hσSucc : Order.succ σ ≤ κ)
    (seed : ∀ i, Set (infra_78_bkCarrier M i)) (hseed : ∀ i, #(seed i) ≤ ρ) :
    ∃ R : ∀ i, Set (infra_78_bkCarrier M i),
      (∀ i, #(R i) ≤ ρ) ∧
      (∀ {j i} (h : j < i), infra_78_bkStep M h '' R j ⊆ R i) ∧
      (∀ i, Order.IsSuccLimit i → R i = ⋃ j : Set.Iio i, infra_78_bkStep M j.2 '' R j.1) ∧
      (∀ i, ¬ Order.IsSuccLimit i → seed i ⊆ R i) ∧
      (∀ i x, (Sum.inl x : infra_78_bkCarrier M i) ∈ R i →
        (Sum.inr ((M.pair i).onVertex PUnit.unit x) : infra_78_bkCarrier M i) ∈ R i) ∧
      (∀ i, (¬ Order.IsSuccLimit i ∨ ℓ < Order.cof (Set.Iio i)) → ∀ s ⊆ R i, #s ≤ ℓ →
        infra_78_bkReq1 M hℓel i s (R i)) ∧
      (∀ i, (¬ Order.IsSuccLimit i ∨ ℓ < Order.cof (Set.Iio i)) → ∀ s ⊆ R i, #s ≤ ℓ →
        ∃ seq : ApproximationSequence (infra_78_bkTuple M i s), seq.τ = ℓ ∧
          ℓ + ℵ₀ < #seq.κIndex ∧
          ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ R i) := by
  have hℓ : ℵ₀ ≤ ℓ := P.aleph0_le hℓel
  have hσ : ℵ₀ ≤ σ := hℓ.trans hℓσ
  obtain ⟨R, hcard, hmono, hlim, hseedR, hpair, hsupp1, hsupp2⟩ :=
    infra_78_bookkeeping_sets_instantiate M hℓel hℓκ.le hℓρ hpow seed hseed
  have hsupp2' : ∀ i, ¬ Order.IsSuccLimit i → ∀ s ⊆ R i, #s ≤ ℓ →
      #(Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) ≤ σ →
      ∃ seq : ApproximationSequence (infra_78_bkTuple M i s), seq.τ = ℓ ∧
        ℓ + ℵ₀ < #seq.κIndex ∧
        ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ R i :=
    fun i hi s hs hsl hσs => hsupp2 i hi σ hσ hrec hσSucc hℓκ s hs hsl hσs
  refine ⟨R, hcard, hmono, hlim, hseedR, hpair, ?_, ?_⟩
  · rintro i (hi | hcof) s hs hsl
    · exact hsupp1 i hi s hs hsl
    · exact infra_78_bookkeeping_req1_high_cof M hM hℓel R hmono hlim hsupp1 i hcof s hs hsl
  · intro i hic s hs hsl
    have hσs : #(Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) ≤ σ :=
      ((Cardinal.mk_preimage_of_injective _ _ Sum.inr_injective).trans hsl).trans hℓσ
    rcases hic with hi | hcof
    · exact hsupp2' i hi s hs hsl hσs
    · exact infra_78_bookkeeping_req2_high_cof M hM hC hℓ hℓκ σ hσ hrec hσSucc R hmono hlim
        hsupp2' i hcof s hs hsl hσs

end

section PairLocal
variable {P : SingleModelData K} {κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}
  {X Y : P.scheme.Object κ hκ}
  (f : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y))
  (hf : P.scheme.permitted (X := X) (Y := Y) f)

/-- The tuple of top points of `s ⊆ |X| ⊕ |Y|` over `X` (realized in `Y` along `f`). -/
def infra_78_pairTuple (s : Set (X.model.carrier ⊕ Y.model.carrier)) :
    TupleOver K oneVertexShape P.scheme hκ X :=
  ⟨κ, hκ, Y, f, hf, (Sum.inr ⁻¹' s : Set _), fun k => Y.occ k.1⟩

/-- Pair-local closure requirement 1 request. -/
def infra_78_pairLsReq {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (s T : Set (X.model.carrier ⊕ Y.model.carrier)) : Prop :=
  ∃ (A V : P.scheme.Object ℓ hℓel)
    (iA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hκ X))
    (iV : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel V) (P.scheme.asSystem hκ Y))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hℓel V)),
    P.scheme.permitted (X := A) (Y := X) iA ∧
    P.scheme.permitted (X := V) (Y := Y) iV ∧
    P.scheme.permitted (X := A) (Y := V) g ∧
    (∀ v, (iV.onVertex v).comp (g.onVertex v) = (f.onVertex v).comp (iA.onVertex v)) ∧
    Sum.inl ⁻¹' s ⊆ Set.range (iA.onVertex PUnit.unit) ∧
    Sum.inr ⁻¹' s ⊆ Set.range (iV.onVertex PUnit.unit) ∧
    T = Sum.inl '' Set.range (iA.onVertex PUnit.unit) ∪
      Sum.inr '' Set.range (iV.onVertex PUnit.unit)

/-- Pair-local closure requirement 2 request. -/
def infra_78_pairCopyReq (ℓ : Cardinal.{u}) (s T : Set (X.model.carrier ⊕ Y.model.carrier)) :
    Prop :=
  ∃ seq : ApproximationSequence (infra_78_pairTuple f hf s), seq.τ = ℓ ∧
    ℓ + ℵ₀ < #seq.κIndex ∧
    T = Set.range (fun ab : seq.κIndex × (infra_78_pairTuple f hf s).idx =>
      (Sum.inl (X.val (seq.family ab.1 ab.2)) : X.model.carrier ⊕ Y.model.carrier))

/-- The tuple of a LIST `d` of top points over `X` (realized in `Y` along `f`); entries may
repeat. -/
def infra_78_pairListTuple {I : Type u} (d : I → Y.model.carrier) :
    TupleOver K oneVertexShape P.scheme hκ X :=
  ⟨κ, hκ, Y, f, hf, I, fun k => Y.occ (d k)⟩

/-- The `λ`-fold repetition list of the top points of `s`: every point of `s` occurs `λ` times,
so every list of length `≤ λ` from `s` (with arbitrary repetitions) is an INJECTIVE reindexing
of it. -/
def infra_78_pairRep (ℓ : Cardinal.{u}) (s : Set (X.model.carrier ⊕ Y.model.carrier)) :
    (Sum.inr ⁻¹' s : Set Y.model.carrier) × ℓ.ord.ToType → Y.model.carrier :=
  fun x => x.1.1

/-- Pair-local list-indexed closure requirement 2 request (the repetition list of `s`). -/
def infra_78_pairRepCopyReq (ℓ : Cardinal.{u}) (s T : Set (X.model.carrier ⊕ Y.model.carrier)) :
    Prop :=
  ∃ seq : ApproximationSequence (infra_78_pairListTuple f hf (infra_78_pairRep ℓ s)),
    seq.τ = ℓ ∧ ℓ + ℵ₀ < #seq.κIndex ∧
    T = Set.range (fun ab : seq.κIndex × (infra_78_pairListTuple f hf (infra_78_pairRep ℓ s)).idx =>
      (Sum.inl (X.val (seq.family ab.1 ab.2)) : X.model.carrier ⊕ Y.model.carrier))

/-- Restriction of a list sequence along an injective coordinate map `ρ` with `d' ∘ ρ = d`
(`ApproximationSequence.subtuple_uniform`; no many-to-one reindexing). -/
noncomputable def infra_78_listSeq_reindex {I I' : Type u} (d : I → Y.model.carrier)
    (d' : I' → Y.model.carrier) (ρ : I → I') (hρ : Function.Injective ρ)
    (h : ∀ k, d' (ρ k) = d k) (seq : ApproximationSequence (infra_78_pairListTuple f hf d')) :
    ApproximationSequence (infra_78_pairListTuple f hf d) where
  τ := seq.τ
  κIndex := seq.κIndex
  family := fun a k => seq.family a (ρ k)
  concat_bounded := by
    refine lt_of_le_of_lt ?_ seq.concat_bounded
    exact Cardinal.mk_le_of_injective (f := Prod.map id ρ) (Function.injective_id.prodMap hρ)
  few_exceptions := fun {β} Z hZ => by
    have hsub := seq.subtuple_uniform ρ hρ Z hZ
    have htj : typeJoint (p := infra_78_pairListTuple f hf d) Z =
        typeJoint (p := (infra_78_pairListTuple f hf d').reindex ρ) Z := by
      funext t
      cases t with
      | inl k =>
        exact (congrArg (fun y => Y.occ y) (h k)).symm
      | inr _ => rfl
    rw [htj]
    exact hsub

/-- Pair-local requests of a small parameter set. -/
noncomputable def infra_78_pairRequests (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}}
    (hℓel : ℓ ∈ P.eligible) (s : Set (X.model.carrier ⊕ Y.model.carrier)) :
    Set (X.model.carrier ⊕ Y.model.carrier) :=
  (Sum.inr '' (f.onVertex PUnit.unit '' (Sum.inl ⁻¹' s))) ∪
    infra_78_pick ρ (infra_78_pairLsReq f hℓel s) ∪ infra_78_pick ρ (infra_78_pairCopyReq f hf ℓ s) ∪
    infra_78_pick ρ (infra_78_pairRepCopyReq f hf ℓ s)

/-- **Stage-local bookkeeping closure (Prop 7.8 interleaving).** For a single permitted pair
`f : X → Y` at level `κ` and any `T ⊆ |X| ⊕ |Y|` of size `≤ ρ`, there is `T' ⊇ T` of size
`≤ ρ` closed under the pair (`R ⊆ S`) and under the requests of closure requirements 1 and 2
for every `≤ λ` subset. The output depends only on the current pair, so the bookkeeping can be
interleaved with the matrix recursion. -/
theorem infra_78_pair_bookkeeping_close {ρ ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
    (hℓκ : ℓ ≤ κ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ)
    (T : Set (X.model.carrier ⊕ Y.model.carrier)) (hT : #T ≤ ρ) :
    ∃ T' : Set (X.model.carrier ⊕ Y.model.carrier), T ⊆ T' ∧ #T' ≤ ρ ∧
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
          ∀ a b, (Sum.inl (X.val (seq.family a b)) : X.model.carrier ⊕ Y.model.carrier) ∈ T') ∧
      (∀ σ : Cardinal.{u}, ℵ₀ ≤ σ → κ ∈ recursionClosedLevels P σ → Order.succ σ ≤ κ → ℓ < κ →
        ℓ ≤ σ → ∀ {I : Type u} (d : I → Y.model.carrier), #I ≤ ℓ →
        (∀ k, (Sum.inr (d k) : X.model.carrier ⊕ Y.model.carrier) ∈ T') →
        ∃ seq : ApproximationSequence (infra_78_pairListTuple f hf d), seq.τ = ℓ ∧
          ℓ + ℵ₀ < #seq.κIndex ∧
          ∀ a b, (Sum.inl (X.val (seq.family a b)) : X.model.carrier ⊕ Y.model.carrier) ∈ T') := by
  have hℓ : ℵ₀ ≤ ℓ := P.aleph0_le hℓel
  have hρ : ℵ₀ ≤ ρ := hℓ.trans hℓρ.le
  have hF : ∀ s : Set (X.model.carrier ⊕ Y.model.carrier), #s ≤ ℓ →
      #(infra_78_pairRequests f hf ρ hℓel s) ≤ ρ := by
    intro s hs
    have h1 : #(Sum.inr '' (f.onVertex PUnit.unit '' (Sum.inl ⁻¹' s)) :
        Set (X.model.carrier ⊕ Y.model.carrier)) ≤ ρ :=
      Cardinal.mk_image_le.trans (Cardinal.mk_image_le.trans
        ((Cardinal.mk_preimage_of_injective _ _ Sum.inl_injective).trans (hs.trans hℓρ.le)))
    refine (mk_union_le _ _).trans ?_
    refine (add_le_add ((mk_union_le _ _).trans (add_le_add ((mk_union_le _ _).trans
      (add_le_add h1 (infra_78_pick_card _ _))) (infra_78_pick_card _ _)))
      (infra_78_pick_card _ _)).trans ?_
    rw [add_eq_self hρ, add_eq_self hρ, add_eq_self hρ]
  obtain ⟨T', hTT', hcard, hcl⟩ :=
    infra_78_cardinal_closure T hℓ hℓρ hpow (infra_78_pairRequests f hf ρ hℓel) hF hT
  refine ⟨T', hTT', hcard, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hs : ({Sum.inl x} : Set (X.model.carrier ⊕ Y.model.carrier)) ⊆ T' :=
      Set.singleton_subset_iff.2 hx
    have hsl : #({Sum.inl x} : Set (X.model.carrier ⊕ Y.model.carrier)) ≤ ℓ := by
      rw [Cardinal.mk_singleton]; exact one_le_aleph0.trans hℓ
    apply hcl _ hs hsl
    left; left; left
    exact ⟨_, ⟨x, Set.mem_singleton _, rfl⟩, rfl⟩
  · intro s hs hsl
    have hS : #(Sum.inl ⁻¹' s : Set X.model.carrier) ≤ ℓ :=
      (Cardinal.mk_preimage_of_injective _ _ Sum.inl_injective).trans hsl
    have hT2 : #(Sum.inr ⁻¹' s : Set Y.model.carrier) ≤ ℓ :=
      (Cardinal.mk_preimage_of_injective _ _ Sum.inr_injective).trans hsl
    have hex : ∃ T : Set (X.model.carrier ⊕ Y.model.carrier), #T ≤ ρ ∧
        infra_78_pairLsReq f hℓel s T := by
      obtain ⟨A, V, iA, iV, g, h1, h2, h3, h4, h5, h6⟩ :=
        infra_78_mixed_ls_pair hℓel hκ hℓκ f _ _ hS hT2
      refine ⟨_, ?_, A, V, iA, iV, g, h1, h2, h3, h4, h5, h6, rfl⟩
      refine (mk_union_le _ _).trans ?_
      have eA : #(Set.range (iA.onVertex PUnit.unit)) ≤ ℓ :=
        Cardinal.mk_range_le.trans (le_of_eq A.card)
      have eV : #(Set.range (iV.onVertex PUnit.unit)) ≤ ℓ :=
        Cardinal.mk_range_le.trans (le_of_eq V.card)
      refine (add_le_add (Cardinal.mk_image_le.trans eA) (Cardinal.mk_image_le.trans eV)).trans ?_
      rw [add_eq_self hℓ]; exact hℓρ.le
    obtain ⟨A, V, iA, iV, g, h1, h2, h3, h4, h5, h6, hTe⟩ := infra_78_pick_spec hex
    have hsub : infra_78_pick ρ (infra_78_pairLsReq f hℓel s) ⊆ T' := fun z hz =>
      hcl s hs hsl (Or.inl (Or.inl (Or.inr hz)))
    rw [hTe] at hsub
    exact ⟨A, V, iA, iV, g, h1, h2, h3, h4, h5, h6,
      fun z hz => hsub (Or.inl hz), fun z hz => hsub (Or.inr hz)⟩
  · intro σ hσ hrec hσSucc hℓκ' s hs hsl hσs
    have hidxℓ : #(infra_78_pairTuple f hf s).idx ≤ ℓ :=
      (Cardinal.mk_preimage_of_injective _ _ Sum.inr_injective).trans hsl
    have hex : ∃ T : Set (X.model.carrier ⊕ Y.model.carrier), #T ≤ ρ ∧
        infra_78_pairCopyReq f hf ℓ s T := by
      obtain ⟨seq, hτ, hκI, hprod⟩ := infra_78_code_copies_bounded P σ hσ hκ hrec hσSucc
        (infra_78_pairTuple f hf s) rfl hσs hℓ hℓκ' hidxℓ
      refine ⟨_, Cardinal.mk_range_le.trans (hprod.trans (Order.succ_le_of_lt hℓρ)), seq, hτ,
        ?_, rfl⟩
      rw [hκI, Cardinal.add_eq_left hℓ hℓ]
      exact Order.lt_succ_of_not_isMax (not_isMax ℓ)
    obtain ⟨seq, hτ, hlen, hTe⟩ := infra_78_pick_spec hex
    have hsub : infra_78_pick ρ (infra_78_pairCopyReq f hf ℓ s) ⊆ T' := fun z hz =>
      hcl s hs hsl (Or.inl (Or.inr hz))
    rw [hTe] at hsub
    exact ⟨seq, hτ, hlen, fun a b => hsub ⟨(a, b), rfl⟩⟩
  · intro σ hσ hrec hσSucc hℓκ' hℓσ I d hI hdT
    classical
    let s : Set (X.model.carrier ⊕ Y.model.carrier) := Sum.inr '' Set.range d
    have hs : s ⊆ T' := by
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      exact hdT k
    have hsl : #s ≤ ℓ := Cardinal.mk_image_le.trans (Cardinal.mk_range_le.trans hI)
    have hidxℓ : #(infra_78_pairListTuple f hf (infra_78_pairRep ℓ s)).idx ≤ ℓ := by
      show #((Sum.inr ⁻¹' s : Set Y.model.carrier) × ℓ.ord.ToType) ≤ ℓ
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_ord_toType]
      exact (mul_le_mul ((Cardinal.mk_preimage_of_injective _ _ Sum.inr_injective).trans hsl)
        le_rfl zero_le zero_le).trans (Cardinal.mul_eq_self hℓ).le
    have hex : ∃ T : Set (X.model.carrier ⊕ Y.model.carrier), #T ≤ ρ ∧
        infra_78_pairRepCopyReq f hf ℓ s T := by
      obtain ⟨seq, hτ, hκI, hprod⟩ := infra_78_code_copies_bounded P σ hσ hκ hrec hσSucc
        (infra_78_pairListTuple f hf (infra_78_pairRep ℓ s)) rfl (hidxℓ.trans hℓσ) hℓ hℓκ' hidxℓ
      refine ⟨_, Cardinal.mk_range_le.trans (hprod.trans (Order.succ_le_of_lt hℓρ)), seq, hτ,
        ?_, rfl⟩
      rw [hκI, Cardinal.add_eq_left hℓ hℓ]
      exact Order.lt_succ_of_not_isMax (not_isMax ℓ)
    obtain ⟨seq, hτ, hlen, hTe⟩ := infra_78_pick_spec hex
    have hsub : infra_78_pick ρ (infra_78_pairRepCopyReq f hf ℓ s) ⊆ T' := fun z hz =>
      hcl s hs hsl (Or.inr hz)
    rw [hTe] at hsub
    obtain ⟨e⟩ : Nonempty (I ↪ ℓ.ord.ToType) :=
      (Cardinal.le_def _ _).1 (by rw [Cardinal.mk_ord_toType]; exact hI)
    let ρ' : I → (infra_78_pairListTuple f hf (infra_78_pairRep ℓ s)).idx :=
      fun k => (⟨d k, ⟨d k, ⟨k, rfl⟩, rfl⟩⟩, e k)
    have hρ' : Function.Injective ρ' := fun a b hab => e.injective (congrArg Prod.snd hab)
    exact ⟨infra_78_listSeq_reindex f hf d (infra_78_pairRep ℓ s) ρ' hρ' (fun _ => rfl) seq, hτ,
      hlen, fun a b => hsub ⟨(a, ρ' b), rfl⟩⟩

end PairLocal

/-- The matrix tuple at stage `i` is the pair-local tuple of the stage pair. -/
theorem infra_78_bkTuple_eq_pairTuple {P : SingleModelData K} {ρ κ : Cardinal.{u}}
    {hκ : κ ∈ P.eligible} (M : Infra78Matrix P ρ hκ) (i : (Order.succ ρ).ord.ToType)
    (s : Set (infra_78_bkCarrier M i)) :
    infra_78_bkTuple M i s = infra_78_pairTuple (M.pair i) (M.pair_permitted i) s := rfl


section ListReq
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}
  (M : Infra78Matrix P ρ hκ)

/-- The tuple of a LIST of top points of stage `i` over `X_i` (entries may repeat). -/
abbrev infra_78_bkListTuple (i : (Order.succ ρ).ord.ToType) {I : Type u}
    (d : I → (M.Y i).model.carrier) : TupleOver K oneVertexShape P.scheme hκ (M.X i) :=
  infra_78_pairListTuple (M.pair i) (M.pair_permitted i) d

/-- **List-indexed closure requirement 2 at stages of cofinality `> λ`.** As
`infra_78_bookkeeping_req2_high_cof`, for LISTS `d : I → Y_i` (`|I| ≤ λ ≤ σ`, repetitions
allowed) whose points lie in `R_i`: the list is pulled back to an intervening non-limit stage
`k` past a local-character stage (`infra_78_bk_pull`, choosing preimages of its points), the
non-limit list supply gives a sequence there, and it is transferred to `Y_i` along `stepY` with
the identity on the list index (`infra_78_seq_host_transfer`) and persists over `X_i`. -/
theorem infra_78_bookkeeping_req2_list_high_cof (hM : M.CompLaw) (hC : M.ContAtLimits)
    {ℓ : Cardinal.{u}} (hℓ : ℵ₀ ≤ ℓ) (hℓκ : ℓ < κ) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (hℓσ : ℓ ≤ σ) (hrec : κ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ κ)
    (R : ∀ i, Set (infra_78_bkCarrier M i))
    (hmono : ∀ {j i} (h : j < i), infra_78_bkStep M h '' R j ⊆ R i)
    (hlim : ∀ i, Order.IsSuccLimit i → R i = ⋃ j : Set.Iio i, infra_78_bkStep M j.2 '' R j.1)
    (hsupp : ∀ i, ¬ Order.IsSuccLimit i → ∀ {I : Type u} (d : I → (M.Y i).model.carrier),
      #I ≤ ℓ → (∀ k, (Sum.inr (d k) : infra_78_bkCarrier M i) ∈ R i) →
      ∃ seq : ApproximationSequence (infra_78_bkListTuple M i d), seq.τ = ℓ ∧
        ℓ + ℵ₀ < #seq.κIndex ∧
        ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ R i)
    (i : (Order.succ ρ).ord.ToType) (hcof : ℓ < Order.cof (Set.Iio i))
    {I : Type u} (d : I → (M.Y i).model.carrier) (hI : #I ≤ ℓ)
    (hd : ∀ k, (Sum.inr (d k) : infra_78_bkCarrier M i) ∈ R i) :
    ∃ seq : ApproximationSequence (infra_78_bkListTuple M i d), seq.τ = ℓ ∧
      ℓ + ℵ₀ < #seq.κIndex ∧
      ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ R i := by
  classical
  by_cases hi : Order.IsSuccLimit i
  swap
  · exact hsupp i hi d hI hd
  set q := infra_78_bkListTuple M i d with hqdef
  let C := infra_78_stageChain M hM hC i hi
  obtain ⟨α₀, hα₀, hF⟩ := infra_78_tied_local P σ hσ hκ hrec hσSucc C q rfl (hI.trans hℓσ)
    (by
      show #I < (infra_78_stageChain M hM hC i hi).δ.cof
      rw [infra_78_stageChain_cof]; exact hI.trans_lt hcof)
  set j₀ := infra_78_stg i α₀ hα₀ with hj₀def
  have hj₀ : j₀ < i := infra_78_stg_lt i α₀ hα₀
  let s : Set (infra_78_bkCarrier M i) := Sum.inr '' Set.range d
  have hs : s ⊆ R i := by
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    exact hd k
  have hsl : #s ≤ ℓ := Cardinal.mk_image_le.trans (Cardinal.mk_range_le.trans hI)
  obtain ⟨k, hk, hj₀k, hknl, s', hs'R, -, hs'eq⟩ :=
    infra_78_bk_pull M hM R hmono hlim i hi hcof s hs hsl j₀ hj₀
  have hpre : ∀ t : I, ∃ y : (M.Y k).model.carrier,
      (Sum.inr y : infra_78_bkCarrier M k) ∈ s' ∧ (M.stepY hk.le).onVertex PUnit.unit y = d t := by
    intro t
    have hmem : (Sum.inr (d t) : infra_78_bkCarrier M i) ∈ s := ⟨d t, ⟨t, rfl⟩, rfl⟩
    rw [← hs'eq] at hmem
    obtain ⟨z, hz, hze⟩ := hmem
    rcases z with x | y
    · exact (Sum.inl_ne_inr hze).elim
    · exact ⟨y, hz, Sum.inr_injective hze⟩
  choose d' hd'R hd'eq using hpre
  obtain ⟨sk, hτk, hlenk, hink⟩ := hsupp k hknl d' hI (fun t => hs'R (hd'R t))
  have hb : #(infra_78_bkListTuple M k d').idx + sk.τ < κ := by
    rw [hτk]
    exact (add_le_add hI le_rfl).trans_lt (by rw [Cardinal.add_eq_self hℓ]; exact hℓκ)
  let s2 := infra_78_seq_host_transfer (infra_78_bkListTuple M k d')
    (q.restrict (M.stepX hk.le) trivial) (M.stepY hk.le) trivial (Equiv.refl I)
    (fun x => infra_78_bkStep_pair M hk x)
    (fun t => by
      show (M.Y i).occ (d t) = _
      rw [← hd'eq t]
      rfl) sk hb hb
  have hfree := infra_78_tiedFree_congr_arrow (P := P) (A := M.X j₀) (B := M.X i)
    (f := M.stepX (infra_78_stg_lt i α₀ hα₀).le)
    (f' := SystemArrow.comp (M.stepX hj₀k.le) (M.stepX hk.le)) trivial trivial q
    (hM.1 hj₀k.le hk.le) hF
  have hs2 : s2.τ + ℵ₀ < #s2.κIndex := by
    show sk.τ + ℵ₀ < #sk.κIndex
    rw [hτk]; exact hlenk
  have hs2μ : s2.τ < κ := by show sk.τ < κ; rw [hτk]; exact hℓκ
  obtain ⟨seq, hτ, e', hfam⟩ := infra_78_copies_persist_at_limits P σ hσ hκ hrec hσSucc
    (M.stepX hj₀k.le) trivial (M.stepX hk.le) trivial q rfl (hI.trans hℓσ) hfree s2 hs2 hs2μ
  refine ⟨seq, hτ.trans hτk, ?_, ?_⟩
  · rw [Cardinal.mk_congr e']; exact hlenk
  · intro a b
    rw [hfam a b]
    exact hmono hk ⟨_, hink (e' a) b, rfl⟩

end ListReq

end AEC
