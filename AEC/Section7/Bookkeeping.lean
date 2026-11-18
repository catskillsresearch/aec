module

public import AEC.Section7.TiedLocalCharacter

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
composition law `Infra78Matrix.CompLaw` as an explicit hypothesis; it and continuity at limits
are tracked obligations of `infra_78_matrix_construction`, not hidden assumptions.
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
    T = Set.range (fun ab : seq.κIndex × (infra_78_bkTuple M i s).idx =>
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
            ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ R i) := by
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
      obtain ⟨seq, hτ, -, hprod⟩ := infra_78_code_copies_bounded P σ hσ hκ hrec hσSucc
        (infra_78_bkTuple M i s) rfl hσs hℓ hℓκ' hidxℓ
      exact ⟨_, Cardinal.mk_range_le.trans (hprod.trans (Order.succ_le_of_lt hℓρ)), seq, hτ, rfl⟩
    obtain ⟨seq, hτ, hT⟩ := infra_78_pick_spec hex
    have hsub : infra_78_pick ρ (infra_78_bkCopyReq M ℓ i s) ⊆ R i := fun z hz =>
      hreq i hi s hs hsl (Or.inr hz)
    rw [hT] at hsub
    exact ⟨seq, hτ, fun a b => hsub ⟨(a, b), rfl⟩⟩

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
end AEC
