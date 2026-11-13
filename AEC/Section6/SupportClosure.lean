module

public import AEC.Section3.OrderEqualityDiagram
public import Mathlib.Data.Bool.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace AEC
section

universe u

open Cardinal Classical Set Function

attribute [local instance] Classical.propDecidable

namespace Section6SupportClosure

abbrev EmptyU : Type u := PEmpty.{u + 1}
abbrev NatU : Type u := ULift.{u, 0} ℕ
abbrev BoolU : Type u := ULift.{u, 0} Bool

/-- A canonical index of cardinality `χ`. -/
abbrev ChiType (χ : Cardinal.{u}) : Type u := χ.ord.ToType

lemma mk_chiType (χ : Cardinal.{u}) : #(ChiType χ) = χ := mk_ord_toType _

/-- Order, equality, and color pattern of a `χ`-indexed query over a parameter list and a
fixed support list `T★`. The query index is `ChiType χ` in the closure; smaller queries
embed into it. -/
structure PatternCode (ρ ι τ : Type u) : Type u where
  eqQ : ρ → ρ → BoolU
  ltQ : ρ → ρ → BoolU
  eqR : ρ → ι → BoolU
  ltR : ρ → ι → BoolU
  eqT : ρ → τ → BoolU
  ltT : ρ → τ → BoolU
  col : ρ → NatU

noncomputable def patternCode {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ρ ι τ : Type u} (Tstar : τ → J) (r : ι → J) (q : ρ → J) : PatternCode ρ ι τ where
  eqQ := fun i j => ULift.up (decide (q i = q j))
  ltQ := fun i j => ULift.up (decide (q i < q j))
  eqR := fun i k => ULift.up (decide (q i = r k))
  ltR := fun i k => ULift.up (decide (q i < r k))
  eqT := fun i t => ULift.up (decide (q i = Tstar t))
  ltT := fun i t => ULift.up (decide (q i < Tstar t))
  col := fun i => ULift.up (color (q i))

lemma patternCode_components {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ρ ι τ : Type u} (Tstar : τ → J) (r : ι → J) (q q' : ρ → J)
    (h : patternCode color Tstar r q = patternCode color Tstar r q') :
    (∀ i j, q i = q j ↔ q' i = q' j) ∧
    (∀ i j, q i < q j ↔ q' i < q' j) ∧
    (∀ i k, q i = r k ↔ q' i = r k) ∧
    (∀ i k, q i < r k ↔ q' i < r k) ∧
    (∀ i t, q i = Tstar t ↔ q' i = Tstar t) ∧
    (∀ i t, q i < Tstar t ↔ q' i < Tstar t) ∧
    (∀ i, color (q i) = color (q' i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    have := congr_fun (congr_fun (congrArg PatternCode.eqQ h) i) j
    simpa [patternCode, Bool.decide_iff] using this
  · intro i j
    have := congr_fun (congr_fun (congrArg PatternCode.ltQ h) i) j
    simpa [patternCode, Bool.decide_iff] using this
  · intro i k
    have := congr_fun (congr_fun (congrArg PatternCode.eqR h) i) k
    simpa [patternCode, Bool.decide_iff] using this
  · intro i k
    have := congr_fun (congr_fun (congrArg PatternCode.ltR h) i) k
    simpa [patternCode, Bool.decide_iff] using this
  · intro i t
    have := congr_fun (congr_fun (congrArg PatternCode.eqT h) i) t
    simpa [patternCode, Bool.decide_iff] using this
  · intro i t
    have := congr_fun (congr_fun (congrArg PatternCode.ltT h) i) t
    simpa [patternCode, Bool.decide_iff] using this
  · intro i
    exact ULift.up_injective (congr_fun (congrArg PatternCode.col h) i)

lemma sameOrderDiagram_rfl {ι α : Type u} [LinearOrder α] (xs : ι → α) :
    SameOrderDiagram xs xs :=
  ⟨fun _ _ => Iff.rfl, fun _ _ => Iff.rfl⟩

/-- Comparing a query with a fixed base list in both directions, from the stored
`q = base` and `q < base` bits. The base list is the same on both sides. -/
lemma lt_base_of_pattern {J : Type u} [LinearOrder J] {ρ β : Type u}
    (base : β → J) (q q' : ρ → J)
    (heq : ∀ i k, q i = base k ↔ q' i = base k)
    (hlt : ∀ i k, q i < base k ↔ q' i < base k)
    (k : β) (i : ρ) : base k < q i ↔ base k < q' i := by
  constructor
  · intro hij
    rcases lt_trichotomy (base k) (q' i) with hlt' | heq' | hgt
    · exact hlt'
    · exact (hij.ne ((heq i k).2 heq'.symm).symm).elim
    · exact (lt_asymm hij ((hlt i k).2 hgt)).elim
  · intro hij
    rcases lt_trichotomy (base k) (q i) with hlt' | heq' | hgt
    · exact hlt'
    · exact (hij.ne ((heq i k).1 heq'.symm).symm).elim
    · exact (lt_asymm hij ((hlt i k).1 hgt)).elim

lemma sameDiagram_of_patternCode {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ρ ι τ : Type u} (Tstar : τ → J) (r : ι → J) (q q' : ρ → J)
    (h : patternCode color Tstar r q = patternCode color Tstar r q') :
    SameOrderDiagram (Sum.elim (Sum.elim r Tstar) q) (Sum.elim (Sum.elim r Tstar) q') ∧
      ∀ i, color (q i) = color (q' i) := by
  obtain ⟨heqQ, hltQ, heqR, hltR, heqT, hltT, hcol⟩ :=
    patternCode_components color Tstar r q q' h
  refine ⟨⟨?eq, ?lt⟩, hcol⟩
  · intro a b
    rcases a with (⟨i | t⟩ | i) <;> rcases b with (⟨j | t'⟩ | j)
    · simp [Sum.elim]
    · simp [Sum.elim]
    · simp only [Sum.elim]
      exact ⟨fun h => ((heqR j i).1 h.symm).symm, fun h => ((heqR j i).2 h.symm).symm⟩
    · simp [Sum.elim]
    · simp [Sum.elim]
    · simp only [Sum.elim]
      exact ⟨fun h => ((heqT j t).1 h.symm).symm, fun h => ((heqT j t).2 h.symm).symm⟩
    · simpa [Sum.elim] using heqR i j
    · simpa [Sum.elim] using heqT i t'
    · simpa [Sum.elim] using heqQ i j
  · intro a b
    rcases a with (⟨i | t⟩ | i) <;> rcases b with (⟨j | t'⟩ | j)
    · simp [Sum.elim]
    · simp [Sum.elim]
    · simpa [Sum.elim] using lt_base_of_pattern r q q' heqR hltR i j
    · simp [Sum.elim]
    · simp [Sum.elim]
    · simpa [Sum.elim] using lt_base_of_pattern Tstar q q' heqT hltT t j
    · simpa [Sum.elim] using hltR i j
    · simpa [Sum.elim] using hltT i t'
    · simpa [Sum.elim] using hltQ i j

lemma sameDiagram_restrict_param {J : Type u} [LinearOrder J]
    {ι ι' τ ρ : Type u} (e : ι ↪ ι') (r : ι' → J) (t : τ → J) (q q' : ρ → J)
    (h : SameOrderDiagram (Sum.elim (Sum.elim r t) q) (Sum.elim (Sum.elim r t) q')) :
    SameOrderDiagram (Sum.elim (Sum.elim (r ∘ e) t) q)
      (Sum.elim (Sum.elim (r ∘ e) t) q') := by
  refine ⟨?_, ?_⟩
  · intro a b
    rcases a with (⟨i | t₁⟩ | i) <;> rcases b with (⟨j | t₂⟩ | j)
    · simpa [Sum.elim, Function.comp] using h.1 (Sum.inl (Sum.inl (e i))) (Sum.inl (Sum.inl (e j)))
    · simpa [Sum.elim, Function.comp] using h.1 (Sum.inl (Sum.inl (e i))) (Sum.inl (Sum.inr t₂))
    · simpa [Sum.elim, Function.comp] using h.1 (Sum.inl (Sum.inl (e i))) (Sum.inr j)
    · simpa [Sum.elim, Function.comp] using h.1 (Sum.inl (Sum.inr t₁)) (Sum.inl (Sum.inl (e j)))
    · simpa [Sum.elim, Function.comp] using h.1 (Sum.inl (Sum.inr t₁)) (Sum.inl (Sum.inr t₂))
    · simpa [Sum.elim, Function.comp] using h.1 (Sum.inl (Sum.inr t₁)) (Sum.inr j)
    · simpa [Sum.elim, Function.comp] using h.1 (Sum.inr i) (Sum.inl (Sum.inl (e j)))
    · simpa [Sum.elim, Function.comp] using h.1 (Sum.inr i) (Sum.inl (Sum.inr t₂))
    · simpa [Sum.elim, Function.comp] using h.1 (Sum.inr i) (Sum.inr j)
  · intro a b
    rcases a with (⟨i | t₁⟩ | i) <;> rcases b with (⟨j | t₂⟩ | j)
    · simpa [Sum.elim, Function.comp] using h.2 (Sum.inl (Sum.inl (e i))) (Sum.inl (Sum.inl (e j)))
    · simpa [Sum.elim, Function.comp] using h.2 (Sum.inl (Sum.inl (e i))) (Sum.inl (Sum.inr t₂))
    · simpa [Sum.elim, Function.comp] using h.2 (Sum.inl (Sum.inl (e i))) (Sum.inr j)
    · simpa [Sum.elim, Function.comp] using h.2 (Sum.inl (Sum.inr t₁)) (Sum.inl (Sum.inl (e j)))
    · simpa [Sum.elim, Function.comp] using h.2 (Sum.inl (Sum.inr t₁)) (Sum.inl (Sum.inr t₂))
    · simpa [Sum.elim, Function.comp] using h.2 (Sum.inl (Sum.inr t₁)) (Sum.inr j)
    · simpa [Sum.elim, Function.comp] using h.2 (Sum.inr i) (Sum.inl (Sum.inl (e j)))
    · simpa [Sum.elim, Function.comp] using h.2 (Sum.inr i) (Sum.inl (Sum.inr t₂))
    · simpa [Sum.elim, Function.comp] using h.2 (Sum.inr i) (Sum.inr j)

lemma sameDiagram_restrict_query {J : Type u} [LinearOrder J]
    {ι ρ ρ' : Type u} (e : ρ ↪ ρ') (base : ι → J) (q q' : ρ' → J)
    (h : SameOrderDiagram (Sum.elim base q) (Sum.elim base q')) :
    SameOrderDiagram (Sum.elim base (q ∘ e)) (Sum.elim base (q' ∘ e)) := by
  refine ⟨?_, ?_⟩
  · intro a b
    rcases a with i | i <;> rcases b with j | j
    · exact h.1 (Sum.inl i) (Sum.inl j)
    · exact h.1 (Sum.inl i) (Sum.inr (e j))
    · exact h.1 (Sum.inr (e i)) (Sum.inl j)
    · exact h.1 (Sum.inr (e i)) (Sum.inr (e j))
  · intro a b
    rcases a with i | i <;> rcases b with j | j
    · exact h.2 (Sum.inl i) (Sum.inl j)
    · exact h.2 (Sum.inl i) (Sum.inr (e j))
    · exact h.2 (Sum.inr (e i)) (Sum.inl j)
    · exact h.2 (Sum.inr (e i)) (Sum.inr (e j))

lemma sameDiagram_drop_empty {J : Type u} [LinearOrder J]
    {ι τ ρ : Type u} [IsEmpty ι] (p : ι → J) (t : τ → J) (q q' : ρ → J)
    (h : SameOrderDiagram (Sum.elim (Sum.elim p t) q) (Sum.elim (Sum.elim p t) q')) :
    SameOrderDiagram (Sum.elim t q) (Sum.elim t q') := by
  refine ⟨?_, ?_⟩
  · intro a b
    rcases a with t₁ | i <;> rcases b with t₂ | j
    · exact h.1 (Sum.inl (Sum.inr t₁)) (Sum.inl (Sum.inr t₂))
    · exact h.1 (Sum.inl (Sum.inr t₁)) (Sum.inr j)
    · exact h.1 (Sum.inr i) (Sum.inl (Sum.inr t₂))
    · exact h.1 (Sum.inr i) (Sum.inr j)
  · intro a b
    rcases a with t₁ | i <;> rcases b with t₂ | j
    · exact h.2 (Sum.inl (Sum.inr t₁)) (Sum.inl (Sum.inr t₂))
    · exact h.2 (Sum.inl (Sum.inr t₁)) (Sum.inr j)
    · exact h.2 (Sum.inr i) (Sum.inl (Sum.inr t₂))
    · exact h.2 (Sum.inr i) (Sum.inr j)

lemma sameDiagram_empty_param {J : Type u} [LinearOrder J]
    {ι τ ρ : Type u} [IsEmpty ι] (p : ι → J) (t : τ → J) (q q' : ρ → J)
    (h : SameOrderDiagram (Sum.elim t q) (Sum.elim t q')) :
    SameOrderDiagram (Sum.elim (Sum.elim p t) q) (Sum.elim (Sum.elim p t) q') := by
  refine ⟨?_, ?_⟩
  · intro a b
    rcases a with (⟨i | t₁⟩ | i) <;> rcases b with (⟨j | t₂⟩ | j)
    · exact isEmptyElim i
    · exact isEmptyElim i
    · exact isEmptyElim i
    · exact isEmptyElim j
    · exact h.1 (Sum.inl t₁) (Sum.inl t₂)
    · exact h.1 (Sum.inl t₁) (Sum.inr j)
    · exact isEmptyElim j
    · exact h.1 (Sum.inr i) (Sum.inl t₂)
    · exact h.1 (Sum.inr i) (Sum.inr j)
  · intro a b
    rcases a with (⟨i | t₁⟩ | i) <;> rcases b with (⟨j | t₂⟩ | j)
    · exact isEmptyElim i
    · exact isEmptyElim i
    · exact isEmptyElim i
    · exact isEmptyElim j
    · exact h.2 (Sum.inl t₁) (Sum.inl t₂)
    · exact h.2 (Sum.inl t₁) (Sum.inr j)
    · exact isEmptyElim j
    · exact h.2 (Sum.inr i) (Sum.inl t₂)
    · exact h.2 (Sum.inr i) (Sum.inr j)

noncomputable def witnessRange {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ρ ι τ : Type u} (Tstar : τ → J) (r : ι → J) (c : PatternCode ρ ι τ) : Set J :=
  if h : ∃ q : ρ → J, patternCode color Tstar r q = c then
    Set.range (Classical.choose h)
  else
    ∅

lemma exists_chosen_witness {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ρ ι τ : Type u} (Tstar : τ → J) (r : ι → J) (q : ρ → J) :
    ∃ q' : ρ → J,
      (∀ i, q' i ∈ witnessRange color Tstar r (patternCode color Tstar r q)) ∧
      patternCode color Tstar r q' = patternCode color Tstar r q := by
  let c := patternCode color Tstar r q
  have hEx : ∃ q' : ρ → J, patternCode color Tstar r q' = c := ⟨q, rfl⟩
  refine ⟨Classical.choose hEx, fun i => ?_, Classical.choose_spec hEx⟩
  change Classical.choose hEx i ∈ witnessRange color Tstar r c
  simp only [witnessRange, dite_eq_left hEx]
  exact ⟨i, rfl⟩

lemma witnessRange_card_le {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ι τ : Type u} (Tstar : τ → J) (r : ι → J) (χ : Cardinal.{u})
    (c : PatternCode (ChiType χ) ι τ) :
    #(witnessRange color Tstar r c) ≤ χ := by
  unfold witnessRange
  split_ifs with h
  · exact mk_range_le.trans (le_of_eq (mk_chiType χ))
  · simp

lemma two_power_aleph0_le (lam : Cardinal.{u}) (hlam : aleph0 ≤ lam) :
    aleph0 ≤ (2 : Cardinal.{u}) ^ lam :=
  hlam.trans (le_of_lt (cantor lam))

lemma aleph0_power_eq_two_power (χ : Cardinal.{u}) (hχ : aleph0 ≤ χ) :
    aleph0 ^ χ = (2 : Cardinal.{u}) ^ χ := by
  apply le_antisymm
  · calc aleph0 ^ χ ≤ ((2 : Cardinal.{u}) ^ χ) ^ χ :=
        power_le_power_right (hχ.trans (le_of_lt (cantor χ)))
      _ = (2 : Cardinal.{u}) ^ (χ * χ) := by rw [← power_mul]
      _ = (2 : Cardinal.{u}) ^ χ := by rw [mul_eq_self hχ]
  · exact power_le_power_right (natCast_le_aleph0 (n := 2))

lemma kappa_pow_chi (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) :
    ((2 : Cardinal.{u}) ^ lam) ^ χ = (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have h1 : κ ^ χ ≤ κ := by
    have : κ ^ χ = (2 : Cardinal.{u}) ^ (lam * χ) := by
      dsimp [κ]; rw [← power_mul]
    rw [this]
    exact power_le_power_left two_ne_zero <|
      (mul_le_max_of_aleph0_le_left (hχ.trans hlam)).trans (max_le le_rfl hlam)
  have h2 : κ ≤ κ ^ χ := by
    simpa [power_one] using
      power_le_power_left (ne_of_gt (aleph0_pos.trans_le hκ)) (one_le_aleph0.trans hχ)
  exact le_antisymm h1 h2

lemma mk_patternCode_le {ι τ : Type u} {χ lam : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) (hι : #ι ≤ χ) (hτ : #τ ≤ lam) :
    #(PatternCode (ChiType χ) ι τ) ≤ (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have hmul {a b : Cardinal.{u}} (ha : a ≤ κ) (hb : b ≤ κ) : a * b ≤ κ :=
    (mul_le_mul' ha hb).trans_eq (mul_eq_self hκ)
  have hBool : #(BoolU.{u}) = (2 : Cardinal.{u}) := by
    rw [mk_uLift]
    simp
  have hChi : #(ChiType χ) = χ := mk_chiType χ
  have hQQ : #(ChiType χ → ChiType χ → BoolU.{u}) ≤ κ := by
    calc #(ChiType χ → ChiType χ → BoolU.{u})
        = (#BoolU ^ #(ChiType χ)) ^ #(ChiType χ) := by rw [← power_def, ← power_def]
      _ = ((2 : Cardinal.{u}) ^ χ) ^ χ := by rw [hBool, hChi]
      _ = (2 : Cardinal.{u}) ^ (χ * χ) := by rw [← power_mul]
      _ = (2 : Cardinal.{u}) ^ χ := by rw [mul_eq_self hχ]
      _ ≤ κ := power_le_power_left two_ne_zero hlam
  have hQR : #(ChiType χ → ι → BoolU.{u}) ≤ κ := by
    have hmulχ : #(ChiType χ) * #ι ≤ lam := by
      rw [hChi]
      exact (mul_le_max_of_aleph0_le_left hχ).trans (max_le hlam (hι.trans hlam))
    calc #(ChiType χ → ι → BoolU.{u})
        = (#BoolU ^ #ι) ^ #(ChiType χ) := by rw [← power_def, ← power_def]
      _ = (2 : Cardinal.{u}) ^ (#ι * #(ChiType χ)) := by rw [hBool, ← power_mul]
      _ = (2 : Cardinal.{u}) ^ (#(ChiType χ) * #ι) := by rw [mul_comm]
      _ ≤ κ := power_le_power_left two_ne_zero hmulχ
  have hQT : #(ChiType χ → τ → BoolU.{u}) ≤ κ := by
    have hmulχ : #(ChiType χ) * #τ ≤ lam := by
      rw [hChi]
      exact (mul_le_max_of_aleph0_le_left hχ).trans (max_le hlam hτ)
    calc #(ChiType χ → τ → BoolU.{u})
        = (#BoolU ^ #τ) ^ #(ChiType χ) := by rw [← power_def, ← power_def]
      _ = (2 : Cardinal.{u}) ^ (#τ * #(ChiType χ)) := by rw [hBool, ← power_mul]
      _ = (2 : Cardinal.{u}) ^ (#(ChiType χ) * #τ) := by rw [mul_comm]
      _ ≤ κ := power_le_power_left two_ne_zero hmulχ
  have hCol : #(ChiType χ → NatU.{u}) ≤ κ := by
    calc #(ChiType χ → NatU.{u})
        = aleph0 ^ χ := by
          rw [← power_def, hChi, show #(NatU.{u}) = aleph0 by rw [mk_uLift, mk_nat, lift_aleph0]]
      _ = (2 : Cardinal.{u}) ^ χ := aleph0_power_eq_two_power χ hχ
      _ ≤ κ := power_le_power_left two_ne_zero hlam
  let f : PatternCode (ChiType χ) ι τ →
      (ChiType χ → ChiType χ → BoolU) × (ChiType χ → ChiType χ → BoolU) ×
      (ChiType χ → ι → BoolU) × (ChiType χ → ι → BoolU) ×
      (ChiType χ → τ → BoolU) × (ChiType χ → τ → BoolU) ×
      (ChiType χ → NatU) :=
    fun c => (c.eqQ, c.ltQ, c.eqR, c.ltR, c.eqT, c.ltT, c.col)
  have hinj : Function.Injective f := by
    intro a b h
    cases a
    cases b
    simp only [f, Prod.mk.injEq] at h
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7⟩
    simp [h1, h2, h3, h4, h5, h6, h7]
  refine (mk_le_of_injective hinj).trans ?_
  simp only [mk_prod, lift_id]
  exact hmul hQQ (hmul hQQ (hmul hQR (hmul hQR (hmul hQT (hmul hQT hCol)))))

noncomputable def emptyParamWitnesses {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) (χ : Cardinal.{u}) : Set J :=
  ⋃ c : PatternCode (ChiType χ) EmptyU τ,
    witnessRange color Tstar (fun e : EmptyU => e.elim) c

noncomputable def paramWitnesses {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) (χ : Cardinal.{u}) (S : Set J) : Set J :=
  ⋃ (r : ChiType χ → ↥S), ⋃ c : PatternCode (ChiType χ) (ChiType χ) τ,
    witnessRange color Tstar (fun i => (r i).1) c

noncomputable def enrich {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) (χ : Cardinal.{u}) (S : Set J) : Set J :=
  (S ∪ emptyParamWitnesses color Tstar χ) ∪ paramWitnesses color Tstar χ S

lemma enrich_subset_left {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) (χ : Cardinal.{u}) (S : Set J) :
    S ⊆ enrich color Tstar χ S :=
  fun _ hx => Or.inl (Or.inl hx)

lemma emptyParamWitnesses_card {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) {χ lam : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) (hτ : #τ ≤ lam) :
    #(emptyParamWitnesses (J := J) color Tstar χ) ≤ (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  change #(emptyParamWitnesses (J := J) color Tstar χ) ≤ κ
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have hκκ : κ * κ = κ := mul_eq_self hκ
  have hχκ : χ ≤ κ := hlam.trans (le_of_lt (cantor lam))
  refine (mk_iUnion_le (α := J) (ι := PatternCode (ChiType χ) EmptyU τ)
      (fun c => witnessRange color Tstar (fun e : EmptyU => e.elim) c)).trans ?_
  have hc : #(PatternCode (ChiType χ) EmptyU τ) ≤ κ :=
    mk_patternCode_le hχ hlam (by simp [EmptyU, mk_eq_zero]) hτ
  rw [← hκκ]
  exact mul_le_mul' hc (ciSup_le' fun c => (witnessRange_card_le color Tstar _ χ c).trans hχκ)

lemma paramWitnesses_card {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) (χ lam : Cardinal.{u})
    (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) (hτ : #τ ≤ lam)
    {S : Set J} (hS : #S ≤ (2 : Cardinal.{u}) ^ lam) :
    #(paramWitnesses color Tstar χ S) ≤ (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  change #(paramWitnesses color Tstar χ S) ≤ κ
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have hκκ : κ * κ = κ := mul_eq_self hκ
  have hpow : κ ^ χ = κ := kappa_pow_chi χ lam hχ hlam
  have hχκ : χ ≤ κ := hlam.trans (le_of_lt (cantor lam))
  refine (mk_iUnion_le (α := J) (ι := ChiType χ → ↥S)
    (fun r => ⋃ c : PatternCode (ChiType χ) (ChiType χ) τ,
      witnessRange color Tstar (fun i => (r i).1) c)).trans ?_
  have hidx : #(ChiType χ → ↥S) ≤ κ := by
    rw [← power_def, mk_chiType]
    exact (power_le_power_right hS).trans_eq hpow
  refine (mul_le_mul' hidx (ciSup_le' fun r => ?_)).trans (by rw [hκκ])
  refine (mk_iUnion_le _).trans ?_
  have hc : #(PatternCode (ChiType χ) (ChiType χ) τ) ≤ κ :=
    mk_patternCode_le hχ hlam (le_of_eq (mk_chiType χ)) hτ
  rw [← hκκ]
  exact mul_le_mul' hc (ciSup_le' fun c => (witnessRange_card_le color Tstar _ χ c).trans hχκ)

lemma enrich_card {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) (χ lam : Cardinal.{u})
    (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) (hτ : #τ ≤ lam)
    {S : Set J} (hS : #S ≤ (2 : Cardinal.{u}) ^ lam) :
    #(enrich color Tstar χ S) ≤ (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have hadd : κ + κ = κ := add_eq_self hκ
  have h1 : #(emptyParamWitnesses (J := J) color Tstar χ) ≤ κ :=
    emptyParamWitnesses_card color Tstar hχ hlam hτ
  have h2 : #(paramWitnesses color Tstar χ S) ≤ κ :=
    paramWitnesses_card color Tstar χ lam hχ hlam hτ hS
  have hleft : Cardinal.mk (↥(S ∪ emptyParamWitnesses (J := J) color Tstar χ)) ≤ κ :=
    (mk_union_le _ _).trans ((add_le_add hS h1).trans (le_of_eq hadd))
  exact (mk_union_le _ _).trans ((add_le_add hleft h2).trans (le_of_eq hadd))

lemma enrich_realizes {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) (χ : Cardinal.{u}) (hχ : aleph0 ≤ χ) (S : Set J)
    {ι : Type u} (hι : #ι ≤ χ) (p : ι → J) (hp : ∀ i, p i ∈ S)
    {ρ : Type u} (hρ : #ρ ≤ χ) (q : ρ → J) :
    ∃ q' : ρ → J, (∀ i, q' i ∈ enrich color Tstar χ S) ∧
      SameOrderDiagram (Sum.elim (Sum.elim p Tstar) q) (Sum.elim (Sum.elim p Tstar) q') ∧
      ∀ i, color (q i) = color (q' i) := by
  cases isEmpty_or_nonempty ρ with
  | inl hempty =>
      letI : IsEmpty ρ := hempty
      refine ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, ?_, fun i => isEmptyElim i⟩
      have hq : q = fun i => isEmptyElim i := funext fun i => isEmptyElim i
      rw [hq]
      exact sameOrderDiagram_rfl _
  | inr hρne =>
      let iρ : ρ := Classical.choice hρne
      have heρ : lift.{u} #ρ ≤ lift.{u} #(ChiType χ) := by simpa [mk_chiType] using hρ
      let eρ : ρ ↪ ChiType χ := Classical.choice (lift_mk_le'.mp heρ)
      let Q : ChiType χ → J :=
        Function.extend eρ q (fun _ => q iρ)
      have hQ : ∀ i, Q (eρ i) = q i := by
        intro i
        change Function.extend eρ q (fun _ => q iρ) (eρ i) = q i
        rw [eρ.injective.extend_apply]
      cases isEmpty_or_nonempty ι with
      | inl hempty =>
          letI : IsEmpty ι := hempty
          obtain ⟨Q', hQ'mem, hcode⟩ :=
            exists_chosen_witness color Tstar (fun e : EmptyU => e.elim) Q
          have hfull := sameDiagram_of_patternCode color Tstar
            (fun e : EmptyU => e.elim) Q Q' hcode.symm
          let q' : ρ → J := fun i => Q' (eρ i)
          refine ⟨q', ?_, ?_, ?_⟩
          · intro i
            exact Or.inl (Or.inr (mem_iUnion.mpr ⟨patternCode color Tstar
              (fun e : EmptyU => e.elim) Q, hQ'mem (eρ i)⟩))
          · have hdrop := sameDiagram_drop_empty (fun e : EmptyU => e.elim) Tstar Q Q' hfull.1
            have hrest := sameDiagram_restrict_query eρ Tstar Q Q' hdrop
            have hQe : Q ∘ eρ = q := funext hQ
            rw [hQe] at hrest
            exact sameDiagram_empty_param p Tstar q q' hrest
          · intro i
            have hcol := hfull.2 (eρ i)
            simpa [q', hQ] using hcol
      | inr hιne =>
          let i0 : ι := Classical.choice hιne
          have heι : lift.{u} #ι ≤ lift.{u} #(ChiType χ) := by simpa [mk_chiType] using hι
          let eι : ι ↪ ChiType χ := Classical.choice (lift_mk_le'.mp heι)
          let r : ChiType χ → ↥S :=
            Function.extend eι (fun i => ⟨p i, hp i⟩) (fun _ => ⟨p i0, hp i0⟩)
          have hr : ∀ i, (r (eι i)).1 = p i := by
            intro i
            change (Function.extend eι (fun i => (⟨p i, hp i⟩ : ↥S))
              (fun _ => (⟨p i0, hp i0⟩ : ↥S)) (eι i)).1 = p i
            rw [eι.injective.extend_apply]
          obtain ⟨Q', hQ'mem, hcode⟩ :=
            exists_chosen_witness color Tstar (fun i => (r i).1) Q
          have hfull := sameDiagram_of_patternCode color Tstar (fun i => (r i).1) Q Q' hcode.symm
          let q' : ρ → J := fun i => Q' (eρ i)
          refine ⟨q', ?_, ?_, ?_⟩
          · intro i
            exact Or.inr (mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨patternCode color Tstar
              (fun k => (r k).1) Q, hQ'mem (eρ i)⟩⟩)
          · have hrestQ := sameDiagram_restrict_query eρ
              (Sum.elim (fun i => (r i).1) Tstar) Q Q' hfull.1
            have hQe : Q ∘ eρ = q := funext hQ
            rw [hQe] at hrestQ
            have hrest := sameDiagram_restrict_param eι (fun i => (r i).1) Tstar q q' hrestQ
            have hr' : (fun i => (r i).1) ∘ eι = p := funext hr
            simpa [hr'] using hrest
          · intro i
            have hcol := hfull.2 (eρ i)
            simpa [q', hQ] using hcol

noncomputable def closureStage {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) (χ : Cardinal.{u}) (S : Set J)
    (i : (Order.succ χ).ord.ToType) : Set J :=
  enrich color Tstar χ
    (S ∪ ⋃ j : {j : (Order.succ χ).ord.ToType // j < i}, closureStage color Tstar χ S j.1)
termination_by i
decreasing_by
  exact j.2

lemma closureStage_card {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) (χ lam : Cardinal.{u})
    (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) (hτ : #τ ≤ lam)
    {S : Set J} (hS : #S ≤ (2 : Cardinal.{u}) ^ lam)
    (i : (Order.succ χ).ord.ToType) :
    #(closureStage color Tstar χ S i) ≤ (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have hsucc : Order.succ χ ≤ κ :=
    Order.succ_le_of_lt (lt_of_le_of_lt hlam (cantor lam))
  apply (wellFounded_lt (α := (Order.succ χ).ord.ToType)).induction i
  intro i ih
  rw [closureStage.eq_def]
  apply enrich_card color Tstar χ lam hχ hlam hτ
  have hprev :
      #(⋃ j : {j : (Order.succ χ).ord.ToType // j < i},
        closureStage color Tstar χ S j.1) ≤ κ := by
    refine (mk_iUnion_le _).trans ?_
    refine (mul_le_mul'
      ((mk_le_of_injective Subtype.val_injective).trans (by rw [mk_ord_toType]))
      (ciSup_le' fun j : {j : (Order.succ χ).ord.ToType // j < i} => ih j.1 j.2)).trans ?_
    exact (mul_le_mul' hsucc le_rfl).trans (by rw [mul_eq_self hκ])
  exact (mk_union_le _ _).trans
    ((add_le_add hS hprev).trans (by rw [add_eq_self hκ]))

lemma closureSet_card {J : Type u} [LinearOrder J] (color : J → ℕ)
    {τ : Type u} (Tstar : τ → J) (χ lam : Cardinal.{u})
    (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) (hτ : #τ ≤ lam)
    {S : Set J} (hS : #S ≤ (2 : Cardinal.{u}) ^ lam) :
    #(⋃ i : (Order.succ χ).ord.ToType, closureStage color Tstar χ S i) ≤
      (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have hsucc : Order.succ χ ≤ κ :=
    Order.succ_le_of_lt (lt_of_le_of_lt hlam (cantor lam))
  refine (mk_iUnion_le _).trans ?_
  refine (mul_le_mul' (by rw [mk_ord_toType])
    (ciSup_le' (closureStage_card color Tstar χ lam hχ hlam hτ hS))).trans ?_
  exact (mul_le_mul' hsucc le_rfl).trans (by rw [mul_eq_self hκ])

lemma toType_lt_of_ordinal_lt {o : _root_.Ordinal.{u}} {x : o.ToType}
    {a : _root_.Ordinal.{u}} (ha : a < o)
    (hx : (Ordinal.ToType.toOrd x).1 < a) :
    x < Ordinal.ToType.mk ⟨a, ha⟩ := by
  have hsub : Ordinal.ToType.toOrd x < ⟨a, ha⟩ := Subtype.mk_lt_mk.mpr hx
  have hmap := (Ordinal.ToType.mk.lt_iff_lt).mpr hsub
  simpa [Ordinal.ToType.mk.apply_symm_apply] using hmap

/-- **Lemma 6.14** (Closure of a bounded support set), widened. Queries are indexed by an
arbitrary type of size at most `χ`, and a fixed support enumeration `T★` of size at most `λ`
is part of every pattern. A terminal strip needs no side-of-`V` coloring: pass a constant
`color`. The closed set still has size at most `2^λ` and contains `S₀` and the range of `T★`. -/
theorem lemma_6_14_proof {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) :
    ∀ {τ : Type u} (Tstar : τ → J) (_hτ : #τ ≤ lam) (S0 : Set J), #S0 ≤ lam →
      ∃ S : Set J, S0 ⊆ S ∧ (∀ t, Tstar t ∈ S) ∧ #S ≤ (2 : Cardinal.{u}) ^ lam ∧
        ∀ {ι : Type u} (hι : #ι ≤ χ) (p : ι → J), (∀ i, p i ∈ S) →
          ∀ {ρ : Type u} (hρ : #ρ ≤ χ) (q : ρ → J),
            ∃ q' : ρ → J, (∀ i, q' i ∈ S) ∧
              SameOrderDiagram (Sum.elim (Sum.elim p Tstar) q)
                (Sum.elim (Sum.elim p Tstar) q') ∧
              ∀ i, color (q i) = color (q' i) := by
  intro τ Tstar hτ S0 hS0
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hlam0 : aleph0 ≤ lam := hχ.trans hlam
  let Sbase : Set J := S0 ∪ Set.range Tstar
  have hbase : #Sbase ≤ κ := by
    refine (mk_union_le _ _).trans ?_
    have h1 : #S0 ≤ κ := hS0.trans (le_of_lt (cantor lam))
    have h2 : #(Set.range Tstar) ≤ κ :=
      mk_range_le.trans (hτ.trans (le_of_lt (cantor lam)))
    exact (add_le_add h1 h2).trans (le_of_eq (add_eq_self (two_power_aleph0_le lam hlam0)))
  let S : Set J := ⋃ i : (Order.succ χ).ord.ToType, closureStage color Tstar χ Sbase i
  have hpos : (0 : _root_.Ordinal.{u}) < (Order.succ χ).ord := by
    refine lt_of_lt_of_le (Ordinal.natCast_lt_omega0 0) ?_
    rw [← ord_aleph0]
    exact ord_le_ord.mpr (hχ.trans (Order.le_succ χ))
  let i0 : (Order.succ χ).ord.ToType := Ordinal.ToType.mk ⟨0, hpos⟩
  have hS0sub : Sbase ⊆ S := by
    intro x hx
    refine mem_iUnion.mpr ⟨i0, ?_⟩
    rw [closureStage.eq_def]
    exact enrich_subset_left color Tstar χ _ (Or.inl hx)
  have hcard : #S ≤ κ := closureSet_card color Tstar χ lam hχ hlam hτ hbase
  refine ⟨S, fun x hx => hS0sub (Or.inl hx), fun t => hS0sub (Or.inr ⟨t, rfl⟩), hcard, ?_⟩
  intro ι hι p hp ρ hρ q
  have hreg : Ordinal.cof (Order.succ χ).ord = Order.succ χ :=
    (isRegular_succ hχ).cof_ord
  let j : ι → (Order.succ χ).ord.ToType :=
    fun i => Classical.choose (mem_iUnion.mp (hp i))
  have hj : ∀ i, p i ∈ closureStage color Tstar χ Sbase (j i) :=
    fun i => Classical.choose_spec (mem_iUnion.mp (hp i))
  have hidx : #ι < Ordinal.cof (Order.succ χ).ord := by
    rw [hreg]
    exact hι.trans_lt (Order.lt_succ χ)
  have hsup : (⨆ i, (Ordinal.ToType.toOrd (j i)).1) < (Order.succ χ).ord :=
    Ordinal.iSup_lt_of_lt_cof hidx (fun i => (Ordinal.ToType.toOrd (j i)).2)
  have h1 : (⨆ i, (Ordinal.ToType.toOrd (j i)).1) + 1 < (Order.succ χ).ord :=
    (isSuccLimit_ord (hχ.trans (Order.le_succ χ))).succ_lt hsup
  let i1 : (Order.succ χ).ord.ToType :=
    Ordinal.ToType.mk ⟨(⨆ i, (Ordinal.ToType.toOrd (j i)).1) + 1, h1⟩
  have hjlt : ∀ i, j i < i1 := by
    intro i
    refine toType_lt_of_ordinal_lt h1 ?_
    exact lt_of_le_of_lt
      (Ordinal.le_iSup (fun k => (Ordinal.ToType.toOrd (j k)).1) i)
      (lt_add_of_pos_right _ zero_lt_one)
  let R : Set J :=
    Sbase ∪ ⋃ k : {k : (Order.succ χ).ord.ToType // k < i1},
      closureStage color Tstar χ Sbase k.1
  have hpR : ∀ i, p i ∈ R := by
    intro i
    exact Or.inr (mem_iUnion.mpr ⟨⟨j i, hjlt i⟩, hj i⟩)
  obtain ⟨q', hq', hdiag, hcolor⟩ := enrich_realizes color Tstar χ hχ R hι p hpR hρ q
  refine ⟨q', ?_, hdiag, hcolor⟩
  intro k
  exact mem_iUnion.mpr ⟨i1, by
    rw [closureStage.eq_def]
    exact hq' k⟩

end Section6SupportClosure

alias lemma_6_14_proof := Section6SupportClosure.lemma_6_14_proof

end
end AEC
