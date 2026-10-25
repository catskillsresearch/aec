module

public import AEC.Section3.FiniteSupportOrder
public import AEC.Section3.OrderCharacter
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Hom.Set
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Finsupp
public import Mathlib.SetTheory.Cardinal.Rat

@[expose] public section

namespace AEC
section

universe u v

open Cardinal Finsupp Set

namespace HOrder

variable {δ : _root_.Ordinal.{u}}

/-- The rational coefficient of an `H(δ)` vector at a `Γδ` index. -/
def coeff (a : HOrder δ) (g : Gamma δ) : ℚ :=
  (ofColex a) g

/-- The integer coefficient of a `Γδ` vector. -/
def coeffZ (g : Gamma δ) (i : OrdIndex δ) : ℤ :=
  (ofColex g) i

/-- Multiply every rational coefficient by `r`. -/
noncomputable def smulQ (r : ℚ) (a : HOrder δ) : HOrder δ :=
  toColex ((ofColex a).mapRange (fun x => r * x) (by simp))

lemma coeff_smulQ (r : ℚ) (a : HOrder δ) (g : Gamma δ) :
    coeff (smulQ r a) g = r * coeff a g := by
  simp [coeff, smulQ, mapRange_apply, ofColex_toColex]

lemma smulQ_add (r : ℚ) (a b : HOrder δ) : smulQ r (a + b) = smulQ r a + smulQ r b := by
  apply ofColex.injective
  ext g
  simp [smulQ, mapRange_apply, ofColex_toColex, add_apply, mul_add]

lemma coeff_add (a b : HOrder δ) (g : Gamma δ) : coeff (a + b) g = coeff a g + coeff b g := by
  simp [coeff, add_apply]

lemma coeff_neg (a : HOrder δ) (g : Gamma δ) : coeff (-a) g = -coeff a g := by
  simp [coeff]

lemma coeffZ_neg (g : Gamma δ) (i : OrdIndex δ) : coeffZ (-g) i = -coeffZ g i := by
  simp [coeffZ]

lemma coeffZ_basis_self (i : OrdIndex δ) : coeffZ (basisZ i) i = 1 := by
  simp [coeffZ, basisZ, ofColex_toColex, single_eq_same]

lemma coeffZ_basis_of_ne {i j : OrdIndex δ} (h : j ≠ i) : coeffZ (basisZ i) j = 0 := by
  simp [coeffZ, basisZ, ofColex_toColex, single_eq_of_ne h]

lemma rat_add_lt_add_right {p q r : ℚ} (h : p < q) : p + r < q + r :=
  lt_of_le_of_ne (IsOrderedAddMonoid.add_le_add_left p q h.le r)
    (fun heq => h.ne (add_right_cancel heq))

lemma rat_mul_lt_mul_left {r p q : ℚ} (hr : 0 < r) (h : p < q) : r * p < r * q :=
  mul_lt_mul_of_pos_left h hr

lemma addRight_lt {c x y : HOrder δ} (h : x < y) : x + c < y + c := by
  rw [Colex.lt_iff] at h ⊢
  obtain ⟨i, hi, hlt⟩ := h
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, coeff_add, coeff_add, show coeff x j = coeff y j from hi j hj]
  · rw [← coeff, ← coeff, coeff_add, coeff_add]
    exact rat_add_lt_add_right (by simpa [coeff] using hlt)

lemma addRight_lt_iff (c x y : HOrder δ) : x + c < y + c ↔ x < y := by
  constructor
  · intro h
    simpa [add_assoc, add_neg_cancel, add_zero] using addRight_lt (c := -c) h
  · exact addRight_lt

/-- Translation is an order automorphism of `H(δ)`. -/
noncomputable def addRightOrderIso (c : HOrder δ) : HOrder δ ≃o HOrder δ where
  toFun x := x + c
  invFun x := x - c
  left_inv x := add_sub_cancel_right x c
  right_inv x := sub_add_cancel x c
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact (addRight_lt_iff c x y).1 hlt |>.le
      · exact le_of_eq (add_right_cancel heq)
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact (addRight_lt_iff c x y).2 hlt |>.le
      · exact le_of_eq (congrArg (· + c) heq)

lemma neg_lt_neg_H {x y : HOrder δ} (h : x < y) : -y < -x := by
  rw [Colex.lt_iff] at h ⊢
  obtain ⟨i, hi, hlt⟩ := h
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, coeff_neg, coeff_neg]
    exact congrArg Neg.neg (show coeff y j = coeff x j from (hi j hj).symm)
  · rw [← coeff, ← coeff, coeff_neg, coeff_neg]
    exact neg_lt_neg (by simpa [coeff] using hlt)

lemma neg_le_neg_iff_H (x y : HOrder δ) : -x ≤ -y ↔ y ≤ x := by
  have hiff : ∀ {p q : HOrder δ}, -q < -p ↔ p < q := by
    intro p q
    constructor
    · intro h
      simpa using neg_lt_neg_H h
    · exact neg_lt_neg_H
  rw [← not_lt, ← not_lt]
  exact not_congr hiff

lemma smulQ_lt {r : ℚ} (hr : 0 < r) {a b : HOrder δ} (h : a < b) : smulQ r a < smulQ r b := by
  rw [Colex.lt_iff] at h ⊢
  obtain ⟨i, hi, hlt⟩ := h
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, coeff_smulQ, coeff_smulQ, show coeff a j = coeff b j from hi j hj]
  · rw [← coeff, ← coeff, coeff_smulQ, coeff_smulQ]
    exact rat_mul_lt_mul_left hr (by simpa [coeff] using hlt)

lemma smulQ_pos {r : ℚ} (hr : 0 < r) {a : HOrder δ} (ha : 0 < a) : 0 < smulQ r a := by
  have h := smulQ_lt hr ha
  simpa [smulQ, mapRange_zero, toColex_ofColex] using h

lemma basisQ_pos (g : Gamma δ) : 0 < basisQ (δ := δ) g := by
  rw [Colex.lt_iff]
  refine ⟨g, ?_, ?_⟩
  · intro j hj
    simp [basisQ, single_eq_of_ne hj.ne']
  · simp [basisQ, single_eq_same]

lemma sub_pos_of_lt {a b : HOrder δ} (hab : a < b) : 0 < b - a :=
  (addRight_lt_iff a 0 (b - a)).1 (by simpa [zero_add, sub_add_cancel] using hab)

lemma dense (a b : HOrder δ) (hab : a < b) : ∃ c : HOrder δ, a < c ∧ c < b := by
  let d : HOrder δ := b - a
  have hd : 0 < d := sub_pos_of_lt hab
  have hhalf : smulQ (1 / 2) d < d := by
    rw [Colex.lt_iff] at hd ⊢
    obtain ⟨i, hi, hlt⟩ := hd
    refine ⟨i, ?_, ?_⟩
    · intro j hj
      have hz : coeff d j = 0 := by simpa [coeff] using (hi j hj).symm
      rw [← coeff, ← coeff, coeff_smulQ, hz, mul_zero]
    · rw [← coeff, ← coeff, coeff_smulQ]
      have hpos : (0 : ℚ) < coeff d i := by simpa [coeff] using hlt
      have hone : (1 : ℚ) / 2 < 1 := by norm_num
      simpa [one_mul] using mul_lt_mul_of_pos_right hone hpos
  refine ⟨a + smulQ (1 / 2) d, ?_, ?_⟩
  · have hpos : 0 < smulQ (1 / 2) d := smulQ_pos (by norm_num) hd
    simpa [zero_add, add_comm] using addRight_lt (c := a) hpos
  · simpa [d, sub_add_cancel, add_comm] using addRight_lt (c := a) hhalf

lemma neg_lt_zero_of_pos {a : HOrder δ} (ha : 0 < a) : -a < 0 := by
  simpa [zero_add, add_neg_cancel] using addRight_lt (c := -a) ha

lemma noBot (a : HOrder δ) : ∃ b : HOrder δ, b < a := by
  refine ⟨a + (-basisQ (0 : Gamma δ)), ?_⟩
  simpa [add_comm, zero_add] using addRight_lt (c := a) (neg_lt_zero_of_pos (basisQ_pos _))

lemma noTop (a : HOrder δ) : ∃ c : HOrder δ, a < c :=
  ⟨a + basisQ (0 : Gamma δ), by
    simpa [add_comm, zero_add] using addRight_lt (c := a) (basisQ_pos (0 : Gamma δ))⟩

lemma card_ordIndex (δ : _root_.Ordinal.{u}) : #(OrdIndex δ) = lift.{u + 1} δ.card :=
  mk_Iio_ordinal δ

lemma aleph0_le_card_of_isSuccLimit (hδ : Order.IsSuccLimit δ) : ℵ₀ ≤ δ.card := by
  rw [← _root_.Ordinal.card_omega0]
  exact _root_.Ordinal.card_le_card (_root_.Ordinal.omega0_le_of_isSuccLimit hδ)

lemma infinite_ordIndex (hδ : Order.IsSuccLimit δ) : Infinite (OrdIndex δ) := by
  rw [Cardinal.infinite_iff, card_ordIndex]
  exact aleph0_le_lift.2 (aleph0_le_card_of_isSuccLimit hδ)

lemma card_gamma (hδ : Order.IsSuccLimit δ) : #(Gamma δ) = lift.{u + 1} δ.card := by
  have hinf : Infinite (OrdIndex δ) := infinite_ordIndex hδ
  rw [← (toColex : (OrdIndex δ →₀ ℤ) ≃ Gamma δ).cardinal_eq, mk_finsupp_lift_of_infinite]
  simp only [Cardinal.mk_int, lift_aleph0, lift_uzero, card_ordIndex]
  exact max_eq_left (aleph0_le_lift.2 (aleph0_le_card_of_isSuccLimit hδ))

lemma infinite_gamma (hδ : Order.IsSuccLimit δ) : Infinite (Gamma δ) := by
  rw [Cardinal.infinite_iff, card_gamma hδ]
  exact aleph0_le_lift.2 (aleph0_le_card_of_isSuccLimit hδ)

lemma card_eq (hδ : Order.IsSuccLimit δ) : lift.{u + 1} δ.card = #(HOrder δ) := by
  have hinf : Infinite (Gamma δ) := infinite_gamma hδ
  rw [← (toColex : (Gamma δ →₀ ℚ) ≃ HOrder δ).cardinal_eq, mk_finsupp_lift_of_infinite]
  simp only [Cardinal.mkRat, lift_aleph0, lift_uzero, card_gamma hδ]
  exact (max_eq_left (aleph0_le_lift.2 (aleph0_le_card_of_isSuccLimit hδ))).symm

/-- The greatest `Γδ` coordinate at which a nonzero vector of `H(δ)` is nonzero. -/
noncomputable def rankOf (a : HOrder δ) (ha : a ≠ 0) : Gamma δ :=
  (ofColex a).support.max' (by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    simpa using ha)

lemma le_rankOf (a : HOrder δ) (ha : a ≠ 0) {j : Gamma δ} (hj : j ∈ (ofColex a).support) :
    j ≤ rankOf a ha :=
  Finset.le_max' _ j hj

lemma coeff_eq_zero_of_rank_lt (a : HOrder δ) (ha : a ≠ 0) {j : Gamma δ}
    (hj : rankOf a ha < j) : coeff a j = 0 := by
  by_contra hne
  exact (le_rankOf a ha (mem_support_iff.mpr (by simpa [coeff] using hne))).not_gt hj

lemma coeff_rank_pos {a : HOrder δ} (ha : 0 < a) : 0 < coeff a (rankOf a ha.ne') := by
  rw [Colex.lt_iff] at ha
  obtain ⟨i, hi, hlt⟩ := ha
  have himem : i ∈ (ofColex a).support := mem_support_iff.mpr (by simpa [coeff] using hlt.ne')
  have hrank : rankOf a ha.ne' = i := by
    apply le_antisymm
    · refine Finset.max'_le _ _ ?_
      intro j hj
      by_contra hji
      exact mem_support_iff.mp hj (by simpa [coeff] using hi j (lt_of_not_ge hji))
    · exact Finset.le_max' _ i himem
  simpa [coeff, hrank] using hlt

lemma basisQ_lt_of_lt_rank {a : HOrder δ} (ha : 0 < a) {g : Gamma δ}
    (hg : g < rankOf a ha.ne') : basisQ g < a := by
  rw [Colex.lt_iff]
  refine ⟨rankOf a ha.ne', ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, coeff_eq_zero_of_rank_lt a ha.ne' hj]
    simp [coeff, basisQ, ofColex_toColex, single_eq_of_ne (hg.trans hj).ne']
  · rw [← coeff, ← coeff]
    have hb0 : coeff (basisQ g) (rankOf a ha.ne') = 0 := by
      simp [coeff, basisQ, ofColex_toColex, single_eq_of_ne hg.ne']
    rw [hb0]
    exact coeff_rank_pos ha

lemma neg_basisZ_lt_of_support {g : Gamma δ} {β : OrdIndex δ}
    (h : ∀ i ∈ (ofColex g).support, i < β) : -basisZ β < g := by
  rw [Colex.lt_iff]
  refine ⟨β, ?_, ?_⟩
  · intro j hj
    have hg : coeffZ g j = 0 := by
      by_contra hne
      exact (h j (mem_support_iff.mpr (by simpa [coeffZ] using hne))).not_gt hj
    have hb : coeffZ (-basisZ β) j = 0 := by
      rw [coeffZ_neg, coeffZ_basis_of_ne hj.ne']
      simp
    rw [← coeffZ, ← coeffZ, hg, hb]
  · have hg : coeffZ g β = 0 := by
      by_contra hne
      exact (h β (mem_support_iff.mpr (by simpa [coeffZ] using hne))).false
    rw [← coeffZ, ← coeffZ, coeffZ_neg, coeffZ_basis_self, hg]
    exact neg_one_lt_zero

lemma basisQ_injective : Function.Injective (basisQ (δ := δ)) := by
  intro g₁ g₂ h
  have h' : single g₁ (1 : ℚ) = single g₂ 1 := by simpa [basisQ] using congrArg ofColex h
  exact (single_left_injective (one_ne_zero : (1 : ℚ) ≠ 0)) h'

lemma basisZ_injective : Function.Injective (basisZ (δ := δ)) := by
  intro i j h
  have h' : single i (1 : ℤ) = single j 1 := by simpa [basisZ] using congrArg ofColex h
  exact (single_left_injective (one_ne_zero : (1 : ℤ) ≠ 0)) h'

/-- `u` at the negative basis vector `-e_α`. -/
noncomputable def lowBasis (α : OrdIndex δ) : HOrder δ :=
  basisQ (-basisZ α)

lemma lowBasis_pos (α : OrdIndex δ) : 0 < lowBasis (δ := δ) α :=
  basisQ_pos _

lemma lowBasis_injective : Function.Injective (lowBasis (δ := δ)) := by
  intro α β h
  exact basisZ_injective (neg_injective (basisQ_injective h))

lemma lowBasis_lt_of_support {a : HOrder δ} (ha : 0 < a) {α : OrdIndex δ}
    (h : ∀ i ∈ (ofColex (rankOf a ha.ne')).support, i < α) : lowBasis α < a :=
  basisQ_lt_of_lt_rank ha (neg_basisZ_lt_of_support h)

lemma cof_ordIndex (δ : _root_.Ordinal.{u}) :
    Order.cof (OrdIndex δ) = lift.{u + 1} (_root_.Ordinal.cof δ) := by
  rw [show Order.cof (OrdIndex δ) = Order.cof (Iio δ) from rfl, _root_.Ordinal.cof_Iio]
  exact (_root_.Ordinal.lift_cof δ).symm

lemma aleph0_le_cof_ordIndex (hδ : Order.IsSuccLimit δ) : ℵ₀ ≤ Order.cof (OrdIndex δ) := by
  rw [cof_ordIndex]
  exact aleph0_le_lift.2 ((_root_.Ordinal.aleph0_le_cof_iff).2 ((_root_.Ordinal.one_lt_cof_iff).2 hδ))

lemma setCofinality_le {α : Type v} [LinearOrder α] {s t : Set α} (ht : t ⊆ s)
    (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : setCofinality s ≤ #t := by
  unfold setCofinality
  apply csInf_le'
  exact ⟨t, ht, rfl, h⟩

lemma le_setCofinality {α : Type v} [LinearOrder α] {κ : Cardinal.{v}} {s : Set α}
    (h : ∀ t ⊆ s, (∀ x ∈ s, ∃ y ∈ t, x ≤ y) → κ ≤ #t) : κ ≤ setCofinality s := by
  unfold setCofinality
  refine (le_csInf_iff' ?_).2 ?_
  · exact ⟨#s, s, subset_rfl, rfl, fun x hx => ⟨x, hx, le_rfl⟩⟩
  · rintro κ' ⟨t, ht, rfl, hcof⟩
    exact h t ht hcof

lemma setCoinitiality_le {α : Type v} [LinearOrder α] {s t : Set α} (ht : t ⊆ s)
    (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : setCoinitiality s ≤ #t := by
  unfold setCoinitiality setCofinality
  apply csInf_le'
  refine ⟨OrderDual.toDual '' t, image_mono ht, mk_image_eq OrderDual.toDual.injective, ?_⟩
  intro x hx
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y, hy, hyx⟩ := h x' hx'
  exact ⟨OrderDual.toDual y, mem_image_of_mem _ hy, hyx⟩

lemma le_setCoinitiality {α : Type v} [LinearOrder α] {κ : Cardinal.{v}} {s : Set α}
    (h : ∀ t ⊆ s, (∀ x ∈ s, ∃ y ∈ t, y ≤ x) → κ ≤ #t) : κ ≤ setCoinitiality s := by
  unfold setCoinitiality setCofinality
  refine (le_csInf_iff' ?_).2 ?_
  · exact ⟨#(OrderDual.toDual '' s), OrderDual.toDual '' s, subset_rfl, rfl, fun x hx => ⟨x, hx, le_rfl⟩⟩
  · rintro κ' ⟨t, ht, rfl, hcof⟩
    let t' : Set α := OrderDual.ofDual '' t
    have ht' : t' ⊆ s := by
      intro y hy
      obtain ⟨y', hy', rfl⟩ := hy
      exact ht hy'
    have hco : ∀ x ∈ s, ∃ y ∈ t', y ≤ x := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hcof (OrderDual.toDual x) (mem_image_of_mem _ hx)
      refine ⟨OrderDual.ofDual y, mem_image_of_mem _ hy, ?_⟩
      simpa using hyx
    exact (h t' ht' hco).trans_eq (mk_image_eq OrderDual.ofDual.injective)

lemma setCofinality_image_le {α β : Type v} [LinearOrder α] [LinearOrder β] (f : α ≃o β)
    (s : Set α) : setCofinality (f '' s) ≤ setCofinality s := by
  unfold setCofinality
  refine (le_csInf_iff' ?_).2 ?_
  · exact ⟨#s, s, subset_rfl, rfl, fun x hx => ⟨x, hx, le_rfl⟩⟩
  · rintro κ ⟨u, hu, rfl, hcof⟩
    refine (setCofinality_le (image_mono hu) ?_).trans_eq (mk_image_eq f.injective)
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨z, hz, hxz⟩ := hcof x hx
    exact ⟨f z, mem_image_of_mem _ hz, f.monotone hxz⟩

lemma setCofinality_orderIso {α β : Type v} [LinearOrder α] [LinearOrder β] (f : α ≃o β)
    (s : Set α) : setCofinality (f '' s) = setCofinality s := by
  apply le_antisymm (setCofinality_image_le f s)
  simpa [Equiv.symm_image_image] using setCofinality_image_le f.symm (f '' s)

lemma setCoinitiality_orderIso {α β : Type v} [LinearOrder α] [LinearOrder β] (f : α ≃o β)
    (s : Set α) : setCoinitiality (f '' s) = setCoinitiality s := by
  unfold setCoinitiality
  have hd : OrderDual.toDual '' (f '' s) = f.dual '' (OrderDual.toDual '' s) := by
    ext x
    simp only [mem_image, OrderIso.dual_apply]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hb
      refine ⟨OrderDual.toDual a, mem_image_of_mem _ ha, ?_⟩
      simp [OrderIso.dual_apply]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hy
      refine ⟨f a, mem_image_of_mem _ ha, ?_⟩
      simp [OrderIso.dual_apply]
  rw [hd]
  exact setCofinality_orderIso f.dual (OrderDual.toDual '' s)

lemma image_Iio (c : HOrder δ) : addRightOrderIso c '' Iio 0 = Iio c := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hlt : y + c < 0 + c := addRight_lt hy
    simpa [zero_add] using hlt
  · intro hx
    refine ⟨x - c, ?_, sub_add_cancel x c⟩
    exact (addRight_lt_iff c (x - c) 0).1 (by
      have : x < c := hx
      simpa [sub_add_cancel, zero_add] using this)

lemma image_Ioi (c : HOrder δ) : addRightOrderIso c '' Ioi 0 = Ioi c := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hlt : 0 + c < y + c := addRight_lt hy
    simpa [zero_add] using hlt
  · intro hx
    refine ⟨x - c, ?_, sub_add_cancel x c⟩
    exact (addRight_lt_iff c 0 (x - c)).1 (by
      have : c < x := hx
      simpa [sub_add_cancel, zero_add] using this)

/-- Negation, as an isomorphism onto the dual order. -/
noncomputable def negOrderIso : HOrder δ ≃o (HOrder δ)ᵒᵈ where
  toFun x := OrderDual.toDual (-x)
  invFun x := -OrderDual.ofDual x
  left_inv x := by simp
  right_inv x := by simp
  map_rel_iff' := by
    intro x y
    simpa using (neg_le_neg_iff_H y x)

lemma neg_image_Iio : negOrderIso (δ := δ) '' Iio 0 = OrderDual.toDual '' Ioi 0 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-y, ?_, rfl⟩
    simpa [zero_add, add_neg_cancel] using addRight_lt (c := -y) hy
  · rintro ⟨y, hy, rfl⟩
    exact ⟨-y, neg_lt_zero_of_pos hy, by simp⟩

lemma left_zero_cofinality_eq_pos_coinitiality :
    setCofinality (Iio (0 : HOrder δ)) = setCoinitiality (Ioi (0 : HOrder δ)) := by
  simpa [setCoinitiality, neg_image_Iio] using
    (setCofinality_orderIso (negOrderIso (δ := δ)) (Iio (0 : HOrder δ))).symm

lemma not_cofinal_of_card_lt {α : Type v} [LinearOrder α] {s : Set α}
    (h : #s < Order.cof α) : ¬ IsCofinal s := by
  intro hcof
  exact lt_irrefl _ ((Order.cof_le hcof).trans_lt h)

lemma exists_strict_bound_of_not_cofinal {α : Type v} [LinearOrder α] {s : Set α}
    (h : ¬ IsCofinal s) : ∃ β : α, ∀ y ∈ s, y < β := by
  unfold IsCofinal at h
  push Not at h
  obtain ⟨β, hβ⟩ := h
  exact ⟨β, hβ⟩

lemma rankSupportCard (g : Gamma δ) : #((ofColex g).support : Set (OrdIndex δ)) < ℵ₀ :=
  finset_card_lt_aleph0 _

lemma posCone_coinitiality (hδ : Order.IsSuccLimit δ) :
    setCoinitiality (Ioi (0 : HOrder δ)) = Order.cof (OrdIndex δ) := by
  apply le_antisymm
  · obtain ⟨s, hs, hcard⟩ := Order.exists_cof_eq (OrdIndex δ)
    let t : Set (HOrder δ) := lowBasis '' s
    have ht : t ⊆ Ioi 0 := by
      intro x hx
      obtain ⟨α, _, rfl⟩ := hx
      exact lowBasis_pos α
    have hco : ∀ x ∈ Ioi (0 : HOrder δ), ∃ y ∈ t, y ≤ x := by
      intro x hx
      let used : Set (OrdIndex δ) := (ofColex (rankOf x hx.ne')).support
      have hlt : #used < Order.cof (OrdIndex δ) :=
        (rankSupportCard _).trans_le (aleph0_le_cof_ordIndex hδ)
      obtain ⟨β, hβ⟩ := exists_strict_bound_of_not_cofinal (not_cofinal_of_card_lt hlt)
      obtain ⟨α, hαs, hβα⟩ := hs ⟨_root_.Order.succ β.1, hδ.succ_lt β.2⟩
      refine ⟨lowBasis α, mem_image_of_mem _ hαs, le_of_lt ?_⟩
      apply lowBasis_lt_of_support hx
      intro i hi
      have hiβ : i < β := hβ i hi
      have hsucc : _root_.Order.succ β.1 ≤ α.1 := Subtype.mk_le_mk.1 hβα
      exact hiβ.trans (Subtype.mk_lt_mk.2 ((_root_.Order.lt_succ β.1).trans_le hsucc))
    exact (setCoinitiality_le ht hco).trans_eq ((mk_image_eq lowBasis_injective).trans hcard)
  · refine le_setCoinitiality ?_
    intro t ht hco
    refine le_of_not_gt ?_
    intro hlt
    let U : Set (OrdIndex δ) :=
      ⋃ a : ↥t, ((ofColex (rankOf a.1 (ne_of_gt (ht a.2)))).support : Set (OrdIndex δ))
    have hU : #U < Order.cof (OrdIndex δ) := by
      by_cases hfin : #↥t < ℵ₀
      · have hidx : Finite (↥t) := mk_lt_aleph0_iff.1 hfin
        have hUfin : U.Finite :=
          Set.finite_iUnion fun a =>
            ((ofColex (rankOf a.1 (ne_of_gt (ht a.2)))).support).finite_toSet
        exact (mk_lt_aleph0_iff.2 hUfin).trans_le (aleph0_le_cof_ordIndex hδ)
      · have hinf : ℵ₀ ≤ #↥t := le_of_not_gt hfin
        have hle : #U ≤ #↥t * ℵ₀ := by
          refine (Cardinal.mk_iUnion_le _).trans ?_
          refine mul_le_mul' le_rfl ?_
          refine ciSup_le' fun a => (rankSupportCard _).le
        rw [mul_aleph0_eq hinf] at hle
        exact hle.trans_lt hlt
    obtain ⟨β, hβ⟩ := exists_strict_bound_of_not_cofinal (not_cofinal_of_card_lt hU)
    let α : OrdIndex δ := ⟨_root_.Order.succ β.1, hδ.succ_lt β.2⟩
    have hbelow : ∀ x ∈ t, lowBasis α < x := by
      intro x hx
      apply lowBasis_lt_of_support (ht hx)
      intro i hi
      have himem : i ∈ U := mem_iUnion.2 ⟨⟨x, hx⟩, hi⟩
      exact (hβ i himem).trans (Subtype.mk_lt_mk.2 (_root_.Order.lt_succ β.1))
    obtain ⟨y, hy, hyx⟩ := hco (lowBasis α) (lowBasis_pos α)
    exact lt_irrefl _ ((hbelow y hy).trans_le hyx)

lemma leftChar (hδ : Order.IsSuccLimit δ) (a : HOrder δ) :
    setCofinality (Iio a) = lift.{u + 1} (_root_.Ordinal.cof δ) := by
  have h := setCofinality_orderIso (addRightOrderIso a) (Iio (0 : HOrder δ))
  rw [image_Iio] at h
  rw [← cof_ordIndex, ← posCone_coinitiality hδ, ← left_zero_cofinality_eq_pos_coinitiality]
  exact h

lemma rightChar (hδ : Order.IsSuccLimit δ) (a : HOrder δ) :
    setCoinitiality (Ioi a) = lift.{u + 1} (_root_.Ordinal.cof δ) := by
  have h := setCoinitiality_orderIso (addRightOrderIso a) (Ioi (0 : HOrder δ))
  rw [image_Ioi] at h
  rw [← cof_ordIndex, ← posCone_coinitiality hδ]
  exact h

noncomputable def mapIio (c : HOrder δ) : ↥(Iio (0 : HOrder δ)) ≃o ↥(Iio c) where
  toFun x := ⟨x.1 + c, by
    have hlt : x.1 + c < 0 + c := addRight_lt x.2
    simpa [zero_add] using hlt⟩
  invFun x := ⟨x.1 - c, (addRight_lt_iff c (x.1 - c) 0).1 (by
    have hx : x.1 < c := x.2
    simpa [sub_add_cancel, zero_add] using hx)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp [sub_add_cancel]
  map_rel_iff' := by
    intro x y
    simp only [Subtype.mk_le_mk]
    exact (addRightOrderIso c).map_rel_iff

noncomputable def mapIoi (c : HOrder δ) : ↥(Ioi (0 : HOrder δ)) ≃o ↥(Ioi c) where
  toFun x := ⟨x.1 + c, by
    have hlt : 0 + c < x.1 + c := addRight_lt x.2
    simpa [zero_add] using hlt⟩
  invFun x := ⟨x.1 - c, (addRight_lt_iff c 0 (x.1 - c)).1 (by
    have hx : c < x.1 := x.2
    simpa [sub_add_cancel, zero_add] using hx)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp [sub_add_cancel]
  map_rel_iff' := by
    intro x y
    simp only [Subtype.mk_le_mk]
    exact (addRightOrderIso c).map_rel_iff

lemma leftRay (a b : HOrder δ) : Nonempty (↥(Iio a) ≃o ↥(Iio b)) :=
  ⟨(mapIio a).symm.trans (mapIio b)⟩

lemma rightRay (a b : HOrder δ) : Nonempty (↥(Ioi a) ≃o ↥(Ioi b)) :=
  ⟨(mapIoi a).symm.trans (mapIoi b)⟩

end HOrder

end
end AEC
