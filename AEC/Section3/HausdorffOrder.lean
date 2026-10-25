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

lemma one_lt_two_rat : (1 : ℚ) < 2 := by
  have h := rat_add_lt_add_right (r := (1 : ℚ)) zero_lt_one
  rwa [zero_add, one_add_one_eq_two] at h

lemma half_pos_rat : (0 : ℚ) < 1 / 2 := by
  rw [div_eq_mul_inv, one_mul]
  exact inv_pos.2 (zero_lt_one.trans one_lt_two_rat)

lemma half_lt_one_rat : (1 : ℚ) / 2 < 1 := by
  rw [div_eq_mul_inv, one_mul]
  exact inv_lt_one_of_one_lt₀ one_lt_two_rat

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
      exact mul_lt_of_lt_one_left hpos half_lt_one_rat
  refine ⟨a + smulQ (1 / 2) d, ?_, ?_⟩
  · have hlt := addRight_lt (c := a) (smulQ_pos half_pos_rat hd)
    rwa [zero_add, add_comm] at hlt
  · have hlt := addRight_lt (c := a) hhalf
    have hdadd : d + a = b := by simp [d, sub_add_cancel]
    rwa [add_comm, hdadd] at hlt

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
    · apply Finset.max'_le
      intro j hj
      rcases lt_trichotomy j i with hltj | heq | hgt
      · exact hltj.le
      · exact le_of_eq heq
      · exact (mem_support_iff.mp hj (by simpa [coeff] using (hi j hgt).symm)).elim
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
      obtain ⟨a, ha, rfl⟩ := ht hy'
      exact ha
    have hco : ∀ x ∈ s, ∃ y ∈ t', y ≤ x := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hcof (OrderDual.toDual x) (mem_image_of_mem _ hx)
      refine ⟨OrderDual.ofDual y, mem_image_of_mem _ hy, ?_⟩
      rw [← OrderDual.toDual_ofDual y] at hyx
      exact OrderDual.toDual_le_toDual.mp hyx
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
      rfl
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hy
      refine ⟨f a, mem_image_of_mem _ ha, ?_⟩
      rfl
  rw [hd]
  exact setCofinality_orderIso f.dual (OrderDual.toDual '' s)

lemma image_Iio (c : HOrder δ) : addRightOrderIso c '' Iio 0 = Iio c := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hlt : y + c < 0 + c := addRight_lt hy
    rw [zero_add] at hlt
    exact hlt
  · intro hx
    refine ⟨x - c, ?_, sub_add_cancel x c⟩
    apply (addRight_lt_iff c (x - c) 0).1
    rw [sub_add_cancel, zero_add]
    exact hx

lemma image_Ioi (c : HOrder δ) : addRightOrderIso c '' Ioi 0 = Ioi c := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hlt : 0 + c < y + c := addRight_lt hy
    rw [zero_add] at hlt
    exact hlt
  · intro hx
    refine ⟨x - c, ?_, sub_add_cancel x c⟩
    apply (addRight_lt_iff c 0 (x - c)).1
    rw [sub_add_cancel, zero_add]
    exact hx

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
    have hlt := addRight_lt (c := -y) hy
    rwa [zero_add, add_neg_cancel] at hlt
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-y, neg_lt_zero_of_pos hy, ?_⟩
    show OrderDual.toDual (-(-y)) = OrderDual.toDual y
    rw [neg_neg]

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
  toFun x := ⟨x.1 + c, mem_Iio.2 (by
    have hlt : x.1 + c < 0 + c := addRight_lt x.2
    rwa [zero_add] at hlt)⟩
  invFun x := ⟨x.1 - c, mem_Iio.2 ((addRight_lt_iff c (x.1 - c) 0).1 (by
    rw [sub_add_cancel, zero_add]
    exact x.2))⟩
  left_inv x := by
    ext
    exact add_sub_cancel_right x.1 c
  right_inv x := by
    ext
    exact sub_add_cancel x.1 c
  map_rel_iff' := by
    intro x y
    rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe]
    exact (addRightOrderIso c).map_rel_iff

noncomputable def mapIoi (c : HOrder δ) : ↥(Ioi (0 : HOrder δ)) ≃o ↥(Ioi c) where
  toFun x := ⟨x.1 + c, mem_Ioi.2 (by
    have hlt : 0 + c < x.1 + c := addRight_lt x.2
    rwa [zero_add] at hlt)⟩
  invFun x := ⟨x.1 - c, mem_Ioi.2 ((addRight_lt_iff c 0 (x.1 - c)).1 (by
    rw [sub_add_cancel, zero_add]
    exact x.2))⟩
  left_inv x := by
    ext
    exact add_sub_cancel_right x.1 c
  right_inv x := by
    ext
    exact sub_add_cancel x.1 c
  map_rel_iff' := by
    intro x y
    rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe]
    exact (addRightOrderIso c).map_rel_iff

lemma leftRay (a b : HOrder δ) : Nonempty (↥(Iio a) ≃o ↥(Iio b)) :=
  ⟨(mapIio a).symm.trans (mapIio b)⟩

lemma rightRay (a b : HOrder δ) : Nonempty (↥(Ioi a) ≃o ↥(Ioi b)) :=
  ⟨(mapIoi a).symm.trans (mapIoi b)⟩

lemma coeffZ_add (g h : Gamma δ) (i : OrdIndex δ) :
    coeffZ (g + h) i = coeffZ g i + coeffZ h i := by
  simp [coeffZ, add_apply]

lemma int_add_lt_add_right {p q r : ℤ} (h : p < q) : p + r < q + r :=
  lt_of_le_of_ne (IsOrderedAddMonoid.add_le_add_left p q h.le r)
    (fun heq => h.ne (add_right_cancel heq))

lemma gamma_addRight_lt {s x y : Gamma δ} (h : x < y) : x + s < y + s := by
  rw [Colex.lt_iff] at h ⊢
  obtain ⟨i, hi, hlt⟩ := h
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    rw [← coeffZ, ← coeffZ, coeffZ_add, coeffZ_add, show coeffZ x j = coeffZ y j from hi j hj]
  · rw [← coeffZ, ← coeffZ, coeffZ_add, coeffZ_add]
    exact int_add_lt_add_right (by simpa [coeffZ] using hlt)

lemma gamma_addRight_lt_iff (s x y : Gamma δ) : x + s < y + s ↔ x < y := by
  constructor
  · intro h
    simpa [add_assoc, add_neg_cancel, add_zero] using gamma_addRight_lt (s := -s) h
  · exact gamma_addRight_lt

/-- Translation of the `Γδ` index. -/
noncomputable def gammaAdd (s : Gamma δ) : Gamma δ ≃o Gamma δ where
  toFun g := g + s
  invFun g := g - s
  left_inv g := add_sub_cancel_right g s
  right_inv g := sub_add_cancel g s
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact (gamma_addRight_lt_iff s x y).1 hlt |>.le
      · exact le_of_eq (add_right_cancel heq)
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact (gamma_addRight_lt_iff s x y).2 hlt |>.le
      · exact le_of_eq (congrArg (· + s) heq)

/-- Move rational coefficients along an equivalence of `Γδ`. -/
noncomputable def relabel (e : Gamma δ ≃ Gamma δ) (x : HOrder δ) : HOrder δ :=
  toColex (equivMapDomain e (ofColex x))

lemma coeff_relabel (e : Gamma δ ≃ Gamma δ) (x : HOrder δ) (g : Gamma δ) :
    coeff (relabel e x) (e g) = coeff x g := by
  simp [coeff, relabel, equivMapDomain_apply, ofColex_toColex]

lemma coeff_relabel_symm (e : Gamma δ ≃ Gamma δ) (x : HOrder δ) (j : Gamma δ) :
    coeff (relabel e x) j = coeff x (e.symm j) := by
  simp [coeff, relabel, equivMapDomain_apply, ofColex_toColex]

lemma relabel_zero (e : Gamma δ ≃ Gamma δ) : relabel e (0 : HOrder δ) = 0 := by
  simp [relabel]

lemma relabel_symm (e : Gamma δ ≃ Gamma δ) (x : HOrder δ) :
    relabel e.symm (relabel e x) = x := by
  apply ofColex.injective
  ext g
  simp [relabel, equivMapDomain_apply, ofColex_toColex]

lemma relabel_lt (e : Gamma δ ≃o Gamma δ) {x y : HOrder δ} (h : x < y) :
    relabel e.toEquiv x < relabel e.toEquiv y := by
  rw [Colex.lt_iff] at h ⊢
  obtain ⟨i, hi, hlt⟩ := h
  refine ⟨e.toEquiv i, ?_, ?_⟩
  · intro j hj
    have hjs : i < e.symm j := by
      have hje : e.toEquiv i < e.toEquiv (e.symm j) := by
        simpa [OrderIso.apply_symm_apply] using hj
      exact e.lt_iff_lt.mp hje
    rw [← coeff, ← coeff, coeff_relabel_symm, coeff_relabel_symm]
    exact hi (e.toEquiv.symm j) hjs
  · rw [← coeff, ← coeff, coeff_relabel, coeff_relabel]
    exact hlt

/-- Relabeling along an order automorphism of `Γδ` is an order automorphism of `H(δ)`. -/
noncomputable def relabelOrderIso (e : Gamma δ ≃o Gamma δ) : HOrder δ ≃o HOrder δ where
  toFun := relabel e.toEquiv
  invFun := relabel e.symm.toEquiv
  left_inv := relabel_symm e.toEquiv
  right_inv x := by
    simpa [OrderIso.symm_apply_apply] using relabel_symm e.symm.toEquiv x
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · have hxy := relabel_lt e.symm hlt
        simpa [relabel_symm] using hxy.le
      · exact le_of_eq (by
          simpa [relabel_symm] using congrArg (relabel e.symm.toEquiv) heq)
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · exact (relabel_lt e hlt).le
      · exact le_of_eq (congrArg (relabel e.toEquiv) heq)

lemma relabel_injective (e : Gamma δ ≃ Gamma δ) : Function.Injective (relabel e) := by
  intro x y h
  apply_fun relabel e.symm at h
  simpa [relabel_symm] using h

/-- A vector whose coefficients at and above `g` all vanish. -/
def SupportedBelow (g : Gamma δ) (a : HOrder δ) : Prop :=
  ∀ j, g ≤ j → coeff a j = 0

lemma supportedBelow_smulQ {r : ℚ} {g : Gamma δ} {a : HOrder δ} (ha : SupportedBelow g a) :
    SupportedBelow g (smulQ r a) := by
  intro j hj
  simp [coeff_smulQ, ha j hj]

lemma coeff_sub (a b : HOrder δ) (g : Gamma δ) : coeff (a - b) g = coeff a g - coeff b g := by
  simp [coeff, sub_eq_add_neg, add_apply]

lemma supportedBelow_sub {g : Gamma δ} {a b : HOrder δ}
    (ha : SupportedBelow g a) (hb : SupportedBelow g b) : SupportedBelow g (a - b) := by
  intro j hj
  rw [coeff_sub, ha j hj, hb j hj, sub_zero]

/-- Replace the `g`-coefficient `c` by `factor * c` and add `c` times `lower`. -/
noncomputable def shear (g : Gamma δ) (factor : ℚ) (lower : HOrder δ) (x : HOrder δ) : HOrder δ :=
  (x - smulQ (coeff x g) (basisQ g)) + smulQ (coeff x g) (smulQ factor (basisQ g) + lower)

lemma coeff_basis_self (g : Gamma δ) : coeff (basisQ g) g = 1 := by
  simp [coeff, basisQ, ofColex_toColex, single_eq_same]

lemma coeff_basis_ne {g i : Gamma δ} (h : i ≠ g) : coeff (basisQ g) i = 0 := by
  simp [coeff, basisQ, ofColex_toColex, single_eq_of_ne h]

lemma coeff_shear {g : Gamma δ} {factor : ℚ} {lower x : HOrder δ} (hgl : coeff lower g = 0)
    (i : Gamma δ) :
    coeff (shear g factor lower x) i =
      if i = g then factor * coeff x g else coeff x i + coeff x g * coeff lower i := by
  classical
  by_cases hi : i = g
  · subst hi
    simp [shear, coeff_add, coeff_sub, coeff_smulQ, coeff_basis_self, hgl, mul_comm]
  · simp [shear, coeff_add, coeff_sub, coeff_smulQ, coeff_basis_ne hi, hi]

lemma smulQ_zero (r : ℚ) : smulQ r (0 : HOrder δ) = 0 := by
  simp [smulQ, mapRange_zero]

lemma smulQ_zero_left (a : HOrder δ) : smulQ 0 a = 0 := by
  apply ofColex.injective
  ext i
  simp [smulQ, mapRange_apply, ofColex_toColex]

lemma shear_zero (g : Gamma δ) (factor : ℚ) (lower : HOrder δ) :
    shear g factor lower 0 = 0 := by
  have h0 : coeff (0 : HOrder δ) g = 0 := by simp [coeff]
  unfold shear
  rw [h0, smulQ_zero_left, sub_zero, smulQ_zero_left, add_zero]

lemma shear_add (g : Gamma δ) (factor : ℚ) (lower : HOrder δ) (hgl : coeff lower g = 0)
    (x y : HOrder δ) :
    shear g factor lower (x + y) = shear g factor lower x + shear g factor lower y := by
  classical
  apply ofColex.injective
  ext i
  rw [← coeff, ← coeff, coeff_add, coeff_shear hgl, coeff_shear hgl, coeff_shear hgl, coeff_add]
  by_cases hi : i = g
  · simp only [hi, ite_true, mul_add]
  · simp only [hi, ite_false]
    rw [coeff_add, add_mul]
    calc
      coeff x i + coeff y i + (coeff x g * coeff lower i + coeff y g * coeff lower i)
          = coeff x i + (coeff y i + (coeff x g * coeff lower i + coeff y g * coeff lower i)) := by
            rw [add_assoc]
      _ = coeff x i + (coeff x g * coeff lower i + (coeff y i + coeff y g * coeff lower i)) := by
            rw [add_left_comm (coeff y i) (coeff x g * coeff lower i)]
      _ = coeff x i + coeff x g * coeff lower i + (coeff y i + coeff y g * coeff lower i) := by
            rw [← add_assoc]

lemma shear_neg (g : Gamma δ) (factor : ℚ) (lower : HOrder δ) (hgl : coeff lower g = 0)
    (x : HOrder δ) : shear g factor lower (-x) = -shear g factor lower x := by
  have h := shear_add g factor lower hgl x (-x)
  rw [add_neg_cancel, shear_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

lemma rank_eq_of_witness {a : HOrder δ} (ha : 0 < a) (i : Gamma δ)
    (hi : ∀ j, i < j → coeff a j = 0) (hpos : 0 < coeff a i) : rankOf a ha.ne' = i := by
  have himem : i ∈ (ofColex a).support := mem_support_iff.mpr (by simpa [coeff] using hpos.ne')
  apply le_antisymm
  · apply Finset.max'_le
    intro j hj
    rcases lt_trichotomy j i with hlt | heq | hgt
    · exact hlt.le
    · exact le_of_eq heq
    · exact (mem_support_iff.mp hj (by simpa [coeff] using hi j hgt)).elim
  · exact Finset.le_max' _ i himem

lemma shear_pos {g : Gamma δ} {factor : ℚ} {lower x : HOrder δ} (hf : 0 < factor)
    (hl : SupportedBelow g lower) (hx : 0 < x) : 0 < shear g factor lower x := by
  have hgl : coeff lower g = 0 := hl g le_rfl
  let r := rankOf x hx.ne'
  have hrpos : 0 < coeff x r := coeff_rank_pos hx
  have hrzero : ∀ j, r < j → coeff x j = 0 := fun j hj => coeff_eq_zero_of_rank_lt x hx.ne' hj
  rcases lt_trichotomy r g with hlt | heq | hgt
  · have hcg : coeff x g = 0 := hrzero g hlt
    have hx' : shear g factor lower x = x := by
      apply ofColex.injective
      ext i
      rw [← coeff, ← coeff, coeff_shear hgl]
      by_cases hi : i = g
      · simp [hi, hcg]
      · simp [hi, hcg, mul_zero, add_zero]
    simpa [hx'] using hx
  · have habove : ∀ j, g < j → coeff (shear g factor lower x) j = 0 := by
      intro j hj
      have hxj : coeff x j = 0 := hrzero j (heq ▸ hj)
      have hlj : coeff lower j = 0 := hl j hj.le
      simp [coeff_shear hgl, hj.ne', hxj, hlj]
    have hlead : 0 < coeff (shear g factor lower x) g := by
      simpa [coeff_shear hgl, heq] using rat_mul_lt_mul_left hf hrpos
    rw [Colex.lt_iff]
    refine ⟨g, ?_, ?_⟩
    · intro j hj
      simpa [coeff] using (habove j hj).symm
    · simpa [coeff] using hlead
  · have habove : ∀ j, r < j → coeff (shear g factor lower x) j = 0 := by
      intro j hj
      have hxj : coeff x j = 0 := hrzero j hj
      have hlj : coeff lower j = 0 := hl j (hgt.trans hj).le
      simp [coeff_shear hgl, (hgt.trans hj).ne', hxj, hlj]
    have hlead : 0 < coeff (shear g factor lower x) r := by
      have hlj : coeff lower r = 0 := hl r hgt.le
      rw [coeff_shear hgl, if_neg (Ne.symm hgt.ne), hlj, mul_zero, add_zero]
      exact hrpos
    rw [Colex.lt_iff]
    refine ⟨r, ?_, ?_⟩
    · intro j hj
      simpa [coeff] using (habove j hj).symm
    · simpa [coeff] using hlead

lemma shear_left_inv {g : Gamma δ} {factor : ℚ} {lower : HOrder δ} (hf : factor ≠ 0)
    (hl : SupportedBelow g lower) (x : HOrder δ) :
    shear g factor⁻¹ (smulQ (-factor⁻¹) lower) (shear g factor lower x) = x := by
  classical
  have hgl : coeff lower g = 0 := hl g le_rfl
  have hgl' : coeff (smulQ (-factor⁻¹) lower) g = 0 := by simp [coeff_smulQ, hgl]
  apply ofColex.injective
  ext i
  rw [← coeff, ← coeff, coeff_shear hgl', coeff_smulQ, coeff_shear hgl]
  by_cases hi : i = g
  · simp only [hi, ite_true]
    rw [← mul_assoc, inv_mul_cancel₀ hf, one_mul]
  · simp only [hi, ite_true, ite_false]
    rw [coeff_shear hgl, if_neg hi]
    set c := coeff x g
    set L := coeff lower i
    have hcancel : factor * c * (-factor⁻¹ * L) = -(c * L) := by
      calc
        factor * c * (-factor⁻¹ * L) = factor * (c * (-factor⁻¹ * L)) := by rw [mul_assoc]
        _ = factor * (c * -factor⁻¹ * L) := by rw [mul_assoc]
        _ = factor * (-factor⁻¹ * c * L) := by rw [mul_comm c (-factor⁻¹)]
        _ = factor * (-factor⁻¹ * (c * L)) := by rw [mul_assoc]
        _ = factor * -factor⁻¹ * (c * L) := by rw [mul_assoc]
        _ = -(c * L) := by rw [mul_neg, mul_inv_cancel₀ hf, neg_one_mul]
    rw [hcancel, add_assoc, add_neg_cancel, add_zero]

/-- The triangular change of leading coefficient, as an order automorphism. -/
noncomputable def shearOrderIso (g : Gamma δ) (factor : ℚ) (hf : 0 < factor) (lower : HOrder δ)
    (hl : SupportedBelow g lower) : HOrder δ ≃o HOrder δ where
  toFun := shear g factor lower
  invFun := shear g factor⁻¹ (smulQ (-factor⁻¹) lower)
  left_inv := shear_left_inv hf.ne' hl
  right_inv x := by
    have hl' : SupportedBelow g (smulQ (-factor⁻¹) lower) := supportedBelow_smulQ hl
    have hL : smulQ (-factor) (smulQ (-factor⁻¹) lower) = lower := by
      apply ofColex.injective
      ext i
      simp only [smulQ, mapRange_apply, ofColex_toColex]
      rw [← mul_assoc, neg_mul_neg, mul_inv_cancel₀ hf.ne', one_mul]
    simpa [hL] using shear_left_inv (inv_ne_zero hf.ne') hl' x
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · have hl' : SupportedBelow g (smulQ (-factor⁻¹) lower) := supportedBelow_smulQ hl
        have hpos : 0 < factor⁻¹ := inv_pos.2 hf
        have hdiff : 0 < shear g factor lower y - shear g factor lower x := sub_pos_of_lt hlt
        have hinv := shear_pos hpos hl' hdiff
        have hgl : coeff lower g = 0 := hl g le_rfl
        have hsum : x + (y - x) = y := by
          rw [sub_eq_add_neg, add_comm x, add_assoc, neg_add_cancel, add_zero]
        have hadd := shear_add g factor lower hgl x (y - x)
        rw [hsum] at hadd
        have hdiff' : shear g factor lower y - shear g factor lower x =
            shear g factor lower (y - x) := by
          have hsub := congrArg (fun z => z - shear g factor lower x) hadd
          simpa [add_sub_cancel_left] using hsub
        have hback := shear_left_inv hf.ne' hl (y - x)
        have hlt' : 0 < y - x := by simpa [hdiff', hback] using hinv
        exact (sub_pos.mp hlt').le
      · have hinj : Function.Injective (shear g factor lower) := by
          intro p q hpq
          apply_fun shear g factor⁻¹ (smulQ (-factor⁻¹) lower) at hpq
          simpa [shear_left_inv hf.ne' hl] using hpq
        exact le_of_eq (hinj heq)
    · intro h
      rcases lt_or_eq_of_le h with hlt | heq
      · have hxy : 0 < shear g factor lower (y - x) :=
          shear_pos hf hl (sub_pos_of_lt hlt)
        have hadd := shear_add g factor lower (hl g le_rfl) x (y - x)
        have hsub : x + (y - x) = y := by
          rw [sub_eq_add_neg, add_comm x, add_assoc, neg_add_cancel, add_zero]
        rw [hsub] at hadd
        have hneg : shear g factor lower x + shear g factor lower (y - x) =
            shear g factor lower y := hadd.symm
        have : shear g factor lower x <
            shear g factor lower x + shear g factor lower (y - x) := by
          have h0 := shear_pos hf hl (sub_pos_of_lt hlt)
          simpa [zero_add, add_comm] using addRight_lt (c := shear g factor lower x) h0
        exact this.le.trans_eq hneg
      · exact le_of_eq (congrArg (shear g factor lower) heq)

lemma coeff_eq_zero_above_rank {a : HOrder δ} (ha : 0 < a) {j : Gamma δ}
    (hj : rankOf a ha.ne' < j) : coeff a j = 0 :=
  coeff_eq_zero_of_rank_lt a ha.ne' hj

lemma relabel_pos (e : Gamma δ ≃o Gamma δ) {x : HOrder δ} (hx : 0 < x) :
    0 < relabel e.toEquiv x := by
  simpa [relabel_zero] using relabel_lt e hx

lemma rank_relabel (e : Gamma δ ≃o Gamma δ) {x : HOrder δ} (hx : 0 < x) :
    rankOf (relabel e.toEquiv x) (relabel_pos e hx).ne' = e.toEquiv (rankOf x hx.ne') := by
  refine rank_eq_of_witness (relabel_pos e hx) (e.toEquiv (rankOf x hx.ne')) ?_ ?_
  · intro j hj
    have hjs : rankOf x hx.ne' < e.symm j := by
      have : e.toEquiv (rankOf x hx.ne') < e.toEquiv (e.symm j) := by
        simpa [OrderIso.apply_symm_apply] using hj
      exact e.lt_iff_lt.mp this
    rw [coeff_relabel_symm]
    exact coeff_eq_zero_above_rank hx hjs
  · rw [coeff_relabel]
    exact coeff_rank_pos hx

lemma tail_supported {a : HOrder δ} (ha : 0 < a) (g : Gamma δ)
    (hg : rankOf a ha.ne' = g) :
    SupportedBelow g (a - smulQ (coeff a g) (basisQ g)) := by
  intro j hj
  by_cases hje : j = g
  · subst hje
    rw [coeff_sub, coeff_smulQ, coeff_basis_self, mul_one, sub_self]
  · have hlt : g < j := lt_of_le_of_ne hj (Ne.symm hje)
    rw [coeff_sub, coeff_smulQ, coeff_basis_ne hje, mul_zero, sub_zero]
    exact coeff_eq_zero_above_rank ha (by simpa [hg] using hlt)

lemma smulQ_mul (r s : ℚ) (a : HOrder δ) : smulQ r (smulQ s a) = smulQ (r * s) a := by
  apply ofColex.injective
  ext i
  simp [smulQ, mapRange_apply, ofColex_toColex, mul_assoc]

lemma gammaAdd_toEquiv (s g : Gamma δ) : (gammaAdd s).toEquiv g = g + s := rfl

lemma rank_shifted (p q : HOrder δ) (hp : 0 < p) (hq : 0 < q) :
    rankOf (relabel (gammaAdd (rankOf q hq.ne' - rankOf p hp.ne')).toEquiv p)
        (relabel_pos (gammaAdd (rankOf q hq.ne' - rankOf p hp.ne')) hp).ne' =
      rankOf q hq.ne' := by
  have hsum : rankOf p hp.ne' + (rankOf q hq.ne' - rankOf p hp.ne') = rankOf q hq.ne' := by
    rw [sub_eq_add_neg, add_comm (rankOf p hp.ne'), add_assoc, neg_add_cancel, add_zero]
  rw [rank_relabel (hx := hp), gammaAdd_toEquiv]
  exact hsum

lemma coeff_shifted_pos (p q : HOrder δ) (hp : 0 < p) (hq : 0 < q) :
    0 < coeff (relabel (gammaAdd (rankOf q hq.ne' - rankOf p hp.ne')).toEquiv p)
      (rankOf q hq.ne') := by
  have h := coeff_rank_pos
    (relabel_pos (gammaAdd (rankOf q hq.ne' - rankOf p hp.ne')) hp)
  simpa [rank_shifted p q hp hq] using h

lemma align_lower_supported (p q : HOrder δ) (hp : 0 < p) (hq : 0 < q) :
    let rq := rankOf q hq.ne'
    let p' := relabel (gammaAdd (rq - rankOf p hp.ne')).toEquiv p
    let cp := coeff p' rq
    let w := q - smulQ (coeff q rq) (basisQ rq)
    let v := p' - smulQ cp (basisQ rq)
    SupportedBelow rq (smulQ cp⁻¹ (w - v)) := by
  intro rq p' cp w v
  exact supportedBelow_smulQ
    (supportedBelow_sub (tail_supported hq rq rfl)
      (tail_supported (relabel_pos (gammaAdd (rq - rankOf p hp.ne')) hp) rq
        (rank_shifted p q hp hq)))

lemma shear_hits (p q : HOrder δ) (hp : 0 < p) (hq : 0 < q) :
    let rq := rankOf q hq.ne'
    let p' := relabel (gammaAdd (rq - rankOf p hp.ne')).toEquiv p
    let cp := coeff p' rq
    let cq := coeff q rq
    let lower := smulQ cp⁻¹
      ((q - smulQ cq (basisQ rq)) - (p' - smulQ cp (basisQ rq)))
    shear rq (cq / cp) lower p' = q := by
  intro rq p' cp cq lower
  have hcp : 0 < cp := coeff_shifted_pos p q hp hq
  have hcq : 0 < cq := by
    simpa [rq, cq] using coeff_rank_pos hq
  have hgl : coeff lower rq = 0 := align_lower_supported p q hp hq rq le_rfl
  apply ofColex.injective
  ext i
  rw [← coeff, ← coeff, coeff_shear hgl]
  by_cases hi : i = rq
  · simp only [hi, ite_true]
    rw [div_mul_cancel₀ _ hcp.ne']
  · simp only [hi, ite_false]
    have htail : coeff (p' - smulQ cp (basisQ rq)) i = coeff p' i := by
      rw [coeff_sub, coeff_smulQ, coeff_basis_ne hi, mul_zero, sub_zero]
    have hbasis : coeff (basisQ rq) i = 0 := coeff_basis_ne hi
    have hlow : coeff lower i = cp⁻¹ * (coeff q i - coeff p' i) := by
      rw [show lower = smulQ cp⁻¹ ((q - smulQ cq (basisQ rq)) - (p' - smulQ cp (basisQ rq))) from rfl]
      rw [coeff_smulQ, coeff_sub, coeff_sub, coeff_smulQ]
      rw [hbasis, htail, mul_zero, sub_zero]
    rw [hlow, show coeff p' rq = cp from rfl, ← mul_assoc, mul_inv_cancel₀ hcp.ne', one_mul]
    rw [sub_eq_add_neg, add_comm (coeff p' i), add_assoc, neg_add_cancel, add_zero]

/-- An order automorphism fixing `0` and carrying one positive vector onto another. -/
noncomputable def positiveAlign (p q : HOrder δ) (hp : 0 < p) (hq : 0 < q) :
    HOrder δ ≃o HOrder δ :=
  let rq := rankOf q hq.ne'
  let p' := relabel (gammaAdd (rq - rankOf p hp.ne')).toEquiv p
  let cp := coeff p' rq
  let cq := coeff q rq
  let lower := smulQ cp⁻¹
    ((q - smulQ cq (basisQ rq)) - (p' - smulQ cp (basisQ rq)))
  (relabelOrderIso (gammaAdd (rq - rankOf p hp.ne'))).trans
    (shearOrderIso rq (cq / cp) (div_pos (by simpa [cq] using coeff_rank_pos hq)
      (coeff_shifted_pos p q hp hq)) lower (align_lower_supported p q hp hq))

lemma positiveAlign_zero (p q : HOrder δ) (hp : 0 < p) (hq : 0 < q) :
    positiveAlign p q hp hq 0 = 0 := by
  unfold positiveAlign
  rw [OrderIso.trans_apply]
  change shear _ _ _ (relabel _ 0) = 0
  rw [relabel_zero, shear_zero]

lemma positiveAlign_apply (p q : HOrder δ) (hp : 0 < p) (hq : 0 < q) :
    positiveAlign p q hp hq p = q := by
  unfold positiveAlign
  rw [OrderIso.trans_apply]
  exact shear_hits p q hp hq

/-- Translate so that `a` goes to `c` and the displacement is transformed by `φ`. -/
noncomputable def translateConj (a c : HOrder δ) (φ : HOrder δ ≃o HOrder δ) :
    HOrder δ ≃o HOrder δ :=
  (addRightOrderIso a).symm.trans (φ.trans (addRightOrderIso c))

lemma translateConj_apply (a c : HOrder δ) (φ : HOrder δ ≃o HOrder δ) (x : HOrder δ) :
    translateConj a c φ x = φ (x - a) + c := by
  simp [translateConj, OrderIso.trans_apply, addRightOrderIso]

noncomputable def mapIoo (f : HOrder δ ≃o HOrder δ) {a b c d : HOrder δ}
    (hfa : f a = c) (hfb : f b = d) : ↥(Ioo a b) ≃o ↥(Ioo c d) where
  toFun x := ⟨f x.1, mem_Ioo.2 ⟨
    hfa ▸ (f.lt_iff_lt.mpr x.2.1),
    hfb ▸ (f.lt_iff_lt.mpr x.2.2)⟩⟩
  invFun y :=
    let hsa : f.symm c = a := by rw [← hfa, f.symm_apply_apply]
    let hsb : f.symm d = b := by rw [← hfb, f.symm_apply_apply]
    ⟨f.symm y.1, mem_Ioo.2 ⟨
      hsa ▸ (f.symm.lt_iff_lt.mpr y.2.1),
      hsb ▸ (f.symm.lt_iff_lt.mpr y.2.2)⟩⟩
  left_inv x := by
    ext
    exact f.symm_apply_apply x.1
  right_inv y := by
    ext
    exact f.apply_symm_apply y.1
  map_rel_iff' := by
    intro x y
    rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe]
    exact f.map_rel_iff

lemma interval (a b c d : HOrder δ) (hab : a < b) (hcd : c < d) :
    Nonempty (↥(Ioo a b) ≃o ↥(Ioo c d)) := by
  let φ := positiveAlign (b - a) (d - c) (sub_pos_of_lt hab) (sub_pos_of_lt hcd)
  let ψ := translateConj a c φ
  have ha : ψ a = c := by
    rw [translateConj_apply, sub_self, positiveAlign_zero, zero_add]
  have hb : ψ b = d := by
    rw [translateConj_apply, positiveAlign_apply, sub_add_cancel]
  exact ⟨mapIoo ψ ha hb⟩

end HOrder

end
end AEC
