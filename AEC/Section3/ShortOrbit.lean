module

public import AEC.Section3.Occupancy
public import AEC.Section3.OrderEqualityDiagram
public import AEC.Section3.Segment
public import Mathlib.Order.Hom.Basic
public import Mathlib.SetTheory.Cardinal.Cofinality.Basic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

@[expose] public section

namespace AEC
section

universe u v

open Cardinal Classical Set

variable {α : Type v} [LinearOrder α]

/-- A nonempty linear order with no greatest element has infinite cofinality. -/
lemma aleph0_le_orderCof [Nonempty α] [NoMaxOrder α] : ℵ₀ ≤ Order.cof α :=
  Order.aleph0_le_cof

/-- The cofinality of a nonempty linear order with no greatest element is a regular cardinal. -/
lemma isRegular_orderCof [Nonempty α] [NoMaxOrder α] : Cardinal.IsRegular (Order.cof α) := by
  refine ⟨aleph0_le_orderCof, ?_⟩
  by_contra hbad
  let κ : Cardinal.{v} := Order.cof α
  have hκ : ℵ₀ ≤ κ := aleph0_le_orderCof
  have hne : κ.ord.cof ≠ κ := fun h => hbad (le_of_eq h.symm)
  have hcof : κ.ord.cof < κ := lt_of_le_of_ne (Ordinal.cof_ord_le κ) hne
  obtain ⟨t, ht, hcard⟩ := Order.exists_cof_eq α
  have heq : #(κ.ord.ToType) = #↥t := by
    rw [Cardinal.mk_ord_toType, hcard]
  obtain ⟨e⟩ := Cardinal.eq.mp heq
  obtain ⟨s, hs, hsType⟩ := Ordinal.exists_ord_cof_eq (κ.ord.ToType)
  have hsType' : Ordinal.type (α := ↥s) (· < ·) = κ.ord.cof.ord := by
    rw [hsType, Ordinal.cof_toType]
  have hscard : #↥s = κ.ord.cof := by
    rw [← Ordinal.card_type (α := ↥s) (· < ·), hsType', Cardinal.card_ord]
  have hslt : #↥s < κ := hscard.symm ▸ hcof
  let piece : ↥s → Set α := fun i =>
    (fun j : κ.ord.ToType => (e j : α)) '' Iic (i : κ.ord.ToType)
  have hpiece : ∀ i, ¬ IsCofinal (piece i) := by
    intro i hcofP
    have hκ' : ℵ₀ ≤ #(κ.ord.ToType) := by
      rw [Cardinal.mk_ord_toType]
      exact hκ
    have htype : Cardinal.ord #(κ.ord.ToType) = Ordinal.type (α := κ.ord.ToType) (· < ·) := by
      rw [Cardinal.mk_ord_toType, Ordinal.type_toType]
    have hI : #(Iic (i : κ.ord.ToType)) < κ := by
      simpa [Cardinal.mk_ord_toType] using Cardinal.mk_Iic_lt (i : κ.ord.ToType) htype hκ'
    have hsmall : #(piece i) < κ := lt_of_le_of_lt Cardinal.mk_image_le hI
    exact lt_irrefl κ ((Order.cof_le hcofP).trans_lt hsmall)
  have hunion : IsCofinal (⋃ i, piece i) := by
    intro x
    obtain ⟨y, hy, hle⟩ := ht x
    let j : κ.ord.ToType := e.symm ⟨y, hy⟩
    obtain ⟨i, hi, hj⟩ := hs j
    have hyj : (e j : α) = y := by
      have happ : e (e.symm ⟨y, hy⟩) = ⟨y, hy⟩ := e.apply_symm_apply _
      exact congrArg Subtype.val happ
    refine ⟨y, ?_, hle⟩
    rw [← hyj]
    exact mem_iUnion.2 ⟨⟨i, hi⟩, mem_image_of_mem _ hj⟩
  obtain ⟨i, hi⟩ := isCofinal_of_isCofinal_iUnion hunion hslt
  exact hpiece i hi

lemma setCofinality_eq_orderCof (s : Set α) : setCofinality s = Order.cof (↥s) := by
  by_cases hne : s.Nonempty
  · obtain ⟨t, ht, hcard, hcof⟩ := exists_setCofinality_witness s hne
    apply le_antisymm
    · obtain ⟨u, hu, hucard⟩ := Order.exists_cof_eq (↥s)
      refine (HOrder.setCofinality_le (t := Subtype.val '' u) ?_ ?_).trans
        (Cardinal.mk_image_le.trans_eq hucard)
      · intro x hx
        obtain ⟨z, hz, rfl⟩ := hx
        exact z.2
      · intro x hx
        obtain ⟨z, hz, hle⟩ := hu ⟨x, hx⟩
        exact ⟨z.1, mem_image_of_mem _ hz, hle⟩
    · rw [← hcard]
      let u : Set (↥s) := {z | z.1 ∈ t}
      have huco : IsCofinal u := by
        intro z
        obtain ⟨y, hy, hle⟩ := hcof z.1 z.2
        exact ⟨⟨y, ht hy⟩, hy, hle⟩
      have hbij : #u = #t := by
        refine Cardinal.eq.mpr ⟨?_⟩
        exact
          { toFun := fun z => ⟨z.1.1, z.2⟩
            invFun := fun y => ⟨⟨y.1, ht y.2⟩, y.2⟩
            left_inv := fun z => Subtype.ext (Subtype.ext rfl)
            right_inv := fun y => Subtype.ext rfl }
      exact (Order.cof_le huco).trans_eq hbij
  · have hempty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    haveI : IsEmpty (↥s) := by
      rw [hempty]
      infer_instance
    rw [Order.cof_eq_zero]
    unfold setCofinality
    refine le_antisymm ?_ ?_
    · apply csInf_le'
      refine ⟨∅, hempty ▸ empty_subset s, ?_, ?_⟩
      · simp
      · intro x hx
        exact (hempty ▸ hx).elim
    · refine (le_csInf_iff' ?_).2 ?_
      · exact ⟨0, ∅, hempty ▸ empty_subset s, by simp, fun x hx => (hempty ▸ hx).elim⟩
      · rintro κ ⟨t, ht, rfl, _⟩
        have : t = ∅ := subset_eq_empty ht hempty
        simp [this]

/-- Cofinality of a nonempty subset with no greatest element is an infinite regular cardinal. -/
lemma isRegular_setCofinality {s : Set α} (hne : s.Nonempty)
    (hno : ∀ a ∈ s, ∃ b ∈ s, a < b) : Cardinal.IsRegular (setCofinality s) := by
  haveI : Nonempty (↥s) := nonempty_subtype.mpr hne
  haveI : NoMaxOrder (↥s) := ⟨fun a =>
    let ⟨b, hb, hlt⟩ := hno a.1 a.2
    ⟨⟨b, hb⟩, hlt⟩⟩
  simpa [setCofinality_eq_orderCof s] using isRegular_orderCof (α := ↥s)

end

section Adjoin

variable {L : Type v} [LinearOrder L]

/-- Add the greatest element to an isomorphism of the strict lower parts. -/
noncomputable def adjoinGreatest {s t : Set L} {a b : L} (ha : a ∈ s) (hb : b ∈ t)
    (hsa : ∀ x ∈ s, x ≤ a) (htb : ∀ y ∈ t, y ≤ b)
    (e : ↥{x | x ∈ s ∧ x < a} ≃o ↥{y | y ∈ t ∧ y < b}) : ↥s ≃o ↥t where
  toFun x :=
    if h : (x : L) = a then ⟨b, hb⟩
    else ⟨e ⟨x, x.2, lt_of_le_of_ne (hsa x x.2) h⟩, (e ⟨x, x.2, lt_of_le_of_ne (hsa x x.2) h⟩).2.1⟩
  invFun y :=
    if h : (y : L) = b then ⟨a, ha⟩
    else ⟨e.symm ⟨y, y.2, lt_of_le_of_ne (htb y y.2) h⟩,
      (e.symm ⟨y, y.2, lt_of_le_of_ne (htb y y.2) h⟩).2.1⟩
  left_inv x := by
    ext
    by_cases h : (x : L) = a
    · simp [h]
    · have hx : (x : L) < a := lt_of_le_of_ne (hsa x x.2) h
      have hne : (e ⟨x, x.2, hx⟩ : L) ≠ b := (e ⟨x, x.2, hx⟩).2.2.ne
      simp [h, hx, hne, OrderIso.symm_apply_apply]
  right_inv y := by
    ext
    by_cases h : (y : L) = b
    · simp [h]
    · have hy : (y : L) < b := lt_of_le_of_ne (htb y y.2) h
      have hne : (e.symm ⟨y, y.2, hy⟩ : L) ≠ a := (e.symm ⟨y, y.2, hy⟩).2.2.ne
      simp [h, hy, hne, OrderIso.apply_symm_apply]
  map_rel_iff' {x y} := by
    by_cases hx : (x : L) = a
    · by_cases hy : (y : L) = a
      · have hxy : x = y := Subtype.ext (hx.trans hy.symm)
        simp [hxy]
      · have hy' : (y : L) < a := lt_of_le_of_ne (hsa y y.2) hy
        constructor
        · intro hle
          rw [← Subtype.coe_le_coe] at hle
          simp [hx, hy] at hle
          exact (not_le_of_gt (e ⟨y, y.2, hy'⟩).2.2 hle).elim
        · intro hle
          have hlt : (y : L) < (x : L) := by
            rw [hx]
            exact hy'
          exact (not_le_of_gt hlt (Subtype.coe_le_coe.mpr hle)).elim
    · by_cases hy : (y : L) = a
      · have hx' : (x : L) < a := lt_of_le_of_ne (hsa x x.2) hx
        constructor
        · intro _
          rw [← Subtype.coe_le_coe, hy]
          exact hsa x x.2
        · intro _
          rw [← Subtype.coe_le_coe]
          simp [hx, hy]
          exact (e ⟨x, x.2, hx'⟩).2.2.le
      · have hx' : (x : L) < a := lt_of_le_of_ne (hsa x x.2) hx
        have hy' : (y : L) < a := lt_of_le_of_ne (hsa y y.2) hy
        constructor
        · intro hle
          rw [← Subtype.coe_le_coe] at hle
          have hle' : (e ⟨x, x.2, hx'⟩ : L) ≤ e ⟨y, y.2, hy'⟩ := by
            simpa [hx, hy] using hle
          have hsub : (⟨(x : L), x.2, hx'⟩ : ↥{z | z ∈ s ∧ z < a}) ≤ ⟨y, y.2, hy'⟩ :=
            (Subtype.coe_le_coe).mp (e.map_rel_iff.mp ((Subtype.coe_le_coe).mpr hle'))
          exact (Subtype.coe_le_coe).mp hsub
        · intro hle
          rw [← Subtype.coe_le_coe]
          have hsub : (⟨(x : L), x.2, hx'⟩ : ↥{z | z ∈ s ∧ z < a}) ≤ ⟨y, y.2, hy'⟩ :=
            (Subtype.coe_le_coe).mpr hle
          have hle' : (e ⟨x, x.2, hx'⟩ : L) ≤ e ⟨y, y.2, hy'⟩ :=
            (Subtype.coe_le_coe).mp (e.map_rel_iff.mpr hsub)
          simpa [hx, hy] using hle'

/-- Add the least element to an isomorphism of the strict upper parts. -/
noncomputable def adjoinLeast {s t : Set L} {a b : L} (ha : a ∈ s) (hb : b ∈ t)
    (hsa : ∀ x ∈ s, a ≤ x) (htb : ∀ y ∈ t, b ≤ y)
    (e : ↥{x | x ∈ s ∧ a < x} ≃o ↥{y | y ∈ t ∧ b < y}) : ↥s ≃o ↥t where
  toFun x :=
    if h : (x : L) = a then ⟨b, hb⟩
    else ⟨e ⟨x, x.2, lt_of_le_of_ne (hsa x x.2) (Ne.symm h)⟩,
      (e ⟨x, x.2, lt_of_le_of_ne (hsa x x.2) (Ne.symm h)⟩).2.1⟩
  invFun y :=
    if h : (y : L) = b then ⟨a, ha⟩
    else ⟨e.symm ⟨y, y.2, lt_of_le_of_ne (htb y y.2) (Ne.symm h)⟩,
      (e.symm ⟨y, y.2, lt_of_le_of_ne (htb y y.2) (Ne.symm h)⟩).2.1⟩
  left_inv x := by
    ext
    by_cases h : (x : L) = a
    · simp [h]
    · have hx : a < (x : L) := lt_of_le_of_ne (hsa x x.2) (Ne.symm h)
      have hne : (e ⟨x, x.2, hx⟩ : L) ≠ b := Ne.symm (ne_of_lt (e ⟨x, x.2, hx⟩).2.2)
      simp [h, hx, hne, OrderIso.symm_apply_apply]
  right_inv y := by
    ext
    by_cases h : (y : L) = b
    · simp [h]
    · have hy : b < (y : L) := lt_of_le_of_ne (htb y y.2) (Ne.symm h)
      have hne : (e.symm ⟨y, y.2, hy⟩ : L) ≠ a :=
        Ne.symm (ne_of_lt (e.symm ⟨y, y.2, hy⟩).2.2)
      simp [h, hy, hne, OrderIso.apply_symm_apply]
  map_rel_iff' {x y} := by
    by_cases hx : (x : L) = a
    · by_cases hy : (y : L) = a
      · have hxy : x = y := Subtype.ext (hx.trans hy.symm)
        simp [hxy]
      · have hy' : a < (y : L) := lt_of_le_of_ne (hsa y y.2) (Ne.symm hy)
        constructor
        · intro _
          rw [← Subtype.coe_le_coe, hx]
          exact hsa y y.2
        · intro _
          rw [← Subtype.coe_le_coe]
          simp [hx, hy]
          exact (e ⟨y, y.2, hy'⟩).2.2.le
    · by_cases hy : (y : L) = a
      · have hx' : a < (x : L) := lt_of_le_of_ne (hsa x x.2) (Ne.symm hx)
        constructor
        · intro hle
          rw [← Subtype.coe_le_coe] at hle
          simp [hx, hy] at hle
          exact (not_le_of_gt (e ⟨x, x.2, hx'⟩).2.2 hle).elim
        · intro hle
          have hlt : (y : L) < (x : L) := by
            rw [hy]
            exact hx'
          exact (not_le_of_gt hlt (Subtype.coe_le_coe.mpr hle)).elim
      · have hx' : a < (x : L) := lt_of_le_of_ne (hsa x x.2) (Ne.symm hx)
        have hy' : a < (y : L) := lt_of_le_of_ne (hsa y y.2) (Ne.symm hy)
        constructor
        · intro hle
          rw [← Subtype.coe_le_coe] at hle
          have hle' : (e ⟨x, x.2, hx'⟩ : L) ≤ e ⟨y, y.2, hy'⟩ := by
            simpa [hx, hy] using hle
          have hsub : (⟨(x : L), x.2, hx'⟩ : ↥{z | z ∈ s ∧ a < z}) ≤ ⟨y, y.2, hy'⟩ :=
            (Subtype.coe_le_coe).mp (e.map_rel_iff.mp ((Subtype.coe_le_coe).mpr hle'))
          exact (Subtype.coe_le_coe).mp hsub
        · intro hle
          rw [← Subtype.coe_le_coe]
          have hsub : (⟨(x : L), x.2, hx'⟩ : ↥{z | z ∈ s ∧ a < z}) ≤ ⟨y, y.2, hy'⟩ :=
            (Subtype.coe_le_coe).mpr hle
          have hle' : (e ⟨x, x.2, hx'⟩ : L) ≤ e ⟨y, y.2, hy'⟩ :=
            (Subtype.coe_le_coe).mp (e.map_rel_iff.mpr hsub)
          simpa [hx, hy] using hle'

end Adjoin

section Rays

open Set

variable {δ : _root_.Ordinal.{u}}

/-- The order type of `(−∞, p]` depends only on the endpoint, by ray homogeneity. -/
noncomputable def iicIso (a b : HOrder δ) : ↥(Iic a) ≃o ↥(Iic b) := by
  let e := Classical.choice (HOrder.leftRay a b)
  have hsa : {x | x ∈ Iic a ∧ x < a} = Iio a := by
    ext z
    constructor
    · intro h
      exact mem_Iio.mpr h.2
    · intro h
      exact ⟨mem_Iic.mpr (mem_Iio.mp h).le, mem_Iio.mp h⟩
  have hsb : {y | y ∈ Iic b ∧ y < b} = Iio b := by
    ext z
    constructor
    · intro h
      exact mem_Iio.mpr h.2
    · intro h
      exact ⟨mem_Iic.mpr (mem_Iio.mp h).le, mem_Iio.mp h⟩
  let ea : ↥{x | x ∈ Iic a ∧ x < a} ≃o ↥(Iio a) :=
    ({x | x ∈ Iic a ∧ x < a} : Set (HOrder δ)).orderIsoOfEq (Iio a) hsa
  let eb : ↥(Iio b) ≃o ↥{y | y ∈ Iic b ∧ y < b} :=
    (Iio b).orderIsoOfEq {y | y ∈ Iic b ∧ y < b} hsb.symm
  exact adjoinGreatest (mem_Iic.mpr (le_rfl : a ≤ a)) (mem_Iic.mpr (le_rfl : b ≤ b))
    (fun x hx => mem_Iic.mp hx) (fun y hy => mem_Iic.mp hy) (ea.trans (e.trans eb))

/-- The order type of `[p, +∞)` depends only on the endpoint, by ray homogeneity. -/
noncomputable def iciIso (a b : HOrder δ) : ↥(Ici a) ≃o ↥(Ici b) := by
  let e := Classical.choice (HOrder.rightRay a b)
  have hsa : {x | x ∈ Ici a ∧ a < x} = Ioi a := by
    ext z
    constructor
    · intro h
      exact mem_Ioi.mpr h.2
    · intro h
      exact ⟨mem_Ici.mpr (mem_Ioi.mp h).le, mem_Ioi.mp h⟩
  have hsb : {y | y ∈ Ici b ∧ b < y} = Ioi b := by
    ext z
    constructor
    · intro h
      exact mem_Ioi.mpr h.2
    · intro h
      exact ⟨mem_Ici.mpr (mem_Ioi.mp h).le, mem_Ioi.mp h⟩
  let ea : ↥{x | x ∈ Ici a ∧ a < x} ≃o ↥(Ioi a) :=
    ({x | x ∈ Ici a ∧ a < x} : Set (HOrder δ)).orderIsoOfEq (Ioi a) hsa
  let eb : ↥(Ioi b) ≃o ↥{y | y ∈ Ici b ∧ b < y} :=
    (Ioi b).orderIsoOfEq {y | y ∈ Ici b ∧ b < y} hsb.symm
  exact adjoinLeast (mem_Ici.mpr (le_rfl : a ≤ a)) (mem_Ici.mpr (le_rfl : b ≤ b))
    (fun x hx => mem_Ici.mp hx) (fun y hy => mem_Ici.mp hy) (ea.trans (e.trans eb))

end Rays

end AEC
