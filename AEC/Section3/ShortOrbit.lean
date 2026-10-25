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

/-- Coinitiality of a nonempty subset with no least element is an infinite regular cardinal. -/
lemma isRegular_setCoinitiality {s : Set α} (hne : s.Nonempty)
    (hno : ∀ a ∈ s, ∃ b ∈ s, b < a) : Cardinal.IsRegular (setCoinitiality s) := by
  have hne' : (OrderDual.toDual '' s).Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨OrderDual.toDual a, mem_image_of_mem _ ha⟩
  have hno' : ∀ a ∈ OrderDual.toDual '' s, ∃ b ∈ OrderDual.toDual '' s, a < b := by
    intro a ha
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b, hb, hba⟩ := hno a' ha'
    exact ⟨OrderDual.toDual b, mem_image_of_mem _ hb, OrderDual.toDual_lt_toDual.mpr hba⟩
  simpa [setCoinitiality] using isRegular_setCofinality hne' hno'

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

/-- The order type of `(a, p]` depends only on the endpoints, by bounded-interval homogeneity. -/
noncomputable def iocIso {a b c d : HOrder δ} (hab : a < b) (hcd : c < d) :
    ↥(rightHalf a b) ≃o ↥(rightHalf c d) :=
  halfOpenRight hab hcd (Classical.choice (HOrder.interval a b c d hab hcd))

/-- The order type of `[p, b)` depends only on the endpoints, by bounded-interval homogeneity. -/
noncomputable def icoIso {a b c d : HOrder δ} (hab : a < b) (hcd : c < d) :
    ↥(Ico a b) ≃o ↥(Ico c d) := by
  let e := Classical.choice (HOrder.interval a b c d hab hcd)
  have hsa : {x | x ∈ Ico a b ∧ a < x} = Ioo a b := by
    ext z
    constructor
    · intro h
      exact mem_Ioo.mpr ⟨h.2, (mem_Ico.mp h.1).2⟩
    · intro h
      have hz := mem_Ioo.mp h
      exact ⟨mem_Ico.mpr ⟨hz.1.le, hz.2⟩, hz.1⟩
  have hsb : {y | y ∈ Ico c d ∧ c < y} = Ioo c d := by
    ext z
    constructor
    · intro h
      exact mem_Ioo.mpr ⟨h.2, (mem_Ico.mp h.1).2⟩
    · intro h
      have hz := mem_Ioo.mp h
      exact ⟨mem_Ico.mpr ⟨hz.1.le, hz.2⟩, hz.1⟩
  let ea : ↥{x | x ∈ Ico a b ∧ a < x} ≃o ↥(Ioo a b) :=
    ({x | x ∈ Ico a b ∧ a < x} : Set (HOrder δ)).orderIsoOfEq (Ioo a b) hsa
  let eb : ↥(Ioo c d) ≃o ↥{y | y ∈ Ico c d ∧ c < y} :=
    (Ioo c d).orderIsoOfEq {y | y ∈ Ico c d ∧ c < y} hsb.symm
  exact adjoinLeast (mem_Ico.mpr ⟨le_rfl, hab⟩) (mem_Ico.mpr ⟨le_rfl, hcd⟩)
    (fun x hx => (mem_Ico.mp hx).1) (fun y hy => (mem_Ico.mp hy).1)
    (ea.trans (e.trans eb))

end Rays

section DownCut

open Cardinal Classical Set

/-- The downward closure written in the third case of Theorem 3.5. -/
def downSet {δ : _root_.Ordinal.{u}} (A : Set (HOrder δ)) : Set (HOrder δ) :=
  {x | ∃ a ∈ A, x ≤ a}

/-- The cut `(D, H(δ) \ D)` of that downward closure. -/
def downCut {δ : _root_.Ordinal.{u}} (A : Set (HOrder δ)) : Cut (HOrder δ) where
  lower := downSet A
  upper := (downSet A)ᶜ
  union_eq := Set.union_compl_self _
  disjoint := by
    rw [Set.disjoint_left]
    intro x hx hxu
    exact hxu hx
  ordered := by
    intro a ha b hb
    obtain ⟨c, hc, hle⟩ := ha
    have hcb : c < b := by
      by_contra hge
      exact hb ⟨c, hc, le_of_not_gt hge⟩
    exact hle.trans_lt hcb

lemma cofinality_downSet {δ : _root_.Ordinal.{u}} {A : Set (HOrder δ)} (hne : A.Nonempty) :
    setCofinality (downSet A) = setCofinality A := by
  have hdown : (downSet A).Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, a, ha, le_rfl⟩
  apply le_antisymm
  · obtain ⟨t, ht, hcard, hcof⟩ := exists_setCofinality_witness A hne
    refine (HOrder.setCofinality_le (t := t) ?_ ?_).trans_eq hcard
    · intro x hx
      exact ⟨x, ht hx, le_rfl⟩
    · intro x hx
      obtain ⟨a, ha, hle⟩ := hx
      obtain ⟨y, hy, hay⟩ := hcof a ha
      exact ⟨y, hy, hle.trans hay⟩
  · obtain ⟨t, ht, hcard, hcof⟩ := exists_setCofinality_witness (downSet A) hdown
    let pick : ↥t → HOrder δ := fun y => Classical.choose (ht y.2)
    have hpick : ∀ y : ↥t, pick y ∈ A ∧ (y : HOrder δ) ≤ pick y :=
      fun y => Classical.choose_spec (ht y.2)
    refine (HOrder.setCofinality_le (t := Set.range pick) ?_ ?_).trans
      (Cardinal.mk_range_le.trans (le_of_eq hcard))
    · rintro _ ⟨y, rfl⟩
      exact (hpick y).1
    · intro a ha
      obtain ⟨y, hy, hle⟩ := hcof a ⟨a, ha, le_rfl⟩
      let z : ↥t := ⟨y, hy⟩
      refine ⟨pick z, ?_, hle.trans (hpick z).2⟩
      exact ⟨z, rfl⟩

lemma downSet_no_greatest {δ : _root_.Ordinal.{u}} {A : Set (HOrder δ)}
    (hno : ∀ a ∈ A, ∃ b ∈ A, a < b) :
    ∀ a ∈ downSet A, ∃ b ∈ downSet A, a < b := by
  intro x hx
  obtain ⟨a, ha, hle⟩ := hx
  obtain ⟨b, hb, hab⟩ := hno a ha
  exact ⟨b, ⟨b, hb, le_rfl⟩, hle.trans_lt hab⟩

lemma mem_downCut_upper {δ : _root_.Ordinal.{u}} {A : Set (HOrder δ)} {p : HOrder δ}
    (hp : ∀ a ∈ A, a < p) : p ∈ (downCut A).upper := by
  intro h
  obtain ⟨a, ha, hle⟩ := h
  exact not_le_of_gt (hp a ha) hle

lemma downCut_no_least {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {A : Set (HOrder δ)}
    (hcard : #A ≤ Cardinal.lift.{u + 1} θ)
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hne : A.Nonempty) (b : HOrder δ) (hb : b ∈ (downCut A).upper) :
    ∃ a ∈ (downCut A).upper, a < b := by
  by_contra hnone
  have hleast : ∀ a ∈ (downCut A).upper, ¬ a < b := by
    intro a ha hlt
    exact hnone ⟨a, ha, hlt⟩
  have heq : downSet A = Set.Iio b := by
    ext x
    constructor
    · intro hx
      exact Set.mem_Iio.mpr ((downCut A).ordered x hx b hb)
    · intro hx
      have hxlt : x < b := Set.mem_Iio.mp hx
      have hxU : x ∉ (downSet A)ᶜ := by
        intro hxu
        exact (hleast x hxu hxlt).elim
      simpa [Set.mem_compl_iff] using hxU
  have hcofA : setCofinality A ≤ Cardinal.lift.{u + 1} θ :=
    (HOrder.setCofinality_le (t := A) (fun _ hx => hx) (fun x hx => ⟨x, hx, le_rfl⟩)).trans hcard
  have hsmall : setCofinality (downSet A) < Cardinal.lift.{u + 1} (Ordinal.cof δ) :=
    ((cofinality_downSet hne).trans_le hcofA).trans_lt hcf
  have hpoint : setCofinality (Set.Iio b) = Cardinal.lift.{u + 1} (Ordinal.cof δ) :=
    HOrder.leftChar hδ b
  exact lt_irrefl _ ((heq ▸ hpoint).symm ▸ hsmall)

lemma downCut_interior {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {A : Set (HOrder δ)} {p : HOrder δ}
    (hcard : #A ≤ Cardinal.lift.{u + 1} θ)
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hne : A.Nonempty) (hno : ∀ a ∈ A, ∃ b ∈ A, a < b) (hp : ∀ a ∈ A, a < p) :
    Cut.IsInteriorNonprincipal (downCut A) where
  lower_nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, a, ha, le_rfl⟩
  upper_nonempty := ⟨p, mem_downCut_upper hp⟩
  lower_no_greatest := downSet_no_greatest hno
  upper_no_least := fun b hb => downCut_no_least hδ hcard hcf hne b hb

/-- The setup Lemma 3.4 asks for on `H(δ)`. -/
theorem horderSetup {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ) :
    SegmentSetup (HOrder δ) (Cardinal.lift.{u + 1} (Ordinal.cof δ)) where
  dense := HOrder.dense
  noBot := HOrder.noBot
  noTop := HOrder.noTop
  pointChar := fun a => ⟨HOrder.leftChar hδ a, HOrder.rightChar hδ a⟩
  oneInterval := HOrder.interval
  balanced := fun c hc => horder_balanced c hc

/-- The third case: the portion `((D, U), p]` has the order type of Lemma 3.4 at character `cf(A⁻)`. -/
theorem down_upperHead_iso {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}}
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    {A B : Set (HOrder δ)} {p q : HOrder δ}
    (hA : #A ≤ Cardinal.lift.{u + 1} θ) (hB : #B ≤ Cardinal.lift.{u + 1} θ)
    (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hnoA : ∀ a ∈ A, ∃ b ∈ A, a < b) (hnoB : ∀ b ∈ B, ∃ c ∈ B, b < c)
    (hp : ∀ a ∈ A, a < p) (hq : ∀ b ∈ B, b < q)
    (hcof : setCofinality A = setCofinality B) :
    Nonempty (↥(upperHead (downCut A) p) ≃o ↥(upperHead (downCut B) q)) := by
  let ε : Cardinal.{u + 1} := setCofinality A
  have hreg : Cardinal.IsRegular ε := isRegular_setCofinality hneA hnoA
  have hεlt : ε < Cardinal.lift.{u + 1} (Ordinal.cof δ) := by
    have hle : ε ≤ Cardinal.lift.{u + 1} θ :=
      (HOrder.setCofinality_le (t := A) (fun _ hx => hx) (fun x hx => ⟨x, hx, le_rfl⟩)).trans hA
    exact hle.trans_lt hcf
  have hintA := downCut_interior hδ hA hcf hneA hnoA hp
  have hintB := downCut_interior hδ hB hcf hneB hnoB hq
  have hbalA := horder_balanced (downCut A) hintA
  have hbalB := horder_balanced (downCut B) hintB
  have hcharA : (downCut A).characters = (ε, ε) := by
    unfold Cut.characters
    refine Prod.ext (cofinality_downSet hneA) ?_
    exact (hbalA.characters).symm.trans (cofinality_downSet hneA)
  have hcharB : (downCut B).characters = (ε, ε) := by
    unfold Cut.characters
    refine Prod.ext ((cofinality_downSet hneB).trans hcof.symm) ?_
    exact (hbalB.characters).symm.trans ((cofinality_downSet hneB).trans hcof.symm)
  obtain ⟨a0, ha0⟩ := hintA.lower_nonempty
  obtain ⟨b0, hb0⟩ := hintB.lower_nonempty
  exact (bothSegments_of_regular hreg.aleph0_le hreg hεlt (HOrder δ) (horderSetup hδ)
    (downCut A) (downCut B) hintA hintB hbalA hbalB hcharA hcharB
    a0 b0 ha0 hb0 p q (mem_downCut_upper hp) (mem_downCut_upper hq)).2

/-- The upward closure written for the portion at or above `p`. -/
def upSet {δ : _root_.Ordinal.{u}} (A : Set (HOrder δ)) : Set (HOrder δ) :=
  {x | ∃ a ∈ A, a ≤ x}

/-- The cut whose upper side is that upward closure. -/
def upCut {δ : _root_.Ordinal.{u}} (A : Set (HOrder δ)) : Cut (HOrder δ) where
  lower := (upSet A)ᶜ
  upper := upSet A
  union_eq := by
    rw [Set.compl_union_self]
  disjoint := by
    rw [Set.disjoint_left]
    intro x hx hxu
    exact hx hxu
  ordered := by
    intro a ha b hb
    obtain ⟨c, hc, hle⟩ := hb
    have hac : a < c := by
      by_contra hge
      exact ha ⟨c, hc, le_of_not_gt hge⟩
    exact hac.trans_le hle

lemma coinitiality_upSet {δ : _root_.Ordinal.{u}} {A : Set (HOrder δ)} (hne : A.Nonempty) :
    setCoinitiality (upSet A) = setCoinitiality A := by
  have hup : (upSet A).Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, a, ha, le_rfl⟩
  apply le_antisymm
  · obtain ⟨t, ht, hcard, hcof⟩ := exists_setCoinitiality_witness A hne
    refine (HOrder.setCoinitiality_le (t := t) ?_ ?_).trans_eq hcard
    · intro x hx
      exact ⟨x, ht hx, le_rfl⟩
    · intro x hx
      obtain ⟨a, ha, hle⟩ := hx
      obtain ⟨y, hy, hay⟩ := hcof a ha
      exact ⟨y, hy, hay.trans hle⟩
  · obtain ⟨t, ht, hcard, hcof⟩ := exists_setCoinitiality_witness (upSet A) hup
    let pick : ↥t → HOrder δ := fun y => Classical.choose (ht y.2)
    have hpick : ∀ y : ↥t, pick y ∈ A ∧ pick y ≤ (y : HOrder δ) :=
      fun y => Classical.choose_spec (ht y.2)
    refine (HOrder.setCoinitiality_le (t := Set.range pick) ?_ ?_).trans
      (Cardinal.mk_range_le.trans (le_of_eq hcard))
    · rintro _ ⟨y, rfl⟩
      exact (hpick y).1
    · intro a ha
      obtain ⟨y, hy, hle⟩ := hcof a ⟨a, ha, le_rfl⟩
      let z : ↥t := ⟨y, hy⟩
      refine ⟨pick z, ?_, (hpick z).2.trans hle⟩
      exact ⟨z, rfl⟩

lemma upSet_no_least {δ : _root_.Ordinal.{u}} {A : Set (HOrder δ)}
    (hno : ∀ a ∈ A, ∃ b ∈ A, b < a) :
    ∀ a ∈ upSet A, ∃ b ∈ upSet A, b < a := by
  intro x hx
  obtain ⟨a, ha, hle⟩ := hx
  obtain ⟨b, hb, hba⟩ := hno a ha
  exact ⟨b, ⟨b, hb, le_rfl⟩, hba.trans_le hle⟩

lemma mem_upCut_lower {δ : _root_.Ordinal.{u}} {A : Set (HOrder δ)} {p : HOrder δ}
    (hp : ∀ a ∈ A, p < a) : p ∈ (upCut A).lower := by
  intro h
  obtain ⟨a, ha, hle⟩ := h
  exact not_le_of_gt (hp a ha) hle

lemma upCut_no_greatest {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {A : Set (HOrder δ)}
    (hcard : #A ≤ Cardinal.lift.{u + 1} θ)
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hne : A.Nonempty) (a : HOrder δ) (ha : a ∈ (upCut A).lower) :
    ∃ b ∈ (upCut A).lower, a < b := by
  by_contra hnone
  have hgreat : ∀ b ∈ (upCut A).lower, ¬ a < b := by
    intro b hb hlt
    exact hnone ⟨b, hb, hlt⟩
  have heq : upSet A = Set.Ioi a := by
    ext x
    constructor
    · intro hx
      exact Set.mem_Ioi.mpr ((upCut A).ordered a ha x hx)
    · intro hx
      have hxgt : a < x := Set.mem_Ioi.mp hx
      have hxL : x ∉ (upSet A)ᶜ := by
        intro hxl
        exact (hgreat x hxl hxgt).elim
      simpa [Set.mem_compl_iff] using hxL
  have hcoA : setCoinitiality A ≤ Cardinal.lift.{u + 1} θ :=
    (HOrder.setCoinitiality_le (t := A) (fun _ hx => hx) (fun x hx => ⟨x, hx, le_rfl⟩)).trans hcard
  have hsmall : setCoinitiality (upSet A) < Cardinal.lift.{u + 1} (Ordinal.cof δ) :=
    ((coinitiality_upSet hne).trans_le hcoA).trans_lt hcf
  have hpoint : setCoinitiality (Set.Ioi a) = Cardinal.lift.{u + 1} (Ordinal.cof δ) :=
    HOrder.rightChar hδ a
  exact lt_irrefl _ ((heq ▸ hpoint).symm ▸ hsmall)

lemma upCut_interior {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {A : Set (HOrder δ)} {p : HOrder δ}
    (hcard : #A ≤ Cardinal.lift.{u + 1} θ)
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hne : A.Nonempty) (hno : ∀ a ∈ A, ∃ b ∈ A, b < a) (hp : ∀ a ∈ A, p < a) :
    Cut.IsInteriorNonprincipal (upCut A) where
  lower_nonempty := ⟨p, mem_upCut_lower hp⟩
  upper_nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, a, ha, le_rfl⟩
  lower_no_greatest := fun a ha => upCut_no_greatest hδ hcard hcf hne a ha
  upper_no_least := upSet_no_least hno

/-- The portion `[p, …)` below `A⁺` has the order type of Lemma 3.4 at character `ci(A⁺)`. -/
theorem up_lowerTail_iso {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}}
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    {A B : Set (HOrder δ)} {p q : HOrder δ}
    (hA : #A ≤ Cardinal.lift.{u + 1} θ) (hB : #B ≤ Cardinal.lift.{u + 1} θ)
    (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hnoA : ∀ a ∈ A, ∃ b ∈ A, b < a) (hnoB : ∀ b ∈ B, ∃ c ∈ B, c < b)
    (hp : ∀ a ∈ A, p < a) (hq : ∀ b ∈ B, q < b)
    (hci : setCoinitiality A = setCoinitiality B) :
    Nonempty (↥(lowerTail (upCut A) p) ≃o ↥(lowerTail (upCut B) q)) := by
  let ε : Cardinal.{u + 1} := setCoinitiality A
  have hreg : Cardinal.IsRegular ε := isRegular_setCoinitiality hneA hnoA
  have hεlt : ε < Cardinal.lift.{u + 1} (Ordinal.cof δ) := by
    have hle : ε ≤ Cardinal.lift.{u + 1} θ :=
      (HOrder.setCoinitiality_le (t := A) (fun _ hx => hx) (fun x hx => ⟨x, hx, le_rfl⟩)).trans hA
    exact hle.trans_lt hcf
  have hintA := upCut_interior hδ hA hcf hneA hnoA hp
  have hintB := upCut_interior hδ hB hcf hneB hnoB hq
  have hbalA := horder_balanced (upCut A) hintA
  have hbalB := horder_balanced (upCut B) hintB
  have hcharA : (upCut A).characters = (ε, ε) := by
    unfold Cut.characters
    refine Prod.ext ((hbalA.characters).trans (coinitiality_upSet hneA)) (coinitiality_upSet hneA)
  have hcharB : (upCut B).characters = (ε, ε) := by
    refine Prod.ext ?_ ?_
    · exact (hbalB.characters).trans ((coinitiality_upSet hneB).trans hci.symm)
    · unfold Cut.characters
      exact (coinitiality_upSet hneB).trans hci.symm
  obtain ⟨a0, ha0⟩ := hintA.upper_nonempty
  obtain ⟨b0, hb0⟩ := hintB.upper_nonempty
  exact (bothSegments_of_regular hreg.aleph0_le hreg hεlt (HOrder δ) (horderSetup hδ)
    (upCut A) (upCut B) hintA hintB hbalA hbalB hcharA hcharB
    p q (mem_upCut_lower hp) (mem_upCut_lower hq) a0 b0 ha0 hb0).1

end DownCut

section Glue

open Set

variable {L M : Type v} [LinearOrder L] [LinearOrder M]

/-- An order isomorphism of two sets bounded above sends the greatest element to the greatest element. -/
lemma coe_orderIso_greatest {s : Set L} {t : Set M} {p : L} {q : M}
    (hp : p ∈ s) (hq : q ∈ t) (hs : ∀ x ∈ s, x ≤ p) (ht : ∀ y ∈ t, y ≤ q)
    (e : ↥s ≃o ↥t) : (e ⟨p, hp⟩ : M) = q := by
  have hle : (e ⟨p, hp⟩ : M) ≤ q := ht _ (e ⟨p, hp⟩).2
  have hsym : (e.symm ⟨q, hq⟩ : L) ≤ p := hs _ (e.symm ⟨q, hq⟩).2
  have hge : q ≤ (e ⟨p, hp⟩ : M) := by
    have hsub : e.symm ⟨q, hq⟩ ≤ ⟨p, hp⟩ := (Subtype.coe_le_coe).mp hsym
    have hsub' : ⟨q, hq⟩ ≤ e ⟨p, hp⟩ := by
      simpa using e.map_rel_iff.mpr hsub
    exact (Subtype.coe_le_coe).mpr hsub'
  exact le_antisymm hle hge

/-- An order isomorphism of two sets bounded below sends the least element to the least element. -/
lemma coe_orderIso_least {s : Set L} {t : Set M} {p : L} {q : M}
    (hp : p ∈ s) (hq : q ∈ t) (hs : ∀ x ∈ s, p ≤ x) (ht : ∀ y ∈ t, q ≤ y)
    (e : ↥s ≃o ↥t) : (e ⟨p, hp⟩ : M) = q := by
  have hge : q ≤ (e ⟨p, hp⟩ : M) := ht _ (e ⟨p, hp⟩).2
  have hsym : p ≤ (e.symm ⟨q, hq⟩ : L) := hs _ (e.symm ⟨q, hq⟩).2
  have hle : (e ⟨p, hp⟩ : M) ≤ q := by
    have hsub : ⟨p, hp⟩ ≤ e.symm ⟨q, hq⟩ := (Subtype.coe_le_coe).mp hsym
    have hsub' : e ⟨p, hp⟩ ≤ ⟨q, hq⟩ := by
      simpa using e.map_rel_iff.mpr hsub
    exact (Subtype.coe_le_coe).mpr hsub'
  exact le_antisymm hle hge

/-- Glue the portion at or below `p` to the portion at or above `p`, with `p` sent to `q`. -/
noncomputable def glueAt {s : Set L} {t : Set M} {p : L} {q : M}
    (hp : p ∈ s) (_hq : q ∈ t)
    (eLo : ↥{x | x ∈ s ∧ x ≤ p} ≃o ↥{y | y ∈ t ∧ y ≤ q})
    (eHi : ↥{x | x ∈ s ∧ p ≤ x} ≃o ↥{y | y ∈ t ∧ q ≤ y})
    (_hLo : (eLo ⟨p, hp, le_rfl⟩ : M) = q) (hHi : (eHi ⟨p, hp, le_rfl⟩ : M) = q) :
    ↥s ≃o ↥t := by
  refine StrictMono.orderIsoOfSurjective
    (fun x =>
      if hx : (x : L) ≤ p then
        ⟨eLo ⟨x, x.2, hx⟩, (eLo ⟨x, x.2, hx⟩).2.1⟩
      else
        ⟨eHi ⟨x, x.2, le_of_not_ge hx⟩, (eHi ⟨x, x.2, le_of_not_ge hx⟩).2.1⟩)
    ?_ ?_
  · intro x y hxy
    by_cases hx : (x : L) ≤ p
    · by_cases hy : (y : L) ≤ p
      · have hlt : (⟨x, x.2, hx⟩ : ↥{z | z ∈ s ∧ z ≤ p}) < ⟨y, y.2, hy⟩ :=
          Subtype.mk_lt_mk.mpr hxy
        rw [← Subtype.coe_lt_coe]
        simpa [hx, hy] using (Subtype.coe_lt_coe).mpr (eLo.lt_iff_lt.mpr hlt)
      · have hpy : p < (y : L) := lt_of_not_ge hy
        have hxq : (eLo ⟨x, x.2, hx⟩ : M) ≤ q := (eLo ⟨x, x.2, hx⟩).2.2
        have hpt : (⟨p, hp, le_rfl⟩ : ↥{z | z ∈ s ∧ p ≤ z}) < ⟨y, y.2, le_of_not_ge hy⟩ :=
          Subtype.mk_lt_mk.mpr hpy
        have hyq : q < (eHi ⟨y, y.2, le_of_not_ge hy⟩ : M) := by
          have hltE : eHi ⟨p, hp, le_rfl⟩ < eHi ⟨y, y.2, le_of_not_ge hy⟩ :=
            eHi.lt_iff_lt.mpr hpt
          have hcoe := (Subtype.coe_lt_coe).mpr hltE
          simpa [hHi] using hcoe
        rw [← Subtype.coe_lt_coe]
        simpa [hx, hy] using lt_of_le_of_lt hxq hyq
    · have hy' : ¬ (y : L) ≤ p := fun hy =>
        not_lt_of_ge (hy.trans (le_of_lt (lt_of_not_ge hx))) hxy
      have hlt : (⟨x, x.2, le_of_not_ge hx⟩ : ↥{z | z ∈ s ∧ p ≤ z}) <
          ⟨y, y.2, le_of_not_ge hy'⟩ := Subtype.mk_lt_mk.mpr hxy
      rw [← Subtype.coe_lt_coe]
      simpa [hx, hy'] using (Subtype.coe_lt_coe).mpr (eHi.lt_iff_lt.mpr hlt)
  · intro y
    by_cases hy : (y : M) ≤ q
    · let x := eLo.symm ⟨y, y.2, hy⟩
      refine ⟨⟨x, x.2.1⟩, ?_⟩
      have hx : (x : L) ≤ p := x.2.2
      have happ : eLo x = ⟨y, y.2, hy⟩ := eLo.apply_symm_apply _
      apply Subtype.ext
      simpa [hx] using congrArg (fun z : ↥{w | w ∈ t ∧ w ≤ q} => (z : M)) happ
    · let x := eHi.symm ⟨y, y.2, le_of_not_ge hy⟩
      refine ⟨⟨x, x.2.1⟩, ?_⟩
      have hxle : p ≤ (x : L) := x.2.2
      have hx : ¬ (x : L) ≤ p := by
        intro hle
        have hxeq : (x : L) = p := le_antisymm hle hxle
        have hxsub : x = ⟨p, hp, le_rfl⟩ := Subtype.ext hxeq
        have happ : eHi x = ⟨y, y.2, le_of_not_ge hy⟩ := eHi.apply_symm_apply _
        have hyq : (y : M) = q := by
          have hcoe := congrArg (fun z : ↥{w | w ∈ t ∧ q ≤ w} => (z : M)) happ
          rw [hxsub] at hcoe
          rw [hHi] at hcoe
          exact hcoe.symm
        exact (ne_of_gt (lt_of_not_ge hy)) hyq
      have happ : eHi x = ⟨y, y.2, le_of_not_ge hy⟩ := eHi.apply_symm_apply _
      apply Subtype.ext
      simpa [hx] using congrArg (fun z : ↥{w | w ∈ t ∧ q ≤ w} => (z : M)) happ

end Glue

section Orbit

open Cardinal Classical Set

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

lemma diagram_le {ι : Type v} {α β : Type v} [LinearOrder α] [LinearOrder β]
    {xs : ι → α} {ys : ι → β} (h : SameOrderDiagram xs ys) (i j : ι) :
    xs i ≤ xs j ↔ ys i ≤ ys j := by
  constructor
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact le_of_lt ((h.2 i j).mp hlt)
    · exact le_of_eq ((h.1 i j).mp heq)
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact le_of_lt ((h.2 i j).mpr hlt)
    · exact le_of_eq ((h.1 i j).mpr heq)

/-- The increasing bijection of entry sets induced by an order/equality diagram. -/
noncomputable def entryPick {ι : Type v} {α : Type v} (xs : ι → α) {lower : Set ι}
    (x : α) (hx : x ∈ xs '' lower) : ι :=
  Classical.choose ((mem_image xs lower x).mp hx)

lemma entryPick_mem {ι : Type v} {α : Type v} (xs : ι → α) {lower : Set ι}
    (x : α) (hx : x ∈ xs '' lower) :
    entryPick xs x hx ∈ lower ∧ xs (entryPick xs x hx) = x :=
  Classical.choose_spec ((mem_image xs lower x).mp hx)

noncomputable def entryIso {ι : Type v} {α β : Type v} [LinearOrder α] [LinearOrder β]
    {xs : ι → α} {ys : ι → β} (h : SameOrderDiagram xs ys) (lower : Set ι) :
    ↥(xs '' lower) ≃o ↥(ys '' lower) where
  toFun x := ⟨ys (entryPick xs (x : α) x.2), mem_image_of_mem _ (entryPick_mem xs _ x.2).1⟩
  invFun y := ⟨xs (entryPick ys (y : β) y.2), mem_image_of_mem _ (entryPick_mem ys _ y.2).1⟩
  left_inv x := by
    ext
    dsimp
    have hi := entryPick_mem xs (x : α) x.2
    have hj := entryPick_mem ys (ys (entryPick xs (x : α) x.2))
      (mem_image_of_mem _ hi.1)
    rw [(h.1 _ _).mpr hj.2]
    exact hi.2
  right_inv y := by
    ext
    dsimp
    have hi := entryPick_mem ys (y : β) y.2
    have hj := entryPick_mem xs (xs (entryPick ys (y : β) y.2))
      (mem_image_of_mem _ hi.1)
    rw [(h.1 _ _).mp hj.2]
    exact hi.2
  map_rel_iff' {x y} := by
    dsimp
    rw [← Subtype.coe_le_coe, ← Subtype.coe_le_coe]
    have hx := (entryPick_mem xs (x : α) x.2).2
    have hy := (entryPick_mem xs (y : α) y.2).2
    have hle := diagram_le h (entryPick xs (x : α) x.2) (entryPick xs (y : α) y.2)
    rw [hx, hy] at hle
    exact hle.symm

lemma setCoinitiality_subtype_iso {α β : Type v} [LinearOrder α] [LinearOrder β]
    {s : Set α} {t : Set β} (e : ↥s ≃o ↥t) : setCoinitiality s = setCoinitiality t := by
  by_cases hne : s.Nonempty
  · have hne' : t.Nonempty := by
      obtain ⟨a, ha⟩ := hne
      exact ⟨e ⟨a, ha⟩, (e ⟨a, ha⟩).2⟩
    apply le_antisymm
    · obtain ⟨u, hu, hcard, hcof⟩ := exists_setCoinitiality_witness t hne'
      let f : ↥u → α := fun y => e.symm ⟨y.1, hu y.2⟩
      refine (HOrder.setCoinitiality_le (t := Set.range f) ?_ ?_).trans
        (Cardinal.mk_range_le.trans (le_of_eq (by
          have htu : #↥u = #u := rfl
          rw [htu, hcard])))
      · rintro _ ⟨y, rfl⟩
        exact (e.symm ⟨y.1, hu y.2⟩).2
      · intro x hx
        obtain ⟨y, hy, hle⟩ := hcof (e ⟨x, hx⟩) (e ⟨x, hx⟩).2
        have hyt : (⟨y, hu hy⟩ : ↥t) ≤ e ⟨x, hx⟩ := by
          rw [← Subtype.coe_le_coe]
          exact hle
        have hsub : e.symm ⟨y, hu hy⟩ ≤ ⟨x, hx⟩ := by
          simpa using e.symm.monotone hyt
        exact ⟨f ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, (Subtype.coe_le_coe).mpr hsub⟩
    · obtain ⟨u, hu, hcard, hcof⟩ := exists_setCoinitiality_witness s hne
      let f : ↥u → β := fun y => e ⟨y.1, hu y.2⟩
      refine (HOrder.setCoinitiality_le (t := Set.range f) ?_ ?_).trans
        (Cardinal.mk_range_le.trans (le_of_eq (by rw [hcard])))
      · rintro _ ⟨y, rfl⟩
        exact (e ⟨y.1, hu y.2⟩).2
      · intro z hz
        obtain ⟨y, hy, hle⟩ := hcof (e.symm ⟨z, hz⟩) (e.symm ⟨z, hz⟩).2
        have hyt : (⟨y, hu hy⟩ : ↥s) ≤ e.symm ⟨z, hz⟩ := by
          rw [← Subtype.coe_le_coe]
          exact hle
        have hsub : e ⟨y, hu hy⟩ ≤ ⟨z, hz⟩ := by
          simpa using e.monotone hyt
        exact ⟨f ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, (Subtype.coe_le_coe).mpr hsub⟩
  · have hempty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have ht : t = ∅ := by
      ext y
      constructor
      · intro hy
        have hmem := (e.symm ⟨y, hy⟩).2
        simp [hempty] at hmem
      · intro hy
        simp [hempty] at hy
    unfold setCoinitiality
    simp only [hempty, ht, Set.image_empty]
    have hα : setCofinality (∅ : Set αᵒᵈ) = 0 := by
      rw [setCofinality_eq_orderCof, Order.cof_eq_zero]
    have hβ : setCofinality (∅ : Set βᵒᵈ) = 0 := by
      rw [setCofinality_eq_orderCof, Order.cof_eq_zero]
    rw [hα, hβ]

lemma strictSlot_empty_of_not_separated {α : Type v} [LinearOrder α] {A B : Set α}
    (h : ¬ ∀ a ∈ A, ∀ b ∈ B, a < b) : strictSlot A B = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  apply h
  intro a ha b hb
  exact (hx.2.2.1 a ha).trans (hx.2.2.2 b hb)

lemma entryImage_eq_empty_iff {ι : Type v} {α β : Type v} {xs : ι → α} {ys : ι → β}
    (lower : Set ι) : xs '' lower = ∅ ↔ ys '' lower = ∅ := by
  constructor
  · intro hempty
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hy
    obtain ⟨i, hi, rfl⟩ := hy
    have : xs i ∈ xs '' lower := mem_image_of_mem _ hi
    simp [hempty] at this
  · intro hempty
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨i, hi, rfl⟩ := hx
    have : ys i ∈ ys '' lower := mem_image_of_mem _ hi
    simp [hempty] at this

lemma entryImage_card_le {δ : _root_.Ordinal.{u}} {θ : Cardinal.{u}} {ι : Type (u + 1)}
    (xs : ι → HOrder δ) (lower : Set ι) (hι : #ι ≤ Cardinal.lift.{u + 1} θ) :
    #(xs '' lower) ≤ Cardinal.lift.{u + 1} θ :=
  (Cardinal.mk_image_le (f := xs) (s := lower)).trans ((Cardinal.mk_subtype_le lower).trans hι)

lemma entry_cofinality {ι : Type v} {α β : Type v} [LinearOrder α] [LinearOrder β]
    {xs : ι → α} {ys : ι → β} (h : SameOrderDiagram xs ys) (lower : Set ι) :
    setCofinality (xs '' lower) = setCofinality (ys '' lower) := by
  rw [setCofinality_eq_orderCof, setCofinality_eq_orderCof, (entryIso h lower).cof_congr]

lemma entry_coinitiality {ι : Type v} {α β : Type v} [LinearOrder α] [LinearOrder β]
    {xs : ι → α} {ys : ι → β} (h : SameOrderDiagram xs ys) (lower : Set ι) :
    setCoinitiality (xs '' lower) = setCoinitiality (ys '' lower) :=
  setCoinitiality_subtype_iso (entryIso h lower)

lemma isGreatest_of_diagram {ι : Type v} {α β : Type v} [LinearOrder α] [LinearOrder β]
    {xs : ι → α} {ys : ι → β} (h : SameOrderDiagram xs ys) {lower : Set ι} {i : ι}
    (hi : i ∈ lower) (hg : IsGreatest (xs '' lower) (xs i)) :
    IsGreatest (ys '' lower) (ys i) := by
  refine ⟨mem_image_of_mem _ hi, ?_⟩
  intro b hb
  obtain ⟨j, hj, rfl⟩ := hb
  exact (diagram_le h j i).mp (hg.2 (mem_image_of_mem _ hj))

lemma exists_isGreatest_iff {ι : Type v} {α β : Type v} [LinearOrder α] [LinearOrder β]
    {xs : ι → α} {ys : ι → β} (h : SameOrderDiagram xs ys) (lower : Set ι) :
    (∃ a, IsGreatest (xs '' lower) a) ↔ (∃ b, IsGreatest (ys '' lower) b) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨i, hi, rfl⟩ := ha.1
    exact ⟨ys i, isGreatest_of_diagram h hi ha⟩
  · rintro ⟨b, hb⟩
    obtain ⟨i, hi, rfl⟩ := hb.1
    refine ⟨xs i, mem_image_of_mem _ hi, ?_⟩
    intro a ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact (diagram_le h j i).mpr (hb.2 (mem_image_of_mem _ hj))

lemma forall_no_greatest {α : Type v} [LinearOrder α] {s : Set α}
    (h : ¬ ∃ a, IsGreatest s a) : ∀ a ∈ s, ∃ b ∈ s, a < b := by
  intro a ha
  by_contra hnone
  refine h ⟨a, ha, ?_⟩
  intro b hb
  exact le_of_not_gt fun hlt => hnone ⟨b, hb, hlt⟩

lemma forall_no_least {α : Type v} [LinearOrder α] {s : Set α}
    (h : ¬ ∃ a, IsLeast s a) : ∀ a ∈ s, ∃ b ∈ s, b < a := by
  intro a ha
  by_contra hnone
  refine h ⟨a, ha, ?_⟩
  intro b hb
  exact le_of_not_gt fun hlt => hnone ⟨b, hb, hlt⟩

lemma portion_below_Iic {A B : Set (HOrder δ)} {p : HOrder δ}
    (hp : p ∈ strictSlot A B) (hA : A = ∅) :
    {x | x ∈ strictSlot A B ∧ x ≤ p} = Iic p := by
  ext x
  constructor
  · intro hx
    exact mem_Iic.mpr hx.2
  · intro hx
    have hxle : x ≤ p := mem_Iic.mp hx
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hxle⟩
    · intro hmem
      simp [hA] at hmem
    · intro hmem
      exact lt_irrefl p ((hp.2.2.2 x hmem).trans_le hxle)
    · intro a ha
      simp [hA] at ha
    · intro b hb
      exact hxle.trans_lt (hp.2.2.2 b hb)

lemma portion_below_rightHalf {A B : Set (HOrder δ)} {a p : HOrder δ}
    (hp : p ∈ strictSlot A B) (ha : IsGreatest A a) :
    {x | x ∈ strictSlot A B ∧ x ≤ p} = rightHalf a p := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1.2.2.1 a ha.1, hx.2⟩
  · intro hx
    have hxA : ∀ c ∈ A, c < x := fun c hc => (ha.2 hc).trans_lt hx.1
    have hxB : ∀ b ∈ B, x < b := fun b hb => hx.2.trans_lt (hp.2.2.2 b hb)
    have hxnotA : x ∉ A := fun hmem => not_lt_of_ge (ha.2 hmem) hx.1
    have hxnotB : x ∉ B := fun hmem => lt_irrefl p ((hp.2.2.2 x hmem).trans_le hx.2)
    exact ⟨⟨hxnotA, hxnotB, hxA, hxB⟩, hx.2⟩

lemma portion_below_head {A B : Set (HOrder δ)} {p : HOrder δ}
    (hp : p ∈ strictSlot A B) :
    {x | x ∈ strictSlot A B ∧ x ≤ p} = upperHead (downCut A) p := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, hx.2⟩
    intro hmem
    obtain ⟨a, ha, hle⟩ := hmem
    exact not_le_of_gt (hx.1.2.2.1 a ha) hle
  · intro hx
    have hxU : ∀ a ∈ A, a < x := by
      intro a ha
      by_contra hge
      exact hx.1 ⟨a, ha, le_of_not_gt hge⟩
    have hxle : x ≤ p := hx.2
    have hxnotA : x ∉ A := fun ha => lt_irrefl x (hxU x ha)
    have hxnotB : x ∉ B := fun hb => lt_irrefl p ((hp.2.2.2 x hb).trans_le hxle)
    have hxB : ∀ b ∈ B, x < b := fun b hb => hxle.trans_lt (hp.2.2.2 b hb)
    exact ⟨⟨hxnotA, hxnotB, hxU, hxB⟩, hxle⟩

/-- The portion of a strict slot at or below an interior point. -/
noncomputable def belowPortion {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {ι : Type (u + 1)}
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hι : #ι ≤ Cardinal.lift.{u + 1} θ)
    {xs ys : ι → HOrder δ} (hdiag : SameOrderDiagram xs ys) (lower upper : Set ι)
    {p q : HOrder δ} (hp : p ∈ strictSlot (xs '' lower) (xs '' upper))
    (hq : q ∈ strictSlot (ys '' lower) (ys '' upper)) :
    ↥{x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ x ≤ p} ≃o
      ↥{y | y ∈ strictSlot (ys '' lower) (ys '' upper) ∧ y ≤ q} := by
  by_cases hempty : xs '' lower = ∅
  · have hempty' : ys '' lower = ∅ := (entryImage_eq_empty_iff lower).mp hempty
    have hxs := portion_below_Iic hp hempty
    have hys := portion_below_Iic hq hempty'
    exact (({x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ x ≤ p} :
        Set (HOrder δ)).orderIsoOfEq (Iic p) hxs).trans
      ((iicIso p q).trans ((Iic q).orderIsoOfEq
        {y | y ∈ strictSlot (ys '' lower) (ys '' upper) ∧ y ≤ q} hys.symm))
  · by_cases hgreat : ∃ a, IsGreatest (xs '' lower) a
    · let a := Classical.choose hgreat
      have ha := Classical.choose_spec hgreat
      let i := Classical.choose ((mem_image xs lower a).mp ha.1)
      have hi := Classical.choose_spec ((mem_image xs lower a).mp ha.1)
      have hb : IsGreatest (ys '' lower) (ys i) := by
        have hga : IsGreatest (xs '' lower) (xs i) := by
          rw [hi.2]
          exact ha
        exact isGreatest_of_diagram hdiag hi.1 hga
      have hap : xs i < p := hp.2.2.1 (xs i) (mem_image_of_mem _ hi.1)
      have hbq : ys i < q := hq.2.2.1 (ys i) hb.1
      have hxs : {x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ x ≤ p} =
          rightHalf (xs i) p := by
        rw [hi.2]
        exact portion_below_rightHalf hp ha
      have hys := portion_below_rightHalf hq hb
      exact (({x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ x ≤ p} :
          Set (HOrder δ)).orderIsoOfEq (rightHalf (xs i) p) hxs).trans
        ((iocIso hap hbq).trans ((rightHalf (ys i) q).orderIsoOfEq
          {y | y ∈ strictSlot (ys '' lower) (ys '' upper) ∧ y ≤ q} hys.symm))
    · have hneA : (xs '' lower).Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
      have hneB : (ys '' lower).Nonempty := by
        obtain ⟨a, ha⟩ := hneA
        obtain ⟨i, hi, rfl⟩ := ha
        exact ⟨ys i, mem_image_of_mem _ hi⟩
      have hnoA := forall_no_greatest hgreat
      have hnoB := forall_no_greatest ((exists_isGreatest_iff hdiag lower).not.mp hgreat)
      have hcardA := entryImage_card_le xs lower hι
      have hcardB := entryImage_card_le ys lower hι
      have hpA : ∀ a ∈ xs '' lower, a < p := fun a ha => hp.2.2.1 a ha
      have hqB : ∀ b ∈ ys '' lower, b < q := fun b hb => hq.2.2.1 b hb
      let e := Classical.choice (down_upperHead_iso hδ hcf hcardA hcardB hneA hneB hnoA hnoB hpA hqB
        (entry_cofinality hdiag lower))
      have hxs := portion_below_head hp
      have hys := portion_below_head hq
      exact (({x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ x ≤ p} :
          Set (HOrder δ)).orderIsoOfEq (upperHead (downCut (xs '' lower)) p) hxs).trans
        (e.trans ((upperHead (downCut (ys '' lower)) q).orderIsoOfEq
          {y | y ∈ strictSlot (ys '' lower) (ys '' upper) ∧ y ≤ q} hys.symm))

lemma isLeast_of_diagram {ι : Type v} {α β : Type v} [LinearOrder α] [LinearOrder β]
    {xs : ι → α} {ys : ι → β} (h : SameOrderDiagram xs ys) {upper : Set ι} {i : ι}
    (hi : i ∈ upper) (hg : IsLeast (xs '' upper) (xs i)) :
    IsLeast (ys '' upper) (ys i) := by
  refine ⟨mem_image_of_mem _ hi, ?_⟩
  intro b hb
  obtain ⟨j, hj, rfl⟩ := hb
  exact (diagram_le h i j).mp (hg.2 (mem_image_of_mem _ hj))

lemma exists_isLeast_iff {ι : Type v} {α β : Type v} [LinearOrder α] [LinearOrder β]
    {xs : ι → α} {ys : ι → β} (h : SameOrderDiagram xs ys) (upper : Set ι) :
    (∃ a, IsLeast (xs '' upper) a) ↔ (∃ b, IsLeast (ys '' upper) b) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨i, hi, rfl⟩ := ha.1
    exact ⟨ys i, isLeast_of_diagram h hi ha⟩
  · rintro ⟨b, hb⟩
    obtain ⟨i, hi, rfl⟩ := hb.1
    refine ⟨xs i, mem_image_of_mem _ hi, ?_⟩
    intro a ha
    obtain ⟨j, hj, rfl⟩ := ha
    exact (diagram_le h i j).mpr (hb.2 (mem_image_of_mem _ hj))

lemma portion_above_Ici {A B : Set (HOrder δ)} {p : HOrder δ}
    (hp : p ∈ strictSlot A B) (hB : B = ∅) :
    {x | x ∈ strictSlot A B ∧ p ≤ x} = Ici p := by
  ext x
  constructor
  · intro hx
    exact mem_Ici.mpr hx.2
  · intro hx
    have hxge : p ≤ x := mem_Ici.mp hx
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hxge⟩
    · intro hmem
      exact lt_irrefl p (hxge.trans_lt (hp.2.2.1 x hmem))
    · intro hmem
      simp [hB] at hmem
    · intro a ha
      exact (hp.2.2.1 a ha).trans_le hxge
    · intro b hb
      simp [hB] at hb

lemma portion_above_Ico {A B : Set (HOrder δ)} {p b : HOrder δ}
    (hp : p ∈ strictSlot A B) (hb : IsLeast B b) :
    {x | x ∈ strictSlot A B ∧ p ≤ x} = Ico p b := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2, hx.1.2.2.2 b hb.1⟩
  · intro hx
    have hxA : ∀ a ∈ A, a < x := fun a ha => (hp.2.2.1 a ha).trans_le hx.1
    have hxB : ∀ c ∈ B, x < c := fun c hc => hx.2.trans_le (hb.2 hc)
    have hxnotA : x ∉ A := fun ha => lt_irrefl x ((hp.2.2.1 x ha).trans_le hx.1)
    have hxnotB : x ∉ B := fun hc => not_lt_of_ge (hb.2 hc) hx.2
    exact ⟨⟨hxnotA, hxnotB, hxA, hxB⟩, hx.1⟩

lemma portion_above_tail {A B : Set (HOrder δ)} {p : HOrder δ}
    (hp : p ∈ strictSlot A B) :
    {x | x ∈ strictSlot A B ∧ p ≤ x} = lowerTail (upCut B) p := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, hx.2⟩
    intro hmem
    obtain ⟨b, hb, hle⟩ := hmem
    exact not_le_of_gt (hx.1.2.2.2 b hb) hle
  · intro hx
    have hxU : ∀ b ∈ B, x < b := by
      intro b hb
      by_contra hge
      exact hx.1 ⟨b, hb, le_of_not_gt hge⟩
    have hxge : p ≤ x := hx.2
    have hxnotB : x ∉ B := fun hb => lt_irrefl x (hxU x hb)
    have hxnotA : x ∉ A := fun ha => lt_irrefl x ((hp.2.2.1 x ha).trans_le hxge)
    have hxA : ∀ a ∈ A, a < x := fun a ha => (hp.2.2.1 a ha).trans_le hxge
    exact ⟨⟨hxnotA, hxnotB, hxA, hxU⟩, hxge⟩

/-- The portion of a strict slot at or above an interior point. -/
noncomputable def abovePortion {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {ι : Type (u + 1)}
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hι : #ι ≤ Cardinal.lift.{u + 1} θ)
    {xs ys : ι → HOrder δ} (hdiag : SameOrderDiagram xs ys) (lower upper : Set ι)
    {p q : HOrder δ} (hp : p ∈ strictSlot (xs '' lower) (xs '' upper))
    (hq : q ∈ strictSlot (ys '' lower) (ys '' upper)) :
    ↥{x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ p ≤ x} ≃o
      ↥{y | y ∈ strictSlot (ys '' lower) (ys '' upper) ∧ q ≤ y} := by
  by_cases hempty : xs '' upper = ∅
  · have hempty' : ys '' upper = ∅ := (entryImage_eq_empty_iff upper).mp hempty
    have hxs := portion_above_Ici hp hempty
    have hys := portion_above_Ici hq hempty'
    exact (({x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ p ≤ x} :
        Set (HOrder δ)).orderIsoOfEq (Ici p) hxs).trans
      ((iciIso p q).trans ((Ici q).orderIsoOfEq
        {y | y ∈ strictSlot (ys '' lower) (ys '' upper) ∧ q ≤ y} hys.symm))
  · by_cases hleast : ∃ b, IsLeast (xs '' upper) b
    · let b := Classical.choose hleast
      have hb := Classical.choose_spec hleast
      let i := Classical.choose ((mem_image xs upper b).mp hb.1)
      have hi := Classical.choose_spec ((mem_image xs upper b).mp hb.1)
      have hc : IsLeast (ys '' upper) (ys i) := by
        have hlb : IsLeast (xs '' upper) (xs i) := by
          rw [hi.2]
          exact hb
        exact isLeast_of_diagram hdiag hi.1 hlb
      have hpb : p < xs i := hp.2.2.2 (xs i) (mem_image_of_mem _ hi.1)
      have hqc : q < ys i := hq.2.2.2 (ys i) hc.1
      have hxs : {x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ p ≤ x} =
          Ico p (xs i) := by
        rw [hi.2]
        exact portion_above_Ico hp hb
      have hys := portion_above_Ico hq hc
      exact (({x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ p ≤ x} :
          Set (HOrder δ)).orderIsoOfEq (Ico p (xs i)) hxs).trans
        ((icoIso hpb hqc).trans ((Ico q (ys i)).orderIsoOfEq
          {y | y ∈ strictSlot (ys '' lower) (ys '' upper) ∧ q ≤ y} hys.symm))
    · have hneA : (xs '' upper).Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
      have hneB : (ys '' upper).Nonempty := by
        obtain ⟨a, ha⟩ := hneA
        obtain ⟨i, hi, rfl⟩ := ha
        exact ⟨ys i, mem_image_of_mem _ hi⟩
      have hnoA := forall_no_least hleast
      have hnoB := forall_no_least ((exists_isLeast_iff hdiag upper).not.mp hleast)
      have hcardA := entryImage_card_le xs upper hι
      have hcardB := entryImage_card_le ys upper hι
      have hpA : ∀ a ∈ xs '' upper, p < a := fun a ha => hp.2.2.2 a ha
      have hqB : ∀ b ∈ ys '' upper, q < b := fun b hb => hq.2.2.2 b hb
      let e := Classical.choice (up_lowerTail_iso hδ hcf hcardA hcardB hneA hneB hnoA hnoB hpA hqB
        (entry_coinitiality hdiag upper))
      have hxs := portion_above_tail hp
      have hys := portion_above_tail hq
      exact (({x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ p ≤ x} :
          Set (HOrder δ)).orderIsoOfEq (lowerTail (upCut (xs '' upper)) p) hxs).trans
        (e.trans ((lowerTail (upCut (ys '' upper)) q).orderIsoOfEq
          {y | y ∈ strictSlot (ys '' lower) (ys '' upper) ∧ q ≤ y} hys.symm))

/-- A point of `H(δ)`, used only to supply `Nonempty` to `Classical.epsilon`. -/
noncomputable def horderZero (δ : _root_.Ordinal.{u}) : HOrder δ :=
  toColex (0 : Gamma δ →₀ ℚ)

/-- The order isomorphism of one occupied strict slot, obtained by gluing its two halves. -/
noncomputable def slotIso {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {ι : Type (u + 1)}
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hι : #ι ≤ Cardinal.lift.{u + 1} θ)
    {xs ys : ι → HOrder δ} (hdiag : SameOrderDiagram xs ys)
    (hocc : SameSlotOccupancy xs ys) (lower upper : Set ι) :
    ↥(strictSlot (xs '' lower) (xs '' upper)) ≃o
      ↥(strictSlot (ys '' lower) (ys '' upper)) := by
  by_cases hsep : ∀ i ∈ lower, ∀ j ∈ upper, xs i < xs j
  · have hsepY : ∀ i ∈ lower, ∀ j ∈ upper, ys i < ys j :=
      fun i hi j hj => (hdiag.2 i j).mp (hsep i hi j hj)
    by_cases hne : (strictSlot (xs '' lower) (xs '' upper)).Nonempty
    · have hneY : (strictSlot (ys '' lower) (ys '' upper)).Nonempty :=
        (hocc lower upper hsep hsepY).mp hne
      let p := @Classical.epsilon (HOrder δ) ⟨horderZero δ⟩
        (fun x => x ∈ strictSlot (xs '' lower) (xs '' upper))
      have hp : p ∈ strictSlot (xs '' lower) (xs '' upper) := Classical.epsilon_spec hne
      let q := @Classical.epsilon (HOrder δ) ⟨horderZero δ⟩
        (fun x => x ∈ strictSlot (ys '' lower) (ys '' upper))
      have hq : q ∈ strictSlot (ys '' lower) (ys '' upper) := Classical.epsilon_spec hneY
      let eLo := belowPortion hδ hcf hι hdiag lower upper hp hq
      let eHi := abovePortion hδ hcf hι hdiag lower upper hp hq
      let sLo : Set (HOrder δ) := {x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ x ≤ p}
      let tLo : Set (HOrder δ) := {y | y ∈ strictSlot (ys '' lower) (ys '' upper) ∧ y ≤ q}
      let sHi : Set (HOrder δ) := {x | x ∈ strictSlot (xs '' lower) (xs '' upper) ∧ p ≤ x}
      let tHi : Set (HOrder δ) := {y | y ∈ strictSlot (ys '' lower) (ys '' upper) ∧ q ≤ y}
      have hpLo : p ∈ sLo := ⟨hp, le_rfl⟩
      have hqLo : q ∈ tLo := ⟨hq, le_rfl⟩
      have hpHi : p ∈ sHi := ⟨hp, le_rfl⟩
      have hqHi : q ∈ tHi := ⟨hq, le_rfl⟩
      exact glueAt hp hq eLo eHi
        (coe_orderIso_greatest hpLo hqLo (fun _ hx => hx.2) (fun _ hy => hy.2) eLo)
        (coe_orderIso_least hpHi hqHi (fun _ hx => hx.2) (fun _ hy => hy.2) eHi)
    · have hempty : strictSlot (xs '' lower) (xs '' upper) = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      have hemptyY : strictSlot (ys '' lower) (ys '' upper) = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.mp
        intro h
        exact hne ((hocc lower upper hsep hsepY).mpr h)
      haveI : IsEmpty (↥(strictSlot (xs '' lower) (xs '' upper))) := by
        rw [hempty]
        infer_instance
      haveI : IsEmpty (↥(strictSlot (ys '' lower) (ys '' upper))) := by
        rw [hemptyY]
        infer_instance
      exact OrderIso.ofIsEmpty _ _
  · have hempty : strictSlot (xs '' lower) (xs '' upper) = ∅ := by
      apply strictSlot_empty_of_not_separated
      intro hall
      apply hsep
      intro i hi j hj
      exact hall (xs i) (mem_image_of_mem _ hi) (xs j) (mem_image_of_mem _ hj)
    have hemptyY : strictSlot (ys '' lower) (ys '' upper) = ∅ := by
      apply strictSlot_empty_of_not_separated
      intro hall
      apply hsep
      intro i hi j hj
      exact (hdiag.2 i j).mpr (hall (ys i) (mem_image_of_mem _ hi) (ys j) (mem_image_of_mem _ hj))
    haveI : IsEmpty (↥(strictSlot (xs '' lower) (xs '' upper))) := by
      rw [hempty]
      infer_instance
    haveI : IsEmpty (↥(strictSlot (ys '' lower) (ys '' upper))) := by
      rw [hemptyY]
      infer_instance
    exact OrderIso.ofIsEmpty _ _

lemma mem_strictSlot_of_not_entry {ι : Type v} {α : Type v} [LinearOrder α]
    (xs : ι → α) (x : α) (hx : ¬ ∃ i, xs i = x) :
    x ∈ strictSlot (xs '' {i | xs i < x}) (xs '' {i | x < xs i}) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hmem
    obtain ⟨i, hi, hi'⟩ := (mem_image _ _ _).mp hmem
    exact lt_irrefl x (hi'.symm ▸ hi)
  · intro hmem
    obtain ⟨i, hi, hi'⟩ := (mem_image _ _ _).mp hmem
    exact lt_irrefl x (hi'.symm ▸ hi)
  · intro a ha
    obtain ⟨i, _hi, rfl⟩ := (mem_image _ _ _).mp ha
    exact _hi
  · intro b hb
    obtain ⟨i, _hi, rfl⟩ := (mem_image _ _ _).mp hb
    exact _hi

lemma below_subset_of_lt {ι : Type v} {α : Type v} [LinearOrder α]
    (xs : ι → α) {x y : α} (hxy : x < y) :
    {i | xs i < x} ⊆ {i | xs i < y} :=
  fun _ hi => hi.trans hxy

lemma above_eq_of_below_eq {ι : Type v} {α : Type v} [LinearOrder α]
    (xs : ι → α) {x y : α} (hx : ¬ ∃ i, xs i = x) (hy : ¬ ∃ i, xs i = y)
    (hxy : x < y) (hbelow : {i | xs i < x} = {i | xs i < y}) :
    {i | x < xs i} = {i | y < xs i} := by
  ext i
  constructor
  · intro hi
    rcases lt_trichotomy (xs i) y with hlt | heq | hgt
    · have hmem : i ∈ {j | xs j < y} := hlt
      rw [← hbelow] at hmem
      exact (not_lt_of_gt hi hmem).elim
    · exact (hy ⟨i, heq⟩).elim
    · exact hgt
  · intro hi
    exact hxy.trans hi

lemma exists_entry_between {ι : Type v} {α : Type v} [LinearOrder α]
    (xs : ι → α) {x y : α} (hxy : x < y) (hx : ¬ ∃ i, xs i = x)
    (hbelow : ¬ {i | xs i < x} = {i | xs i < y}) :
    ∃ i, x < xs i ∧ xs i < y := by
  have hex : ∃ i, xs i < y ∧ ¬ xs i < x := by
    by_contra hall
    push_neg at hall
    apply hbelow
    ext i
    constructor
    · intro hi
      exact below_subset_of_lt xs hxy hi
    · intro hi
      exact hall i hi
  obtain ⟨i, hiY, hiX⟩ := hex
  have hne : xs i ≠ x := fun h => hx ⟨i, h⟩
  exact ⟨i, lt_of_le_of_ne (le_of_not_gt hiX) hne.symm, hiY⟩

/-- Send each entry by the order diagram and each other point by the isomorphism of its slot. -/
noncomputable def orbitMap {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {ι : Type (u + 1)}
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hι : #ι ≤ Cardinal.lift.{u + 1} θ)
    (xs ys : ι → HOrder δ) (hdiag : SameOrderDiagram xs ys)
    (hocc : SameSlotOccupancy xs ys) (x : HOrder δ) : HOrder δ :=
  if hx : ∃ i, xs i = x then ys (Classical.choose hx)
  else
    (slotIso hδ hcf hι hdiag hocc {i | xs i < x} {i | x < xs i}
      ⟨x, mem_strictSlot_of_not_entry xs x hx⟩ : HOrder δ)

lemma orbitMap_entry {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {ι : Type (u + 1)}
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hι : #ι ≤ Cardinal.lift.{u + 1} θ)
    {xs ys : ι → HOrder δ} (hdiag : SameOrderDiagram xs ys)
    (hocc : SameSlotOccupancy xs ys) (i : ι) :
    orbitMap hδ hcf hι xs ys hdiag hocc (xs i) = ys i := by
  have hx : ∃ j, xs j = xs i := ⟨i, rfl⟩
  unfold orbitMap
  rw [dif_pos hx]
  exact (hdiag.1 _ _).mp (Classical.choose_spec hx)

lemma slotIso_cast {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {ι : Type (u + 1)}
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hι : #ι ≤ Cardinal.lift.{u + 1} θ)
    {xs ys : ι → HOrder δ} (hdiag : SameOrderDiagram xs ys)
    (hocc : SameSlotOccupancy xs ys)
    {lower lower' upper upper' : Set ι} (hL : lower = lower') (hU : upper = upper')
    {x : HOrder δ} (hx : x ∈ strictSlot (xs '' lower) (xs '' upper))
    (hx' : x ∈ strictSlot (xs '' lower') (xs '' upper')) :
    (slotIso hδ hcf hι hdiag hocc lower upper ⟨x, hx⟩ : HOrder δ) =
      slotIso hδ hcf hι hdiag hocc lower' upper' ⟨x, hx'⟩ := by
  subst hL
  subst hU
  exact congrArg
    (fun w : ↥(strictSlot (xs '' lower) (xs '' upper)) =>
      (slotIso hδ hcf hι hdiag hocc lower upper w : HOrder δ))
    (Subtype.ext rfl)

lemma orbitMap_strictMono {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {ι : Type (u + 1)}
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hι : #ι ≤ Cardinal.lift.{u + 1} θ)
    {xs ys : ι → HOrder δ} (hdiag : SameOrderDiagram xs ys)
    (hocc : SameSlotOccupancy xs ys) :
    StrictMono (orbitMap hδ hcf hι xs ys hdiag hocc) := by
  intro x y hxy
  by_cases hx : ∃ i, xs i = x
  · by_cases hy : ∃ j, xs j = y
    · let i := Classical.choose hx
      have hi := Classical.choose_spec hx
      let j := Classical.choose hy
      have hj := Classical.choose_spec hy
      unfold orbitMap
      rw [dif_pos hx, dif_pos hy]
      exact (hdiag.2 i j).mp (by rw [hi, hj]; exact hxy)
    · let i := Classical.choose hx
      have hi := Classical.choose_spec hx
      unfold orbitMap
      rw [dif_pos hx, dif_neg hy]
      have hmem := (slotIso hδ hcf hι hdiag hocc {k | xs k < y} {k | y < xs k}
        ⟨y, mem_strictSlot_of_not_entry xs y hy⟩).2
      have hiLt : xs i < y := by
        change xs i < y
        rw [hi]
        exact hxy
      exact hmem.2.2.1 (ys i) (mem_image_of_mem _ hiLt)
  · by_cases hy : ∃ j, xs j = y
    · let j := Classical.choose hy
      have hj := Classical.choose_spec hy
      unfold orbitMap
      rw [dif_neg hx, dif_pos hy]
      have hmem := (slotIso hδ hcf hι hdiag hocc {k | xs k < x} {k | x < xs k}
        ⟨x, mem_strictSlot_of_not_entry xs x hx⟩).2
      have hjLt : x < xs j := by
        change x < xs j
        rw [hj]
        exact hxy
      exact hmem.2.2.2 (ys j) (mem_image_of_mem _ hjLt)
    · by_cases hbelow : {i | xs i < x} = {i | xs i < y}
      · have habove := above_eq_of_below_eq xs hx hy hxy hbelow
        have hxmem : x ∈ strictSlot (xs '' {i | xs i < y}) (xs '' {i | y < xs i}) := by
          have h := mem_strictSlot_of_not_entry xs x hx
          rw [hbelow, habove] at h
          exact h
        have hymem : y ∈ strictSlot (xs '' {i | xs i < y}) (xs '' {i | y < xs i}) :=
          mem_strictSlot_of_not_entry xs y hy
        have hxeq := slotIso_cast hδ hcf hι hdiag hocc hbelow habove
          (mem_strictSlot_of_not_entry xs x hx) hxmem
        unfold orbitMap
        rw [dif_neg hx, dif_neg hy, hxeq]
        rw [Subtype.coe_lt_coe]
        exact (slotIso hδ hcf hι hdiag hocc {i | xs i < y} {i | y < xs i}).lt_iff_lt.mpr
          (Subtype.mk_lt_mk.mpr hxy)
      · obtain ⟨i, hxi, hiy⟩ := exists_entry_between xs hxy hx hbelow
        have hleft : orbitMap hδ hcf hι xs ys hdiag hocc x < ys i := by
          unfold orbitMap
          rw [dif_neg hx]
          have hmem := (slotIso hδ hcf hι hdiag hocc {k | xs k < x} {k | x < xs k}
            ⟨x, mem_strictSlot_of_not_entry xs x hx⟩).2
          exact hmem.2.2.2 (ys i) (mem_image_of_mem _ hxi)
        have hright : ys i < orbitMap hδ hcf hι xs ys hdiag hocc y := by
          unfold orbitMap
          rw [dif_neg hy]
          have hmem := (slotIso hδ hcf hι hdiag hocc {k | xs k < y} {k | y < xs k}
            ⟨y, mem_strictSlot_of_not_entry xs y hy⟩).2
          exact hmem.2.2.1 (ys i) (mem_image_of_mem _ hiy)
        exact hleft.trans hright

lemma orbitMap_surjective {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {θ : Cardinal.{u}} {ι : Type (u + 1)}
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    (hι : #ι ≤ Cardinal.lift.{u + 1} θ)
    {xs ys : ι → HOrder δ} (hdiag : SameOrderDiagram xs ys)
    (hocc : SameSlotOccupancy xs ys) :
    Function.Surjective (orbitMap hδ hcf hι xs ys hdiag hocc) := by
  intro z
  by_cases hz : ∃ i, ys i = z
  · let i := Classical.choose hz
    refine ⟨xs i, ?_⟩
    rw [orbitMap_entry hδ hcf hι hdiag hocc i]
    exact Classical.choose_spec hz
  · let lower : Set ι := {i | ys i < z}
    let upper : Set ι := {i | z < ys i}
    have hmem : z ∈ strictSlot (ys '' lower) (ys '' upper) :=
      mem_strictSlot_of_not_entry ys z hz
    let xSub := (slotIso hδ hcf hι hdiag hocc lower upper).symm ⟨z, hmem⟩
    refine ⟨xSub, ?_⟩
    have hxnot : ¬ ∃ i, xs i = (xSub : HOrder δ) := by
      intro h
      obtain ⟨i, hi⟩ := h
      have hnotL : (xSub : HOrder δ) ∉ xs '' lower := xSub.2.1
      have hnotU : (xSub : HOrder δ) ∉ xs '' upper := xSub.2.2.1
      rcases lt_trichotomy (ys i) z with hlt | heq | hgt
      · exact hnotL (by rw [← hi]; exact mem_image_of_mem _ hlt)
      · exact hz ⟨i, heq⟩
      · exact hnotU (by rw [← hi]; exact mem_image_of_mem _ hgt)
    have hlow : ∀ a ∈ xs '' lower, a < (xSub : HOrder δ) := xSub.2.2.2.1
    have hup : ∀ b ∈ xs '' upper, (xSub : HOrder δ) < b := xSub.2.2.2.2
    have hbelow : {i | xs i < (xSub : HOrder δ)} = lower := by
      ext i
      constructor
      · intro hi
        rcases lt_trichotomy (ys i) z with hlt | heq | hgt
        · exact hlt
        · exact (hz ⟨i, heq⟩).elim
        · exact (not_lt_of_gt (hup (xs i) (mem_image_of_mem _ hgt)) hi).elim
      · intro hi
        exact hlow (xs i) (mem_image_of_mem _ hi)
    have habove : {i | (xSub : HOrder δ) < xs i} = upper := by
      ext i
      constructor
      · intro hi
        rcases lt_trichotomy (ys i) z with hlt | heq | hgt
        · exact (not_lt_of_gt (hlow (xs i) (mem_image_of_mem _ hlt)) hi).elim
        · exact (hz ⟨i, heq⟩).elim
        · exact hgt
      · intro hi
        exact hup (xs i) (mem_image_of_mem _ hi)
    have hxmem : (xSub : HOrder δ) ∈ strictSlot (xs '' lower) (xs '' upper) := xSub.2
    have hxeq := slotIso_cast hδ hcf hι hdiag hocc hbelow habove
      (mem_strictSlot_of_not_entry xs (xSub : HOrder δ) hxnot) hxmem
    unfold orbitMap
    rw [dif_neg hxnot, hxeq]
    have happ := (slotIso hδ hcf hι hdiag hocc lower upper).apply_symm_apply ⟨z, hmem⟩
    have hsubeq : (⟨(xSub : HOrder δ), hxmem⟩ :
        ↥(strictSlot (xs '' lower) (xs '' upper))) = xSub := Subtype.ext rfl
    rw [hsubeq]
    exact congrArg (fun w : ↥(strictSlot (ys '' lower) (ys '' upper)) => (w : HOrder δ)) happ

lemma orbit_iso_necessity {δ : _root_.Ordinal.{u}} {ι : Type (u + 1)}
    {xs ys : ι → HOrder δ} (e : HOrder δ ≃o HOrder δ) (he : ∀ i, e (xs i) = ys i) :
    SameOrderDiagram xs ys ∧ SameSlotOccupancy xs ys := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j
    rw [← he i, ← he j, e.injective.eq_iff]
  · intro i j
    rw [← he i, ← he j, e.lt_iff_lt]
  · intro lower upper _hxs _hys
    constructor
    · intro ⟨p, hp⟩
      refine ⟨e p, ?_, ?_, ?_, ?_⟩
      · intro hmem
        obtain ⟨i, hi, hi'⟩ := (mem_image _ _ _).mp hmem
        have hpEq : p = xs i := (e.injective ((he i).trans hi')).symm
        exact hp.1 (by rw [hpEq]; exact mem_image_of_mem _ hi)
      · intro hmem
        obtain ⟨i, hi, hi'⟩ := (mem_image _ _ _).mp hmem
        have hpEq : p = xs i := (e.injective ((he i).trans hi')).symm
        exact hp.2.1 (by rw [hpEq]; exact mem_image_of_mem _ hi)
      · intro a ha
        obtain ⟨i, hi, rfl⟩ := (mem_image _ _ _).mp ha
        rw [← he i]
        exact (e.lt_iff_lt).mpr (hp.2.2.1 (xs i) (mem_image_of_mem _ hi))
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := (mem_image _ _ _).mp hb
        rw [← he i]
        exact (e.lt_iff_lt).mpr (hp.2.2.2 (xs i) (mem_image_of_mem _ hi))
    · intro ⟨q, hq⟩
      refine ⟨e.symm q, ?_, ?_, ?_, ?_⟩
      · intro hmem
        obtain ⟨i, hi, hi'⟩ := (mem_image _ _ _).mp hmem
        have hqEq : ys i = q := by
          rw [← he i, hi']
          exact e.apply_symm_apply q
        exact hq.1 (by rw [← hqEq]; exact mem_image_of_mem _ hi)
      · intro hmem
        obtain ⟨i, hi, hi'⟩ := (mem_image _ _ _).mp hmem
        have hqEq : ys i = q := by
          rw [← he i, hi']
          exact e.apply_symm_apply q
        exact hq.2.1 (by rw [← hqEq]; exact mem_image_of_mem _ hi)
      · intro a ha
        obtain ⟨i, hi, rfl⟩ := (mem_image _ _ _).mp ha
        have hlt : ys i < q := hq.2.2.1 (ys i) (mem_image_of_mem _ hi)
        have hlt' : e.symm (ys i) < e.symm q := e.symm.lt_iff_lt.mpr hlt
        rw [← he i, OrderIso.symm_apply_apply] at hlt'
        exact hlt'
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := (mem_image _ _ _).mp hb
        have hlt : q < ys i := hq.2.2.2 (ys i) (mem_image_of_mem _ hi)
        have hlt' : e.symm q < e.symm (ys i) := e.symm.lt_iff_lt.mpr hlt
        rw [← he i, OrderIso.symm_apply_apply] at hlt'
        exact hlt'

/-- **Theorem 3.5.** Sequences of length at most `θ` lie in one automorphism orbit of `H(δ)`
exactly when their order diagrams and strict-slot occupancies agree. -/
theorem horder_orbit_iff (δ : _root_.Ordinal.{u}) (θ : Cardinal.{u})
    (hδ : Order.IsSuccLimit δ) (_hθ : aleph0 ≤ θ)
    (hcf : Cardinal.lift.{u + 1} θ < Cardinal.lift.{u + 1} (Ordinal.cof δ))
    {ι : Type (u + 1)} (hι : #ι ≤ Cardinal.lift.{u + 1} θ) (xs ys : ι → HOrder δ) :
    (SameOrderDiagram xs ys ∧ SameSlotOccupancy xs ys) ↔
      ∃ e : HOrder δ ≃o HOrder δ, ∀ i, e (xs i) = ys i := by
  constructor
  · intro ⟨hdiag, hocc⟩
    refine ⟨StrictMono.orderIsoOfSurjective (orbitMap hδ hcf hι xs ys hdiag hocc)
      (orbitMap_strictMono hδ hcf hι hdiag hocc)
      (orbitMap_surjective hδ hcf hι hdiag hocc), ?_⟩
    intro i
    exact orbitMap_entry hδ hcf hι hdiag hocc i
  · rintro ⟨e, he⟩
    exact orbit_iso_necessity e he

end Orbit

end AEC
