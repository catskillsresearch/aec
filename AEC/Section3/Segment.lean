module

public import AEC.Section3.HOrderBalance
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.OrderDual
public import Mathlib.Order.SuccPred.Basic
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal Classical Ordinal Set

variable {L : Type u} [LinearOrder L]

lemma small_not_cofinal {s t : Set L} (ht : t ⊆ s) (hcard : #t < setCofinality s) :
    ¬ ∀ x ∈ s, ∃ y ∈ t, x ≤ y := by
  intro hcof
  exact lt_irrefl _ ((HOrder.setCofinality_le ht hcof).trans_lt hcard)

lemma exists_above_small {s t : Set L} (ht : t ⊆ s) (hcard : #t < setCofinality s) :
    ∃ x ∈ s, ∀ y ∈ t, y < x := by
  by_contra hall
  refine small_not_cofinal ht hcard ?_
  intro x hx
  by_contra hnone
  have hlt : ∀ y ∈ t, y < x := by
    intro y hy
    rcases lt_trichotomy y x with h | h | h
    · exact h
    · exact (hnone ⟨y, hy, le_of_eq h.symm⟩).elim
    · exact (hnone ⟨y, hy, h.le⟩).elim
  exact hall ⟨x, hx, hlt⟩

abbrev rightHalf (a b : L) : Set L := {x | a < x ∧ x ≤ b}

abbrev openMid (a b : L) : Set L := {x | a < x ∧ x < b}

lemma mem_openMid_Ioo {a b : L} {x : L} : x ∈ openMid a b ↔ x ∈ Ioo a b := by
  simp [openMid, mem_Ioo]

noncomputable def halfTo {a b c d : L} (hcd : c < d)
    (e : ↥(openMid a b) ≃o ↥(openMid c d)) (x : ↥(rightHalf a b)) : ↥(rightHalf c d) :=
  if h : (x : L) = b then ⟨d, hcd, le_rfl⟩
  else
    let y : ↥(openMid c d) := e ⟨x, x.2.1, lt_of_le_of_ne x.2.2 h⟩
    ⟨y, y.2.1, y.2.2.le⟩

noncomputable def halfInv {a b c d : L} (hab : a < b)
    (e : ↥(openMid a b) ≃o ↥(openMid c d)) (x : ↥(rightHalf c d)) : ↥(rightHalf a b) :=
  if h : (x : L) = d then ⟨b, hab, le_rfl⟩
  else
    let y : ↥(openMid a b) := e.symm ⟨x, x.2.1, lt_of_le_of_ne x.2.2 h⟩
    ⟨y, y.2.1, y.2.2.le⟩

lemma halfTo_endpoint {a b c d : L} (hcd : c < d) (e : ↥(openMid a b) ≃o ↥(openMid c d))
    (x : ↥(rightHalf a b)) (hx : (x : L) = b) : (halfTo hcd e x : L) = d := by
  simp [halfTo, hx]

lemma halfTo_open {a b c d : L} (hcd : c < d) (e : ↥(openMid a b) ≃o ↥(openMid c d))
    (x : ↥(rightHalf a b)) (hx : (x : L) ≠ b) :
    (halfTo hcd e x : L) = e ⟨x, x.2.1, lt_of_le_of_ne x.2.2 hx⟩ := by
  simp [halfTo, hx]

lemma half_left {a b c d : L} (hab : a < b) (hcd : c < d)
    (e : ↥(openMid a b) ≃o ↥(openMid c d)) (x : ↥(rightHalf a b)) :
    halfInv hab e (halfTo hcd e x) = x := by
  ext
  by_cases h : (x : L) = b
  · have hd : (halfTo hcd e x : L) = d := halfTo_endpoint hcd e x h
    simp [halfInv, hd, h]
  · have hopen : (halfTo hcd e x : L) =
        e ⟨x, x.2.1, lt_of_le_of_ne x.2.2 h⟩ := halfTo_open hcd e x h
    have hne : (halfTo hcd e x : L) ≠ d := by
      rw [hopen]
      exact (e ⟨x, x.2.1, lt_of_le_of_ne x.2.2 h⟩).2.2.ne
    rw [halfInv]
    split
    · next hbad => exact (hne hbad).elim
    · next _hgood =>
      let zx : ↥(openMid a b) := ⟨x, x.2.1, lt_of_le_of_ne x.2.2 h⟩
      let zy : ↥(openMid c d) := e zx
      have hzy : (zy : L) = halfTo hcd e x := hopen.symm
      have hmem : (halfTo hcd e x : L) ∈ openMid c d := by
        rw [← hzy]
        exact zy.2
      have hsame : (⟨(halfTo hcd e x : L), hmem⟩ : ↥(openMid c d)) = zy :=
        Subtype.ext hzy.symm
      have hcongr := congrArg (fun z : ↥(openMid c d) => (e.symm z : L)) hsame
      simpa [zy, zx, OrderIso.symm_apply_apply] using hcongr

lemma half_right {a b c d : L} (hab : a < b) (hcd : c < d)
    (e : ↥(openMid a b) ≃o ↥(openMid c d)) (x : ↥(rightHalf c d)) :
    halfTo hcd e (halfInv hab e x) = x := by
  ext
  by_cases h : (x : L) = d
  · rw [halfInv, dif_pos h, halfTo, dif_pos rfl]
    exact h.symm
  · have hopen : (halfInv hab e x : L) =
        e.symm ⟨x, x.2.1, lt_of_le_of_ne x.2.2 h⟩ := by
      rw [halfInv, dif_neg h]
    have hne : (halfInv hab e x : L) ≠ b := by
      rw [hopen]
      exact (e.symm ⟨x, x.2.1, lt_of_le_of_ne x.2.2 h⟩).2.2.ne
    rw [halfTo]
    split
    · next hbad => exact (hne hbad).elim
    · next _hgood =>
      let zx : ↥(openMid c d) := ⟨x, x.2.1, lt_of_le_of_ne x.2.2 h⟩
      let zy : ↥(openMid a b) := e.symm zx
      have hzy : (zy : L) = halfInv hab e x := hopen.symm
      have hmem : (halfInv hab e x : L) ∈ openMid a b := by
        rw [← hzy]
        exact zy.2
      have hsame : (⟨(halfInv hab e x : L), hmem⟩ : ↥(openMid a b)) = zy :=
        Subtype.ext hzy.symm
      have hcongr := congrArg (fun z : ↥(openMid a b) => (e z : L)) hsame
      simpa [zy, zx, OrderIso.apply_symm_apply] using hcongr

lemma half_rel {a b c d : L} (_hab : a < b) (hcd : c < d)
    (e : ↥(openMid a b) ≃o ↥(openMid c d)) (x y : ↥(rightHalf a b)) :
    halfTo hcd e x ≤ halfTo hcd e y ↔ x ≤ y := by
  by_cases hx : (x : L) = b
  · by_cases hy : (y : L) = b
    · have hxy : x = y := Subtype.ext (hx.trans hy.symm)
      simp [hxy]
    · rw [← Subtype.coe_le_coe, halfTo_endpoint hcd e x hx, halfTo_open hcd e y hy,
        ← Subtype.coe_le_coe]
      constructor
      · intro hle
        exact (not_le_of_gt (e ⟨y, y.2.1, lt_of_le_of_ne y.2.2 hy⟩).2.2 hle).elim
      · intro hle
        rw [hx] at hle
        exact (not_le_of_gt (lt_of_le_of_ne y.2.2 hy) hle).elim
  · by_cases hy : (y : L) = b
    · rw [← Subtype.coe_le_coe, halfTo_open hcd e x hx, halfTo_endpoint hcd e y hy,
        ← Subtype.coe_le_coe, hy]
      constructor
      · intro _
        exact x.2.2
      · intro _
        exact (e ⟨x, x.2.1, lt_of_le_of_ne x.2.2 hx⟩).2.2.le
    · rw [← Subtype.coe_le_coe, halfTo_open hcd e x hx, halfTo_open hcd e y hy]
      have hx0 : a < (x : L) ∧ (x : L) < b := ⟨x.2.1, lt_of_le_of_ne x.2.2 hx⟩
      have hy0 : a < (y : L) ∧ (y : L) < b := ⟨y.2.1, lt_of_le_of_ne y.2.2 hy⟩
      constructor
      · intro hle
        have hsub : (⟨(x : L), hx0⟩ : ↥(openMid a b)) ≤ ⟨(y : L), hy0⟩ :=
          (Subtype.coe_le_coe).mp (e.map_rel_iff.mp ((Subtype.coe_le_coe).mpr hle))
        exact (Subtype.coe_le_coe).mp hsub
      · intro hle
        have hsub : (⟨(x : L), hx0⟩ : ↥(openMid a b)) ≤ ⟨(y : L), hy0⟩ :=
          (Subtype.coe_le_coe).mpr hle
        exact (Subtype.coe_le_coe).mp (e.map_rel_iff.mpr hsub)

/-- Adjoin the right endpoint to an open-interval isomorphism. -/
noncomputable def halfOpenRight {a b c d : L} (hab : a < b) (hcd : c < d)
    (e : ↥(Ioo a b) ≃o ↥(Ioo c d)) :
    ↥(rightHalf a b) ≃o ↥(rightHalf c d) := by
  have hab_set : openMid a b = Ioo a b := by
    ext z
    simp [openMid, mem_Ioo]
  have hcd_set : openMid c d = Ioo c d := by
    ext z
    simp [openMid, mem_Ioo]
  let eab : ↥(openMid a b) ≃o ↥(Ioo a b) :=
    (openMid a b).orderIsoOfEq (Ioo a b) hab_set
  let ecd : ↥(Ioo c d) ≃o ↥(openMid c d) :=
    (Ioo c d).orderIsoOfEq (openMid c d) hcd_set.symm
  let e' : ↥(openMid a b) ≃o ↥(openMid c d) := eab.trans (e.trans ecd)
  exact
    { toFun := halfTo hcd e'
      invFun := halfInv hab e'
      left_inv := half_left hab hcd e'
      right_inv := half_right hab hcd e'
      map_rel_iff' := by
        intro x y
        exact half_rel hab hcd e' x y }

/-- The hypotheses of Lemma 3.4, packaged so the induction can move to the dual order. -/
structure SegmentSetup (L : Type u) [LinearOrder L] (κ : Cardinal.{u}) : Prop where
  dense : ∀ a b : L, a < b → ∃ c, a < c ∧ c < b
  noBot : ∀ a : L, ∃ b, b < a
  noTop : ∀ a : L, ∃ c, a < c
  pointChar : ∀ a : L, setCofinality (Iio a) = κ ∧ setCoinitiality (Ioi a) = κ
  oneInterval : ∀ a b c d : L, a < b → c < d → Nonempty (↥(Ioo a b) ≃o ↥(Ioo c d))
  balanced : ∀ c : Cut L, Cut.IsInteriorNonprincipal c → Cut.IsBalanced c

abbrev lowerTail (c : Cut L) (p : L) : Set L := {x | x ∈ c.lower ∧ p ≤ x}

abbrev upperHead (c : Cut L) (p : L) : Set L := {x | x ∈ c.upper ∧ x ≤ p}

lemma lowerTail_subset (c : Cut L) (p : L) : lowerTail c p ⊆ c.lower := fun _ hx => hx.1

lemma lowerTail_cofinal (c : Cut L) {p : L} (hp : p ∈ c.lower) :
    ∀ x ∈ c.lower, ∃ y ∈ lowerTail c p, x ≤ y := by
  intro x hx
  by_cases h : p ≤ x
  · exact ⟨x, ⟨hx, h⟩, le_rfl⟩
  · exact ⟨p, ⟨hp, le_rfl⟩, le_of_not_ge h⟩

lemma lowerTail_cofinality (c : Cut L) {p : L} (hp : p ∈ c.lower) :
    setCofinality (lowerTail c p) = setCofinality c.lower :=
  (setCofinality_eq_of_cofinal (lowerTail_subset c p) (lowerTail_cofinal c hp)).symm

lemma card_Iic_toType_lt {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) (i : ε.ord.ToType) :
    #(Iic i) < ε := by
  have hio : #(Iio i) < ε := mk_Iio_toType_ord_lt i
  have hIic : Iic i = Iio i ∪ {i} := by
    ext x
    simp only [mem_Iic, mem_union, mem_Iio, mem_singleton_iff, le_iff_lt_or_eq]
  rw [hIic]
  have hsum : #(Iio i) + #({i} : Set ε.ord.ToType) < ε := by
    simpa [mk_singleton] using add_one_lt_of_lt hε hio
  exact (mk_union_le _ _).trans_lt hsum

/-- Points already chosen, together with the fixed enumeration up through the current index. -/
def prevSet {ι : Type u} [LinearOrder ι] (g : ι → L) (i : ι) (rec : ∀ j : ι, j < i → L) : Set L :=
  {y | (∃ j : ι, ∃ hj : j < i, y = rec j hj) ∨ (∃ j : ι, j ≤ i ∧ y = g j)}

lemma prevSet_card {ι : Type u} [LinearOrder ι] {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε)
    (g : ι → L) (i : ι) (rec : ∀ j : ι, j < i → L)
    (hio : #(Iio i) < ε) (hic : #(Iic i) < ε) : #(prevSet g i rec) < ε := by
  classical
  let A : Set L := {y | ∃ j : ι, ∃ hj : j < i, y = rec j hj}
  let B : Set L := {y | ∃ j : ι, j ≤ i ∧ y = g j}
  have hAB : prevSet g i rec = A ∪ B := by
    ext y
    constructor
    · intro hy
      rcases hy with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro hy
      rcases hy with h | h
      · exact Or.inl h
      · exact Or.inr h
  let φ : ↥(Iio i) → A := fun j => ⟨rec j.1 j.2, j.1, j.2, rfl⟩
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨j, hj, hjy⟩ := y.2
    exact ⟨⟨j, hj⟩, Subtype.ext hjy.symm⟩
  let ψ : ↥(Iic i) → B := fun j => ⟨g j.1, j.1, j.2, rfl⟩
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨j, hj, hjy⟩ := y.2
    exact ⟨⟨j, hj⟩, Subtype.ext hjy.symm⟩
  have hA : #A < ε := lt_of_le_of_lt (mk_le_of_surjective hφ) hio
  have hB : #B < ε := lt_of_le_of_lt (mk_le_of_surjective hψ) hic
  rw [hAB]
  exact (mk_union_le A B).trans_lt (add_lt_of_lt hε hA hB)

/-- The zero of `ε.ord.ToType`. -/
noncomputable def botIndex (ε : Cardinal.{u}) (hε : ℵ₀ ≤ ε) : ε.ord.ToType :=
  enum (α := ε.ord.ToType) (· < ·) ⟨0, by
    rw [type_toType]
    exact (Cardinal.ord_pos).2 (aleph0_pos.trans_le hε)⟩

lemma typein_botIndex (ε : Cardinal.{u}) (hε : ℵ₀ ≤ ε) :
    typein (α := ε.ord.ToType) (· < ·) (botIndex ε hε) = 0 := by
  unfold botIndex
  exact typein_enum (· < ·) _

lemma botIndex_no_lt (ε : Cardinal.{u}) (hε : ℵ₀ ≤ ε) {j : ε.ord.ToType} :
    ¬ j < botIndex ε hε := by
  intro hj
  have hlt := (typein_lt_typein (α := ε.ord.ToType) (· < ·)).2 hj
  rw [typein_botIndex ε hε] at hlt
  exact not_lt_of_ge (bot_le (a := typein (α := ε.ord.ToType) (· < ·) j)) hlt

lemma eq_botIndex_of_no_lt {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {i : ε.ord.ToType}
    (h : ∀ j : ε.ord.ToType, ¬ j < i) : i = botIndex ε hε := by
  have htype : typein (α := ε.ord.ToType) (· < ·) i = 0 := by
    rcases lt_trichotomy (typein (α := ε.ord.ToType) (· < ·) i) 0 with hlt | heq | hgt
    · exact (not_lt_of_ge (bot_le (a := typein (α := ε.ord.ToType) (· < ·) i)) hlt).elim
    · exact heq
    · exact (h (botIndex ε hε) ((typein_lt_typein (· < ·)).1
        (by simpa [typein_botIndex ε hε] using hgt))).elim
  exact (typein (α := ε.ord.ToType) (· < ·)).injective
    (htype.trans (typein_botIndex ε hε).symm)

/-- A point of `s` strictly above every previously chosen value and every enumerated value
up through `i`. -/
lemma aboveSpec {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {s : Set L} (hs : setCofinality s = ε)
    (g : ε.ord.ToType → L) (hg : ∀ i, g i ∈ s) (i : ε.ord.ToType) (_hi : i ≠ botIndex ε hε)
    (rec : ∀ j : ε.ord.ToType, j < i → ↥s) :
    ∃ x ∈ s, ∀ y ∈ prevSet g i (fun j hj => (rec j hj : L)), y < x := by
  refine exists_above_small ?_ ?_
  · intro y hy
    rcases hy with ⟨j, hj, rfl⟩ | ⟨j, _, rfl⟩
    · exact (rec j hj).2
    · exact hg j
  · rw [hs]
    exact prevSet_card hε g i (fun j hj => (rec j hj : L))
      (mk_Iio_toType_ord_lt i) (card_Iic_toType_lt hε i)

/-- Strictly increasing sequence through `s`, with value `p` at the zero index. At every later
index the value lies above the earlier values and above the fixed enumeration. -/
noncomputable def strictSeq {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) (s : Set L)
    (hs : setCofinality s = ε) (p : L) (hp : p ∈ s) (g : ε.ord.ToType → L)
    (hg : ∀ i, g i ∈ s) : ε.ord.ToType → ↥s :=
  (wellFounded_lt (α := ε.ord.ToType)).fix fun i rec =>
    if hi : i = botIndex ε hε then ⟨p, hp⟩
    else
      ⟨Classical.choose (aboveSpec hε hs g hg i hi rec),
        (Classical.choose_spec (aboveSpec hε hs g hg i hi rec)).1⟩

lemma strictSeq_bot {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {s : Set L} (hs : setCofinality s = ε)
    {p : L} (hp : p ∈ s) {g : ε.ord.ToType → L} (hg : ∀ i, g i ∈ s) {i : ε.ord.ToType}
    (hi : i = botIndex ε hε) : (strictSeq hε s hs p hp g hg i : L) = p := by
  rw [strictSeq, WellFounded.fix_eq, dif_pos hi]

lemma strictSeq_gt_prev {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {s : Set L}
    (hs : setCofinality s = ε) {p : L} (hp : p ∈ s) {g : ε.ord.ToType → L}
    (hg : ∀ i, g i ∈ s) {i : ε.ord.ToType} (hi : i ≠ botIndex ε hε) {y : L}
    (hy : y ∈ prevSet g i (fun j hj => (strictSeq hε s hs p hp g hg j : L))) :
    y < strictSeq hε s hs p hp g hg i := by
  rw [strictSeq, WellFounded.fix_eq, dif_neg hi]
  exact (Classical.choose_spec
    (aboveSpec hε hs g hg i hi (fun j hj => strictSeq hε s hs p hp g hg j))).2 y hy

lemma strictSeq_lt {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {s : Set L} (hs : setCofinality s = ε)
    {p : L} (hp : p ∈ s) {g : ε.ord.ToType → L} (hg : ∀ i, g i ∈ s)
    {j i : ε.ord.ToType} (hj : j < i) :
    (strictSeq hε s hs p hp g hg j : L) < strictSeq hε s hs p hp g hg i := by
  have hi : i ≠ botIndex ε hε := by
    intro h
    exact botIndex_no_lt ε hε (h ▸ hj)
  exact strictSeq_gt_prev hε hs hp hg hi (Or.inl ⟨j, hj, rfl⟩)

lemma strictSeq_strictMono {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {s : Set L}
    (hs : setCofinality s = ε) {p : L} (hp : p ∈ s) {g : ε.ord.ToType → L}
    (hg : ∀ i, g i ∈ s) : StrictMono fun i => (strictSeq hε s hs p hp g hg i : L) :=
  fun _ _ h => strictSeq_lt hε hs hp hg h

lemma strictSeq_gt_g {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {s : Set L} (hs : setCofinality s = ε)
    {p : L} (hp : p ∈ s) {g : ε.ord.ToType → L} (hg : ∀ i, g i ∈ s) {i j : ε.ord.ToType}
    (hi : i ≠ botIndex ε hε) (hj : j ≤ i) : g j < strictSeq hε s hs p hp g hg i :=
  strictSeq_gt_prev hε hs hp hg hi (Or.inr ⟨j, hj, rfl⟩)

lemma strictSeq_cofinal {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {s : Set L} (hs : setCofinality s = ε)
    {p : L} (hp : p ∈ s) {g : ε.ord.ToType → L} (hg : ∀ i, g i ∈ s)
    (hsurj : ∀ x ∈ s, ∃ i, x ≤ g i) :
    ∀ x ∈ s, ∃ i, x ≤ (strictSeq hε s hs p hp g hg i : L) := by
  haveI : NoMaxOrder ε.ord.ToType := Cardinal.noMaxOrder hε
  intro x hx
  obtain ⟨i, hi⟩ := hsurj x hx
  by_cases hbot : i = botIndex ε hε
  · let k := Order.succ i
    have hik : i < k := Order.lt_succ_of_not_isMax (not_isMax i)
    have hk : k ≠ botIndex ε hε := by
      intro hk
      exact botIndex_no_lt ε hε (hk ▸ hik)
    exact ⟨k, hi.trans (strictSeq_gt_g hε hs hp hg hk hik.le).le⟩
  · exact ⟨i, hi.trans (strictSeq_gt_g hε hs hp hg hbot le_rfl).le⟩

/-- A strictly increasing cofinal map realises the cofinality of its codomain. -/
lemma setCofinality_of_strictMono {ι : Type u} [LinearOrder ι] [WellFoundedLT ι]
    (f : ι → L) (hf : StrictMono f) {s : Set L} (hfmem : ∀ i, f i ∈ s)
    (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) : setCofinality s = Order.cof ι := by
  apply le_antisymm
  · obtain ⟨u, hu, hcard⟩ := Order.exists_cof_eq ι
    let t : Set L := f '' u
    have ht : t ⊆ s := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := hy
      exact hfmem i
    have hco : ∀ x ∈ s, ∃ y ∈ t, x ≤ y := by
      intro x hx
      obtain ⟨i, hxi⟩ := hcof x hx
      obtain ⟨j, hj, hij⟩ := hu i
      exact ⟨f j, mem_image_of_mem _ hj, hxi.trans (hf.monotone hij)⟩
    exact (HOrder.setCofinality_le ht hco).trans (mk_image_le.trans_eq hcard)
  · refine HOrder.le_setCofinality ?_
    intro t ht hco
    let idx : ↥t → ι := fun x =>
      (wellFounded_lt (α := ι)).min {i | (x : L) ≤ f i} (by
        obtain ⟨i, hi⟩ := hcof x (ht x.2)
        exact ⟨i, hi⟩)
    let v : Set ι := Set.range idx
    have hv : IsCofinal v := by
      intro k
      obtain ⟨y, hy, hky⟩ := hco (f k) (hfmem k)
      refine ⟨idx ⟨y, hy⟩, mem_range_self _, ?_⟩
      by_contra hk
      have hlt : idx ⟨y, hy⟩ < k := lt_of_not_ge hk
      have hmem : (y : L) ≤ f (idx ⟨y, hy⟩) :=
        (wellFounded_lt (α := ι)).min_mem {i | (y : L) ≤ f i} _
      exact lt_irrefl (f (idx ⟨y, hy⟩)) ((hf hlt).trans_le (hky.trans hmem))
    exact (Order.cof_le hv).trans mk_range_le

/-- The block of a strictly increasing sequence whose least index is `i`. -/
def seqBlock {ι : Type u} [LinearOrder ι] (s : Set L) (f : ι → L) (i : ι) : Set L :=
  {x | x ∈ s ∧ x ≤ f i ∧ ∀ j, j < i → f j < x}

lemma seqBlock_subset {ι : Type u} [LinearOrder ι] {s : Set L} {f : ι → L} {i : ι} :
    seqBlock s f i ⊆ s := fun _ hx => hx.1

noncomputable def seqIndex {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s : Set L}
    (f : ι → L) (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (x : L) (hx : x ∈ s) : ι :=
  Classical.choose ((wellFounded_lt (α := ι)).has_min {i | x ≤ f i} (hcof x hx))

lemma seqIndex_spec {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s : Set L} (f : ι → L)
    (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (x : L) (hx : x ∈ s) :
    x ≤ f (seqIndex f hcof x hx) ∧
      ∀ j, x ≤ f j → ¬ j < seqIndex f hcof x hx := by
  simpa [seqIndex] using
    Classical.choose_spec ((wellFounded_lt (α := ι)).has_min {i | x ≤ f i} (hcof x hx))

lemma seqIndex_mem {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s : Set L} (f : ι → L)
    (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (x : L) (hx : x ∈ s) :
    x ≤ f (seqIndex f hcof x hx) :=
  (seqIndex_spec f hcof x hx).1

lemma seqIndex_not_le {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s : Set L} (f : ι → L)
    (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (x : L) (hx : x ∈ s) {j : ι}
    (hj : j < seqIndex f hcof x hx) : ¬ x ≤ f j :=
  fun hxj => (seqIndex_spec f hcof x hx).2 j hxj hj

lemma mem_seqBlock_index {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s : Set L} (f : ι → L)
    (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (x : L) (hx : x ∈ s) :
    x ∈ seqBlock s f (seqIndex f hcof x hx) := by
  refine ⟨hx, seqIndex_mem f hcof x hx, ?_⟩
  intro j hj
  exact lt_of_not_ge (seqIndex_not_le f hcof x hx hj)

lemma seqIndex_le {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s : Set L} (f : ι → L)
    (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (x : L) (hx : x ∈ s) {i : ι} (hxi : x ≤ f i) :
    seqIndex f hcof x hx ≤ i := by
  rcases lt_trichotomy (seqIndex f hcof x hx) i with hlt | heq | hgt
  · exact hlt.le
  · exact heq.le
  · exact (seqIndex_not_le f hcof x hx hgt hxi).elim

lemma index_eq_of_mem {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s : Set L} (f : ι → L)
    (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) {i : ι} {x : L}
    (hx : x ∈ seqBlock s f i) : seqIndex f hcof x hx.1 = i := by
  apply le_antisymm
  · exact seqIndex_le f hcof x hx.1 hx.2.1
  · by_contra hlt
    have hlt' : seqIndex f hcof x hx.1 < i := lt_of_not_ge hlt
    exact lt_irrefl (f (seqIndex f hcof x hx.1))
      ((hx.2.2 _ hlt').trans_le (seqIndex_mem f hcof x hx.1))

lemma block_before {ι : Type u} [LinearOrder ι] {s : Set L} (f : ι → L)
    {i k : ι} (hik : i < k) {x y : L} (hx : x ∈ seqBlock s f i) (hy : y ∈ seqBlock s f k) :
    x < y :=
  hx.2.1.trans_lt (hy.2.2 i hik)

lemma indexPred_mem {ε : Cardinal.{u}} (_hε : ℵ₀ ≤ ε) (i : ε.ord.ToType) (α : Ordinal)
    (hα : Order.succ α = typein (α := ε.ord.ToType) (· < ·) i) :
    α < typeLT ε.ord.ToType := by
  rw [type_toType]
  have hlt : α < Order.succ α := Order.lt_succ_of_not_isMax (not_isMax α)
  have hlt' : α < typein (α := ε.ord.ToType) (· < ·) i := by
    rw [← hα]
    exact hlt
  exact hlt'.trans (typein_lt_self i)

/-- The predecessor of a successor index, read off the ordinal successor. -/
noncomputable def indexPred {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) (i : ε.ord.ToType)
    (α : Ordinal) (hα : Order.succ α = typein (α := ε.ord.ToType) (· < ·) i) : ε.ord.ToType :=
  enum (· < ·) ⟨α, indexPred_mem hε i α hα⟩

lemma typein_indexPred {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) (i : ε.ord.ToType) (α : Ordinal)
    (hα : Order.succ α = typein (α := ε.ord.ToType) (· < ·) i) :
    typein (α := ε.ord.ToType) (· < ·) (indexPred hε i α hα) = α := by
  unfold indexPred
  exact typein_enum (· < ·) _

lemma indexPred_lt {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) (i : ε.ord.ToType) (α : Ordinal)
    (hα : Order.succ α = typein (α := ε.ord.ToType) (· < ·) i) :
    indexPred hε i α hα < i :=
  (typein_lt_typein (· < ·)).1 <| by
    rw [typein_indexPred hε i α hα, ← hα]
    exact Order.lt_succ_of_not_isMax (not_isMax α)

lemma indexPred_max {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) (i : ε.ord.ToType) (α : Ordinal)
    (hα : Order.succ α = typein (α := ε.ord.ToType) (· < ·) i) {k : ε.ord.ToType} (hk : k < i) :
    k ≤ indexPred hε i α hα := by
  have hkt : typein (α := ε.ord.ToType) (· < ·) k < Order.succ α := by
    rw [hα]
    exact (typein_lt_typein (· < ·)).2 hk
  have hle : typein (α := ε.ord.ToType) (· < ·) k ≤ α := (Order.lt_succ_iff).1 hkt
  rcases lt_trichotomy k (indexPred hε i α hα) with hlt | heq | hgt
  · exact hlt.le
  · exact heq.le
  · have hti : typein (α := ε.ord.ToType) (· < ·) (indexPred hε i α hα) <
        typein (α := ε.ord.ToType) (· < ·) k := (typein_lt_typein (· < ·)).2 hgt
    rw [typein_indexPred hε i α hα] at hti
    exact (not_lt_of_ge hle hti).elim

lemma block_zero {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {s : Set L} {p : L} (hp : p ∈ s)
    (hs : ∀ x ∈ s, p ≤ x) (f : ε.ord.ToType → L)
    (hf0 : f (botIndex ε hε) = p) :
    seqBlock s f (botIndex ε hε) = {p} := by
  ext x
  constructor
  · intro hx
    have hxp : x ≤ p := by simpa [hf0] using hx.2.1
    exact mem_singleton_iff.2 (le_antisymm hxp (hs x hx.1))
  · intro hx
    have hx' : x = p := mem_singleton_iff.1 hx
    refine ⟨hx' ▸ hp, by simpa [hx', hf0] using le_rfl, ?_⟩
    intro j hj
    exact (botIndex_no_lt ε hε hj).elim

lemma block_succ_eq {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {s : Set L} {c : Cut L} {p : L}
    (hs : s = lowerTail c p) (f : ε.ord.ToType → L) (hf : StrictMono f)
    (hfmem : ∀ i, f i ∈ s) (i : ε.ord.ToType) (α : Ordinal)
    (hα : Order.succ α = typein (α := ε.ord.ToType) (· < ·) i) :
    seqBlock s f i = rightHalf (f (indexPred hε i α hα)) (f i) := by
  let j := indexPred hε i α hα
  have hj : j < i := indexPred_lt hε i α hα
  ext x
  constructor
  · intro hx
    exact ⟨hx.2.2 j hj, hx.2.1⟩
  · intro hx
    have hfi : f i ∈ c.lower := by
      rw [hs] at hfmem
      exact (hfmem i).1
    have hxL : x ∈ c.lower := Cut.lower_down c hfi hx.2
    have hpx : p ≤ x := by
      have hpj : p ≤ f j := by
        rw [hs] at hfmem
        exact (hfmem j).2
      exact hpj.trans (hx.1).le
    refine ⟨by rw [hs]; exact ⟨hxL, hpx⟩, hx.2, ?_⟩
    intro k hk
    have hkj : k ≤ j := indexPred_max hε i α hα hk
    exact (hf.monotone hkj).trans_lt hx.1

/-- Lower and upper sides of the cut read off a strictly increasing sequence at a limit index. -/
def limitLower {ι : Type u} [LinearOrder ι] (f : ι → L) (i : ι) : Set L :=
  {x | ∃ j, j < i ∧ x ≤ f j}

def limitUpper {ι : Type u} [LinearOrder ι] (f : ι → L) (i : ι) : Set L :=
  {x | ∀ j, j < i → f j < x}

def limitCut {ι : Type u} [LinearOrder ι] (f : ι → L) (i : ι) : Cut L where
  lower := limitLower f i
  upper := limitUpper f i
  union_eq := by
    ext x
    refine ⟨fun _ => mem_univ x, fun _ => ?_⟩
    by_cases h : ∃ j, j < i ∧ x ≤ f j
    · exact Or.inl h
    · refine Or.inr ?_
      intro j hj
      exact lt_of_not_ge (fun hxj => h ⟨j, hj, hxj⟩)
  disjoint := by
    rw [Set.disjoint_left]
    intro x hxL hxU
    obtain ⟨j, hj, hxj⟩ := hxL
    exact lt_irrefl (f j) ((hxU j hj).trans_le hxj)
  ordered := by
    intro a ha b hb
    obtain ⟨j, hj, haj⟩ := ha
    exact haj.trans_lt (hb j hj)

lemma limitLower_cofinality {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] (f : ι → L)
    (hf : StrictMono f) (i : ι) :
    setCofinality (limitLower f i) = Order.cof (Iio i) := by
  let f' : ↥(Iio i) → L := fun j => f j.1
  have hf' : StrictMono f' := fun _ _ h => hf h
  have hmem : ∀ j, f' j ∈ limitLower f i := fun j => ⟨j.1, j.2, le_rfl⟩
  have hcof : ∀ x ∈ limitLower f i, ∃ j, x ≤ f' j := by
    intro x hx
    obtain ⟨j, hj, hxj⟩ := hx
    exact ⟨⟨j, hj⟩, hxj⟩
  simpa using setCofinality_of_strictMono f' hf' hmem hcof

noncomputable def singletonOrderIso {a b : L} :
    (↥({a} : Set L)) ≃o (↥({b} : Set L)) where
  toFun := fun _ => ⟨b, mem_singleton_iff.2 rfl⟩
  invFun := fun _ => ⟨a, mem_singleton_iff.2 rfl⟩
  left_inv := fun x => Subtype.ext (mem_singleton_iff.1 x.2).symm
  right_inv := fun x => Subtype.ext (mem_singleton_iff.1 x.2).symm
  map_rel_iff' := by
    intro x y
    constructor
    · intro _
      exact le_of_eq (Subtype.ext ((mem_singleton_iff.1 x.2).trans (mem_singleton_iff.1 y.2).symm))
    · intro _
      exact le_rfl

/-- Send each point of `s` to the image of its block. -/
noncomputable def glueTo {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s t : Set L}
    (f g : ι → L) (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (_hcg : ∀ y ∈ t, ∃ i, y ≤ g i)
    (blockIso : ∀ i, ↥(seqBlock s f i) ≃o ↥(seqBlock t g i)) (x : ↥s) : ↥t :=
  let i := seqIndex f hcof (x : L) x.2
  let hx := mem_seqBlock_index f hcof (x : L) x.2
  let y := blockIso i ⟨(x : L), hx⟩
  ⟨(y : L), seqBlock_subset y.2⟩

lemma glueTo_coe {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s t : Set L}
    (f g : ι → L) (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (hcg : ∀ y ∈ t, ∃ i, y ≤ g i)
    (blockIso : ∀ i, ↥(seqBlock s f i) ≃o ↥(seqBlock t g i)) (x : ↥s) :
    (glueTo f g hcof hcg blockIso x : L) =
      blockIso (seqIndex f hcof (x : L) x.2)
        ⟨(x : L), mem_seqBlock_index f hcof (x : L) x.2⟩ := by
  rfl

lemma coe_blockIso_eq {ι : Type u} [LinearOrder ι] {s t : Set L} {f g : ι → L}
    (blockIso : ∀ i, ↥(seqBlock s f i) ≃o ↥(seqBlock t g i)) {j i : ι} (h : j = i) (a : L)
    (ha : a ∈ seqBlock s f j) (ha' : a ∈ seqBlock s f i) :
    (blockIso j ⟨a, ha⟩ : L) = (blockIso i ⟨a, ha'⟩ : L) := by
  subst h
  rfl

lemma glueTo_strictMono {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s t : Set L}
    (f g : ι → L) (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (hcg : ∀ y ∈ t, ∃ i, y ≤ g i)
    (blockIso : ∀ i, ↥(seqBlock s f i) ≃o ↥(seqBlock t g i)) :
    StrictMono (glueTo f g hcof hcg blockIso) := by
  intro x y hxy
  have hx := mem_seqBlock_index f hcof (x : L) x.2
  have hy := mem_seqBlock_index f hcof (y : L) y.2
  have hnot : ¬ seqIndex f hcof (y : L) y.2 < seqIndex f hcof (x : L) x.2 := by
    intro hki
    exact (not_lt_of_gt (block_before f hki hy hx) hxy).elim
  have hik : seqIndex f hcof (x : L) x.2 ≤ seqIndex f hcof (y : L) y.2 := le_of_not_gt hnot
  rcases lt_or_eq_of_le hik with hik | hik
  · have hximg : (glueTo f g hcof hcg blockIso x : L) ∈
        seqBlock t g (seqIndex f hcof (x : L) x.2) := by
      rw [glueTo_coe]
      exact (blockIso _ ⟨(x : L), hx⟩).2
    have hyimg : (glueTo f g hcof hcg blockIso y : L) ∈
        seqBlock t g (seqIndex f hcof (y : L) y.2) := by
      rw [glueTo_coe]
      exact (blockIso _ ⟨(y : L), hy⟩).2
    exact (Subtype.coe_lt_coe).mpr (block_before g hik hximg hyimg)
  · have hmem : (y : L) ∈ seqBlock s f (seqIndex f hcof (x : L) x.2) := by
      rw [hik]
      exact hy
    rw [← Subtype.coe_lt_coe, glueTo_coe, glueTo_coe,
      coe_blockIso_eq blockIso hik.symm (y : L) hy hmem]
    have hsub : (⟨(x : L), hx⟩ : ↥(seqBlock s f (seqIndex f hcof (x : L) x.2))) <
        ⟨(y : L), hmem⟩ := (Subtype.coe_lt_coe).mpr hxy
    exact (Subtype.coe_lt_coe).mp ((blockIso _).strictMono hsub)

lemma glueTo_surjective {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s t : Set L}
    (f g : ι → L) (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (hcg : ∀ y ∈ t, ∃ i, y ≤ g i)
    (blockIso : ∀ i, ↥(seqBlock s f i) ≃o ↥(seqBlock t g i)) :
    Function.Surjective (glueTo f g hcof hcg blockIso) := by
  intro z
  let i := seqIndex g hcg (z : L) z.2
  let hz := mem_seqBlock_index g hcg (z : L) z.2
  let pre : ↥(seqBlock s f i) := (blockIso i).symm ⟨(z : L), hz⟩
  refine ⟨⟨(pre : L), seqBlock_subset pre.2⟩, ?_⟩
  apply Subtype.ext
  have hidx : seqIndex f hcof (pre : L) (seqBlock_subset pre.2) = i :=
    index_eq_of_mem f hcof pre.2
  have hmem : (pre : L) ∈ seqBlock s f i := by
    have hval := mem_seqBlock_index f hcof (pre : L) (seqBlock_subset pre.2)
    rw [hidx] at hval
    exact hval
  rw [glueTo_coe, coe_blockIso_eq blockIso hidx (pre : L)
    (mem_seqBlock_index f hcof (pre : L) (seqBlock_subset pre.2)) hmem]
  have hsub : (⟨(pre : L), hmem⟩ : ↥(seqBlock s f i)) = pre := Subtype.ext rfl
  rw [hsub, (blockIso i).apply_symm_apply ⟨(z : L), hz⟩]

/-- Glue order isomorphisms of the blocks of two strictly increasing cofinal sequences. -/
noncomputable def glueBlocks {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {s t : Set L}
    (f g : ι → L) (hcof : ∀ x ∈ s, ∃ i, x ≤ f i) (hcg : ∀ y ∈ t, ∃ i, y ≤ g i)
    (blockIso : ∀ i, ↥(seqBlock s f i) ≃o ↥(seqBlock t g i)) : ↥s ≃o ↥t :=
  (glueTo_strictMono f g hcof hcg blockIso).orderIsoOfSurjective
    (glueTo f g hcof hcg blockIso) (glueTo_surjective f g hcof hcg blockIso)

/-- A nonzero limit index has something strictly between any earlier index and itself. -/
lemma exists_index_between {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {i j : ε.ord.ToType}
    (hlim : Order.IsSuccLimit (typein (α := ε.ord.ToType) (· < ·) i)) (hj : j < i) :
    ∃ k, j < k ∧ k < i := by
  have hsucc : typein (α := ε.ord.ToType) (· < ·) j + 1 <
      typein (α := ε.ord.ToType) (· < ·) i :=
    hlim.add_one_lt ((typein_lt_typein (· < ·)).2 hj)
  have hlt : typein (α := ε.ord.ToType) (· < ·) j + 1 < typeLT ε.ord.ToType := by
    rw [type_toType]
    exact hsucc.trans (typein_lt_self i)
  let k : ε.ord.ToType := enum (· < ·) ⟨typein (α := ε.ord.ToType) (· < ·) j + 1, hlt⟩
  refine ⟨k, ?_, ?_⟩
  · exact (typein_lt_typein (· < ·)).1 <| by
      rw [show typein (α := ε.ord.ToType) (· < ·) k = typein (α := ε.ord.ToType) (· < ·) j + 1 from
        typein_enum (· < ·) hlt]
      rw [← Order.succ_eq_add_one]
      exact Order.lt_succ_of_not_isMax (not_isMax _)
  · exact (typein_lt_typein (· < ·)).1 <| by
      rw [show typein (α := ε.ord.ToType) (· < ·) k =
        typein (α := ε.ord.ToType) (· < ·) j + 1 from typein_enum (· < ·) hlt]
      exact hsucc

lemma botIndex_lt_of_limit {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {i : ε.ord.ToType}
    (hlim : Order.IsSuccLimit (typein (α := ε.ord.ToType) (· < ·) i)) :
    botIndex ε hε < i :=
  (typein_lt_typein (· < ·)).1 <| by
    rw [typein_botIndex ε hε]
    exact zero_lt_one.trans (one_lt_of_isSuccLimit hlim)

lemma limit_endpoint_upper {ι : Type u} [LinearOrder ι] {f : ι → L} (hf : StrictMono f) (i : ι) :
    f i ∈ limitUpper f i :=
  fun _ hj => hf hj

/-- A least upper point of the sequence cut would have character `cf(i)`, contradicting `κ`. -/
lemma limitUpper_no_least {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] (f : ι → L)
    (hf : StrictMono f) (i : ι) {κ : Cardinal.{u}}
    (hκ : Order.cof (Iio i) < κ) (pointLower : ∀ a : L, setCofinality (Iio a) = κ) :
    ∀ u, ¬ IsLeast (limitUpper f i) u := by
  intro u hu
  let f' : ↥(Iio i) → L := fun j => f j.1
  have hf' : StrictMono f' := fun _ _ h => hf h
  have hmem : ∀ j, f' j ∈ Iio u := by
    intro j
    exact (limitCut f i).ordered (f j.1) ⟨j.1, j.2, le_rfl⟩ u hu.1
  have hcof : ∀ x ∈ Iio u, ∃ j, x ≤ f' j := by
    intro x hx
    have hxU : x ∉ limitUpper f i := by
      intro hxU
      exact not_le_of_gt hx (hu.2 hxU)
    have hunion : limitLower f i ∪ limitUpper f i = Set.univ := (limitCut f i).union_eq
    have hxAll : x ∈ limitLower f i ∪ limitUpper f i := by
      rw [hunion]
      exact mem_univ x
    have hxL : x ∈ limitLower f i := by
      rcases (mem_union x (limitLower f i) (limitUpper f i)).1 hxAll with hxL | hxU'
      · exact hxL
      · exact (hxU hxU').elim
    obtain ⟨j, hj, hxj⟩ := hxL
    exact ⟨⟨j, hj⟩, hxj⟩
  have heq := setCofinality_of_strictMono f' hf' hmem hcof
  exact hκ.ne (heq.symm.trans (pointLower u))

lemma limitCut_interior {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) (f : ε.ord.ToType → L)
    (hf : StrictMono f) (i : ε.ord.ToType)
    (hlim : Order.IsSuccLimit (typein (α := ε.ord.ToType) (· < ·) i)) {κ : Cardinal.{u}}
    (hκ : Order.cof (Iio i) < κ) (pointLower : ∀ a : L, setCofinality (Iio a) = κ) :
    Cut.IsInteriorNonprincipal (limitCut f i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨f (botIndex ε hε), ?_⟩
    exact ⟨botIndex ε hε, botIndex_lt_of_limit hε hlim, le_rfl⟩
  · exact ⟨f i, limit_endpoint_upper hf i⟩
  · intro a ha
    obtain ⟨j, hj, haj⟩ := ha
    obtain ⟨k, hjk, hki⟩ := exists_index_between hε hlim hj
    exact ⟨f k, ⟨k, hki, le_rfl⟩, haj.trans_lt (hf hjk)⟩
  · intro b hb
    by_contra hnone
    have hleast : IsLeast (limitUpper f i) b := by
      refine ⟨hb, ?_⟩
      intro y hy
      exact le_of_not_gt (fun hlt => hnone ⟨y, hy, hlt⟩)
    exact limitUpper_no_least f hf i hκ pointLower b hleast

/-- Upper segments at one regular character. The inductive step of Lemma 3.4 supplies this below
the character being proved. -/
def UpperSeg (L : Type u) [LinearOrder L] (η : Cardinal.{u}) : Prop :=
  ∀ (c d : Cut L), Cut.IsInteriorNonprincipal c → Cut.IsInteriorNonprincipal d →
    Cut.IsBalanced c → Cut.IsBalanced d →
    c.characters = (η, η) → d.characters = (η, η) →
    ∀ (p' q' : L), p' ∈ c.upper → q' ∈ d.upper →
      Nonempty (↥(upperHead c p') ≃o ↥(upperHead d q'))

/-- A limit block is the upper side of the sequence cut, up through the endpoint. -/
lemma block_limit_eq {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) {s : Set L} {c : Cut L} {p : L}
    (hs : s = lowerTail c p) (f : ε.ord.ToType → L) (hfmem : ∀ i, f i ∈ s)
    (hf0 : f (botIndex ε hε) = p) (i : ε.ord.ToType) (hbot : botIndex ε hε < i) :
    seqBlock s f i = upperHead (limitCut f i) (f i) := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.2.2, hx.2.1⟩
  · intro hx
    have hfi : f i ∈ c.lower := by
      have hmem : f i ∈ lowerTail c p := by
        rw [← hs]
        exact hfmem i
      exact hmem.1
    have hxL : x ∈ c.lower := Cut.lower_down c hfi hx.2
    have hpx : p < x := by
      have hfb : f (botIndex ε hε) < x := hx.1 (botIndex ε hε) hbot
      rwa [hf0] at hfb
    refine ⟨?_, hx.2, hx.1⟩
    rw [hs]
    exact ⟨hxL, hpx.le⟩

/-- A cofinal subset realizing `setCofinality s`. -/
noncomputable def cofinalWitness (s : Set L) (hne : s.Nonempty) : Set L :=
  Classical.choose (exists_setCofinality_witness s hne)

lemma cofinalWitness_spec (s : Set L) (hne : s.Nonempty) :
    cofinalWitness s hne ⊆ s ∧ #(cofinalWitness s hne) = setCofinality s ∧
      ∀ x ∈ s, ∃ y ∈ cofinalWitness s hne, x ≤ y :=
  Classical.choose_spec (exists_setCofinality_witness s hne)

noncomputable def cofinalEquiv {ε : Cardinal.{u}} (s : Set L) (hs : setCofinality s = ε)
    (hne : s.Nonempty) : ↥(cofinalWitness s hne) ≃ ε.ord.ToType :=
  Classical.choice <| Cardinal.eq.mp <|
    (cofinalWitness_spec s hne).2.1.trans (hs.trans (mk_ord_toType ε).symm)

noncomputable def cofinalEnum {ε : Cardinal.{u}} (s : Set L) (hs : setCofinality s = ε)
    (hne : s.Nonempty) : ε.ord.ToType → L :=
  fun i => ((cofinalEquiv s hs hne).symm i : L)

lemma cofinalEnum_mem {ε : Cardinal.{u}} (s : Set L) (hs : setCofinality s = ε)
    (hne : s.Nonempty) (i : ε.ord.ToType) : cofinalEnum s hs hne i ∈ s :=
  (cofinalWitness_spec s hne).1 ((cofinalEquiv s hs hne).symm i).2

lemma cofinalEnum_cofinal {ε : Cardinal.{u}} (s : Set L) (hs : setCofinality s = ε)
    (hne : s.Nonempty) : ∀ x ∈ s, ∃ i, x ≤ cofinalEnum s hs hne i := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := (cofinalWitness_spec s hne).2.2 x hx
  refine ⟨(cofinalEquiv s hs hne) ⟨y, hy⟩, ?_⟩
  have hcoe : cofinalEnum s hs hne ((cofinalEquiv s hs hne) ⟨y, hy⟩) = y := by
    unfold cofinalEnum
    rw [Equiv.symm_apply_apply]
  rw [hcoe]
  exact hxy

/-- The order isomorphism of one block, by the three cases of the index. -/
noncomputable def segmentBlockIso {κ : Cardinal.{u}} (setup : SegmentSetup L κ)
    {ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε) (hεlt : ε < κ)
    (upperSmall : ∀ η : Cardinal.{u}, ℵ₀ ≤ η → Cardinal.IsRegular η → η < ε → UpperSeg L η)
    {c : Cut L} {p : L} {s : Set L} (hs : s = lowerTail c p)
    (f : ε.ord.ToType → L) (hf : StrictMono f) (hfmem : ∀ i, f i ∈ s)
    (hf0 : f (botIndex ε hε) = p)
    {d : Cut L} {q : L} {t : Set L} (ht : t = lowerTail d q)
    (g : ε.ord.ToType → L) (hg : StrictMono g) (hgmem : ∀ i, g i ∈ t)
    (hg0 : g (botIndex ε hε) = q) (i : ε.ord.ToType) :
    ↥(seqBlock s f i) ≃o ↥(seqBlock t g i) :=
  Classical.choice <| by
  rcases zero_or_succ_or_isSuccLimit (typein (α := ε.ord.ToType) (· < ·) i) with h0 | hsucc | hlim
  · have hi : i = botIndex ε hε :=
      (typein (α := ε.ord.ToType) (· < ·)).injective
        (h0.trans (typein_botIndex ε hε).symm)
    have hp : p ∈ s := by
      rw [← hf0]
      exact hfmem (botIndex ε hε)
    have hq : q ∈ t := by
      rw [← hg0]
      exact hgmem (botIndex ε hε)
    have hsAbove : ∀ x ∈ s, p ≤ x := by
      intro x hx
      have hx' : x ∈ lowerTail c p := by
        rw [← hs]
        exact hx
      exact hx'.2
    have htAbove : ∀ x ∈ t, q ≤ x := by
      intro x hx
      have hx' : x ∈ lowerTail d q := by
        rw [← ht]
        exact hx
      exact hx'.2
    have hbf : seqBlock s f i = {p} := by
      rw [hi]
      exact block_zero hε hp hsAbove f hf0
    have hbg : seqBlock t g i = {q} := by
      rw [hi]
      exact block_zero hε hq htAbove g hg0
    exact ⟨((seqBlock s f i).orderIsoOfEq {p} hbf).trans
      (singletonOrderIso.trans (({q} : Set L).orderIsoOfEq (seqBlock t g i) hbg.symm))⟩
  · obtain ⟨α, hα⟩ := hsucc
    have hab : f (indexPred hε i α hα) < f i := hf (indexPred_lt hε i α hα)
    have hcd : g (indexPred hε i α hα) < g i := hg (indexPred_lt hε i α hα)
    have hbf := block_succ_eq hε hs f hf hfmem i α hα
    have hbg := block_succ_eq hε ht g hg hgmem i α hα
    let eopen := Classical.choice (setup.oneInterval _ _ _ _ hab hcd)
    exact ⟨((seqBlock s f i).orderIsoOfEq (rightHalf (f (indexPred hε i α hα)) (f i)) hbf).trans
      ((halfOpenRight hab hcd eopen).trans
        ((rightHalf (g (indexPred hε i α hα)) (g i)).orderIsoOfEq (seqBlock t g i) hbg.symm))⟩
  · let η : Cardinal.{u} := Order.cof (Iio i)
    have hηlt : η < ε :=
      (Order.cof_le_cardinalMk (↥(Iio i))).trans_lt (mk_Iio_toType_ord_lt i)
    have hregη : Cardinal.IsRegular η := by
      show Cardinal.IsRegular (Order.cof (Iio i))
      rw [Order.cof_Iio i]
      exact isRegular_cof hlim
    have hηle : ℵ₀ ≤ η := hregη.aleph0_le
    have hηκ : η < κ := hηlt.trans hεlt
    have hbot : botIndex ε hε < i := botIndex_lt_of_limit hε hlim
    have hinterf :=
      limitCut_interior hε f hf i hlim hηκ (fun a => (setup.pointChar a).1)
    have hinterg :=
      limitCut_interior hε g hg i hlim hηκ (fun a => (setup.pointChar a).1)
    have hbalf := setup.balanced (limitCut f i) hinterf
    have hbalg := setup.balanced (limitCut g i) hinterg
    have hlowf := limitLower_cofinality f hf i
    have hlowg := limitLower_cofinality g hg i
    have hcharf : (limitCut f i).characters = (η, η) := by
      unfold Cut.characters
      exact Prod.ext hlowf (hbalf.characters.symm.trans hlowf)
    have hcharg : (limitCut g i).characters = (η, η) := by
      unfold Cut.characters
      exact Prod.ext hlowg (hbalg.characters.symm.trans hlowg)
    have hbf := block_limit_eq hε hs f hfmem hf0 i hbot
    have hbg := block_limit_eq hε ht g hgmem hg0 i hbot
    let e := Classical.choice (upperSmall η hηle hregη hηlt (limitCut f i) (limitCut g i)
      hinterf hinterg hbalf hbalg hcharf hcharg (f i) (g i)
      (limit_endpoint_upper hf i) (limit_endpoint_upper hg i))
    exact ⟨((seqBlock s f i).orderIsoOfEq (upperHead (limitCut f i) (f i)) hbf).trans
      (e.trans ((upperHead (limitCut g i) (g i)).orderIsoOfEq (seqBlock t g i) hbg.symm))⟩

/-- Lower segments of character `ε` are isomorphic once upper segments of every smaller regular
character are. -/
theorem lowerTailIso {κ : Cardinal.{u}} (setup : SegmentSetup L κ) {ε : Cardinal.{u}}
    (hε : ℵ₀ ≤ ε) (hεlt : ε < κ)
    (upperSmall : ∀ η : Cardinal.{u}, ℵ₀ ≤ η → Cardinal.IsRegular η → η < ε → UpperSeg L η)
    {c d : Cut L} (hcc : c.characters = (ε, ε)) (hdc : d.characters = (ε, ε))
    {p q : L} (hp : p ∈ c.lower) (hq : q ∈ d.lower) :
    Nonempty (↥(lowerTail c p) ≃o ↥(lowerTail d q)) := by
  have hcl : setCofinality c.lower = ε := by
    unfold Cut.characters at hcc
    exact (Prod.ext_iff.mp hcc).1
  have hdl : setCofinality d.lower = ε := by
    unfold Cut.characters at hdc
    exact (Prod.ext_iff.mp hdc).1
  let s := lowerTail c p
  let t := lowerTail d q
  have hscof : setCofinality s = ε := (lowerTail_cofinality c hp).trans hcl
  have htcof : setCofinality t = ε := (lowerTail_cofinality d hq).trans hdl
  have hp_s : p ∈ s := ⟨hp, le_rfl⟩
  have hq_t : q ∈ t := ⟨hq, le_rfl⟩
  let enumC := cofinalEnum s hscof ⟨p, hp_s⟩
  let enumD := cofinalEnum t htcof ⟨q, hq_t⟩
  have henumC : ∀ i, enumC i ∈ s := cofinalEnum_mem s hscof ⟨p, hp_s⟩
  have henumD : ∀ i, enumD i ∈ t := cofinalEnum_mem t htcof ⟨q, hq_t⟩
  let f : ε.ord.ToType → L := fun i => strictSeq hε s hscof p hp_s enumC henumC i
  let g : ε.ord.ToType → L := fun i => strictSeq hε t htcof q hq_t enumD henumD i
  have hf : StrictMono f := strictSeq_strictMono hε hscof hp_s henumC
  have hg : StrictMono g := strictSeq_strictMono hε htcof hq_t henumD
  have hfmem : ∀ i, f i ∈ s := fun i => (strictSeq hε s hscof p hp_s enumC henumC i).2
  have hgmem : ∀ i, g i ∈ t := fun i => (strictSeq hε t htcof q hq_t enumD henumD i).2
  have hf0 : f (botIndex ε hε) = p := strictSeq_bot hε hscof hp_s henumC rfl
  have hg0 : g (botIndex ε hε) = q := strictSeq_bot hε htcof hq_t henumD rfl
  have hfcof : ∀ x ∈ s, ∃ i, x ≤ f i :=
    strictSeq_cofinal hε hscof hp_s henumC (cofinalEnum_cofinal s hscof ⟨p, hp_s⟩)
  have hgcof : ∀ x ∈ t, ∃ i, x ≤ g i :=
    strictSeq_cofinal hε htcof hq_t henumD (cofinalEnum_cofinal t htcof ⟨q, hq_t⟩)
  exact ⟨glueBlocks f g hfcof hgcof fun i =>
    segmentBlockIso setup hε hεlt upperSmall rfl f hf hfmem hf0 rfl g hg hgmem hg0 i⟩

/-- Swap the two sides of a cut and reverse the order. -/
def dualCut (c : Cut L) : Cut Lᵒᵈ where
  lower := OrderDual.toDual '' c.upper
  upper := OrderDual.toDual '' c.lower
  union_eq := by
    ext x
    refine ⟨fun _ => mem_univ x, fun _ => ?_⟩
    have hmem : OrderDual.ofDual x ∈ c.lower ∪ c.upper := by
      rw [c.union_eq]
      exact mem_univ _
    rcases (mem_union (OrderDual.ofDual x) c.lower c.upper).1 hmem with h | h
    · exact Or.inr ⟨OrderDual.ofDual x, h, OrderDual.toDual_ofDual x⟩
    · exact Or.inl ⟨OrderDual.ofDual x, h, OrderDual.toDual_ofDual x⟩
  disjoint := by
    rw [Set.disjoint_left]
    intro x hxL hxU
    obtain ⟨a, ha, haeq⟩ := hxL
    obtain ⟨b, hb, hbeq⟩ := hxU
    have hab : a = b := by
      have ha' : OrderDual.ofDual x = a := by
        rw [← haeq]
        exact OrderDual.ofDual_toDual a
      have hb' : OrderDual.ofDual x = b := by
        rw [← hbeq]
        exact OrderDual.ofDual_toDual b
      exact ha'.symm.trans hb'
    have ha_b : b ∈ c.upper := by
      rw [← hab]
      exact ha
    exact Set.disjoint_left.mp c.disjoint hb ha_b
  ordered := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact OrderDual.toDual_lt_toDual.mpr (c.ordered y hy x hx)

lemma dual_lower_cofinality (c : Cut L) :
    setCofinality (dualCut c).lower = setCoinitiality c.upper := by
  unfold setCoinitiality dualCut
  rfl

lemma dual_upper_coinitiality (c : Cut L) :
    setCoinitiality (dualCut c).upper = setCofinality c.lower := by
  unfold setCoinitiality dualCut
  have himg : OrderDual.toDual '' (OrderDual.toDual '' c.lower) =
      (OrderIso.dualDual L) '' c.lower := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hy
      exact ⟨z, hz, (OrderIso.dualDual_apply z).symm⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨OrderDual.toDual z, ⟨z, hz, rfl⟩, OrderIso.dualDual_apply z⟩
  rw [himg]
  exact HOrder.setCofinality_orderIso (OrderIso.dualDual L) c.lower

lemma dualCut_interior {c : Cut L} (hc : Cut.IsInteriorNonprincipal c) :
    Cut.IsInteriorNonprincipal (dualCut c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hc.upper_nonempty
    exact ⟨OrderDual.toDual x, ⟨x, hx, rfl⟩⟩
  · obtain ⟨x, hx⟩ := hc.lower_nonempty
    exact ⟨OrderDual.toDual x, ⟨x, hx, rfl⟩⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, hxy⟩ := hc.upper_no_least x hx
    exact ⟨OrderDual.toDual y, ⟨y, hy, rfl⟩, OrderDual.toDual_lt_toDual.mpr hxy⟩
  · intro b hb
    obtain ⟨x, hx, rfl⟩ := hb
    obtain ⟨y, hy, hxy⟩ := hc.lower_no_greatest x hx
    exact ⟨OrderDual.toDual y, ⟨y, hy, rfl⟩, OrderDual.toDual_lt_toDual.mpr hxy⟩

lemma dualCut_balanced {c : Cut L} (hcb : Cut.IsBalanced c) : Cut.IsBalanced (dualCut c) :=
  ⟨by
    rw [dual_lower_cofinality, dual_upper_coinitiality]
    exact hcb.characters.symm⟩

lemma dualCharacters {ε : Cardinal.{u}} {c : Cut L} (h : c.characters = (ε, ε)) :
    (dualCut c).characters = (ε, ε) := by
  unfold Cut.characters at h ⊢
  refine Prod.ext ?_ ?_
  · rw [dual_lower_cofinality]
    exact (Prod.ext_iff.mp h).2
  · rw [dual_upper_coinitiality]
    exact (Prod.ext_iff.mp h).1

/-- An open interval of the dual order, read back as the dual of an original interval. -/
noncomputable def dualIoo {a b : Lᵒᵈ} (_hab : a < b) :
    ↥(Ioo (α := Lᵒᵈ) a b) ≃o (↥(Ioo (OrderDual.ofDual b) (OrderDual.ofDual a)))ᵒᵈ where
  toFun x :=
    OrderDual.toDual (⟨OrderDual.ofDual (x : Lᵒᵈ), by
      have hx := mem_Ioo.mp x.2
      refine mem_Ioo.mpr ⟨?_, ?_⟩
      · rw [OrderDual.ofDual_lt_ofDual]
        exact hx.2
      · rw [OrderDual.ofDual_lt_ofDual]
        exact hx.1⟩ : ↥(Ioo (OrderDual.ofDual b) (OrderDual.ofDual a)))
  invFun y :=
    let z : ↥(Ioo (OrderDual.ofDual b) (OrderDual.ofDual a)) := OrderDual.ofDual y
    ⟨OrderDual.toDual (z : L), by
      have hz := mem_Ioo.mp z.2
      refine mem_Ioo.mpr ⟨?_, ?_⟩
      · rw [lt_iff_le_not_ge]
        refine ⟨OrderDual.le_toDual.mpr hz.2.le, ?_⟩
        intro hle
        exact not_le_of_gt hz.2 (OrderDual.toDual_le_toDual.mp hle)
      · rw [lt_iff_le_not_ge]
        refine ⟨OrderDual.toDual_le_toDual.mpr hz.1.le, ?_⟩
        intro hle
        exact not_le_of_gt hz.1 (OrderDual.le_toDual.mp hle)⟩
  left_inv x := Subtype.ext (OrderDual.toDual_ofDual (x : Lᵒᵈ))
  right_inv y := by
    apply OrderDual.ext
    apply Subtype.ext
    exact OrderDual.ofDual_toDual _
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      exact (OrderDual.ofDual_le_ofDual).mp h
    · intro h
      exact (OrderDual.ofDual_le_ofDual).mpr h

def dualSetup {κ : Cardinal.{u}} (setup : SegmentSetup L κ) : SegmentSetup Lᵒᵈ κ where
  dense := by
    intro a b hab
    have hab' : OrderDual.ofDual b < OrderDual.ofDual a := by
      rw [OrderDual.ofDual_lt_ofDual]
      exact hab
    obtain ⟨c, hbc, hca⟩ := setup.dense (OrderDual.ofDual b) (OrderDual.ofDual a) hab'
    refine ⟨OrderDual.toDual c, ?_, ?_⟩
    · rw [lt_iff_le_not_ge]
      refine ⟨?_, ?_⟩
      · rw [OrderDual.le_toDual]
        exact hca.le
      · intro hle
        rw [← OrderDual.toDual_ofDual a, OrderDual.toDual_le_toDual] at hle
        exact not_le_of_gt hca hle
    · rw [lt_iff_le_not_ge]
      refine ⟨?_, ?_⟩
      · rw [← OrderDual.toDual_ofDual b, OrderDual.toDual_le_toDual]
        exact hbc.le
      · intro hle
        rw [OrderDual.le_toDual] at hle
        exact not_le_of_gt hbc hle
  noBot := by
    intro a
    obtain ⟨c, hc⟩ := setup.noTop (OrderDual.ofDual a)
    refine ⟨OrderDual.toDual c, ?_⟩
    rw [lt_iff_le_not_ge]
    refine ⟨?_, ?_⟩
    · rw [← OrderDual.toDual_ofDual a, OrderDual.toDual_le_toDual]
      exact hc.le
    · intro hle
      rw [OrderDual.le_toDual] at hle
      exact not_le_of_gt hc hle
  noTop := by
    intro a
    obtain ⟨b, hb⟩ := setup.noBot (OrderDual.ofDual a)
    refine ⟨OrderDual.toDual b, ?_⟩
    rw [lt_iff_le_not_ge]
    refine ⟨?_, ?_⟩
    · rw [OrderDual.le_toDual]
      exact hb.le
    · intro hle
      rw [← OrderDual.toDual_ofDual a, OrderDual.toDual_le_toDual] at hle
      exact not_le_of_gt hb hle
  pointChar := by
    intro a
    refine ⟨?_, ?_⟩
    · have hset : (Iio a : Set Lᵒᵈ) = OrderDual.toDual '' Ioi (OrderDual.ofDual a) := by
        ext x
        constructor
        · intro hx
          refine ⟨OrderDual.ofDual x, ?_, OrderDual.toDual_ofDual x⟩
          rw [mem_Ioi, OrderDual.ofDual_lt_ofDual]
          exact hx
        · rintro ⟨y, hy, rfl⟩
          rw [mem_Iio, lt_iff_le_not_ge]
          refine ⟨?_, ?_⟩
          · rw [← OrderDual.toDual_ofDual a, OrderDual.toDual_le_toDual]
            exact hy.le
          · intro hle
            rw [OrderDual.le_toDual] at hle
            exact not_le_of_gt hy hle
      rw [hset]
      exact (setup.pointChar (OrderDual.ofDual a)).2
    · unfold setCoinitiality
      have hset : OrderDual.toDual '' (Ioi a : Set Lᵒᵈ) =
          (OrderIso.dualDual L) '' Iio (OrderDual.ofDual a) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          refine ⟨OrderDual.ofDual y, ?_, (OrderIso.dualDual_apply (OrderDual.ofDual y)).symm⟩
          rw [mem_Iio, OrderDual.ofDual_lt_ofDual]
          exact hy
        · rintro ⟨z, hz, rfl⟩
          refine ⟨OrderDual.toDual z, ?_, OrderIso.dualDual_apply z⟩
          rw [mem_Ioi, lt_iff_le_not_ge]
          refine ⟨?_, ?_⟩
          · rw [OrderDual.le_toDual]
            exact hz.le
          · intro hle
            rw [← OrderDual.toDual_ofDual a, OrderDual.toDual_le_toDual] at hle
            exact not_le_of_gt hz hle
      rw [hset, HOrder.setCofinality_orderIso (OrderIso.dualDual L)]
      exact (setup.pointChar (OrderDual.ofDual a)).1
  oneInterval := by
    intro a b c d hab hcd
    have hab' : OrderDual.ofDual b < OrderDual.ofDual a := by
      rw [OrderDual.ofDual_lt_ofDual]
      exact hab
    have hcd' : OrderDual.ofDual d < OrderDual.ofDual c := by
      rw [OrderDual.ofDual_lt_ofDual]
      exact hcd
    obtain ⟨e⟩ := setup.oneInterval (OrderDual.ofDual b) (OrderDual.ofDual a)
      (OrderDual.ofDual d) (OrderDual.ofDual c) hab' hcd'
    exact ⟨(dualIoo hab).trans (e.dual.trans (dualIoo hcd).symm)⟩
  balanced := by
    intro c hc
    have hbal := setup.balanced (dualCut c) (dualCut_interior hc)
    have hswap := hbal.characters
    have h1 : setCofinality (dualCut c).lower = setCoinitiality c.upper :=
      dual_lower_cofinality c
    have h2 : setCoinitiality (dualCut c).upper = setCofinality c.lower :=
      dual_upper_coinitiality c
    exact ⟨(h1.symm.trans (hswap.trans h2)).symm⟩

/-- An upper segment is the order dual of the lower segment of the reversed cut. -/
noncomputable def upperOfDual {c : Cut L} (p : L) :
    ↥(upperHead c p) ≃o (↥(lowerTail (dualCut c) (OrderDual.toDual p)))ᵒᵈ where
  toFun x :=
    OrderDual.toDual (⟨OrderDual.toDual (x : L),
      ⟨⟨(x : L), x.2.1, rfl⟩, OrderDual.toDual_le_toDual.mpr x.2.2⟩⟩ :
      ↥(lowerTail (dualCut c) (OrderDual.toDual p)))
  invFun y :=
    let z : ↥(lowerTail (dualCut c) (OrderDual.toDual p)) := OrderDual.ofDual y
    ⟨OrderDual.ofDual (z : Lᵒᵈ), by
      obtain ⟨a, ha, haeq⟩ := z.2.1
      have hpt : OrderDual.ofDual (z : Lᵒᵈ) = a := by
        rw [← haeq]
        exact OrderDual.ofDual_toDual a
      refine ⟨?_, ?_⟩
      · rw [hpt]
        exact ha
      · have hle : OrderDual.toDual p ≤ OrderDual.toDual a := by
          rw [haeq]
          exact z.2.2
        rw [hpt]
        exact OrderDual.toDual_le_toDual.mp hle⟩
  left_inv x := Subtype.ext (OrderDual.ofDual_toDual (x : L))
  right_inv y := by
    apply OrderDual.ext
    apply Subtype.ext
    exact OrderDual.ofDual_toDual _
  map_rel_iff' := by
    intro x y
    constructor
    · intro h
      exact (OrderDual.ofDual_le_ofDual).mp h
    · intro h
      exact (OrderDual.ofDual_le_ofDual).mpr h

/-- Both segment types at character `ε`, for every linear order of point character `κ`. -/
def bothSegments (κ ε : Cardinal.{u}) : Prop :=
  ∀ (L : Type u) [LinearOrder L], SegmentSetup L κ →
    ∀ (c d : Cut L),
      Cut.IsInteriorNonprincipal c → Cut.IsInteriorNonprincipal d →
      Cut.IsBalanced c → Cut.IsBalanced d →
      c.characters = (ε, ε) → d.characters = (ε, ε) →
      ∀ (p q : L), p ∈ c.lower → q ∈ d.lower →
      ∀ (p' q' : L), p' ∈ c.upper → q' ∈ d.upper →
        Nonempty (↥(lowerTail c p) ≃o ↥(lowerTail d q)) ∧
        Nonempty (↥(upperHead c p') ≃o ↥(upperHead d q'))

theorem bothSegments_of_regular {κ ε : Cardinal.{u}} (hε : ℵ₀ ≤ ε)
    (hreg : Cardinal.IsRegular ε) (hεlt : ε < κ) : bothSegments κ ε :=
  (wellFounded_lt (α := Cardinal.{u})).induction
    (C := fun ε => ℵ₀ ≤ ε → Cardinal.IsRegular ε → ε < κ → bothSegments κ ε) ε
    (fun ε ih hε _hreg hεlt => by
      intro L _ setup c d hc hd hcb hdb hcc hdc p q hp hq p' q' hp' hq'
      refine ⟨?_, ?_⟩
      · have upperSmall : ∀ η : Cardinal.{u}, ℵ₀ ≤ η → Cardinal.IsRegular η → η < ε →
            UpperSeg L η := by
          intro η hηle hregη hηlt c1 d1 hc1 hd1 hcb1 hdb1 hcc1 hdc1 u v hu hv
          obtain ⟨p0, hp0⟩ := hc1.lower_nonempty
          obtain ⟨q0, hq0⟩ := hd1.lower_nonempty
          exact (ih η hηlt hηle hregη (hηlt.trans hεlt) L setup c1 d1 hc1 hd1 hcb1 hdb1
            hcc1 hdc1 p0 q0 hp0 hq0 u v hu hv).2
        exact lowerTailIso setup hε hεlt upperSmall hcc hdc hp hq
      · have upperSmallDual : ∀ η : Cardinal.{u}, ℵ₀ ≤ η → Cardinal.IsRegular η → η < ε →
            UpperSeg Lᵒᵈ η := by
          intro η hηle hregη hηlt c1 d1 hc1 hd1 hcb1 hdb1 hcc1 hdc1 u v hu hv
          obtain ⟨p0, hp0⟩ := hc1.lower_nonempty
          obtain ⟨q0, hq0⟩ := hd1.lower_nonempty
          exact (ih η hηlt hηle hregη (hηlt.trans hεlt) Lᵒᵈ (dualSetup setup) c1 d1 hc1 hd1
            hcb1 hdb1 hcc1 hdc1 p0 q0 hp0 hq0 u v hu hv).2
        obtain ⟨e⟩ := lowerTailIso (dualSetup setup) hε hεlt upperSmallDual
          (dualCharacters hcc) (dualCharacters hdc) ⟨p', hp', rfl⟩ ⟨q', hq', rfl⟩
        exact ⟨(upperOfDual p').trans (e.dual.trans (upperOfDual q').symm)⟩)
    hε hreg hεlt

end
end AEC
