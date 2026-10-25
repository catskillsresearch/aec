module

public import AEC.Section3.HOrderBalance
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal Classical Set

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

end
end AEC
