module

public import AEC.Section3.OrderCharacter
public import AEC.Section3.OrderEqualityDiagram
public import Mathlib.Order.WellFoundedSet
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Family

@[expose] public section

namespace AEC
section

universe u

open Cardinal Classical Set

attribute [local instance] Classical.propDecidable

variable {β : _root_.Ordinal.{u}}

lemma diff_finset_nonempty {s : Set β.ToType} (hs : s.Infinite) (t : Finset β.ToType) :
    (s \ (t : Set β.ToType)).Nonempty := by
  by_contra hempty
  have hsub : s ⊆ (t : Set β.ToType) := by
    intro x hx
    by_contra hxout
    exact hempty ⟨x, hx, hxout⟩
  exact (Finset.finite_toSet t).not_infinite (hs.mono hsub)

/-- The first `n` points of an infinite well-ordered set, in increasing order. -/
noncomputable def omegaPrefix (s : Set β.ToType) (hs : s.Infinite) : ℕ → Finset β.ToType
  | 0 => ∅
  | n + 1 =>
    insert (Set.IsWF.min (Set.IsWF.of_wellFoundedLT _) (diff_finset_nonempty hs (omegaPrefix s hs n)))
      (omegaPrefix s hs n)

noncomputable def omegaEnum (s : Set β.ToType) (hs : s.Infinite) (n : ℕ) : β.ToType :=
  Set.IsWF.min (Set.IsWF.of_wellFoundedLT (s \ (omegaPrefix s hs n : Set _)))
    (diff_finset_nonempty hs (omegaPrefix s hs n))

lemma omegaPrefix_succ (s : Set β.ToType) (hs : s.Infinite) (n : ℕ) :
    omegaPrefix s hs (n + 1) = insert (omegaEnum s hs n) (omegaPrefix s hs n) := rfl

lemma omegaEnum_mem (s : Set β.ToType) (hs : s.Infinite) (n : ℕ) :
    omegaEnum s hs n ∈ s :=
  ((Set.IsWF.min_mem (Set.IsWF.of_wellFoundedLT _) (diff_finset_nonempty hs _)).1)

lemma omegaEnum_not_mem_prefix (s : Set β.ToType) (hs : s.Infinite) (n : ℕ) :
    omegaEnum s hs n ∉ omegaPrefix s hs n :=
  ((Set.IsWF.min_mem (Set.IsWF.of_wellFoundedLT _) (diff_finset_nonempty hs _)).2)

lemma omegaEnum_step (s : Set β.ToType) (hs : s.Infinite) (n : ℕ) :
    omegaEnum s hs n < omegaEnum s hs (n + 1) := by
  have hmem : omegaEnum s hs (n + 1) ∈ s \ (omegaPrefix s hs n : Set _) := by
    have h := Set.IsWF.min_mem (Set.IsWF.of_wellFoundedLT _)
      (diff_finset_nonempty hs (omegaPrefix s hs (n + 1)))
    rw [omegaPrefix_succ] at h
    exact ⟨h.1, fun hin => h.2 (Finset.mem_insert.mpr (Or.inr hin))⟩
  have hle : omegaEnum s hs n ≤ omegaEnum s hs (n + 1) :=
    le_of_not_gt ((Set.IsWF.of_wellFoundedLT _).not_lt_min (diff_finset_nonempty hs _) hmem)
  have hne : omegaEnum s hs n ≠ omegaEnum s hs (n + 1) := by
    intro h
    have hnot := omegaEnum_not_mem_prefix s hs (n + 1)
    rw [omegaPrefix_succ, ← h] at hnot
    exact hnot (Finset.mem_insert_self _ _)
  exact lt_of_le_of_ne hle hne

lemma omegaEnum_strictMono (s : Set β.ToType) (hs : s.Infinite) :
    StrictMono (omegaEnum s hs) := by
  intro n m hnm
  induction m with
  | zero => exact (Nat.not_lt_zero n hnm).elim
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hnm) with hlt | heq
    · exact (ih hlt).trans (omegaEnum_step s hs m)
    · rw [heq]
      exact omegaEnum_step s hs m

/-- The open interval of `β` immediately below an element of `R`. -/
def gapBelow (R : Set β.ToType) (r : ↥R) : Set β.ToType :=
  {x | x < r.1 ∧ ∀ y ∈ R, y < r.1 → y < x}

/-- The final open ray of `β` above every element of `R`. -/
def gapAbove (R : Set β.ToType) : Set β.ToType :=
  {x | ∀ y ∈ R, y < x}

def gapSet (R : Set β.ToType) : Option (↥R) → Set β.ToType
  | some r => gapBelow R r
  | none => gapAbove R

/-- The least element of `R` strictly above `x`, if one exists. -/
noncomputable def leastAbove (R : Set β.ToType) (x : β.ToType) : Option (↥R) :=
  let s : Set β.ToType := {y | y ∈ R ∧ x < y}
  if h : s.Nonempty then
    let m := Set.IsWF.min (Set.IsWF.of_wellFoundedLT s) h
    some ⟨m, (Set.IsWF.min_mem (Set.IsWF.of_wellFoundedLT s) h).1⟩
  else none

lemma leastAbove_min {R : Set β.ToType} {x : β.ToType} {r : ↥R}
    (h : leastAbove R x = some r) {y : β.ToType} (hy : y ∈ R) (hxy : x < y) : r.1 ≤ y := by
  have hne : ({z | z ∈ R ∧ x < z} : Set β.ToType).Nonempty := ⟨y, hy, hxy⟩
  unfold leastAbove at h
  simp only [hne, dite_eq_left_iff] at h
  cases h
  exact le_of_not_gt ((Set.IsWF.of_wellFoundedLT _).not_lt_min hne ⟨hy, hxy⟩)

/-- Locate `x` at its copy in `R`, or in the gap of the cut it determines. -/
noncomputable def locate (R : Set β.ToType) (x : β.ToType) : Sum (Option (↥R)) (↥R) :=
  if h : x ∈ R then Sum.inr ⟨x, h⟩ else Sum.inl (leastAbove R x)

lemma leastAbove_gap (R : Set β.ToType) (x : β.ToType) (hx : x ∉ R) :
    x ∈ gapSet R (leastAbove R x) := by
  unfold leastAbove
  by_cases h : ({y | y ∈ R ∧ x < y} : Set β.ToType).Nonempty
  · have hm := Set.IsWF.min_mem (Set.IsWF.of_wellFoundedLT _) h
    simp only [h, dite_eq_left_iff, gapSet, gapBelow]
    refine ⟨hm.2, ?_⟩
    intro y hy hylt
    by_contra hge
    have hlt : x < y := lt_of_le_of_ne (le_of_not_gt hge) fun heq => hx (heq ▸ hy)
    exact ((Set.IsWF.of_wellFoundedLT _).not_lt_min h ⟨hy, hlt⟩) hylt
  · simp only [h, dite_eq_right_iff, gapSet, gapAbove]
    intro y hy
    by_contra hge
    exact h ⟨y, hy, lt_of_le_of_ne (le_of_not_gt hge) fun heq => hx (heq ▸ hy)⟩

lemma locate_gap (R : Set β.ToType) {x : β.ToType} {c : Option (↥R)}
    (h : locate R x = Sum.inl c) : x ∈ gapSet R c := by
  unfold locate at h
  by_cases hx : x ∈ R
  · simp [hx] at h
  · simp [hx] at h
    rw [← h]
    exact leastAbove_gap R x hx

lemma gap_disjoint_left (R : Set β.ToType) {x : β.ToType} {c : Option (↥R)}
    (hx : x ∈ gapSet R c) : x ∉ R := by
  intro hR
  cases c with
  | some r =>
    exact lt_irrefl x (hx.2 x hR hx.1)
  | none =>
    exact lt_irrefl x (hx x hR)

/-- Every point of one gap stands in the same relation to every point of `R`. -/
lemma gap_rel (R : Set β.ToType) {c : Option (↥R)} {x z : β.ToType}
    (hx : x ∈ gapSet R c) (hz : z ∈ gapSet R c) {r : β.ToType} (hr : r ∈ R) :
    (r < x ↔ r < z) ∧ r ≠ x ∧ r ≠ z := by
  cases c with
  | some s =>
    have hx1 : x < s.1 := hx.1
    have hz1 : z < s.1 := hz.1
    constructor
    · constructor
      · intro hrx
        exact hz.2 r hr (hrx.trans hx.1)
      · intro hrz
        exact hx.2 r hr (hrz.trans hz.1)
    · exact ⟨fun heq => gap_disjoint_left R hx (heq ▸ hr),
        fun heq => gap_disjoint_left R hz (heq ▸ hr)⟩
  | none =>
    constructor
    · exact ⟨fun _ => hz r hr, fun _ => hx r hr⟩
    · exact ⟨fun heq => gap_disjoint_left R hx (heq ▸ hr),
        fun heq => gap_disjoint_left R hz (heq ▸ hr)⟩

lemma gap_separated (R : Set β.ToType) {x y : β.ToType}
    (hxR : x ∉ R) (hyR : y ∉ R) (hxy : x < y)
    (hne : leastAbove R x ≠ leastAbove R y) :
    ∀ a ∈ gapSet R (leastAbove R x), ∀ b ∈ gapSet R (leastAbove R y), a < b := by
  have hxgap := leastAbove_gap R x hxR
  have hygap := leastAbove_gap R y hyR
  intro a ha b hb
  cases hcx : leastAbove R x with
  | none =>
    cases hcy : leastAbove R y with
    | none => exact (hne (hcx.trans hcy.symm)).elim
    | some r =>
      exfalso
      have hxabove : ∀ z ∈ R, z < x := by
        rw [hcx, gapSet, gapAbove, Set.mem_setOf_eq] at hxgap
        exact hxgap
      have hy_lt : y < r.1 := by
        have : y ∈ gapBelow R r := by simpa [hcy, gapSet] using hygap
        exact this.1
      exact not_lt_of_ge (le_of_lt (hxabove r.1 r.2)) (hxy.trans hy_lt)
  | some r =>
    cases hcy : leastAbove R y with
    | none =>
      have ha_lt : a < r.1 := by
        have : a ∈ gapBelow R r := by simpa [hcx, gapSet] using ha
        exact this.1
      have hb_gt : r.1 < b := by
        have : b ∈ gapAbove R := by simpa [hcy, gapSet] using hb
        exact this r.1 r.2
      exact ha_lt.trans hb_gt
    | some s =>
      have hrlt : r.1 < s.1 := by
        by_contra hle
        have hsle : s.1 ≤ r.1 := le_of_not_gt hle
        have hys : y < s.1 := by
          have : y ∈ gapBelow R s := by simpa [hcy, gapSet] using hygap
          exact this.1
        have hxs : x < s.1 := hxy.trans hys
        have hmin : r.1 ≤ s.1 := leastAbove_min (by rw [hcx]) s.2 hxs
        have heq : r.1 = s.1 := le_antisymm hmin hsle
        exact hne (by rw [hcx, hcy, Subtype.ext heq])
      have ha_lt : a < r.1 := by
        have : a ∈ gapBelow R r := by simpa [hcx, gapSet] using ha
        exact this.1
      have hb_gt : r.1 < b := by
        have : b ∈ gapBelow R s := by simpa [hcy, gapSet] using hb
        exact this.2 r.1 r.2 hrlt
      exact ha_lt.trans hb_gt

/-- A finite slot is copied entirely; an infinite slot contributes its first countably many points. -/
noncomputable def addedSlot (R : Set β.ToType) (c : Option (↥R)) : Set β.ToType :=
  if h : (gapSet R c).Finite then gapSet R c
  else Set.range (omegaEnum (gapSet R c) h)

noncomputable def enrich (R : Set β.ToType) : Set β.ToType :=
  R ∪ ⋃ c : Option (↥R), addedSlot R c

lemma addedSlot_card (R : Set β.ToType) (c : Option (↥R)) : #(addedSlot R c) ≤ ℵ₀ := by
  unfold addedSlot
  split
  · rename_i h
    exact (Set.Finite.lt_aleph0 h).le
  · rename_i h
    let f : ULift.{u} ℕ → β.ToType := fun n => omegaEnum (gapSet R c) h n.down
    have hsub : Set.range (omegaEnum (gapSet R c) h) ⊆ Set.range f := by
      intro x hx
      obtain ⟨n, rfl⟩ := hx
      exact ⟨⟨n⟩, rfl⟩
    exact (mk_le_mk_of_subset hsub).trans (mk_range_le.trans (by simp))

lemma option_card_le (R : Set β.ToType) : #(Option (↥R)) ≤ #R + 1 := by
  let f : Option (↥R) → ↥R ⊕ ULift.{u} (Fin 1)
    | some r => Sum.inl r
    | none => Sum.inr ⟨0⟩
  have hf : Function.Injective f := by
    intro x y h
    cases x <;> cases y <;> cases h <;> rfl
  refine (Cardinal.mk_le_of_injective hf).trans ?_
  simp [Cardinal.mk_sum, add_comm]

lemma enrich_card {a : Cardinal.{u}} (ha : ℵ₀ ≤ a) {R : Set β.ToType} (hR : #R ≤ a) :
    #(enrich R) ≤ a := by
  have hunion : #(⋃ c : Option (↥R), addedSlot R c) ≤ a := by
    refine (mk_iUnion_le _).trans ?_
    have hsup : (⨆ c, #(addedSlot R c)) ≤ ℵ₀ := ciSup_le' (addedSlot_card R)
    refine (mul_le_mul' (option_card_le R) hsup).trans ?_
    refine (mul_le_mul' (add_le_add_left hR 1) le_rfl).trans ?_
    rw [Cardinal.add_one_of_aleph0_le ha, Cardinal.mul_eq_max ha (le_refl ℵ₀), max_eq_left ha]
  refine (mk_union_le _ _).trans ((add_le_add hR hunion).trans ?_)
  rw [Cardinal.add_eq_self ha]

/-- Stages of the closure, indexed by the initial ordinal of `θ⁺`. -/
noncomputable def stage (θ : Cardinal.{u}) (S : Set β.ToType)
    (i : (Order.succ θ).ord.ToType) : Set β.ToType :=
  enrich (S ∪ ⋃ j : {j : (Order.succ θ).ord.ToType // j < i}, stage θ S j.1)
termination_by i
decreasing_by
  exact j.2

lemma stage_card {θ a : Cardinal.{u}} (ha : ℵ₀ ≤ a) (hsucc : Order.succ θ ≤ a)
    {S : Set β.ToType} (hS : #S ≤ a) (i : (Order.succ θ).ord.ToType) :
    #(stage θ S i) ≤ a := by
  apply (wellFounded_lt (α := (Order.succ θ).ord.ToType)).induction i
  intro i ih
  rw [stage.eq_def]
  exact enrich_card ha (by
    have hprev : #(⋃ j : {j : (Order.succ θ).ord.ToType // j < i}, stage θ S j.1) ≤ a := by
      refine (mk_iUnion_le _).trans ?_
      refine (mul_le_mul'
        ((Cardinal.mk_le_of_injective Subtype.val_injective).trans (by
          rw [Cardinal.mk_ord_toType]))
        (ciSup_le' (fun j : {j : (Order.succ θ).ord.ToType // j < i} => ih j.1 j.2))).trans ?_
      exact (mul_le_mul' hsucc le_rfl).trans (by rw [Cardinal.mul_eq_self ha])
    refine (mk_union_le _ _).trans ((add_le_add hS hprev).trans ?_)
    rw [Cardinal.add_eq_self ha])

/-- The rank of a tuple entry among the earlier entries of the same gap. -/
noncomputable def gapRank {n : ℕ} (R : Set β.ToType) (q : Fin n → β.ToType)
    (c : Option (↥R)) (k : Fin n) : ℕ :=
  (Finset.univ.filter fun j : Fin n => locate R (q j) = Sum.inl c ∧ q j < q k).card

/-- The image of one tuple entry: parameters stay, finite gaps stay, infinite gaps use `ω`. -/
noncomputable def matched {n : ℕ} (R : Set β.ToType) (q : Fin n → β.ToType)
    (k : Fin n) : β.ToType :=
  match locate R (q k) with
  | Sum.inr r => r.1
  | Sum.inl c =>
    if h : (gapSet R c).Finite then q k
    else omegaEnum (gapSet R c) h (gapRank R q c k)

lemma matched_mem {n : ℕ} (R : Set β.ToType) (q : Fin n → β.ToType) (k : Fin n) :
    matched R q k ∈ enrich R := by
  unfold matched
  split
  · rename_i r h
    exact Or.inl r.2
  · rename_i c h
    refine Or.inr ?_
    refine mem_iUnion.mpr ⟨c, ?_⟩
    unfold addedSlot
    by_cases hfin : (gapSet R c).Finite
    · simp only [hfin, dite_eq_left_iff]
      have hx := locate_gap R h
      exact hx
    · simp only [hfin, dite_eq_right_iff]
      exact ⟨gapRank R q c k, rfl⟩

lemma locate_inr_eq {R : Set β.ToType} {x : β.ToType} {r : ↥R}
    (h : locate R x = Sum.inr r) : x = r.1 := by
  unfold locate at h
  by_cases hx : x ∈ R
  · simp [hx] at h
    cases h
    rfl
  · simp [hx] at h

lemma locate_inl_eq {R : Set β.ToType} {x : β.ToType} {c : Option (↥R)}
    (h : locate R x = Sum.inl c) : leastAbove R x = c ∧ x ∉ R := by
  unfold locate at h
  by_cases hx : x ∈ R
  · simp [hx] at h
  · simp [hx] at h
    exact ⟨h, hx⟩

lemma matched_of_inr {n : ℕ} (R : Set β.ToType) (q : Fin n → β.ToType) (k : Fin n) {r : ↥R}
    (h : locate R (q k) = Sum.inr r) : matched R q k = r.1 := by
  simp [matched, h]

lemma matched_mem_gap {n : ℕ} (R : Set β.ToType) (q : Fin n → β.ToType) (k : Fin n)
    {c : Option (↥R)} (h : locate R (q k) = Sum.inl c) : matched R q k ∈ gapSet R c := by
  have hx := locate_gap R h
  by_cases hfin : (gapSet R c).Finite
  · simpa [matched, h, hfin] using hx
  · simpa [matched, h, hfin] using omegaEnum_mem _ hfin (gapRank R q c k)

lemma matched_eq_of_eq {n : ℕ} (R : Set β.ToType) (q : Fin n → β.ToType) {k m : Fin n}
    (h : q k = q m) : matched R q k = matched R q m := by
  have hrank : ∀ c, gapRank R q c k = gapRank R q c m := by
    intro c
    unfold gapRank
    congr 1
    refine Finset.filter_congr ?_
    intro j _
    simp [h]
  unfold matched
  rw [h]
  split
  · rfl
  · rename_i c hc
    by_cases hfin : (gapSet R c).Finite
    · simp [hfin]
    · simp [hfin, hrank]

/-- A strictly earlier tuple entry is sent to a strictly earlier point. -/
lemma matched_lt {n : ℕ} (R : Set β.ToType) (q : Fin n → β.ToType) {k m : Fin n}
    (hkm : q k < q m) : matched R q k < matched R q m := by
  cases hk : locate R (q k) with
  | inr rk =>
    cases hm : locate R (q m) with
    | inr rm =>
      have hkq : q k = rk.1 := locate_inr_eq hk
      have hmq : q m = rm.1 := locate_inr_eq hm
      simpa [matched_of_inr R q k hk, matched_of_inr R q m hm, hkq, hmq] using hkm
    | inl c =>
      have hkq : matched R q k = q k := by
        rw [matched_of_inr R q k hk, locate_inr_eq hk]
      have hmR : q k ∈ R := by rw [locate_inr_eq hk]; exact rk.2
      have hmg := matched_mem_gap R q m hm
      rw [hkq]
      cases c with
      | some s =>
        have hmlt : q m < s.1 := (locate_gap R hm).1
        exact hmg.2 (q k) hmR (hkm.trans hmlt)
      | none =>
        exact hmg (q k) hmR
  | inl c =>
    cases hm : locate R (q m) with
    | inr rm =>
      have hmq : matched R q m = q m := by
        rw [matched_of_inr R q m hm, locate_inr_eq hm]
      have hmR : q m ∈ R := by rw [locate_inr_eq hm]; exact rm.2
      have hkg := matched_mem_gap R q k hk
      rw [hmq]
      cases c with
      | some s =>
        have hklt : matched R q k < s.1 := (matched_mem_gap R q k hk).1
        have hsle : s.1 ≤ q m :=
          leastAbove_min (locate_inl_eq hk).1 hmR hkm
        exact hklt.trans_le hsle
      | none =>
        exact (lt_asymm hkm ((locate_gap R hk) (q m) hmR)).elim
    | inl d =>
      by_cases hcd : c = d
      · subst hcd
        have hkg := locate_gap R hk
        have hmg := locate_gap R hm
        by_cases hfin : (gapSet R c).Finite
        · have hkq : matched R q k = q k := by simp [matched, hk, hfin]
          have hmq : matched R q m = q m := by simp [matched, hm, hfin]
          simpa [hkq, hmq] using hkm
        · have hkq : matched R q k = omegaEnum (gapSet R c) hfin (gapRank R q c k) := by
            simp [matched, hk, hfin]
          have hmq : matched R q m = omegaEnum (gapSet R c) hfin (gapRank R q c m) := by
            simp [matched, hm, hfin]
          rw [hkq, hmq]
          refine omegaEnum_strictMono _ hfin ?_
          unfold gapRank
          refine Finset.card_lt_card ?_
          refine ⟨?_, ?_⟩
          · intro j hj
            have hj' := Finset.mem_filter.mp hj
            exact Finset.mem_filter.mpr ⟨hj'.1, hj'.2.1, hj'.2.2.trans hkm⟩
          · intro hsub
            have hmem : k ∈ Finset.univ.filter
                (fun j : Fin n => locate R (q j) = Sum.inl c ∧ q j < q m) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hkm⟩
            have hkself := Finset.mem_filter.mp (hsub hmem)
            exact lt_irrefl _ hkself.2.2
      · have hxR := (locate_inl_eq hk).2
        have hyR := (locate_inl_eq hm).2
        have hcut : leastAbove R (q k) ≠ leastAbove R (q m) := by
          rw [(locate_inl_eq hk).1, (locate_inl_eq hm).1]
          exact hcd
        have hmemk : matched R q k ∈ gapSet R (leastAbove R (q k)) := by
          simpa [(locate_inl_eq hk).1] using matched_mem_gap R q k hk
        have hmemm : matched R q m ∈ gapSet R (leastAbove R (q m)) := by
          simpa [(locate_inl_eq hm).1] using matched_mem_gap R q m hm
        exact gap_separated R hxR hyR hkm hcut _ hmemk _ hmemm

lemma matched_eq_iff {n : ℕ} (R : Set β.ToType) (q : Fin n → β.ToType) (k m : Fin n) :
    matched R q k = matched R q m ↔ q k = q m := by
  constructor
  · intro h
    rcases lt_trichotomy (q k) (q m) with hlt | heq | hgt
    · have hlt' := matched_lt R q hlt
      rw [h] at hlt'
      exact (lt_irrefl _ hlt').elim
    · exact heq
    · have hgt' := matched_lt R q hgt
      rw [← h] at hgt'
      exact (lt_irrefl _ hgt').elim
  · exact matched_eq_of_eq R q

lemma matched_lt_iff {n : ℕ} (R : Set β.ToType) (q : Fin n → β.ToType) (k m : Fin n) :
    matched R q k < matched R q m ↔ q k < q m := by
  constructor
  · intro h
    rcases lt_trichotomy (q k) (q m) with hlt | heq | hgt
    · exact hlt
    · have hlt' := h
      rw [matched_eq_of_eq R q heq] at hlt'
      exact (lt_irrefl _ hlt').elim
    · exact (lt_asymm h (matched_lt R q hgt)).elim
  · exact matched_lt R q

/-- Matching preserves every comparison with a parameter from `R`. -/
lemma matched_param {n : ℕ} (R : Set β.ToType) (q : Fin n → β.ToType) (k : Fin n)
    {r : β.ToType} (hr : r ∈ R) :
    (r < q k ↔ r < matched R q k) ∧ (q k < r ↔ matched R q k < r) ∧
      (q k = r ↔ matched R q k = r) := by
  have hpair : (r < q k ↔ r < matched R q k) ∧ (q k = r ↔ matched R q k = r) := by
    cases hloc : locate R (q k) with
    | inr s =>
      have heq : matched R q k = q k := by
        rw [matched_of_inr R q k hloc, locate_inr_eq hloc]
      simp [heq]
    | inl c =>
      have hrel := gap_rel R (locate_gap R hloc) (matched_mem_gap R q k hloc) hr
      refine ⟨hrel.1, ?_⟩
      constructor
      · intro heq
        exact (hrel.2.1 heq.symm).elim
      · intro heq
        exact (hrel.2.2 heq.symm).elim
  refine ⟨hpair.1, ?_, hpair.2⟩
  constructor
  · intro h
    rcases lt_trichotomy (matched R q k) r with hlt | heq | hgt
    · exact hlt
    · exact (h.ne (hpair.2.mpr heq)).elim
    · exact (lt_asymm h (hpair.1.mpr hgt)).elim
  · intro h
    rcases lt_trichotomy (q k) r with hlt | heq | hgt
    · exact hlt
    · exact (h.ne (hpair.2.mp heq)).elim
    · exact (lt_asymm h (hpair.1.mp hgt)).elim

lemma matched_diagram {n : ℕ} {ι : Type u} (R : Set β.ToType) (p : ι → β.ToType)
    (hp : ∀ i, p i ∈ R) (q : Fin n → β.ToType) :
    SameOrderDiagram (Sum.elim p q) (Sum.elim p (matched R q)) := by
  constructor
  · intro a b
    cases a with
    | inl i =>
      cases b with
      | inl j => simp [Sum.elim]
      | inr m =>
        simpa [Sum.elim, eq_comm] using (matched_param R q m (hp i)).2.2
    | inr k =>
      cases b with
      | inl j => simpa [Sum.elim] using (matched_param R q k (hp j)).2.2
      | inr m => simpa [Sum.elim] using (matched_eq_iff R q k m).symm
  · intro a b
    cases a with
    | inl i =>
      cases b with
      | inl j => simp [Sum.elim]
      | inr m => simpa [Sum.elim] using (matched_param R q m (hp i)).1
    | inr k =>
      cases b with
      | inl j => simpa [Sum.elim] using (matched_param R q k (hp j)).2.1
      | inr m => simpa [Sum.elim] using (matched_lt_iff R q k m).symm

/-- Compare an element of `o.ToType` with the point named by a larger ordinal. -/
lemma toType_lt_of_ordinal_lt {o : _root_.Ordinal.{u}} {x : o.ToType} {a : _root_.Ordinal.{u}}
    (ha : a < o) (hx : (Ordinal.ToType.toOrd x).1 < a) : x < Ordinal.ToType.mk ⟨a, ha⟩ := by
  have hsub : Ordinal.ToType.toOrd x < ⟨a, ha⟩ := Subtype.mk_lt_mk.mpr hx
  have hmap := (Ordinal.ToType.mk.lt_iff_lt).mpr hsub
  simpa [Ordinal.ToType.mk.apply_symm_apply] using hmap

lemma ordinal_lt_toType {o : _root_.Ordinal.{u}} {x y : o.ToType}
    (h : (Ordinal.ToType.toOrd x).1 < (Ordinal.ToType.toOrd y).1) : x < y := by
  have hsub : Ordinal.ToType.toOrd x < Ordinal.ToType.toOrd y := Subtype.mk_lt_mk.mpr h
  have hmap := (Ordinal.ToType.mk.lt_iff_lt).mpr hsub
  simpa [Ordinal.ToType.mk.apply_symm_apply] using hmap

/-- The argument of one stage still has cardinality at most `a`. -/
lemma prior_card {θ a : Cardinal.{u}} (ha : ℵ₀ ≤ a) (hsucc : Order.succ θ ≤ a)
    {S : Set β.ToType} (hS : #S ≤ a) (i : (Order.succ θ).ord.ToType) :
    Cardinal.mk (↥(S ∪ Set.iUnion (fun j : {j : (Order.succ θ).ord.ToType // j < i} =>
      stage θ S j.1))) ≤ a := by
  have hprev : Cardinal.mk (↥(Set.iUnion (fun j : {j : (Order.succ θ).ord.ToType // j < i} =>
      stage θ S j.1))) ≤ a := by
    refine (mk_iUnion_le _).trans ?_
    refine (mul_le_mul'
      ((Cardinal.mk_le_of_injective Subtype.val_injective).trans (by
        rw [Cardinal.mk_ord_toType]))
      (ciSup_le' (fun j : {j : (Order.succ θ).ord.ToType // j < i} =>
        stage_card ha hsucc hS j.1))).trans ?_
    exact (mul_le_mul' hsucc le_rfl).trans (by rw [Cardinal.mul_eq_self ha])
  refine (mk_union_le _ _).trans ((add_le_add hS hprev).trans ?_)
  rw [Cardinal.add_eq_self ha]

lemma closureSet_card {θ a : Cardinal.{u}} (ha : ℵ₀ ≤ a) (hsucc : Order.succ θ ≤ a)
    {S : Set β.ToType} (hS : #S ≤ a) :
    #(⋃ i : (Order.succ θ).ord.ToType, stage θ S i) ≤ a := by
  refine (mk_iUnion_le _).trans ?_
  refine (mul_le_mul' (by rw [Cardinal.mk_ord_toType])
    (ciSup_le' (stage_card ha hsucc hS))).trans ?_
  exact (mul_le_mul' hsucc le_rfl).trans (by rw [Cardinal.mul_eq_self ha])

/-- The final gap of a small set is infinite, so the next stage has room above it. -/
lemma gapAbove_infinite (hlim : Order.IsSuccLimit β) {R : Set β.ToType}
    (hR : #R < Ordinal.cof β) :
    (gapAbove R).Infinite := by
  let fOrd : ↥R → _root_.Ordinal.{u} := fun x => (Ordinal.ToType.toOrd x.1).1
  have hsup : (⨆ x, fOrd x) < β :=
    Ordinal.iSup_lt_of_lt_cof hR (fun x => (Ordinal.ToType.toOrd x.1).2)
  have hnat : ∀ n : ℕ, (⨆ x, fOrd x) + n < β := by
    intro n
    induction n with
    | zero => simpa using hsup
    | succ n ih => simpa [Nat.cast_succ, add_assoc] using hlim.succ_lt ih
  let f : ℕ → β.ToType := fun n =>
    Ordinal.ToType.mk ⟨(⨆ x, fOrd x) + (n + 1), hnat (n + 1)⟩
  have hsub : Set.range f ⊆ gapAbove R := by
    intro z hz
    obtain ⟨n, rfl⟩ := hz
    intro x hx
    have hxle : fOrd ⟨x, hx⟩ ≤ ⨆ y, fOrd y := Ordinal.le_iSup fOrd ⟨x, hx⟩
    have hxlt : fOrd ⟨x, hx⟩ < (⨆ y, fOrd y) + (n + 1) :=
      lt_of_le_of_lt hxle (by
        have hpos : (0 : _root_.Ordinal.{u}) < n + 1 := by
          simpa using (Nat.cast_pos.mpr (Nat.succ_pos n) : (0 : _root_.Ordinal.{u}) < (n + 1 : ℕ))
        exact lt_add_of_pos_right _ hpos)
    exact ordinal_lt_toType (by
      have hcoe : (Ordinal.ToType.toOrd (f n)).1 = (⨆ y, fOrd y) + (n + 1) := by
        have happ := Ordinal.ToType.mk.symm_apply_apply
          (⟨(⨆ y, fOrd y) + (n + 1), hnat (n + 1)⟩ : Set.Iio β)
        simpa [f, happ]
      simpa [fOrd, hcoe] using hxlt)
  have hinj : Function.Injective f := by
    intro n m h
    have hord := congrArg (fun z : β.ToType => (Ordinal.ToType.toOrd z).1) h
    have hcoe (k : ℕ) : (Ordinal.ToType.toOrd (f k)).1 = (⨆ y, fOrd y) + (k + 1) := by
      have happ := Ordinal.ToType.mk.symm_apply_apply
        (⟨(⨆ y, fOrd y) + (k + 1), hnat (k + 1)⟩ : Set.Iio β)
      simpa [f, happ]
    rw [hcoe n, hcoe m] at hord
    have hnatEq : (n + 1 : _root_.Ordinal.{u}) = m + 1 := (add_left_cancel_iff (a := ⨆ y, fOrd y)).mp hord
    have hn : n + 1 = m + 1 := Nat.cast_injective hnatEq
    exact Nat.succ_injective hn
  exact (Set.infinite_range_of_injective hinj).mono hsub

lemma exists_enrich_above (hlim : Order.IsSuccLimit β) {R : Set β.ToType}
    (hR : #R < Ordinal.cof β) :
    ∃ z, z ∈ enrich R ∧ ∀ x ∈ R, x < z := by
  have hinf : (gapSet R none).Infinite := gapAbove_infinite hlim hR
  refine ⟨omegaEnum (gapSet R none) hinf 0, ?_, ?_⟩
  · refine Or.inr (mem_iUnion.mpr ⟨none, ?_⟩)
    have hnot : ¬ (gapSet R none).Finite := hinf
    simpa [addedSlot, hnot] using ⟨0, rfl⟩
  · intro x hx
    exact omegaEnum_mem _ hinf 0 x hx

/-- Lemma 3.7: a set of size at most `a` sits in a subset of the same size which matches every
finite order pattern over at most `θ` parameters and is cofinal of character above `θ`. -/
theorem support_closure (θ a : Cardinal.{u}) (hθ : ℵ₀ ≤ θ) (ha : Order.succ θ ≤ a)
    (hcof : a < Ordinal.cof β) (S : Set β.ToType) (hS : #S ≤ a) :
    ∃ T0 : Set β.ToType, S ⊆ T0 ∧ #T0 ≤ a ∧
      (∀ {ι : Type u} (_hι : #ι ≤ θ) (p : ι → β.ToType), (∀ i, p i ∈ T0) →
        ∀ {n : ℕ} (q : Fin n → β.ToType), ∃ q' : Fin n → β.ToType,
          (∀ i, q' i ∈ T0) ∧ SameOrderDiagram (Sum.elim p q) (Sum.elim p q')) ∧
      (∃ b : β.ToType, ∀ x ∈ T0, x ≤ b) ∧ θ < setCofinality T0 := by
  let T0 : Set β.ToType := ⋃ i : (Order.succ θ).ord.ToType, stage θ S i
  have haleph : ℵ₀ ≤ a := hθ.trans ((Order.le_succ θ).trans ha)
  have hlim : Order.IsSuccLimit β := Ordinal.one_lt_cof_iff.mp
    (lt_of_lt_of_le (one_lt_aleph0.trans_le haleph) hcof.le)
  have hpos : (0 : _root_.Ordinal.{u}) < (Order.succ θ).ord := by
    refine lt_of_lt_of_le (Ordinal.natCast_lt_omega0 0) ?_
    rw [← ord_aleph0]
    exact ord_le_ord.mpr (hθ.trans (Order.le_succ θ))
  let i0 : (Order.succ θ).ord.ToType := Ordinal.ToType.mk ⟨0, hpos⟩
  have hSsub : S ⊆ T0 := by
    intro x hx
    refine mem_iUnion.mpr ⟨i0, ?_⟩
    rw [stage.eq_def]
    exact Or.inl (Or.inl hx)
  have hcard : #T0 ≤ a := closureSet_card haleph ha hS
  have hreg : Ordinal.cof (Order.succ θ).ord = Order.succ θ :=
    (isRegular_succ hθ).cof_ord
  have hbound : ∃ b : β.ToType, ∀ x ∈ T0, x ≤ b := by
    let fOrd : ↥T0 → _root_.Ordinal.{u} := fun x => (Ordinal.ToType.toOrd x.1).1
    have hsup : (⨆ x, fOrd x) < β :=
      Ordinal.iSup_lt_of_lt_cof (lt_of_le_of_lt hcard hcof) (fun x => (Ordinal.ToType.toOrd x.1).2)
    have h1 : (⨆ x, fOrd x) + 1 < β := hlim.succ_lt hsup
    refine ⟨Ordinal.ToType.mk ⟨(⨆ x, fOrd x) + 1, h1⟩, ?_⟩
    intro x hx
    have hxlt : fOrd ⟨x, hx⟩ < (⨆ y, fOrd y) + 1 :=
      lt_of_le_of_lt (Ordinal.le_iSup fOrd ⟨x, hx⟩) (lt_add_of_pos_right _ zero_lt_one)
    exact (toType_lt_of_ordinal_lt h1 (by simpa [fOrd] using hxlt)).le
  have habove : ∀ t : Set β.ToType, t ⊆ T0 → #t ≤ θ → ∃ z ∈ T0, ∀ y ∈ t, y < z := by
    intro t ht htcard
    let j : ↥t → (Order.succ θ).ord.ToType :=
      fun x => Classical.choose (mem_iUnion.mp (ht x.2))
    have hj : ∀ x : ↥t, x.1 ∈ stage θ S (j x) :=
      fun x => Classical.choose_spec (mem_iUnion.mp (ht x.2))
    have hidx : #↥t < Ordinal.cof (Order.succ θ).ord := by
      rw [hreg]
      exact htcard.trans_lt (Order.lt_succ θ)
    have hsup : (⨆ x : ↥t, (Ordinal.ToType.toOrd (j x)).1) < (Order.succ θ).ord :=
      Ordinal.iSup_lt_of_lt_cof hidx (fun x => (Ordinal.ToType.toOrd (j x)).2)
    have h1 : (⨆ x : ↥t, (Ordinal.ToType.toOrd (j x)).1) + 1 < (Order.succ θ).ord :=
      (isSuccLimit_ord (hθ.trans (Order.le_succ θ))).succ_lt hsup
    let i1 : (Order.succ θ).ord.ToType :=
      Ordinal.ToType.mk ⟨(⨆ x : ↥t, (Ordinal.ToType.toOrd (j x)).1) + 1, h1⟩
    have hjlt : ∀ x : ↥t, j x < i1 := by
      intro x
      refine toType_lt_of_ordinal_lt h1 ?_
      exact lt_of_le_of_lt (Ordinal.le_iSup (fun y : ↥t => (Ordinal.ToType.toOrd (j y)).1) x)
        (lt_add_of_pos_right _ zero_lt_one)
    let R0 : Set β.ToType :=
      S ∪ ⋃ k : {k : (Order.succ θ).ord.ToType // k < i1}, stage θ S k.1
    have htR : t ⊆ R0 := by
      intro y hy
      exact Or.inr (mem_iUnion.mpr ⟨⟨j ⟨y, hy⟩, hjlt ⟨y, hy⟩⟩, hj ⟨y, hy⟩⟩)
    have hRcard : #R0 < Ordinal.cof β :=
      lt_of_le_of_lt (prior_card haleph ha hS i1) hcof
    obtain ⟨z, hzmem, hzabove⟩ := exists_enrich_above hlim hRcard
    have hzstage : z ∈ stage θ S i1 := by
      rw [stage.eq_def]
      exact hzmem
    refine ⟨z, mem_iUnion.mpr ⟨i1, hzstage⟩, ?_⟩
    intro y hy
    exact hzabove y (htR hy)
  have hcofT : θ < setCofinality T0 := by
    unfold setCofinality
    have hne : {κ : Cardinal.{u} | ∃ t : Set β.ToType, t ⊆ T0 ∧ #t = κ ∧
        ∀ x ∈ T0, ∃ y ∈ t, x ≤ y}.Nonempty :=
      ⟨#T0, T0, subset_rfl, rfl, fun x hx => ⟨x, hx, le_rfl⟩⟩
    refine (Order.lt_succ θ).trans_le (le_csInf hne ?_)
    intro κ hκ
    obtain ⟨t, ht, hcardt, hcofinal⟩ := hκ
    have hbig : θ < #t := by
      by_contra hle
      obtain ⟨z, hz, hab⟩ := habove t ht (le_of_not_gt hle)
      obtain ⟨y, hy, hzy⟩ := hcofinal z hz
      exact not_le_of_gt (hab y hy) hzy
    exact Order.succ_le_of_lt (hcardt ▸ hbig)
  refine ⟨T0, hSsub, hcard, ?_, hbound, hcofT⟩
  intro ι hι p hp n q
  let j : ι → (Order.succ θ).ord.ToType :=
    fun i => Classical.choose (mem_iUnion.mp (hp i))
  have hj : ∀ i, p i ∈ stage θ S (j i) :=
    fun i => Classical.choose_spec (mem_iUnion.mp (hp i))
  have hidx : #ι < Ordinal.cof (Order.succ θ).ord := by
    rw [hreg]
    exact hι.trans_lt (Order.lt_succ θ)
  have hsup : (⨆ i, (Ordinal.ToType.toOrd (j i)).1) < (Order.succ θ).ord :=
    Ordinal.iSup_lt_of_lt_cof hidx (fun i => (Ordinal.ToType.toOrd (j i)).2)
  have h1 : (⨆ i, (Ordinal.ToType.toOrd (j i)).1) + 1 < (Order.succ θ).ord :=
    (isSuccLimit_ord (hθ.trans (Order.le_succ θ))).succ_lt hsup
  let i1 : (Order.succ θ).ord.ToType :=
    Ordinal.ToType.mk ⟨(⨆ i, (Ordinal.ToType.toOrd (j i)).1) + 1, h1⟩
  have hjlt : ∀ i, j i < i1 := by
    intro i
    refine toType_lt_of_ordinal_lt h1 ?_
    exact lt_of_le_of_lt (Ordinal.le_iSup (fun k => (Ordinal.ToType.toOrd (j k)).1) i)
      (lt_add_of_pos_right _ zero_lt_one)
  let R0 : Set β.ToType :=
    S ∪ ⋃ k : {k : (Order.succ θ).ord.ToType // k < i1}, stage θ S k.1
  have hpR : ∀ i, p i ∈ R0 := by
    intro i
    exact Or.inr (mem_iUnion.mpr ⟨⟨j i, hjlt i⟩, hj i⟩)
  refine ⟨matched R0 q, ?_, matched_diagram R0 p hpR q⟩
  intro k
  have hmem : matched R0 q k ∈ stage θ S i1 := by
    rw [stage.eq_def]
    exact matched_mem R0 q k
  exact mem_iUnion.mpr ⟨i1, hmem⟩

end
end AEC
