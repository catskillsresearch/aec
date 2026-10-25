module

public import AEC.Section3.CutBalance
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Basic.Countable.Defs

@[expose] public section

namespace AEC
section

universe u v

open Cardinal Classical Finsupp HOrder Set

variable {δ : _root_.Ordinal.{u}}

lemma exists_nat_gt_rat (q : ℚ) : ∃ n : ℕ, q < n := by
  obtain ⟨n, hn⟩ := Archimedean.arch (q + 1) (zero_lt_one : (0 : ℚ) < 1)
  refine ⟨n, ?_⟩
  have hle : q + 1 ≤ n • (1 : ℚ) := hn
  have hcast : n • (1 : ℚ) = n := by simp
  rw [hcast] at hle
  exact lt_of_lt_of_le (lt_add_one q) hle

lemma exists_setCofinality_witness {α : Type v} [LinearOrder α] (s : Set α) (_hne : s.Nonempty) :
    ∃ t : Set α, t ⊆ s ∧ #t = setCofinality s ∧ ∀ x ∈ s, ∃ y ∈ t, x ≤ y := by
  let C : Set Cardinal.{v} := {κ | ∃ t : Set α, t ⊆ s ∧ #t = κ ∧ ∀ x ∈ s, ∃ y ∈ t, x ≤ y}
  have hC : C.Nonempty := ⟨#s, s, subset_rfl, rfl, fun x hx => ⟨x, hx, le_rfl⟩⟩
  obtain ⟨κ, hκ, hmin⟩ := (wellFounded_lt (α := Cardinal.{v})).has_min C hC
  obtain ⟨t, ht, rfl, hcof⟩ := hκ
  refine ⟨t, ht, ?_, hcof⟩
  apply le_antisymm
  · apply le_setCofinality
    intro u hu huco
    exact le_of_not_gt (hmin _ ⟨u, hu, rfl, huco⟩)
  · exact setCofinality_le ht hcof

lemma exists_setCoinitiality_witness {α : Type v} [LinearOrder α] (s : Set α) (hne : s.Nonempty) :
    ∃ t : Set α, t ⊆ s ∧ #t = setCoinitiality s ∧ ∀ x ∈ s, ∃ y ∈ t, y ≤ x := by
  let s' : Set αᵒᵈ := OrderDual.toDual '' s
  have hne' : s'.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨OrderDual.toDual x, mem_image_of_mem _ hx⟩
  obtain ⟨t, ht, hcard, hcof⟩ := exists_setCofinality_witness s' hne'
  refine ⟨OrderDual.ofDual '' t, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨a, ha, rfl⟩ := ht hy'
    exact ha
  · show #(OrderDual.ofDual '' t) = setCofinality s'
    rw [mk_image_eq OrderDual.ofDual.injective, hcard]
  · intro x hx
    obtain ⟨y, hy, hyx⟩ := hcof (OrderDual.toDual x) (mem_image_of_mem _ hx)
    refine ⟨OrderDual.ofDual y, mem_image_of_mem _ hy, ?_⟩
    rw [← OrderDual.toDual_ofDual y] at hyx
    exact OrderDual.toDual_le_toDual.mp hyx

lemma cof_ge_aleph0 {α : Type v} [LinearOrder α] {s : Set α} (hne : s.Nonempty)
    (hno : ∀ x ∈ s, ∃ y ∈ s, x < y) : ℵ₀ ≤ setCofinality s := by
  apply le_setCofinality
  intro t ht hcof
  have hinf : t.Infinite := by
    intro hfin
    have htne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      obtain ⟨y, hy, _⟩ := hcof x hx
      exact ⟨y, hy⟩
    let tf := hfin.toFinset
    have htf : tf.Nonempty := by
      obtain ⟨x, hx⟩ := htne
      exact ⟨x, hfin.mem_toFinset.mpr hx⟩
    let m := tf.max' htf
    have hm : m ∈ t := hfin.mem_toFinset.mp (tf.max'_mem htf)
    have htop : ∀ y ∈ t, y ≤ m := fun y hy => tf.le_max' y (hfin.mem_toFinset.mpr hy)
    obtain ⟨b, hb, hmb⟩ := hno m (ht hm)
    obtain ⟨y, hy, hby⟩ := hcof b hb
    exact (not_lt_of_ge (hby.trans (htop y hy))) hmb
  exact Cardinal.infinite_iff.mp (Set.infinite_coe_iff.mpr hinf)

lemma coi_ge_aleph0 {α : Type v} [LinearOrder α] {s : Set α} (hne : s.Nonempty)
    (hno : ∀ x ∈ s, ∃ y ∈ s, y < x) : ℵ₀ ≤ setCoinitiality s := by
  have hno' : ∀ x ∈ OrderDual.toDual '' s, ∃ y ∈ OrderDual.toDual '' s, x < y := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, hba⟩ := hno a ha
    refine ⟨OrderDual.toDual b, mem_image_of_mem _ hb, ?_⟩
    exact OrderDual.toDual_lt_toDual.mpr hba
  simpa [setCoinitiality] using
    cof_ge_aleph0 (s := OrderDual.toDual '' s)
      (by obtain ⟨x, hx⟩ := hne; exact ⟨OrderDual.toDual x, mem_image_of_mem _ hx⟩) hno'

lemma cofinality_aleph0_of_nat {α : Type v} [LinearOrder α] {s : Set α} (hne : s.Nonempty)
    (hno : ∀ x ∈ s, ∃ y ∈ s, x < y) (f : ℕ → α) (hf : ∀ n, f n ∈ s)
    (hcof : ∀ x ∈ s, ∃ n, x ≤ f n) : setCofinality s = ℵ₀ := by
  apply le_antisymm
  · have hsub : range f ⊆ s := by
      intro y hy
      obtain ⟨n, rfl⟩ := hy
      exact hf n
    have hpush : ∀ x ∈ s, ∃ y ∈ range f, x ≤ y := by
      intro x hx
      obtain ⟨n, hn⟩ := hcof x hx
      exact ⟨f n, mem_range_self n, hn⟩
    have hcount : Countable (range f) := countable_range f
    exact (setCofinality_le hsub hpush).trans Cardinal.mk_le_aleph0
  · exact cof_ge_aleph0 hne hno

lemma coinitiality_aleph0_of_nat {α : Type v} [LinearOrder α] {s : Set α} (hne : s.Nonempty)
    (hno : ∀ x ∈ s, ∃ y ∈ s, y < x) (f : ℕ → α) (hf : ∀ n, f n ∈ s)
    (hco : ∀ x ∈ s, ∃ n, f n ≤ x) : setCoinitiality s = ℵ₀ := by
  apply le_antisymm
  · have hsub : range f ⊆ s := by
      intro y hy
      obtain ⟨n, rfl⟩ := hy
      exact hf n
    have hpush : ∀ x ∈ s, ∃ y ∈ range f, y ≤ x := by
      intro x hx
      obtain ⟨n, hn⟩ := hco x hx
      exact ⟨f n, mem_range_self n, hn⟩
    have hcount : Countable (range f) := countable_range f
    exact (setCoinitiality_le hsub hpush).trans Cardinal.mk_le_aleph0
  · exact coi_ge_aleph0 hne hno

lemma exists_nat_cofinal_rat {s : Set ℚ} (hne : s.Nonempty) (hup : ∀ q ∈ s, ∃ r ∈ s, q < r) :
    ∃ f : ℕ → ℚ, (∀ n, f n ∈ s) ∧ StrictMono f ∧ ∀ q ∈ s, ∃ n, q < f n := by
  have : Nonempty s := ⟨hne.choose, hne.choose_spec⟩
  obtain ⟨e, he⟩ := exists_surjective_nat s
  have step : ∀ (prev : ℚ) (_hp : prev ∈ s) (n : ℕ), ∃ r, r ∈ s ∧ max prev (e n).1 < r := by
    intro prev hp n
    have hmem : max prev (e n).1 ∈ s := by
      rcases le_total prev (e n).1 with hle | hle
      · rw [max_eq_right hle]
        exact (e n).2
      · rw [max_eq_left hle]
        exact hp
    obtain ⟨r, hr, hlt⟩ := hup _ hmem
    exact ⟨r, hr, hlt⟩
  let fAux : ℕ → s :=
    Nat.rec (e 0) (fun n prev =>
      ⟨Classical.choose (step prev.1 prev.2 n),
        (Classical.choose_spec (step prev.1 prev.2 n)).1⟩)
  let f : ℕ → ℚ := fun n => (fAux n).1
  have hf : ∀ n, f n ∈ s := fun n => (fAux n).2
  have hsucc : ∀ n, f n < f (n + 1) := by
    intro n
    have spec := Classical.choose_spec (step (fAux n).1 (fAux n).2 n)
    exact (le_max_left (fAux n).1 (e n).1).trans_lt spec.2
  have hstrict : StrictMono f := by
    intro a b hab
    induction b with
    | zero => exact (Nat.not_lt_zero a hab).elim
    | succ b ih =>
      have hle : a ≤ b := Nat.le_of_lt_succ hab
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact (ih hlt).trans (hsucc b)
      · exact heq ▸ hsucc a
  refine ⟨f, hf, hstrict, ?_⟩
  intro q hq
  obtain ⟨n, hn⟩ := he ⟨q, hq⟩
  have spec := Classical.choose_spec (step (fAux n).1 (fAux n).2 n)
  have hlt : (e n).1 < f (n + 1) := (le_max_right (fAux n).1 (e n).1).trans_lt spec.2
  rw [show (e n).1 = q from congrArg Subtype.val hn] at hlt
  exact ⟨n + 1, hlt⟩

lemma exists_nat_coinitial_rat {s : Set ℚ} (hne : s.Nonempty) (hdown : ∀ q ∈ s, ∃ r ∈ s, r < q) :
    ∃ f : ℕ → ℚ, (∀ n, f n ∈ s) ∧ StrictAnti f ∧ ∀ q ∈ s, ∃ n, f n < q := by
  have : Nonempty s := ⟨hne.choose, hne.choose_spec⟩
  obtain ⟨e, he⟩ := exists_surjective_nat s
  have step : ∀ (prev : ℚ) (_hp : prev ∈ s) (n : ℕ), ∃ r, r ∈ s ∧ r < min prev (e n).1 := by
    intro prev hp n
    have hmem : min prev (e n).1 ∈ s := by
      rcases le_total prev (e n).1 with hle | hle
      · rw [min_eq_left hle]
        exact hp
      · rw [min_eq_right hle]
        exact (e n).2
    obtain ⟨r, hr, hlt⟩ := hdown _ hmem
    exact ⟨r, hr, hlt⟩
  let fAux : ℕ → s :=
    Nat.rec (e 0) (fun n prev =>
      ⟨Classical.choose (step prev.1 prev.2 n),
        (Classical.choose_spec (step prev.1 prev.2 n)).1⟩)
  let f : ℕ → ℚ := fun n => (fAux n).1
  have hf : ∀ n, f n ∈ s := fun n => (fAux n).2
  have hsucc : ∀ n, f (n + 1) < f n := by
    intro n
    have spec := Classical.choose_spec (step (fAux n).1 (fAux n).2 n)
    exact spec.2.trans_le (min_le_left (fAux n).1 (e n).1)
  have hstrict : StrictAnti f := by
    intro a b hab
    induction b with
    | zero => exact (Nat.not_lt_zero a hab).elim
    | succ b ih =>
      have hle : a ≤ b := Nat.le_of_lt_succ hab
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact (hsucc b).trans (ih hlt)
      · exact heq ▸ hsucc a
  refine ⟨f, hf, hstrict, ?_⟩
  intro q hq
  obtain ⟨n, hn⟩ := he ⟨q, hq⟩
  have spec := Classical.choose_spec (step (fAux n).1 (fAux n).2 n)
  have hlt : f (n + 1) < (e n).1 := spec.2.trans_le (min_le_right (fAux n).1 (e n).1)
  rw [show (e n).1 = q from congrArg Subtype.val hn] at hlt
  exact ⟨n + 1, hlt⟩

lemma addRight_le {c x y : HOrder δ} (h : x ≤ y) : x + c ≤ y + c := by
  rcases lt_or_eq_of_le h with hlt | heq
  · exact (addRight_lt hlt).le
  · exact le_of_eq (congrArg (fun z => z + c) heq)

lemma lt_of_zero_above {a b : HOrder δ} (hb : 0 < b)
    (ha : ∀ j, rankOf b hb.ne' ≤ j → coeff a j = 0) : a < b := by
  rw [Colex.lt_iff]
  refine ⟨rankOf b hb.ne', ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, ha j hj.le, coeff_eq_zero_of_rank_lt b hb.ne' hj]
  · rw [← coeff, ← coeff, ha _ le_rfl]
    exact coeff_rank_pos hb

lemma rank_le_pos {a b : HOrder δ} (ha : 0 < a) (hab : a ≤ b) :
    rankOf a ha.ne' ≤ rankOf b (lt_of_lt_of_le ha hab).ne' := by
  by_contra hlt
  have hba : b < a :=
    lt_of_zero_above ha (fun j hj =>
      coeff_eq_zero_of_rank_lt b (lt_of_lt_of_le ha hab).ne' ((not_le.mp hlt).trans_le hj))
  exact not_le_of_gt hba hab

lemma sub_le_sub_right {r a b : HOrder δ} (h : a ≤ b) : r - b ≤ r - a := by
  have hneg : -b ≤ -a := (neg_le_neg_iff_H b a).mpr h
  simpa [add_comm, sub_eq_add_neg] using addRight_le (c := r) hneg

lemma basisZ_pos (i : OrdIndex δ) : (0 : Gamma δ) < basisZ i := by
  rw [Colex.lt_iff]
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    rw [← coeffZ, ← coeffZ, coeffZ_basis_of_ne hj.ne']
    rfl
  · rw [← coeffZ, ← coeffZ, coeffZ_basis_self]
    exact zero_lt_one

lemma gammaRank_basisZ (i : OrdIndex δ) :
    gammaRank (basisZ i) (basisZ_pos i).ne' = i := by
  apply le_antisymm
  · apply Finset.max'_le
    intro j hj
    have hne : coeffZ (basisZ i) j ≠ 0 := by simpa [coeffZ] using mem_support_iff.mp hj
    have hj' : j = i := by
      by_contra hne'
      exact hne (coeffZ_basis_of_ne hne')
    exact le_of_eq hj'
  · apply Finset.le_max'
    exact mem_support_iff.mpr (by
      change coeffZ (basisZ i) i ≠ 0
      rw [coeffZ_basis_self]
      exact one_ne_zero)

lemma gamma_subsingleton (hδ : δ = 0) : Subsingleton (Gamma δ) := by
  subst hδ
  refine ⟨fun x y => ?_⟩
  apply ofColex.injective
  ext i
  exact (not_lt_of_ge (bot_le (a := i.1)) i.2).elim

noncomputable def leastIndex (hδ : (0 : _root_.Ordinal.{u}) < δ) : OrdIndex δ := ⟨0, hδ⟩

noncomputable def leastPos (hδ : (0 : _root_.Ordinal.{u}) < δ) : Gamma δ :=
  basisZ (leastIndex hδ)

lemma leastIndex_le (hδ : (0 : _root_.Ordinal.{u}) < δ) (j : OrdIndex δ) : leastIndex hδ ≤ j := by
  rw [← Subtype.coe_le_coe]
  exact bot_le

lemma leastPos_least (hδ : (0 : _root_.Ordinal.{u}) < δ) {x : Gamma δ} (hx : 0 < x) :
    leastPos hδ ≤ x := by
  rcases lt_trichotomy (gammaRank x hx.ne') (leastIndex hδ) with hlt | heq | hgt
  · exact ((leastIndex_le hδ _).not_gt hlt).elim
  · apply le_of_not_gt
    intro hxl
    rw [Colex.lt_iff] at hxl
    obtain ⟨i, hi, hci⟩ := hxl
    have hi0 : leastIndex hδ ≤ i := leastIndex_le hδ i
    rcases eq_or_lt_of_le hi0 with heqi | hli
    · have hcoe : coeffZ x i < coeffZ (leastPos hδ) i := by simpa [coeffZ] using hci
      rw [leastPos, heqi, coeffZ_basis_self] at hcoe
      have hpos := coeffZ_gammaRank_pos hx
      rw [heq] at hpos
      have h1 : (1 : ℤ) ≤ coeffZ x (leastIndex hδ) := by
        have hstep : (0 : ℤ) + 1 ≤ coeffZ x (leastIndex hδ) := Int.add_one_le_iff.mpr hpos
        simpa [zero_add] using hstep
      have hcoe' : coeffZ x (leastIndex hδ) < 1 := by simpa [← heqi] using hcoe
      exact not_lt_of_ge h1 hcoe'
    · have hx0 : coeffZ x i = 0 :=
        coeffZ_eq_zero_of_gammaRank_lt x hx.ne' (by rwa [heq])
      have hb0 : coeffZ (leastPos hδ) i = 0 := coeffZ_basis_of_ne hli.ne'
      have hci' : coeffZ x i < coeffZ (leastPos hδ) i := by simpa [coeffZ] using hci
      rw [hx0, hb0] at hci'
      exact lt_irrefl _ hci'
  · have hr : gammaRank (leastPos hδ) (basisZ_pos (leastIndex hδ)).ne' = leastIndex hδ :=
      gammaRank_basisZ (leastIndex hδ)
    have hcmp : gammaRank (leastPos hδ) (basisZ_pos (leastIndex hδ)).ne' < gammaRank x hx.ne' := by
      simpa [hr] using hgt
    exact (gamma_lt_of_rank_lt (basisZ_pos (leastIndex hδ)) hx hcmp).le

lemma gamma_sub_lt_self {g e : Gamma δ} (he : 0 < e) : g - e < g := by
  have hneg : -e < 0 := by simpa using gamma_neg_lt_neg he
  have hlt : -e + g < 0 + g := gamma_addRight_lt hneg
  rw [add_comm (-e) g, add_comm (0 : Gamma δ) g, add_zero, ← sub_eq_add_neg] at hlt
  exact hlt

lemma pred_lt (hδ : (0 : _root_.Ordinal.{u}) < δ) (g : Gamma δ) : g - leastPos hδ < g :=
  gamma_sub_lt_self (basisZ_pos (leastIndex hδ))

lemma no_gamma_between (hδ : (0 : _root_.Ordinal.{u}) < δ) (g x : Gamma δ) :
    g - leastPos hδ < x → x < g → False := by
  intro hlo hhi
  have hxg : x - g < 0 := by
    have hlt : x + -g < g + -g := gamma_addRight_lt hhi
    simpa [add_neg_cancel, sub_eq_add_neg] using hlt
  have hsum : leastPos hδ + (x - g) < leastPos hδ := by
    simpa [add_zero] using gamma_add_lt_add_left (s := leastPos hδ) hxg
  have hre : x - (g - leastPos hδ) = leastPos hδ + (x - g) := by
    apply ofColex.injective
    ext i
    simp [sub_eq_add_neg, add_apply, neg_neg, add_left_comm]
  have hsmall : x - (g - leastPos hδ) < leastPos hδ := by simpa [hre] using hsum
  have hpos : 0 < x - (g - leastPos hδ) := gamma_sub_pos_of_lt hlo
  exact (leastPos_least hδ hpos).not_gt hsmall

lemma coeff_rank_ne_zero {a : HOrder δ} (ha : 0 < a) : coeff a (rankOf a ha.ne') ≠ 0 :=
  (coeff_rank_pos ha).ne'

lemma rank_basisQ (g : Gamma δ) : rankOf (basisQ g) (basisQ_pos g).ne' = g :=
  rank_eq_of_witness (basisQ_pos g) g (fun j hj => coeff_basis_ne hj.ne') (by
    rw [coeff_basis_self]
    exact zero_lt_one)

lemma exists_basis_smul_gt {a : HOrder δ} (ha : 0 < a) :
    ∃ n : ℕ, a < smulQ ((n : ℚ) + 1) (basisQ (rankOf a ha.ne')) := by
  obtain ⟨n, hn⟩ := exists_nat_gt_rat (coeff a (rankOf a ha.ne'))
  refine ⟨n, ?_⟩
  rw [Colex.lt_iff]
  refine ⟨rankOf a ha.ne', ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, coeff_eq_zero_of_rank_lt a ha.ne' hj, coeff_smulQ, coeff_basis_ne hj.ne',
      mul_zero]
  · rw [← coeff, ← coeff, coeff_smulQ, coeff_basis_self, mul_one]
    exact hn.trans (by exact_mod_cast Nat.lt_succ_self n)

def SupportedOn (T : Set (Gamma δ)) (a : HOrder δ) : Prop :=
  ∀ g, coeff a g ≠ 0 → g ∉ T

lemma supportedOn_zero (T : Set (Gamma δ)) : SupportedOn T (0 : HOrder δ) := by
  intro g hg
  exact (hg (by simp [coeff])).elim

lemma supportedOn_basis {T : Set (Gamma δ)} {g : Gamma δ} (hg : g ∉ T) :
    SupportedOn T (basisQ g) := by
  intro i hi hmem
  have hi' : i = g := by
    by_contra hne
    exact hi (coeff_basis_ne hne)
  exact hg (hi' ▸ hmem)

lemma supportedOn_smul {T : Set (Gamma δ)} {r : ℚ} {a : HOrder δ} (ha : SupportedOn T a) :
    SupportedOn T (smulQ r a) := by
  intro g hg hmem
  have hne : coeff a g ≠ 0 := by
    intro hz
    exact hg (by rw [coeff_smulQ, hz, mul_zero])
  exact ha g hne hmem

lemma supported_cofinality (T : Set (Gamma δ)) (hSne : {g | g ∉ T}.Nonempty)
    (hnoMax : ∀ s, s ∉ T → ∃ t, t ∉ T ∧ s < t) :
    setCofinality {a | SupportedOn T a} = setCofinality {g | g ∉ T} := by
  let S : Set (Gamma δ) := {g | g ∉ T}
  let HS : Set (HOrder δ) := {a | SupportedOn T a}
  obtain ⟨t, ht, hcard, hcof⟩ := exists_setCofinality_witness S hSne
  let bset : Set (HOrder δ) := basisQ '' t
  have hbsub : bset ⊆ HS := by
    intro a ha
    obtain ⟨g, hg, rfl⟩ := ha
    exact supportedOn_basis (ht hg)
  have hbcof : ∀ a ∈ HS, ∃ y ∈ bset, a ≤ y := by
    intro a ha
    by_cases hapos : a ≤ 0
    · obtain ⟨g, hg⟩ := hSne
      obtain ⟨y, hy, _⟩ := hcof g hg
      exact ⟨basisQ y, mem_image_of_mem _ hy, hapos.trans (basisQ_pos y).le⟩
    · have hpos : 0 < a := lt_of_not_ge hapos
      have hrankS : rankOf a hpos.ne' ∉ T := by
        intro hT
        exact ha (rankOf a hpos.ne') (coeff_rank_ne_zero hpos) hT
      obtain ⟨s, hsS, hs⟩ := hnoMax _ hrankS
      obtain ⟨y, hy, hsy⟩ := hcof s hsS
      have hry : rankOf a hpos.ne' < y := hs.trans_le hsy
      exact ⟨basisQ y, mem_image_of_mem _ hy,
        (lt_of_zero_above (basisQ_pos y) (fun j hj => by
          have hj' : y ≤ j := by simpa [rank_basisQ y] using hj
          exact coeff_eq_zero_of_rank_lt a hpos.ne' (hry.trans_le hj'))).le⟩
  have hle : setCofinality HS ≤ setCofinality S := by
    have hcardb : #bset = #t := mk_image_eq basisQ_injective
    exact (setCofinality_le hbsub hbcof).trans_eq (hcardb.trans hcard)
  have hge : setCofinality S ≤ setCofinality HS := by
    apply le_setCofinality
    intro u hu huco
    let pos : Set (HOrder δ) := {a | a ∈ u ∧ 0 < a}
    let f : {a // a ∈ pos} → Gamma δ := fun a => rankOf a.1 a.2.2.ne'
    let ranks : Set (Gamma δ) := range f
    have hrsub : ranks ⊆ S := by
      intro g hg
      obtain ⟨a, rfl⟩ := hg
      intro hT
      exact (hu a.2.1) (rankOf a.1 a.2.2.ne') (coeff_rank_ne_zero a.2.2) hT
    have hrcof : ∀ s ∈ S, ∃ g ∈ ranks, s ≤ g := by
      intro s hs
      obtain ⟨a, ha, hsa⟩ := huco (basisQ s) (supportedOn_basis hs)
      have hpos : 0 < a := (basisQ_pos s).trans_le hsa
      have haPos : a ∈ pos := ⟨ha, hpos⟩
      refine ⟨f ⟨a, haPos⟩, mem_range_self _, ?_⟩
      by_contra hlt
      exact not_le_of_gt (lt_of_zero_above (basisQ_pos s) (fun j hj => by
        have hj' : s ≤ j := by simpa [rank_basisQ s] using hj
        exact coeff_eq_zero_of_rank_lt a hpos.ne' ((not_le.mp hlt).trans_le hj'))) hsa
    exact (setCofinality_le hrsub hrcof).trans
      (mk_range_le.trans (Cardinal.mk_le_mk_of_subset fun a ha => ha.1))
  exact le_antisymm hle hge

lemma hAgrees_refl (g : Gamma δ) (x : HOrder δ) : hAgrees g x x := fun _ _ => rfl

lemma bump_mem_hFiber (head : HOrder δ) (g : Gamma δ) (q : ℚ) :
    bump head g q ∈ hFiber g head q := by
  refine ⟨?_, coeff_bump_self head g q⟩
  intro j hj
  rw [coeff_bump_ne head g j q hj.ne']

lemma lt_bump {head x : HOrder δ} {g : Gamma δ} {q : ℚ} (hx : hAgrees g head x)
    (hq : coeff x g < q) : x < bump head g q := by
  rw [Colex.lt_iff]
  refine ⟨g, ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, hx j hj, coeff_bump_ne head g j q hj.ne']
  · rw [← coeff, ← coeff, coeff_bump_self]
    exact hq

lemma bump_lt_of_lt {head x : HOrder δ} {g : Gamma δ} {q : ℚ} (hx : hAgrees g head x)
    (hq : q < coeff x g) : bump head g q < x := by
  rw [Colex.lt_iff]
  refine ⟨g, ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, coeff_bump_ne head g j q hj.ne', hx j hj]
  · rw [← coeff, ← coeff, coeff_bump_self]
    exact hq

lemma hFiber_lt_hFiber {g : Gamma δ} {head : HOrder δ} {p q : ℚ} (hpq : p < q)
    {x y : HOrder δ} (hx : x ∈ hFiber g head p) (hy : y ∈ hFiber g head q) : x < y := by
  rw [Colex.lt_iff]
  refine ⟨g, ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, hx.1 j hj, hy.1 j hj]
  · rw [← coeff, ← coeff, hx.2, hy.2]
    exact hpq

lemma hFiber_rank_lt {g : Gamma δ} {head x y : HOrder δ} {q : ℚ}
    (hx : x ∈ hFiber g head q) (hy : y ∈ hFiber g head q) (hxy : x < y) :
    rankOf (y - x) (HOrder.sub_pos_of_lt hxy).ne' < g := by
  by_contra hge
  have hle : g ≤ rankOf (y - x) (HOrder.sub_pos_of_lt hxy).ne' := le_of_not_gt hge
  have hzero : coeff (y - x) (rankOf (y - x) (HOrder.sub_pos_of_lt hxy).ne') = 0 := by
    rw [coeff_sub]
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [hx.1 _ hlt, hy.1 _ hlt, sub_self]
    · rw [← heq, hx.2, hy.2, sub_self]
  exact (coeff_rank_pos (HOrder.sub_pos_of_lt hxy)).ne' hzero

lemma hFiber_side (c : Cut (HOrder δ)) {g : Gamma δ} (hmin : ∀ h ∈ hCrossing c, g ≤ h)
    (head : HOrder δ) (q : ℚ) :
    hFiber g head q ⊆ c.lower ∨ hFiber g head q ⊆ c.upper := by
  by_cases hL : ∃ x ∈ hFiber g head q, x ∈ c.lower
  · by_cases hU : ∃ y ∈ hFiber g head q, y ∈ c.upper
    · obtain ⟨x, hx, hxl⟩ := hL
      obtain ⟨y, hy, hyu⟩ := hU
      have hxy : x < y := c.ordered x hxl y hyu
      exact False.elim ((hmin _ ⟨x, hxl, y, hyu, rfl⟩).not_gt (hFiber_rank_lt hx hy hxy))
    · refine Or.inl ?_
      intro z hz
      have hmem : z ∈ c.lower ∪ c.upper := by rw [c.union_eq]; exact mem_univ z
      rcases (mem_union z c.lower c.upper).1 hmem with h | h
      · exact h
      · exact False.elim (hU ⟨z, hz, h⟩)
  · refine Or.inr ?_
    intro z hz
    have hmem : z ∈ c.lower ∪ c.upper := by rw [c.union_eq]; exact mem_univ z
    rcases (mem_union z c.lower c.upper).1 hmem with h | h
    · exact False.elim (hL ⟨z, hz, h⟩)
    · exact h

lemma agrees_of_crossing (c : Cut (HOrder δ)) {l r : HOrder δ} (hl : l ∈ c.lower)
    (hr : r ∈ c.upper) {g : Gamma δ}
    (hrank : rankOf (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne' = g) :
    hAgrees g l r := by
  intro j hj
  have hzero := coeff_eq_zero_of_rank_lt (r - l)
    (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne' (by simpa [hrank] using hj)
  rw [coeff_sub] at hzero
  exact sub_eq_zero.mp hzero

lemma coeff_lt_of_crossing (c : Cut (HOrder δ)) {l r : HOrder δ} (hl : l ∈ c.lower)
    (hr : r ∈ c.upper) {g : Gamma δ}
    (hrank : rankOf (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne' = g) :
    coeff l g < coeff r g := by
  have hpos := coeff_rank_pos (HOrder.sub_pos_of_lt (c.ordered l hl r hr))
  rw [hrank, coeff_sub] at hpos
  exact sub_pos.mp hpos

lemma exists_pred_smul_gt (hδ : (0 : _root_.Ordinal.{u}) < δ) {g : Gamma δ} {a : HOrder δ}
    (ha : SupportedBelow g a) :
    ∃ n : ℕ, a < smulQ ((n : ℚ) + 1) (basisQ (g - leastPos hδ)) := by
  set pred : Gamma δ := g - leastPos hδ
  have hpred : pred < g := pred_lt hδ g
  have hone : smulQ 1 (basisQ pred) = basisQ pred := by
    apply ofColex.injective
    ext i
    simp [smulQ, coeff, mapRange_apply, ofColex_toColex, one_mul]
  by_cases hnonpos : a ≤ 0
  · refine ⟨0, ?_⟩
    simp only [Nat.cast_zero, zero_add, hone]
    exact hnonpos.trans_lt (basisQ_pos pred)
  · have hpos : 0 < a := lt_of_not_ge hnonpos
    have hrank : rankOf a hpos.ne' < g := by
      by_contra hge
      exact (coeff_rank_ne_zero hpos) (ha (rankOf a hpos.ne') (le_of_not_gt hge))
    have hrle : rankOf a hpos.ne' ≤ pred := by
      by_contra hgt
      exact no_gamma_between hδ g (rankOf a hpos.ne') (lt_of_not_ge hgt) hrank
    rcases lt_or_eq_of_le hrle with hlt | heq
    · refine ⟨0, ?_⟩
      simp only [Nat.cast_zero, zero_add, hone]
      exact lt_of_zero_above (basisQ_pos pred) (fun j hj => by
        have hj' : pred ≤ j := by simpa [rank_basisQ pred] using hj
        exact coeff_eq_zero_of_rank_lt a hpos.ne' (hlt.trans_le hj'))
    · obtain ⟨n, hn⟩ := exists_nat_gt_rat (coeff a pred)
      refine ⟨n, ?_⟩
      rw [Colex.lt_iff]
      refine ⟨pred, ?_, ?_⟩
      · intro j hj
        rw [← coeff, ← coeff, coeff_eq_zero_of_rank_lt a hpos.ne' (by simpa [heq] using hj),
          coeff_smulQ, coeff_basis_ne hj.ne', mul_zero]
      · change coeff a pred < coeff (smulQ ((n : ℚ) + 1) (basisQ pred)) pred
        rw [coeff_smulQ, coeff_basis_self, mul_one]
        exact hn.trans (by exact_mod_cast Nat.lt_succ_self n)

lemma fiber_sub_supported {g : Gamma δ} {head x : HOrder δ} {q : ℚ}
    (hx : x ∈ hFiber g head q) : SupportedBelow g (x - bump head g q) := by
  intro j hj
  rw [coeff_sub]
  rcases eq_or_lt_of_le hj with heq | hlt
  · rw [← heq, hx.2, coeff_bump_self, sub_self]
  · rw [hx.1 j hlt, coeff_bump_ne head g j q hlt.ne', sub_self]

lemma fiber_subsingleton_delta_zero (hδ : δ = 0) {g : Gamma δ} {head : HOrder δ} {q : ℚ}
    {x y : HOrder δ} (hx : x ∈ hFiber g head q) (hy : y ∈ hFiber g head q) : x = y := by
  have _ : Subsingleton (Gamma δ) := gamma_subsingleton hδ
  apply ofColex.injective
  ext i
  have hi : i = g := Subsingleton.elim i g
  rw [hi]
  change coeff x g = coeff y g
  rw [hx.2, hy.2]

lemma below_head_of_lower (c : Cut (HOrder δ)) {g : Gamma δ}
    (hmin : ∀ h ∈ hCrossing c, g ≤ h) {l r : HOrder δ} (hl : l ∈ c.lower)
    (hr : r ∈ c.upper)
    (hrank : rankOf (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne' = g)
    {z : HOrder δ} (hz : z ∈ c.lower) (hsame : ¬ hAgrees g l z) : z < l := by
  rcases lt_trichotomy z l with hlt | heq | hgt
  · exact hlt
  · exact False.elim (hsame (fun j hj => by rw [heq]))
  · have hdiff : 0 < z - l := HOrder.sub_pos_of_lt hgt
    have hg : g < rankOf (z - l) hdiff.ne' := by
      by_contra hle
      apply hsame
      intro j hj
      have hzero := coeff_eq_zero_of_rank_lt (z - l) hdiff.ne'
        ((le_of_not_gt hle).trans_lt hj)
      rw [coeff_sub] at hzero
      exact sub_eq_zero.mp hzero
    have hpos : 0 < r - l := HOrder.sub_pos_of_lt (c.ordered l hl r hr)
    have hsmall : r - l < z - l :=
      lt_of_zero_above hdiff (fun j hj =>
        coeff_eq_zero_of_rank_lt (r - l) hpos.ne' (by simpa [hrank] using hg.trans_le hj))
    have hadd := addRight_lt (c := l) hsmall
    have hrlt : r < z := by simpa [sub_add_cancel] using hadd
    exact False.elim (Set.disjoint_left.mp c.disjoint hz (c.upper_up hr hrlt.le))

lemma above_head_of_upper (c : Cut (HOrder δ)) {g : Gamma δ} {l : HOrder δ}
    (hl : l ∈ c.lower) {z : HOrder δ} (hz : z ∈ c.upper) (hsame : ¬ hAgrees g l z) : l < z := by
  rcases lt_trichotomy l z with hlt | heq | hgt
  · exact hlt
  · exact False.elim (hsame (fun j hj => by rw [heq]))
  · exact False.elim (Set.disjoint_left.mp c.disjoint (c.lower_down hl hgt.le) hz)

lemma lower_le_bump_seq (c : Cut (HOrder δ)) {g : Gamma δ}
    (hmin : ∀ h ∈ hCrossing c, g ≤ h) {l r : HOrder δ} (hl : l ∈ c.lower)
    (hr : r ∈ c.upper)
    (hrank : rankOf (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne' = g)
    (f : ℕ → ℚ) (hcof : ∀ q, hFiber g l q ⊆ c.lower → ∃ n, q < f n) :
    ∀ z ∈ c.lower, ∃ n, z ≤ bump l g (f n) := by
  intro z hz
  by_cases hsame : hAgrees g l z
  · have hfib : hFiber g l (coeff z g) ⊆ c.lower := by
      rcases hFiber_side c hmin l (coeff z g) with hL | hU
      · exact hL
      · exact False.elim (Set.disjoint_left.mp c.disjoint hz (hU ⟨hsame, rfl⟩))
    obtain ⟨n, hn⟩ := hcof _ hfib
    exact ⟨n, (lt_bump hsame hn).le⟩
  · have hbelow := below_head_of_lower c hmin hl hr hrank hz hsame
    have hfib : hFiber g l (coeff l g) ⊆ c.lower := by
      rcases hFiber_side c hmin l (coeff l g) with hL | hU
      · exact hL
      · exact False.elim (Set.disjoint_left.mp c.disjoint hl (hU ⟨hAgrees_refl g l, rfl⟩))
    obtain ⟨n, hn⟩ := hcof _ hfib
    exact ⟨n, (hbelow.trans (lt_bump (hAgrees_refl g l) hn)).le⟩

lemma bump_lt_of_higher (c : Cut (HOrder δ)) {g : Gamma δ} {l z : HOrder δ}
    (hlz : l < z) (hsame : ¬ hAgrees g l z) (q : ℚ) : bump l g q < z := by
  have hdiff : 0 < z - l := HOrder.sub_pos_of_lt hlz
  have hg : g < rankOf (z - l) hdiff.ne' := by
    by_contra hle
    apply hsame
    intro j hj
    have hzero := coeff_eq_zero_of_rank_lt (z - l) hdiff.ne' ((le_of_not_gt hle).trans_lt hj)
    rw [coeff_sub] at hzero
    exact sub_eq_zero.mp hzero
  have hsmall : bump l g q - l < z - l :=
    lt_of_zero_above hdiff (fun j hj => by
      rw [coeff_sub, coeff_bump_ne l g j q (hg.trans_le hj).ne', sub_self])
  simpa [sub_add_cancel] using addRight_lt (c := l) hsmall

lemma upper_ge_bump_seq (c : Cut (HOrder δ)) {g : Gamma δ} {l : HOrder δ}
    (hl : l ∈ c.lower) (f : ℕ → ℚ)
    (hco : ∀ q, ¬ hFiber g l q ⊆ c.lower → ∃ n, f n < q) :
    ∀ z ∈ c.upper, ∃ n, bump l g (f n) ≤ z := by
  intro z hz
  by_cases hsame : hAgrees g l z
  · have hup : ¬ hFiber g l (coeff z g) ⊆ c.lower := by
      intro hL
      exact Set.disjoint_left.mp c.disjoint (hL ⟨hsame, rfl⟩) hz
    obtain ⟨n, hn⟩ := hco _ hup
    exact ⟨n, (bump_lt_of_lt hsame hn).le⟩
  · exact ⟨0, (bump_lt_of_higher c (above_head_of_upper c hl hz hsame) hsame (f 0)).le⟩

/-- The least-crossing-rank case of Lemma 3.3 for `H(δ)`. -/
lemma horder_least_balanced (c : Cut (HOrder δ)) (hc : Cut.IsInteriorNonprincipal c)
    {g : Gamma δ} (hg : g ∈ hCrossing c) (hmin : ∀ h ∈ hCrossing c, g ≤ h) :
    Cut.IsBalanced c := by
  obtain ⟨l, hl, r, hr, hrank⟩ := hg
  have hagree := agrees_of_crossing c hl hr hrank
  have hcoeff := coeff_lt_of_crossing c hl hr hrank
  let lowerQ : Set ℚ := {q | hFiber g l q ⊆ c.lower}
  let upperQ : Set ℚ := {q | q ∉ lowerQ}
  have hdown : ∀ {p q : ℚ}, q ∈ lowerQ → p ≤ q → p ∈ lowerQ := by
    intro p q hq hpq
    rcases lt_or_eq_of_le hpq with hlt | heq
    · intro x hx
      exact c.lower_down (hq (bump_mem_hFiber l g q))
        (hFiber_lt_hFiber hlt hx (bump_mem_hFiber l g q)).le
    · rw [heq]; exact hq
  have hqL : coeff l g ∈ lowerQ := by
    rcases hFiber_side c hmin l (coeff l g) with hL | hU
    · exact hL
    · exact False.elim (Set.disjoint_left.mp c.disjoint hl (hU ⟨hAgrees_refl g l, rfl⟩))
  have hqR : coeff r g ∈ upperQ := by
    intro hfib
    exact Set.disjoint_left.mp c.disjoint (hfib ⟨hagree, rfl⟩) hr
  have hlow_ne : lowerQ.Nonempty := ⟨coeff l g, hqL⟩
  have hup_ne : upperQ.Nonempty := ⟨coeff r g, hqR⟩
  by_cases hgreat : ∃ q, IsGreatest lowerQ q
  · obtain ⟨q, hqmem, hqmax⟩ := hgreat
    have hfibcof : ∀ z ∈ c.lower, ∃ y ∈ hFiber g l q, z ≤ y := by
      intro z hz
      by_cases hsame : hAgrees g l z
      · have hle : coeff z g ≤ q := by
          by_contra hgt
          have hfib : hFiber g l (coeff z g) ⊆ c.lower := by
            rcases hFiber_side c hmin l (coeff z g) with hL | hU
            · exact hL
            · exact False.elim (Set.disjoint_left.mp c.disjoint hz (hU ⟨hsame, rfl⟩))
          rcases lt_trichotomy (coeff z g) q with hltq | heqq | hgtq
          · exact hgt hltq.le
          · exact hgt (le_of_eq heqq)
          · exact lt_irrefl q (hgtq.trans_le (hqmax hfib))
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact ⟨bump l g q, bump_mem_hFiber l g q, (lt_bump hsame hlt).le⟩
        · exact ⟨z, ⟨hsame, heq⟩, le_rfl⟩
      · have hleL : coeff l g ≤ q := hqmax hqL
        rcases lt_or_eq_of_le hleL with hltL | heqL
        · exact ⟨bump l g q, bump_mem_hFiber l g q,
            ((below_head_of_lower c hmin hl hr hrank hz hsame).trans
              (lt_bump (hAgrees_refl g l) hltL)).le⟩
        · have hbump : l = bump l g q := by
            rw [← heqL]
            exact (bump_self l g).symm
          exact ⟨bump l g q, bump_mem_hFiber l g q,
            ((below_head_of_lower c hmin hl hr hrank hz hsame).trans_eq hbump).le⟩
    have hup_smaller : ∀ p ∈ upperQ, ∃ s ∈ upperQ, s < p := by
      intro p hp
      have hpq : q < p := by
        by_contra hle
        exact hp (hdown hqmem (le_of_not_gt hle))
      obtain ⟨s, hs1, hs2⟩ := exists_between hpq
      refine ⟨s, ?_, hs2⟩
      intro hsL
      exact (hqmax hsL).not_gt hs1
    obtain ⟨f, hf, _, hco⟩ := exists_nat_coinitial_rat hup_ne hup_smaller
    have hupper_le : ∀ z ∈ c.upper, ∃ n, bump l g (f n) ≤ z :=
      upper_ge_bump_seq c hl f (fun p hp => hco p hp)
    have hbump_upper : ∀ n, bump l g (f n) ∈ c.upper := by
      intro n
      rcases hFiber_side c hmin l (f n) with hL | hU
      · exact False.elim ((hf n) hL)
      · exact hU (bump_mem_hFiber l g (f n))
    have hci : setCoinitiality c.upper = ℵ₀ :=
      coinitiality_aleph0_of_nat hc.upper_nonempty hc.upper_no_least (fun n => bump l g (f n))
        hbump_upper hupper_le
    by_cases hδ0 : δ = 0
    · obtain ⟨b, hb, hqb⟩ := hc.lower_no_greatest (bump l g q)
        ((hqmem : hFiber g l q ⊆ c.lower) (bump_mem_hFiber l g q))
      obtain ⟨y, hy, hby⟩ := hfibcof b hb
      exact ((hqb.trans_le hby).ne
        (fiber_subsingleton_delta_zero hδ0 hy (bump_mem_hFiber l g q)).symm).elim
    · have hδ : (0 : _root_.Ordinal.{u}) < δ := lt_of_le_of_ne bot_le (Ne.symm hδ0)
      let pred : Gamma δ := g - leastPos hδ
      let tail : ℕ → HOrder δ := fun n =>
        bump l g q + smulQ ((n : ℚ) + 1) (basisQ pred)
      have htail_mem : ∀ n, tail n ∈ hFiber g l q := by
        intro n
        refine ⟨?_, ?_⟩
        · intro j hj
          rw [coeff_add, coeff_bump_ne l g j q hj.ne', coeff_smulQ,
            coeff_basis_ne (lt_trans (pred_lt hδ g) hj).ne.symm, mul_zero, add_zero]
        · rw [coeff_add, coeff_bump_self, coeff_smulQ, coeff_basis_ne (pred_lt hδ g).ne.symm,
            mul_zero, add_zero]
      have htail_cof : ∀ z ∈ c.lower, ∃ n, z ≤ tail n := by
        intro z hz
        obtain ⟨y, hy, hzy⟩ := hfibcof z hz
        obtain ⟨n, hn⟩ := exists_pred_smul_gt hδ (fiber_sub_supported hy)
        have hlt := addRight_lt (c := bump l g q) hn
        have hmove : y < tail n := by simpa [tail, sub_add_cancel, add_comm] using hlt
        exact ⟨n, hzy.trans hmove.le⟩
      have htail_lower : ∀ n, tail n ∈ c.lower := fun n => hqmem (htail_mem n)
      have hcf : setCofinality c.lower = ℵ₀ :=
        cofinality_aleph0_of_nat hc.lower_nonempty hc.lower_no_greatest tail htail_lower htail_cof
      exact ⟨hcf.trans hci.symm⟩
  · by_cases hleastU : ∃ q, IsLeast upperQ q
    · obtain ⟨q, hqmem, hqmin⟩ := hleastU
      have hlow_larger : ∀ p ∈ lowerQ, ∃ s ∈ lowerQ, p < s := by
        intro p hp
        by_contra hno
        have hgreatest : IsGreatest lowerQ p := by
          refine ⟨hp, ?_⟩
          intro s hs
          exact le_of_not_gt (fun hlt => hno ⟨s, hs, hlt⟩)
        exact hgreat ⟨p, hgreatest⟩
      obtain ⟨f, hf, _, hcof⟩ := exists_nat_cofinal_rat hlow_ne hlow_larger
      have hlower_le : ∀ z ∈ c.lower, ∃ n, z ≤ bump l g (f n) :=
        lower_le_bump_seq c hmin hl hr hrank f (fun p hp => hcof p hp)
      have hbump_lower : ∀ n, bump l g (f n) ∈ c.lower := by
        intro n
        exact hf n (bump_mem_hFiber l g (f n))
      have hcf : setCofinality c.lower = ℵ₀ :=
        cofinality_aleph0_of_nat hc.lower_nonempty hc.lower_no_greatest (fun n => bump l g (f n))
          hbump_lower hlower_le
      have hfibco : ∀ z ∈ c.upper, ∃ y ∈ hFiber g l q, y ≤ z := by
        intro z hz
        by_cases hsame : hAgrees g l z
        · have hge : q ≤ coeff z g := by
            by_contra hlt
            have hU : coeff z g ∈ upperQ := by
              change coeff z g ∉ lowerQ
              intro hL
              exact Set.disjoint_left.mp c.disjoint (hL ⟨hsame, rfl⟩) hz
            rcases lt_trichotomy q (coeff z g) with hltq | heqq | hgtq
            · exact hlt hltq.le
            · exact hlt (le_of_eq heqq)
            · exact lt_irrefl (coeff z g) (hgtq.trans_le (hqmin hU))
          rcases lt_or_eq_of_le hge with hlt | heq
          · exact ⟨bump l g q, bump_mem_hFiber l g q, (bump_lt_of_lt hsame hlt).le⟩
          · exact ⟨z, ⟨hsame, heq.symm⟩, le_rfl⟩
        · exact ⟨bump l g q, bump_mem_hFiber l g q,
            (bump_lt_of_higher c (above_head_of_upper c hl hz hsame) hsame q).le⟩
      by_cases hδ0 : δ = 0
      · obtain ⟨b, hb, hqb⟩ := hc.upper_no_least (bump l g q) (by
          rcases hFiber_side c hmin l q with hL | hU
          · exact False.elim (hqmem hL)
          · exact hU (bump_mem_hFiber l g q))
        obtain ⟨y, hy, hyb⟩ := hfibco b hb
        exact ((hyb.trans_lt hqb).ne
          (fiber_subsingleton_delta_zero hδ0 hy (bump_mem_hFiber l g q))).elim
      · have hδ : (0 : _root_.Ordinal.{u}) < δ := lt_of_le_of_ne bot_le (Ne.symm hδ0)
        let pred : Gamma δ := g - leastPos hδ
        let tail : ℕ → HOrder δ := fun n =>
          bump l g q - smulQ ((n : ℚ) + 1) (basisQ pred)
        have htail_mem : ∀ n, tail n ∈ hFiber g l q := by
          intro n
          refine ⟨?_, ?_⟩
          · intro j hj
            rw [coeff_sub, coeff_bump_ne l g j q hj.ne', coeff_smulQ,
              coeff_basis_ne (lt_trans (pred_lt hδ g) hj).ne.symm, mul_zero, sub_zero]
          · rw [coeff_sub, coeff_bump_self, coeff_smulQ,
              coeff_basis_ne (pred_lt hδ g).ne.symm, mul_zero, sub_zero]
        have htail_co : ∀ z ∈ c.upper, ∃ n, tail n ≤ z := by
          intro z hz
          obtain ⟨y, hy, hyz⟩ := hfibco z hz
          have hneg_sup : SupportedBelow g (-(y - bump l g q)) := by
            intro j hj
            rw [coeff_neg, fiber_sub_supported hy j hj, neg_zero]
          obtain ⟨n, hn⟩ := exists_pred_smul_gt hδ hneg_sup
          have hrev : y - bump l g q > -(smulQ ((n : ℚ) + 1) (basisQ pred)) := by
            simpa [neg_neg] using neg_lt_neg_H hn
          have hlt := addRight_lt (c := bump l g q) hrev
          have hmove : tail n < y := by simpa [tail, sub_eq_add_neg, add_comm, sub_add_cancel] using hlt
          exact ⟨n, hmove.le.trans hyz⟩
        have htail_upper : ∀ n, tail n ∈ c.upper := by
          intro n
          rcases hFiber_side c hmin l q with hL | hU
          · exact False.elim (hqmem hL)
          · exact hU (htail_mem n)
        have hci : setCoinitiality c.upper = ℵ₀ :=
          coinitiality_aleph0_of_nat hc.upper_nonempty hc.upper_no_least tail htail_upper htail_co
        exact ⟨hcf.trans hci.symm⟩
    · have hlow_larger : ∀ p ∈ lowerQ, ∃ s ∈ lowerQ, p < s := by
        intro p hp
        by_contra hno
        exact hgreat ⟨p, hp, fun s hs => le_of_not_gt (fun hlt => hno ⟨s, hs, hlt⟩)⟩
      have hup_smaller : ∀ p ∈ upperQ, ∃ s ∈ upperQ, s < p := by
        intro p hp
        by_contra hno
        exact hleastU ⟨p, hp, fun s hs => le_of_not_gt (fun hlt => hno ⟨s, hs, hlt⟩)⟩
      obtain ⟨f, hf, _, hcof⟩ := exists_nat_cofinal_rat hlow_ne hlow_larger
      obtain ⟨e, he, _, hco⟩ := exists_nat_coinitial_rat hup_ne hup_smaller
      have hlower_le := lower_le_bump_seq c hmin hl hr hrank f (fun p hp => hcof p hp)
      have hupper_le := upper_ge_bump_seq c hl e (fun p hp => hco p hp)
      have hbump_lower : ∀ n, bump l g (f n) ∈ c.lower := fun n =>
        hf n (bump_mem_hFiber l g (f n))
      have hbump_upper : ∀ n, bump l g (e n) ∈ c.upper := by
        intro n
        rcases hFiber_side c hmin l (e n) with hL | hU
        · exact False.elim ((he n) hL)
        · exact hU (bump_mem_hFiber l g (e n))
      have hcf : setCofinality c.lower = ℵ₀ :=
        cofinality_aleph0_of_nat hc.lower_nonempty hc.lower_no_greatest (fun n => bump l g (f n))
          hbump_lower hlower_le
      have hci : setCoinitiality c.upper = ℵ₀ :=
        coinitiality_aleph0_of_nat hc.upper_nonempty hc.upper_no_least (fun n => bump l g (e n))
          hbump_upper hupper_le
      exact ⟨hcf.trans hci.symm⟩

lemma lt_of_rank_lt {a b : HOrder δ} (ha : 0 < a) (hb : 0 < b)
    (h : rankOf a ha.ne' < rankOf b hb.ne') : a < b := by
  rw [Colex.lt_iff]
  refine ⟨rankOf b hb.ne', ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, coeff_eq_zero_of_rank_lt a ha.ne' (h.trans hj),
      coeff_eq_zero_of_rank_lt b hb.ne' hj]
  · rw [← coeff, ← coeff, coeff_eq_zero_of_rank_lt a ha.ne' h]
    exact coeff_rank_pos hb

lemma rankOf_proof_irrel {a : HOrder δ} (ha hb : a ≠ 0) : rankOf a ha = rankOf a hb := by
  have h := Subsingleton.elim ha hb
  subst h
  rfl

lemma rankOf_congr {a b : HOrder δ} (h : a = b) (ha : a ≠ 0) :
    rankOf a ha = rankOf b (h ▸ ha) := by
  subst h
  rfl

lemma neg_sub_neg_H (a b : HOrder δ) : (-a) - (-b) = b - a := by
  apply ofColex.injective
  ext i
  simp [coeff, sub_eq_add_neg, add_apply, neg_neg, add_comm]

lemma lt_sub_of_add_lt {a b c : HOrder δ} (h : a + b < c) : a < c - b := by
  have h' : a + b + (-b) < c + (-b) := addRight_lt (c := -b) h
  simpa [add_neg_cancel_right, sub_eq_add_neg] using h'

lemma lt_of_sub_lt_sub {a b c : HOrder δ} (h : a - c < b - c) : a < b := by
  have h' : a - c + c < b - c + c := addRight_lt h
  simpa [sub_add_cancel] using h'

lemma hCrossing_nonempty (c : Cut (HOrder δ)) (hc : Cut.IsInteriorNonprincipal c) :
    (hCrossing c).Nonempty := by
  obtain ⟨l, hl⟩ := hc.lower_nonempty
  obtain ⟨r, hr⟩ := hc.upper_nonempty
  exact ⟨rankOf (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne', l, hl, r, hr, rfl⟩

lemma hCrossing_noLeast_pos (c : Cut (HOrder δ)) (hc : Cut.IsInteriorNonprincipal c)
    (hno : ¬ ∃ g, g ∈ hCrossing c ∧ ∀ h, h ∈ hCrossing c → g ≤ h) :
    (0 : _root_.Ordinal.{u}) < δ := by
  by_contra hδ
  have h0 : δ = 0 := le_antisymm (le_of_not_gt hδ) bot_le
  obtain ⟨g, hg⟩ := hCrossing_nonempty c hc
  have hsub : Subsingleton (Gamma δ) := gamma_subsingleton h0
  refine hno ⟨g, hg, ?_⟩
  intro h hh
  exact le_of_eq (@Subsingleton.elim _ hsub h g).symm

def ranksFrom (c : Cut (HOrder δ)) (l : HOrder δ) (hl : l ∈ c.lower) : Set (Gamma δ) :=
  {g | ∃ r, ∃ hr : r ∈ c.upper,
    rankOf (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne' = g}

lemma exists_mem_lt_of_noLeast {T : Set (Gamma δ)}
    (hno : ¬ ∃ g, g ∈ T ∧ ∀ h, h ∈ T → g ≤ h) {h : Gamma δ} (hh : h ∈ T) :
    ∃ t, t ∈ T ∧ t < h := by
  by_contra hnone
  exact hno ⟨h, hh, fun t ht => le_of_not_gt (fun hlt => hnone ⟨t, ht, hlt⟩)⟩

lemma exists_ranksFrom_lt (c : Cut (HOrder δ))
    (hno : ¬ ∃ g, g ∈ hCrossing c ∧ ∀ h, h ∈ hCrossing c → g ≤ h)
    (l : HOrder δ) (hl : l ∈ c.lower)
    (hco : ∀ t ∈ hCrossing c, ∃ g ∈ ranksFrom c l hl, g ≤ t)
    {h : Gamma δ} (hh : h ∈ hCrossing c) :
    ∃ g, g ∈ ranksFrom c l hl ∧ g < h := by
  obtain ⟨t, ht, hth⟩ := exists_mem_lt_of_noLeast hno hh
  obtain ⟨g, hg, hle⟩ := hco t ht
  exact ⟨g, hg, lt_of_le_of_lt hle hth⟩

lemma supportedOn_eq_zero {T : Set (Gamma δ)} (hT : ∀ g, g ∈ T) {a : HOrder δ}
    (ha : SupportedOn T a) : a = 0 := by
  apply ofColex.injective
  ext i
  change coeff a i = coeff (0 : HOrder δ) i
  have hzero : coeff (0 : HOrder δ) i = 0 := by simp [coeff]
  rw [hzero]
  by_contra hne
  exact ha i hne (hT i)

lemma add_supported_mem_lower {c : Cut (HOrder δ)} {l a : HOrder δ} (hl : l ∈ c.lower)
    (ha : SupportedOn (hCrossing c) a) : a + l ∈ c.lower := by
  by_contra hnot
  have hmem : a + l ∈ c.lower ∪ c.upper := by rw [c.union_eq]; exact mem_univ _
  have hu : a + l ∈ c.upper :=
    ((mem_union (a + l) c.lower c.upper).1 hmem).resolve_left hnot
  have hlt : l < a + l := c.ordered l hl (a + l) hu
  have hpos : 0 < (a + l) - l := HOrder.sub_pos_of_lt hlt
  have heq : (a + l) - l = a := add_sub_cancel_right a l
  let g : Gamma δ := rankOf ((a + l) - l) hpos.ne'
  have hne : coeff a g ≠ 0 := by
    rw [← heq]
    exact coeff_rank_ne_zero hpos
  exact ha g hne ⟨l, hl, a + l, hu, rfl⟩

lemma exists_supported_above (c : Cut (HOrder δ)) (_hc : Cut.IsInteriorNonprincipal c)
    (hno : ¬ ∃ g, g ∈ hCrossing c ∧ ∀ h, h ∈ hCrossing c → g ≤ h)
    (l : HOrder δ) (hl : l ∈ c.lower)
    (hco : ∀ t ∈ hCrossing c, ∃ g ∈ ranksFrom c l hl, g ≤ t)
    {x : HOrder δ} (hx : x ∈ c.lower) :
    ∃ a, SupportedOn (hCrossing c) a ∧ x ≤ a + l := by
  by_contra hnoA
  have hall : ∀ a, SupportedOn (hCrossing c) a → a + l < x := by
    intro a ha
    rcases lt_trichotomy (a + l) x with h | h | h
    · exact h
    · exact (hnoA ⟨a, ha, le_of_eq h.symm⟩).elim
    · exact (hnoA ⟨a, ha, h.le⟩).elim
  have hxl : l < x := by simpa [zero_add] using hall 0 (supportedOn_zero _)
  have hpos : 0 < x - l := HOrder.sub_pos_of_lt hxl
  let hrank := rankOf (x - l) hpos.ne'
  by_cases hh : hrank ∈ hCrossing c
  · obtain ⟨g, hg, hgh⟩ := exists_ranksFrom_lt c hno l hl hco hh
    obtain ⟨r, hr, hrg⟩ := hg
    have hposr : 0 < r - l := HOrder.sub_pos_of_lt (c.ordered l hl r hr)
    have hdiff : r - l < x - l := lt_of_rank_lt hposr hpos (by
      rw [hrg]
      exact hgh)
    exact lt_asymm (lt_of_sub_lt_sub hdiff) (c.ordered x hx r hr)
  · obtain ⟨n, hn⟩ := exists_basis_smul_gt hpos
    have hsup : SupportedOn (hCrossing c) (smulQ ((n : ℚ) + 1) (basisQ hrank)) :=
      supportedOn_smul (supportedOn_basis hh)
    exact lt_asymm hn (lt_sub_of_add_lt (hall _ hsup))

lemma complement_no_greatest (c : Cut (HOrder δ)) (hδ : (0 : _root_.Ordinal.{u}) < δ)
    (hno : ¬ ∃ g, g ∈ hCrossing c ∧ ∀ h, h ∈ hCrossing c → g ≤ h) :
    ∀ s, s ∉ hCrossing c → ∃ t, t ∉ hCrossing c ∧ s < t := by
  intro s hs
  by_contra hnoT
  have hle : ∀ t, t ∉ hCrossing c → t ≤ s := fun t ht =>
    le_of_not_gt (fun hlt => hnoT ⟨t, ht, hlt⟩)
  have hlt_se : s < s + leastPos hδ := by
    rw [leastPos]
    simpa [add_zero] using gamma_add_lt_add_left (s := s) (basisZ_pos (leastIndex hδ))
  have hmem : s + leastPos hδ ∈ hCrossing c := by
    by_contra hS
    exact lt_irrefl s (hlt_se.trans_le (hle _ hS))
  refine hno ⟨s + leastPos hδ, hmem, ?_⟩
  intro t ht
  by_contra hlt
  have hupper : t < s + leastPos hδ := by
    rcases lt_trichotomy t (s + leastPos hδ) with h | h | h
    · exact h
    · exact (hlt (le_of_eq h.symm)).elim
    · exact (hlt h.le).elim
  have hst : s < t := by
    rcases lt_trichotomy s t with h | h | h
    · exact h
    · exact (hs (h ▸ ht)).elim
    · exact (hs (hCrossing_up c ht h)).elim
  have hlow : (s + leastPos hδ) - leastPos hδ < t := by
    rw [add_sub_cancel_right]
    exact hst
  exact no_gamma_between hδ (s + leastPos hδ) t hlow hupper

lemma lower_character_coinitial (c : Cut (HOrder δ)) (hc : Cut.IsInteriorNonprincipal c)
    (hno : ¬ ∃ g, g ∈ hCrossing c ∧ ∀ h, h ∈ hCrossing c → g ≤ h)
    (l : HOrder δ) (hl : l ∈ c.lower)
    (hco : ∀ t ∈ hCrossing c, ∃ g ∈ ranksFrom c l hl, g ≤ t) :
    setCofinality c.lower = setCoinitiality (hCrossing c) := by
  have hδ : (0 : _root_.Ordinal.{u}) < δ := hCrossing_noLeast_pos c hc hno
  let HS : Set (HOrder δ) := {a | SupportedOn (hCrossing c) a}
  let coset : Set (HOrder δ) := addRightOrderIso l '' HS
  have hsub : coset ⊆ c.lower := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    simpa [addRightOrderIso] using add_supported_mem_lower hl ha
  have hcof : ∀ x ∈ c.lower, ∃ y ∈ coset, x ≤ y := by
    intro x hx
    obtain ⟨a, ha, hle⟩ := exists_supported_above c hc hno l hl hco hx
    refine ⟨addRightOrderIso l a, mem_image_of_mem _ ha, ?_⟩
    simpa [addRightOrderIso] using hle
  have hSne : {g : Gamma δ | g ∉ hCrossing c}.Nonempty := by
    by_contra hempty
    have hT : ∀ g, g ∈ hCrossing c := by
      intro g
      by_contra hg
      exact hempty ⟨g, hg⟩
    have hgreat : ∀ x ∈ c.lower, x ≤ l := by
      intro x hx
      obtain ⟨a, ha, hle⟩ := exists_supported_above c hc hno l hl hco hx
      simpa [supportedOn_eq_zero hT ha, zero_add] using hle
    obtain ⟨b, hb, hbl⟩ := hc.lower_no_greatest l hl
    exact lt_irrefl l ((hbl.trans_le (hgreat b hb)))
  have hnoMax : ∀ s, s ∉ hCrossing c → ∃ t, t ∉ hCrossing c ∧ s < t :=
    complement_no_greatest c hδ hno
  let S : Set (Gamma δ) := {g | g ∉ hCrossing c}
  let γ : Cut (Gamma δ) :=
    { lower := S
      upper := hCrossing c
      union_eq := by
        ext g
        simp only [mem_union, mem_univ, iff_true]
        by_cases h : g ∈ hCrossing c
        · exact Or.inr h
        · exact Or.inl h
      disjoint := Set.disjoint_left.mpr fun g hgS hgT => hgS hgT
      ordered := by
        intro a ha b hb
        rcases lt_trichotomy a b with h | h | h
        · exact h
        · exact (ha (h ▸ hb)).elim
        · exact (ha (hCrossing_up c hb h)).elim }
  have hγ : Cut.IsInteriorNonprincipal γ :=
    ⟨hSne, hCrossing_nonempty c hc, fun a ha => hnoMax a ha,
      fun b hb => exists_mem_lt_of_noLeast hno hb⟩
  have hbal : setCofinality S = setCoinitiality (hCrossing c) := (gamma_balanced γ hγ).characters
  have hHS : setCofinality HS = setCofinality S := supported_cofinality (hCrossing c) hSne hnoMax
  have hcos : setCofinality coset = setCofinality HS := setCofinality_orderIso (addRightOrderIso l) HS
  exact (setCofinality_eq_of_cofinal hsub hcof).trans (hcos.trans (hHS.trans hbal))

lemma crossing_lower_above {c : Cut (HOrder δ)} {l x r : HOrder δ} {g tb : Gamma δ}
    (hx : x ∈ c.lower) (hl : l ∈ c.lower) (hr : r ∈ c.upper)
    (hrank : rankOf (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne' = g)
    (hstrict : ∀ g' ∈ ranksFrom c x hx, tb < g') (hgle : g ≤ tb) : x < l := by
  by_contra hle
  have hxl : l ≤ x := le_of_not_gt hle
  have hposx : 0 < r - x := HOrder.sub_pos_of_lt (c.ordered x hx r hr)
  have hsub : r - x ≤ r - l := sub_le_sub_right hxl
  have hrk := rank_le_pos hposx hsub
  have hposl : 0 < r - l := HOrder.sub_pos_of_lt (c.ordered l hl r hr)
  have hrk' : rankOf (r - x) hposx.ne' ≤ g := by
    rw [rankOf_proof_irrel (a := r - l) (lt_of_lt_of_le hposx hsub).ne' hposl.ne', hrank] at hrk
    exact hrk
  have hlt : tb < rankOf (r - x) hposx.ne' := hstrict _ ⟨r, hr, rfl⟩
  exact lt_irrefl g ((lt_of_le_of_lt hgle hlt).trans_le hrk')

lemma lower_character_bounded (c : Cut (HOrder δ)) (hc : Cut.IsInteriorNonprincipal c)
    (hbound : ∀ l, ∀ hl : l ∈ c.lower, ∃ t ∈ hCrossing c, ∀ g ∈ ranksFrom c l hl, t < g) :
    setCofinality c.lower = setCoinitiality (hCrossing c) := by
  obtain ⟨idx, hidx, hcard, hcoi⟩ :=
    exists_setCoinitiality_witness (hCrossing c) (hCrossing_nonempty c hc)
  have hpair : ∀ g, g ∈ idx → ∃ l, ∃ hl : l ∈ c.lower, ∃ r, ∃ hr : r ∈ c.upper,
      rankOf (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne' = g :=
    fun g hg => hidx hg
  let pick : {g // g ∈ idx} → HOrder δ := fun g => Classical.choose (hpair g.1 g.2)
  have pick_spec : ∀ g : {g // g ∈ idx}, ∃ hl : pick g ∈ c.lower, ∃ r, ∃ hr : r ∈ c.upper,
      rankOf (r - pick g) (HOrder.sub_pos_of_lt (c.ordered (pick g) hl r hr)).ne' = g.1 :=
    fun g => Classical.choose_spec (hpair g.1 g.2)
  have hpick_cof : ∀ x ∈ c.lower, ∃ y ∈ range pick, x ≤ y := by
    intro x hx
    obtain ⟨tb, htb, hstrict⟩ := hbound x hx
    obtain ⟨g, hg, hgle⟩ := hcoi tb htb
    let gs : {g // g ∈ idx} := ⟨g, hg⟩
    obtain ⟨hl, r, hr, hrank⟩ := pick_spec gs
    exact ⟨pick gs, mem_range_self gs,
      (crossing_lower_above hx hl hr hrank (fun g' hg' => hstrict g' hg') hgle).le⟩
  have hpick_sub : range pick ⊆ c.lower := by
    intro y hy
    obtain ⟨g, rfl⟩ := hy
    exact Classical.choose (pick_spec g)
  have hle : setCofinality c.lower ≤ setCoinitiality (hCrossing c) :=
    (setCofinality_le hpick_sub hpick_cof).trans (mk_range_le.trans (le_of_eq hcard))
  have hge : setCoinitiality (hCrossing c) ≤ setCofinality c.lower := by
    apply le_setCofinality
    intro u hu huco
    by_contra hsmall
    have hlt : #u < setCoinitiality (hCrossing c) := by
      rcases lt_trichotomy (#u) (setCoinitiality (hCrossing c)) with h | h | h
      · exact h
      · exact (hsmall (le_of_eq h.symm)).elim
      · exact (hsmall h.le).elim
    let bound : {x // x ∈ u} → Gamma δ := fun x => Classical.choose (hbound x.1 (hu x.2))
    have hBsub : range bound ⊆ hCrossing c := by
      intro g hg
      obtain ⟨x, rfl⟩ := hg
      exact (Classical.choose_spec (hbound x.1 (hu x.2))).1
    have hBlt : #(range bound) < setCoinitiality (hCrossing c) := lt_of_le_of_lt mk_range_le hlt
    have hex : ∃ g, g ∈ hCrossing c ∧ ∀ y ∈ range bound, g < y := by
      by_contra hall
      have hcoB : ∀ x ∈ hCrossing c, ∃ y ∈ range bound, y ≤ x := by
        intro x hx
        by_contra hnone
        have hall' : ∀ y ∈ range bound, x < y := by
          intro y hy
          rcases lt_trichotomy x y with h | h | h
          · exact h
          · exact (hnone ⟨y, hy, le_of_eq h.symm⟩).elim
          · exact (hnone ⟨y, hy, h.le⟩).elim
        exact hall ⟨x, hx, hall'⟩
      exact lt_irrefl _ ((setCoinitiality_le hBsub hcoB).trans_lt hBlt)
    obtain ⟨g, hg, hglow⟩ := hex
    obtain ⟨l0, hl0, r0, hr0, hrank0⟩ := hg
    have habove : ∀ x ∈ u, x < l0 := by
      intro x hx
      have ht := Classical.choose_spec (hbound x (hu hx))
      have htg : g < bound ⟨x, hx⟩ := hglow _ (mem_range_self _)
      exact crossing_lower_above (hu hx) hl0 hr0 hrank0
        (fun g' hg' => (htg.trans (ht.2 g' hg'))) (le_refl g)
    obtain ⟨y, hy, hyle⟩ := huco l0 hl0
    exact lt_irrefl y ((habove y hy).trans_le hyle)
  exact le_antisymm hle hge

lemma horder_lower_eq_coinitiality (c : Cut (HOrder δ)) (hc : Cut.IsInteriorNonprincipal c)
    (hno : ¬ ∃ g, g ∈ hCrossing c ∧ ∀ h, h ∈ hCrossing c → g ≤ h) :
    setCofinality c.lower = setCoinitiality (hCrossing c) := by
  by_cases hcase : ∃ l, ∃ hl : l ∈ c.lower, ∀ t ∈ hCrossing c, ∃ g ∈ ranksFrom c l hl, g ≤ t
  · obtain ⟨l, hl, hco⟩ := hcase
    exact lower_character_coinitial c hc hno l hl hco
  · have hbound : ∀ l, ∀ hl : l ∈ c.lower, ∃ t ∈ hCrossing c, ∀ g ∈ ranksFrom c l hl, t < g := by
      intro l hl
      by_contra hb
      have hco : ∀ t ∈ hCrossing c, ∃ g ∈ ranksFrom c l hl, g ≤ t := by
        intro t ht
        by_contra hnone
        have hall : ∀ g ∈ ranksFrom c l hl, t < g := by
          intro g hg
          rcases lt_trichotomy t g with h | h | h
          · exact h
          · exact (hnone ⟨g, hg, le_of_eq h.symm⟩).elim
          · exact (hnone ⟨g, hg, h.le⟩).elim
        exact hb ⟨t, ht, hall⟩
      exact hcase ⟨l, hl, hco⟩
    exact lower_character_bounded c hc hbound

def cutNeg (c : Cut (HOrder δ)) : Cut (HOrder δ) where
  lower := {x | -x ∈ c.upper}
  upper := {x | -x ∈ c.lower}
  union_eq := by
    ext x
    simp only [mem_union, mem_univ, iff_true]
    have hmem : -x ∈ c.lower ∪ c.upper := by rw [c.union_eq]; exact mem_univ _
    rcases (mem_union (-x) c.lower c.upper).1 hmem with h | h
    · exact Or.inr h
    · exact Or.inl h
  disjoint := Set.disjoint_left.mpr fun x hxL hxU =>
    (Set.disjoint_left.mp c.disjoint hxU) hxL
  ordered := by
    intro a ha b hb
    have h : -b < -a := c.ordered (-b) hb (-a) ha
    simpa [neg_neg] using neg_lt_neg_H h

lemma mem_cutNeg_lower {c : Cut (HOrder δ)} {x : HOrder δ} :
    x ∈ (cutNeg c).lower ↔ -x ∈ c.upper := Iff.rfl

lemma mem_cutNeg_upper {c : Cut (HOrder δ)} {x : HOrder δ} :
    x ∈ (cutNeg c).upper ↔ -x ∈ c.lower := Iff.rfl

lemma cutNeg_interior (c : Cut (HOrder δ)) (hc : Cut.IsInteriorNonprincipal c) :
    Cut.IsInteriorNonprincipal (cutNeg c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hc.upper_nonempty
    refine ⟨-r, ?_⟩
    rw [mem_cutNeg_lower]
    simpa [neg_neg] using hr
  · obtain ⟨l, hl⟩ := hc.lower_nonempty
    refine ⟨-l, ?_⟩
    rw [mem_cutNeg_upper]
    simpa [neg_neg] using hl
  · intro a ha
    obtain ⟨b, hb, hlt⟩ := hc.upper_no_least (-a) (mem_cutNeg_lower.mp ha)
    refine ⟨-b, ?_, ?_⟩
    · rw [mem_cutNeg_lower]
      simpa [neg_neg] using hb
    · simpa [neg_neg] using neg_lt_neg_H hlt
  · intro b hb
    obtain ⟨a, ha, hlt⟩ := hc.lower_no_greatest (-b) (mem_cutNeg_upper.mp hb)
    refine ⟨-a, ?_, ?_⟩
    · rw [mem_cutNeg_upper]
      simpa [neg_neg] using ha
    · simpa [neg_neg] using neg_lt_neg_H hlt

lemma neg_injective_H : Function.Injective (fun x : HOrder δ => -x) := fun x y h => by
  simpa [neg_neg] using congrArg Neg.neg h

lemma cofinality_cutNeg_lower (c : Cut (HOrder δ)) (hc : Cut.IsInteriorNonprincipal c) :
    setCofinality (cutNeg c).lower = setCoinitiality c.upper := by
  apply le_antisymm
  · obtain ⟨t, ht, hcard, hco⟩ := exists_setCoinitiality_witness c.upper hc.upper_nonempty
    let t' : Set (HOrder δ) := (fun x => -x) '' t
    have ht' : t' ⊆ (cutNeg c).lower := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [mem_cutNeg_lower]
      simpa [neg_neg] using ht hx
    have hcof : ∀ y ∈ (cutNeg c).lower, ∃ z ∈ t', y ≤ z := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := hco (-y) (mem_cutNeg_lower.mp hy)
      refine ⟨-x, mem_image_of_mem _ hx, ?_⟩
      simpa [neg_neg] using (neg_le_neg_iff_H (-y) x).mpr hxy
    exact (setCofinality_le ht' hcof).trans_eq ((mk_image_eq neg_injective_H).trans hcard)
  · apply le_setCofinality
    intro u hu huco
    let u' : Set (HOrder δ) := (fun x => -x) '' u
    have hu' : u' ⊆ c.upper := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact hu hx
    have hco : ∀ y ∈ c.upper, ∃ z ∈ u', z ≤ y := by
      intro y hy
      have hy' : -y ∈ (cutNeg c).lower := by
        rw [mem_cutNeg_lower]
        simpa [neg_neg] using hy
      obtain ⟨x, hx, hyx⟩ := huco (-y) hy'
      refine ⟨-x, mem_image_of_mem _ hx, ?_⟩
      simpa [neg_neg] using (neg_le_neg_iff_H x (-y)).mpr hyx
    exact (setCoinitiality_le hu' hco).trans_eq (mk_image_eq neg_injective_H)

lemma hCrossing_neg (c : Cut (HOrder δ)) : hCrossing (cutNeg c) = hCrossing c := by
  ext g
  constructor
  · intro hg
    obtain ⟨l, hl, r, hr, hrank⟩ := hg
    have hl' : -l ∈ c.upper := mem_cutNeg_lower.mp hl
    have hr' : -r ∈ c.lower := mem_cutNeg_upper.mp hr
    have heq : (-l) - (-r) = r - l := neg_sub_neg_H l r
    have hpos : 0 < (-l) - (-r) := HOrder.sub_pos_of_lt (c.ordered (-r) hr' (-l) hl')
    refine ⟨-r, hr', -l, hl', ?_⟩
    have hmove : rankOf ((-l) - (-r)) hpos.ne' = rankOf (r - l) (heq ▸ hpos.ne') :=
      rankOf_congr heq hpos.ne'
    rw [hmove, rankOf_proof_irrel (a := r - l) (heq ▸ hpos.ne')
      (HOrder.sub_pos_of_lt ((cutNeg c).ordered l hl r hr)).ne']
    exact hrank
  · intro hg
    obtain ⟨l, hl, r, hr, hrank⟩ := hg
    have heq : (-l) - (-r) = r - l := neg_sub_neg_H l r
    have hlt : -r < -l := by simpa [neg_neg] using neg_lt_neg_H (c.ordered l hl r hr)
    have hpos : 0 < (-l) - (-r) := HOrder.sub_pos_of_lt hlt
    refine ⟨-r, ?_, -l, ?_, ?_⟩
    · rw [mem_cutNeg_lower]
      simpa [neg_neg] using hr
    · rw [mem_cutNeg_upper]
      simpa [neg_neg] using hl
    · have hmove : rankOf ((-l) - (-r)) hpos.ne' = rankOf (r - l) (heq ▸ hpos.ne') :=
        rankOf_congr heq hpos.ne'
      rw [hmove, rankOf_proof_irrel (a := r - l) (heq ▸ hpos.ne')
        (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne']
      exact hrank

lemma horder_noLeast_balanced (c : Cut (HOrder δ)) (hc : Cut.IsInteriorNonprincipal c)
    (hno : ¬ ∃ g, g ∈ hCrossing c ∧ ∀ h, h ∈ hCrossing c → g ≤ h) :
    Cut.IsBalanced c := by
  have hlow := horder_lower_eq_coinitiality c hc hno
  have hno' : ¬ ∃ g, g ∈ hCrossing (cutNeg c) ∧ ∀ h, h ∈ hCrossing (cutNeg c) → g ≤ h := by
    simpa [hCrossing_neg c] using hno
  have hlow' := horder_lower_eq_coinitiality (cutNeg c) (cutNeg_interior c hc) hno'
  have hci : setCoinitiality c.upper = setCoinitiality (hCrossing c) := by
    rw [← cofinality_cutNeg_lower c hc, hlow', hCrossing_neg c]
  exact ⟨hlow.trans hci.symm⟩

lemma horder_balanced (c : Cut (HOrder δ)) (hc : Cut.IsInteriorNonprincipal c) :
    Cut.IsBalanced c := by
  by_cases hleast : ∃ g, g ∈ hCrossing c ∧ ∀ h, h ∈ hCrossing c → g ≤ h
  · obtain ⟨g, hg, hmin⟩ := hleast
    exact horder_least_balanced c hc hg hmin
  · exact horder_noLeast_balanced c hc hleast

end
end AEC
