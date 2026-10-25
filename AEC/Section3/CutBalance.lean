module

public import AEC.Section3.Balanced
public import AEC.Section3.HausdorffOrder
public import Mathlib.Order.WellFounded

@[expose] public section

namespace AEC
section

universe u v

open Cardinal Finsupp HOrder Set

variable {δ : _root_.Ordinal.{u}}

lemma setCofinality_eq_of_cofinal {α : Type v} [LinearOrder α] {s t : Set α}
    (ht : t ⊆ s) (hcof : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : setCofinality s = setCofinality t := by
  apply le_antisymm
  · apply le_setCofinality
    intro u hu huco
    exact setCofinality_le (ht := hu.trans ht) (fun x hx => by
      obtain ⟨z, hz, hxz⟩ := hcof x hx
      obtain ⟨y, hy, hzy⟩ := huco z hz
      exact ⟨y, hy, hxz.trans hzy⟩)
  · apply le_setCofinality
    intro u hu huco
    classical
    let pick : α → α := fun x => if hx : x ∈ u then Classical.choose (hcof x (hu hx)) else x
    have hpick : ∀ x ∈ u, pick x ∈ t ∧ x ≤ pick x := by
      intro x hx
      have spec := Classical.choose_spec (hcof x (hu hx))
      simpa [pick, hx] using spec
    let v : Set α := pick '' u
    have hv : v ⊆ t := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact (hpick x hx).1
    have hcofv : ∀ x ∈ t, ∃ y ∈ v, x ≤ y := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := huco x (ht hx)
      exact ⟨pick y, mem_image_of_mem _ hy, hxy.trans (hpick y hy).2⟩
    exact (setCofinality_le hv hcofv).trans mk_image_le

lemma setCoinitiality_eq_of_coinitial {α : Type v} [LinearOrder α] {s t : Set α}
    (ht : t ⊆ s) (hco : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : setCoinitiality s = setCoinitiality t := by
  unfold setCoinitiality
  apply setCofinality_eq_of_cofinal (image_mono ht)
  intro x hx
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, hba⟩ := hco a ha
  exact ⟨OrderDual.toDual b, mem_image_of_mem _ hb, OrderDual.toDual_le_toDual.mpr hba⟩

lemma Cut.lower_down {α : Type v} [LinearOrder α] (c : Cut α) {x y : α}
    (hx : x ∈ c.lower) (hyx : y ≤ x) : y ∈ c.lower := by
  by_contra hy
  have hmem : y ∈ c.lower ∪ c.upper := by rw [c.union_eq]; exact mem_univ y
  have hyu : y ∈ c.upper := ((mem_union y c.lower c.upper).1 hmem).resolve_left hy
  exact lt_irrefl x ((c.ordered x hx y hyu).trans_le hyx)

lemma Cut.upper_up {α : Type v} [LinearOrder α] (c : Cut α) {x y : α}
    (hy : y ∈ c.upper) (hxy : y ≤ x) : x ∈ c.upper := by
  by_contra hx
  have hmem : x ∈ c.lower ∪ c.upper := by rw [c.union_eq]; exact mem_univ x
  have hxl : x ∈ c.lower := ((mem_union x c.lower c.upper).1 hmem).resolve_right hx
  exact lt_irrefl x ((c.ordered x hxl y hy).trans_le hxy)

noncomputable def gammaRank (g : Gamma δ) (hg : g ≠ 0) : OrdIndex δ :=
  (ofColex g).support.max' (by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    exact hg (ofColex.injective (support_eq_empty.mp hempty)))

lemma le_gammaRank (g : Gamma δ) (hg : g ≠ 0) {i : OrdIndex δ}
    (hi : i ∈ (ofColex g).support) : i ≤ gammaRank g hg :=
  Finset.le_max' _ i hi

lemma coeffZ_eq_zero_of_gammaRank_lt (g : Gamma δ) (hg : g ≠ 0) {i : OrdIndex δ}
    (hi : gammaRank g hg < i) : coeffZ g i = 0 := by
  by_contra hne
  exact (le_gammaRank g hg (mem_support_iff.mpr (by simpa [coeffZ] using hne))).not_gt hi

lemma coeffZ_gammaRank_pos {g : Gamma δ} (hg : 0 < g) : 0 < coeffZ g (gammaRank g hg.ne') := by
  rw [Colex.lt_iff] at hg
  obtain ⟨i, hi, hlt⟩ := hg
  have himem : i ∈ (ofColex g).support := mem_support_iff.mpr (by simpa [coeffZ] using hlt.ne')
  have hrank : gammaRank g hg.ne' = i := by
    apply le_antisymm
    · apply Finset.max'_le
      intro j hj
      rcases lt_trichotomy j i with hltj | heq | hgt
      · exact hltj.le
      · exact le_of_eq heq
      · exact (mem_support_iff.mp hj (by simpa [coeffZ] using (hi j hgt).symm)).elim
    · exact Finset.le_max' _ i himem
  simpa [coeffZ, hrank] using hlt

lemma gamma_sub_pos_of_lt {l r : Gamma δ} (h : l < r) : 0 < r - l := by
  have hlt : l + -l < r + -l := gamma_addRight_lt h
  rw [add_neg_cancel] at hlt
  rw [sub_eq_add_neg]
  exact hlt

lemma gamma_lt_of_rank_lt {a b : Gamma δ} (ha : 0 < a) (hb : 0 < b)
    (h : gammaRank a ha.ne' < gammaRank b hb.ne') : a < b := by
  rw [Colex.lt_iff]
  refine ⟨gammaRank b hb.ne', ?_, ?_⟩
  · intro j hj
    rw [← coeffZ, ← coeffZ, coeffZ_eq_zero_of_gammaRank_lt a ha.ne' (h.trans hj),
      coeffZ_eq_zero_of_gammaRank_lt b hb.ne' hj]
  · rw [← coeffZ, ← coeffZ, coeffZ_eq_zero_of_gammaRank_lt a ha.ne' h]
    exact coeffZ_gammaRank_pos hb

lemma gamma_add_lt_add_left {s x y : Gamma δ} (h : x < y) : s + x < s + y := by
  simpa [add_comm] using gamma_addRight_lt (s := s) h

noncomputable def basisZN (α : OrdIndex δ) (n : ℤ) : Gamma δ :=
  toColex (single α n)

lemma coeffZ_basisZN_self (α : OrdIndex δ) (n : ℤ) : coeffZ (basisZN α n) α = n := by
  simp [basisZN, coeffZ, ofColex_toColex, single_eq_same]

lemma coeffZ_basisZN_ne {α i : OrdIndex δ} {n : ℤ} (h : i ≠ α) : coeffZ (basisZN α n) i = 0 := by
  simp [basisZN, coeffZ, ofColex_toColex, single_eq_of_ne h]

lemma coeffZ_sub (a b : Gamma δ) (i : OrdIndex δ) : coeffZ (a - b) i = coeffZ a i - coeffZ b i := by
  simp [coeffZ, sub_eq_add_neg, add_apply]

noncomputable def withCoeff (x : Gamma δ) (α : OrdIndex δ) (n : ℤ) : Gamma δ :=
  x - basisZN α (coeffZ x α) + basisZN α n

lemma coeffZ_withCoeff_self (x : Gamma δ) (α : OrdIndex δ) (n : ℤ) :
    coeffZ (withCoeff x α n) α = n := by
  rw [withCoeff, coeffZ_add, coeffZ_sub, coeffZ_basisZN_self, coeffZ_basisZN_self, sub_self,
    zero_add]

lemma coeffZ_withCoeff_ne (x : Gamma δ) (α i : OrdIndex δ) (n : ℤ) (h : i ≠ α) :
    coeffZ (withCoeff x α n) i = coeffZ x i := by
  rw [withCoeff, coeffZ_add, coeffZ_sub, coeffZ_basisZN_ne h, coeffZ_basisZN_ne h, sub_zero,
    add_zero]

lemma withCoeff_mono {x : Gamma δ} {α : OrdIndex δ} {n m : ℤ} (h : n < m) :
    withCoeff x α n < withCoeff x α m := by
  rw [Colex.lt_iff]
  refine ⟨α, ?_, ?_⟩
  · intro j hj
    rw [← coeffZ, ← coeffZ, coeffZ_withCoeff_ne x α j n hj.ne', coeffZ_withCoeff_ne x α j m hj.ne']
  · rw [← coeffZ, ← coeffZ, coeffZ_withCoeff_self, coeffZ_withCoeff_self]
    exact h

def agreesAbove (α : OrdIndex δ) (head x : Gamma δ) : Prop :=
  ∀ j, α < j → coeffZ x j = coeffZ head j

def gammaFiber (α : OrdIndex δ) (head : Gamma δ) (n : ℤ) : Set (Gamma δ) :=
  {x | agreesAbove α head x ∧ coeffZ x α = n}

lemma withCoeff_agrees (x : Gamma δ) (α : OrdIndex δ) (n : ℤ) :
    agreesAbove α x (withCoeff x α n) := by
  intro j hj
  rw [coeffZ_withCoeff_ne x α j n hj.ne']

lemma withCoeff_mem_fiber (x : Gamma δ) (α : OrdIndex δ) (n : ℤ) :
    withCoeff x α n ∈ gammaFiber α x n :=
  ⟨withCoeff_agrees x α n, coeffZ_withCoeff_self x α n⟩

lemma fiber_rank_lt {α : OrdIndex δ} {head : Gamma δ} {n : ℤ} {x y : Gamma δ}
    (hx : x ∈ gammaFiber α head n) (hy : y ∈ gammaFiber α head n) (hxy : x < y) :
    gammaRank (y - x) (gamma_sub_pos_of_lt hxy).ne' < α := by
  by_contra hge
  have hle : α ≤ gammaRank (y - x) (gamma_sub_pos_of_lt hxy).ne' := le_of_not_gt hge
  have hzero : coeffZ (y - x) (gammaRank (y - x) (gamma_sub_pos_of_lt hxy).ne') = 0 := by
    rw [coeffZ_sub]
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [hx.1 _ hlt, hy.1 _ hlt, sub_self]
    · rw [← heq, hx.2, hy.2, sub_self]
  exact (coeffZ_gammaRank_pos (gamma_sub_pos_of_lt hxy)).ne' hzero

lemma gamma_neg_lt_neg {x y : Gamma δ} (h : x < y) : -y < -x := by
  rw [Colex.lt_iff] at h ⊢
  obtain ⟨i, hi, hlt⟩ := h
  refine ⟨i, ?_, ?_⟩
  · intro j hj
    rw [← coeffZ, ← coeffZ, coeffZ_neg, coeffZ_neg]
    exact congrArg Neg.neg (hi j hj).symm
  · rw [← coeffZ, ← coeffZ, coeffZ_neg, coeffZ_neg]
    exact neg_lt_neg (by simpa [coeffZ] using hlt)

lemma gamma_sub_le_iff (s x y : Gamma δ) : s - x ≤ s - y ↔ y ≤ x := by
  constructor
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · have hneg : -x < -y := by
        have h0 : -s + (s - x) < -s + (s - y) := gamma_add_lt_add_left hlt
        simpa [sub_eq_add_neg, add_assoc, neg_add_cancel, zero_add] using h0
      simpa using (gamma_neg_lt_neg hneg).le
    · have hx : x = y := by
        apply_fun (fun z => s - z) at heq
        simpa [sub_sub_cancel] using heq
      exact le_of_eq hx.symm
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · simpa [sub_eq_add_neg] using (gamma_add_lt_add_left (s := s) (gamma_neg_lt_neg hlt)).le
    · exact le_of_eq (by rw [heq])

noncomputable def gammaRev (s : Gamma δ) : Gamma δ ≃o (Gamma δ)ᵒᵈ where
  toFun x := OrderDual.toDual (s - x)
  invFun x := s - OrderDual.ofDual x
  left_inv x := by simp [sub_sub_cancel]
  right_inv x := by simp [sub_sub_cancel]
  map_rel_iff' := by
    intro x y
    change (OrderDual.toDual (s - x) ≤ OrderDual.toDual (s - y)) ↔ x ≤ y
    rw [OrderDual.toDual_le_toDual]
    exact gamma_sub_le_iff s y x

lemma withCoeff_self (x : Gamma δ) (α : OrdIndex δ) : withCoeff x α (coeffZ x α) = x := by
  apply ofColex.injective
  ext i
  change coeffZ (withCoeff x α (coeffZ x α)) i = coeffZ x i
  by_cases hi : i = α
  · subst hi
    rw [coeffZ_withCoeff_self]
  · rw [coeffZ_withCoeff_ne x α i _ hi]

def crossingRanks (c : Cut (Gamma δ)) : Set (OrdIndex δ) :=
  {α | ∃ l, ∃ hl : l ∈ c.lower, ∃ r, ∃ hr : r ∈ c.upper,
    gammaRank (r - l) (gamma_sub_pos_of_lt (c.ordered l hl r hr)).ne' = α}

lemma exists_least_crossing (c : Cut (Gamma δ)) (hL : c.lower.Nonempty) (hR : c.upper.Nonempty) :
    ∃ α ∈ crossingRanks c, ∀ β ∈ crossingRanks c, α ≤ β := by
  obtain ⟨l, hl⟩ := hL
  obtain ⟨r, hr⟩ := hR
  have hpos := gamma_sub_pos_of_lt (c.ordered l hl r hr)
  have hne : (crossingRanks c).Nonempty :=
    ⟨gammaRank (r - l) hpos.ne', l, hl, r, hr, rfl⟩
  obtain ⟨α, hα, hmin⟩ := (wellFounded_lt (α := OrdIndex δ)).has_min (crossingRanks c) hne
  refine ⟨α, hα, ?_⟩
  intro β hβ
  rcases lt_trichotomy β α with hlt | heq | hgt
  · exact (hmin β hβ hlt).elim
  · exact le_of_eq heq.symm
  · exact hgt.le

lemma exists_max_int {s : Set ℤ} {N : ℤ} (hb : ∀ n ∈ s, n ≤ N) (hne : s.Nonempty) :
    ∃ m ∈ s, ∀ n ∈ s, n ≤ m := by
  classical
  obtain ⟨n0, hn0⟩ := hne
  have hnn : 0 ≤ N - n0 := sub_nonneg.mpr (hb n0 hn0)
  let p : ℕ → Prop := fun k => (N - (k : ℤ)) ∈ s
  have hp : ∃ k, p k := by
    refine ⟨(N - n0).toNat, ?_⟩
    have hk : ((N - n0).toNat : ℤ) = N - n0 := Int.toNat_of_nonneg hnn
    simpa [p, hk] using hn0
  have : DecidablePred p := Classical.decPred p
  let k := Nat.find hp
  refine ⟨N - k, Nat.find_spec hp, ?_⟩
  intro n hn
  have hnN : n ≤ N := hb n hn
  have hle : k ≤ (N - n).toNat := by
    by_contra hlt
    have hmem : p (N - n).toNat := by
      have hnat : ((N - n).toNat : ℤ) = N - n := Int.toNat_of_nonneg (sub_nonneg.mpr hnN)
      simpa [p, hnat] using hn
    exact Nat.find_min hp (lt_of_not_ge hlt) hmem
  have hkint : (k : ℤ) ≤ N - n := by
    simpa [Int.toNat_of_nonneg (sub_nonneg.mpr hnN)] using (Int.ofNat_le.mpr hle)
  have h1 : (k : ℤ) + n ≤ N := by
    have h := add_le_add_left hkint n
    rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] at h
    exact h
  have h2 : n ≤ N - (k : ℤ) := by
    have h := add_le_add_left h1 (-(k : ℤ))
    rw [add_assoc, add_comm n (-(k : ℤ)), ← add_assoc, add_neg_cancel, zero_add,
      ← sub_eq_add_neg] at h
    exact h
  exact h2

lemma fiber_one_side (c : Cut (Gamma δ)) {α : OrdIndex δ}
    (hleast : ∀ β ∈ crossingRanks c, α ≤ β) {head : Gamma δ} {n : ℤ} :
    gammaFiber α head n ⊆ c.lower ∨ gammaFiber α head n ⊆ c.upper := by
  by_contra h
  have hL : ¬ gammaFiber α head n ⊆ c.lower := (not_or.mp h).1
  have hU : ¬ gammaFiber α head n ⊆ c.upper := (not_or.mp h).2
  obtain ⟨x, hx, hxnL⟩ := not_subset.mp hL
  obtain ⟨y, hy, hynU⟩ := not_subset.mp hU
  have hxu : x ∈ c.upper := by
    have hmem : x ∈ c.lower ∪ c.upper := by rw [c.union_eq]; exact mem_univ x
    exact ((mem_union x c.lower c.upper).1 hmem).resolve_left hxnL
  have hyl : y ∈ c.lower := by
    have hmem : y ∈ c.lower ∪ c.upper := by rw [c.union_eq]; exact mem_univ y
    exact ((mem_union y c.lower c.upper).1 hmem).resolve_right hynU
  have hlt : y < x := c.ordered y hyl x hxu
  have hcross : gammaRank (x - y) (gamma_sub_pos_of_lt hlt).ne' ∈ crossingRanks c :=
    ⟨y, hyl, x, hxu, rfl⟩
  exact lt_irrefl α ((hleast _ hcross).trans_lt (fiber_rank_lt hy hx hlt))

lemma lt_withCoeff {head : Gamma δ} {α : OrdIndex δ} {x : Gamma δ} {n : ℤ}
    (hx : agreesAbove α head x) (hn : coeffZ x α < n) : x < withCoeff head α n := by
  rw [Colex.lt_iff]
  refine ⟨α, ?_, ?_⟩
  · intro j hj
    rw [← coeffZ, ← coeffZ, hx j hj, coeffZ_withCoeff_ne head α j n hj.ne']
  · rw [← coeffZ, ← coeffZ, coeffZ_withCoeff_self]
    exact hn

lemma same_head_lt {head : Gamma δ} {α : OrdIndex δ} {x : Gamma δ} {n : ℤ}
    (hx : agreesAbove α head x) (hn : n < coeffZ x α) : withCoeff head α n < x := by
  rw [Colex.lt_iff]
  refine ⟨α, ?_, ?_⟩
  · intro j hj
    rw [← coeffZ, ← coeffZ, coeffZ_withCoeff_ne head α j n hj.ne', hx j hj]
  · rw [← coeffZ, ← coeffZ, coeffZ_withCoeff_self]
    exact hn

lemma gamma_balanced (c : Cut (Gamma δ)) (hc : Cut.IsInteriorNonprincipal c) : Cut.IsBalanced c := by
  obtain ⟨α, hα, hleast⟩ := exists_least_crossing c hc.lower_nonempty hc.upper_nonempty
  obtain ⟨l, hl, r, hr, hrank⟩ := hα
  have hpos : 0 < r - l := gamma_sub_pos_of_lt (c.ordered l hl r hr)
  have hagree : agreesAbove α l r := by
    intro j hj
    have hzero : coeffZ (r - l) j = 0 :=
      coeffZ_eq_zero_of_gammaRank_lt (r - l) hpos.ne' (by simpa [hrank] using hj)
    exact (sub_eq_zero.mp (by simpa [coeffZ_sub] using hzero))
  let head : Gamma δ := l
  let lowerN : Set ℤ := {n | withCoeff head α n ∈ c.lower}
  have hself : withCoeff head α (coeffZ head α) = head := withCoeff_self head α
  have hNne : lowerN.Nonempty := ⟨coeffZ head α, by simpa [lowerN, hself] using hl⟩
  have hNbdd : ∀ n ∈ lowerN, n ≤ coeffZ r α := by
    intro n hn
    by_contra hgt
    have hcmp : r < withCoeff head α n := by
      rw [Colex.lt_iff]
      refine ⟨α, ?_, ?_⟩
      · intro j hj
        rw [← coeffZ, ← coeffZ, hagree j hj, coeffZ_withCoeff_ne head α j n hj.ne']
      · rw [← coeffZ, ← coeffZ, coeffZ_withCoeff_self]
        exact lt_of_not_ge hgt
    exact Set.disjoint_left.mp c.disjoint hn (c.upper_up hr hcmp.le)
  obtain ⟨k, hk, hkmax⟩ := exists_max_int hNbdd hNne
  have hfiberL : gammaFiber α head k ⊆ c.lower := by
    rcases fiber_one_side c hleast (head := head) (n := k) with hL | hU
    · exact hL
    · exact False.elim (Set.disjoint_left.mp c.disjoint hk (hU (withCoeff_mem_fiber head α k)))
  have hnot : withCoeff head α (k + 1) ∉ c.lower := by
    intro hmem
    exact lt_irrefl (k + 1) ((hkmax (k + 1) hmem).trans_lt (lt_add_one k))
  have hnext : withCoeff head α (k + 1) ∈ c.upper := by
    have hmem : withCoeff head α (k + 1) ∈ c.lower ∪ c.upper := by rw [c.union_eq]; exact mem_univ _
    exact ((mem_union _ c.lower c.upper).1 hmem).resolve_left hnot
  have hfiberU : gammaFiber α head (k + 1) ⊆ c.upper := by
    rcases fiber_one_side c hleast (head := head) (n := k + 1) with hL | hU
    · exact False.elim
        (Set.disjoint_left.mp c.disjoint (hL (withCoeff_mem_fiber head α (k + 1))) hnext)
    · exact hU
  have hcof : ∀ z ∈ c.lower, ∃ y ∈ gammaFiber α head k, z ≤ y := by
    intro z hz
    by_cases hsame : agreesAbove α head z
    · have hle : coeffZ z α ≤ k := by
        by_contra hgt
        have hge : k + 1 ≤ coeffZ z α := (Int.add_one_le_iff).mpr (lt_of_not_ge hgt)
        rcases eq_or_lt_of_le hge with heq | hltn
        · exact Set.disjoint_left.mp c.disjoint hz
            (hfiberU ⟨hsame, heq.symm⟩)
        · exact Set.disjoint_left.mp c.disjoint hz
            (c.upper_up hnext (same_head_lt hsame hltn).le)
      rcases lt_or_eq_of_le hle with hltn | heq
      · exact ⟨withCoeff head α k, withCoeff_mem_fiber head α k, (lt_withCoeff hsame hltn).le⟩
      · exact ⟨z, ⟨hsame, heq⟩, le_rfl⟩
    · have hltz : z < withCoeff head α k := by
        have hneg : z < head := by
          rcases lt_trichotomy z head with hlt | heq | hgt
          · exact hlt
          · exact False.elim (hsame (by intro j hj; rw [heq]))
          · have hdiff : 0 < z - head := gamma_sub_pos_of_lt hgt
            have hj : α < gammaRank (z - head) hdiff.ne' := by
              by_contra hle
              apply hsame
              intro j hjα
              have hzero := coeffZ_eq_zero_of_gammaRank_lt (z - head) hdiff.ne'
                (lt_of_le_of_lt (le_of_not_gt hle) hjα)
              rw [coeffZ_sub] at hzero
              exact sub_eq_zero.mp hzero
            have hup : r < z := by
              rw [Colex.lt_iff]
              refine ⟨gammaRank (z - head) hdiff.ne', ?_, ?_⟩
              · intro j hjg
                have hzero := coeffZ_eq_zero_of_gammaRank_lt (z - head) hdiff.ne' hjg
                rw [coeffZ_sub] at hzero
                have hzhead : coeffZ z j = coeffZ head j := sub_eq_zero.mp hzero
                rw [← coeffZ, ← coeffZ, hagree j (hj.trans hjg), hzhead]
              · have hlead := coeffZ_gammaRank_pos hdiff
                rw [coeffZ_sub] at hlead
                rw [← coeffZ, ← coeffZ, hagree _ hj]
                exact sub_pos.mp hlead
            exact False.elim (Set.disjoint_left.mp c.disjoint hz (c.upper_up hr hup.le))
        have hmemN : coeffZ head α ∈ lowerN := by simpa [lowerN, withCoeff_self head α] using hl
        rcases lt_or_eq_of_le (hkmax _ hmemN) with hlt | heq
        · have hmono : head < withCoeff head α k := by
            have hmw := withCoeff_mono (x := head) (α := α) hlt
            rwa [withCoeff_self head α] at hmw
          exact hneg.trans hmono
        · exact hneg.trans_eq (by rw [← heq]; exact (withCoeff_self head α).symm)
      exact ⟨withCoeff head α k, withCoeff_mem_fiber head α k, hltz.le⟩
  have hco : ∀ z ∈ c.upper, ∃ y ∈ gammaFiber α head (k + 1), y ≤ z := by
    intro z hz
    by_cases hsame : agreesAbove α head z
    · have hge : k + 1 ≤ coeffZ z α := by
        by_contra hlt
        have hle : coeffZ z α ≤ k := Int.le_of_lt_add_one (lt_of_not_ge hlt)
        rcases lt_or_eq_of_le hle with hltn | heq
        · exact Set.disjoint_right.mp c.disjoint hz
            (c.lower_down (hfiberL (withCoeff_mem_fiber head α k)) (lt_withCoeff hsame hltn).le)
        · exact Set.disjoint_right.mp c.disjoint hz (hfiberL ⟨hsame, heq⟩)
      rcases eq_or_lt_of_le hge with heq | hltn
      · exact ⟨z, ⟨hsame, heq.symm⟩, le_rfl⟩
      · exact ⟨withCoeff head α (k + 1), withCoeff_mem_fiber head α (k + 1),
          (same_head_lt hsame hltn).le⟩
    · have hgtz : withCoeff head α (k + 1) < z := by
        have hposz : head < z := by
          rcases lt_trichotomy head z with hlt | heq | hgt
          · exact hlt
          · exact False.elim (hsame (by intro j hj; rw [heq]))
          · have hlow : z ∈ c.lower :=
              c.lower_down (hfiberL (withCoeff_mem_fiber head α k)) (by
                have hneg : z < head := hgt
                have hmemN : coeffZ head α ∈ lowerN := by
                  simpa [lowerN, withCoeff_self head α] using hl
                rcases lt_or_eq_of_le (hkmax _ hmemN) with hltn | heq
                · have hmono : head < withCoeff head α k := by
                    have hmw := withCoeff_mono (x := head) (α := α) hltn
                    rwa [withCoeff_self head α] at hmw
                  exact (hneg.trans hmono).le
                · exact (hneg.trans_eq (by rw [← heq]; exact (withCoeff_self head α).symm)).le)
            exact False.elim (Set.disjoint_left.mp c.disjoint hlow hz)
        have hdiff : 0 < z - head := gamma_sub_pos_of_lt hposz
        have hj : α < gammaRank (z - head) hdiff.ne' := by
          by_contra hle
          apply hsame
          intro j hjα
          have hzero := coeffZ_eq_zero_of_gammaRank_lt (z - head) hdiff.ne'
            (lt_of_le_of_lt (le_of_not_gt hle) hjα)
          rw [coeffZ_sub] at hzero
          exact sub_eq_zero.mp hzero
        rw [Colex.lt_iff]
        refine ⟨gammaRank (z - head) hdiff.ne', ?_, ?_⟩
        · intro j hjg
          have hzero := coeffZ_eq_zero_of_gammaRank_lt (z - head) hdiff.ne' hjg
          have hzhead : coeffZ z j = coeffZ head j :=
            sub_eq_zero.mp (by rw [coeffZ_sub] at hzero; exact hzero)
          rw [← coeffZ, ← coeffZ, coeffZ_withCoeff_ne head α j (k + 1) (hj.trans hjg).ne', hzhead]
        · have hlead := coeffZ_gammaRank_pos hdiff
          rw [coeffZ_sub] at hlead
          rw [← withCoeff_agrees head α (k + 1) _ hj] at hlead
          rw [← coeffZ, ← coeffZ]
          exact sub_pos.mp hlead
      exact ⟨withCoeff head α (k + 1), withCoeff_mem_fiber head α (k + 1), hgtz.le⟩
  let svec : Gamma δ := withCoeff head α k + withCoeff head α (k + 1)
  have hswapL : ∀ x ∈ gammaFiber α head k, svec - x ∈ gammaFiber α head (k + 1) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [coeffZ_sub, coeffZ_add, hx.1 j hj, withCoeff_agrees head α k j hj,
        withCoeff_agrees head α (k + 1) j hj, add_sub_cancel_right]
    · rw [coeffZ_sub, coeffZ_add, hx.2, coeffZ_withCoeff_self, coeffZ_withCoeff_self,
        add_sub_cancel_left]
  have hswapU : ∀ y ∈ gammaFiber α head (k + 1), svec - y ∈ gammaFiber α head k := by
    intro y hy
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [coeffZ_sub, coeffZ_add, hy.1 j hj, withCoeff_agrees head α k j hj,
        withCoeff_agrees head α (k + 1) j hj, add_sub_cancel_right]
    · rw [coeffZ_sub, coeffZ_add, hy.2, coeffZ_withCoeff_self, coeffZ_withCoeff_self,
        add_sub_cancel_right]
  have himg : gammaRev svec '' gammaFiber α head k =
      OrderDual.toDual '' gammaFiber α head (k + 1) := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨svec - x, hswapL x hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨svec - y, hswapU y hy, ?_⟩
      show OrderDual.toDual (svec - (svec - y)) = OrderDual.toDual y
      rw [sub_sub_cancel]
  have hchars : setCofinality (gammaFiber α head k) =
      setCoinitiality (gammaFiber α head (k + 1)) := by
    rw [← setCofinality_orderIso (gammaRev svec) (gammaFiber α head k), himg]
    rfl
  exact ⟨(setCofinality_eq_of_cofinal hfiberL hcof).trans
    (hchars.trans (setCoinitiality_eq_of_coinitial hfiberU hco).symm)⟩

noncomputable def bump (x : HOrder δ) (g : Gamma δ) (q : ℚ) : HOrder δ :=
  x - smulQ (coeff x g) (basisQ g) + smulQ q (basisQ g)

lemma coeff_bump_self (x : HOrder δ) (g : Gamma δ) (q : ℚ) : coeff (bump x g q) g = q := by
  rw [bump, coeff_add, coeff_sub, coeff_smulQ, coeff_smulQ, coeff_basis_self, mul_one, mul_one,
    sub_self, zero_add]

lemma coeff_bump_ne (x : HOrder δ) (g i : Gamma δ) (q : ℚ) (h : i ≠ g) :
    coeff (bump x g q) i = coeff x i := by
  rw [bump, coeff_add, coeff_sub, coeff_smulQ, coeff_smulQ, coeff_basis_ne h, coeff_basis_ne h,
    mul_zero, mul_zero, sub_zero, add_zero]

lemma bump_self (x : HOrder δ) (g : Gamma δ) : bump x g (coeff x g) = x := by
  apply ofColex.injective
  ext i
  change coeff (bump x g (coeff x g)) i = coeff x i
  by_cases hi : i = g
  · subst hi
    rw [coeff_bump_self]
  · rw [coeff_bump_ne x g i _ hi]

lemma bump_mono {x : HOrder δ} {g : Gamma δ} {p q : ℚ} (h : p < q) : bump x g p < bump x g q := by
  rw [Colex.lt_iff]
  refine ⟨g, ?_, ?_⟩
  · intro j hj
    rw [← coeff, ← coeff, coeff_bump_ne x g j p hj.ne', coeff_bump_ne x g j q hj.ne']
  · rw [← coeff, ← coeff, coeff_bump_self, coeff_bump_self]
    exact h

def hAgrees (g : Gamma δ) (head x : HOrder δ) : Prop :=
  ∀ j, g < j → coeff x j = coeff head j

def hFiber (g : Gamma δ) (head : HOrder δ) (q : ℚ) : Set (HOrder δ) :=
  {x | hAgrees g head x ∧ coeff x g = q}

def hCrossing (c : Cut (HOrder δ)) : Set (Gamma δ) :=
  {g | ∃ l, ∃ hl : l ∈ c.lower, ∃ r, ∃ hr : r ∈ c.upper,
    rankOf (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne' = g}

lemma sub_basis_lt (l : HOrder δ) (h : Gamma δ) : l - basisQ h < l := by
  have hneg : -basisQ h < 0 := neg_lt_zero_of_pos (basisQ_pos h)
  have hlt : -basisQ h + l < 0 + l := addRight_lt hneg
  rw [← sub_eq_add_neg, add_zero] at hlt
  exact hlt

lemma hCrossing_up (c : Cut (HOrder δ)) {g h : Gamma δ} (hg : g ∈ hCrossing c) (hgh : g < h) :
    h ∈ hCrossing c := by
  obtain ⟨l, hl, r, hr, hrank⟩ := hg
  have hl' : l - basisQ h < l := sub_basis_lt l h
  have hlt : l - basisQ h < r := hl'.trans (c.ordered l hl r hr)
  have hpos : 0 < r - (l - basisQ h) := HOrder.sub_pos_of_lt hlt
  have hsum : r - (l - basisQ h) = (r - l) + basisQ h := by
    rw [sub_eq_add_neg, sub_eq_add_neg, neg_add, neg_neg, ← add_assoc, ← sub_eq_add_neg]
  have hpos0 : 0 < (r - l) + basisQ h := by simpa [hsum] using hpos
  have hrank' : rankOf ((r - l) + basisQ h) hpos0.ne' = h := by
    refine rank_eq_of_witness hpos0 h ?_ ?_
    · intro j hj
      change coeff ((r - l) + basisQ h) j = 0
      rw [coeff_add, coeff_eq_zero_of_rank_lt (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne'
        (by simpa [hrank] using hgh.trans hj), coeff_basis_ne hj.ne', add_zero]
    · change 0 < coeff ((r - l) + basisQ h) h
      rw [coeff_add, coeff_eq_zero_of_rank_lt (r - l) (HOrder.sub_pos_of_lt (c.ordered l hl r hr)).ne'
        (by simpa [hrank] using hgh), coeff_basis_self, zero_add]
      exact zero_lt_one
  have hmem : l - basisQ h ∈ c.lower := c.lower_down hl hl'.le
  have hpos' : 0 < r - (l - basisQ h) := hpos
  simpa [hsum] using ⟨l - basisQ h, hmem, r, hr, by simpa [hsum] using hrank'⟩

end
end AEC

