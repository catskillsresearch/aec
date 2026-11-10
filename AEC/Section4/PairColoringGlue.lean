module

public import AEC.Section2.Results
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Pair-coloring glue for Lemma 4.7

English: vectors with `i < j ⇒ ∃ c, uⱼ(c) < uᵢ(c)` are pair-colored by the least such `c`;
Lemma 2.5 yields an infinite homogeneous set; that coordinate then strictly decreases along an
`ℕ`-chain — impossible for ordinals.

Rank-slice ladder construction and Type-u witness packaging are separate infra.
-/

@[expose] public section

namespace AEC
section

universe u

open Classical Cardinal

/-- Least coordinate witnessing `u j c < u i c`. -/
noncomputable def firstDescentCoord {C ι : Type u} [LinearOrder C] [WellFoundedLT C]
    (u : ι → C → Ordinal.{u}) {i j : ι} (h : ∃ c : C, u j c < u i c) : C :=
  WellFounded.min wellFounded_lt {c : C | u j c < u i c} h

theorem firstDescentCoord_mem {C ι : Type u} [LinearOrder C] [WellFoundedLT C]
    (u : ι → C → Ordinal.{u}) {i j : ι} (h : ∃ c : C, u j c < u i c) :
    u j (firstDescentCoord u h) < u i (firstDescentCoord u h) :=
  WellFounded.min_mem wellFounded_lt {c : C | u j c < u i c} h

theorem card_two_pair {ι : Type u} [DecidableEq ι] {a b : ι} (hab : a ≠ b) :
    ({a, b} : Finset ι).card = 2 := by
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  simpa [eq_comm] using hab

theorem finset_card_two_pos {ι : Type u} {s : Finset ι} (hs : s.card = 2) : s.Nonempty :=
  Finset.card_pos.mp (by rw [hs]; decide)

/-- Ordered pair `(min s, the other element)` for a 2-element finset. -/
noncomputable def orderedPairOfCardTwo {ι : Type u} [LinearOrder ι]
    (s : Finset ι) (hs : s.card = 2) : ι × ι := by
  classical
  let a := s.min' (finset_card_two_pos hs)
  have ha : a ∈ s := Finset.min'_mem _ _
  have herase : (s.erase a).card = 1 := by
    rw [Finset.card_erase_of_mem ha, hs]
  let b := (s.erase a).min' (Finset.card_pos.mp (by rw [herase]; decide))
  exact (a, b)

theorem orderedPairOfCardTwo_fst_lt_snd {ι : Type u} [LinearOrder ι]
    (s : Finset ι) (hs : s.card = 2) :
    (orderedPairOfCardTwo s hs).1 < (orderedPairOfCardTwo s hs).2 := by
  classical
  unfold orderedPairOfCardTwo
  -- After unfolding the `by` definition, reason about min' / erase.
  change
    (s.min' (finset_card_two_pos hs)) <
      ((s.erase (s.min' (finset_card_two_pos hs))).min'
        (Finset.card_pos.mp (by
          rw [Finset.card_erase_of_mem (Finset.min'_mem _ _), hs]; decide)))
  set a := s.min' (finset_card_two_pos hs)
  set b := (s.erase a).min' _
  have hb_erase : b ∈ s.erase a := Finset.min'_mem _ _
  have hb_ne : b ≠ a := (Finset.mem_erase.mp hb_erase).1
  have hb : b ∈ s := (Finset.mem_erase.mp hb_erase).2
  exact lt_of_le_of_ne (Finset.min'_le s b hb) (Ne.symm hb_ne)

theorem orderedPairOfCardTwo_of_lt {ι : Type u} [LinearOrder ι]
    {a b : ι} (hab : a < b) :
    orderedPairOfCardTwo ({a, b} : Finset ι) (card_two_pair (ne_of_lt hab)) = (a, b) := by
  classical
  set s : Finset ι := {a, b}
  have hs : s.card = 2 := card_two_pair (ne_of_lt hab)
  have hmin : s.min' (finset_card_two_pos hs) = a := by
    refine le_antisymm ?_ ?_
    · exact s.min'_le a (by simp [s])
    · exact (s.le_min'_iff (finset_card_two_pos hs)).mpr (by
        intro y hy
        simp only [s, Finset.mem_insert, Finset.mem_singleton] at hy
        rcases hy with rfl | rfl
        · exact le_rfl
        · exact le_of_lt hab)
  have herase : s.erase a = {b} := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_erase.mp hx with ⟨hne, hin⟩
      simp only [s, Finset.mem_insert, Finset.mem_singleton] at hin
      rcases hin with rfl | rfl
      · exact (hne rfl).elim
      · simp
    · intro hx
      simp only [Finset.mem_singleton] at hx
      subst hx
      exact Finset.mem_erase.mpr ⟨ne_of_gt hab, by simp [s]⟩
  have hsecond :
      (s.erase (s.min' (finset_card_two_pos hs))).min'
        (Finset.card_pos.mp (by
          rw [Finset.card_erase_of_mem (Finset.min'_mem _ _), hs]; decide)) = b := by
    simp only [hmin, herase]
    exact Finset.min'_singleton b
  refine (Prod.ext ?_ ?_ : orderedPairOfCardTwo s hs = (a, b))
  · simpa [orderedPairOfCardTwo] using hmin
  · simpa [orderedPairOfCardTwo] using hsecond

/-- Color a 2-subset by the least descent coordinate of its ordered pair. -/
noncomputable def pairDescentColor {C ι : Type u} [LinearOrder C] [WellFoundedLT C]
    [LinearOrder ι] (u : ι → C → Ordinal.{u})
    (hdesc : ∀ ⦃i j : ι⦄, i < j → ∃ c : C, u j c < u i c)
    (s : {t : Finset ι // t.card = 2}) : C :=
  firstDescentCoord u (hdesc (orderedPairOfCardTwo_fst_lt_snd s.1 s.2))

theorem pairDescentColor_of_lt {C ι : Type u} [LinearOrder C] [WellFoundedLT C]
    [LinearOrder ι] (u : ι → C → Ordinal.{u})
    (hdesc : ∀ ⦃i j : ι⦄, i < j → ∃ c : C, u j c < u i c)
    {a b : ι} (hab : a < b) :
    pairDescentColor u hdesc ⟨{a, b}, card_two_pair (ne_of_lt hab)⟩ =
      firstDescentCoord u (hdesc hab) := by
  dsimp [pairDescentColor]
  simp only [orderedPairOfCardTwo_of_lt hab]

/-- **Infra: pair-color glue.** Meeting the Lemma 2.5 bound for pairs / `#C` colors, no
well-ordered index can carry ordinal vectors that descend on every increasing pair. -/
theorem pair_coloring_glue {C ι : Type u}
    [LinearOrder C] [WellFoundedLT C] [LinearOrder ι] [WellFoundedLT ι]
    (hC : aleph0 ≤ #C)
    (u : ι → C → Ordinal.{u})
    (hdesc : ∀ ⦃i j : ι⦄, i < j → ∃ c : C, u j c < u i c) :
    ∃ R : Cardinal.{u}, aleph0 ≤ R ∧ (R ≤ #ι → False) := by
  classical
  obtain ⟨R, hRinf, hpart, _⟩ := lemma_2_5 (#C) aleph0 2 hC le_rfl (Nat.succ_pos 1)
  refine ⟨R, hRinf, fun hRι => ?_⟩
  obtain ⟨H, hH, c₀, hc⟩ := hpart ι hRι C rfl (pairDescentColor u hdesc)
  have : Infinite ↥H := Cardinal.infinite_iff.mpr (by simpa using hH)
  obtain ⟨f₀, hmono | hanti⟩ := Infinite.exists_strictMono_or_strictAnti ↥H
  · let f : ℕ → ι := fun n => (f₀ n).1
    have hfH (n : ℕ) : f n ∈ H := (f₀ n).2
    have hfmono : StrictMono f := fun n m hnm => Subtype.coe_lt_coe.mpr (hmono hnm)
    have hantiOrd : StrictAnti (fun n : ℕ => u (f n) c₀) := by
      intro n m hnm
      have hfm : f n < f m := hfmono hnm
      have hsub : ∀ x ∈ ({f n, f m} : Finset ι), x ∈ H := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> [exact hfH n; exact hfH m]
      have hcolor :
          pairDescentColor u hdesc ⟨{f n, f m}, card_two_pair (ne_of_lt hfm)⟩ = c₀ :=
        hc _ _ hsub
      have hEq := pairDescentColor_of_lt u hdesc hfm
      have hmem := firstDescentCoord_mem u (hdesc hfm)
      rw [← hEq, hcolor] at hmem
      exact hmem
    exact (not_strictAnti_of_wellFoundedLT (fun n => u (f n) c₀) hantiOrd).elim
  · exact (not_strictAnti_of_wellFoundedLT (fun n => (f₀ n : ι))
      (fun n m hnm => Subtype.coe_lt_coe.mpr (hanti hnm))).elim

end
end AEC
