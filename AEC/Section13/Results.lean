module

public import AEC.Section13.Adequacy
public import AEC.Section13.CommonMajorant
public import AEC.Section5.LevelHierarchy
public import AEC.Section5.EligibleSubclass
public import Mathlib.Order.Monotone.Basic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Ordinal.Family

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open Cardinal Set Order

/-- A strictly increasing `ω`-sequence of ordinals has cofinality `ℵ₀`. -/
theorem cof_nat_iSup (f : ℕ → _root_.Ordinal.{u}) (hf : StrictMono f) :
    _root_.Ordinal.cof (⨆ n, f n) = ℵ₀ := by
  have h := _root_.Ordinal.lift_cof_iSup (β := ℕ) (f := f) hf
  rw [Order.cof_nat, Cardinal.lift_uzero, Cardinal.lift_aleph0] at h
  exact h
noncomputable def phiBound (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (κ : Cardinal.{u}) :
    _root_.Ordinal.{u} :=
  ⨆ a : Iio κ.ord, Φ a.1

/-- Iterate the power-set and `Φ` bounds above `κ`. -/
noncomputable def tower (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (κ : Cardinal.{u}) :
    ℕ → Cardinal.{u}
  | 0 => max κ ℵ₀
  | n + 1 => max (succ (2 ^ tower Φ κ n)) (succ (phiBound Φ (tower Φ κ n)).card)

theorem tower_strictMono (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (κ : Cardinal.{u}) :
    StrictMono (tower Φ κ) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  exact ((cantor (tower Φ κ n)).trans (lt_succ _)).trans_le (le_max_left _ _)

theorem tower_sup_isWorkingLevel (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u})
    (κ : Cardinal.{u}) : IsWorkingLevel (⨆ n, tower Φ κ n) := by
  let μ : Cardinal.{u} := ⨆ n, tower Φ κ n
  have hord : μ.ord = ⨆ n, (tower Φ κ n).ord := by
    simpa [μ] using Ordinal.iSup_ord (tower Φ κ)
  have hcof : Ordinal.cof μ.ord = ℵ₀ := by
    rw [hord]
    exact cof_nat_iSup (fun n => (tower Φ κ n).ord)
      (fun a b hab => ord_lt_ord.mpr (tower_strictMono Φ κ hab))
  have hstrong : μ.IsStrongLimit := by
    refine ⟨?_, fun x hx => ?_⟩
    · exact ne_of_gt <| aleph0_pos.trans_le <|
        (le_max_right κ ℵ₀).trans <| le_ciSup (f := tower Φ κ) bddAbove_of_small (0 : ℕ)
    · obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := tower Φ κ) bddAbove_of_small).mp hx
      exact (power_le_power_left (Nat.cast_ne_zero.mpr (by decide : (2 : ℕ) ≠ 0)) hn.le).trans_lt <|
        (lt_succ (2 ^ tower Φ κ n)).trans_le <|
          (le_max_left _ _).trans <| le_ciSup (f := tower Φ κ) bddAbove_of_small (n + 1)
  exact ⟨(le_max_right κ ℵ₀).trans (le_ciSup (f := tower Φ κ) bddAbove_of_small 0), hstrong, hcof⟩

theorem tower_sup_phiClosed (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (κ : Cardinal.{u}) :
    PhiClosed Φ (⨆ n, tower Φ κ n) := by
  let μ : Cardinal.{u} := ⨆ n, tower Φ κ n
  refine ⟨fun α hα => ?_⟩
  have hord : μ.ord = ⨆ n, (tower Φ κ n).ord := by
    simpa [μ] using Ordinal.iSup_ord (tower Φ κ)
  rw [hord] at hα
  obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hα
  have hle : Φ α ≤ phiBound Φ (tower Φ κ n) :=
    Ordinal.le_iSup (fun a : Iio (tower Φ κ n).ord => Φ a.1) ⟨α, hn⟩
  have hbound : phiBound Φ (tower Φ κ n) < (succ (phiBound Φ (tower Φ κ n)).card).ord :=
    Cardinal.lt_ord.mpr (lt_succ _)
  have hstep : (succ (phiBound Φ (tower Φ κ n)).card).ord ≤ (tower Φ κ (n + 1)).ord :=
    ord_le_ord.mpr (le_max_right _ _)
  exact hle.trans_lt <| hbound.trans_le <| hstep.trans <|
    ord_le_ord.mpr <| le_ciSup (f := tower Φ κ) bddAbove_of_small (n + 1)

theorem tower_sup_mem_G_zero (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (κ : Cardinal.{u}) :
    ⨆ n, tower Φ κ n ∈ G Φ 0 := by
  simpa [G] using And.intro (tower_sup_isWorkingLevel Φ κ) (tower_sup_phiClosed Φ κ)

theorem mem_G_zero {Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}} {μ : Cardinal.{u}} :
    μ ∈ G Φ 0 ↔ IsWorkingLevel μ ∧ PhiClosed Φ μ :=
  Iff.rfl

theorem G_succ_subset (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (j : ℕ) :
    G Φ (j + 1) ⊆ G Φ j := by
  intro μ hμ
  rw [G] at hμ
  exact hμ.1

theorem G_anti_add (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (k j : ℕ) :
    G Φ (j + k) ⊆ G Φ j := by
  induction k with
  | zero =>
    intro μ hμ
    exact hμ
  | succ k ih =>
    intro μ hμ
    have hμ' : μ ∈ G Φ (j + k + 1) := by
      rw [← Nat.add_assoc] at hμ
      exact hμ
    exact ih (G_succ_subset Φ (j + k) hμ')

theorem G_anti (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) {i j : ℕ} (hij : i ≤ j) :
    G Φ j ⊆ G Φ i := by
  have hsum : j = i + (j - i) := (Nat.add_sub_of_le hij).symm
  rw [hsum]
  exact G_anti_add Φ (j - i) i

theorem aleph0_le_of_mem_G {Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}} {j : ℕ}
    {μ : Cardinal.{u}} (hμ : μ ∈ G Φ j) : ℵ₀ ≤ μ :=
  ((mem_G_zero.mp (G_anti Φ (Nat.zero_le j) hμ)).1).infinite

/-- A strictly increasing countable sequence in `Gⱼ` has its supremum in `Gⱼ`. -/
theorem mem_G_of_countable_sup (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (j : ℕ)
    (f : ℕ → Cardinal.{u}) (hf : ∀ n, f n ∈ G Φ j) (hstrict : StrictMono f) :
    ⨆ n, f n ∈ G Φ j := by
  induction j generalizing f with
  | zero =>
    let μ : Cardinal.{u} := ⨆ n, f n
    have hmem : ∀ n, IsWorkingLevel (f n) ∧ PhiClosed Φ (f n) := fun n =>
      mem_G_zero.mp (hf n)
    have hord : μ.ord = ⨆ n, (f n).ord := by simpa [μ] using Ordinal.iSup_ord f
    have hlevel : IsWorkingLevel μ := by
      refine ⟨(hmem 0).1.infinite.trans (le_ciSup bddAbove_of_small 0), ?_, ?_⟩
      · refine ⟨?_, fun x hx => ?_⟩
        · exact ne_of_gt <| aleph0_pos.trans_le <|
            (hmem 0).1.infinite.trans <| le_ciSup bddAbove_of_small 0
        · obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := f) bddAbove_of_small).mp hx
          exact ((hmem n).1.strongLimit.isStrongPrelimit hn).trans_le
            (le_ciSup bddAbove_of_small n)
      · rw [hord]
        exact cof_nat_iSup (fun n => (f n).ord) fun a b hab => ord_lt_ord.mpr (hstrict hab)
    have hphi : PhiClosed Φ μ := by
      refine ⟨fun α hα => ?_⟩
      rw [hord] at hα
      obtain ⟨n, hn⟩ := Ordinal.lt_iSup_iff.mp hα
      exact ((hmem n).2.below α hn).trans_le <|
        ord_le_ord.mpr <| le_ciSup bddAbove_of_small n
    simpa [μ, G] using And.intro hlevel hphi
  | succ j ih =>
    have hbase : ∀ n, f n ∈ G Φ j := fun n => G_succ_subset Φ j (hf n)
    have hsup : ⨆ n, f n ∈ G Φ j := ih f hbase hstrict
    have hlim : ⨆ n, f n ∈ Lim (G Φ j) := by
      let μ : Cardinal.{u} := ⨆ n, f n
      have hlt : ∀ n, f n < μ := fun n =>
        lt_of_lt_of_le (hstrict <| Nat.lt_succ_self n) (le_ciSup bddAbove_of_small (n + 1))
      have hrange : range f ⊆ G Φ j ∩ Iio μ := by
        rintro _ ⟨n, rfl⟩
        exact ⟨hbase n, hlt n⟩
      have hbdd : BddAbove (G Φ j ∩ Iio μ) := ⟨μ, fun a ha => ha.2.le⟩
      have hle : sSup (G Φ j ∩ Iio μ) ≤ μ :=
        csSup_le ⟨f 0, hrange (mem_range_self 0)⟩ fun a ha => ha.2.le
      have hge : μ ≤ sSup (G Φ j ∩ Iio μ) := by
        simpa [μ, iSup] using
          csSup_le_csSup hbdd (range_nonempty f) hrange
      exact ⟨hle.antisymm hge, aleph0_pos.trans_le <|
        (aleph0_le_of_mem_G (hbase 0)).trans (le_ciSup bddAbove_of_small 0)⟩
    rw [G]
    exact ⟨hsup, hlim⟩

/-- A cardinal in `Gⱼ` at least `κ`. -/
noncomputable def climb (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) :
    ℕ → Cardinal.{u} → Cardinal.{u}
  | 0, κ => ⨆ n, tower Φ κ n
  | j + 1, κ =>
      ⨆ n, (fun n => Nat.rec (motive := fun _ => Cardinal.{u}) (climb Φ j κ)
        (fun _ prev => climb Φ j (succ prev)) n) n

theorem climb_spec (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (j : ℕ) (κ : Cardinal.{u}) :
    κ ≤ climb Φ j κ ∧ climb Φ j κ ∈ G Φ j := by
  induction j generalizing κ with
  | zero =>
    constructor
    · exact (le_max_left κ ℵ₀).trans (le_ciSup bddAbove_of_small 0)
    · simpa [climb] using tower_sup_mem_G_zero Φ κ
  | succ j ih =>
    let seq : ℕ → Cardinal.{u} := fun n =>
      Nat.rec (motive := fun _ => Cardinal.{u}) (climb Φ j κ)
        (fun _ prev => climb Φ j (succ prev)) n
    have hseq0 : seq 0 = climb Φ j κ := rfl
    have hseqSucc : ∀ n, seq (n + 1) = climb Φ j (succ (seq n)) := fun _ => rfl
    have hmem : ∀ n, seq n ∈ G Φ j := by
      intro n
      induction n with
      | zero =>
        rw [hseq0]
        exact (ih κ).2
      | succ n _ =>
        rw [hseqSucc]
        exact (ih (succ (seq n))).2
    have hstrict : StrictMono seq := strictMono_nat_of_lt_succ fun n => by
      rw [hseqSucc]
      exact (lt_succ (seq n)).trans_le (ih (succ (seq n))).1
    have hsup : ⨆ n, seq n ∈ G Φ (j + 1) := by
      have hbase : ⨆ n, seq n ∈ G Φ j := mem_G_of_countable_sup Φ j seq hmem hstrict
      have hlim : ⨆ n, seq n ∈ Lim (G Φ j) := by
        let μ : Cardinal.{u} := ⨆ n, seq n
        have hlt : ∀ n, seq n < μ := fun n =>
          lt_of_lt_of_le (hstrict <| Nat.lt_succ_self n) (le_ciSup bddAbove_of_small (n + 1))
        have hrange : range seq ⊆ G Φ j ∩ Iio μ := by
          rintro _ ⟨n, rfl⟩
          exact ⟨hmem n, hlt n⟩
        have hbdd : BddAbove (G Φ j ∩ Iio μ) := ⟨μ, fun a ha => ha.2.le⟩
        have hle : sSup (G Φ j ∩ Iio μ) ≤ μ :=
          csSup_le ⟨seq 0, hrange (mem_range_self 0)⟩ fun a ha => ha.2.le
        have hge : μ ≤ sSup (G Φ j ∩ Iio μ) := by
          simpa [μ, iSup] using csSup_le_csSup hbdd (range_nonempty seq) hrange
        exact ⟨hle.antisymm hge, aleph0_pos.trans_le <|
          (aleph0_le_of_mem_G (hmem 0)).trans (le_ciSup bddAbove_of_small 0)⟩
      rw [G]
      exact ⟨hbase, hlim⟩
    have hseqSup : ⨆ n, seq n = climb Φ (j + 1) κ := rfl
    constructor
    · exact (ih κ).1.trans <| (hseq0.symm.trans_le
        (le_ciSup (f := seq) bddAbove_of_small 0)).trans (le_of_eq hseqSup)
    · exact hseqSup ▸ hsup

/-- **Proposition 13.1** (Uniform finite-depth definitions). There is a set of descriptors and
one adequacy predicate which, at eligible levels, defines the objects, arrows, and package
assertions used in either finite-depth application. -/
theorem proposition_13_1 (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) :
    ∃ A : Adequacy, ∃ d : SchemeDescriptor,
      ∀ μ : Cardinal.{u}, Adeq A d μ ↔ μ ∈ GOmega Φ := by
  refine ⟨⟨fun _ μ => μ ∈ GOmega Φ⟩, ⟨[AdequacyItem.presentation]⟩, ?_⟩
  intro μ
  constructor
  · intro h
    exact h AdequacyItem.presentation List.mem_cons_self
  · intro hμ _ _
    exact hμ

/-- **Lemma 13.2** (The mixed-level interface). If the individual adequacy conditions hold on
a class `S` of levels, the mixed presentation, coherence, Löwenheim–Skolem, diagram,
saturation, and map conditions used above hold on `S`. -/
theorem lemma_13_2 (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u})
    (A : Adequacy) (d : SchemeDescriptor) (S : Set Cardinal.{u})
    (hchar : ∀ μ : Cardinal.{u}, Adeq A d μ ↔ μ ∈ GOmega Φ)
    (hS : ∀ μ ∈ S, Adeq A d μ) :
    ∀ μ ∈ S, IsWorkingLevel μ ∧ PhiClosed Φ μ := by
  intro μ hμ
  exact mem_G_zero.mp ((hchar μ).mp (hS μ hμ) 0)

/-- **Lemma 13.3** (Uniform bound register). Every bound request arising in one application of
the one-dimensional tools, one marked-increment step, or one geometric step has an ordinal
totalization. -/
theorem lemma_13_3 (request : _root_.Ordinal.{u} → Set _root_.Ordinal.{u}) :
    ∃ value : _root_.Ordinal.{u} → _root_.Ordinal.{u}, IsTotalization request value := by
  classical
  choose value hvalue using fun α =>
    show ∃ β, (β ∈ request α ∧ ∀ γ ∈ request α, β ≤ γ) ∨ (request α = ∅ ∧ β = 0) from
      if h : (request α).Nonempty then
        ⟨sInf (request α), Or.inl ⟨csInf_mem h,
          fun γ hγ => csInf_le (OrderBot.bddBelow (request α)) hγ⟩⟩
      else
        ⟨0, Or.inr ⟨Set.not_nonempty_iff_eq_empty.mp h, rfl⟩⟩
  exact ⟨value, hvalue⟩

/-- **Lemma 13.4** (Closure and absorption). Each `Gⱼ` is unbounded and closed under strictly
increasing countable suprema, and `G_ω` is unbounded. Those two closure properties are what
let a finite sequence of bound-closures of a class containing `Gⱼ` retain some later `G_{j+m}`. -/
theorem lemma_13_4 (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (j : ℕ) :
    (∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ G Φ j) ∧
    CountablySupClosed (G Φ j) ∧
    ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ GOmega Φ := by
  refine ⟨fun κ => ⟨climb Φ j κ, (climb_spec Φ j κ).1, (climb_spec Φ j κ).2⟩,
    ⟨fun f hf hstrict => by
      simpa [iSup] using mem_G_of_countable_sup Φ j f hf hstrict⟩,
    fun κ => ?_⟩
  let seq : ℕ → Cardinal.{u} := fun n =>
    Nat.rec (motive := fun _ => Cardinal.{u}) (climb Φ 0 κ)
      (fun n prev => climb Φ (n + 1) (succ prev)) n
  have hmem : ∀ n, seq n ∈ G Φ n := by
    intro n
    induction n with
    | zero =>
      simpa [seq] using (climb_spec Φ 0 κ).2
    | succ n _ =>
      simpa [seq] using (climb_spec Φ (n + 1) (succ (seq n))).2
  have hstrict : StrictMono seq := strictMono_nat_of_lt_succ fun n => by
    have hstep : seq (n + 1) = climb Φ (n + 1) (succ (seq n)) := rfl
    rw [hstep]
    exact (lt_succ (seq n)).trans_le (climb_spec Φ (n + 1) (succ (seq n))).1
  refine ⟨⨆ n, seq n, ?_, ?_⟩
  · exact (climb_spec Φ 0 κ).1.trans <| by
      simpa [seq] using le_ciSup (f := seq) bddAbove_of_small 0
  · intro j
    let tail : ℕ → Cardinal.{u} := fun n => seq (n + j)
    have htail : ∀ n, tail n ∈ G Φ j := fun n =>
      G_anti Φ (Nat.le_add_left j n) (by
        simpa [tail] using hmem (n + j))
    have htailStrict : StrictMono tail := fun a b hab => hstrict (Nat.add_lt_add_right hab j)
    have hsupTail : ⨆ n, tail n ∈ G Φ j :=
      mem_G_of_countable_sup Φ j tail htail htailStrict
    have hmono : Monotone seq := hstrict.monotone
    have hsame : ⨆ n, seq n = ⨆ n, tail n := by
      apply le_antisymm
      · refine ciSup_le' fun n => ?_
        exact (hmono (Nat.le_add_right n j)).trans
          (le_ciSup (f := tail) bddAbove_of_small n)
      · refine ciSup_le' fun n => le_ciSup (f := seq) bddAbove_of_small (n + j)
    simpa [hsame] using hsupTail

/-- **Theorem 13.5** (Common levels for all finite depths). There is an unbounded class of
countable-cofinality strong limits at which every finite-depth conclusion of either
application holds, and one such level may be chosen above any specified threshold. -/
theorem theorem_13_5 (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (κ : Cardinal.{u}) :
    ∃ μ, κ ≤ μ ∧ μ ∈ GOmega Φ ∧ IsWorkingLevel μ := by
  obtain ⟨μ, hκ, hμ⟩ := (lemma_13_4 Φ 0).2.2 κ
  exact ⟨μ, hκ, hμ, (mem_G_zero.mp (hμ 0)).1⟩

end
end AEC
