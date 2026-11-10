module

public import AEC.Section5.EligibleLevel
public import AEC.Section5.Lim
public import Mathlib.Order.Basic
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal Set

/-- A class of cardinals is closed under strictly increasing countable suprema. -/
class CountablySupClosed (T : Set Cardinal.{u}) : Prop where
  sup : ∀ f : ℕ → Cardinal.{u}, (∀ n, f n ∈ T) → StrictMono f → sSup (Set.range f) ∈ T

/-- **Convention 5.3.** The input eligible class `S` contains a fixed definable unbounded
subclass `T` closed under suprema of strictly increasing countable sequences. -/
def EligibleSubclass (S T : Set Cardinal.{u}) : Prop :=
  T ⊆ S ∧ (∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ T) ∧ CountablySupClosed T

/-- Threshold refinement: “a threshold only removes an initial segment.” -/
def eligibleTail (T : Set Cardinal.{u}) (α : Cardinal.{u}) : Set Cardinal.{u} :=
  {μ ∈ T | α ≤ μ}

namespace EligibleSubclass

theorem mem_source {S T : Set Cardinal.{u}} (h : EligibleSubclass S T)
    {μ : Cardinal.{u}} (hμ : μ ∈ T) : μ ∈ S :=
  h.1 hμ

/-- Countable-sup closure of a tail: a strictly increasing sequence in the tail has
`sSup` still above the threshold. -/
theorem countablySupClosed_tail {T : Set Cardinal.{u}} (h : CountablySupClosed T)
    (α : Cardinal.{u}) : CountablySupClosed (eligibleTail T α) where
  sup f hf hstrict := by
    have hfT : ∀ n, f n ∈ T := fun n => (hf n).1
    refine ⟨h.sup f hfT hstrict, ?_⟩
    exact (hf 0).2.trans <| le_csSup bddAbove_of_small (mem_range_self 0)

/-- Unboundedness of a tail: pick above `max(κ, α)`. -/
theorem unbounded_tail {T : Set Cardinal.{u}}
    (hunb : ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ T) (α κ : Cardinal.{u}) :
    ∃ μ, κ ≤ μ ∧ μ ∈ eligibleTail T α := by
  obtain ⟨μ, hle, hμ⟩ := hunb (κ ⊔ α)
  exact ⟨μ, le_sup_left.trans hle, hμ, le_sup_right.trans hle⟩

/-- Convention 5.3: a threshold only removes an initial segment. -/
theorem tail {S T : Set Cardinal.{u}} (h : EligibleSubclass S T) (α : Cardinal.{u}) :
    EligibleSubclass S (eligibleTail T α) := by
  refine ⟨fun μ hμ => h.1 hμ.1, fun κ => unbounded_tail h.2.1 α κ,
    countablySupClosed_tail h.2.2 α⟩

/-- Prop 5.7 convenience: given an eligible subclass and a naming threshold, the tail
above that threshold remains an eligible subclass. -/
theorem aboveNamingThreshold {S T0 : Set Cardinal.{u}}
    (hT0 : EligibleSubclass S T0) (α : Cardinal.{u}) :
    EligibleSubclass S (eligibleTail T0 α) :=
  tail hT0 α

/-- Climb a countable strictly increasing sequence inside an unbounded class `T`. -/
noncomputable def climb (T : Set Cardinal.{u})
    (hunb : ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ T) (κ : Cardinal.{u}) :
    ℕ → Cardinal.{u}
  | 0 => Classical.choose (hunb κ)
  | n + 1 => Classical.choose (hunb (Order.succ (climb T hunb κ n)))

theorem climb_mem {T : Set Cardinal.{u}}
    (hunb : ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ T) (κ : Cardinal.{u}) (n : ℕ) :
    climb T hunb κ n ∈ T := by
  induction n with
  | zero =>
    exact (Classical.choose_spec (hunb κ)).2
  | succ n _ =>
    exact (Classical.choose_spec (hunb (Order.succ (climb T hunb κ n)))).2

theorem climb_ge {T : Set Cardinal.{u}}
    (hunb : ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ T) (κ : Cardinal.{u}) :
    κ ≤ climb T hunb κ 0 :=
  (Classical.choose_spec (hunb κ)).1

theorem climb_strictMono {T : Set Cardinal.{u}}
    (hunb : ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ T) (κ : Cardinal.{u}) :
    StrictMono (climb T hunb κ) :=
  strictMono_nat_of_lt_succ fun n => by
    have hle : Order.succ (climb T hunb κ n) ≤ climb T hunb κ (n + 1) :=
      (Classical.choose_spec (hunb (Order.succ (climb T hunb κ n)))).1
    exact (Order.lt_succ _).trans_le hle

/-- The countable supremum of a strictly increasing sequence in `T` is a limit point of `T`. -/
theorem sSup_range_mem_Lim {T : Set Cardinal.{u}}
    (f : ℕ → Cardinal.{u}) (hf : ∀ n, f n ∈ T) (hstrict : StrictMono f) :
    sSup (range f) ∈ Lim T := by
  let μ : Cardinal.{u} := sSup (range f)
  have hle_ci : ∀ n, f n ≤ μ := fun n => le_csSup bddAbove_of_small (mem_range_self n)
  have hlt : ∀ n, f n < μ := fun n =>
    (hstrict (Nat.lt_succ_self n)).trans_le (hle_ci (n + 1))
  have hrange : range f ⊆ T ∩ Iio μ := by
    rintro _ ⟨n, rfl⟩
    exact ⟨hf n, hlt n⟩
  have hbdd : BddAbove (T ∩ Iio μ) := ⟨μ, fun _ ha => ha.2.le⟩
  have hle : sSup (T ∩ Iio μ) ≤ μ :=
    csSup_le ⟨f 0, hrange (mem_range_self 0)⟩ fun _ ha => ha.2.le
  have hge : μ ≤ sSup (T ∩ Iio μ) :=
    csSup_le_csSup hbdd (range_nonempty f) hrange
  exact ⟨hle.antisymm hge, lt_of_le_of_lt bot_le (hlt 0)⟩

/-- Limit-point refinement remains countably-sup-closed. -/
theorem countablySupClosed_lim {T : Set Cardinal.{u}} (h : CountablySupClosed T) :
    CountablySupClosed (T ∩ Lim T) where
  sup f hf hstrict := by
    have hfT : ∀ n, f n ∈ T := fun n => (hf n).1
    exact ⟨h.sup f hfT hstrict, sSup_range_mem_Lim f hfT hstrict⟩

/-- Convention 5.3: `{μ ∈ T : sup(T ∩ μ) = μ > 0}` stays unbounded and countably-sup-closed. -/
theorem lim {S T : Set Cardinal.{u}} (h : EligibleSubclass S T) :
    EligibleSubclass S (T ∩ Lim T) := by
  refine ⟨fun μ hμ => h.1 hμ.1, fun κ => ?_, countablySupClosed_lim h.2.2⟩
  let f := climb T h.2.1 κ
  have hf : ∀ n, f n ∈ T := climb_mem h.2.1 κ
  have hstrict : StrictMono f := climb_strictMono h.2.1 κ
  let μ : Cardinal.{u} := sSup (range f)
  have hμT : μ ∈ T := h.2.2.sup f hf hstrict
  have hμLim : μ ∈ Lim T := sSup_range_mem_Lim f hf hstrict
  refine ⟨μ, ?_, hμT, hμLim⟩
  exact (climb_ge h.2.1 κ).trans (le_csSup bddAbove_of_small (mem_range_self 0))

end EligibleSubclass

end
end AEC
