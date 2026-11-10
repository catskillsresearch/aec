module

public import AEC.Section3.AdditivelyIndecomposable
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Exponential

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- Proof of Lemma 3.10: the additively indecomposable ordinals `δ < κ⁺` with `|δ| = κ` and
`cf(δ) = τ` are cofinal in `κ⁺`, for infinite `κ` and infinite regular `τ ≤ κ`. The witness is
`ω ^ (α + κ + τ)`. Kept in its own file so that the elimination argument can use it before
`Results.lean`. -/
theorem indecomposable_cofinal (κ τ : Cardinal.{u}) (hκ : aleph0 ≤ κ) (hτ : aleph0 ≤ τ)
    (hreg : Cardinal.IsRegular τ) (hle : τ ≤ κ) :
    ∀ α : _root_.Ordinal.{u}, α < (Order.succ κ).ord →
      ∃ δ : _root_.Ordinal.{u}, α ≤ δ ∧ δ < (Order.succ κ).ord ∧
        AdditivelyIndecomposable δ ∧ δ.card = κ ∧ Ordinal.cof δ = τ := by
  intro α hα
  have hαcard : α.card ≤ κ := Cardinal.card_le_iff.mpr hα
  let ρ : _root_.Ordinal.{u} := α + κ.ord + τ.ord
  have hτlim : Order.IsSuccLimit τ.ord := Cardinal.isSuccLimit_ord hτ
  have hρlim : Order.IsSuccLimit ρ := Ordinal.isSuccLimit_add (α + κ.ord) hτlim
  have hρcard : ρ.card = κ := by
    have hsum : (α + κ.ord).card = κ := by
      rw [Ordinal.card_add, Cardinal.card_ord, add_comm, Cardinal.add_eq_max hκ,
        max_eq_left hαcard]
    rw [Ordinal.card_add, Cardinal.card_ord, hsum, Cardinal.add_eq_max hκ, max_eq_left hle]
  have hcofρ : Ordinal.cof ρ = τ := by
    rw [Ordinal.cof_add (α + κ.ord) hτlim.ne_bot, hreg.cof_ord]
  refine ⟨Ordinal.omega0 ^ ρ, ?_, ?_, ⟨Ordinal.isPrincipal_add_omega0_opow ρ⟩, ?_, ?_⟩
  · exact (le_self_add : α ≤ α + κ.ord).trans
      ((le_self_add : α + κ.ord ≤ α + κ.ord + τ.ord).trans
        (Ordinal.right_le_opow ρ Ordinal.one_lt_omega0))
  · apply Cardinal.card_le_iff.mp
    rw [Ordinal.card_omega0_opow hρlim.ne_bot, hρcard, max_eq_right hκ]
  · rw [Ordinal.card_omega0_opow hρlim.ne_bot, hρcard, max_eq_right hκ]
  · rw [Ordinal.cof_map_of_isNormal (Ordinal.isNormal_opow Ordinal.one_lt_omega0) hρlim, hcofρ]

end
end AEC
