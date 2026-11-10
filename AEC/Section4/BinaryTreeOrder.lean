module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Order.PiLex
public import AEC.Section2.SmallModel

@[expose] public section

/-!
# Binary-tree parameters for Lemma 4.6

`treeHeight χ` is least infinite with `2^ε > χ`. The order carrier is
`Πₗ (Below ε), Fin 3`. Branches avoid the middle digit; there are `> χ` of them.
Dividers are indexed by `Below χ`.
-/

namespace AEC
section

universe u

open Cardinal Function

/-- Least infinite cardinal `ε` with `2^ε > χ`. -/
noncomputable def treeHeight (χ : Cardinal.{u}) : Cardinal.{u} :=
  sInf {ε : Cardinal.{u} | aleph0 ≤ ε ∧ χ < (2 : Cardinal.{u}) ^ ε}

private theorem treeHeight_set_nonempty (χ : Cardinal.{u}) :
    {ε : Cardinal.{u} | aleph0 ≤ ε ∧ χ < (2 : Cardinal.{u}) ^ ε}.Nonempty :=
  ⟨max aleph0 (Order.succ χ), le_max_left _ _,
    (cantor χ).trans_le
      (power_le_power_left two_ne_zero
        (le_trans (Order.le_succ χ) (le_max_right _ _)))⟩

theorem aleph0_le_treeHeight (χ : Cardinal.{u}) : aleph0 ≤ treeHeight χ :=
  (csInf_mem (treeHeight_set_nonempty χ)).1

theorem treeHeight_power_gt (χ : Cardinal.{u}) : χ < (2 : Cardinal.{u}) ^ treeHeight χ :=
  (csInf_mem (treeHeight_set_nonempty χ)).2

theorem treeHeight_minimal {χ ε : Cardinal.{u}} (hinf : aleph0 ≤ ε)
    (h : χ < (2 : Cardinal.{u}) ^ ε) : treeHeight χ ≤ ε :=
  csInf_le' ⟨hinf, h⟩

theorem treeHeight_le (χ : Cardinal.{u}) (hχ : aleph0 ≤ χ) : treeHeight χ ≤ χ :=
  treeHeight_minimal hχ (cantor χ)

theorem power_le_of_lt_treeHeight {χ κ : Cardinal.{u}} (hχ : aleph0 ≤ χ)
    (h : κ < treeHeight χ) : (2 : Cardinal.{u}) ^ κ ≤ χ := by
  by_cases hinf : aleph0 ≤ κ
  · by_contra hne
    exact not_lt_of_ge (treeHeight_minimal hinf (lt_of_not_ge hne)) h
  · obtain ⟨n, hn⟩ := lt_aleph0.1 (lt_of_not_ge hinf)
    subst hn
    have hlt : (2 : Cardinal.{u}) ^ n < aleph0 := by
      simpa [power_natCast, Nat.cast_pow] using
        (natCast_lt_aleph0 (n := (2 : ℕ) ^ n))
    exact hlt.le.trans hχ

/-- Lex digit space: `0 < 1 < 2` plays the role of `-1 < 0 < 1`. -/
def TreePoint (χ : Cardinal.{u}) : Type u :=
  Lex (Below (treeHeight χ) → Fin 3)

noncomputable instance TreePoint.instLinearOrder (χ : Cardinal.{u}) :
    LinearOrder (TreePoint χ) :=
  inferInstanceAs (LinearOrder (Lex (Below (treeHeight χ) → Fin 3)))

def IsBranch {χ : Cardinal.{u}} (p : TreePoint χ) : Prop :=
  ∀ i, (ofLex p) i ≠ 1

def TreeBranch (χ : Cardinal.{u}) : Type u := {p : TreePoint χ // IsBranch p}

def TreeDivider (χ : Cardinal.{u}) : Type u := Below χ

theorem mk_treeDivider_le (χ : Cardinal.{u}) : #(TreeDivider χ) ≤ χ :=
  le_of_eq (mk_ord_toType χ)

noncomputable def branchBit (b : Bool) : Fin 3 := if b then 2 else 0

theorem branchBit_ne_one (b : Bool) : branchBit b ≠ 1 := by
  dsimp [branchBit]; split_ifs <;> decide

noncomputable def branchOfBits {χ : Cardinal.{u}} (b : Below (treeHeight χ) → Bool) :
    TreeBranch χ :=
  ⟨toLex (branchBit ∘ b), fun i => branchBit_ne_one (b i)⟩

theorem mk_treeBranch_gt (χ : Cardinal.{u}) : χ < #(TreeBranch χ) := by
  have hinj : Function.Injective (branchOfBits (χ := χ)) := by
    intro b₁ b₂ h
    apply funext; intro i
    have hi := congrFun (congrArg (fun p : TreeBranch χ => ofLex p.val) h) i
    dsimp [branchOfBits, branchBit] at hi
    cases hb1 : b₁ i <;> cases hb2 : b₂ i
    · rfl
    · simp [hb1, hb2] at hi
    · simp [hb1, hb2] at hi
    · rfl
  have hle : #(Below (treeHeight χ) → Bool) ≤ #(TreeBranch χ) := mk_le_of_injective hinj
  have hcard : #(Below (treeHeight χ) → Bool) = (2 : Cardinal.{u}) ^ treeHeight χ := by
    rw [mk_arrow, mk_bool, mk_ord_toType]; simp
  exact (treeHeight_power_gt χ).trans_le (hcard.symm.le.trans hle)

/-- Exponent for `lemma46Chi`. -/
noncomputable def lemma46Mu (lsBound σ : Cardinal.{u}) : Cardinal.{u} :=
  lsBound + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) + σ

/-- `χ = 2^μ` for `μ = lsBound + 2^(2^σ) + σ`. -/
noncomputable def lemma46Chi (lsBound σ : Cardinal.{u}) : Cardinal.{u} :=
  (2 : Cardinal.{u}) ^ lemma46Mu lsBound σ

theorem lemma46Mu_ge_sigma (lsBound σ : Cardinal.{u}) : σ ≤ lemma46Mu lsBound σ := by
  dsimp [lemma46Mu]
  set a := lsBound + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ)
  exact (self_le_add_right σ a).trans (le_of_eq (add_comm σ a))

theorem lemma46Chi_power_eq (lsBound σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    lemma46Chi lsBound σ ^ σ = lemma46Chi lsBound σ := by
  dsimp [lemma46Chi]
  have hμinf : aleph0 ≤ lemma46Mu lsBound σ := hσ.trans (lemma46Mu_ge_sigma lsBound σ)
  have hσ0 : σ ≠ 0 := by
    intro h; rw [h] at hσ; exact (not_lt_of_ge hσ) aleph0_pos
  rw [← power_mul, mul_eq_left hμinf (lemma46Mu_ge_sigma lsBound σ) hσ0]

theorem lemma46Chi_bound (lsBound σ : Cardinal.{u}) :
    lsBound + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ lemma46Chi lsBound σ := by
  dsimp [lemma46Chi, lemma46Mu]
  exact (self_le_add_right
      (lsBound + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ)) σ).trans
    (cantor _).le

theorem aleph0_le_lemma46Chi (lsBound σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    aleph0 ≤ lemma46Chi lsBound σ :=
  (hσ.trans (lemma46Mu_ge_sigma lsBound σ)).trans (cantor _).le

end
end AEC
