module

public import Mathlib.ModelTheory.Basic
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Lemma 8.3: the mark as designated terms

The prescription fixes the arity `n` of the mark (`Pr.arity : idx ≃ Fin n`), so the mark is
named by `n` constant symbols.  A set containing the mark values is closed under them, and the
constants realize the mark.
-/

@[expose] public section

universe u

open FirstOrder FirstOrder.Language Cardinal

namespace AEC
namespace Mark83

/-- `n` mark constants. -/
def markLang (n : ℕ) : Language.{u, u} where
  Functions k := {_i : ULift.{u} (Fin n) // k = 0}
  Relations _ := PEmpty

/-- The mark constants interpreted by `m`. -/
@[instance_reducible]
def markStr {n : ℕ} {N : Type u} (m : Fin n → N) : (markLang.{u} n).Structure N where
  funMap := fun f _ => m f.1.down
  RelMap := fun r => PEmpty.elim r

/-- A set containing the mark is closed under the mark constants. -/
theorem mark_mem {n : ℕ} {N : Type u} (m : Fin n → N) {S : Set N} (hS : ∀ i, m i ∈ S)
    {k : ℕ} (f : (markLang.{u} n).Functions k) (x : Fin k → N) :
    @Structure.funMap _ _ (markStr m) k f x ∈ S :=
  hS _

/-- The mark constants realize the mark. -/
theorem mark_realize {n : ℕ} {N : Type u} (m : Fin n → N) (i : Fin n) :
    @Structure.funMap _ _ (markStr m) 0 ⟨⟨i⟩, rfl⟩ Fin.elim0 = m i :=
  rfl

/-- Finitely many mark constants. -/
theorem markLang_card (n : ℕ) : #(Σ k, (markLang.{u} n).Functions k) ≤ ℵ₀ := by
  refine (mk_le_of_injective (f := fun a : (Σ k, (markLang.{u} n).Functions k) => a.2.1)
    ?_).trans (by simp)
  rintro ⟨k, ⟨i⟩, hi⟩ ⟨l, ⟨j⟩, hj⟩ h
  simp only [ULift.up.injEq] at h
  subst h hi hj
  rfl

end Mark83
end AEC
