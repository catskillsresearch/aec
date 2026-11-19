module

public import AEC.Section8.HullExtract83
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

/-!
# Audit: joint samples at every finite arity do not give an all-arity homogeneous sample

`Hull83.Joint P n c κ` (admitted samples of size `≥ κ`, homogeneous through arity `n`) for
every `n` and `κ` does not by itself supply one admitted infinite sample homogeneous in every
arity (hypothesis `hhom : ∀ n, Homog S n c` of `infra_83_mix_pair_into_saturated_sample`).

Counterexample (sorry-free): Boolean colors, `c ≡ true`, and the admitted class "there is a
bound `N` with `col m s = (m ≤ N)`". Every `Joint` instance holds (take `N = n`), but an
infinite admitted sample has an `(N+1)`-set colored `false`.  So the gap
`infra_83_all_arity_sample` cannot be closed from the abstract `Joint` interface alone; it
needs the specific admitted class, or the tuple-wise reformulation.
-/

namespace AEC
namespace Audit
namespace JointNoAllArity

universe u

open Cardinal Hull83

/-- Boolean colors at every arity. -/
abbrev C : ℕ → Type u := fun _ => ULift.{u} Bool

/-- The constant color `true`. -/
def c : (m : ℕ) → 0 < m → C.{u} m := fun _ _ => ⟨true⟩

/-- The admitted class: colors are `true` exactly up to some finite arity bound. -/
def Adm (S : ColorSample C.{u}) : Prop :=
  ∃ N : ℕ, ∀ (m : ℕ) (s : Finset S.α), s.card = m → S.col m s = ⟨decide (m ≤ N)⟩

/-- Every finite-arity joint instance holds. -/
theorem joint_all (n : ℕ) (κ : Cardinal.{u}) : Joint Adm n c κ := by
  refine ⟨@ColorSample.mk C κ.out (IsWellOrder.linearOrder WellOrderingRel)
    (fun m _ => ⟨decide (m ≤ n)⟩), ⟨n, fun m s _ => rfl⟩, ?_, ?_⟩
  · exact (Cardinal.mk_out κ).ge
  · intro m hm0 hmn s _
    simp [c, hmn]

/-- No infinite admitted sample is homogeneous in every arity. -/
theorem no_all_arity :
    ¬ ∃ S : ColorSample C.{u}, Adm S ∧ ℵ₀ ≤ #S.α ∧ ∀ n, Homog S n c := by
  rintro ⟨S, ⟨N, hN⟩, hinf, hhom⟩
  have : Infinite S.α := Cardinal.infinite_iff.mpr hinf
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq S.α (N + 1)
  have h1 := hhom (N + 1) (N + 1) (Nat.succ_pos N) le_rfl s hs
  rw [hN (N + 1) s hs] at h1
  simp [c] at h1

end JointNoAllArity
end Audit
end AEC
