module

public import AEC.Section2.FiniteHull
public import Mathlib.Order.SuccPred.Basic
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

noncomputable local instance instDecidablePropEnumeration (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The ordinals below the initial ordinal of `LS(K)`. Every hull of size at most `LS(K)`
is enumerated by this type. -/
abbrev Enum (K : AbstractElementaryClass.{u}) := (ls K).ord.ToType

theorem enum_card (K : AbstractElementaryClass.{u}) : #(Enum K) = ls K :=
  Cardinal.mk_ord_toType _

theorem enum_noMax (K : AbstractElementaryClass.{u}) : NoMaxOrder (Enum K) :=
  Cardinal.noMaxOrder (isLSBound_ls K).1

theorem enum_nonempty (K : AbstractElementaryClass.{u}) : Nonempty (Enum K) := by
  rw [← Cardinal.mk_ne_zero_iff, enum_card]
  exact ne_of_gt ((natCast_lt_aleph0 (n := 0)).trans_le (isLSBound_ls K).1)

/-- The `n`-th element of the enumeration order. -/
noncomputable def enumNth (K : AbstractElementaryClass.{u}) : ℕ → Enum K
  | 0 => WellFoundedLT.min Set.univ ⟨Classical.choice (enum_nonempty K), Set.mem_univ _⟩
  | n + 1 => Order.succ (enumNth K n)

theorem enumNth_succ_lt (K : AbstractElementaryClass.{u}) (n : ℕ) :
    enumNth K n < enumNth K (n + 1) := by
  haveI : NoMaxOrder (Enum K) := enum_noMax K
  have hlt : enumNth K n < Order.succ (enumNth K n) := Order.lt_succ (enumNth K n)
  simpa [enumNth] using hlt

theorem enumNth_strictMono (K : AbstractElementaryClass.{u}) : StrictMono (enumNth K) := by
  intro a b hlt
  induction b generalizing a with
  | zero => exact (Nat.not_lt_zero a hlt).elim
  | succ b ih =>
      cases lt_or_eq_of_le (Nat.le_of_lt_succ hlt) with
      | inl h => exact (ih h).trans (enumNth_succ_lt K b)
      | inr h =>
          subst h
          exact enumNth_succ_lt K a

/-- The first `n` enumeration names. -/
noncomputable def slot (K : AbstractElementaryClass.{u}) (n : ℕ) (i : Fin n) : Enum K :=
  enumNth K i.1

theorem slot_injective (K : AbstractElementaryClass.{u}) (n : ℕ) :
    Function.Injective (slot K n) :=
  fun i j hij => Fin.ext ((enumNth_strictMono K).injective hij)

/-- An enumeration name among the first `n`. -/
abbrev inSlot (K : AbstractElementaryClass.{u}) (n : ℕ) (e : Enum K) : Prop :=
  ∃ i : Fin n, e = slot K n i

theorem slot_card (K : AbstractElementaryClass.{u}) (n : ℕ) :
    #({e : Enum K // inSlot K n e}) = n := by
  apply le_antisymm
  · have hle : #({e : Enum K // inSlot K n e}) ≤ #(ULift.{u} (Fin n)) :=
      mk_le_of_injective (f := fun e : {e : Enum K // inSlot K n e} =>
        ULift.up (Classical.choose e.2)) <| by
        intro e₁ e₂ h
        apply Subtype.ext
        have hidx : Classical.choose e₁.2 = Classical.choose e₂.2 := ULift.up_injective h
        rw [Classical.choose_spec e₁.2, Classical.choose_spec e₂.2, hidx]
    rw [mk_uLift, mk_fin, lift_natCast] at hle
    exact hle
  · have hge : #(ULift.{u} (Fin n)) ≤ #({e : Enum K // inSlot K n e}) :=
      mk_le_of_injective (f := fun i : ULift.{u} (Fin n) =>
        (⟨slot K n i.down, ⟨i.down, rfl⟩⟩ : {e : Enum K // inSlot K n e})) <| by
        intro i j hij
        apply ULift.ext
        exact slot_injective K n (congrArg Subtype.val hij)
    rw [mk_uLift, mk_fin, lift_natCast] at hge
    exact hge

/-- Names outside the first `n` still have cardinality `LS(K)`. -/
theorem complement_card (K : AbstractElementaryClass.{u}) (n : ℕ) :
    #({e : Enum K // ¬ inSlot K n e}) = ls K := by
  let slots : Set (Enum K) := {e | inSlot K n e}
  have hsum := mk_sum_compl slots
  have hslots : #slots = n := slot_card K n
  rw [hslots, enum_card] at hsum
  have hall : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hcomp : #(slotsᶜ : Set (Enum K)) = #({e : Enum K // ¬ inSlot K n e}) := rfl
  rw [hcomp] at hsum
  have hinf : aleph0 ≤ #({e : Enum K // ¬ inSlot K n e}) := by
    by_contra hsmall
    have hlt : #({e : Enum K // ¬ inSlot K n e}) < aleph0 := lt_of_not_ge hsmall
    have hsum_small : (n : Cardinal) + #({e : Enum K // ¬ inSlot K n e}) < aleph0 :=
      add_lt_aleph0 natCast_lt_aleph0 hlt
    rw [hsum] at hsum_small
    exact not_lt_of_ge hall hsum_small
  rw [add_eq_max' hinf] at hsum
  have hn : (n : Cardinal) ≤ #({e : Enum K // ¬ inSlot K n e}) :=
    natCast_lt_aleph0.le.trans hinf
  rw [max_eq_right hn] at hsum
  exact hsum

variable {K : AbstractElementaryClass.{u}}

/-- An injection of a small nonempty set into the enumeration names outside the first `n`. -/
noncomputable def enumRest {α : Type u} (hα : #α ≤ ls K) (n : ℕ) [Nonempty α] :
    α ↪ {e : Enum K // ¬ inSlot K n e} :=
  Classical.choice ((le_def α _).mp (hα.trans_eq (complement_card K n).symm))

/-- A surjection from the enumeration onto a nonempty set of size at most `LS(K)`,
sending the first `n` names to a prescribed injective tuple. -/
noncomputable def enumOf {α : Type u} (hα : #α ≤ ls K) {n : ℕ}
    (seed : Fin n → α) (_hseed : Function.Injective seed) [Nonempty α] : Enum K → α :=
  fun e =>
    if h : inSlot K n e then seed (Classical.choose h)
    else Function.invFun (enumRest hα n) ⟨e, h⟩

theorem enumOf_slot {α : Type u} (hα : #α ≤ ls K) {n : ℕ}
    (seed : Fin n → α) (hseed : Function.Injective seed) [Nonempty α] (i : Fin n) :
    enumOf hα seed hseed (slot K n i) = seed i := by
  have h : inSlot K n (slot K n i) := ⟨i, rfl⟩
  simp only [enumOf, dif_pos h]
  have hidx : Classical.choose h = i :=
    slot_injective K n (Classical.choose_spec h).symm
  rw [hidx]

theorem enumRest_irrel {α : Type u} (hα hα' : #α ≤ ls K) (n : ℕ) [Nonempty α] :
    enumRest hα n = enumRest hα' n := by
  unfold enumRest
  exact congrArg Classical.choice (Subsingleton.elim _ _)

theorem enumOf_congr {α : Type u} (hα hα' : #α ≤ ls K) {n : ℕ}
    {seed seed' : Fin n → α} (hseed : Function.Injective seed)
    (hseed' : Function.Injective seed') (hs : seed = seed') [Nonempty α] :
    enumOf hα seed hseed = enumOf hα' seed' hseed' := by
  subst hs
  funext e
  unfold enumOf
  split_ifs with h
  · rfl
  · rw [enumRest_irrel hα hα']

/-- An enumeration is unchanged by transporting its carrier along an equality, and by
transporting the finite seed along an equality of its length. -/
theorem enumOf_point_heq {α β : Type u} (hαβ : α = β) {n m : ℕ} (hnm : n = m)
    (hα : #α ≤ ls K) (hβ : #β ≤ ls K) {seed : Fin n → α} {seed' : Fin m → β}
    (hseed : Function.Injective seed) (hseed' : Function.Injective seed')
    (hs : ∀ i : Fin n, HEq (seed i) (seed' (Fin.cast hnm i)))
    [Nonempty α] [Nonempty β] (η : Enum K) :
    HEq (enumOf hα seed hseed η) (enumOf hβ seed' hseed' η) := by
  subst hαβ
  subst hnm
  have hseedeq : seed = seed' := by
    funext i
    exact eq_of_heq (hs i)
  rw [enumOf_congr hα hβ hseed hseed' hseedeq]

theorem enumOf_surjective {α : Type u} (hα : #α ≤ ls K) {n : ℕ}
    (seed : Fin n → α) (hseed : Function.Injective seed) [Nonempty α] :
    Function.Surjective (enumOf hα seed hseed) := by
  intro a
  refine ⟨(enumRest hα n a).1, ?_⟩
  have hnot : ¬ inSlot K n (enumRest hα n a).1 := (enumRest hα n a).2
  rw [enumOf, dif_neg hnot]
  have hsub : (⟨(enumRest hα n a).1, hnot⟩ : {e : Enum K // ¬ inSlot K n e}) =
      enumRest hα n a := Subtype.eta _ _
  rw [hsub]
  exact Function.leftInverse_invFun (enumRest hα n).injective a

end
end AEC
