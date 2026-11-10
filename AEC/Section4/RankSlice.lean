module

public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Family
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Cardinal.Basic

/-!
# Rank-slice layer for Lemma 4.7

Codes `U ∩ V_β` as a `Type u` family `Slice` of vectors with values in `β.ToType`,
defines the escape rank `h(β)`, builds a well-founded ladder, and produces a coordinatewise
descent family for `pair_coloring_glue`.
-/

@[expose] public section

namespace AEC
section

universe u

open Classical Ordinal

/-- Coordinatewise domination. -/
def VecLe {C : Type u} (f g : C → Ordinal.{u}) : Prop :=
  ∀ c, f c ≤ g c

/-- All values of `f` lie strictly below `β`. -/
def ValuesBelow {C : Type u} (β : Ordinal.{u}) (f : C → Ordinal.{u}) : Prop :=
  ∀ c, f c < β

/-- Type-`u` coding of coordinates `< β`. -/
def BoundVec (C : Type u) (β : Ordinal.{u}) : Type u :=
  C → β.ToType

/-- Decode a bound vector to an ordinal vector. -/
noncomputable def BoundVec.decode {C : Type u} {β : Ordinal.{u}}
    (f : BoundVec C β) : C → Ordinal.{u} :=
  fun c => (f c : Ordinal.{u})

theorem BoundVec.decode_lt {C : Type u} {β : Ordinal.{u}} (f : BoundVec C β) (c : C) :
    BoundVec.decode f c < β :=
  (ToType.toOrd (f c)).2

theorem BoundVec.decode_valuesBelow {C : Type u} {β : Ordinal.{u}} (f : BoundVec C β) :
    ValuesBelow β (BoundVec.decode f) :=
  BoundVec.decode_lt f

/-- Encode a values-below-`β` vector as a `BoundVec`. -/
noncomputable def BoundVec.encode {C : Type u} {β : Ordinal.{u}}
    (f : C → Ordinal.{u}) (hf : ValuesBelow β f) : BoundVec C β :=
  fun c => ToType.mk ⟨f c, hf c⟩

@[simp] theorem BoundVec.decode_encode {C : Type u} {β : Ordinal.{u}}
    (f : C → Ordinal.{u}) (hf : ValuesBelow β f) :
    BoundVec.decode (BoundVec.encode f hf) = f := by
  ext c
  simp [BoundVec.decode, BoundVec.encode, ToType.toOrd]

/-- `U ∩ V_β` as a `Type u` index of coded vectors. -/
def Slice (C : Type u) (holds : (C → Ordinal.{u}) → Prop) (β : Ordinal.{u}) : Type u :=
  { f : BoundVec C β // holds (BoundVec.decode f) }

noncomputable def Slice.decode {C : Type u} {holds : (C → Ordinal.{u}) → Prop}
    {β : Ordinal.{u}} (f : Slice C holds β) : C → Ordinal.{u} :=
  BoundVec.decode f.1

theorem Slice.decode_holds {C : Type u} {holds : (C → Ordinal.{u}) → Prop}
    {β : Ordinal.{u}} (f : Slice C holds β) : holds (Slice.decode f) :=
  f.2

theorem Slice.decode_valuesBelow {C : Type u} {holds : (C → Ordinal.{u}) → Prop}
    {β : Ordinal.{u}} (f : Slice C holds β) : ValuesBelow β (Slice.decode f) :=
  BoundVec.decode_valuesBelow f.1

/-- The slice generates every `holds`-vector upward. -/
def GeneratesFromSlice {C : Type u}
    (holds : (C → Ordinal.{u}) → Prop) (β : Ordinal.{u}) : Prop :=
  ∀ f, holds f → ∃ g : Slice C holds β, VecLe (Slice.decode g) f

/-- Positive packaging: a generating slice is already a Type-`u` witness family. -/
theorem lemma_4_7_of_slice {C : Type u} (holds : (C → Ordinal.{u}) → Prop)
    (β : Ordinal.{u}) (hgen : GeneratesFromSlice holds β) :
    ∃ (ι : Type u) (v : ι → C → Ordinal.{u}),
      (∀ i, holds (v i)) ∧
      ∀ f, holds f → ∃ i, ∀ c, v i c ≤ f c := by
  refine ⟨Slice C holds β, fun g => Slice.decode g, fun g => Slice.decode_holds g, ?_⟩
  intro f hf
  obtain ⟨g, hg⟩ := hgen f hf
  exact ⟨g, hg⟩

/-- If no slice generates, every rank has an escaping vector. -/
theorem exists_escape {C : Type u} (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β) (β : Ordinal.{u}) :
    ∃ f, holds f ∧ ∀ g : Slice C holds β, ¬ VecLe (Slice.decode g) f := by
  simpa [GeneratesFromSlice, not_forall, not_imp] using hnone β

noncomputable def escapeVec {C : Type u} (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β) (β : Ordinal.{u}) :
    C → Ordinal.{u} :=
  Classical.choose (exists_escape holds hnone β)

theorem escapeVec_holds {C : Type u} (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β) (β : Ordinal.{u}) :
    holds (escapeVec holds hnone β) :=
  (Classical.choose_spec (exists_escape holds hnone β)).1

theorem escapeVec_not_dominated {C : Type u} (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β) (β : Ordinal.{u})
    (g : Slice C holds β) :
    ¬ VecLe (Slice.decode g) (escapeVec holds hnone β) :=
  (Classical.choose_spec (exists_escape holds hnone β)).2 g

/-- Paper `h(β)`: strict bound past `β` and past the escape range. -/
noncomputable def escapeBound {C : Type u} (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β) (β : Ordinal.{u}) : Ordinal.{u} :=
  Order.succ (β ⊔ iSup (escapeVec holds hnone β))

theorem escapeVec_lt_escapeBound {C : Type u}
    (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β) (β : Ordinal.{u}) (c : C) :
    escapeVec holds hnone β c < escapeBound holds hnone β := by
  dsimp [escapeBound]
  exact (Ordinal.le_iSup (escapeVec holds hnone β) c).trans_lt <|
    (le_max_right β _).trans_lt (Order.lt_succ _)

theorem lt_escapeBound_of_lt_beta {C : Type u}
    (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β) {β γ : Ordinal.{u}} (hγ : γ < β) :
    γ < escapeBound holds hnone β := by
  dsimp [escapeBound]
  exact hγ.trans_le <| (le_max_left _ _).trans (Order.le_succ _)

/-- Ladder of ranks along a well-order: at `i`, take a strict upper bound of all earlier
`escapeBound`s. -/
noncomputable def boundLadder {C : Type u} (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β)
    {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] : ι → Ordinal.{u} :=
  wellFounded_lt.fix fun i (IH : ∀ j, j < i → Ordinal.{u}) =>
    sSup (Set.range fun j : { j : ι // j < i } =>
      Order.succ (escapeBound holds hnone (IH j.1 j.2)))

theorem boundLadder_eq {C : Type u} (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β)
    {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] (i : ι) :
    boundLadder holds hnone i =
      sSup (Set.range fun j : { j : ι // j < i } =>
        Order.succ (escapeBound holds hnone (boundLadder holds hnone j.1))) :=
  wellFounded_lt.fix_eq _ i

theorem escapeBound_lt_boundLadder_of_lt {C : Type u}
    (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β)
    {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] {i j : ι} (hij : i < j) :
    escapeBound holds hnone (boundLadder holds hnone i) < boundLadder holds hnone j := by
  rw [boundLadder_eq (i := j)]
  have hmem :
      Order.succ (escapeBound holds hnone (boundLadder holds hnone i)) ∈
        Set.range fun k : { k : ι // k < j } =>
          Order.succ (escapeBound holds hnone (boundLadder holds hnone k.1)) :=
    ⟨⟨i, hij⟩, rfl⟩
  exact (Order.lt_succ _).trans_le (le_csSup bddAbove_of_small hmem)

/-- Re-encode the escape at `i` as a slice vector at the later ladder rank `j`. -/
noncomputable def escapeAsSlice {C : Type u}
    (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β)
    {ι : Type u} [LinearOrder ι] [WellFoundedLT ι]
    {i j : ι} (hij : i < j) : Slice C holds (boundLadder holds hnone j) :=
  let f := escapeVec holds hnone (boundLadder holds hnone i)
  let hf : ValuesBelow (boundLadder holds hnone j) f :=
    fun c => (escapeVec_lt_escapeBound holds hnone _ c).trans
      (escapeBound_lt_boundLadder_of_lt holds hnone hij)
  ⟨BoundVec.encode f hf, by
    rw [BoundVec.decode_encode]
    exact escapeVec_holds holds hnone _⟩

theorem escapeAsSlice_decode {C : Type u}
    (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β)
    {ι : Type u} [LinearOrder ι] [WellFoundedLT ι]
    {i j : ι} (hij : i < j) :
    Slice.decode (escapeAsSlice holds hnone hij) =
      escapeVec holds hnone (boundLadder holds hnone i) := by
  dsimp [escapeAsSlice, Slice.decode]
  exact BoundVec.decode_encode _ _

/-- **Infra: rank-slice.** From “no generating slice at any rank”, a well-ordered index
carries holds-vectors with a strict coordinate descent on every increasing pair. -/
theorem ladder_descent_family {C : Type u} [Nonempty C]
    (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β)
    {ι : Type u} [LinearOrder ι] [WellFoundedLT ι] :
    ∃ u : ι → C → Ordinal.{u},
      (∀ i, holds (u i)) ∧
      ∀ ⦃i j : ι⦄, i < j → ∃ c, u j c < u i c := by
  classical
  let u : ι → C → Ordinal.{u} := fun i =>
    escapeVec holds hnone (boundLadder holds hnone i)
  refine ⟨u, fun i => escapeVec_holds holds hnone _, ?_⟩
  intro i j hij
  have hnot :
      ¬ VecLe (Slice.decode (escapeAsSlice holds hnone hij)) (u j) :=
    escapeVec_not_dominated holds hnone (boundLadder holds hnone j)
      (escapeAsSlice holds hnone hij)
  rw [escapeAsSlice_decode, show escapeVec holds hnone (boundLadder holds hnone i) = u i from rfl]
    at hnot
  simpa [VecLe, not_forall, not_le] using hnot

/-- If every Type-`u` family fails to dominate, then no slice generates. -/
theorem not_generates_of_no_type_u_witnesses {C : Type u}
    (holds : (C → Ordinal.{u}) → Prop)
    (hno : ¬ ∃ (ι : Type u) (v : ι → C → Ordinal.{u}),
        (∀ i, holds (v i)) ∧ ∀ f, holds f → ∃ i, ∀ c, v i c ≤ f c) :
    ∀ β, ¬ GeneratesFromSlice holds β := by
  intro β hgen
  exact hno (lemma_4_7_of_slice holds β hgen)

end
end AEC
