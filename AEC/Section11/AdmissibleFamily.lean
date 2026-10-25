module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fintype.Fin

@[expose] public section

namespace AEC
section

universe u

/-- Push a label along the inclusion of the first `n` axes into `n + 1` axes. -/
def castUp (n : ℕ) (s : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  s.map Fin.castSuccEmb

/-- Add the new last axis to a label. -/
def withLast (n : ℕ) (s : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  insert (Fin.last n) (s.map Fin.castSuccEmb)

/-- `Q` is upward closed in `L`. -/
def UpwardClosed {n : ℕ} (L Q : Set (Finset (Fin n))) : Prop :=
  ∀ s t, s ∈ Q → s ⊆ t → t ∈ L → t ∈ Q

/-- The family obtained by adding a last axis, with new labels `s ∪ {k}` for `s ∈ Q`. -/
def extendFamily (n : ℕ) (L Q : Set (Finset (Fin n))) : Set (Finset (Fin (n + 1))) :=
  {t | ∃ s, s ∈ L ∧ t = castUp n s} ∪ {t | ∃ s, s ∈ Q ∧ t = withLast n s}

/-- **Definition 11.1.** An admissible family of active labels. On no axes the family is `{∅}`.
At a new last axis one chooses an upward closed subset `Q` of the previous family and adds
`s ∪ {k}` for each `s ∈ Q`. -/
inductive Admissible : (n : ℕ) → Set (Finset (Fin n)) → Prop
  | nil : Admissible 0 ({∅} : Set (Finset (Fin 0)))
  | step {n : ℕ} {L Q : Set (Finset (Fin n))} :
      Admissible n L → Q ⊆ L → UpwardClosed L Q →
      Admissible (n + 1) (extendFamily n L Q)

open Finset

theorem castUp_union (n : ℕ) (s t : Finset (Fin n)) :
    castUp n (s ∪ t) = castUp n s ∪ castUp n t := by
  simp [castUp, map_union]

theorem withLast_union (n : ℕ) (s t : Finset (Fin n)) :
    withLast n (s ∪ t) = withLast n s ∪ withLast n t := by
  simp only [withLast, map_union]
  ext x
  simp only [mem_insert, mem_union]
  tauto

theorem castUp_union_withLast (n : ℕ) (s t : Finset (Fin n)) :
    castUp n s ∪ withLast n t = withLast n (s ∪ t) := by
  simp only [withLast, castUp, map_union]
  ext x
  simp only [mem_insert, mem_union]
  tauto

theorem castUp_mono {n : ℕ} {s t : Finset (Fin n)} (h : s ⊆ t) :
    castUp n s ⊆ castUp n t := by
  intro x hx
  simp only [castUp, mem_map] at hx ⊢
  obtain ⟨i, hi, rfl⟩ := hx
  exact ⟨i, h hi, rfl⟩

theorem withLast_mono {n : ℕ} {s t : Finset (Fin n)} (h : s ⊆ t) :
    withLast n s ⊆ withLast n t := by
  intro x hx
  simp only [withLast, mem_insert, mem_map, Fin.castSuccEmb_apply] at hx ⊢
  rcases hx with rfl | ⟨i, hi, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, h hi, rfl⟩

theorem last_mem_withLast (n : ℕ) (s : Finset (Fin n)) :
    Fin.last n ∈ withLast n s := by
  simp [withLast]

theorem last_not_mem_castUp (n : ℕ) (s : Finset (Fin n)) :
    Fin.last n ∉ castUp n s := by
  intro h
  simp only [castUp, mem_map] at h
  obtain ⟨i, -, hi⟩ := h
  rw [Fin.castSuccEmb_apply] at hi
  exact lt_irrefl _ (hi ▸ Fin.castSucc_lt_last i)

/-- The axes of `t` other than the last one. -/
def toOld (n : ℕ) (t : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n => i.castSucc ∈ t

theorem mem_toOld {n : ℕ} {t : Finset (Fin (n + 1))} {i : Fin n} :
    i ∈ toOld n t ↔ i.castSucc ∈ t := by
  simp [toOld]

theorem toOld_mono {n : ℕ} {s t : Finset (Fin (n + 1))} (h : s ⊆ t) :
    toOld n s ⊆ toOld n t := by
  intro i hi
  exact mem_toOld.mpr (h (mem_toOld.mp hi))

theorem toOld_castUp {n : ℕ} (s : Finset (Fin n)) : toOld n (castUp n s) = s := by
  ext i
  simp only [mem_toOld, castUp, mem_map, Fin.castSuccEmb_apply]
  constructor
  · rintro ⟨j, hj, hji⟩
    exact Fin.castSucc_injective _ hji ▸ hj
  · intro hi
    exact ⟨i, hi, rfl⟩

theorem toOld_withLast {n : ℕ} (s : Finset (Fin n)) : toOld n (withLast n s) = s := by
  ext i
  simp only [mem_toOld, withLast, mem_insert, mem_map, Fin.castSuccEmb_apply]
  constructor
  · rintro (hlast | ⟨j, hj, hji⟩)
    · exact (lt_irrefl _ (hlast.symm ▸ Fin.castSucc_lt_last i)).elim
    · exact Fin.castSucc_injective _ hji ▸ hj
  · intro hi
    exact Or.inr ⟨i, hi, rfl⟩

theorem castUp_toOld_subset {n : ℕ} (t : Finset (Fin (n + 1))) :
    castUp n (toOld n t) ⊆ t := by
  intro x hx
  simp only [castUp, mem_map, Fin.castSuccEmb_apply] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  exact mem_toOld.mp hi

theorem mem_extendFamily {n : ℕ} {L Q : Set (Finset (Fin n))} {t : Finset (Fin (n + 1))} :
    t ∈ extendFamily n L Q ↔
      (∃ s, s ∈ L ∧ t = castUp n s) ∨ ∃ s, s ∈ Q ∧ t = withLast n s := by
  simp [extendFamily, Set.mem_union]

theorem Admissible.empty_mem {n : ℕ} {L : Set (Finset (Fin n))} (h : Admissible n L) :
    ∅ ∈ L := by
  induction h with
  | nil => simp
  | step hL hQ hup ih =>
    exact Or.inl ⟨∅, ih, by simp [castUp]⟩

theorem Admissible.union_mem {n : ℕ} {L : Set (Finset (Fin n))} (h : Admissible n L)
    {s t : Finset (Fin n)} (hs : s ∈ L) (ht : t ∈ L) : s ∪ t ∈ L := by
  induction h with
  | nil =>
    simp only [Set.mem_singleton_iff] at hs ht
    simp [hs, ht]
  | step hL hQ hup ih =>
    rcases mem_extendFamily.mp hs with ⟨s0, hs0, rfl⟩ | ⟨s0, hs0, rfl⟩
    <;> rcases mem_extendFamily.mp ht with ⟨t0, ht0, rfl⟩ | ⟨t0, ht0, rfl⟩
    · exact Or.inl ⟨s0 ∪ t0, ih hs0 ht0, castUp_union _ _ _ |>.symm⟩
    · exact Or.inr ⟨s0 ∪ t0,
        hup t0 (s0 ∪ t0) ht0 subset_union_right (ih hs0 (hQ ht0)),
        castUp_union_withLast _ _ _⟩
    · exact Or.inr ⟨s0 ∪ t0,
        hup s0 (s0 ∪ t0) hs0 subset_union_left (ih (hQ hs0) ht0), by
          rw [union_comm, castUp_union_withLast, union_comm]⟩
    · exact Or.inr ⟨s0 ∪ t0,
        hup s0 (s0 ∪ t0) hs0 subset_union_left (ih (hQ hs0) (hQ ht0)),
        withLast_union _ _ _ |>.symm⟩

end
end AEC
