module

public import AEC.Section11.AdmissibleFamily

@[expose] public section

namespace AEC
section

/-- **Lemma 11.2.** `u` is the largest active label contained in `t`. -/
def IsLargestActive {n : ℕ} (L : Set (Finset (Fin n))) (t u : Finset (Fin n)) : Prop :=
  u ∈ L ∧ u ⊆ t ∧ ∀ s, s ∈ L → s ⊆ t → s ⊆ u

open Finset

theorem Admissible.exists_largest {n : ℕ} {L : Set (Finset (Fin n))} (h : Admissible n L)
    (t : Finset (Fin n)) : ∃ u, IsLargestActive L t u := by
  induction h with
  | nil =>
    refine ⟨∅, ?_, empty_subset t, ?_⟩
    · simp
    · intro s hs _
      simp only [Set.mem_singleton_iff] at hs
      simp [hs]
  | @step n L Q hL hQ hup ih =>
    obtain ⟨u, huL, huSub, huMax⟩ := ih (toOld _ t)
    by_cases hlast : Fin.last _ ∈ t
    · by_cases huQ : u ∈ Q
      · refine ⟨withLast _ u, Or.inr ⟨u, huQ, rfl⟩, ?_, ?_⟩
        · rw [withLast]
          exact insert_subset hlast ((castUp_mono huSub).trans (castUp_toOld_subset t))
        · intro s hs hst
          rcases mem_extendFamily.mp hs with ⟨s0, hs0, rfl⟩ | ⟨s0, hs0, rfl⟩
          · have hs0Sub : s0 ⊆ toOld _ t := by
              intro i hi
              exact mem_toOld.mpr (hst (mem_map_of_mem _ hi))
            exact (castUp_mono (huMax s0 hs0 hs0Sub)).trans (subset_insert _ _)
          · have hs0Sub : s0 ⊆ u :=
              huMax s0 (hQ hs0) (by
                rw [← toOld_withLast (s := s0)]
                exact toOld_mono hst)
            exact withLast_mono hs0Sub
      · refine ⟨castUp _ u, Or.inl ⟨u, huL, rfl⟩,
          (castUp_mono huSub).trans (castUp_toOld_subset t), ?_⟩
        intro s hs hst
        rcases mem_extendFamily.mp hs with ⟨s0, hs0, rfl⟩ | ⟨s0, hs0, rfl⟩
        · have hs0Sub : s0 ⊆ toOld _ t := by
            intro i hi
            exact mem_toOld.mpr (hst (mem_map_of_mem _ hi))
          exact castUp_mono (huMax s0 hs0 hs0Sub)
        · have hs0Sub : s0 ⊆ u :=
            huMax s0 (hQ hs0) (by
              rw [← toOld_withLast (s := s0)]
              exact toOld_mono hst)
          exact (huQ (hup s0 u hs0 hs0Sub huL)).elim
    · refine ⟨castUp _ u, Or.inl ⟨u, huL, rfl⟩,
        (castUp_mono huSub).trans (castUp_toOld_subset t), ?_⟩
      intro s hs hst
      rcases mem_extendFamily.mp hs with ⟨s0, hs0, rfl⟩ | ⟨s0, hs0, rfl⟩
      · have hs0Sub : s0 ⊆ toOld _ t := by
          intro i hi
          exact mem_toOld.mpr (hst (mem_map_of_mem _ hi))
        exact castUp_mono (huMax s0 hs0 hs0Sub)
      · exact (hlast (hst (last_mem_withLast _ s0))).elim

end
end AEC
