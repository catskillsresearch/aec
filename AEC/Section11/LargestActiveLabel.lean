module

public import AEC.Section11.AdmissibleFamily

@[expose] public section

namespace AEC
section

/-- **Lemma 11.2.** `u` is the largest active label contained in `t`. -/
def IsLargestActive {n : ℕ} (L : Set (Finset (Fin n))) (t u : Finset (Fin n)) : Prop :=
  u ∈ L ∧ u ⊆ t ∧ ∀ s, s ∈ L → s ⊆ t → s ⊆ u

end
end AEC
