module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fin.Embedding

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

end
end AEC
