module

public import AEC.Section2.SupportTerm
public import Mathlib.Order.Compare

@[expose] public section

/-!
# Support profiles (Proposition 4.9)

A support profile over a parameter set records the labels of the new tuple, its formal
support order `T₀`, and the comparisons and coincidences of the formal support positions with
the old supporting positions.

* `SupportProfile.ofTerms`: the profile of a list of terms over an extension of the old
  positions; its formal support `T₀` is the set of positions used by the terms.
* `SupportProfile.Agree`: two profiles are the same along an identification of their index
  types: same labels, same order pattern of the formal support positions, same comparisons
  with the old positions.
* `SupportProfile.SameSlot`: two formal support positions lie in one strict slot over the old
  positions. The positions in one slot form a *cluster*.

`AEC.Section4.CompactPlacement` uses these for placements over an order presentation
(`Placement.profile`, `sameProfile_iff_agree`) and proves that there are at most `χ ^ σ = χ`
profiles (`mk_profileCode_le`).
-/

namespace AEC
section

universe u

/-- A support profile of a new tuple over a parameter set, as used in Proposition 4.9.
It records the labels of the new tuple, a formal linear order on its support, and the
comparison of each new position with each old supporting position. -/
structure SupportProfile (lab : Type u) (arity : lab → ℕ) (old : Type u) [LinearOrder old] where
  index : Type u
  label : index → lab
  support : Type u
  supportOrder : LinearOrder support
  arg : ∀ i, Fin (arity (label i)) → support
  arg_mono : ∀ i, haveI := supportOrder; StrictMono (arg i)
  compare : support → old → Ordering

/-- Two comparisons in linear orders agree exactly when they agree on `<` in both
directions (coincidence is the remaining case). -/
theorem compare_eq_compare_iff {X Y : Type u} [LinearOrder X] [LinearOrder Y] {a b : X}
    {c d : Y} : compare a b = compare c d ↔ (a < b ↔ c < d) ∧ (b < a ↔ d < c) := by
  constructor
  · intro h
    exact ⟨by rw [← compare_lt_iff_lt, ← compare_lt_iff_lt, h],
      by rw [← compare_gt_iff_gt, ← compare_gt_iff_gt, h]⟩
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy a b with h | h | h
    · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (h1.mp h)]
    · have hcd : c = d := by
        refine le_antisymm (not_lt.mp fun hlt => ?_) (not_lt.mp fun hlt => ?_)
        · exact absurd (h2.mpr hlt) (by rw [h]; exact lt_irrefl _)
        · exact absurd (h1.mpr hlt) (by rw [h]; exact lt_irrefl _)
      rw [compare_eq_iff_eq.mpr h, compare_eq_iff_eq.mpr hcd]
    · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (h2.mp h)]

namespace SupportProfile

variable {lab : Type u} {arity : lab → ℕ} {old : Type u} [LinearOrder old]

/-- The strict order of the formal support `T₀`. -/
def lt (p : SupportProfile lab arity old) (x y : p.support) : Prop :=
  letI := p.supportOrder
  x < y

/-- **The support profile of a list of terms** `z` over an order `J`, relative to the old
positions `e : old → J`. The formal support `T₀` is the set of positions used by the terms,
with the order induced from `J`; `compare` records the comparison (and coincidence) of every
formal support position with every old position. -/
def ofTerms {J : Type u} [LinearOrder J] {α : Type u} (z : α → SupportTerm lab arity J)
    (e : old → J) : SupportProfile lab arity old where
  index := α
  label a := (z a).label
  support := {x : J // ∃ a k, (z a).pos k = x}
  supportOrder := inferInstance
  arg a k := ⟨(z a).pos k, a, k, rfl⟩
  arg_mono a := fun _ _ h => (z a).increasing h
  compare x s := Ord.compare x.1 (e s)

/-- **The same profile**, along an identification `φ` of the index types: the labels agree,
the formal support positions have the same order pattern, and they are compared with the old
positions in the same way. -/
def Agree (p q : SupportProfile lab arity old) (φ : p.index → q.index) : Prop :=
  (∀ i, p.label i = q.label (φ i)) ∧
  (∀ i j k l (hk : k < arity (p.label i)) (hl : l < arity (p.label j))
    (hk' : k < arity (q.label (φ i))) (hl' : l < arity (q.label (φ j))),
    p.lt (p.arg i ⟨k, hk⟩) (p.arg j ⟨l, hl⟩) ↔
      q.lt (q.arg (φ i) ⟨k, hk'⟩) (q.arg (φ j) ⟨l, hl'⟩)) ∧
  (∀ i k (hk : k < arity (p.label i)) (hk' : k < arity (q.label (φ i))) (s : old),
    p.compare (p.arg i ⟨k, hk⟩) s = q.compare (q.arg (φ i) ⟨k, hk'⟩) s)

/-- Two formal support positions lie in the same strict slot over the old positions: the
same old positions are below them. The positions in one slot form a *cluster*. -/
def SameSlot (p : SupportProfile lab arity old) (x y : p.support) : Prop :=
  ∀ s, p.compare x s = Ordering.gt ↔ p.compare y s = Ordering.gt

end SupportProfile

end
end AEC
