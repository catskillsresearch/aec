module

public import AEC.Section3.PresentationRecord
public import AEC.Section3.OrderEqualityDiagram
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace AEC
section

universe u

open Set

variable {lab flat flat' : Type u} {arity : lab → ℕ}
  [LinearOrder flat] [LinearOrder flat']

/-- Transport a cut along an order isomorphism. -/
def Cut.along (e : flat ≃o flat') (c : Cut flat) : Cut flat' where
  lower := e '' c.lower
  upper := e '' c.upper
  union_eq := by
    ext y
    constructor
    · rintro (⟨x, _, rfl⟩ | ⟨x, _, rfl⟩)
      · exact mem_univ _
      · exact mem_univ _
    · intro _
      obtain ⟨x, rfl⟩ := e.surjective y
      have hx : x ∈ c.lower ∪ c.upper := by simp [c.union_eq]
      rcases hx with hx | hx
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨x, hx, rfl⟩
  disjoint := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext y
    simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false]
    rintro ⟨⟨x, hx, rfl⟩, ⟨x', hx', hxx'⟩⟩
    have hxeq : x = x' := e.injective hxx'.symm
    subst hxeq
    exact Set.disjoint_left.mp c.disjoint hx hx'
  ordered := by
    intro a ha b hb
    rcases ha with ⟨a', ha', rfl⟩
    rcases hb with ⟨b', hb', rfl⟩
    exact (e.lt_iff_lt).mpr (c.ordered a' ha' b' hb')

/-- Two presentation records are the same when an index bijection preserves labels
and an order isomorphism of the flattened positions preserves arguments and occupancy. -/
def SameRecord (r : PresentationRecord lab arity flat)
    (s : PresentationRecord lab arity flat') : Prop :=
  ∃ (e : r.index ≃ s.index) (f : flat ≃o flat') (hlabel : ∀ i, r.label i = s.label (e i)),
    (∀ i (a : Fin (arity (r.label i))),
      f (r.arg i a) = s.arg (e i) (Fin.cast (congrArg arity (hlabel i)) a)) ∧
    (∀ c, r.occupied c ↔ s.occupied (c.along f))

end
end AEC
