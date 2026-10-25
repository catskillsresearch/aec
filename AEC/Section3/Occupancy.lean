module

public import AEC.Section3.StrictSlot

@[expose] public section

namespace AEC
section

universe u v


/-- A strict slot is occupied when it is nonempty. -/
def Occupied {α : Type u} [LinearOrder α] (lower upper : Set α) : Prop :=
  (strictSlot lower upper).Nonempty

/-- Strict slots over a sequence are occupied in the same pattern. -/
def SameSlotOccupancy {ι α : Type v} [LinearOrder α] (xs ys : ι → α) : Prop :=
  ∀ (lower upper : Set ι),
    (∀ i ∈ lower, ∀ j ∈ upper, xs i < xs j) →
    (∀ i ∈ lower, ∀ j ∈ upper, ys i < ys j) →
    (Occupied (Set.image xs lower) (Set.image xs upper) ↔
      Occupied (Set.image ys lower) (Set.image ys upper))

end
end AEC
