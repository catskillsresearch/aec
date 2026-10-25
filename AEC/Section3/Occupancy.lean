module

public import AEC.Section3.StrictSlot

@[expose] public section

namespace AEC
section

universe u


/-- A strict slot is occupied when it is nonempty. -/
def Occupied {α : Type u} [LinearOrder α] (lower upper : Set α) : Prop :=
  (strictSlot lower upper).Nonempty

end
end AEC
