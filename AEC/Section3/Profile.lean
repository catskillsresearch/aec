module

public import AEC.Section3.OrbitName

@[expose] public section

namespace AEC
section

universe u

/-- The profile of a presentation, in the sense of Section 3.3: the named orbit-arrow
relation, together with the partial function sending each realized presentation record
to its orbit name. -/
structure Profile (Record Name : Type u) where
  arrow : Name → Name → Prop
  arrow_refl : ∀ n, arrow n n
  arrow_trans : ∀ a b c, arrow a b → arrow b c → arrow a c
  assign : Record → Option Name

end
end AEC
