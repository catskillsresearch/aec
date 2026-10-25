module

public import AEC.Section1.AbstractElementaryClass

@[expose] public section

namespace AEC
section

universe u

/-- Convention 5.1. A system shape has finitely many vertices and a specification of which
pairs of vertices carry a map. -/
structure SystemShape where
  Vertex : Type u
  vertexFinite : Finite Vertex
  specified : Vertex → Vertex → Prop

end
end AEC
