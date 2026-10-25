module

public import AEC.Section5.SystemShape

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A system of shape `S`: one `K`-model at each vertex, and a `τ`-embedding along each
specified pair of vertices. An element that occurs in two vertices is two occurrences, related
by the specified map when that map is present. -/
structure SystemObject (K : AbstractElementaryClass.{u}) (S : SystemShape.{u}) where
  obj : S.Vertex → Model K.τ
  inK : ∀ v, K.Mem (obj v)
  edge : ∀ {i j}, S.specified i j → Language.Embedding K.τ (obj i).carrier (obj j).carrier
  edge_strong : ∀ {i j} (h : S.specified i j), K.Strong (edge h)

end
end AEC
