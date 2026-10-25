module

public import AEC.Section5.SystemArrow
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A finite-support term template: a system for every nonempty linear order, and a system
arrow for every order embedding, by substitution of positions. -/
structure TermTemplate (K : AbstractElementaryClass.{u}) (S : SystemShape.{u}) where
  present : ∀ (I : Type u) [LinearOrder I] [Nonempty I], SystemObject K S
  onOrder : ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J],
    (I ↪o J) → SystemArrow K S (present I) (present J)
  onOrder_id : ∀ {I : Type u} [LinearOrder I] [Nonempty I] (v : S.Vertex)
    (x : ((present I).obj v).carrier),
    (onOrder (OrderIso.refl I).toOrderEmbedding).onVertex v x = x
  onOrder_comp : ∀ {I J P : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder P]
    [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P) (v : S.Vertex)
    (x : ((present I).obj v).carrier),
    (onOrder (f.trans g)).onVertex v x =
      (onOrder g).onVertex v ((onOrder f).onVertex v x)

end
end AEC
