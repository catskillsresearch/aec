module

public import AEC.Section5.WorkingScheme
public import Mathlib.Order.WellFounded

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- Definition 5.2(2), presentations. Well-order presentations of eligible cardinality are
compared to scheme objects by vertexwise language equivalence, and an order embedding of
well-orders of eligible cardinalities induces a permitted arrow between any objects at those
levels. (Every object is isomorphic to a well-order presentation by the empty-diagram clause of
the scheme, so it is enough to state the arrow condition for arbitrary objects.) -/
class HasPresentations {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (F : TermTemplate K S) : Prop where
  /-- At an eligible level, the vertex models of `F.present I` are language-equivalent to those of
  any scheme object whenever `#I` equals that level. -/
  present_equiv : ∀ {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (X : W.Object μ hμ)
    (I : Type u) [LinearOrder I] [Nonempty I],
    #I = μ →
    ∀ v, Nonempty (((F.present I).obj v).carrier ≃[K.τ]
      ((W.asSystem hμ X).obj v).carrier)
  /-- An order embedding of well-orders of eligible cardinalities induces a permitted arrow. -/
  wellOrder_arrow : ∀ {μ ν : Cardinal.{u}} (hμ : μ ∈ W.eligible) (hν : ν ∈ W.eligible)
    (I J : Type u) [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    [WellFoundedLT I] [WellFoundedLT J]
    (X : W.Object μ hμ) (Y : W.Object ν hν) (_f : I ↪o J),
    #I = μ → #J = ν →
    ∃ arr : SystemArrow K S (W.asSystem hμ X) (W.asSystem hν Y),
      W.permitted (X := X) (Y := Y) arr

/-- Definition 5.2(1), unions. A nonempty increasing chain of objects at one eligible level, whose
union has cardinality that level, is an object; inclusions are a cocone for the chain arrows; and a
chain that maps into an object at a larger eligible level has its union arrow into that object.

"All members of the chain map by the inclusions into one object `Z`": the family `toZ` is a
cocone over the chain arrows (`le i j ≫ toZ j = toZ i`). Without this hypothesis the clause,
applied to a two-element index with identity transition maps, would identify any two permitted
arrows `X → Z`. -/
class HasChainUnions {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) : Prop where
  union : ∀ {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (index : Type u) [Nonempty index]
    (obj : index → W.Object μ hμ)
    (le : (i j : index) → SystemArrow K S (W.asSystem hμ (obj i)) (W.asSystem hμ (obj j)))
    (_le_arrow : ∀ i j, W.permitted (X := obj i) (Y := obj j) (le i j)),
    (∀ i j k, SystemArrow.comp (le i j) (le j k) = le i k) →
    #index ≤ μ →
    ∃ U : W.Object μ hμ,
      ∃ incl : (i : index) → SystemArrow K S (W.asSystem hμ (obj i)) (W.asSystem hμ U),
        (∀ i, W.permitted (X := obj i) (Y := U) (incl i)) ∧
        (∀ i j, SystemArrow.comp (le i j) (incl j) = incl i) ∧
        ∀ {ν : Cardinal.{u}} (hν : ν ∈ W.eligible) (Z : W.Object ν hν)
          (toZ : (i : index) →
            SystemArrow K S (W.asSystem hμ (obj i)) (W.asSystem hν Z)),
          (∀ i, W.permitted (X := obj i) (Y := Z) (toZ i)) →
          (∀ i j, SystemArrow.comp (le i j) (toZ j) = toZ i) →
          μ ≤ ν →
          ∃ toU : SystemArrow K S (W.asSystem hμ U) (W.asSystem hν Z),
            W.permitted (X := U) (Y := Z) toU ∧
            ∀ i, SystemArrow.comp (incl i) toU = toZ i

/-- Definition 5.2(2), mixed downward closure. At most `ν` vertex occurrences in a level-`μ`
object sit in an arrow image of some level-`ν` object. -/
class HasMixedDownward {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) : Prop where
  downward : ∀ {μ ν : Cardinal.{u}} (hμ : μ ∈ W.eligible) (hν : ν ∈ W.eligible)
    (X : W.Object μ hμ) (ι : Type u)
    (occ : ι → Occurrence K S (W.asSystem hμ X)),
    ν ≤ μ → #ι ≤ ν →
    ∃ Y : W.Object ν hν,
      ∃ f : SystemArrow K S (W.asSystem hν Y) (W.asSystem hμ X),
        W.permitted (X := Y) (Y := X) f ∧
        ∀ i, ∃ y : Occurrence K S (W.asSystem hν Y),
          occ i = ⟨y.1, f.onVertex y.1 y.2⟩

/-- Definition 5.2(3), saturation. A joint diagram of bounded length that extends the diagram
of an actual bounded list, and is witnessed in any eligible object, is realized over that list at
its own level.

The witness `ext` extends the list `base` whose diagram is that of the actual list `xs`
(`ext ∘ Sum.inl = base`). Without this link the clause would ask for a realization of an
arbitrary list `ext` over `xs`, which fails already for `ext` constant and `xs` injective. -/
class IsSaturated {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) : Prop where
  saturated : ∀ {μ ν : Cardinal.{u}} {hμ : μ ∈ W.eligible} {hν : ν ∈ W.eligible}
    {α β : Type u} (X : W.Object μ hμ) (Y : W.Object ν hν)
    (xs : α → Occurrence K S (W.asSystem hμ X))
    (base : α → Occurrence K S (W.asSystem hν Y))
    (ext : α ⊕ β → Occurrence K S (W.asSystem hν Y)),
    #α < μ → #β < μ →
    (∀ i, ext (Sum.inl i) = base i) →
    W.DiagramEq (X := X) (Y := Y) xs base →
    ∃ (Z : W.Object μ hμ)
      (f : SystemArrow K S (W.asSystem hμ X) (W.asSystem hμ Z))
      (zs : α ⊕ β → Occurrence K S (W.asSystem hμ Z)),
      W.permitted (X := X) (Y := Z) f ∧
      (∀ i, zs (Sum.inl i) = ⟨(xs i).1, f.onVertex (xs i).1 (xs i).2⟩) ∧
      W.DiagramEq (X := Z) (Y := Y) zs ext

/-- Definition 5.2(4). A commuting family of strong vertex maps at one level is an arrow when it
preserves the `D`-diagram of every list bounded at that level. Component strongness is the
`onVertex_strong` field; an additional scheme condition is included by concluding `permitted`. -/
class SatisfiesExhaustion {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) : Prop where
  exhaustion : ∀ {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible}
    (X Y : W.Object μ hμ)
    (f : SystemArrow K S (W.asSystem hμ X) (W.asSystem hμ Y)),
    (∀ {ι : Type u} (xs : ι → Occurrence K S (W.asSystem hμ X)),
      #ι < μ →
      W.DiagramEq (X := X) (Y := Y) xs
        (fun i => ⟨(xs i).1, f.onVertex (xs i).1 (xs i).2⟩)) →
    W.permitted (X := X) (Y := Y) f

/-- The four working-package clauses of Definition 5.2 beyond the scheme data. -/
def IsWorkingPackage {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) : Prop :=
  HasChainUnions W ∧ HasMixedDownward W ∧ IsSaturated W ∧ SatisfiesExhaustion W

end
end AEC
