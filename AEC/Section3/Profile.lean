module

public import AEC.Section3.OrbitName
public import AEC.Section3.OrbitArrow
public import AEC.Section3.UniformOrbitBound
public import AEC.Section3.AdditivelyIndecomposable
public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- The profile of a presentation, in the sense of Section 3.3: the named orbit-arrow
relation, together with the partial function sending each realized presentation record
to its orbit name. -/
structure Profile (Record Name : Type u) where
  arrow : Name → Name → Prop
  arrow_refl : ∀ n, arrow n n
  arrow_trans : ∀ a b c, arrow a b → arrow b c → arrow a c
  assign : Record → Option Name

/-- A package of common-profile data for Proposition 3.9: one indecomposable presentation of
`C_μ` and a cofinal family of indecomposable presentations of `C_a` sharing one assign. -/
structure CommonProfileSetup (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ a μ : Cardinal.{u}) (N : OrbitNaming K θ) (hθ : aleph0 ≤ θ) where
  β : _root_.Ordinal.{u}
  β_indecomposable : AdditivelyIndecomposable β
  β_card : β.card = μ
  β_cof : a < Ordinal.cof β
  Deltas : Set (_root_.Ordinal.{u})
  deltas_spec : ∀ δ ∈ Deltas,
    AdditivelyIndecomposable δ ∧ δ.card = a ∧ θ < Ordinal.cof δ ∧ δ < (Order.succ a).ord
  deltas_cofinal : ∀ η : _root_.Ordinal.{u}, η < (Order.succ a).ord →
    ∃ δ ∈ Deltas, η ≤ δ
  assign : CanonicalRecord E.lab E.arity θ → Option Cardinal.{u}
  /-- On the large presentation, the canonical record of a tuple receives its orbit name. -/
  assign_large :
    ∀ {I : Type u} [LinearOrder I] [Nonempty I] (_e : HOrder β ≃o I)
      {ι : Type u} (hι : #ι ≤ θ) (xs : ι → (E.obj I).carrier),
      assign (canonicalOfTuple E hθ hι xs) =
        some (N.name (orderPresentation_obj_mem E I) xs hι)
  /-- On each small presentation, the canonical record of a tuple receives its orbit name. -/
  assign_small :
    ∀ δ ∈ Deltas,
      ∀ {I : Type u} [LinearOrder I] [Nonempty I] (_e : HOrder δ ≃o I)
        {ι : Type u} (hι : #ι ≤ θ) (xs : ι → (E.obj I).carrier),
        assign (canonicalOfTuple E hθ hι xs) =
          some (N.name (orderPresentation_obj_mem E I) xs hι)
  /-- The shared assign depends only on the record up to `OrbitRecord.Same`. -/
  assign_same :
    ∀ r s : CanonicalRecord E.lab E.arity θ,
      OrbitRecord.Same (CanonicalRecord.toOrbitRecord r) (CanonicalRecord.toOrbitRecord s) →
        assign r = assign s
  /-- On the large presentation, any canonical record realizing a reindexing of `xs`
  receives the name of `xs`. (All realized records of one orbit share one name.) -/
  assign_realizes_large :
    ∀ {I : Type u} [LinearOrder I] [Nonempty I] (_e : HOrder β ≃o I)
      {ι : Type u} (hι : #ι ≤ θ) (xs : ι → (E.obj I).carrier)
      (r : CanonicalRecord E.lab E.arity θ)
      (place : (CanonicalRecord.toOrbitRecord r).slot → I)
      (reindex : (CanonicalRecord.toOrbitRecord r).index ≃ ι),
      RealizesOrbitRecord (I := I) E (CanonicalRecord.toOrbitRecord r) place
        (fun j => xs (reindex j)) →
      assign r = some (N.name (orderPresentation_obj_mem E I) xs hι)

end
end AEC
