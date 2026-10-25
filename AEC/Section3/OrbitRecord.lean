module

public import AEC.Section2.OrderPresentation
public import AEC.Section3.Occupancy

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A presentation record in the sense of Lemma 3.6: labels, the order of the flattened
argument positions, and which cuts of those positions are occupied. The ambient order is
not part of the record. `slot` is exactly the set of argument positions. -/
structure OrbitRecord (lab : Type u) (arity : lab → ℕ) where
  index : Type u
  slot : Type u
  label : index → lab
  arg : ∀ i, Fin (arity (label i)) → slot
  lt : slot → slot → Prop
  arg_strict : ∀ i {a b : Fin (arity (label i))}, a < b → lt (arg i a) (arg i b)
  arg_surj : ∀ x : slot, ∃ i, ∃ a, arg i a = x
  occupied : Set slot → Set slot → Prop

/-- Two records are the same when a bijection of entries and an order isomorphism of the
flattened positions preserve labels, arguments, and occupancy. -/
def OrbitRecord.Same {lab : Type u} {arity : lab → ℕ}
    (r s : OrbitRecord lab arity) : Prop :=
  ∃ (e : r.index ≃ s.index) (f : r.slot ≃ s.slot)
    (hlabel : ∀ i, r.label i = s.label (e i)),
    (∀ a b, r.lt a b ↔ s.lt (f a) (f b)) ∧
    (∀ i (a : Fin (arity (r.label i))),
      f (r.arg i a) = s.arg (e i) (Fin.cast (congrArg arity (hlabel i)) a)) ∧
    ∀ lower upper, r.occupied lower upper ↔ s.occupied (f '' lower) (f '' upper)

/-- `xs` realizes `rec` in `E(I)` when the entries are the values of the record's terms,
the placement of the flattened positions is an order embedding into `I`, and `rec.occupied`
is the occupancy of those positions in `I`. -/
def RealizesOrbitRecord {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] (rec : OrbitRecord E.lab E.arity)
    (place : rec.slot → I) (xs : rec.index → (E.obj I).carrier) : Prop :=
  Function.Injective place ∧
  (∀ a b, rec.lt a b ↔ place a < place b) ∧
  (∀ i, ∃ (pos : Fin (E.arity (rec.label i)) → I) (hinc : StrictMono pos),
    (∀ a, pos a = place (rec.arg i a)) ∧
    xs i = E.realize ⟨rec.label i, pos, hinc⟩) ∧
  ∀ lower upper, rec.occupied lower upper ↔ Occupied (place '' lower) (place '' upper)

/-- The record occurs as the presentation record of some tuple in `E(I)`. -/
def OrbitRecordRealized {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] (rec : OrbitRecord E.lab E.arity) : Prop :=
  ∃ (place : rec.slot → I) (xs : rec.index → (E.obj I).carrier),
    RealizesOrbitRecord E rec place xs

end
end AEC
