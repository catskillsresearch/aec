module

public import AEC.Section3.Profile
public import AEC.Section3.SupportClosure
public import AEC.Section3.IndecomposableSegment
public import AEC.Section3.AdditivelyIndecomposable
public import AEC.Section1.Categorical
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal Set
open scoped Ordinal

/-- Ordinal positions in the finite codes of realizing terms, transported from a soft copy
of `H(β)` back to ordinal indices below `β`. -/
noncomputable def ordinalSupportOf {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {β : _root_.Ordinal.{u}} {I : Type u} [LinearOrder I] [Nonempty I]
    (e : HOrder β ≃o I) (S : Set (E.obj I).carrier) : Set β.ToType :=
  ⋃ x ∈ S, ⋃ p ∈ Set.range (supportTermOf E x).pos,
    (fun i : OrdIndex β => Ordinal.ToType.mk (asIio i)) ''
      (hSupport (e.symm p) : Set (OrdIndex β))

theorem ordinalSupportOf_card {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {β : _root_.Ordinal.{u}} {I : Type u} [LinearOrder I] [Nonempty I]
    (e : HOrder β ≃o I) {a : Cardinal.{u}} (ha : aleph0 ≤ a)
    (S : Set (E.obj I).carrier) (hS : #S ≤ a) :
    #(ordinalSupportOf E e S) ≤ a := by
  have hterm (x : (E.obj I).carrier) :
      #(Set.range (supportTermOf E x).pos) ≤ (ℵ₀ : Cardinal.{u}) := by
    have h := mk_range_le_lift (f := (supportTermOf E x).pos)
    rw [lift_uzero] at h
    refine h.trans ?_
    rw [mk_fin, lift_natCast]
    exact (natCast_lt_aleph0 (n := _)).le
  have hfin (t : Set β.ToType) (ht : t.Finite) : #t ≤ (ℵ₀ : Cardinal.{u}) :=
    ht.lt_aleph0.le
  dsimp [ordinalSupportOf]
  have hper (x : (E.obj I).carrier) :
      #(⋃ p ∈ Set.range (supportTermOf E x).pos,
          (fun i : OrdIndex β => Ordinal.ToType.mk (asIio i)) ''
            (hSupport (e.symm p) : Set (OrdIndex β))) ≤ (ℵ₀ : Cardinal.{u}) := by
    refine (mk_biUnion_le _ _).trans ?_
    have h2 : (⨆ p : ↥(Set.range (supportTermOf E x).pos),
        #((fun i : OrdIndex β => Ordinal.ToType.mk (asIio i)) ''
          (hSupport (e.symm (p : I)) : Set (OrdIndex β)))) ≤ (ℵ₀ : Cardinal.{u}) :=
      ciSup_le' fun p => hfin _ ((hSupport (e.symm (p : I))).finite_toSet.image _)
    exact (mul_le_mul' (hterm x) h2).trans
      (le_of_eq (Cardinal.mul_eq_left le_rfl le_rfl aleph0_ne_zero))
  refine (mk_biUnion_le _ S).trans ?_
  have hsup : (⨆ x : ↥S,
      #(⋃ p ∈ Set.range (supportTermOf E (x : (E.obj I).carrier)).pos,
          (fun i : OrdIndex β => Ordinal.ToType.mk (asIio i)) ''
            (hSupport (e.symm p) : Set (OrdIndex β)))) ≤ (ℵ₀ : Cardinal.{u}) :=
    ciSup_le' fun x => hper _
  exact (mul_le_mul' hS hsup).trans
    (le_of_eq (Cardinal.mul_eq_left ha ha aleph0_ne_zero))

/-- Order type of a size-`≤ a` set of ordinals is strictly below `a⁺`. -/
theorem typeLT_lt_succ_ord {a : Cardinal.{u}} {β : _root_.Ordinal.{u}}
    (T0 : Set β.ToType) (hcard : #T0 ≤ a) :
    typeLT (↥T0) < (Order.succ a).ord := by
  have hle : (typeLT (↥T0)).card ≤ a := by
    rw [Ordinal.card_type (· < ·)]
    exact hcard
  exact (Cardinal.card_le_iff).mp hle

/-- Embed a set of order type strictly below `δ` into an initial segment of `δ`. -/
theorem exists_otp_embedding {β δ : _root_.Ordinal.{u}}
    (T0 : Set β.ToType) (hotp : typeLT (↥T0) < δ) :
    ∃ e : ↥T0 ↪o δ.ToType, ∃ b : δ.ToType, ∀ x, e x < b := by
  classical
  have : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  have hlt : typeLT (↥T0) < typeLT δ.ToType := by
    rw [Ordinal.type_toType]; exact hotp
  let b : δ.ToType := Ordinal.enum (· < ·) ⟨typeLT (↥T0), hlt⟩
  have hb : Ordinal.typein (· < ·) b = typeLT (↥T0) := Ordinal.typein_enum _ _
  have hty : typeLT (↥T0) = typeLT (↥(Iio b)) := by
    rw [← hb]
    simp [Ordinal.type_Iio_lt (α := δ.ToType) b]
  have hrel : Nonempty
      (((· < ·) : ↥T0 → ↥T0 → Prop) ≃r ((· < ·) : ↥(Iio b) → ↥(Iio b) → Prop)) :=
    (Ordinal.type_eq).mp hty
  let iso : ↥T0 ≃o ↥(Iio b) := OrderIso.ofRelIsoLT (Classical.choice hrel)
  let emb : ↥T0 ↪o δ.ToType :=
    iso.toOrderEmbedding.trans (OrderEmbedding.subtype (Iio b))
  refine ⟨emb, b, fun x => (iso x).property⟩

/-- Transport a Hausdorff-order embedding between soft copies of `H(δ)` and `H(β)`. -/
noncomputable def softPush {δ β : _root_.Ordinal.{u}}
    {I J : Type u} [LinearOrder I] [LinearOrder J]
    (eδ : HOrder δ ≃o I) (eβ : HOrder β ≃o J) (φ : HOrder δ ↪o HOrder β) : I ↪o J :=
  OrderEmbedding.ofStrictMono (fun i => eβ (φ (eδ.symm i))) fun i j hij => by
    exact (eβ.lt_iff_lt).mpr ((φ.lt_iff_lt).mpr ((eδ.symm.lt_iff_lt).mpr hij))

theorem softPush_strong {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {δ β : _root_.Ordinal.{u}} {I J : Type u}
    [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (eδ : HOrder δ ≃o I) (eβ : HOrder β ≃o J) (φ : HOrder δ ↪o HOrder β) :
    K.Strong (E.map (softPush eδ eβ φ)) :=
  E.map_strong (softPush eδ eβ φ)

/-- Names agree when a shared assign identifies the two canonical records up to `Same`. -/
theorem name_eq_of_assign {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) (θ : Cardinal.{u}) (N : OrbitNaming K θ) (hθ : aleph0 ≤ θ)
    (assign : CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ))
    {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    {ι : Type u} (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) (ys : ι → (E.obj J).carrier)
    (hassignI : assign (canonicalOfTuple E hθ hι xs) =
      some (N.name (orderPresentation_obj_mem E I) xs hι))
    (hassignJ : assign (canonicalOfTuple E hθ hι ys) =
      some (N.name (orderPresentation_obj_mem E J) ys hι))
    (hsame : OrbitRecord.Same
      (CanonicalRecord.toOrbitRecord (canonicalOfTuple E hθ hι xs))
      (CanonicalRecord.toOrbitRecord (canonicalOfTuple E hθ hι ys)))
    (hassign_same : ∀ r s : CanonicalRecord E.lab E.arity θ,
      OrbitRecord.Same (CanonicalRecord.toOrbitRecord r) (CanonicalRecord.toOrbitRecord s) →
        assign r = assign s) :
    N.name (orderPresentation_obj_mem E I) xs hι =
      N.name (orderPresentation_obj_mem E J) ys hι := by
  have h := hassign_same _ _ hsame
  have : some (N.name (orderPresentation_obj_mem E I) xs hι) =
      some (N.name (orderPresentation_obj_mem E J) ys hι) := by
    rw [← hassignI, ← hassignJ, h]
  exact Option.some.inj this

/-- Choose a profile ordinal `δ` strictly above the order type of `T₀`. -/
theorem exists_profile_delta {θ a : Cardinal.{u}} (ha : aleph0 ≤ a) {β : _root_.Ordinal.{u}}
    (Deltas : Set (_root_.Ordinal.{u}))
    (deltas_spec : ∀ δ ∈ Deltas,
      AdditivelyIndecomposable δ ∧ δ.card = a ∧ θ < Ordinal.cof δ ∧ δ < (Order.succ a).ord)
    (deltas_cofinal : ∀ η : _root_.Ordinal.{u}, η < (Order.succ a).ord →
      ∃ δ ∈ Deltas, η ≤ δ)
    (T0 : Set β.ToType) (hcard : #T0 ≤ a) :
    ∃ δ ∈ Deltas, typeLT (↥T0) < δ ∧
      AdditivelyIndecomposable δ ∧ δ.card = a ∧ θ < Ordinal.cof δ := by
  have hotp : typeLT (↥T0) < (Order.succ a).ord := typeLT_lt_succ_ord T0 hcard
  have haleph : aleph0 ≤ Order.succ a := ha.trans (Order.le_succ a)
  have hlim : Order.IsSuccLimit (Order.succ a).ord := Cardinal.isSuccLimit_ord haleph
  have h1 : typeLT (↥T0) + 1 < (Order.succ a).ord := hlim.succ_lt hotp
  obtain ⟨δ, hδmem, hδε⟩ := deltas_cofinal (typeLT (↥T0) + 1) h1
  have hspec := deltas_spec δ hδmem
  refine ⟨δ, hδmem, ?_, hspec.1, hspec.2.1, hspec.2.2.1⟩
  exact (lt_add_of_pos_right _ (zero_lt_one' _root_.Ordinal)).trans_le hδε

/-- The canonical record of `xs` on `J`, placed into `I` along `softPush`, still realizes the
image tuple. Occupancy is transported by the hypothesis from Lemma 3.8. -/
theorem realizes_canonical_softPush {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ)
    {δ β : _root_.Ordinal.{u}} {I J : Type u}
    [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (eδ : HOrder δ ≃o J) (eβ : HOrder β ≃o I) (φH : HOrder δ ↪o HOrder β)
    (hocc : ∀ {ι : Type u} (hι : #ι ≤ θ) (ys : ι → HOrder δ) (lower upper : Set ι),
      Occupied (ys '' lower) (ys '' upper) ↔
        Occupied ((fun i => φH (ys i)) '' lower) ((fun i => φH (ys i)) '' upper))
    {ι : Type u} (hι : #ι ≤ θ) (xs : ι → (E.obj J).carrier) :
    RealizesOrbitRecord (I := I) E
      (CanonicalRecord.toOrbitRecord (canonicalOfTuple E hθ hι xs))
      (fun s => softPush eδ eβ φH (canonicalPlaceOfTuple E hθ hι xs s))
      (fun j => E.map (softPush eδ eβ φH)
        (canonicalTupleReindex E hθ hι xs j)) := by
  classical
  have h0 := realizes_canonicalOfTuple E hθ hι xs
  let emb := softPush eδ eβ φH
  refine ⟨?inj, ?lt, ?term, ?occ⟩
  · intro a b h
    exact h0.1 (emb.inj' h)
  · intro a b
    constructor
    · intro hlt
      exact (emb.lt_iff_lt).mpr ((h0.2.1 a b).mp hlt)
    · intro hlt
      exact (h0.2.1 a b).mpr ((emb.lt_iff_lt).mp hlt)
  · intro j
    obtain ⟨pos, hinc, hpos, hxs⟩ := h0.2.2.1 j
    refine ⟨emb ∘ pos, emb.strictMono.comp hinc, fun a => congrArg emb (hpos a), ?_⟩
    dsimp
    rw [← E.realize_map emb ⟨_, pos, hinc⟩, hxs]
  · intro L U
    have hsrc := h0.2.2.2 L U
    rw [hsrc]
    let place := canonicalPlaceOfTuple E hθ hι xs
    let ys : (canonicalOfTuple E hθ hι xs).slt → HOrder δ := fun s => eδ.symm (place s)
    have hι' : #(canonicalOfTuple E hθ hι xs).slt ≤ θ := canonical_record_card_slot _
    have himgδ (S : Set (canonicalOfTuple E hθ hι xs).slt) :
        eδ.symm '' (place '' S) = ys '' S := by
      ext z; constructor
      · rintro ⟨p, ⟨s, hs, rfl⟩, rfl⟩; exact ⟨s, hs, rfl⟩
      · rintro ⟨s, hs, rfl⟩; exact ⟨place s, ⟨s, hs, rfl⟩, rfl⟩
    have himgβ (S : Set (canonicalOfTuple E hθ hι xs).slt) :
        eβ '' ((φH ∘ ys) '' S) = (emb ∘ place) '' S := by
      ext z; constructor
      · rintro ⟨q, ⟨s, hs, rfl⟩, rfl⟩
        refine ⟨s, hs, ?_⟩
        change emb (place s) = eβ (φH (ys s))
        rfl
      · rintro ⟨s, hs, rfl⟩
        refine ⟨φH (ys s), ⟨s, hs, rfl⟩, ?_⟩
        change eβ (φH (ys s)) = emb (place s)
        rfl
    calc
      Occupied (place '' L) (place '' U)
          ↔ Occupied (eδ.symm '' (place '' L)) (eδ.symm '' (place '' U)) :=
            occupied_orderIso eδ.symm _ _
      _ ↔ Occupied (ys '' L) (ys '' U) := by rw [himgδ L, himgδ U]
      _ ↔ Occupied ((φH ∘ ys) '' L) ((φH ∘ ys) '' U) := hocc hι' ys L U
      _ ↔ Occupied (eβ '' ((φH ∘ ys) '' L)) (eβ '' ((φH ∘ ys) '' U)) :=
            occupied_orderIso eβ _ _
      _ ↔ Occupied ((emb ∘ place) '' L) ((emb ∘ place) '' U) := by rw [himgβ L, himgβ U]

end
end AEC
