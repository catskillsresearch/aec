module

public import AEC.Section3.AdditivelyIndecomposable
public import AEC.Section3.FiniteSupportOrder
public import AEC.Section3.Occupancy
public import AEC.Section3.SupportClosure
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Hom.Set
public import Mathlib.Order.Sum.Order

@[expose] public section

namespace AEC
section

universe u v w

open Finsupp Classical

attribute [local instance] Classical.propDecidable

/-- Move finite-support vectors along an increasing map of positions, padding by zero.
This is the embedding claim of Lemma 3.2. -/
noncomputable def colexPush {α β : Type v} {M : Type w} [LinearOrder α] [LinearOrder β]
    [AddCommMonoid M] [LinearOrder M] [DecidableEq β] (φ : α ↪o β) :
    Colex (α →₀ M) ↪o Colex (β →₀ M) :=
  OrderEmbedding.ofStrictMono (fun x => toColex (mapDomain φ (ofColex x))) <| by
    intro x y hxy
    rw [Colex.lt_iff] at hxy ⊢
    obtain ⟨i, hi, hlt⟩ := hxy
    refine ⟨φ i, ?_, ?_⟩
    · intro j hj
      by_cases hmem : ∃ a, φ a = j
      · obtain ⟨a, ha⟩ := hmem
        have hagt : i < a := φ.lt_iff_lt.mp (by rw [ha]; exact hj)
        have hcoeff : (ofColex x) a = (ofColex y) a := by
          simpa using hi a hagt
        have hxj : mapDomain φ (ofColex x) j = (ofColex x) a := by
          rw [← ha]
          exact mapDomain_apply_of_injective φ.injective _ a
        have hyj : mapDomain φ (ofColex y) j = (ofColex y) a := by
          rw [← ha]
          exact mapDomain_apply_of_injective φ.injective _ a
        simpa [ofColex_toColex, hxj, hyj, hcoeff]
      · have hx0 : mapDomain φ (ofColex x) j = 0 := by
          rw [← notMem_support_iff]
          intro hsup
          rw [mapDomain_support_of_injective φ.injective] at hsup
          obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hsup
          exact hmem ⟨a, ha⟩
        have hy0 : mapDomain φ (ofColex y) j = 0 := by
          rw [← notMem_support_iff]
          intro hsup
          rw [mapDomain_support_of_injective φ.injective] at hsup
          obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hsup
          exact hmem ⟨a, ha⟩
        simpa [ofColex_toColex, hx0, hy0]
    · have hx : mapDomain φ (ofColex x) (φ i) = (ofColex x) i :=
        mapDomain_apply_of_injective φ.injective _ i
      have hy : mapDomain φ (ofColex y) (φ i) = (ofColex y) i :=
        mapDomain_apply_of_injective φ.injective _ i
      simpa [ofColex_toColex, hx, hy] using hlt

/-- The position embedding of an indecomposable segment induces the embedding of `H`. -/
noncomputable def horderPush {δ β : _root_.Ordinal.{u}} (φ : OrdIndex δ ↪o OrdIndex β) :
    HOrder δ ↪o HOrder β :=
  letI : DecidableEq (OrdIndex β) := Classical.decEq _
  let φΓ : Gamma δ ↪o Gamma β := colexPush φ
  letI : DecidableEq (Gamma β) := Classical.decEq _
  colexPush (M := ℚ) φΓ

open Cardinal Set

open scoped Ordinal

/-- The ordinal named by a point of `o.ToType`. -/
noncomputable def ordOf {o : _root_.Ordinal.{u}} (x : o.ToType) : _root_.Ordinal.{u} :=
  (Ordinal.ToType.toOrd x).1

@[simp]
lemma ordOf_mk {o ξ : _root_.Ordinal.{u}} (h : ξ < o) :
    ordOf (Ordinal.ToType.mk ⟨ξ, h⟩) = ξ := by
  simp [ordOf, Ordinal.ToType.toOrd, OrderIso.symm_apply_apply]

lemma ordOf_lt_iff {o : _root_.Ordinal.{u}} {x y : o.ToType} : ordOf x < ordOf y ↔ x < y := by
  constructor
  · intro h
    exact ordinal_lt_toType h
  · intro h
    have hxy : Ordinal.ToType.mk (Ordinal.ToType.toOrd x) <
        Ordinal.ToType.mk (Ordinal.ToType.toOrd y) := by
      simpa [OrderIso.apply_symm_apply] using h
    exact Subtype.mk_lt_mk.mp ((Ordinal.ToType.mk.lt_iff_lt).mp hxy)

lemma ordOf_eq_iff {o : _root_.Ordinal.{u}} {x y : o.ToType} : ordOf x = ordOf y ↔ x = y := by
  constructor
  · intro h
    apply (Ordinal.ToType.mk (o := o)).symm.injective
    apply Subtype.ext
    exact h
  · intro h
    simp [h]

/-- A finite shift stays below a limit ordinal. -/
lemma add_nat_lt_of_isSuccLimit {o a : _root_.Ordinal.{u}} (ho : Order.IsSuccLimit o)
    (ha : a < o) (n : ℕ) : a + n < o := by
  induction n with
  | zero => simpa using ha
  | succ n ih =>
    have hstep : a + ((n + 1 : ℕ) : _root_.Ordinal.{u}) = Order.succ (a + n) := by
      rw [Nat.cast_succ, ← add_assoc, ← Order.succ_eq_add_one]
    rw [hstep]
    exact ho.succ_lt ih

/-- Strictly above every point of `T₀`, with room for a copy of `δ`. -/
lemma exists_segment_base {a : Cardinal.{u}} {β δ : _root_.Ordinal.{u}}
    (haleph : ℵ₀ ≤ a) (hcofβ : a < Ordinal.cof β) (hβ : AdditivelyIndecomposable β)
    (hδlt : δ < β) (T0 : Set β.ToType) (hcard : #T0 ≤ a) :
    ∃ α : _root_.Ordinal.{u}, α < β ∧ α + δ < β ∧ ∀ x ∈ T0, ordOf x < α := by
  have hlim : Order.IsSuccLimit β :=
    Ordinal.one_lt_cof_iff.mp (one_lt_aleph0.trans_le (haleph.trans hcofβ.le))
  let fOrd : ↥T0 → _root_.Ordinal.{u} := fun x => ordOf x.1
  have hsup : (⨆ x, fOrd x) < β :=
    Ordinal.iSup_lt_of_lt_cof (lt_of_le_of_lt hcard hcofβ) (fun x => (Ordinal.ToType.toOrd x.1).2)
  refine ⟨(⨆ x, fOrd x) + 1, hlim.succ_lt hsup, ?_, ?_⟩
  · exact hβ.principal (hlim.succ_lt hsup) hδlt
  · intro x hx
    have hxle : fOrd ⟨x, hx⟩ ≤ ⨆ y, fOrd y := Ordinal.le_iSup fOrd ⟨x, hx⟩
    exact lt_of_le_of_lt hxle (lt_add_of_pos_right _ zero_lt_one)

/-- An order embedding into a bounded part of `δ` has order type strictly below `δ`. -/
lemma typeLT_support_lt {β δ : _root_.Ordinal.{u}} (T0 : Set β.ToType)
    (hotp : ∃ e : ↥T0 ↪o δ.ToType, ∃ b : δ.ToType, ∀ x, e x < b) :
    typeLT (↥T0) < δ := by
  obtain ⟨e, b, hb⟩ := hotp
  haveI : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  have hle : typeLT (↥T0) ≤ typeLT (↥(Iio b)) := by
    refine (RelEmbedding.ofMonotone (fun x : ↥T0 => (⟨e x, hb x⟩ : Iio b)) ?_).ordinal_type_le
    intro x y hxy
    exact Subtype.mk_lt_mk.mpr ((e.lt_iff_lt).mpr hxy)
  have hIio : typeLT (↥(Iio b)) = Ordinal.typein (· < ·) b := by
    simpa using Ordinal.type_Iio_lt (α := δ.ToType) b
  have htin : Ordinal.typein (· < ·) b < typeLT δ.ToType := Ordinal.typein_lt_type (· < ·) b
  rw [Ordinal.type_toType] at htin
  exact hle.trans_lt (hIio.symm ▸ htin)

/-- `T₀`, followed by the half-open interval of type `δ`, has order type `δ`. -/
lemma exists_extended_iso {β δ : _root_.Ordinal.{u}} (hδ : AdditivelyIndecomposable δ)
    (α : _root_.Ordinal.{u}) (hαδ : α + δ < β) (T0 : Set β.ToType)
    (hT0lt : ∀ x ∈ T0, ordOf x < α)
    (hotp : ∃ e : ↥T0 ↪o δ.ToType, ∃ b : δ.ToType, ∀ x, e x < b) :
    ∃ T : Set β.ToType, T0 ⊆ T ∧ Nonempty (↥T ≃o δ.ToType) ∧
      ∀ x, x ∈ T ↔ x ∈ T0 ∨ α ≤ ordOf x ∧ ordOf x < α + δ := by
  let J : Set β.ToType := {x | α ≤ ordOf x ∧ ordOf x < α + δ}
  let T : Set β.ToType := T0 ∪ J
  have hmem : ∀ x, x ∈ T ↔ x ∈ T0 ∨ α ≤ ordOf x ∧ ordOf x < α + δ := by
    intro x
    simp [T, J, mem_union]
  let jOf : δ.ToType → ↥J := fun i =>
    have hξ : α + ordOf i < β :=
      ((add_lt_add_iff_left α).2 (Ordinal.ToType.toOrd i).2).trans hαδ
    ⟨Ordinal.ToType.mk ⟨α + ordOf i, hξ⟩, by
      have hord : ordOf (Ordinal.ToType.mk ⟨α + ordOf i, hξ⟩) = α + ordOf i := ordOf_mk hξ
      refine ⟨?_, ?_⟩
      · rw [hord]
        exact le_self_add
      · rw [hord]
        exact (add_lt_add_iff_left α).2 (Ordinal.ToType.toOrd i).2⟩
  have hjMono : StrictMono jOf := by
    intro i j hij
    have hi : ordOf (jOf i).1 = α + ordOf i := by
      simp only [jOf]
      exact ordOf_mk _
    have hj : ordOf (jOf j).1 = α + ordOf j := by
      simp only [jOf]
      exact ordOf_mk _
    have hlt : α + ordOf i < α + ordOf j := (add_lt_add_iff_left α).2 ((ordOf_lt_iff).mpr hij)
    exact Subtype.mk_lt_mk.mpr ((ordOf_lt_iff).mp (by rw [hi, hj]; exact hlt))
  have hjSurj : Function.Surjective jOf := by
    intro x
    have hx := x.2
    have hd : ordOf x.1 - α < δ := (Ordinal.sub_lt_of_le hx.1).mpr hx.2
    let i : δ.ToType := Ordinal.ToType.mk ⟨ordOf x.1 - α, hd⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    apply (ordOf_eq_iff).mp
    have hcancel : α + (ordOf x.1 - α) = ordOf x.1 := Ordinal.add_sub_cancel_of_le hx.1
    have hord : ordOf (jOf i).1 = α + ordOf i := by
      simp only [jOf]
      exact ordOf_mk _
    rw [hord, ordOf_mk hd, hcancel]
  let jIso : δ.ToType ≃o ↥J := hjMono.orderIsoOfSurjective jOf hjSurj
  let toSum : ↥T → ↥T0 ⊕ₗ ↥J := fun z =>
    if hz : z.1 ∈ T0 then Sum.inlₗ ⟨z.1, hz⟩
    else Sum.inrₗ ⟨z.1, by
      have hzT : z.1 ∈ T0 ∪ J := by simpa only [T] using z.2
      exact (Set.mem_or_mem_of_mem_union hzT).resolve_left hz⟩
  have htoSum : StrictMono toSum := by
    intro z w hzw
    by_cases hz : z.1 ∈ T0 <;> by_cases hw : w.1 ∈ T0
    · have hpts : (⟨z.1, hz⟩ : ↥T0) < ⟨w.1, hw⟩ := Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp hzw)
      simpa [toSum, hz, hw, Sum.Lex.inl_lt_inl_iff] using hpts
    · simpa [toSum, hz, hw] using Sum.Lex.inl_lt_inr (⟨z.1, hz⟩ : ↥T0)
        ⟨w.1, by
          have hwT : w.1 ∈ T0 ∪ J := by simpa only [T] using w.2
          exact (Set.mem_or_mem_of_mem_union hwT).resolve_left hw⟩
    · have hwlt : ordOf w.1 < α := hT0lt w.1 hw
      have hzJ : z.1 ∈ J := by
        have hzT : z.1 ∈ T0 ∪ J := by simpa only [T] using z.2
        exact (Set.mem_or_mem_of_mem_union hzT).resolve_left hz
      exact absurd ((ordOf_lt_iff).mpr hzw) (not_lt_of_ge (hwlt.trans_le hzJ.1).le)
    · have hpts : (⟨z.1, by
          have hzT : z.1 ∈ T0 ∪ J := by simpa only [T] using z.2
          exact (Set.mem_or_mem_of_mem_union hzT).resolve_left hz⟩ : ↥J) <
        ⟨w.1, by
          have hwT : w.1 ∈ T0 ∪ J := by simpa only [T] using w.2
          exact (Set.mem_or_mem_of_mem_union hwT).resolve_left hw⟩ :=
        Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp hzw)
      simpa [toSum, hz, hw, Sum.Lex.inr_lt_inr_iff] using hpts
  have htype : typeLT (↥T) = δ := by
    have hJ : typeLT (↥J) = δ := by
      rw [← jIso.ordinalType_congr, Ordinal.type_toType]
    have hle : typeLT (↥T) ≤ typeLT (↥T0) + typeLT (↥J) := by
      have hembed :=
        (RelEmbedding.ofMonotone toSum htoSum).ordinal_type_le
      simpa [Ordinal.type_lt_sum_lex] using hembed
    have hge : δ ≤ typeLT (↥T) := by
      have hincl : StrictMono (fun y : ↥J => (⟨y.1, Or.inr y.2⟩ : ↥T)) := by
        intro y₁ y₂ hy
        exact Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp hy)
      have hembed := (RelEmbedding.ofMonotone _ hincl).ordinal_type_le
      exact hJ.symm ▸ hembed
    have hclosed : typeLT (↥T0) + δ = δ :=
      hδ.principal.add_eq_right (typeLT_support_lt T0 hotp)
    have hupper : typeLT (↥T) ≤ δ := by
      have hle' : typeLT (↥T) ≤ typeLT (↥T0) + δ := by simpa [hJ] using hle
      exact hle'.trans_eq hclosed
    exact le_antisymm hupper hge
  have hty : typeLT (↥T) = typeLT δ.ToType := by rw [htype, Ordinal.type_toType]
  have hrel : Nonempty (((· < ·) : ↥T → ↥T → Prop) ≃r ((· < ·) : δ.ToType → δ.ToType → Prop)) :=
    (Ordinal.type_eq).mp hty
  exact ⟨T, subset_union_left, ⟨OrderIso.ofRelIsoLT (Classical.choice hrel)⟩, hmem⟩

/-- The appended segment keeps the finite order/equality patterns of the closed support. -/
lemma extended_pattern {θ : Cardinal.{u}} {β δ : _root_.Ordinal.{u}}
    (hθ : ℵ₀ ≤ θ) (hcfδ : θ < Ordinal.cof δ)
    (α : _root_.Ordinal.{u}) (hαδ : α + δ < β) (T0 : Set β.ToType)
    (hT0lt : ∀ x ∈ T0, ordOf x < α)
    (hpat : ∀ {ι : Type u} (_hι : #ι ≤ θ) (p : ι → β.ToType), (∀ i, p i ∈ T0) →
      ∀ {n : ℕ} (q : Fin n → β.ToType), ∃ q' : Fin n → β.ToType,
        (∀ i, q' i ∈ T0) ∧ SameOrderDiagram (Sum.elim p q) (Sum.elim p q'))
    (T : Set β.ToType)
    (hmem : ∀ x, x ∈ T ↔ x ∈ T0 ∨ α ≤ ordOf x ∧ ordOf x < α + δ) :
    ∀ {ι : Type u} (_hι : #ι ≤ θ) (p : ι → β.ToType), (∀ i, p i ∈ T) →
      ∀ {n : ℕ} (q : Fin n → β.ToType), ∃ q' : Fin n → β.ToType,
        (∀ k, q' k ∈ T) ∧ SameOrderDiagram (Sum.elim p q) (Sum.elim p q') := by
  intro ι hι p hp n q
  have hlimδ : Order.IsSuccLimit δ :=
    Ordinal.one_lt_cof_iff.mp (one_lt_aleph0.trans_le (hθ.trans hcfδ.le))
  have hδpos : (0 : _root_.Ordinal.{u}) < δ :=
    hlimδ.pos
  have hpord (i : ι) : ordOf (p i) < α + δ := by
    rcases (hmem (p i)).mp (hp i) with h0 | hJ
    · exact (hT0lt (p i) h0).trans_le le_self_add
    · exact hJ.2
  let bump : ι ⊕ ULift.{u} (Fin n) → _root_.Ordinal.{u} := fun
    | Sum.inl i => if h : α ≤ ordOf (p i) then ordOf (p i) - α else 0
    | Sum.inr k =>
      if h : α ≤ ordOf (q k.down) ∧ ordOf (q k.down) < α + δ then ordOf (q k.down) - α else 0
  have hbump (z : ι ⊕ ULift.{u} (Fin n)) : bump z < δ := by
    cases z with
    | inl i =>
      by_cases h : α ≤ ordOf (p i)
      · simpa [bump, h] using (Ordinal.sub_lt_of_le h).mpr (hpord i)
      · simpa [bump, h] using hδpos
    | inr k =>
      by_cases h : α ≤ ordOf (q k.down) ∧ ordOf (q k.down) < α + δ
      · simpa [bump, h] using (Ordinal.sub_lt_of_le h.1).mpr h.2
      · simpa [bump, h] using hδpos
  have hidx : #(ι ⊕ ULift.{u} (Fin n)) < Ordinal.cof δ := by
    have hfin : #(ULift.{u} (Fin n)) ≤ θ := by
      rw [Cardinal.mk_uLift, Cardinal.lift_mk_fin]
      exact Cardinal.natCast_le_aleph0.trans hθ
    calc
      #(ι ⊕ ULift.{u} (Fin n)) = #ι + #(ULift.{u} (Fin n)) := by
        rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      _ ≤ θ + θ := add_le_add hι hfin
      _ = θ := Cardinal.add_eq_self hθ
      _ < Ordinal.cof δ := hcfδ
  have hsup : (⨆ z, bump z) < δ := Ordinal.iSup_lt_of_lt_cof hidx hbump
  let shift : _root_.Ordinal.{u} := (⨆ z, bump z) + 1
  have hshift : shift < δ := hlimδ.succ_lt hsup
  have lt_shift (ξ : _root_.Ordinal.{u}) (hαξ : α ≤ ξ) (hξ : ξ - α ≤ ⨆ z, bump z) :
      ξ < α + shift := by
    have hξeq : ξ = α + (ξ - α) := (Ordinal.add_sub_cancel_of_le hαξ).symm
    rw [hξeq]
    exact (add_lt_add_iff_left α).2 (lt_of_le_of_lt hξ (lt_add_of_pos_right _ zero_lt_one))
  have param_lt_shift (i : ι) (hi : α ≤ ordOf (p i)) : ordOf (p i) < α + shift := by
    refine lt_shift (ordOf (p i)) hi ?_
    have hb : bump (Sum.inl i) = ordOf (p i) - α := by simp [bump, hi]
    simpa [hb] using Ordinal.le_iSup bump (Sum.inl i)
  have inside_lt_shift (k : Fin n) (hk : α ≤ ordOf (q k) ∧ ordOf (q k) < α + δ) :
      ordOf (q k) < α + shift := by
    refine lt_shift (ordOf (q k)) hk.1 ?_
    have hb : bump (Sum.inr (ULift.up k)) = ordOf (q k) - α := by simp [bump, hk]
    simpa [hb] using Ordinal.le_iSup bump (Sum.inr (ULift.up k))
  let ι0 : Type u := {i : ι // ordOf (p i) < α}
  have hι0 : #ι0 ≤ θ :=
    (Cardinal.mk_le_of_injective (f := Subtype.val) Subtype.val_injective).trans hι
  let B := {k : Fin n // ordOf (q k) < α}
  let eqv : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let qB : Fin (Fintype.card B) → β.ToType := fun m => q (eqv.symm m).1
  have hp0 : ∀ i : ι0, p i.1 ∈ T0 := by
    intro i
    rcases (hmem (p i.1)).mp (hp i.1) with h0 | hJ
    · exact h0
    · exact absurd i.2 (not_lt_of_ge hJ.1)
  obtain ⟨qB', hqBmem, hqBdiag⟩ := hpat hι0 (fun i : ι0 => p i.1) hp0 qB
  let lowerAbove (k : Fin n) : Finset (Fin n) :=
    Finset.univ.filter fun j => α + δ ≤ ordOf (q j) ∧ ordOf (q j) < ordOf (q k)
  let aboveRank (k : Fin n) : ℕ := (lowerAbove k).card
  have hhigh (k : Fin n) : α + shift + aboveRank k < β := by
    have hlt : shift + aboveRank k < δ := add_nat_lt_of_isSuccLimit hlimδ hshift (aboveRank k)
    rw [add_assoc]
    exact ((add_lt_add_iff_left α).2 hlt).trans hαδ
  let q' : Fin n → β.ToType := fun k =>
    if hk : ordOf (q k) < α then qB' (eqv ⟨k, hk⟩)
    else if hk2 : ordOf (q k) < α + δ then q k
    else Ordinal.ToType.mk ⟨α + shift + aboveRank k, hhigh k⟩
  have q'_below (k : Fin n) (hk : ordOf (q k) < α) : q' k = qB' (eqv ⟨k, hk⟩) := by
    simp [q', hk]
  have q'_inside (k : Fin n) (hk : ¬ ordOf (q k) < α) (hk2 : ordOf (q k) < α + δ) :
      q' k = q k := by
    simp [q', hk, hk2]
  have q'_above (k : Fin n) (hk : α + δ ≤ ordOf (q k)) :
      q' k = Ordinal.ToType.mk ⟨α + shift + aboveRank k, hhigh k⟩ := by
    have hkα : ¬ ordOf (q k) < α := fun h => not_lt_of_ge hk (h.trans_le le_self_add)
    have hkδ : ¬ ordOf (q k) < α + δ := not_lt_of_ge hk
    simp [q', hkα, hkδ]
  have q'_above_ord (k : Fin n) (hk : α + δ ≤ ordOf (q k)) :
      ordOf (q' k) = α + shift + aboveRank k := by
    rw [q'_above k hk]
    exact ordOf_mk _
  have q'_above_ge (k : Fin n) (hk : α + δ ≤ ordOf (q k)) : α + shift ≤ ordOf (q' k) := by
    rw [q'_above_ord k hk]
    exact le_self_add
  have low_ord (k : Fin n) (hk : ordOf (q k) < α) : ordOf (q' k) < α := by
    rw [q'_below k hk]
    exact hT0lt _ (hqBmem (eqv ⟨k, hk⟩))
  have high_ge (k : Fin n) (hk : ¬ ordOf (q k) < α) : α ≤ ordOf (q' k) := by
    by_cases hk2 : ordOf (q k) < α + δ
    · rw [q'_inside k hk hk2]
      exact le_of_not_gt hk
    · have hge : α + δ ≤ ordOf (q k) := le_of_not_gt hk2
      exact (le_self_add.trans (q'_above_ge k hge))
  have rank_lt (j k : Fin n) (hj : α + δ ≤ ordOf (q j)) (hk : α + δ ≤ ordOf (q k))
      (hlt : ordOf (q j) < ordOf (q k)) : aboveRank j < aboveRank k := by
    have hsub : lowerAbove j ⊆ lowerAbove k := by
      intro t ht
      simp only [lowerAbove, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      exact ⟨ht.1, lt_trans ht.2 hlt⟩
    have hmem : j ∈ lowerAbove k := by
      simp [lowerAbove, Finset.mem_filter, hj, hlt]
    have hnot : j ∉ lowerAbove j := by
      simp [lowerAbove, Finset.mem_filter]
    exact Nat.lt_of_lt_of_le (Finset.card_lt_card ⟨hsub, fun h => hnot (h hmem)⟩) le_rfl
  have rank_eq_of_eq (j k : Fin n) (heq : ordOf (q j) = ordOf (q k)) :
      aboveRank j = aboveRank k := by
    simp [aboveRank, lowerAbove, heq]
  have above_ord_lt (j k : Fin n) (hj : α + δ ≤ ordOf (q j)) (hk : α + δ ≤ ordOf (q k)) :
      ordOf (q j) < ordOf (q k) ↔ ordOf (q' j) < ordOf (q' k) := by
    rw [q'_above_ord j hj, q'_above_ord k hk, add_lt_add_iff_left]
    constructor
    · intro hlt
      exact_mod_cast rank_lt j k hj hk hlt
    · intro hlt
      rcases lt_trichotomy (ordOf (q j)) (ordOf (q k)) with h | h | h
      · exact h
      · exact absurd hlt (by rw [rank_eq_of_eq j k h]; exact lt_irrefl _)
      · exact absurd (Nat.cast_lt.mpr (rank_lt k j hk hj h)) (not_lt_of_ge hlt.le)
  have above_ord_eq (j k : Fin n) (hj : α + δ ≤ ordOf (q j)) (hk : α + δ ≤ ordOf (q k)) :
      ordOf (q j) = ordOf (q k) ↔ ordOf (q' j) = ordOf (q' k) := by
    rw [q'_above_ord j hj, q'_above_ord k hk, add_left_cancel_iff]
    constructor
    · intro h
      exact_mod_cast rank_eq_of_eq j k h
    · intro h
      rcases lt_trichotomy (ordOf (q j)) (ordOf (q k)) with hlt | heq | hgt
      · exact absurd (Nat.cast_lt.mpr (rank_lt j k hj hk hlt)) (by rw [h]; exact lt_irrefl _)
      · exact heq
      · exact absurd (Nat.cast_lt.mpr (rank_lt k j hk hj hgt)) (by rw [h]; exact lt_irrefl _)
  have low_param (i : ι) (hi : ordOf (p i) < α) (k : Fin n) (hk : ordOf (q k) < α) :
      (p i = q k ↔ p i = q' k) ∧ (p i < q k ↔ p i < q' k) ∧ (q k < p i ↔ q' k < p i) := by
    have heq := hqBdiag.1 (Sum.inl ⟨i, hi⟩) (Sum.inr (eqv ⟨k, hk⟩))
    have hlt := hqBdiag.2 (Sum.inl ⟨i, hi⟩) (Sum.inr (eqv ⟨k, hk⟩))
    have hgt := hqBdiag.2 (Sum.inr (eqv ⟨k, hk⟩)) (Sum.inl ⟨i, hi⟩)
    have hL : Sum.elim (fun i : ι0 => p i.1) qB (Sum.inl ⟨i, hi⟩) = p i := rfl
    have hR : Sum.elim (fun i : ι0 => p i.1) qB (Sum.inr (eqv ⟨k, hk⟩)) = q k := by
      change qB (eqv ⟨k, hk⟩) = q k
      unfold qB
      rw [Equiv.symm_apply_apply]
    have hL' : Sum.elim (fun i : ι0 => p i.1) qB' (Sum.inl ⟨i, hi⟩) = p i := rfl
    have hR' : Sum.elim (fun i : ι0 => p i.1) qB' (Sum.inr (eqv ⟨k, hk⟩)) = q' k := by
      change qB' (eqv ⟨k, hk⟩) = q' k
      exact (q'_below k hk).symm
    rw [hL, hR, hL', hR'] at heq hlt hgt
    exact ⟨heq, hlt, hgt⟩
  have low_coord (k l : Fin n) (hk : ordOf (q k) < α) (hl : ordOf (q l) < α) :
      (q k = q l ↔ q' k = q' l) ∧ (q k < q l ↔ q' k < q' l) := by
    have heq := hqBdiag.1 (Sum.inr (eqv ⟨k, hk⟩)) (Sum.inr (eqv ⟨l, hl⟩))
    have hlt := hqBdiag.2 (Sum.inr (eqv ⟨k, hk⟩)) (Sum.inr (eqv ⟨l, hl⟩))
    have hRk : Sum.elim (fun i : ι0 => p i.1) qB (Sum.inr (eqv ⟨k, hk⟩)) = q k := by
      change qB (eqv ⟨k, hk⟩) = q k
      unfold qB
      rw [Equiv.symm_apply_apply]
    have hRl : Sum.elim (fun i : ι0 => p i.1) qB (Sum.inr (eqv ⟨l, hl⟩)) = q l := by
      change qB (eqv ⟨l, hl⟩) = q l
      unfold qB
      rw [Equiv.symm_apply_apply]
    have hR'k : Sum.elim (fun i : ι0 => p i.1) qB' (Sum.inr (eqv ⟨k, hk⟩)) = q' k := by
      change qB' (eqv ⟨k, hk⟩) = q' k
      exact (q'_below k hk).symm
    have hR'l : Sum.elim (fun i : ι0 => p i.1) qB' (Sum.inr (eqv ⟨l, hl⟩)) = q' l := by
      change qB' (eqv ⟨l, hl⟩) = q' l
      exact (q'_below l hl).symm
    rw [hRk, hRl, hR'k, hR'l] at heq hlt
    exact ⟨heq, hlt⟩
  have param_coord (i : ι) (k : Fin n) :
      (p i = q k ↔ p i = q' k) ∧ (p i < q k ↔ p i < q' k) ∧
        (q k < p i ↔ q' k < p i) := by
    by_cases hi : ordOf (p i) < α <;> by_cases hk : ordOf (q k) < α
    · exact low_param i hi k hk
    · have hp_lt : ordOf (p i) < α := hi
      have hq_ge : α ≤ ordOf (q k) := le_of_not_gt hk
      have hp'_lt : ordOf (p i) < α := hp_lt
      have hq'_ge : α ≤ ordOf (q' k) := high_ge k hk
      refine ⟨?_, ?_, ?_⟩
      · constructor
        · intro h
          exact absurd (h ▸ hp_lt) (not_lt_of_ge hq_ge)
        · intro h
          exact absurd (h ▸ hp'_lt) (not_lt_of_ge hq'_ge)
      · constructor
        · intro _
          exact (ordOf_lt_iff).mp (hp'_lt.trans_le hq'_ge)
        · intro _
          exact (ordOf_lt_iff).mp (hp_lt.trans_le hq_ge)
      · constructor
        · intro h
          exact absurd ((ordOf_lt_iff).mpr h) (not_lt_of_ge (hp_lt.trans_le hq_ge).le)
        · intro h
          exact absurd ((ordOf_lt_iff).mpr h) (not_lt_of_ge (hp'_lt.trans_le hq'_ge).le)
    · have hq_lt : ordOf (q k) < α := hk
      have hp_ge : α ≤ ordOf (p i) := le_of_not_gt hi
      have hq'_lt : ordOf (q' k) < α := low_ord k hk
      refine ⟨?_, ?_, ?_⟩
      · constructor
        · intro h
          exact absurd (h.symm ▸ hq_lt) (not_lt_of_ge hp_ge)
        · intro h
          exact absurd (h.symm ▸ hq'_lt) (not_lt_of_ge hp_ge)
      · constructor
        · intro h
          exact absurd ((ordOf_lt_iff).mpr h) (not_lt_of_ge (hq_lt.trans_le hp_ge).le)
        · intro h
          exact absurd ((ordOf_lt_iff).mpr h) (not_lt_of_ge (hq'_lt.trans_le hp_ge).le)
      · constructor
        · intro _
          exact (ordOf_lt_iff).mp (hq'_lt.trans_le hp_ge)
        · intro _
          exact (ordOf_lt_iff).mp (hq_lt.trans_le hp_ge)
    · have hpJ : α ≤ ordOf (p i) ∧ ordOf (p i) < α + δ := ⟨le_of_not_gt hi, hpord i⟩
      by_cases hk2 : ordOf (q k) < α + δ
      · have hq' : q' k = q k := q'_inside k hk hk2
        simp [hq']
      · have hge : α + δ ≤ ordOf (q k) := le_of_not_gt hk2
        have hp_lt_q : ordOf (p i) < ordOf (q k) := (hpord i).trans_le hge
        have hp_lt_q' : ordOf (p i) < ordOf (q' k) :=
          (param_lt_shift i hpJ.1).trans_le (q'_above_ge k hge)
        refine ⟨?_, ?_, ?_⟩
        · constructor
          · intro h
            exact absurd (h ▸ hp_lt_q) (lt_irrefl _)
          · intro h
            exact absurd (h ▸ hp_lt_q') (lt_irrefl _)
        · constructor
          · intro _
            exact (ordOf_lt_iff).mp hp_lt_q'
          · intro _
            exact (ordOf_lt_iff).mp hp_lt_q
        · constructor
          · intro h
            exact absurd ((ordOf_lt_iff).mpr h) hp_lt_q.not_gt
          · intro h
            exact absurd ((ordOf_lt_iff).mpr h) hp_lt_q'.not_gt
  have coord_coord (k l : Fin n) :
      (q k = q l ↔ q' k = q' l) ∧ (q k < q l ↔ q' k < q' l) := by
    by_cases hk : ordOf (q k) < α <;> by_cases hl : ordOf (q l) < α
    · exact low_coord k l hk hl
    · have hk' : ordOf (q' k) < α := low_ord k hk
      have hl' : α ≤ ordOf (q' l) := high_ge l hl
      have hkl : ordOf (q k) < ordOf (q l) := hk.trans_le (le_of_not_gt hl)
      refine ⟨?_, ?_⟩
      · constructor
        · intro h
          exact absurd (h ▸ hkl) (lt_irrefl _)
        · intro h
          exact absurd (h ▸ (hk'.trans_le hl')) (lt_irrefl _)
      · constructor
        · intro _
          exact (ordOf_lt_iff).mp (hk'.trans_le hl')
        · intro _
          exact (ordOf_lt_iff).mp hkl
    · have hl' : ordOf (q' l) < α := low_ord l hl
      have hk' : α ≤ ordOf (q' k) := high_ge k hk
      have hlk : ordOf (q l) < ordOf (q k) := hl.trans_le (le_of_not_gt hk)
      refine ⟨?_, ?_⟩
      · constructor
        · intro h
          exact absurd (h.symm ▸ hlk) (lt_irrefl _)
        · intro h
          exact absurd (h.symm ▸ (hl'.trans_le hk')) (lt_irrefl _)
      · constructor
        · intro h
          exact absurd ((ordOf_lt_iff).mpr h) hlk.not_gt
        · intro h
          exact absurd ((ordOf_lt_iff).mpr h) (hl'.trans_le hk').not_gt
    · by_cases hk2 : ordOf (q k) < α + δ <;> by_cases hl2 : ordOf (q l) < α + δ
      · have hqk : q' k = q k := q'_inside k hk hk2
        have hql : q' l = q l := q'_inside l hl hl2
        simp [hqk, hql]
      · have hqk : q' k = q k := q'_inside k hk hk2
        have hge : α + δ ≤ ordOf (q l) := le_of_not_gt hl2
        have hinside : α ≤ ordOf (q k) := le_of_not_gt hk
        have hkl : ordOf (q k) < ordOf (q l) := hk2.trans_le hge
        have hkl' : ordOf (q' k) < ordOf (q' l) := by
          rw [hqk]
          exact (inside_lt_shift k ⟨hinside, hk2⟩).trans_le (q'_above_ge l hge)
        refine ⟨?_, ?_⟩
        · constructor
          · intro h
            exact absurd (h ▸ hkl) (lt_irrefl _)
          · intro h
            exact absurd (h ▸ hkl') (lt_irrefl _)
        · constructor
          · intro _
            exact (ordOf_lt_iff).mp hkl'
          · intro _
            exact (ordOf_lt_iff).mp hkl
      · have hql : q' l = q l := q'_inside l hl hl2
        have hge : α + δ ≤ ordOf (q k) := le_of_not_gt hk2
        have hinside : α ≤ ordOf (q l) := le_of_not_gt hl
        have hlk : ordOf (q l) < ordOf (q k) := hl2.trans_le hge
        have hlk' : ordOf (q' l) < ordOf (q' k) := by
          rw [hql]
          exact (inside_lt_shift l ⟨hinside, hl2⟩).trans_le (q'_above_ge k hge)
        refine ⟨?_, ?_⟩
        · constructor
          · intro h
            exact absurd (h.symm ▸ hlk) (lt_irrefl _)
          · intro h
            exact absurd (h.symm ▸ hlk') (lt_irrefl _)
        · constructor
          · intro h
            exact absurd ((ordOf_lt_iff).mpr h) hlk.not_gt
          · intro h
            exact absurd ((ordOf_lt_iff).mpr h) hlk'.not_gt
      · have hgek : α + δ ≤ ordOf (q k) := le_of_not_gt hk2
        have hgel : α + δ ≤ ordOf (q l) := le_of_not_gt hl2
        refine ⟨?_, ?_⟩
        · rw [← ordOf_eq_iff, ← ordOf_eq_iff, above_ord_eq k l hgek hgel]
        · rw [← ordOf_lt_iff, ← ordOf_lt_iff, above_ord_lt k l hgek hgel]
  have hq'mem (k : Fin n) : q' k ∈ T := by
    by_cases hk : ordOf (q k) < α
    · exact (hmem _).mpr (Or.inl (by rw [q'_below k hk]; exact hqBmem _))
    · by_cases hk2 : ordOf (q k) < α + δ
      · rw [q'_inside k hk hk2]
        exact (hmem _).mpr (Or.inr ⟨le_of_not_gt hk, hk2⟩)
      · have hge : α + δ ≤ ordOf (q k) := le_of_not_gt hk2
        have hord : ordOf (q' k) = α + shift + aboveRank k := q'_above_ord k hge
        have hlt : ordOf (q' k) < α + δ := by
          rw [hord, add_assoc]
          exact (add_lt_add_iff_left α).2
            (add_nat_lt_of_isSuccLimit hlimδ hshift (aboveRank k))
        exact (hmem _).mpr (Or.inr ⟨le_self_add.trans (q'_above_ge k hge), hlt⟩)
  refine ⟨q', hq'mem, ?_, ?_⟩
  · intro a b
    cases a with
    | inl i =>
      cases b with
      | inl j => simp
      | inr k => exact (param_coord i k).1
    | inr k =>
      cases b with
      | inl j =>
        dsimp [Sum.elim]
        rw [eq_comm, eq_comm (a := q' k)]
        exact (param_coord j k).1
      | inr l => exact (coord_coord k l).1
  · intro a b
    cases a with
    | inl i =>
      cases b with
      | inl j => simp
      | inr k => exact (param_coord i k).2.1
    | inr k =>
      cases b with
      | inl j => exact (param_coord j k).2.2
      | inr l => exact (coord_coord k l).2

/-- Moving the second vector along an order embedding that fixes the first vector's support
preserves the colexicographic comparison. This is the finite-support form of Lemma 3.2. -/
lemma colex_relocate {α : Type v} {M : Type w} [LinearOrder α] [AddCommMonoid M] [LinearOrder M]
    (a b : Colex (α →₀ M)) (s : Finset α)
    (ha : (ofColex a).support ⊆ s) (hb : (ofColex b).support ⊆ s)
    (ρ : {i // i ∈ s} ↪o α)
    (hfix : ∀ i : {i // i ∈ s}, (ofColex a) i.1 ≠ 0 → ρ i = i.1) :
    let bPush := embDomain ρ.toEmbedding
      (comapDomain Subtype.val (ofColex b) Subtype.val_injective.injOn)
    let b' : Colex (α →₀ M) := toColex bPush
    (a = b ↔ a = b') ∧ (a < b ↔ a < b') ∧ (b < a ↔ b' < a) := by
  intro bPush b'
  let aval : α →₀ M := ofColex a
  let bval : α →₀ M := ofColex b
  have coeff_eq (i : {x // x ∈ s}) : aval (ρ i) = aval i.1 := by
    by_cases hz : aval i.1 = 0
    · by_cases hρ : ρ i = i.1
      · rw [hρ, hz]
      · suffices h0 : aval (ρ i) = 0 by rw [h0, hz]
        by_contra hne
        have hmem : ρ i ∈ s := ha (mem_support_iff.mpr hne)
        have hfixρ : ρ ⟨ρ i, hmem⟩ = ρ i := hfix ⟨ρ i, hmem⟩ hne
        have heq : (⟨ρ i, hmem⟩ : {x // x ∈ s}) = i := ρ.injective hfixρ
        exact hne (by rw [show ρ i = i.1 from congrArg Subtype.val heq, hz])
    · rw [hfix i hz]
  have push_eq (i : {x // x ∈ s}) : bPush (ρ i) = bval i.1 := by
    have hcoe : ρ.toEmbedding i = ρ i := rfl
    unfold bPush
    rw [← hcoe, embDomain_apply_self, comapDomain_apply]
  have b'_eq (j : α) : ofColex b' j = bPush j := by
    simp [b', ofColex_toColex]
  have tail_forward (i : α) (his : i ∈ s)
      (hi : ∀ j, i < j → aval j = bval j) (j : α) (hj : ρ ⟨i, his⟩ < j) :
      aval j = bPush j := by
    by_cases hmem : j ∈ Set.range (⇑ρ)
    · obtain ⟨m, hm⟩ := hmem
      have hmgt : i < m.1 := by
        by_contra hle
        have hle' : m ≤ (⟨i, his⟩ : {x // x ∈ s}) :=
          Subtype.coe_le_coe.mpr (le_of_not_gt hle)
        have hρle : ρ m ≤ ρ ⟨i, his⟩ := ρ.monotone hle'
        have hρlt : ρ ⟨i, his⟩ < ρ m := by
          rw [hm]
          exact hj
        exact not_lt_of_ge hρle hρlt
      calc aval j = aval m.1 := by rw [← hm, coeff_eq]
        _ = bval m.1 := hi m.1 hmgt
        _ = bPush j := by rw [← hm, push_eq]
    · have hb0 : bPush j = 0 := embDomain_of_notMem_range _ _ j hmem
      have ha0 : aval j = 0 := by
        by_contra hne
        have hjs : j ∈ s := ha (mem_support_iff.mpr hne)
        exact hmem ⟨⟨j, hjs⟩, hfix ⟨j, hjs⟩ hne⟩
      rw [ha0, hb0]
  have hlt : a < b ↔ a < b' := by
    constructor
    · intro h
      rw [Colex.lt_iff] at h ⊢
      obtain ⟨i, hi, hlt⟩ := h
      have hne : aval i ≠ bval i := hlt.ne
      have his : i ∈ s := by
        by_cases h0 : aval i = 0
        · exact hb (mem_support_iff.mpr (by
            intro hb0
            exact hne (by rw [h0, hb0])))
        · exact ha (mem_support_iff.mpr h0)
      refine ⟨ρ ⟨i, his⟩, ?_, ?_⟩
      · intro j hj
        rw [b'_eq]
        exact tail_forward i his hi j hj
      · rw [b'_eq, coeff_eq, push_eq]
        exact hlt
    · intro h
      rw [Colex.lt_iff] at h ⊢
      obtain ⟨j, hj, hlt⟩ := h
      have hjrange : j ∈ Set.range (⇑ρ) := by
        by_cases ha0 : aval j = 0
        · have hb0 : bPush j ≠ 0 := by
            intro hb0
            exact hlt.ne (by rw [b'_eq, ha0, hb0])
          have hsup : j ∈ bPush.support := mem_support_iff.mpr hb0
          have hmap : j ∈
              (comapDomain Subtype.val bval Subtype.val_injective.injOn).support.map ρ.toEmbedding := by
            simpa [bPush, support_embDomain] using hsup
          obtain ⟨m, _, hm⟩ := Finset.mem_map.mp hmap
          exact ⟨m, hm⟩
        · have hjs : j ∈ s := ha (mem_support_iff.mpr ha0)
          exact ⟨⟨j, hjs⟩, hfix ⟨j, hjs⟩ ha0⟩
      obtain ⟨m, hm⟩ := hjrange
      refine ⟨m.1, ?_, ?_⟩
      · intro k hk
        by_contra hne
        have hks : k ∈ s := by
          by_cases h0 : aval k = 0
          · exact hb (mem_support_iff.mpr (by
              intro hb0
              exact hne (by rw [h0, hb0])))
          · exact ha (mem_support_iff.mpr h0)
        have hρ : j < ρ ⟨k, hks⟩ := by
          rw [← hm]
          exact (ρ.lt_iff_lt).mpr (Subtype.mk_lt_mk.mpr hk)
        have hdiff : aval (ρ ⟨k, hks⟩) ≠ bPush (ρ ⟨k, hks⟩) := by
          rw [coeff_eq, push_eq]
          exact hne
        have hagree : aval (ρ ⟨k, hks⟩) = bPush (ρ ⟨k, hks⟩) := by
          rw [← b'_eq]
          exact hj _ hρ
        exact hdiff hagree
      · rw [← coeff_eq m, ← push_eq m, ← b'_eq, hm]
        exact hlt
  have hgt : b < a ↔ b' < a := by
    constructor
    · intro h
      rw [Colex.lt_iff] at h ⊢
      obtain ⟨i, hi, hlt⟩ := h
      have hne : bval i ≠ aval i := hlt.ne
      have his : i ∈ s := by
        by_cases h0 : bval i = 0
        · exact ha (mem_support_iff.mpr (by
            intro ha0
            exact hne (by rw [h0, ha0])))
        · exact hb (mem_support_iff.mpr h0)
      refine ⟨ρ ⟨i, his⟩, ?_, ?_⟩
      · intro j hj
        rw [b'_eq]
        exact (tail_forward i his (fun j hj => (hi j hj).symm) j hj).symm
      · rw [b'_eq, coeff_eq, push_eq]
        exact hlt
    · intro h
      rw [Colex.lt_iff] at h ⊢
      obtain ⟨j, hj, hlt⟩ := h
      have hjrange : j ∈ Set.range (⇑ρ) := by
        by_cases hb0 : bPush j = 0
        · have ha0 : aval j ≠ 0 := by
            intro ha0
            exact hlt.ne (by rw [b'_eq, ha0, hb0])
          have hjs : j ∈ s := ha (mem_support_iff.mpr ha0)
          exact ⟨⟨j, hjs⟩, hfix ⟨j, hjs⟩ ha0⟩
        · have hsup : j ∈ bPush.support := mem_support_iff.mpr hb0
          have hmap : j ∈
              (comapDomain Subtype.val bval Subtype.val_injective.injOn).support.map ρ.toEmbedding := by
            simpa [bPush, support_embDomain] using hsup
          obtain ⟨m, _, hm⟩ := Finset.mem_map.mp hmap
          exact ⟨m, hm⟩
      obtain ⟨m, hm⟩ := hjrange
      refine ⟨m.1, ?_, ?_⟩
      · intro k hk
        by_contra hne
        have hks : k ∈ s := by
          by_cases h0 : bval k = 0
          · exact ha (mem_support_iff.mpr (by
              intro ha0
              exact hne (by rw [h0, ha0])))
          · exact hb (mem_support_iff.mpr h0)
        have hρ : j < ρ ⟨k, hks⟩ := by
          rw [← hm]
          exact (ρ.lt_iff_lt).mpr (Subtype.mk_lt_mk.mpr hk)
        have hdiff : bPush (ρ ⟨k, hks⟩) ≠ aval (ρ ⟨k, hks⟩) := by
          rw [coeff_eq, push_eq]
          exact hne
        have hagree : bPush (ρ ⟨k, hks⟩) = aval (ρ ⟨k, hks⟩) := by
          rw [← b'_eq]
          exact hj _ hρ
        exact hdiff hagree
      · rw [← push_eq m, ← coeff_eq m, ← b'_eq, hm]
        exact hlt
  refine ⟨?_, hlt, hgt⟩
  constructor
  · intro heq
    have hnotlt : ¬ a < b := by
      intro h
      rw [heq] at h
      exact lt_irrefl _ h
    have hnotgt : ¬ b < a := by
      intro h
      rw [heq] at h
      exact lt_irrefl _ h
    exact le_antisymm (le_of_not_gt (mt hgt.mpr hnotgt)) (le_of_not_gt (mt hlt.mpr hnotlt))
  · intro heq
    have hnotlt : ¬ a < b' := by
      intro h
      rw [heq] at h
      exact lt_irrefl _ h
    have hnotgt : ¬ b' < a := by
      intro h
      rw [heq] at h
      exact lt_irrefl _ h
    exact le_antisymm (le_of_not_gt (mt hgt.mp hnotgt)) (le_of_not_gt (mt hlt.mp hnotlt))

/-- A pair of vectors supported inside `s` compares the same way as the pair read on `s`. -/
lemma colex_comap_lt {α : Type v} {M : Type w} [LinearOrder α] [AddCommMonoid M] [LinearOrder M]
    (s : Finset α) (g h : Colex (α →₀ M))
    (hg : (ofColex g).support ⊆ s) (hh : (ofColex h).support ⊆ s) :
    g < h ↔
      toColex (comapDomain (Subtype.val : {x // x ∈ s} → α) (ofColex g)
        Subtype.val_injective.injOn) <
        toColex (comapDomain (Subtype.val : {x // x ∈ s} → α) (ofColex h)
          Subtype.val_injective.injOn) := by
  let gS := toColex (comapDomain (Subtype.val : {x // x ∈ s} → α) (ofColex g)
    Subtype.val_injective.injOn)
  let hS := toColex (comapDomain (Subtype.val : {x // x ∈ s} → α) (ofColex h)
    Subtype.val_injective.injOn)
  let gval := ofColex g
  let hval := ofColex h
  have gS_eq (i : {x // x ∈ s}) : ofColex gS i = gval i.1 := by
    unfold gS gval
    rw [ofColex_toColex, comapDomain_apply]
  have hS_eq (i : {x // x ∈ s}) : ofColex hS i = hval i.1 := by
    unfold hS hval
    rw [ofColex_toColex, comapDomain_apply]
  constructor
  · intro hlt
    rw [Colex.lt_iff] at hlt ⊢
    obtain ⟨i, hi, hcoeff⟩ := hlt
    have his : i ∈ s := by
      by_cases h0 : gval i = 0
      · exact hh (mem_support_iff.mpr (by
          intro hhz
          exact hcoeff.ne (by rw [h0, hhz])))
      · exact hg (mem_support_iff.mpr h0)
    refine ⟨⟨i, his⟩, ?_, ?_⟩
    · intro j hj
      rw [gS_eq, hS_eq]
      exact hi j.1 (Subtype.coe_lt_coe.mp hj)
    · rw [gS_eq, hS_eq]
      exact hcoeff
  · intro hlt
    rw [Colex.lt_iff] at hlt ⊢
    obtain ⟨i, hi, hcoeff⟩ := hlt
    refine ⟨i.1, ?_, ?_⟩
    · intro j hj
      by_cases hjs : j ∈ s
      · have hij : i < (⟨j, hjs⟩ : {x // x ∈ s}) := Subtype.coe_lt_coe.mpr hj
        have hagree := hi ⟨j, hjs⟩ hij
        rw [gS_eq, hS_eq] at hagree
        exact hagree
      · have hg0 : gval j = 0 := by
          by_contra hne
          exact hjs (hg (mem_support_iff.mpr hne))
        have hh0 : hval j = 0 := by
          by_contra hne
          exact hjs (hh (mem_support_iff.mpr hne))
        rw [hg0, hh0]
    · rw [← gS_eq, ← hS_eq]
      exact hcoeff

/-- Pushing two vectors along one order embedding of a common support preserves their comparison. -/
lemma colex_image_lt {α : Type v} {M : Type w} [LinearOrder α] [AddCommMonoid M] [LinearOrder M]
    [DecidableEq α] (s : Finset α) (ρ : {i // i ∈ s} ↪o α)
    (g h : Colex (α →₀ M))
    (hg : (ofColex g).support ⊆ s) (hh : (ofColex h).support ⊆ s) :
    let gPush := toColex (embDomain ρ.toEmbedding
      (comapDomain (Subtype.val : {x // x ∈ s} → α) (ofColex g) Subtype.val_injective.injOn))
    let hPush := toColex (embDomain ρ.toEmbedding
      (comapDomain (Subtype.val : {x // x ∈ s} → α) (ofColex h) Subtype.val_injective.injOn))
    g < h ↔ gPush < hPush := by
  intro gPush hPush
  let gS := toColex (comapDomain (Subtype.val : {x // x ∈ s} → α) (ofColex g)
    Subtype.val_injective.injOn)
  let hS := toColex (comapDomain (Subtype.val : {x // x ∈ s} → α) (ofColex h)
    Subtype.val_injective.injOn)
  have hgS : g < h ↔ gS < hS := colex_comap_lt s g h hg hh
  have hpushG : gPush = colexPush ρ gS := by
    apply ofColex.injective
    unfold colexPush gPush gS
    rw [OrderEmbedding.coe_ofStrictMono, ofColex_toColex, ofColex_toColex, ofColex_toColex,
      embDomain_eq_mapDomain]
    rfl
  have hpushH : hPush = colexPush ρ hS := by
    apply ofColex.injective
    unfold colexPush hPush hS
    rw [OrderEmbedding.coe_ofStrictMono, ofColex_toColex, ofColex_toColex, ofColex_toColex,
      embDomain_eq_mapDomain]
    rfl
  rw [hgS, hpushG, hpushH]
  exact (colexPush ρ).lt_iff_lt.symm

/-- A point of `H(β)` supported on the image of an ordinal embedding is the image of a point of `H(δ)`. -/
lemma horder_supported_pull {δ β : _root_.Ordinal.{u}} (φ : OrdIndex δ ↪o OrdIndex β)
    (x : HOrder β)
    (hx : ∀ g ∈ (ofColex x).support, ∀ i ∈ (ofColex g).support, i ∈ Set.range (⇑φ)) :
    ∃ w : HOrder δ, horderPush φ w = x := by
  letI : DecidableEq (OrdIndex β) := Classical.decEq _
  let φΓ : Gamma δ ↪o Gamma β := colexPush φ
  letI : DecidableEq (Gamma β) := Classical.decEq _
  let pullG (g : Gamma β) : Gamma δ :=
    toColex (comapDomain (⇑φ) (ofColex g) φ.injective.injOn)
  have hpull (g : Gamma β) (hg : ∀ i ∈ (ofColex g).support, i ∈ Set.range (⇑φ)) :
      φΓ (pullG g) = g := by
    apply ofColex.injective
    unfold φΓ colexPush pullG
    rw [OrderEmbedding.coe_ofStrictMono, ofColex_toColex, ofColex_toColex]
    exact mapDomain_comapDomain (⇑φ) φ.injective (ofColex g) (by
      intro i hi
      exact hg i hi)
  have hrange : ∀ g ∈ (ofColex x).support, g ∈ Set.range (⇑φΓ) := by
    intro g hg
    exact ⟨pullG g, hpull g (hx g hg)⟩
  refine ⟨toColex (comapDomain (⇑φΓ) (ofColex x) φΓ.injective.injOn), ?_⟩
  have happly : horderPush φ (toColex (comapDomain (⇑φΓ) (ofColex x) φΓ.injective.injOn)) =
      colexPush (M := ℚ) φΓ (toColex (comapDomain (⇑φΓ) (ofColex x) φΓ.injective.injOn)) := by
    rfl
  rw [happly]
  apply ofColex.injective
  unfold colexPush
  rw [OrderEmbedding.coe_ofStrictMono, ofColex_toColex, ofColex_toColex]
  exact mapDomain_comapDomain (⇑φΓ) φΓ.injective (ofColex x) hrange

/-- An order embedding preserves occupancy of a strict slot. -/
lemma occupied_of_orderEmbedding {α β : Type v} {ι : Type w} [LinearOrder α] [LinearOrder β]
    (f : α ↪o β) (xs : ι → α) (lower upper : Set ι) :
    Occupied (xs '' lower) (xs '' upper) →
      Occupied ((fun i => f (xs i)) '' lower) ((fun i => f (xs i)) '' upper) := by
  intro ⟨w, hw⟩
  refine ⟨f w, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hmem
    obtain ⟨i, hi, heq⟩ := (mem_image _ _ _).mp hmem
    exact hw.1 ((mem_image _ _ _).mpr ⟨i, hi, f.injective heq⟩)
  · intro hmem
    obtain ⟨i, hi, heq⟩ := (mem_image _ _ _).mp hmem
    exact hw.2.1 ((mem_image _ _ _).mpr ⟨i, hi, f.injective heq⟩)
  · intro a hmem
    obtain ⟨i, hi, rfl⟩ := (mem_image _ _ _).mp hmem
    exact (f.lt_iff_lt).mpr (hw.2.2.1 (xs i) ((mem_image _ _ _).mpr ⟨i, hi, rfl⟩))
  · intro b hmem
    obtain ⟨i, hi, rfl⟩ := (mem_image _ _ _).mp hmem
    exact (f.lt_iff_lt).mpr (hw.2.2.2 (xs i) ((mem_image _ _ _).mpr ⟨i, hi, rfl⟩))

/-- The ordinal positions appearing in the finite code of a point of `H`. -/
noncomputable def hSupport {β : _root_.Ordinal.{u}} (x : HOrder β) : Finset (OrdIndex β) :=
  letI : DecidableEq (Gamma β) := Classical.decEq _
  letI : DecidableEq (OrdIndex β) := Classical.decEq _
  (ofColex x).support.biUnion fun g => (ofColex g).support

/-- `OrdIndex` and the initial segment used by `ToType` name the same ordinals. -/
def asIio {o : _root_.Ordinal.{u}} (i : OrdIndex o) : Set.Iio o := ⟨i.1, i.2⟩

def asOrdIndex {o : _root_.Ordinal.{u}} (i : Set.Iio o) : OrdIndex o := ⟨i.1, i.2⟩

/-- The order isomorphism of the appended segment, read as an embedding of ordinal positions. -/
noncomputable def segmentPosition {β δ : _root_.Ordinal.{u}} {T : Set β.ToType}
    (e : ↥T ≃o δ.ToType) : OrdIndex δ ↪o OrdIndex β :=
  OrderEmbedding.ofStrictMono
    (fun i : OrdIndex δ =>
      asOrdIndex ((Ordinal.ToType.mk (o := β)).symm (e.symm (Ordinal.ToType.mk (asIio i))).1)) <| by
    intro i j hij
    have h1 : Ordinal.ToType.mk (asIio i) < Ordinal.ToType.mk (asIio j) :=
      (Ordinal.ToType.mk.lt_iff_lt).mpr (Subtype.mk_lt_mk.mpr hij)
    have h2 : e.symm (Ordinal.ToType.mk (asIio i)) < e.symm (Ordinal.ToType.mk (asIio j)) :=
      (e.symm.lt_iff_lt).mpr h1
    have h3 : (e.symm (Ordinal.ToType.mk (asIio i))).1 <
        (e.symm (Ordinal.ToType.mk (asIio j))).1 :=
      (Subtype.coe_lt_coe (x := e.symm (Ordinal.ToType.mk (asIio i)))
        (y := e.symm (Ordinal.ToType.mk (asIio j)))).mp h2
    have h4 := ((Ordinal.ToType.mk (o := β)).symm.lt_iff_lt).mpr h3
    exact Subtype.mk_lt_mk.mpr h4

lemma segmentPosition_mem {β δ : _root_.Ordinal.{u}} {T : Set β.ToType}
    (e : ↥T ≃o δ.ToType) (i : OrdIndex δ) :
    Ordinal.ToType.mk (asIio (segmentPosition e i)) ∈ T := by
  have : Ordinal.ToType.mk (asIio (segmentPosition e i)) =
      (e.symm (Ordinal.ToType.mk (asIio i))).1 := by
    simp [segmentPosition, asOrdIndex, asIio, OrderEmbedding.coe_ofStrictMono,
      OrderIso.apply_symm_apply]
  rw [this]
  exact Subtype.coe_prop _

/-- Match the ordinal positions of one finite support into `T`, fixing every parameter position. -/
lemma exists_position_embedding {θ : Cardinal.{u}} {β : _root_.Ordinal.{u}}
    (T : Set β.ToType)
    (hpat : ∀ {ι : Type u} (_hι : #ι ≤ θ) (p : ι → β.ToType), (∀ i, p i ∈ T) →
      ∀ {n : ℕ} (q : Fin n → β.ToType), ∃ q' : Fin n → β.ToType,
        (∀ k, q' k ∈ T) ∧ SameOrderDiagram (Sum.elim p q) (Sum.elim p q'))
    (param : Set β.ToType) (hcard : #↥param ≤ θ) (hparamT : ∀ x ∈ param, x ∈ T)
    (s : Finset (OrdIndex β)) :
    ∃ ρ : {i // i ∈ s} ↪o OrdIndex β,
      (∀ i, Ordinal.ToType.mk (asIio (ρ i)) ∈ T) ∧
      (∀ i, Ordinal.ToType.mk (asIio i.1) ∈ param → ρ i = i.1) ∧
      (∀ (t : β.ToType) (_ht : t ∈ param) (i : {i // i ∈ s}),
        t < Ordinal.ToType.mk (asIio i.1) ↔ t < Ordinal.ToType.mk (asIio (ρ i))) ∧
      (∀ (t : β.ToType) (_ht : t ∈ param) (i : {i // i ∈ s}),
        t = Ordinal.ToType.mk (asIio i.1) ↔ t = Ordinal.ToType.mk (asIio (ρ i))) := by
  let sType := {i // i ∈ s}
  let eqv : sType ≃ Fin (Fintype.card sType) := Fintype.equivFin sType
  let q : Fin (Fintype.card sType) → β.ToType :=
    fun k => Ordinal.ToType.mk (asIio (eqv.symm k).1)
  obtain ⟨q', hq'T, hq'diag⟩ := hpat hcard (fun t : ↥param => t.1) (fun t => hparamT t.1 t.2) q
  let ρ₀ : sType → OrdIndex β :=
    fun i => asOrdIndex ((Ordinal.ToType.mk (o := β)).symm (q' (eqv i)))
  have hmono : StrictMono ρ₀ := by
    intro i j hij
    have hqlt : q (eqv i) < q (eqv j) := by
      have hi : q (eqv i) = Ordinal.ToType.mk (asIio i.1) := by
        unfold q
        rw [Equiv.symm_apply_apply]
      have hj : q (eqv j) = Ordinal.ToType.mk (asIio j.1) := by
        unfold q
        rw [Equiv.symm_apply_apply]
      rw [hi, hj]
      have hidx : i.1 < j.1 := Subtype.coe_lt_coe.mp hij
      exact (Ordinal.ToType.mk.lt_iff_lt).mpr (Subtype.mk_lt_mk.mpr (Subtype.mk_lt_mk.mp hidx))
    have hq'lt : q' (eqv i) < q' (eqv j) :=
      (hq'diag.2 (Sum.inr (eqv i)) (Sum.inr (eqv j))).mp hqlt
    exact Subtype.mk_lt_mk.mpr (((Ordinal.ToType.mk (o := β)).symm.lt_iff_lt).mpr hq'lt)
  have hρmem (i : sType) : Ordinal.ToType.mk (asIio (ρ₀ i)) ∈ T := by
    have : Ordinal.ToType.mk (asIio (ρ₀ i)) = q' (eqv i) := by
      simp [ρ₀, asOrdIndex, asIio, OrderIso.apply_symm_apply]
    rw [this]
    exact hq'T (eqv i)
  have hρfix (i : sType) (hi : Ordinal.ToType.mk (asIio i.1) ∈ param) : ρ₀ i = i.1 := by
    let t : ↥param := ⟨Ordinal.ToType.mk (asIio i.1), hi⟩
    have hqeq : q (eqv i) = t.1 := by
      unfold q
      rw [Equiv.symm_apply_apply]
    have hleft : Sum.elim (fun u : ↥param => u.1) q (Sum.inl t) = t.1 := rfl
    have hright : Sum.elim (fun u : ↥param => u.1) q (Sum.inr (eqv i)) = q (eqv i) := rfl
    have hsame : Sum.elim (fun u : ↥param => u.1) q (Sum.inl t) =
        Sum.elim (fun u : ↥param => u.1) q (Sum.inr (eqv i)) := by
      rw [hleft, hright, hqeq]
    have hfixq : q' (eqv i) = t.1 := by
      have hmatched := (hq'diag.1 (Sum.inl t) (Sum.inr (eqv i))).mp hsame
      change t.1 = q' (eqv i) at hmatched
      exact hmatched.symm
    apply Subtype.ext
    change (asOrdIndex ((Ordinal.ToType.mk (o := β)).symm (q' (eqv i)))).1 = i.1.1
    rw [hfixq, show t.1 = Ordinal.ToType.mk (asIio i.1) from rfl, asOrdIndex,
      OrderIso.symm_apply_apply]
    rfl
  have hcross (t : β.ToType) (ht : t ∈ param) (i : sType) :
      t < Ordinal.ToType.mk (asIio i.1) ↔ t < Ordinal.ToType.mk (asIio (ρ₀ i)) := by
    let u : ↥param := ⟨t, ht⟩
    have hqi : q (eqv i) = Ordinal.ToType.mk (asIio i.1) := by
      unfold q
      rw [Equiv.symm_apply_apply]
    have hq'i : Ordinal.ToType.mk (asIio (ρ₀ i)) = q' (eqv i) := by
      simp [ρ₀, asOrdIndex, asIio, OrderIso.apply_symm_apply]
    have hdiag := hq'diag.2 (Sum.inl u) (Sum.inr (eqv i))
    rw [← hqi, hq'i]
    simpa [Sum.elim] using hdiag
  have heq (t : β.ToType) (ht : t ∈ param) (i : sType) :
      t = Ordinal.ToType.mk (asIio i.1) ↔ t = Ordinal.ToType.mk (asIio (ρ₀ i)) := by
    let u : ↥param := ⟨t, ht⟩
    have hqi : q (eqv i) = Ordinal.ToType.mk (asIio i.1) := by
      unfold q
      rw [Equiv.symm_apply_apply]
    have hq'i : Ordinal.ToType.mk (asIio (ρ₀ i)) = q' (eqv i) := by
      simp [ρ₀, asOrdIndex, asIio, OrderIso.apply_symm_apply]
    constructor
    · intro hteq
      have hsame : Sum.elim (fun v : ↥param => v.1) q (Sum.inl u) =
          Sum.elim (fun v : ↥param => v.1) q (Sum.inr (eqv i)) := by
        dsimp [Sum.elim]
        rw [hqi]
        exact hteq
      have hmatched := (hq'diag.1 (Sum.inl u) (Sum.inr (eqv i))).mp hsame
      change t = q' (eqv i) at hmatched
      rw [← hq'i] at hmatched
      exact hmatched
    · intro hteq
      have hsame : Sum.elim (fun v : ↥param => v.1) q' (Sum.inl u) =
          Sum.elim (fun v : ↥param => v.1) q' (Sum.inr (eqv i)) := by
        dsimp [Sum.elim]
        rw [← hq'i]
        exact hteq
      have hmatched := (hq'diag.1 (Sum.inl u) (Sum.inr (eqv i))).mpr hsame
      change t = q (eqv i) at hmatched
      rw [hqi] at hmatched
      exact hmatched
  refine ⟨OrderEmbedding.ofStrictMono ρ₀ hmono,
    fun i => by simpa [OrderEmbedding.coe_ofStrictMono] using hρmem i,
    fun i hi => by simpa [OrderEmbedding.coe_ofStrictMono] using hρfix i hi,
    fun t ht i => by simpa [OrderEmbedding.coe_ofStrictMono] using hcross t ht i,
    fun t ht i => by simpa [OrderEmbedding.coe_ofStrictMono] using heq t ht i⟩

/-- `embDomain` does not see coordinates outside the relevant support. -/
lemma embDomain_of_agree {α γ β : Type v} {M : Type w} [AddCommMonoid M]
    (f : α ↪ β) (g : γ ↪ β) (e : α ↪ γ) (v : α →₀ M) (w : γ →₀ M)
    (hagree : ∀ a, g (e a) = f a) (hw : ∀ a, w (e a) = v a)
    (hzero : ∀ c, c ∉ Set.range (⇑e) → w c = 0) : embDomain f v = embDomain g w := by
  ext b
  by_cases hb : b ∈ Set.range (⇑f)
  · obtain ⟨a, rfl⟩ := hb
    rw [embDomain_apply_self, ← hagree, embDomain_apply_self, hw]
  · rw [embDomain_of_notMem_range _ _ _ hb]
    by_cases hb' : b ∈ Set.range (⇑g)
    · obtain ⟨c, rfl⟩ := hb'
      rw [embDomain_apply_self]
      have hnot : c ∉ Set.range (⇑e) := by
        intro ⟨a, ha⟩
        exact hb ⟨a, by rw [← hagree, ha]⟩
      exact (hzero c hnot).symm
    · exact (embDomain_of_notMem_range _ _ _ hb').symm

/-- Push the finite code of `z` along an order embedding of a set of ordinal positions. -/
noncomputable def canonicalPush {β : _root_.Ordinal.{u}} (s : Finset (OrdIndex β))
    (ρ : {i // i ∈ s} ↪o OrdIndex β) (z : HOrder β)
    (hz : ∀ g ∈ (ofColex z).support, ∀ i ∈ (ofColex g).support, i ∈ s) : HOrder β :=
  letI : DecidableEq (OrdIndex β) := Classical.decEq _
  letI : DecidableEq (Gamma β) := Classical.decEq _
  let sΓ : Finset (Gamma β) := (ofColex z).support
  let pushG (g : Gamma β) : Gamma β :=
    toColex (embDomain ρ.toEmbedding
      (comapDomain (Subtype.val : {x // x ∈ s} → OrdIndex β) (ofColex g)
        Subtype.val_injective.injOn))
  let ρΓ : {g // g ∈ sΓ} ↪o Gamma β :=
    OrderEmbedding.ofStrictMono (fun g => pushG g.1) (by
      intro g h hlt
      exact (colex_image_lt s ρ g.1 h.1 (fun i hi => hz g.1 g.2 i hi)
        (fun i hi => hz h.1 h.2 i hi)).mp hlt)
  toColex (embDomain ρΓ.toEmbedding
    (comapDomain (Subtype.val : {g // g ∈ sΓ} → Gamma β) (ofColex z)
      Subtype.val_injective.injOn))

/-- Move a witness along an ordinal embedding that fixes one point of `H`, and pull the result
back to `H(δ)`. Comparisons with that point are unchanged. -/
lemma relocate_witness {δ β : _root_.Ordinal.{u}} (φ : OrdIndex δ ↪o OrdIndex β)
    (a : HOrder δ) (z : HOrder β) (s : Finset (OrdIndex β))
    (ha : ∀ g ∈ (ofColex (horderPush φ a)).support, ∀ i ∈ (ofColex g).support, i ∈ s)
    (hz : ∀ g ∈ (ofColex z).support, ∀ i ∈ (ofColex g).support, i ∈ s)
    (ρ : {i // i ∈ s} ↪o OrdIndex β)
    (hfix : ∀ i : {i // i ∈ s},
      (∃ g ∈ (ofColex (horderPush φ a)).support, i.1 ∈ (ofColex g).support) → ρ i = i.1)
    (hrange : ∀ i, ρ i ∈ Set.range (⇑φ)) :
    ∃ w : HOrder δ, (horderPush φ a = z ↔ a = w) ∧ (horderPush φ a < z ↔ a < w) ∧
      (z < horderPush φ a ↔ w < a) ∧
      horderPush φ w = canonicalPush s ρ z hz := by
  letI : DecidableEq (OrdIndex β) := Classical.decEq _
  letI : DecidableEq (Gamma β) := Classical.decEq _
  let A : HOrder β := horderPush φ a
  let sΓ : Finset (Gamma β) := (ofColex A).support ∪ (ofColex z).support
  let pushG (g : Gamma β) : Gamma β :=
    toColex (embDomain ρ.toEmbedding
      (comapDomain (Subtype.val : {x // x ∈ s} → OrdIndex β) (ofColex g)
        Subtype.val_injective.injOn))
  have push_id (g : Gamma β) (hgsup : (ofColex g).support ⊆ s)
      (hfixg : ∀ i : {i // i ∈ s}, (ofColex g) i.1 ≠ 0 → ρ i = i.1) : pushG g = g := by
    apply ofColex.injective
    ext j
    by_cases hj : j ∈ Set.range (⇑ρ)
    · obtain ⟨i, rfl⟩ := hj
      have hleft : ofColex (pushG g) (ρ i) = (ofColex g) i.1 := by
        unfold pushG
        rw [ofColex_toColex]
        have hcoe : ρ.toEmbedding i = ρ i := rfl
        rw [← hcoe, embDomain_apply_self, comapDomain_apply]
      rw [hleft]
      by_cases h0 : (ofColex g) i.1 = 0
      · suffices (ofColex g) (ρ i) = 0 by rw [h0, this]
        by_contra hne
        have hmem : ρ i ∈ s := hgsup (mem_support_iff.mpr hne)
        have hfixed : ρ ⟨ρ i, hmem⟩ = ρ i := hfixg ⟨ρ i, hmem⟩ hne
        have heqi : (⟨ρ i, hmem⟩ : {x // x ∈ s}) = i := ρ.injective hfixed
        have hpos : (ofColex g) i.1 ≠ 0 := by
          rw [show i.1 = ρ i from (congrArg Subtype.val heqi).symm]
          exact hne
        exact hpos h0
      · rw [hfixg i h0]
    · have hpush0 : ofColex (pushG g) j = 0 := by
        unfold pushG
        rw [ofColex_toColex]
        exact embDomain_of_notMem_range _ _ j hj
      suffices (ofColex g) j = 0 by rw [hpush0, this]
      by_contra hne
      have hmem : j ∈ s := hgsup (mem_support_iff.mpr hne)
      exact hj ⟨⟨j, hmem⟩, hfixg ⟨j, hmem⟩ hne⟩
  have hγsupp (g : {g // g ∈ sΓ}) : (ofColex g.1).support ⊆ s := by
    intro i hi
    rcases Finset.mem_union.mp g.2 with hg | hg
    · exact ha g.1 hg i hi
    · exact hz g.1 hg i hi
  let ρΓ₀ : {g // g ∈ sΓ} → Gamma β := fun g => pushG g.1
  have hγmono : StrictMono ρΓ₀ := by
    intro g h hlt
    have hcmp := colex_image_lt s ρ g.1 h.1 (hγsupp g) (hγsupp h)
    have hpush : pushG g.1 < pushG h.1 := by
      have : g.1 < h.1 := hlt
      -- hcmp equates the order of the vectors with the order of their pushes
      have hleft : g.1 < h.1 := this
      exact (hcmp.mp hleft)
    exact hpush
  let ρΓ : {g // g ∈ sΓ} ↪o Gamma β := OrderEmbedding.ofStrictMono ρΓ₀ hγmono
  have hfixΓ : ∀ i : {g // g ∈ sΓ}, (ofColex A) i.1 ≠ 0 → ρΓ i = i.1 := by
    intro i hne
    have hmem : i.1 ∈ (ofColex A).support := mem_support_iff.mpr hne
    have hfixg : ∀ j : {j // j ∈ s}, (ofColex i.1) j.1 ≠ 0 → ρ j = j.1 := by
      intro j hj
      exact hfix j ⟨i.1, hmem, mem_support_iff.mpr hj⟩
    have hgsup : (ofColex i.1).support ⊆ s := by
      intro j hj
      exact ha i.1 hmem j hj
    have hid := push_id i.1 hgsup hfixg
    simpa [ρΓ, ρΓ₀, OrderEmbedding.coe_ofStrictMono] using hid
  have hrel := colex_relocate A z sΓ
    (by intro g hg; exact Finset.mem_union_left _ hg)
    (by intro g hg; exact Finset.mem_union_right _ hg) ρΓ hfixΓ
  let z' : HOrder β := toColex (embDomain ρΓ.toEmbedding
    (comapDomain (Subtype.val : {g // g ∈ sΓ} → Gamma β) (ofColex z) Subtype.val_injective.injOn))
  have hzrange : ∀ g ∈ (ofColex z').support, ∀ i ∈ (ofColex g).support, i ∈ Set.range (⇑φ) := by
    intro g hg i hi
    have hgin : g ∈ Set.range (⇑ρΓ) := by
      have hsup : g ∈ (embDomain ρΓ.toEmbedding
          (comapDomain (Subtype.val : {g // g ∈ sΓ} → Gamma β) (ofColex z)
            Subtype.val_injective.injOn)).support := by
        simpa [z', ofColex_toColex] using hg
      rw [support_embDomain] at hsup
      obtain ⟨m, _, hm⟩ := Finset.mem_map.mp hsup
      exact ⟨m, hm⟩
    obtain ⟨m, hm⟩ := hgin
    have hord : i ∈ Set.range (⇑ρ) := by
      have hpush : g = pushG m.1 := by
        simpa [ρΓ, ρΓ₀, OrderEmbedding.coe_ofStrictMono] using hm.symm
      have hsupi : i ∈ (ofColex (pushG m.1)).support := by rw [← hpush]; exact hi
      unfold pushG at hsupi
      rw [ofColex_toColex, support_embDomain] at hsupi
      obtain ⟨k, _, hk⟩ := Finset.mem_map.mp hsupi
      exact ⟨k, hk⟩
    obtain ⟨k, hk⟩ := hord
    rw [← hk]
    exact hrange k
  obtain ⟨w, hw⟩ := horder_supported_pull φ z' hzrange
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro hAz
      have hAz' : A = z' := by simpa [z'] using (hrel.1).mp hAz
      have : horderPush φ a = horderPush φ w := by simpa [A, hw] using hAz'
      exact (horderPush φ).injective this
    · intro haw
      have : A = z' := by simpa [A, hw] using congrArg (horderPush φ) haw
      simpa [z'] using (hrel.1).mpr this
  · constructor
    · intro hlt
      have : A < z' := by simpa [z'] using (hrel.2.1).mp hlt
      exact (horderPush φ).lt_iff_lt.mp (by simpa [A, hw] using this)
    · intro hlt
      have : A < z' := by simpa [A, hw] using (horderPush φ).lt_iff_lt.mpr hlt
      simpa [z'] using (hrel.2.1).mpr this
  · constructor
    · intro hlt
      have : z' < A := by simpa [z'] using (hrel.2.2).mp hlt
      exact (horderPush φ).lt_iff_lt.mp (by simpa [A, hw] using this)
    · intro hlt
      have : z' < A := by simpa [A, hw] using (horderPush φ).lt_iff_lt.mpr hlt
      simpa [z'] using (hrel.2.2).mpr this
  · rw [hw]
    apply ofColex.injective
    unfold canonicalPush z'
    rw [ofColex_toColex, ofColex_toColex]
    let small : Type (u + 1) := {g // g ∈ (ofColex z).support}
    let inclFun : small → {g // g ∈ sΓ} := fun m => ⟨m.1, Finset.mem_union_right _ m.2⟩
    have hinj : Function.Injective inclFun := by
      intro m n h
      exact Subtype.ext (congrArg (fun x : {g // g ∈ sΓ} => x.1) h)
    let incl : small ↪ {g // g ∈ sΓ} := ⟨inclFun, hinj⟩
    let pushSmall (g : Gamma β) : Gamma β :=
      toColex (embDomain ρ.toEmbedding
        (comapDomain (Subtype.val : {x // x ∈ s} → OrdIndex β) (ofColex g)
          Subtype.val_injective.injOn))
    let ρSmall : small ↪o Gamma β :=
      OrderEmbedding.ofStrictMono (fun m => pushSmall m.1) (by
        intro m n hlt
        exact (colex_image_lt s ρ m.1 n.1 (fun i hi => hz m.1 m.2 i hi)
          (fun i hi => hz n.1 n.2 i hi)).mp hlt)
    have hagree : ∀ m : small, ρΓ (incl m) = ρSmall m := by
      intro m
      unfold ρΓ ρΓ₀ ρSmall pushG pushSmall incl inclFun
      rw [OrderEmbedding.coe_ofStrictMono]
      rfl
    have hcoeff : ∀ m : small,
        comapDomain (Subtype.val : {g // g ∈ sΓ} → Gamma β) (ofColex z)
          Subtype.val_injective.injOn (incl m) =
        comapDomain (Subtype.val : small → Gamma β) (ofColex z)
          Subtype.val_injective.injOn m := by
      intro m
      rw [comapDomain_apply, comapDomain_apply]
      rfl
    have hzero : ∀ c : {g // g ∈ sΓ}, c ∉ Set.range (⇑incl) →
        comapDomain (Subtype.val : {g // g ∈ sΓ} → Gamma β) (ofColex z)
          Subtype.val_injective.injOn c = 0 := by
      intro c hc
      rw [comapDomain_apply]
      have hnot : c.1 ∉ (ofColex z).support := by
        intro hmem
        exact hc ⟨⟨c.1, hmem⟩, Subtype.ext rfl⟩
      simpa [mem_support_iff] using hnot
    have hembed := embDomain_of_agree ρSmall.toEmbedding ρΓ.toEmbedding incl
      (comapDomain (Subtype.val : small → Gamma β) (ofColex z) Subtype.val_injective.injOn)
      (comapDomain (Subtype.val : {g // g ∈ sΓ} → Gamma β) (ofColex z)
        Subtype.val_injective.injOn)
      (by
        intro m
        have hcoeS : ρSmall.toEmbedding m = ρSmall m := rfl
        have hcoeΓ : ρΓ.toEmbedding (incl m) = ρΓ (incl m) := rfl
        rw [hcoeS, hcoeΓ]
        exact (hagree m).symm)
      hcoeff hzero
    simpa [ρSmall, OrderEmbedding.coe_ofStrictMono] using hembed.symm

/-- Pushing one integer vector uses only the ordinals in its support. -/
lemma pushGamma_congr {β : _root_.Ordinal.{u}} {s t : Finset (OrdIndex β)} (hst : s ⊆ t)
    (ρs : {i // i ∈ s} ↪o OrdIndex β) (ρt : {i // i ∈ t} ↪o OrdIndex β)
    (hagree : ∀ i : {i // i ∈ s}, ρt ⟨i.1, hst i.2⟩ = ρs i) (g : Gamma β)
    (hg : (ofColex g).support ⊆ s) :
    toColex (embDomain ρs.toEmbedding
      (comapDomain (Subtype.val : {x // x ∈ s} → OrdIndex β) (ofColex g)
        Subtype.val_injective.injOn)) =
    toColex (embDomain ρt.toEmbedding
      (comapDomain (Subtype.val : {x // x ∈ t} → OrdIndex β) (ofColex g)
        Subtype.val_injective.injOn)) := by
  letI : DecidableEq (OrdIndex β) := Classical.decEq _
  apply ofColex.injective
  rw [ofColex_toColex, ofColex_toColex]
  let σ := {i // i ∈ (ofColex g).support}
  let inclSFun : σ → {x // x ∈ s} := fun i => ⟨i.1, hg i.2⟩
  have hinjS : Function.Injective inclSFun := by
    intro i j h
    exact Subtype.ext (congrArg (fun x : {x // x ∈ s} => x.1) h)
  let inclS : σ ↪ {x // x ∈ s} := ⟨inclSFun, hinjS⟩
  let inclTFun : σ → {x // x ∈ t} := fun i => ⟨i.1, hst (hg i.2)⟩
  have hinjT : Function.Injective inclTFun := by
    intro i j h
    exact Subtype.ext (congrArg (fun x : {x // x ∈ t} => x.1) h)
  let inclT : σ ↪ {x // x ∈ t} := ⟨inclTFun, hinjT⟩
  let ρσ : σ ↪ OrdIndex β :=
    ⟨fun i => ρs (inclS i), fun i j h => inclS.injective (ρs.injective h)⟩
  have hcommon : ∀ i, ρt (inclT i) = ρσ i := by
    intro i
    exact hagree (inclS i)
  have hembedS := embDomain_of_agree ρσ ρs.toEmbedding inclS
    (comapDomain (Subtype.val : σ → OrdIndex β) (ofColex g) Subtype.val_injective.injOn)
    (comapDomain (Subtype.val : {x // x ∈ s} → OrdIndex β) (ofColex g)
      Subtype.val_injective.injOn)
    (by
      intro i
      have hcoe : ρs.toEmbedding (inclS i) = ρs (inclS i) := rfl
      rw [hcoe]
      unfold ρσ
      rfl)
    (by
      intro i
      rw [comapDomain_apply, comapDomain_apply]
      dsimp [inclS, inclSFun])
    (by
      intro c hc
      rw [comapDomain_apply]
      have hnot : c.1 ∉ (ofColex g).support := by
        intro hmem
        exact hc ⟨⟨c.1, hmem⟩, Subtype.ext rfl⟩
      simpa [mem_support_iff] using hnot)
  have hembedT := embDomain_of_agree ρσ ρt.toEmbedding inclT
    (comapDomain (Subtype.val : σ → OrdIndex β) (ofColex g) Subtype.val_injective.injOn)
    (comapDomain (Subtype.val : {x // x ∈ t} → OrdIndex β) (ofColex g)
      Subtype.val_injective.injOn)
    (by
      intro i
      have hcoe : ρt.toEmbedding (inclT i) = ρt (inclT i) := rfl
      rw [hcoe]
      unfold ρσ
      exact hcommon i)
    (by
      intro i
      rw [comapDomain_apply, comapDomain_apply]
      dsimp [inclT, inclTFun])
    (by
      intro c hc
      rw [comapDomain_apply]
      have hnot : c.1 ∉ (ofColex g).support := by
        intro hmem
        exact hc ⟨⟨c.1, hmem⟩, Subtype.ext rfl⟩
      simpa [mem_support_iff] using hnot)
  exact hembedS.symm.trans hembedT

/-- Extending the position embedding by the identity off the witness leaves its code fixed. -/
lemma canonicalPush_congr {β : _root_.Ordinal.{u}} {s t : Finset (OrdIndex β)} (hst : s ⊆ t)
    (ρs : {i // i ∈ s} ↪o OrdIndex β) (ρt : {i // i ∈ t} ↪o OrdIndex β)
    (hagree : ∀ i : {i // i ∈ s}, ρt ⟨i.1, hst i.2⟩ = ρs i) (z : HOrder β)
    (hzs : ∀ g ∈ (ofColex z).support, ∀ i ∈ (ofColex g).support, i ∈ s)
    (hzt : ∀ g ∈ (ofColex z).support, ∀ i ∈ (ofColex g).support, i ∈ t) :
    canonicalPush s ρs z hzs = canonicalPush t ρt z hzt := by
  letI : DecidableEq (OrdIndex β) := Classical.decEq _
  letI : DecidableEq (Gamma β) := Classical.decEq _
  apply ofColex.injective
  unfold canonicalPush
  rw [ofColex_toColex, ofColex_toColex]
  let idx := {g // g ∈ (ofColex z).support}
  let ρsΓ : idx ↪o Gamma β :=
    OrderEmbedding.ofStrictMono (fun m =>
      toColex (embDomain ρs.toEmbedding
        (comapDomain (Subtype.val : {x // x ∈ s} → OrdIndex β) (ofColex m.1)
          Subtype.val_injective.injOn))) (by
      intro m n hlt
      exact (colex_image_lt s ρs m.1 n.1 (fun i hi => hzs m.1 m.2 i hi)
        (fun i hi => hzs n.1 n.2 i hi)).mp hlt)
  let ρtΓ : idx ↪o Gamma β :=
    OrderEmbedding.ofStrictMono (fun m =>
      toColex (embDomain ρt.toEmbedding
        (comapDomain (Subtype.val : {x // x ∈ t} → OrdIndex β) (ofColex m.1)
          Subtype.val_injective.injOn))) (by
      intro m n hlt
      exact (colex_image_lt t ρt m.1 n.1 (fun i hi => hzt m.1 m.2 i hi)
        (fun i hi => hzt n.1 n.2 i hi)).mp hlt)
  have hpt : ∀ m : idx, ρtΓ m = ρsΓ m := by
    intro m
    dsimp [ρsΓ, ρtΓ]
    exact (pushGamma_congr hst ρs ρt hagree m.1 (fun i hi => hzs m.1 m.2 i hi)).symm
  let idE : idx ↪ idx := ⟨id, fun a b h => h⟩
  have hembed := embDomain_of_agree ρsΓ.toEmbedding ρtΓ.toEmbedding idE
    (comapDomain (Subtype.val : idx → Gamma β) (ofColex z) Subtype.val_injective.injOn)
    (comapDomain (Subtype.val : idx → Gamma β) (ofColex z) Subtype.val_injective.injOn)
    (by
      intro m
      have hcoeS : ρsΓ.toEmbedding m = ρsΓ m := rfl
      have hcoeT : ρtΓ.toEmbedding (idE m) = ρtΓ m := rfl
      rw [hcoeS, hcoeT]
      exact hpt m)
    (by
      intro m
      rw [comapDomain_apply, comapDomain_apply]
      have hval : (idE m).1 = m.1 := rfl
      rw [hval])
    (by
      intro c hc
      exact (hc ⟨c, rfl⟩).elim)
  simpa [ρsΓ, ρtΓ, OrderEmbedding.coe_ofStrictMono] using hembed

/-- Pushing the zero code stays zero. -/
lemma horderPush_zero {δ β : _root_.Ordinal.{u}} (φ : OrdIndex δ ↪o OrdIndex β) :
    horderPush φ (0 : HOrder δ) = 0 := by
  have h1 : horderPush φ (0 : HOrder δ) =
      colexPush (M := ℚ) (colexPush φ) (0 : HOrder δ) := rfl
  rw [h1]
  apply ofColex.injective
  unfold colexPush
  rw [OrderEmbedding.coe_ofStrictMono, ofColex_toColex]
  have hzero : ofColex (0 : HOrder δ) = 0 := rfl
  rw [hzero, mapDomain_zero]
  exact (show ofColex (0 : HOrder β) = 0 from rfl).symm

/-- Every ordinal position of a pushed code lies in the image of the position embedding. -/
lemma hSupport_horderPush {δ β : _root_.Ordinal.{u}} (φ : OrdIndex δ ↪o OrdIndex β)
    (x : HOrder δ) {i : OrdIndex β} (hi : i ∈ hSupport (horderPush φ x)) :
    i ∈ Set.range (⇑φ) := by
  letI : DecidableEq (OrdIndex β) := Classical.decEq _
  letI : DecidableEq (Gamma β) := Classical.decEq _
  simp only [hSupport, Finset.mem_biUnion] at hi
  obtain ⟨g, hg, hi⟩ := hi
  have happly : ofColex (horderPush φ x) = mapDomain (⇑(colexPush φ)) (ofColex x) := by
    have h1 : horderPush φ x = colexPush (M := ℚ) (colexPush φ) x := rfl
    rw [h1]
    unfold colexPush
    rw [OrderEmbedding.coe_ofStrictMono, ofColex_toColex]
  rw [happly, mapDomain_support_of_injective (colexPush φ).injective] at hg
  obtain ⟨g0, -, rfl⟩ := Finset.mem_image.mp hg
  have hpush : ofColex ((colexPush φ) g0) = mapDomain (⇑φ) (ofColex g0) := by
    unfold colexPush
    rw [OrderEmbedding.coe_ofStrictMono, ofColex_toColex]
  rw [hpush, mapDomain_support_of_injective φ.injective] at hi
  obtain ⟨i0, -, rfl⟩ := Finset.mem_image.mp hi
  exact ⟨i0, rfl⟩

/-- Every ordinal of the segment `T` is hit by `segmentPosition`. -/
lemma segmentPosition_of_mem {β δ : _root_.Ordinal.{u}} {T : Set β.ToType}
    (e : ↥T ≃o δ.ToType) (j : OrdIndex β)
    (hj : Ordinal.ToType.mk (asIio j) ∈ T) : j ∈ Set.range (⇑(segmentPosition e)) := by
  let u : ↥T := ⟨Ordinal.ToType.mk (asIio j), hj⟩
  let i : OrdIndex δ := asOrdIndex ((Ordinal.ToType.mk (o := δ)).symm (e u))
  refine ⟨i, ?_⟩
  apply Subtype.ext
  have has : asIio i = (Ordinal.ToType.mk (o := δ)).symm (e u) := by
    simp [i, asIio, asOrdIndex]
  rw [segmentPosition, OrderEmbedding.coe_ofStrictMono, asOrdIndex, has]
  have hround : Ordinal.ToType.mk ((Ordinal.ToType.mk (o := δ)).symm (e u)) = e u :=
    OrderIso.apply_symm_apply _ _
  rw [hround]
  have hback : e.symm (e u) = u := OrderIso.symm_apply_apply _ _
  rw [hback]
  have hu : u.1 = Ordinal.ToType.mk (asIio j) := rfl
  rw [hu, OrderIso.symm_apply_apply, asIio]

/-- The ordinal positions of a `≤ θ` sequence of finite codes still have size at most `θ`. -/
lemma parameter_card {θ : Cardinal.{u}} {β : _root_.Ordinal.{u}} {ι : Type u}
    (hθ : ℵ₀ ≤ θ) (hι : #ι ≤ θ) (pos : ι → Finset (OrdIndex β)) :
    #↥{t : β.ToType | ∃ i, ∃ j ∈ pos i, t = Ordinal.ToType.mk (asIio j)} ≤ θ := by
  let param : Set β.ToType := {t | ∃ i, ∃ j ∈ pos i, t = Ordinal.ToType.mk (asIio j)}
  let src := {p : ι × ULift.{u} ℕ // p.2.down < Fintype.card (↥(pos p.1))}
  let toParam : src → ↥param := fun p =>
    let eqv := Fintype.equivFin (↥(pos p.1.1))
    let j := eqv.symm ⟨p.1.2.down, p.2⟩
    ⟨Ordinal.ToType.mk (asIio j.1), p.1.1, j.1, j.2, rfl⟩
  have hsurj : Function.Surjective toParam := by
    intro t
    obtain ⟨i, j, hj, ht⟩ := t.2
    let eqv := Fintype.equivFin (↥(pos i))
    let n : Fin (Fintype.card (↥(pos i))) := eqv ⟨j, hj⟩
    refine ⟨⟨(i, ULift.up n.1), n.2⟩, ?_⟩
    apply Subtype.ext
    change Ordinal.ToType.mk (asIio (eqv.symm ⟨n.1, n.2⟩).1) = t.1
    rw [ht]
    have hback : eqv.symm ⟨n.1, n.2⟩ = ⟨j, hj⟩ := by
      simp [n, eqv, Equiv.symm_apply_apply]
    rw [hback]
  have hsrc : #src ≤ #(ι × ULift.{u} ℕ) :=
    Cardinal.mk_le_of_injective (f := Subtype.val) Subtype.val_injective
  have hprod : #(ι × ULift.{u} ℕ) = #ι * ℵ₀ := by
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_uLift, Cardinal.mk_nat,
      Cardinal.lift_aleph0]
  have hmul : #ι * ℵ₀ ≤ θ := by
    calc
      #ι * ℵ₀ ≤ θ * ℵ₀ := mul_le_mul' hι le_rfl
      _ = θ := mul_aleph0_eq hθ
  exact (Cardinal.mk_le_of_surjective (f := toParam) hsurj).trans (hsrc.trans (hprod ▸ hmul))

/-- Extend a position embedding by the identity on parameter positions. -/
lemma extend_position_embedding {β : _root_.Ordinal.{u}} (sz sA : Finset (OrdIndex β))
    (ρ : {i // i ∈ sz} ↪o OrdIndex β) (param : Set β.ToType)
    (hfix : ∀ i : {i // i ∈ sz}, Ordinal.ToType.mk (asIio i.1) ∈ param → ρ i = i.1)
    (hcross : ∀ (t : β.ToType) (_ht : t ∈ param) (i : {i // i ∈ sz}),
      t < Ordinal.ToType.mk (asIio i.1) ↔ t < Ordinal.ToType.mk (asIio (ρ i)))
    (heq : ∀ (t : β.ToType) (_ht : t ∈ param) (i : {i // i ∈ sz}),
      t = Ordinal.ToType.mk (asIio i.1) ↔ t = Ordinal.ToType.mk (asIio (ρ i)))
    (hparam : ∀ i ∈ sA, Ordinal.ToType.mk (asIio i) ∈ param) :
    ∃ ρt : {i // i ∈ sz ∪ sA} ↪o OrdIndex β,
      (∀ i : {i // i ∈ sz},
        ρt ⟨i.1, Finset.subset_union_left (s₁ := sz) (s₂ := sA) i.2⟩ = ρ i) ∧
      (∀ i : {i // i ∈ sz ∪ sA}, i.1 ∈ sA → ρt i = i.1) := by
  let dom := {i // i ∈ sz ∪ sA}
  let ρfun : dom → OrdIndex β := fun i => if h : i.1 ∈ sz then ρ ⟨i.1, h⟩ else i.1
  have hmono : StrictMono ρfun := by
    intro i j hij
    have hlt : i.1 < j.1 := Subtype.mk_lt_mk.mp hij
    by_cases hi : i.1 ∈ sz
    · by_cases hj : j.1 ∈ sz
      · have hsub : (⟨i.1, hi⟩ : {x // x ∈ sz}) < ⟨j.1, hj⟩ := Subtype.mk_lt_mk.mpr hlt
        have hρ : ρ ⟨i.1, hi⟩ < ρ ⟨j.1, hj⟩ := (ρ.lt_iff_lt).mpr hsub
        simpa [ρfun, hi, hj] using hρ
      · have hjA : j.1 ∈ sA := (Finset.mem_union.mp j.2).resolve_left hj
        have ht : Ordinal.ToType.mk (asIio j.1) ∈ param := hparam _ hjA
        have hpt : Ordinal.ToType.mk (asIio i.1) < Ordinal.ToType.mk (asIio j.1) :=
          (Ordinal.ToType.mk.lt_iff_lt).mpr (Subtype.mk_lt_mk.mpr hlt)
        have hne : ¬ Ordinal.ToType.mk (asIio j.1) = Ordinal.ToType.mk (asIio i.1) := ne_of_gt hpt
        have hneρ : ¬ Ordinal.ToType.mk (asIio j.1) =
            Ordinal.ToType.mk (asIio (ρ ⟨i.1, hi⟩)) := by
          intro hbad
          exact hne ((heq _ ht ⟨i.1, hi⟩).mpr hbad)
        have hnot : ¬ Ordinal.ToType.mk (asIio j.1) < Ordinal.ToType.mk (asIio i.1) :=
          not_lt_of_gt hpt
        have hnotρ : ¬ Ordinal.ToType.mk (asIio j.1) <
            Ordinal.ToType.mk (asIio (ρ ⟨i.1, hi⟩)) :=
          (not_congr (hcross _ ht ⟨i.1, hi⟩)).mp hnot
        have hle : Ordinal.ToType.mk (asIio (ρ ⟨i.1, hi⟩)) ≤ Ordinal.ToType.mk (asIio j.1) :=
          le_of_not_gt hnotρ
        have hltρ : Ordinal.ToType.mk (asIio (ρ ⟨i.1, hi⟩)) < Ordinal.ToType.mk (asIio j.1) :=
          lt_of_le_of_ne hle (Ne.symm hneρ)
        have hidx : ρ ⟨i.1, hi⟩ < j.1 :=
          Subtype.mk_lt_mk.mpr
            (Subtype.mk_lt_mk.mp ((Ordinal.ToType.mk.lt_iff_lt).mp hltρ))
        simpa [ρfun, hi, hj] using hidx
    · by_cases hj : j.1 ∈ sz
      · have hiA : i.1 ∈ sA := (Finset.mem_union.mp i.2).resolve_left hi
        have ht : Ordinal.ToType.mk (asIio i.1) ∈ param := hparam _ hiA
        have hpt : Ordinal.ToType.mk (asIio i.1) < Ordinal.ToType.mk (asIio j.1) :=
          (Ordinal.ToType.mk.lt_iff_lt).mpr (Subtype.mk_lt_mk.mpr hlt)
        have hltρ : Ordinal.ToType.mk (asIio i.1) <
            Ordinal.ToType.mk (asIio (ρ ⟨j.1, hj⟩)) := (hcross _ ht ⟨j.1, hj⟩).mp hpt
        have hidx : i.1 < ρ ⟨j.1, hj⟩ :=
          Subtype.mk_lt_mk.mpr
            (Subtype.mk_lt_mk.mp ((Ordinal.ToType.mk.lt_iff_lt).mp hltρ))
        simpa [ρfun, hi, hj] using hidx
      · simpa [ρfun, hi, hj] using hlt
  refine ⟨OrderEmbedding.ofStrictMono ρfun hmono, ?_, ?_⟩
  · intro i
    have hmem : i.1 ∈ sz := i.2
    simp [ρfun, OrderEmbedding.coe_ofStrictMono, hmem]
  · intro i hiA
    by_cases hsz : i.1 ∈ sz
    · have hfixi : ρ ⟨i.1, hsz⟩ = i.1 := hfix ⟨i.1, hsz⟩ (hparam i.1 hiA)
      simp [ρfun, OrderEmbedding.coe_ofStrictMono, hsz, hfixi]
    · simp [ρfun, OrderEmbedding.coe_ofStrictMono, hsz]

/-- One point of `H(δ)` fills a strict slot exactly when its image does. -/
lemma extended_occupancy {θ : Cardinal.{u}} {β δ : _root_.Ordinal.{u}} (T : Set β.ToType)
    (hpat : ∀ {ι : Type u} (_hι : #ι ≤ θ) (p : ι → β.ToType), (∀ i, p i ∈ T) →
      ∀ {n : ℕ} (q : Fin n → β.ToType), ∃ q' : Fin n → β.ToType,
        (∀ k, q' k ∈ T) ∧ SameOrderDiagram (Sum.elim p q) (Sum.elim p q'))
    (e : ↥T ≃o δ.ToType) (hθ : ℵ₀ ≤ θ) :
    ∀ {ι : Type u} (hι : #ι ≤ θ) (xs : ι → HOrder δ) (lower upper : Set ι),
      Occupied (xs '' lower) (xs '' upper) ↔
        Occupied ((fun i => horderPush (segmentPosition e) (xs i)) '' lower)
          ((fun i => horderPush (segmentPosition e) (xs i)) '' upper) := by
  intro ι hι xs lower upper
  set φ : OrdIndex δ ↪o OrdIndex β := segmentPosition e
  set f : HOrder δ ↪o HOrder β := horderPush φ
  constructor
  · exact occupied_of_orderEmbedding f xs lower upper
  · intro ⟨z, hzslot⟩
    let sz : Finset (OrdIndex β) := hSupport z
    let param : Set β.ToType :=
      {t | ∃ i, ∃ j ∈ hSupport (f (xs i)), t = Ordinal.ToType.mk (asIio j)}
    have hcard : #↥param ≤ θ :=
      parameter_card hθ hι (fun i => hSupport (f (xs i)))
    have hparamT : ∀ x ∈ param, x ∈ T := by
      intro x hx
      obtain ⟨i, j, hj, rfl⟩ := hx
      obtain ⟨k, hk⟩ := hSupport_horderPush φ (xs i) hj
      rw [← hk]
      simpa [φ, OrderEmbedding.coe_ofStrictMono] using segmentPosition_mem e k
    obtain ⟨ρ, hρT, hρfix, hρcross, hρeq⟩ :=
      exists_position_embedding T hpat param hcard hparamT sz
    have hrangeρ : ∀ i : {i // i ∈ sz}, ρ i ∈ Set.range (⇑φ) :=
      fun i => segmentPosition_of_mem e (ρ i) (hρT i)
    have hzsz : ∀ g ∈ (ofColex z).support, ∀ i ∈ (ofColex g).support, i ∈ sz := by
      intro g hg i hi
      simp only [sz, hSupport, Finset.mem_biUnion]
      exact ⟨g, hg, hi⟩
    have ha0 : ∀ g ∈ (ofColex (f (0 : HOrder δ))).support, ∀ i ∈ (ofColex g).support, i ∈ sz := by
      intro g hg _ hi
      rw [show f (0 : HOrder δ) = 0 from horderPush_zero φ] at hg
      rw [show ofColex (0 : HOrder β) = 0 from rfl, support_zero] at hg
      exact (Finset.notMem_empty g hg).elim
    have hfix0 : ∀ i : {i // i ∈ sz},
        (∃ g ∈ (ofColex (f (0 : HOrder δ))).support, i.1 ∈ (ofColex g).support) → ρ i = i.1 := by
      intro i ⟨g, hg, _⟩
      rw [show f (0 : HOrder δ) = 0 from horderPush_zero φ] at hg
      rw [show ofColex (0 : HOrder β) = 0 from rfl, support_zero] at hg
      exact (Finset.notMem_empty g hg).elim
    obtain ⟨w0, -, -, -, himg0⟩ := relocate_witness φ (0 : HOrder δ) z sz ha0 hzsz ρ hfix0 hrangeρ
    have hcmp (k : ι) : (f (xs k) = z ↔ xs k = w0) ∧ (f (xs k) < z ↔ xs k < w0) ∧
        (z < f (xs k) ↔ w0 < xs k) := by
      let sA : Finset (OrdIndex β) := hSupport (f (xs k))
      have hparamA : ∀ i ∈ sA, Ordinal.ToType.mk (asIio i) ∈ param := by
        intro i hi
        exact ⟨k, i, hi, rfl⟩
      obtain ⟨ρt, hagree, hfixA⟩ :=
        extend_position_embedding sz sA ρ param hρfix hρcross hρeq hparamA
      have hst : sz ⊆ sz ∪ sA := Finset.subset_union_left (s₁ := sz) (s₂ := sA)
      have hz_t : ∀ g ∈ (ofColex z).support, ∀ i ∈ (ofColex g).support, i ∈ sz ∪ sA :=
        fun g hg i hi => hst (hzsz g hg i hi)
      have ha_t : ∀ g ∈ (ofColex (f (xs k))).support, ∀ i ∈ (ofColex g).support,
          i ∈ sz ∪ sA := by
        intro g hg i hi
        exact Finset.subset_union_right (s₁ := sz) (s₂ := sA) (by
          simp only [sA, hSupport, Finset.mem_biUnion]
          exact ⟨g, hg, hi⟩)
      have hfix_t : ∀ i : {i // i ∈ sz ∪ sA},
          (∃ g ∈ (ofColex (f (xs k))).support, i.1 ∈ (ofColex g).support) → ρt i = i.1 := by
        intro i ⟨g, hg, hi⟩
        exact hfixA i (by
          simp only [sA, hSupport, Finset.mem_biUnion]
          exact ⟨g, hg, hi⟩)
      have hrange_t : ∀ i : {i // i ∈ sz ∪ sA}, ρt i ∈ Set.range (⇑φ) := by
        intro i
        by_cases hsz : i.1 ∈ sz
        · have hi' : i = ⟨i.1, Finset.subset_union_left (s₁ := sz) (s₂ := sA) hsz⟩ :=
            Subtype.ext rfl
          rw [hi', hagree ⟨i.1, hsz⟩]
          exact hrangeρ ⟨i.1, hsz⟩
        · have hiA : i.1 ∈ sA := (Finset.mem_union.mp i.2).resolve_left hsz
          rw [hfixA i hiA]
          exact hSupport_horderPush φ (xs k) hiA
      obtain ⟨w, heq, hlt, hgt, himg⟩ :=
        relocate_witness φ (xs k) z (sz ∪ sA) ha_t hz_t ρt hfix_t hrange_t
      have hw : w = w0 := by
        apply f.injective
        rw [himg, himg0]
        exact (canonicalPush_congr hst ρ ρt hagree z hzsz hz_t).symm
      rw [heq, hlt, hgt, hw]
      exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩
    refine ⟨w0, ?_, ?_, ?_, ?_⟩
    · intro hmem
      obtain ⟨i, hi, heq⟩ := (mem_image _ _ _).mp hmem
      exact hzslot.1 ((mem_image _ _ _).mpr ⟨i, hi, (hcmp i).1.mpr heq⟩)
    · intro hmem
      obtain ⟨i, hi, heq⟩ := (mem_image _ _ _).mp hmem
      exact hzslot.2.1 ((mem_image _ _ _).mpr ⟨i, hi, (hcmp i).1.mpr heq⟩)
    · intro a hmem
      obtain ⟨i, hi, rfl⟩ := (mem_image _ _ _).mp hmem
      exact (hcmp i).2.1.mp (hzslot.2.2.1 _ ((mem_image _ _ _).mpr ⟨i, hi, rfl⟩))
    · intro b hmem
      obtain ⟨i, hi, rfl⟩ := (mem_image _ _ _).mp hmem
      exact (hcmp i).2.2.mp (hzslot.2.2.2 _ ((mem_image _ _ _).mpr ⟨i, hi, rfl⟩))

end
end AEC
