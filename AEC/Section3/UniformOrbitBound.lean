module

public import AEC.Section2.OrderPresentation
public import AEC.Section2.SmallModel
public import AEC.Section2.DirectedLimit
public import AEC.Section3.OrbitRecord
public import AEC.Section3.OrbitRecordBound
public import AEC.Section3.OrbitName
public import AEC.Section3.ShortOrbit
public import AEC.Section3.HausdorffOrder
public import AEC.Section1.Categorical
public import Mathlib.Order.Hom.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace AEC
section

universe u v

open FirstOrder Cardinal Set

/-- A presentation record with index and slot sets chosen among the ordinals `< θ`. -/
structure CanonicalRecord (lab : Type u) (arity : lab → ℕ) (θ : Cardinal.{u}) where
  idx : Set (Below θ)
  slt : Set (Below θ)
  label : ↥idx → lab
  arg : ∀ i, Fin (arity (label i)) → ↥slt
  lt : ↥slt → ↥slt → Prop
  arg_strict : ∀ i {a b : Fin (arity (label i))}, a < b → lt (arg i a) (arg i b)
  arg_surj : ∀ x : ↥slt, ∃ i, ∃ a, arg i a = x
  occupied : Set (↥slt) → Set (↥slt) → Prop

def CanonicalRecord.toOrbitRecord {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (r : CanonicalRecord lab arity θ) : OrbitRecord lab arity where
  index := ↥r.idx
  slot := ↥r.slt
  label := r.label
  arg := r.arg
  lt := r.lt
  arg_strict := r.arg_strict
  arg_surj := r.arg_surj
  occupied := r.occupied

theorem canonical_record_card_index {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (r : CanonicalRecord lab arity θ) :
    # ((CanonicalRecord.toOrbitRecord r).index) ≤ θ := by
  dsimp [CanonicalRecord.toOrbitRecord]
  have h := Cardinal.mk_subtype_le r.idx
  rw [mk_ord_toType] at h
  exact h

theorem canonical_record_card_slot {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (r : CanonicalRecord lab arity θ) :
    # ((CanonicalRecord.toOrbitRecord r).slot) ≤ θ := by
  dsimp [CanonicalRecord.toOrbitRecord]
  have h := Cardinal.mk_subtype_le r.slt
  rw [mk_ord_toType] at h
  exact h

theorem fin_cast_arg_rec {lab : Type u} {arity : lab → ℕ} {index slot : Type u}
    (label : index → lab) (arg : ∀ i, Fin (arity (label i)) → slot)
    (i j : index) (h : i = j) (a : Fin (arity (label i))) :
    arg i a = arg j (Fin.cast (congrArg arity (congrArg label h)) a) := by
  subst h
  rfl

/-- A fixed embedding of a type of cardinality `≤ θ` into `Below θ`. -/
noncomputable def embedBelow {α : Type u} {θ : Cardinal.{u}} (h : #α ≤ θ) : α ↪ Below θ := by
  have : #α ≤ #(Below θ) := by rw [mk_ord_toType]; exact h
  exact Classical.choice ((Cardinal.le_def α (Below θ)).mp this)

/-- Index embedding used when canonizing a record of size `≤ θ`. -/
noncomputable def OrbitRecord.idxEmbed {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (rec : OrbitRecord lab arity) (hidx : #rec.index ≤ θ) : rec.index ↪ Below θ :=
  embedBelow hidx

/-- Slot embedding used when canonizing a record of size `≤ θ`. -/
noncomputable def OrbitRecord.sltEmbed {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (rec : OrbitRecord lab arity) (hslt : #rec.slot ≤ θ) : rec.slot ↪ Below θ :=
  embedBelow hslt

/-- Canonize by the fixed `embedBelow` embeddings of index and slot. -/
noncomputable def OrbitRecord.toCanonical {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (rec : OrbitRecord lab arity) (hidx : #rec.index ≤ θ) (hslt : #rec.slot ≤ θ) :
    CanonicalRecord lab arity θ := by
  let e_idx := rec.idxEmbed hidx
  let e_slt := rec.sltEmbed hslt
  let e_i : rec.index ≃ ↥(Set.range e_idx) := Equiv.ofInjective e_idx.1 e_idx.2
  let e_s : rec.slot ≃ ↥(Set.range e_slt) := Equiv.ofInjective e_slt.1 e_slt.2
  exact {
    idx := Set.range e_idx
    slt := Set.range e_slt
    label := fun i => rec.label (e_i.symm i)
    arg := fun i a => e_s (rec.arg (e_i.symm i) a)
    lt := fun a b => rec.lt (e_s.symm a) (e_s.symm b)
    arg_strict := fun i a b hab => by
      simpa [Equiv.symm_apply_apply] using rec.arg_strict (e_i.symm i) hab
    arg_surj := fun x => by
      obtain ⟨i, a, ha⟩ := rec.arg_surj (e_s.symm x)
      have hcast : i = e_i.symm (e_i i) := (e_i.symm_apply_apply i).symm
      refine ⟨e_i i, Fin.cast (congrArg arity (congrArg rec.label hcast)) a, ?_⟩
      have h_app := fin_cast_arg_rec rec.label rec.arg i (e_i.symm (e_i i)) hcast a
      rw [← h_app, ha, Equiv.apply_symm_apply]
    occupied := fun lower upper => rec.occupied (e_s.symm '' lower) (e_s.symm '' upper)
  }

/-- Index equivalence into the canonical record. -/
noncomputable def OrbitRecord.toCanonicalIndexEquiv {lab : Type u} {arity : lab → ℕ}
    {θ : Cardinal.{u}} (rec : OrbitRecord lab arity) (hidx : #rec.index ≤ θ)
    (hslt : #rec.slot ≤ θ) :
    rec.index ≃ ↥(rec.toCanonical hidx hslt).idx :=
  Equiv.ofInjective (rec.idxEmbed hidx).1 (rec.idxEmbed hidx).2

/-- Slot equivalence into the canonical record. -/
noncomputable def OrbitRecord.toCanonicalSlotEquiv {lab : Type u} {arity : lab → ℕ}
    {θ : Cardinal.{u}} (rec : OrbitRecord lab arity) (hidx : #rec.index ≤ θ)
    (hslt : #rec.slot ≤ θ) :
    rec.slot ≃ ↥(rec.toCanonical hidx hslt).slt :=
  Equiv.ofInjective (rec.sltEmbed hslt).1 (rec.sltEmbed hslt).2

/-- Data witnessing `OrbitRecord.Same`, kept outside `Prop` so equivalences remain usable. -/
structure OrbitRecord.SameData {lab : Type u} {arity : lab → ℕ}
    (r s : OrbitRecord lab arity) where
  e : r.index ≃ s.index
  f : r.slot ≃ s.slot
  hlabel : ∀ i, r.label i = s.label (e i)
  hlt : ∀ a b, r.lt a b ↔ s.lt (f a) (f b)
  harg : ∀ i (a : Fin (arity (r.label i))),
    f (r.arg i a) = s.arg (e i) (Fin.cast (congrArg arity (hlabel i)) a)
  hocc : ∀ lower upper, r.occupied lower upper ↔ s.occupied (f '' lower) (f '' upper)

theorem OrbitRecord.SameData.toSame {lab : Type u} {arity : lab → ℕ}
    {r s : OrbitRecord lab arity} (w : OrbitRecord.SameData r s) : OrbitRecord.Same r s :=
  ⟨w.e, w.f, w.hlabel, w.hlt, w.harg, w.hocc⟩

noncomputable def OrbitRecord.toCanonicalSameData {lab : Type u} {arity : lab → ℕ}
    {θ : Cardinal.{u}} (rec : OrbitRecord lab arity)
    (hidx : #rec.index ≤ θ) (hslt : #rec.slot ≤ θ) :
    OrbitRecord.SameData rec (CanonicalRecord.toOrbitRecord (rec.toCanonical hidx hslt)) where
  e := rec.toCanonicalIndexEquiv hidx hslt
  f := rec.toCanonicalSlotEquiv hidx hslt
  hlabel := fun i => by
    change rec.label i = rec.label ((rec.toCanonicalIndexEquiv hidx hslt).symm
      ((rec.toCanonicalIndexEquiv hidx hslt) i))
    rw [Equiv.symm_apply_apply]
  hlt := fun a b => by
    change rec.lt a b ↔ rec.lt
      ((rec.toCanonicalSlotEquiv hidx hslt).symm ((rec.toCanonicalSlotEquiv hidx hslt) a))
      ((rec.toCanonicalSlotEquiv hidx hslt).symm ((rec.toCanonicalSlotEquiv hidx hslt) b))
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  harg := fun i a => by
    change (rec.toCanonicalSlotEquiv hidx hslt) (rec.arg i a) =
      (rec.toCanonicalSlotEquiv hidx hslt)
        (rec.arg ((rec.toCanonicalIndexEquiv hidx hslt).symm
          ((rec.toCanonicalIndexEquiv hidx hslt) i))
          (Fin.cast _ a))
    congr 1
    exact fin_cast_arg_rec rec.label rec.arg i
      ((rec.toCanonicalIndexEquiv hidx hslt).symm ((rec.toCanonicalIndexEquiv hidx hslt) i))
      ((rec.toCanonicalIndexEquiv hidx hslt).symm_apply_apply i).symm a
  hocc := fun lower upper => by
    change rec.occupied lower upper ↔
      rec.occupied
        ((rec.toCanonicalSlotEquiv hidx hslt).symm ''
          ((rec.toCanonicalSlotEquiv hidx hslt) '' lower))
        ((rec.toCanonicalSlotEquiv hidx hslt).symm ''
          ((rec.toCanonicalSlotEquiv hidx hslt) '' upper))
    have h1 : (rec.toCanonicalSlotEquiv hidx hslt).symm ''
        ((rec.toCanonicalSlotEquiv hidx hslt) '' lower) = lower := by
      rw [← Set.image_comp, Equiv.symm_comp_self, Set.image_id]
    have h2 : (rec.toCanonicalSlotEquiv hidx hslt).symm ''
        ((rec.toCanonicalSlotEquiv hidx hslt) '' upper) = upper := by
      rw [← Set.image_comp, Equiv.symm_comp_self, Set.image_id]
    rw [h1, h2]

theorem OrbitRecord.toCanonical_same {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (rec : OrbitRecord lab arity) (hidx : #rec.index ≤ θ) (hslt : #rec.slot ≤ θ) :
    OrbitRecord.Same rec (CanonicalRecord.toOrbitRecord (rec.toCanonical hidx hslt)) :=
  (rec.toCanonicalSameData hidx hslt).toSame

theorem canonical_record_covers {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (rec : OrbitRecord lab arity) (hidx : # rec.index ≤ θ) (hslt : # rec.slot ≤ θ) :
    ∃ r : CanonicalRecord lab arity θ, OrbitRecord.Same rec (CanonicalRecord.toOrbitRecord r) :=
  ⟨rec.toCanonical hidx hslt, rec.toCanonical_same hidx hslt⟩

/-- Flattened non-dependent data of a canonical record (for the cardinality bound). -/
structure FlatRecord (lab : Type u) (θ : Cardinal.{u}) where
  idx : Set (Below θ)
  slt : Set (Below θ)
  label : Below θ → Option lab
  arg : Below θ → ℕ → Option (Below θ)
  lt : Below θ → Below θ → Bool
  occupied : Set (Below θ) → Set (Below θ) → Bool

noncomputable def CanonicalRecord.toFlat {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (r : CanonicalRecord lab arity θ) : FlatRecord lab θ := by
  classical
  exact {
    idx := r.idx
    slt := r.slt
    label := fun x => if hx : x ∈ r.idx then some (r.label ⟨x, hx⟩) else none
    arg := fun x n =>
      if hx : x ∈ r.idx then
        let i : ↥r.idx := ⟨x, hx⟩
        if hn : n < arity (r.label i) then some (r.arg i ⟨n, hn⟩).1 else none
      else none
    lt := fun a b =>
      decide (∃ ha : a ∈ r.slt, ∃ hb : b ∈ r.slt, r.lt ⟨a, ha⟩ ⟨b, hb⟩)
    occupied := fun L U =>
      decide (∃ (_hL : L ⊆ r.slt) (_hU : U ⊆ r.slt),
        r.occupied {z : ↥r.slt | z.1 ∈ L} {z : ↥r.slt | z.1 ∈ U})
  }

/-- Equivalence unpacking a flat record into a product of plain data types. -/
def flatRecordEquiv (lab : Type u) (θ : Cardinal.{u}) :
    FlatRecord lab θ ≃
      Set (Below θ) × Set (Below θ) × (Below θ → Option lab) ×
        (Below θ → ℕ → Option (Below θ)) × (Below θ → Below θ → Bool) ×
        (Set (Below θ) → Set (Below θ) → Bool) where
  toFun r := ⟨r.idx, r.slt, r.label, r.arg, r.lt, r.occupied⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2⟩
  left_inv r := by cases r; rfl
  right_inv p := by
    rcases p with ⟨a, b, c, d, e, f⟩; rfl

private theorem add_one_le_two_pow {a : Cardinal.{u}} (ha : aleph0 ≤ a) :
    a + 1 ≤ (2 : Cardinal) ^ a := by
  refine (add_le_max a 1).trans ?_
  refine max_le (max_le ?_ ?_) ?_
  · exact (Cardinal.cantor a).le
  · exact one_lt_aleph0.le.trans (ha.trans (Cardinal.cantor a).le)
  · exact ha.trans (Cardinal.cantor a).le

/-- `#FlatRecord ≤ B(ℓ, θ)`. -/
theorem mk_flatRecord_le_orbitRecordBound {lab : Type u} (θ ell : Cardinal.{u})
    (hlab : #lab ≤ ell) (hθ : aleph0 ≤ θ) (hell : aleph0 ≤ ell) :
    #(FlatRecord lab θ) ≤ orbitRecordBound ell θ := by
  have h2ne : (2 : Cardinal.{u}) ≠ 0 := two_ne_zero
  have hB : orbitRecordBound ell θ = (2 : Cardinal) ^ ((2 : Cardinal) ^ (ell + θ)) := rfl
  have hcant (a : Cardinal.{u}) : a ≤ (2 : Cardinal) ^ a := (Cardinal.cantor a).le
  have hBinf : aleph0 ≤ orbitRecordBound ell θ := by
    rw [hB]
    exact le_trans hell <| (hcant ell).trans <|
      (power_le_power_left h2ne le_self_add).trans (hcant _)
  have hBB : orbitRecordBound ell θ * orbitRecordBound ell θ = orbitRecordBound ell θ :=
    Cardinal.mul_eq_self hBinf
  have hprod {a b : Cardinal.{u}} (ha : a ≤ orbitRecordBound ell θ)
      (hb : b ≤ orbitRecordBound ell θ) : a * b ≤ orbitRecordBound ell θ :=
    (mul_le_mul' ha hb).trans (by rw [hBB])
  have h2θ : (2 : Cardinal) ^ θ ≤ orbitRecordBound ell θ := by
    rw [hB]
    exact (power_le_power_left h2ne le_add_self).trans (hcant _)
  have hSet : #(Set (Below θ)) ≤ orbitRecordBound ell θ := by
    simp [mk_set, mk_ord_toType]; exact h2θ
  have hLab : #(Below θ → Option lab) ≤ orbitRecordBound ell θ := by
    have heq : #(Below θ → Option lab) = #(Option lab) ^ θ := by
      simp [mk_arrow, mk_ord_toType]
    rw [heq]
    have hopt : #(Option lab) ≤ (2 : Cardinal) ^ (ell + θ) := by
      have h1 : #(Option lab) ≤ ell + 1 :=
        (mk_option (α := lab)).trans_le (add_le_add_left hlab 1)
      exact h1.trans ((add_one_le_two_pow hell).trans (power_le_power_left h2ne le_self_add))
    refine (power_le_power_right hopt).trans ?_
    rw [← power_mul, hB]
    apply power_le_power_left h2ne
    have haleph : aleph0 ≤ (2 : Cardinal) ^ (ell + θ) :=
      le_trans hell <| (hcant ell).trans (power_le_power_left h2ne le_self_add)
    have hle : ell + θ ≤ (2 : Cardinal) ^ (ell + θ) := hcant _
    have hθ' : θ ≤ (2 : Cardinal) ^ (ell + θ) := le_trans le_add_self hle
    exact (mul_le_mul' hle hθ').trans (by rw [Cardinal.mul_eq_self haleph])
  have hArg : #(Below θ → ℕ → Option (Below θ)) ≤ orbitRecordBound ell θ := by
    have heq : #(Below θ → ℕ → Option (Below θ)) = #(Option (Below θ)) ^ θ := by
      have h1 : #(Below θ → ℕ → Option (Below θ)) = #(Below θ × ℕ → Option (Below θ)) :=
        mk_congr ⟨fun f p => f p.1 p.2, fun f a n => f (a, n), fun _ => rfl, fun _ => rfl⟩
      have hdom : #(Below θ × ℕ) = θ := by
        have : #(Below θ × ℕ) = θ * ℵ₀ := by
          simp [mk_prod, mk_ord_toType, mk_nat, lift_uzero, lift_aleph0]
        rw [this, Cardinal.mul_eq_left hθ hθ aleph0_ne_zero]
      have harr : #(Below θ × ℕ → Option (Below θ)) = #(Option (Below θ)) ^ θ := by
        simp [mk_arrow, hdom]
      rw [h1, harr]
    rw [heq]
    have hop : #(Option (Below θ)) ≤ (2 : Cardinal) ^ θ := by
      have : #(Option (Below θ)) = θ + 1 := by simp [mk_option, mk_ord_toType]
      rw [this]; exact add_one_le_two_pow hθ
    exact (power_le_power_right hop).trans <| by
      rw [← power_mul, Cardinal.mul_eq_self hθ]; exact h2θ
  have hLt : #(Below θ → Below θ → Bool) ≤ orbitRecordBound ell θ := by
    have h1 : #(Below θ → Below θ → Bool) = #(Below θ × Below θ → Bool) :=
      mk_congr ⟨fun f p => f p.1 p.2, fun f a b => f (a, b), fun _ => rfl, fun _ => rfl⟩
    have h2 : #(Below θ × Below θ → Bool) = (2 : Cardinal) ^ (θ * θ) := by
      have hp : #(Below θ × Below θ) = θ * θ := by simp [mk_prod, mk_ord_toType]
      simp [mk_arrow, hp, mk_bool, lift_uzero, lift_two]
    rw [h1, h2, Cardinal.mul_eq_self hθ]
    exact h2θ
  have hOcc : #(Set (Below θ) → Set (Below θ) → Bool) ≤ orbitRecordBound ell θ := by
    have h1 : #(Set (Below θ) → Set (Below θ) → Bool) =
        #(Set (Below θ) × Set (Below θ) → Bool) :=
      mk_congr ⟨fun f p => f p.1 p.2, fun f a b => f (a, b), fun _ => rfl, fun _ => rfl⟩
    have hinf : aleph0 ≤ (2 : Cardinal) ^ θ := le_trans hθ (hcant θ)
    have h2 : #(Set (Below θ) × Set (Below θ) → Bool) =
        (2 : Cardinal) ^ (((2 : Cardinal) ^ θ) * ((2 : Cardinal) ^ θ)) := by
      have hp : #(Set (Below θ) × Set (Below θ)) =
          ((2 : Cardinal) ^ θ) * ((2 : Cardinal) ^ θ) := by
        simp [mk_prod, mk_set, mk_ord_toType]
      simp [mk_arrow, hp, mk_bool, lift_uzero, lift_two]
    rw [h1, h2, Cardinal.mul_eq_self hinf]
    exact (power_le_power_left h2ne (power_le_power_left h2ne le_add_self)).trans_eq hB.symm
  rw [Cardinal.mk_congr (flatRecordEquiv lab θ)]
  simp only [mk_prod, lift_id]
  exact hprod hSet (hprod hSet (hprod hLab (hprod hArg (hprod hLt hOcc))))

/-- The forgetful map to flat records is injective. -/
theorem CanonicalRecord.toFlat_injective {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}} :
    Function.Injective (CanonicalRecord.toFlat (lab := lab) (arity := arity) (θ := θ)) := by
  classical
  rintro ⟨idx, slt, label₁, arg₁, lt₁, _, _, occ₁⟩ ⟨_, _, label₂, arg₂, lt₂, _, _, occ₂⟩ h
  have hidx : idx = _ := congrArg FlatRecord.idx h
  have hslt : slt = _ := congrArg FlatRecord.slt h
  subst hidx; subst hslt
  have hlab : label₁ = label₂ := by
    funext i
    have hx := congrFun (congrArg FlatRecord.label h) i.1
    dsimp [CanonicalRecord.toFlat] at hx
    simp only [i.2, ↓reduceDIte] at hx
    exact Option.some.inj hx
  subst hlab
  have harg : arg₁ = arg₂ := by
    funext i a
    have hx := congrFun (congrFun (congrArg FlatRecord.arg h) i.1) a.1
    dsimp [CanonicalRecord.toFlat] at hx
    simp only [i.2, a.2, ↓reduceDIte] at hx
    exact Subtype.ext (Option.some.inj hx)
  subst harg
  have hlt : lt₁ = lt₂ := by
    funext a b
    have hx := congrFun (congrFun (congrArg FlatRecord.lt h) a.1) b.1
    dsimp [CanonicalRecord.toFlat] at hx
    apply propext
    constructor
    · intro hab
      have : decide (∃ ha : a.1 ∈ slt, ∃ hb : b.1 ∈ slt, lt₁ ⟨a.1, ha⟩ ⟨b.1, hb⟩) = true :=
        decide_eq_true ⟨a.2, b.2, hab⟩
      rw [hx] at this
      exact (of_decide_eq_true this).choose_spec.choose_spec
    · intro hab
      have : decide (∃ ha : a.1 ∈ slt, ∃ hb : b.1 ∈ slt, lt₂ ⟨a.1, ha⟩ ⟨b.1, hb⟩) = true :=
        decide_eq_true ⟨a.2, b.2, hab⟩
      rw [← hx] at this
      exact (of_decide_eq_true this).choose_spec.choose_spec
  subst hlt
  have hocc : occ₁ = occ₂ := by
    funext L U
    have hx := congrFun (congrFun (congrArg FlatRecord.occupied h) (Subtype.val '' L))
      (Subtype.val '' U)
    dsimp [CanonicalRecord.toFlat] at hx
    have hL : Subtype.val '' L ⊆ slt := fun _ hx => by obtain ⟨z, _, rfl⟩ := hx; exact z.2
    have hU : Subtype.val '' U ⊆ slt := fun _ hx => by obtain ⟨z, _, rfl⟩ := hx; exact z.2
    have hLset : {z : ↥slt | z.1 ∈ Subtype.val '' L} = L := by
      ext z; simp [Set.mem_image]
    have hUset : {z : ↥slt | z.1 ∈ Subtype.val '' U} = U := by
      ext z; simp [Set.mem_image]
    apply propext
    constructor
    · intro ho
      have : decide (∃ (_hL : Subtype.val '' L ⊆ slt) (_hU : Subtype.val '' U ⊆ slt),
          occ₁ {z | z.1 ∈ Subtype.val '' L} {z | z.1 ∈ Subtype.val '' U}) = true :=
        decide_eq_true ⟨hL, hU, by rw [hLset, hUset]; exact ho⟩
      rw [hx] at this
      obtain ⟨_, _, hh⟩ := of_decide_eq_true this
      rwa [hLset, hUset] at hh
    · intro ho
      have : decide (∃ (_hL : Subtype.val '' L ⊆ slt) (_hU : Subtype.val '' U ⊆ slt),
          occ₂ {z | z.1 ∈ Subtype.val '' L} {z | z.1 ∈ Subtype.val '' U}) = true :=
        decide_eq_true ⟨hL, hU, by rw [hLset, hUset]; exact ho⟩
      rw [← hx] at this
      obtain ⟨_, _, hh⟩ := of_decide_eq_true this
      rwa [hLset, hUset] at hh
  subst hocc
  rfl

theorem mk_canonicalRecord_le_orbitRecordBound {lab : Type u} {arity : lab → ℕ}
    (θ ell : Cardinal.{u}) (hlab : #lab ≤ ell) (hθ : aleph0 ≤ θ) (hell : aleph0 ≤ ell) :
    #(CanonicalRecord lab arity θ) ≤ orbitRecordBound ell θ :=
  (mk_le_of_injective (CanonicalRecord.toFlat_injective (arity := arity))).trans
    (mk_flatRecord_le_orbitRecordBound (lab := lab) θ ell hlab hθ hell)

/-- An order isomorphism induces an isomorphism of models in an order presentation. -/
noncomputable def orderPresentationMapEquiv {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K)
    {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (e : I ≃o J) : (E.obj I).carrier ≃[K.τ] (E.obj J).carrier where
  toFun := E.map e.toOrderEmbedding
  invFun := E.map e.symm.toOrderEmbedding
  left_inv x := by
    have hcomp := E.map_comp e.toOrderEmbedding e.symm.toOrderEmbedding
    have htrans : e.toOrderEmbedding.trans e.symm.toOrderEmbedding =
        (OrderIso.refl I).toOrderEmbedding := by
      ext; exact e.symm_apply_apply _
    rw [htrans, E.map_id] at hcomp
    simpa [Language.Embedding.comp_apply, Language.Embedding.refl_apply] using
      (congrFun (congrArg (⇑) hcomp) x).symm
  right_inv y := by
    have hcomp := E.map_comp e.symm.toOrderEmbedding e.toOrderEmbedding
    have htrans : e.symm.toOrderEmbedding.trans e.toOrderEmbedding =
        (OrderIso.refl J).toOrderEmbedding := by
      ext; exact e.apply_symm_apply _
    rw [htrans, E.map_id] at hcomp
    simpa [Language.Embedding.comp_apply, Language.Embedding.refl_apply] using
      (congrFun (congrArg (⇑) hcomp) y).symm
  map_fun' {_} F xs := (E.map e.toOrderEmbedding).map_fun' F xs
  map_rel' {_} R xs := (E.map e.toOrderEmbedding).map_rel' R xs

theorem orderPresentationMapEquiv_strong {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K)
    {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (e : I ≃o J) : K.Strong (orderPresentationMapEquiv E e).toEmbedding :=
  E.map_strong e.toOrderEmbedding

theorem orderPresentation_obj_mem {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    (I : Type u) [LinearOrder I] [Nonempty I] : K.Mem (E.obj I) := by
  inhabit I
  exact K.strong_mem_cod (E.sub_incl {default} (Finset.singleton_nonempty _))
    (E.sub_strong {default} (Finset.singleton_nonempty _))

theorem orderPresentation_obj_card {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] {κ : Cardinal.{u}}
    (hI : #I = κ) (hle : ls K ≤ κ) (hκ : aleph0 ≤ κ) :
    Model.card (E.obj I) = κ := by
  apply le_antisymm
  · have hupper := E.card_upper (I := I)
    rw [E.ell_eq, hI] at hupper
    exact hupper.trans (le_of_eq (add_eq_left hκ hle))
  · simpa [hI] using E.card_lower (I := I)

/-- A fresh copy of `Below κ`, so we can equip it with the transported `H(δ)` order. -/
structure SoftCarrier (κ : Cardinal.{u}) where
  toBelow : Below κ

noncomputable def softCarrierEquiv (κ : Cardinal.{u}) : SoftCarrier κ ≃ Below κ where
  toFun := SoftCarrier.toBelow
  invFun := SoftCarrier.mk
  left_inv := fun ⟨_⟩ => rfl
  right_inv := fun _ => rfl

theorem mk_softCarrier (κ : Cardinal.{u}) : #(SoftCarrier κ) = κ := by
  rw [Cardinal.mk_congr (softCarrierEquiv κ), mk_ord_toType]

/-- A small linear order isomorphic to `H(δ)` when `|δ| = κ`, with matching cardinality. -/
noncomputable def horderSmallCopy {δ : _root_.Ordinal.{u}} {κ : Cardinal.{u}}
    (hδ : Order.IsSuccLimit δ) (hcard : δ.card = κ) :
    Σ' (I : Type u) (_ : LinearOrder I) (_ : Nonempty I) (_ : HOrder δ ≃o I), #I = κ := by
  classical
  have hmk : #(HOrder δ) = lift.{u + 1} κ := by rw [← hcard, ← HOrder.card_eq hδ]
  let β : Type u := SoftCarrier κ
  have hβ : #β = κ := mk_softCarrier κ
  have hU : #(ULift.{u + 1} β) = lift.{u + 1} κ := by rw [mk_uLift, hβ]
  let e : HOrder δ ≃ ULift.{u + 1} β :=
    Classical.choice (Cardinal.eq.mp (hmk.trans hU.symm))
  let eβ : HOrder δ ≃ β := e.trans Equiv.ulift
  letI lin : LinearOrder β := LinearOrder.lift' eβ.symm eβ.symm.injective
  have hpos : κ ≠ 0 := by
    intro hz
    exact hδ.ne_bot (Ordinal.card_eq_zero.mp (hcard.trans hz))
  haveI : Nonempty β := (mk_ne_zero_iff.mp (by rw [hβ]; exact hpos))
  refine ⟨β, lin, ‹Nonempty β›, RelIso.mk eβ ?_, hβ⟩
  intro a b
  change eβ.symm (eβ a) ≤ eβ.symm (eβ b) ↔ a ≤ b
  simp [Equiv.symm_apply_apply]

noncomputable def categoricityOrdinal (κ θ : Cardinal.{u}) : _root_.Ordinal.{u} :=
  κ.ord + (Order.succ θ).ord

theorem categoricityOrdinal_card {κ θ : Cardinal.{u}}
    (hκ : aleph0 ≤ κ) (hle : Order.succ θ ≤ κ) :
    (categoricityOrdinal κ θ).card = κ := by
  dsimp [categoricityOrdinal]
  rw [Ordinal.card_add, Cardinal.card_ord, Cardinal.card_ord]
  rw [Cardinal.add_eq_max hκ, max_eq_left hle]

theorem categoricityOrdinal_cof {κ θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) :
    Ordinal.cof (categoricityOrdinal κ θ) = Order.succ θ := by
  dsimp [categoricityOrdinal]
  have hlim : Order.IsSuccLimit (Order.succ θ).ord :=
    Cardinal.isSuccLimit_ord (le_trans hθ (Order.le_succ θ))
  rw [Ordinal.cof_add κ.ord hlim.ne_bot, (isRegular_succ hθ).cof_ord]

theorem categoricityOrdinal_isSuccLimit {κ θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) :
    Order.IsSuccLimit (categoricityOrdinal κ θ) := by
  dsimp [categoricityOrdinal]
  exact Ordinal.isSuccLimit_add κ.ord
    (Cardinal.isSuccLimit_ord (le_trans hθ (Order.le_succ θ)))

/-- Occupancy is preserved by order isomorphisms (cross-universe). -/
theorem occupied_orderIso {α : Type u} {β : Type v} [LinearOrder α] [LinearOrder β]
    (e : α ≃o β) (L U : Set α) : Occupied L U ↔ Occupied (e '' L) (e '' U) := by
  simp only [Occupied, strictSlot]
  constructor
  · rintro ⟨x, hxL, hxU, hL, hU⟩
    refine ⟨e x, ?_, ?_, ?_, ?_⟩
    · intro ⟨z, hz, heq⟩; exact hxL (e.injective heq ▸ hz)
    · intro ⟨z, hz, heq⟩; exact hxU (e.injective heq ▸ hz)
    · intro a ha; obtain ⟨z, hz, rfl⟩ := ha; exact e.lt_iff_lt.mpr (hL z hz)
    · intro b hb; obtain ⟨z, hz, rfl⟩ := hb; exact e.lt_iff_lt.mpr (hU z hz)
  · rintro ⟨y, hyL, hyU, hL, hU⟩
    obtain ⟨x, rfl⟩ : ∃ x, e x = y := ⟨e.symm y, e.apply_symm_apply y⟩
    refine ⟨x, ?_, ?_, ?_, ?_⟩
    · intro hx; exact hyL ⟨x, hx, rfl⟩
    · intro hx; exact hyU ⟨x, hx, rfl⟩
    · intro a ha; exact e.lt_iff_lt.mp (hL (e a) ⟨a, ha, rfl⟩)
    · intro b hb; exact e.lt_iff_lt.mp (hU (e b) ⟨b, hb, rfl⟩)

/-- Structure automorphisms of a member of `K` are strong, so orbit equality is pure
conjugacy of tuples. -/
theorem sameAutOrbit_iff_equiv (K : AbstractElementaryClass.{u}) {M : Model K.τ}
    (hM : K.Mem M) {ι : Type u} (xs ys : ι → M.carrier) :
    SameAutOrbit K M xs ys ↔
      ∃ e : M.carrier ≃[K.τ] M.carrier, ∀ i, e (xs i) = ys i := by
  constructor
  · rintro ⟨e, _, he⟩; exact ⟨e, he⟩
  · rintro ⟨e, he⟩; exact ⟨e, strong_of_equiv K e hM, he⟩

/-- Conjugate a structure automorphism along a structure isomorphism. -/
noncomputable def conjAut {L : FirstOrder.Language} {M N : Type u}
    [L.Structure M] [L.Structure N] (φ : M ≃[L] N) (e : M ≃[L] M) : N ≃[L] N := by
  refine ⟨φ.toEquiv.symm.trans (e.toEquiv.trans φ.toEquiv), ?_, ?_⟩
  · intro n f xs
    change φ (e (φ.symm (Language.Structure.funMap f xs))) =
      Language.Structure.funMap f (fun i => φ (e (φ.symm (xs i))))
    have h1 : φ.symm (Language.Structure.funMap f xs) =
        Language.Structure.funMap f (fun i => φ.symm (xs i)) := φ.symm.map_fun' f xs
    have h2 : e (Language.Structure.funMap f (fun i => φ.symm (xs i))) =
        Language.Structure.funMap f (fun i => e (φ.symm (xs i))) :=
      e.map_fun' f (fun i => φ.symm (xs i))
    have h3 : φ (Language.Structure.funMap f (fun i => e (φ.symm (xs i)))) =
        Language.Structure.funMap f (fun i => φ (e (φ.symm (xs i)))) :=
      φ.map_fun' f (fun i => e (φ.symm (xs i)))
    rw [h1, h2, h3]
  · intro n r xs
    change Language.Structure.RelMap r (fun i => φ (e (φ.symm (xs i)))) ↔
      Language.Structure.RelMap r xs
    exact (φ.map_rel' r (fun i => e (φ.symm (xs i)))).trans <|
      (e.map_rel' r (fun i => φ.symm (xs i))).trans (φ.symm.map_rel' r xs)

/-- Conjugating tuples by a structure isomorphism preserves automorphism orbits. -/
theorem sameAutOrbit_congr (K : AbstractElementaryClass.{u}) {M N : Model K.τ}
    (hM : K.Mem M) (φ : M.carrier ≃[K.τ] N.carrier) {ι : Type u}
    (xs ys : ι → M.carrier) :
    SameAutOrbit K M xs ys ↔ SameAutOrbit K N (φ ∘ xs) (φ ∘ ys) := by
  have hN : K.Mem N := K.iso_closed ⟨φ⟩ hM
  rw [sameAutOrbit_iff_equiv K hM, sameAutOrbit_iff_equiv K hN]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨conjAut φ e, fun i => ?_⟩
    change φ (e (φ.symm (φ (xs i)))) = φ (ys i)
    rw [φ.symm_apply_apply, he i]
  · rintro ⟨e, he⟩
    refine ⟨conjAut φ.symm e, fun i => ?_⟩
    change φ.symm (e (φ (xs i))) = ys i
    exact φ.symm_apply_eq.mpr (he i)

/-- A choice of realizing support term for each element of an EM model. -/
noncomputable def supportTermOf {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] (x : (E.obj I).carrier) :
    SupportTerm E.lab E.arity I :=
  Classical.choose (E.realize_surjective (I := I) x)

theorem realize_supportTermOf {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] (x : (E.obj I).carrier) :
    E.realize (supportTermOf E x) = x :=
  Classical.choose_spec (E.realize_surjective (I := I) x)

/-- Positions appearing in the realizing terms of a tuple. -/
noncomputable def tuplePositions {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] {ι : Type u}
    (xs : ι → (E.obj I).carrier) : Set I :=
  ⋃ i, Set.range (supportTermOf E (xs i)).pos

/-- Flatten the finitely many argument positions of a tuple of realizing terms. -/
noncomputable def orbitRecordOfTuple {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] {ι : Type u}
    (xs : ι → (E.obj I).carrier) : OrbitRecord E.lab E.arity where
  index := ι
  slot := ↥(tuplePositions E xs)
  label := fun i => (supportTermOf E (xs i)).label
  arg := fun i a =>
    ⟨(supportTermOf E (xs i)).pos a,
      Set.mem_iUnion.mpr ⟨i, Set.mem_range_self a⟩⟩
  lt := fun a b => (a : I) < b
  arg_strict := fun i a b hab => (supportTermOf E (xs i)).increasing hab
  arg_surj := fun x => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp x.2
    obtain ⟨a, ha⟩ := Set.mem_range.mp hi
    exact ⟨i, a, Subtype.ext ha⟩
  occupied := fun L U => Occupied (Subtype.val '' L) (Subtype.val '' U)

theorem orbitRecordOfTuple_slot_card {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] {ι : Type u} {θ : Cardinal.{u}}
    (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ) (xs : ι → (E.obj I).carrier) :
    #(orbitRecordOfTuple E xs).slot ≤ θ := by
  have hfin (i : ι) : #(Set.range (supportTermOf E (xs i)).pos) ≤ (ℵ₀ : Cardinal.{u}) := by
    have h := mk_range_le_lift (f := (supportTermOf E (xs i)).pos)
    rw [lift_uzero] at h
    refine h.trans ?_
    rw [mk_fin, lift_natCast]
    exact (natCast_lt_aleph0 (n := _)).le
  have hunion : #(tuplePositions E xs) ≤ #ι * (ℵ₀ : Cardinal.{u}) :=
    (mk_iUnion_le_sum_mk).trans <|
      (Cardinal.sum_le_sum (fun i => #(Set.range (supportTermOf E (xs i)).pos))
        (fun _ => (ℵ₀ : Cardinal.{u})) hfin).trans <| by simp [Cardinal.sum_const]
  have hmul : #ι * (ℵ₀ : Cardinal.{u}) ≤ θ :=
    (mul_le_mul' hι (le_rfl : (ℵ₀ : Cardinal.{u}) ≤ ℵ₀)).trans <|
      le_of_eq (Cardinal.mul_eq_left hθ hθ aleph0_ne_zero)
  exact hunion.trans hmul

theorem realizes_orbitRecordOfTuple {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] {ι : Type u}
    (xs : ι → (E.obj I).carrier) :
    RealizesOrbitRecord (I := I) E (orbitRecordOfTuple E xs)
      (fun s => Subtype.val s) xs := by
  refine ⟨Subtype.val_injective, fun _ _ => Iff.rfl, ?_, fun _ _ => Iff.rfl⟩
  intro i
  refine ⟨(supportTermOf E (xs i)).pos, (supportTermOf E (xs i)).increasing, fun _ => rfl, ?_⟩
  exact (realize_supportTermOf E (xs i)).symm

/-- Canonical record assigned to a tuple via its realizing presentation, using the
fixed `embedBelow` so index equivalences are unique for fixed `ι` and `θ`. -/
noncomputable def canonicalOfTuple {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] {ι : Type u} {θ : Cardinal.{u}}
    (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ) (xs : ι → (E.obj I).carrier) :
    CanonicalRecord E.lab E.arity θ :=
  (orbitRecordOfTuple E xs).toCanonical hι (orbitRecordOfTuple_slot_card E hθ hι xs)

theorem canonicalOfTuple_same {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] {ι : Type u} {θ : Cardinal.{u}}
    (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ) (xs : ι → (E.obj I).carrier) :
    OrbitRecord.Same (orbitRecordOfTuple E xs)
      (CanonicalRecord.toOrbitRecord (canonicalOfTuple E hθ hι xs)) :=
  (orbitRecordOfTuple E xs).toCanonical_same hι (orbitRecordOfTuple_slot_card E hθ hι xs)

/-- Index equivalence for `canonicalOfTuple`; depends only on `ι` and `θ`, not the tuple. -/
noncomputable def canonicalOfTupleIndexEquiv {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I : Type u} [LinearOrder I] [Nonempty I]
    {ι : Type u} {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) :
    ι ≃ ↥(canonicalOfTuple E hθ hι xs).idx :=
  (orbitRecordOfTuple E xs).toCanonicalIndexEquiv hι
    (orbitRecordOfTuple_slot_card E hθ hι xs)

/-- Slot equivalence for `canonicalOfTuple`. -/
noncomputable def canonicalOfTupleSlotEquiv {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I : Type u} [LinearOrder I] [Nonempty I]
    {ι : Type u} {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) :
    (orbitRecordOfTuple E xs).slot ≃ ↥(canonicalOfTuple E hθ hι xs).slt :=
  (orbitRecordOfTuple E xs).toCanonicalSlotEquiv hι
    (orbitRecordOfTuple_slot_card E hθ hι xs)

/-- Placement of the canonical slot into `I` for a realizing tuple. -/
noncomputable def canonicalPlaceOfTuple {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I : Type u} [LinearOrder I] [Nonempty I]
    {ι : Type u} {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) :
    (canonicalOfTuple E hθ hι xs).slt → I :=
  fun s => ((canonicalOfTupleSlotEquiv E hθ hι xs).symm s).val

/-- Reindexed tuple realizing the canonical record. -/
noncomputable def canonicalTupleReindex {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I : Type u} [LinearOrder I] [Nonempty I]
    {ι : Type u} {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) :
    (canonicalOfTuple E hθ hι xs).idx → (E.obj I).carrier :=
  fun j => xs ((canonicalOfTupleIndexEquiv E hθ hι xs).symm j)

theorem realizes_canonicalOfTuple {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I : Type u} [LinearOrder I] [Nonempty I]
    {ι : Type u} {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) :
    RealizesOrbitRecord (I := I) E
      (CanonicalRecord.toOrbitRecord (canonicalOfTuple E hθ hι xs))
      (canonicalPlaceOfTuple E hθ hι xs) (canonicalTupleReindex E hθ hι xs) := by
  let rec0 := orbitRecordOfTuple E xs
  let e_i := canonicalOfTupleIndexEquiv E hθ hι xs
  let e_s := canonicalOfTupleSlotEquiv E hθ hι xs
  have h0 := realizes_orbitRecordOfTuple E xs
  refine ⟨?inj, ?lt, ?term, ?occ⟩
  · intro a b h
    dsimp [canonicalPlaceOfTuple] at h
    exact e_s.symm.injective (Subtype.ext h)
  · intro a b
    dsimp [canonicalPlaceOfTuple, CanonicalRecord.toOrbitRecord, OrbitRecord.toCanonical]
    change rec0.lt (e_s.symm a) (e_s.symm b) ↔ (e_s.symm a).val < (e_s.symm b).val
    exact h0.2.1 (e_s.symm a) (e_s.symm b)
  · intro j
    obtain ⟨pos, hinc, hpos, hxs⟩ := h0.2.2.1 (e_i.symm j)
    refine ⟨pos, hinc, ?_, ?_⟩
    · intro a
      dsimp [canonicalPlaceOfTuple, CanonicalRecord.toOrbitRecord]
      have harg : (canonicalOfTuple E hθ hι xs).arg j a = e_s (rec0.arg (e_i.symm j) a) := by
        dsimp [canonicalOfTuple, OrbitRecord.toCanonical, OrbitRecord.toCanonicalSlotEquiv,
          OrbitRecord.toCanonicalIndexEquiv]
        rfl
      rw [harg, Equiv.symm_apply_apply]
      exact hpos a
    · dsimp [canonicalTupleReindex]
      convert hxs
      refine SupportTerm.ext_of_label_eq ?_ fun _ => rfl
      dsimp [CanonicalRecord.toOrbitRecord, canonicalOfTuple, OrbitRecord.toCanonical,
        OrbitRecord.toCanonicalIndexEquiv]
      rfl
  · intro L U
    have h := h0.2.2.2 (e_s.symm '' L) (e_s.symm '' U)
    have himg (S : Set ↥(canonicalOfTuple E hθ hι xs).slt) :
        Subtype.val '' (e_s.symm '' S) =
          (fun s : ↥(canonicalOfTuple E hθ hι xs).slt => (e_s.symm s).val) '' S := by
      ext x
      constructor
      · rintro ⟨t, ⟨s, hs, rfl⟩, rfl⟩
        exact ⟨s, hs, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨e_s.symm s, ⟨s, hs, rfl⟩, rfl⟩
    dsimp [canonicalPlaceOfTuple, CanonicalRecord.toOrbitRecord, OrbitRecord.toCanonical]
    change rec0.occupied (e_s.symm '' L) (e_s.symm '' U) ↔
      Occupied ((fun s => (e_s.symm s).val) '' L) ((fun s => (e_s.symm s).val) '' U)
    rw [← himg L, ← himg U]
    exact h

/-- The setoid of automorphism orbits of `ι`-tuples. -/
def autOrbitSetoid (K : AbstractElementaryClass.{u}) (M : Model K.τ) (hM : K.Mem M)
    (ι : Type u) : Setoid (ι → M.carrier) where
  r := SameAutOrbit K M
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro xs
      exact ⟨Language.Equiv.refl _ _, strong_of_equiv K (Language.Equiv.refl _ _) hM, fun _ => rfl⟩
    · intro xs ys ⟨e, _, he⟩
      refine ⟨e.symm, strong_of_equiv K e.symm hM, fun i => ?_⟩
      have := congrArg e.symm (he i)
      simpa [Equiv.symm_apply_apply] using this.symm
    · intro xs ys zs ⟨e, _, he⟩ ⟨f, _, hf⟩
      let ef : M.carrier ≃[K.τ] M.carrier :=
        ⟨e.toEquiv.trans f.toEquiv,
          fun {_} F xs => by
            change f (e (Language.Structure.funMap F xs)) =
              Language.Structure.funMap F (fun a => f (e (xs a)))
            have h1 : e (Language.Structure.funMap F xs) =
                Language.Structure.funMap F (fun a => e (xs a)) := e.map_fun' F xs
            have h2 : f (Language.Structure.funMap F (fun a => e (xs a))) =
                Language.Structure.funMap F (fun a => f (e (xs a))) :=
              f.map_fun' F (fun a => e (xs a))
            rw [h1, h2],
          fun {_} R xs => by
            change Language.Structure.RelMap R (fun a => f (e (xs a))) ↔
              Language.Structure.RelMap R xs
            exact (f.map_rel' R (fun a => e (xs a))).trans (e.map_rel' R xs)⟩
      exact ⟨ef, strong_of_equiv K ef hM, fun i => by
        change f (e (xs i)) = zs i; rw [he i, hf i]⟩

/-- Equal realized records determine a single model automorphism orbit, via Theorem 3.5. -/
theorem same_record_sameAutOrbit {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    (δ : _root_.Ordinal.{u}) (θ : Cardinal.{u})
    (hδ : Order.IsSuccLimit δ) (hθ : aleph0 ≤ θ)
    (hcf : θ < Ordinal.cof δ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (rec : OrbitRecord E.lab E.arity) (hslot : #rec.slot ≤ θ)
    (place₁ place₂ : rec.slot → I) (xs ys : rec.index → (E.obj I).carrier)
    (h₁ : RealizesOrbitRecord (I := I) E rec place₁ xs)
    (h₂ : RealizesOrbitRecord (I := I) E rec place₂ ys) :
    SameAutOrbit K (E.obj I) xs ys := by
  classical
  -- Work with order diagrams on `I` (universe `u`), then transport to `H(δ)`.
  have hdiagI : SameOrderDiagram place₁ place₂ := by
    constructor
    · intro a b
      constructor
      · intro h; exact congrArg place₂ (h₁.1 h)
      · intro h; exact congrArg place₁ (h₂.1 h)
    · intro a b; rw [← h₁.2.1 a b, ← h₂.2.1 a b]
  have hoccI : SameSlotOccupancy place₁ place₂ := by
    intro lower upper _ _
    exact (h₁.2.2.2 lower upper).symm.trans (h₂.2.2.2 lower upper)
  let xsH : ULift.{u + 1} rec.slot → HOrder δ := fun i => eISO.symm (place₁ i.down)
  let ysH : ULift.{u + 1} rec.slot → HOrder δ := fun i => eISO.symm (place₂ i.down)
  have hdiag : SameOrderDiagram xsH ysH := by
    constructor
    · intro a b
      constructor
      · intro h
        have hpl : place₁ a.down = place₁ b.down := by
          have := congrArg eISO h
          simpa [xsH, OrderIso.apply_symm_apply] using this
        have hab : a.down = b.down := h₁.1 hpl
        cases a; cases b; cases hab; rfl
      · intro h
        have hpl : place₂ a.down = place₂ b.down := by
          have := congrArg eISO h
          simpa [ysH, OrderIso.apply_symm_apply] using this
        have hab : a.down = b.down := h₂.1 hpl
        cases a; cases b; cases hab; rfl
    · intro a b
      rw [eISO.symm.lt_iff_lt, eISO.symm.lt_iff_lt, hdiagI.2 a.down b.down]
  have hocc : SameSlotOccupancy xsH ysH := by
    intro lower upper hlt1 hlt2
    let lower0 : Set rec.slot := ULift.down '' lower
    let upper0 : Set rec.slot := ULift.down '' upper
    have hlt1' : ∀ i ∈ lower0, ∀ j ∈ upper0, place₁ i < place₁ j := by
      intro i hi j hj
      obtain ⟨i', hi', rfl⟩ := hi; obtain ⟨j', hj', rfl⟩ := hj
      exact eISO.symm.lt_iff_lt.mp (hlt1 i' hi' j' hj')
    have hlt2' : ∀ i ∈ lower0, ∀ j ∈ upper0, place₂ i < place₂ j := by
      intro i hi j hj
      obtain ⟨i', hi', rfl⟩ := hi; obtain ⟨j', hj', rfl⟩ := hj
      exact eISO.symm.lt_iff_lt.mp (hlt2 i' hi' j' hj')
    have hPlaces := hoccI lower0 upper0 hlt1' hlt2'
    have hxL : xsH '' lower = eISO.symm '' (place₁ '' lower0) := by
      change (fun i => eISO.symm (place₁ i.down)) '' lower = _
      rw [← Set.image_comp, ← Set.image_comp]
      rfl
    have hxU : xsH '' upper = eISO.symm '' (place₁ '' upper0) := by
      change (fun i => eISO.symm (place₁ i.down)) '' upper = _
      rw [← Set.image_comp, ← Set.image_comp]
      rfl
    have hyL : ysH '' lower = eISO.symm '' (place₂ '' lower0) := by
      change (fun i => eISO.symm (place₂ i.down)) '' lower = _
      rw [← Set.image_comp, ← Set.image_comp]
      rfl
    have hyU : ysH '' upper = eISO.symm '' (place₂ '' upper0) := by
      change (fun i => eISO.symm (place₂ i.down)) '' upper = _
      rw [← Set.image_comp, ← Set.image_comp]
      rfl
    have hx : Occupied (xsH '' lower) (xsH '' upper) ↔
        Occupied (place₁ '' lower0) (place₁ '' upper0) := by
      rw [hxL, hxU]
      exact (occupied_orderIso eISO.symm (place₁ '' lower0) (place₁ '' upper0)).symm
    have hy : Occupied (ysH '' lower) (ysH '' upper) ↔
        Occupied (place₂ '' lower0) (place₂ '' upper0) := by
      rw [hyL, hyU]
      exact (occupied_orderIso eISO.symm (place₂ '' lower0) (place₂ '' upper0)).symm
    exact hx.trans (hPlaces.trans hy.symm)
  have hιU : #(ULift.{u + 1} rec.slot) ≤ lift.{u + 1} θ := by
    rw [mk_uLift]; exact lift_le.mpr hslot
  have hcfU : lift.{u + 1} θ < lift.{u + 1} (Ordinal.cof δ) := lift_lt.mpr hcf
  obtain ⟨φ, hφ⟩ :=
    (horder_orbit_iff δ θ hδ hθ hcfU (ι := ULift.{u + 1} rec.slot) hιU xsH ysH).mp
      ⟨hdiag, hocc⟩
  let ψ : I ≃o I := eISO.symm.trans (φ.trans eISO)
  have hψplace : ∀ s, ψ (place₁ s) = place₂ s := by
    intro s
    have := hφ ⟨s⟩
    dsimp [xsH, ysH] at this
    change eISO (φ (eISO.symm (place₁ s))) = place₂ s
    rw [this, OrderIso.apply_symm_apply]
  let Φ := orderPresentationMapEquiv E ψ
  refine ⟨Φ, orderPresentationMapEquiv_strong E ψ, ?_⟩
  intro i
  obtain ⟨pos₁, hinc₁, hpos₁, hxs⟩ := h₁.2.2.1 i
  obtain ⟨pos₂, _hinc₂, hpos₂, hys⟩ := h₂.2.2.1 i
  have hmap := E.realize_map ψ.toOrderEmbedding ⟨rec.label i, pos₁, hinc₁⟩
  have hposψ : ∀ a, ψ (pos₁ a) = pos₂ a := by
    intro a; rw [hpos₁ a, hpos₂ a, hψplace]
  have hxs' : Φ (xs i) = E.realize ⟨rec.label i, ψ ∘ pos₁, ψ.strictMono.comp hinc₁⟩ := by
    rw [hxs]; exact hmap
  rw [hxs']
  convert hys.symm using 1
  congr 1
  exact SupportTerm.ext_of_label_eq rfl fun a => by
    change (ψ ∘ pos₁) a = pos₂ (Fin.cast (congrArg E.arity rfl) a)
    simpa using hposψ a

private theorem setElem_congr {α : Type u} {s t : Set α} (h : s = t) :
    { x // x ∈ s } = { x // x ∈ t } :=
  congrArg (fun u : Set α => { x // x ∈ u }) h

/-- Placement of `xs` into a canon `r` equal to `canonicalOfTuple xs`. -/
noncomputable def canonicalPlaceEq {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I : Type u} [LinearOrder I] [Nonempty I]
    {ι : Type u} {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) (r : CanonicalRecord E.lab E.arity θ)
    (hr : canonicalOfTuple E hθ hι xs = r) : ↥r.slt → I :=
  fun s => canonicalPlaceOfTuple E hθ hι xs
    (cast (setElem_congr (congrArg CanonicalRecord.slt hr.symm)) s)

/-- Reindexed `xs` at a canon `r` equal to `canonicalOfTuple xs`. -/
noncomputable def canonicalTupleEq {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I : Type u} [LinearOrder I] [Nonempty I]
    {ι : Type u} {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) (r : CanonicalRecord E.lab E.arity θ)
    (hr : canonicalOfTuple E hθ hι xs = r) : ↥r.idx → (E.obj I).carrier :=
  fun j => canonicalTupleReindex E hθ hι xs
    (cast (setElem_congr (congrArg CanonicalRecord.idx hr.symm)) j)

theorem realizes_canonical_eq {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I : Type u} [LinearOrder I] [Nonempty I]
    {ι : Type u} {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) (r : CanonicalRecord E.lab E.arity θ)
    (hr : canonicalOfTuple E hθ hι xs = r) :
    RealizesOrbitRecord (I := I) E (CanonicalRecord.toOrbitRecord r)
      (canonicalPlaceEq E hθ hι xs r hr) (canonicalTupleEq E hθ hι xs r hr) := by
  subst hr
  have hp : canonicalPlaceEq E hθ hι xs (canonicalOfTuple E hθ hι xs) rfl =
      canonicalPlaceOfTuple E hθ hι xs := by
    ext s; simp [canonicalPlaceEq]
  have ht : canonicalTupleEq E hθ hι xs (canonicalOfTuple E hθ hι xs) rfl =
      canonicalTupleReindex E hθ hι xs := by
    ext j; simp [canonicalTupleEq]
  rw [hp, ht]
  exact realizes_canonicalOfTuple E hθ hι xs

theorem canonicalTupleEq_apply {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I : Type u} [LinearOrder I] [Nonempty I]
    {ι : Type u} {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) (r : CanonicalRecord E.lab E.arity θ)
    (hr : canonicalOfTuple E hθ hι xs = r) (i : ι) :
    canonicalTupleEq E hθ hι xs r hr
      (cast (setElem_congr (congrArg CanonicalRecord.idx hr))
        (canonicalOfTupleIndexEquiv E hθ hι xs i)) = xs i := by
  subst hr
  simp [canonicalTupleEq, canonicalTupleReindex, Equiv.symm_apply_apply]

theorem indexCast_eq {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I : Type u} [LinearOrder I] [Nonempty I]
    {ι : Type u} {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hι : #ι ≤ θ)
    (xs ys : ι → (E.obj I).carrier)
    (hcan : canonicalOfTuple E hθ hι xs = canonicalOfTuple E hθ hι ys) (i : ι) :
    cast (setElem_congr (congrArg CanonicalRecord.idx hcan))
      (canonicalOfTupleIndexEquiv E hθ hι xs i) =
      canonicalOfTupleIndexEquiv E hθ hι ys i := by
  apply Subtype.ext
  rfl

/-- Equal canonical records for two `ι`-tuples yield the same automorphism orbit. -/
theorem same_canonical_sameAutOrbit {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) (δ : _root_.Ordinal.{u}) (θ : Cardinal.{u})
    (hδ : Order.IsSuccLimit δ) (hθ : aleph0 ≤ θ) (hcf : θ < Ordinal.cof δ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    {ι : Type u} (hι : #ι ≤ θ) (xs ys : ι → (E.obj I).carrier)
    (hcan : canonicalOfTuple E hθ hι xs = canonicalOfTuple E hθ hι ys) :
    SameAutOrbit K (E.obj I) xs ys := by
  classical
  let r := canonicalOfTuple E hθ hι ys
  have hslt : #(CanonicalRecord.toOrbitRecord r).slot ≤ θ := canonical_record_card_slot r
  have hrx := realizes_canonical_eq E hθ hι xs r hcan
  have hry := realizes_canonical_eq E hθ hι ys r rfl
  have horb := same_record_sameAutOrbit E δ θ hδ hθ hcf eISO
    (CanonicalRecord.toOrbitRecord r) hslt _ _ _ _ hrx hry
  obtain ⟨Φ, hstrong, hΦ⟩ := horb
  refine ⟨Φ, hstrong, fun i => ?_⟩
  have hx := canonicalTupleEq_apply E hθ hι xs r hcan i
  have hy : canonicalTupleEq E hθ hι ys r rfl
      (canonicalOfTupleIndexEquiv E hθ hι ys i) = ys i := by
    simpa [cast_eq] using canonicalTupleEq_apply E hθ hι ys r rfl i
  have he := indexCast_eq E hθ hι xs ys hcan i
  rw [← hx]
  refine (hΦ _).trans ?_
  rw [he, hy]

end
end AEC
