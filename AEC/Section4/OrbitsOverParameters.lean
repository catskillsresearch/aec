module

public import AEC.Section2.OrderPresentation
public import AEC.Section3.UniformOrbitBound
public import AEC.Section3.Elimination
public import AEC.Section3.Alignment
public import AEC.Section3.IndecomposableSegment
public import AEC.Section3.Occupancy
public import AEC.Section3.OrderEqualityDiagram
public import AEC.Section1.Categorical
public import AEC.Section1.ArbitrarilyLarge
public import AEC.Section2.Results
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Finsupp
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.Data.Rat.Denumerable

/-!
# Lemma 4.5 — orbits over parameters

Relative fingerprints (`RelFingerprint`) are ≤χ (`mk_relFingerprint_le`). The joint soft
canon is reconstructed by `relJointCanonOf` from fixed parameters + fingerprint, so
`equal_fingerprint_equal_joint_canon` holds. The remaining gap for the orbit step is
`equal_fingerprint_same_orbit_over_params` (soft/eqOld/occ realize the joint record).
-/

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal Set Finsupp

private theorem add_one_le_two_pow' {a : Cardinal.{u}} (ha : aleph0 ≤ a) :
    a + 1 ≤ (2 : Cardinal) ^ a := by
  refine (add_le_max a 1).trans ?_
  refine max_le (max_le ?_ ?_) ?_
  · exact (Cardinal.cantor a).le
  · exact one_lt_aleph0.le.trans (ha.trans (Cardinal.cantor a).le)
  · exact ha.trans (Cardinal.cantor a).le

theorem mk_flatRecord_le_chi (lab : Type u) {σ χ : Cardinal.{u}}
    (hlab : #lab ≤ χ) (hσ : aleph0 ≤ σ) (hχinf : aleph0 ≤ χ) (hpow : χ ^ σ = χ)
    (h2 : (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) :
    #(FlatRecord lab σ) ≤ χ := by
  have h2ne : (2 : Cardinal.{u}) ≠ 0 := two_ne_zero
  have hχχ : χ * χ = χ := Cardinal.mul_eq_self hχinf
  have hmul {a b : Cardinal.{u}} (ha : a ≤ χ) (hb : b ≤ χ) : a * b ≤ χ :=
    (mul_le_mul' ha hb).trans (le_of_eq hχχ)
  have h2σ : (2 : Cardinal.{u}) ^ σ ≤ χ :=
    (power_le_power_left h2ne (cantor σ).le).trans h2
  have hSet : #(Set (Below σ)) ≤ χ := by
    simp [mk_set, mk_ord_toType]; exact h2σ
  have hLab : #(Below σ → Option lab) ≤ χ := by
    have heq : #(Below σ → Option lab) = #(Option lab) ^ σ := by
      simp [mk_arrow, mk_ord_toType]
    rw [heq]
    have hop : #(Option lab) ≤ χ := by
      rw [mk_option]
      exact (add_le_add hlab (one_le_aleph0.trans hχinf)).trans
        (le_of_eq (add_eq_self hχinf))
    exact (power_le_power_right hop).trans_eq hpow
  have hArg : #(Below σ → ℕ → Option (Below σ)) ≤ χ := by
    have heq : #(Below σ → ℕ → Option (Below σ)) = #(Option (Below σ)) ^ σ := by
      have h1 : #(Below σ → ℕ → Option (Below σ)) =
          #(Below σ × ℕ → Option (Below σ)) :=
        mk_congr ⟨fun f p => f p.1 p.2, fun f a n => f (a, n), fun _ => rfl, fun _ => rfl⟩
      have hdom : #(Below σ × ℕ) = σ := by
        have : #(Below σ × ℕ) = σ * ℵ₀ := by
          simp [mk_prod, mk_ord_toType, mk_nat, lift_uzero, lift_aleph0]
        rw [this, Cardinal.mul_eq_left hσ hσ aleph0_ne_zero]
      have harr : #(Below σ × ℕ → Option (Below σ)) = #(Option (Below σ)) ^ σ := by
        simp [mk_arrow, hdom]
      rw [h1, harr]
    rw [heq]
    have hop : #(Option (Below σ)) ≤ χ := by
      have : #(Option (Below σ)) = σ + 1 := by simp [mk_option, mk_ord_toType]
      rw [this]; exact (add_one_le_two_pow' hσ).trans h2σ
    exact (power_le_power_right hop).trans_eq hpow
  have hLt : #(Below σ → Below σ → Bool) ≤ χ := by
    have h1 : #(Below σ → Below σ → Bool) = #(Below σ × Below σ → Bool) :=
      mk_congr ⟨fun f p => f p.1 p.2, fun f a b => f (a, b), fun _ => rfl, fun _ => rfl⟩
    have h2' : #(Below σ × Below σ → Bool) = (2 : Cardinal) ^ (σ * σ) := by
      have hp : #(Below σ × Below σ) = σ * σ := by simp [mk_prod, mk_ord_toType]
      simp [mk_arrow, hp, mk_bool, lift_uzero, lift_two]
    rw [h1, h2', Cardinal.mul_eq_self hσ]
    exact h2σ
  have hOcc : #(Set (Below σ) → Set (Below σ) → Bool) ≤ χ := by
    have h1 : #(Set (Below σ) → Set (Below σ) → Bool) =
        #(Set (Below σ) × Set (Below σ) → Bool) :=
      mk_congr ⟨fun f p => f p.1 p.2, fun f a b => f (a, b), fun _ => rfl, fun _ => rfl⟩
    have hinf : aleph0 ≤ (2 : Cardinal) ^ σ := le_trans hσ (cantor σ).le
    have h2' : #(Set (Below σ) × Set (Below σ) → Bool) =
        (2 : Cardinal) ^ (((2 : Cardinal) ^ σ) * ((2 : Cardinal) ^ σ)) := by
      have hp : #(Set (Below σ) × Set (Below σ)) =
          ((2 : Cardinal) ^ σ) * ((2 : Cardinal) ^ σ) := by
        simp [mk_prod, mk_set, mk_ord_toType]
      simp [mk_arrow, hp, mk_bool, lift_uzero, lift_two]
    rw [h1, h2', Cardinal.mul_eq_self hinf]
    exact h2
  rw [Cardinal.mk_congr (flatRecordEquiv lab σ)]
  simp only [mk_prod, lift_id]
  exact hmul hSet (hmul hSet (hmul hLab (hmul hArg (hmul hLt hOcc))))

theorem mk_canonicalRecord_le_chi {lab : Type u} {arity : lab → ℕ}
    {σ χ : Cardinal.{u}} (hlab : #lab ≤ χ) (hσ : aleph0 ≤ σ) (hχinf : aleph0 ≤ χ)
    (hpow : χ ^ σ = χ)
    (h2 : (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) :
    #(CanonicalRecord lab arity σ) ≤ χ :=
  (mk_le_of_injective (CanonicalRecord.toFlat_injective (arity := arity))).trans
    (mk_flatRecord_le_chi lab hlab hσ hχinf hpow h2)

/-- Soft point with ordinals renamed into `Below χ` via cuts over a well-ordered support. -/
abbrev AbstractPoint (χ : Cardinal.{u}) : Type u :=
  (Below χ →₀ ℤ) →₀ ℚ

theorem mk_abstractPoint (χ : Cardinal.{u}) (hχ : aleph0 ≤ χ) :
    #(AbstractPoint χ) = χ := by
  haveI : Infinite (Below χ) := by
    rw [infinite_iff, mk_ord_toType]
    exact hχ
  have h1 : #(Below χ →₀ ℤ) = χ := by
    rw [mk_finsupp_lift_of_infinite (Below χ) ℤ]
    simp only [mk_ord_toType, mk_int, lift_uzero, lift_aleph0]
    exact max_eq_left hχ
  haveI : Infinite (Below χ →₀ ℤ) := by
    rw [infinite_iff, h1]; exact hχ
  -- Outer finsupp: `#((Below χ →₀ ℤ) →₀ ℚ) = max (lift #(_)) (lift #ℚ) = χ`.
  rw [mk_finsupp_lift_of_infinite (Below χ →₀ ℤ) ℚ, h1, mk_eq_aleph0 ℚ]
  simp [lift_aleph0, max_eq_left hχ]

/-- σ-bounded relative fingerprint over fixed parameter support (English Lemma 4.5 count). -/
structure RelFingerprint (lab : Type u) (arity : lab → ℕ) (σ χ : Cardinal.{u}) where
  newCanon : CanonicalRecord lab arity σ
  soft : Below σ → AbstractPoint χ
  eqOld : Below σ → Option (Below χ)
  occ : Set (Below σ) → Set (Below σ) → Bool

theorem mk_relFingerprint_le {lab : Type u} {arity : lab → ℕ} {σ χ : Cardinal.{u}}
    (hlab : #lab ≤ χ) (hσ : aleph0 ≤ σ) (hχinf : aleph0 ≤ χ) (hpow : χ ^ σ = χ)
    (h2 : (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) :
    #(RelFingerprint lab arity σ χ) ≤ χ := by
  classical
  let e : RelFingerprint lab arity σ χ ≃
      CanonicalRecord lab arity σ × (Below σ → AbstractPoint χ) ×
        (Below σ → Option (Below χ)) × (Set (Below σ) → Set (Below σ) → Bool) :=
    ⟨fun c => (c.newCanon, c.soft, c.eqOld, c.occ),
      fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩, fun _ => rfl, fun ⟨_, _, _, _⟩ => rfl⟩
  rw [Cardinal.mk_congr e]
  have hχχ : χ * χ = χ := Cardinal.mul_eq_self hχinf
  have hmul {a b : Cardinal.{u}} (ha : a ≤ χ) (hb : b ≤ χ) : a * b ≤ χ :=
    (mul_le_mul' ha hb).trans (le_of_eq hχχ)
  have h1 := mk_canonicalRecord_le_chi (arity := arity) hlab hσ hχinf hpow h2
  have hSoft : #(Below σ → AbstractPoint χ) ≤ χ := by
    have heq : #(Below σ → AbstractPoint χ) = #(AbstractPoint χ) ^ σ := by
      simp [mk_arrow, mk_ord_toType]
    rw [heq, mk_abstractPoint χ hχinf]
    exact le_of_eq hpow
  have hOpt : #(Below σ → Option (Below χ)) ≤ χ := by
    have heq : #(Below σ → Option (Below χ)) = #(Option (Below χ)) ^ σ := by
      simp [mk_arrow, mk_ord_toType]
    rw [heq]
    have hop : #(Option (Below χ)) ≤ χ := by
      rw [mk_option, mk_ord_toType]
      exact (add_le_add (le_refl χ) (one_le_aleph0.trans hχinf)).trans
        (le_of_eq (add_eq_self hχinf))
    exact (power_le_power_right hop).trans_eq hpow
  have hOcc : #(Set (Below σ) → Set (Below σ) → Bool) ≤ χ := by
    have h1' : #(Set (Below σ) → Set (Below σ) → Bool) =
        #(Set (Below σ) × Set (Below σ) → Bool) :=
      mk_congr ⟨fun f p => f p.1 p.2, fun f a b => f (a, b), fun _ => rfl, fun _ => rfl⟩
    have hinf : aleph0 ≤ (2 : Cardinal) ^ σ := le_trans hσ (cantor σ).le
    have h2' : #(Set (Below σ) × Set (Below σ) → Bool) =
        (2 : Cardinal) ^ (((2 : Cardinal) ^ σ) * ((2 : Cardinal) ^ σ)) := by
      have hp : #(Set (Below σ) × Set (Below σ)) =
          ((2 : Cardinal) ^ σ) * ((2 : Cardinal) ^ σ) := by
        simp [mk_prod, mk_set, mk_ord_toType]
      simp [mk_arrow, hp, mk_bool, lift_uzero, lift_two]
    rw [h1', h2', Cardinal.mul_eq_self hinf]
    exact h2
  simp only [mk_prod, lift_id]
  exact hmul h1 (hmul hSoft (hmul hOpt hOcc))

/-- Relative code: fingerprint-determined joint soft canon plus σ-bounded fingerprint.
`jointCanon` is `relJointCanonOf` of the fingerprint (`equal_fingerprint_equal_joint_canon`).
Cardinality ≤χ of fingerprints: `mk_relFingerprint_le`. -/
structure RelCode (lab : Type u) (arity : lab → ℕ) (σ χ : Cardinal.{u}) where
  jointCanon : CanonicalRecord lab arity χ
  fingerprint : RelFingerprint lab arity σ χ

@[simp] def RelCode.newCanon {lab : Type u} {arity : lab → ℕ} {σ χ : Cardinal.{u}}
    (c : RelCode lab arity σ χ) : CanonicalRecord lab arity σ :=
  c.fingerprint.newCanon

@[simp] def RelCode.soft {lab : Type u} {arity : lab → ℕ} {σ χ : Cardinal.{u}}
    (c : RelCode lab arity σ χ) : Below σ → AbstractPoint χ :=
  c.fingerprint.soft

@[simp] def RelCode.eqOld {lab : Type u} {arity : lab → ℕ} {σ χ : Cardinal.{u}}
    (c : RelCode lab arity σ χ) : Below σ → Option (Below χ) :=
  c.fingerprint.eqOld

@[simp] def RelCode.occ {lab : Type u} {arity : lab → ℕ} {σ χ : Cardinal.{u}}
    (c : RelCode lab arity σ χ) : Set (Below σ) → Set (Below σ) → Bool :=
  c.fingerprint.occ

def SameOrbitOverParams (K : AbstractElementaryClass.{u}) (M : Model K.τ)
    (P : Set M.carrier) {ι : Type u} (xs ys : ι → M.carrier) : Prop :=
  ∃ e : M.carrier ≃[K.τ] M.carrier,
    K.Strong e.toEmbedding ∧ (∀ p ∈ P, e p = p) ∧ ∀ i, e (xs i) = ys i

theorem sameOrbitOverParams_congr (K : AbstractElementaryClass.{u})
    {M N : Model K.τ} (hM : K.Mem M) (φ : M.carrier ≃[K.τ] N.carrier)
    (P : Set M.carrier) {ι : Type u} (xs ys : ι → M.carrier) :
    SameOrbitOverParams K M P xs ys ↔
      SameOrbitOverParams K N (φ '' P) (φ ∘ xs) (φ ∘ ys) := by
  have hN : K.Mem N := K.iso_closed ⟨φ⟩ hM
  constructor
  · rintro ⟨e, heS, heP, he⟩
    refine ⟨conjAut φ e, strong_of_equiv K (conjAut φ e) hN, ?_, fun i => ?_⟩
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := hq
      change φ (e (φ.symm (φ p))) = φ p
      rw [φ.symm_apply_apply, heP p hp]
    · change φ (e (φ.symm (φ (xs i)))) = φ (ys i)
      rw [φ.symm_apply_apply, he i]
  · rintro ⟨e, heS, heP, he⟩
    refine ⟨conjAut φ.symm e, strong_of_equiv K (conjAut φ.symm e) hM, ?_, fun i => ?_⟩
    · intro p hp
      change φ.symm (e (φ p)) = p
      exact φ.symm_apply_eq.mpr (heP (φ p) ⟨p, hp, rfl⟩)
    · change φ.symm (e (φ (xs i))) = ys i
      exact φ.symm_apply_eq.mpr (he i)

theorem joint_card {P ι : Type u} {χ : Cardinal.{u}} (hχinf : aleph0 ≤ χ)
    (hP : #P ≤ χ) (hι : #ι ≤ χ) : #(P ⊕ ι) ≤ χ := by
  rw [mk_sum, lift_id, lift_id]
  exact (add_le_add hP hι).trans (le_of_eq (add_eq_self hχinf))

/-- Equal joint soft canons ⇒ parameter-fixing strong automorphism (Theorem 3.5). -/
theorem same_joint_canon_fixes_params {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) (δ : _root_.Ordinal.{u}) (χ : Cardinal.{u})
    (hδ : Order.IsSuccLimit δ) (hχ : aleph0 ≤ χ) (hcf : χ < Ordinal.cof δ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    {P ι : Type u} (hP : #P ≤ χ) (hι : #ι ≤ χ)
    (p : P → (E.obj I).carrier)
    (xs ys : ι → (E.obj I).carrier)
    (hcan : canonicalOfTuple E hχ (joint_card hχ hP hι) (Sum.elim p xs) =
        canonicalOfTuple E hχ (joint_card hχ hP hι) (Sum.elim p ys)) :
    SameOrbitOverParams K (E.obj I) (Set.range p) xs ys := by
  classical
  have hjoint : #(P ⊕ ι) ≤ χ := joint_card hχ hP hι
  obtain ⟨Φ, hΦS, hΦ⟩ :=
    same_canonical_sameAutOrbit E δ χ hδ hχ hcf eISO hjoint
      (Sum.elim p xs) (Sum.elim p ys) hcan
  refine ⟨Φ, hΦS, ?_, fun i => hΦ (Sum.inr i)⟩
  intro q hq
  obtain ⟨a, rfl⟩ := hq
  exact hΦ (Sum.inl a)

/-- Realized cuts of a well-ordered set. -/
def RealizedCut {α : Type u} [LinearOrder α] (S : Set α) : Type u :=
  {C : Set ↥S // ∃ x : α, C = {s : ↥S | (s : α) < x}}

theorem mk_realizedCut_le {α : Type u} [LinearOrder α] [WellFoundedLT α] (S : Set α) :
    #(RealizedCut S) ≤ #↥S + 1 := by
  classical
  letI : WellFoundedLT ↥S := inferInstance
  let f : RealizedCut S → Option ↥S := fun C =>
    let rest : Set ↥S := {s | s ∉ C.1}
    if h : rest.Nonempty then
      some (@WellFounded.min (↥S) (· < ·) wellFounded_lt rest h)
    else none
  have hinj : Function.Injective f := by
    intro C₁ C₂ hf
    apply Subtype.ext
    obtain ⟨x₁, hx₁⟩ := C₁.2
    obtain ⟨x₂, hx₂⟩ := C₂.2
    have princ (C : RealizedCut S) (x : α)
        (hx : C.1 = {s : ↥S | (s : α) < x}) :
        C.1 =
          let rest : Set ↥S := {s | s ∉ C.1}
          if h : rest.Nonempty then
            {s : ↥S | (s : α) <
              (@WellFounded.min (↥S) (· < ·) wellFounded_lt rest h : α)}
          else univ := by
      set rest : Set ↥S := {s | s ∉ C.1}
      by_cases h : rest.Nonempty
      · simp only [h, ↓reduceDIte]
        ext s
        have hall : ∀ t ∈ rest, x ≤ (t : α) := by
          intro t ht
          exact le_of_not_gt fun hlt =>
            (show t ∉ C.1 from ht) (by simpa [hx] using hlt)
        constructor
        · intro hs
          exact lt_of_lt_of_le (by simpa [hx] using hs)
            (hall _ (WellFounded.min_mem wellFounded_lt rest h))
        · intro hs
          by_contra hsC
          have hsRest : s ∈ rest := hsC
          exact (WellFounded.not_lt_min wellFounded_lt rest hsRest)
            (Subtype.coe_lt_coe.mp hs)
      · simp only [h, ↓reduceDIte]
        ext s; exact ⟨fun _ => trivial, fun _ => by
          by_contra hs; exact h ⟨s, hs⟩⟩
    have p1 := princ C₁ x₁ hx₁
    have p2 := princ C₂ x₂ hx₂
    dsimp [f] at hf
    set R₁ : Set ↥S := {s | s ∉ C₁.1}
    set R₂ : Set ↥S := {s | s ∉ C₂.1}
    by_cases h1 : R₁.Nonempty
    · by_cases h2 : R₂.Nonempty
      · simp only [h1, h2, ↓reduceDIte] at hf
        injection hf with hmin
        simp only [h1, ↓reduceDIte] at p1
        simp only [h2, ↓reduceDIte] at p2
        rw [p1, p2, hmin]
      · simp only [h1, h2, ↓reduceDIte] at hf; cases hf
    · by_cases h2 : R₂.Nonempty
      · simp only [h1, h2, ↓reduceDIte] at hf; cases hf
      · simp only [h1, ↓reduceDIte] at p1
        simp only [h2, ↓reduceDIte] at p2
        rw [p1, p2]
  exact (mk_le_of_injective hinj).trans (by rw [mk_option])

noncomputable def cutAt {α : Type u} [LinearOrder α] (S : Set α) (x : α) : RealizedCut S :=
  ⟨{s : ↥S | (s : α) < x}, ⟨x, rfl⟩⟩

/-- Inclusion order on realized cuts (initial segments). -/
instance {α : Type u} [LinearOrder α] {S : Set α} : PartialOrder (RealizedCut S) where
  le C D := C.1 ⊆ D.1
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ := Set.Subset.trans
  le_antisymm _ _ h h' := Subtype.ext (Set.Subset.antisymm h h')

lemma realizedCut_le_total {α : Type u} [LinearOrder α] {S : Set α}
    (C D : RealizedCut S) : C ≤ D ∨ D ≤ C := by
  obtain ⟨x, hx⟩ := C.2
  obtain ⟨y, hy⟩ := D.2
  rcases le_total x y with hxy | hyx
  · refine Or.inl ?_
    intro s hs
    have : (s : α) < x := by simpa [hx] using hs
    exact by simpa [hy] using lt_of_lt_of_le this hxy
  · refine Or.inr ?_
    intro s hs
    have : (s : α) < y := by simpa [hy] using hs
    exact by simpa [hx] using lt_of_lt_of_le this hyx

noncomputable instance {α : Type u} [LinearOrder α] {S : Set α} :
    LinearOrder (RealizedCut S) where
  le_total := realizedCut_le_total
  toDecidableLE := Classical.decRel _
  toDecidableEq := Classical.decEq _
  toDecidableLT := Classical.decRel _

/-- Soft rename key: realized cut + gap tag.
Gap `⊤` marks `T`-ordinals (above every finite gap index in the cut);
`↑n` marks the `n`-th non-`T` support ordinal in that cut. Lex order by cut inclusion
then `WithTop ℕ` preserves ordinal order on `T ∪ hSupport`. -/
abbrev SoftKey {α : Type u} [LinearOrder α] (T : Set α) : Type u :=
  RealizedCut T ×ₗ WithTop ℕ

/-- SoftKey lifted to match `OrdIndex : Type (u+1)` for `colexPush`. -/
abbrev SoftKeyU {α : Type u} [LinearOrder α] (T : Set α) : Type (u + 1) :=
  ULift.{u + 1} (SoftKey T)

noncomputable instance {α : Type u} [LinearOrder α] {T : Set α} :
    LinearOrder (SoftKeyU T) :=
  LinearOrder.lift' (ULift.down : SoftKeyU T → SoftKey T) ULift.down_injective

abbrev SoftPoint {α : Type u} [LinearOrder α] (T : Set α) : Type u :=
  (SoftKey T →₀ ℤ) →₀ ℚ

theorem mk_softKey_le {α : Type u} [LinearOrder α] [WellFoundedLT α]
    {χ : Cardinal.{u}} (T : Set α) (hT : #T ≤ χ) (hχ : aleph0 ≤ χ) :
    #(SoftKey T) ≤ χ := by
  have hcuts : #(RealizedCut T) ≤ χ :=
    (mk_realizedCut_le (S := T)).trans <|
      (add_le_add hT (one_le_aleph0.trans hχ)).trans (le_of_eq (add_eq_self hχ))
  have hN0 : #(WithTop ℕ) ≤ (ℵ₀ : Cardinal.{0}) := by
    change #(Option ℕ) ≤ ℵ₀
    rw [mk_option, mk_nat]
    exact le_of_eq (add_eq_left (le_rfl : (ℵ₀ : Cardinal.{0}) ≤ ℵ₀) one_le_aleph0)
  have hN : lift.{u} #(WithTop ℕ) ≤ (ℵ₀ : Cardinal.{u}) := by
    simpa [lift_aleph0] using (lift_le.mpr hN0)
  change #(RealizedCut T × WithTop ℕ) ≤ χ
  rw [mk_prod]
  simp only [lift_uzero]
  refine (mul_le_mul' (by simpa using hcuts) hN).trans ?_
  exact le_of_eq (Cardinal.mul_eq_left hχ hχ aleph0_ne_zero)

/-- Embed soft keys into `Below χ` for fingerprint packaging. -/
noncomputable def softKeyEmbed {χ : Cardinal.{u}} (hχ : aleph0 ≤ χ)
    {α : Type u} [LinearOrder α] [WellFoundedLT α] (T : Set α) (hT : #T ≤ χ) :
    SoftKey T ↪ Below χ :=
  embedBelow (mk_softKey_le T hT hχ)

theorem mk_softPoint_le {α : Type u} [LinearOrder α] [WellFoundedLT α]
    {χ : Cardinal.{u}} (T : Set α) (hT : #T ≤ χ) (hχ : aleph0 ≤ χ) :
    #(SoftPoint T) ≤ χ := by
  classical
  let e := softKeyEmbed hχ T hT
  have hinj : Function.Injective
      (fun p : SoftPoint T =>
        (p.mapDomain (Finsupp.mapDomain (α := SoftKey T) (β := Below χ) (M := ℤ) (⇑e)) :
          AbstractPoint χ)) := by
    intro p q hpq
    exact mapDomain_injective (mapDomain_injective e.injective) hpq
  exact (mk_le_of_injective hinj).trans (le_of_eq (mk_abstractPoint χ hχ))


noncomputable def cutOverWell {χ : Cardinal.{u}} (hχ : aleph0 ≤ χ)
    {α : Type u} [LinearOrder α] [WellFoundedLT α] (S : Set α) (hS : #S ≤ χ) (x : α) :
    Below χ := by
  classical
  have hS' : #↥S ≤ χ := hS
  have hcuts : #(RealizedCut S) ≤ χ :=
    (mk_realizedCut_le (S := S)).trans <|
      (add_le_add hS' (one_le_aleph0.trans hχ)).trans
        (le_of_eq (add_eq_self hχ))
  exact (embedBelow hcuts).1 (cutAt S x)

/-- Local index of a non-`T` ordinal among those of `y` in the same cut of `T` (0-based). -/
noncomputable def gapIndex {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ)
    (i : OrdIndex δ) : ℕ := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  exact ((hSupport y).filter fun j =>
      Ordinal.ToType.mk (asIio j) ∉ T ∧
      cutAt T (Ordinal.ToType.mk (asIio j)) = cutAt T (Ordinal.ToType.mk (asIio i)) ∧
        j < i).card

/-- Gap tag: `⊤` on `T`, else `↑(gapIndex)`. -/
noncomputable def softGap {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ)
    (i : OrdIndex δ) : WithTop ℕ := by
  classical
  exact if Ordinal.ToType.mk (asIio i) ∈ T then ⊤ else (gapIndex T y i : WithTop ℕ)

/-- Ordered soft key of an ordinal relative to `T` and the support of `y`. -/
noncomputable def softKeyOf {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ)
    (i : OrdIndex δ) : SoftKey T := by
  classical
  letI : LinearOrder δ.ToType := inferInstance
  exact toLex (cutAt T (Ordinal.ToType.mk (asIio i)), softGap T y i)

/-- Soft rename into `Below χ` (order-destroying packaging of `softKeyOf`). -/
noncomputable def softRename {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) (y : HOrder δ)
    (i : OrdIndex δ) : Below χ := by
  classical
  letI : LinearOrder δ.ToType := inferInstance
  letI : WellFoundedLT δ.ToType := inferInstance
  exact softKeyEmbed hχ T hT (softKeyOf T y i)

/-- Soft point before embedding: colex keys ordered by cut inclusion then gap. -/
noncomputable def abstractifySoft {δ : _root_.Ordinal.{u}} (T : Set δ.ToType)
    (y : HOrder δ) : SoftPoint T := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  letI : DecidableEq (SoftKey T) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  let rename : OrdIndex δ → SoftKey T := softKeyOf T y
  let pushG : Gamma δ → (SoftKey T →₀ ℤ) := fun g => (ofColex g).mapDomain rename
  exact (ofColex y).mapDomain pushG

/-- Push an `H(δ)` point to an `AbstractPoint` by SoftKey rename then embedding into `Below χ`. -/
noncomputable def abstractify {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) (y : HOrder δ) :
    AbstractPoint χ := by
  classical
  letI : DecidableEq (SoftKey T) := Classical.decEq _
  letI : DecidableEq (Below χ) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  letI : WellFoundedLT δ.ToType := inferInstance
  let e := softKeyEmbed hχ T hT
  exact (abstractifySoft T y).mapDomain (Finsupp.mapDomain (⇑e))

theorem cutAt_injOn_T {α : Type u} [LinearOrder α] (T : Set α) :
    Set.InjOn (cutAt T) T := by
  classical
  intro x hx y hy hxy
  by_contra hne
  rcases lt_trichotomy x y with hlt | heq | hgt
  · have mem : (⟨x, hx⟩ : ↥T) ∈ (cutAt T y).1 := hlt
    have nmem : (⟨x, hx⟩ : ↥T) ∉ (cutAt T x).1 := lt_irrefl (x : α)
    have hsets : (cutAt T x).1 = (cutAt T y).1 := congrArg Subtype.val hxy
    exact nmem (hsets ▸ mem)
  · exact hne heq
  · have mem : (⟨y, hy⟩ : ↥T) ∈ (cutAt T x).1 := hgt
    have nmem : (⟨y, hy⟩ : ↥T) ∉ (cutAt T y).1 := lt_irrefl (y : α)
    have hsets : (cutAt T x).1 = (cutAt T y).1 := congrArg Subtype.val hxy
    exact nmem (hsets.symm ▸ mem)

theorem cutOverWell_injOn_T {χ : Cardinal.{u}} (hχ : aleph0 ≤ χ)
    {α : Type u} [LinearOrder α] [WellFoundedLT α] (T : Set α) (hT : #T ≤ χ) :
    Set.InjOn (cutOverWell (α := α) hχ T hT) T := by
  classical
  intro x hx y hy hxy
  have hcuts : #(RealizedCut T) ≤ χ :=
    (mk_realizedCut_le (S := T)).trans <|
      (add_le_add hT (one_le_aleph0.trans hχ)).trans (le_of_eq (add_eq_self hχ))
  have hcut : cutAt T x = cutAt T y := by
    refine (embedBelow hcuts).injective ?_
    change (embedBelow hcuts) (cutAt T x) = (embedBelow hcuts) (cutAt T y)
    simpa [cutOverWell] using hxy
  exact cutAt_injOn_T T hx hy hcut

theorem softGap_of_mem_T {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ)
    {i : OrdIndex δ} (hi : Ordinal.ToType.mk (asIio i) ∈ T) :
    softGap T y i = ⊤ := by
  classical
  simp [softGap, hi]

theorem softGap_of_not_mem_T {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ)
    {i : OrdIndex δ} (hi : Ordinal.ToType.mk (asIio i) ∉ T) :
    softGap T y i = (gapIndex T y i : WithTop ℕ) := by
  classical
  simp [softGap, hi]

theorem softKeyOf_eq_iff {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ)
    {i j : OrdIndex δ} :
    softKeyOf T y i = softKeyOf T y j ↔
      cutAt T (Ordinal.ToType.mk (asIio i)) = cutAt T (Ordinal.ToType.mk (asIio j)) ∧
        softGap T y i = softGap T y j := by
  classical
  letI : LinearOrder δ.ToType := inferInstance
  constructor
  · intro h
    have h' : ofLex (softKeyOf T y i) = ofLex (softKeyOf T y j) := congrArg ofLex h
    exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
  · intro ⟨hcut, hgap⟩
    exact congrArg toLex (Prod.ext hcut hgap)

theorem softRename_eq_iff {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) (y : HOrder δ)
    {i j : OrdIndex δ} :
    softRename hχ T hT y i = softRename hχ T hT y j ↔
      softKeyOf T y i = softKeyOf T y j := by
  classical
  letI : LinearOrder δ.ToType := inferInstance
  letI : WellFoundedLT δ.ToType := inferInstance
  constructor
  · intro h
    exact (softKeyEmbed hχ T hT).injective (by simpa [softRename] using h)
  · intro h
    simpa [softRename] using congrArg (softKeyEmbed hχ T hT) h

theorem softKeyOf_of_mem_T {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ)
    {i : OrdIndex δ} (hi : Ordinal.ToType.mk (asIio i) ∈ T) :
    softKeyOf T y i = toLex (cutAt T (Ordinal.ToType.mk (asIio i)), ⊤) := by
  classical
  letI : LinearOrder δ.ToType := inferInstance
  simp [softKeyOf, softGap, hi]

theorem softRename_of_mem_T {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) (y : HOrder δ)
    {i : OrdIndex δ} (hi : Ordinal.ToType.mk (asIio i) ∈ T) :
    softRename hχ T hT y i =
      softKeyEmbed hχ T hT (toLex (cutAt T (Ordinal.ToType.mk (asIio i)), ⊤)) := by
  classical
  letI : LinearOrder δ.ToType := inferInstance
  letI : WellFoundedLT δ.ToType := inferInstance
  simp [softRename, softKeyOf_of_mem_T T y hi]

theorem softKeyOf_eq_on_mem_T {δ : _root_.Ordinal.{u}} (T : Set δ.ToType)
    (y₁ y₂ : HOrder δ) {i : OrdIndex δ}
    (hi : Ordinal.ToType.mk (asIio i) ∈ T) :
    softKeyOf T y₁ i = softKeyOf T y₂ i := by
  rw [softKeyOf_of_mem_T T y₁ hi, softKeyOf_of_mem_T T y₂ hi]

theorem softRename_eq_on_mem_T {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ)
    (y₁ y₂ : HOrder δ) {i : OrdIndex δ}
    (hi : Ordinal.ToType.mk (asIio i) ∈ T) :
    softRename hχ T hT y₁ i = softRename hχ T hT y₂ i := by
  rw [softRename_of_mem_T hχ T hT y₁ hi, softRename_of_mem_T hχ T hT y₂ hi]

theorem softKeyOf_injOn_hSupport {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ) :
    Set.InjOn (softKeyOf T y) (hSupport y) := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  letI : DecidablePred (· ∈ T) := Classical.decPred _
  intro i hi j hj hij
  obtain ⟨hcut, hgap⟩ := (softKeyOf_eq_iff T y).mp hij
  by_cases hiT : Ordinal.ToType.mk (asIio i) ∈ T
  · by_cases hjT : Ordinal.ToType.mk (asIio j) ∈ T
    · have heq :
          Ordinal.ToType.mk (asIio i) = Ordinal.ToType.mk (asIio j) :=
        cutAt_injOn_T T hiT hjT hcut
      have : asIio i = asIio j := (Ordinal.ToType.mk (o := δ)).injective heq
      exact Subtype.ext (congrArg Subtype.val this)
    · have htop : (⊤ : WithTop ℕ) = (gapIndex T y j : WithTop ℕ) := by
        rw [softGap_of_mem_T T y hiT, softGap_of_not_mem_T T y hjT] at hgap
        exact hgap
      exact False.elim ((Option.some_ne_none (gapIndex T y j)).symm htop)
  · by_cases hjT : Ordinal.ToType.mk (asIio j) ∈ T
    · have htop : (gapIndex T y i : WithTop ℕ) = ⊤ := by
        rw [softGap_of_not_mem_T T y hiT, softGap_of_mem_T T y hjT] at hgap
        exact hgap
      exact False.elim (Option.some_ne_none (gapIndex T y i) htop)
    · have hgap' : gapIndex T y i = gapIndex T y j := by
        have := hgap
        rw [softGap_of_not_mem_T T y hiT, softGap_of_not_mem_T T y hjT] at this
        exact WithTop.coe_injective this
      by_contra hne
      rcases lt_trichotomy i j with hlt | heq | hgt
      · let Fi := (hSupport y).filter fun k =>
          Ordinal.ToType.mk (asIio k) ∉ T ∧
            cutAt T (Ordinal.ToType.mk (asIio k)) =
                cutAt T (Ordinal.ToType.mk (asIio i)) ∧
              k < i
        let Fj := (hSupport y).filter fun k =>
          Ordinal.ToType.mk (asIio k) ∉ T ∧
            cutAt T (Ordinal.ToType.mk (asIio k)) =
                cutAt T (Ordinal.ToType.mk (asIio j)) ∧
              k < j
        have hsub : Fi ⊂ Fj := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro k hk
            obtain ⟨hkY, hkT, hkCr⟩ := Finset.mem_filter.mp hk
            obtain ⟨hkC, hklt⟩ := hkCr
            exact Finset.mem_filter.mpr ⟨hkY, hkT, hcut ▸ hkC, hklt.trans hlt⟩
          · intro hEq
            have himem : i ∈ Fj :=
              Finset.mem_filter.mpr ⟨hi, hiT, hcut, hlt⟩
            have : i ∈ Fi := by simpa [hEq] using himem
            obtain ⟨_, _, _, hlt'⟩ := Finset.mem_filter.mp this
            exact lt_irrefl i hlt'
        have : gapIndex T y i < gapIndex T y j := by
          change Fi.card < Fj.card
          have hi' : gapIndex T y i = Fi.card := by simp [gapIndex, Fi]
          have hj' : gapIndex T y j = Fj.card := by simp [gapIndex, Fj]
          simpa [hi', hj'] using Finset.card_lt_card hsub
        exact absurd this (by simp [hgap'])
      · exact hne heq
      · let Fi := (hSupport y).filter fun k =>
          Ordinal.ToType.mk (asIio k) ∉ T ∧
            cutAt T (Ordinal.ToType.mk (asIio k)) =
                cutAt T (Ordinal.ToType.mk (asIio i)) ∧
              k < i
        let Fj := (hSupport y).filter fun k =>
          Ordinal.ToType.mk (asIio k) ∉ T ∧
            cutAt T (Ordinal.ToType.mk (asIio k)) =
                cutAt T (Ordinal.ToType.mk (asIio j)) ∧
              k < j
        have hsub : Fj ⊂ Fi := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
          · intro k hk
            obtain ⟨hkY, hkT, hkCr⟩ := Finset.mem_filter.mp hk
            obtain ⟨hkC, hklt⟩ := hkCr
            exact Finset.mem_filter.mpr ⟨hkY, hkT, hcut.symm ▸ hkC, hklt.trans hgt⟩
          · intro hEq
            have hjmem : j ∈ Fi :=
              Finset.mem_filter.mpr ⟨hj, hjT, hcut.symm, hgt⟩
            have : j ∈ Fj := by simpa [← hEq] using hjmem
            obtain ⟨_, _, _, hlt'⟩ := Finset.mem_filter.mp this
            exact lt_irrefl j hlt'
        have : gapIndex T y j < gapIndex T y i := by
          change Fj.card < Fi.card
          have hi' : gapIndex T y i = Fi.card := by simp [gapIndex, Fi]
          have hj' : gapIndex T y j = Fj.card := by simp [gapIndex, Fj]
          simpa [hi', hj'] using Finset.card_lt_card hsub
        exact absurd this (by simp [hgap'])

theorem softRename_injOn_hSupport {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) (y : HOrder δ) :
    Set.InjOn (softRename hχ T hT y) (hSupport y) := by
  intro i hi j hj hij
  exact softKeyOf_injOn_hSupport T y hi hj ((softRename_eq_iff hχ T hT y).mp hij)

theorem softKeyOf_injOn_T {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ) :
    Set.InjOn (softKeyOf T y)
      {i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} := by
  classical
  intro i hi j hj hij
  obtain ⟨hcut, _⟩ := (softKeyOf_eq_iff T y).mp hij
  have heq :
      Ordinal.ToType.mk (asIio i) = Ordinal.ToType.mk (asIio j) :=
    cutAt_injOn_T T hi hj hcut
  have : asIio i = asIio j := (Ordinal.ToType.mk (o := δ)).injective heq
  exact Subtype.ext (congrArg Subtype.val this)

theorem softRename_injOn_T {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) (y : HOrder δ) :
    Set.InjOn (softRename hχ T hT y)
      {i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} := by
  intro i hi j hj hij
  exact softKeyOf_injOn_T T y hi hj ((softRename_eq_iff hχ T hT y).mp hij)

theorem softKeyOf_injOn_T_union_hSupport {δ : _root_.Ordinal.{u}}
    (T : Set δ.ToType) (y : HOrder δ) :
    Set.InjOn (softKeyOf T y)
      ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport y)) := by
  classical
  letI : DecidablePred (· ∈ T) := Classical.decPred _
  intro i hi j hj hij
  have hi' : Ordinal.ToType.mk (asIio i) ∈ T ∨ i ∈ hSupport y := by
    simpa [Set.mem_union] using hi
  have hj' : Ordinal.ToType.mk (asIio j) ∈ T ∨ j ∈ hSupport y := by
    simpa [Set.mem_union] using hj
  obtain ⟨hcut, hgap⟩ := (softKeyOf_eq_iff T y).mp hij
  by_cases hiT : Ordinal.ToType.mk (asIio i) ∈ T
  · by_cases hjT : Ordinal.ToType.mk (asIio j) ∈ T
    · exact softKeyOf_injOn_T T y hiT hjT hij
    · have htop : (⊤ : WithTop ℕ) = (gapIndex T y j : WithTop ℕ) := by
        rw [softGap_of_mem_T T y hiT, softGap_of_not_mem_T T y hjT] at hgap
        exact hgap
      exact False.elim ((Option.some_ne_none (gapIndex T y j)).symm htop)
  · have hiY : i ∈ hSupport y := by
      cases hi' with
      | inl h => exact (hiT h).elim
      | inr h => exact h
    by_cases hjT : Ordinal.ToType.mk (asIio j) ∈ T
    · have htop : (gapIndex T y i : WithTop ℕ) = ⊤ := by
        rw [softGap_of_not_mem_T T y hiT, softGap_of_mem_T T y hjT] at hgap
        exact hgap
      exact False.elim (Option.some_ne_none (gapIndex T y i) htop)
    · have hjY : j ∈ hSupport y := by
        cases hj' with
        | inl h => exact (hjT h).elim
        | inr h => exact h
      exact softKeyOf_injOn_hSupport T y hiY hjY hij

theorem softRename_injOn_T_union_hSupport {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) (y : HOrder δ) :
    Set.InjOn (softRename hχ T hT y)
      ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport y)) := by
  intro i hi j hj hij
  exact softKeyOf_injOn_T_union_hSupport T y hi hj
    ((softRename_eq_iff hχ T hT y).mp hij)

theorem support_subset_hSupport {δ : _root_.Ordinal.{u}} (y : HOrder δ)
    {g : Gamma δ} (hg : g ∈ (ofColex y).support) :
    (ofColex g).support ⊆ hSupport y := by
  intro i hi
  simp only [hSupport, Finset.mem_biUnion]
  exact ⟨g, hg, hi⟩

theorem cutAt_mono {α : Type u} [LinearOrder α] (S : Set α) {x y : α}
    (h : x ≤ y) : cutAt S x ≤ cutAt S y := by
  intro s hs
  have : (s : α) < x := by simpa [cutAt] using hs
  exact by simpa [cutAt] using lt_of_lt_of_le this h

theorem softKeyOf_strictMonoOn {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ) :
    StrictMonoOn (softKeyOf T y)
      ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport y)) := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  letI : DecidablePred (· ∈ T) := Classical.decPred _
  intro i hi j hj hij
  have hii : asIio i < asIio j := by
    simpa [asIio] using Subtype.coe_lt_coe.mp hij
  have hmk : Ordinal.ToType.mk (asIio i) < Ordinal.ToType.mk (asIio j) :=
    (Ordinal.ToType.mk (o := δ)).strictMono hii
  have hcut_le :
      cutAt T (Ordinal.ToType.mk (asIio i)) ≤ cutAt T (Ordinal.ToType.mk (asIio j)) :=
    cutAt_mono T hmk.le
  by_cases hcut_lt :
      cutAt T (Ordinal.ToType.mk (asIio i)) < cutAt T (Ordinal.ToType.mk (asIio j))
  · refine (Prod.Lex.toLex_lt_toLex
        (x := (cutAt T (Ordinal.ToType.mk (asIio i)), softGap T y i))
        (y := (cutAt T (Ordinal.ToType.mk (asIio j)), softGap T y j))).2 ?_
    exact Or.inl hcut_lt
  · have hcut_eq :
        cutAt T (Ordinal.ToType.mk (asIio i)) = cutAt T (Ordinal.ToType.mk (asIio j)) :=
      le_antisymm hcut_le (le_of_not_gt hcut_lt)
    have hgap_lt : softGap T y i < softGap T y j := by
      by_cases hiT : Ordinal.ToType.mk (asIio i) ∈ T
      · by_cases hjT : Ordinal.ToType.mk (asIio j) ∈ T
        · have : Ordinal.ToType.mk (asIio i) = Ordinal.ToType.mk (asIio j) :=
            cutAt_injOn_T T hiT hjT hcut_eq
          have : asIio i = asIio j := (Ordinal.ToType.mk (o := δ)).injective this
          have : i = j := Subtype.ext (congrArg Subtype.val this)
          exact (hij.ne this).elim
        · -- i ∈ T, j ∉ T, same cut, i < j ⇒ ⟨i⟩ ∈ cutAt j, contradiction
          have mem : (⟨Ordinal.ToType.mk (asIio i), hiT⟩ : ↥T) ∈
              (cutAt T (Ordinal.ToType.mk (asIio j))).1 := hmk
          have nmem : (⟨Ordinal.ToType.mk (asIio i), hiT⟩ : ↥T) ∉
              (cutAt T (Ordinal.ToType.mk (asIio i))).1 := by
            simp [cutAt]
          have : (cutAt T (Ordinal.ToType.mk (asIio i))).1 =
              (cutAt T (Ordinal.ToType.mk (asIio j))).1 := congrArg Subtype.val hcut_eq
          exact (nmem (this ▸ mem)).elim
      · have hiY : i ∈ hSupport y := by
          have : Ordinal.ToType.mk (asIio i) ∈ T ∨ i ∈ hSupport y := by
            simpa [Set.mem_union] using hi
          cases this with
          | inl h => exact (hiT h).elim
          | inr h => exact h
        by_cases hjT : Ordinal.ToType.mk (asIio j) ∈ T
        · -- gap before T in same cut
          rw [softGap_of_not_mem_T T y hiT, softGap_of_mem_T T y hjT]
          exact WithTop.coe_lt_top _
        · have hjY : j ∈ hSupport y := by
            have : Ordinal.ToType.mk (asIio j) ∈ T ∨ j ∈ hSupport y := by
              simpa [Set.mem_union] using hj
            cases this with
            | inl h => exact (hjT h).elim
            | inr h => exact h
          rw [softGap_of_not_mem_T T y hiT, softGap_of_not_mem_T T y hjT]
          refine (WithTop.coe_lt_coe).mpr ?_
          let Fi := (hSupport y).filter fun k =>
            Ordinal.ToType.mk (asIio k) ∉ T ∧
              cutAt T (Ordinal.ToType.mk (asIio k)) =
                  cutAt T (Ordinal.ToType.mk (asIio i)) ∧
                k < i
          let Fj := (hSupport y).filter fun k =>
            Ordinal.ToType.mk (asIio k) ∉ T ∧
              cutAt T (Ordinal.ToType.mk (asIio k)) =
                  cutAt T (Ordinal.ToType.mk (asIio j)) ∧
                k < j
          have hsub : Fi ⊂ Fj := by
            refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
            · intro k hk
              obtain ⟨hkY, hkT, hkCr⟩ := Finset.mem_filter.mp hk
              obtain ⟨hkC, hklt⟩ := hkCr
              exact Finset.mem_filter.mpr ⟨hkY, hkT, hcut_eq ▸ hkC, hklt.trans hij⟩
            · intro hEq
              have himem : i ∈ Fj :=
                Finset.mem_filter.mpr ⟨hiY, hiT, hcut_eq, hij⟩
              have : i ∈ Fi := by simpa [hEq] using himem
              obtain ⟨_, _, _, hlt'⟩ := Finset.mem_filter.mp this
              exact lt_irrefl i hlt'
          change Fi.card < Fj.card
          have hi' : gapIndex T y i = Fi.card := by simp [gapIndex, Fi]
          have hj' : gapIndex T y j = Fj.card := by simp [gapIndex, Fj]
          simpa [hi', hj'] using Finset.card_lt_card hsub
    refine (Prod.Lex.toLex_lt_toLex
        (x := (cutAt T (Ordinal.ToType.mk (asIio i)), softGap T y i))
        (y := (cutAt T (Ordinal.ToType.mk (asIio j)), softGap T y j))).2 ?_
    exact Or.inr ⟨hcut_eq, hgap_lt⟩

/-- Soft-point form of `abstractify` (before `Below χ` packaging). -/
theorem abstractifySoft_eq_of_abstractify {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) {x y : HOrder δ}
    (hxy : abstractify hχ T hT x = abstractify hχ T hT y) :
    abstractifySoft T x = abstractifySoft T y := by
  classical
  letI : LinearOrder δ.ToType := inferInstance
  letI : WellFoundedLT δ.ToType := inferInstance
  let e := softKeyEmbed hχ T hT
  have hinj : Function.Injective
      (fun p : SoftPoint T =>
        p.mapDomain (Finsupp.mapDomain (α := SoftKey T) (β := Below χ) (M := ℤ) (⇑e))) := by
    intro p q hpq
    exact mapDomain_injective (mapDomain_injective e.injective) hpq
  exact hinj hxy

/-- `mapDomain` along soft rename recovers a `T`-supported `Γ` coefficient from soft codes. -/
theorem abstractifySoft_apply_T_gamma {δ : _root_.Ordinal.{u}} (T : Set δ.ToType)
    (x : HOrder δ)
    (g : Gamma δ) (hg : ∀ i ∈ (ofColex g).support, Ordinal.ToType.mk (asIio i) ∈ T) :
    abstractifySoft T x ((ofColex g).mapDomain (softKeyOf T x)) = (ofColex x) g := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  letI : DecidableEq (SoftKey T) := Classical.decEq _
  letI : DecidableEq (Gamma δ) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  let S : Set (OrdIndex δ) :=
    {i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport x)
  let rename := softKeyOf T x
  let pushG : Gamma δ → (SoftKey T →₀ ℤ) := fun g' => (ofColex g').mapDomain rename
  let U : Set (Gamma δ) := {g' | ((ofColex g').support : Set (OrdIndex δ)) ⊆ S}
  have hinjRename : Set.InjOn rename S := softKeyOf_injOn_T_union_hSupport T x
  have hinjPush : Set.InjOn pushG U := by
    intro g₁ hg₁ g₂ hg₂ heq
    exact ofColex.injective (mapDomain_injOn (S := S) hinjRename hg₁ hg₂ heq)
  have hxU : ((ofColex x).support : Set (Gamma δ)) ⊆ U := by
    intro g' hg'
    intro i hi
    exact Or.inr (support_subset_hSupport x hg' hi)
  have hgU : g ∈ U := by
    intro i hi
    exact Or.inl (hg i hi)
  change ((ofColex x).mapDomain pushG) (pushG g) = (ofColex x) g
  exact mapDomain_apply' (S := U) (f := pushG) (ofColex x) hxU hinjPush hgU

theorem abstractify_apply_T_gamma {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) (x : HOrder δ)
    (g : Gamma δ) (hg : ∀ i ∈ (ofColex g).support, Ordinal.ToType.mk (asIio i) ∈ T) :
    abstractify hχ T hT x ((ofColex g).mapDomain (softRename hχ T hT x)) =
      (ofColex x) g := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  letI : DecidableEq (SoftKey T) := Classical.decEq _
  letI : DecidableEq (Below χ) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  letI : WellFoundedLT δ.ToType := inferInstance
  let e := softKeyEmbed hχ T hT
  have hinj_e : Function.Injective
      (Finsupp.mapDomain (α := SoftKey T) (β := Below χ) (M := ℤ) (⇑e)) :=
    mapDomain_injective e.injective
  have hren :
      (ofColex g).mapDomain (softRename hχ T hT x) =
        ((ofColex g).mapDomain (softKeyOf T x)).mapDomain (⇑e) := by
    have hfun : softRename hχ T hT x = (⇑e ∘ softKeyOf T x) := by
      funext i; rfl
    rw [hfun, mapDomain_comp]
  have hsoft := abstractifySoft_apply_T_gamma T x g hg
  calc
    abstractify hχ T hT x ((ofColex g).mapDomain (softRename hχ T hT x))
        = abstractify hχ T hT x
            (((ofColex g).mapDomain (softKeyOf T x)).mapDomain (⇑e)) := by rw [hren]
    _ = abstractifySoft T x ((ofColex g).mapDomain (softKeyOf T x)) := by
        change ((abstractifySoft T x).mapDomain
            (Finsupp.mapDomain (α := SoftKey T) (β := Below χ) (M := ℤ) (⇑e)))
          (((ofColex g).mapDomain (softKeyOf T x)).mapDomain (⇑e)) =
          abstractifySoft T x ((ofColex g).mapDomain (softKeyOf T x))
        exact mapDomain_apply_of_injective (M := ℚ) hinj_e _ _
    _ = (ofColex x) g := hsoft

/-- Equal soft codes agree on every `T`-supported `Γ`-coefficient. -/
theorem abstractify_coeff_eq_of_T_support {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) (x y : HOrder δ)
    (hxy : abstractify hχ T hT x = abstractify hχ T hT y)
    (g : Gamma δ) (hg : ∀ i ∈ (ofColex g).support, Ordinal.ToType.mk (asIio i) ∈ T) :
    (ofColex x) g = (ofColex y) g := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  have hren : ∀ i ∈ (ofColex g).support,
      softRename hχ T hT x i = softRename hχ T hT y i := by
    intro i hi
    exact softRename_eq_on_mem_T hχ T hT x y (hg i hi)
  have hpush :
      (ofColex g).mapDomain (softRename hχ T hT x) =
        (ofColex g).mapDomain (softRename hχ T hT y) :=
    mapDomain_congr hren
  have hx := abstractify_apply_T_gamma hχ T hT x g hg
  have hy := abstractify_apply_T_gamma hχ T hT y g hg
  calc
    (ofColex x) g = abstractify hχ T hT x ((ofColex g).mapDomain (softRename hχ T hT x)) := hx.symm
    _ = abstractify hχ T hT y ((ofColex g).mapDomain (softRename hχ T hT x)) := by rw [hxy]
    _ = abstractify hχ T hT y ((ofColex g).mapDomain (softRename hχ T hT y)) := by rw [hpush]
    _ = (ofColex y) g := hy

/-- Soft support of a set of EM-model elements. -/
noncomputable def paramSoftSupport {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] (P : Set (E.obj I).carrier) : Set I :=
  ⋃ x ∈ P, Set.range (supportTermOf E x).pos

theorem paramSoftSupport_card {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] {χ : Cardinal.{u}} (hχ : aleph0 ≤ χ)
    (P : Set (E.obj I).carrier) (hP : #P ≤ χ) :
    #(paramSoftSupport E P) ≤ χ := by
  have hfin (x : (E.obj I).carrier) :
      #(Set.range (supportTermOf E x).pos) ≤ (ℵ₀ : Cardinal.{u}) := by
    have h := mk_range_le_lift (f := (supportTermOf E x).pos)
    rw [lift_uzero] at h
    refine h.trans ?_
    rw [mk_fin, lift_natCast]
    exact (natCast_lt_aleph0 (n := _)).le
  dsimp [paramSoftSupport]
  refine (mk_biUnion_le _ _).trans ?_
  have hsup : (⨆ x : ↥P, #(Set.range (supportTermOf E (x : (E.obj I).carrier)).pos)) ≤
      (ℵ₀ : Cardinal.{u}) :=
    ciSup_le' fun x => hfin _
  exact (mul_le_mul' hP hsup).trans (le_of_eq (Cardinal.mul_eq_left hχ hχ aleph0_ne_zero))

/-- Encode occupancy of a short sequence into a Bool table on `Below σ`. -/
noncomputable def occTable {σ : Cardinal.{u}} {ι : Type u} (hι : #ι ≤ σ)
    {α : Type u} [LinearOrder α] (xs : ι → α) :
    Set (Below σ) → Set (Below σ) → Bool := by
  classical
  let e := embedBelow hι
  exact fun L U =>
    decide (Occupied
      (xs '' ((↑) '' (e ⁻¹' L)))
      (xs '' ((↑) '' (e ⁻¹' U))))

/-- Occupancy of a new-slot cut `(L,U)` relative to ambient support `S` and placement `place`. -/
noncomputable def relOccOf {σ : Cardinal.{u}} {α : Type u} [LinearOrder α]
    {slt : Type u} (S : Set α) (place : slt → α)
    (coe : slt → Below σ) (L U : Set (Below σ)) : Bool := by
  classical
  let LN : Set slt := {z | coe z ∈ L}
  let UN : Set slt := {z | coe z ∈ U}
  let SL : Set α := {x | x ∈ S ∧ ∀ z ∈ LN ∪ UN, x < place z}
  let SU : Set α := {x | x ∈ S ∧ ∀ z ∈ LN ∪ UN, place z < x}
  exact decide (Occupied (SL ∪ place '' LN) (SU ∪ place '' UN))

/-- Soft-place fingerprint of a short tuple over fixed parameter support.
Uses the full flattened support slots of `xs` (via `canonicalPlaceOfTuple`), not only leading
positions, so `soft`/`eqOld`/`occ` track the joint soft presentation relative to `S`,`T`. -/
noncomputable def relFingerprintOf {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {δ : _root_.Ordinal.{u}} {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hσ : aleph0 ≤ σ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (T : Set δ.ToType) (hT : #T ≤ χ)
    (S : Set I) (hS : #S ≤ χ)
    {ι : Type u} (hι : #ι ≤ σ) (xs : ι → (E.obj I).carrier) :
    RelFingerprint E.lab E.arity σ χ := by
  classical
  let eS := embedBelow hS
  let r := canonicalOfTuple E hσ hι xs
  let place := canonicalPlaceOfTuple E hσ hι xs
  exact {
    newCanon := r
    soft := fun b =>
      if hb : b ∈ r.slt then
        abstractify hχ T hT (eISO.symm (place ⟨b, hb⟩))
      else 0
    eqOld := fun b =>
      if hb : b ∈ r.slt then
        let pl := place ⟨b, hb⟩
        if hmem : pl ∈ S then some (eS ⟨pl, hmem⟩) else none
      else none
    occ := relOccOf (σ := σ) S place Subtype.val
  }

/-- Joint orbit record from fixed parameters + relative fingerprint.
Index/slot universes are `P ⊕ newCanon.idx` and `param.slot ⊕ newCanon.slt`, so they depend
only on `p` and `fp` (equal fingerprints ⇒ identical types for `toCanonical`). -/
noncomputable def relJointOrbitRecordOf {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ)
    {I : Type u} [LinearOrder I] [Nonempty I]
    {P : Type u} (hP : #P ≤ χ)
    (p : P → (E.obj I).carrier) (fp : RelFingerprint E.lab E.arity σ χ) :
    OrbitRecord E.lab E.arity := by
  classical
  let paramRec := orbitRecordOfTuple E p
  let newRec := CanonicalRecord.toOrbitRecord fp.newCanon
  exact {
    index := P ⊕ newRec.index
    slot := paramRec.slot ⊕ newRec.slot
    label := Sum.elim paramRec.label newRec.label
    arg := fun
      | Sum.inl a, k => Sum.inl (paramRec.arg a k)
      | Sum.inr j, k => Sum.inr (newRec.arg j k)
    lt := fun
      | Sum.inl a, Sum.inl b => paramRec.lt a b
      | Sum.inr a, Sum.inr b => newRec.lt a b
      -- Param slots before new slots; refinements via soft/eqOld live in the realizes bridge.
      | Sum.inl _, Sum.inr _ => True
      | Sum.inr _, Sum.inl _ => False
    arg_strict := fun i a b hab => by
      cases i with
      | inl a' => exact paramRec.arg_strict a' hab
      | inr j => exact newRec.arg_strict j hab
    arg_surj := fun x => by
      cases x with
      | inl s =>
          obtain ⟨i, a, ha⟩ := paramRec.arg_surj s
          exact ⟨Sum.inl i, a, congrArg Sum.inl ha⟩
      | inr s =>
          obtain ⟨j, a, ha⟩ := newRec.arg_surj s
          exact ⟨Sum.inr j, a, congrArg Sum.inr ha⟩
    occupied := fun L U =>
      let Ln : Set (Below σ) := Subtype.val '' {z : newRec.slot | Sum.inr z ∈ L}
      let Un : Set (Below σ) := Subtype.val '' {z : newRec.slot | Sum.inr z ∈ U}
      fp.occ Ln Un = true
  }

/-- Joint soft `CanonicalRecord` determined by fixed parameters + relative fingerprint. -/
noncomputable def relJointCanonOf {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ)
    (hσle : σ ≤ χ)
    {I : Type u} [LinearOrder I] [Nonempty I]
    {P : Type u} (hP : #P ≤ χ)
    (p : P → (E.obj I).carrier) (fp : RelFingerprint E.lab E.arity σ χ) :
    CanonicalRecord E.lab E.arity χ := by
  classical
  let rec0 := relJointOrbitRecordOf E hχ hP p fp
  have hidx : #rec0.index ≤ χ := by
    change #(P ⊕ ↥(fp.newCanon.idx)) ≤ χ
    have hnew : #(↥(fp.newCanon.idx)) ≤ σ := canonical_record_card_index fp.newCanon
    exact joint_card hχ hP (hnew.trans hσle)
  have hslt : #rec0.slot ≤ χ := by
    change #((orbitRecordOfTuple E p).slot ⊕ ↥(fp.newCanon.slt)) ≤ χ
    have hp := orbitRecordOfTuple_slot_card E hχ hP p
    have hn : #(↥(fp.newCanon.slt)) ≤ σ := canonical_record_card_slot fp.newCanon
    rw [mk_sum, lift_id, lift_id]
    exact (add_le_add hp (hn.trans hσle)).trans (le_of_eq (add_eq_self hχ))
  exact rec0.toCanonical hidx hslt

/-- Relative code of a `σ`-tuple over fixed parameters in a soft copy.
`jointCanon` is the fingerprint-determined joint soft canon. -/
noncomputable def relCodeOf {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {δ : _root_.Ordinal.{u}} {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hσ : aleph0 ≤ σ)
    (hσle : σ ≤ χ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (T : Set δ.ToType) (hT : #T ≤ χ)
    (S : Set I) (hS : #S ≤ χ)
    {P ι : Type u} (hP : #P ≤ χ) (hι : #ι ≤ σ) (hιχ : #ι ≤ χ)
    (p : P → (E.obj I).carrier) (xs : ι → (E.obj I).carrier) :
    RelCode E.lab E.arity σ χ where
  fingerprint := relFingerprintOf E hχ hσ eISO T hT S hS hι xs
  jointCanon :=
    relJointCanonOf E hχ hσle hP p (relFingerprintOf E hχ hσ eISO T hT S hS hι xs)

/-- Equal corrected relative codes ⇒ equal joint soft canons. -/
theorem equal_relCode_equal_joint_canon {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K)
    {δ : _root_.Ordinal.{u}} {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hσ : aleph0 ≤ σ)
    (hσle : σ ≤ χ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (T : Set δ.ToType) (hT : #T ≤ χ)
    (S : Set I) (hS : #S ≤ χ)
    {P ι : Type u} (hP : #P ≤ χ) (hι : #ι ≤ σ) (hιχ : #ι ≤ χ)
    (p : P → (E.obj I).carrier) (xs ys : ι → (E.obj I).carrier)
    (hcode : relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p xs =
        relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p ys) :
    (relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p xs).jointCanon =
      (relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p ys).jointCanon :=
  congrArg RelCode.jointCanon hcode

/-- **Infra `infra_relcode_orbit_record`:** equal relative fingerprints determine the joint
soft canon built by `relJointCanonOf` (image of `relCodeOf`). -/
theorem equal_fingerprint_equal_joint_canon {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K)
    {δ : _root_.Ordinal.{u}} {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hσ : aleph0 ≤ σ)
    (hσle : σ ≤ χ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (T : Set δ.ToType) (hT : #T ≤ χ)
    (S : Set I) (hS : #S ≤ χ)
    {P ι : Type u} (hP : #P ≤ χ) (hι : #ι ≤ σ) (hιχ : #ι ≤ χ)
    (p : P → (E.obj I).carrier) (xs ys : ι → (E.obj I).carrier)
    (hfp : (relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p xs).fingerprint =
        (relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p ys).fingerprint) :
    (relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p xs).jointCanon =
      (relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p ys).jointCanon := by
  dsimp [relCodeOf] at hfp ⊢
  exact congrArg (relJointCanonOf E hχ hσle hP p) hfp


/-- From equal fingerprints, the σ-canons of the new tuples agree. -/
theorem equal_fingerprint_equal_newCanon {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K)
    {δ : _root_.Ordinal.{u}} {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hσ : aleph0 ≤ σ)
    (hσle : σ ≤ χ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (T : Set δ.ToType) (hT : #T ≤ χ) (S : Set I) (hS : #S ≤ χ)
    {P ι : Type u} (hP : #P ≤ χ) (hι : #ι ≤ σ) (hιχ : #ι ≤ χ)
    (p : P → (E.obj I).carrier) (xs ys : ι → (E.obj I).carrier)
    (hfp : (relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p xs).fingerprint =
        (relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p ys).fingerprint) :
    canonicalOfTuple E hσ hι xs = canonicalOfTuple E hσ hι ys := by
  change
      (relFingerprintOf E hχ hσ eISO T hT S hS hι xs).newCanon =
        (relFingerprintOf E hχ hσ eISO T hT S hS hι ys).newCanon
  simpa [relCodeOf] using congrArg RelFingerprint.newCanon hfp


/-- Soft positions of parameters have ordinal support inside `ordinalSupportOf`. -/
theorem mem_ordinalSupportOf_of_paramSoftSupport {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {δ : _root_.Ordinal.{u}}
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (P : Set (E.obj I).carrier) {s : I} (hs : s ∈ paramSoftSupport E P)
    {i : OrdIndex δ} (hi : i ∈ hSupport (eISO.symm s)) :
    Ordinal.ToType.mk (asIio i) ∈ ordinalSupportOf E eISO P := by
  obtain ⟨x, hxP, hx⟩ := Set.mem_iUnion₂.mp hs
  refine Set.mem_iUnion₂.mpr ⟨x, hxP, ?_⟩
  refine Set.mem_iUnion₂.mpr ⟨s, hx, ?_⟩
  exact Set.mem_image_of_mem _ hi

/-- Every ordinal in `hSupport s` lies in `T`, so every `Γ` of `s` is `T`-supported. -/
theorem hSupport_gamma_T {δ : _root_.Ordinal.{u}}
    (T : Set δ.ToType) (s : HOrder δ)
    (hs : ∀ i ∈ hSupport s, Ordinal.ToType.mk (asIio i) ∈ T)
    {g : Gamma δ} (hg : g ∈ (ofColex s).support) :
    ∀ i ∈ (ofColex g).support, Ordinal.ToType.mk (asIio i) ∈ T := by
  intro i hi
  exact hs i (support_subset_hSupport s hg hi)

/-- Soft `Γ` after SoftKeyU rename (universe-aligned with `OrdIndex`). -/
abbrev SoftGamma {α : Type u} [LinearOrder α] (T : Set α) : Type (u + 1) :=
  Colex (SoftKeyU T →₀ ℤ)

/-- Soft `H` after SoftKeyU rename. -/
abbrev SoftH {α : Type u} [LinearOrder α] (T : Set α) : Type (u + 1) :=
  Colex (SoftGamma T →₀ ℚ)

/-- SoftKey as SoftKeyU. -/
noncomputable def softKeyUOf {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ)
    (i : OrdIndex δ) : SoftKeyU T :=
  ⟨softKeyOf T y i⟩

theorem softKeyUOf_strictMonoOn {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ) :
    StrictMonoOn (softKeyUOf T y)
      ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport y)) := by
  intro i hi j hj hij
  -- SoftKeyU order is the lift of SoftKey order along `ULift.down`
  change softKeyOf T y i < softKeyOf T y j
  exact softKeyOf_strictMonoOn T y hi hj hij

/-- Soft push of an `H`-point along SoftKeyU rename of `y`. -/
noncomputable def softHPush {δ : _root_.Ordinal.{u}} (T : Set δ.ToType)
    (y z : HOrder δ) : SoftH T := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  letI : DecidableEq (SoftKeyU T) := Classical.decEq _
  letI : DecidableEq (SoftGamma T) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  let pushG : Gamma δ → SoftGamma T := fun g =>
    toColex ((ofColex g).mapDomain (softKeyUOf T y))
  exact toColex ((ofColex z).mapDomain pushG)

theorem softHPush_eq_on_T_supported {δ : _root_.Ordinal.{u}} (T : Set δ.ToType)
    (y₁ y₂ s : HOrder δ)
    (hs : ∀ i ∈ hSupport s, Ordinal.ToType.mk (asIio i) ∈ T) :
    softHPush T y₁ s = softHPush T y₂ s := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  letI : DecidableEq (SoftKeyU T) := Classical.decEq _
  letI : DecidableEq (SoftGamma T) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  refine congrArg toColex (mapDomain_congr ?_)
  intro g hg
  refine congrArg toColex (mapDomain_congr ?_)
  intro i hi
  have hiT := hs i (support_subset_hSupport s hg hi)
  simp [softKeyUOf, softKeyOf_eq_on_mem_T T y₁ y₂ hiT]

/-- Equal SoftPoints package equal SoftH self-pushes (via SoftKey ↪ SoftKeyU). -/
theorem softHPush_eq_of_abstractifySoft {δ : _root_.Ordinal.{u}} (T : Set δ.ToType)
    {x y : HOrder δ} (h : abstractifySoft T x = abstractifySoft T y) :
    softHPush T x x = softHPush T y y := by
  classical
  letI : DecidableEq (SoftKey T) := Classical.decEq _
  letI : DecidableEq (SoftKeyU T) := Classical.decEq _
  letI : DecidableEq (SoftGamma T) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  have hpack (z : HOrder δ) :
      ((abstractifySoft T z).mapDomain (Finsupp.mapDomain (M := ℤ) ULift.up)).mapDomain
          (toColex : (SoftKeyU T →₀ ℤ) → SoftGamma T) =
        (ofColex z).mapDomain (fun g =>
          toColex (((ofColex g).mapDomain (softKeyOf T z)).mapDomain ULift.up)) := by
    dsimp only [abstractifySoft]
    rw [← mapDomain_comp (M := ℚ), ← mapDomain_comp (M := ℚ)]
    rfl
  have hform (z : HOrder δ) :
      ofColex (softHPush T z z) =
        ((abstractifySoft T z).mapDomain (Finsupp.mapDomain (M := ℤ) ULift.up)).mapDomain
          (toColex : (SoftKeyU T →₀ ℤ) → SoftGamma T) := by
    rw [hpack]
    dsimp only [softHPush, softKeyUOf]
    rw [ofColex_toColex]
    refine mapDomain_congr (M := ℚ) (v := ofColex z) ?_
    intro g hg
    congr 1
    exact mapDomain_comp (α := OrdIndex δ) (β := SoftKey T) (γ := SoftKeyU T) (M := ℤ)
      (f := softKeyOf T z) (g := (ULift.up : SoftKey T → SoftKeyU T)) (v := ofColex g)
  apply ofColex.injective
  rw [hform, hform, h]

/-- `mapDomain f` on a vector supported in `s` equals the subtype-comap push. -/
theorem mapDomain_eq_mapDomain_subtype {α : Type*} {β : Type*} {M : Type*}
    [DecidableEq α] [DecidableEq β] [AddCommMonoid M]
    (s : Finset α) (f : α → β) (v : α →₀ M) (hv : v.support ⊆ s) :
    v.mapDomain f =
      (comapDomain (Subtype.val : {x // x ∈ s} → α) v Subtype.val_injective.injOn).mapDomain
        (fun i : {x // x ∈ s} => f i.1) := by
  classical
  have hv' :
      embDomain (Function.Embedding.subtype (· ∈ s))
          (comapDomain Subtype.val v Subtype.val_injective.injOn) = v := by
    refine embDomain_comapDomain (f := Function.Embedding.subtype (· ∈ s)) ?_
    intro x hx
    exact ⟨⟨x, hv hx⟩, rfl⟩
  calc
    v.mapDomain f
        = (embDomain (Function.Embedding.subtype (· ∈ s))
            (comapDomain Subtype.val v Subtype.val_injective.injOn)).mapDomain f := by
          rw [hv']
    _ = (mapDomain (⇑(Function.Embedding.subtype (· ∈ s)))
            (comapDomain Subtype.val v Subtype.val_injective.injOn)).mapDomain f := by
          rw [embDomain_eq_mapDomain]
    _ = mapDomain (f ∘ ⇑(Function.Embedding.subtype (· ∈ s)))
          (comapDomain Subtype.val v Subtype.val_injective.injOn) := by
          rw [← mapDomain_comp]
    _ = mapDomain (fun i : {x // x ∈ s} => f i.1)
          (comapDomain Subtype.val v Subtype.val_injective.injOn) := rfl

/-- Colex comparison is preserved by SoftKeyU rename on a joint support. -/
theorem softHPush_lt_iff {δ : _root_.Ordinal.{u}} (T : Set δ.ToType) (y : HOrder δ)
    (a b : HOrder δ)
    (ha : ↑(hSupport a) ⊆
      ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport y)))
    (hb : ↑(hSupport b) ⊆
      ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport y))) :
    a < b ↔ softHPush T y a < softHPush T y b := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  letI : DecidableEq (SoftKeyU T) := Classical.decEq _
  letI : DecidableEq (SoftGamma T) := Classical.decEq _
  letI : DecidableEq (Gamma δ) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  let U : Finset (OrdIndex δ) := hSupport a ∪ hSupport b
  have hU : ↑U ⊆
      ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport y)) := by
    intro i hi
    rcases Finset.mem_union.mp hi with hia | hib
    · exact ha hia
    · exact hb hib
  have hmono : StrictMono (fun i : {i // i ∈ U} => softKeyUOf T y i.1) := by
    intro i j hij
    exact softKeyUOf_strictMonoOn T y (hU i.property) (hU j.property)
      (Subtype.coe_lt_coe.mpr hij)
  let φ : {i // i ∈ U} ↪o SoftKeyU T := OrderEmbedding.ofStrictMono _ hmono
  let φΓ : Colex ({i // i ∈ U} →₀ ℤ) ↪o SoftGamma T := colexPush (M := ℤ) φ
  let restG (g : Gamma δ) : Colex ({i // i ∈ U} →₀ ℤ) :=
    toColex (comapDomain (Subtype.val : {x // x ∈ U} → OrdIndex δ) (ofColex g)
      Subtype.val_injective.injOn)
  have hγsupp (g : Gamma δ) (hg : g ∈ (ofColex a).support ∨ g ∈ (ofColex b).support) :
      (ofColex g).support ⊆ U := by
    intro i hi
    cases hg with
    | inl hga => exact Finset.mem_union_left _ (support_subset_hSupport a hga hi)
    | inr hgb => exact Finset.mem_union_right _ (support_subset_hSupport b hgb hi)
  have hpushG_eq (g : Gamma δ) (hg : (ofColex g).support ⊆ U) :
      φΓ (restG g) = toColex ((ofColex g).mapDomain (softKeyUOf T y)) := by
    apply ofColex.injective
    unfold φΓ restG colexPush
    rw [OrderEmbedding.coe_ofStrictMono, ofColex_toColex, ofColex_toColex, ofColex_toColex]
    have hφ : ⇑φ = fun i : {i // i ∈ U} => softKeyUOf T y i.1 := rfl
    rw [hφ]
    exact (mapDomain_eq_mapDomain_subtype U (softKeyUOf T y) (ofColex g) hg).symm
  have hγlt (g h : Gamma δ)
      (hg : (ofColex g).support ⊆ U) (hh : (ofColex h).support ⊆ U) :
      g < h ↔ φΓ (restG g) < φΓ (restG h) :=
    (colex_comap_lt (M := ℤ) U g h hg hh).trans
      ((φΓ).lt_iff_lt (a := restG g) (b := restG h)).symm
  let sΓ : Finset (Gamma δ) := (ofColex a).support ∪ (ofColex b).support
  have haΓ : (ofColex a).support ⊆ sΓ := Finset.subset_union_left
  have hbΓ : (ofColex b).support ⊆ sΓ := Finset.subset_union_right
  have hγU (g : Gamma δ) (hg : g ∈ sΓ) : (ofColex g).support ⊆ U :=
    hγsupp g (Finset.mem_union.mp hg)
  have hmonoΓ : StrictMono (fun g : {g // g ∈ sΓ} => φΓ (restG g.1)) := by
    intro g h hgh
    exact (hγlt g.1 h.1 (hγU g.1 g.property) (hγU h.1 h.property)).mp
      (Subtype.coe_lt_coe.mpr hgh)
  let ψ : {g // g ∈ sΓ} ↪o SoftGamma T := OrderEmbedding.ofStrictMono _ hmonoΓ
  let ψH : Colex ({g // g ∈ sΓ} →₀ ℚ) ↪o SoftH T := colexPush (M := ℚ) ψ
  let restH (z : HOrder δ) : Colex ({g // g ∈ sΓ} →₀ ℚ) :=
    toColex (comapDomain (Subtype.val : {g // g ∈ sΓ} → Gamma δ) (ofColex z)
      Subtype.val_injective.injOn)
  have hsoft_eq (z : HOrder δ) (hz : (ofColex z).support ⊆ sΓ) :
      ψH (restH z) = softHPush T y z := by
    apply ofColex.injective
    unfold ψH restH colexPush softHPush
    rw [OrderEmbedding.coe_ofStrictMono, ofColex_toColex, ofColex_toColex, ofColex_toColex]
    have hψ : ⇑ψ = fun g : {g // g ∈ sΓ} => φΓ (restG g.1) := rfl
    rw [hψ]
    have h1 :
        mapDomain (fun g : {g // g ∈ sΓ} => φΓ (restG g.1))
            (comapDomain Subtype.val (ofColex z) Subtype.val_injective.injOn) =
          mapDomain (fun g : {g // g ∈ sΓ} =>
              toColex ((ofColex g.1).mapDomain (softKeyUOf T y)))
            (comapDomain Subtype.val (ofColex z) Subtype.val_injective.injOn) := by
      refine mapDomain_congr ?_
      intro g hg
      exact hpushG_eq g.1 (hγU g.1 g.property)
    rw [h1]
    exact (mapDomain_eq_mapDomain_subtype sΓ
      (fun g => toColex ((ofColex g).mapDomain (softKeyUOf T y))) (ofColex z) hz).symm
  have hL : a < b ↔ ψH (restH a) < ψH (restH b) :=
    (colex_comap_lt (M := ℚ) sΓ a b haΓ hbΓ).trans
      ((ψH).lt_iff_lt (a := restH a) (b := restH b)).symm
  rw [hL, hsoft_eq a haΓ, hsoft_eq b hbΓ]

/-- Soft codes over `T` determine comparisons with every `T`-supported point.

Equal gap-indexed soft codes match comparisons against every point whose ordinal support
lies in `T` (English Lemma 4.5 / Lemma 3.2). -/
theorem abstractify_lt_of_hSupport {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ)
    (s x y : HOrder δ)
    (hs : ∀ i ∈ hSupport s, Ordinal.ToType.mk (asIio i) ∈ T)
    (hxy : abstractify hχ T hT x = abstractify hχ T hT y) :
    s < x ↔ s < y := by
  classical
  letI : LinearOrder δ.ToType := inferInstance
  have hsoft : abstractifySoft T x = abstractifySoft T y :=
    abstractifySoft_eq_of_abstractify hχ T hT hxy
  have hs_sub_x :
      ↑(hSupport s) ⊆
        ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport x)) := by
    intro i hi; exact Or.inl (hs i hi)
  have hx_sub :
      ↑(hSupport x) ⊆
        ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport x)) := by
    intro i hi; exact Or.inr hi
  have hs_sub_y :
      ↑(hSupport s) ⊆
        ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport y)) := by
    intro i hi; exact Or.inl (hs i hi)
  have hy_sub :
      ↑(hSupport y) ⊆
        ({i : OrdIndex δ | Ordinal.ToType.mk (asIio i) ∈ T} ∪ ↑(hSupport y)) := by
    intro i hi; exact Or.inr hi
  have hltx := softHPush_lt_iff (T := T) (y := x) (a := s) (b := x) hs_sub_x hx_sub
  have hlty := softHPush_lt_iff (T := T) (y := y) (a := s) (b := y) hs_sub_y hy_sub
  have hs_eq : softHPush T x s = softHPush T y s :=
    softHPush_eq_on_T_supported T x y s hs
  have hxyH : softHPush T x x = softHPush T y y :=
    softHPush_eq_of_abstractifySoft T hsoft
  calc
    s < x ↔ softHPush T x s < softHPush T x x := hltx
    _ ↔ softHPush T y s < softHPush T y y := by rw [hs_eq, hxyH]
    _ ↔ s < y := hlty.symm

theorem soft_eq_of_fingerprint {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {δ : _root_.Ordinal.{u}} {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hσ : aleph0 ≤ σ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (T : Set δ.ToType) (hT : #T ≤ χ) (S : Set I) (hS : #S ≤ χ)
    {ι : Type u} (hι : #ι ≤ σ) (xs ys : ι → (E.obj I).carrier)
    (hfp : relFingerprintOf E hχ hσ eISO T hT S hS hι xs =
        relFingerprintOf E hχ hσ eISO T hT S hS hι ys)
    (b : Below σ) :
    (relFingerprintOf E hχ hσ eISO T hT S hS hι xs).soft b =
      (relFingerprintOf E hχ hσ eISO T hT S hS hι ys).soft b :=
  congrFun (congrArg RelFingerprint.soft hfp) b

theorem eqOld_eq_of_fingerprint {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {δ : _root_.Ordinal.{u}} {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hσ : aleph0 ≤ σ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (T : Set δ.ToType) (hT : #T ≤ χ) (S : Set I) (hS : #S ≤ χ)
    {ι : Type u} (hι : #ι ≤ σ) (xs ys : ι → (E.obj I).carrier)
    (hfp : relFingerprintOf E hχ hσ eISO T hT S hS hι xs =
        relFingerprintOf E hχ hσ eISO T hT S hS hι ys)
    (b : Below σ) :
    (relFingerprintOf E hχ hσ eISO T hT S hS hι xs).eqOld b =
      (relFingerprintOf E hχ hσ eISO T hT S hS hι ys).eqOld b :=
  congrFun (congrArg RelFingerprint.eqOld hfp) b

/-- Equal fingerprints determine the same order/occupancy diagram on `S ⊕ new` places. -/
theorem fingerprint_same_order_and_occupancy {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K)
    {δ : _root_.Ordinal.{u}} {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hσ : aleph0 ≤ σ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (T : Set δ.ToType) (hT : #T ≤ χ) (S : Set I) (hS : #S ≤ χ)
    {ι : Type u} (hι : #ι ≤ σ) (xs ys : ι → (E.obj I).carrier)
    (hTS : ∀ s ∈ S, ∀ i ∈ hSupport (eISO.symm s), Ordinal.ToType.mk (asIio i) ∈ T)
    (hfp : relFingerprintOf E hχ hσ eISO T hT S hS hι xs =
        relFingerprintOf E hχ hσ eISO T hT S hS hι ys) :
    SameOrderDiagram
        (Sum.elim (Subtype.val : ↥S → I)
          (canonicalPlaceOfTuple E hσ hι xs))
        (Sum.elim (Subtype.val : ↥S → I)
          (canonicalPlaceEq E hσ hι ys (canonicalOfTuple E hσ hι xs)
            (by
              simpa [relFingerprintOf] using
                congrArg RelFingerprint.newCanon hfp.symm))) ∧
      SameSlotOccupancy
        (Sum.elim (Subtype.val : ↥S → I)
          (canonicalPlaceOfTuple E hσ hι xs))
        (Sum.elim (Subtype.val : ↥S → I)
          (canonicalPlaceEq E hσ hι ys (canonicalOfTuple E hσ hι xs)
            (by
              simpa [relFingerprintOf] using
                congrArg RelFingerprint.newCanon hfp.symm))) := by
  classical
  let r : CanonicalRecord E.lab E.arity σ := canonicalOfTuple E hσ hι xs
  have hrY : canonicalOfTuple E hσ hι ys = r := by
    simpa [relFingerprintOf] using congrArg RelFingerprint.newCanon hfp.symm
  let placeX : ↥r.slt → I := canonicalPlaceOfTuple E hσ hι xs
  let placeY : ↥r.slt → I := canonicalPlaceEq E hσ hι ys r hrY
  let enumX : ↥S ⊕ ↥r.slt → I := Sum.elim Subtype.val placeX
  let enumY : ↥S ⊕ ↥r.slt → I := Sum.elim Subtype.val placeY
  have hrx := realizes_canonicalOfTuple E hσ hι xs
  have hry := realizes_canonical_eq E hσ hι ys r hrY
  have heqOld (b : Below σ) :=
    eqOld_eq_of_fingerprint E hχ hσ eISO T hT S hS hι xs ys hfp b
  have hsoft (b : Below σ) :=
    soft_eq_of_fingerprint E hχ hσ eISO T hT S hS hι xs ys hfp b
  have hoccFp := congrArg RelFingerprint.occ hfp
  have hsoft_place (b : ↥r.slt) :
      abstractify hχ T hT (eISO.symm (placeX b)) =
        abstractify hχ T hT (eISO.symm (placeY b)) := by
    have hb := b.property
    have hx :
        (relFingerprintOf E hχ hσ eISO T hT S hS hι xs).soft b.1 =
          abstractify hχ T hT (eISO.symm (placeX b)) := by
      dsimp [relFingerprintOf, placeX, r]; simp [hb]
    have hy :
        (relFingerprintOf E hχ hσ eISO T hT S hS hι ys).soft b.1 =
          abstractify hχ T hT (eISO.symm (placeY b)) := by
      dsimp [relFingerprintOf, placeY, canonicalPlaceEq]; simp [hrY, hb]
    exact (hx.symm.trans (hsoft b.1)).trans hy
  have hplace_eq (b : ↥r.slt) (hs : placeX b ∈ S) : placeY b = placeX b := by
    have hb := b.property
    have hx :
        (relFingerprintOf E hχ hσ eISO T hT S hS hι xs).eqOld b.1 =
          some (embedBelow hS ⟨placeX b, hs⟩) := by
      simp [relFingerprintOf, placeX, r, hb, hs]
    have hmemY : placeY b ∈ S := by
      by_contra hne
      have hyNone :
          (relFingerprintOf E hχ hσ eISO T hT S hS hι ys).eqOld b.1 = none := by
        simpa [relFingerprintOf, placeY, canonicalPlaceEq, hrY, hb] using hne
      have hnone : some (embedBelow hS ⟨placeX b, hs⟩) = (none : Option (Below χ)) :=
        hx.symm.trans ((heqOld b.1).trans hyNone)
      cases hnone
    have hy :
        (relFingerprintOf E hχ hσ eISO T hT S hS hι ys).eqOld b.1 =
          some (embedBelow hS ⟨placeY b, hmemY⟩) := by
      simp [relFingerprintOf, placeY, canonicalPlaceEq, hrY, hb]
      exact (by simpa [placeY, canonicalPlaceEq, hrY] using hmemY)
    have hsome := hx.symm.trans ((heqOld b.1).trans hy)
    injection hsome with hEq
    exact (congrArg Subtype.val ((embedBelow hS).injective hEq)).symm
  have hplace_mem_iff (b : ↥r.slt) : placeX b ∈ S ↔ placeY b ∈ S := by
    constructor
    · intro hs; rwa [hplace_eq b hs]
    · intro hsY
      have hb := b.property
      have hy :
          (relFingerprintOf E hχ hσ eISO T hT S hS hι ys).eqOld b.1 =
            some (embedBelow hS ⟨placeY b, hsY⟩) := by
        simpa [relFingerprintOf, placeY, canonicalPlaceEq, hrY, hb] using hsY
      by_cases hsX : placeX b ∈ S
      · exact hsX
      · have hxNone :
            (relFingerprintOf E hχ hσ eISO T hT S hS hι xs).eqOld b.1 = none := by
          simp [relFingerprintOf, placeX, r, hb, hsX]
        have hnone : (none : Option (Below χ)) = some (embedBelow hS ⟨placeY b, hsY⟩) :=
          hxNone.symm.trans ((heqOld b.1).trans hy)
        cases hnone
  have hcross_lt (s : ↥S) (b : ↥r.slt) :
      (s : I) < placeX b ↔ (s : I) < placeY b := by
    by_cases hs : placeX b ∈ S
    · rw [← hplace_eq b hs]
    · have hcmp :=
        abstractify_lt_of_hSupport hχ T hT (eISO.symm (s : I))
          (eISO.symm (placeX b)) (eISO.symm (placeY b))
          (fun i hi => hTS s.val s.property i hi) (hsoft_place b)
      simpa [eISO.symm.lt_iff_lt] using hcmp
  have hcross_gt (s : ↥S) (b : ↥r.slt) :
      placeX b < (s : I) ↔ placeY b < (s : I) := by
    constructor
    · intro h
      rcases lt_trichotomy (placeY b) (s : I) with hlt | heq | hgt
      · exact hlt
      · have hsY : placeY b ∈ S := by simpa [heq] using s.property
        have hsX : placeX b ∈ S := (hplace_mem_iff b).mpr hsY
        have : placeY b = placeX b := hplace_eq b hsX
        exact (h.ne (by simp [← this, heq])).elim
      · exact (lt_asymm h ((hcross_lt s b).mpr hgt)).elim
    · intro h
      rcases lt_trichotomy (placeX b) (s : I) with hlt | heq | hgt
      · exact hlt
      · have hsX : placeX b ∈ S := by simpa [heq] using s.property
        have : placeY b = placeX b := hplace_eq b hsX
        exact (h.ne (by simp [this, heq])).elim
      · exact (lt_asymm h ((hcross_lt s b).mp hgt)).elim
  have hcross_eq (s : ↥S) (b : ↥r.slt) :
      (s : I) = placeX b ↔ (s : I) = placeY b := by
    constructor
    · intro h
      have hsX : placeX b ∈ S := by simpa [← h] using s.property
      exact h.trans (hplace_eq b hsX).symm
    · intro h
      have hsY : placeY b ∈ S := by simpa [← h] using s.property
      have hsX : placeX b ∈ S := (hplace_mem_iff b).mpr hsY
      exact h.trans (hplace_eq b hsX)
  have hdiag : SameOrderDiagram enumX enumY := by
    refine ⟨?_, ?_⟩
    · intro i j
      cases i with
      | inl a =>
        cases j with
        | inl b => change (a.val = b.val) ↔ (a.val = b.val); rfl
        | inr b => exact hcross_eq a b
      | inr a =>
        cases j with
        | inl b =>
          constructor
          · intro h; exact ((hcross_eq b a).mp h.symm).symm
          · intro h; exact ((hcross_eq b a).mpr h.symm).symm
        | inr b =>
          constructor
          · intro h; exact congrArg placeY (hrx.1 h)
          · intro h; exact congrArg placeX (hry.1 h)
    · intro i j
      cases i with
      | inl a =>
        cases j with
        | inl b => change (a.val < b.val) ↔ (a.val < b.val); rfl
        | inr b => exact hcross_lt a b
      | inr a =>
        cases j with
        | inl b => exact hcross_gt b a
        | inr b =>
          change placeX a < placeX b ↔ placeY a < placeY b
          rw [← hrx.2.1 a b, ← hry.2.1 a b]
  refine ⟨hdiag, ?_⟩
  intro lower upper hltX hltY
  have hfill :
      (∃ k, enumX k ∈ strictSlot (enumX '' lower) (enumX '' upper)) ↔
        (∃ k, enumY k ∈ strictSlot (enumY '' lower) (enumY '' upper)) := by
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      dsimp [strictSlot] at hk ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hmem
        obtain ⟨i, hi, heq⟩ := (Set.mem_image _ _ _).mp hmem
        exact hk.1 ((Set.mem_image _ _ _).mpr ⟨i, hi, ((hdiag.1 k i).mpr heq.symm).symm⟩)
      · intro hmem
        obtain ⟨i, hi, heq⟩ := (Set.mem_image _ _ _).mp hmem
        exact hk.2.1 ((Set.mem_image _ _ _).mpr ⟨i, hi, ((hdiag.1 k i).mpr heq.symm).symm⟩)
      · intro a ha
        obtain ⟨i, hi, rfl⟩ := (Set.mem_image _ _ _).mp ha
        exact (hdiag.2 i k).mp (hk.2.2.1 _ ((Set.mem_image _ _ _).mpr ⟨i, hi, rfl⟩))
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := (Set.mem_image _ _ _).mp hb
        exact (hdiag.2 k i).mp (hk.2.2.2 _ ((Set.mem_image _ _ _).mpr ⟨i, hi, rfl⟩))
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      dsimp [strictSlot] at hk ⊢
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hmem
        obtain ⟨i, hi, heq⟩ := (Set.mem_image _ _ _).mp hmem
        exact hk.1 ((Set.mem_image _ _ _).mpr ⟨i, hi, ((hdiag.1 k i).mp heq.symm).symm⟩)
      · intro hmem
        obtain ⟨i, hi, heq⟩ := (Set.mem_image _ _ _).mp hmem
        exact hk.2.1 ((Set.mem_image _ _ _).mpr ⟨i, hi, ((hdiag.1 k i).mp heq.symm).symm⟩)
      · intro a ha
        obtain ⟨i, hi, rfl⟩ := (Set.mem_image _ _ _).mp ha
        exact (hdiag.2 i k).mpr (hk.2.2.1 _ ((Set.mem_image _ _ _).mpr ⟨i, hi, rfl⟩))
      · intro b hb
        obtain ⟨i, hi, rfl⟩ := (Set.mem_image _ _ _).mp hb
        exact (hdiag.2 k i).mpr (hk.2.2.2 _ ((Set.mem_image _ _ _).mpr ⟨i, hi, rfl⟩))
  by_cases hfillX : ∃ k, enumX k ∈ strictSlot (enumX '' lower) (enumX '' upper)
  · exact iff_of_true ⟨enumX hfillX.choose, hfillX.choose_spec⟩
      ⟨enumY (hfill.mp hfillX).choose, (hfill.mp hfillX).choose_spec⟩
  · let LN : Set ↥r.slt := {z | Sum.inr z ∈ lower}
    let UN : Set ↥r.slt := {z | Sum.inr z ∈ upper}
    let LS : Set ↥S := {z | Sum.inl z ∈ lower}
    let US : Set ↥S := {z | Sum.inl z ∈ upper}
    have hXL : enumX '' lower = (Subtype.val '' LS) ∪ placeX '' LN := by
      ext x; constructor
      · rintro ⟨i, hi, rfl⟩; cases i with
        | inl a => exact Or.inl ⟨a, hi, rfl⟩
        | inr b => exact Or.inr ⟨b, hi, rfl⟩
      · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
        · exact ⟨Sum.inl a, ha, rfl⟩
        · exact ⟨Sum.inr b, hb, rfl⟩
    have hXU : enumX '' upper = (Subtype.val '' US) ∪ placeX '' UN := by
      ext x; constructor
      · rintro ⟨i, hi, rfl⟩; cases i with
        | inl a => exact Or.inl ⟨a, hi, rfl⟩
        | inr b => exact Or.inr ⟨b, hi, rfl⟩
      · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
        · exact ⟨Sum.inl a, ha, rfl⟩
        · exact ⟨Sum.inr b, hb, rfl⟩
    have hYL : enumY '' lower = (Subtype.val '' LS) ∪ placeY '' LN := by
      ext x; constructor
      · rintro ⟨i, hi, rfl⟩; cases i with
        | inl a => exact Or.inl ⟨a, hi, rfl⟩
        | inr b => exact Or.inr ⟨b, hi, rfl⟩
      · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
        · exact ⟨Sum.inl a, ha, rfl⟩
        · exact ⟨Sum.inr b, hb, rfl⟩
    have hYU : enumY '' upper = (Subtype.val '' US) ∪ placeY '' UN := by
      ext x; constructor
      · rintro ⟨i, hi, rfl⟩; cases i with
        | inl a => exact Or.inl ⟨a, hi, rfl⟩
        | inr b => exact Or.inr ⟨b, hi, rfl⟩
      · rintro (⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩)
        · exact ⟨Sum.inl a, ha, rfl⟩
        · exact ⟨Sum.inr b, hb, rfl⟩
    by_cases hSonly : LN ∪ UN = ∅
    · rw [hXL, hXU, hYL, hYU]
      have hLN0 : LN = ∅ := (union_empty_iff.mp hSonly).1
      have hUN0 : UN = ∅ := (union_empty_iff.mp hSonly).2
      simp [hLN0, hUN0]
    · by_cases hNonly : LS ∪ US = ∅
      · rw [hXL, hXU, hYL, hYU]
        have hLS0 : LS = ∅ := (union_empty_iff.mp hNonly).1
        have hUS0 : US = ∅ := (union_empty_iff.mp hNonly).2
        simp only [hLS0, hUS0, Set.image_empty, Set.empty_union]
        exact (hrx.2.2.2 LN UN).symm.trans (hry.2.2.2 LN UN)
      · have himpureX :
            Occupied (enumX '' lower) (enumX '' upper) →
              Occupied (Subtype.val '' LS) (Subtype.val '' US) := by
          intro ⟨w, hw⟩
          refine ⟨w, ?_⟩
          dsimp [strictSlot] at hw ⊢
          rw [hXL, hXU] at hw
          exact ⟨fun h => hw.1 (Or.inl h), fun h => hw.2.1 (Or.inl h),
            fun a ha => hw.2.2.1 a (Or.inl ha), fun b hb => hw.2.2.2 b (Or.inl hb)⟩
        have himpureY :
            Occupied (enumY '' lower) (enumY '' upper) →
              Occupied (Subtype.val '' LS) (Subtype.val '' US) := by
          intro ⟨w, hw⟩
          refine ⟨w, ?_⟩
          dsimp [strictSlot] at hw ⊢
          rw [hYL, hYU] at hw
          exact ⟨fun h => hw.1 (Or.inl h), fun h => hw.2.1 (Or.inl h),
            fun a ha => hw.2.2.1 a (Or.inl ha), fun b hb => hw.2.2.2 b (Or.inl hb)⟩
        by_cases hpure : Occupied (Subtype.val '' LS) (Subtype.val '' US)
        · let LNin : Set ↥r.slt :=
            {z | z ∈ LN ∧ (∀ s ∈ LS, (s : I) < placeX z) ∧ (∀ s ∈ US, placeX z < (s : I))}
          let UNin : Set ↥r.slt :=
            {z | z ∈ UN ∧ (∀ s ∈ LS, (s : I) < placeX z) ∧ (∀ s ∈ US, placeX z < (s : I))}
          have hinY (z : ↥r.slt) :
              ((∀ s ∈ LS, (s : I) < placeX z) ∧ (∀ s ∈ US, placeX z < (s : I))) ↔
                ((∀ s ∈ LS, (s : I) < placeY z) ∧ (∀ s ∈ US, placeY z < (s : I))) :=
            ⟨fun h => ⟨fun s hs => (hcross_lt s z).mp (h.1 s hs),
                fun s hs => (hcross_gt s z).mp (h.2 s hs)⟩,
              fun h => ⟨fun s hs => (hcross_lt s z).mpr (h.1 s hs),
                fun s hs => (hcross_gt s z).mpr (h.2 s hs)⟩⟩
          have hsideLN (place : ↥r.slt → I)
              (hUS : ∀ z ∈ LN, ∀ s ∈ US, place z < (s : I)) :
              ∀ z ∈ LN,
                ((∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I))) ∨
                  ∃ s ∈ LS, place z ≤ (s : I) := by
            intro z hz
            by_cases hLS : ∀ s ∈ LS, (s : I) < place z
            · exact Or.inl ⟨hLS, fun s hs => hUS z hz s hs⟩
            · push Not at hLS
              obtain ⟨s, hs, hle⟩ := hLS
              exact Or.inr ⟨s, hs, hle⟩
          have hsideUN (place : ↥r.slt → I)
              (hLS : ∀ z ∈ UN, ∀ s ∈ LS, (s : I) < place z) :
              ∀ z ∈ UN,
                ((∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I))) ∨
                  ∃ s ∈ US, (s : I) ≤ place z := by
            intro z hz
            by_cases hUS : ∀ s ∈ US, place z < (s : I)
            · exact Or.inl ⟨fun s hs => hLS z hz s hs, hUS⟩
            · push Not at hUS
              obtain ⟨s, hs, hle⟩ := hUS
              exact Or.inr ⟨s, hs, hle⟩
          by_cases hempty : LNin ∪ UNin = ∅
          · have hup (place : ↥r.slt → I) {enum : ↥S ⊕ ↥r.slt → I}
                (hEnumL : enum '' lower = (Subtype.val '' LS) ∪ place '' LN)
                (hEnumU : enum '' upper = (Subtype.val '' US) ∪ place '' UN)
                (hLN : ∀ z ∈ LN,
                  ((∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I))) ∨
                    ∃ s ∈ LS, place z ≤ (s : I))
                (hUN : ∀ z ∈ UN,
                  ((∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I))) ∨
                    ∃ s ∈ US, (s : I) ≤ place z)
                (hnoin : ∀ z ∈ LN ∪ UN,
                  ¬((∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I)))) :
                Occupied (enum '' lower) (enum '' upper) := by
              obtain ⟨w, hw⟩ := hpure
              refine ⟨w, ?_⟩
              dsimp [strictSlot] at hw ⊢
              rw [hEnumL, hEnumU]
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro hmem; rcases hmem with hmem | ⟨z, hz, rfl⟩
                · exact hw.1 hmem
                · rcases hLN z hz with hin | ⟨s, hs, hle⟩
                  · exact (hnoin z (Or.inl hz) hin).elim
                  · exact (not_le_of_gt (hw.2.2.1 s.val ⟨s, hs, rfl⟩) hle).elim
              · intro hmem; rcases hmem with hmem | ⟨z, hz, rfl⟩
                · exact hw.2.1 hmem
                · rcases hUN z hz with hin | ⟨s, hs, hle⟩
                  · exact (hnoin z (Or.inr hz) hin).elim
                  · exact (not_le_of_gt (hw.2.2.2 s.val ⟨s, hs, rfl⟩) hle).elim
              · intro a ha; rcases ha with ha | ⟨z, hz, rfl⟩
                · exact hw.2.2.1 a ha
                · rcases hLN z hz with hin | ⟨s, hs, hle⟩
                  · exact (hnoin z (Or.inl hz) hin).elim
                  · exact lt_of_le_of_lt hle (hw.2.2.1 s.val ⟨s, hs, rfl⟩)
              · intro b hb; rcases hb with hb | ⟨z, hz, rfl⟩
                · exact hw.2.2.2 b hb
                · rcases hUN z hz with hin | ⟨s, hs, hle⟩
                  · exact (hnoin z (Or.inr hz) hin).elim
                  · exact lt_of_lt_of_le (hw.2.2.2 s.val ⟨s, hs, rfl⟩) hle
            have hnoinX : ∀ z ∈ LN ∪ UN,
                ¬((∀ s ∈ LS, (s : I) < placeX z) ∧ (∀ s ∈ US, placeX z < (s : I))) := by
              intro z hz h
              have : z ∈ LNin ∪ UNin :=
                Or.elim hz (fun hLN => Or.inl ⟨hLN, h.1, h.2⟩)
                  (fun hUN => Or.inr ⟨hUN, h.1, h.2⟩)
              exact (Set.mem_empty_iff_false z).mp (hempty ▸ this)
            have hnoinY : ∀ z ∈ LN ∪ UN,
                ¬((∀ s ∈ LS, (s : I) < placeY z) ∧ (∀ s ∈ US, placeY z < (s : I))) := by
              intro z hz h
              exact hnoinX z hz ((hinY z).mpr h)
            exact iff_of_true
              (hup placeX hXL hXU
                (hsideLN placeX (fun z hz s hs =>
                  hltX (Sum.inr z) hz (Sum.inl s) hs))
                (hsideUN placeX (fun z hz s hs =>
                  hltX (Sum.inl s) hs (Sum.inr z) hz))
                hnoinX)
              (hup placeY hYL hYU
                (hsideLN placeY (fun z hz s hs =>
                  hltY (Sum.inr z) hz (Sum.inl s) hs))
                (hsideUN placeY (fun z hz s hs =>
                  hltY (Sum.inl s) hs (Sum.inr z) hz))
                hnoinY)
          · -- Inside places: occupancy equals joint `occ` of the inside coordinates.
            let L : Set (Below σ) := Subtype.val '' LNin
            let U : Set (Below σ) := Subtype.val '' UNin
            have hLset : {z : ↥r.slt | z.1 ∈ L} = LNin := by
              ext z; constructor
              · intro ⟨z', hz', heq⟩; exact (Subtype.ext heq) ▸ hz'
              · intro hz; exact ⟨z, hz, rfl⟩
            have hUset : {z : ↥r.slt | z.1 ∈ U} = UNin := by
              ext z; constructor
              · intro ⟨z', hz', heq⟩; exact (Subtype.ext heq) ▸ hz'
              · intro hz; exact ⟨z, hz, rfl⟩
            have hxDecide :
                (relFingerprintOf E hχ hσ eISO T hT S hS hι xs).occ L U =
                  decide
                    (Occupied
                      ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, x < placeX z} ∪ placeX '' LNin)
                      ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, placeX z < x} ∪ placeX '' UNin)) := by
              dsimp [relFingerprintOf, relOccOf]
              change decide
                  (Occupied
                    ({x | x ∈ S ∧ ∀ z ∈ {z : ↥r.slt | ↑z ∈ L} ∪ {z | ↑z ∈ U},
                        x < placeX z} ∪ placeX '' {z | ↑z ∈ L})
                    ({x | x ∈ S ∧ ∀ z ∈ {z : ↥r.slt | ↑z ∈ L} ∪ {z | ↑z ∈ U},
                        placeX z < x} ∪ placeX '' {z | ↑z ∈ U})) =
                decide
                  (Occupied
                    ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, x < placeX z} ∪ placeX '' LNin)
                    ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, placeX z < x} ∪ placeX '' UNin))
              simp_rw [hLset, hUset]
            have hyDecide :
                (relFingerprintOf E hχ hσ eISO T hT S hS hι ys).occ L U =
                  decide
                    (Occupied
                      ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, x < placeY z} ∪ placeY '' LNin)
                      ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, placeY z < x} ∪ placeY '' UNin)) := by
              -- Abstract `r` so `cases hr` can fire (cannot `subst` a `let`-bound).
              have gen (r' : CanonicalRecord E.lab E.arity σ)
                  (hr : canonicalOfTuple E hσ hι ys = r')
                  (LNin' UNin' : Set ↥r'.slt)
                  (hL' : {z : ↥r'.slt | ↑z ∈ Subtype.val '' LNin'} = LNin')
                  (hU' : {z : ↥r'.slt | ↑z ∈ Subtype.val '' UNin'} = UNin') :
                  (relFingerprintOf E hχ hσ eISO T hT S hS hι ys).occ
                      (Subtype.val '' LNin') (Subtype.val '' UNin') =
                    decide
                      (Occupied
                        ({x | x ∈ S ∧ ∀ z ∈ LNin' ∪ UNin',
                            x < canonicalPlaceEq E hσ hι ys r' hr z} ∪
                          canonicalPlaceEq E hσ hι ys r' hr '' LNin')
                        ({x | x ∈ S ∧ ∀ z ∈ LNin' ∪ UNin',
                            canonicalPlaceEq E hσ hι ys r' hr z < x} ∪
                          canonicalPlaceEq E hσ hι ys r' hr '' UNin')) := by
                cases hr
                dsimp [relFingerprintOf, relOccOf, canonicalPlaceEq]
                change decide
                    (Occupied
                      ({x | x ∈ S ∧ ∀ z ∈
                          {z : ↥(canonicalOfTuple E hσ hι ys).slt |
                            ↑z ∈ Subtype.val '' LNin'} ∪
                          {z | ↑z ∈ Subtype.val '' UNin'},
                          x < canonicalPlaceOfTuple E hσ hι ys z} ∪
                        canonicalPlaceOfTuple E hσ hι ys ''
                          {z | ↑z ∈ Subtype.val '' LNin'})
                      ({x | x ∈ S ∧ ∀ z ∈
                          {z : ↥(canonicalOfTuple E hσ hι ys).slt |
                            ↑z ∈ Subtype.val '' LNin'} ∪
                          {z | ↑z ∈ Subtype.val '' UNin'},
                          canonicalPlaceOfTuple E hσ hι ys z < x} ∪
                        canonicalPlaceOfTuple E hσ hι ys ''
                          {z | ↑z ∈ Subtype.val '' UNin'})) =
                  decide
                    (Occupied
                      ({x | x ∈ S ∧ ∀ z ∈ LNin' ∪ UNin',
                          x < canonicalPlaceOfTuple E hσ hι ys z} ∪
                        canonicalPlaceOfTuple E hσ hι ys '' LNin')
                      ({x | x ∈ S ∧ ∀ z ∈ LNin' ∪ UNin',
                          canonicalPlaceOfTuple E hσ hι ys z < x} ∪
                        canonicalPlaceOfTuple E hσ hι ys '' UNin'))
                simp_rw [hL', hU']
              simpa [placeY, L, U] using gen r hrY LNin UNin hLset hUset
            have hjoint :
                Occupied
                    ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, x < placeX z} ∪ placeX '' LNin)
                    ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, placeX z < x} ∪ placeX '' UNin) ↔
                  Occupied
                    ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, x < placeY z} ∪ placeY '' LNin)
                    ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, placeY z < x} ∪ placeY '' UNin) := by
              have hbool := congrFun (congrFun hoccFp L) U
              exact (decide_eq_decide).mp (hxDecide.symm.trans (hbool.trans hyDecide))
            have hLSsub (place : ↥r.slt → I)
                (hinside : ∀ z ∈ LNin ∪ UNin,
                  (∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I))) :
                Subtype.val '' LS ⊆
                  {x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, x < place z} := by
              intro x hx
              obtain ⟨s, hs, rfl⟩ := hx
              exact ⟨s.property, fun z hz => (hinside z hz).1 s hs⟩
            have hUSsub (place : ↥r.slt → I)
                (hinside : ∀ z ∈ LNin ∪ UNin,
                  (∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I))) :
                Subtype.val '' US ⊆
                  {x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, place z < x} := by
              intro x hx
              obtain ⟨s, hs, rfl⟩ := hx
              exact ⟨s.property, fun z hz => (hinside z hz).2 s hs⟩
            have hfillY :
                ¬∃ k, enumY k ∈ strictSlot (enumY '' lower) (enumY '' upper) :=
              fun h => hfillX (hfill.mpr h)
            have hneIn : (LNin ∪ UNin).Nonempty :=
              Set.nonempty_iff_ne_empty.mpr hempty
            have hred {place : ↥r.slt → I} {enum : ↥S ⊕ ↥r.slt → I}
                (hEnumDef : enum = Sum.elim Subtype.val place)
                (hEnumL : enum '' lower = (Subtype.val '' LS) ∪ place '' LN)
                (hEnumU : enum '' upper = (Subtype.val '' US) ∪ place '' UN)
                (hfillE : ¬∃ k, enum k ∈ strictSlot (enum '' lower) (enum '' upper))
                (hLN : ∀ z ∈ LN,
                  ((∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I))) ∨
                    ∃ s ∈ LS, place z ≤ (s : I))
                (hUN : ∀ z ∈ UN,
                  ((∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I))) ∨
                    ∃ s ∈ US, (s : I) ≤ place z)
                (hinside : ∀ z ∈ LNin ∪ UNin,
                  (∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I)))
                (htoLN : ∀ z ∈ LN,
                  (∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I)) →
                    z ∈ LNin)
                (htoUN : ∀ z ∈ UN,
                  (∀ s ∈ LS, (s : I) < place z) ∧ (∀ s ∈ US, place z < (s : I)) →
                    z ∈ UNin)
                (hmemL : ∀ z ∈ LNin, z ∈ LN)
                (hmemU : ∀ z ∈ UNin, z ∈ UN)
                (hLSsub' : Subtype.val '' LS ⊆
                  {x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, x < place z})
                (hUSsub' : Subtype.val '' US ⊆
                  {x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, place z < x}) :
                Occupied (enum '' lower) (enum '' upper) ↔
                  Occupied
                    ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, x < place z} ∪ place '' LNin)
                    ({x | x ∈ S ∧ ∀ z ∈ LNin ∪ UNin, place z < x} ∪ place '' UNin) := by
              constructor
              · intro ⟨w, hw⟩
                refine ⟨w, ?_⟩
                dsimp [strictSlot] at hw ⊢
                rw [hEnumL, hEnumU] at hw
                have hwS : w ∉ S := fun hsS =>
                  hfillE ⟨Sum.inl ⟨w, hsS⟩, by
                    subst hEnumDef
                    rw [Sum.elim_inl, hEnumL, hEnumU]; exact hw⟩
                have hfillS {a : I} (haS : a ∈ S)
                    (ha : a ∈
                      strictSlot
                        ((Subtype.val '' LS) ∪ place '' LN)
                        ((Subtype.val '' US) ∪ place '' UN)) : False :=
                  hfillE ⟨Sum.inl ⟨a, haS⟩, by
                    subst hEnumDef
                    rw [Sum.elim_inl, hEnumL, hEnumU]; exact ha⟩
                refine ⟨?_, ?_, ?_, ?_⟩
                · intro hmem; rcases hmem with hmem | ⟨z, hz, rfl⟩
                  · exact hwS hmem.1
                  · exact hw.1 (Or.inr ⟨z, hmemL z hz, rfl⟩)
                · intro hmem; rcases hmem with hmem | ⟨z, hz, rfl⟩
                  · exact hwS hmem.1
                  · exact hw.2.1 (Or.inr ⟨z, hmemU z hz, rfl⟩)
                · intro a ha; rcases ha with ha | ⟨z, hz, rfl⟩
                  · by_contra hna
                    have hgt : w < a :=
                      lt_of_le_of_ne (le_of_not_gt hna) (fun he => hwS (he ▸ ha.1))
                    refine hfillS ha.1 ⟨?_, ?_, ?_, ?_⟩
                    · intro hmem
                      exact not_lt_of_gt hgt (hw.2.2.1 a hmem)
                    · intro hmem; rcases hmem with hUS | hP
                      · obtain ⟨s, hs, heq⟩ := hUS
                        obtain ⟨z0, hz0⟩ := hneIn
                        have hlt : a < (s : I) :=
                          (ha.2 z0 hz0).trans ((hinside z0 hz0).2 s hs)
                        exact lt_irrefl a (heq ▸ hlt)
                      · obtain ⟨z, hz, heq⟩ := hP
                        have ha' : a = place z := heq.symm
                        rcases hUN z hz with hin | ⟨s, hs, hle⟩
                        · exact lt_irrefl a (ha' ▸
                            ha.2 z (Or.inr (htoUN z hz hin)))
                        · obtain ⟨z0, hz0⟩ := hneIn
                          exact not_lt_of_ge (ha' ▸ hle)
                            ((ha.2 z0 hz0).trans ((hinside z0 hz0).2 s hs))
                    · intro c hc; rcases hc with ⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩
                      · exact (hw.2.2.1 s.val (Or.inl ⟨s, hs, rfl⟩)).trans hgt
                      · exact (hw.2.2.1 (place z) (Or.inr ⟨z, hz, rfl⟩)).trans hgt
                    · intro c hc; rcases hc with ⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩
                      · obtain ⟨z0, hz0⟩ := hneIn
                        exact (ha.2 z0 hz0).trans ((hinside z0 hz0).2 s hs)
                      · rcases hUN z hz with hin | ⟨s, hs, hle⟩
                        · exact ha.2 z (Or.inr (htoUN z hz hin))
                        · obtain ⟨z0, hz0⟩ := hneIn
                          exact lt_of_lt_of_le
                            ((ha.2 z0 hz0).trans ((hinside z0 hz0).2 s hs)) hle
                  · exact hw.2.2.1 (place z) (Or.inr ⟨z, hmemL z hz, rfl⟩)
                · intro b hb; rcases hb with hb | ⟨z, hz, rfl⟩
                  · by_contra hnb
                    have hgt : b < w :=
                      lt_of_le_of_ne (le_of_not_gt hnb) (fun he => hwS (he ▸ hb.1))
                    refine hfillS hb.1 ⟨?_, ?_, ?_, ?_⟩
                    · intro hmem; rcases hmem with hLS | hP
                      · obtain ⟨s, hs, heq⟩ := hLS
                        obtain ⟨z0, hz0⟩ := hneIn
                        have hlt : (s : I) < b :=
                          ((hinside z0 hz0).1 s hs).trans (hb.2 z0 hz0)
                        exact lt_irrefl b (heq ▸ hlt)
                      · obtain ⟨z, hz, heq⟩ := hP
                        have hb' : b = place z := heq.symm
                        rcases hLN z hz with hin | ⟨s, hs, hle⟩
                        · exact lt_irrefl b (hb' ▸
                            hb.2 z (Or.inl (htoLN z hz hin)))
                        · obtain ⟨z0, hz0⟩ := hneIn
                          exact not_lt_of_ge (hb' ▸ hle)
                            (((hinside z0 hz0).1 s hs).trans (hb.2 z0 hz0))
                    · intro hmem
                      exact not_lt_of_gt hgt (hw.2.2.2 b hmem)
                    · intro c hc; rcases hc with ⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩
                      · obtain ⟨z0, hz0⟩ := hneIn
                        exact ((hinside z0 hz0).1 s hs).trans (hb.2 z0 hz0)
                      · rcases hLN z hz with hin | ⟨s, hs, hle⟩
                        · exact hb.2 z (Or.inl (htoLN z hz hin))
                        · obtain ⟨z0, hz0⟩ := hneIn
                          exact lt_of_le_of_lt hle
                            (((hinside z0 hz0).1 s hs).trans (hb.2 z0 hz0))
                    · intro c hc; rcases hc with ⟨s, hs, rfl⟩ | ⟨z, hz, rfl⟩
                      · exact hgt.trans (hw.2.2.2 s.val (Or.inl ⟨s, hs, rfl⟩))
                      · exact hgt.trans (hw.2.2.2 (place z) (Or.inr ⟨z, hz, rfl⟩))
                  · exact hw.2.2.2 (place z) (Or.inr ⟨z, hmemU z hz, rfl⟩)
              · intro ⟨w, hw⟩
                refine ⟨w, ?_⟩
                dsimp [strictSlot] at hw ⊢
                rw [hEnumL, hEnumU]
                refine ⟨?_, ?_, ?_, ?_⟩
                · intro hmem; rcases hmem with hmem | ⟨z, hz, rfl⟩
                  · exact hw.1 (Or.inl (hLSsub' hmem))
                  · rcases hLN z hz with hin | ⟨s, hs, hle⟩
                    · exact hw.1 (Or.inr ⟨z, htoLN z hz hin, rfl⟩)
                    · exact absurd (hw.2.2.1 s.val (Or.inl (hLSsub' ⟨s, hs, rfl⟩)))
                        (not_lt_of_ge hle)
                · intro hmem; rcases hmem with hmem | ⟨z, hz, rfl⟩
                  · exact hw.2.1 (Or.inl (hUSsub' hmem))
                  · rcases hUN z hz with hin | ⟨s, hs, hle⟩
                    · exact hw.2.1 (Or.inr ⟨z, htoUN z hz hin, rfl⟩)
                    · exact absurd (hw.2.2.2 s.val (Or.inl (hUSsub' ⟨s, hs, rfl⟩)))
                        (not_lt_of_ge hle)
                · intro a ha; rcases ha with ha | ⟨z, hz, rfl⟩
                  · exact hw.2.2.1 a (Or.inl (hLSsub' ha))
                  · rcases hLN z hz with hin | ⟨s, hs, hle⟩
                    · exact hw.2.2.1 (place z) (Or.inr ⟨z, htoLN z hz hin, rfl⟩)
                    · exact lt_of_le_of_lt hle
                        (hw.2.2.1 s.val (Or.inl (hLSsub' ⟨s, hs, rfl⟩)))
                · intro b hb; rcases hb with hb | ⟨z, hz, rfl⟩
                  · exact hw.2.2.2 b (Or.inl (hUSsub' hb))
                  · rcases hUN z hz with hin | ⟨s, hs, hle⟩
                    · exact hw.2.2.2 (place z) (Or.inr ⟨z, htoUN z hz hin, rfl⟩)
                    · exact lt_of_lt_of_le
                        (hw.2.2.2 s.val (Or.inl (hUSsub' ⟨s, hs, rfl⟩))) hle
            have hmemLY : ∀ z ∈ LNin, z ∈ LN := fun z hz => hz.1
            have hmemUY : ∀ z ∈ UNin, z ∈ UN := fun z hz => hz.1
            have hinsideX : ∀ z ∈ LNin ∪ UNin,
                (∀ s ∈ LS, (s : I) < placeX z) ∧ (∀ s ∈ US, placeX z < (s : I)) :=
              fun z hz => Or.elim hz (fun h => ⟨h.2.1, h.2.2⟩) (fun h => ⟨h.2.1, h.2.2⟩)
            have hinsideY : ∀ z ∈ LNin ∪ UNin,
                (∀ s ∈ LS, (s : I) < placeY z) ∧ (∀ s ∈ US, placeY z < (s : I)) :=
              fun z hz => (hinY z).mp (hinsideX z hz)
            exact
              (hred rfl hXL hXU hfillX
                (hsideLN placeX (fun z hz s hs =>
                  hltX (Sum.inr z) hz (Sum.inl s) hs))
                (hsideUN placeX (fun z hz s hs =>
                  hltX (Sum.inl s) hs (Sum.inr z) hz))
                hinsideX
                (fun z hz hin => ⟨hz, hin.1, hin.2⟩)
                (fun z hz hin => ⟨hz, hin.1, hin.2⟩)
                hmemLY hmemUY (hLSsub placeX hinsideX) (hUSsub placeX hinsideX)).trans
              (hjoint.trans
                (hred rfl hYL hYU hfillY
                  (hsideLN placeY (fun z hz s hs =>
                    hltY (Sum.inr z) hz (Sum.inl s) hs))
                  (hsideUN placeY (fun z hz s hs =>
                    hltY (Sum.inl s) hs (Sum.inr z) hz))
                  hinsideY
                  (fun z hz hin =>
                    ⟨hz, (hinY z |>.mpr hin).1, (hinY z |>.mpr hin).2⟩)
                  (fun z hz hin =>
                    ⟨hz, (hinY z |>.mpr hin).1, (hinY z |>.mpr hin).2⟩)
                  hmemLY hmemUY (hLSsub placeY hinsideY) (hUSsub placeY hinsideY)).symm)
        · exact iff_of_false (fun h => hpure (himpureX h)) (fun h => hpure (himpureY h))

/-- Fingerprint equality ⇒ parameter-fixing same orbit (Lemma 4.5 orbit step).

English route: equal soft records give matching diagrams on `S ⊕ newCanon.slt`; Theorem 3.5
yields an order auto fixing `S`; the induced presentation auto fixes parameters and matches
the tuples. Avoids equal joint `canonicalOfTuple` / `embedBelow` on distinct slot subtypes. -/
theorem equal_fingerprint_same_orbit_over_params {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) (δ : _root_.Ordinal.{u}) (χ σ : Cardinal.{u})
    (hδ : Order.IsSuccLimit δ) (hχ : aleph0 ≤ χ) (hσ : aleph0 ≤ σ) (hσle : σ ≤ χ)
    (hcf : χ < Ordinal.cof δ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (T : Set δ.ToType) (hT : #T ≤ χ) (S : Set I) (hS : #S ≤ χ)
    {P ι : Type u} (hP : #P ≤ χ) (hι : #ι ≤ σ) (hιχ : #ι ≤ χ)
    (p : P → (E.obj I).carrier) (xs ys : ι → (E.obj I).carrier)
    (hSp : paramSoftSupport E (Set.range p) ⊆ S)
    (hTS : ∀ s ∈ S, ∀ i ∈ hSupport (eISO.symm s), Ordinal.ToType.mk (asIio i) ∈ T)
    (hfp : (relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p xs).fingerprint =
        (relCodeOf E hχ hσ hσle eISO T hT S hS hP hι hιχ p ys).fingerprint) :
    SameOrbitOverParams K (E.obj I) (Set.range p) xs ys := by
  classical
  have hfp' :
      relFingerprintOf E hχ hσ eISO T hT S hS hι xs =
        relFingerprintOf E hχ hσ eISO T hT S hS hι ys := by
    simpa [relCodeOf] using hfp
  have hnc :
      canonicalOfTuple E hσ hι xs = canonicalOfTuple E hσ hι ys :=
    equal_fingerprint_equal_newCanon E hχ hσ hσle eISO T hT S hS hP hι hιχ p xs ys hfp
  let r : CanonicalRecord E.lab E.arity σ := canonicalOfTuple E hσ hι xs
  have hrY : canonicalOfTuple E hσ hι ys = r := hnc.symm
  let placeX : ↥r.slt → I := canonicalPlaceOfTuple E hσ hι xs
  let placeY : ↥r.slt → I := canonicalPlaceEq E hσ hι ys r hrY
  let enumX : ↥S ⊕ ↥r.slt → I := Sum.elim Subtype.val placeX
  let enumY : ↥S ⊕ ↥r.slt → I := Sum.elim Subtype.val placeY
  have hdiagOcc :=
    fingerprint_same_order_and_occupancy E hχ hσ eISO T hT S hS hι xs ys hTS hfp'
  have hdiagI : SameOrderDiagram enumX enumY := by
    simpa [enumX, enumY, placeX, placeY, r, hrY] using hdiagOcc.1
  have hoccI : SameSlotOccupancy enumX enumY := by
    simpa [enumX, enumY, placeX, placeY, r, hrY] using hdiagOcc.2
  let xsH : ULift.{u + 1} (↥S ⊕ ↥r.slt) → HOrder δ := fun i => eISO.symm (enumX i.down)
  let ysH : ULift.{u + 1} (↥S ⊕ ↥r.slt) → HOrder δ := fun i => eISO.symm (enumY i.down)
  have hrx0 := realizes_canonicalOfTuple E hσ hι xs
  have hry0 := realizes_canonical_eq E hσ hι ys r hrY
  have hdiag : SameOrderDiagram xsH ysH := by
    constructor
    · intro a b
      constructor
      · intro h
        have hpl : enumX a.down = enumX b.down := by
          have := congrArg eISO h
          simpa [xsH, OrderIso.apply_symm_apply] using this
        exact congrArg eISO.symm ((hdiagI.1 a.down b.down).mp hpl)
      · intro h
        have hpl : enumY a.down = enumY b.down := by
          have := congrArg eISO h
          simpa [ysH, OrderIso.apply_symm_apply] using this
        exact congrArg eISO.symm ((hdiagI.1 a.down b.down).mpr hpl)
    · intro a b
      rw [eISO.symm.lt_iff_lt, eISO.symm.lt_iff_lt, hdiagI.2 a.down b.down]
  have hocc : SameSlotOccupancy xsH ysH := by
    intro lower upper hlt1 hlt2
    let lower0 : Set (↥S ⊕ ↥r.slt) := ULift.down '' lower
    let upper0 : Set (↥S ⊕ ↥r.slt) := ULift.down '' upper
    have hlt1' : ∀ i ∈ lower0, ∀ j ∈ upper0, enumX i < enumX j := by
      intro i hi j hj
      obtain ⟨i', hi', rfl⟩ := hi; obtain ⟨j', hj', rfl⟩ := hj
      exact eISO.symm.lt_iff_lt.mp (hlt1 i' hi' j' hj')
    have hlt2' : ∀ i ∈ lower0, ∀ j ∈ upper0, enumY i < enumY j := by
      intro i hi j hj
      obtain ⟨i', hi', rfl⟩ := hi; obtain ⟨j', hj', rfl⟩ := hj
      exact eISO.symm.lt_iff_lt.mp (hlt2 i' hi' j' hj')
    have hPlaces := hoccI lower0 upper0 hlt1' hlt2'
    have hxL : xsH '' lower = eISO.symm '' (enumX '' lower0) := by
      change (fun i => eISO.symm (enumX i.down)) '' lower = _
      rw [← Set.image_comp, ← Set.image_comp]; rfl
    have hxU : xsH '' upper = eISO.symm '' (enumX '' upper0) := by
      change (fun i => eISO.symm (enumX i.down)) '' upper = _
      rw [← Set.image_comp, ← Set.image_comp]; rfl
    have hyL : ysH '' lower = eISO.symm '' (enumY '' lower0) := by
      change (fun i => eISO.symm (enumY i.down)) '' lower = _
      rw [← Set.image_comp, ← Set.image_comp]; rfl
    have hyU : ysH '' upper = eISO.symm '' (enumY '' upper0) := by
      change (fun i => eISO.symm (enumY i.down)) '' upper = _
      rw [← Set.image_comp, ← Set.image_comp]; rfl
    have hx : Occupied (xsH '' lower) (xsH '' upper) ↔
        Occupied (enumX '' lower0) (enumX '' upper0) := by
      rw [hxL, hxU]
      exact (occupied_orderIso eISO.symm (enumX '' lower0) (enumX '' upper0)).symm
    have hy : Occupied (ysH '' lower) (ysH '' upper) ↔
        Occupied (enumY '' lower0) (enumY '' upper0) := by
      rw [hyL, hyU]
      exact (occupied_orderIso eISO.symm (enumY '' lower0) (enumY '' upper0)).symm
    exact hx.trans (hPlaces.trans hy.symm)
  have hιU : #(ULift.{u + 1} (↥S ⊕ ↥r.slt)) ≤ lift.{u + 1} χ := by
    rw [mk_uLift, mk_sum, lift_id, lift_id]
    have hr : #(↥r.slt) ≤ σ := canonical_record_card_slot r
    exact lift_le.mpr <|
      (add_le_add hS (hr.trans hσle)).trans (le_of_eq (add_eq_self hχ))
  have hcfU : lift.{u + 1} χ < lift.{u + 1} (Ordinal.cof δ) := lift_lt.mpr hcf
  obtain ⟨φ, hφ⟩ :=
    (horder_orbit_iff δ χ hδ hχ hcfU
      (ι := ULift.{u + 1} (↥S ⊕ ↥r.slt)) hιU xsH ysH).mp ⟨hdiag, hocc⟩
  let ψ : I ≃o I := eISO.symm.trans (φ.trans eISO)
  have hψS (s : ↥S) : ψ s.val = s.val := by
    have := hφ ⟨Sum.inl s⟩
    dsimp [xsH, ysH, enumX, enumY] at this
    change eISO (φ (eISO.symm (s : I))) = (s : I)
    rw [this, OrderIso.apply_symm_apply]
  have hψplace (b : ↥r.slt) : ψ (placeX b) = placeY b := by
    have := hφ ⟨Sum.inr b⟩
    dsimp [xsH, ysH, enumX, enumY] at this
    change eISO (φ (eISO.symm (placeX b))) = placeY b
    rw [this, OrderIso.apply_symm_apply]
  let Φ := orderPresentationMapEquiv E ψ
  refine ⟨Φ, orderPresentationMapEquiv_strong E ψ, ?_, ?_⟩
  · intro q hq
    obtain ⟨a, rfl⟩ := hq
    have hpos (k : Fin (E.arity (supportTermOf E (p a)).label)) :
        (supportTermOf E (p a)).pos k ∈ S :=
      hSp <| Set.mem_iUnion₂.mpr ⟨p a, ⟨a, rfl⟩, Set.mem_range_self k⟩
    have hmap := E.realize_map ψ.toOrderEmbedding (supportTermOf E (p a))
    change E.map ψ.toOrderEmbedding (p a) = p a
    rw [← realize_supportTermOf E (p a), hmap]
    refine congrArg E.realize ?_
    exact SupportTerm.ext_of_label_eq rfl fun k => by
      change ψ ((supportTermOf E (p a)).pos k) =
        (supportTermOf E (p a)).pos (Fin.cast (congrArg E.arity rfl) k)
      simpa using hψS ⟨_, hpos k⟩
  · intro i
    -- Shared canon + `hψplace`: replay `same_record_sameAutOrbit` matching.
    change E.map ψ.toOrderEmbedding (xs i) = ys i
    let j : ↥r.idx := canonicalOfTupleIndexEquiv E hσ hι xs i
    have hxsi : xs i = canonicalTupleReindex E hσ hι xs j := by
      simp [j, canonicalTupleReindex, Equiv.symm_apply_apply]
    have hcast :
        cast (congrArg (fun u : Set (Below σ) => { x // x ∈ u })
            (congrArg CanonicalRecord.idx hrY))
          (canonicalOfTupleIndexEquiv E hσ hι ys i) = j := by
      have he := indexCast_eq E hσ hι xs ys hnc i
      -- `cast hnc j = e_i ys i`; apply `cast hrY` (`= hnc.symm`) to both sides.
      rw [← he]
      -- `cast hrY (cast hnc j) = j`
      simp [j, cast_cast]
    have hysi : ys i = canonicalTupleEq E hσ hι ys r hrY j := by
      have hy := canonicalTupleEq_apply E hσ hι ys r hrY i
      simpa [hcast] using hy.symm
    have hrx : RealizesOrbitRecord (I := I) E (CanonicalRecord.toOrbitRecord r)
        placeX (canonicalTupleReindex E hσ hι xs) := by
      simpa [r, placeX] using hrx0
    have hry : RealizesOrbitRecord (I := I) E (CanonicalRecord.toOrbitRecord r)
        placeY (canonicalTupleEq E hσ hι ys r hrY) := hry0
    obtain ⟨pos₁, hinc₁, hpos₁, hxs⟩ := hrx.2.2.1 j
    obtain ⟨pos₂, _hinc₂, hpos₂, hys⟩ := hry.2.2.1 j
    have hmap :=
      E.realize_map ψ.toOrderEmbedding
        ⟨(CanonicalRecord.toOrbitRecord r).label j, pos₁, hinc₁⟩
    have hposψ (a : Fin (E.arity ((CanonicalRecord.toOrbitRecord r).label j))) :
        ψ (pos₁ a) = pos₂ a := by
      rw [hpos₁ a, hpos₂ a]
      exact hψplace _
    rw [hxsi, hxs, hmap, hysi, hys]
    refine congrArg E.realize (SupportTerm.ext_of_label_eq rfl fun a => ?_)
    change (ψ ∘ pos₁) a = pos₂ (Fin.cast (congrArg E.arity rfl) a)
    simpa using hposψ a


/-- Cardinality bound on soft positions of a short tuple. -/
theorem tuplePositions_card_le {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] {ι : Type u} {σ : Cardinal.{u}}
    (hσ : aleph0 ≤ σ) (hι : #ι ≤ σ) (xs : ι → (E.obj I).carrier) :
    #(tuplePositions E xs) ≤ σ :=
  orbitRecordOfTuple_slot_card E hσ hι xs

/-- `σ ≤ χ` from the Lemma 4.5 cardinal arithmetic hypotheses. -/
theorem sigma_le_chi_of_lemma45 {σ χ : Cardinal.{u}} (hσ : aleph0 ≤ σ)
    (h2 : (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) : σ ≤ χ :=
  (cantor σ).le.trans <|
    (power_le_power_left two_ne_zero (cantor σ).le).trans h2

/-- Main soft-copy form of Lemma 4.5: ≤χ orbits over ≤χ parameters. -/
theorem orbits_over_params_soft {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    (σ χ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hpow : χ ^ σ = χ)
    (hχbound : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ)
    (δ : _root_.Ordinal.{u}) (hδ : Order.IsSuccLimit δ)
    (hcf : χ < Ordinal.cof δ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (P : Set (E.obj I).carrier) (hP : #P ≤ χ)
    {ι : Type u} (hι : #ι ≤ σ) :
    ∃ reps : Set (ι → (E.obj I).carrier), #reps ≤ χ ∧
      ∀ xs : ι → (E.obj I).carrier, ∃ ys ∈ reps,
        SameOrbitOverParams K (E.obj I) P xs ys := by
  classical
  have h2 : (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ :=
    (le_add_of_le_right (le_refl _)).trans hχbound
  have hχinf : aleph0 ≤ χ :=
    (le_trans hσ (cantor σ).le).trans <|
      (power_le_power_left two_ne_zero (cantor σ).le).trans h2
  have hσle : σ ≤ χ := sigma_le_chi_of_lemma45 hσ h2
  have hlab : #E.lab ≤ χ := by
    have : #E.lab ≤ ls K := by simpa [E.ell_eq] using E.lab_small
    exact this.trans ((le_add_of_le_left (le_refl _)).trans hχbound)
  let S : Set I := paramSoftSupport E P
  have hS : #S ≤ χ := paramSoftSupport_card E hχinf P hP
  let T : Set δ.ToType := ordinalSupportOf E eISO P
  have hT : #T ≤ χ := ordinalSupportOf_card E eISO hχinf P hP
  have hιχ : #ι ≤ χ := hι.trans hσle
  let fpOf (xs : ι → (E.obj I).carrier) :=
    relFingerprintOf E hχinf hσ eISO T hT S hS hι xs
  let F : Set (RelFingerprint E.lab E.arity σ χ) := Set.range fpOf
  have hF : #F ≤ χ :=
    (mk_set_le F).trans (mk_relFingerprint_le hlab hσ hχinf hpow h2)
  let sec : ↥F → ι → (E.obj I).carrier := fun f =>
    Classical.choose (Set.mem_range.mp f.property)
  have hsec (f : ↥F) : fpOf (sec f) = (f : RelFingerprint _ _ _ _) :=
    Classical.choose_spec (Set.mem_range.mp f.property)
  let reps : Set (ι → (E.obj I).carrier) := Set.range sec
  refine ⟨reps, (mk_range_le).trans hF, ?_⟩
  intro xs
  refine ⟨sec ⟨fpOf xs, ⟨xs, rfl⟩⟩, ⟨⟨fpOf xs, ⟨xs, rfl⟩⟩, rfl⟩, ?_⟩
  let p : ↥P → (E.obj I).carrier := fun x => x.1
  have hP' : #↥P ≤ χ := hP
  have hfp :
      (relCodeOf E hχinf hσ hσle eISO T hT S hS hP' hι hιχ p xs).fingerprint =
        (relCodeOf E hχinf hσ hσle eISO T hT S hS hP' hι hιχ p
          (sec ⟨fpOf xs, ⟨xs, rfl⟩⟩)).fingerprint := by
    dsimp [relCodeOf, fpOf]
    exact (hsec ⟨fpOf xs, ⟨xs, rfl⟩⟩).symm
  have hrng : Set.range p = P := Subtype.range_coe
  have hSp : paramSoftSupport E (Set.range p) ⊆ S := by
    simpa [hrng, S] using (subset_refl _)
  have hTS : ∀ s ∈ S, ∀ i ∈ hSupport (eISO.symm s),
      Ordinal.ToType.mk (asIio i) ∈ T := by
    intro s hs i hi
    simpa [hrng, T, S] using
      mem_ordinalSupportOf_of_paramSoftSupport E eISO P (by simpa [hrng, S] using hs) hi
  have horb :=
    equal_fingerprint_same_orbit_over_params E δ χ σ hδ hχinf hσ hσle hcf eISO T hT S hS
      hP' hι hιχ p xs (sec ⟨fpOf xs, ⟨xs, rfl⟩⟩) hSp hTS hfp
  simpa [hrng] using horb

/-- **Lemma 4.5** (Orbits over parameters), soft-presentation form with an EM functor. -/
theorem lemma_4_5_with_E (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (σ χ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hpow : χ ^ σ = χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) :
    ∃ κ0 : Cardinal.{u}, ∀ κ, κ0 ≤ κ → Categorical K κ →
      ∀ (M : Model K.τ), K.Mem M → Model.card M = κ →
        ∀ P : Set M.carrier, #P ≤ χ →
          ∀ {ι : Type u}, #ι ≤ σ →
            ∃ reps : Set (ι → M.carrier), #reps ≤ χ ∧
              ∀ xs : ι → M.carrier, ∃ ys ∈ reps,
                ∃ e : M.carrier ≃[K.τ] M.carrier,
                  K.Strong e.toEmbedding ∧ (∀ p ∈ P, e p = p) ∧ ∀ i, e (xs i) = ys i := by
  classical
  have h2 : (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ :=
    (le_add_of_le_right (le_refl _)).trans hχ
  have hχinf : aleph0 ≤ χ :=
    (le_trans hσ (cantor σ).le).trans <|
      (power_le_power_left two_ne_zero (cantor σ).le).trans h2
  let κ0 := max (ls K) (Order.succ χ)
  refine ⟨κ0, fun κ hκ0 hcat M hM hMcard P hP ι hι => ?_⟩
  have hle : max (ls K) (Order.succ χ) ≤ κ := hκ0
  let soft := catSoftIndex K E χ κ hχinf hle hcat
  have hδlim := categoricityOrdinal_isSuccLimit (κ := κ) (θ := χ) hχinf
  have hδcof := categoricityOrdinal_cof (κ := κ) (θ := χ) hχinf
  have hcf : χ < Ordinal.cof (categoricityOrdinal κ χ) := by
    rw [hδcof]; exact Order.lt_succ χ
  let φ : M.carrier ≃[K.τ] (E.obj soft.I).carrier :=
    Classical.choice (hcat.unique_model M (E.obj soft.I) hM soft.mem hMcard soft.card_eq)
  have hPφ : #(φ '' P) ≤ χ := (mk_image_le).trans hP
  obtain ⟨reps0, hreps0, horb0⟩ :=
    orbits_over_params_soft E σ χ hσ hpow hχ
      (categoricityOrdinal κ χ) hδlim hcf soft.e (φ '' P) hPφ hι
  let reps : Set (ι → M.carrier) := (fun ys => φ.symm ∘ ys) '' reps0
  refine ⟨reps, (mk_image_le).trans hreps0, ?_⟩
  intro xs
  obtain ⟨ys0, hys0, hsame⟩ := horb0 (φ ∘ xs)
  refine ⟨φ.symm ∘ ys0, Set.mem_image_of_mem _ hys0, ?_⟩
  refine (sameOrbitOverParams_congr K hM φ P xs (φ.symm ∘ ys0)).mpr ?_
  have hys0' : φ ∘ φ.symm ∘ ys0 = ys0 := by
    funext i; exact φ.apply_symm_apply (ys0 i)
  simpa [hys0'] using hsame
end
end AEC
