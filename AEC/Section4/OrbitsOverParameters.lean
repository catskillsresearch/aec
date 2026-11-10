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
public import Mathlib.SetTheory.Cardinal.Rat

/-!
# Lemma 4.5 — orbits over parameters (WIP / blocked)

Relative codes (`RelCode`) of cardinality `≤ χ` and the Thm 3.5 wrapper
`same_joint_canon_fixes_params` are in place. **Blocked:** equal `RelCode`s do not yet
imply equal joint `canonicalOfTuple` (see board infra `infra_relcode_joint_canonical`,
`infra_relcode_orbit_record`). Do not import into `Results` until that bridge compiles.
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
    rw [mk_finsupp_of_infinite, mk_ord_toType, mk_int]
    exact max_eq_left (natCast_le_aleph0.trans hχ)
  haveI : Infinite (Below χ →₀ ℤ) := by
    rw [infinite_iff, h1]; exact hχ
  rw [mk_finsupp_of_infinite, h1, mk_rat]
  exact max_eq_left (natCast_le_aleph0.trans hχ)

/-- Relative record over fixed parameter support (English Lemma 4.5). -/
structure RelCode (lab : Type u) (arity : lab → ℕ) (σ χ : Cardinal.{u}) where
  canon : CanonicalRecord lab arity σ
  soft : Below σ → AbstractPoint χ
  eqOld : Below σ → Option (Below χ)
  occ : Set (Below σ) → Set (Below σ) → Bool

theorem mk_relCode_le {lab : Type u} {arity : lab → ℕ} {σ χ : Cardinal.{u}}
    (hlab : #lab ≤ χ) (hσ : aleph0 ≤ σ) (hχinf : aleph0 ≤ χ) (hpow : χ ^ σ = χ)
    (h2 : (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) :
    #(RelCode lab arity σ χ) ≤ χ := by
  classical
  let e : RelCode lab arity σ χ ≃
      CanonicalRecord lab arity σ × (Below σ → AbstractPoint χ) ×
        (Below σ → Option (Below χ)) × (Set (Below σ) → Set (Below σ) → Bool) :=
    ⟨fun c => (c.canon, c.soft, c.eqOld, c.occ),
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
  let f : RealizedCut S → Option ↥S := fun C =>
    let rest : Set ↥S := {s | s ∉ C.1}
    if h : rest.Nonempty then some (WellFounded.min wellFounded_lt rest h) else none
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
            {s : ↥S | (s : α) < (WellFounded.min wellFounded_lt rest h : α)}
          else univ := by
      set rest : Set ↥S := {s | s ∉ C.1}
      by_cases h : rest.Nonempty
      · simp only [h, ↓reduceDIte]
        ext s
        have omit : ∀ t ∈ rest, x ≤ (t : α) := by
          intro t ht
          exact le_of_not_gt fun hlt =>
            (show t ∉ C.1 from ht) (by simpa [hx] using hlt)
        constructor
        · intro hs
          exact lt_of_lt_of_le (by simpa [hx] using hs)
            (omit _ (WellFounded.min_mem wellFounded_lt rest h))
        · intro hs
          by_contra hsC
          exact (WellFounded.not_lt_min wellFounded_lt rest h (by simpa using hsC))
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
  exact (mk_le_of_injective hinj).trans (by rw [mk_option]; exact le_rfl)

noncomputable def cutOverWell {χ : Cardinal.{u}} (hχ : aleph0 ≤ χ)
    {α : Type u} [LinearOrder α] [WellFoundedLT α] (S : Set α) (hS : #S ≤ χ) (x : α) :
    Below χ := by
  classical
  have hcuts : #(RealizedCut S) ≤ χ :=
    (mk_realizedCut_le (S := S)).trans <|
      (add_le_add ((Cardinal.mk_subtype_le S).trans hS) (one_le_aleph0.trans hχ)).trans
        (le_of_eq (add_eq_self hχ))
  exact (embedBelow hcuts).1 ⟨{s : ↥S | (s : α) < x}, ⟨x, rfl⟩⟩

/-- Push an `H(δ)` point to an `AbstractPoint` by renaming ordinals via cuts over `T`. -/
noncomputable def abstractify {δ : _root_.Ordinal.{u}} {χ : Cardinal.{u}}
    (hχ : aleph0 ≤ χ) (T : Set δ.ToType) (hT : #T ≤ χ) (y : HOrder δ) :
    AbstractPoint χ := by
  classical
  letI : DecidableEq (OrdIndex δ) := Classical.decEq _
  letI : DecidableEq (Below χ) := Classical.decEq _
  letI : LinearOrder δ.ToType := inferInstance
  letI : WellFoundedLT δ.ToType := inferInstance
  let rename : OrdIndex δ → Below χ := fun i =>
    cutOverWell (α := δ.ToType) hχ T hT (Ordinal.ToType.mk (asIio i))
  let pushG : Gamma δ → (Below χ →₀ ℤ) := fun g =>
    (ofColex g).mapDomain rename
  exact (ofColex y).mapDomain pushG

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

/-- Relative code of a `σ`-tuple over fixed parameters in a soft copy. -/
noncomputable def relCodeOf {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {δ : _root_.Ordinal.{u}} {χ σ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hσ : aleph0 ≤ σ)
    {I : Type u} [LinearOrder I] [Nonempty I] (eISO : HOrder δ ≃o I)
    (T : Set δ.ToType) (hT : #T ≤ χ)
    (S : Set I) (hS : #S ≤ χ)
    {ι : Type u} (hι : #ι ≤ σ) (xs : ι → (E.obj I).carrier) :
    RelCode E.lab E.arity σ χ := by
  classical
  let eS := embedBelow hS
  let places : ι → I := fun i =>
    -- representative soft place: first argument position of the realizing term, if any;
    -- fall back via choice on the finite support
    let t := supportTermOf E (xs i)
    t.pos ⟨0, E.arity_pos t.label⟩
  let softPlaces : ι → HOrder δ := fun i => eISO.symm (places i)
  refine {
    canon := canonicalOfTuple E hσ hι xs
    soft := fun b =>
      if hb : b ∈ range (embedBelow hι) then
        abstractify hχ T hT (softPlaces ((embedBelow hι).symm ⟨b, hb⟩))
      else 0
    eqOld := fun b =>
      if hb : b ∈ range (embedBelow hι) then
        let pl := places ((embedBelow hι).symm ⟨b, hb⟩)
        if hmem : pl ∈ S then some (eS ⟨pl, hmem⟩) else none
      else none
    occ := occTable hι (fun i => softPlaces i)
  }

/-- Cardinality bound on soft positions of a short tuple. -/
theorem tuplePositions_card_le {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] [Nonempty I] {ι : Type u} {σ : Cardinal.{u}}
    (hσ : aleph0 ≤ σ) (hι : #ι ≤ σ) (xs : ι → (E.obj I).carrier) :
    #(tuplePositions E xs) ≤ σ :=
  orbitRecordOfTuple_slot_card E hσ hι xs

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
  have hell : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hχinf : aleph0 ≤ χ := hell.trans (le_trans le_self_add hχbound)
  have h2 : (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ :=
    (le_add_left _ _).trans hχbound
  have hlab : #E.lab ≤ χ := by
    have := E.lab_small
    rw [E.ell_eq] at this
    exact this.trans (le_trans le_self_add hχbound)
  have hιχ : #ι ≤ χ := hι.trans <| by
    have hσχ : σ ≤ χ := by
      have : σ ≤ (2 : Cardinal) ^ σ := (cantor σ).le
      exact this.trans <|
        (power_le_power_left two_ne_zero (cantor σ).le).trans h2 |> fun h =>
          (cantor σ).le.trans h
    -- σ ≤ 2^σ ≤ 2^{2^σ} ≤ χ
    have h1 : σ ≤ (2 : Cardinal) ^ σ := (cantor σ).le
    have h2' : (2 : Cardinal) ^ σ ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ σ) :=
      power_le_power_left two_ne_zero (cantor σ).le
    exact h1.trans (h2'.trans h2)
  let S : Set I := paramSoftSupport E P
  have hS : #S ≤ χ := paramSoftSupport_card E hχinf P hP
  let T : Set δ.ToType := ordinalSupportOf E eISO P
  have hT : #T ≤ χ := ordinalSupportOf_card E eISO hχinf P hP
  -- Enumerate parameters for joint soft canons.
  let Pα : Type u := ↥P
  have hPα : #Pα ≤ χ := (mk_subtype_le P).trans hP
  let pEnum : Pα → (E.obj I).carrier := fun x => x.1
  let code : (ι → (E.obj I).carrier) → RelCode E.lab E.arity σ χ := fun xs =>
    relCodeOf E hχinf hσ eISO T hT S hS hι xs
  have hcode_le : #(RelCode E.lab E.arity σ χ) ≤ χ :=
    mk_relCode_le (arity := E.arity) hlab hσ hχinf hpow h2
  -- Representatives: one tuple per realized relative code, via choice on the fiber.
  let realized : Set (RelCode E.lab E.arity σ χ) :=
    {c | ∃ xs : ι → (E.obj I).carrier, code xs = c}
  have hreal : #realized ≤ χ :=
    (mk_le_mk_of_subset (fun _ _ => trivial)).trans hcode_le
  -- Pick a representative for each realized code.
  let repOf : RelCode E.lab E.arity σ χ → ι → (E.obj I).carrier := fun c =>
    if h : ∃ xs, code xs = c then Classical.choose h else fun _ =>
      Classical.choice (by
        have : Nonempty (E.obj I).carrier :=
          (E.realize_surjective (I := I)).nonempty
        inferInstance)
  let reps : Set (ι → (E.obj I).carrier) :=
    repOf '' realized
  have hreps : #reps ≤ χ := (mk_image_le).trans hreal
  refine ⟨reps, hreps, fun xs => ?_⟩
  refine ⟨repOf (code xs), ⟨code xs, ⟨xs, rfl⟩, rfl⟩, ?_⟩
  -- Equal codes ⇒ same joint soft canon on (params ⊕ tuple) ⇒ same orbit fixing params.
  -- Use the joint soft canon comparison; relative codes agree so the new soft data and the
  -- fixed parameter part determine the same joint `canonicalOfTuple`.
  have hcode_eq : code (repOf (code xs)) = code xs := by
    have hex : ∃ ys, code ys = code xs := ⟨xs, rfl⟩
    simp only [repOf, dite_eq_left hex]
    exact Classical.choose_spec hex
  -- Fall back through joint soft canons at bound `χ` (params ⊕ tuple).
  -- Two tuples with the same relative code share the same new soft canon and the same
  -- abstract soft fingerprints / occupancy over the fixed parameter support; the joint
  -- soft presentation record is therefore identical, so Theorem 3.5 applies.
  have hjoint : #(Pα ⊕ ι) ≤ χ := joint_card hχinf hPα hιχ
  -- Show equal relative codes give equal joint canons by transporting through the shared
  -- soft-place diagram fixed by the relative data.
  have hcan :
      canonicalOfTuple E hχinf hjoint (Sum.elim pEnum xs) =
        canonicalOfTuple E hχinf hjoint (Sum.elim pEnum (repOf (code xs))) := by
    -- Both tuples realize soft configurations with identical relative codes over `T`.
    -- The soft joint record depends only on labels (from `canon`) and the order/occupancy
    -- pattern of parameter soft support together with new places (from `soft`/`eqOld`/`occ`).
    -- Equality of those data forces equality of `canonicalOfTuple` on the joint index.
    --
    -- Implementation: compare via `same_canonical` after noting `code` equality rewrites.
    cases hcode_eq
    -- When the representative equals `xs` up to the code fiber, reduce to reflexivity if
    -- `repOf (code xs)` was chosen as `xs`; otherwise use that any two fiber elements with
    -- equal codes are linked by a parameter-fixing auto, which preserves joint canons.
    -- Direct approach: apply `same_joint_canon` after establishing canon equality from fiber.
    rfl
  have horb := same_joint_canon_fixes_params E δ χ hδ hχinf hcf eISO hPα hιχ
    pEnum xs (repOf (code xs)) hcan
  -- Range of `pEnum` is `P`.
  have hrangep : Set.range pEnum = P := by
    ext z; constructor
    · rintro ⟨⟨z', hz'⟩, rfl⟩; exact hz'
    · intro hz; exact ⟨⟨z, hz⟩, rfl⟩
  simpa [SameOrbitOverParams, hrangep] using horb

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
  have hell : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hχinf : aleph0 ≤ χ := hell.trans (le_trans le_self_add hχ)
  let κ0 : Cardinal.{u} := max (ls K) (Order.succ χ)
  refine ⟨κ0, fun κ hκ0 hcat M hM hMcard P hP ι hι => ?_⟩
  have hle : max (ls K) (Order.succ χ) ≤ κ := hκ0
  let soft := catSoftIndex K E χ κ hχinf hle hcat
  let I := soft.I
  let δ := categoricityOrdinal κ χ
  have hδlim := categoricityOrdinal_isSuccLimit (κ := κ) (θ := χ) hχinf
  have hδcof := categoricityOrdinal_cof (κ := κ) (θ := χ) hχinf
  have hcf : χ < Ordinal.cof δ := by rw [hδcof]; exact Order.lt_succ χ
  obtain ⟨φ⟩ := hcat.unique_model M (E.obj I) hM soft.mem hMcard soft.card_eq
  let P' : Set (E.obj I).carrier := φ '' P
  have hP' : #P' ≤ χ := (mk_image_le).trans hP
  obtain ⟨reps', hreps', hcov'⟩ :=
    orbits_over_params_soft E σ χ hσ hpow hχ δ hδlim hcf soft.e P' hP' hι
  let reps : Set (ι → M.carrier) :=
    (fun ys' : ι → (E.obj I).carrier => φ.symm ∘ ys') '' reps'
  refine ⟨reps, (mk_image_le).trans hreps', fun xs => ?_⟩
  obtain ⟨ys', hys', horb'⟩ := hcov' (φ ∘ xs)
  refine ⟨φ.symm ∘ ys', ⟨ys', hys', rfl⟩, ?_⟩
  have horb := (sameOrbitOverParams_congr K hM φ P xs (φ.symm ∘ ys')).mpr ?_
  · obtain ⟨e, heS, heP, he⟩ := horb
    exact ⟨e, heS, heP, he⟩
  · -- transport: P' = φ '' P, and φ ∘ (φ.symm ∘ ys') = ys'
    have hys : (φ ∘ (φ.symm ∘ ys')) = ys' := by
      ext i; exact φ.apply_symm_apply (ys' i)
    have hPeq : φ '' P = P' := rfl
    simpa [hys, hPeq, Function.comp] using horb'

end
end AEC
