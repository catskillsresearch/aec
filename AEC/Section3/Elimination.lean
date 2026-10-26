module

public import AEC.Section3.Profile
public import AEC.Section3.Alignment
public import AEC.Section3.OrbitArrow
public import AEC.Section3.OrbitName
public import AEC.Section3.Reversal
public import AEC.Section3.OrbitRecordBound
public import AEC.Section3.AdditivelyIndecomposable
public import AEC.Section3.UniformOrbitBound
public import AEC.Section2.Presentation
public import AEC.Section2.OrderPresentation
public import AEC.Section2.SmallModel
public import AEC.Section2.DirectedLimit
public import AEC.Section1.ArbitrarilyLarge
public import AEC.Section1.Categorical
public import AEC.Section1.LoewenheimSkolem
public import AEC.Section1.OrdinalChain
public import AEC.Section1.ChainUnion
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Pigeonhole
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal Set

set_option linter.unusedVariables false

/-! ### Exact length and arrow symmetry (text.md 178–178) -/

/-- At a categoricity cardinal, reversal is equivalent to symmetry of `OrbitArrow` on
tuples of length at most `θ`. -/
theorem reversalProperty_iff_orbitArrow_symmetric (K : AbstractElementaryClass.{u})
    (θ κ : Cardinal.{u}) :
    ReversalProperty K θ κ ↔
      ∀ (M : Model K.τ) {ι : Type u} (xs ys : ι → M.carrier),
        K.Mem M → Model.card M = κ → #ι ≤ θ →
          OrbitArrow K M xs ys → OrbitArrow K M ys xs := by
  constructor
  · intro hrev M ι xs ys hM hcard hι ⟨f, hfS, hf⟩
    obtain ⟨g, hgS, hg⟩ := hrev M f xs hM hcard hfS hι
    exact ⟨g, hgS, fun i => by rw [← hf i]; exact hg i⟩
  · intro hsym M f ι xs hM hcard hfS hι
    exact hsym M xs (fun i => f (xs i)) hM hcard hι ⟨f, hfS, fun _ => rfl⟩

/-- It suffices to treat length exactly `θ`: pad a nonempty shorter tuple by a surjection
from a type of cardinality `θ`, and use the identity for the empty tuple. -/
theorem reversalProperty_of_exact_length (K : AbstractElementaryClass.{u})
    (θ κ : Cardinal.{u}) (hθ : aleph0 ≤ θ)
    (hexact : ∀ (M : Model K.τ) (f : Language.Embedding K.τ M.carrier M.carrier)
      {ι : Type u} (xs : ι → M.carrier),
      K.Mem M → Model.card M = κ → K.Strong f → #ι = θ →
        ∃ g : Language.Embedding K.τ M.carrier M.carrier,
          K.Strong g ∧ ∀ i, g (f (xs i)) = xs i) :
    ReversalProperty K θ κ := by
  intro M f ι xs hM hc hfS hι
  by_cases hne : Nonempty ι
  · have hex : ∃ (β : Type u) (e : β → ι), #β = θ ∧ Function.Surjective e := by
      refine ⟨Below θ ⊕ ι, Sum.elim (fun _ => Classical.choice hne) id, ?_, ?_⟩
      · have hsum : #(Below θ ⊕ ι) = θ + #ι := by
          rw [mk_sum, mk_ord_toType, lift_id, lift_id]
        rw [hsum, add_eq_left hθ hι]
      · intro i; exact ⟨Sum.inr i, rfl⟩
    obtain ⟨β, e, hβ, hsurj⟩ := hex
    let ys : β → M.carrier := fun b => xs (e b)
    obtain ⟨g, hgS, hg⟩ := hexact M f ys hM hc hfS hβ
    refine ⟨g, hgS, fun i => ?_⟩
    obtain ⟨b, hb⟩ := hsurj i
    simpa [ys, hb] using hg b
  · refine ⟨Language.Embedding.refl _ _, K.strong_refl M hM, fun i => ?_⟩
    exact (not_nonempty_iff.mp hne).elim i

/-- Failure of reversal yields an asymmetric orbit arrow. -/
theorem exists_asymmetric_orbitArrow (K : AbstractElementaryClass.{u})
    (θ κ : Cardinal.{u}) (hFail : FailsReversal K θ κ) :
    ∃ (M : Model K.τ) (hM : K.Mem M) (_hc : Model.card M = κ)
      (ι : Type u) (xs ys : ι → M.carrier),
      #ι ≤ θ ∧ OrbitArrow K M xs ys ∧ ¬ OrbitArrow K M ys xs := by
  have hnot : ¬ ReversalProperty K θ κ := hFail.2
  rw [reversalProperty_iff_orbitArrow_symmetric] at hnot
  push Not at hnot
  obtain ⟨M, ι, xs, ys, hM, hcard, hι, harrow, hno⟩ := hnot
  exact ⟨M, hM, hcard, ι, xs, ys, hι, harrow, hno⟩

/-! ### Profile palette and failing sequence (text.md 180–186) -/

/-- Profile palette bound `P = 2^{B(ℓ,θ)}` from the Theorem 3.11 proof. -/
noncomputable def profilePaletteBound (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u}) :
    Cardinal.{u} :=
  (2 : Cardinal.{u}) ^ orbitRecordBound (ls K) θ

theorem profilePaletteBound_aleph0_le (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (_hθ : aleph0 ≤ θ) : aleph0 ≤ profilePaletteBound K θ := by
  have hell : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hsum : aleph0 ≤ ls K + θ := le_add_of_le_left hell
  have hB : aleph0 ≤ orbitRecordBound (ls K) θ := by
    dsimp [orbitRecordBound]
    have hinner : aleph0 ≤ (2 : Cardinal.{u}) ^ (ls K + θ) :=
      le_trans (cantor (aleph0 : Cardinal.{u})).le (power_le_power_left two_ne_zero hsum)
    have hpow : (2 : Cardinal.{u}) ^ (aleph0 : Cardinal.{u}) ≤
        (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ls K + θ)) :=
      power_le_power_left two_ne_zero hinner
    exact le_trans (cantor (aleph0 : Cardinal.{u})).le hpow
  dsimp [profilePaletteBound]
  exact le_trans (cantor (aleph0 : Cardinal.{u})).le (power_le_power_left two_ne_zero hB)

/-- From unboundedly many failing categoricity cardinals, models are arbitrarily large. -/
theorem arbitrarilyLarge_of_unbounded_fails (K : AbstractElementaryClass.{u})
    (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ) :
    ArbitrarilyLarge K :=
  ⟨fun bound => by
    obtain ⟨κ, hFail, hlt⟩ := hUnb bound
    obtain ⟨M, hM, hcard⟩ := hFail.1.exists_model
    exact ⟨M, hM, hlt.le.trans (le_of_eq hcard.symm)⟩⟩

/-- Above any bound there is a failing categoricity cardinal large enough for the next stage. -/
theorem exists_fail_above (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    (B : Cardinal.{u}) :
    ∃ κ, FailsReversal K θ κ ∧
      B < κ ∧ max (ls K) (Order.succ θ) ≤ κ ∧ profilePaletteBound K θ < κ := by
  let bound := max B (max (max (ls K) (Order.succ θ)) (profilePaletteBound K θ))
  obtain ⟨κ, hFail, hlt⟩ := hUnb (Order.succ bound)
  have hbig : bound < κ := (Order.lt_succ bound).trans hlt
  refine ⟨κ, hFail, (le_max_left B _).trans_lt hbig, ?_, ?_⟩
  · have h1 : max (ls K) (Order.succ θ) ≤ bound :=
      (le_max_left _ _).trans (le_max_right B _)
    exact h1.trans hbig.le
  · have h1 : profilePaletteBound K θ ≤ bound :=
      (le_max_right _ _).trans (le_max_right B _)
    exact lt_of_le_of_lt h1 hbig

/-- Bound on earlier values of a failing sequence: successors and `θ`-powers (text.md 182). -/
noncomputable def failingPriorBound {α : Type u} (θ : Cardinal.{u})
    (rec : α → Cardinal.{u}) : Cardinal.{u} :=
  Cardinal.sum fun a : α => Order.succ (max (rec a) (rec a ^ θ))

/-- Recursively choose a strictly increasing `P⁺`-sequence of failing categoricity cardinals. -/
noncomputable def failingSequence (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ) :
    Below (Order.succ (profilePaletteBound K θ)) → Cardinal.{u} :=
  WellFounded.fix (inferInstance : WellFounded ((· < ·) :
      Below (Order.succ (profilePaletteBound K θ)) → _ → Prop))
    (fun i rec =>
      Classical.choose (exists_fail_above K θ hUnb
        (failingPriorBound θ fun j : {j : Below (Order.succ (profilePaletteBound K θ)) // j < i} =>
          rec j.1 j.2)))

theorem failingSequence_eq (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    (i : Below (Order.succ (profilePaletteBound K θ))) :
    failingSequence K θ hUnb i =
      Classical.choose (exists_fail_above K θ hUnb
        (failingPriorBound θ fun j : {j : Below (Order.succ (profilePaletteBound K θ)) // j < i} =>
          failingSequence K θ hUnb j.1)) := by
  unfold failingSequence
  exact WellFounded.fix_eq _ _ i

theorem failingSequence_spec (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    (i : Below (Order.succ (profilePaletteBound K θ))) :
    FailsReversal K θ (failingSequence K θ hUnb i) ∧
      max (ls K) (Order.succ θ) ≤ failingSequence K θ hUnb i ∧
      profilePaletteBound K θ < failingSequence K θ hUnb i := by
  rw [failingSequence_eq]
  have h := Classical.choose_spec (exists_fail_above K θ hUnb
    (failingPriorBound θ fun j : {j // j < i} => failingSequence K θ hUnb j.1))
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

theorem failingSequence_strict (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    {i j : Below (Order.succ (profilePaletteBound K θ))} (hij : i < j) :
    failingSequence K θ hUnb i < failingSequence K θ hUnb j := by
  rw [failingSequence_eq K θ hUnb j]
  have h := Classical.choose_spec (exists_fail_above K θ hUnb
    (failingPriorBound θ fun k : {k // k < j} => failingSequence K θ hUnb k.1))
  have hle : failingSequence K θ hUnb i ≤
      failingPriorBound θ fun k : {k // k < j} => failingSequence K θ hUnb k.1 := by
    dsimp [failingPriorBound]
    exact (le_max_left _ _).trans <| (Order.le_succ _).trans
      (Cardinal.le_sum (fun k : {k // k < j} =>
        Order.succ (max (failingSequence K θ hUnb k.1)
          (failingSequence K θ hUnb k.1 ^ θ))) ⟨i, hij⟩)
  exact lt_of_le_of_lt hle h.2.1

/-- Later sequence values dominate `θ`-powers of earlier ones (text.md 182). -/
theorem failingSequence_power_le (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    {i j : Below (Order.succ (profilePaletteBound K θ))} (hij : i < j) :
    failingSequence K θ hUnb i ^ θ ≤ failingSequence K θ hUnb j := by
  rw [failingSequence_eq K θ hUnb j]
  have h := Classical.choose_spec (exists_fail_above K θ hUnb
    (failingPriorBound θ fun k : {k // k < j} => failingSequence K θ hUnb k.1))
  have hle : failingSequence K θ hUnb i ^ θ ≤
      failingPriorBound θ fun k : {k // k < j} => failingSequence K θ hUnb k.1 := by
    dsimp [failingPriorBound]
    exact (le_max_right _ _).trans <| (Order.le_succ _).trans
      (Cardinal.le_sum (fun k : {k // k < j} =>
        Order.succ (max (failingSequence K θ hUnb k.1)
          (failingSequence K θ hUnb k.1 ^ θ))) ⟨i, hij⟩)
  exact hle.trans h.2.1.le

/-- Named orbit arrow at exact length `θ` (index `Below θ`), for profile comparison. -/
def NamedArrow (K : AbstractElementaryClass.{u}) (θ κ : Cardinal.{u})
    (N : OrbitNaming K θ) (p r : OrbitName K θ) : Prop :=
  ∃ (M : Model K.τ) (hM : K.Mem M) (_hc : Model.card M = κ)
      (xs ys : Below θ → M.carrier),
    N.name hM xs (by rw [mk_ord_toType]) = p ∧
      N.name hM ys (by rw [mk_ord_toType]) = r ∧ OrbitArrow K M xs ys

theorem namedArrow_refl (K : AbstractElementaryClass.{u}) (θ κ : Cardinal.{u})
    (N : OrbitNaming K θ) (p : OrbitName K θ)
    (hp : ∃ (M : Model K.τ) (hM : K.Mem M), Model.card M = κ ∧
      ∃ (xs : Below θ → M.carrier), N.name hM xs (by rw [mk_ord_toType]) = p) :
    NamedArrow K θ κ N p p := by
  obtain ⟨M, hM, hc, xs, hxs⟩ := hp
  exact ⟨M, hM, hc, xs, xs, hxs, hxs,
    ⟨Language.Embedding.refl _ _, K.strong_refl M hM, fun _ => rfl⟩⟩

/-- A copy of `C_a` with no name-`p` θ-tuple contradicts occurrence of `p` (text.md 200–201). -/
theorem killed_copy_impossible (K : AbstractElementaryClass.{u})
    (θ a : Cardinal.{u}) (N : OrbitNaming K θ)
    (hcat : Categorical K a) (p : OrbitName K θ)
    (hp : ∃ (M : Model K.τ) (hM : K.Mem M), Model.card M = a ∧
      ∃ (ι : Type u) (hι : #ι ≤ θ) (xs : ι → M.carrier), N.name hM xs hι = p)
    (hkill : ∃ (A : Model K.τ) (hA : K.Mem A), Model.card A = a ∧
      ∀ {ι : Type u} (hι : #ι ≤ θ) (xs : ι → A.carrier), N.name hA xs hι ≠ p) :
    False := by
  obtain ⟨A, hA, hAcard, hno⟩ := hkill
  obtain ⟨M, hM, hMcard, ι, hι, xs, hxs⟩ := hp
  obtain ⟨φ⟩ := hcat.unique_model M A hM hA hMcard hAcard
  have : N.name hA (fun i => φ (xs i)) hι = p := by
    rw [← N.name_iso φ hM hA xs hι, hxs]
  exact (hno hι (fun i => φ (xs i))) this

/-- Alignment package matching the conclusion of Proposition 3.9. -/
def AlignmentProperty (K : AbstractElementaryClass.{u}) (θ a μ : Cardinal.{u})
    (N : OrbitNaming K θ) : Prop :=
  ∀ (M : Model K.τ) (hM : K.Mem M), Model.card M = μ →
    ∀ S : Set M.carrier, #S ≤ a →
      ∃ (A : Model K.τ) (f : Language.Embedding K.τ A.carrier M.carrier) (hA : K.Mem A),
        K.Strong f ∧ Model.card A = a ∧
        (∀ x ∈ S, ∃ y, f y = x) ∧
        ∀ {ι : Type u} (hι : #ι ≤ θ) (xs : ι → A.carrier),
          N.name hA xs hι = N.name hM (fun i => f (xs i)) hι

/-! ### Orbit naming from an order presentation (text.md 128–128) -/

/-- Fixed injection of canonical records into the name set `B(ℓ, θ)`. -/
noncomputable def recordNameEmb (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) :
    CanonicalRecord E.lab E.arity θ ↪ OrbitName K θ := by
  classical
  have hell : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hlab : #E.lab ≤ ls K := by simpa [E.ell_eq] using E.lab_small
  have hR : #(CanonicalRecord E.lab E.arity θ) ≤ orbitRecordBound (ls K) θ :=
    mk_canonicalRecord_le_orbitRecordBound (arity := E.arity) θ (ls K) hlab hθ hell
  have hBelow : #(OrbitName K θ) = orbitRecordBound (ls K) θ := by
    dsimp [OrbitName, Below]; exact mk_ord_toType _
  have : #(CanonicalRecord E.lab E.arity θ) ≤ #(OrbitName K θ) := by
    rw [hBelow]; exact hR
  exact Classical.choice ((Cardinal.le_def _ _).mp this)

/-- Soft presentation of the unique model of a large categoricity cardinal. -/
structure CatSoftIndex (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ κ : Cardinal.{u}) where
  I : Type u
  lin : LinearOrder I
  non : Nonempty I
  e : HOrder (categoricityOrdinal κ θ) ≃o I
  card_eq : Model.card (E.obj I) = κ
  mem : K.Mem (E.obj I)

attribute [instance] CatSoftIndex.lin CatSoftIndex.non

noncomputable def catSoftIndex (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ κ : Cardinal.{u}) (hθ : aleph0 ≤ θ)
    (hle : max (ls K) (Order.succ θ) ≤ κ) (_hcat : Categorical K κ) :
    CatSoftIndex K E θ κ := by
  classical
  have hlsκ : ls K ≤ κ := (le_max_left _ _).trans hle
  have hsuccκ : Order.succ θ ≤ κ := (le_max_right _ _).trans hle
  have hell : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hκinf : aleph0 ≤ κ := hell.trans hlsκ
  let δ := categoricityOrdinal κ θ
  have hδcard := categoricityOrdinal_card (κ := κ) (θ := θ) hκinf hsuccκ
  have hδlim := categoricityOrdinal_isSuccLimit (κ := κ) (θ := θ) hθ
  obtain ⟨I, linI, nonI, eISO, hIcard⟩ := horderSmallCopy hδlim hδcard
  exact ⟨I, linI, nonI, eISO, orderPresentation_obj_card E hIcard hlsκ hκinf,
    orderPresentation_obj_mem E I⟩

/-! ### Orbit naming via soft-copy Quotient.out -/

/-- Name a tuple by the canonical record of its soft-copy orbit representative. -/
noncomputable def catOrbitNameAt (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (κ : Cardinal.{u})
    (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    {M : Model K.τ} {ι : Type u}
    (hM : K.Mem M) (hMcard : Model.card M = κ)
    (xs : ι → M.carrier) (hι : #ι ≤ θ) : OrbitName K θ := by
  classical
  let soft := catSoftIndex K E θ κ hθ hle hcat
  let I := soft.I
  have hEcard := soft.card_eq
  have hImem := soft.mem
  let φ : M.carrier ≃[K.τ] (E.obj I).carrier :=
    Classical.choice (hcat.unique_model M (E.obj I) hM hImem hMcard hEcard)
  let s := autOrbitSetoid K (E.obj I) hImem ι
  exact recordNameEmb K E θ hθ
    (canonicalOfTuple E hθ hι (Quotient.out (s := s) (⟦φ ∘ xs⟧ : Quotient s)))

/-- Convenience wrapper at `Model.card M`. -/
noncomputable def catOrbitName (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) {M : Model K.τ} {ι : Type u}
    (hM : K.Mem M) (xs : ι → M.carrier) (hι : #ι ≤ θ)
    (hle : max (ls K) (Order.succ θ) ≤ Model.card M)
    (hcat : Categorical K (Model.card M)) : OrbitName K θ :=
  catOrbitNameAt K E θ hθ (Model.card M) hle hcat hM rfl xs hι

/-- Default name away from the large-categoricity regime. -/
noncomputable def defaultOrbitName (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u}) :
    OrbitName K θ := by
  classical
  have hell : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hpos : (0 : Cardinal.{u}) < orbitRecordBound (ls K) θ := by
    dsimp [orbitRecordBound]
    exact zero_lt_one.trans_le (one_le_aleph0.trans
      ((cantor (aleph0 : Cardinal.{u})).le.trans
        (power_le_power_left two_ne_zero
          ((cantor (aleph0 : Cardinal.{u})).le.trans
            (power_le_power_left two_ne_zero (le_add_of_le_left hell))))))
  have : Nonempty (OrbitName K θ) := by
    rw [← mk_ne_zero_iff]
    dsimp [OrbitName, Below]
    rw [mk_ord_toType]
    exact hpos.ne'
  exact Classical.choice this

noncomputable def namingDecision (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) {M : Model K.τ} {ι : Type u}
    (hM : K.Mem M) (xs : ι → M.carrier) (hι : #ι ≤ θ) : OrbitName K θ := by
  classical
  by_cases h : max (ls K) (Order.succ θ) ≤ Model.card M ∧ Categorical K (Model.card M)
  · exact catOrbitName K E θ hθ hM xs hι h.1 h.2
  · exact defaultOrbitName K θ

theorem catOrbitNameAt_iso (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (κ : Cardinal.{u})
    (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    {M₁ M₂ : Model K.τ} (φ : M₁.carrier ≃[K.τ] M₂.carrier)
    (hM₁ : K.Mem M₁) (hM₂ : K.Mem M₂)
    (hc1 : Model.card M₁ = κ) (hc2 : Model.card M₂ = κ)
    {ι : Type u} (xs : ι → M₁.carrier) (hι : #ι ≤ θ) :
    catOrbitNameAt K E θ hθ κ hle hcat hM₁ hc1 xs hι =
      catOrbitNameAt K E θ hθ κ hle hcat hM₂ hc2 (fun i => φ (xs i)) hι := by
  classical
  dsimp [catOrbitNameAt]
  let soft := catSoftIndex K E θ κ hθ hle hcat
  let I := soft.I
  have hEcard := soft.card_eq
  have hImem := soft.mem
  let ψ₁ : M₁.carrier ≃[K.τ] (E.obj I).carrier :=
    Classical.choice (hcat.unique_model M₁ (E.obj I) hM₁ hImem hc1 hEcard)
  let ψ₂ : M₂.carrier ≃[K.τ] (E.obj I).carrier :=
    Classical.choice (hcat.unique_model M₂ (E.obj I) hM₂ hImem hc2 hEcard)
  let s := autOrbitSetoid K (E.obj I) hImem ι
  let auto : (E.obj I).carrier ≃[K.τ] (E.obj I).carrier :=
    ψ₂.comp (φ.comp ψ₁.symm)
  have horb : SameAutOrbit K (E.obj I) (ψ₁ ∘ xs) (ψ₂ ∘ (fun i => φ (xs i))) := by
    refine ⟨auto, strong_of_equiv K auto hImem, fun i => ?_⟩
    change ψ₂ (φ (ψ₁.symm (ψ₁ (xs i)))) = ψ₂ (φ (xs i))
    simp [Language.Equiv.symm_apply_apply]
  exact congrArg (recordNameEmb K E θ hθ)
    (congrArg (fun q : Quotient s =>
      canonicalOfTuple E hθ hι (Quotient.out (s := s) q))
      (Quotient.sound horb))

theorem catOrbitNameAt_card_eq (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) {κ₁ κ₂ : Cardinal.{u}}
    (hle₁ : max (ls K) (Order.succ θ) ≤ κ₁) (hcat₁ : Categorical K κ₁)
    (hle₂ : max (ls K) (Order.succ θ) ≤ κ₂) (hcat₂ : Categorical K κ₂)
    (hκ : κ₁ = κ₂) {M : Model K.τ} {ι : Type u}
    (hM : K.Mem M) (hc₁ : Model.card M = κ₁) (hc₂ : Model.card M = κ₂)
    (xs : ι → M.carrier) (hι : #ι ≤ θ) :
    catOrbitNameAt K E θ hθ κ₁ hle₁ hcat₁ hM hc₁ xs hι =
      catOrbitNameAt K E θ hθ κ₂ hle₂ hcat₂ hM hc₂ xs hι := by
  subst hκ
  rfl

noncomputable def elimOrbitNaming (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) : OrbitNaming K θ where
  name := namingDecision K E θ hθ
  name_spec {M} {ι} hM xs ys hι hle hcat := by
    classical
    have hx : namingDecision K E θ hθ hM xs hι =
        catOrbitName K E θ hθ hM xs hι hle hcat := by
      dsimp [namingDecision]; simp [hle, hcat]
    have hy : namingDecision K E θ hθ hM ys hι =
        catOrbitName K E θ hθ hM ys hι hle hcat := by
      dsimp [namingDecision]; simp [hle, hcat]
    rw [hx, hy]
    dsimp [catOrbitName, catOrbitNameAt]
    let soft := catSoftIndex K E θ (Model.card M) hθ hle hcat
    let I := soft.I
    let eISO := soft.e
    have hEcard := soft.card_eq
    have hImem := soft.mem
    let φ : M.carrier ≃[K.τ] (E.obj I).carrier :=
      Classical.choice (hcat.unique_model M (E.obj I) hM hImem rfl hEcard)
    let s := autOrbitSetoid K (E.obj I) hImem ι
    let δ := categoricityOrdinal (Model.card M) θ
    have hδlim := categoricityOrdinal_isSuccLimit (κ := Model.card M) (θ := θ) hθ
    have hδcof := categoricityOrdinal_cof (κ := Model.card M) (θ := θ) hθ
    have hθlt : θ < Ordinal.cof δ := by rw [hδcof]; exact Order.lt_succ θ
    have hcan_inj :
        Function.Injective fun q : Quotient s =>
          canonicalOfTuple E hθ hι (Quotient.out (s := s) q) := by
      intro q1 q2 hf
      rw [← Quotient.out_eq (s := s) q1, ← Quotient.out_eq (s := s) q2]
      exact Quotient.sound (same_canonical_sameAutOrbit E δ θ hδlim hθ hθlt eISO hι
        (Quotient.out (s := s) q1) (Quotient.out (s := s) q2) hf)
    constructor
    · intro hnames
      have hcan :
          canonicalOfTuple E hθ hι (Quotient.out (s := s) (⟦φ ∘ xs⟧ : Quotient s)) =
          canonicalOfTuple E hθ hι (Quotient.out (s := s) (⟦φ ∘ ys⟧ : Quotient s)) :=
        (recordNameEmb K E θ hθ).injective hnames
      exact (sameAutOrbit_congr K hM φ xs ys).mpr (Quotient.exact (hcan_inj hcan))
    · intro horb
      exact congrArg (recordNameEmb K E θ hθ)
        (congrArg (fun q : Quotient s => canonicalOfTuple E hθ hι (Quotient.out (s := s) q))
          (Quotient.sound ((sameAutOrbit_congr K hM φ xs ys).mp horb)))
  name_iso {M₁ M₂} φ hM₁ hM₂ {ι} xs hι := by
    classical
    have hcard : Model.card M₁ = Model.card M₂ :=
      le_antisymm (mk_le_of_injective φ.injective) (mk_le_of_injective φ.symm.injective)
    dsimp [namingDecision]
    by_cases h₁ : max (ls K) (Order.succ θ) ≤ Model.card M₁ ∧ Categorical K (Model.card M₁)
    · have h₂ : max (ls K) (Order.succ θ) ≤ Model.card M₂ ∧ Categorical K (Model.card M₂) := by
        rw [← hcard]; exact h₁
      simp only [h₁, h₂]
      dsimp [catOrbitName]
      refine (catOrbitNameAt_iso K E θ hθ (Model.card M₁) h₁.1 h₁.2
        φ hM₁ hM₂ rfl hcard.symm xs hι).trans ?_
      exact catOrbitNameAt_card_eq K E θ hθ h₁.1 h₁.2 h₂.1 h₂.2 hcard
        hM₂ hcard.symm rfl (fun i => φ (xs i)) hι
    · have h₂ : ¬ (max (ls K) (Order.succ θ) ≤ Model.card M₂ ∧
          Categorical K (Model.card M₂)) := by
        rw [← hcard]; exact h₁
      split_ifs <;> first | rfl | contradiction

/-! ### Arrow transport and asymmetric named arrows -/

theorem orbitArrow_comp (K : AbstractElementaryClass.{u}) (M : Model K.τ) {ι : Type u}
    {xs ys zs : ι → M.carrier} :
    OrbitArrow K M xs ys → OrbitArrow K M ys zs → OrbitArrow K M xs zs := by
  rintro ⟨f, hfS, hf⟩ ⟨g, hgS, hg⟩
  exact ⟨g.comp f, K.strong_trans f g hfS hgS,
    fun i => by rw [Language.Embedding.comp_apply, hf, hg]⟩

theorem orbitArrow_iso (K : AbstractElementaryClass.{u}) {M N : Model K.τ}
    (hM : K.Mem M) (hN : K.Mem N) (φ : M.carrier ≃[K.τ] N.carrier)
    {ι : Type u} {xs ys : ι → M.carrier} :
    OrbitArrow K M xs ys → OrbitArrow K N (fun i => φ (xs i)) (fun i => φ (ys i)) := by
  rintro ⟨f, hfS, hf⟩
  refine ⟨φ.toEmbedding.comp (f.comp φ.symm.toEmbedding),
    K.strong_trans _ _ (K.strong_trans _ _ (strong_of_equiv K φ.symm hN) hfS)
      (strong_of_equiv K φ hM), fun i => ?_⟩
  change φ (f (φ.symm (φ (xs i)))) = φ (ys i)
  simp [hf, Language.Equiv.symm_apply_apply]

theorem orbitArrow_of_sameAutOrbit (K : AbstractElementaryClass.{u}) {M : Model K.τ}
    (hM : K.Mem M) {ι : Type u} {xs ys xs' ys' : ι → M.carrier}
    (hxs : SameAutOrbit K M xs xs') (hys : SameAutOrbit K M ys ys')
    (harrow : OrbitArrow K M xs ys) : OrbitArrow K M xs' ys' := by
  obtain ⟨e, _, he⟩ := hxs
  obtain ⟨f, _, hf⟩ := hys
  obtain ⟨g, hgS, hg⟩ := harrow
  refine ⟨f.toEmbedding.comp (g.comp e.symm.toEmbedding),
    K.strong_trans _ _ (K.strong_trans _ _ (strong_of_equiv K e.symm hM) hgS)
      (strong_of_equiv K f hM), fun i => ?_⟩
  change f (g (e.symm (xs' i))) = ys' i
  have hx' : e.symm (xs' i) = xs i := by
    have := congrArg e.symm (he i)
    simpa [Language.Equiv.symm_apply_apply] using this.symm
  rw [hx', hg, hf]

/-- Pad a short nonempty tuple to exact length `θ` along a surjection from `Below θ`. -/
noncomputable def padTuple {α : Type u} {ι : Type u} (θ : Cardinal.{u})
    (hθ : aleph0 ≤ θ) (hne : Nonempty ι) (xs : ι → α) : Below θ → α :=
  fun b => xs (Classical.choice hne)

theorem padTuple_orbitArrow (K : AbstractElementaryClass.{u}) (M : Model K.τ)
    {ι : Type u} (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (hne : Nonempty ι)
    {xs ys : ι → M.carrier} (h : OrbitArrow K M xs ys) :
    OrbitArrow K M (padTuple θ hθ hne xs) (padTuple θ hθ hne ys) := by
  obtain ⟨f, hfS, hf⟩ := h
  exact ⟨f, hfS, fun _ => hf _⟩

/-- Surjective padding `Below θ ⊕ ι → ι` so `# = θ` and coordinates of `ι` appear. -/
noncomputable def exactPad {ι : Type u} (θ : Cardinal.{u}) (hne : Nonempty ι) :
    Below θ ⊕ ι → ι :=
  Sum.elim (fun _ => Classical.choice hne) id

theorem exactPad_surjective {ι : Type u} (θ : Cardinal.{u}) (hne : Nonempty ι) :
    Function.Surjective (exactPad (ι := ι) θ hne) := fun i => ⟨Sum.inr i, rfl⟩

theorem exactPad_card {ι : Type u} (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ)
    (hne : Nonempty ι) (hι : #ι ≤ θ) : #(Below θ ⊕ ι) = θ := by
  have hsum : #(Below θ ⊕ ι) = θ + #ι := by
    rw [mk_sum, mk_ord_toType, lift_id, lift_id]
  rw [hsum, Cardinal.add_eq_left hθ hι]

/-- Failure at a large categoricity size yields an asymmetric `NamedArrow` at length `θ`. -/
theorem exists_asymmetric_namedArrow (K : AbstractElementaryClass.{u})
    (θ κ : Cardinal.{u}) (N : OrbitNaming K θ) (hθ : aleph0 ≤ θ)
    (hFail : FailsReversal K θ κ) (hle : max (ls K) (Order.succ θ) ≤ κ) :
    ∃ p r : OrbitName K θ,
      NamedArrow K θ κ N p r ∧ ¬ NamedArrow K θ κ N r p ∧
        (∃ (M : Model K.τ) (hM : K.Mem M), Model.card M = κ ∧
          ∃ xs : Below θ → M.carrier, N.name hM xs (by rw [mk_ord_toType]) = p) := by
  obtain ⟨M, hM, hc, ι, xs, ys, hι, harrow, hno⟩ := exists_asymmetric_orbitArrow K θ κ hFail
  have hne : Nonempty ι := by
    by_contra hempty
    exact hno ⟨Language.Embedding.refl _ _, K.strong_refl M hM,
      fun i => (not_nonempty_iff.mp hempty).elim i⟩
  -- Pad to a type of cardinality θ, then transport names along an equiv with `Below θ`.
  let ιθ : Type u := Below θ ⊕ ι
  have hιθ : #ιθ = θ := exactPad_card θ hθ hne hι
  let s := exactPad (ι := ι) θ hne
  let xsθ : ιθ → M.carrier := fun i => xs (s i)
  let ysθ : ιθ → M.carrier := fun i => ys (s i)
  have harrowθ : OrbitArrow K M xsθ ysθ := by
    obtain ⟨f, hfS, hf⟩ := harrow
    exact ⟨f, hfS, fun i => hf (s i)⟩
  have hnoθ : ¬ OrbitArrow K M ysθ xsθ := by
    intro ⟨f, hfS, hf⟩
    refine hno ⟨f, hfS, fun i => ?_⟩
    obtain ⟨j, hj⟩ := exactPad_surjective θ hne i
    simpa [ysθ, xsθ, s, hj] using hf j
  -- Identify `ιθ` with `Below θ` via cardinality.
  have eθ : ιθ ≃ Below θ := Classical.choice (Cardinal.eq.mp (by
    rw [hιθ, mk_ord_toType]))
  let xsB : Below θ → M.carrier := fun b => xsθ (eθ.symm b)
  let ysB : Below θ → M.carrier := fun b => ysθ (eθ.symm b)
  have harrowB : OrbitArrow K M xsB ysB := by
    obtain ⟨f, hfS, hf⟩ := harrowθ
    exact ⟨f, hfS, fun b => hf (eθ.symm b)⟩
  have hnoB : ¬ OrbitArrow K M ysB xsB := by
    intro ⟨f, hfS, hf⟩
    refine hnoθ ⟨f, hfS, fun i => ?_⟩
    simpa [ysB, xsB, Equiv.apply_symm_apply] using hf (eθ i)
  have hιB : #(Below θ) ≤ θ := by rw [mk_ord_toType]
  let p := N.name hM xsB hιB
  let r := N.name hM ysB hιB
  refine ⟨p, r, ⟨M, hM, hc, xsB, ysB, rfl, rfl, harrowB⟩, ?_,
    ⟨M, hM, hc, xsB, rfl⟩⟩
  intro ⟨M', hM', hc', us, vs, hus, hvs, harrow'⟩
  obtain ⟨φ⟩ := hFail.1.unique_model M' M hM' hM hc' hc
  have harrowM : OrbitArrow K M (fun i => φ (us i)) (fun i => φ (vs i)) :=
    orbitArrow_iso K hM' hM φ harrow'
  have hus' : N.name hM (fun i => φ (us i)) hιB = r := by
    rw [← N.name_iso φ hM' hM us hιB, hus]
  have hvs' : N.name hM (fun i => φ (vs i)) hιB = p := by
    rw [← N.name_iso φ hM' hM vs hιB, hvs]
  have hleM : max (ls K) (Order.succ θ) ≤ Model.card M := by rw [hc]; exact hle
  have hcatM : Categorical K (Model.card M) := by rw [hc]; exact hFail.1
  have hus_orb : SameAutOrbit K M (fun i => φ (us i)) ysB :=
    (N.name_spec hM (fun i => φ (us i)) ysB hιB hleM hcatM).1 hus'
  have hvs_orb : SameAutOrbit K M (fun i => φ (vs i)) xsB :=
    (N.name_spec hM (fun i => φ (vs i)) xsB hιB hleM hcatM).1 hvs'
  exact hnoB (orbitArrow_of_sameAutOrbit K hM hus_orb hvs_orb harrowM)

/-! ### Profiles for the pigeonhole (text.md 186–188) -/

/-- A coded profile: named-arrow relation and record assign, as concrete functions. -/
structure FailProfile (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) where
  arrow : OrbitName K θ → OrbitName K θ → Bool
  assign : CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ)

/-- Assign a canonical record its elim-orbit name when realized in the soft model of size `κ`.
Uses only the record's own index: a realization of `toOrbitRecord r` on `(toOrbitRecord r).index`. -/
noncomputable def softAssign (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (κ : Cardinal.{u})
    (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    (N : OrbitNaming K θ) (r : CanonicalRecord E.lab E.arity θ) :
    Option (OrbitName K θ) := by
  classical
  let soft := catSoftIndex K E θ κ hθ hle hcat
  let I := soft.I
  let ι := (CanonicalRecord.toOrbitRecord r).index
  let hι := canonical_record_card_index r
  exact
    if h : ∃ (place : (CanonicalRecord.toOrbitRecord r).slot → I)
        (xs : ι → (E.obj I).carrier),
        RealizesOrbitRecord (I := I) E (CanonicalRecord.toOrbitRecord r) place xs then
      let place := Classical.choose h
      let xs := Classical.choose (Classical.choose_spec h)
      some (N.name soft.mem xs hι)
    else
      none

/-- `softAssign` of a canon returns the name of its realizing reindexed tuple
(uniqueness on `r.index` via `same_record_sameAutOrbit` + `name_spec`).
The further identity `N.name (canonicalTupleReindex xs) = N.name xs` is deferred
(text.md 186–201: profile pigeonhole → Prop 3.9 → renaming kill). -/
theorem softAssign_canonical (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (κ : Cardinal.{u})
    (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    (N : OrbitNaming K θ) {ι : Type u} (hι : #ι ≤ θ)
    (xs : ι → (E.obj (catSoftIndex K E θ κ hθ hle hcat).I).carrier) :
    softAssign K E θ hθ κ hle hcat N (canonicalOfTuple E hθ hι xs) =
      some (N.name (catSoftIndex K E θ κ hθ hle hcat).mem
        (canonicalTupleReindex E hθ hι xs)
        (canonical_record_card_index (canonicalOfTuple E hθ hι xs))) := by
  classical
  let soft := catSoftIndex K E θ κ hθ hle hcat
  let r := canonicalOfTuple E hθ hι xs
  let zs := canonicalTupleReindex E hθ hι xs
  let hιr := canonical_record_card_index r
  have hreal := realizes_canonicalOfTuple E hθ hι xs
  have hne : ∃ (place : (CanonicalRecord.toOrbitRecord r).slot → soft.I)
      (ys : (CanonicalRecord.toOrbitRecord r).index → (E.obj soft.I).carrier),
      RealizesOrbitRecord (I := soft.I) E (CanonicalRecord.toOrbitRecord r) place ys :=
    ⟨canonicalPlaceOfTuple E hθ hι xs, zs, hreal⟩
  dsimp [softAssign]
  split_ifs with h
  · let place := Classical.choose h
    let ys := Classical.choose (Classical.choose_spec h)
    have hys : RealizesOrbitRecord (I := soft.I) E (CanonicalRecord.toOrbitRecord r)
        place ys := Classical.choose_spec (Classical.choose_spec h)
    let δ := categoricityOrdinal κ θ
    have hδlim := categoricityOrdinal_isSuccLimit (κ := κ) (θ := θ) hθ
    have hδcof := categoricityOrdinal_cof (κ := κ) (θ := θ) hθ
    have hθlt : θ < Ordinal.cof δ := by rw [hδcof]; exact Order.lt_succ θ
    have horb := same_record_sameAutOrbit E δ θ hδlim hθ hθlt soft.e
      (CanonicalRecord.toOrbitRecord r) (canonical_record_card_slot r)
      place (canonicalPlaceOfTuple E hθ hι xs) ys zs hys hreal
    have hcard : Model.card (E.obj soft.I) = κ := soft.card_eq
    have hleM : max (ls K) (Order.succ θ) ≤ Model.card (E.obj soft.I) := by
      rw [hcard]; exact hle
    have hcatM : Categorical K (Model.card (E.obj soft.I)) := by
      rw [hcard]; exact hcat
    exact congrArg some ((N.name_spec soft.mem ys zs hιr hleM hcatM).2 horb)
  · exact (h hne).elim

noncomputable def failProfileAt (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (κ : Cardinal.{u})
    (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    (N : OrbitNaming K θ) : FailProfile K E θ where
  arrow p r := (Classical.dec (NamedArrow K θ κ N p r)).decide
  assign := softAssign K E θ hθ κ hle hcat N

private theorem orbitRecordBound_aleph0 (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u}) :
    aleph0 ≤ orbitRecordBound (ls K) θ := by
  have hell : aleph0 ≤ ls K := (isLSBound_ls K).1
  dsimp [orbitRecordBound]
  exact le_trans (cantor (aleph0 : Cardinal.{u})).le
    (power_le_power_left two_ne_zero
      (le_trans (cantor (aleph0 : Cardinal.{u})).le
        (power_le_power_left two_ne_zero (le_add_of_le_left hell))))

/-- `#FailProfile ≤ P = 2^B`. -/
theorem mk_failProfile_le (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) :
    #(FailProfile K E θ) ≤ profilePaletteBound K θ := by
  classical
  have hB := orbitRecordBound_aleph0 K θ
  have hName : #(OrbitName K θ) = orbitRecordBound (ls K) θ := by
    dsimp [OrbitName, Below]; exact mk_ord_toType _
  have hell : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hlab : #E.lab ≤ ls K := by simpa [E.ell_eq] using E.lab_small
  have hRec : #(CanonicalRecord E.lab E.arity θ) ≤ orbitRecordBound (ls K) θ :=
    mk_canonicalRecord_le_orbitRecordBound (arity := E.arity) θ (ls K) hlab hθ hell
  have h2B : (2 : Cardinal.{u}) ^ orbitRecordBound (ls K) θ ≤ profilePaletteBound K θ :=
    le_of_eq rfl
  have hadd1 : orbitRecordBound (ls K) θ + 1 ≤
      (2 : Cardinal.{u}) ^ orbitRecordBound (ls K) θ := by
    have hle : orbitRecordBound (ls K) θ ≤ (2 : Cardinal.{u}) ^ orbitRecordBound (ls K) θ :=
      (cantor _).le
    have hone : (1 : Cardinal.{u}) ≤ (2 : Cardinal.{u}) ^ orbitRecordBound (ls K) θ :=
      one_le_aleph0.trans ((cantor _).le.trans (power_le_power_left two_ne_zero hB))
    exact (add_le_add hle hone).trans <| by
      rw [Cardinal.add_eq_self ((cantor _).le.trans (power_le_power_left two_ne_zero hB))]
  let toProd : FailProfile K E θ →
      (OrbitName K θ → OrbitName K θ → Bool) ×
        (CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ)) :=
    fun p => (p.arrow, p.assign)
  have hinj : Function.Injective toProd := by
    intro p q h
    cases p; cases q
    injection h with h1 h2
    cases h1; cases h2; rfl
  refine (mk_le_of_injective hinj).trans ?_
  have harrow : #(OrbitName K θ → OrbitName K θ → Bool) ≤ profilePaletteBound K θ := by
    have h1 : #(OrbitName K θ → OrbitName K θ → Bool) =
        #(OrbitName K θ × OrbitName K θ → Bool) :=
      mk_congr ⟨fun f p => f p.1 p.2, fun f a b => f (a, b), fun _ => rfl, fun _ => rfl⟩
    have h2 : #(OrbitName K θ × OrbitName K θ → Bool) =
        (2 : Cardinal.{u}) ^ (#(OrbitName K θ) * #(OrbitName K θ)) := by
      have hp : #(OrbitName K θ × OrbitName K θ) =
          #(OrbitName K θ) * #(OrbitName K θ) := by simp [mk_prod]
      simp [mk_arrow, hp, mk_bool, lift_uzero, lift_two]
    rw [h1, h2, hName, Cardinal.mul_eq_self hB]
    exact h2B
  have hassign : #(CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ)) ≤
      profilePaletteBound K θ := by
    have hop : #(Option (OrbitName K θ)) ≤ profilePaletteBound K θ := by
      have : #(Option (OrbitName K θ)) = orbitRecordBound (ls K) θ + 1 := by
        simp [mk_option, hName]
      rw [this]
      exact hadd1.trans h2B
    have hfun : #(CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ)) =
        (#(Option (OrbitName K θ))) ^ #(CanonicalRecord E.lab E.arity θ) := by
      simp [mk_arrow]
    rw [hfun]
    refine (power_le_power_right hop).trans ?_
    have hPne : profilePaletteBound K θ ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_one
        (one_le_aleph0.trans (profilePaletteBound_aleph0_le K θ hθ)))
    have : profilePaletteBound K θ ^ #(CanonicalRecord E.lab E.arity θ) ≤
        profilePaletteBound K θ ^ orbitRecordBound (ls K) θ :=
      power_le_power_left hPne hRec
    refine this.trans ?_
    dsimp [profilePaletteBound]
    rw [← power_mul, Cardinal.mul_eq_self hB]
  have hPinf : aleph0 ≤ profilePaletteBound K θ := profilePaletteBound_aleph0_le K θ hθ
  simp only [mk_prod, lift_id]
  have hmul : #(OrbitName K θ → OrbitName K θ → Bool) *
      #(CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ)) ≤
        profilePaletteBound K θ := by
    have : #(OrbitName K θ → OrbitName K θ → Bool) *
        #(CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ)) ≤
          profilePaletteBound K θ * profilePaletteBound K θ :=
      mul_le_mul' harrow hassign
    refine this.trans ?_
    rw [Cardinal.mul_eq_self hPinf]
  exact hmul

/-- Pigeonhole on the `P⁺`-sequence of failing sizes: two sizes share a fail-profile. -/
theorem exists_common_fail_profile (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (N : OrbitNaming K θ)
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ) :
    ∃ (a μ : Cardinal.{u}) (haFail : FailsReversal K θ a) (hμFail : FailsReversal K θ μ)
      (hale : max (ls K) (Order.succ θ) ≤ a) (hμle : max (ls K) (Order.succ θ) ≤ μ),
      a < μ ∧ a ^ θ ≤ μ ∧
        failProfileAt K E θ hθ a hale haFail.1 N =
          failProfileAt K E θ hθ μ hμle hμFail.1 N := by
  classical
  let P := profilePaletteBound K θ
  let Idx := Below (Order.succ P)
  have hIdx : #Idx = Order.succ P := mk_ord_toType _
  have hPinf : aleph0 ≤ P := profilePaletteBound_aleph0_le K θ hθ
  have hIdxinf : aleph0 ≤ #Idx := by
    rw [hIdx]; exact hPinf.trans (Order.le_succ P)
  let f : Idx → FailProfile K E θ := fun i =>
    failProfileAt K E θ hθ (failingSequence K θ hUnb i)
      (failingSequence_spec K θ hUnb i).2.1 (failingSequence_spec K θ hUnb i).1.1 N
  have hcod : #(FailProfile K E θ) < (#Idx).ord.cof := by
    rw [hIdx, (isRegular_succ hPinf).cof_ord]
    exact lt_of_le_of_lt (mk_failProfile_le K E θ hθ) (Order.lt_succ P)
  obtain ⟨Φ, hfiber⟩ := infinite_pigeonhole f hIdxinf hcod
  have h2 : (2 : Cardinal.{u}) ≤ #(f ⁻¹' {Φ}) := by
    rw [hfiber, hIdx]
    exact (le_of_lt (Nat.cast_lt.mpr (by decide : 2 < 3))).trans
      ((natCast_le_aleph0 (n := 3)).trans (hPinf.trans (Order.le_succ P)))
  have hnontriv : Nontrivial (f ⁻¹' {Φ}) :=
    Cardinal.one_lt_iff_nontrivial.mp (lt_of_lt_of_le one_lt_two h2)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (f ⁻¹' {Φ})
  let i : Idx := x.1
  let j : Idx := y.1
  have hfi : f i = Φ := x.2
  have hfj : f j = Φ := y.2
  have hne : i ≠ j := fun heq => hxy (Subtype.ext heq)
  rcases lt_trichotomy i j with hij | heq | hji
  · refine ⟨failingSequence K θ hUnb i, failingSequence K θ hUnb j,
      (failingSequence_spec K θ hUnb i).1, (failingSequence_spec K θ hUnb j).1,
      (failingSequence_spec K θ hUnb i).2.1, (failingSequence_spec K θ hUnb j).2.1,
      failingSequence_strict K θ hUnb hij, failingSequence_power_le K θ hUnb hij, ?_⟩
    change f i = f j; rw [hfi, hfj]
  · exact False.elim (hne heq)
  · refine ⟨failingSequence K θ hUnb j, failingSequence K θ hUnb i,
      (failingSequence_spec K θ hUnb j).1, (failingSequence_spec K θ hUnb i).1,
      (failingSequence_spec K θ hUnb j).2.1, (failingSequence_spec K θ hUnb i).2.1,
      failingSequence_strict K θ hUnb hji, failingSequence_power_le K θ hUnb hji, ?_⟩
    change f j = f i; rw [hfj, hfi]

end
end AEC
