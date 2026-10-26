module

public import AEC.Section3.OrderEqualityDiagram
public import Mathlib.Data.Bool.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Continuum
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace AEC
section

universe u

open Cardinal Classical Set

attribute [local instance] Classical.propDecidable

abbrev EmptyU : Type u := PEmpty.{u + 1}
abbrev FinU (n : ℕ) : Type u := ULift.{u, 0} (Fin n)
abbrev NatU : Type u := ULift.{u, 0} ℕ
abbrev BoolU : Type u := ULift.{u, 0} Bool

/-- Pattern codes over `ι`, with finite indices lifted to `Type u`. -/
abbrev PatternCode (ι : Type u) (n : ℕ) : Type u :=
  (FinU.{u} n → FinU.{u} n → BoolU.{u}) ×
  (FinU.{u} n → FinU.{u} n → BoolU.{u}) ×
  (FinU.{u} n → ι → BoolU.{u}) ×
  (FinU.{u} n → ι → BoolU.{u}) ×
  (FinU.{u} n → NatU.{u})

noncomputable def patternCode {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ι : Type u} {n : ℕ} (r : ι → J) (q : Fin n → J) : PatternCode ι n :=
  (fun i j => ULift.up (decide (q i.down = q j.down)),
   fun i j => ULift.up (decide (q i.down < q j.down)),
   fun i k => ULift.up (decide (q i.down = r k)),
   fun i k => ULift.up (decide (q i.down < r k)),
   fun i => ULift.up (color (q i.down)))

lemma patternCode_eq_iff {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ι : Type u} {n : ℕ} (r : ι → J) (q q' : Fin n → J) :
    patternCode color r q = patternCode color r q' ↔
      (∀ i j : Fin n, q i = q j ↔ q' i = q' j) ∧
      (∀ i j : Fin n, q i < q j ↔ q' i < q' j) ∧
      (∀ i : Fin n, ∀ k, q i = r k ↔ q' i = r k) ∧
      (∀ i : Fin n, ∀ k, q i < r k ↔ q' i < r k) ∧
      (∀ i : Fin n, color (q i) = color (q' i)) := by
  constructor
  · intro h
    have h1 := congr_arg Prod.fst h
    have h2 := congr_arg Prod.fst (congr_arg Prod.snd h)
    have h3 := congr_arg Prod.fst (congr_arg Prod.snd (congr_arg Prod.snd h))
    have h4 := congr_arg Prod.fst (congr_arg Prod.snd (congr_arg Prod.snd (congr_arg Prod.snd h)))
    have h5 := congr_arg Prod.snd (congr_arg Prod.snd (congr_arg Prod.snd (congr_arg Prod.snd h)))
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i j
      have := congr_fun (congr_fun h1 (ULift.up i)) (ULift.up j)
      simpa [patternCode, Bool.decide_iff] using this
    · intro i j
      have := congr_fun (congr_fun h2 (ULift.up i)) (ULift.up j)
      simpa [patternCode, Bool.decide_iff] using this
    · intro i k
      have := congr_fun (congr_fun h3 (ULift.up i)) k
      simpa [patternCode, Bool.decide_iff] using this
    · intro i k
      have := congr_fun (congr_fun h4 (ULift.up i)) k
      simpa [patternCode, Bool.decide_iff] using this
    · intro i
      simpa [patternCode] using congr_fun h5 (ULift.up i)
  · intro ⟨heq, hlt, heqp, hltp, hcol⟩
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · ext i j; cases i; cases j; simp [patternCode, heq]
    · ext i j; cases i; cases j; simp [patternCode, hlt]
    · ext i k; cases i; simp [patternCode, heqp]
    · ext i k; cases i; simp [patternCode, hltp]
    · ext i; cases i; simp [patternCode, hcol]

lemma sameDiagram_of_patternCode {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ι : Type u} {n : ℕ} (r : ι → J) (q q' : Fin n → J)
    (h : patternCode color r q = patternCode color r q') :
    SameOrderDiagram (Sum.elim r q) (Sum.elim r q') ∧
      ∀ i, color (q i) = color (q' i) := by
  obtain ⟨heqN, hltN, heqP, hltP, hcol⟩ := (patternCode_eq_iff color r q q').1 h
  refine ⟨⟨?eq, ?lt⟩, hcol⟩
  · intro a b
    match a, b with
    | .inl i, .inl j => simp [Sum.elim]
    | .inl i, .inr j =>
        simp only [Sum.elim]
        exact ⟨fun hij => ((heqP j i).1 hij.symm).symm,
          fun hij => ((heqP j i).2 hij.symm).symm⟩
    | .inr i, .inl j => simpa [Sum.elim] using heqP i j
    | .inr i, .inr j => simpa [Sum.elim] using heqN i j
  · intro a b
    match a, b with
    | .inl i, .inl j => simp [Sum.elim]
    | .inl i, .inr j =>
        simp only [Sum.elim]
        constructor
        · intro hij
          rcases lt_trichotomy (r i) (q' j) with hlt | heq | hgt
          · exact hlt
          · exact (hij.ne ((heqP j i).2 heq.symm).symm).elim
          · exact (lt_asymm hij ((hltP j i).2 hgt)).elim
        · intro hij
          rcases lt_trichotomy (r i) (q j) with hlt | heq | hgt
          · exact hlt
          · exact (hij.ne ((heqP j i).1 heq.symm).symm).elim
          · exact (lt_asymm hij ((hltP j i).1 hgt)).elim
    | .inr i, .inl j => simpa [Sum.elim] using hltP i j
    | .inr i, .inr j => simpa [Sum.elim] using hltN i j

lemma sameDiagram_comp_embed {J : Type u} [LinearOrder J]
    {ι ρ : Type u} {n : ℕ} (e : ι ↪ ρ) (r : ρ → J) (q q' : Fin n → J)
    (h : SameOrderDiagram (Sum.elim r q) (Sum.elim r q')) :
    SameOrderDiagram (Sum.elim (r ∘ e) q) (Sum.elim (r ∘ e) q') := by
  refine ⟨?_, ?_⟩
  · intro a b
    match a, b with
    | .inl i, .inl j => simpa [Sum.elim, Function.comp] using h.1 (Sum.inl (e i)) (Sum.inl (e j))
    | .inl i, .inr j => simpa [Sum.elim, Function.comp] using h.1 (Sum.inl (e i)) (Sum.inr j)
    | .inr i, .inl j => simpa [Sum.elim, Function.comp] using h.1 (Sum.inr i) (Sum.inl (e j))
    | .inr i, .inr j => simpa [Sum.elim, Function.comp] using h.1 (Sum.inr i) (Sum.inr j)
  · intro a b
    match a, b with
    | .inl i, .inl j => simpa [Sum.elim, Function.comp] using h.2 (Sum.inl (e i)) (Sum.inl (e j))
    | .inl i, .inr j => simpa [Sum.elim, Function.comp] using h.2 (Sum.inl (e i)) (Sum.inr j)
    | .inr i, .inl j => simpa [Sum.elim, Function.comp] using h.2 (Sum.inr i) (Sum.inl (e j))
    | .inr i, .inr j => simpa [Sum.elim, Function.comp] using h.2 (Sum.inr i) (Sum.inr j)

lemma sameDiagram_of_empty_params {J : Type u} [LinearOrder J]
    {ι : Type u} [IsEmpty ι] {n : ℕ} (_p : ι → J) (q q' : Fin n → J)
    (h : SameOrderDiagram (Sum.elim (fun e : EmptyU => e.elim) q)
      (Sum.elim (fun e : EmptyU => e.elim) q')) :
    SameOrderDiagram (Sum.elim _p q) (Sum.elim _p q') := by
  refine ⟨?_, ?_⟩
  · intro a b
    match a, b with
    | .inl i, _ => exact isEmptyElim i
    | .inr _, .inl j => exact isEmptyElim j
    | .inr i, .inr j => exact h.1 (Sum.inr i) (Sum.inr j)
  · intro a b
    match a, b with
    | .inl i, _ => exact isEmptyElim i
    | .inr _, .inl j => exact isEmptyElim j
    | .inr i, .inr j => exact h.2 (Sum.inr i) (Sum.inr j)

noncomputable def witnessRange {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ι : Type u} {n : ℕ} (r : ι → J) (c : PatternCode ι n) : Set J :=
  if h : ∃ q : Fin n → J, patternCode color r q = c then
    Set.range (Classical.choose h)
  else
    ∅

lemma exists_chosen_witness {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ι : Type u} {n : ℕ} (r : ι → J) (q : Fin n → J) :
    ∃ q' : Fin n → J,
      (∀ i, q' i ∈ witnessRange color r (patternCode color r q)) ∧
      patternCode color r q' = patternCode color r q := by
  let c := patternCode color r q
  have hEx : ∃ q' : Fin n → J, patternCode color r q' = c := ⟨q, rfl⟩
  refine ⟨Classical.choose hEx, fun i => ?_, Classical.choose_spec hEx⟩
  change Classical.choose hEx i ∈ witnessRange color r c
  simp only [witnessRange, dif_pos hEx]
  exact ⟨i, rfl⟩

lemma witnessRange_card_le {J : Type u} [LinearOrder J] (color : J → ℕ)
    {ι : Type u} {n : ℕ} (r : ι → J) (c : PatternCode ι n) :
    #(witnessRange color r c) ≤ aleph0 := by
  unfold witnessRange
  split_ifs with h
  · let f : FinU.{u} n → J := fun i => Classical.choose h i.down
    have hsub : Set.range (Classical.choose h) ⊆ Set.range f := by
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      exact ⟨ULift.up i, rfl⟩
    refine (mk_le_mk_of_subset hsub).trans (mk_range_le.trans ?_)
    rw [show #(FinU.{u} n) = lift.{u, 0} (#(Fin n)) by exact mk_uLift (Fin n),
      mk_fin, lift_natCast]
    exact natCast_le_aleph0
  · simp

lemma mk_finU (n : ℕ) : #(FinU n) = (n : Cardinal.{u}) := by
  rw [show #(FinU.{u} n) = lift.{u, 0} (#(Fin n)) by exact mk_uLift (Fin n)]
  rw [mk_fin, lift_natCast]

lemma mk_patternCode_le {ι : Type u} (n : ℕ) {lam : Cardinal.{u}}
    (hι : #ι ≤ lam) (hlam : aleph0 ≤ lam) :
    #(PatternCode ι n) ≤ (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hκ : aleph0 ≤ κ := hlam.trans (le_of_lt (cantor lam))
  have hmul {a b : Cardinal.{u}} (ha : a ≤ κ) (hb : b ≤ κ) : a * b ≤ κ :=
    (mul_le_mul' ha hb).trans_eq (mul_eq_self hκ)
  have hn : #(FinU n) ≤ lam := (mk_finU n).symm ▸ natCast_le_aleph0.trans hlam
  have hBool : #(BoolU.{u}) = (2 : Cardinal.{u}) := by
    rw [mk_uLift]
    simp
  have hNN : #(FinU.{u} n → FinU.{u} n → BoolU.{u}) ≤ κ := by
    rw [← power_def, ← power_def, hBool, ← power_mul]
    exact power_le_power_left two_ne_zero <|
      (mul_le_max _ _).trans (max_le (max_le hn hn) hlam)
  have hPar : #(FinU.{u} n → ι → BoolU.{u}) ≤ κ := by
    rw [← power_def, ← power_def, hBool, ← power_mul]
    exact power_le_power_left two_ne_zero <|
      (mul_le_max _ _).trans (max_le (max_le hι hn) hlam)
  have hCol : #(FinU.{u} n → NatU.{u}) ≤ κ := by
    rw [← power_def, show #(NatU.{u}) = aleph0 by rw [mk_uLift, mk_nat, lift_aleph0]]
    have hFinA : #(FinU n) ≤ aleph0 := (mk_finU n).symm ▸ natCast_le_aleph0
    refine (power_le_power_left aleph0_ne_zero hFinA).trans ?_
    rw [aleph0_power_aleph0, ← two_power_aleph0]
    exact power_le_power_left two_ne_zero hlam
  change #((FinU n → FinU n → BoolU) × (FinU n → FinU n → BoolU) ×
      (FinU n → ι → BoolU) × (FinU n → ι → BoolU) × (FinU n → NatU)) ≤ κ
  simp only [mk_prod, lift_id]
  exact hmul hNN (hmul hNN (hmul hPar (hmul hPar hCol)))

abbrev ChiType (χ : Cardinal.{u}) : Type u := χ.ord.ToType

lemma mk_chiType (χ : Cardinal.{u}) : #(ChiType χ) = χ := mk_ord_toType _

noncomputable def emptyParamWitnesses {J : Type u} [LinearOrder J] (color : J → ℕ) : Set J :=
  ⋃ n : NatU.{u}, ⋃ c : PatternCode EmptyU n.down,
    witnessRange color (fun e : EmptyU => e.elim) c

noncomputable def paramWitnesses {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ : Cardinal.{u}) (S : Set J) : Set J :=
  ⋃ (r : ChiType χ → ↥S), ⋃ n : NatU.{u},
    ⋃ c : PatternCode (ChiType χ) n.down,
    witnessRange color (fun i => (r i).1) c

noncomputable def enrich {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ : Cardinal.{u}) (S : Set J) : Set J :=
  (S ∪ emptyParamWitnesses color) ∪ paramWitnesses color χ S

lemma enrich_subset_left {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ : Cardinal.{u}) (S : Set J) : S ⊆ enrich color χ S :=
  fun _ hx => Or.inl (Or.inl hx)

lemma two_power_aleph0_le (lam : Cardinal.{u}) (hlam : aleph0 ≤ lam) :
    aleph0 ≤ (2 : Cardinal.{u}) ^ lam :=
  hlam.trans (le_of_lt (cantor lam))

lemma emptyParamWitnesses_card {J : Type u} [LinearOrder J] (color : J → ℕ)
    {lam : Cardinal.{u}} (hlam : aleph0 ≤ lam) :
    #(emptyParamWitnesses (J := J) color) ≤ (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  change #(emptyParamWitnesses (J := J) color) ≤ κ
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam hlam
  have hκκ : κ * κ = κ := mul_eq_self hκ
  refine (mk_iUnion_le (α := J) (ι := NatU)
      (fun n => ⋃ c : PatternCode EmptyU n.down,
        witnessRange color (fun e : EmptyU => e.elim) c)).trans ?_
  rw [show #NatU = aleph0 by rw [mk_uLift, mk_nat, lift_aleph0], ← hκκ]
  refine mul_le_mul' hκ (ciSup_le' fun n => ?_)
  refine (mk_iUnion_le _).trans ?_
  have hc : #(PatternCode EmptyU n.down) ≤ κ :=
    mk_patternCode_le n.down (by simp [EmptyU, mk_eq_zero]) hlam
  rw [← hκκ]
  exact mul_le_mul' hc (ciSup_le' fun c => (witnessRange_card_le color _ c).trans hκ)

lemma kappa_pow_chi (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) :
    ((2 : Cardinal.{u}) ^ lam) ^ χ = (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have h1 : κ ^ χ ≤ κ := by
    have : κ ^ χ = (2 : Cardinal.{u}) ^ (lam * χ) := by
      dsimp [κ]; rw [← power_mul]
    rw [this]
    exact power_le_power_left two_ne_zero <|
      (mul_le_max_of_aleph0_le_left (hχ.trans hlam)).trans (max_le le_rfl hlam)
  have h2 : κ ≤ κ ^ χ := by
    simpa [power_one] using
      power_le_power_left (ne_of_gt (aleph0_pos.trans_le hκ)) (one_le_aleph0.trans hχ)
  exact le_antisymm h1 h2

lemma paramWitnesses_card {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam)
    {S : Set J} (hS : #S ≤ (2 : Cardinal.{u}) ^ lam) :
    #(paramWitnesses color χ S) ≤ (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  change #(paramWitnesses color χ S) ≤ κ
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have hκκ : κ * κ = κ := mul_eq_self hκ
  have hpow : κ ^ χ = κ := kappa_pow_chi χ lam hχ hlam
  refine (mk_iUnion_le (α := J) (ι := ChiType χ → ↥S)
    (fun r => ⋃ n : NatU, ⋃ c : PatternCode (ChiType χ) n.down,
      witnessRange color (fun i => (r i).1) c)).trans ?_
  have hidx : #(ChiType χ → ↥S) ≤ κ := by
    rw [← power_def, mk_chiType]
    exact (power_le_power_right hS).trans_eq hpow
  refine (mul_le_mul' hidx (ciSup_le' fun r => ?_)).trans (by rw [hκκ])
  refine (mk_iUnion_le (α := J) (ι := NatU)
    (fun n => ⋃ c : PatternCode (ChiType χ) n.down,
      witnessRange color (fun i => (r i).1) c)).trans ?_
  rw [show #NatU = aleph0 by rw [mk_uLift, mk_nat, lift_aleph0], ← hκκ]
  refine mul_le_mul' hκ (ciSup_le' fun n => ?_)
  refine (mk_iUnion_le _).trans ?_
  have hc : #(PatternCode (ChiType χ) n.down) ≤ κ :=
    mk_patternCode_le n.down ((le_of_eq (mk_chiType χ)).trans hlam) (hχ.trans hlam)
  rw [← hκκ]
  exact mul_le_mul' hc (ciSup_le' fun c => (witnessRange_card_le color _ c).trans hκ)

lemma enrich_card {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam)
    {S : Set J} (hS : #S ≤ (2 : Cardinal.{u}) ^ lam) :
    #(enrich color χ S) ≤ (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have hadd : κ + κ = κ := add_eq_self hκ
  have h1 : #(emptyParamWitnesses (J := J) color) ≤ κ :=
    emptyParamWitnesses_card color (hχ.trans hlam)
  have h2 : #(paramWitnesses color χ S) ≤ κ :=
    paramWitnesses_card color χ lam hχ hlam hS
  have hleft : Cardinal.mk (↥(S ∪ emptyParamWitnesses (J := J) color)) ≤ κ :=
    (mk_union_le _ _).trans ((add_le_add hS h1).trans (le_of_eq hadd))
  exact (mk_union_le _ _).trans ((add_le_add hleft h2).trans (le_of_eq hadd))

lemma enrich_realizes {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ : Cardinal.{u}) (S : Set J) {ι : Type u} (hι : #ι ≤ χ)
    (p : ι → J) (hp : ∀ i, p i ∈ S) {n : ℕ} (q : Fin n → J) :
    ∃ q' : Fin n → J, (∀ i, q' i ∈ enrich color χ S) ∧
      SameOrderDiagram (Sum.elim p q) (Sum.elim p q') ∧
      ∀ i, color (q i) = color (q' i) := by
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
      letI : IsEmpty ι := hempty
      obtain ⟨q', hq'mem, hcode⟩ :=
        exists_chosen_witness color (fun e : EmptyU => e.elim) q
      refine ⟨q', ?_, ?_, ?_⟩
      · intro i
        exact Or.inl (Or.inr (mem_iUnion.mpr ⟨ULift.up n,
          mem_iUnion.mpr ⟨patternCode color (fun e : EmptyU => e.elim) q, hq'mem i⟩⟩))
      · exact sameDiagram_of_empty_params p q q'
          (sameDiagram_of_patternCode color (fun e : EmptyU => e.elim) q q' hcode.symm).1
      · exact (sameDiagram_of_patternCode color (fun e : EmptyU => e.elim) q q' hcode.symm).2
  | inr hnonempty =>
      let i0 : ι := Classical.choice hnonempty
      have hembCard : lift.{u} #ι ≤ lift.{u} #(ChiType χ) := by
        simpa [mk_chiType] using hι
      let e : ι ↪ ChiType χ := Classical.choice (lift_mk_le'.mp hembCard)
      let r : ChiType χ → ↥S :=
        Function.extend e (fun i => ⟨p i, hp i⟩) (fun _ => ⟨p i0, hp i0⟩)
      have hre : ∀ i, (r (e i)).1 = p i := by
        intro i
        change (Function.extend e (fun i => (⟨p i, hp i⟩ : ↥S))
          (fun _ => (⟨p i0, hp i0⟩ : ↥S)) (e i)).1 = p i
        rw [e.injective.extend_apply]
      obtain ⟨q', hq'mem, hcode⟩ :=
        exists_chosen_witness color (fun i => (r i).1) q
      have hfull := sameDiagram_of_patternCode color (fun i => (r i).1) q q' hcode.symm
      refine ⟨q', ?_, ?_, hfull.2⟩
      · intro i
        exact Or.inr (mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨ULift.up n,
          mem_iUnion.mpr ⟨patternCode color (fun k => (r k).1) q, hq'mem i⟩⟩⟩)
      · have hrestricted := sameDiagram_comp_embed e (fun i => (r i).1) q q' hfull.1
        have hre' : (fun i => (r i).1) ∘ e = p := funext hre
        rw [hre'] at hrestricted
        exact hrestricted

noncomputable def closureStage {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ : Cardinal.{u}) (S : Set J) (i : (Order.succ χ).ord.ToType) : Set J :=
  enrich color χ
    (S ∪ ⋃ j : {j : (Order.succ χ).ord.ToType // j < i}, closureStage color χ S j.1)
termination_by i
decreasing_by
  exact j.2

lemma closureStage_card {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam)
    {S : Set J} (hS : #S ≤ (2 : Cardinal.{u}) ^ lam)
    (i : (Order.succ χ).ord.ToType) :
    #(closureStage color χ S i) ≤ (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have hsucc : Order.succ χ ≤ κ :=
    Order.succ_le_of_lt (lt_of_le_of_lt hlam (cantor lam))
  apply (wellFounded_lt (α := (Order.succ χ).ord.ToType)).induction i
  intro i ih
  rw [closureStage.eq_def]
  apply enrich_card color χ lam hχ hlam
  have hprev :
      #(⋃ j : {j : (Order.succ χ).ord.ToType // j < i}, closureStage color χ S j.1) ≤ κ := by
    refine (mk_iUnion_le _).trans ?_
    refine (mul_le_mul'
      ((mk_le_of_injective Subtype.val_injective).trans (by rw [mk_ord_toType]))
      (ciSup_le' fun j : {j : (Order.succ χ).ord.ToType // j < i} => ih j.1 j.2)).trans ?_
    exact (mul_le_mul' hsucc le_rfl).trans (by rw [mul_eq_self hκ])
  exact (mk_union_le _ _).trans
    ((add_le_add hS hprev).trans (by rw [add_eq_self hκ]))

lemma closureSet_card {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam)
    {S : Set J} (hS : #S ≤ (2 : Cardinal.{u}) ^ lam) :
    #(⋃ i : (Order.succ χ).ord.ToType, closureStage color χ S i) ≤
      (2 : Cardinal.{u}) ^ lam := by
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hκ : aleph0 ≤ κ := two_power_aleph0_le lam (hχ.trans hlam)
  have hsucc : Order.succ χ ≤ κ :=
    Order.succ_le_of_lt (lt_of_le_of_lt hlam (cantor lam))
  refine (mk_iUnion_le _).trans ?_
  refine (mul_le_mul' (by rw [mk_ord_toType])
    (ciSup_le' (closureStage_card color χ lam hχ hlam hS))).trans ?_
  exact (mul_le_mul' hsucc le_rfl).trans (by rw [mul_eq_self hκ])

lemma toType_lt_of_ordinal_lt {o : _root_.Ordinal.{u}} {x : o.ToType}
    {a : _root_.Ordinal.{u}} (ha : a < o)
    (hx : (Ordinal.ToType.toOrd x).1 < a) :
    x < Ordinal.ToType.mk ⟨a, ha⟩ := by
  have hsub : Ordinal.ToType.toOrd x < ⟨a, ha⟩ := Subtype.mk_lt_mk.mpr hx
  have hmap := (Ordinal.ToType.mk.lt_iff_lt).mpr hsub
  simpa [Ordinal.ToType.mk.apply_symm_apply] using hmap

theorem lemma_6_14_proof {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) :
    ∀ (S0 : Set J), #S0 ≤ lam →
      ∃ S : Set J, S0 ⊆ S ∧ #S ≤ (2 : Cardinal.{u}) ^ lam ∧
        ∀ {ι : Type u} (hι : #ι ≤ χ) (p : ι → J), (∀ i, p i ∈ S) →
          ∀ {n : ℕ} (q : Fin n → J), n ≤ χ →
            ∃ q' : Fin n → J, (∀ i, q' i ∈ S) ∧
              SameOrderDiagram (Sum.elim p q) (Sum.elim p q') ∧
              ∀ i, color (q i) = color (q' i) := by
  intro S0 hS0
  let κ : Cardinal.{u} := (2 : Cardinal.{u}) ^ lam
  have hSκ : #S0 ≤ κ := hS0.trans (le_of_lt (cantor lam))
  let S : Set J := ⋃ i : (Order.succ χ).ord.ToType, closureStage color χ S0 i
  have hpos : (0 : _root_.Ordinal.{u}) < (Order.succ χ).ord := by
    refine lt_of_lt_of_le (Ordinal.natCast_lt_omega0 0) ?_
    rw [← ord_aleph0]
    exact ord_le_ord.mpr (hχ.trans (Order.le_succ χ))
  let i0 : (Order.succ χ).ord.ToType := Ordinal.ToType.mk ⟨0, hpos⟩
  have hS0sub : S0 ⊆ S := by
    intro x hx
    refine mem_iUnion.mpr ⟨i0, ?_⟩
    rw [closureStage.eq_def]
    exact enrich_subset_left color χ _ (Or.inl hx)
  have hcard : #S ≤ κ := closureSet_card color χ lam hχ hlam hSκ
  refine ⟨S, hS0sub, hcard, ?_⟩
  intro ι hι p hp n q _hn
  have hreg : Ordinal.cof (Order.succ χ).ord = Order.succ χ :=
    (isRegular_succ hχ).cof_ord
  let j : ι → (Order.succ χ).ord.ToType :=
    fun i => Classical.choose (mem_iUnion.mp (hp i))
  have hj : ∀ i, p i ∈ closureStage color χ S0 (j i) :=
    fun i => Classical.choose_spec (mem_iUnion.mp (hp i))
  have hidx : #ι < Ordinal.cof (Order.succ χ).ord := by
    rw [hreg]
    exact hι.trans_lt (Order.lt_succ χ)
  have hsup : (⨆ i, (Ordinal.ToType.toOrd (j i)).1) < (Order.succ χ).ord :=
    Ordinal.iSup_lt_of_lt_cof hidx (fun i => (Ordinal.ToType.toOrd (j i)).2)
  have h1 : (⨆ i, (Ordinal.ToType.toOrd (j i)).1) + 1 < (Order.succ χ).ord :=
    (isSuccLimit_ord (hχ.trans (Order.le_succ χ))).succ_lt hsup
  let i1 : (Order.succ χ).ord.ToType :=
    Ordinal.ToType.mk ⟨(⨆ i, (Ordinal.ToType.toOrd (j i)).1) + 1, h1⟩
  have hjlt : ∀ i, j i < i1 := by
    intro i
    refine toType_lt_of_ordinal_lt h1 ?_
    exact lt_of_le_of_lt
      (Ordinal.le_iSup (fun k => (Ordinal.ToType.toOrd (j k)).1) i)
      (lt_add_of_pos_right _ zero_lt_one)
  let R : Set J :=
    S0 ∪ ⋃ k : {k : (Order.succ χ).ord.ToType // k < i1},
      closureStage color χ S0 k.1
  have hpR : ∀ i, p i ∈ R := by
    intro i
    exact Or.inr (mem_iUnion.mpr ⟨⟨j i, hjlt i⟩, hj i⟩)
  obtain ⟨q', hq', hdiag, hcolor⟩ := enrich_realizes color χ R hι p hpR q
  refine ⟨q', ?_, hdiag, hcolor⟩
  intro k
  exact mem_iUnion.mpr ⟨i1, by
    rw [closureStage.eq_def]
    exact hq' k⟩

end
end AEC
