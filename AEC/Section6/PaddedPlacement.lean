module

public import AEC.Section4.ClosedLevels
public import AEC.Section4.CompactPlacement

@[expose] public section

/-!
# Padded compact placement (Lemma 6.4, the non-well-ordered clause)

The well-ordered engine (`compact_placement`) bounds profiles by `χ ^ σ = χ` using least
elements of cuts. A padded chart has no least elements. Lemma 6.4 replaces that count by
`2^{|X| + σ + b}` and iterates `β₀`, `β ↦ 2^β + σ + b`, through `σ⁺`, suprema at limits.
The hypothesis is that this one supremum lies strictly below the level. A closure point of
`{D.t, g}` need not satisfy it (`iSup_profileTower_eq_of_ge`).
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

attribute [local instance] Classical.propDecidable

/-! ## The σ⁺ profile recursion -/

/-- The padded profile recursion. At `0` it is the test size `β₀`. At a successor it is
`2^β + σ + b`. At a limit it is the supremum of the earlier values. The value at `(σ⁺).ord`
is `sup_{i < σ⁺} β_i`. -/
noncomputable def infra_69_pad_recursion (σ b β₀ : Cardinal.{u}) : Ordinal.{u} → Cardinal.{u} :=
  WellFounded.fix (r := (· < · : Ordinal.{u} → Ordinal.{u} → Prop)) wellFounded_lt
    fun i ih =>
      if h : Order.IsSuccPrelimit i then
        if i = 0 then β₀ else ⨆ j : Set.Iio i, ih j.1 (Set.mem_Iio.mp j.2)
      else
        have hex : ∃ j, CovBy j i := by
          by_contra hno
          exact h (fun j hj => hno ⟨j, hj⟩)
        (2 : Cardinal.{u}) ^ ih (Classical.choose hex) (Classical.choose_spec hex).1 + σ + b

theorem infra_69_pad_recursion_zero (σ b β₀ : Cardinal.{u}) :
    infra_69_pad_recursion σ b β₀ 0 = β₀ := by
  rw [infra_69_pad_recursion, WellFounded.fix_eq]
  have hbot : (0 : Ordinal.{u}) = ⊥ := bot_eq_zero.symm
  rw [hbot, dif_pos Order.isSuccPrelimit_bot, if_pos rfl]

theorem infra_69_pad_recursion_succ (σ b β₀ : Cardinal.{u}) (j : Ordinal.{u}) :
    infra_69_pad_recursion σ b β₀ (Order.succ j) =
      (2 : Cardinal.{u}) ^ infra_69_pad_recursion σ b β₀ j + σ + b := by
  rw [infra_69_pad_recursion, WellFounded.fix_eq]
  rw [dif_neg (Order.not_isSuccPrelimit_succ j)]
  set hex : ∃ k, CovBy k (Order.succ j) := by
    by_contra hno
    exact Order.not_isSuccPrelimit_succ j (fun k hk => hno ⟨k, hk⟩)
  have hkj : Classical.choose hex = j := by
    have hspec := Classical.choose_spec hex
    have hcov : CovBy j (Order.succ j) := Order.covBy_succ j
    -- An ordinal has at most one immediate predecessor.
    rcases lt_trichotomy (Classical.choose hex) j with hlt | heq | hgt
    · exact absurd (Order.lt_succ j) (hspec.2 hlt)
    · exact heq
    · exact absurd hspec.1 (hcov.2 hgt)
  have hrec : infra_69_pad_recursion σ b β₀ (Classical.choose hex) =
      infra_69_pad_recursion σ b β₀ j := congrArg (infra_69_pad_recursion σ b β₀) hkj
  change (2 : Cardinal.{u}) ^ infra_69_pad_recursion σ b β₀ (Classical.choose hex) + σ + b =
    (2 : Cardinal.{u}) ^ infra_69_pad_recursion σ b β₀ j + σ + b
  rw [hrec]

theorem infra_69_pad_recursion_limit {σ b β₀ : Cardinal.{u}} {i : Ordinal.{u}}
    (h0 : i ≠ 0) (hsucc : ∀ j, i ≠ Order.succ j) :
    infra_69_pad_recursion σ b β₀ i =
      ⨆ j : Set.Iio i, infra_69_pad_recursion σ b β₀ j.1 := by
  have hlim : Order.IsSuccPrelimit i := fun j hj =>
    hsucc j (by
      -- `CovBy j i` on a successor order is `i = succ j`.
      apply le_antisymm
      · by_contra hlt
        exact hj.2 (Order.lt_succ j) (lt_of_not_ge hlt)
      · exact Order.succ_le_of_lt hj.1)
  rw [infra_69_pad_recursion, WellFounded.fix_eq, dif_pos hlim, if_neg h0]

theorem infra_69_pad_recursion_mono (σ b β₀ : Cardinal.{u}) :
    Monotone (infra_69_pad_recursion σ b β₀) := by
  intro i j hij
  refine WellFounded.induction
    (C := fun j => ∀ i, i ≤ j →
      infra_69_pad_recursion σ b β₀ i ≤ infra_69_pad_recursion σ b β₀ j)
    wellFounded_lt j ?_ i hij
  intro j ih i hij
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact le_rfl
  · by_cases h0 : j = 0
    · exact absurd hij (by rw [h0]; exact not_lt_of_ge (bot_le : (0 : Ordinal.{u}) ≤ i))
    · by_cases hsuc : ∃ k, j = Order.succ k
      · obtain ⟨k, hk⟩ := hsuc
        have hkj : k < j := by rw [hk]; exact Order.lt_succ k
        have hik : i ≤ k := by
          rw [hk] at hij
          exact (Order.lt_succ_iff).mp hij
        have hle : infra_69_pad_recursion σ b β₀ i ≤ infra_69_pad_recursion σ b β₀ k :=
          ih k hkj i hik
        rw [hk, infra_69_pad_recursion_succ]
        exact hle.trans ((le_of_lt (cantor _)).trans (le_self_add.trans le_self_add))
      · rw [infra_69_pad_recursion_limit h0 (fun k hk => hsuc ⟨k, hk⟩)]
        exact le_ciSup (f := fun t : Set.Iio j => infra_69_pad_recursion σ b β₀ t.1)
          bddAbove_of_small ⟨i, hij⟩

theorem infra_69_pad_recursion_mono_start {σ b a c : Cardinal.{u}} (hac : a ≤ c)
    (i : Ordinal.{u}) :
    infra_69_pad_recursion σ b a i ≤ infra_69_pad_recursion σ b c i := by
  refine WellFounded.induction
    (C := fun i => infra_69_pad_recursion σ b a i ≤ infra_69_pad_recursion σ b c i)
    wellFounded_lt i ?_
  intro i ih
  by_cases h0 : i = 0
  · rw [h0, infra_69_pad_recursion_zero, infra_69_pad_recursion_zero]
    exact hac
  · by_cases hsuc : ∃ j, i = Order.succ j
    · obtain ⟨j, hj⟩ := hsuc
      have hlt : j < i := by rw [hj]; exact Order.lt_succ j
      rw [hj, infra_69_pad_recursion_succ, infra_69_pad_recursion_succ]
      exact add_le_add (add_le_add_left
        (power_le_power_left two_ne_zero (ih j hlt)) σ) le_rfl
    · rw [infra_69_pad_recursion_limit h0 (fun j hj => hsuc ⟨j, hj⟩),
        infra_69_pad_recursion_limit h0 (fun j hj => hsuc ⟨j, hj⟩)]
      haveI : Nonempty (Set.Iio i) := ⟨⟨0,
        lt_of_le_of_ne (bot_le : (0 : Ordinal.{u}) ≤ i) (Ne.symm h0)⟩⟩
      exact ciSup_le fun t => (ih t.1 t.2).trans
        (le_ciSup (f := fun t : Set.Iio i => infra_69_pad_recursion σ b c t.1)
          bddAbove_of_small t)

theorem infra_69_pad_recursion_ge_start (σ b β₀ : Cardinal.{u}) (i : Ordinal.{u}) :
    β₀ ≤ infra_69_pad_recursion σ b β₀ i := by
  calc β₀ = infra_69_pad_recursion σ b β₀ 0 := (infra_69_pad_recursion_zero σ b β₀).symm
    _ ≤ infra_69_pad_recursion σ b β₀ i :=
      infra_69_pad_recursion_mono σ b β₀ (bot_le : (0 : Ordinal.{u}) ≤ i)

/-- **Infra `infra_69_pad_recursion_closed`.** The `σ⁺` supremum of the profile recursion lies
strictly below `μ`. This is the paper's closure under the whole recursion. It is not inherited
from `IsClosurePoint {D.t, g}`. -/
def infra_69_pad_recursion_closed (σ b β₀ μ : Cardinal.{u}) : Prop :=
  infra_69_pad_recursion σ b β₀ (Order.succ σ).ord < μ

theorem infra_69_pad_recursion_two_le (σ b β₀ : Cardinal.{u}) (j : Ordinal.{u}) :
    (2 : Cardinal.{u}) ^ infra_69_pad_recursion σ b β₀ j ≤
      infra_69_pad_recursion σ b β₀ (Order.succ j) := by
  rw [infra_69_pad_recursion_succ]
  exact le_self_add.trans le_self_add

theorem ord_card_le_of_lt_succ_ord {σ : Cardinal.{u}} {o : Ordinal.{u}}
    (h : o < (Order.succ σ).ord) : o.card ≤ σ := by
  by_contra hgt
  have hlt : σ < o.card := lt_of_not_ge hgt
  exact not_lt_of_ge
    ((Cardinal.ord_le_ord.mpr (Order.succ_le_of_lt hlt)).trans (Cardinal.ord_card_le o)) h

/-- One power of the start lies under the `σ⁺` value, once `σ` is infinite so that `(σ⁺).ord`
sits strictly above `1`. -/
theorem infra_69_pad_recursion_pow_start_le (σ b β₀ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    (2 : Cardinal.{u}) ^ β₀ ≤
      infra_69_pad_recursion σ b β₀ (Order.succ σ).ord := by
  have h1 : Order.succ (0 : Ordinal.{u}) < (Order.succ σ).ord :=
    (Cardinal.isSuccLimit_ord (hσ.trans (Order.le_succ σ))).succ_lt
      (Cardinal.isSuccLimit_ord (hσ.trans (Order.le_succ σ))).bot_lt
  refine le_trans ?_ (infra_69_pad_recursion_mono σ b β₀ h1.le)
  rw [infra_69_pad_recursion_succ, infra_69_pad_recursion_zero]
  exact le_self_add.trans le_self_add

/-! ## Such levels exist -/

/-- Countable iteration of one full `σ⁺` recursion. -/
noncomputable def padLevelTower (σ b κ : Cardinal.{u}) : ℕ → Cardinal.{u}
  | 0 => max κ (max σ (max b ℵ₀))
  | n + 1 => Order.succ (infra_69_pad_recursion σ b (padLevelTower σ b κ n) (Order.succ σ).ord)

theorem padLevelTower_strictMono (σ b κ : Cardinal.{u}) : StrictMono (padLevelTower σ b κ) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  exact (infra_69_pad_recursion_ge_start _ _ _ _).trans_lt (Order.lt_succ _)

theorem padLevelTower_le_iSup (σ b κ : Cardinal.{u}) (n : ℕ) :
    padLevelTower σ b κ n ≤ ⨆ n, padLevelTower σ b κ n :=
  le_ciSup (f := padLevelTower σ b κ) bddAbove_of_small n

/-- **Infra `infra_69_pad_exists_closed`.** Above any start there is a strong limit of
cofinality `ℵ₀` closed under the `σ⁺` profile recursion at every smaller test size. -/
theorem infra_69_pad_exists_closed (σ b κ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) (_hb : ℵ₀ ≤ b) :
    ∃ μ, κ ≤ μ ∧ IsWorkingLevel μ ∧
      ∀ β₀, β₀ < μ → infra_69_pad_recursion_closed σ b β₀ μ := by
  refine ⟨⨆ n, padLevelTower σ b κ n,
    (le_max_left κ _).trans (padLevelTower_le_iSup σ b κ 0), ?_, ?_⟩
  · have hinf : ℵ₀ ≤ ⨆ n, padLevelTower σ b κ n :=
      (le_max_of_le_right (le_max_of_le_right (le_max_right _ _))).trans
        (padLevelTower_le_iSup σ b κ 0)
    refine ⟨hinf, ⟨(aleph0_pos.trans_le hinf).ne', fun x hx => ?_⟩, ?_⟩
    · obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := padLevelTower σ b κ) bddAbove_of_small).mp hx
      have hxle : x ≤ padLevelTower σ b κ n := le_of_lt hn
      have hpow : (2 : Cardinal.{u}) ^ x ≤ (2 : Cardinal.{u}) ^ padLevelTower σ b κ n :=
        power_le_power_left two_ne_zero hxle
      have hF : (2 : Cardinal.{u}) ^ padLevelTower σ b κ n ≤
          infra_69_pad_recursion σ b (padLevelTower σ b κ n) (Order.succ σ).ord :=
        infra_69_pad_recursion_pow_start_le σ b _ hσ
      exact hpow.trans_lt (hF.trans_lt ((Order.lt_succ _).trans_le
        (padLevelTower_le_iSup σ b κ (n + 1))))
    · rw [Ordinal.iSup_ord]
      exact cof_iSup_nat_of_strictMono (fun n => (padLevelTower σ b κ n).ord)
        fun m n hmn => ord_lt_ord.mpr (padLevelTower_strictMono σ b κ hmn)
  · intro β₀ hβ
    obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := padLevelTower σ b κ) bddAbove_of_small).mp hβ
    exact (infra_69_pad_recursion_mono_start (le_of_lt hn) _).trans_lt
      ((Order.lt_succ _).trans_le (padLevelTower_le_iSup σ b κ (n + 1)))

/-! ## Down-set profile codes -/

variable {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I] {α : Type u}

/-- A profile code with no least element: labels, the order pattern of the formal support,
and, for each support position, the set of old points strictly below it together with the
set of old points strictly above it. -/
abbrev infra_69_pad_downsetCode (lab α : Type u) {I : Type u} (S : Set I) : Type u :=
  (α → lab) × Set ((α × ℕ) × (α × ℕ)) × (α × ℕ → Set ↥S × Set ↥S)

namespace Placement

open Classical in
/-- The down-set code of a placement over the old positions `S`. -/
noncomputable def downSetCode (P : Placement lab arity I α) (S : Set I) :
    infra_69_pad_downsetCode lab α S :=
  (fun a => (P.z a).label,
    {x | ∃ (hk : x.1.2 < arity (P.z x.1.1).label) (hl : x.2.2 < arity (P.z x.2.1).label),
      (P.z x.1.1).pos ⟨x.1.2, hk⟩ < (P.z x.2.1).pos ⟨x.2.2, hl⟩},
    fun x => if hk : x.2 < arity (P.z x.1).label then
        ({s : ↥S | P.f s.1 < (P.z x.1).pos ⟨x.2, hk⟩},
          {s : ↥S | (P.z x.1).pos ⟨x.2, hk⟩ < P.f s.1})
      else (∅, ∅))

end Placement

/-- **Infra `infra_69_pad_downset`.** Equal down-set codes are the same support profile.
Coincidence with an old point is the remaining comparison, when the point is neither below
nor above. -/
theorem infra_69_pad_downset {S : Set I} {P P' : Placement lab arity I α}
    (h : P.downSetCode S = P'.downSetCode S) : SameProfile S P P' := by
  have h1 : ∀ a, (P.z a).label = (P'.z a).label := fun a => congrFun (congrArg Prod.fst h) a
  refine ⟨h1, fun a b k l hk hl hk' hl' => ?_, fun a k hk hk' s hs => ?_⟩
  · have h2 := congrArg
      (fun c : infra_69_pad_downsetCode lab α S => ((a, k), (b, l)) ∈ c.2.1) h
    simp only [Placement.downSetCode, Set.mem_ofPred_eq, eq_iff_iff] at h2
    constructor
    · intro hlt
      obtain ⟨_, _, hlt'⟩ := h2.mp ⟨hk, hl, hlt⟩
      exact hlt'
    · intro hlt
      obtain ⟨_, _, hlt'⟩ := h2.mpr ⟨hk', hl', hlt⟩
      exact hlt'
  · have h3 := congrArg (fun c : infra_69_pad_downsetCode lab α S => c.2.2 (a, k)) h
    simp only [Placement.downSetCode, dite_eq_left hk, dite_eq_left hk'] at h3
    have hbelow := congrArg Prod.fst h3
    have habove := congrArg Prod.snd h3
    constructor
    · have hmem := congrArg (fun t : Set ↥S => (⟨s, hs⟩ : ↥S) ∈ t) hbelow
      simpa [Set.mem_setOf_eq] using hmem
    · have hmem := congrArg (fun t : Set ↥S => (⟨s, hs⟩ : ↥S) ∈ t) habove
      simpa [Set.mem_setOf_eq] using hmem

/-- **Infra `infra_69_pad_count`.** There are at most `2^{|S| + σ + b}` down-set profiles. -/
theorem infra_69_pad_count {σ b : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hb : ℵ₀ ≤ b)
    (hα : #α ≤ σ) (hlab : #lab ≤ b) (S : Set I) :
    #(infra_69_pad_downsetCode lab α S) ≤ (2 : Cardinal.{u}) ^ (#S + σ + b) := by
  classical
  set ρ : Cardinal.{u} := #S + σ + b
  have hSρ : #S ≤ ρ :=
    le_trans (le_self_add : #S ≤ #S + σ) (le_self_add : #S + σ ≤ #S + σ + b)
  have hσρ : σ ≤ ρ := by
    have h1 : σ ≤ σ + b := le_self_add
    have h2 : σ + b ≤ #S + (σ + b) := le_add_left le_rfl
    have h3 : #S + (σ + b) = ρ := by simp [ρ, add_assoc]
    exact h1.trans (h2.trans h3.le)
  have hbρ : b ≤ ρ := by
    calc b ≤ b + σ := le_self_add
      _ ≤ b + σ + #S := le_self_add
      _ = ρ := by simp [ρ, add_comm, add_left_comm, add_assoc]
  have hρinf : ℵ₀ ≤ ρ := hσ.trans hσρ
  have hσne : σ ≠ 0 := ne_of_gt (aleph0_pos.trans_le hσ)
  have hbne : b ≠ 0 := ne_of_gt (aleph0_pos.trans_le hb)
  have hpos : #(α × ℕ) ≤ σ := mk_prod_nat_le hσ hα
  have hpos2 : #((α × ℕ) × (α × ℕ)) ≤ σ := mk_prod_le_of_le hσ hpos hpos
  have hmul : b * σ ≤ max b σ := by
    rcases le_total b σ with h | h
    · rw [mul_comm, mul_eq_left hσ h hbne, max_eq_right h]
    · rw [mul_eq_left hb h hσne, max_eq_left h]
  have hmulρ : b * σ ≤ ρ := hmul.trans (max_le hbρ hσρ)
  have h1 : #(α → lab) ≤ (2 : Cardinal.{u}) ^ ρ := by
    rw [mk_arrow, lift_id, lift_id]
    calc #lab ^ #α ≤ b ^ #α := power_le_power_right hlab
      _ ≤ b ^ σ := power_le_power_left hbne hα
      _ ≤ ((2 : Cardinal.{u}) ^ b) ^ σ := power_le_power_right (le_of_lt (cantor b))
      _ = (2 : Cardinal.{u}) ^ (b * σ) := by rw [← power_mul]
      _ ≤ (2 : Cardinal.{u}) ^ ρ := power_le_power_left two_ne_zero hmulρ
  have h2 : #(Set ((α × ℕ) × (α × ℕ))) ≤ (2 : Cardinal.{u}) ^ ρ := by
    rw [mk_set]
    exact power_le_power_left two_ne_zero (hpos2.trans hσρ)
  have hSS : #(Set ↥S × Set ↥S) ≤ (2 : Cardinal.{u}) ^ ρ := by
    rw [mk_prod, mk_set, lift_id]
    have hsum : #S + #S ≤ ρ := by
      have hmax : ℵ₀ ≤ max #S ℵ₀ := le_max_right _ _
      exact (add_le_of_le hmax (le_max_left _ _) (le_max_left _ _)).trans
        (max_le (hSρ.trans le_rfl) (hσ.trans hσρ))
    rw [← power_add]
    exact power_le_power_left two_ne_zero hsum
  have hne2 : (2 : Cardinal.{u}) ^ ρ ≠ 0 :=
    ne_of_gt (aleph0_pos.trans ((cantor ℵ₀).trans_le
      (power_le_power_left two_ne_zero hρinf)))
  have h3 : #(α × ℕ → Set ↥S × Set ↥S) ≤ (2 : Cardinal.{u}) ^ ρ := by
    rw [mk_arrow, lift_id, lift_id]
    have hpow : #(Set ↥S × Set ↥S) ^ #(α × ℕ) ≤ ((2 : Cardinal.{u}) ^ ρ) ^ σ :=
      (power_le_power_right hSS).trans (power_le_power_left hne2 hpos)
    rw [← power_mul, mul_eq_left hρinf hσρ hσne] at hpow
    exact hpow
  simp only [mk_prod, lift_id]
  have hself : (2 : Cardinal.{u}) ^ ρ * (2 : Cardinal.{u}) ^ ρ = (2 : Cardinal.{u}) ^ ρ :=
    mul_eq_self (le_of_lt ((cantor ℵ₀).trans_le (power_le_power_left two_ne_zero hρinf)))
  exact (mul_le_mul' h1 (mul_le_mul' h2 h3)).trans
    ((mul_le_mul' le_rfl hself.le).trans hself.le)

/-! ## Stages along `σ⁺` -/

/-- **Infra `infra_69_pad_stage_card`.** If each step at most doubles the recursion value
into a power set, every stage of `stageSet` stays under the recursion, and so does the
union of the steps. `mk_stageSet_le` does not apply: its bound is one fixed `χ`. -/
theorem infra_69_pad_stage_card {σ b β₀ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hσβ : σ ≤ β₀)
    (hb : ℵ₀ ≤ b) (hbβ : b ≤ β₀) {A : Type u} (G : Set A → Set A)
    (hG : ∀ (i : Below (Order.succ σ)) (X : Set A),
      #X ≤ infra_69_pad_recursion σ b β₀ (i : Ordinal) →
      #(G X) ≤ (2 : Cardinal.{u}) ^ infra_69_pad_recursion σ b β₀ (i : Ordinal)) :
    (∀ i : Below (Order.succ σ),
        #(stageSet G i) ≤ infra_69_pad_recursion σ b β₀ (i : Ordinal)) ∧
      #(⋃ i : Below (Order.succ σ), G (stageSet G i)) ≤
        infra_69_pad_recursion σ b β₀ (Order.succ σ).ord := by
  have hmem (i : Below (Order.succ σ)) : (i : Ordinal) < (Order.succ σ).ord :=
    (Ordinal.ToType.toOrd i).2
  have hstage : ∀ i : Below (Order.succ σ),
      #(stageSet G i) ≤ infra_69_pad_recursion σ b β₀ (i : Ordinal) := by
    intro i
    refine WellFounded.induction
      (C := fun i : Below (Order.succ σ) =>
        #(stageSet G i) ≤ infra_69_pad_recursion σ b β₀ (i : Ordinal))
      wellFounded_lt i ?_
    intro i ih
    rw [stageSet_eq]
    refine (mk_iUnion_le _).trans ?_
    have hsup : (⨆ j : {j : Below (Order.succ σ) // j < i}, #(G (stageSet G j.1))) ≤
        infra_69_pad_recursion σ b β₀ (i : Ordinal) := by
      refine ciSup_le' fun j => ?_
      refine (hG j.1 (stageSet G j.1) (ih j.1 j.2)).trans ?_
      refine le_trans (infra_69_pad_recursion_two_le σ b β₀ (j.1 : Ordinal)) ?_
      exact infra_69_pad_recursion_mono σ b β₀
        (Order.succ_le_of_lt ((Ordinal.ToType.mk.symm.lt_iff_lt).mp j.2))
    have hpred : #{j : Below (Order.succ σ) // j < i} ≤ σ := by
      let f : {j : Below (Order.succ σ) // j < i} → (i : Ordinal).ToType :=
        fun j => Ordinal.ToType.mk ⟨(j.1 : Ordinal), (Ordinal.ToType.mk.symm.lt_iff_lt).mp j.2⟩
      have hinj : Function.Injective f := by
        intro j j' (h : f j = f j')
        have hI : Ordinal.ToType.toOrd (f j) = Ordinal.ToType.toOrd (f j') :=
          congrArg Ordinal.ToType.toOrd h
        have hL := (Ordinal.ToType.mk (o := (i : Ordinal))).symm_apply_apply
          ⟨(j.1 : Ordinal), (Ordinal.ToType.mk.symm.lt_iff_lt).mp j.2⟩
        have hR := (Ordinal.ToType.mk (o := (i : Ordinal))).symm_apply_apply
          ⟨(j'.1 : Ordinal), (Ordinal.ToType.mk.symm.lt_iff_lt).mp j'.2⟩
        have hord : (j.1 : Ordinal) = (j'.1 : Ordinal) := by
          have hsub : (⟨(j.1 : Ordinal), (Ordinal.ToType.mk.symm.lt_iff_lt).mp j.2⟩ :
              Set.Iio (i : Ordinal)) =
              ⟨(j'.1 : Ordinal), (Ordinal.ToType.mk.symm.lt_iff_lt).mp j'.2⟩ := by
            rw [← hL, ← hR]; exact hI
          exact congrArg (fun s : Set.Iio (i : Ordinal) => (s : Ordinal)) hsub
        apply Subtype.ext
        exact (Ordinal.ToType.mk (o := (Order.succ σ).ord)).symm.injective
          (Subtype.ext (show (Ordinal.ToType.toOrd j.1).1 = (Ordinal.ToType.toOrd j'.1).1 from hord))
      exact (mk_le_of_injective hinj).trans (by
        rw [mk_toType]; exact ord_card_le_of_lt_succ_ord (hmem i))
    have hge : σ ≤ infra_69_pad_recursion σ b β₀ (i : Ordinal) :=
      hσβ.trans (infra_69_pad_recursion_ge_start σ b β₀ (i : Ordinal))
    have hinf : ℵ₀ ≤ infra_69_pad_recursion σ b β₀ (i : Ordinal) := hσ.trans hge
    have hσne : σ ≠ 0 := ne_of_gt (aleph0_pos.trans_le hσ)
    exact (mul_le_mul' hpred hsup).trans
      ((mul_comm _ _).trans (mul_eq_left hinf hge hσne)).le
  refine ⟨hstage, ?_⟩
  have hlim : Order.IsSuccLimit (Order.succ σ).ord :=
    Cardinal.isSuccLimit_ord (hσ.trans (Order.le_succ σ))
  refine (mk_iUnion_le _).trans ?_
  have hΘ : #(Below (Order.succ σ)) = Order.succ σ := mk_ord_toType _
  have hstep : ∀ i : Below (Order.succ σ),
      #(G (stageSet G i)) ≤ infra_69_pad_recursion σ b β₀ (Order.succ σ).ord := by
    intro i
    refine (hG i _ (hstage i)).trans ?_
    refine le_trans (infra_69_pad_recursion_two_le σ b β₀ (i : Ordinal)) ?_
    exact infra_69_pad_recursion_mono σ b β₀ (hlim.succ_lt (hmem i)).le
  have hσle : Order.succ σ ≤ infra_69_pad_recursion σ b β₀ (Order.succ σ).ord := by
    refine le_trans (Order.succ_le_of_lt (cantor σ)) ?_
    exact (power_le_power_left two_ne_zero hσβ).trans
      (infra_69_pad_recursion_pow_start_le σ b β₀ hσ)
  have hinf : ℵ₀ ≤ infra_69_pad_recursion σ b β₀ (Order.succ σ).ord :=
    hσ.trans (hσβ.trans (infra_69_pad_recursion_ge_start σ b β₀ _))
  exact (mul_le_mul' hΘ.le (ciSup_le' hstep)).trans
    ((mul_comm _ _).trans (mul_eq_left hinf hσle
      (ne_of_gt (lt_of_lt_of_le aleph0_pos (hσ.trans (Order.le_succ σ)))))).le

/-! ## The obstruction -/

variable [CategoricalUnbounded K] {E : OrderPresentation K} {D : StableDiagram K}

/-- **Infra `infra_69_pad_obstruction`.** One placement solves every prescription of size at
most the test size `β₀`, once the `σ⁺` profile recursion from `β₀` fits under `‖E(I)‖`.
Profiles are down-set codes. Continuations, no-event comparison, event codes, and one local
placement are the well-ordered lemmas, which do not use `WellFoundedLT I`. -/
theorem infra_69_pad_obstruction {I : Type u} [LinearOrder I] [Nonempty I] {α : Type u}
    (σ b β₀ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) (hb : ℵ₀ ≤ b) (hσβ : σ ≤ β₀) (hbβ : b ≤ β₀)
    (hα : #α ≤ σ) (hlab : #E.lab ≤ b)
    (hcardI : D.t (σ + infra_69_pad_recursion σ b β₀ (Order.succ σ).ord) ≤
      Model.card (E.obj I))
    (q : ∀ {β : Type u},
      #β ≤ infra_69_pad_recursion σ b β₀ (Order.succ σ).ord →
        (β → (E.obj I).carrier) → α ⊕ β → (E.obj I).carrier)
    (hnat : ∀ {β : Type u}
      (hβ : #β ≤ infra_69_pad_recursion σ b β₀ (Order.succ σ).ord)
      (p : β → (E.obj I).carrier)
      (hβ' : #β ≤ σ + infra_69_pad_recursion σ b β₀ (Order.succ σ).ord),
      D.same hβ' (orderPresentation_obj_mem E I) (orderPresentation_obj_mem E I)
        hcardI hcardI (fun b => q hβ p (Sum.inr b)) p)
    (hcoh : ∀ {β β' : Type u}
      (hβ : #β ≤ infra_69_pad_recursion σ b β₀ (Order.succ σ).ord)
      (hβ' : #β' ≤ infra_69_pad_recursion σ b β₀ (Order.succ σ).ord)
      (p : β → (E.obj I).carrier) (ι : β' → β)
      (hj : #(α ⊕ β') ≤ σ + infra_69_pad_recursion σ b β₀ (Order.succ σ).ord),
      D.same hj (orderPresentation_obj_mem E I) (orderPresentation_obj_mem E I)
        hcardI hcardI (fun i => q hβ p (Sum.map id ι i)) (q hβ' (fun b => p (ι b)))) :
    ∃ P : Placement E.lab E.arity I α,
      ∀ {β : Type u} (hβ : #β ≤ β₀) (p : β → (E.obj I).carrier)
        (hj : #(α ⊕ β) ≤ σ + β₀),
        P.Solves E D (σ + infra_69_pad_recursion σ b β₀ (Order.succ σ).ord)
          (hj.trans (add_le_add_right
            (infra_69_pad_recursion_ge_start σ b β₀ (Order.succ σ).ord) σ))
          p (q (hβ.trans (infra_69_pad_recursion_ge_start σ b β₀ _)) p) := by
  classical
  let γ : Cardinal.{u} := infra_69_pad_recursion σ b β₀ (Order.succ σ).ord
  have hβγ : β₀ ≤ γ := infra_69_pad_recursion_ge_start σ b β₀ _
  have hργ : σ + β₀ ≤ σ + γ := add_le_add_right hβγ σ
  have hρinf : ℵ₀ ≤ σ + γ := hσ.trans (le_self_add : σ ≤ σ + γ)
  have hI : K.Mem (E.obj I) := orderPresentation_obj_mem E I
  have hjoint : ∀ {β : Type u}, #β ≤ γ → #(α ⊕ β) ≤ σ + γ := fun hβ => by
    rw [mk_sum, lift_id, lift_id]; exact add_le_add hα hβ
  have hγadd : γ ≤ σ + γ := by rw [add_comm]; exact le_self_add
  have hpar : ∀ {β : Type u}, #β ≤ γ → #β ≤ σ + γ := fun hβ => hβ.trans hγadd
  have hrestr : ∀ (P : Placement E.lab E.arity I α) {β β' : Type u} (hβ : #β ≤ γ)
      (hβ' : #β' ≤ γ) (p : β → (E.obj I).carrier) (ι : β' → β),
      P.Solves E D (σ + γ) (hjoint hβ) p (q hβ p) →
      P.Solves E D (σ + γ) (hjoint hβ') (fun b => p (ι b)) (q hβ' (fun b => p (ι b))) := by
    intro P β β' hβ hβ' p ι h
    refine h.comp hρinf (hjoint hβ') ι _ ?_
    refine sameNaturalDiagram_of_D_same E D (hjoint hβ') _ _ hcardI hI ?_
    simp only [realize_supportTermOf]
    exact hcoh hβ hβ' p ι (hjoint hβ')
  by_contra hno
  push Not at hno
  have hbad : ∀ P : Placement E.lab E.arity I α, ∃ Y : Set (E.obj I).carrier,
      ∃ hY : #Y ≤ β₀, ¬ P.Solves E D (σ + γ) (hjoint (hY.trans hβγ))
        (Subtype.val : ↥Y → (E.obj I).carrier) (q (hY.trans hβγ) Subtype.val) := by
    intro P
    obtain ⟨β, hβ, p, hj, hfail⟩ := hno P
    refine ⟨Set.range p, mk_range_le.trans hβ, ?_⟩
    intro hsol
    exact hfail (hrestr P ((mk_range_le.trans hβ).trans hβγ) (hβ.trans hβγ)
      Subtype.val (Set.rangeFactorization p) hsol)
  choose bad hbadcard hbadfail using hbad
  let G : Set (E.obj I).carrier → Set (E.obj I).carrier := fun X =>
    X ∪ ⋃ k : infra_69_pad_downsetCode E.lab α (paramSupport E X),
      if h : ∃ P : Placement E.lab E.arity I α,
          P.downSetCode (paramSupport E X) = k ∧
            P.NoEvent (paramSupport E X) Set.univ
        then bad (Classical.choose h) else ∅
  have hGsub : ∀ X, X ⊆ G X := fun X => Set.subset_union_left
  have hGbound : ∀ (i : Below (Order.succ σ)) (X : Set (E.obj I).carrier),
      #X ≤ infra_69_pad_recursion σ b β₀ (i : Ordinal) →
      #(G X) ≤ (2 : Cardinal.{u}) ^ infra_69_pad_recursion σ b β₀ (i : Ordinal) := by
    intro i X hX
    set δ : Cardinal.{u} := infra_69_pad_recursion σ b β₀ (i : Ordinal)
    have hδinf : ℵ₀ ≤ δ := hσ.trans (hσβ.trans (infra_69_pad_recursion_ge_start σ b β₀ _))
    have hδσ : σ ≤ δ := hσβ.trans (infra_69_pad_recursion_ge_start σ b β₀ _)
    have hδb : b ≤ δ := hbβ.trans (infra_69_pad_recursion_ge_start σ b β₀ _)
    have hδβ : β₀ ≤ δ := infra_69_pad_recursion_ge_start σ b β₀ _
    have hS : #(paramSupport E X) ≤ δ := (mk_paramSupport_le E hδinf hX)
    have hcode : #(infra_69_pad_downsetCode E.lab α (paramSupport E X)) ≤
        (2 : Cardinal.{u}) ^ δ := by
      refine (infra_69_pad_count hσ hb hα hlab (paramSupport E X)).trans ?_
      refine power_le_power_left two_ne_zero ?_
      exact (add_le_of_le hδinf (add_le_of_le hδinf hS hδσ) hδb)
    have h2inf : ℵ₀ ≤ (2 : Cardinal.{u}) ^ δ :=
      le_of_lt ((cantor ℵ₀).trans_le (power_le_power_left two_ne_zero hδinf))
    refine (mk_union_le _ _).trans (add_le_of_le h2inf (hX.trans (le_of_lt (cantor δ))) ?_)
    have hself : (2 : Cardinal.{u}) ^ δ * δ = (2 : Cardinal.{u}) ^ δ :=
      mul_eq_left h2inf (le_of_lt (cantor δ)) (ne_of_gt (aleph0_pos.trans_le hδinf))
    refine (mk_iUnion_le _).trans ((mul_le_mul' hcode (ciSup_le' fun _ => ?_)).trans hself.le)
    split_ifs with h
    · exact (hbadcard _).trans hδβ
    · simp
  obtain ⟨hXcard, hUnion⟩ :=
    infra_69_pad_stage_card hσ hσβ hb hbβ G hGbound
  let X : Below (Order.succ σ) → Set (E.obj I).carrier := stageSet G
  have hXs : #(⋃ i, G (X i)) ≤ γ := hUnion
  obtain ⟨Ps, hPs⟩ := exists_local_placement (D := D) hρinf (hjoint hXs) (hpar hXs) hcardI
    (Subtype.val : ↥(⋃ i, G (X i)) → (E.obj I).carrier) (q hXs Subtype.val) (hnat hXs _ _)
  have hGspec : ∀ (P₀ : Placement E.lab E.arity I α) (X0 : Set (E.obj I).carrier),
      ∃ P' : Placement E.lab E.arity I α,
        SameProfile (paramSupport E X0) P₀ P' ∧
        P'.NoEvent (paramSupport E X0) Set.univ ∧ bad P' ⊆ G X0 := by
    intro P₀ X0
    obtain ⟨P₁, hprof, hne⟩ := exists_inert_continuation P₀ (paramSupport E X0)
    have hex : ∃ P : Placement E.lab E.arity I α,
        P.downSetCode (paramSupport E X0) = P₁.downSetCode (paramSupport E X0) ∧
          P.NoEvent (paramSupport E X0) Set.univ := ⟨P₁, rfl, hne⟩
    refine ⟨Classical.choose hex,
      hprof.trans (infra_69_pad_downset (Classical.choose_spec hex).1).symm,
      (Classical.choose_spec hex).2, fun y hy => ?_⟩
    refine Or.inr (Set.mem_iUnion.mpr ⟨P₁.downSetCode (paramSupport E X0), ?_⟩)
    rw [dite_eq_left hex]
    exact hy
  have hevent : ∀ i, ¬ Ps.NoEvent (paramSupport E (X i)) (paramSupport E (G (X i))) := by
    intro i hNE
    obtain ⟨P', hprof, hP'ne, hbadsub⟩ := hGspec Ps (X i)
    have hsubs : G (X i) ⊆ ⋃ i, G (X i) := Set.subset_iUnion (fun i => G (X i)) i
    have hGc : #(G (X i)) ≤ γ := by
      have hGi : #(G (X i)) ≤ (2 : Cardinal.{u}) ^ infra_69_pad_recursion σ b β₀ (i : Ordinal) :=
        hGbound i _ (hXcard i)
      have hlt : Order.succ (i : Ordinal) ≤ (Order.succ σ).ord :=
        ((Cardinal.isSuccLimit_ord (hσ.trans (Order.le_succ σ))).succ_lt
          (Ordinal.ToType.toOrd i).2).le
      exact hGi.trans ((infra_69_pad_recursion_two_le σ b β₀ (i : Ordinal)).trans
        (infra_69_pad_recursion_mono σ b β₀ hlt))
    have h1 : Ps.Solves E D (σ + γ) (hjoint hGc)
        (Subtype.val : ↥(G (X i)) → (E.obj I).carrier) (q hGc Subtype.val) :=
      hrestr Ps hXs hGc Subtype.val (Set.inclusion hsubs) hPs
    have h2 : SameNaturalDiagram K E D (σ + γ) (hjoint hGc)
        (Ps.joint (fun x : ↥(G (X i)) => supportTermOf E x.1))
        (P'.joint (fun x : ↥(G (X i)) => supportTermOf E x.1)) :=
      sameNaturalDiagram_of_sameProfile_noEvent hρinf (hjoint hGc) Ps P'
        (paramSupport_mono E (hGsub (X i))) (paramSupport_nonempty E _) hprof hNE
        (hP'ne.mono (Set.subset_univ _)) _ (fun x => termSupport_subset_paramSupport E x.2)
    have h3 : P'.Solves E D (σ + γ) (hjoint hGc)
        (Subtype.val : ↥(G (X i)) → (E.obj I).carrier) (q hGc Subtype.val) :=
      (sameNaturalDiagram_symm E D h2).trans hρinf h1
    exact hbadfail P' (hrestr P' hGc ((hbadcard P').trans hβγ) Subtype.val
      (Set.inclusion hbadsub) h3)
  choose ev hev using fun i => Ps.exists_event_of_not_noEvent (hevent i)
  have hinj : Function.Injective ev := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hj := hev j
      rw [← hij] at hj
      exact (hev i).not_later (paramSupport_mono E (step_subset_stageSet G hlt)) hj
    · have hi := hev i
      rw [hij] at hi
      exact (hev j).not_later (paramSupport_mono E (step_subset_stageSet G hlt)) hi
  have hΘ : #(Below (Order.succ σ)) = Order.succ σ := mk_ord_toType _
  have hle : Order.succ σ ≤ σ :=
    hΘ.symm.le.trans ((mk_le_of_injective hinj).trans (mk_eventCode_le hσ hα))
  exact absurd hle (not_le.mpr (Order.lt_succ σ))

end
end AEC
