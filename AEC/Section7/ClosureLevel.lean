module

public import AEC.Section7.ThetaShrink
public import AEC.Section6.FreshStrip

@[expose] public section

/-!
# Prop 7.8: the closure level of the `θ⁺` shrink (`infra_78_theta_shrink_closure_level`)

Paper (Prop 7.8): "Let `λ` be a sufficiently closed eligible level ... For every infinite
`θ < λ` ... The closure requirements at the output level are uniform functions of bounded
arities; they do not require `θ` to have been fixed before the level was chosen."

So the tail of `proposition_7_8` is existential and chosen before `θ`, but the closure it asks
for is closure under the uniform bound functions at EVERY bounded arity. The tail
`infra_78_closedTail P` below is such a tail: each of its levels `μ` is

* in `infra_73_tailSet P σ` (recursion-closed at `σ` and `h(σ) < μ`) for EVERY infinite
  `σ < μ`, and
* a limit of eligible levels.

It is unbounded (`infra_78_closedTail_tail`), built by the same `ω`-tower as
`infra_615_tail` (recursion closure passes to the supremum by monotonicity of the profile
recursion in `σ`, start and length: `infra_615_pad_mono_arg`,
`infra_69_pad_recursion_mono_start`, `infra_69_pad_recursion_mono`), with `h` bounded on
`[0, x]` by a supremum (no monotonicity of `h` assumed) and a next eligible level inserted at
every step.

`infra_78_theta_shrink_closure_level`: at every level of that tail and for every infinite
`θ < μ`, there are an eligible `λ` and `ρ` with `θ⁺ ≤ λ ≤ σ := λ`, `μ ∈ infra_73_tailSet P λ`,
`λ < ρ`, `ρ^λ = ρ`, `ρ⁺ < μ` — every closure hypothesis of `infra_78_theta_shrink` on the
levels. Choosing this better-closed tail in `proposition_7_8` is faithful to the English
(the tail is existential), adds no hypothesis to 7.8 and does not weaken its conclusion.
-/

universe u

open Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- The next eligible level (in `infra_615_closed`) at or above `x⁺`. -/
noncomputable def infra_78_nextElig (P : SingleModelData K) (x : Cardinal.{u}) : Cardinal.{u} :=
  Classical.choose ((infra_615_tail P).2 (Order.succ x))

theorem infra_78_nextElig_spec (P : SingleModelData K) (x : Cardinal.{u}) :
    Order.succ x ≤ infra_78_nextElig P x ∧ infra_78_nextElig P x ∈ P.eligible :=
  let h := Classical.choose_spec ((infra_615_tail P).2 (Order.succ x))
  ⟨h.1, h.2.1⟩

/-- `h` bounded on `[0, x]` (a supremum over a small set; no monotonicity of `h` used). -/
noncomputable def infra_78_hBound (P : SingleModelData K) (x : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ σ : Set.Iic x, infra_73_h P σ.1

theorem infra_78_le_hBound (P : SingleModelData K) {σ x : Cardinal.{u}} (h : σ ≤ x) :
    infra_73_h P σ ≤ infra_78_hBound P x :=
  le_ciSup (f := fun σ : Set.Iic x => infra_73_h P σ.1) bddAbove_of_small ⟨σ, h⟩

/-- The `ω`-tower of the closure level. -/
noncomputable def infra_78_closedTower (P : SingleModelData K) (κ : Cardinal.{u}) :
    ℕ → Cardinal.{u}
  | 0 => max κ (Order.succ (max (ls K) ℵ₀))
  | n + 1 =>
      let prev := infra_78_closedTower P κ n
      Order.succ (max
        (max ((2 : Cardinal.{u}) ^ prev ⊔ closureBound P.D.t P.g prev)
          (infra_69_pad_recursion prev (max (ls K) ℵ₀) prev (Order.succ prev).ord))
        (max (infra_78_hBound P prev) (infra_78_nextElig P prev)))

theorem infra_78_closedTower_succ_gt (P : SingleModelData K) (κ : Cardinal.{u}) (n : ℕ) :
    max (max ((2 : Cardinal.{u}) ^ infra_78_closedTower P κ n ⊔
        closureBound P.D.t P.g (infra_78_closedTower P κ n))
      (infra_69_pad_recursion (infra_78_closedTower P κ n) (max (ls K) ℵ₀)
        (infra_78_closedTower P κ n) (Order.succ (infra_78_closedTower P κ n)).ord))
      (max (infra_78_hBound P (infra_78_closedTower P κ n))
        (infra_78_nextElig P (infra_78_closedTower P κ n))) <
      infra_78_closedTower P κ (n + 1) :=
  Order.lt_succ _

theorem infra_78_closedTower_strictMono (P : SingleModelData K) (κ : Cardinal.{u}) :
    StrictMono (infra_78_closedTower P κ) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  refine ((cantor _).trans_le ?_).trans (infra_78_closedTower_succ_gt P κ n)
  exact le_sup_left.trans ((le_max_left _ _).trans (le_max_left _ _))

theorem infra_78_closedTower_le_iSup (P : SingleModelData K) (κ : Cardinal.{u}) (n : ℕ) :
    infra_78_closedTower P κ n ≤ ⨆ n, infra_78_closedTower P κ n :=
  le_ciSup (f := infra_78_closedTower P κ) bddAbove_of_small n

/-- **The closure tail of Prop 7.8.** Eligible levels `μ` lying in `infra_73_tailSet P σ` for
every infinite `σ < μ`, and limits of eligible levels. -/
def infra_78_closedTail (P : SingleModelData K) : Set Cardinal.{u} :=
  {μ | μ ∈ P.eligible ∧ (∀ σ, ℵ₀ ≤ σ → σ < μ → μ ∈ infra_73_tailSet P σ) ∧
    ∀ θ, θ < μ → ∃ ℓ, ℓ ∈ P.eligible ∧ θ < ℓ ∧ ℓ < μ}

/-- **`infra_78_closedTail` is a tail** (unbounded in the eligible levels). -/
theorem infra_78_closedTail_tail (P : SingleModelData K) :
    Tail P.eligible (infra_78_closedTail P) := by
  refine ⟨fun μ hμ => hμ.1, fun κ => ?_⟩
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let t := P.D.t
  let g := P.g
  let tower := infra_78_closedTower P κ
  let μ : Cardinal.{u} := ⨆ n, tower n
  have hle : ∀ n, tower n ≤ μ := infra_78_closedTower_le_iSup P κ
  have hgt := infra_78_closedTower_succ_gt P κ
  have hμge : κ ≤ μ := le_trans (le_max_left _ _) (hle 0)
  have hinf : ℵ₀ ≤ μ :=
    le_trans (le_max_right (ls K) ℵ₀)
      (le_trans (le_of_lt (Order.lt_succ (max (ls K) ℵ₀)))
        (le_trans (le_max_right κ _) (hle 0)))
  have hbelow : ∀ x, x < μ → ∃ n, x < tower n := fun x hx =>
    (lt_ciSup_iff' (f := tower) bddAbove_of_small).mp hx
  have hSL : μ.IsStrongLimit := by
    refine ⟨(aleph0_pos.trans_le hinf).ne', fun x hx => ?_⟩
    obtain ⟨n, hn⟩ := hbelow x hx
    have h2 : (2 : Cardinal.{u}) ^ tower n < tower (n + 1) :=
      lt_of_le_of_lt (le_sup_left.trans ((le_max_left _ _).trans (le_max_left _ _))) (hgt n)
    exact (power_le_power_left two_ne_zero (le_of_lt hn)).trans_lt (h2.trans_le (hle (n + 1)))
  have hcof : Ordinal.cof μ.ord = ℵ₀ := by
    rw [Ordinal.iSup_ord]
    exact cof_iSup_nat_of_strictMono (fun n => (tower n).ord)
      fun i j hij => ord_lt_ord.mpr (infra_78_closedTower_strictMono P κ hij)
  have hworking : IsWorkingLevel μ := ⟨hinf, hSL, hcof⟩
  have hclosedFun : IsClosurePoint {t, g} μ := by
    refine ⟨hworking, fun u hu => ⟨fun θ _ hθμ => ?_⟩⟩
    obtain ⟨n, hn⟩ := hbelow θ hθμ
    have hbound : t θ ⊔ g θ ≤ closureBound t g (tower n) := le_closureBound t g (le_of_lt hn)
    have hstep : closureBound t g (tower n) < μ :=
      ((le_sup_right.trans ((le_max_left _ _).trans (le_max_left _ _))).trans_lt
        (hgt n)).trans_le (hle (n + 1))
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact (le_sup_left.trans hbound).trans_lt hstep
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (le_sup_right.trans hbound).trans_lt hstep
  have hls : ls K < μ := by
    refine (Order.lt_succ (ls K)).trans_le ?_
    refine le_trans ?_ (hle 0)
    exact le_trans (Order.succ_le_succ (le_max_left (ls K) ℵ₀)) (le_max_right κ _)
  have hel : μ ∈ P.eligible := ⟨hclosedFun, hls⟩
  have hrec : ∀ σ, ℵ₀ ≤ σ → σ < μ → ∀ β₀, β₀ < μ →
      infra_69_pad_recursion_closed σ b β₀ μ := by
    intro σ hσinf hσμ β₀ hβ
    obtain ⟨nσ, hnσ⟩ := hbelow σ hσμ
    obtain ⟨nβ, hnβ⟩ := hbelow β₀ hβ
    let N := max nσ nβ
    have hσN : σ ≤ tower N :=
      (le_of_lt hnσ).trans ((infra_78_closedTower_strictMono P κ).monotone (le_max_left nσ nβ))
    have hβN : β₀ ≤ tower N :=
      (le_of_lt hnβ).trans ((infra_78_closedTower_strictMono P κ).monotone (le_max_right nσ nβ))
    have hord : (Order.succ σ).ord ≤ (Order.succ (tower N)).ord :=
      ord_le_ord.mpr (Order.succ_le_succ hσN)
    have hle' : infra_69_pad_recursion σ b β₀ (Order.succ σ).ord ≤
        infra_69_pad_recursion (tower N) b (tower N) (Order.succ (tower N)).ord := by
      refine le_trans (infra_615_pad_mono_arg hσN _) ?_
      refine le_trans (infra_69_pad_recursion_mono_start hβN _) ?_
      exact infra_69_pad_recursion_mono _ _ _ hord
    exact hle'.trans_lt (((le_max_right _ _).trans (le_max_left _ _)).trans_lt
      ((hgt N).trans_le (hle (N + 1))))
  refine ⟨μ, hμge, hel, ?_, ?_⟩
  · intro σ hσ hσμ
    refine ⟨⟨hel, fun β₀ hβ => hrec σ hσ hσμ β₀ hβ⟩, ?_⟩
    obtain ⟨n, hn⟩ := hbelow σ hσμ
    have hh : infra_73_h P σ < tower (n + 1) :=
      ((infra_78_le_hBound P hn.le).trans ((le_max_left _ _).trans (le_max_right _ _))).trans_lt
        (hgt n)
    have hσ1 : σ < tower (n + 1) := hn.trans (infra_78_closedTower_strictMono P κ (Nat.lt_succ_self n))
    have hmax : max σ (infra_73_h P σ) < μ := (max_lt hσ1 hh).trans_le (hle (n + 1))
    exact Order.succ_le_of_lt hmax
  · intro θ hθ
    obtain ⟨n, hn⟩ := hbelow θ hθ
    obtain ⟨hs, hel'⟩ := infra_78_nextElig_spec P (tower n)
    refine ⟨infra_78_nextElig P (tower n), hel', hn.trans ((Order.lt_succ _).trans_le hs), ?_⟩
    exact (((le_max_right _ _).trans (le_max_right _ _)).trans_lt (hgt n)).trans_le (hle (n + 1))

/-- **`infra_78_theta_shrink_closure_level`.** At every level `μ` of the closure tail
`infra_78_closedTail P` and for every infinite `θ < μ` there are an eligible level `λ` and a
cardinal `ρ` meeting every level hypothesis of `infra_78_theta_shrink` with `σ := λ`:
`θ⁺ ≤ λ`, `λ < μ`, `μ ∈ infra_73_tailSet P λ`, `λ < ρ`, `ρ ^ λ = ρ`, `ρ⁺ < μ` (`ρ = 2^λ`). -/
theorem infra_78_theta_shrink_closure_level (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ infra_78_closedTail P) {θ : Cardinal.{u}} (hθμ : θ < μ) :
    ∃ ℓ ρ : Cardinal.{u}, ℓ ∈ P.eligible ∧ Order.succ θ ≤ ℓ ∧ ℓ < μ ∧
      μ ∈ infra_73_tailSet P ℓ ∧ ℓ < ρ ∧ ρ ^ ℓ = ρ ∧ Order.succ ρ < μ := by
  obtain ⟨hel, htail, hcof⟩ := hμ
  obtain ⟨ℓ, hℓel, hθℓ, hℓμ⟩ := hcof θ hθμ
  have hℓ : ℵ₀ ≤ ℓ := P.aleph0_le hℓel
  have hSL : μ.IsStrongLimit := hel.1.working.strongLimit
  refine ⟨ℓ, 2 ^ ℓ, hℓel, Order.succ_le_of_lt hθℓ, hℓμ, htail ℓ hℓ hℓμ, cantor ℓ, ?_, ?_⟩
  · rw [← power_mul, mul_eq_self hℓ]
  · exact hSL.isSuccLimit.succ_lt (hSL.2 hℓμ)

end AEC
