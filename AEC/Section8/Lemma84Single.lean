module

public import AEC.Section8.PairOrbitSingle
public import AEC.Section7.IsolationBound

@[expose] public section

/-!
# Lemma 8.4 for the Prop 5.6 scheme: testing pieces (cycle 96)

English (Lemma 8.4): "For each σ < ν there is a bound k(σ) < ν, uniform in these objects, with the
following property. If v ∈ T and v′ ∈ T′ have length at most σ, their comparisons on joint tests
from U and C of total size at most k(σ) determine their comparisons on all such tests of total size
< ν." The one-base testing bound comes from the differing-test form of Proposition 7.3
(`infra_73_differing_test`) and Theorem 6.6 (`infra_72_diagramEq_of_sameGalois`).
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **One-base testing bound (Lemma 8.4, tests from `C`).** At a level `μ` closed for the
`σ`-recursion, two same-level tuples over one base `C` of size at most `σ` whose diagrams agree on
every test from `C` of size at most `g σ + LS(K)` agree on every test from `C` of size `< μ`. -/
theorem infra_84_base_testing_single (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {C : P.scheme.Object μ hμ}
    (q q' : TupleOver K oneVertexShape P.scheme hμ C) {ι : Type u}
    (e : q.idx ≃ ι) (e' : q'.idx ≃ ι)
    (hqν : q.ν = μ) (hq'ν : q'.ν = μ) (hidx : #q.idx ≤ σ)
    (hsmall : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ C)),
      #β ≤ P.g σ + ls K →
      P.scheme.DiagramEq (X := q.host) (Y := q'.host)
        (alignJoint e (typeJoint (p := q) Z)) (alignJoint e' (typeJoint (p := q') Z))) :
    ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ C)), #β < μ →
      P.scheme.DiagramEq (X := q.host) (Y := q'.host)
        (alignJoint e (typeJoint (p := q) Z)) (alignJoint e' (typeJoint (p := q') Z)) := by
  intro β Z hβ
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #q.idx < μ := hidx.trans_lt hσlt
  have hG : SameGaloisType q q' e e' := by
    by_contra hne
    obtain ⟨β', Z', hβ', hnot⟩ :=
      infra_73_differing_test P σ hσ hμ hrec hσSucc q q' e e' hqν hq'ν hidx hidxμ hne
    exact hnot (hsmall Z' hβ')
  have hι : #ι < μ := by
    rw [← Cardinal.mk_congr e]; exact hidxμ
  exact infra_72_diagramEq_of_sameGalois hG Z hqν hq'ν hι hβ

/-- The profile recursion is monotone in the test size `σ`. -/
theorem infra_84_pad_recursion_mono_sigma {σ σ' b c : Cardinal.{u}} (hσ : σ ≤ σ')
    (i : Ordinal.{u}) :
    infra_69_pad_recursion σ b c i ≤ infra_69_pad_recursion σ' b c i := by
  refine WellFounded.induction
    (C := fun i => infra_69_pad_recursion σ b c i ≤ infra_69_pad_recursion σ' b c i)
    wellFounded_lt i ?_
  intro i ih
  by_cases h0 : i = 0
  · rw [h0, infra_69_pad_recursion_zero, infra_69_pad_recursion_zero]
  · by_cases hsuc : ∃ j, i = Order.succ j
    · obtain ⟨j, hj⟩ := hsuc
      have hlt : j < i := by rw [hj]; exact Order.lt_succ j
      rw [hj, infra_69_pad_recursion_succ, infra_69_pad_recursion_succ]
      exact add_le_add (add_le_add
        (power_le_power_left two_ne_zero (ih j hlt)) hσ) le_rfl
    · rw [infra_69_pad_recursion_limit h0 (fun j hj => hsuc ⟨j, hj⟩),
        infra_69_pad_recursion_limit h0 (fun j hj => hsuc ⟨j, hj⟩)]
      have : Nonempty (Set.Iio i) := ⟨⟨0,
        lt_of_le_of_ne (bot_le : (0 : Ordinal.{u}) ≤ i) (Ne.symm h0)⟩⟩
      exact ciSup_le fun t => (ih t.1 t.2).trans
        (le_ciSup (f := fun t : Set.Iio i => infra_69_pad_recursion σ' b c t.1)
          bddAbove_of_small t)

/-- Countable iteration closing under `{t, g}`, powers, and the profile recursion at every test
size below the current stage (diagonal in `σ`). -/
noncomputable def infra_84_diagTower (t g : Cardinal.{u} → Cardinal.{u})
    (b κ : Cardinal.{u}) : ℕ → Cardinal.{u}
  | 0 => max κ (max b ℵ₀)
  | n + 1 =>
      Order.succ (max
        ((2 : Cardinal.{u}) ^ infra_84_diagTower t g b κ n ⊔
          closureBound t g (infra_84_diagTower t g b κ n))
        (infra_69_pad_recursion (infra_84_diagTower t g b κ n) b
          (infra_84_diagTower t g b κ n) (Order.succ (infra_84_diagTower t g b κ n)).ord))

theorem infra_84_diagTower_strictMono (t g : Cardinal.{u} → Cardinal.{u})
    (b κ : Cardinal.{u}) : StrictMono (infra_84_diagTower t g b κ) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have hlt : infra_84_diagTower t g b κ n <
      max ((2 : Cardinal.{u}) ^ infra_84_diagTower t g b κ n ⊔
          closureBound t g (infra_84_diagTower t g b κ n))
        (infra_69_pad_recursion (infra_84_diagTower t g b κ n) b
          (infra_84_diagTower t g b κ n) (Order.succ (infra_84_diagTower t g b κ n)).ord) :=
    (cantor _).trans_le (le_sup_left.trans (le_max_left _ _))
  exact hlt.trans (Order.lt_succ _)

theorem infra_84_diagTower_le_iSup (t g : Cardinal.{u} → Cardinal.{u})
    (b κ : Cardinal.{u}) (n : ℕ) :
    infra_84_diagTower t g b κ n ≤ ⨆ n, infra_84_diagTower t g b κ n :=
  le_ciSup (f := infra_84_diagTower t g b κ) bddAbove_of_small n

/-- **Diagonal recursion tail (Lemma 8.4 uniformity).** Unboundedly many eligible levels are
closed for the `σ`-recursion simultaneously at every infinite `σ` below them. -/
theorem infra_84_diagonal_tail (P : SingleModelData K) :
    Tail P.eligible {μ | μ ∈ P.eligible ∧
      ∀ σ, ℵ₀ ≤ σ → σ < μ → μ ∈ recursionClosedLevels P σ} := by
  refine ⟨fun μ hμ => hμ.1, fun κ => ?_⟩
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let t := P.D.t
  let g := P.g
  let tower := infra_84_diagTower t g b (max κ (Order.succ (ls K)))
  let μ : Cardinal.{u} := ⨆ n, tower n
  have hmono : Monotone tower := (infra_84_diagTower_strictMono t g b _).monotone
  have hμge : max κ (Order.succ (ls K)) ≤ μ :=
    (le_max_left _ _).trans (infra_84_diagTower_le_iSup t g b _ 0)
  have hinf : ℵ₀ ≤ μ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      (infra_84_diagTower_le_iSup t g b _ 0))
  have hSL : μ.IsStrongLimit := by
    refine ⟨(aleph0_pos.trans_le hinf).ne', fun x hx => ?_⟩
    obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := tower) bddAbove_of_small).mp hx
    exact (power_le_power_left two_ne_zero (le_of_lt hn)).trans_lt
      (((le_sup_left : (2 : Cardinal.{u}) ^ tower n ≤ _).trans (le_max_left _ _)).trans_lt
        ((Order.lt_succ _).trans_le (infra_84_diagTower_le_iSup t g b _ (n + 1))))
  have hcof : Ordinal.cof μ.ord = ℵ₀ := by
    rw [Ordinal.iSup_ord]
    exact cof_iSup_nat_of_strictMono (fun n => (tower n).ord)
      fun i j hij => ord_lt_ord.mpr
        (infra_84_diagTower_strictMono t g b (max κ (Order.succ (ls K))) hij)
  have hworking : IsWorkingLevel μ := ⟨hinf, hSL, hcof⟩
  have hclosed : IsClosurePoint {t, g} μ := by
    refine ⟨hworking, fun u hu => ⟨fun θ hθinf hθμ => ?_⟩⟩
    obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := tower) bddAbove_of_small).mp hθμ
    have hbound : t θ ⊔ g θ ≤ closureBound t g (tower n) :=
      le_closureBound t g (le_of_lt hn)
    have hstep : closureBound t g (tower n) < tower (n + 1) :=
      ((le_sup_right : closureBound t g (tower n) ≤ _).trans (le_max_left _ _)).trans_lt
        (Order.lt_succ _)
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact (le_sup_left.trans hbound).trans_lt (hstep.trans_le
        (infra_84_diagTower_le_iSup t g b _ (n + 1)))
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (le_sup_right.trans hbound).trans_lt (hstep.trans_le
        (infra_84_diagTower_le_iSup t g b _ (n + 1)))
  have hls : ls K < μ :=
    (Order.lt_succ (ls K)).trans_le ((le_max_right κ _).trans hμge)
  have hel : μ ∈ P.eligible := ⟨hclosed, hls⟩
  refine ⟨μ, (le_max_left _ _).trans hμge, hel, fun σ _ hσμ => ⟨hel, fun β₀ hβ => ?_⟩⟩
  obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := tower) bddAbove_of_small).mp hσμ
  obtain ⟨m, hm⟩ := (lt_ciSup_iff' (f := tower) bddAbove_of_small).mp hβ
  have hσx : σ ≤ tower (max n m) := (le_of_lt hn).trans (hmono (le_max_left n m))
  have hβx : β₀ ≤ tower (max n m) := (le_of_lt hm).trans (hmono (le_max_right n m))
  have h1 := infra_84_pad_recursion_mono_sigma (b := b) (c := β₀) hσx (Order.succ σ).ord
  have h2 := infra_69_pad_recursion_mono_start (σ := tower (max n m)) (b := b) hβx
    (Order.succ σ).ord
  have h3 := infra_69_pad_recursion_mono (tower (max n m)) b (tower (max n m))
    (Cardinal.ord_le_ord.mpr (Order.succ_le_succ hσx))
  have h4 : infra_69_pad_recursion (tower (max n m)) b (tower (max n m))
      (Order.succ (tower (max n m))).ord < tower (max n m + 1) :=
    (le_max_right _ _).trans_lt (Order.lt_succ _)
  exact (h1.trans (h2.trans h3)).trans_lt
    (h4.trans_le (infra_84_diagTower_le_iSup t g b _ _))

end AEC
