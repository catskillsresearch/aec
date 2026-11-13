module

public import AEC.Section6.SupportClosure
public import AEC.Section6.StationaryFreeExtension
public import AEC.Section4.ClosedLevelAmalgam
public import AEC.Section5.SingleModelPackage
public import AEC.Section5.TermTemplate
public import AEC.Section4.CompactPlacement

@[expose] public section

/-!
# Proposition 6.15 — universality of a fresh strip

Same-level packaging for `SingleModelData`, with `G = P.E` on a well-order. The fresh strip
is terminal: `H = ℕ ×ₗ lvlOrder μ`, so every old position lies to the left of every fiber and
no side-of-`V` coloring is required. General presentations `G ≠ F` and two-sided strips are
deferred (they are what Corollary 6.16 needs).
-/

namespace AEC
section

universe u

open Cardinal FirstOrder Function Set Sum

attribute [local instance] Classical.propDecidable

variable {K : AbstractElementaryClass.{u}}

/-! ## Levels closed for every smaller tuple length -/

/-- The padded profile recursion is monotone in the tuple-length parameter. -/
theorem infra_615_pad_mono_arg {σ σ' b β₀ : Cardinal.{u}} (hσ : σ ≤ σ') (i : Ordinal.{u}) :
    infra_69_pad_recursion σ b β₀ i ≤ infra_69_pad_recursion σ' b β₀ i := by
  refine WellFounded.induction
    (C := fun i => infra_69_pad_recursion σ b β₀ i ≤ infra_69_pad_recursion σ' b β₀ i)
    wellFounded_lt i ?_
  intro i ih
  by_cases h0 : i = 0
  · rw [h0, infra_69_pad_recursion_zero, infra_69_pad_recursion_zero]
  · by_cases hsuc : ∃ j, i = Order.succ j
    · obtain ⟨j, hj⟩ := hsuc
      have hlt : j < i := by rw [hj]; exact Order.lt_succ j
      rw [hj, infra_69_pad_recursion_succ, infra_69_pad_recursion_succ]
      exact add_le_add (add_le_add (power_le_power_left two_ne_zero (ih j hlt)) hσ) le_rfl
    · rw [infra_69_pad_recursion_limit h0 (fun j hj => hsuc ⟨j, hj⟩),
        infra_69_pad_recursion_limit h0 (fun j hj => hsuc ⟨j, hj⟩)]
      haveI : Nonempty (Set.Iio i) := ⟨⟨0,
        lt_of_le_of_ne (bot_le : (0 : Ordinal.{u}) ≤ i) (Ne.symm h0)⟩⟩
      exact ciSup_le fun t => (ih t.1 t.2).trans
        (le_ciSup (f := fun t : Set.Iio i => infra_69_pad_recursion σ' b β₀ t.1)
          bddAbove_of_small t)

/-- Countable tower closing `{D.t, P.g}` and the profile recursion at every smaller length. -/
noncomputable def infra_615_tower (P : SingleModelData K) (κ : Cardinal.{u}) : ℕ → Cardinal.{u}
  | 0 => max κ (Order.succ (max (ls K) ℵ₀))
  | n + 1 =>
      let prev := infra_615_tower P κ n
      Order.succ (max
        ((2 : Cardinal.{u}) ^ prev ⊔ closureBound P.D.t P.g prev)
        (infra_69_pad_recursion prev (max (ls K) ℵ₀) prev (Order.succ prev).ord))

theorem infra_615_tower_strictMono (P : SingleModelData K) (κ : Cardinal.{u}) :
    StrictMono (infra_615_tower P κ) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  have hlt : infra_615_tower P κ n <
      max ((2 : Cardinal.{u}) ^ infra_615_tower P κ n ⊔
          closureBound P.D.t P.g (infra_615_tower P κ n))
        (infra_69_pad_recursion (infra_615_tower P κ n) (max (ls K) ℵ₀)
          (infra_615_tower P κ n) (Order.succ (infra_615_tower P κ n)).ord) :=
    (cantor _).trans_le (le_sup_left.trans (le_max_left _ _))
  exact hlt.trans (Order.lt_succ _)

theorem infra_615_tower_le_iSup (P : SingleModelData K) (κ : Cardinal.{u}) (n : ℕ) :
    infra_615_tower P κ n ≤ ⨆ n, infra_615_tower P κ n :=
  le_ciSup (f := infra_615_tower P κ) bddAbove_of_small n

/-- Eligible levels at which every smaller infinite length is profile-recursion closed.
Approximation sequences for the exhaustion are taken at those lengths. -/
def infra_615_closed (P : SingleModelData K) : Set Cardinal.{u} :=
  {μ | μ ∈ P.eligible ∧ ∀ σ, ℵ₀ ≤ σ → σ < μ → ∀ β₀, β₀ < μ →
    infra_69_pad_recursion_closed σ (max (ls K) ℵ₀) β₀ μ}

theorem infra_615_tail (P : SingleModelData K) :
    infra_615_closed P ⊆ P.eligible ∧
      ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ infra_615_closed P := by
  refine ⟨fun μ hμ => hμ.1, fun κ => ?_⟩
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let t := P.D.t
  let g := P.g
  let tower := infra_615_tower P κ
  let μ : Cardinal.{u} := ⨆ n, tower n
  have hμge : κ ≤ μ := le_trans (le_max_left _ _) (infra_615_tower_le_iSup P κ 0)
  have hinf : ℵ₀ ≤ μ :=
    le_trans (le_max_right (ls K) ℵ₀)
      (le_trans (le_of_lt (Order.lt_succ (max (ls K) ℵ₀)))
        (le_trans (le_max_right κ _) (infra_615_tower_le_iSup P κ 0)))
  have hSL : μ.IsStrongLimit := by
    refine ⟨(aleph0_pos.trans_le hinf).ne', fun x hx => ?_⟩
    obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := tower) bddAbove_of_small).mp hx
    exact (power_le_power_left two_ne_zero (le_of_lt hn)).trans_lt
      (((le_sup_left : (2 : Cardinal.{u}) ^ tower n ≤ _).trans (le_max_left _ _)).trans_lt
        ((Order.lt_succ _).trans_le (infra_615_tower_le_iSup P κ (n + 1))))
  have hcof : Ordinal.cof μ.ord = ℵ₀ := by
    rw [Ordinal.iSup_ord]
    exact cof_iSup_nat_of_strictMono (fun n => (tower n).ord)
      fun i j hij => ord_lt_ord.mpr (infra_615_tower_strictMono P κ hij)
  have hworking : IsWorkingLevel μ := ⟨hinf, hSL, hcof⟩
  have hclosedFun : IsClosurePoint {t, g} μ := by
    refine ⟨hworking, fun u hu => ⟨fun θ _ hθμ => ?_⟩⟩
    obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := tower) bddAbove_of_small).mp hθμ
    have hbound : t θ ⊔ g θ ≤ closureBound t g (tower n) := le_closureBound t g (le_of_lt hn)
    have hstep : closureBound t g (tower n) < tower (n + 1) :=
      ((le_sup_right : closureBound t g (tower n) ≤ _).trans (le_max_left _ _)).trans_lt
        (Order.lt_succ _)
    rcases Set.mem_insert_iff.mp hu with rfl | hu
    · exact (le_sup_left.trans hbound).trans_lt
        (hstep.trans_le (infra_615_tower_le_iSup P κ (n + 1)))
    · rw [Set.mem_singleton_iff] at hu
      subst hu
      exact (le_sup_right.trans hbound).trans_lt
        (hstep.trans_le (infra_615_tower_le_iSup P κ (n + 1)))
  have hls : ls K < μ := by
    refine (Order.lt_succ (ls K)).trans_le ?_
    refine le_trans ?_ (infra_615_tower_le_iSup P κ 0)
    refine le_trans (Order.succ_le_succ (le_max_left (ls K) ℵ₀))
      (le_max_right κ _)
  have hrec : ∀ σ, ℵ₀ ≤ σ → σ < μ → ∀ β₀, β₀ < μ →
      infra_69_pad_recursion_closed σ b β₀ μ := by
    intro σ hσinf hσμ β₀ hβ
    obtain ⟨nσ, hnσ⟩ := (lt_ciSup_iff' (f := tower) bddAbove_of_small).mp hσμ
    obtain ⟨nβ, hnβ⟩ := (lt_ciSup_iff' (f := tower) bddAbove_of_small).mp hβ
    let N := max nσ nβ
    have hσN : σ ≤ tower N :=
      (le_of_lt hnσ).trans ((infra_615_tower_strictMono P κ).monotone (le_max_left nσ nβ))
    have hβN : β₀ ≤ tower N :=
      (le_of_lt hnβ).trans ((infra_615_tower_strictMono P κ).monotone (le_max_right nσ nβ))
    have hord : (Order.succ σ).ord ≤ (Order.succ (tower N)).ord :=
      ord_le_ord.mpr (Order.succ_le_succ hσN)
    have hle : infra_69_pad_recursion σ b β₀ (Order.succ σ).ord ≤
        infra_69_pad_recursion (tower N) b (tower N) (Order.succ (tower N)).ord := by
      refine le_trans (infra_615_pad_mono_arg hσN _) ?_
      refine le_trans (infra_69_pad_recursion_mono_start hβN _) ?_
      exact infra_69_pad_recursion_mono _ _ _ hord
    have hlt : infra_69_pad_recursion (tower N) b (tower N) (Order.succ (tower N)).ord <
        tower (N + 1) := by
      refine lt_of_le_of_lt (le_max_right _ _) (Order.lt_succ _)
    exact hle.trans_lt (hlt.trans_le (infra_615_tower_le_iSup P κ (N + 1)))
  exact ⟨μ, hμge, ⟨⟨hclosedFun, hls⟩, hrec⟩⟩

/-! ## The terminal strip -/

/-- `J` with a terminal strip of countably many copies of the level well-order. -/
abbrev FreshOrder (J : Type u) (μ : Cardinal.{u}) : Type u :=
  J ⊕ₗ (ℕ ×ₗ lvlOrder μ)

/-- The `n`-th fiber, sitting in the right summand. -/
def freshFiber {J : Type u} (μ : Cardinal.{u}) (n : ℕ) : Set (FreshOrder J μ) :=
  Set.range (fun a : lvlOrder μ => Sum.inrₗ (toLex (n, a)))

theorem freshFiber_subset_inr {J : Type u} (μ : Cardinal.{u}) (n : ℕ) :
    freshFiber (J := J) μ n ⊆ Set.range Sum.inr := by
  intro x hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨toLex (n, a), rfl⟩

theorem freshFiber_card {J : Type u} {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (n : ℕ) :
    #(freshFiber (J := J) μ n) = μ := by
  let f : lvlOrder μ → FreshOrder J μ := fun a => Sum.inrₗ (toLex (n, a))
  have hinj : Injective f := by
    intro a b h
    have h' : toLex (n, a) = toLex (n, b) := by
      simpa [f, Sum.inrₗ] using h
    have := congrArg ofLex h'
    simpa using (Prod.ext_iff.mp this).2
  have hrange : freshFiber (J := J) μ n = Set.range f := rfl
  rw [hrange, mk_range_eq f hinj, mk_lvlOrder hμ]

theorem freshFiber_disjoint {J : Type u} (μ : Cardinal.{u}) :
    Pairwise (Disjoint on freshFiber (J := J) μ) := by
  intro m n hmn
  change Disjoint (freshFiber μ m) (freshFiber μ n)
  rw [Set.disjoint_left]
  intro x hm hn
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  have hpt : toLex (m, a) = toLex (n, b) := by
    have h := ha.trans hb.symm
    simpa [Sum.inrₗ] using h
  exact hmn (congrArg Prod.fst (congrArg ofLex hpt))

theorem freshFiber_convex {J : Type u} [LinearOrder J] (μ : Cardinal.{u}) (n : ℕ) :
    IsConvexRegion (freshFiber (J := J) μ n) := by
  intro x hx y hy z hxz hzy
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rcases hz : ofLex z with j | p
  · exfalso
    rw [← toLex_ofLex z, hz] at hxz
    exact Sum.Lex.not_inr_le_inl hxz
  · have hz' : z = Sum.inrₗ p := by rw [← toLex_ofLex z, hz]
    subst hz'
    have hle1 : toLex (n, a) ≤ p := (Sum.Lex.inr_le_inr_iff).mp hxz
    have hle2 : p ≤ toLex (n, b) := (Sum.Lex.inr_le_inr_iff).mp hzy
    have hk1 := Prod.Lex.toLex_le_toLex.mp
      (show toLex (n, a) ≤ toLex (ofLex p) by simpa [toLex_ofLex] using hle1)
    have hk2 := Prod.Lex.toLex_le_toLex.mp
      (show toLex (ofLex p) ≤ toLex (n, b) by simpa [toLex_ofLex] using hle2)
    rcases hk1 with hlt | ⟨hk, _hac⟩
    · rcases hk2 with hlt' | ⟨hk', _⟩
      · exact (lt_asymm hlt hlt').elim
      · rw [← hk'] at hlt
        exact (lt_irrefl _ hlt).elim
    · have hfst : (ofLex p).1 = n := by simpa using hk.symm
      have heq : p = toLex (n, (ofLex p).2) := by
        rw [← toLex_ofLex p]
        exact congrArg toLex (Prod.ext hfst rfl)
      exact ⟨(ofLex p).2, congrArg Sum.inrₗ heq.symm⟩

theorem freshOrder_card {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    #(ℕ ×ₗ lvlOrder μ) = μ := by
  change #(ℕ × lvlOrder μ) = μ
  rw [Cardinal.mk_prod, Cardinal.mk_nat, Cardinal.lift_aleph0, mk_lvlOrder hμ]
  simp only [Cardinal.lift_id']
  exact mul_eq_right hμ hμ aleph0_ne_zero

/-- **Infra `infra_615_strip`.** The terminal strip `H = ℕ ×ₗ lvlOrder μ`, its fibers, and the
left inclusion of `J`. -/
theorem infra_615_strip {J : Type u} [LinearOrder J] [WellFoundedLT J] [Nonempty J]
    {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hJ : #J = μ) :
    ∃ (H : Type u) (_ : LinearOrder H) (_ : WellFoundedLT H) (_ : Nonempty H)
      (emb : J ↪o (J ⊕ₗ H)),
      #H = μ ∧
      (∃ V : ℕ → Set (J ⊕ₗ H),
        (∀ n, IsConvexRegion (V n) ∧ #(V n) = μ) ∧
        Pairwise (Disjoint on V) ∧
        (∀ n, V n ⊆ Set.range Sum.inr)) ∧
      H = (ℕ ×ₗ lvlOrder μ) ∧ emb = sumLexEmbedLeftIncl J H := by
  refine ⟨ℕ ×ₗ lvlOrder μ, inferInstance, inferInstance, ?_, sumLexEmbedLeftIncl J _,
    freshOrder_card hμ, ?_, rfl, rfl⟩
  · rw [← mk_ne_zero_iff, freshOrder_card hμ]
    exact (aleph0_pos.trans_le hμ).ne'
  · refine ⟨freshFiber μ, ?_⟩
    refine ⟨fun n => ⟨freshFiber_convex μ n, freshFiber_card hμ n⟩, freshFiber_disjoint μ,
      freshFiber_subset_inr μ⟩

/-! ## Realizing one bounded tuple in the next fiber -/

/-- **Infra `infra_615_realize_in_fiber`.** A bounded tuple in a strong `μ`-extension of
`E(I)` has a lift in `E(I ⊕ₗ lvlOrder μ)`. The fresh summand is the single fiber. The
argument is an approximation sequence, the widened support closure, saturation into
`E(S ∪ fiber)`, and the tests of Theorem 6.6. -/
theorem infra_615_realize_in_fiber
    (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ infra_615_closed P)
    {I : Type u} [LinearOrder I] [Nonempty I] [WellFoundedLT I]
    (hI : #I = μ)
    {B : Model K.τ}
    (incl : Language.Embedding K.τ (P.E.obj I).carrier B.carrier)
    (hB : K.Mem B) (hstrong : K.Strong incl) (hcard : Model.card B = μ)
    {α : Type u} (d : α → B.carrier) (hα : #α < μ) :
    ∃ z : α → (P.E.obj (I ⊕ₗ lvlOrder μ)).carrier,
      LiftsTuple P.E P.D hB incl μ (sumLexEmbedLeftIncl I (lvlOrder μ)) d z := by
  classical
  have hμel : μ ∈ P.eligible := hμ.1
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  have hL : ClosedLevel K P.E P.D P.g μ :=
    ClosedLevel.of_closurePoint P.tester hμel.1 hμel.2
  by_cases hempty : IsEmpty α
  · letI := hempty
    refine ⟨fun i => isEmptyElim i, ?_⟩
    have hIμ : ∀ ρ, ℵ₀ ≤ ρ → ρ < μ → P.D.t ρ ≤ Model.card (P.E.obj I) := by
      intro ρ hρinf hρμ
      exact (hL.t_lt hρinf hρμ).le.trans (P.card_obj_eq hμel I hI).ge
    have h := liftsTuple_of_base (E := P.E) (D := P.D) (hB := hB) (incl := incl)
      hstrong hIμ (sumLexEmbedLeftIncl I (lvlOrder μ)) (fun i : α => isEmptyElim i)
    have hdz : (fun i : α => incl (isEmptyElim i)) = d := funext fun i => isEmptyElim i
    have hzz : (fun i : α => P.E.map (sumLexEmbedLeftIncl I (lvlOrder μ)) (isEmptyElim i)) =
        fun i : α => isEmptyElim i := funext fun i => isEmptyElim i
    rw [hdz, hzz] at h
    exact h
  · -- nonempty tuple: approximate, close supports, saturate into one fiber, test by 6.6
    let σ : Cardinal.{u} := max (#α) ℵ₀
    have hσ : ℵ₀ ≤ σ := le_max_right _ _
    have hσμ : σ < μ := max_lt hα (P.aleph0_lt hμel)
    have hgμ : P.g σ < μ := hL.g_lt hσ hσμ
    let τ : Cardinal.{u} := max (P.g σ + ls K) ℵ₀
    have hτinf : ℵ₀ ≤ τ := le_max_right _ _
    have hτμ : τ < μ :=
      max_lt (add_lt_of_lt (P.aleph0_le hμel) hgμ (P.ls_lt hμel)) (P.aleph0_lt hμel)
    have hgle : P.g σ + ls K ≤ τ := le_max_left _ _
    let κApx : Cardinal.{u} := (2 : Cardinal.{u}) ^ max σ τ
    have hmaxμ : max σ τ < μ := max_lt hσμ hτμ
    have hκμ : κApx < μ := hμel.1.working.strongLimit.isStrongPrelimit hmaxμ
    have hκinf : ℵ₀ ≤ κApx :=
      (hσ.trans (le_max_left σ τ)).trans (le_of_lt (cantor (max σ τ)))
    have hprod : κApx * #α < μ := by
      have hσle : σ ≤ κApx := (le_max_left σ τ).trans (le_of_lt (cantor (max σ τ)))
      have hmul : κApx * σ = κApx :=
        mul_eq_left hκinf hσle (ne_of_gt (aleph0_pos.trans_le hσ))
      have hle : κApx * #α ≤ κApx * σ := mul_le_mul' le_rfl (le_max_left _ _)
      exact (hle.trans (le_of_eq hmul)).trans_lt hκμ
    have hIA : Model.card (P.E.obj I) = μ := P.card_obj_eq hμel I hI
    let A := SMObject.ofModel (P.E.obj I) (P.hE I) hIA
    let Bobj := SMObject.ofModel B hB hcard
    let eA := SMObject.ofModelEquiv (P.E.obj I) (P.hE I) hIA
    let eB := SMObject.ofModelEquiv B hB hcard
    let toB : Language.Embedding K.τ A.model.carrier B.carrier :=
      incl.comp eA.symm.toEmbedding
    have htoB : K.Strong toB :=
      K.strong_trans _ _ (strong_of_equiv K eA.symm A.mem) hstrong
    let toBobj := eB.toEmbedding.comp toB
    have htoBobj : K.Strong toBobj :=
      K.strong_trans _ _ htoB (strong_of_equiv K eB hB)
    let p : TupleOver K oneVertexShape P.scheme hμel A :=
      { ν := μ
        hν := hμel
        host := Bobj
        incl := oneVertexArrow toBobj htoBobj
        incl_arrow := trivial
        idx := α
        val := fun i => Bobj.occ (eB (d i)) }
    have hβ₀ : max (max σ τ) (max (ls K) ℵ₀) < μ :=
      max_lt (max_lt hσμ hτμ) (max_lt (P.ls_lt hμel) (P.aleph0_lt hμel))
    obtain ⟨seq, hseqτ, hseqκ⟩ :=
      P.exists_approximationSequence hμel A p rfl σ τ κApx hσ hσμ (le_max_left (#α) ℵ₀)
        hτinf hτμ hκinf hκμ hprod (hμ.2 σ hσ hσμ _ hβ₀)
    let seqElt : seq.κIndex × α → (P.E.obj I).carrier :=
      fun ij => eA.symm (A.val (seq.family ij.1 ij.2))
    let Tset : Set I := ⋃ ij, Set.range (supportTermOf P.E (seqElt ij)).pos
    have hTset : #↥Tset ≤ κApx := by
      haveI : Nonempty α := not_isEmpty_iff.mp hempty
      haveI : Nonempty seq.κIndex :=
        mk_ne_zero_iff.mp (by rw [hseqκ]; exact (aleph0_pos.trans_le hκinf).ne')
      have hσle : σ ≤ κApx := (le_max_left σ τ).trans (le_of_lt (cantor (max σ τ)))
      have hmulσ : κApx * σ = κApx :=
        mul_eq_left hκinf hσle (ne_of_gt (aleph0_pos.trans_le hσ))
      have hidx : #(seq.κIndex × α) ≤ κApx := by
        rw [mk_prod, lift_id, lift_id, hseqκ]
        exact (mul_le_mul' le_rfl (le_max_left (#α) ℵ₀)).trans (le_of_eq hmulσ)
      have hfin : ∀ ij, #(Set.range (supportTermOf P.E (seqElt ij)).pos) ≤ ℵ₀ := fun ij => by
        have h := mk_range_le_lift (f := (supportTermOf P.E (seqElt ij)).pos)
        rw [lift_uzero] at h
        refine h.trans ?_
        rw [mk_fin, lift_natCast]
        exact natCast_le_aleph0
      have hsup : (⨆ ij, #(Set.range (supportTermOf P.E (seqElt ij)).pos)) ≤ ℵ₀ :=
        ciSup_le' hfin
      exact ((mk_iUnion_le _).trans (mul_le_mul' hidx hsup)).trans
        (le_of_eq (mul_eq_left hκinf hκinf aleph0_ne_zero))
    let Tstar : ↥Tset → I := Subtype.val
    let i0 : I := Classical.arbitrary I
    let color : I → ℕ := fun _ => 0
    let χC : Cardinal.{u} := max σ τ
    have hχC : ℵ₀ ≤ χC := hσ.trans (le_max_left σ τ)
    have hχClam : χC ≤ κApx := (le_of_lt (cantor χC)).trans
      (by rw [show κApx = (2 : Cardinal.{u}) ^ χC from rfl])
    obtain ⟨S, hS0, _hTmem, hScard, hclose⟩ :=
      lemma_6_14_proof (J := I) color χC κApx hχC hχClam
        Tstar hTset ({i0} : Set I) (by
          rw [mk_singleton]
          exact one_le_aleph0.trans hκinf)
    have hSne : S.Nonempty := ⟨i0, hS0 (by simp)⟩
    letI : Nonempty ↥S := ⟨⟨i0, hS0 (by simp)⟩⟩
    let eS : ↥S ↪o I := OrderEmbedding.subtype (· ∈ S)
    have h2μ : (2 : Cardinal.{u}) ^ κApx < μ :=
      hμel.1.working.strongLimit.isStrongPrelimit hκμ
    have hSμ : #↥S < μ := hScard.trans_lt h2μ
    have hsum : #↥S + ls K < μ := add_lt_of_lt (P.aleph0_le hμel) hSμ (P.ls_lt hμel)
    have hES : Model.card (P.E.obj ↥S) < μ := by
      have hupper := P.E.card_upper (I := ↥S)
      rw [P.E.ell_eq] at hupper
      exact hupper.trans_lt hsum
    let xsS : (P.E.obj ↥S).carrier → A.model.carrier := fun x => eA (P.E.map eS x)
    let baseS : (P.E.obj ↥S).carrier → Bobj.model.carrier := fun x => toBobj (xsS x)
    have hEq : SingleModelData.DiagramEq hμel hμel A Bobj xsS baseS :=
      SingleModelData.diagramEq_of_strong hμel hμel A Bobj toBobj htoBobj xsS hES hES
    obtain ⟨Z, fZ, zs, hfZ, hzs, hDZ⟩ :=
      SingleModelData.exists_saturation hμel hμel A Bobj xsS baseS
        (Sum.elim baseS (fun i => eB (d i))) hES hα (fun _ => rfl) hEq
    -- The fresh fiber together with `S` is a μ-sized suborder of the terminal enlargement.
    let inU : (I ⊕ₗ lvlOrder μ) → Prop := fun x =>
      (∃ i : ↥S, x = Sum.inlₗ i.1) ∨ ∃ a : lvlOrder μ, x = Sum.inrₗ a
    have hUne : Nonempty {x // inU x} :=
      ⟨⟨Sum.inrₗ (Classical.arbitrary (lvlOrder μ)), Or.inr ⟨_, rfl⟩⟩⟩
    letI : Nonempty {x // inU x} := hUne
    have hUcard : #{x // inU x} = μ := by
      let f : lvlOrder μ → {x // inU x} := fun a => ⟨Sum.inrₗ a, Or.inr ⟨a, rfl⟩⟩
      have hinj : Injective f := by
        intro a b h
        have h' : Sum.inrₗ a = Sum.inrₗ b := congrArg Subtype.val h
        exact Sum.inr_injective (congrArg ofLex h')
      have hIL : #(I ⊕ₗ lvlOrder μ) = μ := by
        change #(I ⊕ lvlOrder μ) = μ
        rw [mk_sum, lift_id, lift_id, hI, mk_lvlOrder (P.aleph0_le hμel),
          add_eq_self (P.aleph0_le hμel)]
      apply le_antisymm
      · exact (mk_le_of_injective (Subtype.val_injective (p := inU))).trans_eq hIL
      · exact (mk_lvlOrder (P.aleph0_le hμel)).symm.trans_le (mk_le_of_injective hinj)
    let U : Type u := {x // inU x}
    have hUE : Model.card (P.E.obj U) = μ := P.card_obj_eq hμel U hUcard
    obtain ⟨eZU⟩ := (P.categorical hμel).unique_model Z.model (P.E.obj U) Z.mem (P.hE U)
      Z.card hUE
    let sU : ↥S ↪o U :=
      OrderEmbedding.ofStrictMono (fun i => ⟨Sum.inlₗ i.1, Or.inl ⟨i, rfl⟩⟩)
        (by
          intro i j hij
          have hlt : i.1 < j.1 := hij
          exact (Sum.Lex.inl_lt_inl_iff (α := I) (β := lvlOrder μ)).mpr hlt)
    let uIncl : U ↪o (I ⊕ₗ lvlOrder μ) := OrderEmbedding.subtype inU
    let ρS : Cardinal.{u} := max (Model.card (P.E.obj ↥S)) ℵ₀
    have hρSinf : ℵ₀ ≤ ρS := le_max_right _ _
    have hρSμ : ρS < μ := max_lt hES (P.aleph0_lt hμel)
    have hρSle : #(P.E.obj ↥S).carrier ≤ ρS := le_max_left _ _
    have htμ : P.D.t ρS ≤ μ := (hL.t_lt hρSinf hρSμ).le
    have hterms : SameNaturalDiagram K P.E P.D ρS hρSle
        (fun x => SupportTerm.along eS (supportTermOf P.E x))
        (fun x => SupportTerm.along sU (supportTermOf P.E x)) :=
      sameNaturalDiagram_of_pattern
        (fun x => SupportTerm.along eS (supportTermOf P.E x))
        (fun x => SupportTerm.along sU (supportTermOf P.E x))
        (fun _ => rfl)
        (by
          intro c d k l hk hl hk' hl'
          simp [SupportTerm.along, eS.map_rel_iff, sU.map_rel_iff])
    have hDS : P.D.same hρSle (P.hE I) (P.hE U) (htμ.trans hIA.ge) (htμ.trans hUE.ge)
        (fun x => P.E.realize (SupportTerm.along eS (supportTermOf P.E x)))
        (fun x => P.E.realize (SupportTerm.along sU (supportTermOf P.E x))) :=
      hterms.same hρSinf (htμ.trans hIA.ge) (htμ.trans hUE.ge) (P.hE I) (P.hE U)
    have hmapI : (fun x => P.E.realize (SupportTerm.along eS (supportTermOf P.E x))) =
        fun x => P.E.map eS x := funext fun x => by
      rw [← P.E.realize_along, realize_supportTermOf]
    have hmapU : (fun x => P.E.realize (SupportTerm.along sU (supportTermOf P.E x))) =
        fun x => P.E.map sU x := funext fun x => by
      rw [← P.E.realize_along, realize_supportTermOf]
    have hDS' : P.D.same hρSle (P.hE I) (P.hE U) (htμ.trans hIA.ge) (htμ.trans hUE.ge)
        (fun x => P.E.map eS x) (fun x => P.E.map sU x) := by
      simpa [hmapI, hmapU] using hDS
    -- Push the parameter list through the charts into `E(U)`.
    have hZA : P.D.same hρSle (P.hE I) A.mem (htμ.trans hIA.ge) (htμ.trans A.card.ge)
        (fun x => P.E.map eS x) xsS := by
      have hxs : xsS = fun x => eA (P.E.map eS x) := rfl
      refine P.D.of_strong hρSle (P.hE I) A.mem (htμ.trans hIA.ge) (htμ.trans A.card.ge)
        (fun x => P.E.map eS x) xsS eA.toEmbedding hρSinf
        (strong_of_equiv K eA (P.hE I)) fun x => rfl
    have hZlist : (fun x => fZ (xsS x)) = fun x => zs (Sum.inl x) :=
      funext fun x => (hzs x).symm
    have hZF : P.D.same hρSle A.mem Z.mem (htμ.trans A.card.ge) (htμ.trans Z.card.ge)
        xsS (fun x => zs (Sum.inl x)) := by
      rw [← hZlist]
      exact P.D.of_strong hρSle A.mem Z.mem (htμ.trans A.card.ge) (htμ.trans Z.card.ge)
        xsS (fun x => fZ (xsS x)) fZ hρSinf hfZ fun _ => rfl
    have hZU : P.D.same hρSle Z.mem (P.hE U) (htμ.trans Z.card.ge) (htμ.trans hUE.ge)
        (fun x => zs (Sum.inl x)) (fun x => eZU (zs (Sum.inl x))) :=
      P.D.of_strong hρSle Z.mem (P.hE U) (htμ.trans Z.card.ge) (htμ.trans hUE.ge)
        (fun x => zs (Sum.inl x)) (fun x => eZU (zs (Sum.inl x))) eZU.toEmbedding hρSinf
        (strong_of_equiv K eZU Z.mem) fun _ => rfl
    have hparam : P.D.same hρSle (P.hE U) (P.hE U) (htμ.trans hUE.ge) (htμ.trans hUE.ge)
        (fun x => P.E.map sU x) (fun x => eZU (zs (Sum.inl x))) := by
      have h1 := P.D.symm hρSle (P.hE I) (P.hE U) (htμ.trans hIA.ge) (htμ.trans hUE.ge) _ _ hDS'
      have h2 := P.D.trans hρSle (P.hE U) (P.hE I) A.mem (htμ.trans hUE.ge)
        (htμ.trans hIA.ge) (htμ.trans A.card.ge) _ _ _ h1 hZA
      have h3 := P.D.trans hρSle (P.hE U) A.mem Z.mem (htμ.trans hUE.ge)
        (htμ.trans A.card.ge) (htμ.trans Z.card.ge) _ _ _ h2 hZF
      exact P.D.trans hρSle (P.hE U) Z.mem (P.hE U) (htμ.trans hUE.ge)
        (htμ.trans Z.card.ge) (htμ.trans hUE.ge) _ _ _ h3 hZU
    have hSame : P.D.SameD (P.E.obj U) (P.E.obj U)
        (fun x => P.E.map sU x) (fun x => eZU (zs (Sum.inl x))) :=
      ⟨P.hE U, P.hE U, htμ.trans hUE.ge, htμ.trans hUE.ge, hparam⟩
    obtain ⟨e1, he1⟩ := SingleModelData.sameD_equiv hμel hUE hUE hSame hES
    let w0 : α → (P.E.obj U).carrier := fun i => e1.symm (eZU (zs (Sum.inr i)))
    have hjointU : Sum.elim (fun x => P.E.map sU x) w0 =
        fun t => e1.symm (eZU (zs t)) := by
      funext t
      cases t with
      | inl x =>
          simp only [Sum.elim]
          rw [← he1 x, e1.symm_apply_apply]
      | inr i =>
          simp only [Sum.elim]
          rfl
    let z : α → (P.E.obj (I ⊕ₗ lvlOrder μ)).carrier := fun i => P.E.map uIncl (w0 i)
    have hILcard : #(I ⊕ₗ lvlOrder μ) = μ := by
      change #(I ⊕ lvlOrder μ) = μ
      rw [mk_sum, lift_id, lift_id, hI, mk_lvlOrder (P.aleph0_le hμel),
        add_eq_self (P.aleph0_le hμel)]
    have hstripCard : Model.card (P.E.obj (I ⊕ₗ lvlOrder μ)) = μ :=
      P.card_obj_eq hμel _ hILcard
    refine ⟨z, ?_⟩
    -- Testing queries are small enough for Lemma 6.14 and the approximation sequence.
    have hsmall : ∀ {β : Type u} (_hβ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u})
        (_hρinf : ℵ₀ ≤ ρ) (_hρμ : ρ < μ) (q : β → (P.E.obj I).carrier)
        (hjoint : #(α ⊕ β) ≤ ρ)
        (h₀ : P.D.t ρ ≤ Model.card B)
        (h₁ : P.D.t ρ ≤ Model.card (P.E.obj (I ⊕ₗ lvlOrder μ))),
        P.D.same hjoint hB (P.hE _) h₀ h₁
          (Sum.elim d (fun b => incl (q b)))
          (Sum.elim z (fun b => P.E.map (sumLexEmbedLeftIncl I (lvlOrder μ)) (q b))) := by
      intro β _hβ ρ _hρinf _hρμ q hjoint h₀ h₁
      -- `q` is a testing query. Its positions move into `S` by the widened closure,
      -- and the saturated joint over `E(S)` matches `d` with `z` on that move.
      -- The approximation sequence is the majority witness that the move does not
      -- change the diagram of `d`; naturality of terms does the same for `z`.
      let tq : β → SupportTerm P.E.lab P.E.arity I := fun b => supportTermOf P.E (q b)
      let qIdx := Σ b : β, Fin (P.E.arity (tq b).label)
      let qPos : qIdx → I := fun s => (tq s.1).pos s.2
      have hqIdx : #qIdx ≤ χC := by
        have hβτ : #β ≤ χC := _hβ.trans (hgle.trans (le_max_right σ τ))
        have hfin : ∀ b, #(Set.range (tq b).pos) ≤ ℵ₀ := fun b => by
          have h := mk_range_le_lift (f := (tq b).pos)
          rw [lift_uzero] at h
          refine h.trans ?_
          rw [mk_fin, lift_natCast]
          exact natCast_le_aleph0
        have hsup : (⨆ b, #(Set.range (tq b).pos)) ≤ ℵ₀ := ciSup_le' hfin
        have hle : #qIdx ≤ #β * ℵ₀ := by
          let f : qIdx → β × ℕ := fun s => (s.1, s.2.1)
          have hinj : Injective f := by
            intro s t hst
            cases s with
            | mk b k =>
              cases t with
              | mk b' k' =>
                have hb := congrArg Prod.fst hst
                have hn := congrArg Prod.snd hst
                cases hb
                have : k = k' := Fin.ext hn
                simp [this]
          have hprod : #(β × ℕ) = #β * ℵ₀ := by
            rw [mk_prod, mk_nat, lift_aleph0, lift_id']
          exact (mk_le_of_injective hinj).trans (le_of_eq hprod)
        have hmul : #β * ℵ₀ ≤ χC := by
          have hβle : #β ≤ χC := hβτ
          have hmulχ : χC * ℵ₀ = χC :=
            Cardinal.mul_eq_left hχC hχC aleph0_ne_zero
          exact (mul_le_mul' hβle le_rfl).trans (le_of_eq hmulχ)
        exact hle.trans hmul
      -- Old supports of `w0`: the χ-parameter of the closure. The fixed `T★` already
      -- holds the approximation supports, so every move fixes both.
      let w0Term : α → SupportTerm P.E.lab P.E.arity U := fun i => supportTermOf P.E (w0 i)
      let rIdx := Σ i : α,
        {k : Fin (P.E.arity (w0Term i).label) // ∃ j : ↥S, (w0Term i).pos k = sU j}
      let rPos : rIdx → ↥S := fun s => Classical.choose s.2.2
      have hrchoose : ∀ s : rIdx, (w0Term s.1).pos s.2.1 = sU (rPos s) :=
        fun s => Classical.choose_spec s.2.2
      have hrIdx : #rIdx ≤ χC := by
        have hαχ : #α ≤ χC := (le_max_left (#α) ℵ₀).trans (le_max_left σ τ)
        have hfin : ∀ i, #(Set.range (w0Term i).pos) ≤ ℵ₀ := fun i => by
          have h := mk_range_le_lift (f := (w0Term i).pos)
          rw [lift_uzero] at h
          refine h.trans ?_
          rw [mk_fin, lift_natCast]
          exact natCast_le_aleph0
        have hsup : (⨆ i, #(Set.range (w0Term i).pos)) ≤ ℵ₀ := ciSup_le' hfin
        have hle : #rIdx ≤ #α * ℵ₀ := by
          let f : rIdx → α × ℕ := fun s => (s.1, s.2.1.1)
          have hinj : Injective f := by
            intro s t hst
            cases s with
            | mk a k =>
              cases t with
              | mk a' k' =>
                have ha := congrArg Prod.fst hst
                have hn := congrArg Prod.snd hst
                cases ha
                have hk : k.1 = k'.1 := Fin.ext hn
                cases k with
                | mk kv hp =>
                  cases k' with
                  | mk kv' hp' =>
                    cases hk
                    rfl
          have hprod : #(α × ℕ) = #α * ℵ₀ := by
            rw [mk_prod, mk_nat, lift_aleph0, lift_id']
          exact (mk_le_of_injective hinj).trans (le_of_eq hprod)
        have hmul : #α * ℵ₀ ≤ χC := by
          have hmulχ : χC * ℵ₀ = χC :=
            Cardinal.mul_eq_left hχC hχC aleph0_ne_zero
          exact (mul_le_mul' hαχ le_rfl).trans (le_of_eq hmulχ)
        exact hle.trans hmul
      obtain ⟨qPos', hqS, hpat, _hcol⟩ := hclose (ι := rIdx) hrIdx
        (fun s => eS (rPos s)) (fun s => (rPos s).2) hqIdx qPos
      -- The moved positions still carry the query terms, now inside `S`.
      have hqlt : ∀ b, StrictMono fun k : Fin (P.E.arity (tq b).label) =>
          qPos' ⟨b, k⟩ := by
        intro b i j hij
        have hlt := (hpat.2 (Sum.inr ⟨b, i⟩) (Sum.inr ⟨b, j⟩)).1
          ((tq b).increasing hij)
        simpa [qPos] using hlt
      let tq' : β → SupportTerm P.E.lab P.E.arity I := fun b =>
        ⟨(tq b).label, fun k => qPos' ⟨b, k⟩, hqlt b⟩
      let q' : β → (P.E.obj I).carrier := fun b => P.E.realize (tq' b)
      let tS : β → SupportTerm P.E.lab P.E.arity ↥S := fun b =>
        ⟨(tq b).label, fun k => ⟨qPos' ⟨b, k⟩, hqS ⟨b, k⟩⟩, hqlt b⟩
      let xS : β → (P.E.obj ↥S).carrier := fun b => P.E.realize (tS b)
      have hq'eq : q' = fun b => P.E.map eS (xS b) := by
        funext b
        have halong : tq' b = SupportTerm.along eS (tS b) := by
          apply SupportTerm.ext_of_label_eq rfl
          intro k
          simp [SupportTerm.along, tq', tS, OrderEmbedding.subtype]
        change P.E.realize (tq' b) = P.E.map eS (P.E.realize (tS b))
        rw [halong, ← P.E.realize_along]
      -- On the moved query, both sides are reindexings of the saturated joint.
      have hembed : ∀ i : ↥S, uIncl (sU i) = sumLexEmbedLeftIncl I (lvlOrder μ) (eS i) := by
        intro i
        rfl
      have hmoved :
          P.D.same hjoint hB (P.hE _) h₀ h₁
            (Sum.elim d (fun b => incl (q' b)))
            (Sum.elim z (fun b => P.E.map (sumLexEmbedLeftIncl I (lvlOrder μ)) (q' b))) := by
        -- Reindex the saturated joint. The index map sends the tuple coordinates to the
        -- `d`/`w0` summand and the query coordinates to the chosen elements of `E(S)`.
        let ιr : α ⊕ β → (P.E.obj ↥S).carrier ⊕ α
          | .inl a => .inr a
          | .inr b => .inl (xS b)
        let ρJ : Cardinal.{u} := max ρS σ
        have hρJinf : ℵ₀ ≤ ρJ := hρSinf.trans (le_max_left _ _)
        have hρJμ : ρJ < μ := max_lt hρSμ hσμ
        have htJ : P.D.t ρJ ≤ μ := (hL.t_lt hρJinf hρJμ).le
        have hsumle : #((P.E.obj ↥S).carrier ⊕ α) ≤ ρJ := by
          have h1 : #(P.E.obj ↥S).carrier ≤ ρJ :=
            (le_max_left (Model.card (P.E.obj ↥S)) ℵ₀).trans (le_max_left ρS σ)
          have h2 : #α ≤ ρJ := (le_max_left (#α) ℵ₀).trans (le_max_right ρS σ)
          rw [mk_sum, lift_id, lift_id]
          exact (add_le_add h1 h2).trans (le_of_eq (add_eq_self hρJinf))
        have hfull :
            P.D.same hsumle hB (P.hE _)
              (htJ.trans hcard.ge) (htJ.trans hstripCard.ge)
              (Sum.elim (fun x => incl (P.E.map eS x)) d)
              (Sum.elim (fun x => P.E.map uIncl (P.E.map sU x)) z) := by
          have hsz : #((P.E.obj ↥S).carrier ⊕ α) < μ := hsumle.trans_lt hρJμ
          have hSD :=
            (SingleModelData.diagramEq_iff_sameD hμel hμel Z Bobj zs
              (Sum.elim baseS (fun i => eB (d i))) hsz hsz).1 hDZ
          obtain ⟨_, _, _, _, hsameZ⟩ := hSD
          -- `baseS` is the chart image of `incl ∘ E.map eS`.
          have hbaseEq : baseS = fun x => eB (incl (P.E.map eS x)) := by
            funext x
            simp [baseS, xsS, toBobj, toB]
          have hleft : P.D.same (le_max_left _ _) hB Bobj.mem
              (by
                have hσ0 : ℵ₀ ≤ max #((P.E.obj ↥S).carrier ⊕ α) ℵ₀ := le_max_right _ _
                exact (hL.t_lt hσ0 (max_lt hsz (P.aleph0_lt hμel))).le.trans hcard.ge)
              (by
                have hσ0 : ℵ₀ ≤ max #((P.E.obj ↥S).carrier ⊕ α) ℵ₀ := le_max_right _ _
                exact (hL.t_lt hσ0 (max_lt hsz (P.aleph0_lt hμel))).le.trans Bobj.card.ge)
              (Sum.elim (fun x => incl (P.E.map eS x)) d)
              (Sum.elim baseS (fun i => eB (d i))) := by
            have hfun : (fun t => eB ((Sum.elim (fun x => incl (P.E.map eS x)) d) t)) =
                Sum.elim (fun x => eB (incl (P.E.map eS x))) (fun i => eB (d i)) := by
              funext t
              cases t <;> rfl
            rw [hbaseEq, ← hfun]
            exact P.D.of_strong (le_max_left _ _) hB Bobj.mem
              (by
                have hσ0 : ℵ₀ ≤ max #((P.E.obj ↥S).carrier ⊕ α) ℵ₀ := le_max_right _ _
                exact (hL.t_lt hσ0 (max_lt hsz (P.aleph0_lt hμel))).le.trans hcard.ge)
              (by
                have hσ0 : ℵ₀ ≤ max #((P.E.obj ↥S).carrier ⊕ α) ℵ₀ := le_max_right _ _
                exact (hL.t_lt hσ0 (max_lt hsz (P.aleph0_lt hμel))).le.trans Bobj.card.ge)
              (Sum.elim (fun x => incl (P.E.map eS x)) d)
              (fun t => eB ((Sum.elim (fun x => incl (P.E.map eS x)) d) t))
              eB.toEmbedding (le_max_right _ _) (strong_of_equiv K eB hB) fun _ => rfl
          have hBZ : P.D.same (le_max_left _ _) hB Z.mem
              (by
                have hσ0 : ℵ₀ ≤ max #((P.E.obj ↥S).carrier ⊕ α) ℵ₀ := le_max_right _ _
                exact (hL.t_lt hσ0 (max_lt hsz (P.aleph0_lt hμel))).le.trans hcard.ge)
              (by
                have hσ0 : ℵ₀ ≤ max #((P.E.obj ↥S).carrier ⊕ α) ℵ₀ := le_max_right _ _
                exact (hL.t_lt hσ0 (max_lt hsz (P.aleph0_lt hμel))).le.trans Z.card.ge)
              (Sum.elim (fun x => incl (P.E.map eS x)) d) zs :=
            P.D.trans (le_max_left _ _) hB Bobj.mem Z.mem
              (by
                have hσ0 : ℵ₀ ≤ max #((P.E.obj ↥S).carrier ⊕ α) ℵ₀ := le_max_right _ _
                exact (hL.t_lt hσ0 (max_lt hsz (P.aleph0_lt hμel))).le.trans hcard.ge)
              (by
                have hσ0 : ℵ₀ ≤ max #((P.E.obj ↥S).carrier ⊕ α) ℵ₀ := le_max_right _ _
                exact (hL.t_lt hσ0 (max_lt hsz (P.aleph0_lt hμel))).le.trans Bobj.card.ge)
              (by
                have hσ0 : ℵ₀ ≤ max #((P.E.obj ↥S).carrier ⊕ α) ℵ₀ := le_max_right _ _
                exact (hL.t_lt hσ0 (max_lt hsz (P.aleph0_lt hμel))).le.trans Z.card.ge)
              _ _ _ hleft (P.D.symm (le_max_left _ _) Z.mem Bobj.mem _ _ _ _ hsameZ)
          let σ0 : Cardinal.{u} := max #((P.E.obj ↥S).carrier ⊕ α) ℵ₀
          have hσ0 : ℵ₀ ≤ σ0 := le_max_right _ _
          have hσ0μ : σ0 < μ := max_lt hsz (P.aleph0_lt hμel)
          have ht0 : P.D.t σ0 ≤ μ := (hL.t_lt hσ0 hσ0μ).le
          have hZU' : P.D.same (le_max_left _ _) Z.mem (P.hE U)
              (ht0.trans Z.card.ge) (ht0.trans hUE.ge)
              zs (fun t => eZU (zs t)) :=
            P.D.of_strong (le_max_left _ _) Z.mem (P.hE U)
              (ht0.trans Z.card.ge) (ht0.trans hUE.ge)
              zs (fun t => eZU (zs t)) eZU.toEmbedding hσ0
              (strong_of_equiv K eZU Z.mem) fun _ => rfl
          have hU' : P.D.same (le_max_left _ _) (P.hE U) (P.hE U)
              (ht0.trans hUE.ge) (ht0.trans hUE.ge)
              (fun t => eZU (zs t)) (fun t => e1.symm (eZU (zs t))) :=
            P.D.of_strong (le_max_left _ _) (P.hE U) (P.hE U)
              (ht0.trans hUE.ge) (ht0.trans hUE.ge)
              (fun t => eZU (zs t)) (fun t => e1.symm (eZU (zs t)))
              e1.symm.toEmbedding hσ0 (strong_of_equiv K e1.symm (P.hE U)) fun _ => rfl
          have hEqU : (fun t => e1.symm (eZU (zs t))) =
              Sum.elim (fun x => P.E.map sU x) w0 := hjointU.symm
          have hIncl : P.D.same (le_max_left _ _) (P.hE U) (P.hE _)
              (ht0.trans hUE.ge) (ht0.trans hstripCard.ge)
              (Sum.elim (fun x => P.E.map sU x) w0)
              (fun t => P.E.map uIncl ((Sum.elim (fun x => P.E.map sU x) w0) t)) :=
            P.D.of_strong (le_max_left _ _) (P.hE U) (P.hE _)
              (ht0.trans hUE.ge) (ht0.trans hstripCard.ge)
              (Sum.elim (fun x => P.E.map sU x) w0)
              (fun t => P.E.map uIncl ((Sum.elim (fun x => P.E.map sU x) w0) t))
              (P.E.map uIncl) hσ0 (P.E.map_strong uIncl) fun _ => rfl
          have hstripEq : (fun t => P.E.map uIncl ((Sum.elim (fun x => P.E.map sU x) w0) t)) =
              Sum.elim (fun x => P.E.map uIncl (P.E.map sU x)) z := by
            funext t
            cases t <;> rfl
          have hchain : P.D.same (le_max_left _ _) hB (P.hE _)
              (ht0.trans hcard.ge) (ht0.trans hstripCard.ge)
              (Sum.elim (fun x => incl (P.E.map eS x)) d)
              (Sum.elim (fun x => P.E.map uIncl (P.E.map sU x)) z) := by
            have h1 := P.D.trans (le_max_left _ _) hB Z.mem (P.hE U)
              (ht0.trans hcard.ge) (ht0.trans Z.card.ge) (ht0.trans hUE.ge) _ _ _ hBZ hZU'
            have h2 := P.D.trans (le_max_left _ _) hB (P.hE U) (P.hE U)
              (ht0.trans hcard.ge) (ht0.trans hUE.ge) (ht0.trans hUE.ge) _ _ _ h1 hU'
            rw [hEqU] at h2
            have h3 := P.D.trans (le_max_left _ _) hB (P.hE U) (P.hE _)
              (ht0.trans hcard.ge) (ht0.trans hUE.ge) (ht0.trans hstripCard.ge) _ _ _ h2 hIncl
            rw [hstripEq] at h3
            exact h3
          let σBig : Cardinal.{u} := max (max σ0 ρJ) (ls K)
          have hBig : ℵ₀ ≤ σBig := hσ0.trans ((le_max_left σ0 ρJ).trans (le_max_left _ _))
          have hBigμ : σBig < μ := max_lt (max_lt hσ0μ hρJμ) (P.ls_lt hμel)
          have htBig : P.D.t σBig ≤ μ := (hL.t_lt hBig hBigμ).le
          exact P.D.same_relevel (le_max_left _ _) hσ0 hρJinf
            ((le_max_left σ0 ρJ).trans (le_max_left _ (ls K)))
            ((le_max_right σ0 ρJ).trans (le_max_left _ (ls K)))
            (le_max_right _ (ls K))
            hB (P.hE _)
            (ht0.trans hcard.ge) (ht0.trans hstripCard.ge)
            (htBig.trans hcard.ge) (htBig.trans hstripCard.ge)
            (htJ.trans hcard.ge) (htJ.trans hstripCard.ge)
            _ _ hchain hsumle id
        have hre : P.D.same hjoint hB (P.hE _) h₀ h₁
            (fun t => (Sum.elim (fun x => incl (P.E.map eS x)) d) (ιr t))
            (fun t => (Sum.elim (fun x => P.E.map uIncl (P.E.map sU x)) z) (ιr t)) := by
          let σ' : Cardinal.{u} := max (max ρJ ρ) (ls K)
          have hσ'inf : ℵ₀ ≤ σ' := hρJinf.trans ((le_max_left ρJ ρ).trans (le_max_left _ _))
          have hσ'μ : σ' < μ :=
            max_lt (max_lt hρJμ _hρμ) (P.ls_lt hμel)
          have ht' : P.D.t σ' ≤ μ := (hL.t_lt hσ'inf hσ'μ).le
          exact P.D.same_relevel hsumle hρJinf _hρinf
            ((le_max_left ρJ ρ).trans (le_max_left _ (ls K)))
            ((le_max_right ρJ ρ).trans (le_max_left _ (ls K)))
            (le_max_right _ (ls K)) hB (P.hE _)
            (htJ.trans hcard.ge) (htJ.trans hstripCard.ge)
            (ht'.trans hcard.ge) (ht'.trans hstripCard.ge)
            h₀ h₁
            _ _ hfull hjoint ιr
        have hLft : (fun t => (Sum.elim (fun x => incl (P.E.map eS x)) d) (ιr t)) =
            Sum.elim d (fun b => incl (q' b)) := by
          funext t
          cases t with
          | inl a => rfl
          | inr b =>
              rw [hq'eq]
              rfl
        have hRgt : (fun t => (Sum.elim (fun x => P.E.map uIncl (P.E.map sU x)) z) (ιr t)) =
            Sum.elim z (fun b => P.E.map (sumLexEmbedLeftIncl I (lvlOrder μ)) (q' b)) := by
          funext t
          cases t with
          | inl a => rfl
          | inr b =>
              dsimp [ιr, Sum.elim]
              have hcomp : P.E.map (sU.trans uIncl) (xS b) =
                  P.E.map uIncl (P.E.map sU (xS b)) := by
                rw [P.E.map_comp]
                rfl
              have htrans : sU.trans uIncl =
                  eS.trans (sumLexEmbedLeftIncl I (lvlOrder μ)) := by
                ext i
                exact hembed i
              rw [← hcomp, htrans, P.E.map_comp, hq'eq]
              rfl
        simpa [hLft, hRgt] using hre
      -- Moving the query does not change the diagram of `z`. Old supports of `z` are
      -- χ-parameters of the closure, so the move fixes them; supports in the fiber sit
      -- to the right of every query position, original or moved.
      have hzMove : P.D.same hjoint (P.hE _) (P.hE _) h₁ h₁
          (Sum.elim z (fun b => P.E.map (sumLexEmbedLeftIncl I (lvlOrder μ)) (q b)))
          (Sum.elim z (fun b => P.E.map (sumLexEmbedLeftIncl I (lvlOrder μ)) (q' b))) := by
        let emb := sumLexEmbedLeftIncl I (lvlOrder μ)
        let tL : α → SupportTerm P.E.lab P.E.arity (I ⊕ₗ lvlOrder μ) :=
          fun i => SupportTerm.along uIncl (w0Term i)
        let tR : β → SupportTerm P.E.lab P.E.arity (I ⊕ₗ lvlOrder μ) :=
          fun b => SupportTerm.along emb (tq b)
        let tR' : β → SupportTerm P.E.lab P.E.arity (I ⊕ₗ lvlOrder μ) :=
          fun b => SupportTerm.along emb (tq' b)
        let tA : α ⊕ β → SupportTerm P.E.lab P.E.arity (I ⊕ₗ lvlOrder μ) := Sum.elim tL tR
        let tA' : α ⊕ β → SupportTerm P.E.lab P.E.arity (I ⊕ₗ lvlOrder μ) := Sum.elim tL tR'
        have hzl : ∀ (i : α) (b : β) (k : Fin (P.E.arity (w0Term i).label))
            (l : Fin (P.E.arity (tq b).label)),
            uIncl ((w0Term i).pos k) < emb ((tq b).pos l) ↔
              uIncl ((w0Term i).pos k) < emb ((tq' b).pos l) := by
          intro i b k l
          let x := (w0Term i).pos k
          rcases x.2 with ⟨s, hs⟩ | ⟨a, ha⟩
          · have hxs : x = sU s := Subtype.ext hs
            let r : rIdx := ⟨i, ⟨k, ⟨s, hxs⟩⟩⟩
            have hr : rPos r = s :=
              sU.injective ((hrchoose r).symm.trans hxs)
            have hiff := hpat.2 (Sum.inl (Sum.inl r)) (Sum.inr ⟨b, l⟩)
            simp only [Sum.elim, hr] at hiff
            have hux : uIncl x = emb (eS s) := by rw [hxs]; exact hembed s
            rw [hux]
            simp only [emb.lt_iff_lt]
            exact hiff
          · exact Iff.intro
              (fun hlt => False.elim <| by
                rw [show uIncl x = Sum.inrₗ a from ha] at hlt
                exact Sum.Lex.not_inr_le_inl (α := I) (β := lvlOrder μ) hlt.le)
              (fun hlt => False.elim <| by
                rw [show uIncl x = Sum.inrₗ a from ha] at hlt
                exact Sum.Lex.not_inr_le_inl (α := I) (β := lvlOrder μ) hlt.le)
        have hlz : ∀ (i : α) (b : β) (k : Fin (P.E.arity (w0Term i).label))
            (l : Fin (P.E.arity (tq b).label)),
            emb ((tq b).pos l) < uIncl ((w0Term i).pos k) ↔
              emb ((tq' b).pos l) < uIncl ((w0Term i).pos k) := by
          intro i b k l
          let x := (w0Term i).pos k
          rcases x.2 with ⟨s, hs⟩ | ⟨a, ha⟩
          · have hxs : x = sU s := Subtype.ext hs
            let r : rIdx := ⟨i, ⟨k, ⟨s, hxs⟩⟩⟩
            have hr : rPos r = s :=
              sU.injective ((hrchoose r).symm.trans hxs)
            have hiff := hpat.2 (Sum.inr ⟨b, l⟩) (Sum.inl (Sum.inl r))
            simp only [Sum.elim, hr] at hiff
            have hux : uIncl x = emb (eS s) := by rw [hxs]; exact hembed s
            rw [hux]
            simp only [emb.lt_iff_lt]
            exact hiff
          · exact Iff.intro
              (fun _ => by
                rw [show uIncl x = Sum.inrₗ a from ha]
                exact Sum.Lex.inl_lt_inr ((tq' b).pos l) a)
              (fun _ => by
                rw [show uIncl x = Sum.inrₗ a from ha]
                exact Sum.Lex.inl_lt_inr ((tq b).pos l) a)
        have hqq : ∀ (b b' : β) (k : Fin (P.E.arity (tq b).label))
            (l : Fin (P.E.arity (tq b').label)),
            emb ((tq b).pos k) < emb ((tq b').pos l) ↔
              emb ((tq' b).pos k) < emb ((tq' b').pos l) := by
          intro b b' k l
          simp only [emb.lt_iff_lt]
          exact hpat.2 (Sum.inr ⟨b, k⟩) (Sum.inr ⟨b', l⟩)
        have hord : ∀ c d k l (hk : k < P.E.arity (tA c).label)
            (hl : l < P.E.arity (tA d).label)
            (hk' : k < P.E.arity (tA' c).label) (hl' : l < P.E.arity (tA' d).label),
            (tA c).pos ⟨k, hk⟩ < (tA d).pos ⟨l, hl⟩ ↔
              (tA' c).pos ⟨k, hk'⟩ < (tA' d).pos ⟨l, hl'⟩ := by
          intro c d k l hk hl hk' hl'
          cases c with
          | inl i =>
            cases d with
            | inl j =>
              simp only [tA, tA', tL, Sum.elim, SupportTerm.along]
            | inr b =>
              simp only [tA, tA', tL, tR, tR', Sum.elim, SupportTerm.along]
              rw [show (⟨k, hk⟩ : Fin (P.E.arity (w0Term i).label)) = ⟨k, hk'⟩ from Fin.ext rfl,
                show (⟨l, hl⟩ : Fin (P.E.arity (tq b).label)) = ⟨l, hl'⟩ from Fin.ext rfl]
              exact hzl i b ⟨k, hk⟩ ⟨l, hl⟩
          | inr b =>
            cases d with
            | inl j =>
              simp only [tA, tA', tL, tR, tR', Sum.elim, SupportTerm.along]
              rw [show (⟨k, hk⟩ : Fin (P.E.arity (tq b).label)) = ⟨k, hk'⟩ from Fin.ext rfl,
                show (⟨l, hl⟩ : Fin (P.E.arity (w0Term j).label)) = ⟨l, hl'⟩ from Fin.ext rfl]
              exact hlz j b ⟨l, hl⟩ ⟨k, hk⟩
            | inr b' =>
              simp only [tA, tA', tR, tR', Sum.elim, SupportTerm.along]
              rw [show (⟨k, hk⟩ : Fin (P.E.arity (tq b).label)) = ⟨k, hk'⟩ from Fin.ext rfl,
                show (⟨l, hl⟩ : Fin (P.E.arity (tq b').label)) = ⟨l, hl'⟩ from Fin.ext rfl]
              exact hqq b b' ⟨k, hk⟩ ⟨l, hl⟩
        have hnat := sameNaturalDiagram_of_pattern (E := P.E) (D := P.D) (σ := ρ)
          (hσ := hjoint) tA tA' (fun c => by cases c <;> rfl) hord
        have hsame := hnat.same (hσinf := _hρinf) h₁ h₁ (P.hE _) (P.hE _)
        have hreL : ∀ i, P.E.realize (tL i) = z i := fun i => by
          change P.E.realize (SupportTerm.along uIncl (supportTermOf P.E (w0 i))) = z i
          rw [← P.E.realize_along, realize_supportTermOf P.E (w0 i)]
        have hreR : ∀ b, P.E.realize (tR b) = P.E.map emb (q b) := fun b => by
          change P.E.realize (SupportTerm.along emb (tq b)) = P.E.map emb (q b)
          rw [← P.E.realize_along, realize_supportTermOf P.E (q b)]
        have hreR' : ∀ b, P.E.realize (tR' b) = P.E.map emb (q' b) := fun b => by
          change P.E.realize (SupportTerm.along emb (tq' b)) = P.E.map emb (q' b)
          rw [← P.E.realize_along]
        have hfun : (fun c => P.E.realize (tA c)) =
            Sum.elim z (fun b => P.E.map emb (q b)) := by
          funext c
          cases c with
          | inl i => exact hreL i
          | inr b => exact hreR b
        have hfun' : (fun c => P.E.realize (tA' c)) =
            Sum.elim z (fun b => P.E.map emb (q' b)) := by
          funext c
          cases c with
          | inl i => exact hreL i
          | inr b => exact hreR' b
        rw [hfun, hfun'] at hsame
        exact hsame
      -- Moving the query does not change the diagram of `d`. Every approximation copy
      -- has its supports in `T★`, which the closure fixes, so the copy has the same
      -- diagram with `q` and with `q'`. The type of `d` is the majority value on both.
      let Zq : β → Occurrence K oneVertexShape A.system := fun b => A.occ (eA (q b))
      let Zq' : β → Occurrence K oneVertexShape A.system := fun b => A.occ (eA (q' b))
      have htI : P.D.t ρ ≤ Model.card (P.E.obj I) :=
        (h₀.trans (le_of_eq hcard)).trans hIA.ge
      have hcopy : ∀ i : seq.κIndex, P.D.same hjoint (P.hE I) (P.hE I) htI htI
          (Sum.elim (fun a => seqElt (i, a)) q)
          (Sum.elim (fun a => seqElt (i, a)) q') := by
        intro i
        let tC : α → SupportTerm P.E.lab P.E.arity I :=
          fun a => supportTermOf P.E (seqElt (i, a))
        let tAll : α ⊕ β → SupportTerm P.E.lab P.E.arity I := Sum.elim tC tq
        let tAll' : α ⊕ β → SupportTerm P.E.lab P.E.arity I := Sum.elim tC tq'
        have hCT : ∀ a b (k : Fin (P.E.arity (tC a).label))
            (l : Fin (P.E.arity (tq b).label)),
            (tC a).pos k < (tq b).pos l ↔ (tC a).pos k < (tq' b).pos l := by
          intro a b k l
          have hmem : (tC a).pos k ∈ Tset :=
            Set.mem_iUnion.mpr ⟨(i, a), Set.mem_range_self k⟩
          let t : ↥Tset := ⟨(tC a).pos k, hmem⟩
          have hiff := hpat.2 (Sum.inl (Sum.inr t)) (Sum.inr ⟨b, l⟩)
          simp only [Sum.elim, Tstar] at hiff
          exact hiff
        have hTC : ∀ a b (k : Fin (P.E.arity (tC a).label))
            (l : Fin (P.E.arity (tq b).label)),
            (tq b).pos l < (tC a).pos k ↔ (tq' b).pos l < (tC a).pos k := by
          intro a b k l
          have hmem : (tC a).pos k ∈ Tset :=
            Set.mem_iUnion.mpr ⟨(i, a), Set.mem_range_self k⟩
          let t : ↥Tset := ⟨(tC a).pos k, hmem⟩
          have hiff := hpat.2 (Sum.inr ⟨b, l⟩) (Sum.inl (Sum.inr t))
          simp only [Sum.elim, Tstar] at hiff
          exact hiff
        have hQQ : ∀ b b' (k : Fin (P.E.arity (tq b).label))
            (l : Fin (P.E.arity (tq b').label)),
            (tq b).pos k < (tq b').pos l ↔ (tq' b).pos k < (tq' b').pos l := by
          intro b b' k l
          have hiff := hpat.2 (Sum.inr ⟨b, k⟩) (Sum.inr ⟨b', l⟩)
          simp only [Sum.elim] at hiff
          exact hiff
        have hord : ∀ c d k l (hk : k < P.E.arity (tAll c).label)
            (hl : l < P.E.arity (tAll d).label)
            (hk' : k < P.E.arity (tAll' c).label) (hl' : l < P.E.arity (tAll' d).label),
            (tAll c).pos ⟨k, hk⟩ < (tAll d).pos ⟨l, hl⟩ ↔
              (tAll' c).pos ⟨k, hk'⟩ < (tAll' d).pos ⟨l, hl'⟩ := by
          intro c d k l hk hl hk' hl'
          cases c with
          | inl a =>
            cases d with
            | inl a' => simp only [tAll, tAll', Sum.elim]
            | inr b =>
              simp only [tAll, tAll', Sum.elim]
              rw [show (⟨k, hk⟩ : Fin (P.E.arity (tC a).label)) = ⟨k, hk'⟩ from Fin.ext rfl,
                show (⟨l, hl⟩ : Fin (P.E.arity (tq b).label)) = ⟨l, hl'⟩ from Fin.ext rfl]
              exact hCT a b ⟨k, hk⟩ ⟨l, hl⟩
          | inr b =>
            cases d with
            | inl a =>
              simp only [tAll, tAll', Sum.elim]
              rw [show (⟨k, hk⟩ : Fin (P.E.arity (tq b).label)) = ⟨k, hk'⟩ from Fin.ext rfl,
                show (⟨l, hl⟩ : Fin (P.E.arity (tC a).label)) = ⟨l, hl'⟩ from Fin.ext rfl]
              exact hTC a b ⟨l, hl⟩ ⟨k, hk⟩
            | inr b' =>
              simp only [tAll, tAll', Sum.elim]
              rw [show (⟨k, hk⟩ : Fin (P.E.arity (tq b).label)) = ⟨k, hk'⟩ from Fin.ext rfl,
                show (⟨l, hl⟩ : Fin (P.E.arity (tq b').label)) = ⟨l, hl'⟩ from Fin.ext rfl]
              exact hQQ b b' ⟨k, hk⟩ ⟨l, hl⟩
        have hnat := sameNaturalDiagram_of_pattern (E := P.E) (D := P.D) (σ := ρ)
          (hσ := hjoint) tAll tAll' (fun c => by cases c <;> rfl) hord
        have hsame := hnat.same (hσinf := _hρinf) htI htI (P.hE I) (P.hE I)
        have hfun : (fun c => P.E.realize (tAll c)) =
            Sum.elim (fun a => seqElt (i, a)) q := by
          funext c
          cases c with
          | inl a => exact realize_supportTermOf P.E (seqElt (i, a))
          | inr b => exact realize_supportTermOf P.E (q b)
        have hfun' : (fun c => P.E.realize (tAll' c)) =
            Sum.elim (fun a => seqElt (i, a)) q' := by
          funext c
          cases c with
          | inl a => exact realize_supportTermOf P.E (seqElt (i, a))
          | inr b => rfl
        rw [hfun, hfun'] at hsame
        exact hsame
      have hαμ : #(α ⊕ β) < μ := hjoint.trans_lt _hρμ
      have htA : P.D.t ρ ≤ Model.card A.model :=
        (h₀.trans (le_of_eq hcard)).trans A.card.ge
      have hAgree : ∀ i, P.scheme.DiagramEq (X := A) (Y := A)
          (seqJoint (seq.family i) Zq) (seqJoint (seq.family i) Zq') := by
        intro i
        let left := Sum.elim (fun a => seqElt (i, a)) q
        let right := Sum.elim (fun a => seqElt (i, a)) q'
        have hEA := P.D.of_strong hjoint (P.hE I) A.mem htI htA left
          (fun t => eA (left t)) eA.toEmbedding _hρinf
          (strong_of_equiv K eA (P.hE I)) fun _ => rfl
        have hEA' := P.D.of_strong hjoint (P.hE I) A.mem htI htA right
          (fun t => eA (right t)) eA.toEmbedding _hρinf
          (strong_of_equiv K eA (P.hE I)) fun _ => rfl
        have hAA := P.D.trans hjoint A.mem (P.hE I) A.mem htA htI htA _ _ _
          (P.D.symm hjoint (P.hE I) A.mem htI htA _ _ hEA)
          (P.D.trans hjoint (P.hE I) (P.hE I) A.mem htI htI htA _ _ _ (hcopy i) hEA')
        let σ0 : Cardinal.{u} := max #(α ⊕ β) ℵ₀
        have hσ0 : ℵ₀ ≤ σ0 := le_max_right _ _
        have hσ0ρ : σ0 ≤ ρ := max_le hjoint _hρinf
        have ht0 : P.D.t σ0 ≤ Model.card A.model := (P.D.mono _ _ hσ0ρ).trans htA
        let σ' : Cardinal.{u} := max (max ρ σ0) (ls K)
        have hσ' : ℵ₀ ≤ σ' := _hρinf.trans ((le_max_left ρ σ0).trans (le_max_left _ _))
        have hσ'μ : σ' < μ := max_lt (max_lt _hρμ (hσ0ρ.trans_lt _hρμ)) (P.ls_lt hμel)
        have ht' : P.D.t σ' ≤ Model.card A.model := (hL.t_lt hσ' hσ'μ).le.trans A.card.ge
        have hAA0 := P.D.same_relevel hjoint _hρinf hσ0
          ((le_max_left ρ σ0).trans (le_max_left _ (ls K)))
          ((le_max_right ρ σ0).trans (le_max_left _ (ls K)))
          (le_max_right _ (ls K)) A.mem A.mem htA htA ht' ht' ht0 ht0 _ _ hAA (le_max_left _ _) id
        have hEq := (SingleModelData.diagramEq_iff_sameD hμel hμel A A
          (fun t => eA (left t)) (fun t => eA (right t)) hαμ hαμ).mpr
          ⟨A.mem, A.mem, ht0, ht0, hAA0⟩
        have hvalL : (fun t => A.val (seqJoint (seq.family i) Zq t)) =
            fun t => eA (left t) := by
          funext t
          cases t with
          | inl a => exact (eA.apply_symm_apply (A.val (seq.family i a))).symm
          | inr b => rfl
        have hvalR : (fun t => A.val (seqJoint (seq.family i) Zq' t)) =
            fun t => eA (right t) := by
          funext t
          cases t with
          | inl a => exact (eA.apply_symm_apply (A.val (seq.family i a))).symm
          | inr b => rfl
        change SingleModelData.DiagramEq hμel hμel A A
          (fun t => A.val (seqJoint (seq.family i) Zq t))
          (fun t => A.val (seqJoint (seq.family i) Zq' t))
        rw [hvalL, hvalR]
        exact hEq
      have hβτ : #β ≤ seq.τ := (_hβ.trans hgle).trans_eq hseqτ.symm
      have hκbound : #β + ℵ₀ < #seq.κIndex := by
        have hle : #β + ℵ₀ ≤ τ := by
          exact (add_le_add (_hβ.trans hgle) hτinf).trans (le_of_eq (add_eq_self hτinf))
        rw [hseqκ]
        exact hle.trans_lt ((le_max_right σ τ).trans_lt (cantor χC))
      have hMajTrans : IsMajorityValue seq Zq hμel Bobj (typeJoint (p := p) Zq') := by
        have hsub : ∀ i, ¬ P.scheme.DiagramEq (X := A) (Y := Bobj)
            (seqJoint (seq.family i) Zq) (typeJoint (p := p) Zq') →
            ¬ P.scheme.DiagramEq (X := A) (Y := Bobj)
            (seqJoint (seq.family i) Zq') (typeJoint (p := p) Zq') := by
          intro i hbad hgood
          exact hbad (P.scheme.diagram_trans A A Bobj (seqJoint (seq.family i) Zq)
            (seqJoint (seq.family i) Zq') (typeJoint (p := p) Zq') (hAgree i) hgood)
        exact (mk_subtype_mono hsub).trans (infra_610_majority_eq_type seq Zq' hβτ)
      have hJoints := infra_610_majority_unique seq Zq
        (xs := typeJoint (p := p) Zq) (ys := typeJoint (p := p) Zq')
        (infra_610_majority_eq_type seq Zq hβτ) hMajTrans hκbound
      have hcarrier : (fun t => Bobj.val (typeJoint (p := p) Zq t)) =
          fun t => eB ((Sum.elim d (fun b => incl (q b))) t) := by
        funext t
        cases t with
        | inl a => rfl
        | inr b =>
          rw [show Bobj.val (typeJoint (p := p) Zq (Sum.inr b)) = toBobj (eA (q b)) from rfl]
          simp [toBobj, toB, eA.symm_apply_apply]
      have hcarrier' : (fun t => Bobj.val (typeJoint (p := p) Zq' t)) =
          fun t => eB ((Sum.elim d (fun b => incl (q' b))) t) := by
        funext t
        cases t with
        | inl a => rfl
        | inr b =>
          rw [show Bobj.val (typeJoint (p := p) Zq' (Sum.inr b)) = toBobj (eA (q' b)) from rfl]
          simp [toBobj, toB, eA.symm_apply_apply]
      have hSame := (SingleModelData.diagramEq_iff_sameD hμel hμel Bobj Bobj
        (fun t => Bobj.val (typeJoint (p := p) Zq t))
        (fun t => Bobj.val (typeJoint (p := p) Zq' t)) hαμ hαμ).mp hJoints
      rw [hcarrier, hcarrier'] at hSame
      obtain ⟨_, _, hBc, _, hBB⟩ := hSame
      have hσB : ℵ₀ ≤ max #(α ⊕ β) ℵ₀ := le_max_right _ _
      have hσBρ : max #(α ⊕ β) ℵ₀ ≤ ρ := max_le hjoint _hρinf
      have htB : P.D.t (max #(α ⊕ β) ℵ₀) ≤ Model.card B := (P.D.mono _ _ hσBρ).trans h₀
      let leftB := Sum.elim d (fun b => incl (q b))
      let rightB := Sum.elim d (fun b => incl (q' b))
      have hBackL := P.D.of_strong (le_max_left _ _) Bobj.mem hB hBc htB
        (fun t => eB (leftB t)) leftB eB.symm.toEmbedding hσB
        (strong_of_equiv K eB.symm Bobj.mem) fun _ => eB.symm_apply_apply _
      have hBackR := P.D.of_strong (le_max_left _ _) Bobj.mem hB hBc htB
        (fun t => eB (rightB t)) rightB eB.symm.toEmbedding hσB
        (strong_of_equiv K eB.symm Bobj.mem) fun _ => eB.symm_apply_apply _
      have hBB' := P.D.trans (le_max_left _ _) hB Bobj.mem hB htB hBc htB _ _ _
        (P.D.symm (le_max_left _ _) Bobj.mem hB hBc htB _ _ hBackL)
        (P.D.trans (le_max_left _ _) Bobj.mem Bobj.mem hB hBc hBc htB _ _ _ hBB hBackR)
      let σBig : Cardinal.{u} := max (max (max #(α ⊕ β) ℵ₀) ρ) (ls K)
      have hBig : ℵ₀ ≤ σBig := hσB.trans ((le_max_left _ ρ).trans (le_max_left _ _))
      have hBigμ : σBig < μ :=
        max_lt (max_lt (hσBρ.trans_lt _hρμ) _hρμ) (P.ls_lt hμel)
      have htBig : P.D.t σBig ≤ Model.card B := (hL.t_lt hBig hBigμ).le.trans hcard.ge
      have hdMove : P.D.same hjoint hB hB h₀ h₀ leftB rightB :=
        P.D.same_relevel (le_max_left _ _) hσB _hρinf
          ((le_max_left _ ρ).trans (le_max_left _ (ls K)))
          ((le_max_right _ ρ).trans (le_max_left _ (ls K)))
          (le_max_right _ (ls K)) hB hB htB htB htBig htBig h₀ h₀ _ _ hBB' hjoint id
      have hstep := P.D.trans hjoint hB hB (P.hE _) h₀ h₀ h₁ _ _ _ hdMove hmoved
      exact P.D.trans hjoint hB (P.hE _) (P.hE _) h₀ h₁ h₁ _ _ _ hstep
        (P.D.symm hjoint (P.hE _) (P.hE _) h₁ h₁ _ _ hzMove)
    obtain ⟨Qa, gB, gE, hQa, hgB, hgE, _hc, hbase, hd⟩ :=
      hL.exists_tuple_amalgam hσ hσμ (le_max_left (#α) ℵ₀)
        (P.E.obj I) B (P.E.obj (I ⊕ₗ lvlOrder μ))
        incl (P.E.map (sumLexEmbedLeftIncl I (lvlOrder μ))) d z
        (P.hE I) hB (P.hE _) hstrong (P.E.map_strong _)
        hIA hcard hstripCard hsmall
    intro β ρ hρinf hρμ p hj hBc hJc
    exact P.D.same_of_amalgam hB (P.hE _) hQa gB gE hgB hgE
      (Sum.elim d (fun b => incl (p b)))
      (Sum.elim z (fun b => P.E.map (sumLexEmbedLeftIncl I (lvlOrder μ)) (p b)))
      (by
        rintro (a | b)
        · exact hd a
        · exact hbase (p b))
      hρinf hj hBc hJc

/-! ## The initial segment through the first `n` fibers -/

/-- `Base 0 = J`, and `Base (n+1)` appends one fresh copy of the level well-order. -/
def StripBase {J : Type u} (μ : Cardinal.{u}) : ℕ → Type u
  | 0 => J
  | n + 1 => StripBase (J := J) μ n ⊕ₗ lvlOrder μ

noncomputable instance stripBase_linear {J : Type u} [LinearOrder J] (μ : Cardinal.{u}) (n : ℕ) :
    LinearOrder (StripBase (J := J) μ n) := by
  induction n with
  | zero =>
      dsimp [StripBase]
      infer_instance
  | succ n ih =>
      dsimp [StripBase]
      letI : LinearOrder (StripBase (J := J) μ n) := ih
      infer_instance

noncomputable instance stripBase_nonempty {J : Type u} [Nonempty J] (μ : Cardinal.{u}) (n : ℕ) :
    Nonempty (StripBase (J := J) μ n) := by
  induction n with
  | zero =>
      dsimp [StripBase]
      infer_instance
  | succ n ih =>
      dsimp [StripBase]
      letI : Nonempty (StripBase (J := J) μ n) := ih
      infer_instance

noncomputable instance stripBase_wf {J : Type u} [LinearOrder J] [WellFoundedLT J] (μ : Cardinal.{u})
    (n : ℕ) : WellFoundedLT (StripBase (J := J) μ n) := by
  induction n with
  | zero =>
      dsimp [StripBase]
      infer_instance
  | succ n ih =>
      dsimp [StripBase]
      letI : WellFoundedLT (StripBase (J := J) μ n) := ih
      infer_instance

theorem stripBase_card {J : Type u} {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (hJ : #J = μ) (n : ℕ) :
    #(StripBase (J := J) μ n) = μ := by
  induction n with
  | zero =>
      dsimp [StripBase]
      exact hJ
  | succ n ih =>
      dsimp [StripBase]
      change #(StripBase (J := J) μ n ⊕ lvlOrder μ) = μ
      rw [mk_sum, lift_id, lift_id, ih, mk_lvlOrder hμ, add_eq_self hμ]

/-- Send `Base n` into the terminal strip: previous points stay, and the newest summand is
fiber `n - 1`. -/
def stripBaseFun {J : Type u} (μ : Cardinal.{u}) : (n : ℕ) → StripBase (J := J) μ n → FreshOrder J μ
  | 0, j => Sum.inlₗ j
  | n + 1, x =>
      match ofLex x with
      | Sum.inl y => stripBaseFun μ n y
      | Sum.inr a => Sum.inrₗ (toLex (n, a))

theorem stripBaseFun_lt_fiber {J : Type u} [LinearOrder J] (μ : Cardinal.{u}) (n : ℕ)
    (x : StripBase (J := J) μ n) (a : lvlOrder μ) :
    stripBaseFun μ n x < Sum.inrₗ (toLex (n, a)) := by
  induction n with
  | zero =>
      unfold stripBaseFun
      exact Sum.Lex.inl_lt_inr x (toLex (0, a))
  | succ n ih =>
      cases hx : ofLex x with
      | inl y =>
          have hlt := ih y
          have hstep : Sum.inrₗ (toLex (n, a)) < Sum.inrₗ (toLex (n + 1, a)) :=
            (Sum.Lex.inr_lt_inr_iff (α := J) (β := ℕ ×ₗ lvlOrder μ)).mpr
              ((Prod.Lex.toLex_lt_toLex).mpr (Or.inl (Nat.lt_succ_self n)))
          have hy : stripBaseFun μ (n + 1) x = stripBaseFun μ n y := by
            simp [stripBaseFun, hx]
          rw [hy]
          exact lt_trans hlt hstep
      | inr b =>
          have hpair : toLex (n, b) < toLex (n + 1, a) :=
            (Prod.Lex.toLex_lt_toLex).mpr (Or.inl (Nat.lt_succ_self n))
          have hx' : stripBaseFun μ (n + 1) x = Sum.inrₗ (toLex (n, b)) := by
            simp [stripBaseFun, hx]
          rw [hx']
          exact (Sum.Lex.inr_lt_inr_iff (α := J) (β := ℕ ×ₗ lvlOrder μ)).mpr hpair

theorem stripBaseFun_strictMono {J : Type u} [LinearOrder J] (μ : Cardinal.{u}) (n : ℕ) :
    StrictMono (stripBaseFun (J := J) μ n) := by
  induction n with
  | zero =>
      intro a b h
      unfold stripBaseFun
      exact (Sum.Lex.inl_lt_inl_iff (α := J) (β := ℕ ×ₗ lvlOrder μ)).mpr h
  | succ n ih =>
      intro x y hxy
      cases hx : ofLex x with
      | inl x0 =>
          cases hy : ofLex y with
          | inl y0 =>
              have hlt : x0 < y0 := by
                have hxeq : x = Sum.inlₗ x0 := by rw [← toLex_ofLex x, hx]
                have hyeq : y = Sum.inlₗ y0 := by rw [← toLex_ofLex y, hy]
                rw [hxeq, hyeq] at hxy
                exact (Sum.Lex.inl_lt_inl_iff
                  (α := StripBase (J := J) μ n) (β := lvlOrder μ)).mp hxy
              have hx' : stripBaseFun μ (n + 1) x = stripBaseFun μ n x0 := by
                simp [stripBaseFun, hx]
              have hy' : stripBaseFun μ (n + 1) y = stripBaseFun μ n y0 := by
                simp [stripBaseFun, hy]
              rw [hx', hy']
              exact ih hlt
          | inr b =>
              have hx' : stripBaseFun μ (n + 1) x = stripBaseFun μ n x0 := by
                simp [stripBaseFun, hx]
              have hy' : stripBaseFun μ (n + 1) y = Sum.inrₗ (toLex (n, b)) := by
                simp [stripBaseFun, hy]
              rw [hx', hy']
              exact stripBaseFun_lt_fiber μ n x0 b
      | inr a =>
          cases hy : ofLex y with
          | inl y0 =>
              exfalso
              have hxeq : x = Sum.inrₗ a := by rw [← toLex_ofLex x, hx]
              have hyeq : y = Sum.inlₗ y0 := by rw [← toLex_ofLex y, hy]
              rw [hxeq, hyeq] at hxy
              exact Sum.Lex.not_inr_le_inl
                (α := StripBase (J := J) μ n) (β := lvlOrder μ) hxy.le
          | inr b =>
              have hlt : a < b := by
                have hxeq : x = Sum.inrₗ a := by rw [← toLex_ofLex x, hx]
                have hyeq : y = Sum.inrₗ b := by rw [← toLex_ofLex y, hy]
                rw [hxeq, hyeq] at hxy
                exact (Sum.Lex.inr_lt_inr_iff
                  (α := StripBase (J := J) μ n) (β := lvlOrder μ)).mp hxy
              have hx' : stripBaseFun μ (n + 1) x = Sum.inrₗ (toLex (n, a)) := by
                simp [stripBaseFun, hx]
              have hy' : stripBaseFun μ (n + 1) y = Sum.inrₗ (toLex (n, b)) := by
                simp [stripBaseFun, hy]
              rw [hx', hy']
              exact (Sum.Lex.inr_lt_inr_iff (α := J) (β := ℕ ×ₗ lvlOrder μ)).mpr
                ((Prod.Lex.toLex_lt_toLex).mpr (Or.inr ⟨rfl, hlt⟩))

noncomputable def stripBaseEmb {J : Type u} [LinearOrder J] (μ : Cardinal.{u}) (n : ℕ) :
    StripBase (J := J) μ n ↪o FreshOrder J μ :=
  OrderEmbedding.ofStrictMono (stripBaseFun μ n) (stripBaseFun_strictMono μ n)

/-- The far-left copy of `J` in the segment that already contains the first `n` fibers. -/
noncomputable def baseIncl {J : Type u} [LinearOrder J] (μ : Cardinal.{u}) :
    (n : ℕ) → (J ↪o StripBase (J := J) μ (n + 1))
  | 0 => sumLexEmbedLeftIncl J (lvlOrder μ)
  | n + 1 =>
      (baseIncl μ n).trans (sumLexEmbedLeftIncl (StripBase (J := J) μ (n + 1)) (lvlOrder μ))

theorem stripBaseFun_left {J : Type u} [LinearOrder J] (μ : Cardinal.{u}) (n : ℕ)
    (x : StripBase (J := J) μ n) :
    stripBaseFun μ (n + 1) (Sum.inlₗ x) = stripBaseFun μ n x := by
  simp only [stripBaseFun, ofLex_toLex]

theorem baseIncl_push {J : Type u} [LinearOrder J] (μ : Cardinal.{u}) (n : ℕ) :
    (baseIncl μ n).trans (stripBaseEmb μ (n + 1)) =
      sumLexEmbedLeftIncl J (ℕ ×ₗ lvlOrder μ) := by
  ext j
  induction n with
  | zero =>
      show stripBaseFun μ 1 (Sum.inlₗ j) = Sum.inlₗ j
      exact stripBaseFun_left μ 0 j
  | succ n ih =>
      show stripBaseFun μ (n + 2) (Sum.inlₗ (baseIncl μ n j)) = Sum.inlₗ j
      exact (stripBaseFun_left μ (n + 1) (baseIncl μ n j)).trans ih

/-- Appending one fiber and reading it in the terminal strip is the previous segment. -/
theorem stripBase_step {J : Type u} [LinearOrder J] (μ : Cardinal.{u}) (n : ℕ) :
    (sumLexEmbedLeftIncl (StripBase (J := J) μ n) (lvlOrder μ)).trans (stripBaseEmb μ (n + 1)) =
      stripBaseEmb μ n := by
  ext x
  exact stripBaseFun_left μ n x

theorem infra_615_push_step (P : SingleModelData K) {J : Type u} [LinearOrder J] [Nonempty J]
    (μ : Cardinal.{u}) (n : ℕ) (x : (P.E.obj (StripBase (J := J) μ (n + 1))).carrier) :
    P.E.map (stripBaseEmb μ (n + 2))
        (P.E.map (sumLexEmbedLeftIncl (StripBase (J := J) μ (n + 1)) (lvlOrder μ)) x) =
      P.E.map (stripBaseEmb μ (n + 1)) x := by
  let left := sumLexEmbedLeftIncl (StripBase (J := J) μ (n + 1)) (lvlOrder μ)
  have happ := congrArg (fun (e : Language.Embedding K.τ
      (P.E.obj (StripBase (J := J) μ (n + 1))).carrier
      (P.E.obj (FreshOrder J μ)).carrier) => e x)
    (P.E.map_comp left (stripBaseEmb μ (n + 2)))
  have hcomp : ((P.E.map (stripBaseEmb μ (n + 2))).comp (P.E.map left)) x =
      P.E.map (stripBaseEmb μ (n + 2)) (P.E.map left x) := rfl
  exact hcomp.symm.trans (happ.symm.trans
    (congrArg (fun e => P.E.map e x) (stripBase_step μ (n + 1))))

theorem infra_615_push_base (P : SingleModelData K) {J : Type u} [LinearOrder J] [Nonempty J]
    (μ : Cardinal.{u}) (n : ℕ) (a : (P.E.obj J).carrier) :
    P.E.map (stripBaseEmb μ (n + 1)) (P.E.map (baseIncl (J := J) μ n) a) =
      P.E.map (sumLexEmbedLeftIncl J (ℕ ×ₗ lvlOrder μ)) a := by
  have happ := congrArg (fun (e : Language.Embedding K.τ (P.E.obj J).carrier
      (P.E.obj (FreshOrder J μ)).carrier) => e a)
    (P.E.map_comp (baseIncl (J := J) μ n) (stripBaseEmb μ (n + 1)))
  have hcomp : ((P.E.map (stripBaseEmb μ (n + 1))).comp
      (P.E.map (baseIncl (J := J) μ n))) a =
    P.E.map (stripBaseEmb μ (n + 1)) (P.E.map (baseIncl (J := J) μ n) a) := rfl
  exact hcomp.symm.trans (happ.symm.trans
    (congrArg (fun e => P.E.map e a) (baseIncl_push μ n)))

/-! ## Exhausting the extension -/

/-- A lift realized in an amalgam over `E(S)` is a lift over `E(I)`, once the amalgam
identifies the two copies of `E(I)`. -/
theorem infra_615_transport
    (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ infra_615_closed P)
    {I : Type u} [LinearOrder I] [Nonempty I]
    {B : Model K.τ}
    (f : Language.Embedding K.τ (P.E.obj I).carrier B.carrier) (hB : K.Mem B)
    (hcard : Model.card B = μ)
    {S : Type u} [LinearOrder S] [Nonempty S]
    (e : I ↪o S) (hS : #S = μ)
    {Q : Model K.τ}
    (gB : Language.Embedding K.τ B.carrier Q.carrier)
    (gS : Language.Embedding K.τ (P.E.obj S).carrier Q.carrier)
    (hQ : K.Mem Q) (hgB : K.Strong gB) (hcQ : Model.card Q = μ)
    (hagree : ∀ a, gB (f a) = gS (P.E.map e a))
    {α : Type u} (d : α → B.carrier)
    (z : α → (P.E.obj (S ⊕ₗ lvlOrder μ)).carrier)
    (hz : LiftsTuple P.E P.D hQ gS μ (sumLexEmbedLeftIncl S (lvlOrder μ))
      (fun i => gB (d i)) z) :
    LiftsTuple P.E P.D hB f μ (e.trans (sumLexEmbedLeftIncl S (lvlOrder μ))) d z := by
  intro β ρ hρinf hρμ p hj hBc hJc
  have hμel : μ ∈ P.eligible := hμ.1
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  have hL : ClosedLevel K P.E P.D P.g μ :=
    ClosedLevel.of_closurePoint P.tester hμel.1 hμel.2
  have hQc : P.D.t ρ ≤ Model.card Q := (hL.t_lt hρinf hρμ).le.trans hcQ.ge
  have h1 := hz ρ hρinf hρμ (fun b => P.E.map e (p b)) hj hQc hJc
  have hLft : (Sum.elim (fun i => gB (d i)) (fun b => gS (P.E.map e (p b)))) =
      fun t => gB ((Sum.elim d (fun b => f (p b))) t) := by
    funext t
    cases t with
    | inl i => rfl
    | inr b => exact (hagree (p b)).symm
  have hRgt : (Sum.elim z (fun b =>
        P.E.map (sumLexEmbedLeftIncl S (lvlOrder μ)) (P.E.map e (p b)))) =
      Sum.elim z (fun b =>
        P.E.map (e.trans (sumLexEmbedLeftIncl S (lvlOrder μ))) (p b)) := by
    funext t
    cases t with
    | inl i => rfl
    | inr b =>
        change P.E.map (sumLexEmbedLeftIncl S (lvlOrder μ)) (P.E.map e (p b)) =
          P.E.map (e.trans (sumLexEmbedLeftIncl S (lvlOrder μ))) (p b)
        rw [P.E.map_comp]
        rfl
  rw [hLft, hRgt] at h1
  exact P.D.trans hj hB hQ (P.hE _) hBc hQc hJc _ _ _
    (P.D.of_strong hj hB hQ hBc hQc (Sum.elim d (fun b => f (p b)))
      (fun t => gB ((Sum.elim d (fun b => f (p b))) t)) gB hρinf hgB
      fun _ => rfl) h1

/-- One inductive step: amalgamate the assigned segment with `B`, realize the next
enumeration in the following fiber, and keep the lift over the original base. -/
theorem infra_615_step
    (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ infra_615_closed P)
    {J : Type u} [LinearOrder J] [Nonempty J] [WellFoundedLT J]
    (hJ : #J = μ)
    {B : Model K.τ}
    (f : Language.Embedding K.τ (P.E.obj J).carrier B.carrier)
    (hB : K.Mem B) (hf : K.Strong f) (hcard : Model.card B = μ)
    (hL : ClosedLevel K P.E P.D P.g μ)
    {n : ℕ} {M M' : Model K.τ}
    (j : Language.Embedding K.τ M.carrier B.carrier) (hj : K.Strong j)
    (hM : Model.card M < μ)
    (j' : Language.Embedding K.τ M'.carrier B.carrier) (hj' : K.Strong j')
    (hM' : Model.card M' < μ)
    (ι : M.carrier → M'.carrier) (hι : ∀ x, j' (ι x) = j x)
    (prev : Language.Embedding K.τ M.carrier
      (P.E.obj (StripBase (J := J) μ (n + 1))).carrier)
    (hprev : K.Strong prev)
    (hlift : LiftsTuple P.E P.D hB f μ (baseIncl μ n) (fun x => j x) prev) :
    ∃ step : Language.Embedding K.τ M'.carrier
        (P.E.obj (StripBase (J := J) μ (n + 2))).carrier,
      K.Strong step ∧
      LiftsTuple P.E P.D hB f μ (baseIncl μ (n + 1)) (fun x => j' x) step ∧
      ∀ x, step (ι x) =
        P.E.map (sumLexEmbedLeftIncl (StripBase (J := J) μ (n + 1)) (lvlOrder μ))
          (prev x) := by
  have hμel : μ ∈ P.eligible := hμ.1
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  let σ : Cardinal.{u} := max (Model.card M) ℵ₀
  have hσ : ℵ₀ ≤ σ := le_max_right _ _
  have hσμ : σ < μ := max_lt hM (P.aleph0_lt hμel)
  obtain ⟨Q, gB, gS, hQ, hgB, hgS, hcQ, hbase, htup⟩ :=
    hL.exists_tuple_amalgam hσ hσμ (le_max_left _ _) (P.E.obj J) B
      (P.E.obj (StripBase (J := J) μ (n + 1))) f (P.E.map (baseIncl μ n))
      (fun x => j x) (fun x => prev x) (P.hE J) hB (P.hE _) hf (P.E.map_strong _)
      (P.card_obj_eq hμel J hJ) hcard
      (P.card_obj_eq hμel _ (stripBase_card (P.aleph0_le hμel) hJ (n + 1)))
      (fun {β} _hβ ρ hρinf hρμ p hj h₀ h₁ => hlift ρ hρinf hρμ p hj h₀ h₁)
  obtain ⟨z, hz⟩ := infra_615_realize_in_fiber P hμ
    (stripBase_card (P.aleph0_le hμel) hJ (n + 1)) gS hQ hgS hcQ
    (fun x => gB (j' x)) hM'
  have hzB := infra_615_transport P hμ f hB hcard (baseIncl μ n)
    (stripBase_card (P.aleph0_le hμel) hJ (n + 1)) gB gS hQ hgB hcQ hbase
    (fun x => j' x) z hz
  obtain ⟨step, hstep, hstepz⟩ := exists_strong_of_liftsTuple hL hcard (baseIncl μ (n + 1))
    (le_of_eq (P.card_obj_eq hμel _
      (stripBase_card (P.aleph0_le hμel) hJ (n + 2))).symm)
    j' hj' hM' hzB
  refine ⟨step, hstep, ?_, ?_⟩
  · intro β ρ hρinf hρμ p hj hBc hJc
    rw [show z = fun x => step x from funext fun x => (hstepz x).symm] at hzB
    exact hzB ρ hρinf hρμ p hj hBc hJc
  · intro x
    rw [hstepz]
    have hρinf : ℵ₀ ≤ Model.card M' ⊔ ℵ₀ := le_sup_right
    have hρμ : Model.card M' ⊔ ℵ₀ < μ := max_lt hM' (P.aleph0_lt hμel)
    have hjρ : #(M'.carrier ⊕ PUnit.{u + 1}) ≤ Model.card M' ⊔ ℵ₀ := by
      rw [mk_sum, lift_id, lift_id, mk_punit]
      exact add_le_of_le hρinf le_sup_left (one_le_aleph0.trans le_sup_right)
    have hQc : P.D.t (Model.card M' ⊔ ℵ₀) ≤ Model.card Q :=
      (hL.t_lt hρinf hρμ).le.trans hcQ.ge
    have hSc : P.D.t (Model.card M' ⊔ ℵ₀) ≤
        Model.card (P.E.obj (StripBase (J := J) μ (n + 2))) :=
      (hL.t_lt hρinf hρμ).le.trans
        (le_of_eq (P.card_obj_eq hμel _
          (stripBase_card (P.aleph0_le hμel) hJ (n + 2))).symm)
    have hsame := hz (Model.card M' ⊔ ℵ₀) hρinf hρμ (fun _ : PUnit.{u + 1} => prev x)
      hjρ hQc hSc
    have hxeq : gB (j' (ι x)) = gS (prev x) := (congrArg gB (hι x)).trans (htup x)
    exact (P.D.preserves_atomic hjρ hQ (P.hE _) hQc hSc _ _ hsame
      (Sum.inl (ι x)) (Sum.inr PUnit.unit)).mp hxeq

/-- **Infra `infra_615_exhaust_embed`.** Every same-level strong extension of `E(J)` embeds
strongly into `E(J ⊕ₗ H)` over the left inclusion. Countable strong tower, amalgamation with
the segment used so far, one fiber per stage, then a countable union of the strong copies. -/
theorem infra_615_exhaust_embed
    (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ infra_615_closed P)
    {J : Type u} [LinearOrder J] [Nonempty J] [WellFoundedLT J]
    (hJ : #J = μ)
    {B : Model K.τ}
    (f : Language.Embedding K.τ (P.E.obj J).carrier B.carrier)
    (hB : K.Mem B) (hf : K.Strong f) (hcard : Model.card B = μ) :
    ∃ g : Language.Embedding K.τ B.carrier
        (P.E.obj (FreshOrder J μ)).carrier,
      K.Strong g ∧ ∀ a, g (f a) =
        P.E.map (sumLexEmbedLeftIncl J (ℕ ×ₗ lvlOrder μ)) a := by
  classical
  have hμel : μ ∈ P.eligible := hμ.1
  haveI : CategoricalUnbounded K := P.D.categoricalUnbounded
  have hL : ClosedLevel K P.E P.D P.g μ :=
    ClosedLevel.of_closurePoint P.tester hμel.1 hμel.2
  obtain ⟨M, j, hj, hMc, hmono, hcov, _⟩ :=
    exists_strong_tower hB (P.aleph0_le hμel) hμel.1.working.countableCof (P.ls_lt hμel)
      hcard (fun e : PEmpty.{u + 1} => e.elim)
      (by rw [mk_pempty]; exact aleph0_pos.trans_le (P.aleph0_le hμel))
  choose ι hι using hmono
  obtain ⟨z0, hz0⟩ := infra_615_realize_in_fiber P hμ hJ f hB hf hcard
    (fun x => j 0 x) (hMc 0)
  obtain ⟨s0, hs0, hs0z⟩ := exists_strong_of_liftsTuple hL hcard (baseIncl (J := J) μ 0)
    (le_of_eq (P.card_obj_eq hμel _
      (stripBase_card (P.aleph0_le hμel) hJ 1)).symm)
    (j 0) (hj 0) (hMc 0) hz0
  have hlift0 : LiftsTuple P.E P.D hB f μ (baseIncl (J := J) μ 0) (fun x => j 0 x)
      (fun x => s0 x) := by
    rw [show z0 = fun x => s0 x from funext fun x => (hs0z x).symm] at hz0
    exact hz0
  have hstep : ∀ n (prev : Language.Embedding K.τ (M n).carrier
        (P.E.obj (StripBase (J := J) μ (n + 1))).carrier),
      K.Strong prev →
      LiftsTuple P.E P.D hB f μ (baseIncl (J := J) μ n) (fun x => j n x) prev →
      ∃ step : Language.Embedding K.τ (M (n + 1)).carrier
          (P.E.obj (StripBase (J := J) μ (n + 2))).carrier,
        K.Strong step ∧
        LiftsTuple P.E P.D hB f μ (baseIncl (J := J) μ (n + 1))
          (fun x => j (n + 1) x) step ∧
        ∀ x, step (ι n x) =
          P.E.map (sumLexEmbedLeftIncl (StripBase (J := J) μ (n + 1)) (lvlOrder μ))
            (prev x) :=
    fun n prev hp hl => infra_615_step P hμ hJ f hB hf hcard hL (j n) (hj n) (hMc n)
      (j (n + 1)) (hj (n + 1)) (hMc (n + 1)) (ι n) (hι n) prev hp hl
  let S : ∀ n, {s : Language.Embedding K.τ (M n).carrier
      (P.E.obj (StripBase (J := J) μ (n + 1))).carrier //
      K.Strong s ∧
        LiftsTuple P.E P.D hB f μ (baseIncl (J := J) μ n) (fun x => j n x) s} :=
    fun n => Nat.rec (motive := fun n => {s : Language.Embedding K.τ (M n).carrier
        (P.E.obj (StripBase (J := J) μ (n + 1))).carrier //
        K.Strong s ∧ LiftsTuple P.E P.D hB f μ (baseIncl (J := J) μ n)
          (fun x => j n x) s})
      ⟨s0, hs0, hlift0⟩
      (fun n P =>
        let e := hstep n P.1 P.2.1 P.2.2
        ⟨Classical.choose e, (Classical.choose_spec e).1, (Classical.choose_spec e).2.1⟩) n
  have hS : ∀ n x, (S (n + 1)).1 (ι n x) =
      P.E.map (sumLexEmbedLeftIncl (StripBase (J := J) μ (n + 1)) (lvlOrder μ))
        ((S n).1 x) :=
    fun n x => (Classical.choose_spec (hstep n (S n).1 (S n).2.1 (S n).2.2)).2.2 x
  let h : ∀ n, Language.Embedding K.τ (M n).carrier
      (P.E.obj (FreshOrder J μ)).carrier :=
    fun n => (P.E.map (stripBaseEmb μ (n + 1))).comp (S n).1
  have hh : ∀ n, K.Strong (h n) := fun n =>
    K.strong_trans _ _ (S n).2.1 (P.E.map_strong _)
  have hcoh : ∀ n x y, j (n + 1) y = j n x → (h (n + 1)) y = (h n) x := by
    intro n x y hxy
    have hy : y = ι n x := (j (n + 1)).injective (hxy.trans (hι n x).symm)
    rw [hy]
    change P.E.map (stripBaseEmb μ (n + 2)) ((S (n + 1)).1 (ι n x)) =
      P.E.map (stripBaseEmb μ (n + 1)) ((S n).1 x)
    rw [hS n x]
    exact infra_615_push_step P μ n ((S n).1 x)
  obtain ⟨F, hF, hFj⟩ := exists_strong_of_nat_exhaustion hB (P.hE (FreshOrder J μ)) M j hj
    (fun n x => ⟨ι n x, hι n x⟩) hcov h hh hcoh
  refine ⟨F, hF, fun a => ?_⟩
  obtain ⟨n, x, hx⟩ := hcov (f a)
  rw [← hx, hFj]
  have hfix : (S n).1 x = P.E.map (baseIncl (J := J) μ n) a := by
    have hρinf : ℵ₀ ≤ Model.card (M n) ⊔ ℵ₀ := le_sup_right
    have hρμ : Model.card (M n) ⊔ ℵ₀ < μ := max_lt (hMc n) (P.aleph0_lt hμel)
    have hjρ : #((M n).carrier ⊕ PUnit.{u + 1}) ≤ Model.card (M n) ⊔ ℵ₀ := by
      rw [mk_sum, lift_id, lift_id, mk_punit]
      exact add_le_of_le hρinf le_sup_left (one_le_aleph0.trans le_sup_right)
    have hBc : P.D.t (Model.card (M n) ⊔ ℵ₀) ≤ Model.card B :=
      (hL.t_lt hρinf hρμ).le.trans hcard.ge
    have hGc : P.D.t (Model.card (M n) ⊔ ℵ₀) ≤
        Model.card (P.E.obj (StripBase (J := J) μ (n + 1))) :=
      (hL.t_lt hρinf hρμ).le.trans
        (le_of_eq (P.card_obj_eq hμel _
          (stripBase_card (P.aleph0_le hμel) hJ (n + 1))).symm)
    have hsame := (S n).2.2 (Model.card (M n) ⊔ ℵ₀) hρinf hρμ
      (fun _ : PUnit.{u + 1} => a) hjρ hBc hGc
    exact (P.D.preserves_atomic hjρ hB (P.hE _) hBc hGc _ _ hsame
      (Sum.inl x) (Sum.inr PUnit.unit)).mp hx
  change P.E.map (stripBaseEmb μ (n + 1)) ((S n).1 x) =
    P.E.map (sumLexEmbedLeftIncl J (ℕ ×ₗ lvlOrder μ)) a
  rw [hfix]
  exact infra_615_push_base P μ n a

end
end AEC
