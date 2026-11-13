module

public import AEC.Section6.FreshStrip
public import AEC.Section6.ApproximateRetraction
public import AEC.Section4.UniformTesting
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

/-!
# Corollary 6.16: approximate retractions

Present `A` on the well-order `W = lvlOrder μ ×ₗ (ℕ ×ₗ lvlOrder μ)`, a lexicographic
product of `μ` blocks each of size `μ`. Block `0` is a sentinel. For each later block `i`,
the complement splits into the blocks strictly below `i` and those strictly above `i`.
The order isomorphism `φᵢ : MTop L R μ ≃o W` sends the fresh middle strip onto block `i`
and satisfies `φᵢ ∘ baseInto =` the inclusion of the complement. Proposition 6.15's
two-sided exhaustion (`infra_615_middle_exhaust`) embeds `B` into `E(MTop)` over that
complement; postcomposing with `E.map φᵢ` and the presentation equivalence `E(W) ≃ A`
lands in `A`. A point of `A` is moved only when its finite support meets the block, so
each point is moved only finitely often.

The one-sided enlargement `infra_615_terminal` is not used.
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function Ordinal Set Sum

attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-- Blocks of the presentation order, each a copy of `ℕ ×ₗ lvlOrder μ`. -/
abbrev RetFiber (μ : Cardinal.{u}) := ℕ ×ₗ lvlOrder μ

/-- The well-order presenting `A`: one block for each point of `lvlOrder μ`. -/
abbrev RetWell (μ : Cardinal.{u}) := lvlOrder μ ×ₗ RetFiber μ

instance (μ : Cardinal.{u}) : Nonempty (RetWell μ) :=
  ⟨toLex (Classical.arbitrary (lvlOrder μ), toLex (0, Classical.arbitrary (lvlOrder μ)))⟩

def blockOf {μ : Cardinal.{u}} (w : RetWell μ) : lvlOrder μ := (ofLex w).1

def fiberOf {μ : Cardinal.{u}} (w : RetWell μ) : RetFiber μ := (ofLex w).2

@[simp] theorem blockOf_toLex {μ : Cardinal.{u}} (b : lvlOrder μ) (h : RetFiber μ) :
    blockOf (toLex (b, h)) = b := rfl

@[simp] theorem fiberOf_toLex {μ : Cardinal.{u}} (b : lvlOrder μ) (h : RetFiber μ) :
    fiberOf (toLex (b, h)) = h := rfl

theorem retWell_lt_iff {μ : Cardinal.{u}} {w₁ w₂ : RetWell μ} :
    w₁ < w₂ ↔
      blockOf w₁ < blockOf w₂ ∨
        blockOf w₁ = blockOf w₂ ∧ fiberOf w₁ < fiberOf w₂ := by
  rw [Prod.Lex.lt_iff]
  simp [blockOf, fiberOf]

theorem retWell_lt_block {μ : Cardinal.{u}} {w₁ w₂ : RetWell μ}
    (h : blockOf w₁ < blockOf w₂) : w₁ < w₂ :=
  (retWell_lt_iff).mpr (Or.inl h)

theorem retWell_card {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) : #(RetWell μ) = μ := by
  have hfiber : #(RetFiber μ) = μ := freshOrder_card hμ
  change #(lvlOrder μ × RetFiber μ) = μ
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, mk_lvlOrder hμ, hfiber]
  exact mul_eq_right hμ le_rfl ((aleph0_pos.trans_le hμ).ne')

/-- The least block. It is never a retraction index, so every index has blocks on its left. -/
def blockBot {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) : lvlOrder μ :=
  enum (α := lvlOrder μ) (· < ·) ⟨0, by
    rw [type_toType]
    exact (Cardinal.ord_pos).2 (zero_lt_one.trans_le (le_max_right μ 1))⟩

theorem typein_blockBot {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) :
    typein (α := lvlOrder μ) (· < ·) (blockBot hμ) = 0 := by
  unfold blockBot
  exact typein_enum (· < ·) _

theorem not_lt_blockBot {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) {j : lvlOrder μ} :
    ¬ j < blockBot hμ := by
  intro hj
  have hlt : typein (α := lvlOrder μ) (· < ·) j <
      typein (α := lvlOrder μ) (· < ·) (blockBot hμ) :=
    (typein_lt_typein (· < ·)).2 hj
  rw [typein_blockBot hμ] at hlt
  exact not_lt_bot hlt

theorem blockBot_le {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (i : lvlOrder μ) :
    blockBot hμ ≤ i :=
  le_of_not_gt (not_lt_blockBot hμ)

theorem blockBot_lt_of_ne {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) {i : lvlOrder μ}
    (hi : i ≠ blockBot hμ) : blockBot hμ < i :=
  lt_of_le_of_ne (blockBot_le hμ i) hi.symm

theorem exists_block_gt {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (i : lvlOrder μ) :
    ∃ j, i < j := by
  have hcard : max μ 1 = μ := max_eq_left (one_le_aleph0.trans hμ)
  have hord : (max μ 1).ord = μ.ord := congrArg Cardinal.ord hcard
  have hlim : Order.IsSuccLimit μ.ord := Cardinal.isSuccLimit_ord hμ
  have hi : (i : Ordinal) < (max μ 1).ord := (ToType.toOrd i).2
  have hsucc : Order.succ (i : Ordinal) < (max μ 1).ord :=
    (hlim.succ_lt (hi.trans_eq hord)).trans_eq hord.symm
  let j : lvlOrder μ := ToType.mk ⟨Order.succ (i : Ordinal), hsucc⟩
  have hj : (j : Ordinal) = Order.succ (i : Ordinal) := by
    change (ToType.toOrd j).1 = Order.succ (i : Ordinal)
    rw [show ToType.toOrd j = ⟨Order.succ (i : Ordinal), hsucc⟩ from
      (ToType.mk (o := (max μ 1).ord)).symm_apply_apply _]
  have hlt : (ToType.mk (o := (max μ 1).ord)).symm i <
      (ToType.mk (o := (max μ 1).ord)).symm j := by
    change (i : Ordinal) < (j : Ordinal)
    rw [hj]
    exact (Order.lt_succ_iff).mpr le_rfl
  exact ⟨j, ((ToType.mk (o := (max μ 1).ord)).symm.lt_iff_lt).mpr hlt⟩

/-- Retraction indices: every block except the sentinel. -/
abbrev RetIndex {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) := {i : lvlOrder μ // i ≠ blockBot hμ}

theorem mk_remove_one {α : Type u} (h : ℵ₀ ≤ #α) (a : α) : #{x // x ≠ a} = #α := by
  classical
  have hsplit : #{x // x = a} + #{x // x ≠ a} = #α := by
    refine Eq.trans ?_ (Cardinal.mk_congr (Equiv.sumCompl (fun x => x = a)))
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
  have hone : #{x // x = a} = 1 := by
    haveI : Subsingleton {x // x = a} := ⟨fun x y => Subtype.ext (x.2.trans y.2.symm)⟩
    haveI : Nonempty {x // x = a} := ⟨⟨a, rfl⟩⟩
    exact Cardinal.mk_eq_one _
  have hinf : ℵ₀ ≤ #{x // x ≠ a} := by
    by_contra hlt
    have hsmall : #{x // x ≠ a} < ℵ₀ := lt_of_not_ge hlt
    have hsum : #{x // x = a} + #{x // x ≠ a} < ℵ₀ := by
      rw [hone]
      exact Cardinal.add_lt_aleph0 one_lt_aleph0 hsmall
    rw [hsplit] at hsum
    exact not_lt_of_ge h hsum
  calc #{x // x ≠ a}
      = 1 + #{x // x ≠ a} :=
        (Cardinal.add_eq_right hinf (one_le_aleph0.trans hinf)).symm
    _ = #{x // x = a} + #{x // x ≠ a} := by rw [hone]
    _ = #α := hsplit

theorem retIndex_card {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) : #(RetIndex hμ) = μ := by
  have hα : ℵ₀ ≤ #(lvlOrder μ) := by simpa [mk_lvlOrder hμ] using hμ
  rw [mk_remove_one hα (blockBot hμ), mk_lvlOrder hμ]

abbrev LeftBlocks (μ : Cardinal.{u}) (i : lvlOrder μ) := {w : RetWell μ // blockOf w < i}

abbrev RightBlocks (μ : Cardinal.{u}) (i : lvlOrder μ) := {w : RetWell μ // i < blockOf w}

abbrev missedBlocks (μ : Cardinal.{u}) (i : lvlOrder μ) : Set (RetWell μ) :=
  {w | blockOf w ≠ i}

theorem leftBlocks_nonempty {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) {i : lvlOrder μ}
    (hi : i ≠ blockBot hμ) : Nonempty (LeftBlocks μ i) := by
  refine ⟨⟨toLex (blockBot hμ, toLex (0, Classical.arbitrary (lvlOrder μ))), ?_⟩⟩
  simpa [blockOf_toLex] using blockBot_lt_of_ne hμ hi

theorem rightBlocks_nonempty {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (i : lvlOrder μ) :
    Nonempty (RightBlocks μ i) := by
  obtain ⟨j, hj⟩ := exists_block_gt hμ i
  refine ⟨⟨toLex (j, toLex (0, Classical.arbitrary (lvlOrder μ))), ?_⟩⟩
  simpa [blockOf_toLex] using hj

noncomputable def sumBlocksEquiv {μ : Cardinal.{u}} (i : lvlOrder μ) :
    (LeftBlocks μ i ⊕ RightBlocks μ i) ≃ {w : RetWell μ // blockOf w ≠ i} where
  toFun
    | Sum.inl l => ⟨l.1, ne_of_lt l.2⟩
    | Sum.inr r => ⟨r.1, ne_of_gt r.2⟩
  invFun w :=
    if h : blockOf w.1 < i then Sum.inl ⟨w.1, h⟩
    else Sum.inr ⟨w.1, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm w.2)⟩
  left_inv := by
    rintro (l | r)
    · dsimp
      rw [dite_eq_left l.2]
    · dsimp
      rw [dite_eq_right (not_lt_of_gt r.2)]
  right_inv w := by
    dsimp
    by_cases h : blockOf w.1 < i
    · rw [dite_eq_left h]
    · rw [dite_eq_right h]

noncomputable def complProdEquiv {μ : Cardinal.{u}} (i : lvlOrder μ) :
    {w : RetWell μ // blockOf w ≠ i} ≃ {b : lvlOrder μ // b ≠ i} × RetFiber μ where
  toFun w := (⟨blockOf w.1, w.2⟩, fiberOf w.1)
  invFun p := ⟨toLex (p.1.1, p.2), by simpa [blockOf_toLex] using p.1.2⟩
  left_inv w := Subtype.ext <| by
    change toLex (blockOf w.1, fiberOf w.1) = w.1
    rw [← toLex_ofLex w.1]
    rfl
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (by simp [blockOf_toLex])
    · simp [fiberOf_toLex]

theorem compl_card {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (i : lvlOrder μ) :
    #{w : RetWell μ // blockOf w ≠ i} = μ := by
  rw [Cardinal.mk_congr (complProdEquiv i), Cardinal.mk_prod, Cardinal.lift_id,
    Cardinal.lift_id]
  have hidx : #{b : lvlOrder μ // b ≠ i} = μ := by
    have hα : ℵ₀ ≤ #(lvlOrder μ) := by simpa [mk_lvlOrder hμ] using hμ
    rw [mk_remove_one hα i, mk_lvlOrder hμ]
  rw [hidx, freshOrder_card hμ]
  exact mul_eq_right hμ le_rfl ((aleph0_pos.trans_le hμ).ne')

theorem blocks_card {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) (i : lvlOrder μ) :
    #((LeftBlocks μ i) ⊕ₗ (RightBlocks μ i)) = μ := by
  change #((LeftBlocks μ i) ⊕ (RightBlocks μ i)) = μ
  rw [Cardinal.mk_congr (sumBlocksEquiv i)]
  exact compl_card hμ i

/-! ## Complement inclusion and the block isomorphism -/

def complementInclFun {μ : Cardinal.{u}} (i : lvlOrder μ) :
    ((LeftBlocks μ i) ⊕ₗ (RightBlocks μ i)) → RetWell μ
  | x =>
    match ofLex x with
    | Sum.inl l => l.1
    | Sum.inr r => r.1

@[simp] theorem complementInclFun_inl {μ : Cardinal.{u}} (i : lvlOrder μ)
    (l : LeftBlocks μ i) :
    complementInclFun i (Sum.inlₗ l) = l.1 := rfl

@[simp] theorem complementInclFun_inr {μ : Cardinal.{u}} (i : lvlOrder μ)
    (r : RightBlocks μ i) :
    complementInclFun i (Sum.inrₗ r) = r.1 := rfl

theorem complementInclFun_strictMono {μ : Cardinal.{u}} (i : lvlOrder μ) :
    StrictMono (complementInclFun i) := by
  intro x y hxy
  cases hx : ofLex x with
  | inl xl =>
    cases hy : ofLex y with
    | inl yl =>
      have hlt : xl < yl := by
        rw [eq_inlₗ hx, eq_inlₗ hy] at hxy
        exact (Sum.Lex.inl_lt_inl_iff).mp hxy
      rw [eq_inlₗ hx, eq_inlₗ hy, complementInclFun_inl, complementInclFun_inl]
      exact hlt
    | inr yr =>
      rw [eq_inlₗ hx, eq_inrₗ hy, complementInclFun_inl, complementInclFun_inr]
      exact retWell_lt_block (lt_trans xl.2 yr.2)
  | inr xr =>
    cases hy : ofLex y with
    | inl _ =>
      exfalso
      rw [eq_inrₗ hx, eq_inlₗ hy] at hxy
      exact Sum.Lex.not_inr_le_inl hxy.le
    | inr yr =>
      have hlt : xr < yr := by
        rw [eq_inrₗ hx, eq_inrₗ hy] at hxy
        exact (Sum.Lex.inr_lt_inr_iff).mp hxy
      rw [eq_inrₗ hx, eq_inrₗ hy, complementInclFun_inr, complementInclFun_inr]
      exact hlt

def complementIncl {μ : Cardinal.{u}} (i : lvlOrder μ) :
    ((LeftBlocks μ i) ⊕ₗ (RightBlocks μ i)) ↪o RetWell μ :=
  OrderEmbedding.ofStrictMono (complementInclFun i) (complementInclFun_strictMono i)

@[simp] theorem complementIncl_apply {μ : Cardinal.{u}} (i : lvlOrder μ)
    (x : (LeftBlocks μ i) ⊕ₗ (RightBlocks μ i)) :
    complementIncl i x = complementInclFun i x := rfl

def phiFun {μ : Cardinal.{u}} (i : lvlOrder μ) :
    MTop (L := LeftBlocks μ i) (R := RightBlocks μ i) μ → RetWell μ
  | x =>
    match ofLex x with
    | Sum.inl l => l.1
    | Sum.inr p =>
      match ofLex p with
      | Sum.inl h => toLex (i, h)
      | Sum.inr r => r.1

@[simp] theorem phiFun_inl {μ : Cardinal.{u}} (i : lvlOrder μ) (l : LeftBlocks μ i) :
    phiFun i (Sum.inlₗ l) = l.1 := rfl

@[simp] theorem phiFun_fiber {μ : Cardinal.{u}} (i : lvlOrder μ) (h : RetFiber μ) :
    phiFun i (Sum.inrₗ (Sum.inlₗ h)) = toLex (i, h) := rfl

@[simp] theorem phiFun_right {μ : Cardinal.{u}} (i : lvlOrder μ) (r : RightBlocks μ i) :
    phiFun i (Sum.inrₗ (Sum.inrₗ r)) = r.1 := rfl

def phiInvFun {μ : Cardinal.{u}} (i : lvlOrder μ) (w : RetWell μ) :
    MTop (L := LeftBlocks μ i) (R := RightBlocks μ i) μ :=
  if hlt : blockOf w < i then Sum.inlₗ ⟨w, hlt⟩
  else if hgt : i < blockOf w then Sum.inrₗ (Sum.inrₗ ⟨w, hgt⟩)
  else Sum.inrₗ (Sum.inlₗ (fiberOf w))

theorem phiInv_left {μ : Cardinal.{u}} {i : lvlOrder μ} {w : RetWell μ}
    (hlt : blockOf w < i) :
    phiInvFun i w = Sum.inlₗ (⟨w, hlt⟩ : LeftBlocks μ i) := by
  rw [phiInvFun, dite_eq_left hlt]

theorem phiInv_right {μ : Cardinal.{u}} {i : lvlOrder μ} {w : RetWell μ}
    (hgt : i < blockOf w) :
    phiInvFun i w = Sum.inrₗ (Sum.inrₗ (⟨w, hgt⟩ : RightBlocks μ i)) := by
  have hnot : ¬ blockOf w < i := not_lt_of_gt hgt
  rw [phiInvFun, dite_eq_right hnot, dite_eq_left hgt]

theorem phiInv_mid {μ : Cardinal.{u}} {i : lvlOrder μ} {w : RetWell μ}
    (heq : blockOf w = i) :
    phiInvFun i w = Sum.inrₗ (Sum.inlₗ (fiberOf w)) := by
  have hnotlt : ¬ blockOf w < i := by rw [heq]; exact lt_irrefl _
  have hnotgt : ¬ i < blockOf w := by rw [heq]; exact lt_irrefl _
  rw [phiInvFun, dite_eq_right hnotlt, dite_eq_right hnotgt]

theorem phiFun_left_inv {μ : Cardinal.{u}} (i : lvlOrder μ)
    (x : MTop (L := LeftBlocks μ i) (R := RightBlocks μ i) μ) :
    phiInvFun i (phiFun i x) = x := by
  cases hx : ofLex x with
  | inl l =>
    rw [eq_inlₗ hx, phiFun_inl, phiInv_left l.2]
  | inr p =>
    cases hp : ofLex p with
    | inl h =>
      rw [eq_inrₗ hx, eq_inlₗ hp, phiFun_fiber]
      have heq : blockOf (toLex (i, h)) = i := by simp [blockOf_toLex]
      rw [phiInv_mid heq, fiberOf_toLex]
    | inr r =>
      rw [eq_inrₗ hx, eq_inrₗ hp, phiFun_right, phiInv_right r.2]

theorem phiFun_right_inv {μ : Cardinal.{u}} (i : lvlOrder μ) (w : RetWell μ) :
    phiFun i (phiInvFun i w) = w := by
  by_cases hlt : blockOf w < i
  · rw [phiInv_left hlt, phiFun_inl]
  · by_cases hgt : i < blockOf w
    · rw [phiInv_right hgt, phiFun_right]
    · have heq : blockOf w = i :=
        le_antisymm (le_of_not_gt hgt) (le_of_not_gt hlt)
      rw [phiInv_mid heq, phiFun_fiber, ← heq]
      rw [← toLex_ofLex w]
      rfl

theorem phiFun_strictMono {μ : Cardinal.{u}} (i : lvlOrder μ) : StrictMono (phiFun i) := by
  intro x y hxy
  cases hx : ofLex x with
  | inl xl =>
    cases hy : ofLex y with
    | inl yl =>
      have hlt : xl < yl := by
        rw [eq_inlₗ hx, eq_inlₗ hy] at hxy
        exact (Sum.Lex.inl_lt_inl_iff).mp hxy
      rw [eq_inlₗ hx, eq_inlₗ hy, phiFun_inl, phiFun_inl]
      exact hlt
    | inr yp =>
      cases hyp : ofLex yp with
      | inl h =>
        rw [eq_inlₗ hx, eq_inrₗ hy, eq_inlₗ hyp, phiFun_inl, phiFun_fiber]
        exact retWell_lt_block (by simpa [blockOf_toLex] using xl.2)
      | inr r =>
        rw [eq_inlₗ hx, eq_inrₗ hy, eq_inrₗ hyp, phiFun_inl, phiFun_right]
        exact retWell_lt_block (lt_trans xl.2 r.2)
  | inr xp =>
    cases hy : ofLex y with
    | inl _ =>
      exfalso
      rw [eq_inrₗ hx, eq_inlₗ hy] at hxy
      exact Sum.Lex.not_inr_le_inl hxy.le
    | inr yp =>
      have hinner : xp < yp := by
        rw [eq_inrₗ hx, eq_inrₗ hy] at hxy
        exact (Sum.Lex.inr_lt_inr_iff).mp hxy
      cases hxp : ofLex xp with
      | inl hxF =>
        cases hyp : ofLex yp with
        | inl hyF =>
          have hF : hxF < hyF := by
            rw [eq_inlₗ hxp, eq_inlₗ hyp] at hinner
            exact (Sum.Lex.inl_lt_inl_iff).mp hinner
          rw [eq_inrₗ hx, eq_inrₗ hy, eq_inlₗ hxp, eq_inlₗ hyp, phiFun_fiber, phiFun_fiber]
          exact (retWell_lt_iff).mpr
            (Or.inr ⟨by simp [blockOf_toLex], by simpa [fiberOf_toLex] using hF⟩)
        | inr r =>
          rw [eq_inrₗ hx, eq_inrₗ hy, eq_inlₗ hxp, eq_inrₗ hyp, phiFun_fiber, phiFun_right]
          exact retWell_lt_block (by simpa [blockOf_toLex] using r.2)
      | inr xr =>
        cases hyp : ofLex yp with
        | inl _ =>
          exfalso
          rw [eq_inrₗ hxp, eq_inlₗ hyp] at hinner
          exact Sum.Lex.not_inr_le_inl hinner.le
        | inr yr =>
          have hrr : xr < yr := by
            rw [eq_inrₗ hxp, eq_inrₗ hyp] at hinner
            exact (Sum.Lex.inr_lt_inr_iff).mp hinner
          rw [eq_inrₗ hx, eq_inrₗ hy, eq_inrₗ hxp, eq_inrₗ hyp, phiFun_right, phiFun_right]
          exact hrr

theorem phiInvFun_strictMono {μ : Cardinal.{u}} (i : lvlOrder μ) :
    StrictMono (phiInvFun i) := by
  intro w₁ w₂ hlt
  rcases (retWell_lt_iff).mp hlt with hbl | ⟨heq, hf⟩
  · by_cases h1 : blockOf w₁ < i
    · by_cases h2 : blockOf w₂ < i
      · rw [phiInv_left h1, phiInv_left h2]
        exact (Sum.Lex.inl_lt_inl_iff).mpr hlt
      · by_cases h2eq : blockOf w₂ = i
        · rw [phiInv_left h1, phiInv_mid h2eq]
          exact Sum.Lex.inl_lt_inr _ _
        · have h2gt : i < blockOf w₂ :=
            lt_of_le_of_ne (le_of_not_gt h2) (Ne.symm h2eq)
          rw [phiInv_left h1, phiInv_right h2gt]
          exact Sum.Lex.inl_lt_inr _ _
    · have h1ge : i ≤ blockOf w₁ := le_of_not_gt h1
      have h2gt : i < blockOf w₂ := lt_of_le_of_lt h1ge hbl
      by_cases h1eq : blockOf w₁ = i
      · rw [phiInv_mid h1eq, phiInv_right h2gt]
        exact (Sum.Lex.inr_lt_inr_iff).mpr (Sum.Lex.inl_lt_inr _ _)
      · have h1gt : i < blockOf w₁ := lt_of_le_of_ne h1ge (Ne.symm h1eq)
        rw [phiInv_right h1gt, phiInv_right h2gt]
        exact (Sum.Lex.inr_lt_inr_iff).mpr ((Sum.Lex.inr_lt_inr_iff).mpr hlt)
  · by_cases hlt1 : blockOf w₁ < i
    · have hlt2 : blockOf w₂ < i := by rwa [← heq]
      rw [phiInv_left hlt1, phiInv_left hlt2]
      exact (Sum.Lex.inl_lt_inl_iff).mpr hlt
    · by_cases hgt1 : i < blockOf w₁
      · have hgt2 : i < blockOf w₂ := by rwa [← heq]
        rw [phiInv_right hgt1, phiInv_right hgt2]
        exact (Sum.Lex.inr_lt_inr_iff).mpr ((Sum.Lex.inr_lt_inr_iff).mpr hlt)
      · have heq1 : blockOf w₁ = i :=
          le_antisymm (le_of_not_gt hgt1) (le_of_not_gt hlt1)
        have heq2 : blockOf w₂ = i := by rw [← heq, heq1]
        rw [phiInv_mid heq1, phiInv_mid heq2]
        exact (Sum.Lex.inr_lt_inr_iff).mpr ((Sum.Lex.inl_lt_inl_iff).mpr hf)

/-- Identify the two-sided enlargement of the complement of block `i` with `W`,
sending the fresh strip onto that block. -/
def blockPhi {μ : Cardinal.{u}} (i : lvlOrder μ) :
    MTop (L := LeftBlocks μ i) (R := RightBlocks μ i) μ ≃o RetWell μ where
  toFun := phiFun i
  invFun := phiInvFun i
  left_inv := phiFun_left_inv i
  right_inv := phiFun_right_inv i
  map_rel_iff' := by
    intro a b
    constructor
    · intro h
      simpa [phiFun_left_inv] using (phiInvFun_strictMono i).monotone h
    · intro h
      exact (phiFun_strictMono i).monotone h

@[simp] theorem blockPhi_apply {μ : Cardinal.{u}} (i : lvlOrder μ)
    (x : MTop (L := LeftBlocks μ i) (R := RightBlocks μ i) μ) :
    blockPhi i x = phiFun i x := rfl

theorem phi_baseInto {μ : Cardinal.{u}} (i : lvlOrder μ)
    [Nonempty (LeftBlocks μ i)] [Nonempty (RightBlocks μ i)] :
    ((baseInto (L := LeftBlocks μ i) (R := RightBlocks μ i) μ).trans
        (blockPhi i).toOrderEmbedding) =
      complementIncl i := by
  ext x
  rw [RelEmbedding.trans_apply, OrderIso.coe_toOrderEmbedding]
  cases hx : ofLex x with
  | inl l =>
    rw [eq_inlₗ hx, baseInto_apply, baseIntoFun_inl, blockPhi_apply, phiFun_inl,
      complementIncl_apply, complementInclFun_inl]
  | inr r =>
    rw [eq_inrₗ hx, baseInto_apply, baseIntoFun_inr, blockPhi_apply, phiFun_right,
      complementIncl_apply, complementInclFun_inr]

theorem complementInclFun_ne {μ : Cardinal.{u}} (i : lvlOrder μ)
    (x : (LeftBlocks μ i) ⊕ₗ (RightBlocks μ i)) :
    blockOf (complementInclFun i x) ≠ i := by
  cases hx : ofLex x with
  | inl l =>
    rw [eq_inlₗ hx, complementInclFun_inl]
    exact ne_of_lt l.2
  | inr r =>
    rw [eq_inrₗ hx, complementInclFun_inr]
    exact ne_of_gt r.2

def placePos {μ : Cardinal.{u}} (i : lvlOrder μ) (w : RetWell μ) (h : blockOf w ≠ i) :
    (LeftBlocks μ i) ⊕ₗ (RightBlocks μ i) :=
  if hlt : blockOf w < i then Sum.inlₗ ⟨w, hlt⟩
  else Sum.inrₗ ⟨w, lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm h)⟩

theorem placePos_spec {μ : Cardinal.{u}} (i : lvlOrder μ) (w : RetWell μ)
    (h : blockOf w ≠ i) :
    complementInclFun i (placePos i w h) = w := by
  by_cases hlt : blockOf w < i
  · rw [placePos, dite_eq_left hlt, complementInclFun_inl]
  · rw [placePos, dite_eq_right hlt, complementInclFun_inr]

/-- The complement of block `i`, as an order, is `L ⊕ₗ R`. -/
def complIso {μ : Cardinal.{u}} (i : lvlOrder μ) :
    ((LeftBlocks μ i) ⊕ₗ (RightBlocks μ i)) ≃o ↥(missedBlocks μ i) where
  toFun x := ⟨complementInclFun i x, complementInclFun_ne i x⟩
  invFun w := placePos i w.1 w.2
  left_inv x := (complementIncl i).injective <| by
    rw [complementIncl_apply, placePos_spec, complementIncl_apply]
  right_inv w := Subtype.ext (placePos_spec i w.1 w.2)
  map_rel_iff' := by
    intro a b
    simpa [complementIncl_apply, Subtype.mk_le_mk] using
      (complementIncl i).le_iff_le (a := a) (b := b)

theorem complementIncl_eq {μ : Cardinal.{u}} (i : lvlOrder μ) :
    complementIncl i =
      (complIso i).toOrderEmbedding.trans
        (OrderEmbedding.subtype (· ∈ missedBlocks μ i)) := by
  ext x
  rw [RelEmbedding.trans_apply, OrderIso.coe_toOrderEmbedding, OrderEmbedding.subtype_apply]
  rfl

theorem along_complement_restrict {lab : Type u} {arity : lab → ℕ}
    {μ : Cardinal.{u}} (i : lvlOrder μ)
    (t : SupportTerm lab arity (RetWell μ))
    (h : termSupport t ⊆ missedBlocks μ i) :
    SupportTerm.along (complementIncl i)
        (SupportTerm.along ((complIso i).symm.toOrderEmbedding)
          (t.restrict (missedBlocks μ i) h)) =
      t := by
  rw [SupportTerm.along_trans]
  have hembed :
      ((complIso i).symm.toOrderEmbedding).trans (complementIncl i) =
        OrderEmbedding.subtype (· ∈ missedBlocks μ i) := by
    ext z
    rw [RelEmbedding.trans_apply]
    rw [complementIncl_eq]
    rw [RelEmbedding.trans_apply]
    rw [OrderIso.coe_toOrderEmbedding]
    rw [OrderEmbedding.subtype_apply, OrderEmbedding.subtype_apply]
    exact congrArg Subtype.val ((complIso i).apply_symm_apply z)
  rw [hembed, SupportTerm.along_restrict]

/-! ## One retraction, then the family -/

theorem block_retract_exists (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ infra_615_closed P)
    (A B : SMObject K μ)
    (incl : Language.Embedding K.τ A.model.carrier B.model.carrier)
    (hincl : K.Strong incl)
    (ψ : (P.E.obj (RetWell μ)).carrier ≃[K.τ] A.model.carrier)
    (i : lvlOrder μ) (hi : i ≠ blockBot (P.aleph0_le hμ.1)) :
    ∃ r : Language.Embedding K.τ B.model.carrier A.model.carrier,
      K.Strong r ∧
      ∀ x : (P.E.obj (RetWell μ)).carrier,
        (∀ k, blockOf ((supportTermOf P.E x).pos k) ≠ i) →
          r (incl (ψ x)) = ψ x := by
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ.1
  haveI : Nonempty (LeftBlocks μ i) := leftBlocks_nonempty hμinf hi
  haveI : Nonempty (RightBlocks μ i) := rightBlocks_nonempty hμinf i
  haveI : Nonempty ((LeftBlocks μ i) ⊕ₗ (RightBlocks μ i)) :=
    ⟨Sum.inlₗ (Classical.arbitrary _)⟩
  haveI : Nonempty (MTop (L := LeftBlocks μ i) (R := RightBlocks μ i) μ) :=
    ⟨Sum.inlₗ (Classical.arbitrary _)⟩
  let embC := complementIncl (μ := μ) i
  let base := baseInto (L := LeftBlocks μ i) (R := RightBlocks μ i) μ
  let φe := (blockPhi (μ := μ) i).toOrderEmbedding
  let fBase : Language.Embedding K.τ
      (P.E.obj ((LeftBlocks μ i) ⊕ₗ (RightBlocks μ i))).carrier B.model.carrier :=
    incl.comp (ψ.toEmbedding.comp (P.E.map embC))
  have hfBase : K.Strong fBase :=
    K.strong_trans (ψ.toEmbedding.comp (P.E.map embC)) incl
      (K.strong_trans (P.E.map embC) ψ.toEmbedding
        (P.E.map_strong embC) (strong_of_equiv K ψ (P.hE (RetWell μ))))
      hincl
  obtain ⟨g, hg, hfix⟩ :=
    infra_615_middle_exhaust (L := LeftBlocks μ i) (R := RightBlocks μ i)
      P hμ (blocks_card hμinf i) fBase B.mem hfBase B.card
  let r : Language.Embedding K.τ B.model.carrier A.model.carrier :=
    ψ.toEmbedding.comp ((P.E.map φe).comp g)
  have hr : K.Strong r :=
    K.strong_trans ((P.E.map φe).comp g) ψ.toEmbedding
      (K.strong_trans g (P.E.map φe) hg (P.E.map_strong φe))
      (strong_of_equiv K ψ (P.hE (RetWell μ)))
  refine ⟨r, hr, fun x hmiss => ?_⟩
  let t := supportTermOf P.E x
  have hsub : termSupport t ⊆ missedBlocks μ i := by
    intro w hw
    rcases hw with ⟨k, rfl⟩
    exact hmiss k
  let tC := SupportTerm.along ((complIso i).symm.toOrderEmbedding)
    (t.restrict (missedBlocks μ i) hsub)
  have halong : SupportTerm.along embC tC = t :=
    along_complement_restrict i t hsub
  let y := P.E.realize tC
  have hmapy : P.E.map embC y = x := by
    rw [P.E.realize_along, halong, realize_supportTermOf]
  have hcoe : ∀ z, ψ.toEmbedding z = ψ z :=
    congrFun (FirstOrder.Language.Equiv.coe_toEmbedding ψ)
  have hfb : fBase y = incl (ψ x) := by
    simp only [fBase, Language.Embedding.comp_apply, hmapy, hcoe]
  have hφ : P.E.map φe (P.E.map base y) = x := by
    have hcomp := congrArg (fun e => e y) (P.E.map_comp base φe)
    rw [phi_baseInto (μ := μ) i] at hcomp
    have hcomp' : P.E.map φe (P.E.map base y) = P.E.map embC y := by
      simpa [Language.Embedding.comp_apply] using hcomp.symm
    rw [hcomp', hmapy]
  calc r (incl (ψ x))
      = ψ.toEmbedding (P.E.map φe (g (incl (ψ x)))) := by
        simp only [r, Language.Embedding.comp_apply]
    _ = ψ.toEmbedding (P.E.map φe (g (fBase y))) := by rw [hfb]
    _ = ψ.toEmbedding (P.E.map φe (P.E.map base y)) := by rw [hfix y]
    _ = ψ.toEmbedding x := by rw [hφ]
    _ = ψ x := hcoe x

/-- **Corollary 6.16** for one closed level: a `μ`-indexed family of strong arrows
`B → A`, each point of `A` moved only on the finitely many blocks that meet its support. -/
theorem corollary_6_16_family (P : SingleModelData K)
    {μ : Cardinal.{u}} (hμ : μ ∈ infra_615_closed P)
    (A B : P.scheme.Object μ hμ.1)
    (incl : SystemArrow K oneVertexShape
      (P.scheme.asSystem hμ.1 A) (P.scheme.asSystem hμ.1 B)) :
    Nonempty (ApproximateRetraction K oneVertexShape P.scheme hμ.1 A B incl) := by
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ.1
  let ψ : (P.E.obj (RetWell μ)).carrier ≃[K.τ] A.model.carrier :=
    Classical.choice
      (SingleModelData.exists_present_equiv hμ.1 A (RetWell μ) (retWell_card hμinf))
  let inclEmb := incl.onVertex PUnit.unit
  have hincl : K.Strong inclEmb := incl.onVertex_strong PUnit.unit
  let rfun : RetIndex hμinf →
      Language.Embedding K.τ B.model.carrier A.model.carrier :=
    fun i => Classical.choose
      (block_retract_exists P hμ A B inclEmb hincl ψ i.1 i.2)
  have rspec : ∀ i : RetIndex hμinf,
      K.Strong (rfun i) ∧
        ∀ x, (∀ k, blockOf ((supportTermOf P.E x).pos k) ≠ i.1) →
          rfun i (inclEmb (ψ x)) = ψ x :=
    fun i => Classical.choose_spec
      (block_retract_exists P hμ A B inclEmb hincl ψ i.1 i.2)
  refine ⟨{
    index := RetIndex hμinf
    index_card := retIndex_card hμinf
    retr := fun i =>
      oneVertexArrow (hM := B.mem) (hN := A.mem) (rfun i) (rspec i).1
    retr_arrow := fun _ => trivial
    almost_id := ?_
  }⟩
  intro a
  let x := ψ.symm a.2
  let t := supportTermOf P.E x
  have hfin : Finite {i : RetIndex hμinf // ∃ k, blockOf (t.pos k) = i.1} := by
    refine Finite.of_injective
      (fun j : {i : RetIndex hμinf // ∃ k, blockOf (t.pos k) = i.1} =>
        Classical.choose j.2) ?_
    intro j₁ j₂ hj
    have h1 := Classical.choose_spec j₁.2
    have h2 := Classical.choose_spec j₂.2
    have hch : Classical.choose j₁.2 = Classical.choose j₂.2 := hj
    apply Subtype.ext
    apply Subtype.ext
    calc j₁.1.1 = blockOf (t.pos (Classical.choose j₁.2)) := h1.symm
      _ = blockOf (t.pos (Classical.choose j₂.2)) :=
        congrArg (fun k => blockOf (t.pos k)) hch
      _ = j₂.1.1 := h2
  haveI : Finite {i : RetIndex hμinf // ∃ k, blockOf (t.pos k) = i.1} := hfin
  refine Finite.of_injective
    (fun s : {i : RetIndex hμinf // rfun i (incl.onVertex a.1 a.2) ≠ a.2} =>
      (⟨s.1, ?_⟩ : {i : RetIndex hμinf // ∃ k, blockOf (t.pos k) = i.1}))
    ?_
  · by_contra hmiss
    have hall : ∀ k, blockOf (t.pos k) ≠ s.1.1 := by
      intro k hk
      exact hmiss ⟨k, hk⟩
    have hfix := (rspec s.1).2 x hall
    have hx : ψ x = a.2 := ψ.apply_symm_apply a.2
    rw [hx] at hfix
    exact s.2 hfix
  · intro s₁ s₂ hs
    exact Subtype.ext <|
      congrArg
        (fun z : {i : RetIndex hμinf // ∃ k, blockOf (t.pos k) = i.1} => (z : RetIndex hμinf))
        hs

end
end
end AEC
