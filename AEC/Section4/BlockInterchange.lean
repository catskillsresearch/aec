module

public import AEC.Section4.NaturalDiagram
public import AEC.Section4.OrbitsOverParameters
public import AEC.Section1.UnboundedCategoricity
public import AEC.Section5.TermTemplate
public import Mathlib.Order.PiLex
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Order.Sum.Order
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

/-!
# Disjoint block interchange (Lemma 4.6), by the English orbit-counting argument

This file follows the proof of Lemma 4.6 in `text.md` §4.2.

* `LexTree`: the cardinal `χ = 2 ^ (ℓ + 2^(2^σ) + σ)` (so `χ ^ σ = χ` and
  `ℓ + 2^(2^σ) ≤ χ`), the least `ε` with `2 ^ ε > χ`, and the lexicographic order on
  sequences of digits `-1 < 0 < 1` of length `ε`. Branches of `2^ε` use the digits `±1`; the
  divider at a node `s ∈ 2^{<ε}` is `s` followed by `0`. There are at most `χ` nodes
  (dividers), more than `χ` branches, and two distinct branches are separated by a divider.
* `RepeatsAlong`: "the pair of blocks can be repeated along the linear order `L`": families
  `d i`, `e j` (`i j : L`) on one index order such that `(d i, e j)` is a copy of the original
  joint configuration for `i < j` and of the modified one for `j < i`.
* `sameNaturalDiagram_of_repeatsAlong`: the orbit argument. Repeat along the tree order, use
  the divider-indexed `e j` as at most `χ` parameters in a padded presentation of large
  categoricity size, and apply Lemma 4.5 (`lemma_4_5_with_E`): two of the more than `χ`
  branch-indexed `d i` lie in one orbit over the parameters, and a divider between the two
  branches then identifies the original and the modified joint natural diagrams. (The text
  argues by contradiction; the same steps give the conclusion directly.)
* `BlockRegions`: disjoint convex regions of the joint support order, each made of two
  adjacent blocks, one for each family, in either order. `BlockRegions.Interchange` is an
  order on the same positions with the two blocks of every region interchanged, and
  `BlockRegions.interchange` constructs one.
* `BlockRegions.Interchange.repeatsAlong`: the block-repetition construction, along `L` in
  the regions whose first-family block is on the left and along the reverse of `L` in the
  others.
* `lemma_4_6_blockInterchange`, `lemma_4_6_blockRegions`: Lemma 4.6.

## Why this is not stated for `DisjointBlockSwap`

`DisjointBlockSwap` asks for an order *automorphism* `swap : I ≃o I` with
`swap '' p.1 = p.2`, `swap '' p.2 = p.1` and `p.1 < p.2`. No order automorphism does that for
a nonempty block (`orderIso_swaps_blocks_empty`: `a ∈ p.1` gives `a < swap a` and
`swap (swap a) < swap a`). So every block of a `DisjointBlockSwap` is empty and its `swap` is
the identity: a statement about it has no block-interchange content, and there is nothing to
repeat. Interchanging two adjacent blocks preserves the order on the support of each family
separately but not on the joint support, so the modified configuration is modelled here by a
second linear order `I'` and a bijection `I ≃ I'` reversing exactly the pairs made of a
first-family and a second-family position of one region. `twoPointRegions` is the smallest
example with nonempty blocks.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

/-! ## The cardinal `χ` and the binary-tree order with dividers -/

namespace LexTree

/-- `χ = 2 ^ (ℓ + 2^(2^σ) + σ)`: "a sufficiently large power of two". -/
noncomputable def chi (ℓ σ : Cardinal.{u}) : Cardinal.{u} :=
  (2 : Cardinal.{u}) ^ (ℓ + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) + σ)

theorem sigma_le_exponent (ℓ σ : Cardinal.{u}) :
    σ ≤ ℓ + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) + σ :=
  le_add_self

theorem chi_pow (ℓ σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) : chi ℓ σ ^ σ = chi ℓ σ := by
  have hσ0 : σ ≠ 0 := (aleph0_pos.trans_le hσ).ne'
  rw [chi, ← power_mul,
    mul_eq_left (hσ.trans (sigma_le_exponent ℓ σ)) (sigma_le_exponent ℓ σ) hσ0]

theorem le_chi (ℓ σ : Cardinal.{u}) :
    ℓ + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ chi ℓ σ :=
  le_self_add.trans (cantor _).le

theorem sigma_le_chi (ℓ σ : Cardinal.{u}) : σ ≤ chi ℓ σ :=
  (sigma_le_exponent ℓ σ).trans (cantor _).le

theorem aleph0_le_chi (ℓ σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) : aleph0 ≤ chi ℓ σ :=
  hσ.trans (sigma_le_chi ℓ σ)

/-- The least cardinal `ε` with `2 ^ ε > χ`. -/
noncomputable def height (χ : Cardinal.{u}) : Cardinal.{u} :=
  sInf {ε : Cardinal.{u} | χ < (2 : Cardinal.{u}) ^ ε}

theorem lt_two_pow_height (χ : Cardinal.{u}) : χ < (2 : Cardinal.{u}) ^ height χ :=
  csInf_mem (s := {ε : Cardinal.{u} | χ < (2 : Cardinal.{u}) ^ ε}) ⟨χ, cantor χ⟩

theorem height_le (χ : Cardinal.{u}) : height χ ≤ χ :=
  csInf_le' (s := {ε : Cardinal.{u} | χ < (2 : Cardinal.{u}) ^ ε}) (cantor χ)

theorem two_pow_le_of_lt_height {χ ν : Cardinal.{u}} (h : ν < height χ) :
    (2 : Cardinal.{u}) ^ ν ≤ χ :=
  le_of_not_gt fun h' =>
    (csInf_le' (s := {ε : Cardinal.{u} | χ < (2 : Cardinal.{u}) ^ ε}) h').not_gt h

/-- Levels of the tree: the ordinals below `ε`. -/
abbrev Level (χ : Cardinal.{u}) : Type u := (height χ).ord.ToType

/-- Sequences of digits `-1 < 0 < 1` of length `ε`, ordered lexicographically. This is the
order `L` of the proof. -/
abbrev Point (χ : Cardinal.{u}) : Type u := Lex (Level χ → SignType)

/-- Branch digits are encoded by `-1` and `1`. -/
def digit (b : Bool) : SignType := if b then 1 else -1

theorem digit_injective : Function.Injective digit := by
  intro a b h
  cases a <;> cases b <;> simp [digit] at h ⊢

theorem digit_false_lt_zero : digit false < 0 := by decide

theorem zero_lt_digit_true : 0 < digit true := by decide

/-- The point of a branch in `2^ε`. -/
def branch {χ : Cardinal.{u}} (b : Level χ → Bool) : Point χ :=
  toLex fun a => digit (b a)

/-- Nodes of the binary tree `2^{<ε}`. -/
abbrev Node (χ : Cardinal.{u}) : Type u := Σ a : Level χ, (Set.Iio a → Bool)

/-- The divider at a node `s`: the sequence `s` followed by `0`. -/
noncomputable def divider {χ : Cardinal.{u}} (n : Node χ) : Point χ :=
  toLex fun c => if h : c < n.1 then digit (n.2 ⟨c, h⟩) else 0

theorem branch_injective {χ : Cardinal.{u}} : Function.Injective (branch (χ := χ)) := by
  intro b b' h
  funext a
  exact digit_injective (congrFun (congrArg ofLex h) a)

/-- There are more than `χ` branches. -/
theorem lt_mk_branches (χ : Cardinal.{u}) : χ < #(Level χ → Bool) := by
  have h : #(Level χ → Bool) = (2 : Cardinal.{u}) ^ height χ := by
    rw [mk_arrow, mk_bool, mk_ord_toType]; simp
  rw [h]
  exact lt_two_pow_height χ

/-- The binary tree `2^{<ε}` has at most `χ` nodes, hence there are at most `χ` dividers. -/
theorem mk_node_le {χ : Cardinal.{u}} (hχ : aleph0 ≤ χ) : #(Node χ) ≤ χ := by
  rw [mk_sigma]
  have hlevel : ∀ a : Level χ, #(Set.Iio a → Bool) ≤ χ := by
    intro a
    have hlt : #(Set.Iio a) < height χ := by simpa using mk_Iio_lt a
    have h : #(Set.Iio a → Bool) = (2 : Cardinal.{u}) ^ #(Set.Iio a) := by
      rw [mk_arrow, mk_bool]; simp
    rw [h]
    exact two_pow_le_of_lt_height hlt
  calc sum (fun a : Level χ => #(Set.Iio a → Bool))
      ≤ sum (fun _ : Level χ => χ) := sum_le_sum _ _ hlevel
    _ = #(Level χ) * χ := sum_const' _ _
    _ ≤ χ * χ := mul_le_mul' (by rw [mk_ord_toType]; exact height_le χ) le_rfl
    _ = χ := mul_eq_self hχ

/-- Distinct branch points determine distinct strict cuts over the divider points: some
divider lies strictly between them. -/
theorem exists_divider_between {χ : Cardinal.{u}} {b b' : Level χ → Bool} (hne : b ≠ b') :
    ∃ n : Node χ,
      (branch b < divider n ∧ divider n < branch b') ∨
      (branch b' < divider n ∧ divider n < branch b) := by
  classical
  have hex : ∃ a, b a ≠ b' a := Function.ne_iff.mp hne
  let S : Set (Level χ) := {a | b a ≠ b' a}
  let a : Level χ := wellFounded_lt.min S hex
  have ha : b a ≠ b' a := wellFounded_lt.min_mem S hex
  have hmin : ∀ c, c < a → b c = b' c := by
    intro c hc
    by_contra h
    exact wellFounded_lt.not_lt_min S (x := c) h hc
  -- the node `b ↾ a = b' ↾ a`
  let n : Node χ := ⟨a, fun c => b c.1⟩
  have key : ∀ (x y : Level χ → Bool), (∀ c, c < a → x c = b c) → (∀ c, c < a → y c = b c) →
      x a = false → y a = true → branch x < divider n ∧ divider n < branch y := by
    intro x y hx hy hxa hya
    constructor
    · refine ⟨a, fun c hc => ?_, ?_⟩
      · simp [branch, divider, n, hc, hx c hc]
      · simpa [branch, divider, n, hxa] using digit_false_lt_zero
    · refine ⟨a, fun c hc => ?_, ?_⟩
      · simp [branch, divider, n, hc, hy c hc]
      · simpa [branch, divider, n, hya] using zero_lt_digit_true
  refine ⟨n, ?_⟩
  cases hba : b a with
  | false =>
    have hb'a : b' a = true := by
      cases h : b' a with
      | false => exact absurd (hba.trans h.symm) ha
      | true => rfl
    exact Or.inl (key b b' (fun _ _ => rfl) (fun c hc => (hmin c hc).symm) hba hb'a)
  | true =>
    have hb'a : b' a = false := by
      cases h : b' a with
      | false => rfl
      | true => exact absurd (hba.trans h.symm) ha
    exact Or.inr (key b' b (fun c hc => (hmin c hc).symm) (fun _ _ => rfl) hb'a hba)

end LexTree

/-! ## Repetition along a linear order, and the orbit argument -/

/-- The joint configuration `(t, s)` over `I`, with modified configuration `(t', s')` over
`I'`, *repeats along* the linear order `L`: on one index order `J` there are first-family
lists `d i` and second-family lists `e j` (`i j : L`) such that `(d i, e j)` is a copy of the
original configuration when `i < j`, and a copy of the modified one when `j < i`. A copy is
the image under an order embedding of the whole index order. -/
def RepeatsAlong {lab : Type u} {arity : lab → ℕ} {I I' : Type u}
    [LinearOrder I] [LinearOrder I'] {α β : Type u}
    (t : α → SupportTerm lab arity I) (s : β → SupportTerm lab arity I)
    (t' : α → SupportTerm lab arity I') (s' : β → SupportTerm lab arity I')
    (L : Type u) [LinearOrder L] : Prop :=
  ∃ (J : Type u) (_ : LinearOrder J) (d : L → α → SupportTerm lab arity J)
    (e : L → β → SupportTerm lab arity J),
    (∀ i j, i < j → ∃ φ : I ↪o J,
      (∀ a, SupportTerm.along φ (t a) = d i a) ∧ ∀ b, SupportTerm.along φ (s b) = e j b) ∧
    (∀ i j, j < i → ∃ φ : I' ↪o J,
      (∀ a, SupportTerm.along φ (t' a) = d i a) ∧ ∀ b, SupportTerm.along φ (s' b) = e j b)

/-- Cardinality of an index order padded on the right by `Below κ`. -/
theorem mk_sumLex_below {J : Type u} {κ : Cardinal.{u}} (hκ : aleph0 ≤ κ) (hJ : #J ≤ κ) :
    #(J ⊕ₗ Below κ) = κ := by
  have h : #(J ⊕ₗ Below κ) = #(J ⊕ Below κ) := mk_congr ofLex
  rw [h, mk_sum, lift_id, lift_id, mk_ord_toType]
  exact add_eq_right hκ hJ

/-- **The orbit argument of Lemma 4.6.** If the block pairs of a joint configuration can be
repeated along the binary-tree order with dividers, then the original and the modified
configuration have the same joint natural diagram.

The divider-indexed second-family tuples are at most `χ` parameters in a padded presentation
of categoricity size. By Lemma 4.5 the more than `χ` branch-indexed first-family tuples
cannot lie in pairwise distinct orbits over them, and an automorphism fixing the parameters
and moving one branch tuple to another carries the configuration at a divider between the
two branches from the original pattern to the modified one. -/
theorem sameNaturalDiagram_of_repeatsAlong (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (D : StableDiagram K)
    {I I' : Type u} [LinearOrder I] [LinearOrder I'] [Nonempty I] [Nonempty I']
    {α β : Type u} (σ : Cardinal.{u}) (hjoint : #(α ⊕ β) ≤ σ) (hσ : aleph0 ≤ σ)
    (t : α → SupportTerm E.lab E.arity I) (s : β → SupportTerm E.lab E.arity I)
    (t' : α → SupportTerm E.lab E.arity I') (s' : β → SupportTerm E.lab E.arity I')
    (hrep : RepeatsAlong t s t' s' (LexTree.Point (LexTree.chi (ls K) σ))) :
    SameNaturalDiagram K E D σ hjoint (Sum.elim t s) (Sum.elim t' s') := by
  classical
  -- the cardinal `χ`
  set χ : Cardinal.{u} := LexTree.chi (ls K) σ with hχdef
  have hpow : χ ^ σ = χ := LexTree.chi_pow (ls K) σ hσ
  have hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ := LexTree.le_chi (ls K) σ
  have hχinf : aleph0 ≤ χ := LexTree.aleph0_le_chi (ls K) σ hσ
  have hσχ : σ ≤ χ := LexTree.sigma_le_chi (ls K) σ
  have hα : #α ≤ σ := (mk_le_of_injective Sum.inl_injective).trans hjoint
  have hβ : #β ≤ σ := (mk_le_of_injective Sum.inr_injective).trans hjoint
  -- the repeated blocks along the tree order
  obtain ⟨J, linJ, d, e, hlt, hgt⟩ := hrep
  -- pad to a large categoricity size
  obtain ⟨κ0, h45⟩ := lemma_4_5_with_E K E σ χ hσ hpow hχ
  obtain ⟨κ, hκ, hcat⟩ :=
    CategoricalUnbounded.unbounded (K := K) (κ0 ⊔ D.t σ ⊔ #J ⊔ ls K ⊔ aleph0)
  have hκinf : aleph0 ≤ κ := le_sup_right.trans hκ
  have hκls : ls K ≤ κ := (le_sup_right.trans le_sup_left).trans hκ
  have hκJ : #J ≤ κ := ((le_sup_right.trans le_sup_left).trans le_sup_left).trans hκ
  have hκt : D.t σ ≤ κ :=
    (((le_sup_right.trans le_sup_left).trans le_sup_left).trans le_sup_left).trans hκ
  have hκ0 : κ0 ≤ κ :=
    (((le_sup_left.trans le_sup_left).trans le_sup_left).trans le_sup_left).trans hκ
  have : Nonempty (Below κ) :=
    mk_ne_zero_iff.mp (by rw [mk_ord_toType]; exact (aleph0_pos.trans_le hκinf).ne')
  have hM : K.Mem (E.obj (J ⊕ₗ Below κ)) := orderPresentation_obj_mem E _
  have hMcard : Model.card (E.obj (J ⊕ₗ Below κ)) = κ :=
    orderPresentation_obj_card E (mk_sumLex_below hκinf hκJ) hκls hκinf
  have hcard : D.t σ ≤ Model.card (E.obj (J ⊕ₗ Below κ)) := hκt.trans hMcard.ge
  let pad : J ↪o J ⊕ₗ Below κ := sumLexEmbedLeftIncl J (Below κ)
  -- the divider tuples are at most `χ` parameters
  let par : LexTree.Node χ × β → (E.obj (J ⊕ₗ Below κ)).carrier := fun q =>
    E.realize (SupportTerm.along pad (e (LexTree.divider q.1) q.2))
  have hP : #(Set.range par) ≤ χ := by
    refine mk_range_le.trans ?_
    rw [mk_prod, lift_id, lift_id]
    exact (mul_le_mul' (LexTree.mk_node_le hχinf) (hβ.trans hσχ)).trans (mul_eq_self hχinf).le
  -- the branch tuples
  let xs : (LexTree.Level χ → Bool) → α → (E.obj (J ⊕ₗ Below κ)).carrier := fun b a =>
    E.realize (SupportTerm.along pad (d (LexTree.branch b) a))
  -- a divider between two branch tuples in one orbit identifies the two diagrams
  have core : ∀ (i i' : LexTree.Point χ) (n : LexTree.Node χ),
      i < LexTree.divider n → LexTree.divider n < i' →
      ∀ ψ : (E.obj (J ⊕ₗ Below κ)).carrier ≃[K.τ] (E.obj (J ⊕ₗ Below κ)).carrier,
        (∀ p ∈ Set.range par, ψ p = p) →
        (∀ a, ψ (E.realize (SupportTerm.along pad (d i a))) =
          E.realize (SupportTerm.along pad (d i' a))) →
        SameNaturalDiagram K E D σ hjoint (Sum.elim t s) (Sum.elim t' s') := by
    intro i i' n hin hni' ψ hψP hψ
    obtain ⟨φ, hφt, hφs⟩ := hlt i (LexTree.divider n) hin
    obtain ⟨φ', hφ't, hφ's⟩ := hgt i' (LexTree.divider n) hni'
    refine sameNaturalDiagram_along E D _ _ (φ.trans pad) (φ'.trans pad) hcard hM ?_
    refine D.of_strong hjoint hM hM hcard hcard _ _ ψ.toEmbedding hσ
      (strong_of_equiv K ψ hM) ?_
    rintro (a | b)
    · change ψ (E.realize (SupportTerm.along pad (SupportTerm.along φ (t a)))) =
        E.realize (SupportTerm.along pad (SupportTerm.along φ' (t' a)))
      rw [hφt, hφ't]
      exact hψ a
    · change ψ (E.realize (SupportTerm.along pad (SupportTerm.along φ (s b)))) =
        E.realize (SupportTerm.along pad (SupportTerm.along φ' (s' b)))
      rw [hφs, hφ's]
      exact hψP _ ⟨(n, b), rfl⟩
  -- Lemma 4.5: at most `χ` orbits of `α`-tuples over the parameters
  obtain ⟨reps, hreps, horb⟩ :=
    h45 κ hκ0 hcat (E.obj (J ⊕ₗ Below κ)) hM hMcard (Set.range par) hP (ι := α) hα
  choose F hFmem hF using fun b => horb (xs b)
  -- more than `χ` branches: two of them have the same orbit representative
  obtain ⟨b, b', hne, hFbb'⟩ : ∃ b b', b ≠ b' ∧ F b = F b' := by
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (fun b => (⟨F b, hFmem b⟩ : reps)) := by
      intro b b' h
      by_contra hbb'
      exact hcon b b' hbb' (congrArg Subtype.val h)
    exact absurd ((mk_le_of_injective hinj).trans hreps) (not_le.mpr (LexTree.lt_mk_branches χ))
  obtain ⟨e₁, -, he₁P, he₁⟩ := hF b
  obtain ⟨e₂, -, he₂P, he₂⟩ := hF b'
  obtain ⟨n, hn | hn⟩ := LexTree.exists_divider_between hne
  · refine core _ _ n hn.1 hn.2 (e₂.symm.comp e₁) (fun p hp => ?_) (fun a => ?_)
    · change e₂.symm (e₁ p) = p
      rw [he₁P p hp]
      exact e₂.symm_apply_eq.mpr (he₂P p hp).symm
    · change e₂.symm (e₁ (xs b a)) = xs b' a
      rw [he₁ a, hFbb', ← he₂ a]
      exact e₂.symm_apply_apply _
  · refine core _ _ n hn.1 hn.2 (e₁.symm.comp e₂) (fun p hp => ?_) (fun a => ?_)
    · change e₁.symm (e₂ p) = p
      rw [he₂P p hp]
      exact e₁.symm_apply_eq.mpr (he₁P p hp).symm
    · change e₁.symm (e₂ (xs b' a)) = xs b a
      rw [he₂ a, ← hFbb', ← he₁ a]
      exact e₁.symm_apply_apply _

/-! ## Block interchange and the repetition of blocks -/

/-- No order automorphism interchanges two nonempty blocks one of which lies entirely before
the other. (This is why the interchange below is a bijection onto a *second* linear order and
not an order automorphism of the index.) -/
theorem orderIso_swaps_blocks_empty {I : Type u} [LinearOrder I] (f : I ≃o I) {P Q : Set I}
    (hlt : ∀ a ∈ P, ∀ b ∈ Q, a < b) (hPQ : f '' P = Q) (hQP : f '' Q = P) :
    P = ∅ ∧ Q = ∅ := by
  have hP : P = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun a ha => ?_
    have hfa : f a ∈ Q := hPQ ▸ Set.mem_image_of_mem _ ha
    have hffa : f (f a) ∈ P := hQP ▸ Set.mem_image_of_mem _ hfa
    have h1 : a < f a := hlt a ha _ hfa
    have h2 : f (f a) < f a := hlt _ hffa _ hfa
    exact absurd (f.lt_iff_lt.mp h2) (not_lt.mpr h1.le)
  refine ⟨hP, ?_⟩
  rw [← hPQ, hP, Set.image_empty]

/-- **Disjoint convex regions made of two adjacent blocks.**

`key` is a monotone map to a linear order `Region`; the regions are its fibres that meet
`first ∪ second`, so they are disjoint and convex, and the remaining positions lie outside
the regions. A region consists of two adjacent blocks: its positions in `first` (the block
used only by the first family) and its positions in `second` (the block used only by the
second family). In the regions of `firstOnRight` the first family's block is the right one;
in all other regions it is the left one. -/
structure BlockRegions (I : Type u) [LinearOrder I] where
  /-- The linear order that `key` maps to. -/
  Region : Type u
  [regionOrder : LinearOrder Region]
  /-- Two positions of `first ∪ second` are in the same region when they have the same key. -/
  key : I → Region
  key_mono : Monotone key
  /-- Positions in the blocks used only by the first family. -/
  first : Set I
  /-- Positions in the blocks used only by the second family. -/
  second : Set I
  /-- The regions whose first-family block is the right one. -/
  firstOnRight : Set Region
  /-- In each region one block lies entirely before the other. -/
  blocks_ordered : ∀ x ∈ first, ∀ y ∈ second, key x = key y →
    (key x ∈ firstOnRight → y < x) ∧ (key x ∉ firstOnRight → x < y)
  /-- A region consists of its two blocks. -/
  region_blocks : ∀ x y, key x = key y → x ∈ first ∪ second → y ∈ first ∪ second

attribute [instance] BlockRegions.regionOrder

namespace BlockRegions

variable {I : Type u} [LinearOrder I] (R : BlockRegions I)

/-- Two positions are *crossed* when they lie in the two different blocks of one region. -/
def Crossed (x y : I) : Prop :=
  R.key x = R.key y ∧ (x ∈ R.first ∧ y ∈ R.second ∨ x ∈ R.second ∧ y ∈ R.first)

/-- **The interchange of the two blocks in every region.** `I'` carries the same positions
(via `toEquiv`), and its order differs from that of `I` exactly by reversing every crossed
pair. So the internal orders of the blocks and all positions outside the regions are
retained. -/
structure Interchange (R : BlockRegions I) (I' : Type u) [LinearOrder I'] where
  /-- The position of a point after the interchange. -/
  toEquiv : I ≃ I'
  lt_iff_of_crossed : ∀ x y, R.Crossed x y → (toEquiv x < toEquiv y ↔ y < x)
  lt_iff_of_not_crossed : ∀ x y, ¬R.Crossed x y → (toEquiv x < toEquiv y ↔ x < y)

theorem not_first_and_second (x : I) : ¬(x ∈ R.first ∧ x ∈ R.second) := by
  rintro ⟨h1, h2⟩
  have h := R.blocks_ordered x h1 x h2 rfl
  by_cases hf : R.key x ∈ R.firstOnRight
  · exact lt_irrefl _ (h.1 hf)
  · exact lt_irrefl _ (h.2 hf)

section Placement

variable {L : Type u} [LinearOrder L]

/-- The index order in which every region is replaced by copies of its pair of blocks, one
copy for each element of `L`: ordered along `L` in the regions whose first-family block is on
the left, and along the reverse of `L` in the others. Positions outside the regions sit at
`⊥`. -/
abbrev Rep (R : BlockRegions I) (L : Type u) [LinearOrder L] : Type u :=
  R.Region ×ₗ (WithBot L ×ₗ (WithBot Lᵒᵈ ×ₗ I))

open Classical in
/-- The copy used by a position when the first family uses the blocks at index `i` and the
second family those at index `j`. -/
noncomputable def copy (i j : L) (x : I) : WithBot L :=
  if x ∈ R.first then (i : WithBot L) else if x ∈ R.second then (j : WithBot L) else ⊥

open Classical in
/-- Place the positions in the repeated order: `first` positions in copy `i`, `second`
positions in copy `j`. -/
noncomputable def place (i j : L) (x : I) : R.Rep L :=
  if R.key x ∈ R.firstOnRight then
    toLex (R.key x, toLex (⊥, toLex ((R.copy i j x).map OrderDual.toDual, x)))
  else toLex (R.key x, toLex (R.copy i j x, toLex (⊥, x)))

omit [LinearOrder L] in
theorem copy_first (i j : L) {x : I} (hx : x ∈ R.first) : R.copy i j x = i :=
  ite_eq_left hx

omit [LinearOrder L] in
theorem copy_second (i j : L) {x : I} (hx : x ∈ R.second) : R.copy i j x = j := by
  rw [copy, ite_eq_right fun h => R.not_first_and_second x ⟨h, hx⟩, ite_eq_left hx]

omit [LinearOrder L] in
theorem copy_neutral (i j : L) {x : I} (h1 : x ∉ R.first) (h2 : x ∉ R.second) :
    R.copy i j x = ⊥ := by
  rw [copy, ite_eq_right h1, ite_eq_right h2]

theorem place_eq_of_notMem_second (i j : L) {x : I} (hx : x ∉ R.second) :
    R.place i j x = R.place i i x := by
  simp [place, copy, hx]

theorem place_eq_of_notMem_first (i j : L) {x : I} (hx : x ∉ R.first) :
    R.place i j x = R.place j j x := by
  simp [place, copy, hx]

theorem place_lt_of_key_lt (i j : L) {x y : I} (h : R.key x < R.key y) :
    R.place i j x < R.place i j y := by
  unfold place
  split_ifs <;> exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

theorem place_lt_of_copy_eq (i j : L) {x y : I} (hk : R.key x = R.key y)
    (hc : R.copy i j x = R.copy i j y) (hxy : x < y) : R.place i j x < R.place i j y := by
  unfold place
  rw [hc, hk]
  split_ifs
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hxy⟩)⟩)⟩)
  · exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr
      (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨rfl, hxy⟩)⟩)⟩)

/-- In a region whose first-family block is on the left, copies are ordered along `L`. -/
theorem place_lt_of_copy_lt (i j : L) {x y : I} (hk : R.key x = R.key y)
    (hf : R.key x ∉ R.firstOnRight) (hc : R.copy i j x < R.copy i j y) :
    R.place i j x < R.place i j y := by
  have hf' : R.key y ∉ R.firstOnRight := hk ▸ hf
  rw [place, place, ite_eq_right hf, ite_eq_right hf']
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hk, Prod.Lex.toLex_lt_toLex.mpr (Or.inl hc)⟩)

/-- In a region whose first-family block is on the right, copies are ordered along the
reverse of `L`. -/
theorem place_lt_of_copy_gt (i j : L) {x y : I} {a b : L} (hk : R.key x = R.key y)
    (hf : R.key x ∈ R.firstOnRight) (hx : R.copy i j x = a) (hy : R.copy i j y = b)
    (hab : b < a) : R.place i j x < R.place i j y := by
  have hf' : R.key y ∈ R.firstOnRight := hk ▸ hf
  rw [place, place, ite_eq_left hf, ite_eq_left hf', hx, hy]
  refine Prod.Lex.toLex_lt_toLex.mpr (Or.inr ⟨hk, Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, Prod.Lex.toLex_lt_toLex.mpr (Or.inl ?_)⟩)⟩)
  simpa using hab

/-- For `i ≤ j` the placement is a copy of the original order: the first family's blocks at
index `i` and the second family's at index `j` are in their original relative position. -/
theorem place_strictMono {i j : L} (hij : i ≤ j) : StrictMono (R.place i j) := by
  intro x y hxy
  rcases (R.key_mono hxy.le).lt_or_eq with hk | hk
  · exact R.place_lt_of_key_lt i j hk
  by_cases hx1 : x ∈ R.first
  · by_cases hy1 : y ∈ R.first
    · exact R.place_lt_of_copy_eq i j hk (by rw [R.copy_first i j hx1, R.copy_first i j hy1]) hxy
    · have hy2 : y ∈ R.second := (R.region_blocks x y hk (Or.inl hx1)).resolve_left hy1
      have hord := R.blocks_ordered x hx1 y hy2 hk
      by_cases hf : R.key x ∈ R.firstOnRight
      · exact absurd (hord.1 hf) (not_lt.mpr hxy.le)
      · rcases hij.lt_or_eq with h | h
        · exact R.place_lt_of_copy_lt i j hk hf (by
            rw [R.copy_first i j hx1, R.copy_second i j hy2]
            exact WithBot.coe_lt_coe.mpr h)
        · exact R.place_lt_of_copy_eq i j hk (by
            rw [R.copy_first i j hx1, R.copy_second i j hy2, h]) hxy
  · by_cases hx2 : x ∈ R.second
    · by_cases hy1 : y ∈ R.first
      · have hord := R.blocks_ordered y hy1 x hx2 hk.symm
        by_cases hf : R.key x ∈ R.firstOnRight
        · rcases hij.lt_or_eq with h | h
          · exact R.place_lt_of_copy_gt i j hk hf (R.copy_second i j hx2)
              (R.copy_first i j hy1) h
          · exact R.place_lt_of_copy_eq i j hk (by
              rw [R.copy_second i j hx2, R.copy_first i j hy1, h]) hxy
        · exact absurd (hord.2 (hk ▸ hf)) (not_lt.mpr hxy.le)
      · have hy2 : y ∈ R.second := (R.region_blocks x y hk (Or.inr hx2)).resolve_left hy1
        exact R.place_lt_of_copy_eq i j hk (by
          rw [R.copy_second i j hx2, R.copy_second i j hy2]) hxy
    · have hy1 : y ∉ R.first := fun h =>
        (R.region_blocks y x hk.symm (Or.inl h)).elim hx1 hx2
      have hy2 : y ∉ R.second := fun h =>
        (R.region_blocks y x hk.symm (Or.inr h)).elim hx1 hx2
      exact R.place_lt_of_copy_eq i j hk (by
        rw [R.copy_neutral i j hx1 hx2, R.copy_neutral i j hy1 hy2]) hxy

end Placement

namespace Interchange

variable {R} {I' : Type u} [LinearOrder I'] (T : R.Interchange I')

/-- A term using no `second` position, or no `first` position, still has increasing positions
after the interchange. -/
theorem strictMono_toEquiv_comp {n : ℕ} {pos : Fin n → I} (hpos : StrictMono pos)
    (h : (∀ k, pos k ∉ R.second) ∨ (∀ k, pos k ∉ R.first)) :
    StrictMono (T.toEquiv ∘ pos) := by
  intro a b hab
  have hnc : ¬R.Crossed (pos a) (pos b) := by
    rintro ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · rcases h with h | h
      · exact h b h2
      · exact h a h1
    · rcases h with h | h
      · exact h a h1
      · exact h b h2
  exact (T.lt_iff_of_not_crossed _ _ hnc).mpr (hpos hab)

/-- The term after the interchange: same label, positions moved by `toEquiv`. -/
def move {lab : Type u} {arity : lab → ℕ} (t : SupportTerm lab arity I)
    (h : (∀ k, t.pos k ∉ R.second) ∨ (∀ k, t.pos k ∉ R.first)) : SupportTerm lab arity I' where
  label := t.label
  pos := T.toEquiv ∘ t.pos
  increasing := T.strictMono_toEquiv_comp t.increasing h

/-- For `j < i` the placement is a copy of the interchanged order: the first family's blocks
at index `i` and the second family's at index `j` are in the opposite relative position. -/
theorem place_symm_strictMono {L : Type u} [LinearOrder L] {i j : L} (hji : j < i) :
    StrictMono fun z : I' => R.place i j (T.toEquiv.symm z) := by
  intro z w hzw
  obtain ⟨x, rfl⟩ := T.toEquiv.surjective z
  obtain ⟨y, rfl⟩ := T.toEquiv.surjective w
  simp only [Equiv.symm_apply_apply]
  by_cases hc : R.Crossed x y
  · have hyx : y < x := (T.lt_iff_of_crossed x y hc).mp hzw
    obtain ⟨hk, hc | hc⟩ := hc
    · have hord := R.blocks_ordered x hc.1 y hc.2 hk
      by_cases hf : R.key x ∈ R.firstOnRight
      · exact R.place_lt_of_copy_gt i j hk hf (R.copy_first i j hc.1)
          (R.copy_second i j hc.2) hji
      · exact absurd (hord.2 hf) (not_lt.mpr hyx.le)
    · have hord := R.blocks_ordered y hc.2 x hc.1 hk.symm
      by_cases hf : R.key x ∈ R.firstOnRight
      · exact absurd (hord.1 (hk ▸ hf)) (not_lt.mpr hyx.le)
      · exact R.place_lt_of_copy_lt i j hk hf (by
          rw [R.copy_second i j hc.1, R.copy_first i j hc.2]
          exact WithBot.coe_lt_coe.mpr hji)
  · have hxy : x < y := (T.lt_iff_of_not_crossed x y hc).mp hzw
    rcases (R.key_mono hxy.le).lt_or_eq with hk | hk
    · exact R.place_lt_of_key_lt i j hk
    have hc' : ¬(x ∈ R.first ∧ y ∈ R.second ∨ x ∈ R.second ∧ y ∈ R.first) :=
      fun h => hc ⟨hk, h⟩
    refine R.place_lt_of_copy_eq i j hk ?_ hxy
    by_cases hx1 : x ∈ R.first
    · have hy1 : y ∈ R.first := by
        rcases R.region_blocks x y hk (Or.inl hx1) with h | h
        · exact h
        · exact absurd (Or.inl ⟨hx1, h⟩) hc'
      rw [R.copy_first i j hx1, R.copy_first i j hy1]
    · by_cases hx2 : x ∈ R.second
      · have hy2 : y ∈ R.second := by
          rcases R.region_blocks x y hk (Or.inr hx2) with h | h
          · exact absurd (Or.inr ⟨hx2, h⟩) hc'
          · exact h
        rw [R.copy_second i j hx2, R.copy_second i j hy2]
      · have hy1 : y ∉ R.first := fun h =>
          (R.region_blocks y x hk.symm (Or.inl h)).elim hx1 hx2
        have hy2 : y ∉ R.second := fun h =>
          (R.region_blocks y x hk.symm (Or.inr h)).elim hx1 hx2
        rw [R.copy_neutral i j hx1 hx2, R.copy_neutral i j hy1 hy2]

/-- **Block repetition.** Repeat the pair of blocks of every region along an arbitrary linear
order `L` (along the reverse of `L` where the first family's block is on the right). Let
`d i` be the first family using the blocks at index `i` and `e j` the second family using
those at index `j`. For `i < j` the pair `(d i, e j)` is a copy of the original configuration,
and for `j < i` a copy of the interchanged one. -/
theorem repeatsAlong {lab : Type u} {arity : lab → ℕ} {α β : Type u}
    (t : α → SupportTerm lab arity I) (s : β → SupportTerm lab arity I)
    (ht : ∀ a k, (t a).pos k ∉ R.second) (hs : ∀ b k, (s b).pos k ∉ R.first)
    (L : Type u) [LinearOrder L] :
    RepeatsAlong t s (fun a => T.move (t a) (Or.inl (ht a)))
      (fun b => T.move (s b) (Or.inr (hs b))) L := by
  refine ⟨R.Rep L, inferInstance,
    fun i a => SupportTerm.along
      (OrderEmbedding.ofStrictMono (R.place i i) (R.place_strictMono le_rfl)) (t a),
    fun j b => SupportTerm.along
      (OrderEmbedding.ofStrictMono (R.place j j) (R.place_strictMono le_rfl)) (s b), ?_, ?_⟩
  · intro i j hij
    refine ⟨OrderEmbedding.ofStrictMono (R.place i j) (R.place_strictMono hij.le),
      fun a => ?_, fun b => ?_⟩
    · refine SupportTerm.ext_of_label_eq rfl fun k => ?_
      exact R.place_eq_of_notMem_second i j (ht a k)
    · refine SupportTerm.ext_of_label_eq rfl fun k => ?_
      exact R.place_eq_of_notMem_first i j (hs b k)
  · intro i j hji
    refine ⟨OrderEmbedding.ofStrictMono _ (T.place_symm_strictMono hji),
      fun a => ?_, fun b => ?_⟩
    · refine SupportTerm.ext_of_label_eq rfl fun k => ?_
      change R.place i j (T.toEquiv.symm (T.toEquiv ((t a).pos k))) = R.place i i ((t a).pos k)
      rw [Equiv.symm_apply_apply]
      exact R.place_eq_of_notMem_second i j (ht a k)
    · refine SupportTerm.ext_of_label_eq rfl fun k => ?_
      change R.place i j (T.toEquiv.symm (T.toEquiv ((s b).pos k))) = R.place j j ((s b).pos k)
      rw [Equiv.symm_apply_apply]
      exact R.place_eq_of_notMem_first i j (hs b k)

end Interchange

/-! ### The interchanged order exists -/

/-- The positions of `I`, to be ordered with the two blocks of every region interchanged. -/
def Interchanged (_R : BlockRegions I) : Type u := I

instance [h : Nonempty I] : Nonempty R.Interchanged := h

open Classical in
/-- After the interchange, the block that was on the right comes first in its region. -/
noncomputable def rank (x : I) : Bool :=
  if x ∈ R.first then (if R.key x ∈ R.firstOnRight then false else true)
  else if x ∈ R.second then (if R.key x ∈ R.firstOnRight then true else false) else false

/-- Regions in their old order; inside a region the old right block, then the old left
block; inside a block the old order. -/
noncomputable def interchangeCode (x : I) : R.Region ×ₗ (Bool ×ₗ I) :=
  toLex (R.key x, toLex (R.rank x, x))

theorem interchangeCode_injective : Function.Injective R.interchangeCode := fun _ _ h =>
  congrArg (fun p : R.Region ×ₗ (Bool ×ₗ I) => (ofLex (ofLex p).2).2) h

noncomputable instance : LinearOrder R.Interchanged :=
  LinearOrder.lift' (β := R.Region ×ₗ (Bool ×ₗ I)) R.interchangeCode R.interchangeCode_injective

open Classical in
theorem rank_first {x : I} (hx : x ∈ R.first) :
    R.rank x = if R.key x ∈ R.firstOnRight then false else true :=
  ite_eq_left hx

open Classical in
theorem rank_second {x : I} (hx : x ∈ R.second) :
    R.rank x = if R.key x ∈ R.firstOnRight then true else false := by
  rw [rank, ite_eq_right fun h => R.not_first_and_second x ⟨h, hx⟩, ite_eq_left hx]

theorem rank_neutral {x : I} (h1 : x ∉ R.first) (h2 : x ∉ R.second) : R.rank x = false := by
  rw [rank, ite_eq_right h1, ite_eq_right h2]

theorem interchangeCode_lt_iff (x y : I) :
    R.interchangeCode x < R.interchangeCode y ↔
      R.key x < R.key y ∨
        R.key x = R.key y ∧ (R.rank x < R.rank y ∨ R.rank x = R.rank y ∧ x < y) := by
  simp [interchangeCode, Prod.Lex.toLex_lt_toLex]

/-- The canonical interchange: the same positions with the two blocks of every region
interchanged. -/
noncomputable def interchange : R.Interchange R.Interchanged where
  toEquiv := Equiv.refl I
  lt_iff_of_crossed x y hc := by
    change R.interchangeCode x < R.interchangeCode y ↔ y < x
    rw [R.interchangeCode_lt_iff]
    obtain ⟨hk, hc | hc⟩ := hc
    · have hord := R.blocks_ordered x hc.1 y hc.2 hk
      by_cases hf : R.key x ∈ R.firstOnRight
      · have hf' : R.key y ∈ R.firstOnRight := hk ▸ hf
        have hyx : y < x := hord.1 hf
        simp [hk, R.rank_first hc.1, R.rank_second hc.2, hf', hyx]
      · have hf' : R.key y ∉ R.firstOnRight := hk ▸ hf
        have hyx : ¬y < x := (hord.2 hf).asymm
        simp [hk, R.rank_first hc.1, R.rank_second hc.2, hf', hyx]
    · have hord := R.blocks_ordered y hc.2 x hc.1 hk.symm
      by_cases hf : R.key y ∈ R.firstOnRight
      · have hyx : ¬y < x := (hord.1 hf).asymm
        simp [hk, R.rank_second hc.1, R.rank_first hc.2, hf, hyx]
      · have hyx : y < x := hord.2 hf
        simp [hk, R.rank_second hc.1, R.rank_first hc.2, hf, hyx]
  lt_iff_of_not_crossed x y hc := by
    change R.interchangeCode x < R.interchangeCode y ↔ x < y
    rw [R.interchangeCode_lt_iff]
    rcases lt_trichotomy (R.key x) (R.key y) with hk | hk | hk
    · have hxy : x < y := lt_of_not_ge fun h => (R.key_mono h).not_gt hk
      simp [hk, hxy]
    · have hc' : ¬(x ∈ R.first ∧ y ∈ R.second ∨ x ∈ R.second ∧ y ∈ R.first) :=
        fun h => hc ⟨hk, h⟩
      have hr : R.rank x = R.rank y := by
        by_cases hx1 : x ∈ R.first
        · have hy1 : y ∈ R.first := by
            rcases R.region_blocks x y hk (Or.inl hx1) with h | h
            · exact h
            · exact absurd (Or.inl ⟨hx1, h⟩) hc'
          rw [R.rank_first hx1, R.rank_first hy1, hk]
        · by_cases hx2 : x ∈ R.second
          · have hy2 : y ∈ R.second := by
              rcases R.region_blocks x y hk (Or.inr hx2) with h | h
              · exact absurd (Or.inr ⟨hx2, h⟩) hc'
              · exact h
            rw [R.rank_second hx2, R.rank_second hy2, hk]
          · have hy1 : y ∉ R.first := fun h =>
              (R.region_blocks y x hk.symm (Or.inl h)).elim hx1 hx2
            have hy2 : y ∉ R.second := fun h =>
              (R.region_blocks y x hk.symm (Or.inr h)).elim hx1 hx2
            rw [R.rank_neutral hx1 hx2, R.rank_neutral hy1 hy2]
      simp [hk, hr]
    · have hxy : ¬x < y := fun h => (R.key_mono h.le).not_gt hk
      simp [hk.asymm, hk.ne', hxy]

end BlockRegions

/-- The smallest configuration with nonempty blocks: two positions forming one region, the
first family's block `{false}` on the left and the second family's block `{true}` on the
right. -/
def twoPointRegions : BlockRegions Bool where
  Region := PUnit
  key := fun _ => PUnit.unit
  key_mono := fun _ _ _ => le_rfl
  first := {false}
  second := {true}
  firstOnRight := ∅
  blocks_ordered := by
    rintro x hx y hy -
    rw [Set.mem_singleton_iff] at hx hy
    subst hx hy
    exact ⟨fun h => absurd h (Set.notMem_empty _), fun _ => by decide⟩
  region_blocks := by
    intro x y _ _
    cases y <;> simp

/-- The interchange really reverses the two blocks. -/
example :
    twoPointRegions.interchange.toEquiv true < twoPointRegions.interchange.toEquiv false :=
  (twoPointRegions.interchange.lt_iff_of_crossed true false ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩).mpr
    (by decide)

/-- **Lemma 4.6** (Disjoint block transpositions). Take two families of labeled terms. In
disjoint convex regions of their joint support order, suppose each region consists of two
adjacent blocks, one used only by the first family and one only by the second. Interchange the
blocks in every such region, retaining their internal orders and all positions outside the
regions. The joint natural diagram is unchanged.

Proof as in `text.md`: repeat the blocks along the binary-tree order with dividers
(`BlockRegions.Interchange.repeatsAlong`) and count orbits over the divider parameters with
Lemma 4.5 (`sameNaturalDiagram_of_repeatsAlong`). -/
theorem lemma_4_6_blockInterchange (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K)
    {I I' : Type u} [LinearOrder I] [LinearOrder I'] [Nonempty I] [Nonempty I']
    {α β : Type u} (σ : Cardinal.{u}) (hjoint : #(α ⊕ β) ≤ σ) (hσ : aleph0 ≤ σ)
    (t : α → SupportTerm E.lab E.arity I) (s : β → SupportTerm E.lab E.arity I)
    (R : BlockRegions I) (T : R.Interchange I')
    (ht : ∀ a k, (t a).pos k ∉ R.second) (hs : ∀ b k, (s b).pos k ∉ R.first) :
    SameNaturalDiagram K E D σ hjoint (Sum.elim t s)
      (Sum.elim (fun a => T.move (t a) (Or.inl (ht a)))
        (fun b => T.move (s b) (Or.inr (hs b)))) :=
  sameNaturalDiagram_of_repeatsAlong K E D σ hjoint hσ t s _ _ (T.repeatsAlong t s ht hs _)

/-- **Lemma 4.6**, for the canonical interchanged order `R.Interchanged` of the regions `R`:
the configuration obtained by interchanging the two blocks of every region has the same joint
natural diagram as the original one. -/
theorem lemma_4_6_blockRegions (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K)
    {I : Type u} [LinearOrder I] [Nonempty I]
    {α β : Type u} (σ : Cardinal.{u}) (hjoint : #(α ⊕ β) ≤ σ) (hσ : aleph0 ≤ σ)
    (t : α → SupportTerm E.lab E.arity I) (s : β → SupportTerm E.lab E.arity I)
    (R : BlockRegions I)
    (ht : ∀ a k, (t a).pos k ∉ R.second) (hs : ∀ b k, (s b).pos k ∉ R.first) :
    SameNaturalDiagram K E D σ hjoint (Sum.elim t s)
      (Sum.elim (fun a => R.interchange.move (t a) (Or.inl (ht a)))
        (fun b => R.interchange.move (s b) (Or.inr (hs b)))) :=
  lemma_4_6_blockInterchange K E D σ hjoint hσ t s R R.interchange ht hs

/-- **Lemma 4.6** (canonical Results name): disjoint block interchange along `BlockRegions`. -/
theorem lemma_4_6 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K)
    {I : Type u} [LinearOrder I] [Nonempty I]
    {α β : Type u} (σ : Cardinal.{u}) (hjoint : #(α ⊕ β) ≤ σ) (hσ : aleph0 ≤ σ)
    (t : α → SupportTerm E.lab E.arity I) (s : β → SupportTerm E.lab E.arity I)
    (R : BlockRegions I)
    (ht : ∀ a k, (t a).pos k ∉ R.second) (hs : ∀ b k, (s b).pos k ∉ R.first) :
    SameNaturalDiagram K E D σ hjoint (Sum.elim t s)
      (Sum.elim (fun a => R.interchange.move (t a) (Or.inl (ht a)))
        (fun b => R.interchange.move (s b) (Or.inr (hs b)))) :=
  lemma_4_6_blockRegions K E D σ hjoint hσ t s R ht hs

end
end AEC
