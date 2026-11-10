module

public import AEC.Section4.NaturalDiagram
public import AEC.Section4.BinaryTreeOrder
public import AEC.Section4.OrbitsOverParameters
public import AEC.Section1.UnboundedCategoricity
public import AEC.Section5.TermTemplate
public import Mathlib.Order.Sum.Order

@[expose] public section

/-!
# Degenerate `DisjointBlockSwap` packaging (not English Lemma 4.6)

`DisjointBlockSwap` requires an order automorphism that swaps adjacent exclusive blocks.
That forces every block empty (`orderIso_swaps_blocks_empty` in `BlockInterchange.lean`).
The English Lemma 4.6 lives in `BlockInterchange.lean` (`BlockRegions` / `lemma_4_6`).

This module keeps the auto-along-padded-swap reading and the older `χ`/tree scaffolding
for reference only.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal Sum

/-- A family of disjoint adjacent block pairs, swapped by an order automorphism and fixing
every position outside those blocks. -/
structure DisjointBlockSwap (I : Type u) [LinearOrder I] where
  swap : I ≃o I
  blocks : Set (Set I × Set I)
  disjoint : ∀ p ∈ blocks, ∀ q ∈ blocks, p = q ∨
    Disjoint p.1 q.1 ∧ Disjoint p.1 q.2 ∧ Disjoint p.2 q.1 ∧ Disjoint p.2 q.2
  leftBeforeRight : ∀ p ∈ blocks, ∀ a ∈ p.1, ∀ b ∈ p.2, a < b
  convex : ∀ p ∈ blocks,
    (∀ a c b, a ∈ p.1 → c ∈ p.1 → a ≤ b → b ≤ c → b ∈ p.1) ∧
    (∀ a c b, a ∈ p.2 → c ∈ p.2 → a ≤ b → b ≤ c → b ∈ p.2) ∧
    (∀ x, (∃ a ∈ p.1, ∃ b ∈ p.2, a ≤ x ∧ x ≤ b) → x ∈ p.1 ∨ x ∈ p.2)
  swaps : ∀ p ∈ blocks, swap '' p.1 = p.2 ∧ swap '' p.2 = p.1
  fixes : ∀ i, (∀ p ∈ blocks, i ∉ p.1 ∧ i ∉ p.2) → swap i = i

/-- Pad `I` on the right so the presentation meets the diagram threshold. -/
noncomputable def blockSwapPad (I : Type u) [LinearOrder I] (θ : Cardinal.{u}) : Type u :=
  I ⊕ₗ Below θ

noncomputable instance blockSwapPad.linearOrder {I : Type u} [LinearOrder I] {θ : Cardinal.{u}} :
    LinearOrder (blockSwapPad I θ) :=
  inferInstanceAs (LinearOrder (I ⊕ₗ Below θ))

noncomputable instance blockSwapPad.nonempty {I : Type u} [LinearOrder I] [Nonempty I]
    {θ : Cardinal.{u}} : Nonempty (blockSwapPad I θ) :=
  ⟨inlₗ (Classical.arbitrary I)⟩

theorem mk_blockSwapPad_ge {I : Type u} [LinearOrder I] {θ : Cardinal.{u}} :
    θ ≤ #(blockSwapPad I θ) := by
  -- Inject `Below θ` into the right summand of the padded index.
  refine (le_of_eq (mk_ord_toType θ).symm).trans ?_
  exact mk_le_of_injective
    (f := fun x : Below θ => (inrₗ x : blockSwapPad I θ))
    (fun a b h => by
      have := congrArg ofLex h
      simpa [inrₗ] using this)

/-- Extend an order automorphism of `I` by the identity on a right summand. -/
noncomputable def sumLexCongrLeft {I H : Type u} [LinearOrder I] [LinearOrder H]
    (e : I ≃o I) : (I ⊕ₗ H) ≃o (I ⊕ₗ H) :=
  OrderIso.sumLexCongr e (OrderIso.refl H)

/-- English cardinal setup: `χ` with `χ^σ = χ` and `ℓ + 2^(2^σ) ≤ χ`. -/
noncomputable def lemma46_chi (K : AbstractElementaryClass.{u}) (σ : Cardinal.{u}) : Cardinal.{u} :=
  lemma46Chi (ls K) σ

theorem lemma46_chi_power (K : AbstractElementaryClass.{u}) {σ : Cardinal.{u}}
    (hσ : aleph0 ≤ σ) : lemma46_chi K σ ^ σ = lemma46_chi K σ :=
  lemma46Chi_power_eq (ls K) σ hσ

theorem lemma46_chi_bound (K : AbstractElementaryClass.{u}) (σ : Cardinal.{u}) :
    ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ lemma46_chi K σ :=
  lemma46Chi_bound (ls K) σ

/-- Branch index set of the English tree order; cardinality `> χ`. -/
def lemma46_branches (K : AbstractElementaryClass.{u}) (σ : Cardinal.{u}) : Type u :=
  TreeBranch (lemma46_chi K σ)

theorem lemma46_branches_gt (K : AbstractElementaryClass.{u}) {σ : Cardinal.{u}}
    (hσ : aleph0 ≤ σ) : lemma46_chi K σ < #(lemma46_branches K σ) := by
  simpa [lemma46_branches, lemma46_chi] using
    mk_treeBranch_gt (lemma46Chi (ls K) σ)

/-- Divider index set; cardinality `≤ χ`. -/
def lemma46_dividers (K : AbstractElementaryClass.{u}) (σ : Cardinal.{u}) : Type u :=
  TreeDivider (lemma46_chi K σ)

theorem lemma46_dividers_le (K : AbstractElementaryClass.{u}) (σ : Cardinal.{u}) :
    #(lemma46_dividers K σ) ≤ lemma46_chi K σ := by
  simpa [lemma46_dividers, lemma46_chi] using mk_treeDivider_le (lemma46Chi (ls K) σ)

/-- First-family placements into the padded ambient (block-repeat scaffolding). -/
noncomputable def blockRepeat_d {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] {α : Type u} {θ : Cardinal.{u}}
    (t : α → SupportTerm E.lab E.arity I) :
    α → SupportTerm E.lab E.arity (blockSwapPad I θ) :=
  fun a => SupportTerm.along (sumLexEmbedLeftIncl I (Below θ)) (t a)

noncomputable def blockRepeat_e {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I : Type u} [LinearOrder I] {β : Type u} {θ : Cardinal.{u}}
    (s : β → SupportTerm E.lab E.arity I) :
    β → SupportTerm E.lab E.arity (blockSwapPad I θ) :=
  fun b => SupportTerm.along (sumLexEmbedLeftIncl I (Below θ)) (s b)

/-- Orbit-bound interface from Lemma 4.5 at the English `χ`. -/
theorem lemma46_orbit_bound (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ) :
    ∃ κ0 : Cardinal.{u}, ∀ κ, κ0 ≤ κ → Categorical K κ →
      ∀ (M : Model K.τ), K.Mem M → Model.card M = κ →
        ∀ P : Set M.carrier, #P ≤ lemma46_chi K σ →
          ∀ {ι : Type u}, #ι ≤ σ →
            ∃ reps : Set (ι → M.carrier), #reps ≤ lemma46_chi K σ ∧
              ∀ xs : ι → M.carrier, ∃ ys ∈ reps,
                SameOrbitOverParams K M P xs ys := by
  obtain ⟨κ0, h⟩ := lemma_4_5_with_E K E σ (lemma46_chi K σ) hσ
    (lemma46_chi_power K hσ) (lemma46_chi_bound K σ)
  refine ⟨κ0, fun κ hκ0 hcat M hM hMcard P hP ι hι => ?_⟩
  obtain ⟨reps, hreps, horb⟩ := h κ hκ0 hcat M hM hMcard P hP hι
  refine ⟨reps, hreps, fun xs => ?_⟩
  obtain ⟨ys, hys, e, heS, heP, he⟩ := horb xs
  exact ⟨ys, hys, ⟨e, heS, heP, he⟩⟩

/-- Degenerate packaging: `DisjointBlockSwap` forces empty blocks (`orderIso_swaps_blocks_empty`
in `BlockInterchange.lean`), so this only records `D.same` along an order automorphism of `I`.
The English Lemma 4.6 is `lemma_4_6` / `BlockRegions` in `BlockInterchange.lean`. -/
theorem lemma_4_6_disjointBlockSwap_auto (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K)
    {I : Type u} [LinearOrder I] [Nonempty I]
    {α β : Type u} (σ : Cardinal.{u}) (hjoint : #(α ⊕ β) ≤ σ) (hσinf : aleph0 ≤ σ)
    (t : α → SupportTerm E.lab E.arity I) (s : β → SupportTerm E.lab E.arity I)
    (B : DisjointBlockSwap I)
    (_ht : ∀ a (i : Fin (E.arity (t a).label)) p, p ∈ B.blocks →
      (t a).pos i ∈ p.1 ∨ (t a).pos i ∈ p.2 → (t a).pos i ∈ p.1)
    (_hs : ∀ b (i : Fin (E.arity (s b).label)) p, p ∈ B.blocks →
      (s b).pos i ∈ p.1 ∨ (s b).pos i ∈ p.2 → (s b).pos i ∈ p.2) :
    SameNaturalDiagram K E D σ hjoint (Sum.elim t s)
      (Sum.elim (fun a => SupportTerm.along B.swap.toOrderEmbedding (t a))
        (fun b => SupportTerm.along B.swap.toOrderEmbedding (s b))) := by
  classical
  -- English cardinal / tree / orbit-bound setup (Lemma 4.5 parameters).
  let χ := lemma46_chi K σ
  have _hpow := lemma46_chi_power K hσinf
  have _hχ := lemma46_chi_bound K σ
  have _hbr := lemma46_branches_gt K hσinf
  have _hdiv := lemma46_dividers_le K σ
  have _horb := lemma46_orbit_bound K E hσinf
  -- Pad past the diagram threshold; witness `D.same` via `of_strong` along the padded swap.
  let θ : Cardinal.{u} := D.t σ
  let J : Type u := blockSwapPad I θ
  let ι : I ↪o J := sumLexEmbedLeftIncl I (Below θ)
  let swapJ : J ≃o J := sumLexCongrLeft (H := Below θ) B.swap
  have hM : K.Mem (E.obj J) := orderPresentation_obj_mem E J
  have hcard : D.t σ ≤ Model.card (E.obj J) :=
    (mk_blockSwapPad_ge (I := I) (θ := θ)).trans (E.card_lower (I := J))
  have hmatch : ∀ x,
      E.map swapJ.toOrderEmbedding
        (E.realize (SupportTerm.along ι (Sum.elim t s x))) =
      E.realize (SupportTerm.along ι
        (Sum.elim (fun a => SupportTerm.along B.swap.toOrderEmbedding (t a))
          (fun b => SupportTerm.along B.swap.toOrderEmbedding (s b)) x)) := by
    intro x
    have hnat := E.realize_along swapJ.toOrderEmbedding
      (SupportTerm.along ι (Sum.elim t s x))
    refine hnat.trans ?_
    congr 1
    cases x with
    | inl a =>
      refine SupportTerm.ext_of_label_eq rfl fun k => ?_
      change swapJ (ι (t a |>.pos k)) = ι (B.swap (t a |>.pos k))
      rfl
    | inr b =>
      refine SupportTerm.ext_of_label_eq rfl fun k => ?_
      change swapJ (ι (s b |>.pos k)) = ι (B.swap (s b |>.pos k))
      rfl
  refine sameNaturalDiagram_along E D (Sum.elim t s)
    (Sum.elim (fun a => SupportTerm.along B.swap.toOrderEmbedding (t a))
      (fun b => SupportTerm.along B.swap.toOrderEmbedding (s b)))
    ι ι hcard hM ?_
  exact D.of_strong hjoint hM hM hcard hcard _ _
    (E.map swapJ.toOrderEmbedding) hσinf (E.map_strong _) hmatch

end
end AEC
