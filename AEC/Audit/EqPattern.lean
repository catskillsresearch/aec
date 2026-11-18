module

public import AEC.Audit.AllSets
public import AEC.Section12.Results

@[expose] public section

/-!
# An order presentation and a stable diagram on the AEC of all sets (statement audit)

`setsPresentation`: `E(I) = I` (bare set), one label of arity `1`, `realize t = t.pos 0`.
`eqDiagram`: `t σ = σ⁺`, and `same xs ys` is equality of equality patterns. Every field of
`OrderPresentation` and `StableDiagram` holds. Used to refute Lemma 12.6 as formalized
(the unoccupied strip `V` of the paper was dropped from the statement).
-/

namespace AEC
namespace Audit

universe u

open FirstOrder Cardinal

set_option linter.deprecated false

theorem eL_card : eL.{u}.card = 0 := by
  simp [Language.card, Language.Symbols, eL]

/-- A type as a bare `eL`-structure. -/
def bareModel (I : Type u) : Model eL.{u} := ⟨I, eStr _⟩

theorem fin_one_strictMono {β : Type u} [Preorder β] (p : Fin 1 → β) : StrictMono p :=
  fun a b h => absurd h (by rw [Subsingleton.elim a b]; exact lt_irrefl b)

/-- The order presentation `E(I) = I` on `allSetsAEC`. -/
noncomputable abbrev setsPresentation : OrderPresentation allSetsAEC.{u} where
  ell := ls allSetsAEC.{u}
  ell_eq := rfl
  lab := PUnit.{u + 1}
  lab_small := by
    rw [Cardinal.mk_punit]
    exact one_le_aleph0.trans (isLSBound_ls _).1
  arity _ := 1
  arity_pos _ := Nat.one_pos
  obj I _ _ := bareModel I
  map f := embOf (M := bareModel _) (N := bareModel _) f f.injective
  map_strong _ := trivial
  map_id := by intros; ext x; rfl
  map_comp := by intros; ext x; rfl
  realize t := t.pos ⟨0, Nat.one_pos⟩
  realize_surjective := fun i => ⟨⟨PUnit.unit, fun _ => i, fin_one_strictMono _⟩, rfl⟩
  realize_map _ _ := rfl
  pattern_determines := by
    intro I _ _ n t s hl heq _
    refine ⟨fun i j => heq i j ⟨0, Nat.one_pos⟩ ⟨0, Nat.one_pos⟩, fun f => isEmptyElim (α := eL.{u}.Functions _) f,
      fun f => isEmptyElim (α := eL.{u}.Functions _) f, fun r => isEmptyElim (α := eL.{u}.Relations _) r⟩
  skeleton := Function.Embedding.refl _
  skeleton_natural _ _ := rfl
  sub s := bareModel {x // x ∈ s}
  sub_incl s _ := embOf (M := bareModel _) (N := bareModel _) Subtype.val Subtype.val_injective
  sub_strong _ _ := trivial
  sub_card s _ := (Cardinal.lt_aleph0_of_finite {x // x ∈ s}).le.trans (isLSBound_ls _).1
  sub_mono s t _ _ hst :=
    ⟨embOf (M := bareModel {x // x ∈ s}) (N := bareModel {x // x ∈ t})
      (fun x => ⟨x.1, hst x.2⟩) (fun a b h => Subtype.ext (by have := congrArg Subtype.val h; exact this)),
      trivial, Language.Embedding.ext fun _ => rfl⟩
  sub_cover x := ⟨{x}, Finset.singleton_nonempty x, ⟨x, Finset.mem_singleton_self x⟩, rfl⟩
  card_lower := le_rfl
  card_upper := le_self_add

/-- Equality patterns. -/
def EqPat {α M N : Type u} (xs : α → M) (ys : α → N) : Prop :=
  ∀ i j, xs i = xs j ↔ ys i = ys j

theorem eqPat_extend {α M N : Type u} (xs : α → M) (ys : α → N) (hp : EqPat xs ys)
    (e : ↥(Set.range xs)ᶜ ≃ ↥(Set.range ys)ᶜ) :
    ∃ F : M → N, Function.Injective F ∧ ∀ i, F (xs i) = ys i := by
  classical
  let F : M → N := fun m =>
    if h : m ∈ Set.range xs then ys (Classical.choose h) else (e ⟨m, h⟩).1
  have hF1 : ∀ i, F (xs i) = ys i := fun i => by
    have h : xs i ∈ Set.range xs := ⟨i, rfl⟩
    simp only [F, dif_pos h]
    exact (hp _ _).mp (Classical.choose_spec h)
  refine ⟨F, fun m m' hmm => ?_, hF1⟩
  by_cases h : m ∈ Set.range xs <;> by_cases h' : m' ∈ Set.range xs
  · obtain ⟨i, rfl⟩ := h
    obtain ⟨j, rfl⟩ := h'
    rw [hF1, hF1] at hmm
    exact (hp i j).mpr hmm
  · obtain ⟨i, rfl⟩ := h
    rw [hF1] at hmm
    simp only [F, dif_neg h'] at hmm
    exact absurd ⟨i, hmm⟩ (e ⟨m', h'⟩).2
  · obtain ⟨j, rfl⟩ := h'
    rw [hF1] at hmm
    simp only [F, dif_neg h] at hmm
    exact absurd ⟨j, hmm.symm⟩ (e ⟨m, h⟩).2
  · simp only [F, dif_neg h, dif_neg h'] at hmm
    exact congrArg Subtype.val (e.injective (Subtype.ext hmm))

theorem eqPat_joint {α γ M N : Type u} (ac : α ⊕ γ → M) (a : α → N)
    (hp : EqPat (fun i => ac (Sum.inl i)) a) :
    ∃ c : γ → N ⊕ M, EqPat ac (Sum.elim (fun i => (Sum.inl (a i) : N ⊕ M)) c) := by
  classical
  let φ : M → N ⊕ M := fun m =>
    if h : ∃ i, ac (Sum.inl i) = m then Sum.inl (a (Classical.choose h)) else Sum.inr m
  have hφ1 : ∀ i, φ (ac (Sum.inl i)) = Sum.inl (a i) := fun i => by
    have h : ∃ j, ac (Sum.inl j) = ac (Sum.inl i) := ⟨i, rfl⟩
    simp only [φ, dif_pos h]
    exact congrArg Sum.inl ((hp _ _).mp (Classical.choose_spec h))
  have hinj : Function.Injective φ := by
    intro m m' hmm
    by_cases h : ∃ i, ac (Sum.inl i) = m <;> by_cases h' : ∃ i, ac (Sum.inl i) = m'
    · obtain ⟨i, rfl⟩ := h
      obtain ⟨j, rfl⟩ := h'
      rw [hφ1, hφ1] at hmm
      exact (hp i j).mpr (Sum.inl_injective hmm)
    · obtain ⟨i, rfl⟩ := h
      rw [hφ1] at hmm
      simp only [φ, dif_neg h'] at hmm
      cases hmm
    · obtain ⟨j, rfl⟩ := h'
      rw [hφ1] at hmm
      simp only [φ, dif_neg h] at hmm
      cases hmm
    · simp only [φ, dif_neg h, dif_neg h'] at hmm
      exact Sum.inr_injective hmm
  refine ⟨fun g => φ (ac (Sum.inr g)), fun p q => ?_⟩
  have hel : ∀ p, Sum.elim (fun i => (Sum.inl (a i) : N ⊕ M)) (fun g => φ (ac (Sum.inr g))) p =
      φ (ac p) := by
    rintro (i | g)
    · exact (hφ1 i).symm
    · rfl
  rw [hel, hel]
  exact hinj.eq_iff.symm

/-- `allSetsAEC` is categorical in every cardinal. -/
theorem setsCategorical (κ : Cardinal.{u}) : Categorical allSetsAEC.{u} κ where
  exists_model := ⟨bareModel κ.out, trivial, Cardinal.mk_out κ⟩
  unique_model M N _ _ hM hN := by
    obtain ⟨e⟩ := Cardinal.eq.mp (hM.trans hN.symm)
    exact ⟨⟨e, fun {_} f => isEmptyElim (α := eL.{u}.Functions _) f,
      fun {_} r => isEmptyElim (α := eL.{u}.Relations _) r⟩⟩

/-- Equality-pattern stable diagram on `allSetsAEC`. -/
noncomputable def eqDiagram : StableDiagram allSetsAEC.{u} where
  t σ := Order.succ σ
  mono _ _ h := Order.succ_le_succ h
  above σ _ := by
    rw [show allSetsAEC.{u}.τ.card = 0 from eL_card, zero_add]
    exact Order.lt_succ σ
  categoricity σ _ := setsCategorical _
  same _ _ _ _ _ xs ys := EqPat xs ys
  refl _ _ _ _ := fun _ _ => Iff.rfl
  symm _ _ _ _ _ _ _ h := fun i j => (h i j).symm
  trans _ _ _ _ _ _ _ _ _ _ h1 h2 := fun i j => (h1 i j).trans (h2 i j)
  preserves_atomic _ _ _ _ _ _ _ h := h
  of_strong _ _ _ _ _ xs ys f _ _ hf := fun i j => by
    rw [← hf i, ← hf j]
    exact f.injective.eq_iff.symm
  to_strong := by
    intro σ α M N hα _ _ xs ys hσ _ hc hMc hNc hs
    have hinfM : Infinite M.carrier := Cardinal.infinite_iff.mpr
      (hσ.trans ((Order.le_succ σ).trans hMc))
    have hinfN : Infinite N.carrier := Cardinal.infinite_iff.mpr
      (hσ.trans ((Order.le_succ σ).trans hNc))
    have hltM : #(Set.range xs) < #M.carrier :=
      lt_of_le_of_lt (Cardinal.mk_range_le.trans hα) (lt_of_lt_of_le (Order.lt_succ σ) hMc)
    have hltN : #(Set.range ys) < #N.carrier :=
      lt_of_le_of_lt (Cardinal.mk_range_le.trans hα) (lt_of_lt_of_le (Order.lt_succ σ) hNc)
    have hcM := Cardinal.mk_compl_of_infinite _ hltM
    have hcN := Cardinal.mk_compl_of_infinite _ hltN
    obtain ⟨e⟩ := Cardinal.eq.mp (hcM.trans (hc.trans hcN.symm))
    obtain ⟨F, hF, hF1⟩ := eqPat_extend xs ys hs e
    exact ⟨embOf (M := M) (N := N) F hF, trivial, hF1⟩
  realize_joint := by
    intro σ α γ M N _ _ _ _ _ hNc ac a _ _ _ h2
    obtain ⟨c, hc⟩ := eqPat_joint ac a h2
    exact ⟨⟨N.carrier ⊕ M.carrier, eStr _⟩,
      embOf (M := N) (N := ⟨N.carrier ⊕ M.carrier, eStr _⟩) Sum.inl Sum.inl_injective, c,
      trivial, hNc.trans (Cardinal.mk_le_of_injective Sum.inl_injective), trivial, hc⟩

/-- The single term over `J` sitting at `j`. -/
def ptTerm {J : Type u} [LinearOrder J] (j : J) :
    SupportTerm setsPresentation.{u}.lab setsPresentation.{u}.arity J :=
  ⟨PUnit.unit, fun _ => j, fin_one_strictMono _⟩

/-- **Lemma 12.6 is false as formalized.** Without the paper's unoccupied strip, `J` may be a
single point: two distinct new terms over `Jstar` have no realization over `J` with the same
natural diagram. -/
theorem lemma_12_6_false :
    ¬ ∀ (K : AbstractElementaryClass.{u}) (E : OrderPresentation K) (D : StableDiagram K)
      {J Jstar : Type u} [LinearOrder J] [LinearOrder Jstar] [Nonempty J] [Nonempty Jstar]
      (incl : J ↪o Jstar) {α : Type u} (σ : Cardinal.{u}) (hσ : #α ≤ σ)
      (zStar : α → SupportTerm E.lab E.arity Jstar) (old : Set α),
      (∀ i ∈ old, ∃ t : SupportTerm E.lab E.arity J, zStar i = SupportTerm.along incl t) →
      ∃ z : α → SupportTerm E.lab E.arity J,
        SameNaturalDiagram K E D σ hσ z zStar ∧
        ∀ i ∈ old, zStar i = SupportTerm.along incl (z i) := by
  intro H
  let incl : PUnit.{u + 1} ↪o ULift.{u} Bool :=
    OrderEmbedding.ofStrictMono (fun _ => ⟨false⟩) (fun a b h => absurd h (by
      rw [Subsingleton.elim a b]; exact lt_irrefl b))
  obtain ⟨z, hz, -⟩ := H allSetsAEC.{u} setsPresentation.{u} eqDiagram.{u} incl
    (α := ULift.{u} Bool) ℵ₀ (Cardinal.lt_aleph0_of_finite _).le (fun b => ptTerm b) ∅
    (fun _ h => absurd h (Set.notMem_empty _))
  obtain ⟨J', _, _, f, g, _, _, hs⟩ := hz
  have h := (hs ⟨false⟩ ⟨true⟩).mp (congrArg f (Subsingleton.elim ((z ⟨false⟩).pos ⟨0, Nat.one_pos⟩)
    ((z ⟨true⟩).pos ⟨0, Nat.one_pos⟩)))
  have := g.injective h
  exact Bool.false_ne_true (congrArg ULift.down this)

/-- The original form of Lemma 12.5 (query index type `ι` fixed outside the hypothesis) is
false: a query type of size `> g σ τ` makes the hypothesis vacuous. -/
theorem lemma_12_5_original_false :
    ¬ ∀ (K : AbstractElementaryClass.{u}) (E : OrderPresentation K) (D : StableDiagram K),
    ∃ g : Cardinal.{u} → Cardinal.{u} → Cardinal.{u},
      (∀ σ τ σ' τ', σ ≤ σ' → τ ≤ τ' → g σ τ ≤ g σ' τ') ∧
      ∀ {I : Type u} [LinearOrder I] [Nonempty I] {α β ι : Type u}
        (σ τ : Cardinal.{u}) (_hσ : #α ≤ σ) (_hτ : #β ≤ τ)
        (hsum : #(α ⊕ β) ≤ σ + τ)
        (t s : α → SupportTerm E.lab E.arity I) (c : β → SupportTerm E.lab E.arity I),
        (∀ (q : ι → SupportTerm E.lab E.arity I) (_hq : #ι ≤ g σ τ)
            (hquery : #((α ⊕ β) ⊕ ι) ≤ σ + τ + g σ τ),
          SameNaturalDiagram K E D (σ + τ + g σ τ) hquery
            (Sum.elim (Sum.elim t c) q) (Sum.elim (Sum.elim s c) q)) →
        SameNaturalDiagram K E D (σ + τ) hsum (Sum.elim t c) (Sum.elim s c) := by
  intro H
  obtain ⟨g, -, hg⟩ := H allSetsAEC.{u} setsPresentation.{u} eqDiagram.{u}
  have hfin : #(ULift.{u} Bool) ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite _).le
  have hsum : #(ULift.{u} Bool ⊕ PEmpty.{u + 1}) ≤ ℵ₀ + 0 := by
    rw [add_zero]; exact (Cardinal.lt_aleph0_of_finite _).le
  obtain ⟨J', _, _, f, f', _, _, hs⟩ := hg (I := ULift.{u} Bool) (α := ULift.{u} Bool)
    (β := PEmpty.{u + 1}) (ι := (Order.succ (g ℵ₀ 0)).out) ℵ₀ 0 hfin (by simp) hsum
    (fun _ => ptTerm ⟨false⟩) (fun b => ptTerm b) isEmptyElim
    (fun _ hq _ => absurd hq (by rw [Cardinal.mk_out]; exact not_le_of_gt (Order.lt_succ _)))
  have h := (hs (Sum.inl ⟨false⟩) (Sum.inl ⟨true⟩)).mp rfl
  exact Bool.false_ne_true (congrArg ULift.down (f'.injective h))

end Audit
end AEC
