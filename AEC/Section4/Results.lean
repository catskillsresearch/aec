module

public import AEC.Section4.NaturalDiagram
public import AEC.Section4.CountableClosure
public import AEC.Section1.ArbitrarilyLarge
public import AEC.Section2.FiniteHull
public import AEC.Section2.DirectedLimit
public import AEC.Section3.Reversal
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- The natural diagrams of two `σ`-tuples already differ on the induced suborder `X`. -/
def DiagramsDifferOnSubset (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) {I : Type u} [LinearOrder I] [Nonempty I]
    {α : Type u} (σ : Cardinal.{u}) (hσ : #α ≤ σ) (X : Set I) (hX : X.Nonempty) : Prop :=
  haveI : Nonempty (↥X) := hX.to_subtype
  ∃ t' s' : α → SupportTerm E.lab E.arity (↥X),
    ¬ SameNaturalDiagram K E D σ hσ t' s'

/-- Factor a strong embedding through a strong ambient map whose range covers it; coherence
supplies strength of the factor. -/
theorem strongFactorEmbedding {K : AbstractElementaryClass.{u}} {M₀ M₁ M₂ : Model K.τ}
    (f₀₂ : Language.Embedding K.τ M₀.carrier M₂.carrier)
    (f₁₂ : Language.Embedding K.τ M₁.carrier M₂.carrier)
    (hf₀₂ : K.Strong f₀₂) (hf₁₂ : K.Strong f₁₂)
    (himg : ∀ x, ∃ y, f₁₂ y = f₀₂ x) :
    K.Strong (factorEmbedding f₀₂ f₁₂ himg) :=
  K.coherence (factorEmbedding f₀₂ f₁₂ himg) f₀₂ f₁₂ hf₀₂ hf₁₂
    (factorEmbedding_comp f₀₂ f₁₂ himg)

/-- **Lemma 4.1** (Canonical classes above one categoricity size). At a categoricity cardinal
`κ ≥ LS(K)` where reversal holds for `κ`-tuples, a tuple in a model of size at least `κ` has a
well-defined `≡σκ`-class: any two strong `κ`-submodels containing it are related by a strong map
sending the tuple to itself, and a strong embedding of models of size at least `κ` preserves
that class. -/
theorem lemma_4_1 (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    (hcat : Categorical K κ) (hls : ls K ≤ κ) (hrev : ReversalProperty K κ κ)
    (N : Model K.τ) (hN : K.Mem N) (hcard : κ ≤ Model.card N)
    {α : Type u} (a : α → N.carrier) (hα : #α ≤ κ) :
    (∀ (M₁ M₂ : Model K.τ)
        (f₁ : Language.Embedding K.τ M₁.carrier N.carrier)
        (f₂ : Language.Embedding K.τ M₂.carrier N.carrier),
        K.Mem M₁ → K.Mem M₂ → K.Strong f₁ → K.Strong f₂ →
        Model.card M₁ = κ → Model.card M₂ = κ →
        (∀ i, ∃ x, f₁ x = a i) → (∀ i, ∃ y, f₂ y = a i) →
        ∃ e : Language.Embedding K.τ M₁.carrier M₂.carrier,
          K.Strong e ∧
          ∀ i x y, f₁ x = a i → f₂ y = a i → e x = y) ∧
    ∀ (N' : Model K.τ) (g : Language.Embedding K.τ N.carrier N'.carrier),
      K.Mem N' → K.Strong g → κ ≤ Model.card N' →
      ∀ (M₁ M₂ : Model K.τ)
        (f₁ : Language.Embedding K.τ M₁.carrier N.carrier)
        (f₂ : Language.Embedding K.τ M₂.carrier N'.carrier),
        K.Mem M₁ → K.Mem M₂ → K.Strong f₁ → K.Strong f₂ →
        Model.card M₁ = κ → Model.card M₂ = κ →
        (∀ i, ∃ x, f₁ x = a i) → (∀ i, ∃ y, f₂ y = g (a i)) →
        ∃ e : Language.Embedding K.τ M₁.carrier M₂.carrier,
          K.Strong e ∧
          ∀ i x y, f₁ x = a i → f₂ y = g (a i) → e x = y := by
  classical
  have hκinf : aleph0 ≤ κ := (isLSBound_ls K).1.trans hls
  /- Common strong `κ`-hull of two strong `κ`-embeddings into an ambient model. -/
  have commonHull {M₁ M₂ P : Model K.τ}
      (f₁ : Language.Embedding K.τ M₁.carrier P.carrier)
      (f₂ : Language.Embedding K.τ M₂.carrier P.carrier)
      (hP : K.Mem P) (hf₁ : K.Strong f₁) (hf₂ : K.Strong f₂)
      (hc₁ : Model.card M₁ = κ) (hc₂ : Model.card M₂ = κ) :
      ∃ (M₃ : Model K.τ)
        (f₃ : Language.Embedding K.τ M₃.carrier P.carrier)
        (g₁ : Language.Embedding K.τ M₁.carrier M₃.carrier)
        (g₂ : Language.Embedding K.τ M₂.carrier M₃.carrier),
        K.Mem M₃ ∧ K.Strong f₃ ∧ Model.card M₃ = κ ∧
        K.Strong g₁ ∧ K.Strong g₂ ∧
        f₃.comp g₁ = f₁ ∧ f₃.comp g₂ = f₂ := by
    let A : Set P.carrier := Set.range f₁ ∪ Set.range f₂
    have hA_le : #A ≤ κ := by
      have hle := mk_union_le (Set.range f₁) (Set.range f₂)
      have h1 : #(Set.range f₁) ≤ κ :=
        (mk_range_le (f := ⇑f₁)).trans_eq hc₁
      have h2 : #(Set.range f₂) ≤ κ :=
        (mk_range_le (f := ⇑f₂)).trans_eq hc₂
      have hsum := add_le_add h1 h2
      rw [add_eq_self hκinf] at hsum
      exact hle.trans hsum
    have hA_ge : κ ≤ #A := by
      have hr : #(Set.range f₁) = κ :=
        (mk_range_eq (⇑f₁) f₁.injective).trans hc₁
      exact hr.symm.trans_le (mk_le_mk_of_subset Set.subset_union_left)
    have hA_eq : #A = κ := le_antisymm hA_le hA_ge
    obtain ⟨M₃, f₃, hM₃, hf₃, hcov, hcard₃⟩ := (isLSBound_ls K).2.2 P hP A
    have hcard_le : Model.card M₃ ≤ κ := by
      have h := hcard₃.trans (add_le_add (le_of_eq hA_eq) hls)
      rwa [add_eq_self hκinf] at h
    have hcard_ge : κ ≤ Model.card M₃ := by
      have hr : #(Set.range f₁) = κ :=
        (mk_range_eq (⇑f₁) f₁.injective).trans hc₁
      have hsub : Set.range f₁ ⊆ Set.range f₃ := by
        intro x hx
        obtain ⟨n, hn⟩ := hcov x (Or.inl hx)
        exact ⟨n, hn⟩
      have hle : #(Set.range f₁) ≤ #(Set.range f₃) := mk_le_mk_of_subset hsub
      exact hr.symm.trans_le (hle.trans mk_range_le)
    have hc₃ : Model.card M₃ = κ := le_antisymm hcard_le hcard_ge
    have himg₁ : ∀ x, ∃ y, f₃ y = f₁ x := fun x =>
      hcov (f₁ x) (Or.inl ⟨x, rfl⟩)
    have himg₂ : ∀ x, ∃ y, f₃ y = f₂ x := fun x =>
      hcov (f₂ x) (Or.inr ⟨x, rfl⟩)
    let g₁ := factorEmbedding f₁ f₃ himg₁
    let g₂ := factorEmbedding f₂ f₃ himg₂
    refine ⟨M₃, f₃, g₁, g₂, hM₃, hf₃, hc₃,
      strongFactorEmbedding f₁ f₃ hf₁ hf₃ himg₁,
      strongFactorEmbedding f₂ f₃ hf₂ hf₃ himg₂,
      factorEmbedding_comp f₁ f₃ himg₁,
      factorEmbedding_comp f₂ f₃ himg₂⟩
  /- Strong map between two `κ`-models that hit the same ambient tuple. -/
  have sameClass {M₁ M₂ P : Model K.τ} (b : α → P.carrier)
      (f₁ : Language.Embedding K.τ M₁.carrier P.carrier)
      (f₂ : Language.Embedding K.τ M₂.carrier P.carrier)
      (hP : K.Mem P) (hf₁ : K.Strong f₁) (hf₂ : K.Strong f₂)
      (hc₁ : Model.card M₁ = κ) (hc₂ : Model.card M₂ = κ)
      (hhit₁ : ∀ i, ∃ x, f₁ x = b i) (hhit₂ : ∀ i, ∃ y, f₂ y = b i) :
      ∃ e : Language.Embedding K.τ M₁.carrier M₂.carrier,
        K.Strong e ∧ ∀ i x y, f₁ x = b i → f₂ y = b i → e x = y := by
    obtain ⟨M₃, f₃, g₁, g₂, hM₃, _hf₃, hc₃, hg₁, hg₂, hcg₁, hcg₂⟩ :=
      commonHull f₁ f₂ hP hf₁ hf₂ hc₁ hc₂
    let x₁ : α → M₁.carrier := fun i => Classical.choose (hhit₁ i)
    let y₂ : α → M₂.carrier := fun i => Classical.choose (hhit₂ i)
    have hx₁ : ∀ i, f₁ (x₁ i) = b i := fun i => Classical.choose_spec (hhit₁ i)
    have hy₂ : ∀ i, f₂ (y₂ i) = b i := fun i => Classical.choose_spec (hhit₂ i)
    have hz : ∀ i, g₁ (x₁ i) = g₂ (y₂ i) := by
      intro i
      apply f₃.injective
      calc
        f₃ (g₁ (x₁ i)) = f₁ (x₁ i) := by rw [← Language.Embedding.comp_apply, hcg₁]
        _ = b i := hx₁ i
        _ = f₂ (y₂ i) := (hy₂ i).symm
        _ = f₃ (g₂ (y₂ i)) := by rw [← Language.Embedding.comp_apply, hcg₂]
    have hM₂ : K.Mem M₂ := K.strong_mem_dom f₂ hf₂
    obtain ⟨φ⟩ := hcat.unique_model M₃ M₂ hM₃ hM₂ hc₃ hc₂
    have hφstr : K.Strong φ.toEmbedding := strong_of_equiv K φ hM₃
    let s : Language.Embedding K.τ M₂.carrier M₂.carrier := φ.toEmbedding.comp g₂
    have hs : K.Strong s := K.strong_trans g₂ φ.toEmbedding hg₂ hφstr
    obtain ⟨r, hr, hr_tup⟩ := hrev M₂ s (fun i => y₂ i) hM₂ hc₂ hs hα
    let e : Language.Embedding K.τ M₁.carrier M₂.carrier :=
      (r.comp φ.toEmbedding).comp g₁
    have he : K.Strong e :=
      K.strong_trans g₁ (r.comp φ.toEmbedding) hg₁
        (K.strong_trans φ.toEmbedding r hφstr hr)
    refine ⟨e, he, ?_⟩
    intro i x y hx hy
    have hx_eq : x = x₁ i := f₁.injective (hx.trans (hx₁ i).symm)
    have hy_eq : y = y₂ i := f₂.injective (hy.trans (hy₂ i).symm)
    rw [hx_eq, hy_eq]
    change r (φ (g₁ (x₁ i))) = y₂ i
    rw [hz i]
    simpa [s, Language.Embedding.comp_apply] using hr_tup i
  refine ⟨?_, ?_⟩
  · intro M₁ M₂ f₁ f₂ _hM₁ _hM₂ hf₁ hf₂ hc₁ hc₂ hhit₁ hhit₂
    exact sameClass a f₁ f₂ hN hf₁ hf₂ hc₁ hc₂ hhit₁ hhit₂
  · intro N' g hN' hg _hcard' M₁ M₂ f₁ f₂ _hM₁ _hM₂ hf₁ hf₂ hc₁ hc₂ hhit₁ hhit₂
    have hf₁' : K.Strong (g.comp f₁) := K.strong_trans f₁ g hf₁ hg
    have hhit₁' : ∀ i, ∃ x, (g.comp f₁) x = g (a i) := by
      intro i
      obtain ⟨x, hx⟩ := hhit₁ i
      exact ⟨x, by rw [Language.Embedding.comp_apply, hx]⟩
    obtain ⟨e, he, he_tup⟩ :=
      sameClass (fun i => g (a i)) (g.comp f₁) f₂ hN' hf₁' hf₂ hc₁ hc₂ hhit₁' hhit₂
    refine ⟨e, he, ?_⟩
    intro i x y hx hy
    exact he_tup i x y (by rw [Language.Embedding.comp_apply, hx]) hy

/-- **Proposition 4.2** (Stable diagrams). There is a nondecreasing cardinal function `t`,
with `t(σ)` a categoricity cardinal above `ℓ + σ`, whose diagram equality is preserved by
strong embeddings, implemented by a strong map at categoricity cardinals, and realized over
any matching parameter tuple. -/
theorem proposition_4_2 (K : AbstractElementaryClass.{u}) :
    ∃ D : StableDiagram K,
      (∀ {σ : Cardinal.{u}} {α : Type u} {M N : Model K.τ} (hα : #α ≤ σ)
          (hM : K.Mem M) (hN : K.Mem N)
          (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N)
          (xs : α → M.carrier) (ys : α → N.carrier)
          (f : Language.Embedding K.τ M.carrier N.carrier),
          aleph0 ≤ σ → K.Strong f → (∀ i, f (xs i) = ys i) →
          D.same hα hM hN hMcard hNcard xs ys) ∧
      (∀ {σ : Cardinal.{u}} {α : Type u} {M N : Model K.τ} (hα : #α ≤ σ)
          (hM : K.Mem M) (hN : K.Mem N)
          (xs : α → M.carrier) (ys : α → N.carrier),
          aleph0 ≤ σ → Categorical K (Model.card M) →
          Model.card M = Model.card N →
          (hMcard : D.t σ ≤ Model.card M) → (hNcard : D.t σ ≤ Model.card N) →
          D.same hα hM hN hMcard hNcard xs ys →
          ∃ f : Language.Embedding K.τ M.carrier N.carrier,
            K.Strong f ∧ ∀ i, f (xs i) = ys i) ∧
      (∀ {σ : Cardinal.{u}} {α γ : Type u} {M N : Model K.τ}
          (hαγ : #(α ⊕ γ) ≤ σ) (hα : #α ≤ σ)
          (hM : K.Mem M) (hN : K.Mem N)
          (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N)
          (ac : α ⊕ γ → M.carrier) (a : α → N.carrier),
          aleph0 ≤ σ → Categorical K (Model.card N) →
          D.same hαγ hM hM hMcard hMcard ac ac →
          D.same hα hN hN hNcard hNcard a a →
          ∃ (Q : Model K.τ) (f : Language.Embedding K.τ N.carrier Q.carrier)
            (c : γ → Q.carrier) (hQ : K.Mem Q) (hQcard : D.t σ ≤ Model.card Q),
            K.Strong f ∧
            D.same hαγ hM hQ hMcard hQcard ac (Sum.elim (fun i => f (a i)) c)) := by
  sorry

/-- **Proposition 4.3** (Categoricity at countably cofinal closure points). A cardinal `ζ > ℓ`
of countable cofinality strictly above `t(σ)` for every infinite `σ < ζ` is a categoricity
cardinal, and a diagram match of bounded tuples extends to an isomorphism. -/
theorem proposition_4_3 (K : AbstractElementaryClass.{u}) (D : StableDiagram K)
    (ζ : Cardinal.{u}) (hζ : ls K < ζ) (hcof : Ordinal.cof ζ.ord = aleph0)
    (hclosed : ∀ σ, aleph0 ≤ σ → σ < ζ → D.t σ < ζ) :
    Categorical K ζ ∧
    ∀ {α : Type u} (M N : Model K.τ) (xs : α → M.carrier) (ys : α → N.carrier)
      (hM : K.Mem M) (hN : K.Mem N),
      #α < ζ → Model.card M = ζ → Model.card N = ζ →
      (∃ σ, ∃ hα : #α ≤ σ, ∃ _hσ : aleph0 ≤ σ,
          ∃ hMcard : D.t σ ≤ Model.card M, ∃ hNcard : D.t σ ≤ Model.card N,
        D.same hα hM hN hMcard hNcard xs ys) →
      ∃ e : M.carrier ≃[K.τ] N.carrier, ∀ i, e (xs i) = ys i := by
  sorry

/-- **Lemma 4.5** (Orbits over parameters). If `χ ^ σ = χ` and `χ` is at least `ℓ + 2^{2^σ}`,
then at every sufficiently large categoricity cardinal there are at most `χ` automorphism
orbits of `σ`-tuples over any parameter set of size at most `χ`. -/
theorem lemma_4_5 (K : AbstractElementaryClass.{u}) (σ χ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hpow : χ ^ σ = χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) :
    ∃ κ0 : Cardinal.{u}, ∀ κ, κ0 ≤ κ → Categorical K κ →
      ∀ (M : Model K.τ), K.Mem M → Model.card M = κ →
        ∀ P : Set M.carrier, #P ≤ χ →
          ∀ {ι : Type u}, #ι ≤ σ →
            ∃ reps : Set (ι → M.carrier), #reps ≤ χ ∧
              ∀ xs : ι → M.carrier, ∃ ys ∈ reps,
                ∃ e : M.carrier ≃[K.τ] M.carrier,
                  K.Strong e.toEmbedding ∧ (∀ p ∈ P, e p = p) ∧ ∀ i, e (xs i) = ys i := by
  sorry

/-- A family of disjoint adjacent block pairs, swapped by an order automorphism and fixing
every position outside those blocks. **Lemma 4.6.** -/
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

/-- **Lemma 4.6** (Disjoint block transpositions). Swapping, in each of a family of disjoint
convex regions, the adjacent block used only by the first term family with the block used
only by the second, leaves the joint natural diagram unchanged. -/
theorem lemma_4_6 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) {I : Type u} [LinearOrder I] [Nonempty I]
    {α β : Type u} (σ : Cardinal.{u}) (hjoint : #(α ⊕ β) ≤ σ)
    (t : α → SupportTerm E.lab E.arity I) (s : β → SupportTerm E.lab E.arity I)
    (B : DisjointBlockSwap I)
    (ht : ∀ a (i : Fin (E.arity (t a).label)) p, p ∈ B.blocks →
      (t a).pos i ∈ p.1 ∨ (t a).pos i ∈ p.2 → (t a).pos i ∈ p.1)
    (hs : ∀ b (i : Fin (E.arity (s b).label)) p, p ∈ B.blocks →
      (s b).pos i ∈ p.1 ∨ (s b).pos i ∈ p.2 → (s b).pos i ∈ p.2) :
    SameNaturalDiagram K E D σ hjoint (Sum.elim t s)
      (Sum.elim (fun a => SupportTerm.along B.swap.toOrderEmbedding (t a))
        (fun b => SupportTerm.along B.swap.toOrderEmbedding (s b))) := by
  sorry

/-- **Lemma 4.7** (Ordinal-vector witnesses). Let `C` be a set, and let `U` be a definable
class of functions `C → Ord`, with fixed set parameters allowed in its definition. There is a
set `U₀ ⊆ U` such that each `u ∈ U` dominates some `v ∈ U₀` coordinatewise. -/
theorem lemma_4_7 {C parameter : Type u}
    (holds : parameter → (C → _root_.Ordinal.{u}) → Prop) (a : parameter) :
    ∃ (ι : Type u) (v : ι → C → _root_.Ordinal.{u}),
      (∀ i, holds a (v i)) ∧
      ∀ f, holds a f → ∃ i, ∀ c, v i c ≤ f c := by
  sorry

/-- **Proposition 4.8** (Uniform testing of placed comparisons). There is a nondecreasing
infinite cardinal function `g` such that two placements of a tuple of length at most `σ`
over `E(I)` whose placed comparisons differ already have different natural diagrams over some
parameter set of size at most `g(σ)`. -/
theorem proposition_4_8 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) :
    ∃ g : Cardinal.{u} → Cardinal.{u},
      (∀ σ τ, σ ≤ τ → g σ ≤ g τ) ∧ (∀ σ, aleph0 ≤ g σ) ∧
      ∀ {I : Type u} [LinearOrder I] [Nonempty I] [WellFoundedLT I]
        {α : Type u} (σ : Cardinal.{u}) (hσ : #α ≤ σ)
        (t s : α → SupportTerm E.lab E.arity I),
        ¬ SameNaturalDiagram K E D σ hσ t s →
        ∃ X : Set I, ∃ hX : X.Nonempty, #X ≤ g σ ∧
          DiagramsDifferOnSubset K E D σ hσ X hX := by
  sorry

/-- **Proposition 4.9** (Compact placement). Coherent prescriptions of joint diagrams of a
tuple of length at most `σ` with every parameter set of size at most `χ`, where
`χ ^ σ = χ` and `χ > ℓ + σ`, are realized by one placement over `I`. -/
theorem proposition_4_9 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) {I : Type u} [LinearOrder I] [Nonempty I] [WellFoundedLT I]
    {α : Type u} (σ χ : Cardinal.{u}) (hσ : #α ≤ σ) (hχ : ls K + σ < χ)
    (hpow : χ ^ σ = χ) (hI : K.Mem (E.obj I))
    (q : ∀ {β : Type u}, #β ≤ χ → (β → (E.obj I).carrier) → α ⊕ β → (E.obj I).carrier) :
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (f : I ↪o J)
      (z : α → (E.obj J).carrier) (hJ : K.Mem (E.obj J)),
      ∀ {β : Type u} (hβ : #β ≤ χ) (p : β → (E.obj I).carrier)
        (hjoint : #(α ⊕ β) ≤ σ + χ)
        (hcardI : D.t (σ + χ) ≤ Model.card (E.obj I))
        (hcardJ : D.t (σ + χ) ≤ Model.card (E.obj J)),
        D.same hjoint hJ hJ hcardJ hcardJ
          (Sum.elim z (fun b => E.map f (p b)))
          (Sum.elim (fun a => E.map f (q hβ p (Sum.inl a)))
            (fun b => E.map f (q hβ p (Sum.inr b)))) := by
  sorry

/-- **Lemma 4.10** (Unique lifts of bounded diagrams). At a strong limit `μ > ℓ` of countable
cofinality strictly closed under `t` and `g`, the diagrams of a bounded tuple in `B` over
bounded subsets of `A = E(I)` lift to one placed comparison over `A`, uniquely as a comparison
diagram. -/
theorem lemma_4_10 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) (g : Cardinal.{u} → Cardinal.{u})
    (μ σ : Cardinal.{u}) (hμ : IsClosurePoint {D.t, g} μ) (hσ : σ < μ)
    (hℓ : ls K < μ) {I : Type u} [LinearOrder I] [Nonempty I] [WellFoundedLT I]
    (hI : #I = μ) (Aeq : K.Mem (E.obj I))
    (B : Model K.τ) (incl : Language.Embedding K.τ (E.obj I).carrier B.carrier)
    (hB : K.Mem B) (hstrong : K.Strong incl) (hcard : Model.card B = μ)
    {α : Type u} (d : α → B.carrier) (hα : #α ≤ σ) :
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (f : I ↪o J)
      (z : α → (E.obj J).carrier) (hJ : K.Mem (E.obj J)),
      (∀ {β : Type u} (p : β → (E.obj I).carrier)
          (hjoint : #(α ⊕ β) ≤ μ)
          (hBcard : D.t μ ≤ Model.card B) (hJcard : D.t μ ≤ Model.card (E.obj J)),
          D.same hjoint hB hJ hBcard hJcard
            (Sum.elim d (fun b => incl (p b)))
            (Sum.elim z (fun b => E.map f (p b)))) ∧
      ∀ {J' : Type u} [LinearOrder J'] [Nonempty J'] (f' : I ↪o J')
        (z' : α → (E.obj J').carrier) (hJ' : K.Mem (E.obj J')),
        (∀ {β : Type u} (p : β → (E.obj I).carrier)
            (hjoint : #(α ⊕ β) ≤ μ)
            (hBcard : D.t μ ≤ Model.card B) (hJcard : D.t μ ≤ Model.card (E.obj J')),
            D.same hjoint hB hJ' hBcard hJcard
              (Sum.elim d (fun b => incl (p b)))
              (Sum.elim z' (fun b => E.map f' (p b)))) →
        ∀ {β : Type u} (p : β → (E.obj I).carrier)
          (hjoint : #(α ⊕ β) ≤ μ)
          (hJcard : D.t μ ≤ Model.card (E.obj J))
          (hJ'card : D.t μ ≤ Model.card (E.obj J')),
          D.same hjoint hJ hJ' hJcard hJ'card
            (Sum.elim z (fun b => E.map f (p b)))
            (Sum.elim z' (fun b => E.map f' (p b))) := by
  sorry

/-- **Theorem 4.11** (Amalgamation at closed levels). An unbounded class of strong-limit
cardinals of countable cofinality, strictly closed under `t` and `g`, consists of
categoricity cardinals at which `μ`-extensions of a `μ`-model amalgamate, tuples amalgamate
exactly when their diagrams agree up to `g(σ)`, and there are at most `μ` singleton types. -/
theorem theorem_4_11 (K : AbstractElementaryClass.{u}) (D : StableDiagram K)
    (g : Cardinal.{u} → Cardinal.{u}) (hg : ∀ σ τ, σ ≤ τ → g σ ≤ g τ) :
    ∃ S : Set Cardinal.{u},
      (∀ κ, ∃ μ, κ ≤ μ ∧ μ ∈ S) ∧
      (∀ μ ∈ S, IsClosurePoint {D.t, g} μ) ∧
      ∀ μ ∈ S,
        Categorical K μ ∧
        (∀ (A B₀ B₁ : Model K.τ)
            (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
            (f₁ : Language.Embedding K.τ A.carrier B₁.carrier),
            K.Mem A → K.Mem B₀ → K.Mem B₁ → K.Strong f₀ → K.Strong f₁ →
            Model.card A = μ → Model.card B₀ = μ → Model.card B₁ = μ →
            ∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
              (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
              K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧ Model.card P = μ ∧
              ∀ x, g₀ (f₀ x) = g₁ (f₁ x)) ∧
        (∀ σ, σ < μ → ∀ {α β : Type u} (hα : #α ≤ σ) (_hβ : #β ≤ g σ)
            (A B₀ B₁ : Model K.τ)
            (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
            (f₁ : Language.Embedding K.τ A.carrier B₁.carrier)
            (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier)
            (hA : K.Mem A) (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁),
            K.Strong f₀ → K.Strong f₁ →
            Model.card A = μ → Model.card B₀ = μ → Model.card B₁ = μ →
            ((∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
                (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
                K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧
                (∀ x, g₀ (f₀ x) = g₁ (f₁ x)) ∧ ∀ i, g₀ (d₀ i) = g₁ (d₁ i)) ↔
              (∀ (p : β → A.carrier) (hjoint : #(α ⊕ β) ≤ μ)
                  (h₀ : D.t μ ≤ Model.card B₀) (h₁ : D.t μ ≤ Model.card B₁),
                D.same hjoint hB₀ hB₁ h₀ h₁
                  (Sum.elim d₀ (fun b => f₀ (p b)))
                  (Sum.elim d₁ (fun b => f₁ (p b)))))) ∧
        (∀ (A : Model K.τ), K.Mem A → Model.card A = μ →
          ∃ code : A.carrier → μ.ord.ToType,
            ∀ x y, code x = code y ↔
              ∃ (P : Model K.τ) (g₀ g₁ : Language.Embedding K.τ A.carrier P.carrier),
                K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧
                (∀ a, g₀ a = g₁ a) ∧ g₀ x = g₁ y) := by
  sorry

end
end AEC
