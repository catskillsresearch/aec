module

public import AEC.Section4.NaturalDiagram
public import AEC.Section4.CountableClosure
public import AEC.Section1.ArbitrarilyLarge
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

/-- **Lemma 4.1** (Canonical classes above one categoricity size). A tuple in a model of size
at least a categoricity cardinal `κ` has a class computed in any strong `κ`-submodel containing
it, and a strong embedding of models of size at least `κ` preserves that class. -/
theorem lemma_4_1 (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    (hcat : Categorical K κ) (N : Model K.τ) (hN : K.Mem N) (hcard : κ ≤ Model.card N)
    {α : Type u} (a : α → N.carrier) (hα : #α ≤ κ) :
    (∀ (M₁ M₂ : Model K.τ)
        (f₁ : Language.Embedding K.τ M₁.carrier N.carrier)
        (f₂ : Language.Embedding K.τ M₂.carrier N.carrier),
        K.Mem M₁ → K.Mem M₂ → K.Strong f₁ → K.Strong f₂ →
        Model.card M₁ = κ → Model.card M₂ = κ →
        (∀ i, ∃ x, f₁ x = a i) → (∀ i, ∃ y, f₂ y = a i) →
        ∃ e : M₁.carrier ≃[K.τ] M₂.carrier,
          K.Strong e.toEmbedding ∧
          ∀ i x y, f₁ x = a i → f₂ y = a i → e x = y) ∧
    ∀ (N' : Model K.τ) (g : Language.Embedding K.τ N.carrier N'.carrier),
      K.Mem N' → K.Strong g → κ ≤ Model.card N' →
      ∀ (M₁ M₂ : Model K.τ)
        (f₁ : Language.Embedding K.τ M₁.carrier N.carrier)
        (f₂ : Language.Embedding K.τ M₂.carrier N'.carrier),
        K.Mem M₁ → K.Mem M₂ → K.Strong f₁ → K.Strong f₂ →
        Model.card M₁ = κ → Model.card M₂ = κ →
        (∀ i, ∃ x, f₁ x = a i) → (∀ i, ∃ y, f₂ y = g (a i)) →
        ∃ e : M₁.carrier ≃[K.τ] M₂.carrier,
          K.Strong e.toEmbedding ∧
          ∀ i x y, f₁ x = a i → f₂ y = g (a i) → e x = y := by
  sorry

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

/-- **Lemma 4.7** (Ordinal-vector witnesses). A set of functions from a set into the ordinals
has a set of coordinatewise lower bounds from the same family, one under each member. The
paper obtains the family as a set from a definable class with set parameters. -/
theorem lemma_4_7 {C ι : Type u} (u : ι → C → _root_.Ordinal.{u}) :
    ∃ s : Set ι,
      (∀ j ∈ s, ∀ i, (∀ c, u i c ≤ u j c) → ∀ c, u i c = u j c) ∧
      (∀ i, ∃ j ∈ s, ∀ c, u j c ≤ u i c) := by
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
