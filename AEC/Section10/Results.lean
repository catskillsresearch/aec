module

public import AEC.Section10.PointedModel
public import AEC.Section10.Forces
public import AEC.Section10.GeomClosure
public import AEC.Section6.Results
public import AEC.Section5.Results
public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Lemma 10.1** (Preservation of nonalgebraicity). A nonalgebraic singleton type stays
nonalgebraic under free lift, including along a mixed arrow whose testing bounds lie below
the smaller level. -/
theorem lemma_10_1 (K : AbstractElementaryClass.{u}) (D : MinimalData K)
    (M N : Model K.τ) (f : Language.Embedding K.τ M.carrier N.carrier)
    (f0 : Language.Embedding K.τ D.M0.carrier M.carrier) (a : N.carrier) :
    K.Mem M → K.Mem N → K.Strong f → K.Strong f0 →
    D.realizes N (f.comp f0) a → (∀ x, f x ≠ a) →
    ∀ (P : Model K.τ) (g : Language.Embedding K.τ N.carrier P.carrier) (b : P.carrier),
      K.Mem P → K.Strong g → g a = b → ∀ x, g (f x) ≠ b := by
  sorry

/-- **Proposition 10.2** (A minimal type). There is a sufficiently closed level `λ₀`, a model
`M₀` of that size, and a nonalgebraic singleton type over `M₀` with exactly one nonalgebraic
extension to any model of size `λ₀`. -/
theorem proposition_10_2 (K : AbstractElementaryClass.{u}) :
    ∃ D : MinimalData K, aleph0 ≤ D.lam0 := by
  sorry

/-- **Lemma 10.4** (The containment test). A finite independent set fails to force `x` if and
only if `x` independently extends it. -/
theorem lemma_10_4 (K : AbstractElementaryClass.{u}) (D : MinimalData K)
    (M : Model K.τ) (incl : Language.Embedding K.τ D.M0.carrier M.carrier)
    (xs : List M.carrier) (x : M.carrier) (hI : FiniteIndependent D M incl xs) :
    ¬ Forces D M incl {y | y ∈ xs} x ↔
      IndependentlyExtends (fun s => ∃ ys : List M.carrier,
        FiniteIndependent D M incl ys ∧ ∀ z, z ∈ s ↔ z ∈ ys) x {y | y ∈ xs} := by
  sorry

/-- **Theorem 10.5** (The geometry of the minimal type). Finite closure has size at most
`λ₀`, and the closure of an infinite set of points has size at most the size of the set plus
`λ₀`. -/
theorem theorem_10_5 (K : AbstractElementaryClass.{u}) (D : MinimalData K)
    (M : Model K.τ) (incl : Language.Embedding K.τ D.M0.carrier M.carrier)
    (hM : K.Mem M) (hstrong : K.Strong incl) (hcard : D.lam0 ≤ Model.card M) :
    (∀ (F : Set M.carrier), F.Finite →
      ∀ x, InClosure (fun s => ∃ ys : List M.carrier,
        FiniteIndependent D M incl ys ∧ ∀ z, z ∈ s ↔ z ∈ ys) F x →
        ∃ t : Set M.carrier, t.Finite ∧ x ∈ t ∧ #t ≤ D.lam0) ∧
    (∀ F : Set M.carrier,
      #{x | InClosure (fun s => ∃ ys : List M.carrier,
        FiniteIndependent D M incl ys ∧ ∀ z, z ∈ s ↔ z ∈ ys) F x} ≤ #F + D.lam0) := by
  sorry

/-- **Proposition 10.6** (Pointed working levels). Above the bounds for the fixed point, the
pointed models form a categorical working scheme, and `p₀` has a unique nonalgebraic free
extension to each such model. -/
theorem proposition_10_6 (K : AbstractElementaryClass.{u}) (D : MinimalData K) :
    ∃ S : SystemShape.{u}, ∃ W : WorkingScheme K S, IsWorkingPackage W ∧
      ∀ μ (hμ : μ ∈ W.eligible) (X : W.Object μ hμ),
        ∃ P : PointedModel K D, ∃ v, P.M = (W.asSystem hμ X).obj v := by
  sorry

/-- **Proposition 10.7** (Change of base for the geometry). A finite list of points over a
pointed model is independent over `P(B)` if and only if its type is the product of the
corresponding copies of the free extension of `p₀`. -/
theorem proposition_10_7 (K : AbstractElementaryClass.{u}) (D : MinimalData K)
    (B : PointedModel K D) (xs : List B.M.carrier) :
    FiniteIndependent D B.M B.copy xs ↔ D.productCopies B.M B.copy xs := by
  sorry

/-- **Lemma 10.8** (Anchoring a singleton type). There is a fixed cardinal `β` such that any
nonalgebraic singleton type over a sufficiently closed pointed model is named by a list of
length at most `β`. -/
theorem lemma_10_8 (K : AbstractElementaryClass.{u}) (D : MinimalData K) :
    ∃ β : Cardinal.{u}, aleph0 ≤ β ∧
      ∀ (A : PointedModel K D) (a : A.M.carrier),
        D.realizes A.M A.copy a → (∀ x, A.copy x ≠ a) →
        ∃ (ι : Type u) (c : ι → A.M.carrier), #ι ≤ β ∧
          ∀ (B : PointedModel K D), D.Delta B.M B.copy →
            ∃ b : B.M.carrier, D.realizes B.M B.copy b ∧ ∀ x, B.copy x ≠ b := by
  sorry

/-- **Theorem 10.9** (No proper pair with unchanged points at one level). There is a cardinal
`λ > λ₀` at which no proper strong inclusion of pointed models of size `λ` preserves the
point set. -/
theorem theorem_10_9 (K : AbstractElementaryClass.{u}) (D : MinimalData K) :
    ∃ lam : Cardinal.{u}, D.lam0 < lam ∧
      ∀ (A B : PointedModel K D) (f : Language.Embedding K.τ A.M.carrier B.M.carrier),
        K.Strong f → f.comp A.copy = B.copy →
        Model.card A.M = lam → Model.card B.M = lam →
        (∀ x, InPointSet D A.M A.copy x ↔ ∃ y, InPointSet D B.M B.copy y ∧ f x = y) →
        Function.Surjective f := by
  sorry

/-- **Corollary 10.10** (No-growth and rank on the entire tail). Above a threshold, a strong
inclusion of pointed models with the same point set is an isomorphism, and a pointed model
larger than the threshold has point-set cardinality equal to its own cardinality. -/
theorem corollary_10_10 (K : AbstractElementaryClass.{u}) (D : MinimalData K) :
    ∃ lam : Cardinal.{u}, D.lam0 < lam ∧
      (∀ (A B : PointedModel K D) (f : Language.Embedding K.τ A.M.carrier B.M.carrier),
        K.Strong f → f.comp A.copy = B.copy → lam ≤ Model.card A.M →
        (∀ x, InPointSet D A.M A.copy x ↔ ∃ y, InPointSet D B.M B.copy y ∧ f x = y) →
        Function.Bijective f) ∧
      ∀ M : PointedModel K D, lam < Model.card M.M →
        #{x | InPointSet D M.M M.copy x} = Model.card M.M := by
  sorry

end
end AEC
