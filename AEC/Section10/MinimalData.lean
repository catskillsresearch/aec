module

public import AEC.Section1.AbstractElementaryClass

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- **Proposition 10.2** and **Definition 10.3.** The chosen minimal type: a model `M₀` of size
`λ₀` and a nonalgebraic singleton type `p₀` over it with exactly one nonalgebraic extension to
any model of size `λ₀`. `realizes` is membership in `P`, read in the model where the point lives.
`productCopies` is a finite product of copies of `p₀`. -/
structure MinimalData (K : AbstractElementaryClass.{u}) where
  lam0 : Cardinal.{u}
  M0 : Model K.τ
  inM0 : K.Mem M0
  card_eq : Model.card M0 = lam0
  realizes : (M : Model K.τ) → Language.Embedding K.τ M0.carrier M.carrier → M.carrier → Prop
  productCopies : (M : Model K.τ) → Language.Embedding K.τ M0.carrier M.carrier →
    List M.carrier → Prop
  nonalgebraic : ∀ a : M0.carrier, ¬ realizes M0 (Language.Embedding.refl K.τ M0.carrier) a
  singleton : ∀ (M : Model K.τ) (f : Language.Embedding K.τ M0.carrier M.carrier) (a : M.carrier),
    productCopies M f [a] ↔ realizes M f a
  empty : ∀ (M : Model K.τ) (f : Language.Embedding K.τ M0.carrier M.carrier),
    productCopies M f []
  exists_ext : ∀ (A : Model K.τ) (f : Language.Embedding K.τ M0.carrier A.carrier),
    K.Mem A → K.Strong f → Model.card A = lam0 →
    ∃ (N : Model K.τ) (g : Language.Embedding K.τ A.carrier N.carrier) (a : N.carrier),
      K.Mem N ∧ K.Strong g ∧ Model.card N = lam0 ∧ realizes N (g.comp f) a ∧ ∀ b, g b ≠ a
  unique_ext : ∀ (A : Model K.τ) (f : Language.Embedding K.τ M0.carrier A.carrier)
    (N1 N2 : Model K.τ)
    (g1 : Language.Embedding K.τ A.carrier N1.carrier)
    (g2 : Language.Embedding K.τ A.carrier N2.carrier)
    (a1 : N1.carrier) (a2 : N2.carrier),
    K.Mem A → K.Strong f → Model.card A = lam0 →
    K.Mem N1 → K.Mem N2 → K.Strong g1 → K.Strong g2 →
    realizes N1 (g1.comp f) a1 → realizes N2 (g2.comp f) a2 →
    (∀ b, g1 b ≠ a1) → (∀ b, g2 b ≠ a2) →
    ∃ (N : Model K.τ) (h1 : Language.Embedding K.τ N1.carrier N.carrier)
      (h2 : Language.Embedding K.τ N2.carrier N.carrier),
      K.Mem N ∧ h1 a1 = h2 a2 ∧ ∀ x, h1 (g1 x) = h2 (g2 x)
  /-- The stabilized diagram `Δ` of a fixed enumeration of `M₀`. -/
  Delta : (M : Model K.τ) → Language.Embedding K.τ M0.carrier M.carrier → Prop
  Delta_base : Delta M0 (Language.Embedding.refl K.τ M0.carrier)

end
end AEC
