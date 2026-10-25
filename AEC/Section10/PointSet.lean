module

public import AEC.Section10.MinimalData

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- **Definition 10.3.** `a ∈ P(M)` when some strong section of size `λ₀`, containing `M₀` and
`a`, computes `tp(a/M₀) = p₀`. -/
def InPointSet {K : AbstractElementaryClass.{u}} (D : MinimalData K) (M : Model K.τ)
    (incl : Language.Embedding K.τ D.M0.carrier M.carrier) (a : M.carrier) : Prop :=
  ∃ (N : Model K.τ) (f : Language.Embedding K.τ D.M0.carrier N.carrier)
    (g : Language.Embedding K.τ N.carrier M.carrier) (b : N.carrier),
    K.Mem N ∧ K.Strong f ∧ K.Strong g ∧ Model.card N = D.lam0 ∧
    g.comp f = incl ∧ g b = a ∧ D.realizes N f b

/-- A finite ordered list of distinct points of `P(M)` is independent when, in a section of size
`λ₀`, its type over `M₀` is the product of the corresponding copies of `p₀`. -/
structure FiniteIndependent {K : AbstractElementaryClass.{u}} (D : MinimalData K)
    (M : Model K.τ) (incl : Language.Embedding K.τ D.M0.carrier M.carrier)
    (xs : List M.carrier) : Prop where
  nodup : xs.Nodup
  inP : ∀ a, a ∈ xs → InPointSet D M incl a
  product : ∀ (N : Model K.τ) (f : Language.Embedding K.τ D.M0.carrier N.carrier)
    (g : Language.Embedding K.τ N.carrier M.carrier) (ys : List N.carrier),
    K.Mem N → K.Strong f → K.Strong g → Model.card N = D.lam0 → g.comp f = incl →
    ys.map g = xs → D.productCopies N f ys

end
end AEC
