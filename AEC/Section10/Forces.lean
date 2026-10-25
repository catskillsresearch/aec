module

public import AEC.Section10.PointSet

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- **Definition 10.3**, the containment test. `F` forces `x` when every strong image of a
size-`λ₀` section that contains `F` also contains `x`. -/
def Forces {K : AbstractElementaryClass.{u}} (D : MinimalData K) (M : Model K.τ)
    (incl : Language.Embedding K.τ D.M0.carrier M.carrier)
    (F : Set M.carrier) (x : M.carrier) : Prop :=
  ∀ (N : Model K.τ) (g : Language.Embedding K.τ N.carrier M.carrier)
    (f0 : Language.Embedding K.τ D.M0.carrier N.carrier) (b : N.carrier),
    K.Mem N → K.Strong g → K.Strong f0 → Model.card N = D.lam0 →
    g.comp f0 = incl → g b = x →
    (∀ a ∈ F, ∃ c, g c = a) →
    ∀ (W : Model K.τ) (f : Language.Embedding K.τ N.carrier W.carrier)
      (Dmod : Model K.τ) (d0 : Language.Embedding K.τ D.M0.carrier Dmod.carrier)
      (dW : Language.Embedding K.τ Dmod.carrier W.carrier),
      K.Mem W → K.Mem Dmod → K.Strong f → K.Strong dW →
      Model.card W = D.lam0 → Model.card Dmod = D.lam0 →
      f.comp f0 = dW.comp d0 →
      (∀ a ∈ F, ∀ c, g c = a → ∃ d, dW d = f c) →
      ∃ d, dW d = f b

end
end AEC
