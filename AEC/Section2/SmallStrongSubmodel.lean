module

public import AEC.Section1.LoewenheimSkolem

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- `D(M) = {A ≤K M : ‖A‖ ≤ λ}` for `λ = LS(K)`, as a class of models that embed
strongly into `M` with the stated size bound. -/
def smallStrongSubmodel (K : AbstractElementaryClass.{u}) (M : Model K.τ) :
    Set (Model K.τ) :=
  {A | ∃ f : Language.Embedding K.τ A.carrier M.carrier,
    K.Strong f ∧ Model.card A ≤ ls K}

end
end AEC
