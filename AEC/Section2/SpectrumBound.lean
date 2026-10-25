module

public import AEC.Section2.CategoricitySpectrum
public import AEC.Section1.CategoricalTail
public import AEC.Section1.LoewenheimSkolem

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- The bound `b_c` of Proposition 2.3. If the spectrum is bounded, `b_c` is the least
infinite cardinal strictly above every categoricity cardinal. If the spectrum is
unbounded, `b_c` is the least infinite cardinal from which the class is categorical. -/
noncomputable def spectrumBound (K : AbstractElementaryClass.{u}) : Cardinal.{u} :=
  sInf {κ | aleph0 ≤ κ ∧
    ((SpectrumBounded K ∧ ∀ μ ∈ categoricitySpectrum K, μ < κ) ∨
      (¬ SpectrumBounded K ∧ ∀ μ, κ ≤ μ → Categorical K μ))}

end
end AEC
