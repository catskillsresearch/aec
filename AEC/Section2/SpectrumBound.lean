module

public import AEC.Section2.CategoricitySpectrum
public import AEC.Section1.CategoricalTail
public import AEC.Section1.UnboundedCategoricity
public import AEC.Section1.LoewenheimSkolem

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- The bound `b_c` of Proposition 2.3. If the spectrum is bounded, `b_c` is the least
infinite cardinal strictly above every categoricity cardinal. If the spectrum is
unbounded, `b_c` is the least infinite cardinal from which the class is categorical. -/
def spectrumBoundSet (K : AbstractElementaryClass.{u}) : Set Cardinal.{u} :=
  {κ | aleph0 ≤ κ ∧
    ((SpectrumBounded K ∧ ∀ μ ∈ categoricitySpectrum K, μ < κ) ∨
      (¬ SpectrumBounded K ∧ ∀ μ, κ ≤ μ → Categorical K μ))}

noncomputable def spectrumBound (K : AbstractElementaryClass.{u}) : Cardinal.{u} :=
  sInf (spectrumBoundSet K)

theorem spectrumBoundSet_nonempty (K : AbstractElementaryClass.{u})
    (hqual : CategoricalUnbounded K → CategoricalOnTail K) :
    (spectrumBoundSet K).Nonempty := by
  by_cases h : SpectrumBounded K
  · obtain ⟨κ₀, hκ₀⟩ := h.bound
    refine ⟨max aleph0 (Order.succ κ₀), le_max_left _ _, Or.inl ⟨h, ?_⟩⟩
    intro μ hμ
    have hle := hκ₀ μ hμ
    have hlt := Order.lt_succ_of_le hle
    exact hlt.trans_le (le_max_right _ _)
  · have hunb : CategoricalUnbounded K := by
      refine ⟨?_⟩
      intro κ
      by_contra! hle
      have hbdd : SpectrumBounded K := ⟨κ, fun μ hμ => by
        by_contra! hgt
        exact hle μ hgt.le hμ⟩
      exact h hbdd
    obtain ⟨μ₀, hμ₀⟩ := (hqual hunb).tail
    refine ⟨max aleph0 μ₀, le_max_left _ _, Or.inr ⟨h, ?_⟩⟩
    intro μ hμ
    exact hμ₀ μ ((le_max_right _ _).trans hμ)

theorem spectrumBound_mem (K : AbstractElementaryClass.{u})
    (hqual : CategoricalUnbounded K → CategoricalOnTail K) :
    spectrumBound K ∈ spectrumBoundSet K :=
  csInf_mem (spectrumBoundSet_nonempty K hqual)

theorem spectrumBound_ge_aleph0 (K : AbstractElementaryClass.{u})
    (hqual : CategoricalUnbounded K → CategoricalOnTail K) :
    aleph0 ≤ spectrumBound K :=
  (spectrumBound_mem K hqual).1

theorem categorical_of_ge_spectrumBound (K : AbstractElementaryClass.{u})
    (hqual : CategoricalUnbounded K → CategoricalOnTail K)
    {κ : Cardinal.{u}} (hκ : spectrumBound K ≤ κ) (hcat : Categorical K κ) :
    ∀ κ', spectrumBound K ≤ κ' → Categorical K κ' := by
  have hmem := spectrumBound_mem K hqual
  dsimp [spectrumBoundSet] at hmem
  obtain ⟨_, ⟨_hbounded, hlt⟩ | ⟨_hunbounded, htail⟩⟩ := hmem
  · have h_in : κ ∈ categoricitySpectrum K := hcat
    have h_lt := hlt κ h_in
    exact (lt_irrefl _ (h_lt.trans_le hκ)).elim
  · intro κ' hκ'
    exact htail κ' hκ'

end
end AEC
