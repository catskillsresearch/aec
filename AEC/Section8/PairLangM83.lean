module

public import AEC.Section8.ChartRel83
public import AEC.Section8.MarkLang83

/-!
# Lemma 8.3: the pair languages with the mark constants in the `Y`-language
-/

@[expose] public section

namespace AEC
namespace LS83

universe u

open FirstOrder FirstOrder.Language Cardinal Hull83

variable {K : AbstractElementaryClass.{u}} (E : OrderPresentation K) (n : ℕ)

/-- The `Y`-language with mark constants. -/
abbrev pairLangM2 : Language.{u, u} := (pairLangR E).sum ((yLang E).sum (Mark83.markLang n))

/-- The full language. -/
abbrev pairLangM3 : Language.{u, u} :=
  ((pairLangM2 E n).sum (Lab83.labLang E)).sum Lab83.chartLang

abbrev pairInlM3 : lsLang K →ᴸ pairLangM3 E n :=
  ((LHom.sumInl : (pairLangM2 E n).sum (Lab83.labLang E) →ᴸ pairLangM3 E n).comp
    (LHom.sumInl : pairLangM2 E n →ᴸ (pairLangM2 E n).sum (Lab83.labLang E))).comp
    ((LHom.sumInl : pairLangR E →ᴸ pairLangM2 E n).comp (pairInlR E))

theorem hullStrong_pairM3 :
    HullStrong ((pairInlM3 E n).comp (lsInl K))
      (fun N _ => @LSClosed K N ((pairInlM3 E n).reduct N)) :=
  hullStrong_exp _

theorem pairLangM2_functions_le : max ℵ₀ #(Σ i, (pairLangM2 E n).Functions i) ≤ ls K :=
  sum_functions_le (pairLangR_functions_le E) (le_trans (le_max_right _ _)
    (sum_functions_le (max_le (isLSBound_ls K).1 (yLang_card_le E))
      ((Mark83.markLang_card n).trans (isLSBound_ls K).1)))

theorem pairLangM3_functions_le : max ℵ₀ #(Σ i, (pairLangM3 E n).Functions i) ≤ ls K :=
  sum_functions_le (sum_functions_le (pairLangM2_functions_le E n) (labLang_card_le E))
    (by rw [Lab83.chartLang_functions]; exact zero_le)

end LS83
end AEC
