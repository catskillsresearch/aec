module

public import AEC.Section8.PairLang83
public import AEC.Section8.LabRepT83

/-!
# Lemma 8.3: the pair languages with representation positions

`pairLangR` = `pairLang` + representation positions (the `X`-language), `pairLangR2` adds the
`Y`-labels, `pairLangR3` the full labels.
-/

@[expose] public section

namespace AEC
namespace LS83

universe u

open FirstOrder FirstOrder.Language Cardinal Hull83

variable {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)

/-- A sum of a small language and a label copy is small. -/
theorem sum_functions_le {L L' : Language.{u, u}} (h : max ℵ₀ #(Σ i, L.Functions i) ≤ ls K)
    (h' : #(Σ i, L'.Functions i) ≤ ls K) : max ℵ₀ #(Σ i, (L.sum L').Functions i) ≤ ls K := by
  have hall : ℵ₀ ≤ ls K := (isLSBound_ls K).1
  have hp : #(Σ i, L.Functions i) ≤ ls K := le_trans (le_max_right _ _) h
  have hsum : #(Σ i, (L.sum L').Functions i) ≤
      #((Σ i, L.Functions i) ⊕ (Σ i, L'.Functions i)) :=
    mk_le_of_injective (f := fun a => match a with
      | ⟨i, Sum.inl f⟩ => Sum.inl ⟨i, f⟩
      | ⟨i, Sum.inr f⟩ => Sum.inr ⟨i, f⟩) (by
        rintro ⟨i, f | f⟩ ⟨j, g | g⟩ h
        · simp only [Sum.inl.injEq, Sigma.mk.inj_iff] at h
          obtain ⟨rfl, h⟩ := h
          rw [eq_of_heq h]
        · simp at h
        · simp at h
        · simp only [Sum.inr.injEq, Sigma.mk.inj_iff] at h
          obtain ⟨rfl, h⟩ := h
          rw [eq_of_heq h])
  refine max_le hall (hsum.trans ?_)
  rw [mk_sum, lift_id, lift_id]
  exact (add_le_add hp h').trans (by rw [add_eq_max hall, max_self])

theorem labLang_card_le : #(Σ i, (Lab83.labLang E).Functions i) ≤ ls K := by
  refine (mk_le_of_injective (f := fun a : (Σ i, (Lab83.labLang E).Functions i) => a.2.1)
    ?_).trans (E.lab_small.trans E.ell_eq.le)
  rintro ⟨n, a, ha⟩ ⟨m, b, hb⟩ h
  simp only at h
  subst h
  subst ha
  subst hb
  rfl

/-- The `X`-language: pair language plus representation positions. -/
abbrev pairLangR : Language.{u, u} := (pairLang E).sum Lab83.repLang

abbrev pairInlR : lsLang K →ᴸ pairLangR E :=
  (LHom.sumInl : pairLang E →ᴸ pairLangR E).comp (pairInl E)

/-- The `Y`-sort additions: transported labels and transported representation positions. -/
abbrev yLang : Language.{u, u} := (Lab83.labLang E).sum Lab83.repLang

/-- The `Y`-language. -/
abbrev pairLangR2 : Language.{u, u} := (pairLangR E).sum (yLang E)

abbrev pairInlR2 : lsLang K →ᴸ pairLangR2 E :=
  (LHom.sumInl : pairLangR E →ᴸ pairLangR2 E).comp (pairInlR E)

/-- The full language. -/
abbrev pairLangR3 : Language.{u, u} := (pairLangR2 E).sum (Lab83.labLang E)

abbrev pairInlR3 : lsLang K →ᴸ pairLangR3 E :=
  (LHom.sumInl : pairLangR2 E →ᴸ pairLangR3 E).comp (pairInlR2 E)

theorem hullStrong_pairR :
    HullStrong ((pairInlR E).comp (lsInl K)) (fun N _ => @LSClosed K N ((pairInlR E).reduct N)) :=
  hullStrong_exp _

theorem hullStrong_pairR2 :
    HullStrong ((pairInlR2 E).comp (lsInl K)) (fun N _ => @LSClosed K N ((pairInlR2 E).reduct N)) :=
  hullStrong_exp _

theorem hullStrong_pairR3 :
    HullStrong ((pairInlR3 E).comp (lsInl K)) (fun N _ => @LSClosed K N ((pairInlR3 E).reduct N)) :=
  hullStrong_exp _

theorem pairLangR_functions_le : max ℵ₀ #(Σ i, (pairLangR E).Functions i) ≤ ls K :=
  sum_functions_le (pairLang_functions_le E) (Lab83.repLang_card.trans (isLSBound_ls K).1)

theorem yLang_card_le : #(Σ i, (yLang E).Functions i) ≤ ls K :=
  le_trans (le_max_right _ _) (sum_functions_le (max_le (isLSBound_ls K).1 (labLang_card_le E))
    (Lab83.repLang_card.trans (isLSBound_ls K).1))

theorem pairLangR2_functions_le : max ℵ₀ #(Σ i, (pairLangR2 E).Functions i) ≤ ls K :=
  sum_functions_le (pairLangR_functions_le E) (yLang_card_le E)

theorem pairLangR3_functions_le : max ℵ₀ #(Σ i, (pairLangR3 E).Functions i) ≤ ls K :=
  sum_functions_le (pairLangR2_functions_le E) (labLang_card_le E)

end LS83
end AEC
