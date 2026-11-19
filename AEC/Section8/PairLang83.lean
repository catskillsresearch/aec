module

public import AEC.Section8.LSRet83
public import AEC.Section8.LabLang83

/-!
# Lemma 8.3: the pair language `τ(K)` + LS witnesses + `ret` + old template labels
-/

@[expose] public section

namespace AEC
namespace LS83

universe u

open FirstOrder FirstOrder.Language Cardinal Hull83

variable {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)

/-- The pair language. -/
abbrev pairLang : Language.{u, u} := (retLang K).sum (Lab83.labLang E)

/-- The inclusion of the LS language into the pair language. -/
abbrev pairInl : lsLang K →ᴸ pairLang E :=
  (LHom.sumInl : retLang K →ᴸ pairLang E).comp (LHom.sumInl : lsLang K →ᴸ retLang K)

/-- **Hulls are strong in the pair language** for structures with LS-closed reduct. -/
theorem hullStrong_pair :
    HullStrong ((pairInl E).comp (lsInl K))
      (fun N _ => @LSClosed K N ((pairInl E).reduct N)) :=
  hullStrong_exp _

/-- **Closed sorts in the pair language.**  A set closed under the `retLang` functions and the
label symbols is closed under all pair-language functions. -/
theorem pair_closed {N : Type u} (s₁ : (retLang K).Structure N) (s₂ : (Lab83.labLang E).Structure N)
    {R : Set N}
    (h₁ : ∀ {n} (f : (retLang K).Functions n) (x : Fin n → N), (∀ i, x i ∈ R) →
      @Structure.funMap _ N s₁ n f x ∈ R)
    (h₂ : ∀ {n} (f : (Lab83.labLang E).Functions n) (x : Fin n → N), (∀ i, x i ∈ R) →
      @Structure.funMap _ N s₂ n f x ∈ R)
    {n : ℕ} (f : (pairLang E).Functions n) (x : Fin n → N) (hx : ∀ i, x i ∈ R) :
    @Structure.funMap _ N (@Language.sumStructure _ _ _ s₁ s₂) n f x ∈ R := by
  rcases f with f | f
  · exact h₁ f x hx
  · exact h₂ f x hx

/-- **The pair language has at most `LS(K)` function symbols.** -/
theorem pairLang_functions_le : max ℵ₀ #(Σ i, (pairLang E).Functions i) ≤ ls K := by
  have hall : ℵ₀ ≤ ls K := (isLSBound_ls K).1
  have hret : #(Σ i, (retLang K).Functions i) ≤ ls K := le_trans (le_max_right _ _) retLang_functions_le
  have hlab : #(Σ i, (Lab83.labLang E).Functions i) ≤ ls K := by
    refine (mk_le_of_injective (f := fun a : (Σ i, (Lab83.labLang E).Functions i) => a.2.1)
      ?_).trans (E.lab_small.trans E.ell_eq.le)
    rintro ⟨n, a, ha⟩ ⟨m, b, hb⟩ h
    simp only at h
    subst h
    subst ha
    subst hb
    rfl
  have hsum : #(Σ i, (pairLang E).Functions i) ≤
      #((Σ i, (retLang K).Functions i) ⊕ (Σ i, (Lab83.labLang E).Functions i)) :=
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
  exact (add_le_add hret hlab).trans (by rw [add_eq_max hall, max_self])

/-- **Pair-language hulls are strong inside closed strong sorts** (e.g. `X_H ⊆ X`). -/
theorem hull_strong_in_closed_pair {N : Type u} [(pairLang E).Structure N]
    (hN : @LSClosed K N ((pairInl E).reduct N))
    {X : Model K.τ} (j : X.carrier ↪[K.τ] (red ((pairInl E).comp (lsInl K)) N).carrier)
    (hj : K.Strong j)
    (hR : ∀ {n} (f : (pairLang E).Functions n) (x : Fin n → N), (∀ i, x i ∈ Set.range j) →
      Structure.funMap f x ∈ Set.range j)
    {ι : Type} [Finite ι] [Nonempty ι] (v : ι → N) (hv : ∀ i, v i ∈ Set.range j) :
    ∃ g : (red ((pairInl E).comp (lsInl K)) (Hull (L := pairLang E) v)).carrier ↪[K.τ] X.carrier,
      K.Strong g ∧ j.comp g = redEmb ((pairInl E).comp (lsInl K)) (hullEmb (L := pairLang E) v) := by
  have hsub := hull_range_sub v hR hv
  have himg : ∀ a, ∃ b, j b = redEmb ((pairInl E).comp (lsInl K)) (hullEmb (L := pairLang E) v) a :=
    fun a => hsub ⟨a, rfl⟩
  have hcomp := factorEmbedding_comp
    (redEmb ((pairInl E).comp (lsInl K)) (hullEmb (L := pairLang E) v)) j himg
  refine ⟨factorEmbedding _ j himg, ?_, hcomp⟩
  exact K.coherence _ _ j (hullStrong_pair E N hN v) hj hcomp

/-- The pair language with a second label copy for the `Y`-sort. -/
abbrev pairLang2 : Language.{u, u} := (pairLang E).sum (Lab83.labLang E)

/-- The inclusion of the LS language into `pairLang2`. -/
abbrev pairInl2 : lsLang K →ᴸ pairLang2 E :=
  (LHom.sumInl : pairLang E →ᴸ pairLang2 E).comp (pairInl E)

/-- **Hulls are strong in `pairLang2`** for structures with LS-closed reduct. -/
theorem hullStrong_pair2 :
    HullStrong ((pairInl2 E).comp (lsInl K))
      (fun N _ => @LSClosed K N ((pairInl2 E).reduct N)) :=
  hullStrong_exp _

/-- **`pairLang2` has at most `LS(K)` function symbols.** -/
theorem pairLang2_functions_le : max ℵ₀ #(Σ i, (pairLang2 E).Functions i) ≤ ls K := by
  have hall : ℵ₀ ≤ ls K := (isLSBound_ls K).1
  have hp : #(Σ i, (pairLang E).Functions i) ≤ ls K :=
    le_trans (le_max_right _ _) (pairLang_functions_le E)
  have hlab : #(Σ i, (Lab83.labLang E).Functions i) ≤ ls K := by
    refine (mk_le_of_injective (f := fun a : (Σ i, (Lab83.labLang E).Functions i) => a.2.1)
      ?_).trans (E.lab_small.trans E.ell_eq.le)
    rintro ⟨n, a, ha⟩ ⟨m, b, hb⟩ h
    simp only at h
    subst h
    subst ha
    subst hb
    rfl
  have hsum : #(Σ i, (pairLang2 E).Functions i) ≤
      #((Σ i, (pairLang E).Functions i) ⊕ (Σ i, (Lab83.labLang E).Functions i)) :=
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
  exact (add_le_add hp hlab).trans (by rw [add_eq_max hall, max_self])

end LS83
end AEC
