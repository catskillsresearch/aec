module

public import AEC.Section8.PairLangR83
public import AEC.Section8.HullPieces83

/-!
# Lemma 8.3: `X`-language hulls of chart points are `F(J_H)`

In a sample whose `X`-language structure keeps `X` closed and has chart generation (from
`infra_83_pairR_samples`), the term hull of finitely many `J`-skeleton points is exactly
`F(J_H)` for its chart `J_H`: "`X_H = F(J_H)`".
-/

@[expose] public section

universe u

open FirstOrder FirstOrder.Language

namespace AEC
namespace Lab83

variable {K : AbstractElementaryClass.{u}} {E : OrderPresentation K}
  {J Jp : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jp] [Nonempty Jp] (emb : J ↪o Jp)

/-- **`X_H = F(J_H)`** in a sample: the `X`-language hull of `J`-skeleton points equals the
image of `F(J_H)`, `J_H` the chart of the hull. -/
theorem hull_eq_chart (sR : (LS83.pairLangR E).Structure (E.obj Jp).carrier)
    (hX : ∀ {n} (f : (LS83.pairLangR E).Functions n) (x : Fin n → (E.obj Jp).carrier),
      (∀ i, x i ∈ Set.range (E.map emb)) →
        @Structure.funMap _ _ sR n f x ∈ Set.range (E.map emb))
    (hchart : ∀ (S : Set (E.obj Jp).carrier) [Nonempty (chart emb S)],
      (∀ {n} (f : (LS83.pairLangR E).Functions n) (x : Fin n → (E.obj Jp).carrier),
        (∀ i, x i ∈ S) → @Structure.funMap _ _ sR n f x ∈ S) →
      S ∩ Set.range (E.map emb) = Set.range (E.map (chartEmb emb S)))
    {ι : Type} [Nonempty ι] (j : ι → J) :
    ∃ _ : Nonempty (chart emb (Set.range
        (@Hull83.hullVal _ _ sR ι (fun i => E.skeleton (emb (j i)))))),
      Set.range (@Hull83.hullVal _ _ sR ι (fun i => E.skeleton (emb (j i)))) =
        Set.range (E.map (chartEmb emb (Set.range
          (@Hull83.hullVal _ _ sR ι (fun i => E.skeleton (emb (j i))))))) := by
  letI := sR
  set v : ι → (E.obj Jp).carrier := fun i => E.skeleton (emb (j i))
  set S := Set.range (Hull83.hullVal (L := LS83.pairLangR E) v)
  have hS : S = Set.range fun t : (LS83.pairLangR E).Term ι => t.realize v := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.out, (Hull83.hullVal_out v x).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Quotient.mk _ t, rfl⟩
  have hcl : ∀ {n} (f : (LS83.pairLangR E).Functions n) (x : Fin n → (E.obj Jp).carrier),
      (∀ i, x i ∈ S) → Structure.funMap f x ∈ S := by
    intro n f x hx
    rw [hS] at hx ⊢
    choose t ht using hx
    exact ⟨Term.func f t, by simp only [Term.realize, ht]⟩
  have hsub : S ⊆ Set.range (E.map emb) := by
    rw [hS]
    rintro _ ⟨t, rfl⟩
    induction t with
    | var i => exact ⟨E.skeleton (j i), E.skeleton_natural emb _⟩
    | func f ts ih => exact hX f _ ih
  have hne : Nonempty (chart emb S) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine ⟨⟨j i, ?_⟩⟩
    show v i ∈ S
    rw [hS]
    exact ⟨Term.var i, rfl⟩
  refine ⟨hne, ?_⟩
  rw [← hchart S hcl, Set.inter_eq_left.mpr hsub]

end Lab83
end AEC
