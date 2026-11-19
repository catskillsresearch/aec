module

public import AEC.Section8.Lemma83SampleLikeY
public import AEC.Section8.Lemma83Isolation

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: good ret codes from matches into ret-samples

In a ret-admitted sample (`RetSampleLike`) the codes are a bijection onto the base `J` and `eX`
is onto, so the codes cover the image of every match of `X_I`; the count of good evaluation
indices of `infra_83_good_codes_of_match` then needs only the `Y_I`-match and the sort
intersection.
-/

universe u

open Cardinal FirstOrder FirstOrder.Language

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Good codes from a match into a ret-sample (proved).** With the Cor 6.16 eval law,
surjective `eX`, and bijective codes onto the base `J`, the codes cover the image of every
`X_I`-match, so `infra_83_good_codes_of_match` applies with only the match `mY` of `Y_I` (in a
language with the `ret` symbol) and the sort intersection `hmeet` left: at least `#X_I` codes
send the matched `Y_I` into the matched `X_I`. -/
theorem infra_83_good_codes_of_match_ret (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {J Jplus : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jplus] [Nonempty Jplus]
    {M : MarkedPair K oneVertexShape P.scheme Pr}
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (hsurj : Function.Surjective eX) (emb : J ↪o Jplus)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jplus).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier) (hcode : Function.Bijective code)
    (G : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier)
    (heval : ∀ i y, G (P.E.map emb (code i)) (F y) =
      F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)))
    {L₀ : FirstOrder.Language.{u, u}} {XI YI : Type u} [L₀.Structure YI]
    [L₀.Structure (P.E.obj Jplus).carrier]
    (onX : XI → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (onY : YI → ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier) (inclI : XI → YI)
    (hcomm : ∀ x, onY (inclI x) = M.incl.onVertex PUnit.unit (onX x))
    (mY : YI ↪[L₀] (P.E.obj Jplus).carrier) (hmY : ∀ y, mY y = F (onY y))
    (ret : L₀.Functions 2) (hret : ∀ a b, Structure.funMap ret ![a, b] = G a b)
    (hmeet : ∀ (x' : YI) (z : ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier),
      F (onY x') = F (M.incl.onVertex PUnit.unit z) → ∃ y, x' = inclI y)
    (hFX : Function.Injective (fun x => F (M.incl.onVertex PUnit.unit (onX x)))) :
    #XI ≤ #{i : R.index // ∀ x : YI, ∃ y : XI,
      G (P.E.map emb (code i)) (F (onY x)) = F (M.incl.onVertex PUnit.unit (onX y))} := by
  refine infra_83_good_codes_of_match (M.incl.onVertex PUnit.unit) F
    (fun i y => (R.retr i).onVertex PUnit.unit y) onX onY inclI hcomm G
    (fun i => P.E.map emb (code i)) heval mY hmY ret hret hmeet hFX ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨w, hw⟩ := hsurj (onX x)
  obtain ⟨i, hi⟩ := hcode.2 w
  exact ⟨i, by simp only [hi, ← hF w, hw]⟩


/-- **Sort intersection from a set inclusion (proved).** The `hmeet` hypothesis of
`infra_83_good_codes_of_match_ret` follows from the set-level statement that the matched
`Y_I`-image meets the sample's `X`-image `F(incl(X))` only inside the matched `X_I`-image,
given that the match of `Y_I` is injective. -/
theorem infra_83_meet_of_subset {Xc Yc LL XI YI : Type u} (incl : Xc → Yc) (F : Yc → LL)
    (onX : XI → Xc) (onY : YI → Yc) (inclI : XI → YI)
    (hcomm : ∀ x, onY (inclI x) = incl (onX x))
    (hinj : Function.Injective (fun y => F (onY y)))
    (hsub : Set.range (fun y => F (onY y)) ∩ Set.range (fun z => F (incl z)) ⊆
      Set.range (fun x => F (incl (onX x)))) :
    ∀ (x' : YI) (z : Xc), F (onY x') = F (incl z) → ∃ y, x' = inclI y := by
  intro x' z h
  obtain ⟨y, hy⟩ := hsub ⟨⟨x', rfl⟩, ⟨z, h.symm⟩⟩
  refine ⟨y, hinj ?_⟩
  simp only [hcomm]
  exact hy.symm

/-- **Sort intersection from the `X`-chart (proved).** In a sample whose `X`-copy is
`F(emb)(J)` (`F ∘ incl ∘ eX = F(emb)`, `eX` onto) and whose `X`-closed sets `T` meet the
`X`-copy in `F(chart T)` (the chart clause of `XSampleLike`/`RetSampleLike`), the sort
intersection for an `X`-closed matched `Y_I`-image `T` reduces to: `F(chart T)` lies in the
matched `X_I`-image. -/
theorem infra_83_meet_of_chart (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {J Jplus : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jplus] [Nonempty Jplus]
    {M : MarkedPair K oneVertexShape P.scheme Pr}
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (hsurj : Function.Surjective eX) (emb : J ↪o Jplus)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jplus).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    {XI YI : Type u}
    (onX : XI → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (onY : YI → ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier) (inclI : XI → YI)
    (hcomm : ∀ x, onY (inclI x) = M.incl.onVertex PUnit.unit (onX x))
    (hinj : Function.Injective (fun y => F (onY y)))
    [Nonempty (Lab83.chart emb (Set.range (fun y => F (onY y))))]
    (hT : Set.range (fun y => F (onY y)) ∩ Set.range (P.E.map emb) =
      Set.range (P.E.map (Lab83.chartEmb emb (Set.range (fun y => F (onY y))))))
    (hchart : Set.range (P.E.map (Lab83.chartEmb emb (Set.range (fun y => F (onY y))))) ⊆
      Set.range (fun x => F (M.incl.onVertex PUnit.unit (onX x)))) :
    ∀ (x' : YI) (z : ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier),
      F (onY x') = F (M.incl.onVertex PUnit.unit z) → ∃ y, x' = inclI y := by
  refine infra_83_meet_of_subset _ F onX onY inclI hcomm hinj ?_
  rintro w ⟨hw1, ⟨z, rfl⟩⟩
  obtain ⟨v, rfl⟩ := hsurj z
  have hw : F (M.incl.onVertex PUnit.unit (eX v)) ∈
      Set.range (fun y => F (onY y)) ∩ Set.range (P.E.map emb) := ⟨hw1, v, (hF v).symm⟩
  rw [hT] at hw
  exact hchart hw


/-- **`X_H` as the `X`-sort of the `Y`-hull (sample level, proved).** English (Lemma 8.3 proof:
"write the resulting chart orders as `J_H` … `X_H = F(J_H)`", both directions of generation):
in an `X`-sample-like structure, the `Y`-language term hull of any family meets the `X`-copy
`F(emb)(J)` exactly in `F` of its own `X`-chart. So the `X`-sort part of the whole hull is
`F(J_H)` with `J_H` the `X`-chart points of the hull, and a `Y`-hull element in the `X` sort is
in this `X_H` by definition. -/
theorem infra_83_XH_sort_sample (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] {J Jp : Type u} [LinearOrder J] [Nonempty J]
    [LinearOrder Jp] [Nonempty Jp] (emb : J ↪o Jp) (g : N ≃ (E.obj Jp).carrier)
    (hchart : ∀ (T : Set (E.obj Jp).carrier) [Nonempty (Lab83.chart emb T)],
      (∀ {k} (f : (LS83.pairLangR E).Functions k) (x : Fin k → N), (∀ i, g (x i) ∈ T) →
        g (xFun E n f x) ∈ T) →
      T ∩ Set.range (E.map emb) = Set.range (E.map (Lab83.chartEmb emb T)))
    {ι : Type} (v : ι → N)
    [Nonempty (Lab83.chart emb
      (g '' Set.range (@Hull83.hullVal _ _ ((psiM E n).reduct N) ι v)))] :
    g '' Set.range (@Hull83.hullVal _ _ ((psiM E n).reduct N) ι v) ∩ Set.range (E.map emb) =
      Set.range (E.map (Lab83.chartEmb emb
        (g '' Set.range (@Hull83.hullVal _ _ ((psiM E n).reduct N) ι v)))) := by
  letI := (psiM E n).reduct N
  set S := Set.range (Hull83.hullVal (L := LS83.pairLangM2 E n) v)
  have hS : S = Set.range fun t : (LS83.pairLangM2 E n).Term ι => t.realize v := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.out, (Hull83.hullVal_out v x).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Quotient.mk _ t, rfl⟩
  have hcl : ∀ {k} (f : (LS83.pairLangM2 E n).Functions k) (x : Fin k → N),
      (∀ i, x i ∈ S) → yFun E n f x ∈ S := by
    intro k f x hx
    rw [hS] at hx ⊢
    choose t ht using hx
    exact ⟨Term.func f t, by simp only [Term.realize, ht]⟩
  apply hchart
  intro k f x hx
  refine ⟨_, hcl ((chiM E n).onFunction f) x fun i => ?_, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hx i
  rwa [← g.injective hyx]

end AEC
