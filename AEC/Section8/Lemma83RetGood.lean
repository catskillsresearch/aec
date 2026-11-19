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

end AEC
