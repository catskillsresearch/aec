module

public import AEC.Section8.MarkedPair
public import AEC.Section7.RetractionPair

@[expose] public section

/-!
# Lemma 8.2, first clause for the Prop 5.6 scheme (`infra_82_marked_pair_exists`, cycle 94)

English (Lemma 8.2): "On a further tail of eligible levels, every object sits in a marked pair".
For `SingleModelData` (the scheme of Proposition 5.6) and any stationary prescription (whose marks
are finite, `arity : idx ≃ Fin n`), on the tail `infra_78_closedTail P ∩ infra_615_closed P`
every object `X` is the base of a marked pair `X ≤ Y` (with `e = id`): Theorem 7.9 at the level
(`infra_79_existence_at`) gives an all-dominated realization of the prescribed mark.
-/

universe u

open Cardinal FirstOrder
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Lemma 8.2 (1) for the Prop 5.6 scheme (proved, cycle 94).** Every object at a level of the
Theorem 7.9 tail sits in a marked pair (identity base isomorphism). -/
theorem infra_82_marked_pair_exists (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ T, ∃ hT : Tail P.scheme.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : P.scheme.Object μ (Tail.mem hT hμ)),
        ∃ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ = μ ∧
          ∃ e : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ M.X),
            P.scheme.permitted (X := X) (Y := M.X) e ∧ ∀ v, Function.Bijective (e.onVertex v) := by
  classical
  have htail := infra_79_tail P
  have hT : Tail P.eligible (infra_78_closedTail P ∩ infra_615_closed P) :=
    ⟨fun μ hμ => hμ.1.1, fun κ => by
      obtain ⟨μ, hκμ, h1, h2⟩ := htail κ
      exact ⟨μ, hκμ, h1, h2⟩⟩
  refine ⟨_, hT, fun μ hμ X => ?_⟩
  have hfin : Finite (Pr.assign (Tail.mem hT hμ) X).idx :=
    Finite.of_equiv _ (Pr.arity (Tail.mem hT hμ) X).symm
  obtain ⟨Y, f, hf, b, hAll, hS⟩ :=
    infra_79_existence_at P ⟨htail, infra_79_retraction_pair P⟩ hμ X
      (Pr.assign (Tail.mem hT hμ) X) hfin
  refine ⟨⟨μ, Tail.mem hT hμ, X, Y, f, hf, _, b, ⟨Equiv.refl _, hS.symm⟩, hAll⟩, rfl,
    SystemArrow.refl _, trivial, fun v => ?_⟩
  exact Function.bijective_id

/-- Restricting both sides of a Galois equality along a base arrow. -/
theorem infra_82_sameGalois_restrict {P : SingleModelData K} {μ ν : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {B : P.scheme.Object ν hν}
    (e : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hν B))
    (he : P.scheme.permitted (X := A) (Y := B) e)
    {t1 t2 : TupleOver K oneVertexShape P.scheme hν B} {ι : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι} (h : SameGaloisType t1 t2 e1 e2) :
    SameGaloisType (t1.restrict e he) (t2.restrict e he) e1 e2 := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, fun v => ?_, hval⟩
  have := congrArg (fun φ => φ.comp (e.onVertex v)) (hcomm v)
  exact this

/-- **Lemma 8.2 (2) for the Prop 5.6 scheme, same level (proved, cycle 94).** For marked pairs
`M`, `N` at one level and a class embedding `e : M.X → N.X` of the bases, there is an arrow of
marked pairs extending `e`: Theorem 7.9 primeness (`infra_79_primeness_same_level`) for the
all-dominated `M`, with the Galois hypothesis from `M.realizes`, the stationarity of the
prescription along `e` (the `SameGaloisType` part of `Pr.along`) and `N.realizes` restricted
along `e` (`infra_612_galois_trans_last_base`, twice). -/
theorem infra_82_pair_extend_same_level (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (M N : MarkedPair K oneVertexShape P.scheme Pr) (hlev : M.μ = N.μ)
    (e : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.X) (P.scheme.asSystem N.hμ N.X))
    (he : P.scheme.permitted (X := M.X) (Y := N.X) e) :
    ∃ arr : MarkedArrow K oneVertexShape P.scheme Pr M N, arr.onX = e := by
  classical
  obtain ⟨μ, hμ, X, Y, incl, hincl, bIdx, b, ⟨eM, hM⟩, hdom⟩ := M
  obtain ⟨μ', hμ', X', Y', incl', hincl', bIdx', b', ⟨eN, hN⟩, hdom'⟩ := N
  simp only at hlev e he ⊢
  subst hlev
  obtain ⟨e0, hFL, -⟩ := Pr.along e he
  have hN' := infra_82_sameGalois_restrict e he hN
  have hlt : ℵ₀ < μ := P.aleph0_lt hμ
  have hfinX : Finite (Pr.assign hμ X).idx := Finite.of_equiv _ (Pr.arity hμ X).symm
  have hidxX : #(Pr.assign hμ X).idx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite _).le
  have S1 := infra_612_galois_trans_last_base (t1 := Pr.assign hμ X)
    (t2 := (Pr.assign hμ' X').restrict e he)
    (t3 := (asTuple incl' hincl' b').restrict e he) (e12 := e0) (e32 := eN)
    hFL hN'.symm ℵ₀ le_rfl hlt hidxX rfl
  have hfinB : Finite bIdx := Finite.of_equiv _ (eM.trans (Pr.arity hμ X)).symm
  have hidxB : #bIdx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite _).le
  have S2 := infra_612_galois_trans_last_base (t1 := asTuple incl hincl b)
    (t2 := Pr.assign hμ X) (t3 := (asTuple incl' hincl' b').restrict e he) (e12 := eM)
    hM (SameGaloisType.swap_refl S1) ℵ₀ le_rfl hlt hidxB rfl
  set τ : bIdx ≃ bIdx' := eM.trans (e0.trans eN.symm).symm.symm with hτ
  have hg : P.scheme.permitted (X := X) (Y := Y') (SystemArrow.comp e incl') :=
    P.scheme.comp e incl' he hincl'
  have hGal : SameGaloisType (asTuple incl hincl b)
      (asTuple (SystemArrow.comp e incl') hg (fun j => b' (τ j))) (Equiv.refl _)
      (Equiv.refl _) := by
    rcases S2 with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, fun j => ?_⟩
    have := hval (τ j)
    erw [τ.symm_apply_apply j] at this
    exact this
  obtain ⟨h, hh, hcomp, hv⟩ := infra_79_primeness_same_level hμ X (asTuple incl hincl b) hfinB
    Y incl hincl b hdom (SameGaloisType.refl _) Y' (SystemArrow.comp e incl') hg
    (fun j => b' (τ j)) hGal
  refine ⟨⟨e, h, he, hh, hcomp, fun i => ⟨τ i, ?_⟩⟩, rfl⟩
  show (⟨(b i).1, h.onVertex (b i).1 (b i).2⟩ : Occurrence K oneVertexShape
    (P.scheme.asSystem hμ' Y')) = b' (τ i)
  have h1 : h.onVertex (b i).1 (b i).2 = (b' (τ i)).2 := hv i
  revert h1
  generalize b i = o1
  generalize b' (τ i) = o2
  obtain ⟨⟨⟩, x1⟩ := o1
  obtain ⟨⟨⟩, x2⟩ := o2
  intro h1
  exact congrArg (Sigma.mk PUnit.unit) h1

/-- **Lemma 8.2 for the Prop 5.6 scheme (proved, cycle 94).** The former (pre-cycle-95, weaker) Lean statement of `lemma_8_2`
with `W := P.scheme`: on the Theorem 7.9 tail every object sits in a marked pair
(`infra_82_marked_pair_exists`), and every bijective class embedding of bases extends to an arrow of
marked pairs (`infra_82_pair_extend_same_level`; a bijection of bases forces equal levels, since an
object at level `μ` has cardinality `μ`). -/
theorem infra_82_lemma_8_2_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ T, ∃ hT : Tail P.scheme.eligible T,
      (∀ μ (hμ : μ ∈ T) (X : P.scheme.Object μ (Tail.mem hT hμ)),
        ∃ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ = μ ∧
          ∃ e : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ M.X),
            P.scheme.permitted (X := X) (Y := M.X) e ∧ ∀ v, Function.Bijective (e.onVertex v)) ∧
      ∀ (M N : MarkedPair K oneVertexShape P.scheme Pr)
        (e : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.X)
          (P.scheme.asSystem N.hμ N.X)),
        M.μ ∈ T → N.μ ∈ T →
        (∀ v, Function.Bijective (e.onVertex v)) →
        P.scheme.permitted (X := M.X) (Y := N.X) e →
        ∃ arr : MarkedArrow K oneVertexShape P.scheme Pr M N, arr.onX = e := by
  obtain ⟨T, hT, H⟩ := infra_82_marked_pair_exists P Pr
  refine ⟨T, hT, H, fun M N e _ _ hbij he => ?_⟩
  have hlev : M.μ = N.μ := by
    have h1 : #M.X.model.carrier = M.μ := M.X.card
    have h2 : #N.X.model.carrier = N.μ := N.X.card
    rw [← h1, ← h2]
    exact Cardinal.mk_congr (Equiv.ofBijective _ (hbij PUnit.unit))
  exact infra_82_pair_extend_same_level P Pr M N hlev e he

/-- **Former (pre-cycle-95, weaker) Lean `lemma_8_3` statement for the Prop 5.6 scheme (proved, cycle 94).** With `F` the
scheme's template (`P.template`, the order presentation `E`): for `#I = μ` on the Theorem 7.9 tail,
the marked pair over the coded copy of `E(I)` (`infra_82_marked_pair_exists`) has its upper object
isomorphic to `E(I)`, by categoricity at the level (`SingleModelData.categorical`). Audit note: the
Lean `lemma_8_3` only asks for `F(I) ≅ M.Y`; the English template also presents the base and the
mark, and every marked pair is a value. -/
theorem infra_83_lemma_8_3_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ F : TermTemplate K oneVertexShape, ∃ T, ∃ hT : Tail P.scheme.eligible T,
      ∀ μ (hμ : μ ∈ T) (I : Type u) [LinearOrder I] [Nonempty I],
        #I = μ →
        ∃ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ = μ ∧
          ∀ v, Nonempty (((F.present I).obj v).carrier ≃[K.τ]
            ((P.scheme.asSystem M.hμ M.Y).obj v).carrier) := by
  obtain ⟨T, hT, H⟩ := infra_82_marked_pair_exists P Pr
  refine ⟨P.template, T, hT, fun μ hμ I _ _ hI => ?_⟩
  have hμe : μ ∈ P.eligible := Tail.mem hT hμ
  have hcI : Model.card (P.E.obj I) = μ := SingleModelData.card_obj_eq hμe I hI
  let X : SMObject K μ := SMObject.ofModel (P.E.obj I) (P.hE I) hcI
  obtain ⟨M, hMμ, -⟩ := H μ hμ X
  refine ⟨M, hMμ, fun v => ?_⟩
  have hcat := SingleModelData.categorical (P := P) hμe
  exact hcat.unique_model (P.E.obj I) M.Y.model (P.hE I) M.Y.mem hcI (M.Y.card.trans hMμ)

/-- **Former (pre-cycle-95, weaker) Lean `lemma_8_5` statement for the Prop 5.6 scheme (proved, cycle 94).** On the Theorem 7.9
tail, any family of at most `μ` marked pairs at level `μ` has a common upper bound: take a marked
pair `U` at `μ` (`infra_82_marked_pair_exists` over a model of size `μ`); every base `(M i).X` is
isomorphic to `U.X` by categoricity, and the isomorphism extends to an arrow of marked pairs
(`infra_82_pair_extend_same_level`). Audit note: the Lean `lemma_8_5` has no chain hypothesis and
no union clause; the English asserts that the union of an increasing chain is a marked pair. -/
theorem infra_85_lemma_8_5_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ T, ∃ hT : Tail P.scheme.eligible T,
      ∀ μ (hμ : μ ∈ T) (index : Type u) (M : index → MarkedPair K oneVertexShape P.scheme Pr),
        (∀ i, (M i).μ = μ) → #index ≤ μ →
        ∃ U : MarkedPair K oneVertexShape P.scheme Pr, U.μ = μ ∧
          ∀ i, Nonempty (MarkedArrow K oneVertexShape P.scheme Pr (M i) U) := by
  obtain ⟨T, hT, H⟩ := infra_82_marked_pair_exists P Pr
  refine ⟨T, hT, fun μ hμ index M hM _ => ?_⟩
  have hμe : μ ∈ P.eligible := Tail.mem hT hμ
  have hcat := SingleModelData.categorical (P := P) hμe
  obtain ⟨N0, hN0mem, hN0c⟩ := hcat.exists_model
  obtain ⟨U, hUμ, -⟩ := H μ hμ (SMObject.ofModel N0 hN0mem hN0c)
  refine ⟨U, hUμ, fun i => ?_⟩
  obtain ⟨φ⟩ := hcat.unique_model (M i).X.model U.X.model (M i).X.mem U.X.mem
    ((M i).X.card.trans (hM i)) (U.X.card.trans hUμ)
  let e : SystemArrow K oneVertexShape (P.scheme.asSystem (M i).hμ (M i).X)
      (P.scheme.asSystem U.hμ U.X) :=
    oneVertexArrow φ.toEmbedding (strong_of_equiv K φ (M i).X.mem)
  obtain ⟨arr, -⟩ := infra_82_pair_extend_same_level P Pr (M i) U ((hM i).trans hUμ.symm) e trivial
  exact ⟨arr⟩

end AEC
