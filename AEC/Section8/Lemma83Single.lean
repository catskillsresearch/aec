module

public import AEC.Section8.PairPointedSingle

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme (`infra_83_single_parts`, cycle 95)

English (Lemma 8.3): "There is a fixed set-sized finitary term template F^b such that, on a further
class of sufficiently closed eligible levels, its values on well-orders are objects of C^b. Order
embeddings give the componentwise arrows of Definition 8.1, also between such levels. Every marked
pair at a level is isomorphic to a value of this template of that size."
Proved here for `P.scheme`: the doubled template, the values, the same-size order arrows, and
every pair isomorphic to a value. The cross-level order arrows come from `infra_82_pair_extend_mixed` (Theorem 7.9 mixed
primeness), giving the full restated statement `infra_83_lemma_8_3_full_single`.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- An isomorphism of coded models gives a vertexwise bijective arrow. -/
theorem infra_83_arrow_of_equiv {μ ν : Cardinal.{u}} (X : SMObject K μ) (Y : SMObject K ν)
    (E : X.model.carrier ≃[K.τ] Y.model.carrier) :
    ∃ f : SystemArrow K oneVertexShape X.system Y.system,
      ∀ v, Function.Bijective (f.onVertex v) := by
  have hs : K.Strong E.toEmbedding := by
    have := K.transport_strong (FirstOrder.Language.Embedding.refl K.τ X.model.carrier) E
      (K.strong_refl _ X.mem)
    simpa using this
  exact ⟨⟨fun _ => E.toEmbedding, fun _ => hs, fun h => h.elim⟩, fun _ => E.bijective⟩

/-- The doubled copy of a one-vertex system: both copies are the model, joined by the identity. -/
def infra_83_doubledObject (X : SystemObject K oneVertexShape) :
    SystemObject K oneVertexShape.doubled where
  obj _ := X.obj PUnit.unit
  inK _ := X.inK PUnit.unit
  edge _ := FirstOrder.Language.Embedding.refl K.τ _
  edge_strong _ := K.strong_refl _ (X.inK PUnit.unit)

/-- The doubled copy of a one-vertex arrow. -/
def infra_83_doubledArrow {X Y : SystemObject K oneVertexShape}
    (f : SystemArrow K oneVertexShape X Y) :
    SystemArrow K oneVertexShape.doubled (infra_83_doubledObject X) (infra_83_doubledObject Y) where
  onVertex _ := f.onVertex PUnit.unit
  onVertex_strong _ := f.onVertex_strong PUnit.unit
  comm _ := FirstOrder.Language.Embedding.ext fun _ => rfl

/-- The doubled template `F^b` of a one-vertex template (base copy `inl`, extension copy `inr`). -/
def infra_83_doubledTemplate (F : TermTemplate K oneVertexShape) :
    TermTemplate K oneVertexShape.doubled where
  present I _ _ := infra_83_doubledObject (F.present I)
  onOrder f := infra_83_doubledArrow (F.onOrder f)
  onOrder_id _ x := F.onOrder_id PUnit.unit x
  onOrder_comp f g _ x := F.onOrder_comp f g PUnit.unit x

/-- **Lemma 8.3 for the Prop 5.6 scheme, clauses (1), (3) and the same-size part of (2).**
With `F^b` the doubled order-presentation template (`infra_83_doubledTemplate P.template`), on the
Theorem 7.9 tail: each well-order `I` of a tail size has a marked pair `val I` of level `#I` whose
base and extension are isomorphic to the two copies of `F^b(I)`; order embeddings between
well-orders of one size give marked arrows; and every marked pair at a tail level is isomorphic
(vertexwise bijective marked arrow) to the value of its size. The cross-level part of clause (2)
(`#I < #J`) is in `infra_83_lemma_8_3_full_single`. -/
theorem infra_83_single_parts (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∃ val : (I : Type u) → [LinearOrder I] → [WellFoundedLT I] → [Nonempty I] →
          #I ∈ T → MarkedPair K oneVertexShape P.scheme Pr,
        (∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I] (hI : #I ∈ T),
          (val I hI).μ = #I ∧
          ∀ v, Nonempty ((((infra_83_doubledTemplate P.template).present I).obj
                (Sum.inl v)).carrier ≃[K.τ]
                ((P.scheme.asSystem (val I hI).hμ (val I hI).X).obj v).carrier) ∧
              Nonempty ((((infra_83_doubledTemplate P.template).present I).obj
                (Sum.inr v)).carrier ≃[K.τ]
                ((P.scheme.asSystem (val I hI).hμ (val I hI).Y).obj v).carrier)) ∧
        (∀ (I J : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
            [LinearOrder J] [WellFoundedLT J] [Nonempty J] (_f : I ↪o J)
            (hI : #I ∈ T) (hJ : #J ∈ T), #I = #J →
          Nonempty (MarkedArrow K oneVertexShape P.scheme Pr (val I hI) (val J hJ))) ∧
        (∀ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ ∈ T →
          ∃ (I : Type u) (_ : LinearOrder I) (_ : WellFoundedLT I) (_ : Nonempty I)
            (hI : #I ∈ T), #I = M.μ ∧
            ∃ arr : MarkedArrow K oneVertexShape P.scheme Pr M (val I hI),
              (∀ v, Function.Bijective (arr.onX.onVertex v)) ∧
              ∀ v, Function.Bijective (arr.onY.onVertex v)) := by
  classical
  obtain ⟨T, hT, H⟩ := infra_82_marked_pair_exists P Pr
  have hX : ∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I] (hI : #I ∈ T),
      ∃ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ = #I := fun I _ _ _ hI => by
    obtain ⟨M, hM, -⟩ := H #I hI (SMObject.ofModel (P.E.obj I) (P.hE I)
      (SingleModelData.card_obj_eq (Tail.mem hT hI) I rfl))
    exact ⟨M, hM⟩
  let val : (I : Type u) → [LinearOrder I] → [WellFoundedLT I] → [Nonempty I] →
      #I ∈ T → MarkedPair K oneVertexShape P.scheme Pr :=
    fun I _ _ _ hI => Classical.choose (hX I hI)
  have hval : ∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I] (hI : #I ∈ T),
      (val I hI).μ = #I := fun I _ _ _ hI => Classical.choose_spec (hX I hI)
  refine ⟨T, hT, val, fun I _ _ _ hI => ⟨hval I hI, fun v => ?_⟩, ?_, ?_⟩
  · have hμe : #I ∈ P.eligible := Tail.mem hT hI
    have hcI : Model.card (P.E.obj I) = #I := SingleModelData.card_obj_eq hμe I rfl
    have hcat := SingleModelData.categorical (P := P) hμe
    exact ⟨hcat.unique_model (P.E.obj I) (val I hI).X.model (P.hE I) (val I hI).X.mem hcI
        ((val I hI).X.card.trans (hval I hI)),
      hcat.unique_model (P.E.obj I) (val I hI).Y.model (P.hE I) (val I hI).Y.mem hcI
        ((val I hI).Y.card.trans (hval I hI))⟩
  · intro I J _ _ _ _ _ _ _ hI hJ hIJ
    have hlev : (val I hI).μ = (val J hJ).μ := (hval I hI).trans (hIJ.trans (hval J hJ).symm)
    have hμe : (val I hI).μ ∈ P.eligible := (val I hI).hμ
    have hcat := SingleModelData.categorical (P := P) hμe
    obtain ⟨E⟩ := hcat.unique_model (val I hI).X.model (val J hJ).X.model (val I hI).X.mem
      (val J hJ).X.mem (val I hI).X.card ((val J hJ).X.card.trans hlev.symm)
    obtain ⟨e, -⟩ := infra_83_arrow_of_equiv (val I hI).X (val J hJ).X E
    obtain ⟨arr, -⟩ := infra_82_pair_extend_same_level P Pr (val I hI) (val J hJ) hlev e trivial
    exact ⟨arr⟩
  · intro M hM
    have : Nonempty M.μ.ord.ToType := by
      rw [← Cardinal.mk_ne_zero_iff, mk_ord_toType]
      exact (lt_of_lt_of_le Cardinal.aleph0_pos (P.aleph0_le M.hμ)).ne'
    have hI : #M.μ.ord.ToType ∈ T := by rw [mk_ord_toType]; exact hM
    refine ⟨M.μ.ord.ToType, inferInstance, inferInstance, inferInstance, hI, mk_ord_toType _, ?_⟩
    have hlev : M.μ = (val _ hI).μ := (hval _ hI).trans (mk_ord_toType _) |>.symm
    have hcat := SingleModelData.categorical (P := P) M.hμ
    obtain ⟨E⟩ := hcat.unique_model M.X.model (val _ hI).X.model M.X.mem (val _ hI).X.mem
      M.X.card ((val _ hI).X.card.trans hlev.symm)
    obtain ⟨e, he⟩ := infra_83_arrow_of_equiv M.X (val _ hI).X E
    obtain ⟨arr, harr, hbij⟩ := infra_82_iso_any P Pr M (val _ hI) e he trivial
    exact ⟨arr, fun v => harr ▸ he v, hbij⟩

/-- **Cross-level pair extension** for the Prop 5.6 scheme: an arrow of bases from a lower level
extends to a marked arrow carrying the mark entrywise. -/
theorem infra_82_pair_extend_mixed (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (M N : MarkedPair K oneVertexShape P.scheme Pr) (hlev : M.μ < N.μ)
    (e : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.X) (P.scheme.asSystem N.hμ N.X))
    (he : P.scheme.permitted (X := M.X) (Y := N.X) e) :
    ∃ arr : MarkedArrow K oneVertexShape P.scheme Pr M N, arr.onX = e := by
  classical
  obtain ⟨μ, hμ, X, Y, incl, hincl, bIdx, b, eM, hM, hdom⟩ := M
  obtain ⟨μ', hμ', X', Y', incl', hincl', bIdx', b', eN, hN, hdom'⟩ := N
  simp only at hlev e he ⊢
  obtain ⟨e0, hFL, -⟩ := Pr.along e he
  have hN' := infra_82_sameGalois_restrict e he hN
  have hlt : ℵ₀ < μ := P.aleph0_lt hμ
  have hfinB : Finite bIdx := Finite.of_equiv _ (eM.trans (Pr.arity hμ X)).symm
  have hfinB' : Finite bIdx' := Finite.of_equiv _ (eN.trans (Pr.arity hμ' X')).symm
  have hfinR : Finite (Pr.assign hμ' X').idx := Finite.of_equiv _ (Pr.arity hμ' X').symm
  have SA := infra_612_galois_trans_last_base (t1 := (Pr.assign hμ' X').restrict e he)
    (t2 := Pr.assign hμ X) (t3 := asTuple incl hincl b) (e12 := e0.symm) (e32 := eM)
    (SameGaloisType.unswap_refl hFL.symm) hM.symm ℵ₀ le_rfl hlt
    (Cardinal.lt_aleph0_of_finite (Pr.assign hμ' X').idx).le rfl
  have SB := infra_612_galois_trans_last_base (t1 := (asTuple incl' hincl' b').restrict e he)
    (t2 := (Pr.assign hμ' X').restrict e he) (t3 := asTuple incl hincl b) (e12 := eN)
    (e32 := (e0.symm.trans eM.symm).symm) hN' (SameGaloisType.swap_refl SA) ℵ₀ le_rfl hlt
    (Cardinal.lt_aleph0_of_finite bIdx').le rfl
  set τ : bIdx ≃ bIdx' := (eN.trans (e0.symm.trans eM.symm).symm.symm).symm with hτ
  have hg : P.scheme.permitted (X := X) (Y := Y') (SystemArrow.comp e incl') :=
    P.scheme.comp e incl' he hincl'
  have hGal : SameGaloisType (asTuple incl hincl b)
      (⟨μ', hμ', Y', SystemArrow.comp e incl', hg, bIdx, fun j => b' (τ j)⟩ :
        TupleOver K oneVertexShape P.scheme hμ X) (Equiv.refl _) (Equiv.refl _) := by
    rcases SB.symm with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    exact ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, fun j => hval j⟩
  obtain ⟨h, hh, hcomp, hv⟩ := infra_79_primeness_mixed P μ hμ X (asTuple incl hincl b) hfinB
    Y incl hincl b hdom (SameGaloisType.refl _) μ' hμ' Y' (SystemArrow.comp e incl') hg
    (fun j => b' (τ j)) hlev hGal
  refine ⟨⟨e, h, he, hh, hcomp, τ, fun i => ?_⟩, rfl⟩
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

/-- **Lemma 8.3 for the Prop 5.6 scheme (restated English form, all clauses).** The restated
`lemma_8_3` conclusion for `W := P.scheme` with `F^b = infra_83_doubledTemplate P.template`:
values on well-orders of tail size, marked arrows from order embeddings (same size by
`infra_82_pair_extend_same_level`, larger size by `infra_82_pair_extend_mixed`), and every marked
pair isomorphic to the value of its size. -/
theorem infra_83_lemma_8_3_full_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ F : TermTemplate K oneVertexShape.doubled, ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∃ val : (I : Type u) → [LinearOrder I] → [WellFoundedLT I] → [Nonempty I] →
          #I ∈ T → MarkedPair K oneVertexShape P.scheme Pr,
        (∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I] (hI : #I ∈ T),
          (val I hI).μ = #I ∧
          ∀ v, Nonempty (((F.present I).obj (Sum.inl v)).carrier ≃[K.τ]
                ((P.scheme.asSystem (val I hI).hμ (val I hI).X).obj v).carrier) ∧
              Nonempty (((F.present I).obj (Sum.inr v)).carrier ≃[K.τ]
                ((P.scheme.asSystem (val I hI).hμ (val I hI).Y).obj v).carrier)) ∧
        (∀ (I J : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
            [LinearOrder J] [WellFoundedLT J] [Nonempty J] (_f : I ↪o J)
            (hI : #I ∈ T) (hJ : #J ∈ T),
          Nonempty (MarkedArrow K oneVertexShape P.scheme Pr (val I hI) (val J hJ))) ∧
        (∀ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ ∈ T →
          ∃ (I : Type u) (_ : LinearOrder I) (_ : WellFoundedLT I) (_ : Nonempty I)
            (hI : #I ∈ T), #I = M.μ ∧
            ∃ arr : MarkedArrow K oneVertexShape P.scheme Pr M (val I hI),
              (∀ v, Function.Bijective (arr.onX.onVertex v)) ∧
              ∀ v, Function.Bijective (arr.onY.onVertex v)) := by
  classical
  obtain ⟨T, hT, val, h1, h2, h3⟩ := infra_83_single_parts P Pr
  refine ⟨infra_83_doubledTemplate P.template, T, hT, val, h1, ?_, h3⟩
  intro I J _ _ _ _ _ _ f hI hJ
  have hle : #I ≤ #J := Cardinal.mk_le_of_injective f.injective
  rcases hle.lt_or_eq with hlt | heq
  · have hlev : (val I hI).μ < (val J hJ).μ := by
      rw [(h1 I hI).1, (h1 J hJ).1]; exact hlt
    have hμI : #I ∈ P.eligible := Tail.mem hT hI
    have hμJ : #J ∈ P.eligible := Tail.mem hT hJ
    obtain ⟨EI⟩ := (SingleModelData.categorical (P := P) (val I hI).hμ).unique_model
      (val I hI).X.model (P.E.obj I) (val I hI).X.mem (P.hE I) (val I hI).X.card
      ((SingleModelData.card_obj_eq hμI I rfl).trans (h1 I hI).1.symm)
    obtain ⟨EJ⟩ := (SingleModelData.categorical (P := P) (val J hJ).hμ).unique_model
      (P.E.obj J) (val J hJ).X.model (P.hE J) (val J hJ).X.mem
      ((SingleModelData.card_obj_eq hμJ J rfl).trans (h1 J hJ).1.symm) (val J hJ).X.card
    let g0 := (P.template.onOrder f).onVertex PUnit.unit
    have hg0 : K.Strong g0 := (P.template.onOrder f).onVertex_strong PUnit.unit
    have hEI : K.Strong EI.toEmbedding := by
      have := K.transport_strong (FirstOrder.Language.Embedding.refl K.τ _) EI
        (K.strong_refl _ (val I hI).X.mem)
      simpa using this
    have hEJ : K.Strong EJ.toEmbedding := by
      have := K.transport_strong (FirstOrder.Language.Embedding.refl K.τ _) EJ
        (K.strong_refl _ (P.hE J))
      simpa using this
    let φ := EJ.toEmbedding.comp (g0.comp EI.toEmbedding)
    have hφ : K.Strong φ := K.strong_trans _ _ (K.strong_trans _ _ hEI hg0) hEJ
    let e : SystemArrow K oneVertexShape (P.scheme.asSystem (val I hI).hμ (val I hI).X)
        (P.scheme.asSystem (val J hJ).hμ (val J hJ).X) :=
      ⟨fun _ => φ, fun _ => hφ, fun h => h.elim⟩
    obtain ⟨arr, -⟩ := infra_82_pair_extend_mixed P Pr (val I hI) (val J hJ) hlev e trivial
    exact ⟨arr⟩
  · exact h2 I J f hI hJ heq

end AEC
