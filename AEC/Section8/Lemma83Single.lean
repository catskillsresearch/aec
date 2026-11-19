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
every pair isomorphic to a value. The cross-level order arrows are open
(`infra_83_order_arrows_mixed`).
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
(`#I < #J`) is tracked as `infra_83_order_arrows_mixed`. -/
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

end AEC
