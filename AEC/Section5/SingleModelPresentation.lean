module

public import AEC.Section5.SingleModelPackage
public import AEC.Section5.PresentationClause

@[expose] public section

/-!
# Definition 5.2(2) for the single-model scheme (Proposition 5.6)

The order presentation `E` is the finite-support term data of `P.template`; `E(I)` coded on
the carrier of `#I` is the presentation object; `E(f)` transported along the codings is an
arrow (all strong maps are permitted); and by categoricity every object at `μ` is
isomorphic to the presentation on the well-order `μ.ord.ToType`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

namespace SingleModelData

variable {P : SingleModelData K}

/-- The order presentation `E` as finite-support term data of the one-vertex template. -/
noncomputable def templateFiniteSupport (P : SingleModelData K) :
    P.scheme.template.FiniteSupport where
  Lab := fun _ => P.E.lab
  arity := fun _ => P.E.arity
  realize := fun _ t => P.E.realize t
  realize_surjective := fun _ => P.E.realize_surjective
  realize_map := fun f _ t => P.E.realize_map f t
  pattern_vertex := fun _ => P.E.pattern_determines
  pattern_edge := fun h => h.elim

/-- **Definition 5.2(2) for the single-model scheme.** -/
theorem hasTermPresentations (P : SingleModelData K) : HasTermPresentations P.scheme where
  finiteSupport := ⟨P.templateFiniteSupport⟩
  present := by
    refine ⟨fun {μ} hμ I _ _ _ hI =>
        SMObject.ofModel (P.E.obj I) (P.hE I) (card_obj_eq hμ I hI),
      fun {μ} hμ I _ _ _ hI _ => SMObject.ofModelEquiv (P.E.obj I) (P.hE I)
        (card_obj_eq hμ I hI), ?_, ?_, ?_⟩
    · intro μ hμ I _ _ _ hI i j h
      exact h.elim
    · intro μ ν hμ hν I J _ _ _ _ _ _ hI hJ f
      let eI := SMObject.ofModelEquiv (P.E.obj I) (P.hE I) (card_obj_eq hμ I hI)
      let eJ := SMObject.ofModelEquiv (P.E.obj J) (P.hE J) (card_obj_eq hν J hJ)
      refine ⟨oneVertexArrow (eJ.toEmbedding.comp ((P.E.map f).comp eI.symm.toEmbedding))
        (K.strong_trans _ _
          (K.strong_trans _ _ (strong_of_equiv K eI.symm (SMObject.mem _)) (P.E.map_strong f))
          (strong_of_equiv K eJ (P.hE J))), trivial, ?_⟩
      intro v x
      show eJ (P.E.map f (eI.symm (eI x))) = eJ (P.E.map f x)
      exact congrArg (fun y => eJ (P.E.map f y)) (eI.symm_apply_apply x)
    · intro μ hμ X
      have hμ1 : ℵ₀ ≤ μ := P.aleph0_le hμ
      obtain ⟨e⟩ := exists_present_equiv hμ X (lvlOrder μ) (mk_lvlOrder hμ1)
      let eI := SMObject.ofModelEquiv (P.E.obj (lvlOrder μ)) (P.hE _)
        (card_obj_eq hμ (lvlOrder μ) (mk_lvlOrder hμ1))
      refine ⟨lvlOrder μ, inferInstance, inferInstance, inferInstance, mk_lvlOrder hμ1,
        oneVertexArrow (e.toEmbedding.comp eI.symm.toEmbedding)
          (strong_of_equiv K (e.comp eI.symm) (SMObject.mem _)), ?_⟩
      intro v
      exact (e.comp eI.symm).bijective

/-- **Proposition 5.6.** The single-model scheme is a working package (Definition 5.2,
including the presentation clause 5.2(2)). -/
theorem isWorkingPackage (P : SingleModelData K) : IsWorkingPackage P.scheme :=
  isWorkingPackage_of_core P.isWorkingPackageCore P.hasTermPresentations

end SingleModelData

end
end AEC
