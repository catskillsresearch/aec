module

public import AEC.Section8.PairOrbitSingle
public import AEC.Section7.Lemma72Mixed

@[expose] public section

/-!
# Definition 8.1 with tied freeness (P.scheme)

Cycle 97 ruling (Lars may override): in Definition 8.1, "for every arrow `X → X′` ... `p_{X′}` is
the free extension of `p_X`" is the tied notion (`IsTiedFree` / `IsTiedFreeMixed`), as in
Sections 6–7. The structure field `StationaryPrescription.along` is stated for a general working
scheme, where Lean has only the untied `IsFreeLift` (the tied notion exists only for
`SingleModelData`; generalizing it is `infra_8_general_calculus`, untouched). For `P.scheme` the
Definition 8.1 freeness is therefore the predicate `StationaryPrescription.TiedAlong`, positional
through `arity` like `CommutesWithIso`: along every permitted arrow (including a mixed-level
one) `p_{X′}` read back is `p_X` coordinate by coordinate, and `p_{X′}` is a tied free extension
of `p_X` with that matching.
-/

namespace AEC
section

universe u
open Cardinal Classical FirstOrder Function
variable {K : AbstractElementaryClass.{u}}

/-- **Definition 8.1, tied free extension along arrows (P.scheme).** -/
def StationaryPrescription.TiedAlong {P : SingleModelData K}
    (Pr : StationaryPrescription K oneVertexShape P.scheme) : Prop :=
  ∀ {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (X : P.scheme.Object ν hν) (Y : P.scheme.Object μ hμ)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f),
    SameGaloisType (Pr.assign hν X) ((Pr.assign hμ Y).restrict f hf)
      ((Pr.arity hν X).trans (Pr.arity hμ Y).symm) (Equiv.refl _) ∧
    IsTiedFreeMixed f (Pr.assign hν X) (Pr.assign hμ Y)
      ((Pr.arity hν X).trans (Pr.arity hμ Y).symm)

/-- **Mixed tied freeness under a reindexed change of the base tuple (proved).** If `p'` and
`p` (both over `A`) answer every query bounded below the level of `A` alike, `p'` read through
`ε : p'.idx ≃ p.idx`, then a mixed tied-free extension of `p` is one of `p'`, matched through `ε`. -/
theorem infra_82_tiedFreeMixed_base_equiv
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (p p' : TupleOver K oneVertexShape P.scheme hν A) (ε : p'.idx ≃ p.idx)
    (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx)
    (hD : ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      #ι < ν → P.scheme.DiagramEq (X := p'.host) (Y := p.host)
        (typeJoint (p := p') Z) (fun t => typeJoint (p := p) Z (Sum.map ε id t)))
    (hT : IsTiedFreeMixed f p qB eB) :
    IsTiedFreeMixed f p' qB (ε.trans eB) := by
  intro seq' ι Z Z0 hlong hι hιν hmv
  let seq : ApproximationSequence p :=
    { τ := #ι
      κIndex := seq'.κIndex
      family := fun i k => seq'.family i (ε.symm k)
      concat_bounded := by
        rw [← Cardinal.mk_congr (Equiv.prodCongr (Equiv.refl _) ε)]
        exact seq'.concat_bounded
      few_exceptions := fun {ι'} Z' h' => by
        have h0 := seq'.few_exceptions Z' (h'.trans hι)
        refine le_trans (Cardinal.mk_le_of_injective (f := fun s => (⟨s.1, ?_⟩ :
          {i : seq'.κIndex // ¬ P.scheme.DiagramEq (X := p'.host) (Y := A)
            (typeJoint (p := p') Z') (seqJoint (seq'.family i) Z')})) ?_) h0
        · intro hc
          apply s.2
          have d := hD Z' (h'.trans_lt hιν)
          have d1 := infra_73_scheme_comp (P.scheme.diagram_trans _ _ _ _ _ _
            (P.scheme.diagram_symm _ _ _ _ d) hc) (Sum.map ε.symm id)
          exact infra_73_diagramEq_of_eq d1
            (fun t => by cases t <;> simp [typeJoint])
            (fun t => by cases t <;> rfl)
        · intro s1 s2 h
          have h2 := congrArg Subtype.val h
          exact Subtype.ext h2 }
  have hlong' : seq.τ + ℵ₀ < #seq.κIndex :=
    show #ι + ℵ₀ < #seq'.κIndex from (add_le_add hι le_rfl).trans_lt hlong
  have hmv' : infra_78_isMoveMixed f seq Z Z0 := by
    intro i
    have h := infra_73_scheme_comp (hmv i) (Sum.map ε.symm id)
    exact infra_73_diagramEq_of_eq h (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  have T := hT seq Z Z0 hlong' le_rfl hιν hmv'
  have T' := infra_73_scheme_comp T (Sum.map ε id)
  have d := hD Z0 hιν
  have d' := P.scheme.diagram_trans _ _ _ _ _ _ d T'
  exact infra_73_diagramEq_of_eq d' (fun _ => rfl) (fun t => by cases t <;> rfl)

end
end AEC
