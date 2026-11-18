module

public import AEC.Section7.Lemma712Common

@[expose] public section

/-!
# Finite (injective) projections of tied free lifts (cycle 92)

English (Theorem 7.13 proof): "The finite projections of a free lift are the free lifts of the
finite projections." `infra_713_tiedFree_reindex`: if `qB` over `B` is the tied free lift of `p`
along `f : A → B`, then for every injective coordinate selection `ρ` the subtuple
`qB ∘ eB ∘ ρ` is the tied free lift of `p ∘ ρ`.

Proof: let `r` be a tied free lift of `p ∘ ρ` (`infra_610_tied_free_lift`). If `r` and the
projection differed, a bounded test `Y ⊆ B` would separate them (`infra_73_differing_test`).
`infra_73_tied_move` answers `Y` by a long approximation sequence of the *full* `p` with a move
`Y₀`; its restriction along `ρ` is an approximation sequence of `p ∘ ρ`
(`ApproximationSequence.subtuple_uniform`) on which `Y₀` is still a move. Tied freeness of `qB`
(full sequence, restricted along the injective `jointReindex ρ`) and of `r` (restricted sequence)
answer `Y` identically — contradiction. Then `r`'s answers transfer to the projection.
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- The restriction of an approximation sequence along an injective coordinate selection. -/
def ApproximationSequence.project {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}
    {p : TupleOver K oneVertexShape P.scheme hμ A} (seq : ApproximationSequence p)
    {ι : Type u} (ρ : ι → p.idx) (hρ : Function.Injective ρ) :
    ApproximationSequence (p.reindex ρ) where
  τ := seq.τ
  κIndex := seq.κIndex
  family i j := seq.family i (ρ j)
  concat_bounded := by
    refine lt_of_le_of_lt ?_ seq.concat_bounded
    exact Cardinal.mk_le_of_injective
      (f := fun x : seq.κIndex × ι => (x.1, ρ x.2))
      (by
        intro a b h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1 (hρ h.2))
  few_exceptions := fun Z hZ => seq.subtuple_uniform ρ hρ Z hZ

set_option maxHeartbeats 1600000 in
/-- **Finite projections of tied free lifts (proved, cycle 92).** -/
theorem infra_713_tiedFree_reindex
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A) (hpν : p.ν = μ) (hidx : #p.idx ≤ σ)
    (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx) (hqBν : qB.ν = μ)
    (hT : IsTiedFree f p qB eB)
    {ι : Type u} (ρ : ι → p.idx) (hρ : Function.Injective ρ) :
    IsTiedFree f (p.reindex ρ) (qB.reindex (fun j => eB (ρ j))) (Equiv.refl ι) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hισ : #ι ≤ σ := (Cardinal.mk_le_of_injective hρ).trans hidx
  have hιμ : #ι < μ := hισ.trans_lt hσlt
  set q' := qB.reindex (fun j => eB (ρ j)) with hq'
  have hq'ν : q'.ν = μ := hqBν
  obtain ⟨r, er, hrν, -, hTr⟩ :=
    infra_610_tied_free_lift P σ hσ hμ hrec hσμ f hf (p.reindex ρ) hpν hισ
  have hridx : #r.idx ≤ σ := by rw [← Cardinal.mk_congr er]; exact hισ
  have hS : SameGaloisType r q' er.symm (Equiv.refl ι).symm := by
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ :=
      infra_73_differing_test P σ hσ hμ hrec hσμ r q' er.symm (Equiv.refl ι).symm hrν hq'ν
        hridx (hridx.trans_lt hσlt) hneq
    apply hnot
    obtain ⟨seq, Y0, hlong, hβτ, hβμ, hmv⟩ :=
      infra_73_tied_move P σ hσ hμ hrec hσμ f hf p hpν hidx Y hβ
    have d1 := hT seq Y Y0 hlong hβτ hβμ hmv
    have d1' : P.scheme.DiagramEq (X := p.host) (Y := qB.host)
        (typeJoint (p := p.reindex ρ) Y0) (infra_612_anchored (Equiv.refl ι) q'.incl q'.val Y) :=
      infra_73_diagramEq_of_eq (WorkingScheme.diagramEq_precomp p.host qB.host _ _
        (jointReindex (β := β) ρ) (jointReindex_injective ρ hρ) d1)
        (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    let seqR := seq.project ρ hρ
    have hmvR : infra_73_isMove f seqR Y Y0 := fun i =>
      infra_73_diagramEq_of_eq (WorkingScheme.diagramEq_precomp A B _ _
        (jointReindex (β := β) ρ) (jointReindex_injective ρ hρ) (hmv i))
        (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    have d2 := hTr seqR Y Y0 hlong hβτ hβμ hmvR
    have d := P.scheme.diagram_trans r.host p.host qB.host _ _ _
      (P.scheme.diagram_symm p.host r.host _ _ d2) d1'
    exact infra_73_diagramEq_of_eq d (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  intro seq' γ Z Z0 hlong hγ hγμ hmv
  have dL := hTr seq' Z Z0 hlong hγ hγμ hmv
  have dS := infra_72_diagramEq_of_sameGalois (P := P) hS Z hrν hq'ν hιμ hγμ
  have dS' : P.scheme.DiagramEq (X := r.host) (Y := q'.host)
      (infra_612_anchored er r.incl r.val Z)
      (infra_612_anchored (Equiv.refl ι) q'.incl q'.val Z) :=
    infra_73_diagramEq_of_eq dS (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  exact P.scheme.diagram_trans _ r.host q'.host _ _ _ dL dS'

end
end AEC
