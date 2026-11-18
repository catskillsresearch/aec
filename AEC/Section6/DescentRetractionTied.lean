module

public import AEC.Section6.AverageDescentTied
public import AEC.Section6.DescentRetraction

@[expose] public section

/-!
# Lemma 6.17 (descent through approximate retractions, tied form)

English Lemma 6.17 with "free lift" read as tied freeness across levels (`IsTiedFreeMixed`).
It lives here, not in `AEC/Section6/Results.lean`, because its proof uses Lemma 6.11 in the
tied form (`AEC/Section6/AverageDescentTied.lean`), which rests on the Section 7 tied
infrastructure, which imports `AEC.Section6.Results`.
-/

namespace AEC
section

universe u

open Cardinal

section Aux

variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 3200000 in
/-- **Descent through approximate retractions, tied form (proved).** The English proof of
Lemma 6.17: put `σ = |d| + ℵ₀`, `χ = g(σ) + LS(K) < ν` and `κ = χ⁺ < ν`; on `κ` of the indices the
restrictions `rᵢ ↾ U' : U' → A'` give a sequence `I = (rᵢ(d))` in `A'` whose pushes to `A` agree
with `tp(d/A; U)` on every query `Z ⊆ A` of size `≤ χ` off the `≤ |Z| + ℵ₀` indices that move `Z`
(arrow preservation). Lemma 6.11 (mixed levels, `infra_611_tied_mixed`) makes `tp(d/A)` tied free
over `(tp(d/A)) ↾ A'`, which is `tp(d/A'; U')` by Corollary 6.7 (the commuting square,
`infra_617_same_galois`); approximation sequences are transported along that Galois type
(`infra_611_seqTransport`). -/
theorem infra_617_tied_from_retractions
    (P : SingleModelData K)
    {ν μ : Cardinal.{u}} (hνC : ν ∈ infra_615_closed P) (hμC : μ ∈ infra_615_closed P)
    (hνμ : ν ≤ μ)
    (A : P.scheme.Object μ hμC.1) (U : P.scheme.Object μ hμC.1)
    (A' : P.scheme.Object ν hνC.1) (U' : P.scheme.Object ν hνC.1)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A') (P.scheme.asSystem hμC.1 A))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 U') (P.scheme.asSystem hμC.1 U))
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 A) (P.scheme.asSystem hμC.1 U))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A') (P.scheme.asSystem hνC.1 U'))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (htoU : P.scheme.permitted (X := U') (Y := U) toU)
    (hincl : P.scheme.permitted (X := A) (Y := U) incl)
    (hincl' : P.scheme.permitted (X := A') (Y := U') incl')
    (hsq : ∀ v, (incl.onVertex v).comp (toA.onVertex v) =
      (toU.onVertex v).comp (incl'.onVertex v))
    {ι : Type u}
    (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 U) (P.scheme.asSystem hμC.1 A))
    (hιcard : #ι = ν)
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 A),
      Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2})
    (himg : ∀ i (x : U'.model.carrier),
      ∃ y : A'.model.carrier,
        toA.onVertex PUnit.unit y = (r i).onVertex PUnit.unit (toU.onVertex PUnit.unit x))
    {dIdx : Type u}
    (d : dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 U'))
    (hd : #dIdx < ν) :
    IsTiedFreeMixed toA
      (asTuple incl' hincl' d)
      (asTuple incl hincl (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩))
      (Equiv.refl dIdx) := by
  classical
  have hν : ν ∈ P.eligible := hνC.1
  have hμ : μ ∈ P.eligible := hμC.1
  let σ : Cardinal.{u} := max #dIdx aleph0
  have hσ : aleph0 ≤ σ := le_max_right _ _
  have hσν : σ < ν := max_lt hd (P.aleph0_lt hν)
  have hidx : #dIdx ≤ σ := le_max_left _ _
  have hrecν : ν ∈ recursionClosedLevels P σ := infra_615_recursionClosed P hνC hσ hσν
  have hrecμ : μ ∈ recursionClosedLevels P σ :=
    infra_615_recursionClosed P hμC hσ (hσν.trans_le hνμ)
  have hσSuccν : Order.succ σ ≤ ν := Order.succ_le_of_lt hσν
  let χ : Cardinal.{u} := P.g σ + ls K
  have hg : P.g σ < ν := (hν.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσν
  have hχν : χ < ν := add_lt_of_lt (P.aleph0_le hν) hg (P.ls_lt hν)
  have hχinf : aleph0 ≤ χ := (isLSBound_ls K).1.trans le_add_self
  let κ : Cardinal.{u} := Order.succ χ
  have hκν : κ < ν :=
    (Order.succ_le_of_lt (cantor χ)).trans_lt (hν.1.working.strongLimit.isStrongPrelimit hχν)
  have hlen : χ + aleph0 < κ := by
    rw [add_eq_left hχinf hχinf]
    exact Order.lt_succ χ
  obtain ⟨κIndex, hκcard, e, -⟩ := infra_617_pick_subindex (ι := ι) hιcard hκν.le
  let restr : κIndex →
      SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hν A') :=
    fun k => infra_617_restr A U A' U' toA toU (r (e k)) (himg (e k))
  let I : κIndex → dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν A') :=
    fun k j => ⟨(d j).1, (restr k).onVertex (d j).1 (d j).2⟩
  let q := asTuple incl hincl (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩)
  -- the retraction images `I` have the majority estimate for the actual type over `A`
  have hmaj : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #β ≤ χ →
      #{k : κIndex // ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
        (typeJoint (p := q) Z) (seqJoint (fun j => pushOcc toA (I k j)) Z)} ≤ #β + ℵ₀ := by
    intro β Z hβ
    have hjointμ : #(dIdx ⊕ β) < μ := by
      rw [mk_sum, lift_id, lift_id]
      exact add_lt_of_lt (P.aleph0_le hμ) (hd.trans_le hνμ) ((hβ.trans_lt hχν).trans_le hνμ)
    have hgood : ∀ k : κIndex,
        (∀ b : β, (r (e k)).onVertex (Z b).1 (incl.onVertex (Z b).1 (Z b).2) = (Z b).2) →
        P.scheme.DiagramEq (X := q.host) (Y := A)
          (typeJoint (p := q) Z) (seqJoint (fun j => pushOcc toA (I k j)) Z) := by
      intro k hfix
      have hpush :=
        P.scheme.diagram_preserved q.host A (r (e k)) trivial
          (typeJoint (p := q) Z) hjointμ hjointμ
      have heq : (fun i => (r (e k)).mapOcc (typeJoint (p := q) Z i)) =
          seqJoint (fun j => pushOcc toA (I k j)) Z := by
        funext i
        cases i with
        | inl j =>
          dsimp [SystemArrow.mapOcc, pushOcc, typeJoint, seqJoint, q, I, restr]
          congr 1
          exact (infra_617_restr_comp A U A' U' toA toU (r (e k)) (himg (e k))
            (d j).2).symm
        | inr b =>
          dsimp [SystemArrow.mapOcc, pushOcc, typeJoint, seqJoint]
          congr 1
          exact hfix b
      exact heq ▸ hpush
    have hExc := infra_617_almost_id_bound' (P := P) r incl halmost Z
    refine le_trans (Cardinal.mk_le_of_injective
      (f := fun (k : {k : κIndex // ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
        (typeJoint (p := q) Z) (seqJoint (fun j => pushOcc toA (I k j)) Z)}) =>
        (⟨e k.1, by
          by_contra hnone
          exact k.2 (hgood k.1 (fun b => by
            by_contra hne
            exact hnone ⟨b, hne⟩))⟩ : {i : ι // ∃ b : β,
              (r i).onVertex (Z b).1 (incl.onVertex (Z b).1 (Z b).2) ≠ (Z b).2})) ?_) hExc
    intro k k' h
    exact Subtype.ext (e.injective (congrArg Subtype.val h))
  -- Lemma 6.11 (mixed levels) for `A' → A`
  have hTF : IsTiedFreeMixed toA (q.restrict toA htoA) q (Equiv.refl _) := by
    exact infra_611_tied_mixed P σ hσ hν hrecν hσSuccν hμ hrecμ hνμ toA htoA q rfl hidx I χ
      le_rfl hχν (by rw [hκcard]; exact hlen) (by rw [hκcard]; exact hκν) hmaj
  -- Corollary 6.7: `tp(d/A'; U')` is `(tp(toU ∘ d / A)) ↾ A'`
  have hS : SameGaloisType (asTuple incl' hincl' d) (q.restrict toA htoA) (Equiv.refl dIdx)
      (Equiv.refl dIdx) := infra_617_same_galois A U A' U' toA toU incl incl' htoA htoU hincl hincl' hsq d
  intro seq β Z Z0 hlong hβτ hβν hmv
  let seq1 := infra_611_seqTransport (t1 := asTuple incl' hincl' d)
    (t2 := q.restrict toA htoA) (Equiv.refl dIdx) hS seq #β hβτ hβν hd
  have hlong1 : seq1.τ + ℵ₀ < #seq1.κIndex := (add_le_add hβτ le_rfl).trans_lt hlong
  have hmv1 : infra_78_isMoveMixed toA seq1 Z Z0 := fun i =>
    infra_611_dEq_comp (hmv i) id (fun c => by cases c <;> rfl) (fun c => by cases c <;> rfl)
  have D1 := hTF seq1 Z Z0 hlong1 le_rfl hβν hmv1
  have hb : #(dIdx ⊕ β) < ν := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hν) hd hβν
  have D0 := infra_78_diagramEq_of_sameGalois hS Z0 (hb.trans_le (infra_611_le_nu _))
    (hb.trans_le (infra_611_le_nu _))
  have D0' := infra_611_dEq_comp D0 id
    (xs' := typeJoint (p := asTuple incl' hincl' d) Z0)
    (ys' := typeJoint (p := q.restrict toA htoA) Z0)
    (fun c => by cases c <;> rfl) (fun c => by cases c <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ D0' D1

end Aux

/-- **Lemma 6.17** (Descent through approximate retractions). Let `A ≤ U` be objects at an
eligible level `μ` and `A' ≤ U'` objects at an eligible level `ν ≤ μ`, with compatible arrows
`A' ≤ A` and `U' ≤ U`. Suppose there are arrows `(rᵢ : U → A : i < ν)` such that every `a ∈ A`
is fixed for all but finitely many `i`, and `rᵢ[U'] ⊆ A'` for all `i`. Then for every tuple `d`
in `U'` of length less than `ν`, its actual type over `A` is the free lift of `tp(d/A'; U')`.

"Free lift" is tied freeness across levels (`IsTiedFreeMixed toA (tp(d/A'; U')) (tp(d/A; U))`):
on every long approximation sequence of `tp(d/A'; U')` and every bounded query of `A` with a
mixed sequence-move into `A'`, the actual type over `A` answers with the type over `A'`
(the untied `IsFreeLift` is vacuous, `AEC/Audit/FreeFromVacuous.lean`; the old wrapper is
`lemma_6_17_untied`). Packaging as in Section 6: a tail of closed levels (`infra_615_closed`:
recursion-closed at every `σ` below the level). Proof: `infra_617_tied_from_retractions`. -/
theorem lemma_6_17 {K : AbstractElementaryClass.{u}} (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) ν (hν : ν ∈ T)
        (A : P.scheme.Object μ (Tail.mem hT hμ)) (U : P.scheme.Object μ (Tail.mem hT hμ))
        (A' : P.scheme.Object ν (Tail.mem hT hν)) (U' : P.scheme.Object ν (Tail.mem hT hν))
        (toA : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ A') (P.scheme.asSystem _ A))
        (toU : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ U') (P.scheme.asSystem _ U))
        (incl : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ A) (P.scheme.asSystem _ U))
        (incl' : SystemArrow K oneVertexShape
          (P.scheme.asSystem _ A') (P.scheme.asSystem _ U')),
        ν ≤ μ →
        (htoA : P.scheme.permitted (X := A') (Y := A) toA) →
        (htoU : P.scheme.permitted (X := U') (Y := U) toU) →
        (hincl : P.scheme.permitted (X := A) (Y := U) incl) →
        (hincl' : P.scheme.permitted (X := A') (Y := U') incl') →
        (∀ v, (incl.onVertex v).comp (toA.onVertex v) =
          (toU.onVertex v).comp (incl'.onVertex v)) →
        ∀ {ι : Type u}
          (r : ι → SystemArrow K oneVertexShape
            (P.scheme.asSystem _ U) (P.scheme.asSystem _ A)),
          #ι = ν →
          (∀ i, P.scheme.permitted (X := U) (Y := A) (r i)) →
          (∀ a : Occurrence K oneVertexShape (P.scheme.asSystem _ A),
            Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2}) →
          (∀ i (x : ((P.scheme.asSystem _ U').obj PUnit.unit).carrier),
            ∃ y, toA.onVertex PUnit.unit y =
              (r i).onVertex PUnit.unit (toU.onVertex PUnit.unit x)) →
          ∀ {dIdx : Type u}
            (d : dIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U')),
            #dIdx < ν →
            IsTiedFreeMixed toA (asTuple incl' hincl' d)
              (asTuple incl hincl
                (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩))
              (Equiv.refl dIdx) :=
  ⟨infra_615_closed P, infra_615_tail P, fun μ hμ ν hν A U A' U' toA toU incl incl'
      hνμ htoA htoU hincl hincl' hsq ι r hιcard _ halmost himg dIdx d hd =>
    infra_617_tied_from_retractions P hν hμ hνμ A U A' U' toA toU incl incl'
      htoA htoU hincl hincl' hsq r hιcard halmost himg d hd⟩

end
end AEC
