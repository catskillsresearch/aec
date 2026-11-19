module

public import AEC.Section6.DescentRetractionTied
public import AEC.Section8.MarkedPair

@[expose] public section

/-!
# Lemma 8.3, step (7): descent through retractions for one bounded tuple

The paper's bounded-horizontal-arity step (Lemma 8.3 proof, (7)) only places the images
`r_i(u*)` of the tested tuple in the embedded `X_H`: "Only images of the tested tuple have been
placed in `X_H`; closure of the entire small upper object under these retractions is neither
claimed nor needed here." This is the tuple form of the first half of
`infra_617_tied_from_retractions`: no arrow of a whole small upper object is used.
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 3200000 in
/-- **(7) for one tuple (proved).** Let `A ≤ U` at a closed level `μ`, `toA : A' → A` from a
closed level `ν ≤ μ`, and Cor 6.16-style arrows `(r_i : U → A : i < ν)` almost fixing `A`. If
a tuple `d` of `U` with `|d| < ν` has all its retraction images `r_i(d)` in `toA[A']`, then the
actual type `tp(d/A)` is tied free over its restriction to `A'` (Lemma 6.11, mixed levels): the
paper's "`tp(u*/X)` is the free extension of `tp(u/X_H)`" once `u` is identified with `u*`. -/
theorem infra_83_tied_from_retractions_tuple
    (P : SingleModelData K)
    {ν μ : Cardinal.{u}} (hνC : ν ∈ infra_615_closed P) (hμC : μ ∈ infra_615_closed P)
    (hνμ : ν ≤ μ)
    (A : P.scheme.Object μ hμC.1) (U : P.scheme.Object μ hμC.1)
    (A' : P.scheme.Object ν hνC.1)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A') (P.scheme.asSystem hμC.1 A))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 A) (P.scheme.asSystem hμC.1 U))
    (hincl : P.scheme.permitted (X := A) (Y := U) incl)
    {ι : Type u}
    (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 U) (P.scheme.asSystem hμC.1 A))
    (hιcard : #ι = ν)
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 A),
      Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2})
    {dIdx : Type u}
    (d : dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 U))
    (hd : #dIdx < ν)
    (himg : ∀ i j, ∃ y, toA.onVertex (d j).1 y = (r i).onVertex (d j).1 (d j).2) :
    IsTiedFreeMixed toA ((asTuple incl hincl d).restrict toA htoA) (asTuple incl hincl d)
      (Equiv.refl _) := by
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
  choose y hy using himg
  let I : κIndex → dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν A') :=
    fun k j => ⟨(d j).1, y (e k) j⟩
  let q := asTuple incl hincl d
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
          dsimp [SystemArrow.mapOcc, pushOcc, typeJoint, seqJoint, q, I]
          congr 1
          exact (hy (e k) j).symm
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
  exact infra_611_tied_mixed P σ hσ hν hrecν hσSuccν hμ hrecμ hνμ toA htoA q rfl hidx I χ
    le_rfl hχν (by rw [hκcard]; exact hlen) (by rw [hκcard]; exact hκν) hmaj


set_option maxHeartbeats 3200000 in
/-- **(7) in a marked sample pair (proved).** For a marked pair `N` at a closed level `μ` with
its Cor 6.16 family `R`, an arrow `toA : A' → N.X` from a closed level `ν ≤ μ`, a tuple `d` of
`N.Y` with `|d| < ν`, and `ν` distinguished retraction indices whose images of `d` lie in
`toA[A']` (the matched positions of `r_i(u)` in the paper), `tp(d/N.X)` is tied free over its
restriction to `A'`. -/
theorem infra_83_tied_from_marked_retractions (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    (N : MarkedPair K oneVertexShape P.scheme Pr) (hμC : N.μ ∈ infra_615_closed P)
    {ν : Cardinal.{u}} (hνC : ν ∈ infra_615_closed P) (hνμ : ν ≤ N.μ)
    (R : ApproximateRetraction K oneVertexShape P.scheme N.hμ N.X N.Y N.incl)
    (A' : P.scheme.Object ν hνC.1)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A')
      (P.scheme.asSystem hμC.1 N.X))
    (htoA : P.scheme.permitted (X := A') (Y := N.X) toA)
    {dIdx : Type u}
    (d : dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 N.Y))
    (hd : #dIdx < ν) (S : Set R.index) (hS : #S = ν)
    (himg : ∀ i ∈ S, ∀ j, ∃ y, toA.onVertex (d j).1 y =
      (R.retr i).onVertex (d j).1 (d j).2) :
    IsTiedFreeMixed toA ((asTuple N.incl N.incl_arrow d).restrict toA htoA)
      (asTuple N.incl N.incl_arrow d) (Equiv.refl _) := by
  refine infra_83_tied_from_retractions_tuple P hνC hμC hνμ N.X N.Y A' toA htoA N.incl
    N.incl_arrow (fun i : S => R.retr i.1) hS (fun a => ?_) d hd (fun i j => himg i.1 i.2 j)
  haveI := R.almost_id a
  exact Finite.of_injective (β := {i : R.index // (R.retr i).onVertex a.1
    (N.incl.onVertex a.1 a.2) ≠ a.2}) (fun i => ⟨i.1.1, i.2⟩)
    (fun x y h => Subtype.ext (Subtype.ext (congrArg Subtype.val h :)))

end
end AEC
