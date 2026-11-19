module

public import AEC.Section8.Lemma83TupleDescent
public import AEC.Section8.Lemma83Isolation
public import AEC.Section7.IsolationTransfer

@[expose] public section

/-!
# Lemma 8.3: all-domination from retraction images of bounded tuples only

Tuple form of `infra_83_dominated_of_retraction_pair`: the hypothesis that the retractions send
the image of the *whole* small upper object into the image of `X` is replaced by the paper's
"only images of the tested tuple have been placed in `X_H`".
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 3200000 in
/-- **All-domination from tuple retraction images (proved).** At a level `μ` closed for
Cor 6.15/6.16 and for Lemma 7.6 below `μ`, let `(onX, onY) : (X ≤ Y) → (X' ≤ Y')` be an arrow of
pairs carrying `b` to the mark `b'`, with `Y'` all-dominated over `X' + b'`, and let
`r_i : Y' → X'` (`|ι| = μ`) almost fix `X'`. If for every bounded tuple `c` of `Y` all retraction
images of `onY(b, c)` lie in `onX[X]`, then `Y` is all-dominated over `X + b`. -/
theorem infra_83_dominated_of_tuple_retractions (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμC : μ ∈ infra_615_closed P)
    (hlev : ∀ σ : Cardinal.{u}, ℵ₀ ≤ σ → σ < μ →
      μ ∈ infra_73_tailSet P (infra_76_sigma2 P σ))
    {X Y X' Y' : P.scheme.Object μ hμC.1}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 X)
      (P.scheme.asSystem hμC.1 Y))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 X')
      (P.scheme.asSystem hμC.1 Y'))
    (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 X)
      (P.scheme.asSystem hμC.1 X'))
    (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 Y)
      (P.scheme.asSystem hμC.1 Y'))
    (hcomm : SystemArrow.comp incl onY = SystemArrow.comp onX incl')
    {ι : Type u}
    (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 Y')
      (P.scheme.asSystem hμC.1 X'))
    (hιcard : #ι = μ)
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 X'),
      Finite {i : ι // (r i).onVertex a.1 (incl'.onVertex a.1 a.2) ≠ a.2})
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y'))
    (hb : ∀ i, onY.mapOcc (b i) = b' i) (hbμ : #bIdx < μ)
    (hdom : AllDominated incl' trivial bIdx b')
    (himg : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y)),
      #cIdx < μ → ∀ i (s : bIdx ⊕ cIdx), ∃ y : X.model.carrier,
        onX.onVertex (seqJoint b c s).1 y =
          (r i).onVertex (seqJoint b c s).1 (onY.onVertex (seqJoint b c s).1 (seqJoint b c s).2)) :
    AllDominated incl trivial bIdx b := by
  refine infra_83_dominated_descend_pair P hμC.1 hlev incl incl' onX onY hcomm b b' hb hbμ hdom
    (fun cIdx c hc => ?_)
  have hsum : #(bIdx ⊕ cIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_lt hμC.1).le hbμ hc
  let d : bIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y') :=
    fun s => ⟨(seqJoint b c s).1, onY.onVertex (seqJoint b c s).1 (seqJoint b c s).2⟩
  have H := infra_83_tied_from_retractions_tuple P hμC hμC le_rfl X' Y' X onX trivial incl'
    trivial r hιcard halmost d hsum (fun i s => himg cIdx c hc i s)
  have hx : d = seqJoint b' (fun j => onY.mapOcc (c j)) := by
    funext s
    rcases s with i | j
    · exact hb i
    · rfl
  have H2 := infra_78_tiedFreeMixed_host_transfer onX (asTuple incl trivial (seqJoint b c))
    ((asTuple incl' trivial d).restrict onX trivial) (asTuple incl' trivial d) (Equiv.refl _)
    onY trivial (Equiv.refl _)
    (fun x => (congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex PUnit.unit x)
      hcomm :))
    (fun k => rfl) hsum le_rfl le_rfl H
  rw [hx] at H2
  exact infra_83_tiedFree_of_mixed _ _ _ _ H2

end
end AEC
