module

public import AEC.Section8.Lemma83Assembly
public import AEC.Section7.TiedDescent

@[expose] public section

/-!
# Lemma 8.3 (P.scheme): "the actual sample pair is all-dominated" — isolation descends to pairs

English (proof of Lemma 8.3, "The actual sample pair is all-dominated"): "Apply Lemma 7.6 to (7);
its fragment bound is below λ by closure. It follows that tp(b, c/X_H) is isolated relative to b."
Here (7) is the statement that the type of the image `u_* = (b', c')` over the larger base is the
(tied) free extension of `tp(u/X_H)`.

`infra_83_isolation_descend_pair`: for an arrow of pairs `(X ≤ Y) → (X' ≤ Y')` at one level (of
the Lemma 7.6 tail for the bound `σ`) carrying the tuple `b` to the mark `b'`, with `Y'`
all-dominated over `X' + b'`, every `σ`-bounded tuple `c` from `Y` whose image lift is tied-free
(the (7) hypothesis) has `tp(b, c / X)` isolated relative to `b`.
-/

universe u

open Cardinal FirstOrder
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Isolation descends along an arrow of pairs (Lemma 7.6 applied to (7)).** -/
theorem infra_83_isolation_descend_pair (P : SingleModelData K) (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (X Y X' Y' : P.scheme.Object μ (Tail.mem hT hμ))
        (incl : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y))
        (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem _ X')
          (P.scheme.asSystem _ Y'))
        (onX : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ X'))
        (onY : SystemArrow K oneVertexShape (P.scheme.asSystem _ Y) (P.scheme.asSystem _ Y')),
        SystemArrow.comp incl onY = SystemArrow.comp onX incl' →
        ∀ {bIdx cIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y))
          (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y))
          (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y')),
          (∀ i, onY.mapOcc (b i) = b' i) →
          #(bIdx ⊕ cIdx) ≤ σ → #cIdx < μ →
          AllDominated incl' trivial bIdx b' →
          IsTiedFree onX (asTuple incl trivial (seqJoint b c))
            (asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j))))
            (Equiv.refl _) →
          IsRelativelyIsolated (asTuple incl trivial (seqJoint b c)) (Equiv.refl _) := by
  obtain ⟨T, hT, H⟩ := lemma_7_6_tied P σ hσ
  refine ⟨T, hT, fun μ hμ X Y X' Y' incl incl' onX onY hcomm bIdx cIdx b c b' hb hcard hc
    hdom htied => ?_⟩
  have hIso := hdom cIdx (fun j => onY.mapOcc (c j)) hc
  have hSGT : SameGaloisType (asTuple incl trivial (seqJoint b c))
      ((asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j)))).restrict onX trivial)
      (Equiv.refl _) (Equiv.refl _) := by
    refine ⟨μ, Tail.mem hT hμ, Y', onY, SystemArrow.refl _, trivial, trivial, fun v => ?_,
      fun s => ?_⟩
    · exact congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex v) hcomm
    · rcases s with i | j
      · exact hb i
      · rfl
  exact H μ hμ X X' onX trivial (asTuple incl trivial (seqJoint b c))
    (asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j)))) (Equiv.refl _)
    (Equiv.refl (bIdx ⊕ cIdx)) rfl rfl hcard hSGT htied hIso

/-- **All-domination descends along an arrow of pairs given (7) for every bounded tuple.** At a
level `μ` closed for Lemma 7.6 at every infinite bound below `μ`, if `(onX, onY)` is an arrow of
pairs at level `μ` carrying `b` to the mark `b'` of a pair all-dominated over `X' + b'`, and every
bounded tuple `c` from `Y` has a tied-free lift (the free-extension statement (7) of the proof of
Lemma 8.3), then `Y` is all-dominated over `X + b`. -/
theorem infra_83_dominated_descend_pair (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible)
    (hlev : ∀ σ : Cardinal.{u}, ℵ₀ ≤ σ → σ < μ →
      μ ∈ infra_73_tailSet P (infra_76_sigma2 P σ))
    {X Y X' Y' : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X') (P.scheme.asSystem hμ Y'))
    (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ X'))
    (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ Y'))
    (hcomm : SystemArrow.comp incl onY = SystemArrow.comp onX incl')
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y'))
    (hb : ∀ i, onY.mapOcc (b i) = b' i) (hbμ : #bIdx < μ)
    (hdom : AllDominated incl' trivial bIdx b')
    (htied : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      #cIdx < μ →
      IsTiedFree onX (asTuple incl trivial (seqJoint b c))
        (asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j)))) (Equiv.refl _)) :
    AllDominated incl trivial bIdx b := by
  intro cIdx c hc
  have hlt : ℵ₀ < μ := P.aleph0_lt hμ
  have hsum : #(bIdx ⊕ cIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hlt.le hbμ hc
  set σ : Cardinal.{u} := max ℵ₀ #(bIdx ⊕ cIdx)
  have hσ : ℵ₀ ≤ σ := le_max_left _ _
  have hσμ : σ < μ := max_lt hlt hsum
  have hIso := hdom cIdx (fun j => onY.mapOcc (c j)) hc
  have hSGT : SameGaloisType (asTuple incl trivial (seqJoint b c))
      ((asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j)))).restrict onX trivial)
      (Equiv.refl _) (Equiv.refl _) := by
    refine ⟨μ, hμ, Y', onY, SystemArrow.refl _, trivial, trivial, fun v => ?_, fun s => ?_⟩
    · exact congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex v) hcomm
    · rcases s with i | j
      · exact hb i
      · rfl
  exact infra_76_tied_descent P σ hσ (hlev σ hσ hσμ) onX trivial
    (asTuple incl trivial (seqJoint b c))
    (asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j)))) (Equiv.refl _)
    (Equiv.refl (bIdx ⊕ cIdx)) rfl rfl (le_max_right _ _) hSGT (htied cIdx c hc) hIso

end AEC
