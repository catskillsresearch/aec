module

public import AEC.Section8.Lemma83TupleDominated

@[expose] public section

/-!
# Lemma 8.3 reduced to bounded-list matches of the template values

The paper's route (proof of Lemma 8.3, "Bounded horizontal arity"): no whole template value is
mapped into one sample; each bounded list `(b, c)` of a value is matched into an actual marked
sample pair. This file assembles `Lemma83Conclusion` from such matches.
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 3200000 in
/-- **Lemma 8.3 (P.scheme) reduced to bounded-list matches (proved reduction).** For the
constructed pair template (`infra_83_pair_template_clauses`), `Lemma83Conclusion` holds once, for
every value on a well-order `I` with `#I` in the closed tail and every bounded tuple `c` of `Y_I`,
there is a marked sample pair `N` at a closed level `≥ #I`, an arrow `toA : X_I → N.X`, a Cor 6.16
family `R` of `N` with at least `#I` indices whose retractions send `u* = (N.b ∘ τ, c*)` into
`toA[X_I]`, and `tp(mk_I, c / X_I) = tp(u* / N.X)` restricted along `toA`. -/
theorem infra_83_full_single_of_value_matches (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (X Y : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        P.scheme.Object #I hI)
      (incl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        SystemArrow K oneVertexShape (P.scheme.asSystem hI (X I hI))
          (P.scheme.asSystem hI (Y I hI)))
      (mk : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        Fin Pr.n → Occurrence K oneVertexShape (P.scheme.asSystem hI (Y I hI))),
      (∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
          (hI : #I ∈ infra_78_closedTail P ∩ infra_615_closed P)
          (cIdx : Type u)
          (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hI.2.1 (Y I hI.2.1))),
          #cIdx < #I →
          ∃ (N : MarkedPair K oneVertexShape P.scheme Pr) (hlC : N.μ ∈ infra_615_closed P)
            (_ : N.μ ∈ infra_78_closedTail P) (_ : #I ≤ N.μ)
            (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 (X I hI.2.1))
              (P.scheme.asSystem hlC.1 N.X))
            (htoA : P.scheme.permitted (X := X I hI.2.1) (Y := N.X) toA)
            (R : ApproximateRetraction K oneVertexShape P.scheme N.hμ N.X N.Y N.incl)
            (τ : ULift.{u} (Fin Pr.n) ≃ N.bIdx)
            (cU : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 N.Y)),
            #I ≤ #{i : R.index // ∀ s, ∃ y,
              toA.onVertex (seqJoint (fun a => N.b (τ a)) cU s).1 y =
                (R.retr i).onVertex (seqJoint (fun a => N.b (τ a)) cU s).1
                  (seqJoint (fun a => N.b (τ a)) cU s).2} ∧
            SameGaloisType (asTuple (incl I hI.2.1) trivial
                (seqJoint (fun j : ULift.{u} (Fin Pr.n) => mk I hI.2.1 j.down) c))
              ((asTuple N.incl N.incl_arrow (seqJoint (fun a => N.b (τ a)) cU)).restrict
                toA htoA)
              (Equiv.refl _) (Equiv.refl _)) →
      Lemma83Conclusion P.scheme Pr := by
  obtain ⟨F, X, Y, eX, eY, incl, mk, hincl, harr⟩ := infra_83_pair_template_clauses P Pr
  refine ⟨X, Y, incl, mk, fun hS => ?_⟩
  refine infra_83_conclusion_of_marked_values_idx P Pr F X Y eX eY incl mk hincl harr _
    (infra_83_closed_tail P) (fun I _ _ _ hI => ?_)
  obtain ⟨hR, hD⟩ := infra_83_marked_of_marked_matches_card P Pr hI.2 hI.1 (incl I hI.2.1)
    trivial (fun j : ULift.{u} (Fin Pr.n) => mk I hI.2.1 j.down) (hS I hI)
  obtain ⟨realEq, hr⟩ := hR
  exact ⟨ULift.{u} (Fin Pr.n), Equiv.refl _, realEq, hr, hD⟩

end
end AEC
