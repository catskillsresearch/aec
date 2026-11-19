module

public import AEC.Section7.Theorem713
public import AEC.Section7.GeneralLevel

@[expose] public section

/-!
# Proposition 7.8, general bounded-mark form (`infra_78_general`, cycle 93)

English (Prop 7.8): "Let λ be a sufficiently closed eligible level, let X be an object there, and
let p = tp(b/X) be a finite-tuple type. For every infinite θ < λ there is a same-level extension
X ≤ U containing a realization of p such that tp(b, c/X) is isolated relative to b for every
c ∈ U with |c| ≤ θ. More generally the assertion holds for a bounded mark b satisfying
Definition 7.7, with |b| ≤ θ. The closure requirements at the output level are uniform functions
of bounded arities; they do not require θ to have been fixed before the level was chosen."

`infra_78_general_statement` is the "more generally" sentence on the same uniform tail as
`proposition_7_8` (`infra_78_closedTail`), with the tied Definition 7.7
(`SatisfiesContinuityTied`) and `#p.idx ≤ θ`.

Where the finite proof uses finiteness (cycle 93 scan):
* limit stages of the `ρ⁺` matrix: invariant (5) at a limit `δ` is `infra_78_limit_invariant5`
  when `|b| < cf δ` (finite marks: `infra_78_finite_lt_limit_cof`); for `cf δ ≤ |b|` the paper uses
  Definition 7.7 ("At limits use the working scheme's unions; Definition 7.7 preserves the marginal
  invariant"), with `κ` chosen in the Definition 7.7 tail (tracked: `infra_78_general_small_cof`);
* the joint arity of the isolation bounds: `|b, c| ≤ θ` instead of `ℵ₀ + θ`
  (tracked with the assembly: `infra_78_general_assembly`).
The finite-mark case of the general statement is proved here (`infra_78_general_finite`).
-/

universe u

open Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Prop 7.8, general bounded-mark form (statement; open tip `infra_78_general`).** -/
def infra_78_general_statement (P : SingleModelData K) : Prop :=
  ∀ μ (hμ : μ ∈ infra_78_closedTail P)
    (X : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
    (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X)
    (θ : Cardinal.{u}),
    #p.idx ≤ θ → SatisfiesContinuityTied p → aleph0 ≤ θ → θ < μ →
    ∃ (U : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ U))
      (hf : P.scheme.permitted (X := X) (Y := U) f)
      (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
      SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) ∧
      ∀ {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
        #cIdx ≤ θ →
        IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
          (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx))

/-- **Finite marks (proved, cycle 93).** The general statement for a finite mark holds without
Definition 7.7: it is `infra_78_marginal_general_level`. -/
theorem infra_78_general_finite (P : SingleModelData K) :
    ∀ μ (hμ : μ ∈ infra_78_closedTail P)
      (X : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
      (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X)
      (θ : Cardinal.{u}),
      Finite p.idx → #p.idx ≤ θ → SatisfiesContinuityTied p → aleph0 ≤ θ → θ < μ →
      ∃ (U : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ U))
        (hf : P.scheme.permitted (X := X) (Y := U) f)
        (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
        SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) ∧
        ∀ {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
          #cIdx ≤ θ →
          IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
            (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx)) :=
  fun μ hμ X p θ hfin _ _ hθ hθμ => infra_78_marginal_general_level P μ hμ X p θ hfin hθ hθμ

end AEC
