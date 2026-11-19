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

/-- **Invariant (5) at a matrix limit from freeness over some stage (proved, cycle 93).**
The step of `infra_78_tied_continuity` after local character: if the mark `p` over the union
`X_δ` is tied-free from some stage `X_i` (for `|b| < cf δ` this is local character,
`infra_78_tied_local`; for a bounded mark satisfying Definition 7.7 it is Def 7.7's conclusion at
`i = 0`, "Definition 7.7 preserves the marginal invariant"), and (5) holds at every stage, then
(5) holds at `δ`. No cofinality hypothesis. -/
theorem infra_78_general_limit_invariant {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} (C : SameLevelChain P hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ C.unionObj)
    (X : P.scheme.Object μ hμ)
    (g : SystemArrow K oneVertexShape
      (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ (C.obj 0 C.hlim.1)))
    (hg : P.scheme.permitted (X := X) (Y := C.obj 0 C.hlim.1) g)
    (hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree
        (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
          (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (P.scheme.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hg
            (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _))
    (hF : ∃ i : Ordinal.{u}, ∃ hi : i < C.δ,
      IsTiedFree (C.toUnion i hi)
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) p (Equiv.refl _)) :
    IsTiedFree (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
      (p.restrict (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
        (P.scheme.comp g (C.toUnion 0 C.hlim.1) hg (C.toUnion_arrow 0 C.hlim.1)))
      p (Equiv.refl _) := by
  obtain ⟨i, hi, hF⟩ := hF
  have hzero : (0 : Ordinal.{u}) ≤ i := bot_le
  have hgA := P.scheme.comp g (C.le C.hlim.1 hi hzero) hg (C.le_arrow C.hlim.1 hi hzero)
  have htrans := infra_78_tiedFree_trans (SystemArrow.comp g (C.le C.hlim.1 hi hzero)) hgA
    (C.toUnion i hi) (C.toUnion_arrow i hi) p (hAll i hi) hF
  exact infra_78_tiedFree_congr_arrow _ _ p (infra_613_cocone_arrow C g hi) htrans

end AEC
