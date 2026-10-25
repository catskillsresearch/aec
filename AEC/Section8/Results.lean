module

public import AEC.Section8.MarkedPair
public import AEC.Section5.Results
public import AEC.Section5.TermTemplate
public import AEC.Section6.Results

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Lemma 8.2** (The pair isomorphism test). On a further tail of eligible levels, every
object sits in a marked pair, and an isomorphism of the bases extends to the pairs if and only
if it transports the joint type of the extra tuple with the mark. -/
theorem lemma_8_2 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (P : StationaryPrescription K S W) :
    ∃ T, ∃ hT : Tail W.eligible T,
      (∀ μ (hμ : μ ∈ T) (X : W.Object μ (Tail.mem hT hμ)),
        ∃ M : MarkedPair K S W P, M.μ = μ ∧
          ∃ e : SystemArrow K S (W.asSystem _ X) (W.asSystem _ M.X),
            W.permitted (X := X) (Y := M.X) e ∧ ∀ v, Function.Bijective (e.onVertex v)) ∧
      ∀ (M N : MarkedPair K S W P)
        (e : SystemArrow K S (W.asSystem M.hμ M.X) (W.asSystem N.hμ N.X)),
        M.μ ∈ T → N.μ ∈ T →
        (∀ v, Function.Bijective (e.onVertex v)) →
        W.permitted (X := M.X) (Y := N.X) e →
        ∃ arr : MarkedArrow K S W P M N, arr.onX = e := by
  sorry

/-- **Lemma 8.3** (The marked-pair template). There is a term template whose values at
sufficiently closed levels are marked pairs, and every marked pair at such a level is
isomorphic to a value of that template. -/
theorem lemma_8_3 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (P : StationaryPrescription K S W) :
    ∃ F : TermTemplate K S, ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (I : Type u) [LinearOrder I] [Nonempty I],
        #I = μ →
        ∃ M : MarkedPair K S W P, M.μ = μ ∧
          ∀ v, Nonempty (((F.present I).obj v).carrier ≃[K.τ]
            ((W.asSystem M.hμ M.Y).obj v).carrier) := by
  sorry

/-- **Lemma 8.4** (Testing beside an isolated small upper object). For each `σ < ν` there is
a bound `k(σ) < ν` such that comparisons of tuples of length at most `σ` are determined by
tests of size at most `k(σ)`. -/
theorem lemma_8_4 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T, ∃ k : Cardinal.{u} → Cardinal.{u},
      ∀ ν (hν : ν ∈ T) σ, σ < ν → k σ < ν ∧
        ∀ μ (hμ : μ ∈ T), ν < μ →
          ∀ (A : W.Object ν (Tail.mem hT hν))
            (p q : TupleOver K S W (Tail.mem hT hν) A) (e : p.idx ≃ q.idx),
            #p.idx ≤ σ → #q.idx ≤ σ →
            (∀ {ι : Type u} (Z : ι → Occurrence K S (W.asSystem _ A)), #ι ≤ k σ →
              W.DiagramEq (X := p.host) (Y := q.host) (typeJoint (p := p) Z)
                (reindexJoint e.symm (typeJoint (p := q) Z))) →
            SameGaloisType p q (Equiv.refl p.idx) e.symm := by
  sorry

/-- **Lemma 8.5** (Chain closure). On a further tail, an increasing chain of marked pairs of
total size the level has a marked-pair union, including the common-upper-bound clause. -/
theorem lemma_8_5 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (P : StationaryPrescription K S W) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (index : Type u) (M : index → MarkedPair K S W P),
        (∀ i, (M i).μ = μ) → #index ≤ μ →
        ∃ U : MarkedPair K S W P, U.μ = μ ∧
          ∀ i, Nonempty (MarkedArrow K S W P (M i) U) := by
  sorry

/-- **Theorem 8.6** (The marked-increment working package). From a working scheme with a
stationary finite prescription and an eligible subclass, a further unbounded subclass carries
a working scheme for the marked increment. -/
theorem theorem_8_6 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (P : StationaryPrescription K S W)
    (R : Set Cardinal.{u}) (hR : EligibleSubclass W.eligible R) :
    ∃ S' : SystemShape.{u}, ∃ W' : WorkingScheme K S',
      IsWorkingPackage W' ∧ EligibleSubclass R W'.eligible := by
  sorry

end
end AEC
