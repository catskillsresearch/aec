module

public import AEC.Section5.EmptiedScheme
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

/-- The shape of the marked increment `C^b`: two copies of `S` (the base `X` and the extension
`Y` of a marked pair), with the specified maps of each copy and the inclusion `X_v → Y_v`. -/
def SystemShape.doubled (S : SystemShape.{u}) : SystemShape.{u} where
  Vertex := S.Vertex ⊕ S.Vertex
  vertexFinite := by have := S.vertexFinite; infer_instance
  specified
    | Sum.inl i, Sum.inl j => S.specified i j
    | Sum.inr i, Sum.inr j => S.specified i j
    | Sum.inl i, Sum.inr j => i = j
    | Sum.inr _, Sum.inl _ => False

/-- **Theorem 8.6** (The marked-increment working package). Let `C` be a working scheme with
componentwise arrows and a stationary finite prescription. Assume the eligible-subclass
hypothesis. On an unbounded further class of sufficiently closed eligible levels, `C^b` is again
a working scheme, with componentwise arrows, fixed template and mixed arrows between these levels;
the output class retains the eligible-subclass hypothesis.

**Statement (restated, honest form, open):** the input `W` is a working package with objects at
every eligible level; the output `W'` lives on the doubled shape (`SystemShape.doubled`), is a
working package on an eligible subclass of `R`, has objects at every eligible level, every object
is (vertexwise isomorphic to) a marked pair `(X, Y, b)` of Definition 8.1 at its level, and every
marked pair at an eligible level of `W'` is isomorphic to an object. The former statement had
no nonemptiness and was proved by the object-free `WorkingScheme.emptied` (degenerate). The
correspondence of permitted arrows with `MarkedArrow`s is not yet stated. -/
theorem theorem_8_6 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (hW : IsWorkingPackage W)
    (hne : ∀ μ (hμ : μ ∈ W.eligible), Nonempty (W.Object μ hμ))
    (P : StationaryPrescription K S W)
    (R : Set Cardinal.{u}) (hR : EligibleSubclass W.eligible R) :
    ∃ W' : WorkingScheme K S.doubled,
      IsWorkingPackage W' ∧ EligibleSubclass R W'.eligible ∧
      (∀ μ (hμ : μ ∈ W'.eligible), Nonempty (W'.Object μ hμ)) ∧
      (∀ μ (hμ : μ ∈ W'.eligible) (X' : W'.Object μ hμ),
        ∃ M : MarkedPair K S W P, M.μ = μ ∧
          (∀ v, Nonempty (((W'.asSystem hμ X').obj (Sum.inl v)).carrier ≃[K.τ]
            ((W.asSystem M.hμ M.X).obj v).carrier)) ∧
          (∀ v, Nonempty (((W'.asSystem hμ X').obj (Sum.inr v)).carrier ≃[K.τ]
            ((W.asSystem M.hμ M.Y).obj v).carrier))) ∧
      (∀ M : MarkedPair K S W P, ∀ hμ' : M.μ ∈ W'.eligible,
        ∃ X' : W'.Object M.μ hμ',
          (∀ v, Nonempty (((W'.asSystem hμ' X').obj (Sum.inl v)).carrier ≃[K.τ]
            ((W.asSystem M.hμ M.X).obj v).carrier)) ∧
          (∀ v, Nonempty (((W'.asSystem hμ' X').obj (Sum.inr v)).carrier ≃[K.τ]
            ((W.asSystem M.hμ M.Y).obj v).carrier))) := by
  sorry

end
end AEC
