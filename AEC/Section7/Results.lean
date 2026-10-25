module

public import AEC.Section7.RelativeIsolation
public import AEC.Section7.AllDominated
public import AEC.Section7.ContinuityCondition
public import AEC.Section7.ProductIndependent
public import AEC.Section7.WitnessingChain
public import AEC.Section6.Results

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open Cardinal

/-- **Lemma 7.2.** A projection of a relatively isolated type is relatively isolated, and a free
lift of a type isolated relative to `u` remains isolated relative to `u`. -/
theorem lemma_7_2 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (q : TupleOver K S W (Tail.mem hT hμ) A) {uIdx cIdx : Type u}
        (e : q.idx ≃ uIdx ⊕ cIdx),
        IsRelativelyIsolated q e →
        (∃ e' : (q.marginal e).idx ≃ (q.marginal e).idx ⊕ PEmpty.{u+1},
          IsRelativelyIsolated (q.marginal e) e') ∧
        ∀ {ν : Cardinal.{u}} (hν : ν ∈ T) (B : W.Object ν (Tail.mem hT hν))
          (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B))
          (hf : W.permitted (X := A) (Y := B) f)
          (qB : TupleOver K S W (Tail.mem hT hν) B) (eB : q.idx ≃ qB.idx),
          IsFreeLift q qB f hf eB →
          ∃ uIdx' : Type u, ∃ cIdx' : Type u, ∃ e' : qB.idx ≃ uIdx' ⊕ cIdx',
            IsRelativelyIsolated qB e' := by
  sorry

/-- **Proposition 7.3.** There is a bound `h`, depending only on the scheme, such that a type
`q = tp(u, c/A)` is either isolated relative to `u` by a fragment of size at most `h(σ)`, or
has a same-level extension whose free lift differs from some extension that still lifts `u`
freely. -/
theorem proposition_7_3 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ h : Cardinal.{u} → Cardinal.{u}, ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (q : TupleOver K S W (Tail.mem hT hμ) A) {uIdx cIdx : Type u}
        (e : q.idx ≃ uIdx ⊕ cIdx) (σ : Cardinal.{u}),
        #(uIdx ⊕ cIdx) ≤ σ →
        (∃ ι : Type u, ∃ Z : ι → Occurrence K S (W.asSystem _ A), #ι ≤ h σ ∧
          IsIsolatingFragment q e Z) ∨
        (∃ (B : W.Object μ (Tail.mem hT hμ))
            (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B))
            (hf : W.permitted (X := A) (Y := B) f)
            (qB : TupleOver K S W (Tail.mem hT hμ) B) (eB : q.idx ≃ qB.idx),
            ¬ IsFreeLift q qB f hf eB) := by
  sorry

/-- **Proposition 7.5.** An all-dominated object over `X + b` embeds, over that data, into any
extension containing a tuple of the same type, and any two such objects are isomorphic over
the data. -/
theorem proposition_7_5 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (X Y : W.Object μ (Tail.mem hT hμ))
        (incl : SystemArrow K S (W.asSystem _ X) (W.asSystem _ Y))
        (hincl : W.permitted (X := X) (Y := Y) incl) {bIdx : Type u}
        (b : bIdx → Occurrence K S (W.asSystem _ Y)),
        #bIdx < μ → AllDominated incl hincl bIdx b →
        ∀ (N : W.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K S (W.asSystem _ X) (W.asSystem _ N))
          (hf : W.permitted (X := X) (Y := N) f)
          (b' : bIdx → Occurrence K S (W.asSystem _ N)),
          SameGaloisType (asTuple incl hincl b) (asTuple f hf b')
            (Equiv.refl bIdx) (Equiv.refl bIdx) →
          ∃ g : SystemArrow K S (W.asSystem _ Y) (W.asSystem _ N),
            W.permitted (X := Y) (Y := N) g ∧ SystemArrow.comp incl g = f ∧
            ∀ i, ∃ x, b' i = ⟨(b i).1, x⟩ ∧
              g.onVertex (b i).1 (b i).2 = x := by
  sorry

/-- **Lemma 7.6.** If the free lift of `q_A` is isolated relative to `u`, then `q_A` is
isolated relative to `u`. -/
theorem lemma_7_6 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ ν (hν : ν ∈ T) μ (hμ : μ ∈ T) (A : W.Object ν (Tail.mem hT hν))
        (B : W.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B))
        (hf : W.permitted (X := A) (Y := B) f)
        (qA : TupleOver K S W (Tail.mem hT hν) A)
        (qB : TupleOver K S W (Tail.mem hT hμ) B)
        (e : qA.idx ≃ qB.idx) {uIdx cIdx : Type u}
        (eA : qA.idx ≃ uIdx ⊕ cIdx),
        ν ≤ μ → IsFreeLift qA qB f hf e →
        IsRelativelyIsolated qB (e.symm.trans eA) →
        IsRelativelyIsolated qA eA := by
  sorry

/-- **Proposition 7.8.** A finite-tuple type at a sufficiently closed level has a same-level
extension in which every tuple of length at most `θ` is isolated relative to the mark. -/
theorem proposition_7_8 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : W.Object μ (Tail.mem hT hμ))
        (p : TupleOver K S W (Tail.mem hT hμ) X) (θ : Cardinal.{u}),
        Finite p.idx → aleph0 ≤ θ → θ < μ →
        ∃ (U : W.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K S (W.asSystem _ X) (W.asSystem _ U))
          (hf : W.permitted (X := X) (Y := U) f)
          (b : p.idx → Occurrence K S (W.asSystem _ U)) (e : p.idx ≃ p.idx),
          SameGaloisType p (asTuple f hf b) e (Equiv.refl p.idx) ∧
          ∀ {cIdx : Type u} (c : cIdx → Occurrence K S (W.asSystem _ U)), #cIdx ≤ θ →
            IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
              (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx)) := by
  sorry

/-- **Theorem 7.9.** Every finite-tuple type at a sufficiently closed level has an
all-dominated realization. -/
theorem theorem_7_9 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : W.Object μ (Tail.mem hT hμ))
        (p : TupleOver K S W (Tail.mem hT hμ) X),
        Finite p.idx →
        ∃ (Y : W.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K S (W.asSystem _ X) (W.asSystem _ Y))
          (hf : W.permitted (X := X) (Y := Y) f)
          (b : p.idx → Occurrence K S (W.asSystem _ Y)),
          AllDominated f hf p.idx b ∧
          SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) := by
  sorry

/-- **Lemma 7.11.** A finite tuple that has product over `A` with every finite selection from
an all-dominated-increment chain is free from `A` over the last stage. -/
theorem lemma_7_11 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (C : WitnessingChain W (Tail.mem hT hμ) A),
        AllDominatedIncrement C →
        ∀ (p : TupleOver K S W (Tail.mem hT hμ) A), Finite p.idx →
          (∀ i, ∃ joint : TupleOver K S W (Tail.mem hT hμ) A,
            ∃ e : p.idx ⊕ (C.markIdx i) ≃ joint.idx,
              IsProduct p (asTuple (C.into (C.next i)) (C.into_arrow (C.next i)) (C.mark i))
                joint e) →
          ∀ i, ∃ q : TupleOver K S W (Tail.mem hT hμ) (C.obj i),
            ∃ e : p.idx ≃ q.idx, IsFreeLift p q (C.into i) (C.into_arrow i) e := by
  sorry

/-- **Lemma 7.12.** A product-independent list of finite tuples has an all-dominated-increment
witnessing chain, and the whole amalgamation type is determined by the successive marginal
types. -/
theorem lemma_7_12 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (L : TupleList W (Tail.mem hT hμ) A),
        ProductIndependent L →
        ∃ C : WitnessingChain W (Tail.mem hT hμ) A, AllDominatedIncrement C := by
  sorry

/-- **Theorem 7.13.** The whole type of a bounded product-independent list of finite tuples is
determined by its finite sublists, its free lift is product-independent, and it has an
all-dominated realization. -/
theorem theorem_7_13 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (L : TupleList W (Tail.mem hT hμ) A),
        ProductIndependent L → #L.δ < μ →
        (∃ C : WitnessingChain W (Tail.mem hT hμ) A, AllDominatedIncrement C) ∧
        (∃ p : TupleOver K S W (Tail.mem hT hμ) A, SatisfiesContinuity p) := by
  sorry

end
end AEC
