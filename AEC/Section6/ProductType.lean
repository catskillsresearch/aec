module

public import AEC.Section6.FreeExtension

@[expose] public section

namespace AEC
section

universe u

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {A : W.Object μ hμ}

/-- The concatenation of a tuple `x` over `A` with a tuple `y` over the host of `x`. -/
def TupleOver.join (x : TupleOver K S W hμ A) (y : TupleOver K S W x.hν x.host) :
    TupleOver K S W hμ A where
  ν := y.ν
  hν := y.hν
  host := y.host
  incl := SystemArrow.comp x.incl y.incl
  incl_arrow := W.comp x.incl y.incl x.incl_arrow y.incl_arrow
  idx := x.idx ⊕ y.idx
  val := fun i =>
    match i with
    | Sum.inl i => ⟨(x.val i).1, y.incl.onVertex (x.val i).1 (x.val i).2⟩
    | Sum.inr j => y.val j

/-- **Proposition 6.12.** `joint` is the product `p ⊗ q` when it is the joint type, over `A`, of a
realization of `p` followed by a free lift of `q`. -/
def IsProduct (p q joint : TupleOver K S W hμ A) (e : p.idx ⊕ q.idx ≃ joint.idx) : Prop :=
  ∃ (x : TupleOver K S W hμ A) (ex : p.idx ≃ x.idx),
    SameGaloisType p x ex (Equiv.refl x.idx) ∧
    ∃ (y : TupleOver K S W x.hν x.host) (ey : q.idx ≃ y.idx),
      IsFreeLift q y x.incl x.incl_arrow ey ∧
      SameGaloisType joint (x.join y)
        (e.symm.trans (Equiv.sumCongr ex ey)) (Equiv.refl (x.idx ⊕ y.idx))

/-- The joint type of a finite list of bounded types, by iterating `⊗`. -/
def IsFiniteProduct : (n : ℕ) → (Fin n → TupleOver K S W hμ A) →
    TupleOver K S W hμ A → Prop
  | 0, _, joint => IsEmpty joint.idx
  | n + 1, b, joint =>
      ∃ left : TupleOver K S W hμ A,
        IsFiniteProduct n (fun i => b i.castSucc) left ∧
        ∃ e : left.idx ⊕ (b (Fin.last n)).idx ≃ joint.idx,
          IsProduct left (b (Fin.last n)) joint e

end
end AEC
