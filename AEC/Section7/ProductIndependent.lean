module

public import AEC.Section6.ProductType

@[expose] public section

namespace AEC
section

universe u

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {A : W.Object μ hμ}

/-- A list of finite tuples in one extension of `A`. -/
structure TupleList (W : WorkingScheme K S) {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible)
    (A : W.Object μ hμ) where
  δ : Type u
  host : W.Object μ hμ
  incl : SystemArrow K S (W.asSystem hμ A) (W.asSystem hμ host)
  incl_arrow : W.permitted (X := A) (Y := host) incl
  indexAt : δ → Type u
  val : (i : δ) → indexAt i → Occurrence K S (W.asSystem hμ host)
  finite_each : ∀ i, Finite (indexAt i)

/-- The type over `A` of one entry of a tuple list. -/
def TupleList.one (L : TupleList W hμ A) (i : L.δ) : TupleOver K S W hμ A where
  ν := μ
  hν := hμ
  host := L.host
  incl := L.incl
  incl_arrow := L.incl_arrow
  idx := L.indexAt i
  val := L.val i

/-- The joint type over `A` of a finite sublist. -/
def TupleList.subConcat (L : TupleList W hμ A) (n : ℕ) (ix : Fin n → L.δ) :
    TupleOver K S W hμ A where
  ν := μ
  hν := hμ
  host := L.host
  incl := L.incl
  incl_arrow := L.incl_arrow
  idx := Σ i : Fin n, L.indexAt (ix i)
  val := fun p => L.val (ix p.1) p.2

/-- **Definition 7.10.** The list is product-independent over `A` when each finite sublist has
the product of its marginal types over `A`. -/
def ProductIndependent (L : TupleList W hμ A) : Prop :=
  ∀ (n : ℕ) (ix : Fin n → L.δ), Function.Injective ix →
    ∃ joint : TupleOver K S W hμ A, ∃ e : (L.subConcat n ix).idx ≃ joint.idx,
      IsFiniteProduct n (fun i => L.one (ix i)) joint ∧
      SameGaloisType (L.subConcat n ix) joint e (Equiv.refl joint.idx)

end
end AEC
