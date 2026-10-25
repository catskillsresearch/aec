module

public import AEC.Section5.WorkingScheme

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A tuple in an extension of a scheme object `base`. The extension may sit at another
eligible level. This is the data of an actual type `tp(v/A)` before identifying two such
presentations. -/
structure TupleOver (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (W : WorkingScheme K S) {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible)
    (base : W.Object μ hμ) where
  ν : Cardinal.{u}
  hν : ν ∈ W.eligible
  host : W.Object ν hν
  incl : SystemArrow K S (W.asSystem hμ base) (W.asSystem hν host)
  incl_arrow : W.permitted (X := base) (Y := host) incl
  idx : Type u
  val : idx → Occurrence K S (W.asSystem hν host)

/-- **Theorem 6.6.** Two equally indexed tuples over the same base have the same Galois type
when some pair of arrows into a common object identifies them and commutes with the inclusions
of the base. -/
def SameGaloisType {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    {W : WorkingScheme K S} {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible}
    {base : W.Object μ hμ} {idx : Type u}
    (t1 t2 : TupleOver K S W hμ base) (e1 : t1.idx ≃ idx) (e2 : t2.idx ≃ idx) : Prop :=
  ∃ (ρ : Cardinal.{u}) (hρ : ρ ∈ W.eligible) (top : W.Object ρ hρ)
    (f1 : SystemArrow K S (W.asSystem t1.hν t1.host) (W.asSystem hρ top))
    (f2 : SystemArrow K S (W.asSystem t2.hν t2.host) (W.asSystem hρ top)),
    W.permitted (X := t1.host) (Y := top) f1 ∧
    W.permitted (X := t2.host) (Y := top) f2 ∧
    (∀ v, (f1.onVertex v).comp (t1.incl.onVertex v) =
      (f2.onVertex v).comp (t2.incl.onVertex v)) ∧
    ∀ i : idx,
      (⟨(t1.val (e1.symm i)).1,
          f1.onVertex (t1.val (e1.symm i)).1 (t1.val (e1.symm i)).2⟩ :
        Occurrence K S (W.asSystem hρ top)) =
      ⟨(t2.val (e2.symm i)).1,
          f2.onVertex (t2.val (e2.symm i)).1 (t2.val (e2.symm i)).2⟩

end
end AEC
