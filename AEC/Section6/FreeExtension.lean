module

public import AEC.Section6.MajorityValue

@[expose] public section

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}

/-- The same tuple, read over the source of an arrow `A → B` by composing inclusions. -/
def TupleOver.restrict {μ ν : Cardinal.{u}} {hμ : μ ∈ W.eligible} {hν : ν ∈ W.eligible}
    {A : W.Object μ hμ} {B : W.Object ν hν}
    (f : SystemArrow K S (W.asSystem hμ A) (W.asSystem hν B))
    (hf : W.permitted (X := A) (Y := B) f)
    (q : TupleOver K S W hν B) : TupleOver K S W hμ A where
  ν := q.ν
  hν := q.hν
  host := q.host
  incl := SystemArrow.comp f q.incl
  incl_arrow := W.comp f q.incl hf q.incl_arrow
  idx := q.idx
  val := q.val

/-- Reindex a joint list along an identification of the tuple coordinates. -/
def reindexJoint {pIdx qIdx ι : Type u} {X : SystemObject K S}
    (e : pIdx ≃ qIdx) (xs : pIdx ⊕ ι → Occurrence K S X) :
    qIdx ⊕ ι → Occurrence K S X
  | Sum.inl i => xs (Sum.inl (e.symm i))
  | Sum.inr j => xs (Sum.inr j)

/-- **Theorem 6.10.** `q` over `B` is the free lift of `p` along `A → B` when `p` is the
restriction of `q` and some approximation sequence for `p` has majority value `q` on every
bounded query from `B`. -/
def IsFreeLift {μ ν : Cardinal.{u}} {hμ : μ ∈ W.eligible} {hν : ν ∈ W.eligible}
    {A : W.Object μ hμ} {B : W.Object ν hν}
    (p : TupleOver K S W hμ A) (q : TupleOver K S W hν B)
    (f : SystemArrow K S (W.asSystem hμ A) (W.asSystem hν B))
    (hf : W.permitted (X := A) (Y := B) f)
    (e : p.idx ≃ q.idx) : Prop :=
  SameGaloisType p (q.restrict f hf) e (Equiv.refl q.idx) ∧
  ∃ I : ApproximationSequence p,
    ∀ {ι : Type u} (Z : ι → Occurrence K S (W.asSystem hν B)),
      #ι < ν →
      ∃ (Z0 : ι → Occurrence K S (W.asSystem hμ A))
        (xs : p.idx ⊕ ι → Occurrence K S (W.asSystem q.hν q.host)),
        IsMajorityValue I Z0 q.hν q.host xs ∧
        W.DiagramEq (X := q.host) (Y := q.host) (reindexJoint e xs) (typeJoint (p := q) Z)

/-- An actual type over `B` is free from `A` when it is the free lift of its restriction to `A`. -/
def IsFreeFrom {μ ν : Cardinal.{u}} {hμ : μ ∈ W.eligible} {hν : ν ∈ W.eligible}
    {A : W.Object μ hμ} {B : W.Object ν hν}
    (f : SystemArrow K S (W.asSystem hμ A) (W.asSystem hν B))
    (hf : W.permitted (X := A) (Y := B) f)
    (q : TupleOver K S W hν B) : Prop :=
  ∃ p : TupleOver K S W hμ A, ∃ e : p.idx ≃ q.idx, IsFreeLift p q f hf e

end
end AEC
