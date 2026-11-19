module

public import AEC.Section7.IsolationBound
public import AEC.Section7.MixedLevel

@[expose] public section

/-!
# Lemma 7.2, last sentence (mixed levels)

English Lemma 7.2 ends: "The second assertion also holds when `A` is at a smaller eligible level
than `B`, provided `(u, c)` and the required uniform bounds are below the level of `A`."
`infra_72_over_B_isolation` is the same-level clause 2; this file states the mixed-level clause:
`A` at level `ν ≤ μ`, `B` at level `μ`, the bounds (`recursionClosedLevels`, `σ⁺ ≤ ν`, `|q| < ν`)
at the level of `A`, and the tied-free marginal hypothesis in its mixed form `IsTiedFreeMixed`.
Needed for Lemma 8.2(5) preservation across levels. Open (audit finding, cycle 96).
-/

namespace AEC
section

universe u
open Cardinal Classical FirstOrder Function
variable {K : AbstractElementaryClass.{u}}

/-- **English Lemma 7.2, clause 2 at mixed levels (open).** -/
theorem infra_72_mixed_level
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible) (hμ : μ ∈ P.eligible) (hνμ : ν ≤ μ)
    (hrec : ν ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ ν)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hν A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = ν) (hBν : qB.ν = μ)
    (hidx : #q.idx ≤ σ) (hidxν : #q.idx < ν)
    {wι : Type u} (W : wι → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (hW : IsIsolatingFragment q e W)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    (hMargTied : IsTiedFreeMixed f (q.marginal e) (qB.marginal (eB.symm.trans e))
      (Equiv.refl uIdx)) :
    IsIsolatingFragment qB (eB.symm.trans e) (pushParams f W) := by
  sorry

end
end AEC
