module

public import AEC.Section7.Results

@[expose] public section

/-!
# Audit: the Lean `IsFreeFrom` / `IsFreeLift` majority clause is vacuous

`IsFreeLift p q f hf e` asks for `SameGaloisType p (q ↾ A)` and an approximation sequence `I`
for `p` such that for every query `Z` from `B` *some* `Z0` from `A` and *some* list `xs` form a
majority value of `I`. Neither `Z0` nor `xs` is tied to `Z` or to `q`, so `Z0 := a constant
query` and `xs := typeJoint Z0` (Definition 6.8's few-exceptions bound) always work.

Consequently `IsFreeFrom f hf q` holds for **every** tuple `q` over `B` as soon as its
restriction to `A` has one approximation sequence (Lemma 6.9 supplies one for small tuples):
`q` is "free from `A`" with witness `q ↾ A` itself. The English notion (`q` is *the* free lift,
the majority answer on each `Z` *is* `q`'s diagram on `Z`) is much stronger. Every Lean result
whose conclusion is only `IsFreeFrom` (e.g. Prop 6.13 local character `infra_613_local`,
`infra_613_continuity`, `infra_611_isFreeFrom`) is therefore weaker than its English statement,
and the Prop 7.8 local-character contradiction cannot be run on it: "free from an earlier stage"
carries no information. This file is sorry-free.
-/

namespace AEC
namespace Audit

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- **`IsFreeFrom` is vacuous.** Any tuple whose restriction has an approximation sequence is
"free from" the base, along any permitted arrow. -/
theorem isFreeFrom_of_approximationSequence
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (seq : ApproximationSequence (q.restrict f hf)) :
    IsFreeFrom f hf q := by
  classical
  have hne : Nonempty ((P.scheme.asSystem hμ A).obj PUnit.unit).carrier := by
    have hc : Model.card ((P.scheme.asSystem hμ A).obj PUnit.unit) = μ :=
      P.scheme.vertex_card hμ A PUnit.unit
    have hμ0 : μ ≠ 0 := (aleph0_pos.trans_le (P.aleph0_le hμ)).ne'
    rw [← Cardinal.mk_ne_zero_iff]
    rw [show #((P.scheme.asSystem hμ A).obj PUnit.unit).carrier =
        Model.card ((P.scheme.asSystem hμ A).obj PUnit.unit) from rfl, hc]
    exact hμ0
  refine ⟨q.restrict f hf, Equiv.refl _, SameGaloisType.refl _, seq, ?_⟩
  intro ι Z hι
  let Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun _ => ⟨PUnit.unit, Classical.choice hne⟩
  exact ⟨Z0, typeJoint (p := q.restrict f hf) Z0, infra_610_majority_eq_type seq Z0 hι⟩

end Audit
end AEC
