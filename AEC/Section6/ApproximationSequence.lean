module

public import AEC.Section6.TupleOver
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}

/-- The joint list of a tuple in `X` with an enumerated parameter set in `X`. -/
def seqJoint {idx ι : Type u} {X : SystemObject K S}
    (v : idx → Occurrence K S X) (Z : ι → Occurrence K S X) :
    idx ⊕ ι → Occurrence K S X
  | Sum.inl i => v i
  | Sum.inr j => Z j

/-- The joint list of an actual type with parameters from its base, pushed along the inclusion. -/
def typeJoint {p : TupleOver K S W hμ base} {ι : Type u}
    (Z : ι → Occurrence K S (W.asSystem hμ base)) :
    p.idx ⊕ ι → Occurrence K S (W.asSystem p.hν p.host)
  | Sum.inl i => p.val i
  | Sum.inr j => ⟨(Z j).1, p.incl.onVertex (Z j).1 (Z j).2⟩

/-- **Definition 6.8.** An approximation sequence for `p = tp(v/A)` at query size `τ` is an
indexed family `(vᵢ : i < κ)` in `A`, each of the same index set as `v`, with bounded
concatenation, such that for every parameter enumeration `Z` of size at most `τ` the set of
indices whose joint diagram with `Z` differs from `p ↾ Z` has size at most `|Z| + ℵ₀`. -/
structure ApproximationSequence (p : TupleOver K S W hμ base) where
  τ : Cardinal.{u}
  κIndex : Type u
  family : κIndex → p.idx → Occurrence K S (W.asSystem hμ base)
  concat_bounded : #(κIndex × p.idx) < μ
  few_exceptions : ∀ {ι : Type u}
    (Z : ι → Occurrence K S (W.asSystem hμ base)),
    #ι ≤ τ →
    # {i : κIndex // ¬ W.DiagramEq (X := p.host) (Y := base)
        (typeJoint Z) (seqJoint (family i) Z)} ≤ #ι + aleph0

end
end AEC
