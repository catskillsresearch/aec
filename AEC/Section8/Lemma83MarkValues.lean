module

public import AEC.Section8.Lemma83PairSamplesR
public import AEC.Section8.MarkLang83

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: mark values in the samples

The mark of a marked pair, indexed by `Fin Pr.n` through `realEq` and `Pr.arity`, and carried
into `L` by `F : Y → L`, lies in `Y = range F`; so `Y` is closed under the mark constants.
-/

universe u

open FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- The mark of `M`, indexed by `Fin Pr.n`, as elements of `Y`. -/
def markY {P : SingleModelData K} {Pr : StationaryPrescription K oneVertexShape P.scheme}
    (M : MarkedPair K oneVertexShape P.scheme Pr) (k : Fin Pr.n) :
    ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier :=
  (M.b (M.realEq.symm ((Pr.arity M.hμ M.X).symm k))).2

/-- **`Y` is closed under the mark constants** interpreted by `F ∘ markY`. -/
theorem markY_closed {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    (M : MarkedPair K oneVertexShape P.scheme Pr) {N : Type u}
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → N) {k : ℕ}
    (f : (Mark83.markLang.{u} Pr.n).Functions k) (x : Fin k → N) :
    @Language.Structure.funMap _ _ (Mark83.markStr fun i => F (markY M i)) k f x ∈ Set.range F :=
  Mark83.mark_mem (fun i => F (markY M i)) (S := Set.range F) (fun i => Set.mem_range_self _) f x

end AEC
