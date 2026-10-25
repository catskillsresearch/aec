module

public import AEC.Section1.Model
public import AEC.Section5.BoundedAt

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- A query in a model is an enumerated parameter set together with a displayed tuple.
Repetitions in the enumeration are allowed. An answer is correct on the query when the
whole joint diagram agrees, not merely the diagrams of finite subtuples. -/
structure Query (τ : Tau.{u}) (M : Model τ) where
  paramIndex : Type u
  params : paramIndex → M.carrier
  tupleIndex : Type u
  tuple : tupleIndex → M.carrier

/-- At a level `μ`, a query is bounded when both its parameter set and its displayed
tuple have cardinality strictly less than `μ`. -/
def Query.IsBounded {τ : Tau.{u}} {M : Model τ} (μ : Cardinal.{u}) (q : Query τ M) : Prop :=
  BoundedAt μ q.paramIndex ∧ BoundedAt μ q.tupleIndex

end
end AEC
