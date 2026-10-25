module

public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

namespace AEC
section

universe u

/-- **§13.3.** A common majorant is a monotone ordinal function `Φ` strictly above a fixed
parameter cutoff and strictly above its input. It bounds every request in the fixed register. -/
structure CommonMajorant where
  theta : _root_.Ordinal.{u}
  Phi : _root_.Ordinal.{u} → _root_.Ordinal.{u}
  mono : ∀ α β, α ≤ β → Phi α ≤ Phi β
  aboveCutoff : ∀ α, theta < Phi α
  aboveId : ∀ α, α < Phi α

/-- **Lemma 13.3.** A totalization of a bound request: the least ordinal satisfying the request,
or `0` when no such ordinal exists. -/
def IsTotalization (request : _root_.Ordinal.{u} → Set _root_.Ordinal.{u})
    (value : _root_.Ordinal.{u} → _root_.Ordinal.{u}) : Prop :=
  ∀ α, (value α ∈ request α ∧ ∀ β ∈ request α, value α ≤ β) ∨
    (request α = ∅ ∧ value α = 0)

end
end AEC
