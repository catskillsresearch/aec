module

public import AEC.Section2.DirectedSystem

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A direct limit of a directed system: compatible canonical embeddings that jointly
cover the limit carrier. -/
structure DirectLimit {τ : Tau.{u}} (S : DirectedSystem τ) where
  obj : Model τ
  canon : ∀ i, Language.Embedding τ (S.obj i).carrier obj.carrier
  compat : ∀ {i j} (hij : S.rel i j), (canon j).comp (S.map hij) = canon i
  joint : ∀ x : obj.carrier, ∃ i, ∃ y : (S.obj i).carrier, canon i y = x

end
end AEC
