module

public import AEC.Section2.DirectedSystem

@[expose] public section

namespace AEC
section

universe u

/-- The equivalence used to build a direct limit as a quotient of the disjoint union:
`(i, x) ~ (j, y)` when the two elements agree after mapping into a common later stage. -/
def directLimitRel {τ : Tau.{u}} (S : DirectedSystem τ) :
    (Σ i, (S.obj i).carrier) → (Σ i, (S.obj i).carrier) → Prop :=
  fun a b => ∃ k, ∃ (hik : S.rel a.1 k), ∃ (hjk : S.rel b.1 k),
    S.map hik a.2 = S.map hjk b.2

end
end AEC
