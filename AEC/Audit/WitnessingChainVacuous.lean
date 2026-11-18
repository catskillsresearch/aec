module

public import AEC.Section7.Results

@[expose] public section

/-!
# Audit: `lemma_7_12` (and the first clause of `theorem_7_13`) are vacuous as formalized

`WitnessingChain` does not link its marks to the given `TupleList` (nor has a first stage `A`,
an order, or continuity), so the chain indexed by the empty type is an all-dominated-increment
witnessing chain over every object. Hence the Lean conclusion of `lemma_7_12` holds for every
scheme on the tail `W.eligible`, independently of product-independence: the statement is
degenerate and must be restated with a list-linked chain before it can count as done.
-/

namespace AEC
namespace Audit

universe u

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}

/-- The empty witnessing chain. -/
def emptyWitnessingChain (W : WorkingScheme K S) {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible)
    (A : W.Object μ hμ) : WitnessingChain W hμ A where
  δ := PEmpty
  obj := fun i => i.elim
  into := fun i => i.elim
  into_arrow := fun i => i.elim
  next := fun i => i.elim
  step := fun i => i.elim
  step_arrow := fun i => i.elim
  markIdx := fun i => i.elim
  mark := fun i => i.elim
  finite_mark := fun i => i.elim
  free := fun i => i.elim

theorem emptyWitnessingChain_allDominatedIncrement (W : WorkingScheme K S) {μ : Cardinal.{u}}
    (hμ : μ ∈ W.eligible) (A : W.Object μ hμ) :
    AllDominatedIncrement (emptyWitnessingChain W hμ A) := fun i => i.elim

/-- The Lean statement of `lemma_7_12` is provable for every scheme without any input:
it is degenerate (the English content, a chain witnessing the given list, is not captured). -/
theorem lemma_7_12_statement_vacuous (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (L : TupleList W (Tail.mem hT hμ) A),
        ProductIndependent L →
        ∃ C : WitnessingChain W (Tail.mem hT hμ) A, AllDominatedIncrement C :=
  ⟨W.eligible, ⟨fun _ h => h, W.eligible_unbounded⟩, fun _ _ A _ _ =>
    ⟨emptyWitnessingChain W _ A, emptyWitnessingChain_allDominatedIncrement W _ A⟩⟩

end Audit
end AEC
