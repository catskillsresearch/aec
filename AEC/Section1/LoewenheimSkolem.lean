module

public import AEC.Section1.AbstractElementaryClass
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- `ℓ` is a Löwenheim–Skolem bound for `K`: `ℓ ≥ |τ| + ℵ₀`, and every set `A` in a model
sits in a strong submodel of cardinality at most `|A| + ℓ`. -/
def isLSBound (K : AbstractElementaryClass.{u}) (ℓ : Cardinal.{u}) : Prop :=
  aleph0 ≤ ℓ ∧ K.τ.card + aleph0 ≤ ℓ ∧
    ∀ M : Model K.τ, K.Mem M → ∀ A : Set M.carrier,
      ∃ N : Model K.τ, ∃ f : Language.Embedding K.τ N.carrier M.carrier,
        K.Mem N ∧ K.Strong f ∧ (∀ a ∈ A, ∃ n, f n = a) ∧
        Model.card N ≤ mk A + ℓ

/-- The Löwenheim–Skolem number `LS(K)`, the least such bound. -/
noncomputable def ls (K : AbstractElementaryClass.{u}) : Cardinal.{u} :=
  sInf {ℓ | isLSBound K ℓ}

theorem exists_isLSBound (K : AbstractElementaryClass.{u}) : ∃ ℓ, isLSBound K ℓ :=
  ⟨K.lsBound, K.lsBound_infinite, K.lsBound_language, K.ls_axiom⟩

theorem isLSBound_ls (K : AbstractElementaryClass.{u}) : isLSBound K (ls K) :=
  (isLeast_csInf (s := {ℓ | isLSBound K ℓ}) ⟨K.lsBound, K.lsBound_infinite, K.lsBound_language,
    K.ls_axiom⟩).1

end
end AEC
