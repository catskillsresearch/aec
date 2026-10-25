module

public import AEC.Section1.Model
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- An increasing chain `(Mᵢ : i < δ)` of `τ`-structures, indexed by a nonzero ordinal,
with a transition embedding whenever `i < j`. -/
structure OrdinalChain (τ : Tau.{u}) where
  δ : _root_.Ordinal.{u}
  nonzero : δ ≠ 0
  obj : (i : _root_.Ordinal.{u}) → i < δ → Model τ
  map : (i j : _root_.Ordinal.{u}) → (hi : i < δ) → (hj : j < δ) → i < j →
    Language.Embedding τ (obj i hi).carrier (obj j hj).carrier

/-- Transition embeddings compose along `i < j < k`. -/
def OrdinalChain.map_comp_prop (τ : Tau.{u}) (C : OrdinalChain τ) : Prop :=
  ∀ (i j k : _root_.Ordinal.{u}) (hi : i < C.δ) (hj : j < C.δ) (hk : k < C.δ)
    (hij : i < j) (hjk : j < k),
    Language.Embedding.comp (C.map j k hj hk hjk) (C.map i j hi hj hij) =
      C.map i k hi hk (hij.trans hjk)

end
end AEC
