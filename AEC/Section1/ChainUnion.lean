module

public import AEC.Section1.OrdinalChain

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A union of an ordinal chain: one `τ`-structure, a compatible embedding from each
stage, and a joint cover of the carrier. -/
structure ChainUnion {τ : Tau.{u}} (C : OrdinalChain τ) where
  obj : Model τ
  incl : (i : _root_.Ordinal.{u}) → (hi : i < C.δ) →
    Language.Embedding τ (C.obj i hi).carrier obj.carrier
  compat : ∀ (i j : _root_.Ordinal.{u}) (hi : i < C.δ) (hj : j < C.δ) (hij : i < j),
    Language.Embedding.comp (incl j hj) (C.map i j hi hj hij) = incl i hi
  covers : ∀ x : obj.carrier, ∃ i : _root_.Ordinal.{u}, ∃ hi : i < C.δ,
    ∃ y : (C.obj i hi).carrier, incl i hi y = x

end
end AEC
