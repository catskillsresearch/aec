module

public import AEC.Section1.Model

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A nonempty directed diagram of `τ`-embeddings. The index is a preorder in which
every two indices have a common upper bound, and the transition maps compose. -/
structure DirectedSystem (τ : Tau.{u}) where
  ι : Type u
  nonempty : Nonempty ι
  rel : ι → ι → Prop
  refl : ∀ i, rel i i
  trans : ∀ {i j k}, rel i j → rel j k → rel i k
  directed : ∀ i j, ∃ k, rel i k ∧ rel j k
  obj : ι → Model τ
  map : ∀ {i j}, rel i j → Language.Embedding τ (obj i).carrier (obj j).carrier
  map_refl : ∀ i, map (refl i) = Language.Embedding.refl τ (obj i).carrier
  map_trans : ∀ {i j k} (hij : rel i j) (hjk : rel j k),
    map (trans hij hjk) = (map hjk).comp (map hij)

end
end AEC
