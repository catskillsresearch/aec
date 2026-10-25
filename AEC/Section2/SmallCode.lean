module

public import AEC.Section2.SmallPair

@[expose] public section

namespace AEC
section

universe u

/-- A set code for an AEC of Löwenheim–Skolem number at most `lam`, in the sense of
Lemma 2.2: which small ordinal structures are allowed, and which small pairs are
allowed. -/
structure SmallCode (τ : Tau.{u}) (lam : Cardinal.{u}) where
  model : Set (SmallModel τ lam)
  pair : Set (SmallPair τ lam)
  pair_models : ∀ p ∈ pair, p.big ∈ model ∧ p.small ∈ model

end
end AEC
