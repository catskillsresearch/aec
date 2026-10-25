module

public import AEC.Section2.DecodedMembership
public import AEC.Section2.DecodedStrong
public import AEC.Section1.LoewenheimSkolem

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A small code is valid when decoding it produces an AEC in `τ` with Löwenheim–Skolem
bound `lam`. Proposition 2.3 takes the set of all such codes. -/
class IsValidCode {τ : Tau.{u}} (lam : Cardinal.{u}) (c : SmallCode τ lam) : Prop where
  decodes : ∃ (K : AbstractElementaryClass.{u}) (h : τ = K.τ),
    isLSBound K lam ∧
      (∀ M : Model K.τ, K.Mem M ↔ DecodedMem (h ▸ c) M) ∧
      (∀ {M N : Model K.τ} (f : Language.Embedding K.τ M.carrier N.carrier),
        K.Strong f ↔ DecodedStrong (h ▸ c) f)

end
end AEC
