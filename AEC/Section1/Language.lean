module

public import Mathlib.ModelTheory.Basic

@[expose] public section

namespace AEC
section

universe u

/-- The paper's language `τ`: a set-sized finitary first-order language.
Symbols are mathlib's `FirstOrder.Language`. -/
abbrev Tau := FirstOrder.Language.{u, u}

/-- The cardinality `|τ|` of the set of symbols of `τ`. -/
def languageCard (τ : Tau.{u}) : Cardinal.{u} := τ.card

end
end AEC
