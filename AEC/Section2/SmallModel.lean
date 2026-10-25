module

public import AEC.Section1.Model
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- A type of cardinality `lam`: the ordinals below the initial ordinal of `lam`,
repackaged by mathlib as a `Type u`. -/
abbrev Below (lam : Cardinal.{u}) := lam.ord.ToType

/-- A `τ`-structure carried by a set of ordinals of cardinality at most `lam`.
Lemma 2.2 represents small models on such ordinals. -/
structure SmallModel (τ : Tau.{u}) (lam : Cardinal.{u}) where
  domain : Set (Below lam)
  str : τ.Structure (↥domain)

instance (τ : Tau.{u}) (lam : Cardinal.{u}) (M : SmallModel τ lam) :
    τ.Structure (↥M.domain) := M.str

namespace SmallModel

/-- The underlying model of a small ordinal presentation. -/
def toModel {τ : Tau.{u}} {lam : Cardinal.{u}} (M : SmallModel τ lam) : Model τ where
  carrier := ↥M.domain
  str := M.str

end SmallModel

end
end AEC
