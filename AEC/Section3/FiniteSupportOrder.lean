module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Finsupp

/-- The index set of ordinals `< δ`. -/
abbrev OrdIndex (δ : _root_.Ordinal.{u}) := {i : _root_.Ordinal.{u} // i < δ}

/-- **Definition 3.1.** `Γδ = ℤ^{(δ)}`, integer vectors of finite support, ordered by the
greatest differing coordinate. -/
abbrev Gamma (δ : _root_.Ordinal.{u}) := Colex (OrdIndex δ →₀ ℤ)

/-- **Definition 3.1.** `H(δ) = ℚ^{(Γδ)}`, rational vectors of finite support on `Γδ`,
ordered by the greatest differing coordinate. As an index order it is this pure linear order. -/
abbrev HOrder (δ : _root_.Ordinal.{u}) := Colex (Gamma δ →₀ ℚ)

/-- The integer basis vector `eα`. -/
noncomputable def basisZ {δ : _root_.Ordinal.{u}} (α : OrdIndex δ) : Gamma δ :=
  toColex (single α (1 : ℤ))

/-- The rational basis vector `u_g`. -/
noncomputable def basisQ {δ : _root_.Ordinal.{u}} (g : Gamma δ) : HOrder δ :=
  toColex (single g (1 : ℚ))

end
end AEC
