module

public import AEC.Section5.TermTemplate
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- **Definition 5.2.** A working scheme on an eligible class `S`, a finite system shape, and a
term template. Objects at level `μ` have every vertex of cardinality `μ`. Arrows are the
permitted system arrows. `D`-diagrams are the equivalence `DiagramEq`. -/
structure WorkingScheme (K : AbstractElementaryClass.{u}) (S : SystemShape.{u}) where
  eligible : Set Cardinal.{u}
  eligible_unbounded : ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ eligible
  Object : ∀ μ : Cardinal.{u}, μ ∈ eligible → Type u
  asSystem : ∀ {μ} (h : μ ∈ eligible), Object μ h → SystemObject K S
  vertex_card : ∀ {μ} (h : μ ∈ eligible) (X : Object μ h) (v : S.Vertex),
    Model.card ((asSystem h X).obj v) = μ
  template : TermTemplate K S
  permitted : ∀ {μ ν} {hμ : μ ∈ eligible} {hν : ν ∈ eligible}
    (X : Object μ hμ) (Y : Object ν hν),
    SystemArrow K S (asSystem hμ X) (asSystem hν Y) → Prop
  /-- Arrows include every bijective system embedding. -/
  structural_iso : ∀ {μ} {hμ : μ ∈ eligible} (X Y : Object μ hμ)
    (f : SystemArrow K S (asSystem hμ X) (asSystem hμ Y)),
    (∀ v, Function.Bijective (f.onVertex v)) → permitted (X := X) (Y := Y) f
  /-- Arrows compose. -/
  comp : ∀ {μ ν ρ} {hμ : μ ∈ eligible} {hν : ν ∈ eligible} {hρ : ρ ∈ eligible}
    {X : Object μ hμ} {Y : Object ν hν} {Z : Object ρ hρ}
    (f : SystemArrow K S (asSystem hμ X) (asSystem hν Y))
    (g : SystemArrow K S (asSystem hν Y) (asSystem hρ Z)),
    permitted (X := X) (Y := Y) f → permitted (X := Y) (Y := Z) g →
      permitted (X := X) (Y := Z) (SystemArrow.comp f g)
  /-- If `X` sits in `Y` and both inclusions into `Z` are arrows, then `X → Y` is an arrow. -/
  coherent : ∀ {μ ν ρ} {hμ : μ ∈ eligible} {hν : ν ∈ eligible} {hρ : ρ ∈ eligible}
    {X : Object μ hμ} {Y : Object ν hν} {Z : Object ρ hρ}
    (xy : SystemArrow K S (asSystem hμ X) (asSystem hν Y))
    (xz : SystemArrow K S (asSystem hμ X) (asSystem hρ Z))
    (yz : SystemArrow K S (asSystem hν Y) (asSystem hρ Z)),
    permitted (X := X) (Y := Z) xz → permitted (X := Y) (Y := Z) yz →
    (∀ v, (yz.onVertex v).comp (xy.onVertex v) = xz.onVertex v) →
    permitted (X := X) (Y := Y) xy
  /-- Equality of `D`-diagrams of lists of occurrences. -/
  DiagramEq : ∀ {α : Type u} {μ ν} {hμ : μ ∈ eligible} {hν : ν ∈ eligible}
    (X : Object μ hμ) (Y : Object ν hν),
    (α → Occurrence K S (asSystem hμ X)) →
    (α → Occurrence K S (asSystem hν Y)) → Prop
  diagram_refl : ∀ {α μ} {hμ : μ ∈ eligible} (X : Object μ hμ)
    (xs : α → Occurrence K S (asSystem hμ X)),
    DiagramEq (X := X) (Y := X) xs xs
  diagram_symm : ∀ {α μ ν} {hμ : μ ∈ eligible} {hν : ν ∈ eligible}
    (X : Object μ hμ) (Y : Object ν hν)
    (xs : α → Occurrence K S (asSystem hμ X))
    (ys : α → Occurrence K S (asSystem hν Y)),
    DiagramEq (X := X) (Y := Y) xs ys → DiagramEq (X := Y) (Y := X) ys xs
  diagram_trans : ∀ {α μ ν ρ} {hμ : μ ∈ eligible} {hν : ν ∈ eligible} {hρ : ρ ∈ eligible}
    (X : Object μ hμ) (Y : Object ν hν) (Z : Object ρ hρ)
    (xs : α → Occurrence K S (asSystem hμ X))
    (ys : α → Occurrence K S (asSystem hν Y))
    (zs : α → Occurrence K S (asSystem hρ Z)),
    DiagramEq (X := X) (Y := Y) xs ys → DiagramEq (X := Y) (Y := Z) ys zs →
      DiagramEq (X := X) (Y := Z) xs zs
  /-- At one level, equal diagrams are exactly the lists matched by a structural isomorphism. -/
  diagram_iso : ∀ {α μ} {hμ : μ ∈ eligible} (X Y : Object μ hμ)
    (xs : α → Occurrence K S (asSystem hμ X))
    (ys : α → Occurrence K S (asSystem hμ Y)),
    DiagramEq (X := X) (Y := Y) xs ys ↔
      ∃ f : SystemArrow K S (asSystem hμ X) (asSystem hμ Y),
        (∀ v, Function.Bijective (f.onVertex v)) ∧
        ∀ i, ys i = ⟨(xs i).1, f.onVertex (xs i).1 (xs i).2⟩

end
end AEC
