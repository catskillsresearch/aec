module

public import AEC.Section2.OrderPresentation
public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u


open FirstOrder Cardinal

/-- A stable-diagram function in the sense of Proposition 4.2. `t` is a nondecreasing
cardinal function, `t(σ)` is a categoricity cardinal above `ℓ + σ`, and `same σ xs ys`
is equality of the canonical diagrams `D(xs; M) = D(ys; N)` for tuples of length at most `σ`. -/
structure StableDiagram (K : AbstractElementaryClass.{u}) where
  t : Cardinal.{u} → Cardinal.{u}
  mono : ∀ σ τ, σ ≤ τ → t σ ≤ t τ
  above : ∀ σ, aleph0 ≤ σ → K.τ.card + σ < t σ
  categoricity : ∀ σ, aleph0 ≤ σ → Categorical K (t σ)
  same : ∀ {σ : Cardinal.{u}} {α : Type u} {M N : Model K.τ},
    #α ≤ σ → K.Mem M → K.Mem N → t σ ≤ Model.card M → t σ ≤ Model.card N →
    (α → M.carrier) → (α → N.carrier) → Prop
  refl : ∀ {σ α M} (hα : #α ≤ σ) (hM : K.Mem M) (hcard : t σ ≤ Model.card M)
    (xs : α → M.carrier), same hα hM hM hcard hcard xs xs
  symm : ∀ {σ α M N} (hα : #α ≤ σ) (hM : K.Mem M) (hN : K.Mem N)
    (hMcard : t σ ≤ Model.card M) (hNcard : t σ ≤ Model.card N)
    (xs : α → M.carrier) (ys : α → N.carrier),
    same hα hM hN hMcard hNcard xs ys → same hα hN hM hNcard hMcard ys xs
  preserves_atomic : ∀ {σ α M N} (hα : #α ≤ σ) (hM : K.Mem M) (hN : K.Mem N)
    (hMcard : t σ ≤ Model.card M) (hNcard : t σ ≤ Model.card N)
    (xs : α → M.carrier) (ys : α → N.carrier),
    same hα hM hN hMcard hNcard xs ys →
      ∀ i j, xs i = xs j ↔ ys i = ys j


end
end AEC
