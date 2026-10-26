module

public import AEC.Section1.LoewenheimSkolem
public import AEC.Section1.Categorical
public import AEC.Section2.SmallModel
public import AEC.Section3.OrbitRecordBound
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- Two tuples in one model lie in the same automorphism orbit when a strong
automorphism of the model carries one onto the other. -/
def SameAutOrbit (K : AbstractElementaryClass.{u}) (M : Model K.τ) {ι : Type u}
    (xs ys : ι → M.carrier) : Prop :=
  ∃ e : M.carrier ≃[K.τ] M.carrier, K.Strong e.toEmbedding ∧ ∀ i, e (xs i) = ys i

/-- The fixed name set of size `B(ℓ, θ)` for orbit namings. -/
abbrev OrbitName (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u}) : Type u :=
  Below (orbitRecordBound (ls K) θ)

/-- Section 3.3. An orbit naming injects the automorphism orbits of tuples of length
at most `θ` into the fixed set of size `B(ℓ, θ)` at every categoricity cardinal
`κ ≥ max(ℓ, θ⁺)`. Away from that regime the name is unconstrained. -/
structure OrbitNaming (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u}) where
  name : ∀ {M : Model K.τ} {ι : Type u}, K.Mem M → (ι → M.carrier) → #ι ≤ θ →
    OrbitName K θ
  name_spec : ∀ {M : Model K.τ} {ι : Type u} (hM : K.Mem M) (xs ys : ι → M.carrier)
    (hι : #ι ≤ θ),
    max (ls K) (Order.succ θ) ≤ Model.card M → Categorical K (Model.card M) →
      (name hM xs hι = name hM ys hι ↔ SameAutOrbit K M xs ys)
  name_iso : ∀ {M₁ M₂ : Model K.τ} (φ : M₁.carrier ≃[K.τ] M₂.carrier)
    (hM₁ : K.Mem M₁) (hM₂ : K.Mem M₂) {ι : Type u} (xs : ι → M₁.carrier) (hι : #ι ≤ θ),
    name hM₁ xs hι = name hM₂ (fun i => φ (xs i)) hι

end
end AEC
