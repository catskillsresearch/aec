module

public import AEC.Section1.LoewenheimSkolem
public import AEC.Section3.OrbitRecordBound

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

/-- Section 3.3. An orbit naming injects the automorphism orbits of tuples of length
at most `θ` into the fixed cardinal `B(ℓ, θ)`. The name of a tuple depends only on its orbit. -/
structure OrbitNaming (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u}) where
  ell : Cardinal.{u}
  ell_eq : ell = ls K
  name : ∀ {M : Model K.τ} {ι : Type u}, K.Mem M → (ι → M.carrier) → #ι ≤ θ → Cardinal.{u}
  name_bound : ∀ {M : Model K.τ} {ι : Type u} (hM : K.Mem M) (xs : ι → M.carrier)
    (hι : #ι ≤ θ), name hM xs hι < orbitRecordBound ell θ
  name_spec : ∀ {M : Model K.τ} {ι : Type u} (hM : K.Mem M) (xs ys : ι → M.carrier)
    (hι : #ι ≤ θ), name hM xs hι = name hM ys hι ↔ SameAutOrbit K M xs ys

end
end AEC
