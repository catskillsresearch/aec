module

public import AEC.Section11.GeometricSystem

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- **Definition 12.1.** A prescribed boundary isomorphism is a family of pointed isomorphisms
`h_s : X_s⁻ → X_s⁺` for proper faces `s`, commuting with the displayed inclusions. -/
structure PrescribedBoundaryIso (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (X Y : GeometricSystem K n L) where
  onFace : ∀ (s : Finset (Fin n)), s ≠ Finset.univ →
    (X.vertex s).carrier ≃[K.τ] (Y.vertex s).carrier
  onFace_strong : ∀ (s : Finset (Fin n)) (hs : s ≠ Finset.univ),
    K.Strong (onFace s hs).toEmbedding
  comm : ∀ (s t : Finset (Fin n)) (hs : s ≠ Finset.univ) (ht : t ≠ Finset.univ)
    (hst : s ⊆ t),
    (onFace t ht).toEmbedding.comp (X.le hst) =
      (Y.le hst).comp (onFace s hs).toEmbedding

end
end AEC
