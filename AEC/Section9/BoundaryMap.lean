module

public import AEC.Section9.FaceFamily

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A face is proper when it is not the full set of axes. For `n = 0` the only face is empty,
so the boundary is empty. -/
def IsProper {n : ℕ} (s : Set (Fin n)) : Prop :=
  s ≠ Set.univ

/-- **Definition 9.4.** The boundary `∂J` is the family of proper-axis projections, together with
their specified inclusions. A boundary map is a compatible family of arrows on those faces. -/
structure BoundaryMap (K : AbstractElementaryClass.{u}) {n : ℕ}
    (J Kf : FaceFamily K n) where
  onFace : ∀ {s : Set (Fin n)}, IsProper s →
    Language.Embedding K.τ (J.obj s).carrier (Kf.obj s).carrier
  onFace_strong : ∀ {s : Set (Fin n)} (hs : IsProper s), K.Strong (onFace hs)
  compat : ∀ {s t : Set (Fin n)} (hs : IsProper s) (ht : IsProper t) (hst : s ⊆ t),
    (onFace ht).comp (J.incl hst) = (Kf.incl hst).comp (onFace hs)

/-- A boundary isomorphism is a boundary map whose face maps are bijective. -/
def IsBoundaryIso {K : AbstractElementaryClass.{u}} {n : ℕ} {J Kf : FaceFamily K n}
    (h : BoundaryMap K J Kf) : Prop :=
  ∀ {s : Set (Fin n)} (hs : IsProper s), Function.Bijective (h.onFace hs)

end
end AEC
