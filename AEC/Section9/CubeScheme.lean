module

public import AEC.Section9.BoundaryMap
public import AEC.Section5.Results
public import AEC.Section6.Results

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- The `n`-cube shape: one vertex for each set of axes, with a specified map along every
inclusion. This is the shape of the `n`-fold marked increment `C_n` (Section 9). -/
def cubeShape (n : ℕ) : SystemShape.{u} where
  Vertex := ULift.{u} (Set (Fin n))
  vertexFinite := inferInstance
  specified s t := s.down ⊆ t.down

/-- A working scheme on the `n`-cube shape whose objects are functorial along inclusions, so
each object is a `FaceFamily` (its projections). This is the Lean carrier for the marked
scheme `C_n`: an object `J ∈ C_n` has proper projections `J ↾ s` for `s ⊊ n` and top `J`. -/
structure CubeScheme (K : AbstractElementaryClass.{u}) (n : ℕ) where
  W : WorkingScheme K (cubeShape.{u} n)
  edge_refl : ∀ {μ} (hμ : μ ∈ W.eligible) (X : W.Object μ hμ) (s : Set (Fin n)),
    (W.asSystem hμ X).edge (i := ⟨s⟩) (j := ⟨s⟩) (Set.Subset.refl s) =
      Language.Embedding.refl K.τ ((W.asSystem hμ X).obj ⟨s⟩).carrier
  edge_trans : ∀ {μ} (hμ : μ ∈ W.eligible) (X : W.Object μ hμ) {s t r : Set (Fin n)}
    (hst : s ⊆ t) (htr : t ⊆ r),
    (W.asSystem hμ X).edge (i := ⟨s⟩) (j := ⟨r⟩) (hst.trans htr) =
      ((W.asSystem hμ X).edge (i := ⟨t⟩) (j := ⟨r⟩) htr).comp
        ((W.asSystem hμ X).edge (i := ⟨s⟩) (j := ⟨t⟩) hst)

/-- The face family (projections and their inclusions) of an object of a cube scheme. -/
def CubeScheme.faces {K : AbstractElementaryClass.{u}} {n : ℕ} (C : CubeScheme K n)
    {μ : Cardinal.{u}} (hμ : μ ∈ C.W.eligible) (X : C.W.Object μ hμ) : FaceFamily K n where
  obj s := (C.W.asSystem hμ X).obj ⟨s⟩
  inK s := (C.W.asSystem hμ X).inK ⟨s⟩
  incl h := (C.W.asSystem hμ X).edge (i := ⟨_⟩) (j := ⟨_⟩) h
  incl_strong h := (C.W.asSystem hμ X).edge_strong (i := ⟨_⟩) (j := ⟨_⟩) h
  incl_refl s := C.edge_refl hμ X s
  incl_trans hst htu := C.edge_trans hμ X hst htu

/-- The standing properties of the marked scheme `C_n` that are expressible before the
marked-increment construction is formalized (Theorem 9.3): a working package on the cube
shape, with objects at every eligible level, at working levels only. These hypotheses rule
out the object-free (`WorkingScheme.emptied`) vacuity.

**Caveat:** `C_n` itself is the `n`-fold marked increment of the single-model scheme; that
construction (Section 8 marked pairs iterated over the axes) is not yet formalized, so the
Section 9 statements quantify over every `CubeScheme` with these properties. If one of them
fails for some such scheme, it must be specialized to the construction of Theorem 9.3. -/
structure CubeScheme.IsMarked {K : AbstractElementaryClass.{u}} {n : ℕ}
    (C : CubeScheme K n) : Prop where
  package : IsWorkingPackage C.W
  nonempty : ∀ μ (hμ : μ ∈ C.W.eligible), Nonempty (C.W.Object μ hμ)
  working : ∀ μ ∈ C.W.eligible, IsWorkingLevel μ

/-- A boundary occurrence of a cube-scheme object: an element of a proper projection, read as
an occurrence of the system. -/
def CubeScheme.boundaryOcc {K : AbstractElementaryClass.{u}} {n : ℕ} (C : CubeScheme K n)
    {μ : Cardinal.{u}} {hμ : μ ∈ C.W.eligible} (X : C.W.Object μ hμ) (s : Set (Fin n))
    (x : ((C.faces hμ X).obj s).carrier) : Occurrence K (cubeShape.{u} n) (C.W.asSystem hμ X) :=
  ⟨⟨s⟩, x⟩

end
end AEC
