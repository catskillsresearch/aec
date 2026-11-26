module

public import AEC.Section5.PackageClauses

@[expose] public section

/-!
# Statement audit: working packages with no objects

`IsWorkingPackage W` (Definition 5.2 clauses) quantifies universally over the objects of `W`, so
any scheme whose object types are empty satisfies it. `WorkingScheme.emptied` replaces the
objects of a scheme by `PEmpty` over any unbounded class of levels, keeping only a term
template. Every formal statement of the shape "there is a working scheme `W` with
`IsWorkingPackage W` and conditions on `W.eligible` / universally quantified over objects"
is therefore satisfied degenerately; such proofs do **not** capture the English content.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}

/-- A scheme with no objects at the levels `E`, carrying the template `F`. -/
def WorkingScheme.emptied (F : TermTemplate K S) (E : Set Cardinal.{u})
    (hE : ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ E) : WorkingScheme K S where
  eligible := E
  eligible_unbounded := hE
  Object _ _ := PEmpty.{u + 1}
  asSystem _ X := X.elim
  vertex_card _ X := X.elim
  template := F
  permitted X := X.elim
  IsStructIso X := X.elim
  isStructIso_bijective X := X.elim
  isStructIso_refl X := X.elim
  structural_iso X := X.elim
  comp {_ _ _ _ _ _ X} := X.elim
  coherent {_ _ _ _ _ _ X} := X.elim
  DiagramEq X := X.elim
  diagram_refl X := X.elim
  diagram_symm X := X.elim
  diagram_trans X := X.elim
  diagram_empty X := X.elim
  diagram_preserved X := X.elim
  diagram_reindex X := X.elim
  diagram_restrict X := X.elim
  diagram_iso X := X.elim

/-- The emptied scheme vacuously satisfies every working-package clause except the
presentation clause of Definition 5.2(2) (which needs objects `F(I)`). -/
theorem WorkingScheme.emptied_isWorkingPackageCore (F : TermTemplate K S) (E : Set Cardinal.{u})
    (hE : ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ E) :
    IsWorkingPackageCore (WorkingScheme.emptied F E hE) :=
  ⟨⟨fun _ _ _ obj => (obj (Classical.arbitrary _)).elim⟩,
    ⟨fun _ _ X => X.elim⟩, ⟨fun X => X.elim⟩, ⟨fun X => X.elim⟩⟩

/-- A constant term template. -/
def TermTemplate.const (X : SystemObject K S) : TermTemplate K S where
  present _ := X
  onOrder _ := SystemArrow.refl X
  onOrder_id _ _ := rfl
  onOrder_comp _ _ _ _ := rfl

/-- The edgeless shape on `V`. -/
def SystemShape.discrete (V : Type u) [Finite V] : SystemShape.{u} :=
  ⟨V, inferInstance, fun _ _ => False⟩

/-- A constant system object on the edgeless shape. -/
def SystemObject.constDiscrete (V : Type u) [Finite V] (M : Model K.τ) (hM : K.Mem M) :
    SystemObject K (SystemShape.discrete V) where
  obj _ := M
  inK _ := hM
  edge h := h.elim
  edge_strong h := h.elim

end
end AEC
