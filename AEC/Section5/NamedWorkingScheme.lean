module

public import AEC.Section5.WorkingScheme
public import AEC.Section5.EligibleSubclass

@[expose] public section

/-!
# Named objects over a working scheme (Proposition 5.7, data layer)

Fix a working scheme `W`, an object `X0`, and a list `c` of occurrences of `X0`. This file
builds the data of the named scheme of Proposition 5.7 on top of `W`:

* `WorkingScheme.NamedObject`: an object of `W` together with a list realizing the diagram
  of `c`;
* `WorkingScheme.PreservesNames` / `WorkingScheme.NamedPermitted`: arrows preserving names;
* `WorkingScheme.NamedDiagramEq`: the diagram of a further list `xs` is the `W`-diagram of the
  names followed by `xs`.

`WorkingScheme.IsStructIso` is the scheme-specific isomorphism predicate. For the named scheme
it is `W.IsStructIso` on the underlying objects together with `PreservesNames`. The packer
`namedWorkingScheme` assembles these fields into a `WorkingScheme K S` on an eligible subclass.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}

/-- Image of an occurrence under a system arrow. -/
def SystemArrow.mapOcc {X Y : SystemObject K S} (f : SystemArrow K S X Y)
    (x : Occurrence K S X) : Occurrence K S Y :=
  ⟨x.1, f.onVertex x.1 x.2⟩

@[simp]
theorem SystemArrow.mapOcc_fst {X Y : SystemObject K S} (f : SystemArrow K S X Y)
    (x : Occurrence K S X) : (f.mapOcc x).1 = x.1 :=
  rfl

@[simp]
theorem SystemArrow.mapOcc_mk {X Y : SystemObject K S} (f : SystemArrow K S X Y)
    (v : S.Vertex) (a : (X.obj v).carrier) :
    f.mapOcc ⟨v, a⟩ = ⟨v, f.onVertex v a⟩ :=
  rfl

@[simp]
theorem SystemArrow.mapOcc_refl {X : SystemObject K S} (x : Occurrence K S X) :
    (SystemArrow.refl X).mapOcc x = x :=
  rfl

@[simp]
theorem SystemArrow.mapOcc_comp {X Y Z : SystemObject K S} (f : SystemArrow K S X Y)
    (g : SystemArrow K S Y Z) (x : Occurrence K S X) :
    (f.comp g).mapOcc x = g.mapOcc (f.mapOcc x) :=
  rfl

theorem SystemArrow.mapOcc_injective {X Y : SystemObject K S} (f : SystemArrow K S X Y) :
    Function.Injective f.mapOcc := by
  rintro ⟨v, a⟩ ⟨w, b⟩ h
  have h' : (⟨v, f.onVertex v a⟩ : Occurrence K S Y) = ⟨w, f.onVertex w b⟩ := h
  obtain ⟨rfl, h''⟩ := Sigma.mk.inj_iff.mp h'
  rw [(f.onVertex v).injective (eq_of_heq h'')]

/-- A vertexwise factorization `yz ∘ xy = xz` is a factorization on occurrences. -/
theorem SystemArrow.mapOcc_of_comp_eq {X Y Z : SystemObject K S} (xy : SystemArrow K S X Y)
    (xz : SystemArrow K S X Z) (yz : SystemArrow K S Y Z)
    (h : ∀ v, (yz.onVertex v).comp (xy.onVertex v) = xz.onVertex v) (x : Occurrence K S X) :
    yz.mapOcc (xy.mapOcc x) = xz.mapOcc x := by
  obtain ⟨v, a⟩ := x
  simp only [SystemArrow.mapOcc_mk, ← h v, Language.Embedding.comp_apply]

namespace WorkingScheme

variable (W : WorkingScheme K S) {μ0 : Cardinal.{u}} {hμ0 : μ0 ∈ W.eligible}
  (X0 : W.Object μ0 hμ0) {ι : Type u} (c : ι → Occurrence K S (W.asSystem hμ0 X0))

/-- An object of the named scheme of Proposition 5.7 at level `μ`: an object of `W` at `μ`
with a named realization of the diagram of the list `c` of `X0`. -/
structure NamedObject (μ : Cardinal.{u}) (hμ : μ ∈ W.eligible) where
  /-- The underlying object of `W`. -/
  base : W.Object μ hμ
  /-- The names: one occurrence of `base` for each entry of `c`. -/
  names : ι → Occurrence K S (W.asSystem hμ base)
  /-- The names realize the diagram of `c`. -/
  realizes : W.DiagramEq X0 base c names

variable {W X0 c}
variable {μ ν ρ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {hν : ν ∈ W.eligible}
  {hρ : ρ ∈ W.eligible}

/-- The system of shape `S` under a named object. -/
abbrev NamedObject.system (X : NamedObject W X0 c μ hμ) : SystemObject K S :=
  W.asSystem hμ X.base

/-- `X0` with the list `c` itself as names. -/
def NamedObject.self (W : WorkingScheme K S) {μ0 : Cardinal.{u}} {hμ0 : μ0 ∈ W.eligible}
    (X0 : W.Object μ0 hμ0) {ι : Type u} (c : ι → Occurrence K S (W.asSystem hμ0 X0)) :
    NamedObject W X0 c μ0 hμ0 where
  base := X0
  names := c
  realizes := W.diagram_refl X0 c

/-- An arrow out of `X0` that preserves the diagram of `c` names its target. This is the shape
of the realization clause in the statement of Proposition 5.7. -/
def NamedObject.ofArrow (Y : W.Object μ hμ)
    (arr : SystemArrow K S (W.asSystem hμ0 X0) (W.asSystem hμ Y))
    (h : W.DiagramEq X0 Y c (fun i => ⟨(c i).1, arr.onVertex (c i).1 (c i).2⟩)) :
    NamedObject W X0 c μ hμ where
  base := Y
  names i := arr.mapOcc (c i)
  realizes := h

/-- Transport the names of a named object along a structural isomorphism at the same level. -/
def NamedObject.mapIso (X : NamedObject W X0 c μ hμ) (Y : W.Object μ hμ)
    (f : SystemArrow K S X.system (W.asSystem hμ Y))
    (hIso : W.IsStructIso X.base Y f) : NamedObject W X0 c μ hμ where
  base := Y
  names i := f.mapOcc (X.names i)
  realizes :=
    W.diagram_trans X0 X.base Y c X.names _ X.realizes
      ((W.diagram_iso X.base Y X.names _).mpr ⟨f, hIso, fun _ => rfl⟩)

/-! ### Arrows preserving names -/

/-- The arrow `f` sends each name of `X` to the corresponding name of `Y`. -/
def PreservesNames (X : NamedObject W X0 c μ hμ) (Y : NamedObject W X0 c ν hν)
    (f : SystemArrow K S X.system Y.system) : Prop :=
  ∀ i, Y.names i = f.mapOcc (X.names i)

/-- Arrows of the named scheme: permitted arrows of `W` that preserve names. -/
def NamedPermitted (X : NamedObject W X0 c μ hμ) (Y : NamedObject W X0 c ν hν)
    (f : SystemArrow K S X.system Y.system) : Prop :=
  W.permitted X.base Y.base f ∧ PreservesNames X Y f

/-- Structural isomorphism of the named scheme: a structural iso of `W` that preserves names. -/
def NamedStructIso (X Y : NamedObject W X0 c μ hμ)
    (f : SystemArrow K S X.system Y.system) : Prop :=
  W.IsStructIso X.base Y.base f ∧ PreservesNames X Y f

theorem preservesNames_refl (X : NamedObject W X0 c μ hμ) :
    PreservesNames X X (SystemArrow.refl X.system) :=
  fun _ => rfl

theorem preservesNames_mapIso (X : NamedObject W X0 c μ hμ) (Y : W.Object μ hμ)
    (f : SystemArrow K S X.system (W.asSystem hμ Y))
    (hIso : W.IsStructIso X.base Y f) :
    PreservesNames X (X.mapIso Y f hIso) f :=
  fun _ => rfl

theorem PreservesNames.comp {X : NamedObject W X0 c μ hμ} {Y : NamedObject W X0 c ν hν}
    {Z : NamedObject W X0 c ρ hρ} {f : SystemArrow K S X.system Y.system}
    {g : SystemArrow K S Y.system Z.system}
    (hf : PreservesNames X Y f) (hg : PreservesNames Y Z g) :
    PreservesNames X Z (f.comp g) := by
  intro i
  rw [hg i, hf i, SystemArrow.mapOcc_comp]

/-- If `yz ∘ xy = xz` and both `xz` and `yz` preserve names, then so does `xy`. -/
theorem PreservesNames.of_comp_eq {X : NamedObject W X0 c μ hμ} {Y : NamedObject W X0 c ν hν}
    {Z : NamedObject W X0 c ρ hρ} (xy : SystemArrow K S X.system Y.system)
    {xz : SystemArrow K S X.system Z.system} {yz : SystemArrow K S Y.system Z.system}
    (hxz : PreservesNames X Z xz) (hyz : PreservesNames Y Z yz)
    (h : ∀ v, (yz.onVertex v).comp (xy.onVertex v) = xz.onVertex v) :
    PreservesNames X Y xy := by
  intro i
  apply yz.mapOcc_injective
  rw [← hyz i, hxz i, SystemArrow.mapOcc_of_comp_eq xy xz yz h]

/-- The identity is an arrow of the named scheme. -/
theorem namedPermitted_refl (X : NamedObject W X0 c μ hμ) :
    NamedPermitted X X (SystemArrow.refl X.system) :=
  ⟨W.structural_iso X.base X.base _ (W.isStructIso_refl X.base), preservesNames_refl X⟩

theorem namedStructIso_refl (X : NamedObject W X0 c μ hμ) :
    NamedStructIso X X (SystemArrow.refl X.system) :=
  ⟨W.isStructIso_refl X.base, preservesNames_refl X⟩

theorem namedStructIso_bijective (X Y : NamedObject W X0 c μ hμ)
    (f : SystemArrow K S X.system Y.system) (h : NamedStructIso X Y f) :
    ∀ v, Function.Bijective (f.onVertex v) :=
  W.isStructIso_bijective X.base Y.base f h.1

/-- `structural_iso` for the named scheme: every named structural iso is an arrow. -/
theorem namedPermitted_of_structIso (X Y : NamedObject W X0 c μ hμ)
    (f : SystemArrow K S X.system Y.system) (hIso : NamedStructIso X Y f) :
    NamedPermitted X Y f :=
  ⟨W.structural_iso X.base Y.base f hIso.1, hIso.2⟩

/-- `comp` for the named scheme. -/
theorem namedPermitted_comp {X : NamedObject W X0 c μ hμ} {Y : NamedObject W X0 c ν hν}
    {Z : NamedObject W X0 c ρ hρ} (f : SystemArrow K S X.system Y.system)
    (g : SystemArrow K S Y.system Z.system)
    (hf : NamedPermitted X Y f) (hg : NamedPermitted Y Z g) :
    NamedPermitted X Z (f.comp g) :=
  ⟨W.comp f g hf.1 hg.1, hf.2.comp hg.2⟩

/-- `coherent` for the named scheme. -/
theorem namedPermitted_coherent {X : NamedObject W X0 c μ hμ} {Y : NamedObject W X0 c ν hν}
    {Z : NamedObject W X0 c ρ hρ} (xy : SystemArrow K S X.system Y.system)
    (xz : SystemArrow K S X.system Z.system) (yz : SystemArrow K S Y.system Z.system)
    (hxz : NamedPermitted X Z xz) (hyz : NamedPermitted Y Z yz)
    (h : ∀ v, (yz.onVertex v).comp (xy.onVertex v) = xz.onVertex v) :
    NamedPermitted X Y xy :=
  ⟨W.coherent xy xz yz hxz.1 hyz.1 h, PreservesNames.of_comp_eq xy hxz.2 hyz.2 h⟩

/-! ### Diagrams over the names -/

/-- Diagram equality in the named scheme: the `W`-diagrams of the names followed by the
lists agree. -/
def NamedDiagramEq {α : Type u} (X : NamedObject W X0 c μ hμ) (Y : NamedObject W X0 c ν hν)
    (xs : α → Occurrence K S X.system) (ys : α → Occurrence K S Y.system) : Prop :=
  W.DiagramEq X.base Y.base (Sum.elim X.names xs) (Sum.elim Y.names ys)

/-- `diagram_refl` for the named scheme. -/
theorem namedDiagramEq_refl {α : Type u} (X : NamedObject W X0 c μ hμ)
    (xs : α → Occurrence K S X.system) : NamedDiagramEq X X xs xs :=
  W.diagram_refl X.base _

/-- `diagram_symm` for the named scheme. -/
theorem namedDiagramEq_symm {α : Type u} (X : NamedObject W X0 c μ hμ)
    (Y : NamedObject W X0 c ν hν) (xs : α → Occurrence K S X.system)
    (ys : α → Occurrence K S Y.system) (h : NamedDiagramEq X Y xs ys) :
    NamedDiagramEq Y X ys xs :=
  W.diagram_symm X.base Y.base _ _ h

/-- `diagram_trans` for the named scheme. -/
theorem namedDiagramEq_trans {α : Type u} (X : NamedObject W X0 c μ hμ)
    (Y : NamedObject W X0 c ν hν) (Z : NamedObject W X0 c ρ hρ)
    (xs : α → Occurrence K S X.system) (ys : α → Occurrence K S Y.system)
    (zs : α → Occurrence K S Z.system)
    (hxy : NamedDiagramEq X Y xs ys) (hyz : NamedDiagramEq Y Z ys zs) :
    NamedDiagramEq X Z xs zs :=
  W.diagram_trans X.base Y.base Z.base _ _ _ hxy hyz

/-- `diagram_iso` for the named scheme: at one level, two lists have the same diagram over
the names exactly when a named structural iso carries one list to the other. -/
theorem namedDiagramEq_iff_iso {α : Type u} (X Y : NamedObject W X0 c μ hμ)
    (xs : α → Occurrence K S X.system) (ys : α → Occurrence K S Y.system) :
    NamedDiagramEq X Y xs ys ↔
      ∃ f : SystemArrow K S X.system Y.system,
        NamedStructIso X Y f ∧ ∀ i, ys i = f.mapOcc (xs i) := by
  constructor
  · intro h
    obtain ⟨f, hIso, hf⟩ := (W.diagram_iso X.base Y.base _ _).mp h
    exact ⟨f, ⟨hIso, fun i => hf (Sum.inl i)⟩, fun i => hf (Sum.inr i)⟩
  · rintro ⟨f, ⟨hIso, hn⟩, hx⟩
    refine (W.diagram_iso X.base Y.base _ _).mpr ⟨f, hIso, ?_⟩
    rintro (i | i)
    · exact hn i
    · exact hx i

/-- The form of Proposition 5.8 for the named scheme: equal diagrams over the names are
exactly the lists matched by a named structural iso that is permitted. -/
theorem namedDiagramEq_iff_namedPermitted_iso {α : Type u} (X Y : NamedObject W X0 c μ hμ)
    (xs : α → Occurrence K S X.system) (ys : α → Occurrence K S Y.system) :
    NamedDiagramEq X Y xs ys ↔
      ∃ f : SystemArrow K S X.system Y.system,
        NamedStructIso X Y f ∧ NamedPermitted X Y f ∧
        ∀ i, ys i = f.mapOcc (xs i) := by
  rw [namedDiagramEq_iff_iso]
  constructor
  · rintro ⟨f, hIso, hx⟩
    exact ⟨f, hIso, namedPermitted_of_structIso X Y f hIso, hx⟩
  · rintro ⟨f, hIso, _hp, hx⟩
    exact ⟨f, hIso, hx⟩

/-- Two named objects at one level are isomorphic by an arrow of the named scheme. -/
theorem exists_namedPermitted_iso (X Y : NamedObject W X0 c μ hμ) :
    ∃ f : SystemArrow K S X.system Y.system,
      NamedStructIso X Y f ∧ NamedPermitted X Y f := by
  have h : W.DiagramEq X.base Y.base X.names Y.names :=
    W.diagram_trans X.base X0 Y.base _ _ _
      (W.diagram_symm X0 X.base _ _ X.realizes) Y.realizes
  obtain ⟨f, hIso, hf⟩ := (W.diagram_iso X.base Y.base _ _).mp h
  exact ⟨f, ⟨hIso, hf⟩, namedPermitted_of_structIso X Y f ⟨hIso, hf⟩⟩

/-- At one level, the empty lists of any two named objects have the same diagram over the
names. -/
theorem namedDiagramEq_empty (X Y : NamedObject W X0 c μ hμ) :
    NamedDiagramEq X Y (fun i : PEmpty.{u + 1} => i.elim) (fun i : PEmpty.{u + 1} => i.elim) := by
  obtain ⟨f, hIso, _hp⟩ := exists_namedPermitted_iso X Y
  exact (namedDiagramEq_iff_iso X Y _ _).mpr ⟨f, hIso, fun i => i.elim⟩

/-- Equal diagrams over the names restrict to equal diagrams of the further lists in `W`. -/
theorem NamedDiagramEq.diagramEq {α : Type u} {X : NamedObject W X0 c μ hμ}
    {Y : NamedObject W X0 c ν hν}
    {xs : α → Occurrence K S X.system} {ys : α → Occurrence K S Y.system}
    (h : NamedDiagramEq X Y xs ys) : W.DiagramEq X.base Y.base xs ys :=
  (W.diagram_restrict X.base Y.base X.names Y.names xs ys h).2

/-- At one level, a named structural iso preserves every diagram over the names. -/
theorem namedDiagramEq_mapOcc {α : Type u} (X Y : NamedObject W X0 c μ hμ)
    (f : SystemArrow K S X.system Y.system) (hIso : NamedStructIso X Y f)
    (xs : α → Occurrence K S X.system) :
    NamedDiagramEq X Y xs (fun i => f.mapOcc (xs i)) :=
  (namedDiagramEq_iff_iso X Y xs _).mpr ⟨f, hIso, fun _ => rfl⟩

/-- Reindexing for named diagrams, via reindexing of the concatenated `W`-diagrams. -/
theorem namedDiagramEq_reindex {α β : Type u} (X : NamedObject W X0 c μ hμ)
    (Y : NamedObject W X0 c ν hν) (e : α ≃ β)
    (xs : α → Occurrence K S X.system) (ys : α → Occurrence K S Y.system) :
    NamedDiagramEq X Y xs ys ↔
      NamedDiagramEq X Y (fun b => xs (e.symm b)) (fun b => ys (e.symm b)) := by
  let e' : (ι ⊕ α) ≃ (ι ⊕ β) := Equiv.sumCongr (Equiv.refl ι) e
  have heqX : (fun b => Sum.elim X.names xs (e'.symm b)) =
      Sum.elim X.names (fun b => xs (e.symm b)) := by
    funext i; cases i <;> rfl
  have heqY : (fun b => Sum.elim Y.names ys (e'.symm b)) =
      Sum.elim Y.names (fun b => ys (e.symm b)) := by
    funext i; cases i <;> rfl
  constructor
  · intro h
    have h' :=
      (W.diagram_reindex X.base Y.base e' (Sum.elim X.names xs) (Sum.elim Y.names ys)).mp h
    simpa [NamedDiagramEq, heqX, heqY] using h'
  · intro h
    refine (W.diagram_reindex X.base Y.base e' (Sum.elim X.names xs) (Sum.elim Y.names ys)).mpr ?_
    simpa [NamedDiagramEq, heqX, heqY] using h

/-- `ι ⊕ (α ⊕ β) ≃ (ι ⊕ α) ⊕ β`, associating names with the left further list. -/
def sumAssocNamesLeft (ι α β : Type u) : ι ⊕ (α ⊕ β) ≃ (ι ⊕ α) ⊕ β where
  toFun
    | Sum.inl j => Sum.inl (Sum.inl j)
    | Sum.inr (Sum.inl a) => Sum.inl (Sum.inr a)
    | Sum.inr (Sum.inr b) => Sum.inr b
  invFun
    | Sum.inl (Sum.inl j) => Sum.inl j
    | Sum.inl (Sum.inr a) => Sum.inr (Sum.inl a)
    | Sum.inr b => Sum.inr (Sum.inr b)
  left_inv := by
    rintro (j | (a | b)) <;> rfl
  right_inv := by
    rintro ((j | a) | b) <;> rfl

/-- `ι ⊕ (α ⊕ β) ≃ (ι ⊕ β) ⊕ α`, grouping names with the right further list. -/
def sumShuffleNamesRight (ι α β : Type u) : ι ⊕ (α ⊕ β) ≃ (ι ⊕ β) ⊕ α where
  toFun
    | Sum.inl j => Sum.inl (Sum.inl j)
    | Sum.inr (Sum.inl a) => Sum.inr a
    | Sum.inr (Sum.inr b) => Sum.inl (Sum.inr b)
  invFun
    | Sum.inl (Sum.inl j) => Sum.inl j
    | Sum.inl (Sum.inr b) => Sum.inr (Sum.inr b)
    | Sum.inr a => Sum.inr (Sum.inl a)
  left_inv := by
    rintro (j | (a | b)) <;> rfl
  right_inv := by
    rintro ((j | b) | a) <;> rfl

/-- Restriction for named diagrams: reassociate (or shuffle) so each further list sits next
to the names, then restrict in `W`. -/
theorem namedDiagramEq_restrict {α β : Type u} (X : NamedObject W X0 c μ hμ)
    (Y : NamedObject W X0 c ν hν)
    (xs : α → Occurrence K S X.system) (ys : α → Occurrence K S Y.system)
    (xs' : β → Occurrence K S X.system) (ys' : β → Occurrence K S Y.system)
    (h : NamedDiagramEq X Y (Sum.elim xs xs') (Sum.elim ys ys')) :
    NamedDiagramEq X Y xs ys ∧ NamedDiagramEq X Y xs' ys' := by
  have hLeft : NamedDiagramEq X Y xs ys := by
    let e := sumAssocNamesLeft ι α β
    let unX := Sum.elim X.names (Sum.elim xs xs')
    let unY := Sum.elim Y.names (Sum.elim ys ys')
    let asX := Sum.elim (Sum.elim X.names xs) xs'
    let asY := Sum.elim (Sum.elim Y.names ys) ys'
    have heqX : (fun b => unX (e.symm b)) = asX := by
      funext b; cases b with
        | inl ia => cases ia <;> rfl
        | inr _ => rfl
    have heqY : (fun b => unY (e.symm b)) = asY := by
      funext b; cases b with
        | inl ia => cases ia <;> rfl
        | inr _ => rfl
    have hAssoc : W.DiagramEq X.base Y.base asX asY := by
      have h' := (W.diagram_reindex X.base Y.base e unX unY).mp (by
        simpa [NamedDiagramEq, unX, unY] using h)
      simpa [heqX, heqY] using h'
    exact (W.diagram_restrict X.base Y.base
      (Sum.elim X.names xs) (Sum.elim Y.names ys) xs' ys' hAssoc).1
  have hRight : NamedDiagramEq X Y xs' ys' := by
    let e := sumShuffleNamesRight ι α β
    let unX := Sum.elim X.names (Sum.elim xs xs')
    let unY := Sum.elim Y.names (Sum.elim ys ys')
    let shX : (ι ⊕ β) ⊕ α → Occurrence K S X.system :=
      Sum.elim (Sum.elim X.names xs') xs
    let shY : (ι ⊕ β) ⊕ α → Occurrence K S Y.system :=
      Sum.elim (Sum.elim Y.names ys') ys
    have heqX : (fun b => unX (e.symm b)) = shX := by
      funext b; cases b with
        | inl jb => cases jb <;> rfl
        | inr _ => rfl
    have heqY : (fun b => unY (e.symm b)) = shY := by
      funext b; cases b with
        | inl jb => cases jb <;> rfl
        | inr _ => rfl
    have hShuf : W.DiagramEq X.base Y.base shX shY := by
      have h' := (W.diagram_reindex X.base Y.base e unX unY).mp (by
        simpa [NamedDiagramEq, unX, unY] using h)
      simpa [heqX, heqY] using h'
    exact (W.diagram_restrict X.base Y.base
      (Sum.elim X.names xs') (Sum.elim Y.names ys') xs ys hShuf).1
  exact ⟨hLeft, hRight⟩

/-! ### Packing into a `WorkingScheme` -/

/-- The named working scheme of Proposition 5.7 on an eligible subclass `T ⊆ W.eligible`.
Objects are named realizations of the fixed diagram of `c`; arrows preserve names;
structural isomorphisms are structural isos of `W` that preserve names. -/
noncomputable def namedWorkingScheme
    (W : WorkingScheme K S) {μ0 : Cardinal.{u}} {hμ0 : μ0 ∈ W.eligible}
    (X0 : W.Object μ0 hμ0) {ι : Type u}
    (c : ι → Occurrence K S (W.asSystem hμ0 X0))
    (T : Set Cardinal.{u}) (hT : EligibleSubclass W.eligible T) :
    WorkingScheme K S where
  eligible := T
  eligible_unbounded := hT.2.1
  Object := fun μ hμ => NamedObject W X0 c μ (EligibleSubclass.mem_source hT hμ)
  asSystem := fun {μ} hμ X => X.system
  vertex_card := fun {μ} hμ X v =>
    W.vertex_card (EligibleSubclass.mem_source hT hμ) X.base v
  template := W.template
  permitted := fun {μ ν} {hμ} {hν} X Y f => NamedPermitted X Y f
  IsStructIso := fun {μ} {hμ} X Y f => NamedStructIso X Y f
  isStructIso_bijective := fun {μ} {hμ} X Y f h => namedStructIso_bijective X Y f h
  isStructIso_refl := fun {μ} {hμ} X => namedStructIso_refl X
  structural_iso := fun {μ} {hμ} X Y f h => namedPermitted_of_structIso X Y f h
  comp := fun {μ ν ρ} {hμ} {hν} {hρ} {X Y Z} f g hf hg => namedPermitted_comp f g hf hg
  coherent := fun {μ ν ρ} {hμ} {hν} {hρ} {X Y Z} xy xz yz hxz hyz h =>
    namedPermitted_coherent xy xz yz hxz hyz h
  DiagramEq := fun {α μ ν} {hμ} {hν} X Y xs ys => NamedDiagramEq X Y xs ys
  diagram_refl := fun {α μ} {hμ} X xs => namedDiagramEq_refl X xs
  diagram_symm := fun {α μ ν} {hμ} {hν} X Y xs ys h => namedDiagramEq_symm X Y xs ys h
  diagram_trans := fun {α μ ν ρ} {hμ} {hν} {hρ} X Y Z xs ys zs hxy hyz =>
    namedDiagramEq_trans X Y Z xs ys zs hxy hyz
  diagram_empty := fun {μ ν} {hμ} {hν} X Y => by
    change W.DiagramEq X.base Y.base
      (Sum.elim X.names (fun i : PEmpty.{u + 1} => i.elim))
      (Sum.elim Y.names (fun i : PEmpty.{u + 1} => i.elim))
    have h : W.DiagramEq X.base Y.base X.names Y.names :=
      W.diagram_trans X.base X0 Y.base X.names c Y.names
        (W.diagram_symm X0 X.base c X.names X.realizes) Y.realizes
    let e := (Equiv.sumEmpty (β := PEmpty.{u + 1}) ι).symm
    have heqX : (fun b => X.names (e.symm b)) =
        Sum.elim X.names (fun i : PEmpty.{u + 1} => i.elim) := by
      funext i; cases i with
        | inl _ => rfl
        | inr v => cases v
    have heqY : (fun b => Y.names (e.symm b)) =
        Sum.elim Y.names (fun i : PEmpty.{u + 1} => i.elim) := by
      funext i; cases i with
        | inl _ => rfl
        | inr v => cases v
    have h' := (W.diagram_reindex X.base Y.base e X.names Y.names).mp h
    simpa [heqX, heqY] using h'
  diagram_preserved := fun {α μ ν} {hμ} {hν} X Y f hf xs => by
    change W.DiagramEq X.base Y.base (Sum.elim X.names xs)
      (Sum.elim Y.names (fun i => f.mapOcc (xs i)))
    have hW : W.DiagramEq X.base Y.base (Sum.elim X.names xs)
        (fun i => f.mapOcc (Sum.elim X.names xs i)) :=
      W.diagram_preserved X.base Y.base f hf.1 (Sum.elim X.names xs)
    convert hW using 1
    funext i
    cases i with
    | inl j => exact hf.2 j
    | inr j => rfl
  diagram_reindex := fun {α β μ ν} {hμ} {hν} X Y e xs ys =>
    namedDiagramEq_reindex X Y e xs ys
  diagram_restrict := fun {α β μ ν} {hμ} {hν} X Y xs ys xs' ys' h =>
    namedDiagramEq_restrict X Y xs ys xs' ys' h
  diagram_iso := fun {α μ} {hμ} X Y xs ys => by
    simpa [SystemArrow.mapOcc] using namedDiagramEq_iff_iso X Y xs ys

end WorkingScheme

end
end AEC
