module

public import AEC.Section5.WorkingScheme
public import AEC.Section5.PackageClauses
public import AEC.Section4.ClosedLevels
public import AEC.Section4.Prop43BAF
public import AEC.Section4.BoundedDiagramLift
public import AEC.Section4.StableDiagramConstruction
public import AEC.Section4.CountableClosure
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Order.InitialSeg

@[expose] public section

/-!
# The single-model working scheme (Proposition 5.6, data layer)

Fix a stable-diagram function `D` (Proposition 4.2), a bound `g`, and an order presentation `E`
(Theorem 2.6). The levels are the closure points of `{D.t, g}` above `ℓ = LS(K)`: strong limits
of countable cofinality strictly closed under `D.t` and `g`. At such a level `K` is categorical
and bounded lists with equal `D`-diagrams are matched by an isomorphism (Proposition 4.3).

* `oneVertexShape`, `oneVertexObject`, `oneVertexArrow`: systems with a single vertex.
* `orderPresentationTemplate`: the term template `I ↦ E(I)`.
* `SMObject K μ`: a `K`-model coded on the fixed carrier `μ.ord.ToType`, so that the objects at
  a level form a type in `Type u`.
* `SingleModelData.chart`: an isomorphism of an object at `μ` with `E(μ)`, by categoricity, and
  `SingleModelData.push`: the resulting strong map into `E(ρ)` for a level `ρ ≥ μ`.
* `SingleModelData.DiagramEq`: equality of `D`-diagrams. For a list bounded at both levels it is
  `D.same` for the two lists in their own models (`diagramEq_iff_sameD`). In general the two
  lists are compared, by `D.same`, inside the presentations `E(ρ)` at the levels `ρ` at which
  they are bounded, after the charts. This makes the comparison an equivalence relation on
  lists of every length, compatible with restriction and reindexing.
* `SingleModelData.scheme`: the working scheme. Arrows are all strong maps, structural
  isomorphisms are the bijective ones.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

/-! ## Systems with one vertex -/

/-- The system shape with a single vertex and no specified map. -/
def oneVertexShape : SystemShape.{u} := ⟨PUnit, inferInstance, fun _ _ => False⟩

instance : Nonempty (oneVertexShape.{u}).Vertex := ⟨PUnit.unit⟩

instance : Subsingleton (oneVertexShape.{u}).Vertex := inferInstanceAs (Subsingleton PUnit)

variable {K : AbstractElementaryClass.{u}}

/-- A single `K`-model as a system of shape `oneVertexShape`. -/
def oneVertexObject (K : AbstractElementaryClass.{u}) (M : Model K.τ) (hM : K.Mem M) :
    SystemObject K oneVertexShape :=
  ⟨fun _ => M, fun _ => hM, fun h => h.elim, fun h => h.elim⟩

/-- A strong map as an arrow of one-vertex systems. -/
def oneVertexArrow {M N : Model K.τ} {hM : K.Mem M} {hN : K.Mem N}
    (f : Language.Embedding K.τ M.carrier N.carrier) (hf : K.Strong f) :
    SystemArrow K oneVertexShape (oneVertexObject K M hM) (oneVertexObject K N hN) :=
  ⟨fun _ => f, fun _ => hf, fun h => h.elim⟩

/-- The element under an occurrence of a one-vertex system. -/
def oneVertexVal {M : Model K.τ} {hM : K.Mem M}
    (x : Occurrence K oneVertexShape (oneVertexObject K M hM)) : M.carrier :=
  x.2

/-- An element as an occurrence of a one-vertex system. -/
def oneVertexOcc {M : Model K.τ} {hM : K.Mem M} (a : M.carrier) :
    Occurrence K oneVertexShape (oneVertexObject K M hM) :=
  ⟨PUnit.unit, a⟩

@[simp]
theorem oneVertexVal_occ {M : Model K.τ} {hM : K.Mem M} (a : M.carrier) :
    oneVertexVal (hM := hM) (oneVertexOcc a) = a :=
  rfl

@[simp]
theorem oneVertexOcc_val {M : Model K.τ} {hM : K.Mem M}
    (x : Occurrence K oneVertexShape (oneVertexObject K M hM)) :
    oneVertexOcc (oneVertexVal x) = x :=
  rfl

/-- The term template of an order presentation: `I ↦ E(I)`, with `E.map` on order embeddings. -/
def orderPresentationTemplate (E : OrderPresentation K)
    (hE : ∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Mem (E.obj I)) :
    TermTemplate K oneVertexShape where
  present I := oneVertexObject K (E.obj I) (hE I)
  onOrder f := oneVertexArrow (E.map f) (E.map_strong f)
  onOrder_id := fun {I} _ _ v x => by
    change E.map (OrderIso.refl I).toOrderEmbedding x = x
    rw [E.map_id]
    rfl
  onOrder_comp := fun {I J P} _ _ _ _ _ _ f g v x => by
    change E.map (f.trans g) x = E.map g (E.map f x)
    rw [E.map_comp]
    rfl

/-! ## Diagram equality at the canonical bound -/

/-- `D`-diagram equality of two lists at the canonical bound `#α ⊔ ℵ₀`, in models above the
threshold `t(#α ⊔ ℵ₀)`. -/
def StableDiagram.SameD (D : StableDiagram K) {α : Type u} (M N : Model K.τ)
    (xs : α → M.carrier) (ys : α → N.carrier) : Prop :=
  ∃ (hM : K.Mem M) (hN : K.Mem N) (hMc : D.t (max #α ℵ₀) ≤ Model.card M)
    (hNc : D.t (max #α ℵ₀) ≤ Model.card N),
    D.same (le_max_left _ _) hM hN hMc hNc xs ys

theorem StableDiagram.SameD.symm {D : StableDiagram K} {α : Type u} {M N : Model K.τ}
    {xs : α → M.carrier} {ys : α → N.carrier} (h : D.SameD M N xs ys) : D.SameD N M ys xs := by
  obtain ⟨hM, hN, hMc, hNc, h⟩ := h
  exact ⟨hN, hM, hNc, hMc, D.symm _ hM hN hMc hNc xs ys h⟩

theorem StableDiagram.SameD.trans {D : StableDiagram K} {α : Type u} {M N Q : Model K.τ}
    {xs : α → M.carrier} {ys : α → N.carrier} {zs : α → Q.carrier}
    (h₁ : D.SameD M N xs ys) (h₂ : D.SameD N Q ys zs) : D.SameD M Q xs zs := by
  obtain ⟨hM, hN, hMc, hNc, h₁⟩ := h₁
  obtain ⟨_, hQ, _, hQc, h₂⟩ := h₂
  exact ⟨hM, hQ, hMc, hQc, D.trans _ hM hN hQ hMc hNc hQc xs ys zs h₁ h₂⟩

/-- A stable-diagram function gives categoricity in unboundedly many cardinals. -/
theorem StableDiagram.categoricalUnbounded (D : StableDiagram K) : CategoricalUnbounded K where
  unbounded κ := by
    have hσ : ℵ₀ ≤ max κ ℵ₀ := le_max_right _ _
    exact ⟨D.t (max κ ℵ₀), (le_max_left κ ℵ₀).trans (sigma_lt_t D hσ).le, D.categoricity _ hσ⟩

/-! ## Objects coded on a fixed carrier -/

/-- A `K`-model of cardinality `μ`, coded as a structure on the carrier `μ.ord.ToType`. -/
def SMObject (K : AbstractElementaryClass.{u}) (μ : Cardinal.{u}) : Type u :=
  { s : K.τ.Structure μ.ord.ToType // K.Mem ⟨μ.ord.ToType, s⟩ }

namespace SMObject

variable {μ : Cardinal.{u}}

/-- The model under a coded object. -/
def model (X : SMObject K μ) : Model K.τ := ⟨μ.ord.ToType, X.1⟩

theorem mem (X : SMObject K μ) : K.Mem X.model := X.2

theorem card (X : SMObject K μ) : Model.card X.model = μ :=
  Cardinal.mk_ord_toType μ

/-- The one-vertex system of a coded object. -/
def system (X : SMObject K μ) : SystemObject K oneVertexShape :=
  oneVertexObject K X.model X.mem

/-- The element under an occurrence. -/
def val (X : SMObject K μ) (x : Occurrence K oneVertexShape X.system) : X.model.carrier :=
  oneVertexVal x

/-- An element as an occurrence. -/
def occ (X : SMObject K μ) (a : X.model.carrier) : Occurrence K oneVertexShape X.system :=
  oneVertexOcc a

@[simp]
theorem val_occ (X : SMObject K μ) (a : X.model.carrier) : X.val (X.occ a) = a :=
  rfl

@[simp]
theorem occ_val (X : SMObject K μ) (x : Occurrence K oneVertexShape X.system) :
    X.occ (X.val x) = x :=
  rfl

/-- A bijection of a model of cardinality `μ` with the fixed carrier. -/
noncomputable def carrierEquiv (M : Model K.τ) (hc : Model.card M = μ) :
    M.carrier ≃ μ.ord.ToType :=
  Classical.choice (Cardinal.eq.mp (hc.trans (Cardinal.mk_ord_toType μ).symm))

/-- A model of cardinality `μ` in `K`, transported to the fixed carrier. -/
noncomputable def ofModel (M : Model K.τ) (hM : K.Mem M) (hc : Model.card M = μ) :
    SMObject K μ :=
  ⟨(carrierEquiv M hc).inducedStructure, K.iso_closed
    (N := ⟨μ.ord.ToType, (carrierEquiv M hc).inducedStructure⟩)
    ⟨(carrierEquiv M hc).inducedStructureEquiv⟩ hM⟩

/-- The transported object is isomorphic to the model it codes. -/
noncomputable def ofModelEquiv (M : Model K.τ) (hM : K.Mem M) (hc : Model.card M = μ) :
    M.carrier ≃[K.τ] (ofModel M hM hc).model.carrier :=
  (carrierEquiv M hc).inducedStructureEquiv

end SMObject

/-! ## The well-orders of the levels -/

/-- A nonempty well-order of cardinality `μ` (for `μ ≥ 1`). -/
abbrev lvlOrder (μ : Cardinal.{u}) : Type u := (max μ 1).ord.ToType

instance (μ : Cardinal.{u}) : Nonempty (lvlOrder μ) := by
  rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_ord_toType]
  exact (zero_lt_one.trans_le (le_max_right μ 1)).ne'

theorem mk_lvlOrder {μ : Cardinal.{u}} (hμ : ℵ₀ ≤ μ) : #(lvlOrder μ) = μ := by
  rw [Cardinal.mk_ord_toType, max_eq_left (one_le_aleph0.trans hμ)]

/-- For `μ ≤ ρ`, the well-order of `μ` is an initial segment of the well-order of `ρ`. -/
noncomputable def lvlSeg {μ ρ : Cardinal.{u}} (h : μ ≤ ρ) : lvlOrder μ ≤i lvlOrder ρ :=
  Classical.choice
    ((Ordinal.type_le_iff (r := ((· < ·) : lvlOrder μ → lvlOrder μ → Prop))
      (s := ((· < ·) : lvlOrder ρ → lvlOrder ρ → Prop))).mp (by
        rw [Ordinal.type_toType, Ordinal.type_toType]
        exact Cardinal.ord_le_ord.mpr (max_le_max h le_rfl)))

/-- The order embedding of the well-order of `μ` into the well-order of `ρ ≥ μ`. -/
noncomputable def lvlEmb {μ ρ : Cardinal.{u}} (h : μ ≤ ρ) : lvlOrder μ ↪o lvlOrder ρ :=
  (lvlSeg h).toOrderEmbedding

/-- The level embeddings compose: initial segments of well-orders are unique. -/
theorem lvlEmb_trans {μ ρ κ : Cardinal.{u}} (h₁ : μ ≤ ρ) (h₂ : ρ ≤ κ) :
    (lvlEmb h₁).trans (lvlEmb h₂) = lvlEmb (h₁.trans h₂) := by
  refine RelEmbedding.ext fun x => ?_
  exact InitialSeg.eq ((lvlSeg h₁).trans (lvlSeg h₂)) (lvlSeg (h₁.trans h₂)) x

/-! ## The data of the single-model scheme -/

/-- The data of the single-model scheme of Proposition 5.6: a stable-diagram function, a bound
`g`, and an order presentation. The bound `g` is required to be a `PlacedTester` so closed
levels (`ClosedLevel K E D g μ`) are available at every eligible `μ` (Thm 4.11 / 6.6). -/
structure SingleModelData (K : AbstractElementaryClass.{u}) where
  /-- The stable-diagram function of Proposition 4.2. -/
  D : StableDiagram K
  /-- A further bound under which the levels are closed. -/
  g : Cardinal.{u} → Cardinal.{u}
  /-- The order presentation of Theorem 2.6. -/
  E : OrderPresentation K
  /-- The presentations are models of `K`. -/
  hE : ∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Mem (E.obj I)
  /-- `g` is a placed testing bound (Proposition 4.8). -/
  tester : PlacedTester K E D g

namespace SingleModelData

variable (P : SingleModelData K)

/-- The levels: closure points of `{D.t, g}` above `ℓ = LS(K)`. -/
def eligible : Set Cardinal.{u} := {μ | IsClosurePoint {P.D.t, P.g} μ ∧ ls K < μ}

variable {P}
variable {μ ν ρ κ : Cardinal.{u}}

theorem aleph0_le (hμ : μ ∈ P.eligible) : ℵ₀ ≤ μ := hμ.1.working.infinite

theorem ls_lt (hμ : μ ∈ P.eligible) : ls K < μ := hμ.2

/-- The levels are strictly closed under `D.t`. -/
theorem t_lt (hμ : μ ∈ P.eligible) {σ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (h : σ < μ) :
    P.D.t σ < μ :=
  (hμ.1.closed P.D.t (Set.mem_insert _ _)).below σ hσ h

theorem aleph0_lt (hμ : μ ∈ P.eligible) : ℵ₀ < μ :=
  (isLSBound_ls K).1.trans_lt hμ.2

theorem max_mem (hμ : μ ∈ P.eligible) (hν : ν ∈ P.eligible) : max μ ν ∈ P.eligible := by
  rcases le_total μ ν with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

variable (P) in
/-- The levels are unbounded (the countable closure construction after Proposition 4.3). -/
theorem exists_ge (κ : Cardinal.{u}) : ∃ μ, κ ≤ μ ∧ μ ∈ P.eligible := by
  obtain ⟨μ, hle, hμ⟩ := exists_closurePoint_ge P.D.t P.g (max κ (Order.succ (ls K)))
  exact ⟨μ, (le_max_left _ _).trans hle, hμ,
    (Order.lt_succ _).trans_le ((le_max_right _ _).trans hle)⟩

/-- `K` is categorical at every level (Proposition 4.3). -/
theorem categorical (hμ : μ ∈ P.eligible) : Categorical K μ := by
  haveI := P.D.categoricalUnbounded
  exact categorical_of_closurePoint P.D hμ.1 hμ.2

theorem t_le (hρ : ρ ∈ P.eligible) {M : Model K.τ} (hc : Model.card M = ρ)
    {σ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (h : σ < ρ) : P.D.t σ ≤ Model.card M := by
  rw [hc]
  exact (t_lt hρ hσ h).le

/-! ### `D`-diagrams of bounded lists in models at the levels -/

theorem sameD_refl (hρ : ρ ∈ P.eligible) {M : Model K.τ} (hM : K.Mem M)
    (hc : Model.card M = ρ) {α : Type u} (xs : α → M.carrier) (hα : #α < ρ) :
    P.D.SameD M M xs xs := by
  have hMc := t_le hρ hc (le_max_right #α ℵ₀) (max_lt hα (aleph0_lt hρ))
  exact ⟨hM, hM, hMc, hMc, P.D.refl _ hM hMc xs⟩

/-- Proposition 4.2: strong maps preserve the diagrams of bounded lists. -/
theorem sameD_of_strong (hμ : μ ∈ P.eligible) (hν : ν ∈ P.eligible) {M N : Model K.τ}
    (hcM : Model.card M = μ) (hcN : Model.card N = ν)
    (f : Language.Embedding K.τ M.carrier N.carrier) (hf : K.Strong f) {α : Type u}
    (xs : α → M.carrier) (ys : α → N.carrier) (hxy : ∀ i, f (xs i) = ys i)
    (hαμ : #α < μ) (hαν : #α < ν) : P.D.SameD M N xs ys := by
  have hM := K.strong_mem_dom f hf
  have hN := K.strong_mem_cod f hf
  have hMc := t_le hμ hcM (le_max_right #α ℵ₀) (max_lt hαμ (aleph0_lt hμ))
  have hNc := t_le hν hcN (le_max_right #α ℵ₀) (max_lt hαν (aleph0_lt hν))
  exact ⟨hM, hN, hMc, hNc,
    P.D.of_strong _ hM hN hMc hNc xs ys f (le_max_right _ _) hf hxy⟩

/-- Diagram equality of bounded lists passes to sublists and reindexings
(`StableDiagram.same_relevel`). -/
theorem sameD_comp (hμ : μ ∈ P.eligible) (hν : ν ∈ P.eligible) {M N : Model K.τ}
    (hcM : Model.card M = μ) (hcN : Model.card N = ν) {α γ : Type u}
    {xs : α → M.carrier} {ys : α → N.carrier} (h : P.D.SameD M N xs ys) (ι : γ → α)
    (hαμ : #α < μ) (hαν : #α < ν) (hγμ : #γ < μ) (hγν : #γ < ν) :
    P.D.SameD M N (fun c => xs (ι c)) (fun c => ys (ι c)) := by
  obtain ⟨hM, hN, hMc, hNc, h⟩ := h
  have hσ'μ : max (max (max #α ℵ₀) (max #γ ℵ₀)) (ls K) < μ :=
    max_lt (max_lt (max_lt hαμ (aleph0_lt hμ)) (max_lt hγμ (aleph0_lt hμ))) (ls_lt hμ)
  have hσ'ν : max (max (max #α ℵ₀) (max #γ ℵ₀)) (ls K) < ν :=
    max_lt (max_lt (max_lt hαν (aleph0_lt hν)) (max_lt hγν (aleph0_lt hν))) (ls_lt hν)
  have hσ' : ℵ₀ ≤ max (max (max #α ℵ₀) (max #γ ℵ₀)) (ls K) :=
    (le_max_right #α ℵ₀).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hMcτ := t_le hμ hcM (le_max_right #γ ℵ₀) (max_lt hγμ (aleph0_lt hμ))
  have hNcτ := t_le hν hcN (le_max_right #γ ℵ₀) (max_lt hγν (aleph0_lt hν))
  exact ⟨hM, hN, hMcτ, hNcτ,
    P.D.same_relevel (σ := max #α ℵ₀) (τ := max #γ ℵ₀)
      (σ' := max (max (max #α ℵ₀) (max #γ ℵ₀)) (ls K))
      (le_max_left _ _) (le_max_right _ _) (le_max_right _ _)
      ((le_max_left _ _).trans (le_max_left _ _)) ((le_max_right _ _).trans (le_max_left _ _))
      (le_max_right _ _) hM hN hMc hNc (t_le hμ hcM hσ' hσ'μ) (t_le hν hcN hσ' hσ'ν)
      hMcτ hNcτ xs ys h (le_max_left _ _) ι⟩

/-- Proposition 4.3: at one level, bounded lists with the same diagram are matched by an
isomorphism of their models. -/
theorem sameD_equiv (hρ : ρ ∈ P.eligible) {M N : Model K.τ}
    (hcM : Model.card M = ρ) (hcN : Model.card N = ρ) {α : Type u}
    {xs : α → M.carrier} {ys : α → N.carrier} (h : P.D.SameD M N xs ys) (hα : #α < ρ) :
    ∃ e : M.carrier ≃[K.τ] N.carrier, ∀ i, e (xs i) = ys i := by
  haveI := P.D.categoricalUnbounded
  haveI := arbitrarilyLarge_of_categoricalUnbounded K
  obtain ⟨hM, hN, hMc, hNc, h⟩ := h
  exact (prop43_hull_back_and_forth K P.D ρ (ls_lt hρ) hρ.1.working.countableCof
    (fun σ hσ hσρ => t_lt hρ hσ hσρ)).2 M N xs ys hM hN hα hcM hcN
    ⟨_, le_max_left _ _, le_max_right _ _, hMc, hNc, h⟩

/-! ### The presentations at the levels and the charts -/

variable (P) in
/-- The presentation `E(μ)` on the well-order of the level `μ`. -/
noncomputable def G (μ : Cardinal.{u}) : Model K.τ := P.E.obj (lvlOrder μ)

variable (P) in
theorem mem_G (μ : Cardinal.{u}) : K.Mem (P.G μ) := P.hE _

/-- `‖E(μ)‖ = μ` at a level: `μ ≤ ‖E(μ)‖ ≤ μ + ℓ` and `ℓ < μ`. -/
theorem card_G (hμ : μ ∈ P.eligible) : Model.card (P.G μ) = μ := by
  have hI : #(lvlOrder μ) = μ := mk_lvlOrder (aleph0_le hμ)
  apply le_antisymm
  · calc Model.card (P.G μ) ≤ #(lvlOrder μ) + P.E.ell := P.E.card_upper
      _ = μ + ls K := by rw [hI, P.E.ell_eq]
      _ = μ := Cardinal.add_eq_left (aleph0_le hμ) (ls_lt hμ).le
  · calc μ = #(lvlOrder μ) := hI.symm
      _ ≤ Model.card (P.G μ) := P.E.card_lower

/-- A model of cardinality `#I` at a level is a presentation `E(I)`, up to the bound `ℓ`. -/
theorem card_obj_eq (hμ : μ ∈ P.eligible) (I : Type u) [LinearOrder I] [Nonempty I]
    (hI : #I = μ) : Model.card (P.E.obj I) = μ := by
  apply le_antisymm
  · calc Model.card (P.E.obj I) ≤ #I + P.E.ell := P.E.card_upper
      _ = μ + ls K := by rw [hI, P.E.ell_eq]
      _ = μ := Cardinal.add_eq_left (aleph0_le hμ) (ls_lt hμ).le
  · calc μ = #I := hI.symm
      _ ≤ Model.card (P.E.obj I) := P.E.card_lower

variable (P) in
/-- The order arrow `E(μ) → E(ρ)` for levels `μ ≤ ρ`. -/
noncomputable def lift (h : μ ≤ ρ) :
    Language.Embedding K.τ (P.G μ).carrier (P.G ρ).carrier :=
  P.E.map (lvlEmb h)

variable (P) in
theorem lift_strong (h : μ ≤ ρ) : K.Strong (P.lift h) := P.E.map_strong _

variable (P) in
theorem lift_lift (h₁ : μ ≤ ρ) (h₂ : ρ ≤ κ) (a : (P.G μ).carrier) :
    P.lift h₂ (P.lift h₁ a) = P.lift (h₁.trans h₂) a := by
  change P.E.map (lvlEmb h₂) (P.E.map (lvlEmb h₁) a) = P.E.map (lvlEmb (h₁.trans h₂)) a
  rw [← lvlEmb_trans h₁ h₂, P.E.map_comp]
  rfl

/-- Categoricity at a level: every object is isomorphic to the presentation at that level. -/
theorem exists_chart (hμ : μ ∈ P.eligible) (X : SMObject K μ) :
    Nonempty (X.model.carrier ≃[K.τ] (P.G μ).carrier) :=
  (categorical hμ).unique_model X.model (P.G μ) X.mem (P.mem_G μ) X.card (card_G hμ)

/-- A chart of an object: an isomorphism with the presentation at its level. -/
noncomputable def chart (hμ : μ ∈ P.eligible) (X : SMObject K μ) :
    X.model.carrier ≃[K.τ] (P.G μ).carrier :=
  Classical.choice (exists_chart hμ X)

/-- The chart of an object followed by the order arrow into the presentation at a level
`ρ ≥ μ`. -/
noncomputable def push (hμ : μ ∈ P.eligible) (h : μ ≤ ρ) (X : SMObject K μ) :
    Language.Embedding K.τ X.model.carrier (P.G ρ).carrier :=
  (P.lift h).comp (chart hμ X).toEmbedding

theorem push_strong (hμ : μ ∈ P.eligible) (h : μ ≤ ρ) (X : SMObject K μ) :
    K.Strong (push hμ h X) :=
  K.strong_trans _ _ (strong_of_equiv K (chart hμ X) X.mem) (P.lift_strong h)

theorem lift_push (hμ : μ ∈ P.eligible) (h₁ : μ ≤ ρ) (h₂ : ρ ≤ κ) (X : SMObject K μ)
    (a : X.model.carrier) :
    P.lift h₂ (push hμ h₁ X a) = push hμ (h₁.trans h₂) X a :=
  P.lift_lift h₁ h₂ _

/-! ### Equality of `D`-diagrams -/

/-- Equality of `D`-diagrams of a list of an object at `μ` and a list of an object at `ν`:
at every level `ρ ≥ μ, ν` at which the lists are bounded, their images in the presentation
`E(ρ)` under the charts have the same `D`-diagram. For lists bounded at `μ` and `ν` this is
`D.same` in the two models themselves (`diagramEq_iff_sameD`). -/
def DiagramEq {α : Type u} (hμ : μ ∈ P.eligible) (hν : ν ∈ P.eligible)
    (X : SMObject K μ) (Y : SMObject K ν)
    (xs : α → X.model.carrier) (ys : α → Y.model.carrier) : Prop :=
  ∀ ρ (_ : ρ ∈ P.eligible) (hμρ : μ ≤ ρ) (hνρ : ν ≤ ρ), #α < ρ →
    P.D.SameD (P.G ρ) (P.G ρ) (fun i => push hμ hμρ X (xs i)) (fun i => push hν hνρ Y (ys i))

/-- The images of a list in the presentations at two levels at which it is bounded have the
same diagram. -/
theorem sameD_push_push (hμ : μ ∈ P.eligible) (hρ : ρ ∈ P.eligible) (hκ : κ ∈ P.eligible)
    (h₁ : μ ≤ ρ) (h₂ : ρ ≤ κ) (X : SMObject K μ) {α : Type u} (xs : α → X.model.carrier)
    (hα : #α < ρ) :
    P.D.SameD (P.G ρ) (P.G κ) (fun i => push hμ h₁ X (xs i))
      (fun i => push hμ (h₁.trans h₂) X (xs i)) :=
  sameD_of_strong hρ hκ (card_G hρ) (card_G hκ) (P.lift h₂) (P.lift_strong h₂) _ _
    (fun i => lift_push hμ h₁ h₂ X (xs i)) hα (hα.trans_le h₂)

/-- A bounded list of an object and its image in a presentation have the same diagram. -/
theorem sameD_push (hμ : μ ∈ P.eligible) (hρ : ρ ∈ P.eligible) (h : μ ≤ ρ)
    (X : SMObject K μ) {α : Type u} (xs : α → X.model.carrier) (hα : #α < μ) :
    P.D.SameD X.model (P.G ρ) xs (fun i => push hμ h X (xs i)) :=
  sameD_of_strong hμ hρ X.card (card_G hρ) (push hμ h X) (push_strong hμ h X) _ _
    (fun _ => rfl) hα (hα.trans_le h)

/-- Diagram equality can be tested at a single level at which the lists are bounded. -/
theorem DiagramEq.of_level {α : Type u} (hμ : μ ∈ P.eligible) (hν : ν ∈ P.eligible)
    (X : SMObject K μ) (Y : SMObject K ν)
    {xs : α → X.model.carrier} {ys : α → Y.model.carrier}
    (hρ : ρ ∈ P.eligible) (hμρ : μ ≤ ρ) (hνρ : ν ≤ ρ) (hα : #α < ρ)
    (h : P.D.SameD (P.G ρ) (P.G ρ) (fun i => push hμ hμρ X (xs i))
      (fun i => push hν hνρ Y (ys i))) :
    DiagramEq hμ hν X Y xs ys := by
  intro κ hκ hμκ hνκ hακ
  rcases le_total ρ κ with hle | hle
  · have hx := sameD_push_push hμ hρ hκ hμρ hle X xs hα
    have hy := sameD_push_push hν hρ hκ hνρ hle Y ys hα
    exact hx.symm.trans (h.trans hy)
  · have hx := sameD_push_push hμ hκ hρ hμκ hle X xs hακ
    have hy := sameD_push_push hν hκ hρ hνκ hle Y ys hακ
    exact hx.trans (h.trans hy.symm)

/-- For lists bounded at both levels, diagram equality is `D.same` in the two models. -/
theorem diagramEq_iff_sameD {α : Type u} (hμ : μ ∈ P.eligible) (hν : ν ∈ P.eligible)
    (X : SMObject K μ) (Y : SMObject K ν)
    (xs : α → X.model.carrier) (ys : α → Y.model.carrier) (hαμ : #α < μ) (hαν : #α < ν) :
    DiagramEq hμ hν X Y xs ys ↔ P.D.SameD X.model Y.model xs ys := by
  have hρ := max_mem hμ hν
  have hα : #α < max μ ν := hαμ.trans_le (le_max_left _ _)
  constructor
  · intro h
    have h' := h (max μ ν) hρ (le_max_left _ _) (le_max_right _ _) hα
    exact (sameD_push hμ hρ (le_max_left _ _) X xs hαμ).trans
      (h'.trans (sameD_push hν hρ (le_max_right _ _) Y ys hαν).symm)
  · intro h
    exact DiagramEq.of_level hμ hν X Y hρ (le_max_left _ _) (le_max_right _ _) hα
      ((sameD_push hμ hρ (le_max_left _ _) X xs hαμ).symm.trans
        (h.trans (sameD_push hν hρ (le_max_right _ _) Y ys hαν)))

theorem diagramEq_refl {α : Type u} (hμ : μ ∈ P.eligible) (X : SMObject K μ)
    (xs : α → X.model.carrier) : DiagramEq hμ hμ X X xs xs :=
  fun ρ hρ _ _ hα => sameD_refl hρ (P.mem_G ρ) (card_G hρ) _ hα

theorem DiagramEq.symm {α : Type u} {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {X : SMObject K μ} {Y : SMObject K ν}
    {xs : α → X.model.carrier} {ys : α → Y.model.carrier}
    (h : DiagramEq hμ hν X Y xs ys) : DiagramEq hν hμ Y X ys xs :=
  fun ρ hρ hνρ hμρ hα => (h ρ hρ hμρ hνρ hα).symm

/-- Diagram equality is transitive, for lists of every length: compare the three lists at a
level above the three objects. -/
theorem DiagramEq.trans {α : Type u} {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {hκ : κ ∈ P.eligible} {X : SMObject K μ} {Y : SMObject K ν} {Z : SMObject K κ}
    {xs : α → X.model.carrier} {ys : α → Y.model.carrier} {zs : α → Z.model.carrier}
    (h₁ : DiagramEq hμ hν X Y xs ys) (h₂ : DiagramEq hν hκ Y Z ys zs) :
    DiagramEq hμ hκ X Z xs zs := by
  intro ρ hρ hμρ hκρ hα
  have hρ' := max_mem hρ hν
  have hα' : #α < max ρ ν := hα.trans_le (le_max_left _ _)
  have h := (h₁ (max ρ ν) hρ' (hμρ.trans (le_max_left _ _)) (le_max_right _ _) hα').trans
    (h₂ (max ρ ν) hρ' (le_max_right _ _) (hκρ.trans (le_max_left _ _)) hα')
  exact DiagramEq.of_level hμ hκ X Z hρ' (hμρ.trans (le_max_left _ _))
    (hκρ.trans (le_max_left _ _)) hα' h ρ hρ hμρ hκρ hα

/-- Diagram equality passes to sublists and reindexings: compare at a level at which the
original lists are bounded. -/
theorem DiagramEq.comp {α γ : Type u} {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {X : SMObject K μ} {Y : SMObject K ν}
    {xs : α → X.model.carrier} {ys : α → Y.model.carrier}
    (h : DiagramEq hμ hν X Y xs ys) (ι : γ → α) :
    DiagramEq hμ hν X Y (fun c => xs (ι c)) (fun c => ys (ι c)) := by
  intro ρ hρ hμρ hνρ hγ
  obtain ⟨ρ', hle, hρ'⟩ := P.exists_ge (max ρ (Order.succ #α))
  have hρρ' : ρ ≤ ρ' := (le_max_left _ _).trans hle
  have hα' : #α < ρ' := (Order.lt_succ _).trans_le ((le_max_right _ _).trans hle)
  have hγ' : #γ < ρ' := hγ.trans_le hρρ'
  have h' := sameD_comp hρ' hρ' (card_G hρ') (card_G hρ')
    (h ρ' hρ' (hμρ.trans hρρ') (hνρ.trans hρρ') hα') ι hα' hα' hγ' hγ'
  exact DiagramEq.of_level hμ hν X Y hρ' (hμρ.trans hρρ') (hνρ.trans hρρ') hγ' h' ρ hρ hμρ
    hνρ hγ

/-- Strong maps preserve the diagrams of lists bounded at both levels (Proposition 4.2). -/
theorem diagramEq_of_strong {α : Type u} (hμ : μ ∈ P.eligible) (hν : ν ∈ P.eligible)
    (X : SMObject K μ) (Y : SMObject K ν)
    (f : Language.Embedding K.τ X.model.carrier Y.model.carrier) (hf : K.Strong f)
    (xs : α → X.model.carrier) (hαμ : #α < μ) (hαν : #α < ν) :
    DiagramEq hμ hν X Y xs (fun i => f (xs i)) :=
  (diagramEq_iff_sameD hμ hν X Y xs _ hαμ hαν).mpr
    (sameD_of_strong hμ hν X.card Y.card f hf _ _ (fun _ => rfl) hαμ hαν)

/-- Homogeneity (Proposition 4.3): at one level, two bounded lists have the same diagram
exactly when an isomorphism of their models takes one to the other. -/
theorem diagramEq_iff_equiv {α : Type u} (hμ : μ ∈ P.eligible) (X Y : SMObject K μ)
    (xs : α → X.model.carrier) (ys : α → Y.model.carrier) (hα : #α < μ) :
    DiagramEq hμ hμ X Y xs ys ↔
      ∃ e : X.model.carrier ≃[K.τ] Y.model.carrier, ∀ i, e (xs i) = ys i := by
  rw [diagramEq_iff_sameD hμ hμ X Y xs ys hα hα]
  constructor
  · intro h
    exact sameD_equiv hμ X.card Y.card h hα
  · rintro ⟨e, he⟩
    exact sameD_of_strong hμ hμ X.card Y.card e.toEmbedding (strong_of_equiv K e X.mem) _ _ he
      hα hα

/-! ### The working scheme -/

variable (P) in
/-- The term template of the scheme: the order presentation `E`. -/
def template : TermTemplate K oneVertexShape := orderPresentationTemplate P.E P.hE

variable (P) in
/-- **The single-model working scheme** (Proposition 5.6). Levels: the closure points of
`{D.t, g}` above `ℓ`. Objects at `μ`: the `K`-models coded on `μ.ord.ToType`. Arrows: all
strong maps. Structural isomorphisms: the bijective ones. Diagrams: `D.same`. -/
noncomputable def scheme : WorkingScheme K oneVertexShape where
  eligible := P.eligible
  eligible_unbounded := P.exists_ge
  Object := fun μ _ => SMObject K μ
  asSystem := fun _ X => X.system
  vertex_card := fun _ X _ => X.card
  template := P.template
  permitted := fun _ _ _ => True
  IsStructIso := fun {μ} {hμ} X Y f =>
    bijectiveStructIso (K := K) (S := oneVertexShape) (eligible := P.eligible)
      (Object := fun μ _ => SMObject K μ) (fun _ X => X.system) (hμ := hμ) X Y f
  isStructIso_bijective := fun _ _ _ h => h
  isStructIso_refl := fun _ _ => Function.bijective_id
  structural_iso := fun _ _ _ _ => trivial
  comp := fun _ _ _ _ => trivial
  coherent := fun _ _ _ _ _ _ => trivial
  DiagramEq := fun {α μ ν} {hμ} {hν} X Y xs ys =>
    DiagramEq hμ hν X Y (fun i => X.val (xs i)) (fun i => Y.val (ys i))
  diagram_refl := fun {α μ} {hμ} X xs => diagramEq_refl hμ X _
  diagram_symm := fun _ _ _ _ h => h.symm
  diagram_trans := fun _ _ _ _ _ _ h₁ h₂ => h₁.trans h₂
  diagram_empty := fun {μ ν} {hμ} {hν} X Y => by
    intro ρ hρ hμρ hνρ hα
    have he : (fun i : PEmpty.{u + 1} => push hμ hμρ X (X.val (i.elim))) =
        (fun i : PEmpty.{u + 1} => push hν hνρ Y (Y.val (i.elim))) :=
      funext fun i => i.elim
    rw [he]
    exact sameD_refl hρ (P.mem_G ρ) (card_G hρ) _ hα
  diagram_preserved := fun {α μ ν} {hμ} {hν} X Y f _ xs hαμ hαν =>
    diagramEq_of_strong hμ hν X Y (f.onVertex PUnit.unit) (f.onVertex_strong PUnit.unit)
      (fun i => X.val (xs i)) hαμ hαν
  diagram_reindex := fun {α β μ ν} {hμ} {hν} X Y e xs ys =>
    ⟨fun h => h.comp e.symm, fun h => by simpa using h.comp e⟩
  diagram_restrict := fun _ _ _ _ _ _ h => ⟨h.comp Sum.inl, h.comp Sum.inr⟩
  diagram_iso := fun {α μ} {hμ} X Y xs ys hα => by
    constructor
    · intro h
      obtain ⟨e, he⟩ := (diagramEq_iff_equiv hμ X Y _ _ hα).mp h
      refine ⟨oneVertexArrow e.toEmbedding (strong_of_equiv K e X.mem),
        fun _ => e.bijective, fun i => ?_⟩
      exact (congrArg Y.occ (he i)).symm
    · rintro ⟨f, -, hf⟩
      have h := diagramEq_of_strong hμ hμ X Y (f.onVertex PUnit.unit)
        (f.onVertex_strong PUnit.unit) (fun i => X.val (xs i)) hα hα
      have he : (fun i => Y.val (ys i)) =
          fun i => f.onVertex PUnit.unit (X.val (xs i)) :=
        funext fun i => congrArg Y.val (hf i)
      rw [he]
      exact h

end SingleModelData

end
end AEC
