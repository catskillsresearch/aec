module

public import AEC.Section4.CompactPlacement
public import AEC.Section4.TypeUWitness
public import Mathlib.SetTheory.Ordinal.Basic

@[expose] public section

/-!
# Uniform testing of placed comparisons over the base (Proposition 4.8, English form)

`proposition_4_8` in `Results.lean` records that a natural diagram comparison only depends on
the joint support of the two lists. Lemma 4.10 needs the statement of `text.md` §4.3 itself:
two placements of a tuple of length at most `σ` over `A = E(I)`, `I` a well-order, with
different placed comparisons over `A` already have different natural diagrams over a set of
at most `g(σ)` positions of `I`, where `g(σ)` does not depend on `I`.

This file proves it by the English argument.

* `Placement.AgreeOn P P' X`: the placements `P`, `P'` over `I` have the same natural diagram
  with every list of parameters supported in `X ⊆ I` (the placed comparisons over the
  parameters supported in `X` coincide).
* `PlacedTester K E D g`: over every well-order `I`, placements of a tuple of length at most
  `σ` which agree on every `X ⊆ I` of size at most `g σ` agree on all of `I`.
* `FrozenData`: the frozen data of two placements: the order of the union `T` of the supports
  of the two tuples, the labels and supports of the two tuples, and the subset of positions of
  `T` which belong to `I`. Up to relabeling on a fixed set of size `σ` they range over a set.
* `Layout F v`: a configuration with frozen data `F` in which the component of `I \ T` in each
  strict slot `c` over `T` is a well-order of length `v c`. The vectors `v` of the layouts
  with unequal placed comparisons form a class of ordinal vectors (`badVector`).
* `Layout.exists_embedding`: coordinatewise domination gives an order embedding of the smaller
  configuration into the larger one, fixing `T` and preserving the base positions.
* `exists_frozenBound`: Lemma 4.7 (`type_u_witness_set`) gives a set of witnesses, hence a
  bound on the sizes of the base orders of the witnesses.
* `exists_placedTester`: the resulting nondecreasing infinite `g` is a `PlacedTester`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

/-! ## Natural diagrams: change of bound, lists with equal realizations -/

section NaturalDiagramAPI

variable {K : AbstractElementaryClass.{u}} {E : OrderPresentation K} {D : StableDiagram K}
variable {I₁ I₂ : Type u} [LinearOrder I₁] [LinearOrder I₂] [Nonempty I₁] [Nonempty I₂]
  {γ γ' : Type u} {σ τ : Cardinal.{u}} {hσ : #γ ≤ σ}

/-- Natural diagram equality passes to sublists and reindexings, and is compatible with a
change of the bound: a diagram match in a presentation of categoricity size above both
thresholds is implemented by a strong map (Proposition 4.2). -/
theorem SameNaturalDiagram.relevel [CategoricalUnbounded K] (hσinf : aleph0 ≤ σ)
    (hτinf : aleph0 ≤ τ)
    {t : γ → SupportTerm E.lab E.arity I₁} {s : γ → SupportTerm E.lab E.arity I₂}
    (h : SameNaturalDiagram K E D σ hσ t s) (hγ' : #γ' ≤ τ) (ι : γ' → γ) :
    SameNaturalDiagram K E D τ hγ' (fun c => t (ι c)) (fun c => s (ι c)) := by
  obtain ⟨J, linJ, nonJ, f, g, hcJ, hMJ, hsame⟩ := h
  obtain ⟨L, linL, nonL, e, hcL, hcat⟩ := exists_categorical_extension E J (D.t σ ⊔ D.t τ)
  have hM : K.Mem (E.obj L) := orderPresentation_obj_mem E L
  have hcσ : D.t σ ≤ Model.card (E.obj L) := le_sup_left.trans hcL
  have hcτ : D.t τ ≤ Model.card (E.obj L) := le_sup_right.trans hcL
  have hL := same_map hσinf e hcJ hcσ hMJ hM _ _ hsame
  obtain ⟨φ, hφ, hφxy⟩ := D.to_strong hσ hM hM _ _ hσinf hcat rfl hcσ hcσ hL
  refine ⟨L, linL, nonL, f.trans e, g.trans e, hcτ, hM, ?_⟩
  refine D.of_strong hγ' hM hM hcτ hcτ _ _ φ hτinf hφ fun c => ?_
  have h := hφxy (ι c)
  simp only [E.realize_along] at h
  exact h

/-- Lists of terms with the same realizations have the same natural diagram. -/
theorem sameNaturalDiagram_of_realize_eq (t t' : γ → SupportTerm E.lab E.arity I₁)
    (h : ∀ c, E.realize (t c) = E.realize (t' c)) :
    SameNaturalDiagram K E D σ hσ t t' := by
  obtain ⟨L, linL, nonL, e, hcard⟩ := exists_large_extension E I₁ (D.t σ)
  have hM : K.Mem (E.obj L) := orderPresentation_obj_mem E L
  refine ⟨L, linL, nonL, e, e, hcard, hM, ?_⟩
  have heq : (fun a => E.realize (SupportTerm.along e (t a))) =
      fun a => E.realize (SupportTerm.along e (t' a)) := by
    funext a
    rw [← E.realize_along, ← E.realize_along, h a]
  rw [heq]
  exact D.refl hσ hM hcard _

/-- A diagram match of the realized lists in two presentations above the threshold is a
natural diagram match: amalgamate the two index orders. -/
theorem sameNaturalDiagram_of_same_realize {X : Type u} [LinearOrder X] (hσinf : aleph0 ≤ σ)
    (e₁ : X ↪o I₁) (e₂ : X ↪o I₂)
    (t : γ → SupportTerm E.lab E.arity I₁) (s : γ → SupportTerm E.lab E.arity I₂)
    (hc₁ : D.t σ ≤ Model.card (E.obj I₁)) (hc₂ : D.t σ ≤ Model.card (E.obj I₂))
    (hM₁ : K.Mem (E.obj I₁)) (hM₂ : K.Mem (E.obj I₂))
    (h : D.same hσ hM₁ hM₂ hc₁ hc₂ (fun a => E.realize (t a)) (fun a => E.realize (s a))) :
    SameNaturalDiagram K E D σ hσ t s := by
  obtain ⟨L, linL, F, H, -⟩ := exists_linearOrder_amalgam e₁ e₂
  haveI : Nonempty L := ⟨F (Classical.arbitrary I₁)⟩
  have hM : K.Mem (E.obj L) := orderPresentation_obj_mem E L
  have hc : D.t σ ≤ Model.card (E.obj L) :=
    hc₁.trans (mk_le_of_injective (E.map F).injective)
  refine ⟨L, linL, inferInstance, F, H, hc, hM, ?_⟩
  have h1 := D.of_strong hσ hM₁ hM hc₁ hc (fun a => E.realize (t a))
    (fun a => E.realize (SupportTerm.along F (t a))) (E.map F) hσinf (E.map_strong F)
    (fun a => E.realize_along F (t a))
  have h2 := D.of_strong hσ hM₂ hM hc₂ hc (fun a => E.realize (s a))
    (fun a => E.realize (SupportTerm.along H (s a))) (E.map H) hσinf (E.map_strong H)
    (fun a => E.realize_along H (s a))
  exact D.trans hσ hM hM₁ hM hc hc₁ hc _ _ _ (D.symm hσ hM₁ hM hc₁ hc _ _ h1)
    (D.trans hσ hM₁ hM₂ hM hc₁ hc₂ hc _ _ _ h h2)

end NaturalDiagramAPI

/-! ## Pulling a term back along an order embedding -/

section Pullback

variable {lab : Type u} {arity : lab → ℕ} {X L : Type u} [LinearOrder X] [LinearOrder L]

/-- Read a term over a suborder `h : X ↪o L` containing all its positions. -/
noncomputable def SupportTerm.pullback (h : X ↪o L) (t : SupportTerm lab arity L)
    (ht : termSupport t ⊆ Set.range h) : SupportTerm lab arity X where
  label := t.label
  pos := fun k => Classical.choose (ht (Set.mem_range_self k))
  increasing := fun a b hab => h.lt_iff_lt.mp (by
    rw [Classical.choose_spec (ht (Set.mem_range_self a)),
      Classical.choose_spec (ht (Set.mem_range_self b))]
    exact t.increasing hab)

theorem SupportTerm.along_pullback (h : X ↪o L) (t : SupportTerm lab arity L)
    (ht : termSupport t ⊆ Set.range h) : SupportTerm.along h (t.pullback h ht) = t :=
  SupportTerm.ext_of_label_eq rfl fun k => Classical.choose_spec (ht (Set.mem_range_self k))

end Pullback

/-! ## Placements agreeing on the parameters supported in a set of positions -/

section Agree

variable {K : AbstractElementaryClass.{u}} (E : OrderPresentation K) (D : StableDiagram K)

/-- **Agreement on `X`.** The placements `P`, `P'` over `I` have the same natural diagram with
every list of parameters supported in the set `X` of positions. For `X = Set.univ` this says
that `P` and `P'` have the same placed comparison over `E(I)`. -/
def Placement.AgreeOn {I : Type u} [LinearOrder I] [Nonempty I] {α : Type u}
    (P P' : Placement E.lab E.arity I α) (X : Set I) : Prop :=
  ∀ ⦃β : Type u⦄ (par : β → SupportTerm E.lab E.arity I) (τ : Cardinal.{u}) (_ : aleph0 ≤ τ)
    (hj : #(α ⊕ β) ≤ τ), (∀ b, termSupport (par b) ⊆ X) →
    SameNaturalDiagram K E D τ hj (P.joint par) (P'.joint par)

/-- **Proposition 4.8, as a property of `g`.** Over every well-order `I`, two placements of a
tuple of length at most an infinite `σ` whose natural diagrams agree over every set of at
most `g σ` positions of `I` have the same placed comparison over all of `E(I)`. -/
def PlacedTester (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) (g : Cardinal.{u} → Cardinal.{u}) : Prop :=
  ∀ ⦃I : Type u⦄ [LinearOrder I] [Nonempty I] [WellFoundedLT I] ⦃α : Type u⦄
    (σ : Cardinal.{u}), aleph0 ≤ σ → #α ≤ σ → ∀ P P' : Placement E.lab E.arity I α,
      (∀ X : Set I, #X ≤ g σ → P.AgreeOn E D P' X) → P.AgreeOn E D P' Set.univ

variable {E D}

theorem PlacedTester.mono {g g' : Cardinal.{u} → Cardinal.{u}} (h : PlacedTester K E D g)
    (hgg' : ∀ σ, g σ ≤ g' σ) : PlacedTester K E D g' :=
  fun _ _ _ _ _ σ hσinf hα P P' hsmall =>
    h σ hσinf hα P P' fun X hX => hsmall X (hX.trans (hgg' σ))

variable {I I₁ I₂ : Type u} [LinearOrder I] [LinearOrder I₁] [LinearOrder I₂]
  [Nonempty I] [Nonempty I₁] [Nonempty I₂] {α α' : Type u}

theorem Placement.AgreeOn.mono {P P' : Placement E.lab E.arity I α} {X Y : Set I}
    (h : P.AgreeOn E D P' X) (hYX : Y ⊆ X) : P.AgreeOn E D P' Y :=
  fun _ par τ hτ hj hpar => h par τ hτ hj fun b => (hpar b).trans hYX

/-- Agreement is preserved by extending the orders of the two placements. -/
theorem Placement.AgreeOn.along {P₁ P₁' P₂ P₂' : Placement E.lab E.arity I α} {X : Set I}
    (hag : P₁.AgreeOn E D P₁' X) (h : P₁.J ↪o P₂.J) (h' : P₁'.J ↪o P₂'.J)
    (hf : ∀ i, h (P₁.f i) = P₂.f i) (hf' : ∀ i, h' (P₁'.f i) = P₂'.f i)
    (hz : ∀ a, SupportTerm.along h (P₁.z a) = P₂.z a)
    (hz' : ∀ a, SupportTerm.along h' (P₁'.z a) = P₂'.z a) :
    P₂.AgreeOn E D P₂' X := by
  intro β par τ hτ hj hpar
  have h1 := (hag par τ hτ hj hpar).along hτ h h'
  have e1 : (fun c => SupportTerm.along h (P₁.joint par c)) = P₂.joint par := by
    funext c
    rcases c with a | b
    · exact hz a
    · exact SupportTerm.ext_of_label_eq rfl fun k => hf ((par b).pos k)
  have e2 : (fun c => SupportTerm.along h' (P₁'.joint par c)) = P₂'.joint par := by
    funext c
    rcases c with a | b
    · exact hz' a
    · exact SupportTerm.ext_of_label_eq rfl fun k => hf' ((par b).pos k)
  rw [e1, e2] at h1
  exact h1

/-- **Natural diagrams respect embeddings of configurations.** If a configuration over `I₁`
embeds into a configuration over `I₂`, preserving the base positions and the placed tuples,
then agreement on the image of `X` in the larger configuration gives agreement on `X` in the
smaller one. -/
theorem Placement.AgreeOn.of_base_change {P₁ P₁' : Placement E.lab E.arity I₁ α}
    {P₂ P₂' : Placement E.lab E.arity I₂ α} (hI : I₁ ↪o I₂) (h : P₁.J ↪o P₂.J)
    (h' : P₁'.J ↪o P₂'.J)
    (hf : ∀ i, h (P₁.f i) = P₂.f (hI i)) (hf' : ∀ i, h' (P₁'.f i) = P₂'.f (hI i))
    (hz : ∀ a, SupportTerm.along h (P₁.z a) = P₂.z a)
    (hz' : ∀ a, SupportTerm.along h' (P₁'.z a) = P₂'.z a)
    {X : Set I₁} (hag : P₂.AgreeOn E D P₂' (hI '' X)) : P₁.AgreeOn E D P₁' X := by
  intro β par τ hτ hj hpar
  have h2 := hag (fun b => SupportTerm.along hI (par b)) τ hτ hj (by
    rintro b _ ⟨k, rfl⟩
    exact ⟨(par b).pos k, hpar b (Set.mem_range_self k), rfl⟩)
  have e1 : P₂.joint (fun b => SupportTerm.along hI (par b)) =
      fun c => SupportTerm.along h (P₁.joint par c) := by
    funext c
    rcases c with a | b
    · exact (hz a).symm
    · exact SupportTerm.ext_of_label_eq rfl fun k => (hf ((par b).pos k)).symm
  have e2 : P₂'.joint (fun b => SupportTerm.along hI (par b)) =
      fun c => SupportTerm.along h' (P₁'.joint par c) := by
    funext c
    rcases c with a | b
    · exact (hz' a).symm
    · exact SupportTerm.ext_of_label_eq rfl fun k => (hf' ((par b).pos k)).symm
  rw [e1, e2] at h2
  exact sameNaturalDiagram_of_along h h' h2

/-- Reindex the placed tuple of a placement. -/
def Placement.reindex {lab : Type u} {arity : lab → ℕ} (P : Placement lab arity I α)
    (ε : α' → α) : Placement lab arity I α' where
  J := P.J
  f := P.f
  z := fun a => P.z (ε a)

theorem Placement.reindex_joint {lab : Type u} {arity : lab → ℕ} (P : Placement lab arity I α)
    (ε : α' → α) {β : Type u} (par : β → SupportTerm lab arity I) :
    (P.reindex ε).joint par = fun c => P.joint par (Sum.map ε id c) := by
  funext c
  rcases c with a | b <;> rfl

/-- Agreement passes to sublists and reindexings of the placed tuples. -/
theorem Placement.AgreeOn.reindex [CategoricalUnbounded K] {P P' : Placement E.lab E.arity I α}
    {X : Set I} (h : P.AgreeOn E D P' X) (ε : α' → α) :
    (P.reindex ε).AgreeOn E D (P'.reindex ε) X := by
  intro β par τ hτ hj hpar
  have h1 := h par (τ ⊔ #(α ⊕ β)) (hτ.trans le_sup_left) le_sup_right hpar
  have h2 := h1.relevel (hτ.trans le_sup_left) hτ hj (Sum.map ε id)
  rw [Placement.reindex_joint, Placement.reindex_joint]
  exact h2

end Agree

/-! ## Frozen data and layouts -/

/-- **Frozen data** of two placements of a tuple of length at most `σ`: the order of the union
`T` of the supports of the two tuples, the labels and supports of the two tuples, and the
subset `base` of the positions of `T` which belong to the base order. The carriers are
subsets of a fixed set of size `σ`, so the frozen data range over a set. -/
structure FrozenData (lab : Type u) (arity : lab → ℕ) (σ : Cardinal.{u}) where
  /-- The index set of the two tuples. -/
  A : Set σ.out
  /-- The union of the supports of the two tuples. -/
  T : Set σ.out
  [ord : LinearOrder ↥T]
  /-- The positions of `T` which belong to the base order. -/
  base : Set ↥T
  /-- The first tuple. -/
  z : ↥A → SupportTerm lab arity ↥T
  /-- The second tuple. -/
  z' : ↥A → SupportTerm lab arity ↥T

attribute [instance] FrozenData.ord

/-- **A configuration with frozen data `F` and slot lengths `v`.** The order `L` is the union
of `T` and of the base order `I`; the positions of `T` in the base are those of `F.base`; and
for every strict slot `c` over `T` the component of `I \ T` in `c` is a well-order of length
`v c`. -/
structure Layout {lab : Type u} {arity : lab → ℕ} {σ : Cardinal.{u}}
    (F : FrozenData lab arity σ) (v : LowerSet ↥F.T → Ordinal.{u}) where
  /-- The base order. -/
  I : Type u
  /-- The joint order of the base and of `T`. -/
  L : Type u
  [ordI : LinearOrder I]
  [ordL : LinearOrder L]
  [neI : Nonempty I]
  /-- The base positions. -/
  e : I ↪o L
  /-- The positions of `T`. -/
  ιT : ↥F.T ↪o L
  cover : ∀ x : L, x ∈ Set.range ιT ∨ x ∈ Set.range e
  base_iff : ∀ t, ιT t ∈ Set.range e ↔ t ∈ F.base
  comp : ∀ c : LowerSet ↥F.T,
    Nonempty ({i : I // e i ∉ Set.range ιT ∧ OrderAmalgam.cut ιT (e i) = c} ≃o (v c).ToType)

attribute [instance] Layout.ordI Layout.ordL Layout.neI

namespace Layout

variable {lab : Type u} {arity : lab → ℕ} {σ : Cardinal.{u}} {F : FrozenData lab arity σ}

/-- The first placement of a layout. -/
@[reducible] def plc {v : LowerSet ↥F.T → Ordinal.{u}} (W : Layout F v) :
    Placement lab arity W.I ↥F.A where
  J := W.L
  f := W.e
  z := fun a => SupportTerm.along W.ιT (F.z a)

/-- The second placement of a layout. -/
@[reducible] def plc' {v : LowerSet ↥F.T → Ordinal.{u}} (W : Layout F v) :
    Placement lab arity W.I ↥F.A where
  J := W.L
  f := W.e
  z := fun a => SupportTerm.along W.ιT (F.z' a)

/-- **Coordinatewise domination gives an order embedding** of the smaller configuration into
the larger one, fixing `T` and preserving the base positions. -/
theorem exists_embedding {v w : LowerSet ↥F.T → Ordinal.{u}} (W : Layout F v) (W' : Layout F w)
    (hvw : ∀ c, v c ≤ w c) :
    ∃ (hI : W.I ↪o W'.I) (hL : W.L ↪o W'.L),
      (∀ i, hL (W.e i) = W'.e (hI i)) ∧ ∀ t, hL (W.ιT t) = W'.ιT t := by
  classical
  -- the components embed slot by slot
  have hψ : ∀ c, Nonempty
      ({i : W.I // W.e i ∉ Set.range W.ιT ∧ OrderAmalgam.cut W.ιT (W.e i) = c} ↪o
        {i : W'.I // W'.e i ∉ Set.range W'.ιT ∧ OrderAmalgam.cut W'.ιT (W'.e i) = c}) := by
    intro c
    obtain ⟨a⟩ := W.comp c
    obtain ⟨b⟩ := W'.comp c
    have hle : Ordinal.type (α := (v c).ToType) (· < ·) ≤ Ordinal.type (α := (w c).ToType) (· < ·) := by
      rw [Ordinal.type_toType, Ordinal.type_toType]
      exact hvw c
    obtain ⟨m⟩ := Ordinal.type_le_iff.mp hle
    exact ⟨(a.toOrderEmbedding.trans m.toOrderEmbedding).trans b.symm.toOrderEmbedding⟩
  let ψ := fun c => Classical.choice (hψ c)
  -- the map of the base orders
  have hIex : ∀ i : W.I, ∃ i' : W'.I,
      (∀ t, W.ιT t = W.e i → W'.e i' = W'.ιT t) ∧
      (∀ (h : W.e i ∉ Set.range W.ιT) (c : LowerSet ↥F.T)
        (hc : OrderAmalgam.cut W.ιT (W.e i) = c), i' = (ψ c ⟨i, h, hc⟩).1) := by
    intro i
    by_cases h : W.e i ∈ Set.range W.ιT
    · obtain ⟨t, ht⟩ := h
      obtain ⟨i', hi'⟩ := (W'.base_iff t).mpr ((W.base_iff t).mp ⟨i, ht.symm⟩)
      refine ⟨i', fun t' ht' => ?_, fun h' => absurd ⟨t, ht⟩ h'⟩
      rw [hi', W.ιT.injective (ht'.trans ht.symm)]
    · refine ⟨(ψ _ ⟨i, h, rfl⟩).1, fun t ht => absurd ⟨t, ht⟩ h, fun h' c hc => ?_⟩
      subst hc
      rfl
  choose hI hI_T hI_N using hIex
  have hI_N' : ∀ i, W.e i ∉ Set.range W.ιT → W'.e (hI i) ∉ Set.range W'.ιT ∧
      OrderAmalgam.cut W'.ιT (W'.e (hI i)) = OrderAmalgam.cut W.ιT (W.e i) := by
    intro i h
    rw [hI_N i h _ rfl]
    exact (ψ _ ⟨i, h, rfl⟩).2
  -- the map of the joint orders
  have hLex : ∀ x : W.L, ∃ y : W'.L,
      (∀ t, W.ιT t = x → y = W'.ιT t) ∧ (∀ i, W.e i = x → y = W'.e (hI i)) := by
    intro x
    by_cases hx : x ∈ Set.range W.ιT
    · obtain ⟨t, rfl⟩ := hx
      refine ⟨W'.ιT t, fun t' ht' => by rw [W.ιT.injective ht'], fun i hi => ?_⟩
      exact (hI_T i t hi.symm).symm
    · obtain ⟨i, rfl⟩ := (W.cover x).resolve_left hx
      refine ⟨W'.e (hI i), fun t ht => absurd ⟨t, ht⟩ hx, fun i' hi' => ?_⟩
      rw [W.e.injective hi']
  choose hL hL_T hL_e using hLex
  have hLmono : StrictMono hL := by
    intro x y hxy
    by_cases hx : x ∈ Set.range W.ιT <;> by_cases hy : y ∈ Set.range W.ιT
    · obtain ⟨s, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := hy
      rw [hL_T _ s rfl, hL_T _ t rfl]
      exact W'.ιT.lt_iff_lt.mpr (W.ιT.lt_iff_lt.mp hxy)
    · obtain ⟨s, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := (W.cover y).resolve_left hy
      rw [hL_T _ s rfl, hL_e _ j rfl]
      have hs : s ∈ OrderAmalgam.cut W.ιT (W.e j) := OrderAmalgam.mem_cut.mpr hxy
      rw [← (hI_N' j hy).2] at hs
      exact OrderAmalgam.mem_cut.mp hs
    · obtain ⟨i, rfl⟩ := (W.cover x).resolve_left hx
      obtain ⟨t, rfl⟩ := hy
      rw [hL_e _ i rfl, hL_T _ t rfl]
      have ht : t ∉ OrderAmalgam.cut W.ιT (W.e i) :=
        fun h => lt_asymm (OrderAmalgam.mem_cut.mp h) hxy
      rw [← (hI_N' i hx).2] at ht
      have hle : W'.e (hI i) ≤ W'.ιT t :=
        not_lt.mp fun h => ht (OrderAmalgam.mem_cut.mpr h)
      exact lt_of_le_of_ne hle fun heq => (hI_N' i hx).1 ⟨t, heq.symm⟩
    · obtain ⟨i, rfl⟩ := (W.cover x).resolve_left hx
      obtain ⟨j, rfl⟩ := (W.cover y).resolve_left hy
      rw [hL_e _ i rfl, hL_e _ j rfl]
      have hij : i < j := W.e.lt_iff_lt.mp hxy
      by_cases hc : OrderAmalgam.cut W.ιT (W.e i) = OrderAmalgam.cut W.ιT (W.e j)
      · rw [hI_N i hx _ rfl, hI_N j hy _ hc.symm]
        refine W'.e.lt_iff_lt.mpr ?_
        exact (ψ (OrderAmalgam.cut W.ιT (W.e i))).lt_iff_lt.mpr hij
      · have hle : OrderAmalgam.cut W.ιT (W.e i) ≤ OrderAmalgam.cut W.ιT (W.e j) :=
          OrderAmalgam.cut_mono W.ιT hxy.le
        have hex : ∃ t, t ∈ OrderAmalgam.cut W.ιT (W.e j) ∧
            t ∉ OrderAmalgam.cut W.ιT (W.e i) := by
          by_contra hne
          push Not at hne
          exact hc (le_antisymm hle fun t ht => hne t ht)
        obtain ⟨t, htj, hti⟩ := hex
        rw [← (hI_N' i hx).2] at hti
        rw [← (hI_N' j hy).2] at htj
        exact lt_of_le_of_lt (not_lt.mp fun h => hti (OrderAmalgam.mem_cut.mpr h))
          (OrderAmalgam.mem_cut.mp htj)
  have hcomm : ∀ i, hL (W.e i) = W'.e (hI i) := fun i => hL_e _ i rfl
  have hImono : StrictMono hI := by
    intro i j hij
    refine W'.e.lt_iff_lt.mp ?_
    rw [← hcomm, ← hcomm]
    exact hLmono (W.e.lt_iff_lt.mpr hij)
  exact ⟨OrderEmbedding.ofStrictMono hI hImono, OrderEmbedding.ofStrictMono hL hLmono,
    fun i => hcomm i, fun t => hL_T _ t rfl⟩

end Layout

/-! ## The witnesses of Lemma 4.7 and the testing bound -/

section Bound

variable {K : AbstractElementaryClass.{u}} (E : OrderPresentation K) (D : StableDiagram K)
  {σ : Cardinal.{u}}

/-- The class of ordinal vectors of Proposition 4.8: the slot lengths of the configurations
with frozen data `F` in which the two placed comparisons are unequal. -/
def badVector (F : FrozenData E.lab E.arity σ) (v : LowerSet ↥F.T → Ordinal.{u}) : Prop :=
  ∃ W : Layout F v, ¬ W.plc.AgreeOn E D W.plc' Set.univ

/-- **Lemma 4.7 on the unequal configurations.** For fixed frozen data, a set of witnesses
generates the class of unequal configurations upwards; so the sizes of the base orders of the
witnesses are bounded. -/
theorem exists_frozenBound (F : FrozenData E.lab E.arity σ) :
    ∃ κ : Cardinal.{u}, ∀ w, badVector E D F w →
      ∃ v, (∀ c, v c ≤ w c) ∧
        ∃ W : Layout F v, ¬ W.plc.AgreeOn E D W.plc' Set.univ ∧ #W.I ≤ κ := by
  obtain ⟨ι, v, hv, hdom⟩ := type_u_witness_set (badVector E D F)
  choose W hW using hv
  refine ⟨⨆ i, #(W i).I, fun w hw => ?_⟩
  obtain ⟨i, hi⟩ := hdom w hw
  exact ⟨v i, hi, W i, hW i, le_ciSup (f := fun i => #(W i).I) Cardinal.bddAbove_of_small i⟩

/-- A bound on the base orders of the witnesses for the frozen data `F`. -/
noncomputable def frozenBound (F : FrozenData E.lab E.arity σ) : Cardinal.{u} :=
  Classical.choose (exists_frozenBound E D F)

theorem frozenBound_spec (F : FrozenData E.lab E.arity σ) (w : LowerSet ↥F.T → Ordinal.{u})
    (hw : badVector E D F w) :
    ∃ v, (∀ c, v c ≤ w c) ∧
      ∃ W : Layout F v, ¬ W.plc.AgreeOn E D W.plc' Set.univ ∧ #W.I ≤ frozenBound E D F :=
  Classical.choose_spec (exists_frozenBound E D F) w hw

/-- The bound over the set of frozen data of tuples of length at most `σ`. -/
noncomputable def frozenBoundAt (σ : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ F : FrozenData E.lab E.arity σ, frozenBound E D F

theorem frozenBound_le_frozenBoundAt (F : FrozenData E.lab E.arity σ) :
    frozenBound E D F ≤ frozenBoundAt E D σ :=
  le_ciSup (f := fun F : FrozenData E.lab E.arity σ => frozenBound E D F)
    Cardinal.bddAbove_of_small F

/-- **The testing bound `g(σ)`**, increased to an infinite nondecreasing function. -/
noncomputable def placedTestBound (σ : Cardinal.{u}) : Cardinal.{u} :=
  sSup (frozenBoundAt E D '' Set.Iic σ) ⊔ aleph0

theorem placedTestBound_mono {σ τ : Cardinal.{u}} (h : σ ≤ τ) :
    placedTestBound E D σ ≤ placedTestBound E D τ :=
  sup_le_sup_right (csSup_le_csSup (Cardinal.bddAbove_image _ bddAbove_Iic)
    ⟨_, Set.mem_image_of_mem _ (Set.mem_Iic.mpr le_rfl)⟩
    (Set.image_mono (Set.Iic_subset_Iic.mpr h))) _

theorem aleph0_le_placedTestBound (σ : Cardinal.{u}) : aleph0 ≤ placedTestBound E D σ :=
  le_sup_right

theorem frozenBoundAt_le_placedTestBound (σ : Cardinal.{u}) :
    frozenBoundAt E D σ ≤ placedTestBound E D σ :=
  (le_csSup (Cardinal.bddAbove_image _ bddAbove_Iic)
    (Set.mem_image_of_mem _ (Set.mem_Iic.mpr le_rfl))).trans le_sup_left

end Bound

/-! ## Uniform testing -/

section Testing

variable {K : AbstractElementaryClass.{u}} {E : OrderPresentation K} {D : StableDiagram K}
  {I : Type u} [LinearOrder I] [Nonempty I] {L : Type u} [LinearOrder L]
  {α : Type u} {σ : Cardinal.{u}}

/-- A well-order is order isomorphic to the canonical type of its order type. -/
theorem nonempty_orderIso_toType (W : Type u) [LinearOrder W] [WellFoundedLT W] :
    Nonempty (W ≃o (Ordinal.type (α := W) (· < ·)).ToType) := by
  have h : Ordinal.type (α := W) (· < ·) =
      Ordinal.type (α := (Ordinal.type (α := W) (· < ·)).ToType) (· < ·) :=
    (Ordinal.type_toType _).symm
  obtain ⟨r⟩ := Ordinal.type_eq.mp h
  exact ⟨OrderIso.ofRelIsoLT r⟩

/-- **The frozen data of two placements.** The union of the supports of two tuples of length
at most `σ` has size at most `σ`; relabel it, and the index set, on the fixed set of size
`σ`. -/
theorem exists_frozenData (hσinf : aleph0 ≤ σ) (hα : #α ≤ σ) (e : I ↪o L)
    (z z' : α → SupportTerm E.lab E.arity L) :
    ∃ (F : FrozenData E.lab E.arity σ) (ιT : ↥F.T ↪o L) (ε : α ≃ ↥F.A),
      (∀ t, ιT t ∈ Set.range e ↔ t ∈ F.base) ∧
      (∀ a, SupportTerm.along ιT (F.z (ε a)) = z a) ∧
      (∀ a, SupportTerm.along ιT (F.z' (ε a)) = z' a) := by
  classical
  have hTcard : #↥(tupleSupport z ∪ tupleSupport z') ≤ σ :=
    (mk_union_le _ _).trans (add_le_of_le hσinf
      ((mk_tupleSupport_le hα z).trans (max_le hσinf le_rfl))
      ((mk_tupleSupport_le hα z').trans (max_le hσinf le_rfl)))
  obtain ⟨j₀⟩ : Nonempty (↥(tupleSupport z ∪ tupleSupport z') ↪ σ.out) := by
    rw [← Cardinal.le_def, Cardinal.mk_out]
    exact hTcard
  obtain ⟨a₀⟩ : Nonempty (α ↪ σ.out) := by
    rw [← Cardinal.le_def, Cardinal.mk_out]
    exact hα
  let k : ↥(tupleSupport z ∪ tupleSupport z') ≃ ↥(Set.range j₀) :=
    Equiv.ofInjective j₀ j₀.injective
  let ιfun : ↥(Set.range j₀) → L := fun t => (k.symm t).1
  have ιinj : Function.Injective ιfun := fun a b h => k.symm.injective (Subtype.ext h)
  letI ordT : LinearOrder ↥(Set.range j₀) := LinearOrder.lift' ιfun ιinj
  let ιT : ↥(Set.range j₀) ↪o L := ⟨⟨ιfun, ιinj⟩, Iff.rfl⟩
  have hrange : ∀ x, x ∈ tupleSupport z ∪ tupleSupport z' → x ∈ Set.range ιT := by
    intro x hx
    refine ⟨k ⟨x, hx⟩, ?_⟩
    change (k.symm (k ⟨x, hx⟩)).1 = x
    rw [Equiv.symm_apply_apply]
  let ε : α ≃ ↥(Set.range a₀) := Equiv.ofInjective a₀ a₀.injective
  have hz : ∀ a, termSupport (z a) ⊆ Set.range ιT := fun a x hx =>
    hrange x (Or.inl (termSupport_subset_tupleSupport z a hx))
  have hz' : ∀ a, termSupport (z' a) ⊆ Set.range ιT := fun a x hx =>
    hrange x (Or.inr (termSupport_subset_tupleSupport z' a hx))
  refine ⟨{ A := Set.range a₀
            T := Set.range j₀
            ord := ordT
            base := {t | ιT t ∈ Set.range e}
            z := fun a => (z (ε.symm a)).pullback ιT (hz _)
            z' := fun a => (z' (ε.symm a)).pullback ιT (hz' _) },
    ιT, ε, fun t => Iff.rfl, fun a => ?_, fun a => ?_⟩
  · change SupportTerm.along ιT ((z (ε.symm (ε a))).pullback ιT (hz _)) = z a
    rw [SupportTerm.along_pullback, Equiv.symm_apply_apply]
  · change SupportTerm.along ιT ((z' (ε.symm (ε a))).pullback ιT (hz' _)) = z' a
    rw [SupportTerm.along_pullback, Equiv.symm_apply_apply]

variable [WellFoundedLT I]

/-- **Uniform testing for fixed frozen data.** If two placements with frozen data `F` over a
well-order `I` have unequal placed comparisons, their slot lengths dominate a witness, and the
image of the base order of the witness is a set of positions of `I` of size at most
`frozenBound E D F` over which the natural diagrams already differ. -/
theorem exists_small_disagreement_of_frozen (F : FrozenData E.lab E.arity σ) (e : I ↪o L)
    (ιT : ↥F.T ↪o L) (hbase : ∀ t, ιT t ∈ Set.range e ↔ t ∈ F.base)
    (hbad : ¬ ({ J := L, f := e, z := fun a => SupportTerm.along ιT (F.z a) } :
        Placement E.lab E.arity I ↥F.A).AgreeOn E D
      { J := L, f := e, z := fun a => SupportTerm.along ιT (F.z' a) } Set.univ) :
    ∃ X : Set I, #X ≤ frozenBound E D F ∧
      ¬ ({ J := L, f := e, z := fun a => SupportTerm.along ιT (F.z a) } :
          Placement E.lab E.arity I ↥F.A).AgreeOn E D
        { J := L, f := e, z := fun a => SupportTerm.along ιT (F.z' a) } X := by
  classical
  -- restrict the joint order to the union of `T` and of the base
  let L' : Set L := Set.range ιT ∪ Set.range e
  let incl : ↥L' ↪o L := OrderEmbedding.subtype (· ∈ L')
  let e' : I ↪o ↥L' :=
    OrderEmbedding.ofMapLEIff (fun i => (⟨e i, Or.inr ⟨i, rfl⟩⟩ : ↥L')) fun a b => e.le_iff_le
  let ιT' : ↥F.T ↪o ↥L' :=
    OrderEmbedding.ofMapLEIff (fun t => (⟨ιT t, Or.inl ⟨t, rfl⟩⟩ : ↥L')) fun a b => ιT.le_iff_le
  let W₀ : Layout F (fun c => Ordinal.type
      (α := {i : I // e' i ∉ Set.range ιT' ∧ OrderAmalgam.cut ιT' (e' i) = c}) (· < ·)) :=
    { I := I
      L := ↥L'
      e := e'
      ιT := ιT'
      cover := by
        rintro ⟨x, ⟨t, rfl⟩ | ⟨i, rfl⟩⟩
        · exact Or.inl ⟨t, rfl⟩
        · exact Or.inr ⟨i, rfl⟩
      base_iff := by
        intro t
        rw [← hbase t]
        constructor
        · rintro ⟨i, hi⟩
          exact ⟨i, congrArg Subtype.val hi⟩
        · rintro ⟨i, hi⟩
          exact ⟨i, Subtype.ext hi⟩
      comp := fun c => nonempty_orderIso_toType _ }
  have hW₀ : ¬ W₀.plc.AgreeOn E D W₀.plc' Set.univ := by
    intro hag
    exact hbad (hag.along incl incl (fun i => rfl) (fun i => rfl) (fun a => rfl) (fun a => rfl))
  obtain ⟨v, hvw, W, hWbad, hWcard⟩ := frozenBound_spec E D F _ ⟨W₀, hW₀⟩
  obtain ⟨hI, hL, hcomm, hT⟩ := W.exists_embedding W₀ hvw
  refine ⟨Set.range hI, mk_range_le.trans hWcard, fun hag => hWbad ?_⟩
  refine Placement.AgreeOn.of_base_change hI (hL.trans incl) (hL.trans incl) ?_ ?_ ?_ ?_
    (X := Set.univ) (by rwa [Set.image_univ])
  · intro i
    change incl (hL (W.e i)) = e (hI i)
    rw [hcomm]
    rfl
  · intro i
    change incl (hL (W.e i)) = e (hI i)
    rw [hcomm]
    rfl
  · intro a
    refine SupportTerm.ext_of_label_eq rfl fun k => ?_
    change incl (hL (W.ιT ((F.z a).pos k))) = ιT ((F.z a).pos k)
    rw [hT]
    rfl
  · intro a
    refine SupportTerm.ext_of_label_eq rfl fun k => ?_
    change incl (hL (W.ιT ((F.z' a).pos k))) = ιT ((F.z' a).pos k)
    rw [hT]
    rfl

/-- **Uniform testing over a common order.** Two tuples of terms of length at most `σ` over an
extension `e : I ↪o L` of a well-order with unequal placed comparisons over `E(I)` already
have different natural diagrams over a set of at most `frozenBoundAt E D σ` positions of
`I`. -/
theorem exists_small_disagreement [CategoricalUnbounded K] (hσinf : aleph0 ≤ σ) (hα : #α ≤ σ)
    (e : I ↪o L) (z z' : α → SupportTerm E.lab E.arity L)
    (hbad : ¬ ({ J := L, f := e, z := z } : Placement E.lab E.arity I α).AgreeOn E D
      { J := L, f := e, z := z' } Set.univ) :
    ∃ X : Set I, #X ≤ frozenBoundAt E D σ ∧
      ¬ ({ J := L, f := e, z := z } : Placement E.lab E.arity I α).AgreeOn E D
        { J := L, f := e, z := z' } X := by
  obtain ⟨F, ιT, ε, hbase, hzF, hzF'⟩ := exists_frozenData hσinf hα e z z'
  have hQbad : ¬ ({ J := L, f := e, z := fun a => SupportTerm.along ιT (F.z a) } :
        Placement E.lab E.arity I ↥F.A).AgreeOn E D
      { J := L, f := e, z := fun a => SupportTerm.along ιT (F.z' a) } Set.univ := by
    intro hag
    have h := hag.reindex ε
    have e1 : (fun a => SupportTerm.along ιT (F.z (ε a))) = z := funext hzF
    have e2 : (fun a => SupportTerm.along ιT (F.z' (ε a))) = z' := funext hzF'
    simp only [Placement.reindex, e1, e2] at h
    exact hbad h
  obtain ⟨X, hXcard, hXbad⟩ := exists_small_disagreement_of_frozen F e ιT hbase hQbad
  refine ⟨X, hXcard.trans (frozenBound_le_frozenBoundAt E D F), fun hag => hXbad ?_⟩
  have h := hag.reindex ε.symm
  have e1 : (fun a => z (ε.symm a)) = fun a => SupportTerm.along ιT (F.z a) := by
    funext a
    rw [← hzF, Equiv.apply_symm_apply]
  have e2 : (fun a => z' (ε.symm a)) = fun a => SupportTerm.along ιT (F.z' a) := by
    funext a
    rw [← hzF', Equiv.apply_symm_apply]
  simp only [Placement.reindex, e1, e2] at h
  exact h

/-- **Proposition 4.8 (Uniform testing of placed comparisons), English form.** There is a
nondecreasing infinite cardinal function `g` such that, over every well-order `I`, two
placements of a tuple of length at most `σ` over `E(I)` with different placed comparisons
over `E(I)` already have different natural diagrams over a set of at most `g(σ)` positions of
`I`. The bound is independent of `|I|`.

Proof as in `text.md`: amalgamate the two support orders over `I`; freeze the order of the
union `T` of the two supports, the labels and supports, and the positions of `T` in `I`
(`FrozenData`); the lengths of the components of `I \ T` in the strict slots over `T` form
an ordinal vector; domination gives an embedding of configurations (`Layout.exists_embedding`)
and natural diagrams respect it (`Placement.AgreeOn.of_base_change`); Lemma 4.7 gives a set
of witnesses. -/
theorem exists_placedTester [CategoricalUnbounded K] (E : OrderPresentation K)
    (D : StableDiagram K) :
    ∃ g : Cardinal.{u} → Cardinal.{u},
      (∀ σ τ, σ ≤ τ → g σ ≤ g τ) ∧ (∀ σ, aleph0 ≤ g σ) ∧ PlacedTester K E D g := by
  refine ⟨placedTestBound E D, fun σ τ h => placedTestBound_mono E D h,
    aleph0_le_placedTestBound E D, ?_⟩
  intro I _ _ _ α σ hσinf hα P P' hsmall
  by_contra hbad
  obtain ⟨L, linL, F, H, hFH⟩ := exists_linearOrder_amalgam P.f P'.f
  have hQbad : ¬ ({ J := L, f := P.f.trans F, z := fun a => SupportTerm.along F (P.z a) } :
        Placement E.lab E.arity I α).AgreeOn E D
      { J := L, f := P.f.trans F, z := fun a => SupportTerm.along H (P'.z a) } Set.univ := by
    intro hag
    refine hbad (Placement.AgreeOn.of_base_change (OrderIso.refl I).toOrderEmbedding F H
      (fun i => rfl) (fun i => (hFH i).symm) (fun a => rfl) (fun a => rfl)
      (hag.mono (Set.subset_univ _)))
  obtain ⟨X, hXcard, hXbad⟩ := exists_small_disagreement hσinf hα (P.f.trans F) _ _ hQbad
  refine hXbad ((hsmall X (hXcard.trans (frozenBoundAt_le_placedTestBound E D σ))).along F H
    (fun i => rfl) (fun i => (hFH i).symm) (fun a => rfl) (fun a => rfl))

end Testing

end
end AEC
