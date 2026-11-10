module

public import AEC.Section4.NaturalDiagram
public import AEC.Section4.UniformTesting
public import AEC.Section4.BlockInterchange
public import AEC.Section4.SupportProfile
public import AEC.Section1.UnboundedCategoricity
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

/-!
# Compact placement (Proposition 4.9), by the English support-profile obstruction

This file follows the proof of Proposition 4.9 in `text.md` §4.3.

* `Placement`: a placement of a tuple over `I`, i.e. an order extension `f : I ↪o J` together
  with a list of terms over `J`.
* `SameProfile S P P'`: the placements `P`, `P'` have the same *support profile* over the old
  positions `S ⊆ I` (same labels, same formal support order, same comparisons and coincidences
  with `S`); `Placement.code` is a code of the profile, and there are at most `χ ^ σ = χ` codes
  (`mk_profileCode_le`), because a well-order of size at most `χ` has at most `χ` cuts.
* `Placement.SameCut`: two positions lie in one strict slot over `S`; the positions of a
  placement in one slot form a *cluster*.
* `Placement.NoEvent S S'`: no *new event* over `S' ⊇ S`: no hit of a new parameter position
  on the support (`NoHit`), and no separation of two positions of one cluster by a new
  parameter position (`NoSep`).
* `exists_inert_continuation`: each profile has a *continuation* over `I` which leaves every
  cluster intact (inserted at a single cut of `I` extending its cut over `S`); it has no new
  event over all of `I`.
* `sameNaturalDiagram_of_sameProfile_noEvent`: all continuations of a profile with no new event
  over `S'` have the same natural diagram over parameters supported in `S'`. Within each old
  slot the whole cluster can only change its position across a block of new parameter
  positions; the slots are disjoint, so Lemma 4.6 applies simultaneously (`Placement.regions`).
* `exists_local_placement`: one prescription has a placement (Proposition 4.2 after extending
  `I` to a categoricity size).
* `compact_placement`: the `σ⁺`-stage obstruction. If no placement solved all prescriptions,
  adjoin for every profile over the current parameter set a failing set of its chosen no-event
  continuation. A placement solving the prescription of the union has a new event at every
  stage, but there are at most `σ + σ² = σ` events.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

/-! ## Natural diagrams: transitivity, reindexing, order patterns -/

section NaturalDiagramAPI

variable {K : AbstractElementaryClass.{u}} (E : OrderPresentation K) (D : StableDiagram K)

/-- Every index order extends to one whose presentation has at least `θ` elements. -/
theorem exists_large_extension (I : Type u) [LinearOrder I] [Nonempty I] (θ : Cardinal.{u}) :
    ∃ (L : Type u) (_ : LinearOrder L) (_ : Nonempty L) (_ : I ↪o L),
      θ ≤ Model.card (E.obj L) := by
  set κ : Cardinal.{u} := θ ⊔ #I ⊔ ls K ⊔ aleph0 with hκdef
  have hκinf : aleph0 ≤ κ := le_sup_right
  have hκls : ls K ≤ κ := le_sup_right.trans le_sup_left
  have hκI : #I ≤ κ := (le_sup_right.trans le_sup_left).trans le_sup_left
  have hκθ : θ ≤ κ := ((le_sup_left.trans le_sup_left).trans le_sup_left)
  refine ⟨I ⊕ₗ Below κ, inferInstance, inferInstance, sumLexEmbedLeftIncl I (Below κ), ?_⟩
  exact hκθ.trans (orderPresentation_obj_card E (mk_sumLex_below hκinf hκI) hκls hκinf).ge

/-- Every index order extends to one whose presentation has a categoricity size at least
`θ`. -/
theorem exists_categorical_extension [CategoricalUnbounded K] (I : Type u) [LinearOrder I]
    [Nonempty I] (θ : Cardinal.{u}) :
    ∃ (L : Type u) (_ : LinearOrder L) (_ : Nonempty L) (_ : I ↪o L),
      θ ≤ Model.card (E.obj L) ∧ Categorical K (Model.card (E.obj L)) := by
  obtain ⟨κ, hκ, hcat⟩ :=
    CategoricalUnbounded.unbounded (K := K) (θ ⊔ #I ⊔ ls K ⊔ aleph0)
  have hκinf : aleph0 ≤ κ := le_sup_right.trans hκ
  have hκls : ls K ≤ κ := (le_sup_right.trans le_sup_left).trans hκ
  have hκI : #I ≤ κ := ((le_sup_right.trans le_sup_left).trans le_sup_left).trans hκ
  have hκθ : θ ≤ κ := ((le_sup_left.trans le_sup_left).trans le_sup_left).trans hκ
  have hcard : Model.card (E.obj (I ⊕ₗ Below κ)) = κ :=
    orderPresentation_obj_card E (mk_sumLex_below hκinf hκI) hκls hκinf
  refine ⟨I ⊕ₗ Below κ, inferInstance, inferInstance, sumLexEmbedLeftIncl I (Below κ), ?_, ?_⟩
  · exact hκθ.trans hcard.ge
  · rw [hcard]; exact hcat

variable {E D}
variable {I₁ I₂ I₃ : Type u} [LinearOrder I₁] [LinearOrder I₂] [LinearOrder I₃]
  [Nonempty I₁] [Nonempty I₂] [Nonempty I₃] {γ γ' : Type u} {σ : Cardinal.{u}} {hσ : #γ ≤ σ}

/-- Strong order maps preserve diagram equality of two tuples of one presentation. -/
theorem same_map (hσinf : aleph0 ≤ σ) (F : I₁ ↪o I₂)
    (hc₁ : D.t σ ≤ Model.card (E.obj I₁)) (hc₂ : D.t σ ≤ Model.card (E.obj I₂))
    (hM₁ : K.Mem (E.obj I₁)) (hM₂ : K.Mem (E.obj I₂))
    (xs ys : γ → (E.obj I₁).carrier)
    (h : D.same hσ hM₁ hM₁ hc₁ hc₁ xs ys) :
    D.same hσ hM₂ hM₂ hc₂ hc₂ (fun a => E.map F (xs a)) (fun a => E.map F (ys a)) := by
  have h1 := D.of_strong hσ hM₁ hM₂ hc₁ hc₂ xs (fun a => E.map F (xs a)) (E.map F) hσinf
    (E.map_strong F) (fun _ => rfl)
  have h2 := D.of_strong hσ hM₁ hM₂ hc₁ hc₂ ys (fun a => E.map F (ys a)) (E.map F) hσinf
    (E.map_strong F) (fun _ => rfl)
  exact D.trans hσ hM₂ hM₁ hM₂ hc₂ hc₁ hc₂ _ _ _
    (D.symm hσ hM₁ hM₂ hc₁ hc₂ _ _ h1)
    (D.trans hσ hM₁ hM₁ hM₂ hc₁ hc₁ hc₂ _ _ _ h h2)

/-- Natural diagram equality is transitive. -/
theorem SameNaturalDiagram.trans (hσinf : aleph0 ≤ σ)
    {t : γ → SupportTerm E.lab E.arity I₁} {s : γ → SupportTerm E.lab E.arity I₂}
    {r : γ → SupportTerm E.lab E.arity I₃}
    (h₁ : SameNaturalDiagram K E D σ hσ t s) (h₂ : SameNaturalDiagram K E D σ hσ s r) :
    SameNaturalDiagram K E D σ hσ t r := by
  obtain ⟨J₁, linJ₁, nonJ₁, f₁, g₁, hc₁, hM₁, hs₁⟩ := h₁
  obtain ⟨J₂, linJ₂, nonJ₂, f₂, g₂, hc₂, hM₂, hs₂⟩ := h₂
  obtain ⟨L, linL, F, H, hFH⟩ := exists_linearOrder_amalgam g₁ f₂
  haveI : Nonempty L := ⟨F (Classical.arbitrary J₁)⟩
  have hM : K.Mem (E.obj L) := orderPresentation_obj_mem E L
  have hc : D.t σ ≤ Model.card (E.obj L) :=
    hc₁.trans (mk_le_of_injective (E.map F).injective)
  have e₁ := same_map hσinf F hc₁ hc hM₁ hM _ _ hs₁
  have e₂ := same_map hσinf H hc₂ hc hM₂ hM _ _ hs₂
  refine ⟨L, linL, inferInstance, f₁.trans F, g₂.trans H, hc, hM, ?_⟩
  have hmid : (fun a => E.map F (E.realize (SupportTerm.along g₁ (s a)))) =
      fun a => E.map H (E.realize (SupportTerm.along f₂ (s a))) := by
    funext a
    rw [E.realize_along, E.realize_along]
    congr 1
    refine SupportTerm.ext_of_label_eq rfl fun k => ?_
    exact hFH ((s a).pos k)
  rw [hmid] at e₁
  have e := D.trans hσ hM hM hM hc hc hc _ _ _ e₁ e₂
  simp only [E.realize_along] at e
  exact e

/-- A natural diagram comparison along an extension of the right index order. -/
theorem sameNaturalDiagram_of_along_right {X : Type u} [LinearOrder X] [Nonempty X]
    {t : γ → SupportTerm E.lab E.arity I₁} {s : γ → SupportTerm E.lab E.arity X}
    (e : X ↪o I₂)
    (h : SameNaturalDiagram K E D σ hσ t (fun a => SupportTerm.along e (s a))) :
    SameNaturalDiagram K E D σ hσ t s := by
  obtain ⟨J, linJ, nonJ, f, g, hcard, hM, hsame⟩ := h
  exact ⟨J, linJ, nonJ, f, e.trans g, hcard, hM, hsame⟩

/-- A list of terms has the same natural diagram as any list it is the image of under an
order embedding. -/
theorem sameNaturalDiagram_of_along_eq (e : I₂ ↪o I₁)
    (t : γ → SupportTerm E.lab E.arity I₁) (t' : γ → SupportTerm E.lab E.arity I₂)
    (h : ∀ c, SupportTerm.along e (t' c) = t c) :
    SameNaturalDiagram K E D σ hσ t t' := by
  obtain ⟨L, linL, nonL, e₁, hcard⟩ := exists_large_extension E I₁ (D.t σ)
  have hM : K.Mem (E.obj L) := orderPresentation_obj_mem E L
  refine ⟨L, linL, nonL, e₁, e.trans e₁, hcard, hM, ?_⟩
  have heq : (fun a => E.realize (SupportTerm.along e₁ (t a))) =
      fun a => E.realize (SupportTerm.along (e.trans e₁) (t' a)) := by
    funext a
    rw [← h a]
    rfl
  rw [heq]
  exact D.refl hσ hM hcard _

/-- Natural diagram equality passes to sublists and reindexings: a diagram match in a
presentation of categoricity size is implemented by a strong map (Proposition 4.2), which also
matches the reindexed lists. -/
theorem SameNaturalDiagram.comp [CategoricalUnbounded K] (hσinf : aleph0 ≤ σ)
    {t : γ → SupportTerm E.lab E.arity I₁} {s : γ → SupportTerm E.lab E.arity I₂}
    (h : SameNaturalDiagram K E D σ hσ t s) (hγ' : #γ' ≤ σ) (ι : γ' → γ) :
    SameNaturalDiagram K E D σ hγ' (fun c => t (ι c)) (fun c => s (ι c)) := by
  obtain ⟨J, linJ, nonJ, f, g, hcJ, hMJ, hsame⟩ := h
  obtain ⟨L, linL, nonL, e, hcL, hcat⟩ := exists_categorical_extension E J (D.t σ)
  have hM : K.Mem (E.obj L) := orderPresentation_obj_mem E L
  have hL := same_map hσinf e hcJ hcL hMJ hM _ _ hsame
  obtain ⟨φ, hφ, hφxy⟩ := D.to_strong hσ hM hM _ _ hσinf hcat rfl hcL hcL hL
  refine ⟨L, linL, nonL, f.trans e, g.trans e, hcL, hM, ?_⟩
  refine D.of_strong hγ' hM hM hcL hcL _ _ φ hσinf hφ fun c => ?_
  have h := hφxy (ι c)
  simp only [E.realize_along] at h
  exact h

/-- A natural diagram match is a diagram match of the realized lists, when both
presentations are above the diagram threshold. -/
theorem SameNaturalDiagram.same (hσinf : aleph0 ≤ σ)
    {t : γ → SupportTerm E.lab E.arity I₁} {s : γ → SupportTerm E.lab E.arity I₂}
    (h : SameNaturalDiagram K E D σ hσ t s)
    (hc₁ : D.t σ ≤ Model.card (E.obj I₁)) (hc₂ : D.t σ ≤ Model.card (E.obj I₂))
    (hM₁ : K.Mem (E.obj I₁)) (hM₂ : K.Mem (E.obj I₂)) :
    D.same hσ hM₁ hM₂ hc₁ hc₂ (fun a => E.realize (t a)) (fun a => E.realize (s a)) := by
  obtain ⟨J, linJ, nonJ, f, g, hcJ, hMJ, hsame⟩ := h
  have h1 := D.of_strong hσ hM₁ hMJ hc₁ hcJ (fun a => E.realize (t a))
    (fun a => E.realize (SupportTerm.along f (t a))) (E.map f) hσinf (E.map_strong f)
    (fun a => E.realize_along f (t a))
  have h2 := D.of_strong hσ hM₂ hMJ hc₂ hcJ (fun a => E.realize (s a))
    (fun a => E.realize (SupportTerm.along g (s a))) (E.map g) hσinf (E.map_strong g)
    (fun a => E.realize_along g (s a))
  exact D.trans hσ hM₁ hMJ hM₂ hc₁ hcJ hc₂ _ _ _ h1
    (D.trans hσ hMJ hMJ hM₂ hcJ hcJ hc₂ _ _ _ hsame (D.symm hσ hM₂ hMJ hc₂ hcJ _ _ h2))

/-- **Natural diagrams depend only on the order pattern.** Two lists of terms with the same
labels and the same order pattern of positions have the same natural diagram: the supports
are order isomorphic, and the index orders amalgamate over the isomorphism. -/
theorem sameNaturalDiagram_of_pattern
    (t : γ → SupportTerm E.lab E.arity I₁) (t' : γ → SupportTerm E.lab E.arity I₂)
    (hlab : ∀ c, (t c).label = (t' c).label)
    (hpat : ∀ c d k l (hk : k < E.arity (t c).label) (hl : l < E.arity (t d).label)
      (hk' : k < E.arity (t' c).label) (hl' : l < E.arity (t' d).label),
      (t c).pos ⟨k, hk⟩ < (t d).pos ⟨l, hl⟩ ↔ (t' c).pos ⟨k, hk'⟩ < (t' d).pos ⟨l, hl'⟩) :
    SameNaturalDiagram K E D σ hσ t t' := by
  classical
  -- the partial isomorphism on the support of `t`
  have hex : ∀ x : ↥(tupleSupport t), ∃ c, ∃ k : Fin (E.arity (t c).label), (t c).pos k = x.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨c, k, hk⟩ := Set.mem_iUnion.mp hx
    exact ⟨c, k, hk⟩
  choose cc kk hck using hex
  let g₀ : ↥(tupleSupport t) → I₂ := fun x =>
    (t' (cc x)).pos (Fin.cast (congrArg E.arity (hlab (cc x))) (kk x))
  have hg₀ : StrictMono g₀ := by
    intro x y hxy
    have h : (t (cc x)).pos (kk x) < (t (cc y)).pos (kk y) := by
      rw [hck x, hck y]; exact hxy
    exact (hpat (cc x) (cc y) (kk x) (kk y) (kk x).isLt (kk y).isLt
      (by rw [← hlab]; exact (kk x).isLt) (by rw [← hlab]; exact (kk y).isLt)).mp h
  have hg₀val : ∀ c (k : Fin (E.arity (t c).label)),
      g₀ ⟨(t c).pos k, termSupport_subset_tupleSupport t c (Set.mem_range_self k)⟩ =
        (t' c).pos (Fin.cast (congrArg E.arity (hlab c)) k) := by
    intro c k
    set x : ↥(tupleSupport t) :=
      ⟨(t c).pos k, termSupport_subset_tupleSupport t c (Set.mem_range_self k)⟩ with hx
    have h : (t (cc x)).pos (kk x) = (t c).pos k := hck x
    have h1 := hpat (cc x) c (kk x) k (kk x).isLt k.isLt
      (by rw [← hlab]; exact (kk x).isLt) (by rw [← hlab]; exact k.isLt)
    have h2 := hpat c (cc x) k (kk x) k.isLt (kk x).isLt
      (by rw [← hlab]; exact k.isLt) (by rw [← hlab]; exact (kk x).isLt)
    refine le_antisymm (not_lt.mp fun hlt => ?_) (not_lt.mp fun hlt => ?_)
    · exact absurd (h2.mpr hlt) (by rw [h]; exact lt_irrefl _)
    · exact absurd (h1.mpr hlt) (by rw [h]; exact lt_irrefl _)
  obtain ⟨L₀, linL₀, F, H, hFH⟩ := exists_linearOrder_amalgam
    (OrderEmbedding.subtype (· ∈ tupleSupport t)) (OrderEmbedding.ofStrictMono g₀ hg₀)
  haveI : Nonempty L₀ := ⟨F (Classical.arbitrary I₁)⟩
  obtain ⟨L, linL, nonL, e, hcard⟩ := exists_large_extension E L₀ (D.t σ)
  have hM : K.Mem (E.obj L) := orderPresentation_obj_mem E L
  refine ⟨L, linL, nonL, F.trans e, H.trans e, hcard, hM, ?_⟩
  have key : ∀ c, SupportTerm.along (F.trans e) (t c) = SupportTerm.along (H.trans e) (t' c) := by
    intro c
    refine SupportTerm.ext_of_label_eq (hlab c) fun k => ?_
    have h := hFH ⟨(t c).pos k, termSupport_subset_tupleSupport t c (Set.mem_range_self k)⟩
    simp only [OrderEmbedding.coe_ofStrictMono] at h
    rw [hg₀val c k] at h
    exact congrArg e h
  simp only [key]
  exact D.refl hσ hM hcard _

end NaturalDiagramAPI

/-! ## Placements, slots, clusters and new events -/

/-- A placement of an `α`-tuple over `I`: an extension `f : I ↪o J` of the index order together
with a list of terms over `J`. -/
structure Placement (lab : Type u) (arity : lab → ℕ) (I : Type u) [LinearOrder I]
    (α : Type u) where
  /-- The extended index order. -/
  J : Type u
  [ord : LinearOrder J]
  /-- The inclusion of the old positions. -/
  f : I ↪o J
  /-- The terms of the placed tuple. -/
  z : α → SupportTerm lab arity J

attribute [instance] Placement.ord

namespace Placement

variable {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I] {α : Type u}
  (P : Placement lab arity I α)

instance [Nonempty I] : Nonempty P.J := ⟨P.f (Classical.arbitrary I)⟩

/-- The placed tuple together with a list of parameters given by terms over `I`. -/
def joint {β : Type u} (par : β → SupportTerm lab arity I) :
    α ⊕ β → SupportTerm lab arity P.J :=
  Sum.elim P.z (fun b => SupportTerm.along P.f (par b))

/-- Two positions lie in the same strict slot (cut) over the old positions `S`. The positions
of the placement in one slot form a *cluster*. -/
def SameCut (S : Set I) (x y : P.J) : Prop :=
  ∀ s ∈ S, P.f s < x ↔ P.f s < y

/-- No new parameter position of `S'` hits the support of the placement. -/
def NoHit (S S' : Set I) : Prop :=
  ∀ a k, ∀ i ∈ S', P.f i = (P.z a).pos k → i ∈ S

/-- No new parameter position of `S'` separates two positions of one cluster over `S`. -/
def NoSep (S S' : Set I) : Prop :=
  ∀ a k b l, P.SameCut S ((P.z a).pos k) ((P.z b).pos l) →
    ∀ i ∈ S', ¬((P.z a).pos k < P.f i ∧ P.f i < (P.z b).pos l)

/-- The placement has **no new event** over `S'`, relative to the old positions `S`. -/
def NoEvent (S S' : Set I) : Prop :=
  P.NoHit S S' ∧ P.NoSep S S'

variable {P}

theorem NoEvent.mono {S S' S'' : Set I} (h : P.NoEvent S S'') (hsub : S' ⊆ S'') :
    P.NoEvent S S' :=
  ⟨fun a k i hi => h.1 a k i (hsub hi), fun a k b l hc i hi => h.2 a k b l hc i (hsub hi)⟩

end Placement

/-! ## Support profiles and their codes -/

section Profile

variable {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I] {α : Type u}

/-- **Same support profile over `S`.** The two placements have the same labels, the same
order pattern on their formal supports, and the same comparisons (and coincidences) of every
support position with every old position of `S`. -/
def SameProfile (S : Set I) (P P' : Placement lab arity I α) : Prop :=
  (∀ a, (P.z a).label = (P'.z a).label) ∧
  (∀ a b k l (hk : k < arity (P.z a).label) (hl : l < arity (P.z b).label)
    (hk' : k < arity (P'.z a).label) (hl' : l < arity (P'.z b).label),
    (P.z a).pos ⟨k, hk⟩ < (P.z b).pos ⟨l, hl⟩ ↔
      (P'.z a).pos ⟨k, hk'⟩ < (P'.z b).pos ⟨l, hl'⟩) ∧
  (∀ a k (hk : k < arity (P.z a).label) (hk' : k < arity (P'.z a).label), ∀ s ∈ S,
    (P.f s < (P.z a).pos ⟨k, hk⟩ ↔ P'.f s < (P'.z a).pos ⟨k, hk'⟩) ∧
    ((P.z a).pos ⟨k, hk⟩ < P.f s ↔ (P'.z a).pos ⟨k, hk'⟩ < P'.f s))

theorem SameProfile.symm {S : Set I} {P P' : Placement lab arity I α}
    (h : SameProfile S P P') : SameProfile S P' P :=
  ⟨fun a => (h.1 a).symm,
    fun a b k l hk hl hk' hl' => (h.2.1 a b k l hk' hl' hk hl).symm,
    fun a k hk hk' s hs =>
      ⟨((h.2.2 a k hk' hk s hs).1).symm, ((h.2.2 a k hk' hk s hs).2).symm⟩⟩

theorem SameProfile.trans {S : Set I} {P P' P'' : Placement lab arity I α}
    (h : SameProfile S P P') (h' : SameProfile S P' P'') : SameProfile S P P'' := by
  refine ⟨fun a => (h.1 a).trans (h'.1 a), fun a b k l hk hl hk' hl' => ?_,
    fun a k hk hk' s hs => ?_⟩
  · have hk₁ : k < arity (P'.z a).label := by rw [← h.1 a]; exact hk
    have hl₁ : l < arity (P'.z b).label := by rw [← h.1 b]; exact hl
    exact (h.2.1 a b k l hk hl hk₁ hl₁).trans (h'.2.1 a b k l hk₁ hl₁ hk' hl')
  · have hk₁ : k < arity (P'.z a).label := by rw [← h.1 a]; exact hk
    exact ⟨((h.2.2 a k hk hk₁ s hs).1).trans ((h'.2.2 a k hk₁ hk' s hs).1),
      ((h.2.2 a k hk hk₁ s hs).2).trans ((h'.2.2 a k hk₁ hk' s hs).2)⟩

/-- Coincidences with old positions are part of the profile. -/
theorem SameProfile.pos_eq_iff {S : Set I} {P P' : Placement lab arity I α}
    (h : SameProfile S P P') (a : α) (k : ℕ) (hk : k < arity (P.z a).label)
    (hk' : k < arity (P'.z a).label) {s : I} (hs : s ∈ S) :
    P.f s = (P.z a).pos ⟨k, hk⟩ ↔ P'.f s = (P'.z a).pos ⟨k, hk'⟩ := by
  obtain ⟨h1, h2⟩ := h.2.2 a k hk hk' s hs
  constructor
  · intro heq
    refine le_antisymm (not_lt.mp fun hlt => ?_) (not_lt.mp fun hlt => ?_)
    · exact absurd (h2.mpr hlt) (by rw [heq]; exact lt_irrefl _)
    · exact absurd (h1.mpr hlt) (by rw [heq]; exact lt_irrefl _)
  · intro heq
    refine le_antisymm (not_lt.mp fun hlt => ?_) (not_lt.mp fun hlt => ?_)
    · exact absurd (h2.mp hlt) (by rw [heq]; exact lt_irrefl _)
    · exact absurd (h1.mp hlt) (by rw [heq]; exact lt_irrefl _)

/-! ### The link with `SupportProfile` -/

/-- The support profile of a placement over the old positions `S`, in the sense of
`SupportProfile`: the labels, the formal support `T₀` (the positions used by the terms), and
the comparisons of the formal support positions with `S`. -/
def Placement.profile (P : Placement lab arity I α) (S : Set I) : SupportProfile lab arity ↥S :=
  SupportProfile.ofTerms P.z (fun s : ↥S => P.f s)

/-- `SameProfile` is agreement of the support profiles. -/
theorem sameProfile_iff_agree {S : Set I} {P P' : Placement lab arity I α} :
    SameProfile S P P' ↔ (P.profile S).Agree (P'.profile S) id := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun a b k l hk hl hk' hl' => h2 a b k l hk hl hk' hl', fun a k hk hk' s => ?_⟩
    exact compare_eq_compare_iff.mpr ⟨(h3 a k hk hk' s.1 s.2).2, (h3 a k hk hk' s.1 s.2).1⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun a b k l hk hl hk' hl' => h2 a b k l hk hl hk' hl',
      fun a k hk hk' s hs => ?_⟩
    have h := compare_eq_compare_iff.mp (h3 a k hk hk' ⟨s, hs⟩)
    exact ⟨h.2, h.1⟩

/-- The formal support `T₀` of the profile of a tuple of length at most `σ` has size at most
`σ`. -/
theorem Placement.mk_profile_support_le {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hα : #α ≤ σ)
    (P : Placement lab arity I α) (S : Set I) : #(P.profile S).support ≤ σ := by
  have hmem : ∀ x : (P.profile S).support, x.1 ∈ tupleSupport P.z := by
    rintro ⟨x, a, k, h⟩
    exact Set.mem_iUnion.mpr ⟨a, k, h⟩
  have hinj : Function.Injective
      (fun x : (P.profile S).support => (⟨x.1, hmem x⟩ : ↥(tupleSupport P.z))) :=
    fun x y h => Subtype.ext (congrArg (fun w : ↥(tupleSupport P.z) => w.1) h)
  exact (mk_le_of_injective hinj).trans
    ((mk_tupleSupport_le hα P.z).trans (max_le hσinf le_rfl))

/-- The clusters of the profile are the classes of `Placement.SameCut`. -/
theorem Placement.profile_sameSlot_iff (P : Placement lab arity I α) (S : Set I)
    (x y : (P.profile S).support) :
    (P.profile S).SameSlot x y ↔ P.SameCut S x.1 y.1 := by
  constructor
  · intro h s hs
    exact (compare_gt_iff_gt.symm.trans (h ⟨s, hs⟩)).trans compare_gt_iff_gt
  · intro h s
    exact (compare_gt_iff_gt.trans (h s.1 s.2)).trans compare_gt_iff_gt.symm

/-! ### Codes: a well-order of size at most `χ` has at most `χ` cuts -/

open Classical in
/-- The least element of a subset of a well-order, if there is one. An upper set (the
complement of a cut) is determined by it. -/
noncomputable def leastElt {W : Type u} [LinearOrder W] [WellFoundedLT W] (A : Set W) :
    Option W :=
  if h : A.Nonempty then some (wellFounded_lt.min A h) else none

theorem mem_iff_leastElt {W : Type u} [LinearOrder W] [WellFoundedLT W] {A : Set W}
    (hA : IsUpperSet A) (w : W) : w ∈ A ↔ ∃ m, leastElt A = some m ∧ m ≤ w := by
  classical
  unfold leastElt
  by_cases h : A.Nonempty
  · simp only [h, ↓reduceDIte, Option.some.injEq, exists_eq_left']
    exact ⟨fun hw => not_lt.mp (wellFounded_lt.not_lt_min A hw),
      fun hle => hA hle (wellFounded_lt.min_mem A h)⟩
  · simp only [h, ↓reduceDIte, reduceCtorEq, false_and, exists_false, iff_false]
    exact fun hw => h ⟨w, hw⟩

variable [WellFoundedLT I]

/-- The code of the cut and coincidence of a position over the old positions `S`: the least
old position at or above it, and the least old position strictly above it. -/
noncomputable def Placement.cutCode (P : Placement lab arity I α) (S : Set I) (x : P.J) :
    Option ↥S × Option ↥S :=
  (leastElt {s : ↥S | x ≤ P.f s}, leastElt {s : ↥S | x < P.f s})

theorem Placement.cutCode_eq {P P' : Placement lab arity I α} {S : Set I} {x : P.J} {x' : P'.J}
    (h : P.cutCode S x = P'.cutCode S x') {s : I} (hs : s ∈ S) :
    (P.f s < x ↔ P'.f s < x') ∧ (x < P.f s ↔ x' < P'.f s) := by
  have e1 : leastElt {s : ↥S | x ≤ P.f s} = leastElt {s : ↥S | x' ≤ P'.f s} := congrArg Prod.fst h
  have e2 : leastElt {s : ↥S | x < P.f s} = leastElt {s : ↥S | x' < P'.f s} := congrArg Prod.snd h
  have h1 : x ≤ P.f s ↔ x' ≤ P'.f s := by
    have a := mem_iff_leastElt (A := {s : ↥S | x ≤ P.f s})
      (fun a b hab ha => le_trans ha (P.f.monotone hab)) ⟨s, hs⟩
    have b := mem_iff_leastElt (A := {s : ↥S | x' ≤ P'.f s})
      (fun a b hab ha => le_trans ha (P'.f.monotone hab)) ⟨s, hs⟩
    rw [e1] at a
    exact a.trans b.symm
  have h2 : x < P.f s ↔ x' < P'.f s := by
    have a := mem_iff_leastElt (A := {s : ↥S | x < P.f s})
      (fun a b hab ha => lt_of_lt_of_le ha (P.f.monotone hab)) ⟨s, hs⟩
    have b := mem_iff_leastElt (A := {s : ↥S | x' < P'.f s})
      (fun a b hab ha => lt_of_lt_of_le ha (P'.f.monotone hab)) ⟨s, hs⟩
    rw [e2] at a
    exact a.trans b.symm
  exact ⟨by rw [← not_le, ← not_le, h1], h2⟩

/-- Codes of support profiles over the old positions `S`: the labels, the order pattern of the
formal support positions `(a, k)`, and the cut code of every support position. -/
abbrev ProfileCode (lab : Type u) (α : Type u) (S : Set I) : Type u :=
  (α → lab) × Set ((α × ℕ) × (α × ℕ)) × (α × ℕ → Option ↥S × Option ↥S)

open Classical in
/-- The code of the support profile of a placement over `S`. -/
noncomputable def Placement.code (P : Placement lab arity I α) (S : Set I) :
    ProfileCode lab α S :=
  (fun a => (P.z a).label,
    {x | ∃ (hk : x.1.2 < arity (P.z x.1.1).label) (hl : x.2.2 < arity (P.z x.2.1).label),
      (P.z x.1.1).pos ⟨x.1.2, hk⟩ < (P.z x.2.1).pos ⟨x.2.2, hl⟩},
    fun x => if hk : x.2 < arity (P.z x.1).label then P.cutCode S ((P.z x.1).pos ⟨x.2, hk⟩)
      else (none, none))

/-- Placements with the same code have the same support profile. -/
theorem sameProfile_of_code_eq {S : Set I} {P P' : Placement lab arity I α}
    (h : P.code S = P'.code S) : SameProfile S P P' := by
  have h1 : ∀ a, (P.z a).label = (P'.z a).label := fun a => congrFun (congrArg Prod.fst h) a
  refine ⟨h1, fun a b k l hk hl hk' hl' => ?_, fun a k hk hk' s hs => ?_⟩
  · have h2 := congrArg (fun c : ProfileCode lab α S => ((a, k), (b, l)) ∈ c.2.1) h
    simp only [Placement.code, Set.mem_ofPred_eq, eq_iff_iff] at h2
    constructor
    · intro hlt
      obtain ⟨_, _, h⟩ := h2.mp ⟨hk, hl, hlt⟩
      exact h
    · intro hlt
      obtain ⟨_, _, h⟩ := h2.mpr ⟨hk', hl', hlt⟩
      exact h
  · have h3 := congrArg (fun c : ProfileCode lab α S => c.2.2 (a, k)) h
    simp only [Placement.code, dite_eq_left hk, dite_eq_left hk'] at h3
    exact Placement.cutCode_eq h3 hs

theorem mk_arrow_le_of_pow {A B : Type u} {σ χ : Cardinal.{u}} (hA : #A ≤ σ) (hB : #B ≤ χ)
    (hχ0 : χ ≠ 0) (hpow : χ ^ σ = χ) : #(A → B) ≤ χ := by
  rw [mk_arrow, lift_id, lift_id]
  calc #B ^ #A ≤ χ ^ #A := power_le_power_right hB
    _ ≤ χ ^ σ := power_le_power_left hχ0 hA
    _ = χ := hpow

theorem mk_prod_le_of_le {A B : Type u} {χ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hA : #A ≤ χ)
    (hB : #B ≤ χ) : #(A × B) ≤ χ := by
  rw [mk_prod, lift_id, lift_id]
  exact (mul_le_mul' hA hB).trans (mul_eq_self hχ).le

theorem mk_prod_nat_le {α : Type u} {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hα : #α ≤ σ) :
    #(α × ℕ) ≤ σ := by
  have h : #(α × ℕ) = #α * aleph0 := by simp [mk_prod]
  rw [h]
  exact (mul_le_mul' hα le_rfl).trans (mul_eq_left hσinf hσinf aleph0_ne_zero).le

/-- **There are at most `χ ^ σ = χ` profiles** over a set of old positions of size at most
`χ`. -/
theorem mk_profileCode_le {σ χ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hα : #α ≤ σ)
    (hlab : #lab ≤ χ) (hχinf : aleph0 ≤ χ) (hpow : χ ^ σ = χ) (S : Set I) (hS : #S ≤ χ) :
    #(ProfileCode lab α S) ≤ χ := by
  have hχ0 : χ ≠ 0 := (aleph0_pos.trans_le hχinf).ne'
  have hpos : #(α × ℕ) ≤ σ := mk_prod_nat_le hσinf hα
  have hpos2 : #((α × ℕ) × (α × ℕ)) ≤ σ := mk_prod_le_of_le hσinf hpos hpos
  have h1 : #(α → lab) ≤ χ := mk_arrow_le_of_pow hα hlab hχ0 hpow
  have h2 : #(Set ((α × ℕ) × (α × ℕ))) ≤ χ := by
    rw [mk_set]
    calc (2 : Cardinal.{u}) ^ #((α × ℕ) × (α × ℕ)) ≤ χ ^ #((α × ℕ) × (α × ℕ)) :=
          power_le_power_right ((natCast_lt_aleph0 (n := 2)).le.trans hχinf)
      _ ≤ χ ^ σ := power_le_power_left hχ0 hpos2
      _ = χ := hpow
  have hopt : #(Option ↥S) ≤ χ := by
    rw [mk_option]
    exact add_le_of_le hχinf hS (one_le_aleph0.trans hχinf)
  have h3 : #(α × ℕ → Option ↥S × Option ↥S) ≤ χ :=
    mk_arrow_le_of_pow hpos (mk_prod_le_of_le hχinf hopt hopt) hχ0 hpow
  exact mk_prod_le_of_le hχinf h1 (mk_prod_le_of_le hχinf h2 h3)

end Profile

/-! ## Continuations with no new event over all of `I` -/

section Continuation

variable {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I] {α : Type u}

/-- **Every profile has a continuation over `I` which leaves every cluster intact.** Amalgamate
`I` and the order of the placement over the old positions `S`, placing in every cut of `S`
the remaining positions of `I` before the remaining positions of the placement. So every
cluster is inserted at a single cut of `I` extending its cut over `S`: the result has the
same profile over `S` and no new event over all of `I`. -/
theorem exists_inert_continuation (P : Placement lab arity I α) (S : Set I) :
    ∃ P' : Placement lab arity I α, SameProfile S P P' ∧ P'.NoEvent S Set.univ := by
  classical
  let e : ↥S ↪o I := OrderEmbedding.subtype (· ∈ S)
  let e' : ↥S ↪o P.J := e.trans P.f
  let F : I ↪o LowerSet ↥S ×ₗ WithTop (I ⊕ₗ P.J) :=
    OrderEmbedding.ofStrictMono (OrderAmalgam.place e Sum.inlₗ)
      (OrderAmalgam.place_strictMono e _ fun _ _ h => Sum.Lex.inl_lt_inl_iff.mpr h)
  let H : P.J ↪o LowerSet ↥S ×ₗ WithTop (I ⊕ₗ P.J) :=
    OrderEmbedding.ofStrictMono (OrderAmalgam.place e' Sum.inrₗ)
      (OrderAmalgam.place_strictMono e' _ fun _ _ h => Sum.Lex.inr_lt_inr_iff.mpr h)
  have hFH : ∀ s (hs : s ∈ S), F s = H (P.f s) := by
    intro s hs
    change OrderAmalgam.place e Sum.inlₗ (e ⟨s, hs⟩) = OrderAmalgam.place e' Sum.inrₗ (e' ⟨s, hs⟩)
    rw [OrderAmalgam.place_apply, OrderAmalgam.place_apply]
  have hF : ∀ i, i ∉ S → F i = toLex (OrderAmalgam.cut e i,
      ((Sum.inlₗ i : I ⊕ₗ P.J) : WithTop (I ⊕ₗ P.J))) := by
    intro i hi
    have hr : i ∉ Set.range e := by rintro ⟨s, rfl⟩; exact hi s.2
    simp [F, OrderAmalgam.place, hr]
  have hH : ∀ x, ∃ w : WithTop (I ⊕ₗ P.J), H x = toLex (OrderAmalgam.cut e' x, w) ∧
      ∀ i : I, w ≠ ((Sum.inlₗ i : I ⊕ₗ P.J) : WithTop (I ⊕ₗ P.J)) ∧
        ¬ w < ((Sum.inlₗ i : I ⊕ₗ P.J) : WithTop (I ⊕ₗ P.J)) := by
    intro x
    by_cases hr : x ∈ Set.range e'
    · refine ⟨⊤, by simp [H, OrderAmalgam.place, hr], fun i => ⟨?_, ?_⟩⟩
      · exact (WithTop.coe_ne_top).symm
      · exact not_top_lt
    · refine ⟨((Sum.inrₗ x : I ⊕ₗ P.J) : WithTop (I ⊕ₗ P.J)),
        by simp [H, OrderAmalgam.place, hr], fun i => ⟨?_, ?_⟩⟩
      · intro h
        exact Sum.inr_ne_inl (toLex.injective (WithTop.coe_injective h))
      · intro h
        exact Sum.Lex.not_inr_lt_inl (WithTop.coe_lt_coe.mp h)
  -- a position of the placement lies strictly below a new position of `I` only across cuts
  have hlt : ∀ i, i ∉ S → ∀ x, H x < F i → OrderAmalgam.cut e' x < OrderAmalgam.cut e i := by
    intro i hi x hx
    obtain ⟨w, hw, hwi⟩ := hH x
    rw [hw, hF i hi, Prod.Lex.toLex_lt_toLex] at hx
    rcases hx with hx | ⟨-, hx⟩
    · exact hx
    · exact absurd hx (hwi i).2
  have hle : ∀ i, i ∉ S → ∀ y, F i < H y → OrderAmalgam.cut e i ≤ OrderAmalgam.cut e' y := by
    intro i hi y hy
    obtain ⟨w, hw, -⟩ := hH y
    rw [hw, hF i hi, Prod.Lex.toLex_lt_toLex] at hy
    rcases hy with hy | ⟨hy, -⟩
    · exact hy.le
    · exact hy.le
  refine ⟨{ J := LowerSet ↥S ×ₗ WithTop (I ⊕ₗ P.J), f := F,
            z := fun a => SupportTerm.along H (P.z a) },
    ⟨fun a => rfl, fun a b k l hk hl hk' hl' => H.lt_iff_lt.symm, fun a k hk hk' s hs => ?_⟩,
    ?_, ?_⟩
  · constructor
    · change _ ↔ F s < H _
      rw [hFH s hs]
      exact H.lt_iff_lt.symm
    · change _ ↔ H _ < F s
      rw [hFH s hs]
      exact H.lt_iff_lt.symm
  · intro a k i _ hi
    by_contra hiS
    change F i = H ((P.z a).pos k) at hi
    obtain ⟨w, hw, hwi⟩ := hH ((P.z a).pos k)
    rw [hw, hF i hiS] at hi
    exact (hwi i).1 (congrArg (fun p => (ofLex p).2) hi).symm
  · intro a k b l hcut i _ h12
    obtain ⟨h1, h2⟩ := h12
    by_cases hi : i ∈ S
    · exact lt_asymm ((hcut i hi).mpr h2) h1
    · change H ((P.z a).pos k) < F i at h1
      change F i < H ((P.z b).pos l) at h2
      have hc1 := hlt i hi _ h1
      have hc2 := hle i hi _ h2
      have heq : OrderAmalgam.cut e' ((P.z a).pos k) = OrderAmalgam.cut e' ((P.z b).pos l) := by
        refine SetLike.ext fun s => ?_
        rw [OrderAmalgam.mem_cut, OrderAmalgam.mem_cut]
        have h := hcut s.1 s.2
        change F s.1 < H _ ↔ F s.1 < H _ at h
        rw [hFH s.1 s.2, H.lt_iff_lt, H.lt_iff_lt] at h
        exact h
      exact absurd (hc1.trans_le hc2) (by rw [heq]; exact lt_irrefl _)

end Continuation

/-! ## No-event continuations of one profile have the same natural diagram -/

section NoEventComparison

variable {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I] {α : Type u}

namespace Placement

variable (P : Placement lab arity I α)

/-- The old positions `S` inside the order of the placement. -/
def oldEmb (S : Set I) : ↥S ↪o P.J :=
  (OrderEmbedding.subtype (· ∈ S)).trans P.f

/-- The slot of a position: its strict cut over the old positions `S`. -/
def slot (S : Set I) (x : P.J) : LowerSet ↥S :=
  OrderAmalgam.cut (P.oldEmb S) x

theorem mem_slot {S : Set I} {x : P.J} {s : ↥S} : s ∈ P.slot S x ↔ P.f s < x :=
  Iff.rfl

theorem slot_mono (S : Set I) : Monotone (P.slot S) :=
  OrderAmalgam.cut_mono _

theorem slot_eq_iff {S : Set I} {x y : P.J} : P.slot S x = P.slot S y ↔ P.SameCut S x y := by
  constructor
  · intro h s hs
    have h' : (⟨s, hs⟩ : ↥S) ∈ P.slot S x ↔ (⟨s, hs⟩ : ↥S) ∈ P.slot S y := by rw [h]
    exact h'
  · intro h
    exact SetLike.ext fun s => h s.1 s.2

/-- Positions in different slots are ordered as their slots. -/
theorem lt_iff_slot_lt {S : Set I} {x y : P.J} (h : P.slot S x ≠ P.slot S y) :
    x < y ↔ P.slot S x < P.slot S y := by
  constructor
  · intro hxy
    exact lt_of_le_of_ne (P.slot_mono S hxy.le) h
  · intro hlt
    by_contra hxy
    exact absurd (P.slot_mono S (not_lt.mp hxy)) (not_le.mpr hlt)

/-- An old position is the top of its (closed) slot. -/
theorem lt_old_of_slot_eq {S : Set I} {x : P.J} {s : I} (hs : s ∈ S)
    (h : P.slot S x = P.slot S (P.f s)) (hne : x ≠ P.f s) : x < P.f s := by
  by_contra hlt
  have hgt : P.f s < x := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)
  have hmem : (⟨s, hs⟩ : ↥S) ∈ P.slot S x := hgt
  rw [h] at hmem
  exact lt_irrefl _ (P.mem_slot.mp hmem)

/-- The joint support order: the support of the placement and the parameter positions `S'`. -/
def joinSet (S' : Set I) : Set P.J :=
  tupleSupport P.z ∪ P.f '' S'

theorem pos_mem_joinSet (S' : Set I) (a : α) (k : Fin (arity (P.z a).label)) :
    (P.z a).pos k ∈ P.joinSet S' :=
  Or.inl (termSupport_subset_tupleSupport P.z a (Set.mem_range_self k))

theorem old_mem_joinSet {S' : Set I} {i : I} (hi : i ∈ S') : P.f i ∈ P.joinSet S' :=
  Or.inr ⟨i, hi, rfl⟩

theorem exists_pos_of_mem_joinSet {S' : Set I} {x : P.J} (hx : x ∈ P.joinSet S')
    (hx' : x ∉ P.f '' S') : ∃ a k, (P.z a).pos k = x := by
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (hx.resolve_right hx')
  obtain ⟨k, hk⟩ := ha
  exact ⟨a, k, hk⟩

/-- The blocks used only by the placed tuple: the positions which are not parameter
positions. In every slot they form the cluster. -/
def firstBlock (S' : Set I) : Set ↥(P.joinSet S') :=
  {u | u.1 ∉ P.f '' S'}

/-- The blocks used only by the parameters: the new parameter positions below a cluster
position of their slot. -/
def secondBlock (S S' : Set I) : Set ↥(P.joinSet S') :=
  {u | (∃ i ∈ S', i ∉ S ∧ P.f i = u.1) ∧
    ∃ v : ↥(P.joinSet S'), v.1 ∉ P.f '' S' ∧ P.slot S v.1 = P.slot S u.1 ∧ u.1 < v.1}

theorem mem_blocks_of_lt {S S' : Set I} {u v : ↥(P.joinSet S')} (hv : v.1 ∉ P.f '' S')
    (hslot : P.slot S u.1 = P.slot S v.1) (hlt : u.1 < v.1) :
    u ∈ P.firstBlock S' ∪ P.secondBlock S S' := by
  by_cases hu : u.1 ∈ P.f '' S'
  · obtain ⟨i, hi, hiu⟩ := hu
    refine Or.inr ⟨⟨i, hi, fun hiS => ?_, hiu⟩, v, hv, hslot.symm, hlt⟩
    have hmem : (⟨i, hiS⟩ : ↥S) ∈ P.slot S v.1 := by
      change P.f i < v.1
      rw [hiu]; exact hlt
    rw [← hslot] at hmem
    have h2 : P.f i < u.1 := hmem
    rw [hiu] at h2
    exact lt_irrefl _ h2
  · exact Or.inl hu

open Classical in
/-- **The regions of Lemma 4.6 for moving every cluster to the bottom of its slot.** In the
joint support order, the region of a slot consists of its cluster and of the new parameter
positions below the cluster; the cluster is the right block. The regions are disjoint and
convex because no new parameter position separates a cluster. -/
noncomputable def regions (S S' : Set I) (hsep : P.NoSep S S') :
    BlockRegions ↥(P.joinSet S') where
  Region := LowerSet ↥S ×ₗ Bool
  key u := toLex (P.slot S u.1, if u ∈ P.firstBlock S' ∪ P.secondBlock S S' then false else true)
  key_mono := by
    intro u v huv
    rw [Prod.Lex.toLex_le_toLex]
    rcases (P.slot_mono S (show u.1 ≤ v.1 from huv)).lt_or_eq with h | h
    · exact Or.inl h
    · refine Or.inr ⟨h, ?_⟩
      by_cases hv : v ∈ P.firstBlock S' ∪ P.secondBlock S S'
      · have hu : u ∈ P.firstBlock S' ∪ P.secondBlock S S' := by
          rcases huv.lt_or_eq with hlt | heq
          · rcases hv with hv | hv
            · exact P.mem_blocks_of_lt hv h hlt
            · obtain ⟨-, w, hw, hws, hvw⟩ := hv
              exact P.mem_blocks_of_lt hw (h.trans hws.symm) (lt_trans hlt hvw)
          · rw [heq]; exact hv
        simp only [hu, hv, ite_true, le_refl]
      · simp only [hv, ite_false, Bool.le_true]
  first := P.firstBlock S'
  second := P.secondBlock S S'
  firstOnRight := Set.univ
  blocks_ordered := by
    intro x hx y hy hkey
    refine ⟨fun _ => ?_, fun h => absurd (Set.mem_univ _) h⟩
    have hslot : P.slot S x.1 = P.slot S y.1 := congrArg (fun p => (ofLex p).1) hkey
    obtain ⟨⟨i, hi, hiS, hiy⟩, w, hw, hws, hyw⟩ := hy
    by_contra hnot
    have hxy : x.1 < y.1 :=
      lt_of_le_of_ne (not_lt.mp hnot) (fun heq => hx ⟨i, hi, hiy.trans heq.symm⟩)
    obtain ⟨a, k, hk⟩ := P.exists_pos_of_mem_joinSet x.2 hx
    obtain ⟨b, l, hl⟩ := P.exists_pos_of_mem_joinSet w.2 hw
    refine hsep a k b l ?_ i hi ⟨?_, ?_⟩
    · rw [hk, hl]; exact P.slot_eq_iff.mp (hslot.trans hws.symm)
    · rw [hk, hiy]; exact hxy
    · rw [hl, hiy]; exact hyw
  region_blocks := by
    intro x y hkey hx
    have hflag := congrArg (fun p => (ofLex p).2) hkey
    by_contra hy
    simp [hx, hy] at hflag

/-- The order of the joint support after every cluster has been moved to the bottom of its
slot: first by slots; inside a slot the cluster precedes the parameter positions. -/
def NormLt (S S' : Set I) (x y : P.J) : Prop :=
  P.slot S x < P.slot S y ∨
    (P.slot S x = P.slot S y ∧
      ((x ∉ P.f '' S' ∧ y ∈ P.f '' S') ∨ ((x ∈ P.f '' S' ↔ y ∈ P.f '' S') ∧ x < y)))

theorem interchange_lt_of_first {S S' : Set I} (hsep : P.NoSep S S') {x y : ↥(P.joinSet S')}
    (hx : x.1 ∉ P.f '' S') (hy : y.1 ∈ P.f '' S') (hslot : P.slot S x.1 = P.slot S y.1) :
    (P.regions S S' hsep).interchange.toEquiv x < (P.regions S S' hsep).interchange.toEquiv y := by
  classical
  have hne : x.1 ≠ y.1 := fun h => hx (h ▸ hy)
  by_cases hy2 : y ∈ P.secondBlock S S'
  · have hxF : x ∈ P.firstBlock S' ∪ P.secondBlock S S' := Or.inl hx
    have hyF : y ∈ P.firstBlock S' ∪ P.secondBlock S S' := Or.inr hy2
    have hkey : (P.regions S S' hsep).key x = (P.regions S S' hsep).key y := by
      change toLex (P.slot S x.1, if x ∈ P.firstBlock S' ∪ P.secondBlock S S' then false else true)
        = toLex (P.slot S y.1, if y ∈ P.firstBlock S' ∪ P.secondBlock S S' then false else true)
      rw [ite_eq_left hxF, ite_eq_left hyF, hslot]
    have hc : (P.regions S S' hsep).Crossed x y := ⟨hkey, Or.inl ⟨hx, hy2⟩⟩
    exact ((P.regions S S' hsep).interchange.lt_iff_of_crossed x y hc).mpr
      (((P.regions S S' hsep).blocks_ordered x hx y hy2 hkey).1 (Set.mem_univ _))
  · have hc : ¬(P.regions S S' hsep).Crossed x y := by
      rintro ⟨-, ⟨-, h⟩ | ⟨-, h⟩⟩
      · exact hy2 h
      · exact h hy
    refine ((P.regions S S' hsep).interchange.lt_iff_of_not_crossed x y hc).mpr ?_
    obtain ⟨i, hi, hiy⟩ := hy
    change x.1 < y.1
    by_cases hiS : i ∈ S
    · rw [← hiy]
      exact P.lt_old_of_slot_eq hiS (by rw [hiy]; exact hslot) (by rw [hiy]; exact hne)
    · by_contra hnot
      have hlt : y.1 < x.1 := lt_of_le_of_ne (not_lt.mp hnot) (Ne.symm hne)
      exact hy2 ⟨⟨i, hi, hiS, hiy⟩, x, hx, hslot, hlt⟩

/-- The interchanged order of `regions` is the normalized order `NormLt`. -/
theorem interchange_lt_iff {S S' : Set I} (hsep : P.NoSep S S') (u v : ↥(P.joinSet S')) :
    (P.regions S S' hsep).interchange.toEquiv u < (P.regions S S' hsep).interchange.toEquiv v ↔
      P.NormLt S S' u.1 v.1 := by
  by_cases hslot : P.slot S u.1 = P.slot S v.1
  · by_cases hu : u.1 ∈ P.f '' S' <;> by_cases hv : v.1 ∈ P.f '' S'
    · have hc : ¬(P.regions S S' hsep).Crossed u v := by
        rintro ⟨-, ⟨h, -⟩ | ⟨-, h⟩⟩
        · exact h hu
        · exact h hv
      rw [(P.regions S S' hsep).interchange.lt_iff_of_not_crossed u v hc]
      change u.1 < v.1 ↔ _
      simp [NormLt, hslot, hu, hv]
    · have h := P.interchange_lt_of_first hsep hv hu hslot.symm
      constructor
      · intro h'
        exact absurd h (lt_asymm h')
      · rintro (h' | ⟨-, ⟨h', -⟩ | ⟨h', -⟩⟩)
        · rw [hslot] at h'; exact absurd h' (lt_irrefl _)
        · exact absurd hu h'
        · exact absurd (h'.mp hu) hv
    · exact iff_of_true (P.interchange_lt_of_first hsep hu hv hslot)
        (Or.inr ⟨hslot, Or.inl ⟨hu, hv⟩⟩)
    · have hc : ¬(P.regions S S' hsep).Crossed u v := by
        rintro ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩
        · obtain ⟨⟨i, hi, -, hiv⟩, -⟩ := h
          exact hv ⟨i, hi, hiv⟩
        · obtain ⟨⟨i, hi, -, hiu⟩, -⟩ := h
          exact hu ⟨i, hi, hiu⟩
      rw [(P.regions S S' hsep).interchange.lt_iff_of_not_crossed u v hc]
      change u.1 < v.1 ↔ _
      simp [NormLt, hslot, hu, hv]
  · have hc : ¬(P.regions S S' hsep).Crossed u v := by
      rintro ⟨hkey, -⟩
      exact hslot (congrArg (fun p => (ofLex p).1) hkey)
    rw [(P.regions S S' hsep).interchange.lt_iff_of_not_crossed u v hc]
    change u.1 < v.1 ↔ _
    rw [P.lt_iff_slot_lt hslot]
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd h hslot

end Placement

theorem Placement.normLt_congr {P P' : Placement lab arity I α} {S S' : Set I}
    {x y : P.J} {x' y' : P'.J}
    (hsx : P.slot S x = P'.slot S x') (hsy : P.slot S y = P'.slot S y')
    (hmx : x ∈ P.f '' S' ↔ x' ∈ P'.f '' S') (hmy : y ∈ P.f '' S' ↔ y' ∈ P'.f '' S')
    (hlt : (x ∈ P.f '' S' ↔ y ∈ P.f '' S') → (x < y ↔ x' < y')) :
    P.NormLt S S' x y ↔ P'.NormLt S S' x' y' := by
  have hlt' : (x' ∈ P'.f '' S' ↔ y' ∈ P'.f '' S') → (x < y ↔ x' < y') := by
    rw [← hmx, ← hmy]; exact hlt
  unfold Placement.NormLt
  rw [hsx, hsy, hmx, hmy]
  constructor
  · rintro (h | ⟨h1, h2 | ⟨h2, h3⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · exact Or.inr ⟨h1, Or.inr ⟨h2, (hlt' h2).mp h3⟩⟩
  · rintro (h | ⟨h1, h2 | ⟨h2, h3⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl h2⟩
    · exact Or.inr ⟨h1, Or.inr ⟨h2, (hlt' h2).mpr h3⟩⟩

/-- The slot of an old position does not depend on the placement. -/
theorem Placement.slot_old_eq (P P' : Placement lab arity I α) (S : Set I) (i : I) :
    P.slot S (P.f i) = P'.slot S (P'.f i) := by
  refine SetLike.ext fun s => ?_
  rw [Placement.mem_slot, Placement.mem_slot, P.f.lt_iff_lt, P'.f.lt_iff_lt]

theorem SameProfile.slot_eq {S : Set I} {P P' : Placement lab arity I α}
    (h : SameProfile S P P') (a : α) (k : ℕ) (hk : k < arity (P.z a).label)
    (hk' : k < arity (P'.z a).label) :
    P.slot S ((P.z a).pos ⟨k, hk⟩) = P'.slot S ((P'.z a).pos ⟨k, hk'⟩) :=
  SetLike.ext fun s => (h.2.2 a k hk hk' s.1 s.2).1

/-- With no new hit, a support position is a parameter position of `S'` in one placement iff
it is one in the other. -/
theorem SameProfile.mem_old_iff {S S' : Set I} {P P' : Placement lab arity I α}
    (h : SameProfile S P P') (hSS' : S ⊆ S') (hP : P.NoHit S S') (hP' : P'.NoHit S S')
    (a : α) (k : ℕ) (hk : k < arity (P.z a).label) (hk' : k < arity (P'.z a).label) :
    (P.z a).pos ⟨k, hk⟩ ∈ P.f '' S' ↔ (P'.z a).pos ⟨k, hk'⟩ ∈ P'.f '' S' := by
  constructor
  · rintro ⟨i, hi, hix⟩
    have hiS := hP a ⟨k, hk⟩ i hi hix
    exact ⟨i, hi, (h.pos_eq_iff a k hk hk' hiS).mp hix⟩
  · rintro ⟨i, hi, hix⟩
    have hiS := hP' a ⟨k, hk'⟩ i hi hix
    exact ⟨i, hi, (h.pos_eq_iff a k hk hk' hiS).mpr hix⟩

/-- A support position which is a parameter position is compared with every position of `I`
in the same way in both placements. -/
theorem SameProfile.lt_old_iff {S S' : Set I} {P P' : Placement lab arity I α}
    (h : SameProfile S P P') (hP : P.NoHit S S')
    (a : α) (k : ℕ) (hk : k < arity (P.z a).label) (hk' : k < arity (P'.z a).label)
    (hmem : (P.z a).pos ⟨k, hk⟩ ∈ P.f '' S') (i : I) :
    ((P.z a).pos ⟨k, hk⟩ < P.f i ↔ (P'.z a).pos ⟨k, hk'⟩ < P'.f i) ∧
      (P.f i < (P.z a).pos ⟨k, hk⟩ ↔ P'.f i < (P'.z a).pos ⟨k, hk'⟩) := by
  obtain ⟨j, hj, hjx⟩ := hmem
  have hjS := hP a ⟨k, hk⟩ j hj hjx
  have hjx' := (h.pos_eq_iff a k hk hk' hjS).mp hjx
  rw [← hjx, ← hjx', P.f.lt_iff_lt, P'.f.lt_iff_lt, P.f.lt_iff_lt, P'.f.lt_iff_lt]
  exact ⟨Iff.rfl, Iff.rfl⟩

namespace Placement

variable (P : Placement lab arity I α) {β : Type u}

theorem termSupport_z_subset (S' : Set I) (a : α) : termSupport (P.z a) ⊆ P.joinSet S' :=
  fun _ hx => Or.inl (termSupport_subset_tupleSupport P.z a hx)

theorem termSupport_par_subset {S' : Set I} {par : β → SupportTerm lab arity I}
    (hpar : ∀ b, termSupport (par b) ⊆ S') (b : β) :
    termSupport (SupportTerm.along P.f (par b)) ⊆ P.joinSet S' := by
  rintro _ ⟨k, rfl⟩
  exact Or.inr ⟨(par b).pos k, hpar b (Set.mem_range_self k), rfl⟩

theorem z_notMem_second {S S' : Set I} (hP : P.NoEvent S S') (a : α)
    (k : Fin (arity ((P.z a).restrict (P.joinSet S') (P.termSupport_z_subset S' a)).label)) :
    ((P.z a).restrict (P.joinSet S') (P.termSupport_z_subset S' a)).pos k ∉
      (P.regions S S' hP.2).second := by
  rintro ⟨⟨i, hi, hiS, hiy⟩, -⟩
  exact hiS (hP.1 a k i hi hiy)

theorem par_notMem_first {S S' : Set I} (hP : P.NoEvent S S')
    {par : β → SupportTerm lab arity I} (hpar : ∀ b, termSupport (par b) ⊆ S') (b : β)
    (k : Fin (arity ((SupportTerm.along P.f (par b)).restrict (P.joinSet S')
      (P.termSupport_par_subset hpar b)).label)) :
    ((SupportTerm.along P.f (par b)).restrict (P.joinSet S')
      (P.termSupport_par_subset hpar b)).pos k ∉ (P.regions S S' hP.2).first :=
  fun h => h ⟨(par b).pos k, hpar b (Set.mem_range_self k), rfl⟩

/-- The joint list of the placement and the parameters after every cluster has been moved to
the bottom of its slot over `S`, across the new parameter positions of `S'` below it. -/
noncomputable def normalForm {S S' : Set I} (hP : P.NoEvent S S')
    (par : β → SupportTerm lab arity I) (hpar : ∀ b, termSupport (par b) ⊆ S') :
    α ⊕ β → SupportTerm lab arity (P.regions S S' hP.2).Interchanged :=
  Sum.elim
    (fun a => (P.regions S S' hP.2).interchange.move
      ((P.z a).restrict (P.joinSet S') (P.termSupport_z_subset S' a))
      (Or.inl (P.z_notMem_second hP a)))
    (fun b => (P.regions S S' hP.2).interchange.move
      ((SupportTerm.along P.f (par b)).restrict (P.joinSet S') (P.termSupport_par_subset hpar b))
      (Or.inr (P.par_notMem_first hP hpar b)))

end Placement

variable {K : AbstractElementaryClass.{u}} [CategoricalUnbounded K]
  {E : OrderPresentation K} {D : StableDiagram K}
  {I : Type u} [LinearOrder I] [Nonempty I] {α β : Type u} {σ : Cardinal.{u}}

/-- **Lemma 4.6 on the slots.** Moving every cluster of a placement with no new event to the
bottom of its slot does not change the joint natural diagram with the parameters: the slots
are disjoint, so Lemma 4.6 applies simultaneously. -/
theorem Placement.sameNaturalDiagram_normalForm (hσinf : aleph0 ≤ σ) (hjoint : #(α ⊕ β) ≤ σ)
    (P : Placement E.lab E.arity I α) {S S' : Set I} (hne : S'.Nonempty)
    (hP : P.NoEvent S S') (par : β → SupportTerm E.lab E.arity I)
    (hpar : ∀ b, termSupport (par b) ⊆ S') :
    haveI : Nonempty ↥(P.joinSet S') := ⟨⟨P.f hne.some, P.old_mem_joinSet hne.some_mem⟩⟩
    SameNaturalDiagram K E D σ hjoint (P.joint par) (P.normalForm hP par hpar) := by
  haveI : Nonempty ↥(P.joinSet S') := ⟨⟨P.f hne.some, P.old_mem_joinSet hne.some_mem⟩⟩
  have step1 : SameNaturalDiagram K E D σ hjoint (P.joint par)
      (Sum.elim (fun a => (P.z a).restrict (P.joinSet S') (P.termSupport_z_subset S' a))
        (fun b => (SupportTerm.along P.f (par b)).restrict (P.joinSet S')
          (P.termSupport_par_subset hpar b))) :=
    sameNaturalDiagram_of_along_eq (OrderEmbedding.subtype (· ∈ P.joinSet S')) _ _
      (by rintro (a | b) <;> rfl)
  have step2 := lemma_4_6 K E D σ hjoint hσinf
    (fun a => (P.z a).restrict (P.joinSet S') (P.termSupport_z_subset S' a))
    (fun b => (SupportTerm.along P.f (par b)).restrict (P.joinSet S')
      (P.termSupport_par_subset hpar b))
    (P.regions S S' hP.2) (P.z_notMem_second hP) (P.par_notMem_first hP hpar)
  exact step1.trans hσinf step2

/-- **No-event comparison.** For `S' ⊇ S`, all continuations of a profile over `S` with no new
event over `S'` have the same natural diagram with parameters supported in `S'`. Within each
old slot, the whole cluster can only change its position across a block of new parameter
positions; both continuations are compared with the one whose clusters are at the bottom of
their slots. -/
theorem sameNaturalDiagram_of_sameProfile_noEvent (hσinf : aleph0 ≤ σ)
    (hjoint : #(α ⊕ β) ≤ σ) (P P' : Placement E.lab E.arity I α) {S S' : Set I}
    (hSS' : S ⊆ S') (hne : S'.Nonempty) (hprof : SameProfile S P P')
    (hP : P.NoEvent S S') (hP' : P'.NoEvent S S')
    (par : β → SupportTerm E.lab E.arity I) (hpar : ∀ b, termSupport (par b) ⊆ S') :
    SameNaturalDiagram K E D σ hjoint (P.joint par) (P'.joint par) := by
  haveI : Nonempty ↥(P.joinSet S') := ⟨⟨P.f hne.some, P.old_mem_joinSet hne.some_mem⟩⟩
  haveI : Nonempty ↥(P'.joinSet S') := ⟨⟨P'.f hne.some, P'.old_mem_joinSet hne.some_mem⟩⟩
  have n1 := P.sameNaturalDiagram_normalForm (D := D) hσinf hjoint hne hP par hpar
  have n2 := P'.sameNaturalDiagram_normalForm (D := D) hσinf hjoint hne hP' par hpar
  have mid : SameNaturalDiagram K E D σ hjoint (P.normalForm hP par hpar)
      (P'.normalForm hP' par hpar) := by
    refine sameNaturalDiagram_of_pattern _ _ ?_ ?_
    · rintro (a | b)
      · exact hprof.1 a
      · rfl
    · rintro (a | b) (a' | b') k l hk hl hk' hl'
      · exact (P.interchange_lt_iff hP.2 ⟨_, P.pos_mem_joinSet S' a ⟨k, hk⟩⟩
            ⟨_, P.pos_mem_joinSet S' a' ⟨l, hl⟩⟩).trans
          ((Placement.normLt_congr (hprof.slot_eq a k hk hk') (hprof.slot_eq a' l hl hl')
            (hprof.mem_old_iff hSS' hP.1 hP'.1 a k hk hk')
            (hprof.mem_old_iff hSS' hP.1 hP'.1 a' l hl hl')
            (fun _ => hprof.2.1 a a' k l hk hl hk' hl')).trans
          (P'.interchange_lt_iff hP'.2 ⟨_, P'.pos_mem_joinSet S' a ⟨k, hk'⟩⟩
            ⟨_, P'.pos_mem_joinSet S' a' ⟨l, hl'⟩⟩).symm)
      · have hi : (par b').pos ⟨l, hl⟩ ∈ S' := hpar b' (Set.mem_range_self _)
        exact (P.interchange_lt_iff hP.2 ⟨_, P.pos_mem_joinSet S' a ⟨k, hk⟩⟩
            ⟨_, P.old_mem_joinSet hi⟩).trans
          ((Placement.normLt_congr (hprof.slot_eq a k hk hk') (P.slot_old_eq P' S _)
            (hprof.mem_old_iff hSS' hP.1 hP'.1 a k hk hk')
            (iff_of_true ⟨_, hi, rfl⟩ ⟨_, hi, rfl⟩)
            (fun hiff => (hprof.lt_old_iff hP.1 a k hk hk' (hiff.mpr ⟨_, hi, rfl⟩) _).1)).trans
          (P'.interchange_lt_iff hP'.2 ⟨_, P'.pos_mem_joinSet S' a ⟨k, hk'⟩⟩
            ⟨_, P'.old_mem_joinSet hi⟩).symm)
      · have hi : (par b).pos ⟨k, hk⟩ ∈ S' := hpar b (Set.mem_range_self _)
        exact (P.interchange_lt_iff hP.2 ⟨_, P.old_mem_joinSet hi⟩
            ⟨_, P.pos_mem_joinSet S' a' ⟨l, hl⟩⟩).trans
          ((Placement.normLt_congr (P.slot_old_eq P' S _) (hprof.slot_eq a' l hl hl')
            (iff_of_true ⟨_, hi, rfl⟩ ⟨_, hi, rfl⟩)
            (hprof.mem_old_iff hSS' hP.1 hP'.1 a' l hl hl')
            (fun hiff => (hprof.lt_old_iff hP.1 a' l hl hl' (hiff.mp ⟨_, hi, rfl⟩) _).2)).trans
          (P'.interchange_lt_iff hP'.2 ⟨_, P'.old_mem_joinSet hi⟩
            ⟨_, P'.pos_mem_joinSet S' a' ⟨l, hl'⟩⟩).symm)
      · have hi : (par b).pos ⟨k, hk⟩ ∈ S' := hpar b (Set.mem_range_self _)
        have hi' : (par b').pos ⟨l, hl⟩ ∈ S' := hpar b' (Set.mem_range_self _)
        exact (P.interchange_lt_iff hP.2 ⟨_, P.old_mem_joinSet hi⟩
            ⟨_, P.old_mem_joinSet hi'⟩).trans
          ((Placement.normLt_congr (P.slot_old_eq P' S _) (P.slot_old_eq P' S _)
            (iff_of_true ⟨_, hi, rfl⟩ ⟨_, hi, rfl⟩) (iff_of_true ⟨_, hi', rfl⟩ ⟨_, hi', rfl⟩)
            (fun _ => by rw [P.f.lt_iff_lt, P'.f.lt_iff_lt])).trans
          (P'.interchange_lt_iff hP'.2 ⟨_, P'.old_mem_joinSet hi⟩
            ⟨_, P'.old_mem_joinSet hi'⟩).symm)
  exact (n1.trans hσinf mid).trans hσinf (sameNaturalDiagram_symm E D n2)

end NoEventComparison

/-! ## New events are few -/

section Events

variable {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I] {α : Type u}

/-- Codes of new events: the hit of a formal support position, or the separation of a pair of
formal support positions. -/
abbrev EventCode (α : Type u) : Type u :=
  (α × ℕ) ⊕ ((α × ℕ) × (α × ℕ))

/-- There are at most `σ + σ² = σ` events. -/
theorem mk_eventCode_le {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hα : #α ≤ σ) :
    #(EventCode α) ≤ σ := by
  have hpos : #(α × ℕ) ≤ σ := mk_prod_nat_le hσinf hα
  rw [mk_sum, lift_id, lift_id]
  exact add_le_of_le hσinf hpos (mk_prod_le_of_le hσinf hpos hpos)

/-- The event `e` is a new event of the placement over `S'`, relative to the old positions
`S`: a new parameter position hits the support position, or separates the pair of positions
of one cluster. -/
def Placement.IsEvent (P : Placement lab arity I α) (S S' : Set I) : EventCode α → Prop
  | Sum.inl x => ∃ hk : x.2 < arity (P.z x.1).label,
      ∃ i ∈ S', i ∉ S ∧ P.f i = (P.z x.1).pos ⟨x.2, hk⟩
  | Sum.inr (x, y) => ∃ (hk : x.2 < arity (P.z x.1).label) (hl : y.2 < arity (P.z y.1).label),
      P.SameCut S ((P.z x.1).pos ⟨x.2, hk⟩) ((P.z y.1).pos ⟨y.2, hl⟩) ∧
        ∃ i ∈ S', (P.z x.1).pos ⟨x.2, hk⟩ < P.f i ∧ P.f i < (P.z y.1).pos ⟨y.2, hl⟩

theorem Placement.exists_event_of_not_noEvent {P : Placement lab arity I α} {S S' : Set I}
    (h : ¬P.NoEvent S S') : ∃ e, P.IsEvent S S' e := by
  by_cases hh : P.NoHit S S'
  · have hs : ¬P.NoSep S S' := fun hs => h ⟨hh, hs⟩
    unfold Placement.NoSep at hs
    push Not at hs
    obtain ⟨a, k, b, l, hc, i, hi, h1, h2⟩ := hs
    exact ⟨Sum.inr ((a, k.1), (b, l.1)), k.2, l.2, hc, i, hi, h1, h2⟩
  · unfold Placement.NoHit at hh
    push Not at hh
    obtain ⟨a, k, i, hi, hik, hiS⟩ := hh
    exact ⟨Sum.inl (a, k.1), k.2, i, hi, hiS, hik⟩

/-- A support position can be newly hit only once, and a pair can be newly separated only
once: an event over `S'` is not a new event relative to any `T ⊇ S'`. -/
theorem Placement.IsEvent.not_later {P : Placement lab arity I α} {S S' T T' : Set I}
    (hsub : S' ⊆ T) {e : EventCode α} (h : P.IsEvent S S' e) (h' : P.IsEvent T T' e) :
    False := by
  rcases e with x | ⟨x, y⟩
  · obtain ⟨hk, i, hi, -, hix⟩ := h
    obtain ⟨hk', j, hj, hjT, hjx⟩ := h'
    have hij : i = j := P.f.injective (hix.trans hjx.symm)
    exact hjT (hij ▸ hsub hi)
  · obtain ⟨hk, hl, -, i, hi, h1, h2⟩ := h
    obtain ⟨hk', hl', hc, -⟩ := h'
    exact lt_asymm ((hc i (hsub hi)).mpr h2) h1

end Events

/-! ## Stages -/

section Stages

variable {A : Type u} {Θ : Type u} [LinearOrder Θ] [WellFoundedLT Θ]

/-- The stages of the obstruction: `X i = ⋃ j < i, G (X j)`, where `G` adjoins the failing
sets to a parameter set. (So unions are taken at limits.) -/
noncomputable def stageSet (G : Set A → Set A) : Θ → Set A :=
  wellFounded_lt.fix fun i rec => ⋃ j : {j // j < i}, G (rec j.1 j.2)

theorem stageSet_eq (G : Set A → Set A) (i : Θ) :
    stageSet G i = ⋃ j : {j // j < i}, G (stageSet G j.1) :=
  WellFounded.fix_eq _ _ _

theorem step_subset_stageSet (G : Set A → Set A) {i j : Θ} (h : j < i) :
    G (stageSet G j) ⊆ stageSet G i := by
  rw [stageSet_eq G i]
  exact Set.subset_iUnion (fun j : {j // j < i} => G (stageSet G j.1)) ⟨j, h⟩

/-- Every set constructed has size at most `χ`. -/
theorem mk_stageSet_le {χ : Cardinal.{u}} (hχ : aleph0 ≤ χ) (hΘ : #Θ ≤ χ) (G : Set A → Set A)
    (hG : ∀ X : Set A, #X ≤ χ → #(G X) ≤ χ) (i : Θ) : #(stageSet G i) ≤ χ := by
  refine WellFounded.induction (C := fun i => #(stageSet G i) ≤ χ) wellFounded_lt i ?_
  intro i ih
  rw [stageSet_eq]
  refine (mk_iUnion_le _).trans ?_
  exact (mul_le_mul' ((mk_subtype_le _).trans hΘ)
    (ciSup_le' fun j : {j // j < i} => hG _ (ih j.1 j.2))).trans (mul_eq_self hχ).le

end Stages

/-! ## Local realizability and the obstruction -/

section Obstruction

variable {K : AbstractElementaryClass.{u}} {I : Type u} [LinearOrder I] [Nonempty I]
  {α : Type u}

/-- The supports `S_X ⊆ I` of a parameter set `X ⊆ E(I)`, for the fixed term representations
`supportTermOf` (with one extra point, so that it is nonempty). -/
noncomputable def paramSupport (E : OrderPresentation K) (X : Set (E.obj I).carrier) : Set I :=
  {Classical.arbitrary I} ∪ tupleSupport (fun x : ↥X => supportTermOf E x.1)

theorem paramSupport_nonempty (E : OrderPresentation K) (X : Set (E.obj I).carrier) :
    (paramSupport E X).Nonempty :=
  ⟨Classical.arbitrary I, Or.inl rfl⟩

theorem termSupport_subset_paramSupport (E : OrderPresentation K) {X : Set (E.obj I).carrier}
    {x : (E.obj I).carrier} (hx : x ∈ X) :
    termSupport (supportTermOf E x) ⊆ paramSupport E X :=
  fun _ hi => Or.inr (termSupport_subset_tupleSupport
    (fun x : ↥X => supportTermOf E x.1) ⟨x, hx⟩ hi)

theorem paramSupport_mono (E : OrderPresentation K) {X Y : Set (E.obj I).carrier}
    (h : X ⊆ Y) : paramSupport E X ⊆ paramSupport E Y := by
  rintro i (hi | hi)
  · exact Or.inl hi
  · obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hi
    exact termSupport_subset_paramSupport E (h x.2) hx

theorem mk_paramSupport_le (E : OrderPresentation K) {χ : Cardinal.{u}} (hχ : aleph0 ≤ χ)
    {X : Set (E.obj I).carrier} (hX : #X ≤ χ) : #(paramSupport E X) ≤ χ := by
  refine (mk_union_le _ _).trans (add_le_of_le hχ ?_ ?_)
  · rw [mk_singleton]; exact one_le_aleph0.trans hχ
  · exact (mk_tupleSupport_le hX _).trans (max_le hχ le_rfl)

/-- The placement `P` realizes the joint diagram of the tuple `tgt` with the parameters `p`:
the placed tuple together with the fixed term representations of the parameters has the
natural diagram of `tgt`. -/
def Placement.Solves (E : OrderPresentation K) (D : StableDiagram K)
    (P : Placement E.lab E.arity I α) (ρ : Cardinal.{u}) {β : Type u} (hj : #(α ⊕ β) ≤ ρ)
    (p : β → (E.obj I).carrier) (tgt : α ⊕ β → (E.obj I).carrier) : Prop :=
  SameNaturalDiagram K E D ρ hj (P.joint (fun b => supportTermOf E (p b)))
    (fun i => supportTermOf E (tgt i))

variable [CategoricalUnbounded K] {E : OrderPresentation K} {D : StableDiagram K}

/-- Realizing a prescription realizes its restrictions, when the prescriptions restrict
coherently. -/
theorem Placement.Solves.comp {P : Placement E.lab E.arity I α} {ρ : Cardinal.{u}}
    (hρinf : aleph0 ≤ ρ) {β β' : Type u} {hj : #(α ⊕ β) ≤ ρ} {p : β → (E.obj I).carrier}
    {tgt : α ⊕ β → (E.obj I).carrier} (h : P.Solves E D ρ hj p tgt)
    (hj' : #(α ⊕ β') ≤ ρ) (ι : β' → β) (tgt' : α ⊕ β' → (E.obj I).carrier)
    (hcoh : SameNaturalDiagram K E D ρ hj' (fun i => supportTermOf E (tgt (Sum.map id ι i)))
      (fun i => supportTermOf E (tgt' i))) :
    P.Solves E D ρ hj' (fun b => p (ι b)) tgt' := by
  have h1 := SameNaturalDiagram.comp hρinf h hj' (Sum.map id ι)
  have heq : (fun c => P.joint (fun b => supportTermOf E (p b)) (Sum.map id ι c)) =
      P.joint (fun b => supportTermOf E (p (ι b))) := by
    funext c
    rcases c with a | b <;> rfl
  rw [heq] at h1
  exact h1.trans hρinf hcoh

/-- **One prescription has a placement.** Extend `I` to a categoricity size above the diagram
threshold; by Proposition 4.2 a strong map carries the parameter part of the prescribed tuple
to the actual parameter tuple, and the image of the rest realizes the prescribed joint
diagram. The realization has term representations in that presentation. -/
theorem exists_local_placement {ρ : Cardinal.{u}} (hρinf : aleph0 ≤ ρ) {β : Type u}
    (hj : #(α ⊕ β) ≤ ρ) (hβ : #β ≤ ρ) (hcardI : D.t ρ ≤ Model.card (E.obj I))
    (p : β → (E.obj I).carrier) (tgt : α ⊕ β → (E.obj I).carrier)
    (hnat : D.same hβ (orderPresentation_obj_mem E I) (orderPresentation_obj_mem E I)
      hcardI hcardI (fun b => tgt (Sum.inr b)) p) :
    ∃ P : Placement E.lab E.arity I α, P.Solves E D ρ hj p tgt := by
  obtain ⟨L, linL, nonL, e, hcL, hcat⟩ := exists_categorical_extension E I (D.t ρ)
  have hI : K.Mem (E.obj I) := orderPresentation_obj_mem E I
  have hM : K.Mem (E.obj L) := orderPresentation_obj_mem E L
  have hL := same_map hρinf e hcardI hcL hI hM _ _ hnat
  obtain ⟨g, hg, hgxy⟩ := D.to_strong hβ hM hM _ _ hρinf hcat rfl hcL hcL hL
  refine ⟨{ J := L, f := e, z := fun a => supportTermOf E (g (E.map e (tgt (Sum.inl a)))) }, ?_⟩
  refine sameNaturalDiagram_of_along_right e ?_
  refine sameNaturalDiagram_of_D_same E D hj _ _ hcL hM ?_
  refine D.symm hj hM hM hcL hcL _ _ (D.of_strong hj hM hM hcL hcL _ _ g hρinf hg ?_)
  rintro (a | b)
  · change g (E.realize (SupportTerm.along e (supportTermOf E (tgt (Sum.inl a))))) =
      E.realize (supportTermOf E (g (E.map e (tgt (Sum.inl a)))))
    rw [← E.realize_along, realize_supportTermOf, realize_supportTermOf]
  · change g (E.realize (SupportTerm.along e (supportTermOf E (tgt (Sum.inr b))))) =
      E.realize (SupportTerm.along e (supportTermOf E (p b)))
    rw [← E.realize_along, ← E.realize_along, realize_supportTermOf, realize_supportTermOf]
    exact hgxy b

/-- **Proposition 4.9 (Compact placement), in placement form.** Let `χ > ℓ + σ` satisfy
`χ ^ σ = χ`. Suppose that for every parameter tuple `p` of length at most `χ` in `E(I)` a
joint diagram is prescribed, as the diagram of a tuple `q p` of `E(I)`; that the
prescriptions restrict coherently (`hcoh`); and that their parameter diagrams are the natural
ones (`hnat`). Then one placement over `I` realizes all the prescriptions.

Proof as in `text.md`. If no placement solves all the prescriptions, build `σ⁺` stages of
parameter sets of size at most `χ`: for every profile over the current set `X` choose a
continuation with no new event over all of `I` and adjoin a set on which it fails. A
placement solving the prescription of the union has, at every stage, the profile of one of
the chosen continuations; with no new event at that stage, the no-event comparison would
identify its diagram on the failing set with that of the chosen continuation. So it has a
new event at every one of the `σ⁺` stages, but there are at most `σ` events. -/
theorem compact_placement (E : OrderPresentation K) (D : StableDiagram K)
    [WellFoundedLT I] (σ χ : Cardinal.{u}) (hσinf : aleph0 ≤ σ) (hσ : #α ≤ σ)
    (hχ : ls K + σ < χ) (hpow : χ ^ σ = χ)
    (hcardI : D.t (σ + χ) ≤ Model.card (E.obj I))
    (q : ∀ {β : Type u}, #β ≤ χ → (β → (E.obj I).carrier) → α ⊕ β → (E.obj I).carrier)
    (hnat : ∀ {β : Type u} (hβ : #β ≤ χ) (p : β → (E.obj I).carrier) (hβ' : #β ≤ σ + χ),
      D.same hβ' (orderPresentation_obj_mem E I) (orderPresentation_obj_mem E I)
        hcardI hcardI (fun b => q hβ p (Sum.inr b)) p)
    (hcoh : ∀ {β β' : Type u} (hβ : #β ≤ χ) (hβ' : #β' ≤ χ) (p : β → (E.obj I).carrier)
      (ι : β' → β) (hj : #(α ⊕ β') ≤ σ + χ),
      D.same hj (orderPresentation_obj_mem E I) (orderPresentation_obj_mem E I)
        hcardI hcardI (fun i => q hβ p (Sum.map id ι i)) (q hβ' (fun b => p (ι b)))) :
    ∃ P : Placement E.lab E.arity I α,
      ∀ {β : Type u} (hβ : #β ≤ χ) (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ σ + χ),
        P.Solves E D (σ + χ) hj p (q hβ p) := by
  classical
  have hσχ : σ ≤ χ := (self_le_add_left σ (ls K)).trans hχ.le
  have hχinf : aleph0 ≤ χ := hσinf.trans hσχ
  have hρinf : aleph0 ≤ σ + χ := hσinf.trans (self_le_add_right σ χ)
  have hlab : #E.lab ≤ χ :=
    (E.lab_small.trans E.ell_eq.le).trans ((self_le_add_right (ls K) σ).trans hχ.le)
  have hI : K.Mem (E.obj I) := orderPresentation_obj_mem E I
  have hjoint : ∀ {β : Type u}, #β ≤ χ → #(α ⊕ β) ≤ σ + χ := fun hβ => by
    rw [mk_sum, lift_id, lift_id]; exact add_le_add hσ hβ
  have hpar : ∀ {β : Type u}, #β ≤ χ → #β ≤ σ + χ := fun hβ =>
    hβ.trans (self_le_add_left χ σ)
  -- solving a prescription solves its restrictions
  have hrestr : ∀ (P : Placement E.lab E.arity I α) {β β' : Type u} (hβ : #β ≤ χ)
      (hβ' : #β' ≤ χ) (p : β → (E.obj I).carrier) (ι : β' → β),
      P.Solves E D (σ + χ) (hjoint hβ) p (q hβ p) →
      P.Solves E D (σ + χ) (hjoint hβ') (fun b => p (ι b)) (q hβ' (fun b => p (ι b))) := by
    intro P β β' hβ hβ' p ι h
    refine h.comp hρinf (hjoint hβ') ι _ ?_
    refine sameNaturalDiagram_of_D_same E D (hjoint hβ') _ _ hcardI hI ?_
    simp only [realize_supportTermOf]
    exact hcoh hβ hβ' p ι (hjoint hβ')
  by_contra hno
  push Not at hno
  -- every placement fails the prescription of some parameter set of size at most `χ`
  have hbad : ∀ P : Placement E.lab E.arity I α, ∃ Y : Set (E.obj I).carrier,
      ∃ hY : #Y ≤ χ, ¬P.Solves E D (σ + χ) (hjoint hY) (Subtype.val : ↥Y → (E.obj I).carrier)
        (q hY Subtype.val) := by
    intro P
    obtain ⟨β, hβ, p, hj, hfail⟩ := hno P
    refine ⟨Set.range p, mk_range_le.trans hβ, fun hsol => hfail ?_⟩
    exact hrestr P (mk_range_le.trans hβ) hβ Subtype.val (Set.rangeFactorization p) hsol
  choose bad hbadcard hbadfail using hbad
  -- one stage: adjoin a failing set of a no-event continuation of every profile
  let G : Set (E.obj I).carrier → Set (E.obj I).carrier := fun X =>
    X ∪ ⋃ k : ProfileCode E.lab α (paramSupport E X),
      if h : ∃ P : Placement E.lab E.arity I α,
          P.code (paramSupport E X) = k ∧ P.NoEvent (paramSupport E X) Set.univ
        then bad (Classical.choose h) else ∅
  have hGsub : ∀ X, X ⊆ G X := fun X => Set.subset_union_left
  have hGcard : ∀ X : Set (E.obj I).carrier, #X ≤ χ → #(G X) ≤ χ := by
    intro X hX
    refine (mk_union_le _ _).trans (add_le_of_le hχinf hX ?_)
    refine (mk_iUnion_le _).trans ?_
    refine (mul_le_mul' (mk_profileCode_le hσinf hσ hlab hχinf hpow _
      (mk_paramSupport_le E hχinf hX)) (ciSup_le' fun k => ?_)).trans (mul_eq_self hχinf).le
    split_ifs with h
    · exact hbadcard _
    · simp
  have hGspec : ∀ (P₀ : Placement E.lab E.arity I α) (X : Set (E.obj I).carrier),
      ∃ P' : Placement E.lab E.arity I α, SameProfile (paramSupport E X) P₀ P' ∧
        P'.NoEvent (paramSupport E X) Set.univ ∧ bad P' ⊆ G X := by
    intro P₀ X
    obtain ⟨P₁, hprof, hne⟩ := exists_inert_continuation P₀ (paramSupport E X)
    have hex : ∃ P : Placement E.lab E.arity I α,
        P.code (paramSupport E X) = P₁.code (paramSupport E X) ∧
          P.NoEvent (paramSupport E X) Set.univ := ⟨P₁, rfl, hne⟩
    refine ⟨Classical.choose hex,
      hprof.trans (sameProfile_of_code_eq (Classical.choose_spec hex).1).symm,
      (Classical.choose_spec hex).2, fun y hy => ?_⟩
    refine Or.inr (Set.mem_iUnion.mpr ⟨P₁.code (paramSupport E X), ?_⟩)
    rw [dite_eq_left hex]
    exact hy
  -- the `σ⁺` stages and their union
  have hΘ : #(Below (Order.succ σ)) = Order.succ σ := mk_ord_toType _
  have hΘχ : #(Below (Order.succ σ)) ≤ χ :=
    hΘ.le.trans (Order.succ_le_of_lt (lt_of_le_of_lt (self_le_add_left σ (ls K)) hχ))
  let X : Below (Order.succ σ) → Set (E.obj I).carrier := stageSet G
  have hXcard : ∀ i, #(X i) ≤ χ := mk_stageSet_le hχinf hΘχ G hGcard
  have hXs : #(⋃ i, G (X i)) ≤ χ :=
    (mk_iUnion_le _).trans ((mul_le_mul' hΘχ
      (ciSup_le' fun i => hGcard _ (hXcard i))).trans (mul_eq_self hχinf).le)
  -- a placement realizing the prescription of the union
  obtain ⟨Ps, hPs⟩ := exists_local_placement (D := D) hρinf (hjoint hXs) (hpar hXs) hcardI
    (Subtype.val : ↥(⋃ i, G (X i)) → (E.obj I).carrier) (q hXs Subtype.val) (hnat hXs _ _)
  -- it has a new event at every stage
  have hevent : ∀ i, ¬Ps.NoEvent (paramSupport E (X i)) (paramSupport E (G (X i))) := by
    intro i hNE
    obtain ⟨P', hprof, hP'ne, hbadsub⟩ := hGspec Ps (X i)
    have hsubs : G (X i) ⊆ ⋃ i, G (X i) := Set.subset_iUnion (fun i => G (X i)) i
    have hGc : #(G (X i)) ≤ χ := hGcard _ (hXcard i)
    have h1 : Ps.Solves E D (σ + χ) (hjoint hGc) (Subtype.val : ↥(G (X i)) → (E.obj I).carrier)
        (q hGc Subtype.val) :=
      hrestr Ps hXs hGc Subtype.val (Set.inclusion hsubs) hPs
    have h2 : SameNaturalDiagram K E D (σ + χ) (hjoint hGc)
        (Ps.joint (fun x : ↥(G (X i)) => supportTermOf E x.1))
        (P'.joint (fun x : ↥(G (X i)) => supportTermOf E x.1)) :=
      sameNaturalDiagram_of_sameProfile_noEvent hρinf (hjoint hGc) Ps P'
        (paramSupport_mono E (hGsub (X i))) (paramSupport_nonempty E _) hprof hNE
        (hP'ne.mono (Set.subset_univ _)) _ (fun x => termSupport_subset_paramSupport E x.2)
    have h3 : P'.Solves E D (σ + χ) (hjoint hGc)
        (Subtype.val : ↥(G (X i)) → (E.obj I).carrier) (q hGc Subtype.val) :=
      (sameNaturalDiagram_symm E D h2).trans hρinf h1
    exact hbadfail P'
      (hrestr P' hGc (hbadcard P') Subtype.val (Set.inclusion hbadsub) h3)
  -- but a support position is newly hit only once, and a pair newly separated only once
  choose ev hev using fun i => Ps.exists_event_of_not_noEvent (hevent i)
  have hlater : ∀ i j, i < j → ev i ≠ ev j := by
    intro i j hij heq
    have hj := hev j
    rw [← heq] at hj
    exact (hev i).not_later (paramSupport_mono E (step_subset_stageSet G hij)) hj
  have hinj : Function.Injective ev := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hlater i j hlt hij
    · exact hlater j i hlt hij.symm
  have hle : Order.succ σ ≤ σ :=
    hΘ.symm.le.trans ((mk_le_of_injective hinj).trans (mk_eventCode_le hσinf hσ))
  exact absurd hle (not_le.mpr (Order.lt_succ σ))

end Obstruction

end
end AEC
