module

public import AEC.Section4.NaturalDiagram
public import Mathlib.Order.UpperLower.CompleteLattice
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.UpperLower.Principal
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-! ### Amalgamation of linear orders over a common suborder

Definition 4.4 remarks that linear orders amalgamate over a common suborder: for each cut of
the suborder, place the remaining portions of the two orders in that cut while preserving
each portion's order. The amalgam below is the lexicographic order on pairs
`(cut of X, position inside the cut)`, where the points of `X` sit at the top of their cut
and the remaining points of `I` precede the remaining points of `J`. -/

namespace OrderAmalgam

variable {X A I J : Type u} [LinearOrder X] [LinearOrder A] [LinearOrder I] [LinearOrder J]

/-- The cut of `X` strictly below a point `a` of an extension `e : X ↪o A`. -/
def cut (e : X ↪o A) (a : A) : LowerSet X where
  carrier := {x | e x < a}
  lower' := fun _ _ hyx hx => lt_of_le_of_lt (e.monotone hyx) hx

theorem mem_cut {e : X ↪o A} {a : A} {x : X} : x ∈ cut e a ↔ e x < a :=
  Iff.rfl

theorem cut_mono (e : X ↪o A) : Monotone (cut e) :=
  fun _ _ hab _ hx => lt_of_lt_of_le (mem_cut.mp hx) hab

/-- The cut below a point of `X` does not depend on the extension. -/
theorem cut_apply (e : X ↪o A) (x : X) : cut e (e x) = LowerSet.Iio x :=
  SetLike.ext fun y => by simp [mem_cut]

open Classical in
/-- Place a point of an extension `A` of `X` in the amalgam: points of `X` go to the top of
their cut, the other points keep their tag `ι a` inside the cut. -/
noncomputable def place (e : X ↪o A) (ι : A → I ⊕ₗ J) (a : A) :
    LowerSet X ×ₗ WithTop (I ⊕ₗ J) :=
  toLex (cut e a, if a ∈ Set.range e then ⊤ else (ι a : WithTop (I ⊕ₗ J)))

theorem place_apply (e : X ↪o A) (ι : A → I ⊕ₗ J) (x : X) :
    place e ι (e x) = toLex (LowerSet.Iio x, ⊤) := by
  simp [place, cut_apply]

theorem place_strictMono (e : X ↪o A) (ι : A → I ⊕ₗ J) (hι : StrictMono ι) :
    StrictMono (place e ι) := by
  intro a b hab
  rw [place, place, Prod.Lex.toLex_lt_toLex]
  rcases (cut_mono e hab.le).lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr ⟨h, ?_⟩
    have ha : a ∉ Set.range e := by
      rintro ⟨x, rfl⟩
      have hx : x ∈ cut e b := mem_cut.mpr hab
      rw [← h] at hx
      exact lt_irrefl _ (mem_cut.mp hx)
    dsimp only
    simp only [ha, ↓reduceIte]
    by_cases hb : b ∈ Set.range e
    · simp only [hb, ↓reduceIte]
      exact WithTop.coe_lt_top _
    · simp only [hb, ↓reduceIte]
      exact WithTop.coe_lt_coe.mpr (hι hab)

end OrderAmalgam

/-- **Amalgamation of linear orders.** Two linear orders extending a common suborder embed
into one linear order by maps that agree on the suborder. -/
theorem exists_linearOrder_amalgam {X I J : Type u} [LinearOrder X] [LinearOrder I]
    [LinearOrder J] (e : X ↪o I) (f : X ↪o J) :
    ∃ (L : Type u) (_ : LinearOrder L) (F : I ↪o L) (H : J ↪o L), ∀ x, F (e x) = H (f x) := by
  refine ⟨LowerSet X ×ₗ WithTop (I ⊕ₗ J), inferInstance,
    OrderEmbedding.ofStrictMono (OrderAmalgam.place e Sum.inlₗ)
      (OrderAmalgam.place_strictMono e _ fun _ _ h => Sum.Lex.inl_lt_inl_iff.mpr h),
    OrderEmbedding.ofStrictMono (OrderAmalgam.place f Sum.inrₗ)
      (OrderAmalgam.place_strictMono f _ fun _ _ h => Sum.Lex.inr_lt_inr_iff.mpr h),
    fun x => ?_⟩
  simp only [OrderEmbedding.coe_ofStrictMono]
  rw [OrderAmalgam.place_apply, OrderAmalgam.place_apply]

/-! ### Natural diagrams are invariant under order extension -/

section Along

variable {K : AbstractElementaryClass.{u}} {E : OrderPresentation K} {D : StableDiagram K}
  {X X' I I' : Type u} [LinearOrder X] [LinearOrder X'] [LinearOrder I] [LinearOrder I']
  [Nonempty X] [Nonempty X'] [Nonempty I] [Nonempty I']
  {α : Type u} {σ : Cardinal.{u}} {hσ : #α ≤ σ}
  {t : α → SupportTerm E.lab E.arity X} {s : α → SupportTerm E.lab E.arity X'}

/-- Natural diagrams that agree after extending the index orders already agree before:
compose the witnessing embeddings with the extensions. -/
theorem sameNaturalDiagram_of_along (e : X ↪o I) (e' : X' ↪o I')
    (h : SameNaturalDiagram K E D σ hσ
      (fun a => SupportTerm.along e (t a)) (fun a => SupportTerm.along e' (s a))) :
    SameNaturalDiagram K E D σ hσ t s := by
  obtain ⟨J, linJ, nonJ, f, g, hcard, hM, hsame⟩ := h
  exact ⟨J, linJ, nonJ, e.trans f, e'.trans g, hcard, hM, hsame⟩

/-- Natural diagrams that agree keep agreeing after the index orders are extended: the
extensions amalgamate with the witnessing order over the original index orders, and strong
order maps preserve diagrams. This is the "independent of the extension used" clause of
Definition 4.4; like every operational clause of `StableDiagram`, it needs `σ` infinite. -/
theorem SameNaturalDiagram.along (hσinf : aleph0 ≤ σ)
    (h : SameNaturalDiagram K E D σ hσ t s) (e : X ↪o I) (e' : X' ↪o I') :
    SameNaturalDiagram K E D σ hσ
      (fun a => SupportTerm.along e (t a)) (fun a => SupportTerm.along e' (s a)) := by
  obtain ⟨J, linJ, nonJ, f, g, hcard, hM, hsame⟩ := h
  obtain ⟨L₁, linL₁, F₁, h₁, hF₁⟩ := exists_linearOrder_amalgam e f
  obtain ⟨L₂, linL₂, G, h₂, hG⟩ := exists_linearOrder_amalgam e' (g.trans h₁)
  haveI : Nonempty L₂ := ⟨h₂ (h₁ (Classical.arbitrary J))⟩
  let H : J ↪o L₂ := h₁.trans h₂
  have hM' : K.Mem (E.obj L₂) := orderPresentation_obj_mem E L₂
  have hcard' : D.t σ ≤ Model.card (E.obj L₂) :=
    hcard.trans (mk_le_of_injective (E.map H).injective)
  have hx : ∀ a, E.map H (E.realize (SupportTerm.along f (t a))) =
      E.realize (SupportTerm.along (F₁.trans h₂) (SupportTerm.along e (t a))) := by
    intro a
    rw [E.realize_along]
    congr 1
    refine SupportTerm.ext_of_label_eq rfl fun k => ?_
    exact (congrArg h₂ (hF₁ ((t a).pos k))).symm
  have hy : ∀ a, E.map H (E.realize (SupportTerm.along g (s a))) =
      E.realize (SupportTerm.along G (SupportTerm.along e' (s a))) := by
    intro a
    rw [E.realize_along]
    congr 1
    refine SupportTerm.ext_of_label_eq rfl fun k => ?_
    exact (hG ((s a).pos k)).symm
  refine ⟨L₂, linL₂, inferInstance, F₁.trans h₂, G, hcard', hM', ?_⟩
  have h1 := D.of_strong hσ hM hM' hcard hcard' _ _ (E.map H) hσinf (E.map_strong H) hx
  have h2 := D.of_strong hσ hM hM' hcard hcard' _ _ (E.map H) hσinf (E.map_strong H) hy
  exact D.trans hσ hM' hM hM' hcard' hcard hcard' _ _ _
    (D.symm hσ hM hM' hcard hcard' _ _ h1)
    (D.trans hσ hM hM hM' hcard hcard hcard' _ _ _ hsame h2)

/-- For lists of length at most an infinite `σ`, the natural diagram comparison is unchanged
by extending the index orders. -/
theorem sameNaturalDiagram_along_iff (hσinf : aleph0 ≤ σ) (e : X ↪o I) (e' : X' ↪o I') :
    SameNaturalDiagram K E D σ hσ
        (fun a => SupportTerm.along e (t a)) (fun a => SupportTerm.along e' (s a)) ↔
      SameNaturalDiagram K E D σ hσ t s :=
  ⟨sameNaturalDiagram_of_along e e', fun h => h.along hσinf e e'⟩

end Along

/-! ### Supports and restriction of terms -/

section Support

variable {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I]

/-- The finite set of positions used by a term. -/
def termSupport (t : SupportTerm lab arity I) : Set I :=
  Set.range t.pos

/-- The set of positions used by a list of terms. -/
def tupleSupport {α : Type u} (t : α → SupportTerm lab arity I) : Set I :=
  ⋃ a, termSupport (t a)

theorem termSupport_subset_tupleSupport {α : Type u} (t : α → SupportTerm lab arity I) (a : α) :
    termSupport (t a) ⊆ tupleSupport t :=
  Set.subset_iUnion (fun a => termSupport (t a)) a

theorem mk_termSupport_lt_aleph0 (t : SupportTerm lab arity I) : #(termSupport t) < aleph0 :=
  (Set.finite_range t.pos).lt_aleph0

/-- A list of at most `σ` terms uses at most `max ℵ₀ σ` positions. -/
theorem mk_tupleSupport_le {α : Type u} {σ : Cardinal.{u}} (hσ : #α ≤ σ)
    (t : α → SupportTerm lab arity I) : #(tupleSupport t) ≤ max aleph0 σ := by
  have hsup : (⨆ a, #(termSupport (t a))) ≤ aleph0 :=
    ciSup_le' fun a => (mk_termSupport_lt_aleph0 (t a)).le
  calc #(tupleSupport t) ≤ #α * ⨆ a, #(termSupport (t a)) := mk_iUnion_le _
    _ ≤ σ * aleph0 := mul_le_mul' hσ hsup
    _ ≤ max (max σ aleph0) aleph0 := mul_le_max _ _
    _ = max aleph0 σ := by rw [max_assoc, max_self, max_comm]

/-- Read a term over the induced suborder on a set `X` containing all its positions. -/
def SupportTerm.restrict (t : SupportTerm lab arity I) (X : Set I) (h : termSupport t ⊆ X) :
    SupportTerm lab arity ↥X where
  label := t.label
  pos := fun k => ⟨t.pos k, h (Set.mem_range_self k)⟩
  increasing := fun _ _ hab => t.increasing hab

@[simp]
theorem SupportTerm.restrict_label (t : SupportTerm lab arity I) (X : Set I)
    (h : termSupport t ⊆ X) : (t.restrict X h).label = t.label :=
  rfl

/-- Pushing a restricted term back along the inclusion `X ↪o I` recovers the term. -/
@[simp]
theorem SupportTerm.along_restrict (t : SupportTerm lab arity I) (X : Set I)
    (h : termSupport t ⊆ X) :
    SupportTerm.along (OrderEmbedding.subtype (· ∈ X)) (t.restrict X h) = t :=
  rfl

end Support

/-! ### Uniform testing on the support -/

section Testing

variable {K : AbstractElementaryClass.{u}} (E : OrderPresentation K) (D : StableDiagram K)
  {I : Type u} [LinearOrder I] [Nonempty I] {α : Type u} {σ : Cardinal.{u}}

/-- For lists of length at most an infinite `σ`, the natural diagram comparison of two
placements over `I` can be tested on any induced suborder containing their positions. -/
theorem sameNaturalDiagram_restrict_iff (hσinf : aleph0 ≤ σ) (hσ : #α ≤ σ)
    (t s : α → SupportTerm E.lab E.arity I) (X : Set I) [Nonempty ↥X]
    (ht : ∀ a, termSupport (t a) ⊆ X) (hs : ∀ a, termSupport (s a) ⊆ X) :
    SameNaturalDiagram K E D σ hσ
        (fun a => (t a).restrict X (ht a)) (fun a => (s a).restrict X (hs a)) ↔
      SameNaturalDiagram K E D σ hσ t s :=
  (sameNaturalDiagram_along_iff (t := fun a => (t a).restrict X (ht a))
    (s := fun a => (s a).restrict X (hs a)) hσinf
    (OrderEmbedding.subtype (· ∈ X)) (OrderEmbedding.subtype (· ∈ X))).symm

/-- The joint support of two placements, with one extra point so that it is nonempty. -/
noncomputable def testingSet (t s : α → SupportTerm E.lab E.arity I) : Set I :=
  tupleSupport t ∪ tupleSupport s ∪ {Classical.arbitrary I}

theorem testingSet_nonempty (t s : α → SupportTerm E.lab E.arity I) :
    (testingSet E t s).Nonempty :=
  ⟨Classical.arbitrary I, Or.inr rfl⟩

theorem termSupport_subset_testingSet_left (t s : α → SupportTerm E.lab E.arity I) (a : α) :
    termSupport (t a) ⊆ testingSet E t s :=
  fun _ hx => Or.inl (Or.inl (termSupport_subset_tupleSupport t a hx))

theorem termSupport_subset_testingSet_right (t s : α → SupportTerm E.lab E.arity I) (a : α) :
    termSupport (s a) ⊆ testingSet E t s :=
  fun _ hx => Or.inl (Or.inr (termSupport_subset_tupleSupport s a hx))

/-- The testing set of two placements of length at most `σ` has size at most `max ℵ₀ σ`,
independently of `|I|`. -/
theorem mk_testingSet_le (hσ : #α ≤ σ) (t s : α → SupportTerm E.lab E.arity I) :
    #(testingSet E t s) ≤ max aleph0 σ := by
  have hinf : aleph0 ≤ max aleph0 σ := le_max_left _ _
  refine (mk_union_le _ _).trans (add_le_of_le hinf ((mk_union_le _ _).trans
    (add_le_of_le hinf (mk_tupleSupport_le hσ t) (mk_tupleSupport_le hσ s))) ?_)
  rw [mk_singleton]
  exact one_le_aleph0.trans hinf

/-- **Uniform testing on the support** (the content of Proposition 4.8). Two placements of
length at most an infinite `σ` with different natural diagrams over `I` already have
different natural diagrams over their testing set, which has size at most `max ℵ₀ σ`. -/
theorem not_sameNaturalDiagram_restrict_testingSet (hσinf : aleph0 ≤ σ) (hσ : #α ≤ σ)
    (t s : α → SupportTerm E.lab E.arity I)
    (h : ¬ SameNaturalDiagram K E D σ hσ t s) :
    haveI : Nonempty ↥(testingSet E t s) := (testingSet_nonempty E t s).to_subtype
    ¬ SameNaturalDiagram K E D σ hσ
      (fun a => (t a).restrict (testingSet E t s) (termSupport_subset_testingSet_left E t s a))
      (fun a => (s a).restrict (testingSet E t s) (termSupport_subset_testingSet_right E t s a)) := by
  haveI : Nonempty ↥(testingSet E t s) := (testingSet_nonempty E t s).to_subtype
  exact fun h' => h ((sameNaturalDiagram_restrict_iff E D hσinf hσ t s (testingSet E t s)
    (termSupport_subset_testingSet_left E t s) (termSupport_subset_testingSet_right E t s)).mp h')

end Testing

end
end AEC
