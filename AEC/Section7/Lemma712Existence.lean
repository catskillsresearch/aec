module

public import AEC.Section7.Lemma711Successor
public import AEC.Section7.ClosureLevel

/-!
# Lemma 7.12 (1): existence of a tied witnessing chain (split, cycle 85)

The paper builds the chain `(M_i)_{i ≤ δ}` inside one ambient containing `L`: at a successor,
Theorem 7.9 gives an all-dominated realization over `M_i + b_i` and its primeness clause embeds it
into the ambient over the tuple; at limits, unions. Separately, finite domination (Lemma 7.11,
fed by product independence) makes each actual `b_i` free over `M_i` from `A`.

Accordingly `TiedListPreChain L` is `TiedListWitnessingChain L` without the `free` field; the
construction is `infra_712_prechain_statement` (open) and the freeness is
`infra_712_free_marks_statement` (open). `infra_712_existence_at_of_parts` (proved) assembles
clause (1) of `lemma_7_12` at every level satisfying both sets of level hypotheses.
-/

@[expose] public section

namespace AEC
noncomputable section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- A tied list witnessing chain without its freeness field (Definition 7.10 minus
`tp(bᵢ/Mᵢ) = tp(bᵢ/A)^fr`). -/
structure TiedListPreChain {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} (L : TupleList P.scheme hμ A) [LinearOrder L.δ] where
  stage : WithTop L.δ → P.scheme.Object μ hμ
  into : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hμ A)
    (P.scheme.asSystem hμ (stage j))
  into_arrow : ∀ j, P.scheme.permitted (X := A) (Y := stage j) (into j)
  step : ∀ {i j : WithTop L.δ}, i ≤ j →
    SystemArrow K oneVertexShape (P.scheme.asSystem hμ (stage i)) (P.scheme.asSystem hμ (stage j))
  step_arrow : ∀ {i j : WithTop L.δ} (h : i ≤ j),
    P.scheme.permitted (X := stage i) (Y := stage j) (step h)
  step_comp : ∀ {i j k : WithTop L.δ} (hij : i ≤ j) (hjk : j ≤ k) (v : oneVertexShape.Vertex),
    ((step hjk).onVertex v).comp ((step hij).onVertex v) = (step (hij.trans hjk)).onVertex v
  into_step : ∀ {i j : WithTop L.δ} (h : i ≤ j) (v : oneVertexShape.Vertex),
    ((step h).onVertex v).comp ((into i).onVertex v) = (into j).onVertex v
  first : ∀ i, (∀ k, i ≤ k) → ∀ v, Function.Bijective ((into i).onVertex v)
  continuous : ∀ j, (∀ i, ¬ i ⋖ j) → (∃ i, i < j) →
    ∀ v (x : ((P.scheme.asSystem hμ (stage j)).obj v).carrier),
      ∃ i, ∃ h : i < j, ∃ y, (step h.le).onVertex v y = x
  top : P.scheme.Object μ hμ
  toTop : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (stage ⊤)) (P.scheme.asSystem hμ top)
  toTop_arrow : P.scheme.permitted (X := stage ⊤) (Y := top) toTop
  listToTop : SystemArrow K oneVertexShape (P.scheme.asSystem hμ L.host) (P.scheme.asSystem hμ top)
  listToTop_arrow : P.scheme.permitted (X := L.host) (Y := top) listToTop
  comm_A : ∀ v, (toTop.onVertex v).comp ((into ⊤).onVertex v) =
    (listToTop.onVertex v).comp (L.incl.onVertex v)
  mark : ∀ (i : L.δ) (j : WithTop L.δ), (i : WithTop L.δ) < j →
    L.indexAt i → Occurrence K oneVertexShape (P.scheme.asSystem hμ (stage j))
  mark_step : ∀ (i : L.δ) {j k : WithTop L.δ} (hj : (i : WithTop L.δ) < j) (hjk : j ≤ k)
    (a : L.indexAt i), (step hjk).mapOcc (mark i j hj a) = mark i k (lt_of_lt_of_le hj hjk) a
  mark_spec : ∀ (i : L.δ) (a : L.indexAt i),
    toTop.mapOcc (mark i ⊤ (WithTop.coe_lt_top i) a) = listToTop.mapOcc (L.val i a)

namespace TiedListPreChain

variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
  {A : P.scheme.Object μ hμ} {L : TupleList P.scheme hμ A} [LinearOrder L.δ]

/-- All-dominated increments (Definition 7.10). -/
def AllDominatedIncrement (C : TiedListPreChain L) : Prop :=
  ∀ (i : L.δ) (j : WithTop L.δ) (h : (i : WithTop L.δ) ⋖ j),
    AllDominated (C.step h.le) (C.step_arrow h.le) (L.indexAt i) (C.mark i j h.lt)

/-- The freeness field of Definition 7.10 at `i`: `tp(bᵢ/Mᵢ) = tp(bᵢ/A)^fr_{Mᵢ}` (tied). -/
def FreeAt (C : TiedListPreChain L) (i : L.δ) : Prop :=
  IsTiedFree (C.into (i : WithTop L.δ))
    ((asTuple (C.step (le_top : (i : WithTop L.δ) ≤ ⊤)) (C.step_arrow _)
        (C.mark i ⊤ (WithTop.coe_lt_top i))).restrict (C.into (i : WithTop L.δ)) (C.into_arrow _))
    (asTuple (C.step (le_top : (i : WithTop L.δ) ≤ ⊤)) (C.step_arrow _)
      (C.mark i ⊤ (WithTop.coe_lt_top i)))
    (Equiv.refl _)

/-- A pre-chain whose marks are free is a tied witnessing chain. -/
def toChain (C : TiedListPreChain L) (hfree : ∀ i, C.FreeAt i) : TiedListWitnessingChain L where
  stage := C.stage
  into := C.into
  into_arrow := C.into_arrow
  step := C.step
  step_arrow := C.step_arrow
  step_comp := C.step_comp
  into_step := C.into_step
  first := C.first
  continuous := C.continuous
  top := C.top
  toTop := C.toTop
  toTop_arrow := C.toTop_arrow
  listToTop := C.listToTop
  listToTop_arrow := C.listToTop_arrow
  comm_A := C.comm_A
  mark := C.mark
  mark_step := C.mark_step
  mark_spec := C.mark_spec
  free := hfree

theorem toChain_allDominated (C : TiedListPreChain L) (hfree : ∀ i, C.FreeAt i)
    (h : C.AllDominatedIncrement) : (C.toChain hfree).AllDominatedIncrement := h

end TiedListPreChain

/-- Clause (1) of Lemma 7.12 over a fixed `A` at level `μ`. -/
def infra_712_existence_at (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (A : P.scheme.Object μ hμ) : Prop :=
  ∀ (L : TupleList P.scheme hμ A) [LinearOrder L.δ] [WellFoundedLT L.δ],
    #L.δ ≤ μ → ProductIndependentTied L →
    ∃ C : TiedListWitnessingChain L, C.AllDominatedIncrement

/-- **7.12(1), the chain construction (statement; open tip `infra_712_prechain`).** At a
Theorem 7.9 level (`infra_78_closedTail P ∩ infra_615_closed P`, the tail on which 7.9's
existence clause is proved), every well-ordered list of length `≤ μ` has an all-dominated
increment pre-chain: successors by Theorem 7.9 (realization over `Mᵢ + bᵢ`, embedded over the
tuple into the ambient by its primeness clause), limits by directed unions inside the ambient. -/
def infra_712_prechain_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_78_closedTail P →
    μ ∈ infra_615_closed P →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ], #L.δ ≤ μ →
      ∃ C : TiedListPreChain L, C.AllDominatedIncrement

/-- **7.12(1), freeness of the marks (statement; open tip `infra_712_free_marks`).** At a Lemma
7.11 level, in an all-dominated-increment pre-chain of a product-independent list, every actual
`bᵢ` is free over `Mᵢ` from `A` (paper: Lemma 7.11 applied to the chain below `i`, whose
products with the earlier marks are the original ones). -/
def infra_712_free_marks_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ], ProductIndependentTied L →
      ∀ C : TiedListPreChain L, C.AllDominatedIncrement → ∀ i, C.FreeAt i

/-- **7.12(1), one freeness step (statement; open tip `infra_712_free_step`).** If the marks
below `i` are free, so is `bᵢ` (paper: Lemma 7.11 for the chain truncated at `i`, with
`x = bᵢ` over `Mᵢ`; its product hypotheses come from product independence of `L`). -/
def infra_712_free_step_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ], ProductIndependentTied L →
      ∀ C : TiedListPreChain L, C.AllDominatedIncrement →
        ∀ i, (∀ k, k < i → C.FreeAt k) → C.FreeAt i

/-- **Freeness of all marks by well-founded induction (proved glue).** -/
theorem infra_712_free_marks_of_step (P : SingleModelData K)
    (h : infra_712_free_step_statement P) : infra_712_free_marks_statement P := by
  intro μ hμ h0 h1 hw1 hw2 A L _ _ hind C hC i
  induction i using WellFoundedLT.induction with
  | _ i ih => exact h hμ h0 h1 hw1 hw2 A L hind C hC i ih

/-- **Lemma 7.12 (1) from its parts (proved glue).** -/
theorem infra_712_existence_at_of_parts (P : SingleModelData K)
    (h1 : infra_712_prechain_statement P) (h2 : infra_712_free_marks_statement P)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible) (ht : μ ∈ infra_78_closedTail P)
    (hc : μ ∈ infra_615_closed P) (h0 : μ ∈ recursionClosedLevels P ℵ₀)
    (h1' : Order.succ ℵ₀ ≤ μ) (hw1 : μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀))
    (hw2 : Order.succ (infra_75_wide P ℵ₀) ≤ μ) (A : P.scheme.Object μ hμ) :
    infra_712_existence_at P hμ A := by
  intro L _ _ hδ hind
  obtain ⟨C, hC⟩ := h1 hμ ht hc A L hδ
  have hfree := h2 hμ h0 h1' hw1 hw2 A L hind C hC
  exact ⟨C.toChain hfree, C.toChain_allDominated hfree hC⟩

end
end AEC
