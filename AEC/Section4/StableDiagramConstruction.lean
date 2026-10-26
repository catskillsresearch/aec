module

public import AEC.Section4.StableDiagram
public import AEC.Section3.Results
public import AEC.Section2.Results
public import AEC.Section2.FiniteHull
public import AEC.Section2.DirectedLimit
public import AEC.Section1.UnboundedCategoricity
public import AEC.Section1.ArbitrarilyLarge
public import AEC.Section3.Reversal
public import AEC.Section3.OrbitName
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Basic
public import Mathlib.Order.InitialSeg

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-! ### From unbounded categoricity to EM presentations -/

theorem arbitrarilyLarge_of_categoricalUnbounded (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] : ArbitrarilyLarge K where
  large κ := by
    obtain ⟨μ, hκμ, hcat⟩ := CategoricalUnbounded.unbounded (K := K) κ
    obtain ⟨M, hM, hc⟩ := hcat.exists_model
    exact ⟨M, hM, hκμ.trans_eq hc.symm⟩

theorem exists_orderPresentation_of_categoricalUnbounded (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] :
    ∃ E : OrderPresentation K,
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Mem (E.obj I)) ∧
      ∀ κ : Cardinal.{u}, aleph0 ≤ κ → ls K ≤ κ →
        ∃ M : Model K.τ, K.Mem M ∧ Model.card M = κ := by
  have : ArbitrarilyLarge K := arbitrarilyLarge_of_categoricalUnbounded K
  exact theorem_2_6 K

/-! ### Exact-size strong hulls -/

/-- A strong submodel of exact cardinality `κ` containing a given set of size at most `κ`. -/
theorem exists_strong_hull_exact_card (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    (hls : ls K ≤ κ) (hκinf : aleph0 ≤ κ)
    (N : Model K.τ) (hN : K.Mem N) (hcard : κ ≤ Model.card N)
    (A : Set N.carrier) (hA : #A ≤ κ) :
    ∃ (M : Model K.τ) (f : Language.Embedding K.τ M.carrier N.carrier),
      K.Mem M ∧ K.Strong f ∧ Model.card M = κ ∧ ∀ a ∈ A, ∃ x, f x = a := by
  classical
  have hcard' : κ ≤ #N.carrier := by simpa [Model.card] using hcard
  obtain ⟨e⟩ := (Cardinal.le_def (Below κ) N.carrier).mp (by
    simpa [Below, mk_ord_toType] using hcard')
  let B : Set N.carrier := Set.range e ∪ A
  have hB_le : #B ≤ κ := by
    have hle := mk_union_le (Set.range e) A
    have h1 : #(Set.range e) ≤ κ :=
      (mk_range_le (f := ⇑e)).trans_eq (by simp [Below, mk_ord_toType])
    have hsum := add_le_add h1 hA
    rw [add_eq_self hκinf] at hsum
    exact hle.trans hsum
  have hB_ge : κ ≤ #B := by
    have hr : #(Set.range e) = κ :=
      (mk_range_eq (⇑e) e.injective).trans (by simp [Below, mk_ord_toType])
    exact hr.symm.trans_le (mk_le_mk_of_subset Set.subset_union_left)
  have hB_eq : #B = κ := le_antisymm hB_le hB_ge
  obtain ⟨M, f, hM, hf, hcov, hcardM⟩ := (isLSBound_ls K).2.2 N hN B
  have hcard_le : Model.card M ≤ κ := by
    have h := hcardM.trans (add_le_add (le_of_eq hB_eq) hls)
    rwa [add_eq_self hκinf] at h
  have hcard_ge : κ ≤ Model.card M := by
    have hr : #(Set.range e) = κ :=
      (mk_range_eq (⇑e) e.injective).trans (by simp [Below, mk_ord_toType])
    have hsub : Set.range e ⊆ Set.range f := by
      intro x hx
      obtain ⟨n, hn⟩ := hcov x (Or.inl hx)
      exact ⟨n, hn⟩
    exact hr.symm.trans_le ((mk_le_mk_of_subset hsub).trans mk_range_le)
  refine ⟨M, f, hM, hf, le_antisymm hcard_le hcard_ge, ?_⟩
  intro a ha
  exact hcov a (Or.inr ha)

/-- Exact-size hull containing the range of a tuple of length at most `κ`. -/
theorem exists_strong_hull_of_tuple (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    (hls : ls K ≤ κ) (hκinf : aleph0 ≤ κ)
    (N : Model K.τ) (hN : K.Mem N) (hcard : κ ≤ Model.card N)
    {α : Type u} (a : α → N.carrier) (hα : #α ≤ κ) :
    ∃ (M : Model K.τ) (f : Language.Embedding K.τ M.carrier N.carrier),
      K.Mem M ∧ K.Strong f ∧ Model.card M = κ ∧ ∀ i, ∃ x, f x = a i := by
  let A : Set N.carrier := Set.range a
  have hA : #A ≤ κ := (mk_range_le (f := a)).trans hα
  obtain ⟨M, f, hM, hf, hc, hcov⟩ :=
    exists_strong_hull_exact_card K κ hls hκinf N hN hcard A hA
  exact ⟨M, f, hM, hf, hc, fun i => hcov (a i) ⟨i, rfl⟩⟩

/-! ### Strong-map classes between models of equal categoricity size -/

def SameStrongClass (K : AbstractElementaryClass.{u}) {α : Type u} {M N : Model K.τ}
    (xs : α → M.carrier) (ys : α → N.carrier) : Prop :=
  ∃ e : Language.Embedding K.τ M.carrier N.carrier,
    K.Strong e ∧ ∀ i, e (xs i) = ys i

theorem sameStrongClass_refl (K : AbstractElementaryClass.{u}) {α : Type u} {M : Model K.τ}
    (hM : K.Mem M) (xs : α → M.carrier) : SameStrongClass K xs xs :=
  ⟨Language.Embedding.refl K.τ M.carrier, K.strong_refl M hM, fun _ => rfl⟩

theorem sameStrongClass_of_equiv (K : AbstractElementaryClass.{u}) {α : Type u}
    {M N : Model K.τ} (e : M.carrier ≃[K.τ] N.carrier) (hM : K.Mem M)
    (xs : α → M.carrier) :
    SameStrongClass K xs (fun i => e (xs i)) :=
  ⟨e.toEmbedding, strong_of_equiv K e hM, fun _ => rfl⟩

/-- Symmetry of strong-map classes at a categoricity cardinal with reversal. -/
theorem sameStrongClass_symm (K : AbstractElementaryClass.{u}) (κ θ : Cardinal.{u})
    (hcat : Categorical K κ) (hrev : ReversalProperty K θ κ)
    {α : Type u} {M N : Model K.τ}
    (hM : K.Mem M) (hN : K.Mem N)
    (hcM : Model.card M = κ) (hcN : Model.card N = κ)
    (hα : #α ≤ θ)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (h : SameStrongClass K xs ys) :
    SameStrongClass K ys xs := by
  obtain ⟨e, he, het⟩ := h
  obtain ⟨ι⟩ := hcat.unique_model M N hM hN hcM hcN
  let g : Language.Embedding K.τ N.carrier N.carrier := e.comp ι.symm.toEmbedding
  have hg : K.Strong g :=
    K.strong_trans ι.symm.toEmbedding e (strong_of_equiv K ι.symm hN) he
  have hg_on_image : ∀ i, g (ι (xs i)) = ys i := by
    intro i
    change e (ι.symm (ι (xs i))) = ys i
    simp [het i]
  obtain ⟨r, hr, hr_tup⟩ := hrev N g (fun i => ι (xs i)) hN hcN hg hα
  refine ⟨ι.symm.toEmbedding.comp r,
    K.strong_trans r ι.symm.toEmbedding hr (strong_of_equiv K ι.symm hN), ?_⟩
  intro i
  have hry : r (ys i) = ι (xs i) := by
    simpa [hg_on_image i] using hr_tup i
  change ι.symm (r (ys i)) = xs i
  simp [hry]

theorem sameStrongClass_trans (K : AbstractElementaryClass.{u}) {α : Type u}
    {M N P : Model K.τ}
    (xs : α → M.carrier) (ys : α → N.carrier) (zs : α → P.carrier)
    (h₁ : SameStrongClass K xs ys) (h₂ : SameStrongClass K ys zs) :
    SameStrongClass K xs zs := by
  obtain ⟨e₁, he₁, h₁t⟩ := h₁
  obtain ⟨e₂, he₂, h₂t⟩ := h₂
  refine ⟨e₂.comp e₁, K.strong_trans e₁ e₂ he₁ he₂, ?_⟩
  intro i
  simp [Language.Embedding.comp_apply, h₁t i, h₂t i]

/-- Equality of ambient tuples is preserved by a strong-class witness. -/
theorem sameStrongClass_preserves_eq (K : AbstractElementaryClass.{u}) {α : Type u}
    {M N : Model K.τ} (xs : α → M.carrier) (ys : α → N.carrier)
    (h : SameStrongClass K xs ys) (i j : α) : xs i = xs j ↔ ys i = ys j := by
  obtain ⟨e, _, het⟩ := h
  constructor
  · intro hxy
    rw [← het i, ← het j, hxy]
  · intro hxy
    exact e.injective (by rw [het i, het j, hxy])

/-! ### Canonical diagram equality via a fixed categoricity size -/

/-- Diagram equality witnessed by matching strong `κ`-hulls (Lemma 4.1). -/
def SameDiagramAt (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    {α : Type u} {M N : Model K.τ}
    (xs : α → M.carrier) (ys : α → N.carrier) : Prop :=
  ∃ (M₀ N₀ : Model K.τ)
    (f : Language.Embedding K.τ M₀.carrier M.carrier)
    (g : Language.Embedding K.τ N₀.carrier N.carrier)
    (x₀ : α → M₀.carrier) (y₀ : α → N₀.carrier),
    K.Mem M₀ ∧ K.Mem N₀ ∧ K.Strong f ∧ K.Strong g ∧
    Model.card M₀ = κ ∧ Model.card N₀ = κ ∧
    (∀ i, f (x₀ i) = xs i) ∧ (∀ i, g (y₀ i) = ys i) ∧
    SameStrongClass K x₀ y₀

theorem sameDiagramAt_refl (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    (hls : ls K ≤ κ) (hκinf : aleph0 ≤ κ)
    {α : Type u} {M : Model K.τ} (hM : K.Mem M) (hcard : κ ≤ Model.card M)
    (xs : α → M.carrier) (hα : #α ≤ κ) :
    SameDiagramAt K κ xs xs := by
  obtain ⟨M₀, f, hM₀, hf, hc, hhit⟩ :=
    exists_strong_hull_of_tuple K κ hls hκinf M hM hcard xs hα
  classical
  let x₀ : α → M₀.carrier := fun i => Classical.choose (hhit i)
  have hx₀ : ∀ i, f (x₀ i) = xs i := fun i => Classical.choose_spec (hhit i)
  exact ⟨M₀, M₀, f, f, x₀, x₀, hM₀, hM₀, hf, hf, hc, hc, hx₀, hx₀,
    sameStrongClass_refl K hM₀ x₀⟩

theorem sameDiagramAt_symm (K : AbstractElementaryClass.{u}) (κ θ : Cardinal.{u})
    (hcat : Categorical K κ) (hrev : ReversalProperty K θ κ)
    {α : Type u} {M N : Model K.τ}
    (hα : #α ≤ θ) (xs : α → M.carrier) (ys : α → N.carrier)
    (h : SameDiagramAt K κ xs ys) : SameDiagramAt K κ ys xs := by
  obtain ⟨M₀, N₀, f, g, x₀, y₀, hM₀, hN₀, hf, hg, hcM, hcN, hx, hy, hcls⟩ := h
  exact ⟨N₀, M₀, g, f, y₀, x₀, hN₀, hM₀, hg, hf, hcN, hcM, hy, hx,
    sameStrongClass_symm K κ θ hcat hrev hM₀ hN₀ hcM hcN hα x₀ y₀ hcls⟩

theorem sameDiagramAt_preserves_eq (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    {α : Type u} {M N : Model K.τ} (xs : α → M.carrier) (ys : α → N.carrier)
    (h : SameDiagramAt K κ xs ys) (i j : α) : xs i = xs j ↔ ys i = ys j := by
  obtain ⟨M₀, N₀, f, g, x₀, y₀, _, _, _, _, _, _, hx, hy, hcls⟩ := h
  have h0 := sameStrongClass_preserves_eq K x₀ y₀ hcls i j
  constructor
  · intro heq
    have : x₀ i = x₀ j := f.injective (by rw [hx i, hx j, heq])
    rw [← hy i, ← hy j, ← h0.mp this]
  · intro heq
    have : y₀ i = y₀ j := g.injective (by rw [hy i, hy j, heq])
    rw [← hx i, ← hx j, h0.mpr this]

/-- Strong embeddings preserve `SameDiagramAt` (Lemma 4.1, preservation half). -/
theorem sameDiagramAt_of_strong_image (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    {α : Type u} {M N : Model K.τ}
    (xs : α → M.carrier) (f : Language.Embedding K.τ M.carrier N.carrier)
    (hf : K.Strong f) (h : SameDiagramAt K κ xs xs) :
    SameDiagramAt K κ xs (fun i => f (xs i)) := by
  obtain ⟨M₀, N₀, f₀, g₀, x₀, y₀, hM₀, hN₀, hf₀, hg₀, hcM, hcN, hx, hy, hcls⟩ := h
  refine ⟨M₀, N₀, f₀, f.comp g₀, x₀, y₀, hM₀, hN₀, hf₀,
    K.strong_trans g₀ f hg₀ hf, hcM, hcN, hx, fun i => by
      simp [Language.Embedding.comp_apply, hy i], hcls⟩

/-- Push both sides of a diagram equality along a strong embedding of the ambient of `ys`. -/
theorem sameDiagramAt_comp_right (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    {α : Type u} {M N P : Model K.τ}
    (xs : α → M.carrier) (ys : α → N.carrier)
    (f : Language.Embedding K.τ N.carrier P.carrier) (hf : K.Strong f)
    (h : SameDiagramAt K κ xs ys) :
    SameDiagramAt K κ xs (fun i => f (ys i)) := by
  obtain ⟨M₀, N₀, f₀, g₀, x₀, y₀, hM₀, hN₀, hf₀, hg₀, hcM, hcN, hx, hy, hcls⟩ := h
  refine ⟨M₀, N₀, f₀, f.comp g₀, x₀, y₀, hM₀, hN₀, hf₀,
    K.strong_trans g₀ f hg₀ hf, hcM, hcN, hx, fun i => by
      simp [Language.Embedding.comp_apply, hy i], hcls⟩

/-- Least categoricity cardinal at least `b`. -/
noncomputable def leastCategorical (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (b : Cardinal.{u}) : Cardinal.{u} :=
  sInf {κ : Cardinal.{u} | b ≤ κ ∧ Categorical K κ}

theorem leastCategorical_mem (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (b : Cardinal.{u}) :
    b ≤ leastCategorical K b ∧ Categorical K (leastCategorical K b) := by
  obtain ⟨κ0, hκ0, hcat0⟩ := CategoricalUnbounded.unbounded (K := K) b
  have hne : ({κ : Cardinal.{u} | b ≤ κ ∧ Categorical K κ}).Nonempty :=
    ⟨κ0, hκ0, hcat0⟩
  exact csInf_mem hne

theorem leastCategorical_mono (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    {b c : Cardinal.{u}} (hle : b ≤ c) :
    leastCategorical K b ≤ leastCategorical K c := by
  obtain ⟨hc_le, _⟩ := leastCategorical_mem K c
  have hmem : leastCategorical K c ∈ {κ : Cardinal.{u} | b ≤ κ ∧ Categorical K κ} :=
    ⟨hle.trans hc_le, (leastCategorical_mem K c).2⟩
  exact csInf_le (OrderBot.bddBelow _) hmem

/-- Least reversal threshold for length `σ`, from Theorem 3.11. -/
noncomputable def leastRevThreshold (K : AbstractElementaryClass.{u}) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) : Cardinal.{u} :=
  sInf {b : Cardinal.{u} | IsReversalThreshold K σ b}

theorem leastRevThreshold_mem (K : AbstractElementaryClass.{u}) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) :
    IsReversalThreshold K σ (leastRevThreshold K σ hσ) := by
  obtain ⟨b, hb⟩ := theorem_3_11 K σ hσ
  exact csInf_mem (⟨b, hb⟩ : {b : Cardinal.{u} | IsReversalThreshold K σ b}.Nonempty)

theorem isReversalThreshold_of_le_length (K : AbstractElementaryClass.{u})
    {σ τ b : Cardinal.{u}} (hle : σ ≤ τ) (h : IsReversalThreshold K τ b) :
    IsReversalThreshold K σ b := by
  intro κ hκle hcat
  obtain ⟨hcat', hrev⟩ := h κ hκle hcat
  refine ⟨hcat', ?_⟩
  intro M f ι xs hM hcM hf hι
  exact hrev M f xs hM hcM hf (hι.trans hle)

theorem leastRevThreshold_mono (K : AbstractElementaryClass.{u})
    {σ τ : Cardinal.{u}} (hσ : aleph0 ≤ σ) (hτ : aleph0 ≤ τ) (hle : σ ≤ τ) :
    leastRevThreshold K σ hσ ≤ leastRevThreshold K τ hτ := by
  have hmem : leastRevThreshold K τ hτ ∈
      {b : Cardinal.{u} | IsReversalThreshold K σ b} :=
    isReversalThreshold_of_le_length K hle (leastRevThreshold_mem K τ hτ)
  exact csInf_le (OrderBot.bddBelow _) hmem

/-- Raw lower bound past language, LS, reversal at `σ ⊔ ℵ₀`, and arity. Nondecreasing in `σ`. -/
noncomputable def stableBound (K : AbstractElementaryClass.{u}) (σ : Cardinal.{u}) : Cardinal.{u} :=
  Order.succ (K.τ.card + σ) ⊔ Order.succ (ls K + σ) ⊔ Order.succ σ ⊔ ls K ⊔
    leastRevThreshold K (σ ⊔ aleph0) le_sup_right

theorem stableBound_mono (K : AbstractElementaryClass.{u}) {σ τ : Cardinal.{u}} (hle : σ ≤ τ) :
    stableBound K σ ≤ stableBound K τ := by
  dsimp [stableBound]
  refine sup_le_sup (sup_le_sup (sup_le_sup (sup_le_sup ?_ ?_) ?_) ?_) ?_
  · exact Order.succ_le_succ (add_le_add le_rfl hle)
  · exact Order.succ_le_succ (add_le_add le_rfl hle)
  · exact Order.succ_le_succ hle
  · exact le_rfl
  · exact leastRevThreshold_mono K le_sup_right le_sup_right (sup_le_sup hle le_rfl)

/-- The threshold `t(σ)` of Proposition 4.2: least categoricity cardinal past `stableBound`. -/
noncomputable def stableThreshold (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ : Cardinal.{u}) : Cardinal.{u} :=
  leastCategorical K (stableBound K σ)

theorem stableThreshold_mono (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    {σ τ : Cardinal.{u}} (hle : σ ≤ τ) :
    stableThreshold K σ ≤ stableThreshold K τ :=
  leastCategorical_mono K (stableBound_mono K hle)

theorem stableThreshold_categorical (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ : Cardinal.{u}) : Categorical K (stableThreshold K σ) :=
  (leastCategorical_mem K (stableBound K σ)).2

theorem stableThreshold_above_bound (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ : Cardinal.{u}) : stableBound K σ ≤ stableThreshold K σ :=
  (leastCategorical_mem K (stableBound K σ)).1

theorem stableThreshold_above_tau (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ : Cardinal.{u}) (_hσ : aleph0 ≤ σ) : K.τ.card + σ < stableThreshold K σ := by
  have h := stableThreshold_above_bound K σ
  have hsucc : Order.succ (K.τ.card + σ) ≤ stableBound K σ :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_rfl)))
  exact (Order.lt_succ (K.τ.card + σ)).trans_le (hsucc.trans h)

theorem stableThreshold_ge_ls (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ : Cardinal.{u}) : ls K ≤ stableThreshold K σ := by
  have h := stableThreshold_above_bound K σ
  have : ls K ≤ stableBound K σ :=
    le_sup_of_le_left (le_sup_of_le_right (le_rfl : ls K ≤ ls K))
  exact this.trans h

theorem stableThreshold_ge_succ_sigma (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ : Cardinal.{u}) : Order.succ σ ≤ stableThreshold K σ := by
  have h := stableThreshold_above_bound K σ
  have : Order.succ σ ≤ stableBound K σ :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right le_rfl))
  exact this.trans h

theorem stableThreshold_ge_sigma (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ : Cardinal.{u}) : σ ≤ stableThreshold K σ :=
  (Order.le_succ σ).trans (stableThreshold_ge_succ_sigma K σ)

theorem stableThreshold_reversal (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ : Cardinal.{u}) :
    IsReversalThreshold K (σ ⊔ aleph0) (stableThreshold K σ) := by
  intro κ hκle hcat
  have hrev0 := leastRevThreshold_mem K (σ ⊔ aleph0) le_sup_right
  have hbound : leastRevThreshold K (σ ⊔ aleph0) le_sup_right ≤ stableBound K σ :=
    le_sup_of_le_right le_rfl
  exact hrev0 κ ((hbound.trans (stableThreshold_above_bound K σ)).trans hκle) hcat

theorem stableThreshold_reversal_of_le (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ θ : Cardinal.{u}) (hle : θ ≤ σ ⊔ aleph0) :
    IsReversalThreshold K θ (stableThreshold K σ) :=
  isReversalThreshold_of_le_length K hle (stableThreshold_reversal K σ)

/-- Diagram equality: agreement of `≡σκ`-classes at every categoricity cardinal from the
threshold up to both ambient sizes (equivalent to the stabilized class after Prop. 4.2). -/
def SameStableDiagram (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ : Cardinal.{u}) {α : Type u} {M N : Model K.τ}
    (xs : α → M.carrier) (ys : α → N.carrier) : Prop :=
  ∀ κ : Cardinal.{u}, stableThreshold K σ ≤ κ →
    κ ≤ Model.card M → κ ≤ Model.card N → Categorical K κ →
    SameDiagramAt K κ xs ys

/-- Order embedding `Below κ ↪o Below γ` when `κ ≤ γ`. -/
noncomputable def cardOrderEmbed {κ γ : Cardinal.{u}} (hle : κ ≤ γ) :
    Below κ ↪o Below γ :=
  (Ordinal.initialSegToType (Cardinal.ord_le_ord.mpr hle)).toOrderEmbedding

/-- Extend a categoricity model of size `θ` to one of size `ρ ≥ θ` via the EM presentation
(English Prop. 4.2, assertion 4: grow a `c_σ`-submodel to the target categoricity size). -/
theorem exists_extend_to_card (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (θ ρ : Cardinal.{u})
    (hθinf : aleph0 ≤ θ) (hls : ls K ≤ θ) (hle : θ ≤ ρ)
    (hcatθ : Categorical K θ)
    (M₀ : Model K.τ) (hM₀ : K.Mem M₀) (hc₀ : Model.card M₀ = θ) :
    ∃ (R : Model K.τ) (ι : Language.Embedding K.τ M₀.carrier R.carrier),
      K.Mem R ∧ K.Strong ι ∧ Model.card R = ρ := by
  classical
  let I := Below θ
  let J := Below ρ
  have hI : #I = θ := by simp [I, Below, mk_ord_toType]
  have hJ : #J = ρ := by simp [J, Below, mk_ord_toType]
  haveI : Nonempty I := by
    rw [← mk_ne_zero_iff, hI]
    exact ne_of_gt (aleph0_pos.trans_le hθinf)
  haveI : Nonempty J := by
    rw [← mk_ne_zero_iff, hJ]
    exact ne_of_gt (aleph0_pos.trans_le (hθinf.trans hle))
  have hImem : K.Mem (E.obj I) := orderPresentation_obj_mem E I
  have hJmem : K.Mem (E.obj J) := orderPresentation_obj_mem E J
  have hIcard : Model.card (E.obj I) = θ :=
    orderPresentation_obj_card E hI hls hθinf
  have hJcard : Model.card (E.obj J) = ρ :=
    orderPresentation_obj_card E hJ (hls.trans hle) (hθinf.trans hle)
  obtain ⟨φ⟩ := hcatθ.unique_model M₀ (E.obj I) hM₀ hImem hc₀ hIcard
  let fIJ : I ↪o J := cardOrderEmbed hle
  let ι : Language.Embedding K.τ M₀.carrier (E.obj J).carrier :=
    (E.map fIJ).comp φ.toEmbedding
  exact ⟨E.obj J, ι, hJmem,
    K.strong_trans φ.toEmbedding (E.map fIJ) (strong_of_equiv K φ hM₀) (E.map_strong fIJ),
    hJcard⟩

/-- SameDiagramAt from a strong map between equal-size models. -/
theorem sameDiagramAt_of_sameStrongClass (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    {α : Type u} {M N : Model K.τ}
    (hM : K.Mem M) (hN : K.Mem N)
    (hcM : Model.card M = κ) (hcN : Model.card N = κ)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (h : SameStrongClass K xs ys) : SameDiagramAt K κ xs ys :=
  ⟨M, N, Language.Embedding.refl K.τ M.carrier, Language.Embedding.refl K.τ N.carrier,
    xs, ys, hM, hN, K.strong_refl M hM, K.strong_refl N hN, hcM, hcN,
    fun _ => rfl, fun _ => rfl, h⟩

/-! ### Projections of diagram classes (English Prop. 4.2) -/

/-- Projection well-defined: a `γ`-class determines a `κ`-class for `κ ≤ γ`. -/
theorem sameDiagramAt_of_le (K : AbstractElementaryClass.{u}) (κ γ θ : Cardinal.{u})
    (hκγ : κ ≤ γ) (hcatκ : Categorical K κ) (hlsκ : ls K ≤ κ) (hκinf : aleph0 ≤ κ)
    (hrevκ : ReversalProperty K θ κ) (hακ : θ ≤ κ)
    {α : Type u} {M N : Model K.τ} (hα : #α ≤ θ)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (h : SameDiagramAt K γ xs ys) : SameDiagramAt K κ xs ys := by
  obtain ⟨M₀, N₀, f, g, x₀, y₀, hM₀, hN₀, hf, hg, hcM₀, hcN₀, hx, hy, ⟨e, he, het⟩⟩ := h
  have hα_le_κ : #α ≤ κ := hα.trans hακ
  have hcardM₀ : κ ≤ Model.card M₀ := hκγ.trans (le_of_eq hcM₀.symm)
  have hcardN₀ : κ ≤ Model.card N₀ := hκγ.trans (le_of_eq hcN₀.symm)
  obtain ⟨M₁, i, hM₁, hi, hcM₁, hhitM⟩ :=
    exists_strong_hull_of_tuple K κ hlsκ hκinf M₀ hM₀ hcardM₀ x₀ hα_le_κ
  obtain ⟨N₁, j, hN₁, hj, hcN₁, hhitN⟩ :=
    exists_strong_hull_of_tuple K κ hlsκ hκinf N₀ hN₀ hcardN₀ y₀ hα_le_κ
  classical
  let x₁ : α → M₁.carrier := fun a => Classical.choose (hhitM a)
  let y₁ : α → N₁.carrier := fun a => Classical.choose (hhitN a)
  have hx₁ : ∀ a, i (x₁ a) = x₀ a := fun a => Classical.choose_spec (hhitM a)
  have hy₁ : ∀ a, j (y₁ a) = y₀ a := fun a => Classical.choose_spec (hhitN a)
  let f₁ : Language.Embedding K.τ M₁.carrier N₀.carrier := e.comp i
  have hf₁ : K.Strong f₁ := K.strong_trans i e hi he
  let A : Set N₀.carrier := Set.range f₁ ∪ Set.range j
  have hA_le : #A ≤ κ := by
    have hle := mk_union_le (Set.range f₁) (Set.range j)
    have h1 : #(Set.range f₁) ≤ κ := (mk_range_le (f := ⇑f₁)).trans_eq hcM₁
    have h2 : #(Set.range j) ≤ κ := (mk_range_le (f := ⇑j)).trans_eq hcN₁
    have hsum := add_le_add h1 h2
    rw [add_eq_self hκinf] at hsum
    exact hle.trans hsum
  have hA_ge : κ ≤ #A := by
    have hr : #(Set.range j) = κ := (mk_range_eq (⇑j) j.injective).trans hcN₁
    exact hr.symm.trans_le (mk_le_mk_of_subset Set.subset_union_right)
  have hA_eq : #A = κ := le_antisymm hA_le hA_ge
  obtain ⟨M₃, f₃, hM₃, hf₃, hcov, hcard₃⟩ := (isLSBound_ls K).2.2 N₀ hN₀ A
  have hcard_le : Model.card M₃ ≤ κ := by
    have h := hcard₃.trans (add_le_add (le_of_eq hA_eq) hlsκ)
    rwa [add_eq_self hκinf] at h
  have hcard_ge : κ ≤ Model.card M₃ := by
    have hr : #(Set.range j) = κ := (mk_range_eq (⇑j) j.injective).trans hcN₁
    have hsub : Set.range j ⊆ Set.range f₃ := by
      intro x hx
      obtain ⟨n, hn⟩ := hcov x (Or.inr hx)
      exact ⟨n, hn⟩
    exact hr.symm.trans_le ((mk_le_mk_of_subset hsub).trans mk_range_le)
  have hc₃ : Model.card M₃ = κ := le_antisymm hcard_le hcard_ge
  have himg₁ : ∀ x, ∃ y, f₃ y = f₁ x := fun x => hcov (f₁ x) (Or.inl ⟨x, rfl⟩)
  have himg₂ : ∀ x, ∃ y, f₃ y = j x := fun x => hcov (j x) (Or.inr ⟨x, rfl⟩)
  let g₁ := factorEmbedding f₁ f₃ himg₁
  let g₂ := factorEmbedding j f₃ himg₂
  have hg₁ : K.Strong g₁ :=
    K.coherence g₁ f₁ f₃ hf₁ hf₃ (factorEmbedding_comp f₁ f₃ himg₁)
  have hg₂ : K.Strong g₂ :=
    K.coherence g₂ j f₃ hj hf₃ (factorEmbedding_comp j f₃ himg₂)
  have hcg₁ := factorEmbedding_comp f₁ f₃ himg₁
  have hcg₂ := factorEmbedding_comp j f₃ himg₂
  have hz : ∀ a, g₁ (x₁ a) = g₂ (y₁ a) := by
    intro a
    apply f₃.injective
    calc
      f₃ (g₁ (x₁ a)) = f₁ (x₁ a) := by rw [← Language.Embedding.comp_apply, hcg₁]
      _ = y₀ a := by rw [Language.Embedding.comp_apply, hx₁ a, het a]
      _ = j (y₁ a) := (hy₁ a).symm
      _ = f₃ (g₂ (y₁ a)) := by rw [← Language.Embedding.comp_apply, hcg₂]
  obtain ⟨φ⟩ := hcatκ.unique_model M₃ N₁ hM₃ hN₁ hc₃ hcN₁
  have hφstr : K.Strong φ.toEmbedding := strong_of_equiv K φ hM₃
  let s : Language.Embedding K.τ N₁.carrier N₁.carrier := φ.toEmbedding.comp g₂
  have hs : K.Strong s := K.strong_trans g₂ φ.toEmbedding hg₂ hφstr
  obtain ⟨r, hr, hr_tup⟩ := hrevκ N₁ s (fun a => y₁ a) hN₁ hcN₁ hs hα
  let e₁ : Language.Embedding K.τ M₁.carrier N₁.carrier :=
    (r.comp φ.toEmbedding).comp g₁
  have he₁ : K.Strong e₁ :=
    K.strong_trans g₁ (r.comp φ.toEmbedding) hg₁
      (K.strong_trans φ.toEmbedding r hφstr hr)
  have he₁t : ∀ a, e₁ (x₁ a) = y₁ a := by
    intro a
    change r (φ (g₁ (x₁ a))) = y₁ a
    rw [hz a]
    simpa [s, Language.Embedding.comp_apply] using hr_tup a
  exact ⟨M₁, N₁, f.comp i, g.comp j, x₁, y₁, hM₁, hN₁,
    K.strong_trans i f hi hf, K.strong_trans j g hj hg, hcM₁, hcN₁,
    fun a => by rw [Language.Embedding.comp_apply, hx₁ a, hx a],
    fun a => by rw [Language.Embedding.comp_apply, hy₁ a, hy a],
    ⟨e₁, he₁, he₁t⟩⟩

/-- Surjectivity of `π_γκ`: extend a `κ`-model along EM to size `γ` and push the tuple. -/
theorem exists_diagram_lift (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (κ γ : Cardinal.{u})
    (hκγ : κ ≤ γ) (hls : ls K ≤ κ) (hκinf : aleph0 ≤ κ)
    (hcatκ : Categorical K κ)
    {α : Type u} {M : Model K.τ}
    (hM : K.Mem M) (hcM : Model.card M = κ) (hακ : #α ≤ κ)
    (xs : α → M.carrier) :
    ∃ (N : Model K.τ) (ι : Language.Embedding K.τ M.carrier N.carrier)
      (ys : α → N.carrier),
      K.Mem N ∧ K.Strong ι ∧ Model.card N = γ ∧
      (∀ a, ι (xs a) = ys a) ∧ SameDiagramAt K κ xs ys := by
  obtain ⟨N, ι, hN, hι, hcN⟩ :=
    exists_extend_to_card K E κ γ hκinf hls hκγ hcatκ M hM hcM
  refine ⟨N, ι, fun a => ι (xs a), hN, hι, hcN, fun _ => rfl, ?_⟩
  exact sameDiagramAt_of_strong_image K κ xs ι hι
    (sameDiagramAt_refl K κ hls hκinf hM (le_of_eq hcM.symm) xs hακ)

/-! ### Orbit / strong-class bound `B_σ` -/

/-- Setoid of strong-map classes of `α`-tuples in a fixed model. -/
noncomputable def strongClassSetoid (K : AbstractElementaryClass.{u}) (κ θ : Cardinal.{u})
    (hcat : Categorical K κ) (hrev : ReversalProperty K θ κ)
    {α : Type u} {M : Model K.τ}
    (hM : K.Mem M) (hcM : Model.card M = κ) (hα : #α ≤ θ) :
    Setoid (α → M.carrier) where
  r xs ys := SameStrongClass K xs ys
  iseqv := ⟨fun xs => sameStrongClass_refl K hM xs,
    fun {xs ys} h => sameStrongClass_symm K κ θ hcat hrev hM hM hcM hcM hα xs ys h,
    fun {xs ys zs} h₁ h₂ => sameStrongClass_trans K xs ys zs h₁ h₂⟩

/-- At a categoricity cardinal the number of strong-map classes of length-`≤σ` tuples is
at most `B(ℓ,σ) = orbitRecordBound`. -/
theorem mk_strongClassQuotient_le (K : AbstractElementaryClass.{u})
    (E : OrderPresentation K) (σ κ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hcat : Categorical K κ)
    (hle : max (ls K) (Order.succ σ) ≤ κ)
    (hrev : ReversalProperty K σ κ)
    {M : Model K.τ} (hM : K.Mem M) (hcM : Model.card M = κ) :
    #(Quotient (strongClassSetoid K κ σ hcat hrev hM hcM
        (show #(Below σ) ≤ σ by simp [Below, mk_ord_toType]))) ≤
      orbitRecordBound (ls K) σ := by
  classical
  let α := Below σ
  have hα : #α ≤ σ := by simp [α, Below, mk_ord_toType]
  let s := strongClassSetoid K κ σ hcat hrev hM hcM hα
  let N := elimOrbitNaming K E σ hσ
  let f : Quotient s → OrbitName K σ := fun q =>
    N.name hM (Quotient.out (s := s) q) hα
  have hinj : Function.Injective f := by
    intro q₁ q₂ hf
    have hleM : max (ls K) (Order.succ σ) ≤ Model.card M := by simpa [hcM] using hle
    have hcatM : Categorical K (Model.card M) := by simpa [hcM] using hcat
    have horb : SameAutOrbit K M (Quotient.out (s := s) q₁) (Quotient.out (s := s) q₂) :=
      (N.name_spec hM (Quotient.out (s := s) q₁) (Quotient.out (s := s) q₂) hα hleM hcatM).1 hf
    have hstrong : SameStrongClass K (Quotient.out (s := s) q₁) (Quotient.out (s := s) q₂) := by
      obtain ⟨e, he⟩ := (sameAutOrbit_iff_equiv K hM
        (Quotient.out (s := s) q₁) (Quotient.out (s := s) q₂)).1 horb
      exact ⟨e.toEmbedding, strong_of_equiv K e hM, he⟩
    rw [← Quotient.out_eq (s := s) q₁, ← Quotient.out_eq (s := s) q₂]
    exact Quotient.sound hstrong
  have hmk : #(Quotient s) ≤ #(OrbitName K σ) := mk_le_of_injective hinj
  have hName : #(OrbitName K σ) = orbitRecordBound (ls K) σ := by
    dsimp [OrbitName, Below]; exact mk_ord_toType _
  exact hmk.trans_eq hName

/-- Cardinality of strong-map classes in the unique model of size `κ`. -/
noncomputable def numStrongClasses (K : AbstractElementaryClass.{u})
    (σ κ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hcat : Categorical K κ)
    (hle : max (ls K) (Order.succ σ) ≤ κ)
    (hrev : ReversalProperty K σ κ) : Cardinal.{u} :=
  let M := Classical.choose hcat.exists_model
  let hM := (Classical.choose_spec hcat.exists_model).1
  let hcM := (Classical.choose_spec hcat.exists_model).2
  #(Quotient (strongClassSetoid K κ σ hcat hrev hM hcM
    (show #(Below σ) ≤ σ by simp [Below, mk_ord_toType])))

theorem numStrongClasses_le_B (K : AbstractElementaryClass.{u})
    (E : OrderPresentation K) (σ κ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hcat : Categorical K κ)
    (hle : max (ls K) (Order.succ σ) ≤ κ)
    (hrev : ReversalProperty K σ κ) :
    numStrongClasses K σ κ hσ hcat hle hrev ≤ orbitRecordBound (ls K) σ := by
  classical
  dsimp [numStrongClasses]
  exact mk_strongClassQuotient_le K E σ κ hσ hcat hle hrev
    (Classical.choose_spec hcat.exists_model).1
    (Classical.choose_spec hcat.exists_model).2

/-- Soft lower bound ensuring LS, `σ⁺`, and reversal at length `σ` are available. -/
theorem stableBound_ready (K : AbstractElementaryClass.{u}) (σ : Cardinal.{u})
    (_hσ : aleph0 ≤ σ) :
    max (ls K) (Order.succ σ) ≤ stableBound K σ ∧
      IsReversalThreshold K σ (stableBound K σ) := by
  refine ⟨?_, ?_⟩
  · refine max_le ?_ ?_
    · exact le_sup_of_le_left (le_sup_of_le_right (le_rfl : ls K ≤ ls K))
    · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
        (le_rfl : Order.succ σ ≤ Order.succ σ)))
  · have h := leastRevThreshold_mem K (σ ⊔ aleph0) le_sup_right
    have hle : leastRevThreshold K (σ ⊔ aleph0) le_sup_right ≤ stableBound K σ :=
      le_sup_of_le_right le_rfl
    exact isReversalThreshold_of_le_length K le_sup_left fun κ hκle hcat =>
      h κ (hle.trans hκle) hcat

/-- Projection injectivity: equal `κ`-classes of large enough tuples remain equal at `γ ≥ κ`. -/
def ProjectionInjective (K : AbstractElementaryClass.{u}) (σ κ γ : Cardinal.{u}) : Prop :=
  ∀ {α : Type u} {M N : Model K.τ} (hα : #α ≤ σ)
    (xs : α → M.carrier) (ys : α → N.carrier),
    γ ≤ Model.card M → γ ≤ Model.card N →
    SameDiagramAt K κ xs ys → SameDiagramAt K γ xs ys

/-! ### Extending length-`≤σ` tuples onto `Below σ` (for pair coding) -/

/-- Extend an `α`-tuple along a fixed embedding `α ↪ Below σ` by repeating a default value. -/
noncomputable def extendTupleBelow {α β : Type u} {σ : Cardinal.{u}}
    (e : α ↪ Below σ) (d : β) (xs : α → β) : Below σ → β := by
  classical
  exact fun j => if h : ∃ a, e a = j then xs (Classical.choose h) else d

theorem extendTupleBelow_comp {α β : Type u} {σ : Cardinal.{u}}
    (e : α ↪ Below σ) (d : β) (xs : α → β) (a : α) :
    extendTupleBelow e d xs (e a) = xs a := by
  classical
  dsimp [extendTupleBelow]
  have h : ∃ a', e a' = e a := ⟨a, rfl⟩
  simp only [h, ↓reduceDIte]
  exact congrArg xs (e.injective (Classical.choose_spec h))

/-- Restricting an extended diagram equality recovers the original. -/
theorem sameDiagramAt_of_extendBelow {K : AbstractElementaryClass.{u}} {κ σ : Cardinal.{u}}
    {α : Type u} {M N : Model K.τ}
    (e : α ↪ Below σ) (dx : M.carrier) (dy : N.carrier)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (h : SameDiagramAt K κ (extendTupleBelow e dx xs) (extendTupleBelow e dy ys)) :
    SameDiagramAt K κ xs ys := by
  obtain ⟨M₀, N₀, f, g, x₀, y₀, hM₀, hN₀, hf, hg, hcM, hcN, hx, hy, ⟨emb, he, het⟩⟩ := h
  refine ⟨M₀, N₀, f, g, fun a => x₀ (e a), fun a => y₀ (e a), hM₀, hN₀, hf, hg, hcM, hcN,
    fun a => by rw [hx (e a), extendTupleBelow_comp e dx xs a],
    fun a => by rw [hy (e a), extendTupleBelow_comp e dy ys a],
    ⟨emb, he, fun a => het (e a)⟩⟩

/-- Repeat-extension preserves diagram equality (`α` nonempty, default = value at a fixed index). -/
theorem sameDiagramAt_extendBelow_repeat {K : AbstractElementaryClass.{u}} {κ σ : Cardinal.{u}}
    {α : Type u} [Nonempty α] {M N : Model K.τ}
    (e : α ↪ Below σ) (xs : α → M.carrier) (ys : α → N.carrier)
    (h : SameDiagramAt K κ xs ys) :
    SameDiagramAt K κ
      (extendTupleBelow e (xs (Classical.arbitrary α)) xs)
      (extendTupleBelow e (ys (Classical.arbitrary α)) ys) := by
  obtain ⟨M₀, N₀, f, g, x₀, y₀, hM₀, hN₀, hf, hg, hcM, hcN, hx, hy, ⟨emb, he, het⟩⟩ := h
  classical
  let a0 : α := Classical.arbitrary α
  let xPad : Below σ → M₀.carrier :=
    extendTupleBelow e (x₀ a0) x₀
  let yPad : Below σ → N₀.carrier :=
    extendTupleBelow e (y₀ a0) y₀
  have hxPad : ∀ j, f (xPad j) = extendTupleBelow e (xs a0) xs j := by
    intro j
    dsimp [xPad, extendTupleBelow]
    split_ifs with hj
    · exact hx _
    · exact hx a0
  have hyPad : ∀ j, g (yPad j) = extendTupleBelow e (ys a0) ys j := by
    intro j
    dsimp [yPad, extendTupleBelow]
    split_ifs with hj
    · exact hy _
    · exact hy a0
  have hetPad : ∀ j, emb (xPad j) = yPad j := by
    intro j
    dsimp [xPad, yPad, extendTupleBelow]
    split_ifs with hj
    · exact het _
    · exact het a0
  exact ⟨M₀, N₀, f, g, xPad, yPad, hM₀, hN₀, hf, hg, hcM, hcN, hxPad, hyPad, ⟨emb, he, hetPad⟩⟩

/-- At a categoricity cardinal, empty-index diagrams always match, so a failure witness is nonempty. -/
theorem nonempty_of_not_sameDiagramAt_cat {K : AbstractElementaryClass.{u}}
    {γ : Cardinal.{u}} {α : Type u} {M N : Model K.τ}
    (hcat : Categorical K γ) (hls : ls K ≤ γ) (hγinf : aleph0 ≤ γ)
    (hM : K.Mem M) (hN : K.Mem N)
    (hMc : γ ≤ Model.card M) (hNc : γ ≤ Model.card N)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (hnot : ¬ SameDiagramAt K γ xs ys) : Nonempty α := by
  by_contra hne
  have hEmp : IsEmpty α := not_nonempty_iff.mp hne
  have hα0 : #α ≤ γ := by
    rw [mk_eq_zero_iff.mpr hEmp]
    exact bot_le
  obtain ⟨M₀, f, hM₀, hf, hcM, _⟩ :=
    exists_strong_hull_of_tuple K γ hls hγinf M hM hMc xs hα0
  obtain ⟨N₀, g, hN₀, hg, hcN, _⟩ :=
    exists_strong_hull_of_tuple K γ hls hγinf N hN hNc ys hα0
  obtain ⟨φ⟩ := hcat.unique_model M₀ N₀ hM₀ hN₀ hcM hcN
  have hsame : SameDiagramAt K γ xs ys :=
    ⟨M₀, N₀, f, g, fun a => hEmp.elim a, fun a => hEmp.elim a, hM₀, hN₀, hf, hg, hcM, hcN,
      fun a => hEmp.elim a, fun a => hEmp.elim a,
      ⟨φ.toEmbedding, strong_of_equiv K φ hM₀, fun a => hEmp.elim a⟩⟩
  exact hnot hsame

end
end AEC
