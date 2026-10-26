module

public import AEC.Section4.NaturalDiagram
public import AEC.Section4.CountableClosure
public import AEC.Section4.StableDiagramConstruction
public import AEC.Section1.ArbitrarilyLarge
public import AEC.Section1.UnboundedCategoricity
public import AEC.Section2.FiniteHull
public import AEC.Section2.DirectedLimit
public import AEC.Section3.Reversal
public import Mathlib.Order.WellFounded
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal Ordinal

/-- The natural diagrams of two `σ`-tuples already differ on the induced suborder `X`. -/
def DiagramsDifferOnSubset (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) {I : Type u} [LinearOrder I] [Nonempty I]
    {α : Type u} (σ : Cardinal.{u}) (hσ : #α ≤ σ) (X : Set I) (hX : X.Nonempty) : Prop :=
  haveI : Nonempty (↥X) := hX.to_subtype
  ∃ t' s' : α → SupportTerm E.lab E.arity (↥X),
    ¬ SameNaturalDiagram K E D σ hσ t' s'

/-- Factor a strong embedding through a strong ambient map whose range covers it; coherence
supplies strength of the factor. -/
theorem strongFactorEmbedding {K : AbstractElementaryClass.{u}} {M₀ M₁ M₂ : Model K.τ}
    (f₀₂ : Language.Embedding K.τ M₀.carrier M₂.carrier)
    (f₁₂ : Language.Embedding K.τ M₁.carrier M₂.carrier)
    (hf₀₂ : K.Strong f₀₂) (hf₁₂ : K.Strong f₁₂)
    (himg : ∀ x, ∃ y, f₁₂ y = f₀₂ x) :
    K.Strong (factorEmbedding f₀₂ f₁₂ himg) :=
  K.coherence (factorEmbedding f₀₂ f₁₂ himg) f₀₂ f₁₂ hf₀₂ hf₁₂
    (factorEmbedding_comp f₀₂ f₁₂ himg)

/-- **Lemma 4.1** (Canonical classes above one categoricity size). At a categoricity cardinal
`κ ≥ LS(K)` where reversal holds for `κ`-tuples, a tuple in a model of size at least `κ` has a
well-defined `≡σκ`-class: any two strong `κ`-submodels containing it are related by a strong map
sending the tuple to itself, and a strong embedding of models of size at least `κ` preserves
that class. -/
theorem lemma_4_1 (K : AbstractElementaryClass.{u}) (κ θ : Cardinal.{u})
    (hcat : Categorical K κ) (hls : ls K ≤ κ) (hrev : ReversalProperty K θ κ)
    (N : Model K.τ) (hN : K.Mem N) (hcard : κ ≤ Model.card N)
    {α : Type u} (a : α → N.carrier) (hα : #α ≤ θ) :
    (∀ (M₁ M₂ : Model K.τ)
        (f₁ : Language.Embedding K.τ M₁.carrier N.carrier)
        (f₂ : Language.Embedding K.τ M₂.carrier N.carrier),
        K.Mem M₁ → K.Mem M₂ → K.Strong f₁ → K.Strong f₂ →
        Model.card M₁ = κ → Model.card M₂ = κ →
        (∀ i, ∃ x, f₁ x = a i) → (∀ i, ∃ y, f₂ y = a i) →
        ∃ e : Language.Embedding K.τ M₁.carrier M₂.carrier,
          K.Strong e ∧
          ∀ i x y, f₁ x = a i → f₂ y = a i → e x = y) ∧
    ∀ (N' : Model K.τ) (g : Language.Embedding K.τ N.carrier N'.carrier),
      K.Mem N' → K.Strong g → κ ≤ Model.card N' →
      ∀ (M₁ M₂ : Model K.τ)
        (f₁ : Language.Embedding K.τ M₁.carrier N.carrier)
        (f₂ : Language.Embedding K.τ M₂.carrier N'.carrier),
        K.Mem M₁ → K.Mem M₂ → K.Strong f₁ → K.Strong f₂ →
        Model.card M₁ = κ → Model.card M₂ = κ →
        (∀ i, ∃ x, f₁ x = a i) → (∀ i, ∃ y, f₂ y = g (a i)) →
        ∃ e : Language.Embedding K.τ M₁.carrier M₂.carrier,
          K.Strong e ∧
          ∀ i x y, f₁ x = a i → f₂ y = g (a i) → e x = y := by
  classical
  have hκinf : aleph0 ≤ κ := (isLSBound_ls K).1.trans hls
  /- Common strong `κ`-hull of two strong `κ`-embeddings into an ambient model. -/
  have commonHull {M₁ M₂ P : Model K.τ}
      (f₁ : Language.Embedding K.τ M₁.carrier P.carrier)
      (f₂ : Language.Embedding K.τ M₂.carrier P.carrier)
      (hP : K.Mem P) (hf₁ : K.Strong f₁) (hf₂ : K.Strong f₂)
      (hc₁ : Model.card M₁ = κ) (hc₂ : Model.card M₂ = κ) :
      ∃ (M₃ : Model K.τ)
        (f₃ : Language.Embedding K.τ M₃.carrier P.carrier)
        (g₁ : Language.Embedding K.τ M₁.carrier M₃.carrier)
        (g₂ : Language.Embedding K.τ M₂.carrier M₃.carrier),
        K.Mem M₃ ∧ K.Strong f₃ ∧ Model.card M₃ = κ ∧
        K.Strong g₁ ∧ K.Strong g₂ ∧
        f₃.comp g₁ = f₁ ∧ f₃.comp g₂ = f₂ := by
    let A : Set P.carrier := Set.range f₁ ∪ Set.range f₂
    have hA_le : #A ≤ κ := by
      have hle := mk_union_le (Set.range f₁) (Set.range f₂)
      have h1 : #(Set.range f₁) ≤ κ :=
        (mk_range_le (f := ⇑f₁)).trans_eq hc₁
      have h2 : #(Set.range f₂) ≤ κ :=
        (mk_range_le (f := ⇑f₂)).trans_eq hc₂
      have hsum := add_le_add h1 h2
      rw [add_eq_self hκinf] at hsum
      exact hle.trans hsum
    have hA_ge : κ ≤ #A := by
      have hr : #(Set.range f₁) = κ :=
        (mk_range_eq (⇑f₁) f₁.injective).trans hc₁
      exact hr.symm.trans_le (mk_le_mk_of_subset Set.subset_union_left)
    have hA_eq : #A = κ := le_antisymm hA_le hA_ge
    obtain ⟨M₃, f₃, hM₃, hf₃, hcov, hcard₃⟩ := (isLSBound_ls K).2.2 P hP A
    have hcard_le : Model.card M₃ ≤ κ := by
      have h := hcard₃.trans (add_le_add (le_of_eq hA_eq) hls)
      rwa [add_eq_self hκinf] at h
    have hcard_ge : κ ≤ Model.card M₃ := by
      have hr : #(Set.range f₁) = κ :=
        (mk_range_eq (⇑f₁) f₁.injective).trans hc₁
      have hsub : Set.range f₁ ⊆ Set.range f₃ := by
        intro x hx
        obtain ⟨n, hn⟩ := hcov x (Or.inl hx)
        exact ⟨n, hn⟩
      have hle : #(Set.range f₁) ≤ #(Set.range f₃) := mk_le_mk_of_subset hsub
      exact hr.symm.trans_le (hle.trans mk_range_le)
    have hc₃ : Model.card M₃ = κ := le_antisymm hcard_le hcard_ge
    have himg₁ : ∀ x, ∃ y, f₃ y = f₁ x := fun x =>
      hcov (f₁ x) (Or.inl ⟨x, rfl⟩)
    have himg₂ : ∀ x, ∃ y, f₃ y = f₂ x := fun x =>
      hcov (f₂ x) (Or.inr ⟨x, rfl⟩)
    let g₁ := factorEmbedding f₁ f₃ himg₁
    let g₂ := factorEmbedding f₂ f₃ himg₂
    refine ⟨M₃, f₃, g₁, g₂, hM₃, hf₃, hc₃,
      strongFactorEmbedding f₁ f₃ hf₁ hf₃ himg₁,
      strongFactorEmbedding f₂ f₃ hf₂ hf₃ himg₂,
      factorEmbedding_comp f₁ f₃ himg₁,
      factorEmbedding_comp f₂ f₃ himg₂⟩
  /- Strong map between two `κ`-models that hit the same ambient tuple. -/
  have sameClass {M₁ M₂ P : Model K.τ} (b : α → P.carrier)
      (f₁ : Language.Embedding K.τ M₁.carrier P.carrier)
      (f₂ : Language.Embedding K.τ M₂.carrier P.carrier)
      (hP : K.Mem P) (hf₁ : K.Strong f₁) (hf₂ : K.Strong f₂)
      (hc₁ : Model.card M₁ = κ) (hc₂ : Model.card M₂ = κ)
      (hhit₁ : ∀ i, ∃ x, f₁ x = b i) (hhit₂ : ∀ i, ∃ y, f₂ y = b i) :
      ∃ e : Language.Embedding K.τ M₁.carrier M₂.carrier,
        K.Strong e ∧ ∀ i x y, f₁ x = b i → f₂ y = b i → e x = y := by
    obtain ⟨M₃, f₃, g₁, g₂, hM₃, _hf₃, hc₃, hg₁, hg₂, hcg₁, hcg₂⟩ :=
      commonHull f₁ f₂ hP hf₁ hf₂ hc₁ hc₂
    let x₁ : α → M₁.carrier := fun i => Classical.choose (hhit₁ i)
    let y₂ : α → M₂.carrier := fun i => Classical.choose (hhit₂ i)
    have hx₁ : ∀ i, f₁ (x₁ i) = b i := fun i => Classical.choose_spec (hhit₁ i)
    have hy₂ : ∀ i, f₂ (y₂ i) = b i := fun i => Classical.choose_spec (hhit₂ i)
    have hz : ∀ i, g₁ (x₁ i) = g₂ (y₂ i) := by
      intro i
      apply f₃.injective
      calc
        f₃ (g₁ (x₁ i)) = f₁ (x₁ i) := by rw [← Language.Embedding.comp_apply, hcg₁]
        _ = b i := hx₁ i
        _ = f₂ (y₂ i) := (hy₂ i).symm
        _ = f₃ (g₂ (y₂ i)) := by rw [← Language.Embedding.comp_apply, hcg₂]
    have hM₂ : K.Mem M₂ := K.strong_mem_dom f₂ hf₂
    obtain ⟨φ⟩ := hcat.unique_model M₃ M₂ hM₃ hM₂ hc₃ hc₂
    have hφstr : K.Strong φ.toEmbedding := strong_of_equiv K φ hM₃
    let s : Language.Embedding K.τ M₂.carrier M₂.carrier := φ.toEmbedding.comp g₂
    have hs : K.Strong s := K.strong_trans g₂ φ.toEmbedding hg₂ hφstr
    obtain ⟨r, hr, hr_tup⟩ := hrev M₂ s (fun i => y₂ i) hM₂ hc₂ hs hα
    let e : Language.Embedding K.τ M₁.carrier M₂.carrier :=
      (r.comp φ.toEmbedding).comp g₁
    have he : K.Strong e :=
      K.strong_trans g₁ (r.comp φ.toEmbedding) hg₁
        (K.strong_trans φ.toEmbedding r hφstr hr)
    refine ⟨e, he, ?_⟩
    intro i x y hx hy
    have hx_eq : x = x₁ i := f₁.injective (hx.trans (hx₁ i).symm)
    have hy_eq : y = y₂ i := f₂.injective (hy.trans (hy₂ i).symm)
    rw [hx_eq, hy_eq]
    change r (φ (g₁ (x₁ i))) = y₂ i
    rw [hz i]
    simpa [s, Language.Embedding.comp_apply] using hr_tup i
  refine ⟨?_, ?_⟩
  · intro M₁ M₂ f₁ f₂ _hM₁ _hM₂ hf₁ hf₂ hc₁ hc₂ hhit₁ hhit₂
    exact sameClass a f₁ f₂ hN hf₁ hf₂ hc₁ hc₂ hhit₁ hhit₂
  · intro N' g hN' hg _hcard' M₁ M₂ f₁ f₂ _hM₁ _hM₂ hf₁ hf₂ hc₁ hc₂ hhit₁ hhit₂
    have hf₁' : K.Strong (g.comp f₁) := K.strong_trans f₁ g hf₁ hg
    have hhit₁' : ∀ i, ∃ x, (g.comp f₁) x = g (a i) := by
      intro i
      obtain ⟨x, hx⟩ := hhit₁ i
      exact ⟨x, by rw [Language.Embedding.comp_apply, hx]⟩
    obtain ⟨e, he, he_tup⟩ :=
      sameClass (fun i => g (a i)) (g.comp f₁) f₂ hN' hf₁' hf₂ hc₁ hc₂ hhit₁' hhit₂
    refine ⟨e, he, ?_⟩
    intro i x y hx hy
    exact he_tup i x y (by rw [Language.Embedding.comp_apply, hx]) hy

/-- From a `SameDiagramAt` witness at equal ambient categoricity size, recover a strong map of
the ambient models, using Lemma 4.1 to identify each model with its `κ`-hull. -/
theorem sameDiagramAt_to_strong (K : AbstractElementaryClass.{u}) (κ θ : Cardinal.{u})
    (hcat : Categorical K κ) (hls : ls K ≤ κ) (hrev : ReversalProperty K θ κ)
    {α : Type u} {M N : Model K.τ}
    (hM : K.Mem M) (hN : K.Mem N)
    (hcM : Model.card M = κ) (hcN : Model.card N = κ)
    (hα : #α ≤ θ)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (h : SameDiagramAt K κ xs ys) :
    SameStrongClass K xs ys := by
  obtain ⟨M₀, N₀, f, g, x₀, y₀, hM₀, hN₀, hf, hg, hc₀, hc₁, hx, hy, ⟨e, he, het⟩⟩ := h
  have hL := lemma_4_1 K κ θ hcat hls hrev M hM (le_of_eq hcM.symm) xs hα
  obtain ⟨eM₀, heM₀, heM₀_tup⟩ :=
    hL.1 M M₀ (Language.Embedding.refl K.τ M.carrier) f hM hM₀
      (K.strong_refl M hM) hf hcM hc₀ (fun i => ⟨xs i, rfl⟩) (fun i => ⟨x₀ i, hx i⟩)
  refine ⟨g.comp (e.comp eM₀),
    K.strong_trans eM₀ (g.comp e) heM₀ (K.strong_trans e g he hg), ?_⟩
  intro i
  change g (e (eM₀ (xs i))) = ys i
  have h1 : eM₀ (xs i) = x₀ i := heM₀_tup i (xs i) (x₀ i) rfl (hx i)
  rw [h1, het i, hy i]

/-- Transitivity of `SameDiagramAt` via Lemma 4.1 on the middle ambient. -/
theorem sameDiagramAt_trans (K : AbstractElementaryClass.{u}) (κ θ : Cardinal.{u})
    (hcat : Categorical K κ) (hls : ls K ≤ κ) (hrev : ReversalProperty K θ κ)
    {α : Type u} {M N P : Model K.τ}
    (hN : K.Mem N) (hα : #α ≤ θ)
    (xs : α → M.carrier) (ys : α → N.carrier) (zs : α → P.carrier)
    (h₁ : SameDiagramAt K κ xs ys) (h₂ : SameDiagramAt K κ ys zs) :
    SameDiagramAt K κ xs zs := by
  obtain ⟨A, B, fA, fB, xA, yB, hA, hB, hfA, hfB, hcA, hcB, hxA, hyB, ⟨e1, he1, het1⟩⟩ := h₁
  obtain ⟨C, D, fC, fD, xC, yD, hC, hD, hfC, hfD, hcC, hcD, hxC, hyD, ⟨e2, he2, het2⟩⟩ := h₂
  have hcardN : κ ≤ Model.card N := by
    have : Model.card B ≤ Model.card N := by
      simpa [Model.card, hcB] using
        (Cardinal.mk_le_of_injective (f := ⇑fB) fB.injective)
    exact hcB.symm.trans_le this
  have hLN := lemma_4_1 K κ θ hcat hls hrev N hN hcardN ys hα
  obtain ⟨eBC, heBC, heBCt⟩ :=
    hLN.1 B C fB fC hB hC hfB hfC hcB hcC
      (fun i => ⟨yB i, hyB i⟩) (fun i => ⟨xC i, hxC i⟩)
  refine ⟨A, D, fA, fD, xA, yD, hA, hD, hfA, hfD, hcA, hcD, hxA, hyD,
    ⟨e2.comp (eBC.comp e1),
      K.strong_trans e1 (e2.comp eBC) he1 (K.strong_trans eBC e2 heBC he2), ?_⟩⟩
  intro i
  change e2 (eBC (e1 (xA i))) = yD i
  rw [het1 i, heBCt i (yB i) (xC i) (hyB i) (hxC i), het2 i]

/-- Reversal at length `σ` for every categoricity cardinal `≥ stableThreshold K σ`. -/
theorem reversal_at_stableThreshold (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (σ κ : Cardinal.{u}) (hle : stableThreshold K σ ≤ κ)
    (hcat : Categorical K κ) : ReversalProperty K σ κ :=
  (stableThreshold_reversal_of_le K σ σ le_sup_left κ hle hcat).2

/-- Ready package at categoricity cardinals past `stableBound`. -/
theorem readyAt (K : AbstractElementaryClass.{u}) (σ κ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hb : stableBound K σ ≤ κ) (hcat : Categorical K κ) :
    max (ls K) (Order.succ σ) ≤ κ ∧ ReversalProperty K σ κ ∧
      ls K ≤ κ ∧ aleph0 ≤ κ := by
  have hr := stableBound_ready K σ hσ
  have hle := hr.1.trans hb
  exact ⟨hle, (hr.2 κ hb hcat).2, (le_max_left _ _).trans hle,
    (isLSBound_ls K).1.trans ((le_max_left _ _).trans hle)⟩

/-- Nondecreasing of `numStrongClasses` along `κ ≤ γ` (surjective class projection). -/
theorem numStrongClasses_mono (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (σ κ γ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hκγ : κ ≤ γ)
    (hcatκ : Categorical K κ) (hcatγ : Categorical K γ)
    (hleκ : max (ls K) (Order.succ σ) ≤ κ)
    (hrevκ : ReversalProperty K σ κ) (hrevγ : ReversalProperty K σ γ) :
    numStrongClasses K σ κ hσ hcatκ hleκ hrevκ ≤
      numStrongClasses K σ γ hσ hcatγ (hleκ.trans hκγ) hrevγ := by
  classical
  let Mκ := Classical.choose hcatκ.exists_model
  let hMκ := (Classical.choose_spec hcatκ.exists_model).1
  let hcκ := (Classical.choose_spec hcatκ.exists_model).2
  let Mγ := Classical.choose hcatγ.exists_model
  let hMγ := (Classical.choose_spec hcatγ.exists_model).1
  let hcγ := (Classical.choose_spec hcatγ.exists_model).2
  have hα : #(Below σ) ≤ σ := by simp [Below]
  let sκ := strongClassSetoid K κ σ hcatκ hrevκ hMκ hcκ hα
  let sγ := strongClassSetoid K γ σ hcatγ hrevγ hMγ hcγ hα
  have hlsκ : ls K ≤ κ := (le_max_left _ _).trans hleκ
  have hκinf : aleph0 ≤ κ := (isLSBound_ls K).1.trans hlsκ
  have hακ : #(Below σ) ≤ κ :=
    hα.trans ((Order.le_succ σ).trans ((le_max_right _ _).trans hleκ))
  have hσleκ : σ ≤ κ := (Order.le_succ σ).trans ((le_max_right _ _).trans hleκ)
  -- Project a γ-tuple into the κ-model via a strong κ-hull + iso.
  let projTuple (xs : Below σ → Mγ.carrier) : Below σ → Mκ.carrier := by
    have hcardγ : κ ≤ Model.card Mγ := hκγ.trans (le_of_eq hcγ.symm)
    let H := exists_strong_hull_of_tuple K κ hlsκ hκinf Mγ hMγ hcardγ xs hακ
    let M₀ := Classical.choose H
    let hsp := Classical.choose_spec (Classical.choose_spec H)
    let x₀ : Below σ → M₀.carrier := fun i => Classical.choose (hsp.2.2.2 i)
    let φ := Classical.choice (hcatκ.unique_model M₀ Mκ hsp.1 hMκ hsp.2.2.1 hcκ)
    exact fun i => φ (x₀ i)
  have proj_same (xs : Below σ → Mγ.carrier) :
      SameDiagramAt K κ xs (projTuple xs) := by
    dsimp [projTuple]
    have hcardγ : κ ≤ Model.card Mγ := hκγ.trans (le_of_eq hcγ.symm)
    set H := exists_strong_hull_of_tuple K κ hlsκ hκinf Mγ hMγ hcardγ xs hακ
    set M₀ := Classical.choose H
    set f := Classical.choose (Classical.choose_spec H)
    set hsp := Classical.choose_spec (Classical.choose_spec H)
    set x₀ : Below σ → M₀.carrier := fun i => Classical.choose (hsp.2.2.2 i)
    have hx₀ : ∀ i, f (x₀ i) = xs i := fun i => Classical.choose_spec (hsp.2.2.2 i)
    set φ := Classical.choice (hcatκ.unique_model M₀ Mκ hsp.1 hMκ hsp.2.2.1 hcκ)
    have hφ : K.Strong φ.toEmbedding := strong_of_equiv K φ hsp.1
    -- SameDiagramAt κ xs x₀ via hull, then push along φ to Mκ
    have hhull : SameDiagramAt K κ xs x₀ :=
      ⟨M₀, M₀, f, Language.Embedding.refl K.τ M₀.carrier, x₀, x₀,
        hsp.1, hsp.1, hsp.2.1, K.strong_refl M₀ hsp.1, hsp.2.2.1, hsp.2.2.1,
        hx₀, fun _ => rfl, sameStrongClass_refl K hsp.1 x₀⟩
    exact sameDiagramAt_comp_right K κ xs x₀ φ.toEmbedding hφ hhull
  have pre_wd (xs ys : Below σ → Mγ.carrier) (h : (sγ : Setoid _).r xs ys) :
      (⟦projTuple xs⟧ : Quotient sκ) = ⟦projTuple ys⟧ := by
    apply Quotient.sound
    have hdγ : SameDiagramAt K γ xs ys :=
      sameDiagramAt_of_sameStrongClass K γ hMγ hMγ hcγ hcγ xs ys h
    have hdκ : SameDiagramAt K κ xs ys :=
      sameDiagramAt_of_le K κ γ σ hκγ hcatκ hlsκ hκinf hrevκ hσleκ hα xs ys hdγ
    have h1 := proj_same xs
    have h2 := proj_same ys
    have h3 : SameDiagramAt K κ (projTuple xs) (projTuple ys) :=
      sameDiagramAt_trans K κ σ hcatκ hlsκ hrevκ hMγ hα
        (projTuple xs) xs (projTuple ys)
        (sameDiagramAt_symm K κ σ hcatκ hrevκ hα xs (projTuple xs) h1)
        (sameDiagramAt_trans K κ σ hcatκ hlsκ hrevκ hMγ hα xs ys (projTuple ys) hdκ h2)
    exact sameDiagramAt_to_strong K κ σ hcatκ hlsκ hrevκ
      hMκ hMκ hcκ hcκ hα (projTuple xs) (projTuple ys) h3
  let π : Quotient sγ → Quotient sκ := Quotient.lift (fun xs => ⟦projTuple xs⟧) pre_wd
  have hπsurj : Function.Surjective π := by
    intro qκ
    refine Quotient.inductionOn qκ fun ys => ?_
    obtain ⟨N, _ι, zs, hN, _hι, hcN, _hzs, hdiag⟩ :=
      exists_diagram_lift K E κ γ hκγ hlsκ hκinf hcatκ hMκ hcκ hακ ys
    obtain ⟨ψ⟩ := hcatγ.unique_model N Mγ hN hMγ hcN hcγ
    refine ⟨⟦fun i => ψ (zs i)⟧, ?_⟩
    -- π ⟦ψ ∘ zs⟧ = ⟦projTuple (ψ ∘ zs)⟧ = ⟦ys⟧
    change ⟦projTuple (fun i => ψ (zs i))⟧ = ⟦ys⟧
    apply Quotient.sound
    have h1 : SameDiagramAt K κ ys (fun i => ψ (zs i)) :=
      sameDiagramAt_comp_right K κ ys zs ψ.toEmbedding (strong_of_equiv K ψ hN) hdiag
    have h2 := proj_same (fun i => ψ (zs i))
    have h3 : SameDiagramAt K κ ys (projTuple (fun i => ψ (zs i))) :=
      sameDiagramAt_trans K κ σ hcatκ hlsκ hrevκ hMγ hα
        ys (fun i => ψ (zs i)) (projTuple (fun i => ψ (zs i))) h1 h2
    exact sameStrongClass_symm K κ σ hcatκ hrevκ hMκ hMκ hcκ hcκ hα
      ys (projTuple (fun i => ψ (zs i)))
      (sameDiagramAt_to_strong K κ σ hcatκ hlsκ hrevκ
        hMκ hMκ hcκ hcκ hα ys (projTuple (fun i => ψ (zs i))) h3)
  have hleQ : #(Quotient sκ) ≤ #(Quotient sγ) := mk_le_of_surjective hπsurj
  simpa [numStrongClasses, Mκ, Mγ, hMκ, hMγ, hcκ, hcγ, sκ, sγ] using hleQ

noncomputable def codeOfNum {B n : Cardinal.{u}} (hn : n ≤ B) : Below (Order.succ B) :=
  ToType.mk ⟨n.ord, Cardinal.ord_lt_ord.mpr (Order.lt_succ_iff.mpr hn)⟩

theorem codeOfNum_lt {B n m : Cardinal.{u}} (hn : n ≤ B) (hm : m ≤ B) (hlt : n < m) :
    codeOfNum hn < codeOfNum hm :=
  (ToType.mk.lt_iff_lt).2 (Cardinal.ord_lt_ord.mpr hlt)

def NumClassesUnstable (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) : Prop :=
  ∀ (κ₀ : Cardinal.{u}), stableBound K σ ≤ κ₀ →
    ∀ (_hcat₀ : Categorical K κ₀),
      ∃ γ, κ₀ ≤ γ ∧
        ∃ (_hcatγ : Categorical K γ)
          (_hle₀ : max (ls K) (Order.succ σ) ≤ κ₀)
          (_hrev₀ : ReversalProperty K σ κ₀)
          (_hleγ : max (ls K) (Order.succ σ) ≤ γ)
          (_hrevγ : ReversalProperty K σ γ),
          numStrongClasses K σ κ₀ hσ _hcat₀ _hle₀ _hrev₀ ≠
            numStrongClasses K σ γ hσ _hcatγ _hleγ _hrevγ

noncomputable def numStabStage (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (h : NumClassesUnstable K σ hσ)
    (i : (Order.succ (Order.succ (orbitRecordBound (ls K) σ))).ord.ToType) :
    Cardinal.{u} × Cardinal.{u} × Cardinal.{u} :=
  let β := stableBound K σ
  let B := orbitRecordBound (ls K) σ
  let prev :=
    ⨆ j : { j : (Order.succ (Order.succ B)).ord.ToType // j < i },
      (numStabStage K E σ hσ h j.1).2.1
  let κ₀ := leastCategorical K (β ⊔ Order.succ prev)
  have hmem := leastCategorical_mem K (β ⊔ Order.succ prev)
  let hex := h κ₀ (le_sup_left.trans hmem.1) hmem.2
  let γ := Classical.choose hex
  let hγ := Classical.choose_spec hex
  let hcatγ := Classical.choose hγ.2
  let hrest := Classical.choose_spec hγ.2
  let hle₀ := Classical.choose hrest
  let hrest2 := Classical.choose_spec hrest
  let hrev₀ := Classical.choose hrest2
  let hrest3 := Classical.choose_spec hrest2
  let hleγ := Classical.choose hrest3
  let hrest4 := Classical.choose_spec hrest3
  let hrevγ := Classical.choose hrest4
  (κ₀, γ, numStrongClasses K σ γ hσ hcatγ hleγ hrevγ)
termination_by i
decreasing_by
  exact j.2

theorem numStabStage_num_le_B (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (h : NumClassesUnstable K σ hσ)
    (i : (Order.succ (Order.succ (orbitRecordBound (ls K) σ))).ord.ToType) :
    (numStabStage K E σ hσ h i).2.2 ≤ orbitRecordBound (ls K) σ := by
  classical
  rw [numStabStage.eq_def]
  dsimp only
  exact numStrongClasses_le_B K E σ _ hσ _ _ _

/-- Unpack stage: κ₀ ≤ γ, both cat/ready, and N κ₀ < N γ (= cached num). -/
theorem numStabStage_props (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (h : NumClassesUnstable K σ hσ)
    (i : (Order.succ (Order.succ (orbitRecordBound (ls K) σ))).ord.ToType) :
    let κ₀ := (numStabStage K E σ hσ h i).1
    let γ := (numStabStage K E σ hσ h i).2.1
    let n := (numStabStage K E σ hσ h i).2.2
    stableBound K σ ≤ κ₀ ∧ κ₀ ≤ γ ∧
      ∃ (hcatκ : Categorical K κ₀) (hcatγ : Categorical K γ)
        (hle₀ : max (ls K) (Order.succ σ) ≤ κ₀)
        (hrev₀ : ReversalProperty K σ κ₀)
        (hleγ : max (ls K) (Order.succ σ) ≤ γ)
        (hrevγ : ReversalProperty K σ γ),
        numStrongClasses K σ κ₀ hσ hcatκ hle₀ hrev₀ <
          numStrongClasses K σ γ hσ hcatγ hleγ hrevγ ∧
        n = numStrongClasses K σ γ hσ hcatγ hleγ hrevγ := by
  classical
  let β := stableBound K σ
  let B := orbitRecordBound (ls K) σ
  rw [numStabStage.eq_def]
  dsimp only
  set prev :=
    ⨆ j : { j : (Order.succ (Order.succ B)).ord.ToType // j < i },
      (numStabStage K E σ hσ h j.1).2.1
  set κ₀ := leastCategorical K (β ⊔ Order.succ prev)
  have hmem := leastCategorical_mem K (β ⊔ Order.succ prev)
  set hex := h κ₀ (le_sup_left.trans hmem.1) hmem.2
  set γ := Classical.choose hex
  set hγ := Classical.choose_spec hex
  set hcatγ := Classical.choose hγ.2
  set hrest := Classical.choose_spec hγ.2
  set hle₀ := Classical.choose hrest
  set hrest2 := Classical.choose_spec hrest
  set hrev₀ := Classical.choose hrest2
  set hrest3 := Classical.choose_spec hrest2
  set hleγ := Classical.choose hrest3
  set hrest4 := Classical.choose_spec hrest3
  set hrevγ := Classical.choose hrest4
  set hne := Classical.choose_spec hrest4
  have hmono :=
    numStrongClasses_mono K E σ κ₀ γ hσ hγ.1 hmem.2 hcatγ hle₀ hrev₀ hrevγ
  exact ⟨le_sup_left.trans hmem.1, hγ.1, hmem.2, hcatγ, hle₀, hrev₀, hleγ, hrevγ,
    lt_of_le_of_ne hmono hne, rfl⟩

theorem numStabStage_num_strict_mono (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (h : NumClassesUnstable K σ hσ)
    {i j : (Order.succ (Order.succ (orbitRecordBound (ls K) σ))).ord.ToType}
    (hij : i < j) :
    (numStabStage K E σ hσ h i).2.2 < (numStabStage K E σ hσ h j).2.2 := by
  classical
  let β := stableBound K σ
  let B := orbitRecordBound (ls K) σ
  obtain ⟨hβi, hκγi, hcati0, hcati, hlei0, hrevi0, hlei, hrevi, hlti, hni⟩ :=
    numStabStage_props K E σ hσ h i
  obtain ⟨hβj, hκγj, hcatj0, hcatj, hlej0, hrevj0, hlej, hrevj, hltj, hnj⟩ :=
    numStabStage_props K E σ hσ h j
  have hγi_le_prev : (numStabStage K E σ hσ h i).2.1 ≤
      (⨆ k : { k : (Order.succ (Order.succ B)).ord.ToType // k < j },
        (numStabStage K E σ hσ h k.1).2.1) := by
    exact le_ciSup (Cardinal.bddAbove_of_small
      (s := Set.range fun k : { k : (Order.succ (Order.succ B)).ord.ToType // k < j} =>
        (numStabStage K E σ hσ h k.1).2.1)) ⟨i, hij⟩
  have hγi_le_κ₀j : (numStabStage K E σ hσ h i).2.1 ≤ (numStabStage K E σ hσ h j).1 := by
    rw [numStabStage.eq_def (i := j)]
    dsimp only
    set prev :=
      ⨆ k : { k : (Order.succ (Order.succ B)).ord.ToType // k < j },
        (numStabStage K E σ hσ h k.1).2.1
    have hmem := leastCategorical_mem K (β ⊔ Order.succ prev)
    exact hγi_le_prev.trans ((Order.le_succ prev).trans (le_sup_right.trans hmem.1))
  have hmono_mid :=
    numStrongClasses_mono K E σ
      (numStabStage K E σ hσ h i).2.1 (numStabStage K E σ hσ h j).1 hσ
      hγi_le_κ₀j hcati hcatj0 hlei hrevi hrevj0
  -- N γi ≤ N κ₀j < N γj, and cached nums equal those N values
  have hlt' :
      numStrongClasses K σ (numStabStage K E σ hσ h i).2.1 hσ hcati hlei hrevi <
        numStrongClasses K σ (numStabStage K E σ hσ h j).2.1 hσ hcatj hlej hrevj :=
    lt_of_le_of_lt hmono_mid hltj
  rw [hni, hnj]
  exact hlt'

theorem exists_num_stabilization (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) :
    ∃ (κ₀ : Cardinal.{u}) (hβ : stableBound K σ ≤ κ₀) (hcat₀ : Categorical K κ₀),
      ∀ (γ : Cardinal.{u}) (hκ₀γ : κ₀ ≤ γ) (hcatγ : Categorical K γ)
        (hle₀ : max (ls K) (Order.succ σ) ≤ κ₀)
        (hrev₀ : ReversalProperty K σ κ₀)
        (hleγ : max (ls K) (Order.succ σ) ≤ γ)
        (hrevγ : ReversalProperty K σ γ),
        numStrongClasses K σ κ₀ hσ hcat₀ hle₀ hrev₀ =
          numStrongClasses K σ γ hσ hcatγ hleγ hrevγ := by
  classical
  let β := stableBound K σ
  let B := orbitRecordBound (ls K) σ
  by_cases h :
      ∃ (κ₀ : Cardinal.{u}) (_hβ : β ≤ κ₀) (_hcat₀ : Categorical K κ₀),
        ∀ (γ : Cardinal.{u}) (_hκ₀γ : κ₀ ≤ γ) (_hcatγ : Categorical K γ)
          (_hle₀ : max (ls K) (Order.succ σ) ≤ κ₀)
          (_hrev₀ : ReversalProperty K σ κ₀)
          (_hleγ : max (ls K) (Order.succ σ) ≤ γ)
          (_hrevγ : ReversalProperty K σ γ),
          numStrongClasses K σ κ₀ hσ _hcat₀ _hle₀ _hrev₀ =
            numStrongClasses K σ γ hσ _hcatγ _hleγ _hrevγ
  · exact h
  · push Not at h
    let Idx := (Order.succ (Order.succ B)).ord.ToType
    have hunstab : NumClassesUnstable K σ hσ := h
    let f : Idx → Below (Order.succ B) := fun i =>
      codeOfNum (numStabStage_num_le_B K E σ hσ hunstab i)
    have hf : Function.Injective f := by
      intro a b hab
      rcases lt_trichotomy a b with hlt | heq | hgt
      · have hltN := numStabStage_num_strict_mono K E σ hσ hunstab hlt
        exact absurd hab (ne_of_lt (codeOfNum_lt _ _ hltN))
      · exact heq
      · have hltN := numStabStage_num_strict_mono K E σ hσ hunstab hgt
        exact absurd hab.symm (ne_of_lt (codeOfNum_lt _ _ hltN))
    have hcard : Order.succ (Order.succ B) ≤ Order.succ B := by
      simpa [Idx, Below, mk_ord_toType] using mk_le_of_injective hf
    exact absurd hcard (Order.lt_succ (Order.succ B)).not_ge

/-! ### Projection injectivity via English pair coding -/

def ProjectionUnstable (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) : Prop :=
  ∀ (κ₀ : Cardinal.{u}), stableBound K σ ≤ κ₀ →
    ∀ (_hcat₀ : Categorical K κ₀),
      ∃ κ γ, κ₀ ≤ κ ∧ κ ≤ γ ∧ Categorical K κ ∧ Categorical K γ ∧
        ¬ ProjectionInjective K σ κ γ

/-- Unpack a projection failure into `Below σ`-tuples in ambient models of size `≥ γ`. -/
theorem exists_proj_fail_below (K : AbstractElementaryClass.{u})
    (σ κ γ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hcatγ : Categorical K γ)
    (hleγ : max (ls K) (Order.succ σ) ≤ γ)
    (hfail : ¬ ProjectionInjective K σ κ γ) :
    ∃ (M N : Model K.τ) (hM : K.Mem M) (hN : K.Mem N)
      (xs : Below σ → M.carrier) (ys : Below σ → N.carrier),
      γ ≤ Model.card M ∧ γ ≤ Model.card N ∧
        SameDiagramAt K κ xs ys ∧ ¬ SameDiagramAt K γ xs ys := by
  classical
  unfold ProjectionInjective at hfail
  push_neg at hfail
  obtain ⟨α, M, N, hα, xs, ys, hMc, hNc, hsameκ, hnotγ⟩ := hfail
  have hls : ls K ≤ γ := (le_max_left _ _).trans hleγ
  have hγinf : aleph0 ≤ γ := (isLSBound_ls K).1.trans hls
  have hM : K.Mem M := by
    obtain ⟨_, _, f, _, _, _, _, _, hf, _, _, _, _, _, _⟩ := hsameκ
    exact K.strong_mem_cod f hf
  have hN : K.Mem N := by
    obtain ⟨_, _, _, g, _, _, _, _, _, hg, _, _, _, _, _⟩ := hsameκ
    exact K.strong_mem_cod g hg
  haveI : Nonempty α :=
    nonempty_of_not_sameDiagramAt_cat hcatγ hls hγinf hM hN hMc hNc xs ys hnotγ
  let e : α ↪ Below σ := embedBelow hα
  let xsP := extendTupleBelow e (xs (Classical.arbitrary α)) xs
  let ysP := extendTupleBelow e (ys (Classical.arbitrary α)) ys
  refine ⟨M, N, hM, hN, xsP, ysP, hMc, hNc,
    sameDiagramAt_extendBelow_repeat e xs ys hsameκ, ?_⟩
  intro hγ
  exact hnotγ (sameDiagramAt_of_extendBelow e _ _ xs ys hγ)

/-- Lift a pair of `Below σ`-tuples from size-`≥γ` models into one categoricity model of size `ρ ≥ γ`. -/
theorem exists_lift_pair_to_card (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (σ γ ρ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hγρ : γ ≤ ρ)
    (hcatγ : Categorical K γ) (hcatρ : Categorical K ρ)
    (hleγ : max (ls K) (Order.succ σ) ≤ γ)
    {M N : Model K.τ} (hM : K.Mem M) (hN : K.Mem N)
    (hMc : γ ≤ Model.card M) (hNc : γ ≤ Model.card N)
    (xs : Below σ → M.carrier) (ys : Below σ → N.carrier) :
    ∃ (R : Model K.τ) (hR : K.Mem R) (hcR : Model.card R = ρ)
      (xs' ys' : Below σ → R.carrier),
      SameDiagramAt K γ xs xs' ∧ SameDiagramAt K γ ys ys' := by
  classical
  have hls : ls K ≤ γ := (le_max_left _ _).trans hleγ
  have hγinf : aleph0 ≤ γ := (isLSBound_ls K).1.trans hls
  have hασ : #(Below σ) ≤ σ := by simp [Below, mk_ord_toType]
  have hαγ : #(Below σ) ≤ γ :=
    hασ.trans ((Order.le_succ σ).trans ((le_max_right _ _).trans hleγ))
  obtain ⟨M₀, f, hM₀, hf, hcM₀, hhitM⟩ :=
    exists_strong_hull_of_tuple K γ hls hγinf M hM hMc xs hαγ
  obtain ⟨N₀, g, hN₀, hg, hcN₀, hhitN⟩ :=
    exists_strong_hull_of_tuple K γ hls hγinf N hN hNc ys hαγ
  let x₀ : Below σ → M₀.carrier := fun i => Classical.choose (hhitM i)
  let y₀ : Below σ → N₀.carrier := fun i => Classical.choose (hhitN i)
  have hx₀ : ∀ i, f (x₀ i) = xs i := fun i => Classical.choose_spec (hhitM i)
  have hy₀ : ∀ i, g (y₀ i) = ys i := fun i => Classical.choose_spec (hhitN i)
  obtain ⟨R, ι, hR, hι, hcR⟩ :=
    exists_extend_to_card K E γ ρ hγinf hls hγρ hcatγ M₀ hM₀ hcM₀
  obtain ⟨R₂, ι₂, hR₂, hι₂, hcR₂⟩ :=
    exists_extend_to_card K E γ ρ hγinf hls hγρ hcatγ N₀ hN₀ hcN₀
  obtain ⟨φ⟩ := hcatρ.unique_model R₂ R hR₂ hR hcR₂ hcR
  let xs' : Below σ → R.carrier := fun i => ι (x₀ i)
  let ys' : Below σ → R.carrier := fun i => φ (ι₂ (y₀ i))
  have hxs : SameDiagramAt K γ xs xs' := by
    have hhull : SameDiagramAt K γ xs x₀ :=
      ⟨M₀, M₀, f, Language.Embedding.refl K.τ M₀.carrier, x₀, x₀,
        hM₀, hM₀, hf, K.strong_refl M₀ hM₀, hcM₀, hcM₀, hx₀, fun _ => rfl,
        sameStrongClass_refl K hM₀ x₀⟩
    exact sameDiagramAt_comp_right K γ xs x₀ ι hι hhull
  have hys : SameDiagramAt K γ ys ys' := by
    have hhull : SameDiagramAt K γ ys y₀ :=
      ⟨N₀, N₀, g, Language.Embedding.refl K.τ N₀.carrier, y₀, y₀,
        hN₀, hN₀, hg, K.strong_refl N₀ hN₀, hcN₀, hcN₀, hy₀, fun _ => rfl,
        sameStrongClass_refl K hN₀ y₀⟩
    have h1 := sameDiagramAt_comp_right K γ ys y₀ ι₂ hι₂ hhull
    exact sameDiagramAt_comp_right K γ ys (fun i => ι₂ (y₀ i)) φ.toEmbedding
      (strong_of_equiv K φ hR₂) h1
  exact ⟨R, hR, hcR, xs', ys', hxs, hys⟩

noncomputable def projStabStage (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (h : ProjectionUnstable K σ hσ)
    (i : (Order.succ (Order.succ (orbitRecordBound (ls K) σ))).ord.ToType) :
    Cardinal.{u} × Cardinal.{u} :=
  let β := stableBound K σ
  let B := orbitRecordBound (ls K) σ
  let prev :=
    ⨆ j : { j : (Order.succ (Order.succ B)).ord.ToType // j < i },
      (projStabStage K E σ hσ h j.1).2
  let κ₀ := leastCategorical K (β ⊔ Order.succ prev)
  have hmem := leastCategorical_mem K (β ⊔ Order.succ prev)
  let hex := h κ₀ (le_sup_left.trans hmem.1) hmem.2
  let κ := Classical.choose hex
  let hrest := Classical.choose_spec hex
  let γ := Classical.choose hrest
  (κ, γ)
termination_by i
decreasing_by
  exact j.2

theorem projStabStage_props (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (h : ProjectionUnstable K σ hσ)
    (i : (Order.succ (Order.succ (orbitRecordBound (ls K) σ))).ord.ToType) :
    let κ := (projStabStage K E σ hσ h i).1
    let γ := (projStabStage K E σ hσ h i).2
    stableBound K σ ≤ κ ∧ κ ≤ γ ∧ Categorical K κ ∧ Categorical K γ ∧
      ¬ ProjectionInjective K σ κ γ := by
  classical
  let β := stableBound K σ
  let B := orbitRecordBound (ls K) σ
  rw [projStabStage.eq_def]
  dsimp only
  set prev :=
    ⨆ j : { j : (Order.succ (Order.succ B)).ord.ToType // j < i },
      (projStabStage K E σ hσ h j.1).2
  set κ₀ := leastCategorical K (β ⊔ Order.succ prev)
  have hmem := leastCategorical_mem K (β ⊔ Order.succ prev)
  set hex := h κ₀ (le_sup_left.trans hmem.1) hmem.2
  set κ := Classical.choose hex
  set hrest := Classical.choose_spec hex
  set γ := Classical.choose hrest
  set hγ := Classical.choose_spec hrest
  -- hγ : κ₀ ≤ κ ∧ κ ≤ γ ∧ Categorical K κ ∧ Categorical K γ ∧ ¬ProjInj
  exact ⟨(le_sup_left.trans hmem.1).trans hγ.1, hγ.2.1, hγ.2.2.1, hγ.2.2.2.1, hγ.2.2.2.2⟩

theorem projStabStage_γ_le_next (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (h : ProjectionUnstable K σ hσ)
    {i j : (Order.succ (Order.succ (orbitRecordBound (ls K) σ))).ord.ToType}
    (hij : i < j) :
    (projStabStage K E σ hσ h i).2 ≤ (projStabStage K E σ hσ h j).1 := by
  classical
  let β := stableBound K σ
  let B := orbitRecordBound (ls K) σ
  have hγi_le_prev : (projStabStage K E σ hσ h i).2 ≤
      (⨆ k : { k : (Order.succ (Order.succ B)).ord.ToType // k < j },
        (projStabStage K E σ hσ h k.1).2) :=
    le_ciSup (Cardinal.bddAbove_of_small
      (s := Set.range fun k : { k : (Order.succ (Order.succ B)).ord.ToType // k < j} =>
        (projStabStage K E σ hσ h k.1).2)) ⟨i, hij⟩
  rw [projStabStage.eq_def (i := j)]
  dsimp only
  set prev :=
    ⨆ k : { k : (Order.succ (Order.succ B)).ord.ToType // k < j },
      (projStabStage K E σ hσ h k.1).2
  have hmem := leastCategorical_mem K (β ⊔ Order.succ prev)
  set hex := h (leastCategorical K (β ⊔ Order.succ prev)) (le_sup_left.trans hmem.1) hmem.2
  set hrest := Classical.choose_spec hex
  set hγ := Classical.choose_spec hrest
  exact hγi_le_prev.trans ((Order.le_succ prev).trans (le_sup_right.trans (hmem.1.trans hγ.1)))

/-- A projection-failure witness at stage `i`, realized inside a fixed `ρ`-model, retaining
κ-agreement and γ-disagreement. -/
theorem exists_proj_fail_in_model (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (h : ProjectionUnstable K σ hσ)
    (i : (Order.succ (Order.succ (orbitRecordBound (ls K) σ))).ord.ToType)
    (ρ : Cardinal.{u}) {R : Model K.τ} (hR : K.Mem R) (hcR : Model.card R = ρ)
    (hcatρ : Categorical K ρ)
    (hγρ : (projStabStage K E σ hσ h i).2 ≤ ρ) :
    let κ := (projStabStage K E σ hσ h i).1
    let γ := (projStabStage K E σ hσ h i).2
    ∃ (xs' ys' : Below σ → R.carrier),
      SameDiagramAt K κ xs' ys' ∧ ¬ SameDiagramAt K γ xs' ys' := by
  classical
  let κ := (projStabStage K E σ hσ h i).1
  let γ := (projStabStage K E σ hσ h i).2
  have hprops := projStabStage_props K E σ hσ h i
  have hreadyγ := readyAt K σ γ hσ (hprops.1.trans hprops.2.1) hprops.2.2.2.1
  have hreadyκ := readyAt K σ κ hσ hprops.1 hprops.2.2.1
  obtain ⟨M, N, hM, hN, xs, ys, hMc, hNc, hsameκ, hnotγ⟩ :=
    exists_proj_fail_below K σ κ γ hσ hprops.2.2.2.1 hreadyγ.1 hprops.2.2.2.2
  obtain ⟨R', hR', hcR', xs0, ys0, hxsγ, hysγ⟩ :=
    exists_lift_pair_to_card K E σ γ ρ hσ hγρ hprops.2.2.2.1 hcatρ hreadyγ.1
      hM hN hMc hNc xs ys
  obtain ⟨φ⟩ := hcatρ.unique_model R' R hR' hR hcR' hcR
  let xs' : Below σ → R.carrier := fun a => φ (xs0 a)
  let ys' : Below σ → R.carrier := fun a => φ (ys0 a)
  have hασ : #(Below σ) ≤ σ := by simp [Below, mk_ord_toType]
  have hlsγ : ls K ≤ γ := (le_max_left _ _).trans hreadyγ.1
  have hγinf : aleph0 ≤ γ := (isLSBound_ls K).1.trans hlsγ
  have hσleγ : σ ≤ γ := (Order.le_succ σ).trans ((le_max_right _ _).trans hreadyγ.1)
  have hlsκ : ls K ≤ κ := (le_max_left _ _).trans hreadyκ.1
  have hκinf : aleph0 ≤ κ := (isLSBound_ls K).1.trans hlsκ
  have hσleκ : σ ≤ κ := (Order.le_succ σ).trans ((le_max_right _ _).trans hreadyκ.1)
  have hxsκ : SameDiagramAt K κ xs xs0 :=
    sameDiagramAt_of_le K κ γ σ hprops.2.1 hprops.2.2.1 hlsκ hκinf
      hreadyκ.2.1 hσleκ hασ xs xs0 hxsγ
  have hysκ : SameDiagramAt K κ ys ys0 :=
    sameDiagramAt_of_le K κ γ σ hprops.2.1 hprops.2.2.1 hlsκ hκinf
      hreadyκ.2.1 hσleκ hασ ys ys0 hysγ
  have h00 : SameDiagramAt K κ xs0 ys0 :=
    sameDiagramAt_trans K κ σ hprops.2.2.1 hlsκ hreadyκ.2.1 hM hασ
      xs0 xs ys0
      (sameDiagramAt_symm K κ σ hprops.2.2.1 hreadyκ.2.1 hασ xs xs0 hxsκ)
      (sameDiagramAt_trans K κ σ hprops.2.2.1 hlsκ hreadyκ.2.1 hN hασ
        xs ys ys0 hsameκ hysκ)
  have hφ : K.Strong φ.toEmbedding := strong_of_equiv K φ hR'
  have hκleR' : κ ≤ Model.card R' :=
    (hprops.2.1.trans hγρ).trans (le_of_eq hcR'.symm)
  have hsame' : SameDiagramAt K κ xs' ys' := by
    have hpush : SameDiagramAt K κ xs0 xs' :=
      sameDiagramAt_of_strong_image K κ xs0 φ.toEmbedding hφ
        (sameDiagramAt_refl K κ hlsκ hκinf hR' hκleR' xs0 (hασ.trans hσleκ))
    have hright : SameDiagramAt K κ xs0 ys' :=
      sameDiagramAt_comp_right K κ xs0 ys0 φ.toEmbedding hφ h00
    exact sameDiagramAt_trans K κ σ hprops.2.2.1 hlsκ hreadyκ.2.1 hR' hασ
      xs' xs0 ys'
      (sameDiagramAt_symm K κ σ hprops.2.2.1 hreadyκ.2.1 hασ xs0 xs' hpush) hright
  have hnot' : ¬ SameDiagramAt K γ xs' ys' := by
    intro hγ'
    have hxs'γ : SameDiagramAt K γ xs xs' :=
      sameDiagramAt_comp_right K γ xs xs0 φ.toEmbedding hφ hxsγ
    have hys'γ : SameDiagramAt K γ ys ys' :=
      sameDiagramAt_comp_right K γ ys ys0 φ.toEmbedding hφ hysγ
    have hback : SameDiagramAt K γ xs ys :=
      sameDiagramAt_trans K γ σ hprops.2.2.2.1 hlsγ hreadyγ.2.1 hR hασ
        xs xs' ys hxs'γ
        (sameDiagramAt_trans K γ σ hprops.2.2.2.1 hlsγ hreadyγ.2.1 hR hασ
          xs' ys' ys hγ'
          (sameDiagramAt_symm K γ σ hprops.2.2.2.1 hreadyγ.2.1 hασ ys ys' hys'γ))
    exact hnotγ hback
  exact ⟨xs', ys', hsame', hnot'⟩

/-- After the bound `κ₀`, projections `π_γκ` are injective (English Prop. 4.2 pair coding). -/
theorem exists_proj_stabilization (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) :
    ∃ (κ₀ : Cardinal.{u}) (_hβ : stableBound K σ ≤ κ₀) (_hcat₀ : Categorical K κ₀),
      ∀ (κ γ : Cardinal.{u}), κ₀ ≤ κ → κ ≤ γ →
        Categorical K κ → Categorical K γ →
        ProjectionInjective K σ κ γ := by
  classical
  let β := stableBound K σ
  let B := orbitRecordBound (ls K) σ
  by_cases h :
      ∃ (κ₀ : Cardinal.{u}) (_hβ : β ≤ κ₀) (_hcat₀ : Categorical K κ₀),
        ∀ (κ γ : Cardinal.{u}), κ₀ ≤ κ → κ ≤ γ →
          Categorical K κ → Categorical K γ →
          ProjectionInjective K σ κ γ
  · exact h
  · push Not at h
    let Idx := (Order.succ (Order.succ B)).ord.ToType
    have hunstab : ProjectionUnstable K σ hσ := h
    let ρ₀ := Order.succ (⨆ i : Idx, (projStabStage K E σ hσ hunstab i).2)
    let ρ := leastCategorical K (β ⊔ ρ₀)
    have hρmem := leastCategorical_mem K (β ⊔ ρ₀)
    have hβρ : β ≤ ρ := le_sup_left.trans hρmem.1
    have hcatρ : Categorical K ρ := hρmem.2
    have hreadyρ := readyAt K σ ρ hσ hβρ hcatρ
    have hγρ (i : Idx) : (projStabStage K E σ hσ hunstab i).2 ≤ ρ := by
      have hle : (projStabStage K E σ hσ hunstab i).2 ≤
          ⨆ j : Idx, (projStabStage K E σ hσ hunstab j).2 :=
        le_ciSup (Cardinal.bddAbove_of_small
          (s := Set.range fun j : Idx => (projStabStage K E σ hσ hunstab j).2)) i
      exact hle.trans ((Order.le_succ _).trans (le_sup_right.trans hρmem.1))
    let R := Classical.choose hcatρ.exists_model
    let hR := (Classical.choose_spec hcatρ.exists_model).1
    let hcR := (Classical.choose_spec hcatρ.exists_model).2
    have hασ : #(Below σ) ≤ σ := by simp [Below, mk_ord_toType]
    let Nam := elimOrbitNaming K E σ hσ
    let wit (i : Idx) :=
      exists_proj_fail_in_model K E σ hσ hunstab i ρ hR hcR hcatρ (hγρ i)
    let xsOf (i : Idx) : Below σ → R.carrier := Classical.choose (wit i)
    let ysOf (i : Idx) : Below σ → R.carrier :=
      Classical.choose (Classical.choose_spec (wit i))
    have hsep (i : Idx) :
        SameDiagramAt K (projStabStage K E σ hσ hunstab i).1 (xsOf i) (ysOf i) ∧
        ¬ SameDiagramAt K (projStabStage K E σ hσ hunstab i).2 (xsOf i) (ysOf i) :=
      Classical.choose_spec (Classical.choose_spec (wit i))
    let f : Idx → OrbitName K σ × OrbitName K σ := fun i =>
      (Nam.name hR (xsOf i) hασ, Nam.name hR (ysOf i) hασ)
    have hBinf : aleph0 ≤ B := by
      dsimp [B, orbitRecordBound]
      exact (cantor (aleph0 : Cardinal.{u})).le.trans
        (power_le_power_left two_ne_zero ((cantor (aleph0 : Cardinal.{u})).le.trans
          (power_le_power_left two_ne_zero (le_add_of_le_left (isLSBound_ls K).1))))
    have hmk : #(OrbitName K σ × OrbitName K σ) ≤ B := by
      have hName : #(OrbitName K σ) = B := by
        dsimp [OrbitName, Below, B]; exact mk_ord_toType _
      have hprod : #(OrbitName K σ × OrbitName K σ) =
          #(OrbitName K σ) * #(OrbitName K σ) := by
        simp [mk_prod, Cardinal.lift_id]
      rw [hprod, hName, Cardinal.mul_eq_self hBinf]
    have hcodes_ne {i j : Idx} (hlt : i < j) : f i ≠ f j := by
      intro hfij
      have hγi_le_κj := projStabStage_γ_le_next K E σ hσ hunstab hlt
      have hpropsj := projStabStage_props K E σ hσ hunstab j
      have hpropsi := projStabStage_props K E σ hσ hunstab i
      have hreadyi := readyAt K σ (projStabStage K E σ hσ hunstab i).2 hσ
        (hpropsi.1.trans hpropsi.2.1) hpropsi.2.2.2.1
      have hreadyj := readyAt K σ (projStabStage K E σ hσ hunstab j).1 hσ
        hpropsj.1 hpropsj.2.2.1
      have hleρ' : max (ls K) (Order.succ σ) ≤ ρ := hreadyρ.1
      have hleM : max (ls K) (Order.succ σ) ≤ Model.card R := by rw [hcR]; exact hleρ'
      have hcatM : Categorical K (Model.card R) := by rw [hcR]; exact hcatρ
      have horbx : SameAutOrbit K R (xsOf i) (xsOf j) :=
        (Nam.name_spec hR (xsOf i) (xsOf j) hασ hleM hcatM).1 (Prod.mk.inj hfij).1
      have horby : SameAutOrbit K R (ysOf i) (ysOf j) :=
        (Nam.name_spec hR (ysOf i) (ysOf j) hασ hleM hcatM).1 (Prod.mk.inj hfij).2
      have hdiagx : SameDiagramAt K ρ (xsOf i) (xsOf j) := by
        obtain ⟨e, het⟩ := (sameAutOrbit_iff_equiv K hR (xsOf i) (xsOf j)).1 horbx
        exact sameDiagramAt_of_sameStrongClass K ρ hR hR hcR hcR (xsOf i) (xsOf j)
          ⟨e.toEmbedding, strong_of_equiv K e hR, het⟩
      have hdiagy : SameDiagramAt K ρ (ysOf i) (ysOf j) := by
        obtain ⟨e, het⟩ := (sameAutOrbit_iff_equiv K hR (ysOf i) (ysOf j)).1 horby
        exact sameDiagramAt_of_sameStrongClass K ρ hR hR hcR hcR (ysOf i) (ysOf j)
          ⟨e.toEmbedding, strong_of_equiv K e hR, het⟩
      set γi := (projStabStage K E σ hσ hunstab i).2
      set κj := (projStabStage K E σ hσ hunstab j).1
      have hagree_j := (hsep j).1
      have hlsκj : ls K ≤ κj := (le_max_left _ _).trans hreadyj.1
      have hκjinf : aleph0 ≤ κj := (isLSBound_ls K).1.trans hlsκj
      have hσleκj : σ ≤ κj :=
        (Order.le_succ σ).trans ((le_max_right _ _).trans hreadyj.1)
      have hlsγi : ls K ≤ γi := (le_max_left _ _).trans hreadyi.1
      have hγiinf : aleph0 ≤ γi := (isLSBound_ls K).1.trans hlsγi
      have hσleγi : σ ≤ γi :=
        (Order.le_succ σ).trans ((le_max_right _ _).trans hreadyi.1)
      have hcatγi : Categorical K γi := hpropsi.2.2.2.1
      have hrevγi : ReversalProperty K σ γi := hreadyi.2.1
      have hagree_γi : SameDiagramAt K γi (xsOf j) (ysOf j) :=
        sameDiagramAt_of_le K γi κj σ hγi_le_κj hcatγi hlsγi hγiinf
          hrevγi hσleγi hασ (xsOf j) (ysOf j) hagree_j
      have hx_γ : SameDiagramAt K γi (xsOf i) (xsOf j) :=
        sameDiagramAt_of_le K γi ρ σ (hγρ i) hcatγi hlsγi hγiinf
          hrevγi hσleγi hασ (xsOf i) (xsOf j) hdiagx
      have hy_γ : SameDiagramAt K γi (ysOf i) (ysOf j) :=
        sameDiagramAt_of_le K γi ρ σ (hγρ i) hcatγi hlsγi hγiinf
          hrevγi hσleγi hασ (ysOf i) (ysOf j) hdiagy
      have htrans1 : SameDiagramAt K γi (xsOf i) (ysOf j) :=
        sameDiagramAt_trans K γi σ hcatγi hlsγi hrevγi hR hασ
          (xsOf i) (xsOf j) (ysOf j) hx_γ hagree_γi
      have hfinal : SameDiagramAt K γi (xsOf i) (ysOf i) :=
        sameDiagramAt_trans K γi σ hcatγi hlsγi hrevγi hR hασ
          (xsOf i) (ysOf j) (ysOf i) htrans1
          (sameDiagramAt_symm K γi σ hcatγi hrevγi hασ
            (ysOf i) (ysOf j) hy_γ)
      exact (hsep i).2 hfinal
    have hf : Function.Injective f := by
      intro i j hfij
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact absurd hfij (hcodes_ne hlt)
      · exact heq
      · exact absurd hfij.symm (hcodes_ne hgt)
    have hcard : Order.succ (Order.succ B) ≤ B := by
      simpa [Idx, Below, mk_ord_toType] using
        (mk_le_of_injective hf).trans hmk
    exact absurd hcard (lt_trans (Order.lt_succ B) (Order.lt_succ (Order.succ B))).not_ge

/-! ### Threshold `t(σ)` past reversal and proj/num stabilization (monotone via `Below`-sup) -/

/-- Cardinal of the ordinal coded by `i : Below κ`. -/
noncomputable def belowOrdCard {κ : Cardinal.{u}} (i : Below κ) : Cardinal.{u} :=
  Ordinal.card (ToType.toOrd i).val

theorem belowOrdCard_codeOfNum {B n : Cardinal.{u}} (hn : n ≤ B) :
    belowOrdCard (codeOfNum hn) = n := by
  dsimp [belowOrdCard, codeOfNum]
  simp [ToType.toOrd]

/-- Combined proj/num stabilization bound at length `ν` (applied at `ν ⊔ ℵ₀`). -/
noncomputable def lengthStabAt (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (ν : Cardinal.{u}) : Cardinal.{u} :=
  Classical.choose (exists_proj_stabilization K E (ν ⊔ aleph0) le_sup_right) ⊔
    Classical.choose (exists_num_stabilization K E (ν ⊔ aleph0) le_sup_right)

/-- Sup of stabilization points for all lengths coded below `succ(σ ⊔ ℵ₀)`. -/
noncomputable def lengthStabSup (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u}) : Cardinal.{u} :=
  haveI : Nonempty (Below (Order.succ (σ ⊔ aleph0))) := by simp [Below]
  ⨆ i : Below (Order.succ (σ ⊔ aleph0)), lengthStabAt K E (belowOrdCard i)

/-- Raw monotone bound: language/LS/reversal plus all length-stabilization points `≤ σ ⊔ ℵ₀`. -/
noncomputable def diagramRawBound (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u}) : Cardinal.{u} :=
  Order.succ (K.τ.card + σ) ⊔ stableBound K (σ ⊔ aleph0) ⊔ lengthStabSup K E σ

theorem diagramRawBound_mono (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) {σ τ : Cardinal.{u}}
    (hle : σ ≤ τ) : diagramRawBound K E σ ≤ diagramRawBound K E τ := by
  dsimp [diagramRawBound, lengthStabSup]
  haveI : Nonempty (Below (Order.succ (σ ⊔ aleph0))) := by simp [Below]
  haveI : Nonempty (Below (Order.succ (τ ⊔ aleph0))) := by simp [Below]
  refine sup_le_sup (sup_le_sup (Order.succ_le_succ (add_le_add le_rfl hle))
    (stableBound_mono K (sup_le_sup hle le_rfl))) (ciSup_le fun i => ?_)
  have hord : Order.succ (σ ⊔ aleph0) ≤ Order.succ (τ ⊔ aleph0) :=
    Order.succ_le_succ (sup_le_sup hle le_rfl)
  have hlt : (ToType.toOrd i).val < (Order.succ (τ ⊔ aleph0)).ord :=
    lt_of_lt_of_le (ToType.toOrd i).prop (Cardinal.ord_le_ord.mpr hord)
  let j : Below (Order.succ (τ ⊔ aleph0)) := ToType.mk ⟨(ToType.toOrd i).val, hlt⟩
  have hj : belowOrdCard i = belowOrdCard j := by
    dsimp [belowOrdCard, j]; simp [ToType.toOrd]
  exact hj ▸ le_ciSup (Cardinal.bddAbove_of_small
    (s := Set.range fun k : Below (Order.succ (τ ⊔ aleph0)) =>
      lengthStabAt K E (belowOrdCard k))) j

/-- Definable `t(σ)` of Proposition 4.2. -/
noncomputable def diagramThreshold (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u}) : Cardinal.{u} :=
  leastCategorical K (diagramRawBound K E σ)

theorem diagramThreshold_mono (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) {σ τ : Cardinal.{u}}
    (hle : σ ≤ τ) : diagramThreshold K E σ ≤ diagramThreshold K E τ :=
  leastCategorical_mono K (diagramRawBound_mono K E hle)

theorem diagramThreshold_categorical (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u}) :
    Categorical K (diagramThreshold K E σ) :=
  (leastCategorical_mem K (diagramRawBound K E σ)).2

theorem diagramThreshold_above_raw (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u}) :
    diagramRawBound K E σ ≤ diagramThreshold K E σ :=
  (leastCategorical_mem K (diagramRawBound K E σ)).1

theorem diagramThreshold_above_tau (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (_hσ : aleph0 ≤ σ) :
    K.τ.card + σ < diagramThreshold K E σ :=
  (Order.lt_succ _).trans_le <|
    (le_sup_of_le_left (le_sup_of_le_left (le_rfl : Order.succ (K.τ.card + σ) ≤ _))).trans
      (diagramThreshold_above_raw K E σ)

theorem diagramThreshold_ge_stableBound (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u}) :
    stableBound K (σ ⊔ aleph0) ≤ diagramThreshold K E σ :=
  (le_sup_of_le_left (le_sup_of_le_right (le_rfl : _ ≤ _))).trans
    (diagramThreshold_above_raw K E σ)

theorem diagramThreshold_ge_lengthStabAt (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) :
    lengthStabAt K E σ ≤ diagramThreshold K E σ := by
  haveI : Nonempty (Below (Order.succ (σ ⊔ aleph0))) := by simp [Below]
  have hraw := diagramThreshold_above_raw K E σ
  let ν := σ ⊔ aleph0
  let i : Below (Order.succ ν) := codeOfNum (le_sup_left : σ ≤ ν)
  have hc : belowOrdCard i = σ := belowOrdCard_codeOfNum _
  have hterm : lengthStabAt K E (belowOrdCard i) ≤ lengthStabSup K E σ :=
    le_ciSup (Cardinal.bddAbove_of_small
      (s := Set.range fun j : Below (Order.succ ν) => lengthStabAt K E (belowOrdCard j))) i
  exact ((hc ▸ le_rfl : lengthStabAt K E σ ≤ lengthStabAt K E (belowOrdCard i)).trans
    (hterm.trans le_sup_right)).trans hraw

theorem diagramThreshold_ge_ls (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u}) :
    ls K ≤ diagramThreshold K E σ := by
  have h := diagramThreshold_ge_stableBound K E σ
  have : ls K ≤ stableBound K (σ ⊔ aleph0) :=
    (stableBound_ready K (σ ⊔ aleph0) le_sup_right).1.trans' (le_max_left _ _)
  exact this.trans h

theorem diagramThreshold_ge_succ_sigma (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u}) :
    Order.succ σ ≤ diagramThreshold K E σ := by
  have h := diagramThreshold_ge_stableBound K E σ
  have hsb := (stableBound_ready K (σ ⊔ aleph0) le_sup_right).1
  have : Order.succ σ ≤ stableBound K (σ ⊔ aleph0) :=
    (Order.succ_le_succ le_sup_left).trans ((le_max_right _ _).trans hsb)
  exact this.trans h

/-- Projection injectivity for all cat pairs past `diagramThreshold`. -/
theorem projection_injective_past_threshold (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) {κ γ : Cardinal.{u}}
    (hκ : diagramThreshold K E σ ≤ κ) (hκγ : κ ≤ γ)
    (hcatκ : Categorical K κ) (hcatγ : Categorical K γ) :
    ProjectionInjective K σ κ γ := by
  let hex := exists_proj_stabilization K E (σ ⊔ aleph0) le_sup_right
  have hle : Classical.choose hex ≤ κ :=
    (le_sup_left.trans (diagramThreshold_ge_lengthStabAt K E σ hσ)).trans hκ
  obtain ⟨_, _, hinj⟩ := Classical.choose_spec hex
  have hinj' : ProjectionInjective K (σ ⊔ aleph0) κ γ :=
    hinj κ γ hle hκγ hcatκ hcatγ
  intro α M N hα xs ys hγM hγN hsame
  exact hinj' (hα.trans le_sup_left) xs ys hγM hγN hsame

/-- Reversal at length `σ` past `diagramThreshold`. -/
theorem reversal_at_diagramThreshold (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (σ : Cardinal.{u}) :
    ReversalProperty K σ (diagramThreshold K E σ) := by
  have hβ := diagramThreshold_ge_stableBound K E σ
  have hrev :=
    (readyAt K (σ ⊔ aleph0) (diagramThreshold K E σ) le_sup_right hβ
      (diagramThreshold_categorical K E σ)).2.1
  intro M f ι xs hM hcM hf hι
  exact hrev M f xs hM hcM hf (hι.trans le_sup_left)

/-- Restrict a diagram equality along `Sum.inl`. -/
theorem sameDiagramAt_comp_inl (K : AbstractElementaryClass.{u}) (κ : Cardinal.{u})
    {α γ : Type u} {M N : Model K.τ}
    (ac : α ⊕ γ → M.carrier) (bd : α ⊕ γ → N.carrier)
    (h : SameDiagramAt K κ ac bd) :
    SameDiagramAt K κ (fun i => ac (Sum.inl i)) (fun i => bd (Sum.inl i)) := by
  obtain ⟨A, B, fA, fB, xA, yB, hA, hB, hfA, hfB, hcA, hcB, hxA, hyB, ⟨e, he, het⟩⟩ := h
  exact ⟨A, B, fA, fB, fun i => xA (Sum.inl i), fun i => yB (Sum.inl i),
    hA, hB, hfA, hfB, hcA, hcB, fun i => hxA (Sum.inl i), fun i => hyB (Sum.inl i),
    ⟨e, he, fun i => het (Sum.inl i)⟩⟩

/-- **Proposition 4.2** (Stable diagrams). -/
theorem proposition_4_2 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K] :
    ∃ D : StableDiagram K,
      (∀ {σ : Cardinal.{u}} {α : Type u} {M N : Model K.τ} (hα : #α ≤ σ)
          (hM : K.Mem M) (hN : K.Mem N)
          (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N)
          (xs : α → M.carrier) (ys : α → N.carrier)
          (f : Language.Embedding K.τ M.carrier N.carrier),
          aleph0 ≤ σ → K.Strong f → (∀ i, f (xs i) = ys i) →
          D.same hα hM hN hMcard hNcard xs ys) ∧
      (∀ {σ : Cardinal.{u}} {α : Type u} {M N : Model K.τ} (hα : #α ≤ σ)
          (hM : K.Mem M) (hN : K.Mem N)
          (xs : α → M.carrier) (ys : α → N.carrier),
          aleph0 ≤ σ → Categorical K (Model.card M) →
          Model.card M = Model.card N →
          (hMcard : D.t σ ≤ Model.card M) → (hNcard : D.t σ ≤ Model.card N) →
          D.same hα hM hN hMcard hNcard xs ys →
          ∃ f : Language.Embedding K.τ M.carrier N.carrier,
            K.Strong f ∧ ∀ i, f (xs i) = ys i) ∧
      (∀ {σ : Cardinal.{u}} {α γ : Type u} {M N : Model K.τ}
          (hαγ : #(α ⊕ γ) ≤ σ) (hα : #α ≤ σ)
          (hM : K.Mem M) (hN : K.Mem N)
          (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N)
          (ac : α ⊕ γ → M.carrier) (a : α → N.carrier),
          aleph0 ≤ σ → Categorical K (Model.card N) →
          D.same hαγ hM hM hMcard hMcard ac ac →
          D.same hα hM hN hMcard hNcard (fun i => ac (Sum.inl i)) a →
          ∃ (Q : Model K.τ) (f : Language.Embedding K.τ N.carrier Q.carrier)
            (c : γ → Q.carrier) (hQ : K.Mem Q) (hQcard : D.t σ ≤ Model.card Q),
            K.Strong f ∧
            D.same hαγ hM hQ hMcard hQcard ac (Sum.elim (fun i => f (a i)) c)) := by
  classical
  obtain ⟨E, _, _⟩ := exists_orderPresentation_of_categoricalUnbounded K
  let tFun := diagramThreshold K E
  have ht_cat (σ) : Categorical K (tFun σ) := diagramThreshold_categorical K E σ
  have hlsθ (σ) : ls K ≤ tFun σ := diagramThreshold_ge_ls K E σ
  have hinfθ (σ) : aleph0 ≤ tFun σ := (isLSBound_ls K).1.trans (hlsθ σ)
  have hσle (σ) : σ ≤ tFun σ :=
    (Order.le_succ σ).trans (diagramThreshold_ge_succ_sigma K E σ)
  have hrevθ (σ) : ReversalProperty K σ (tFun σ) :=
    reversal_at_diagramThreshold K E σ
  have hrevθ' (σ) : ReversalProperty K (σ ⊔ aleph0) (tFun σ) :=
    (readyAt K (σ ⊔ aleph0) (tFun σ) le_sup_right
      (diagramThreshold_ge_stableBound K E σ) (ht_cat σ)).2.1
  let D : StableDiagram K := {
    t := tFun
    mono := fun _ _ h => diagramThreshold_mono K E h
    above := fun σ hσ => diagramThreshold_above_tau K E σ hσ
    categoricity := fun σ _ => ht_cat σ
    same := fun {σ α M N} hα hM hN hMc hNc xs ys => SameDiagramAt K (tFun σ) xs ys
    refl := fun {σ α M} hα hM hcard xs =>
      sameDiagramAt_refl K (tFun σ) (hlsθ σ) (hinfθ σ) hM hcard xs (hα.trans (hσle σ))
    symm := fun {σ α M N} hα hM hN _ _ xs ys h =>
      sameDiagramAt_symm K (tFun σ) (σ ⊔ aleph0) (ht_cat σ) (hrevθ' σ)
        (hα.trans le_sup_left) xs ys h
    preserves_atomic := fun {_ α M N} _ _ _ _ _ xs ys h =>
      sameDiagramAt_preserves_eq K (tFun _) xs ys h
  }
  refine ⟨D, ?_, ?_, ?_⟩
  · -- (1) strong embeddings preserve diagrams
    intro σ α M N hα hM hN hMc _ xs ys f _ hf het
    have hrefl := sameDiagramAt_refl K (tFun σ) (hlsθ σ) (hinfθ σ) hM hMc xs
      (hα.trans (hσle σ))
    simpa [D, het] using sameDiagramAt_of_strong_image K (tFun σ) xs f hf hrefl
  · -- (2) equal diagrams at equal categoricity size ⇒ strong map
    intro σ α M N hα hM hN xs ys hσ hcat hc hMc _ hsame
    have hready := readyAt K (σ ⊔ aleph0) (Model.card M) le_sup_right
      ((diagramThreshold_ge_stableBound K E σ).trans hMc) hcat
    have hlsM : ls K ≤ Model.card M := (le_max_left _ _).trans hready.1
    have hrevM : ReversalProperty K σ (Model.card M) :=
      fun M' f _ xs' hM' hcM' hf hι =>
        hready.2.1 M' f xs' hM' hcM' hf (hι.trans le_sup_left)
    have hinj : ProjectionInjective K σ (tFun σ) (Model.card M) :=
      projection_injective_past_threshold K E σ hσ le_rfl hMc (ht_cat σ) hcat
    have hsameκ : SameDiagramAt K (Model.card M) xs ys :=
      hinj hα xs ys (le_of_eq rfl) (le_of_eq hc) hsame
    exact sameDiagramAt_to_strong K (Model.card M) σ hcat hlsM hrevM
      hM hN rfl (by rw [← hc]) hα xs ys hsameκ
  · -- (3) realize joint diagram over a matching parameter tuple
    intro σ α γ M N hαγ hα hM hN hMc hNc ac a hσ _ hsameAC hsameA
    let θ := tFun σ
    have hαγθ : #(α ⊕ γ) ≤ θ := hαγ.trans (hσle σ)
    have hαθ : #α ≤ θ := hα.trans (hσle σ)
    obtain ⟨M₀, f₀, hM₀, hf₀, hcM₀, hhitM⟩ :=
      exists_strong_hull_of_tuple K θ (hlsθ σ) (hinfθ σ) M hM hMc ac hαγθ
    let xac : α ⊕ γ → M₀.carrier := fun i => Classical.choose (hhitM i)
    have hxac : ∀ i, f₀ (xac i) = ac i := fun i => Classical.choose_spec (hhitM i)
    have hAc_xac : SameDiagramAt K θ ac xac := by
      have himg : SameDiagramAt K θ xac (fun i => f₀ (xac i)) :=
        sameDiagramAt_of_strong_image K θ xac f₀ hf₀
          (sameDiagramAt_refl K θ (hlsθ σ) (hinfθ σ) hM₀ (le_of_eq hcM₀.symm) xac hαγθ)
      have himg' : SameDiagramAt K θ xac ac := by simpa [hxac] using himg
      exact sameDiagramAt_symm K θ (σ ⊔ aleph0) (ht_cat σ) (hrevθ' σ)
        (hαγ.trans le_sup_left) xac ac himg'
    obtain ⟨N₀, g₀, hN₀, hg₀, hcN₀, hhitN⟩ :=
      exists_strong_hull_of_tuple K θ (hlsθ σ) (hinfθ σ) N hN hNc a hαθ
    let xa : α → N₀.carrier := fun i => Classical.choose (hhitN i)
    have hxa : ∀ i, g₀ (xa i) = a i := fun i => Classical.choose_spec (hhitN i)
    have ha_xa : SameDiagramAt K θ a xa := by
      have himg : SameDiagramAt K θ xa (fun i => g₀ (xa i)) :=
        sameDiagramAt_of_strong_image K θ xa g₀ hg₀
          (sameDiagramAt_refl K θ (hlsθ σ) (hinfθ σ) hN₀ (le_of_eq hcN₀.symm) xa hαθ)
      have himg' : SameDiagramAt K θ xa a := by simpa [hxa] using himg
      exact sameDiagramAt_symm K θ (σ ⊔ aleph0) (ht_cat σ) (hrevθ' σ)
        (hα.trans le_sup_left) xa a himg'
    have hα_match : SameDiagramAt K θ (fun i => xac (Sum.inl i)) xa :=
      sameDiagramAt_trans K θ (σ ⊔ aleph0) (ht_cat σ) (hlsθ σ) (hrevθ' σ) hM
        (hα.trans le_sup_left)
        (fun i => xac (Sum.inl i)) (fun i => ac (Sum.inl i)) xa
        (sameDiagramAt_symm K θ (σ ⊔ aleph0) (ht_cat σ) (hrevθ' σ)
          (hα.trans le_sup_left) (fun i => ac (Sum.inl i)) (fun i => xac (Sum.inl i))
          (sameDiagramAt_comp_inl K θ ac xac hAc_xac))
        (sameDiagramAt_trans K θ (σ ⊔ aleph0) (ht_cat σ) (hlsθ σ) (hrevθ' σ) hN
          (hα.trans le_sup_left)
          (fun i => ac (Sum.inl i)) a xa hsameA ha_xa)
    have hstr : SameStrongClass K (fun i => xac (Sum.inl i)) xa :=
      sameDiagramAt_to_strong K θ σ (ht_cat σ) (hlsθ σ) (hrevθ σ)
        hM₀ hN₀ hcM₀ hcN₀ hα (fun i => xac (Sum.inl i)) xa hα_match
    obtain ⟨e, he, het⟩ := hstr
    let c₀ : γ → N₀.carrier := fun j => e (xac (Sum.inr j))
    have he_full : ∀ i, e (xac i) = Sum.elim xa c₀ i := by
      intro i; cases i with
      | inl i => exact het i
      | inr j => rfl
    have hjoint : SameDiagramAt K θ xac (Sum.elim xa c₀) :=
      sameDiagramAt_of_sameStrongClass K θ hM₀ hN₀ hcM₀ hcN₀ xac (Sum.elim xa c₀)
        ⟨e, he, he_full⟩
    let c : γ → N.carrier := fun j => g₀ (c₀ j)
    have hfinal : SameDiagramAt K θ ac (Sum.elim a c) := by
      have h1 : SameDiagramAt K θ ac (Sum.elim xa c₀) :=
        sameDiagramAt_trans K θ (σ ⊔ aleph0) (ht_cat σ) (hlsθ σ) (hrevθ' σ) hM₀
          (hαγ.trans le_sup_left) ac xac (Sum.elim xa c₀) hAc_xac hjoint
      have h2 : SameDiagramAt K θ (Sum.elim xa c₀) (Sum.elim a c) := by
        have himg : SameDiagramAt K θ (Sum.elim xa c₀)
            (fun i => g₀ (Sum.elim xa c₀ i)) :=
          sameDiagramAt_of_strong_image K θ (Sum.elim xa c₀) g₀ hg₀
            (sameDiagramAt_refl K θ (hlsθ σ) (hinfθ σ) hN₀ (le_of_eq hcN₀.symm)
              (Sum.elim xa c₀) hαγθ)
        have heq : (fun i => g₀ (Sum.elim xa c₀ i)) = Sum.elim a c := by
          funext i; cases i with
          | inl i => simp [Sum.elim, hxa]
          | inr j => simp [Sum.elim, c]
        simpa [heq] using himg
      exact sameDiagramAt_trans K θ (σ ⊔ aleph0) (ht_cat σ) (hlsθ σ) (hrevθ' σ) hN₀
        (hαγ.trans le_sup_left) ac (Sum.elim xa c₀) (Sum.elim a c) h1 h2
    refine ⟨N, Language.Embedding.refl K.τ N.carrier, c, hN, hNc,
      K.strong_refl N hN, ?_⟩
    simpa [D, Language.Embedding.refl_apply] using hfinal

/-- **Proposition 4.3** (Categoricity at countably cofinal closure points). A cardinal `ζ > ℓ`
of countable cofinality strictly above `t(σ)` for every infinite `σ < ζ` is a categoricity
cardinal, and a diagram match of bounded tuples extends to an isomorphism. -/
theorem proposition_4_3 (K : AbstractElementaryClass.{u}) (D : StableDiagram K)
    (ζ : Cardinal.{u}) (hζ : ls K < ζ) (hcof : Ordinal.cof ζ.ord = aleph0)
    (hclosed : ∀ σ, aleph0 ≤ σ → σ < ζ → D.t σ < ζ) :
    Categorical K ζ ∧
    ∀ {α : Type u} (M N : Model K.τ) (xs : α → M.carrier) (ys : α → N.carrier)
      (hM : K.Mem M) (hN : K.Mem N),
      #α < ζ → Model.card M = ζ → Model.card N = ζ →
      (∃ σ, ∃ hα : #α ≤ σ, ∃ _hσ : aleph0 ≤ σ,
          ∃ hMcard : D.t σ ≤ Model.card M, ∃ hNcard : D.t σ ≤ Model.card N,
        D.same hα hM hN hMcard hNcard xs ys) →
      ∃ e : M.carrier ≃[K.τ] N.carrier, ∀ i, e (xs i) = ys i := by
  sorry

/-- **Lemma 4.5** (Orbits over parameters). If `χ ^ σ = χ` and `χ` is at least `ℓ + 2^{2^σ}`,
then at every sufficiently large categoricity cardinal there are at most `χ` automorphism
orbits of `σ`-tuples over any parameter set of size at most `χ`. -/
theorem lemma_4_5 (K : AbstractElementaryClass.{u}) (σ χ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hpow : χ ^ σ = χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) :
    ∃ κ0 : Cardinal.{u}, ∀ κ, κ0 ≤ κ → Categorical K κ →
      ∀ (M : Model K.τ), K.Mem M → Model.card M = κ →
        ∀ P : Set M.carrier, #P ≤ χ →
          ∀ {ι : Type u}, #ι ≤ σ →
            ∃ reps : Set (ι → M.carrier), #reps ≤ χ ∧
              ∀ xs : ι → M.carrier, ∃ ys ∈ reps,
                ∃ e : M.carrier ≃[K.τ] M.carrier,
                  K.Strong e.toEmbedding ∧ (∀ p ∈ P, e p = p) ∧ ∀ i, e (xs i) = ys i := by
  sorry

/-- A family of disjoint adjacent block pairs, swapped by an order automorphism and fixing
every position outside those blocks. **Lemma 4.6.** -/
structure DisjointBlockSwap (I : Type u) [LinearOrder I] where
  swap : I ≃o I
  blocks : Set (Set I × Set I)
  disjoint : ∀ p ∈ blocks, ∀ q ∈ blocks, p = q ∨
    Disjoint p.1 q.1 ∧ Disjoint p.1 q.2 ∧ Disjoint p.2 q.1 ∧ Disjoint p.2 q.2
  leftBeforeRight : ∀ p ∈ blocks, ∀ a ∈ p.1, ∀ b ∈ p.2, a < b
  convex : ∀ p ∈ blocks,
    (∀ a c b, a ∈ p.1 → c ∈ p.1 → a ≤ b → b ≤ c → b ∈ p.1) ∧
    (∀ a c b, a ∈ p.2 → c ∈ p.2 → a ≤ b → b ≤ c → b ∈ p.2) ∧
    (∀ x, (∃ a ∈ p.1, ∃ b ∈ p.2, a ≤ x ∧ x ≤ b) → x ∈ p.1 ∨ x ∈ p.2)
  swaps : ∀ p ∈ blocks, swap '' p.1 = p.2 ∧ swap '' p.2 = p.1
  fixes : ∀ i, (∀ p ∈ blocks, i ∉ p.1 ∧ i ∉ p.2) → swap i = i

/-- **Lemma 4.6** (Disjoint block transpositions). Swapping, in each of a family of disjoint
convex regions, the adjacent block used only by the first term family with the block used
only by the second, leaves the joint natural diagram unchanged. -/
theorem lemma_4_6 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) {I : Type u} [LinearOrder I] [Nonempty I]
    {α β : Type u} (σ : Cardinal.{u}) (hjoint : #(α ⊕ β) ≤ σ)
    (t : α → SupportTerm E.lab E.arity I) (s : β → SupportTerm E.lab E.arity I)
    (B : DisjointBlockSwap I)
    (ht : ∀ a (i : Fin (E.arity (t a).label)) p, p ∈ B.blocks →
      (t a).pos i ∈ p.1 ∨ (t a).pos i ∈ p.2 → (t a).pos i ∈ p.1)
    (hs : ∀ b (i : Fin (E.arity (s b).label)) p, p ∈ B.blocks →
      (s b).pos i ∈ p.1 ∨ (s b).pos i ∈ p.2 → (s b).pos i ∈ p.2) :
    SameNaturalDiagram K E D σ hjoint (Sum.elim t s)
      (Sum.elim (fun a => SupportTerm.along B.swap.toOrderEmbedding (t a))
        (fun b => SupportTerm.along B.swap.toOrderEmbedding (s b))) := by
  sorry

/-- **Lemma 4.7** (Ordinal-vector witnesses). Let `C` be a set, and let `U` be a definable
class of functions `C → Ord`, with fixed set parameters allowed in its definition. There is a
set `U₀ ⊆ U` such that each `u ∈ U` dominates some `v ∈ U₀` coordinatewise. -/
theorem lemma_4_7 {C parameter : Type u}
    (holds : parameter → (C → _root_.Ordinal.{u}) → Prop) (a : parameter) :
    ∃ (ι : Type u) (v : ι → C → _root_.Ordinal.{u}),
      (∀ i, holds a (v i)) ∧
      ∀ f, holds a f → ∃ i, ∀ c, v i c ≤ f c := by
  sorry

/-- **Proposition 4.8** (Uniform testing of placed comparisons). There is a nondecreasing
infinite cardinal function `g` such that two placements of a tuple of length at most `σ`
over `E(I)` whose placed comparisons differ already have different natural diagrams over some
parameter set of size at most `g(σ)`. -/
theorem proposition_4_8 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) :
    ∃ g : Cardinal.{u} → Cardinal.{u},
      (∀ σ τ, σ ≤ τ → g σ ≤ g τ) ∧ (∀ σ, aleph0 ≤ g σ) ∧
      ∀ {I : Type u} [LinearOrder I] [Nonempty I] [WellFoundedLT I]
        {α : Type u} (σ : Cardinal.{u}) (hσ : #α ≤ σ)
        (t s : α → SupportTerm E.lab E.arity I),
        ¬ SameNaturalDiagram K E D σ hσ t s →
        ∃ X : Set I, ∃ hX : X.Nonempty, #X ≤ g σ ∧
          DiagramsDifferOnSubset K E D σ hσ X hX := by
  sorry

/-- **Proposition 4.9** (Compact placement). Coherent prescriptions of joint diagrams of a
tuple of length at most `σ` with every parameter set of size at most `χ`, where
`χ ^ σ = χ` and `χ > ℓ + σ`, are realized by one placement over `I`. -/
theorem proposition_4_9 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) {I : Type u} [LinearOrder I] [Nonempty I] [WellFoundedLT I]
    {α : Type u} (σ χ : Cardinal.{u}) (hσ : #α ≤ σ) (hχ : ls K + σ < χ)
    (hpow : χ ^ σ = χ) (hI : K.Mem (E.obj I))
    (q : ∀ {β : Type u}, #β ≤ χ → (β → (E.obj I).carrier) → α ⊕ β → (E.obj I).carrier) :
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (f : I ↪o J)
      (z : α → (E.obj J).carrier) (hJ : K.Mem (E.obj J)),
      ∀ {β : Type u} (hβ : #β ≤ χ) (p : β → (E.obj I).carrier)
        (hjoint : #(α ⊕ β) ≤ σ + χ)
        (hcardI : D.t (σ + χ) ≤ Model.card (E.obj I))
        (hcardJ : D.t (σ + χ) ≤ Model.card (E.obj J)),
        D.same hjoint hJ hJ hcardJ hcardJ
          (Sum.elim z (fun b => E.map f (p b)))
          (Sum.elim (fun a => E.map f (q hβ p (Sum.inl a)))
            (fun b => E.map f (q hβ p (Sum.inr b)))) := by
  sorry

/-- **Lemma 4.10** (Unique lifts of bounded diagrams). At a strong limit `μ > ℓ` of countable
cofinality strictly closed under `t` and `g`, the diagrams of a bounded tuple in `B` over
bounded subsets of `A = E(I)` lift to one placed comparison over `A`, uniquely as a comparison
diagram. -/
theorem lemma_4_10 (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) (g : Cardinal.{u} → Cardinal.{u})
    (μ σ : Cardinal.{u}) (hμ : IsClosurePoint {D.t, g} μ) (hσ : σ < μ)
    (hℓ : ls K < μ) {I : Type u} [LinearOrder I] [Nonempty I] [WellFoundedLT I]
    (hI : #I = μ) (Aeq : K.Mem (E.obj I))
    (B : Model K.τ) (incl : Language.Embedding K.τ (E.obj I).carrier B.carrier)
    (hB : K.Mem B) (hstrong : K.Strong incl) (hcard : Model.card B = μ)
    {α : Type u} (d : α → B.carrier) (hα : #α ≤ σ) :
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (f : I ↪o J)
      (z : α → (E.obj J).carrier) (hJ : K.Mem (E.obj J)),
      (∀ {β : Type u} (p : β → (E.obj I).carrier)
          (hjoint : #(α ⊕ β) ≤ μ)
          (hBcard : D.t μ ≤ Model.card B) (hJcard : D.t μ ≤ Model.card (E.obj J)),
          D.same hjoint hB hJ hBcard hJcard
            (Sum.elim d (fun b => incl (p b)))
            (Sum.elim z (fun b => E.map f (p b)))) ∧
      ∀ {J' : Type u} [LinearOrder J'] [Nonempty J'] (f' : I ↪o J')
        (z' : α → (E.obj J').carrier) (hJ' : K.Mem (E.obj J')),
        (∀ {β : Type u} (p : β → (E.obj I).carrier)
            (hjoint : #(α ⊕ β) ≤ μ)
            (hBcard : D.t μ ≤ Model.card B) (hJcard : D.t μ ≤ Model.card (E.obj J')),
            D.same hjoint hB hJ' hBcard hJcard
              (Sum.elim d (fun b => incl (p b)))
              (Sum.elim z' (fun b => E.map f' (p b)))) →
        ∀ {β : Type u} (p : β → (E.obj I).carrier)
          (hjoint : #(α ⊕ β) ≤ μ)
          (hJcard : D.t μ ≤ Model.card (E.obj J))
          (hJ'card : D.t μ ≤ Model.card (E.obj J')),
          D.same hjoint hJ hJ' hJcard hJ'card
            (Sum.elim z (fun b => E.map f (p b)))
            (Sum.elim z' (fun b => E.map f' (p b))) := by
  sorry

/-- **Theorem 4.11** (Amalgamation at closed levels). An unbounded class of strong-limit
cardinals of countable cofinality, strictly closed under `t` and `g`, consists of
categoricity cardinals at which `μ`-extensions of a `μ`-model amalgamate, tuples amalgamate
exactly when their diagrams agree up to `g(σ)`, and there are at most `μ` singleton types. -/
theorem theorem_4_11 (K : AbstractElementaryClass.{u}) (D : StableDiagram K)
    (g : Cardinal.{u} → Cardinal.{u}) (hg : ∀ σ τ, σ ≤ τ → g σ ≤ g τ) :
    ∃ S : Set Cardinal.{u},
      (∀ κ, ∃ μ, κ ≤ μ ∧ μ ∈ S) ∧
      (∀ μ ∈ S, IsClosurePoint {D.t, g} μ) ∧
      ∀ μ ∈ S,
        Categorical K μ ∧
        (∀ (A B₀ B₁ : Model K.τ)
            (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
            (f₁ : Language.Embedding K.τ A.carrier B₁.carrier),
            K.Mem A → K.Mem B₀ → K.Mem B₁ → K.Strong f₀ → K.Strong f₁ →
            Model.card A = μ → Model.card B₀ = μ → Model.card B₁ = μ →
            ∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
              (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
              K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧ Model.card P = μ ∧
              ∀ x, g₀ (f₀ x) = g₁ (f₁ x)) ∧
        (∀ σ, σ < μ → ∀ {α β : Type u} (hα : #α ≤ σ) (_hβ : #β ≤ g σ)
            (A B₀ B₁ : Model K.τ)
            (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
            (f₁ : Language.Embedding K.τ A.carrier B₁.carrier)
            (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier)
            (hA : K.Mem A) (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁),
            K.Strong f₀ → K.Strong f₁ →
            Model.card A = μ → Model.card B₀ = μ → Model.card B₁ = μ →
            ((∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
                (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
                K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧
                (∀ x, g₀ (f₀ x) = g₁ (f₁ x)) ∧ ∀ i, g₀ (d₀ i) = g₁ (d₁ i)) ↔
              (∀ (p : β → A.carrier) (hjoint : #(α ⊕ β) ≤ μ)
                  (h₀ : D.t μ ≤ Model.card B₀) (h₁ : D.t μ ≤ Model.card B₁),
                D.same hjoint hB₀ hB₁ h₀ h₁
                  (Sum.elim d₀ (fun b => f₀ (p b)))
                  (Sum.elim d₁ (fun b => f₁ (p b)))))) ∧
        (∀ (A : Model K.τ), K.Mem A → Model.card A = μ →
          ∃ code : A.carrier → μ.ord.ToType,
            ∀ x y, code x = code y ↔
              ∃ (P : Model K.τ) (g₀ g₁ : Language.Embedding K.τ A.carrier P.carrier),
                K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧
                (∀ a, g₀ a = g₁ a) ∧ g₀ x = g₁ y) := by
  sorry

end
end AEC
