module

public import AEC.Section4.BoundedDiagramLift
public import AEC.Section2.DirectedLimit

@[expose] public section

/-!
# Closed levels (Theorem 4.11, the class of levels)

The levels of Theorem 4.11 are the strong-limit cardinals `μ > ℓ` of countable cofinality
strictly closed under the threshold function `t` of Proposition 4.2 and a testing bound `g` of
Proposition 4.8 (`IsClosurePoint {D.t, g} μ`).

* `exists_closurePoint_ge`: such levels are unbounded, by the countable closure construction
  after Proposition 4.3: iterate `κ ↦ (2 ^ κ ⊔ sup_{θ ≤ κ} (t θ ⊔ g θ))⁺` countably often and
  take the supremum. No monotonicity of `t` or `g` is used.
* `categorical_of_closurePoint`: `K` is categorical at such a level (Proposition 4.3).
* `exists_strong_of_nat_exhaustion`: a model which is the union of a countable increasing
  family of strong submodels maps strongly into `G` as soon as the submodels do, coherently
  (the chain and common-upper-bound axioms, through `directLimit_in_class`).
* `StableDiagram.exists_transport`: Proposition 4.2 at a categoricity cardinal `γ = ‖G‖`: a
  diagram match between a tuple of a model `M`, `‖M‖ ≥ γ`, and a tuple of `G` is implemented
  by a strong map into `G` of a strong `γ`-submodel of `M` containing any prescribed further
  tuple of length at most `γ`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

/-! ## Unboundedness of the closure points -/

section ClosurePoints

variable (t g : Cardinal.{u} → Cardinal.{u})

/-- A bound for the values of `t` and `g` at the cardinals up to `κ`. -/
noncomputable def closureBound (κ : Cardinal.{u}) : Cardinal.{u} :=
  ⨆ θ : Set.Iic κ, t θ.1 ⊔ g θ.1

theorem le_closureBound {θ κ : Cardinal.{u}} (h : θ ≤ κ) :
    t θ ⊔ g θ ≤ closureBound t g κ :=
  le_ciSup (f := fun θ : Set.Iic κ => t θ.1 ⊔ g θ.1) bddAbove_of_small ⟨θ, h⟩

/-- The countable closure construction after Proposition 4.3: iterate the power set and the
bounds for `t` and `g` above `κ`. -/
noncomputable def closureTower (κ : Cardinal.{u}) : ℕ → Cardinal.{u}
  | 0 => max κ ℵ₀
  | n + 1 => Order.succ (2 ^ closureTower κ n ⊔ closureBound t g (closureTower κ n))

theorem closureTower_strictMono (κ : Cardinal.{u}) : StrictMono (closureTower t g κ) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  exact ((cantor (closureTower t g κ n)).trans_le le_sup_left).trans (Order.lt_succ _)

theorem closureTower_le_iSup (κ : Cardinal.{u}) (n : ℕ) :
    closureTower t g κ n ≤ ⨆ n, closureTower t g κ n :=
  le_ciSup (f := closureTower t g κ) bddAbove_of_small n

/-- A strictly increasing `ω`-sequence of ordinals has a supremum of cofinality `ℵ₀`. -/
theorem cof_iSup_nat_of_strictMono (f : ℕ → Ordinal.{u}) (hf : StrictMono f) :
    Ordinal.cof (⨆ n, f n) = ℵ₀ := by
  have h := Ordinal.lift_cof_iSup (β := ℕ) (f := f) hf
  rw [Order.cof_nat, Cardinal.lift_uzero, Cardinal.lift_aleph0] at h
  exact h

/-- The supremum of the closure tower is a strong limit of countable cofinality. -/
theorem closureTower_iSup_isWorkingLevel (κ : Cardinal.{u}) :
    IsWorkingLevel (⨆ n, closureTower t g κ n) := by
  have hinf : ℵ₀ ≤ ⨆ n, closureTower t g κ n :=
    (le_max_right κ ℵ₀).trans (closureTower_le_iSup t g κ 0)
  refine ⟨hinf, ⟨(aleph0_pos.trans_le hinf).ne', fun x hx => ?_⟩, ?_⟩
  · obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := closureTower t g κ) bddAbove_of_small).mp hx
    have h2 : (2 : Cardinal.{u}) ≠ 0 := two_ne_zero
    exact (power_le_power_left h2 hn.le).trans_lt
      (((le_sup_left : (2 : Cardinal.{u}) ^ closureTower t g κ n ≤ _).trans_lt
        (Order.lt_succ _)).trans_le (closureTower_le_iSup t g κ (n + 1)))
  · rw [Ordinal.iSup_ord]
    exact cof_iSup_nat_of_strictMono (fun n => (closureTower t g κ n).ord)
      fun a b hab => ord_lt_ord.mpr (closureTower_strictMono t g κ hab)

/-- The supremum of the closure tower is strictly closed under `t` and `g`. -/
theorem closureTower_iSup_closed (κ θ : Cardinal.{u})
    (hθ : θ < ⨆ n, closureTower t g κ n) :
    t θ ⊔ g θ < ⨆ n, closureTower t g κ n := by
  obtain ⟨n, hn⟩ := (lt_ciSup_iff' (f := closureTower t g κ) bddAbove_of_small).mp hθ
  exact ((le_closureBound t g hn.le).trans le_sup_right).trans_lt
    ((Order.lt_succ _).trans_le (closureTower_le_iSup t g κ (n + 1)))

/-- **The closure points are unbounded** (the countable closure construction after
Proposition 4.3). -/
theorem exists_closurePoint_ge (κ : Cardinal.{u}) :
    ∃ μ, κ ≤ μ ∧ IsClosurePoint {t, g} μ := by
  refine ⟨⨆ n, closureTower t g κ n,
    (le_max_left κ ℵ₀).trans (closureTower_le_iSup t g κ 0),
    closureTower_iSup_isWorkingLevel t g κ, ?_⟩
  intro u hu
  refine ⟨fun θ _ hθ => ?_⟩
  have h := closureTower_iSup_closed t g κ θ hθ
  rcases hu with rfl | hu
  · exact le_sup_left.trans_lt h
  · rw [Set.mem_singleton_iff] at hu
    subst hu
    exact le_sup_right.trans_lt h

end ClosurePoints

variable {K : AbstractElementaryClass.{u}}

/-- **Proposition 4.3 at a closure point.** `K` is categorical at every closure point above
`ℓ`. -/
theorem categorical_of_closurePoint [CategoricalUnbounded K] (D : StableDiagram K)
    {g : Cardinal.{u} → Cardinal.{u}} {μ : Cardinal.{u}} (hμ : IsClosurePoint {D.t, g} μ)
    (hℓ : ls K < μ) : Categorical K μ := by
  haveI : ArbitrarilyLarge K := arbitrarilyLarge_of_categoricalUnbounded K
  exact (prop43_hull_back_and_forth K D μ hℓ hμ.working.countableCof fun σ hσ hσμ =>
    (hμ.closed D.t (Set.mem_insert _ _)).below σ hσ hσμ).1

/-! ## Countable unions of strong submodels -/

/-- Coherence, for a factor through a strong map. -/
theorem strong_factorEmbedding {M₀ M₁ M₂ : Model K.τ}
    (f₀₂ : Language.Embedding K.τ M₀.carrier M₂.carrier)
    (f₁₂ : Language.Embedding K.τ M₁.carrier M₂.carrier)
    (hf₀₂ : K.Strong f₀₂) (hf₁₂ : K.Strong f₁₂) (himg : ∀ x, ∃ y, f₁₂ y = f₀₂ x) :
    K.Strong (factorEmbedding f₀₂ f₁₂ himg) :=
  K.coherence (factorEmbedding f₀₂ f₁₂ himg) f₀₂ f₁₂ hf₀₂ hf₁₂
    (factorEmbedding_comp f₀₂ f₁₂ himg)

theorem factorEmbedding_apply {L : Tau.{u}} {A B C : Type u}
    [L.Structure A] [L.Structure B] [L.Structure C]
    (f : A ↪[L] C) (g : B ↪[L] C) (himg : ∀ a, ∃ b, g b = f a) (a : A) :
    g (factorEmbedding f g himg a) = f a :=
  Classical.choose_spec (himg a)

/-- **A countable union of strong submodels maps strongly.** If `B` is the union of the
increasing strong submodels `j n : M n → B`, and the `M n` map strongly and coherently into
`G`, the union of these maps is a strong map `B → G` (chain and common-upper-bound axioms). -/
theorem exists_strong_of_nat_exhaustion {B G : Model K.τ} (hB : K.Mem B) (hG : K.Mem G)
    (M : ℕ → Model K.τ) (j : ∀ n, Language.Embedding K.τ (M n).carrier B.carrier)
    (hj : ∀ n, K.Strong (j n))
    (hmono : ∀ n x, ∃ y, j (n + 1) y = j n x)
    (hcov : ∀ b, ∃ n x, j n x = b)
    (h : ∀ n, Language.Embedding K.τ (M n).carrier G.carrier) (hh : ∀ n, K.Strong (h n))
    (hcoh : ∀ n x y, j (n + 1) y = j n x → h (n + 1) y = h n x) :
    ∃ F : Language.Embedding K.τ B.carrier G.carrier,
      K.Strong F ∧ ∀ n x, F (j n x) = h n x := by
  classical
  -- the submodels increase, and the maps cohere, along `n ≤ m`
  have hmono' : ∀ n m, n ≤ m → ∀ x, ∃ y, j m y = j n x := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact fun x => ⟨x, rfl⟩
    | succ m _ ih =>
      intro x
      obtain ⟨y, hy⟩ := ih x
      obtain ⟨y', hy'⟩ := hmono m y
      exact ⟨y', hy'.trans hy⟩
  have hcoh' : ∀ n m, n ≤ m → ∀ x y, j m y = j n x → h m y = h n x := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base =>
      intro x y hxy
      rw [(j n).injective hxy]
    | succ m hnm ih =>
      intro x y hxy
      obtain ⟨y', hy'⟩ := hmono' n m hnm x
      exact (hcoh m y' y (hxy.trans hy'.symm)).trans (ih x y' hy')
  -- the directed system of the submodels
  let S : DirectedSystem K.τ :=
    { ι := ULift.{u} ℕ
      nonempty := ⟨⟨0⟩⟩
      rel := fun a b => a.down ≤ b.down
      refl := fun a => le_rfl
      trans := fun hab hbc => le_trans hab hbc
      directed := fun a b => ⟨⟨max a.down b.down⟩, le_max_left _ _, le_max_right _ _⟩
      obj := fun a => M a.down
      map := fun {a b} hab => factorEmbedding (j a.down) (j b.down) (hmono' _ _ hab)
      map_refl := fun a => factorEmbedding_unique (j a.down) (j a.down) _ _
        (factorEmbedding_comp _ _ _) (by ext x; rfl)
      map_trans := fun {a b c} hab hbc => factorEmbedding_unique (j a.down) (j c.down) _ _
        (factorEmbedding_comp _ _ _) (by
          ext x
          simp only [Language.Embedding.comp_apply]
          rw [factorEmbedding_apply, factorEmbedding_apply]) }
  let U : DirectLimit S :=
    { obj := B
      canon := fun a => j a.down
      compat := fun {a b} hab => factorEmbedding_comp _ _ _
      joint := fun x => by
        obtain ⟨n, y, hy⟩ := hcov x
        exact ⟨⟨n⟩, y, hy⟩ }
  have hSmem : ∀ a, K.Mem (S.obj a) := fun a => K.strong_mem_dom _ (hj a.down)
  have hSstrong : ∀ {a b} (hab : S.rel a b), K.Strong (S.map hab) := fun {a b} hab =>
    strong_factorEmbedding _ _ (hj a.down) (hj b.down) _
  obtain ⟨L, hLmem, -, hLuniv⟩ := directLimit_in_class K S hSmem hSstrong
  obtain ⟨f, hf, hfc⟩ := hLuniv G (fun a => h a.down) hG (fun a => hh a.down)
    (fun {a b} hab => by
      ext x
      simp only [Language.Embedding.comp_apply]
      exact hcoh' a.down b.down hab x _ (factorEmbedding_apply _ _ _ x))
  let eL := directLimitEquivAlgebraic S L
  let eU := directLimitEquivAlgebraic S U
  have halg : K.Mem (algebraicLimit S).obj := K.iso_closed ⟨eU.symm⟩ hB
  refine ⟨f.comp (eL.toEmbedding.comp eU.symm.toEmbedding),
    K.strong_trans _ f (K.strong_trans _ _ (strong_of_equiv K eU.symm hB)
      (strong_of_equiv K eL halg)) hf, fun n x => ?_⟩
  have h1 : eU.symm (j n x) = (algebraicLimit S).canon ⟨n⟩ x := by
    apply eU.injective
    rw [Language.Equiv.apply_symm_apply]
    exact (directLimitEquivAlgebraic_canon S U ⟨n⟩ x).symm
  have h2 : eL ((algebraicLimit S).canon ⟨n⟩ x) = L.canon ⟨n⟩ x :=
    directLimitEquivAlgebraic_canon S L ⟨n⟩ x
  have h3 : f (L.canon ⟨n⟩ x) = h n x := by
    have := congrArg (fun φ : Language.Embedding K.τ (M n).carrier G.carrier => φ x)
      (hfc ⟨n⟩)
    simpa [Language.Embedding.comp_apply] using this
  simp only [Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding]
  rw [h1, h2, h3]

/-! ## Proposition 4.2 at a categoricity cardinal: transport into `G` -/

/-- **Proposition 4.2 at `γ = ‖G‖`.** Let `γ = ‖G‖ ≥ t(τ)` be a categoricity cardinal and
`‖M‖ ≥ γ`. If the tuples `xs` of `M` and `ys` of `G`, of length at most `τ`, have the same
diagram, a strong `γ`-submodel `N` of `M` containing `xs` and any further tuple `ws` of length
at most `γ` maps strongly into `G`, taking `xs` to `ys`. -/
theorem StableDiagram.exists_transport (D : StableDiagram K) {τ : Cardinal.{u}}
    {α β : Type u} {M G : Model K.τ} (hM : K.Mem M) (hG : K.Mem G) (hτ : aleph0 ≤ τ)
    (hα : #α ≤ τ) (hcat : Categorical K (Model.card G)) (hls : ls K ≤ Model.card G)
    (hGc : D.t τ ≤ Model.card G) (hMG : Model.card G ≤ Model.card M)
    (xs : α → M.carrier) (ys : α → G.carrier)
    (hsame : D.same hα hM hG (hGc.trans hMG) hGc xs ys)
    (ws : β → M.carrier) (hβ : #β ≤ Model.card G) :
    ∃ (N : Model K.τ) (i : Language.Embedding K.τ N.carrier M.carrier)
      (φ : Language.Embedding K.τ N.carrier G.carrier),
      K.Mem N ∧ Model.card N = Model.card G ∧ K.Strong i ∧ K.Strong φ ∧
      (∀ a, ∃ x, i x = xs a ∧ φ x = ys a) ∧ ∀ b, ∃ x, i x = ws b := by
  have hγinf : aleph0 ≤ Model.card G := (isLSBound_ls K).1.trans hls
  have hαγ : #α ≤ Model.card G := (hα.trans (sigma_lt_t D hτ).le).trans hGc
  have hT : #↥(Set.range xs ∪ Set.range ws) ≤ Model.card G := by
    refine (mk_union_le _ _).trans ?_
    have h := add_le_add ((mk_range_le (f := xs)).trans hαγ) ((mk_range_le (f := ws)).trans hβ)
    rwa [add_eq_self hγinf] at h
  obtain ⟨N, i, hN, hi, hcN, hcov⟩ :=
    exists_strong_hull_exact_card K (Model.card G) hls hγinf M hM hMG _ hT
  have hhit : ∀ a, ∃ x, i x = xs a := fun a => hcov _ (Or.inl ⟨a, rfl⟩)
  choose x₀ hx₀ using hhit
  have hNc : D.t τ ≤ Model.card N := hGc.trans hcN.ge
  have h1 : D.same hα hN hM hNc (hGc.trans hMG) x₀ xs :=
    D.of_strong hα hN hM hNc (hGc.trans hMG) x₀ xs i hτ hi hx₀
  have h2 : D.same hα hN hG hNc hGc x₀ ys :=
    D.trans hα hN hM hG hNc (hGc.trans hMG) hGc x₀ xs ys h1 hsame
  obtain ⟨φ, hφ, hφx⟩ := D.to_strong hα hN hG x₀ ys hτ (by rw [hcN]; exact hcat) hcN hNc hGc h2
  exact ⟨N, i, φ, hN, hcN, hi, hφ, fun a => ⟨x₀ a, hx₀ a, hφx a⟩,
    fun b => hcov _ (Or.inr ⟨b, rfl⟩)⟩

end
end AEC
