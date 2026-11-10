module

public import AEC.Section4.StableDiagramConstruction
public import AEC.Section2.DirectedLimit
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.Finset.Card

/-!
# Hull-based countable back-and-forth for Proposition 4.3

English (text.md): choose countable exhaustions of two `ζ`-models, and alternately extend a
bounded diagram match by putting the data on each side inside strong submodels of size
`t(σ) < ζ` and applying Proposition 4.2 there.

Unlike `StrongClassBAF`, no stage refers to a strong embedding of the full `ζ`-models (that
would presuppose what categoricity at `ζ` is meant to deliver). A stage is a partial match
`R ⊆ |M| × |N|` of size `< ζ` carried by one *common hull*: a model `A` of size `t(σ)` with
strong embeddings into both `M` and `N` (`HullMatch`).

* `StableDiagram.same_of_common_hull`: a common hull yields `D.same` in the ambient models.
* `StableDiagram.exists_common_hull`: `D.same` in the ambient models yields a common hull at
  any larger bound, containing any prescribed further small set (hulls + `D.to_strong`).
* `HullMatch.forth` / `HullMatch.back`: the extension steps.
* `exists_equiv_of_commonDomain_chain`: the union of a countable chain of common-domain
  partial matches exhausting both sides is a `Language.Equiv`.
* `prop43_hull_back_and_forth`: Proposition 4.3.
-/

@[expose] public section

namespace AEC
section

universe u

open Classical FirstOrder Cardinal Function Set

/-! ### Countable exhaustions of singular-cardinality carriers -/

theorem card_Iic_ord_lt {ζ : Cardinal.{u}} (hinf : aleph0 ≤ ζ) (i : ζ.ord.ToType) :
    #(Iic i) < ζ := by
  have htype : ord #(ζ.ord.ToType) = Ordinal.type (α := ζ.ord.ToType) (· < ·) := by
    rw [mk_ord_toType, Ordinal.type_toType]
  have hinf' : aleph0 ≤ #(ζ.ord.ToType) := by rwa [mk_ord_toType]
  simpa [mk_ord_toType] using mk_Iic_lt i htype hinf'

/-- Increasing countable exhaustion of a type of cardinality `ζ` when `cf(ζ)=ℵ₀`. -/
theorem exists_countable_set_exhaustion {X : Type u} {ζ : Cardinal.{u}}
    (hX : #X = ζ) (hinf : aleph0 ≤ ζ) (hcof : Ordinal.cof ζ.ord = aleph0) :
    ∃ (A : ℕ → Set X),
      (∀ n, #(A n) < ζ) ∧
      (∀ n, A n ⊆ A (n + 1)) ∧
      (∀ x, ∃ n, x ∈ A n) := by
  classical
  let α := ζ.ord.ToType
  have hαcard : #α = ζ := by simpa [α] using mk_ord_toType ζ
  have hcofα : Order.cof α = aleph0 := by
    simpa [α, Ordinal.cof_toType] using hcof
  obtain ⟨s, hs, hscard⟩ := Order.exists_cof_eq α
  have hsaleph : #s = aleph0 := hscard.trans hcofα
  obtain ⟨hden⟩ := Cardinal.denumerable_iff.mpr hsaleph
  let eNat : s ≃ ℕ := Denumerable.eqv s
  let g : ℕ → α := fun n => (eNat.symm n).1
  let gInc : ℕ → α := Nat.rec (g 0) fun n prev => max prev (g (n + 1))
  have gInc_mono : ∀ n, gInc n ≤ gInc (n + 1) := fun n => le_max_left _ _
  have gInc_ge : ∀ n, g n ≤ gInc n := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ih =>
      change g (n + 1) ≤ max (gInc n) (g (n + 1))
      exact le_max_right _ _
  have gInc_cofinal : ∀ x : α, ∃ n, x ≤ gInc n := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hs x
    refine ⟨eNat ⟨y, hy⟩, hxy.trans ?_⟩
    have h := gInc_ge (eNat ⟨y, hy⟩)
    simpa [g] using h
  obtain ⟨φ⟩ := Cardinal.eq.mp (hX.trans hαcard.symm)
  let A : ℕ → Set X := fun n => φ.symm '' Iic (gInc n)
  refine ⟨A, ?_, ?_, ?_⟩
  · intro n
    exact (mk_image_le).trans_lt (card_Iic_ord_lt hinf (gInc n))
  · intro n x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, le_trans hi (gInc_mono n), rfl⟩
  · intro x
    obtain ⟨n, hn⟩ := gInc_cofinal (φ x)
    exact ⟨n, ⟨φ x, hn, φ.left_inv x⟩⟩

/-! ### Language equivalence from common-domain partial embeddings -/

theorem map_fun_of_common_domain_embeddings {L : Tau.{u}} {M N : Type u}
    [L.Structure M] [L.Structure N] (f : M → N)
    (H : ∀ s : Finset M,
      ∃ (A : Type u) (_ : L.Structure A) (ι : A ↪[L] M) (ρ : A ↪[L] N),
        ∀ x ∈ s, ∃ a, ι a = x ∧ ρ a = f x)
    {n : ℕ} (F : L.Functions n) (x : Fin n → M) :
    f (Language.Structure.funMap F x) = Language.Structure.funMap F (f ∘ x) := by
  classical
  let s : Finset M := insert (Language.Structure.funMap F x) (Finset.univ.image x)
  obtain ⟨A, _, ι, ρ, hA⟩ := H s
  have hx (i : Fin n) : ∃ a, ι a = x i ∧ ρ a = f (x i) :=
    hA _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))
  choose a haι haρ using hx
  obtain ⟨b, hbι, hbρ⟩ :=
    hA _ (Finset.mem_insert_self _ _)
  have hιF : ι (Language.Structure.funMap F a) = Language.Structure.funMap F x := by
    rw [ι.map_fun F a]
    congr 1
    ext i
    exact haι i
  have hρF : ρ (Language.Structure.funMap F a) = Language.Structure.funMap F (f ∘ x) := by
    rw [ρ.map_fun F a]
    congr 1
    ext i
    exact haρ i
  have hb_eq : b = Language.Structure.funMap F a :=
    ι.injective (hbι.trans hιF.symm)
  calc
    f (Language.Structure.funMap F x) = ρ b := hbρ.symm
    _ = ρ (Language.Structure.funMap F a) := by rw [hb_eq]
    _ = Language.Structure.funMap F (f ∘ x) := hρF

theorem map_rel_of_common_domain_embeddings {L : Tau.{u}} {M N : Type u}
    [L.Structure M] [L.Structure N] (f : M → N)
    (H : ∀ s : Finset M,
      ∃ (A : Type u) (_ : L.Structure A) (ι : A ↪[L] M) (ρ : A ↪[L] N),
        ∀ x ∈ s, ∃ a, ι a = x ∧ ρ a = f x)
    {n : ℕ} (R : L.Relations n) (x : Fin n → M) :
    Language.Structure.RelMap R (f ∘ x) ↔ Language.Structure.RelMap R x := by
  classical
  let s : Finset M := Finset.univ.image x
  obtain ⟨A, _, ι, ρ, hA⟩ := H s
  have hx (i : Fin n) : ∃ a, ι a = x i ∧ ρ a = f (x i) :=
    hA _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  choose a haι haρ using hx
  have hι : Language.Structure.RelMap R (ι ∘ a) ↔ Language.Structure.RelMap R a :=
    ι.map_rel R a
  have hρ : Language.Structure.RelMap R (ρ ∘ a) ↔ Language.Structure.RelMap R a :=
    ρ.map_rel R a
  have hιx : ι ∘ a = x := by ext i; exact haι i
  have hρx : ρ ∘ a = f ∘ x := by ext i; exact haρ i
  rw [hιx] at hι
  rw [hρx] at hρ
  exact hρ.trans hι.symm

/-- A bijection that agrees, on every finite set, with a pair of embeddings out of a common
domain is a `Language.Equiv`. No embedding of the full ambient structures is required. -/
noncomputable def languageEquiv_of_bijective_common_domain {L : Tau.{u}} {M N : Type u}
    [L.Structure M] [L.Structure N] (f : M → N)
    (hinj : Injective f) (hsurj : Surjective f)
    (H : ∀ s : Finset M,
      ∃ (A : Type u) (_ : L.Structure A) (ι : A ↪[L] M) (ρ : A ↪[L] N),
        ∀ x ∈ s, ∃ a, ι a = x ∧ ρ a = f x) :
    M ≃[L] N :=
  embeddingEquivOfSurjective
    ⟨⟨f, hinj⟩,
      fun {_} F x => map_fun_of_common_domain_embeddings f H F x,
      fun {_} R x => map_rel_of_common_domain_embeddings f H R x⟩
    hsurj

theorem languageEquiv_of_bijective_common_domain_apply {L : Tau.{u}} {M N : Type u}
    [L.Structure M] [L.Structure N] (f : M → N)
    (hinj : Injective f) (hsurj : Surjective f)
    (H : ∀ s : Finset M,
      ∃ (A : Type u) (_ : L.Structure A) (ι : A ↪[L] M) (ρ : A ↪[L] N),
        ∀ x ∈ s, ∃ a, ι a = x ∧ ρ a = f x) (x : M) :
    languageEquiv_of_bijective_common_domain f hinj hsurj H x = f x :=
  rfl

/-- A partial match all of whose pairs are carried by one pair of embeddings out of a
common domain. -/
def CommonDomain (L : Tau.{u}) {X Y : Type u} [L.Structure X] [L.Structure Y]
    (R : Set (X × Y)) : Prop :=
  ∃ (A : Type u) (_ : L.Structure A) (ι : A ↪[L] X) (ρ : A ↪[L] Y),
    ∀ p ∈ R, ∃ a, ι a = p.1 ∧ ρ a = p.2

/-- **Countable union of partial matches.** An increasing `ω`-chain of common-domain partial
matches whose domains exhaust `X` and whose ranges exhaust `Y` unions to a structure
isomorphism extending every stage. -/
theorem exists_equiv_of_commonDomain_chain {L : Tau.{u}} {X Y : Type u}
    [L.Structure X] [L.Structure Y] (R : ℕ → Set (X × Y))
    (hmono : ∀ n, R n ⊆ R (n + 1))
    (hcd : ∀ n, CommonDomain L (R n))
    (htot : ∀ x, ∃ n y, (x, y) ∈ R n)
    (hsurj : ∀ y, ∃ n x, (x, y) ∈ R n) :
    ∃ e : X ≃[L] Y, ∀ n, ∀ p ∈ R n, e p.1 = p.2 := by
  classical
  have hmono' : ∀ {n m : ℕ}, n ≤ m → R n ⊆ R m := fun {n m} h =>
    monotone_nat_of_le_succ (f := R) hmono h
  have hfun : ∀ {n m : ℕ} {x : X} {y y' : Y}, (x, y) ∈ R n → (x, y') ∈ R m → y = y' := by
    intro n m x y y' h h'
    obtain ⟨A, _, ι, ρ, hA⟩ := hcd (max n m)
    obtain ⟨a, ha1, ha2⟩ := hA _ (hmono' (le_max_left n m) h)
    obtain ⟨a', ha1', ha2'⟩ := hA _ (hmono' (le_max_right n m) h')
    have haa : a = a' := ι.injective (ha1.trans ha1'.symm)
    calc y = ρ a := ha2.symm
      _ = ρ a' := by rw [haa]
      _ = y' := ha2'
  have hinj : ∀ {n m : ℕ} {x x' : X} {y : Y}, (x, y) ∈ R n → (x', y) ∈ R m → x = x' := by
    intro n m x x' y h h'
    obtain ⟨A, _, ι, ρ, hA⟩ := hcd (max n m)
    obtain ⟨a, ha1, ha2⟩ := hA _ (hmono' (le_max_left n m) h)
    obtain ⟨a', ha1', ha2'⟩ := hA _ (hmono' (le_max_right n m) h')
    have haa : a = a' := ρ.injective (ha2.trans ha2'.symm)
    calc x = ι a := ha1.symm
      _ = ι a' := by rw [haa]
      _ = x' := ha1'
  choose n₀ f hf using htot
  have finj : Injective f := by
    intro x x' h
    have hx' : (x', f x) ∈ R (n₀ x') := by rw [h]; exact hf x'
    exact hinj (hf x) hx'
  have fsurj : Surjective f := by
    intro y
    obtain ⟨n, x, hx⟩ := hsurj y
    exact ⟨x, hfun (hf x) hx⟩
  have H : ∀ s : Finset X,
      ∃ (A : Type u) (_ : L.Structure A) (ι : A ↪[L] X) (ρ : A ↪[L] Y),
        ∀ x ∈ s, ∃ a, ι a = x ∧ ρ a = f x := by
    intro s
    obtain ⟨A, iA, ι, ρ, hA⟩ := hcd (s.sup n₀)
    exact ⟨A, iA, ι, ρ, fun x hx => hA (x, f x) (hmono' (Finset.le_sup hx) (hf x))⟩
  refine ⟨languageEquiv_of_bijective_common_domain f finj fsurj H, ?_⟩
  intro n p hp
  rw [languageEquiv_of_bijective_common_domain_apply]
  exact hfun (hf p.1) (show (p.1, p.2) ∈ R n from hp)

/-! ### Length bounds below ζ -/

/-- A common infinite bound `σ' < ζ` above `LS(K)`, a length `c`, and an old bound `σ`. -/
theorem exists_stage_bound (K : AbstractElementaryClass.{u}) {ζ : Cardinal.{u}}
    (hζ : ls K < ζ) {c σ : Cardinal.{u}} (hc : c < ζ) (hσζ : σ < ζ) (hσ : aleph0 ≤ σ) :
    ∃ σ' : Cardinal.{u}, aleph0 ≤ σ' ∧ ls K ≤ σ' ∧ c ≤ σ' ∧ σ ≤ σ' ∧ σ' < ζ :=
  ⟨max (max c σ) (ls K),
    hσ.trans ((le_max_right c σ).trans (le_max_left _ _)),
    le_max_right _ _,
    (le_max_left c σ).trans (le_max_left _ _),
    (le_max_right c σ).trans (le_max_left _ _),
    max_lt (max_lt hc hσζ) hζ⟩

theorem ls_le_t_of_bound {K : AbstractElementaryClass.{u}} (D : StableDiagram K)
    {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ) (hls : ls K ≤ σ) :
    ls K ≤ D.t σ :=
  (hls.trans (self_le_add_left σ K.τ.card)).trans (D.above σ hσ).le

theorem sigma_lt_t {K : AbstractElementaryClass.{u}} (D : StableDiagram K)
    {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ) : σ < D.t σ :=
  (self_le_add_left σ K.τ.card).trans_lt (D.above σ hσ)

/-! ### Diagram equality versus common strong hulls -/

/-- **Common hull ⇒ diagram equality.** If one model `A` of size at least `t(σ)` embeds
strongly in both `M` and `N`, the two images of any tuple of `A` of length at most `σ` have
the same diagram. -/
theorem StableDiagram.same_of_common_hull {K : AbstractElementaryClass.{u}}
    (D : StableDiagram K) {σ : Cardinal.{u}} {β : Type u} {A M N : Model K.τ}
    (hβ : #β ≤ σ) (hσ : aleph0 ≤ σ)
    (hA : K.Mem A) (hM : K.Mem M) (hN : K.Mem N)
    (hAc : D.t σ ≤ Model.card A) (hMc : D.t σ ≤ Model.card M) (hNc : D.t σ ≤ Model.card N)
    (ι : Language.Embedding K.τ A.carrier M.carrier)
    (ρ : Language.Embedding K.τ A.carrier N.carrier)
    (hι : K.Strong ι) (hρ : K.Strong ρ)
    (a : β → A.carrier) (xs : β → M.carrier) (ys : β → N.carrier)
    (hx : ∀ i, ι (a i) = xs i) (hy : ∀ i, ρ (a i) = ys i) :
    D.same hβ hM hN hMc hNc xs ys :=
  D.trans hβ hM hA hN hMc hAc hNc xs a ys
    (D.symm hβ hA hM hAc hMc a xs (D.of_strong hβ hA hM hAc hMc a xs ι hσ hι hx))
    (D.of_strong hβ hA hN hAc hNc a ys ρ hσ hρ hy)

/-- **Diagram equality ⇒ common hull.** A diagram match of `≤ σ`-tuples in models of size at
least `t(σ')`, `σ ≤ σ'`, is carried by a common hull of size exactly `t(σ')` which can be
chosen to contain any further set `S ⊆ |M|` of size at most `t(σ')`.

Put `xs ∪ S` and `ys` inside strong `t(σ')`-submodels; their tuples still have the same
diagram, and `D.to_strong` at the categoricity cardinal `t(σ')` matches them by a strong map
between the submodels. -/
theorem StableDiagram.exists_common_hull {K : AbstractElementaryClass.{u}}
    (D : StableDiagram K) {σ σ' : Cardinal.{u}} {α : Type u} {M N : Model K.τ}
    (hα : #α ≤ σ) (hσ : aleph0 ≤ σ) (hσσ' : σ ≤ σ') (hls : ls K ≤ σ')
    (hM : K.Mem M) (hN : K.Mem N)
    (hMc : D.t σ ≤ Model.card M) (hNc : D.t σ ≤ Model.card N)
    (hMc' : D.t σ' ≤ Model.card M) (hNc' : D.t σ' ≤ Model.card N)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (hsame : D.same hα hM hN hMc hNc xs ys)
    (S : Set M.carrier) (hS : #S ≤ D.t σ') :
    ∃ (A : Model K.τ) (ι : Language.Embedding K.τ A.carrier M.carrier)
      (ρ : Language.Embedding K.τ A.carrier N.carrier),
      K.Mem A ∧ Model.card A = D.t σ' ∧ K.Strong ι ∧ K.Strong ρ ∧
      (∀ i, ∃ a, ι a = xs i ∧ ρ a = ys i) ∧ ∀ s ∈ S, ∃ a, ι a = s := by
  classical
  have hσ' : aleph0 ≤ σ' := hσ.trans hσσ'
  have hlsκ : ls K ≤ D.t σ' := ls_le_t_of_bound D hσ' hls
  have hκinf : aleph0 ≤ D.t σ' := (isLSBound_ls K).1.trans hlsκ
  have hακ : #α ≤ D.t σ' := (hα.trans hσσ').trans (sigma_lt_t D hσ').le
  have htt : D.t σ ≤ D.t σ' := D.mono σ σ' hσσ'
  have hT : #(↥(Set.range xs ∪ S)) ≤ D.t σ' := by
    refine (mk_union_le _ _).trans ?_
    have h := add_le_add ((mk_range_le (f := xs)).trans hακ) hS
    rwa [add_eq_self hκinf] at h
  obtain ⟨M₀, f₀, hM₀, hf₀, hcM₀, hcov⟩ :=
    exists_strong_hull_exact_card K (D.t σ') hlsκ hκinf M hM hMc' (Set.range xs ∪ S) hT
  obtain ⟨N₀, g₀, hN₀, hg₀, hcN₀, hhitN⟩ :=
    exists_strong_hull_of_tuple K (D.t σ') hlsκ hκinf N hN hNc' ys hακ
  have hhitM : ∀ i, ∃ x, f₀ x = xs i := fun i => hcov _ (Or.inl ⟨i, rfl⟩)
  choose x₀ hx₀ using hhitM
  choose y₀ hy₀ using hhitN
  have hM₀c : D.t σ ≤ Model.card M₀ := htt.trans hcM₀.ge
  have hN₀c : D.t σ ≤ Model.card N₀ := htt.trans hcN₀.ge
  have h1 : D.same hα hM₀ hM hM₀c hMc x₀ xs :=
    D.of_strong hα hM₀ hM hM₀c hMc x₀ xs f₀ hσ hf₀ hx₀
  have h2 : D.same hα hN₀ hN hN₀c hNc y₀ ys :=
    D.of_strong hα hN₀ hN hN₀c hNc y₀ ys g₀ hσ hg₀ hy₀
  have h3 : D.same hα hM₀ hN₀ hM₀c hN₀c x₀ y₀ :=
    D.trans hα hM₀ hN hN₀ hM₀c hNc hN₀c x₀ ys y₀
      (D.trans hα hM₀ hM hN hM₀c hMc hNc x₀ xs ys h1 hsame)
      (D.symm hα hN₀ hN hN₀c hNc y₀ ys h2)
  have hcat : Categorical K (Model.card M₀) := by
    rw [hcM₀]; exact D.categoricity σ' hσ'
  obtain ⟨e, he, het⟩ :=
    D.to_strong hα hM₀ hN₀ x₀ y₀ hσ hcat (hcM₀.trans hcN₀.symm) hM₀c hN₀c h3
  refine ⟨M₀, f₀, g₀.comp e, hM₀, hcM₀, hf₀, K.strong_trans e g₀ he hg₀, ?_, ?_⟩
  · intro i
    exact ⟨x₀ i, hx₀ i, by rw [Language.Embedding.comp_apply, het i, hy₀ i]⟩
  · intro s hs
    exact hcov s (Or.inr hs)

/-! ### Stages of the hull back-and-forth -/

/-- Stage invariant: the partial match `R ⊆ |M| × |N|` has size at most some infinite
`σ < ζ` and is carried by a single model of size at least `t(σ)` strongly embedded in both
`M` and `N`. -/
def HullMatch (K : AbstractElementaryClass.{u}) (D : StableDiagram K) (ζ : Cardinal.{u})
    (M N : Model K.τ) (R : Set (M.carrier × N.carrier)) : Prop :=
  ∃ σ : Cardinal.{u}, aleph0 ≤ σ ∧ σ < ζ ∧ #R ≤ σ ∧
    ∃ (A : Model K.τ) (ι : Language.Embedding K.τ A.carrier M.carrier)
      (ρ : Language.Embedding K.τ A.carrier N.carrier),
      K.Mem A ∧ D.t σ ≤ Model.card A ∧ K.Strong ι ∧ K.Strong ρ ∧
      ∀ p ∈ R, ∃ a, ι a = p.1 ∧ ρ a = p.2

namespace HullMatch

variable {K : AbstractElementaryClass.{u}} {D : StableDiagram K} {ζ : Cardinal.{u}}
  {M N : Model K.τ}

/-- Interchange the two sides of a stage. -/
theorem swap {R : Set (M.carrier × N.carrier)} (h : HullMatch K D ζ M N R) :
    HullMatch K D ζ N M (Prod.swap ⁻¹' R) := by
  obtain ⟨σ, hσ, hσζ, hR, A, ι, ρ, hA, hAc, hι, hρ, hcov⟩ := h
  refine ⟨σ, hσ, hσζ, (mk_preimage_of_injective _ _ Prod.swap_injective).trans hR,
    A, ρ, ι, hA, hAc, hρ, hι, ?_⟩
  intro p hp
  obtain ⟨a, h1, h2⟩ := hcov _ hp
  exact ⟨a, h2, h1⟩

theorem commonDomain {R : Set (M.carrier × N.carrier)} (h : HullMatch K D ζ M N R) :
    CommonDomain K.τ R := by
  obtain ⟨σ, _, _, _, A, ι, ρ, _, _, _, _, hcov⟩ := h
  exact ⟨A.carrier, inferInstance, ι, ρ, hcov⟩

/-- The empty match between two `ζ`-models is a stage: any two strong hulls of the
categoricity size `t(LS(K))` are isomorphic. -/
theorem empty (hζ : ls K < ζ)
    (hclosed : ∀ σ, aleph0 ≤ σ → σ < ζ → D.t σ < ζ)
    (hM : K.Mem M) (hN : K.Mem N)
    (hcM : Model.card M = ζ) (hcN : Model.card N = ζ) :
    HullMatch K D ζ M N ∅ := by
  have hσ : aleph0 ≤ ls K := (isLSBound_ls K).1
  have ht : D.t (ls K) < ζ := hclosed _ hσ hζ
  have hlsκ : ls K ≤ D.t (ls K) := ls_le_t_of_bound D hσ le_rfl
  have hκinf : aleph0 ≤ D.t (ls K) := hσ.trans hlsκ
  have hMc : D.t (ls K) ≤ Model.card M := by rw [hcM]; exact ht.le
  have hNc : D.t (ls K) ≤ Model.card N := by rw [hcN]; exact ht.le
  obtain ⟨M₀, f₀, hM₀, hf₀, hcM₀, -⟩ :=
    exists_strong_hull_exact_card K _ hlsκ hκinf M hM hMc ∅ (by simp)
  obtain ⟨N₀, g₀, hN₀, hg₀, hcN₀, -⟩ :=
    exists_strong_hull_exact_card K _ hlsκ hκinf N hN hNc ∅ (by simp)
  obtain ⟨φ⟩ := (D.categoricity _ hσ).unique_model M₀ N₀ hM₀ hN₀ hcM₀ hcN₀
  exact ⟨ls K, hσ, hζ, by simp, M₀, f₀, g₀.comp φ.toEmbedding, hM₀, hcM₀.ge, hf₀,
    K.strong_trans φ.toEmbedding g₀ (strong_of_equiv K φ hM₀) hg₀,
    fun p hp => absurd hp (Set.notMem_empty p)⟩

/-- A diagram match of bounded tuples in two `ζ`-models is a stage. -/
theorem of_same (hζ : ls K < ζ)
    (hclosed : ∀ σ, aleph0 ≤ σ → σ < ζ → D.t σ < ζ)
    (hM : K.Mem M) (hN : K.Mem N)
    (hcM : Model.card M = ζ) (hcN : Model.card N = ζ)
    {α : Type u} {σ : Cardinal.{u}} (hαζ : #α < ζ) (hα : #α ≤ σ) (hσ : aleph0 ≤ σ)
    (hMc : D.t σ ≤ Model.card M) (hNc : D.t σ ≤ Model.card N)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (hsame : D.same hα hM hN hMc hNc xs ys) :
    HullMatch K D ζ M N (Set.range fun i => (xs i, ys i)) := by
  have hσζ : σ < ζ := (sigma_lt_t D hσ).trans_le (hMc.trans hcM.le)
  obtain ⟨σ', hσ', hls', hασ', hσσ', hσ'ζ⟩ := exists_stage_bound K hζ hαζ hσζ hσ
  have htσ' : D.t σ' < ζ := hclosed σ' hσ' hσ'ζ
  have hMc' : D.t σ' ≤ Model.card M := by rw [hcM]; exact htσ'.le
  have hNc' : D.t σ' ≤ Model.card N := by rw [hcN]; exact htσ'.le
  obtain ⟨A, ι, ρ, hA, hcA, hι, hρ, hcov, -⟩ :=
    D.exists_common_hull hα hσ hσσ' hls' hM hN hMc hNc hMc' hNc' xs ys hsame ∅ (by simp)
  refine ⟨σ', hσ', hσ'ζ, mk_range_le.trans hασ', A, ι, ρ, hA, hcA.ge, hι, hρ, ?_⟩
  rintro _ ⟨i, rfl⟩
  exact hcov i

/-- **Forward step.** Extend a stage so that its domain contains a given set `S ⊆ |M|` of
size `< ζ`. -/
theorem forth (hζ : ls K < ζ)
    (hclosed : ∀ σ, aleph0 ≤ σ → σ < ζ → D.t σ < ζ)
    (hM : K.Mem M) (hN : K.Mem N)
    (hcM : Model.card M = ζ) (hcN : Model.card N = ζ)
    {R : Set (M.carrier × N.carrier)} (h : HullMatch K D ζ M N R)
    (S : Set M.carrier) (hS : #S < ζ) :
    ∃ R' : Set (M.carrier × N.carrier), R ⊆ R' ∧ HullMatch K D ζ M N R' ∧
      ∀ s ∈ S, ∃ y, (s, y) ∈ R' := by
  classical
  obtain ⟨σ, hσ, hσζ, hR, A, ι, ρ, hA, hAc, hι, hρ, hcov⟩ := h
  have htσ : D.t σ < ζ := hclosed σ hσ hσζ
  have hMc : D.t σ ≤ Model.card M := by rw [hcM]; exact htσ.le
  have hNc : D.t σ ≤ Model.card N := by rw [hcN]; exact htσ.le
  -- The current match, read as a diagram equality in the ambient `ζ`-models.
  have hlift : ∀ p : R, ∃ a, ι a = p.1.1 ∧ ρ a = p.1.2 := fun p => hcov p.1 p.2
  choose a ha1 ha2 using hlift
  have hsame : D.same hR hM hN hMc hNc (fun p : R => p.1.1) (fun p : R => p.1.2) :=
    D.same_of_common_hull hR hσ hA hM hN hAc hMc hNc ι ρ hι hρ a _ _ ha1 ha2
  -- Enlarge the bound and rebuild the hull around the old match and `S`.
  obtain ⟨σ', hσ', hls', hSσ', hσσ', hσ'ζ⟩ := exists_stage_bound K hζ hS hσζ hσ
  have htσ' : D.t σ' < ζ := hclosed σ' hσ' hσ'ζ
  have hMc' : D.t σ' ≤ Model.card M := by rw [hcM]; exact htσ'.le
  have hNc' : D.t σ' ≤ Model.card N := by rw [hcN]; exact htσ'.le
  obtain ⟨A', ι', ρ', hA', hcA', hι', hρ', hcov', hcovS⟩ :=
    D.exists_common_hull hR hσ hσσ' hls' hM hN hMc hNc hMc' hNc' _ _ hsame S
      (hSσ'.trans (sigma_lt_t D hσ').le)
  let T : Set M.carrier := Prod.fst '' R ∪ S
  let R' : Set (M.carrier × N.carrier) := (fun a => (ι' a, ρ' a)) '' (ι' ⁻¹' T)
  refine ⟨R', ?_, ⟨σ', hσ', hσ'ζ, ?_, A', ι', ρ', hA', hcA'.ge, hι', hρ', ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨a, h1, h2⟩ := hcov' ⟨p, hp⟩
    exact ⟨a, Or.inl ⟨p, hp, h1.symm⟩, Prod.ext h1 h2⟩
  · have hT : #T ≤ σ' := by
      refine (mk_union_le _ _).trans ?_
      have h := add_le_add
        ((mk_image_le (f := Prod.fst) (s := R)).trans (hR.trans hσσ')) hSσ'
      rwa [add_eq_self hσ'] at h
    exact mk_image_le.trans ((mk_preimage_of_injective _ _ ι'.injective).trans hT)
  · rintro _ ⟨a, _, rfl⟩
    exact ⟨a, rfl, rfl⟩
  · intro s hs
    obtain ⟨a, ha⟩ := hcovS s hs
    exact ⟨ρ' a, a, Or.inr (show ι' a ∈ S from ha.symm ▸ hs), Prod.ext ha rfl⟩

/-- **Backward step.** Extend a stage so that its range contains a given set `T ⊆ |N|` of
size `< ζ` (the forward step with `M`, `N` interchanged). -/
theorem back (hζ : ls K < ζ)
    (hclosed : ∀ σ, aleph0 ≤ σ → σ < ζ → D.t σ < ζ)
    (hM : K.Mem M) (hN : K.Mem N)
    (hcM : Model.card M = ζ) (hcN : Model.card N = ζ)
    {R : Set (M.carrier × N.carrier)} (h : HullMatch K D ζ M N R)
    (T : Set N.carrier) (hT : #T < ζ) :
    ∃ R' : Set (M.carrier × N.carrier), R ⊆ R' ∧ HullMatch K D ζ M N R' ∧
      ∀ t ∈ T, ∃ x, (x, t) ∈ R' := by
  obtain ⟨R'', hsub, hR'', hcov⟩ := forth hζ hclosed hN hM hcN hcM h.swap T hT
  refine ⟨Prod.swap ⁻¹' R'', ?_, hR''.swap, ?_⟩
  · intro p hp
    have hp' : p.swap ∈ Prod.swap ⁻¹' R := by
      simpa using hp
    exact hsub hp'
  · intro t ht
    obtain ⟨x, hx⟩ := hcov t ht
    exact ⟨x, hx⟩

end HullMatch

/-! ### The back-and-forth -/

/-- Countable alternating back-and-forth: every stage between two `ζ`-models extends to an
isomorphism. -/
theorem exists_equiv_of_hullMatch (K : AbstractElementaryClass.{u}) (D : StableDiagram K)
    (ζ : Cardinal.{u}) (hζ : ls K < ζ) (hcof : Ordinal.cof ζ.ord = aleph0)
    (hclosed : ∀ σ, aleph0 ≤ σ → σ < ζ → D.t σ < ζ)
    {M N : Model K.τ} (hM : K.Mem M) (hN : K.Mem N)
    (hcM : Model.card M = ζ) (hcN : Model.card N = ζ)
    {R₀ : Set (M.carrier × N.carrier)} (h₀ : HullMatch K D ζ M N R₀) :
    ∃ e : M.carrier ≃[K.τ] N.carrier, ∀ p ∈ R₀, e p.1 = p.2 := by
  classical
  have hζinf : aleph0 ≤ ζ := (isLSBound_ls K).1.trans hζ.le
  obtain ⟨SA, hSA, -, hSAcov⟩ :=
    exists_countable_set_exhaustion (X := M.carrier) hcM hζinf hcof
  obtain ⟨SB, hSB, -, hSBcov⟩ :=
    exists_countable_set_exhaustion (X := N.carrier) hcN hζinf hcof
  have step : ∀ (Q : {R // HullMatch K D ζ M N R}) (n : ℕ),
      ∃ Q' : {R // HullMatch K D ζ M N R}, Q.1 ⊆ Q'.1 ∧
        (∀ s ∈ SA n, ∃ y, (s, y) ∈ Q'.1) ∧ ∀ t ∈ SB n, ∃ x, (x, t) ∈ Q'.1 := by
    intro Q n
    obtain ⟨R₁, h01, hR₁, hc₁⟩ :=
      HullMatch.forth hζ hclosed hM hN hcM hcN Q.2 (SA n) (hSA n)
    obtain ⟨R₂, h12, hR₂, hc₂⟩ :=
      HullMatch.back hζ hclosed hM hN hcM hcN hR₁ (SB n) (hSB n)
    exact ⟨⟨R₂, hR₂⟩, h01.trans h12,
      fun s hs => (hc₁ s hs).imp fun y hy => h12 hy, hc₂⟩
  choose next hnext using step
  let seq : ℕ → {R // HullMatch K D ζ M N R} :=
    fun n => Nat.rec ⟨R₀, h₀⟩ (fun n Q => next Q n) n
  have hseq : ∀ n, seq (n + 1) = next (seq n) n := fun n => rfl
  obtain ⟨e, he⟩ := exists_equiv_of_commonDomain_chain (L := K.τ) (fun n => (seq n).1)
    (fun n => by
      show (seq n).1 ⊆ (seq (n + 1)).1
      rw [hseq]; exact (hnext (seq n) n).1)
    (fun n => (seq n).2.commonDomain)
    (fun x => by
      obtain ⟨n, hn⟩ := hSAcov x
      obtain ⟨y, hy⟩ := (hnext (seq n) n).2.1 x hn
      exact ⟨n + 1, y, by show (x, y) ∈ (seq (n + 1)).1; rw [hseq]; exact hy⟩)
    (fun y => by
      obtain ⟨n, hn⟩ := hSBcov y
      obtain ⟨x, hx⟩ := (hnext (seq n) n).2.2 y hn
      exact ⟨n + 1, x, by show (x, y) ∈ (seq (n + 1)).1; rw [hseq]; exact hx⟩)
  exact ⟨e, fun p hp => he 0 p hp⟩

/-- **Proposition 4.3**, hull back-and-forth form. -/
theorem prop43_hull_back_and_forth (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K]
    (D : StableDiagram K)
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
  refine ⟨⟨exists_model_of_card_gt_ls K ζ hζ, ?_⟩, ?_⟩
  · intro M N hM hN hcM hcN
    obtain ⟨e, -⟩ := exists_equiv_of_hullMatch K D ζ hζ hcof hclosed hM hN hcM hcN
      (HullMatch.empty hζ hclosed hM hN hcM hcN)
    exact ⟨e⟩
  · intro α M N xs ys hM hN hαζ hcM hcN h
    obtain ⟨σ, hα, hσ, hMc, hNc, hsame⟩ := h
    obtain ⟨e, he⟩ := exists_equiv_of_hullMatch K D ζ hζ hcof hclosed hM hN hcM hcN
      (HullMatch.of_same hζ hclosed hM hN hcM hcN hαζ hα hσ hMc hNc xs ys hsame)
    exact ⟨e, fun i => he (xs i, ys i) ⟨i, rfl⟩⟩

end
end AEC
