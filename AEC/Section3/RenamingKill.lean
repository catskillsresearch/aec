module

public import AEC.Section3.Elimination
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-!
# The `θ⁺ · a^θ` renaming kill (text.md §3.5, lines 188–198)

Given two categoricity sizes `a < μ` with `a^θ ≤ μ`, alignment of `a`-sized strong submodels
inside every `μ`-sized model, and a named arrow `p ⟶ r` at size `μ` with no reverse arrow, this
file builds a model of size `a` in which no `θ`-tuple has the orbit name `p`.

The paper builds an increasing strong chain of `μ`-sized models and renames the codomain of a
strong self-map so that it becomes an inclusion. Here strong maps are embeddings, so no renaming
is needed, and categoricity lets every stage be the *same* model: a chain is a coherent family
of strong self-maps `e α β : M → M` (`β < α`), continued through limits by taking the strong
union of the earlier stages and identifying it with `M` again.

* `selfChainRec`: the generic transfinite construction of such a family.
* `exists_dead_selfMap`: the `a^θ` steps of one round. One strong self-map of the `μ`-sized
  model sends every tuple of a family of size `≤ μ` to a tuple whose name cannot reach `p`.
* `exists_small_dead_selfMap`: one round seen from the small model, through alignment.
* `exists_killed_copy`: the `θ⁺` rounds and their union.

A name `q` "cannot reach `p`" when `¬ NamedArrow K θ μ N q p`. Such names are closed under
arrows (`namedArrow_trans`), which is the persistence assertion of the paper.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal Set

set_option linter.unusedVariables false

theorem mk_below_le (θ : Cardinal.{u}) : #(Below θ) ≤ θ := by rw [mk_ord_toType]

/-! ### The named arrow relation at a large categoricity size -/

/-- A strong embedding between two models of one categoricity size gives a named arrow from
the name of a tuple to the name of its image. -/
theorem namedArrow_of_strong (K : AbstractElementaryClass.{u}) (θ κ : Cardinal.{u})
    (N : OrbitNaming K θ) (hcat : Categorical K κ)
    {M₁ M₂ : Model K.τ} (hM₁ : K.Mem M₁) (hM₂ : K.Mem M₂)
    (hc₁ : Model.card M₁ = κ) (hc₂ : Model.card M₂ = κ)
    (g : Language.Embedding K.τ M₁.carrier M₂.carrier) (hg : K.Strong g)
    (xs : Below θ → M₁.carrier) :
    NamedArrow K θ κ N (N.name hM₁ xs (mk_below_le θ))
      (N.name hM₂ (fun i => g (xs i)) (mk_below_le θ)) := by
  obtain ⟨φ⟩ := hcat.unique_model M₂ M₁ hM₂ hM₁ hc₂ hc₁
  refine ⟨M₁, hM₁, hc₁, xs, fun i => φ (g (xs i)), rfl, ?_, ?_⟩
  · exact (N.name_iso φ hM₂ hM₁ (fun i => g (xs i)) (mk_below_le θ)).symm
  · exact ⟨φ.toEmbedding.comp g,
      K.strong_trans g φ.toEmbedding hg (strong_of_equiv K φ hM₂), fun i => rfl⟩

/-- The named arrow relation is transitive at a large categoricity size. -/
theorem namedArrow_trans (K : AbstractElementaryClass.{u}) (θ κ : Cardinal.{u})
    (N : OrbitNaming K θ) (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    {q₁ q₂ q₃ : OrbitName K θ}
    (h₁ : NamedArrow K θ κ N q₁ q₂) (h₂ : NamedArrow K θ κ N q₂ q₃) :
    NamedArrow K θ κ N q₁ q₃ := by
  obtain ⟨M, hM, hc, xs, ys, hxs, hys, hxy⟩ := h₁
  obtain ⟨M', hM', hc', us, vs, hus, hvs, huv⟩ := h₂
  obtain ⟨φ⟩ := hcat.unique_model M' M hM' hM hc' hc
  have hleM : max (ls K) (Order.succ θ) ≤ Model.card M := by rw [hc]; exact hle
  have hcatM : Categorical K (Model.card M) := by rw [hc]; exact hcat
  have hιB := mk_below_le θ
  have hus' : N.name hM (fun i => φ (us i)) hιB = q₂ := by
    rw [← N.name_iso φ hM' hM us hιB]; exact hus
  have hvs' : N.name hM (fun i => φ (vs i)) hιB = q₃ := by
    rw [← N.name_iso φ hM' hM vs hιB]; exact hvs
  have horb : SameAutOrbit K M (fun i => φ (us i)) ys :=
    (N.name_spec hM _ ys hιB hleM hcatM).1 (hus'.trans hys.symm)
  have hrefl : SameAutOrbit K M (fun i => φ (vs i)) (fun i => φ (vs i)) :=
    (N.name_spec hM _ _ hιB hleM hcatM).1 rfl
  have harrow := orbitArrow_of_sameAutOrbit K hM horb hrefl (orbitArrow_iso K hM' hM φ huv)
  exact ⟨M, hM, hc, xs, fun i => φ (vs i), hxs, hvs', orbitArrow_comp K M hxy harrow⟩

/-- A named arrow out of the name of a given tuple is realized by a strong self-map applied
to that tuple. -/
theorem exists_strong_of_namedArrow (K : AbstractElementaryClass.{u}) (θ κ : Cardinal.{u})
    (N : OrbitNaming K θ) (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    {M : Model K.τ} (hM : K.Mem M) (hc : Model.card M = κ)
    (xs : Below θ → M.carrier) {q : OrbitName K θ}
    (h : NamedArrow K θ κ N (N.name hM xs (mk_below_le θ)) q) :
    ∃ k : Language.Embedding K.τ M.carrier M.carrier, K.Strong k ∧
      N.name hM (fun i => k (xs i)) (mk_below_le θ) = q := by
  obtain ⟨M', hM', hc', us, vs, hus, hvs, huv⟩ := h
  obtain ⟨φ⟩ := hcat.unique_model M' M hM' hM hc' hc
  have hleM : max (ls K) (Order.succ θ) ≤ Model.card M := by rw [hc]; exact hle
  have hcatM : Categorical K (Model.card M) := by rw [hc]; exact hcat
  have hιB := mk_below_le θ
  have hus' : N.name hM (fun i => φ (us i)) hιB = N.name hM xs hιB := by
    rw [← N.name_iso φ hM' hM us hιB]; exact hus
  have hvs' : N.name hM (fun i => φ (vs i)) hιB = q := by
    rw [← N.name_iso φ hM' hM vs hιB]; exact hvs
  have horb : SameAutOrbit K M (fun i => φ (us i)) xs :=
    (N.name_spec hM _ xs hιB hleM hcatM).1 hus'
  have hrefl : SameAutOrbit K M (fun i => φ (vs i)) (fun i => φ (vs i)) :=
    (N.name_spec hM _ _ hιB hleM hcatM).1 rfl
  obtain ⟨k, hk, hkx⟩ :=
    orbitArrow_of_sameAutOrbit K hM horb hrefl (orbitArrow_iso K hM' hM φ huv)
  refine ⟨k, hk, ?_⟩
  have hfun : (fun i => k (xs i)) = fun i => φ (vs i) := funext hkx
  rw [hfun]
  exact hvs'

/-- One step of the kill (text.md 190): every tuple of the large model is sent by a strong
self-map to a tuple whose name cannot reach `p`. If its name reaches `p`, compose with
`p ⟶ r`; the name `r` cannot reach `p`. -/
theorem exists_dead_map (K : AbstractElementaryClass.{u}) (θ μ : Cardinal.{u})
    (N : OrbitNaming K θ) (hle : max (ls K) (Order.succ θ) ≤ μ) (hcat : Categorical K μ)
    (p r : OrbitName K θ) (hpr : NamedArrow K θ μ N p r) (hrp : ¬ NamedArrow K θ μ N r p)
    {M : Model K.τ} (hM : K.Mem M) (hc : Model.card M = μ) (xs : Below θ → M.carrier) :
    ∃ k : Language.Embedding K.τ M.carrier M.carrier, K.Strong k ∧
      ¬ NamedArrow K θ μ N (N.name hM (fun i => k (xs i)) (mk_below_le θ)) p := by
  by_cases hreach : NamedArrow K θ μ N (N.name hM xs (mk_below_le θ)) p
  · obtain ⟨k, hk, hname⟩ := exists_strong_of_namedArrow K θ μ N hle hcat hM hc xs
      (namedArrow_trans K θ μ N hle hcat hreach hpr)
    exact ⟨k, hk, by rw [hname]; exact hrp⟩
  · exact ⟨Language.Embedding.refl _ _, K.strong_refl M hM, hreach⟩

/-! ### Factoring an embedding through another one -/

/-- An embedding whose range lies in the range of a second embedding factors through it. -/
theorem exists_factor_embedding {L : Tau.{u}} {A B M : Type u}
    [L.Structure A] [L.Structure B] [L.Structure M]
    (j : A ↪[L] M) (k : B ↪[L] M) (h : ∀ x, ∃ y, k y = j x) :
    ∃ h₁ : A ↪[L] B, k.comp h₁ = j := by
  classical
  choose h₁ hh using h
  refine ⟨⟨⟨h₁, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro x y hxy
    apply j.injective
    rw [← hh x, ← hh y, hxy]
  · intro n f xs
    apply k.injective
    change k (h₁ (Language.Structure.funMap f xs)) =
      k (Language.Structure.funMap f (h₁ ∘ xs))
    rw [hh, j.map_fun, k.map_fun]
    congr 1
    funext i
    exact (hh (xs i)).symm
  · intro n r xs
    change Language.Structure.RelMap r (h₁ ∘ xs) ↔ Language.Structure.RelMap r xs
    rw [← k.map_rel, ← j.map_rel r xs]
    have hfun : ⇑k ∘ h₁ ∘ xs = ⇑j ∘ xs := funext fun i => hh (xs i)
    rw [hfun]
  · ext x
    exact hh x

/-! ### Chains of strong self-maps of one model -/

/-- The ordinal chain of length `δ` with constant object `M` and transition maps
`e j i : M → M` for `i < j`. -/
@[reducible] def selfChain {τ : Tau.{u}} (M : Model τ) (δ : _root_.Ordinal.{u}) (hδ : δ ≠ 0)
    (e : _root_.Ordinal.{u} → _root_.Ordinal.{u} → Language.Embedding τ M.carrier M.carrier) :
    OrdinalChain τ where
  δ := δ
  nonzero := hδ
  obj := fun _ _ => M
  map := fun i j _ _ _ => e j i

/-- The family `e β γ : M → M` (`γ < β < δ`) is a coherent chain of strong self-maps. -/
def SelfChainGood (K : AbstractElementaryClass.{u}) (M : Model K.τ) (δ : _root_.Ordinal.{u})
    (e : _root_.Ordinal.{u} → _root_.Ordinal.{u} →
      Language.Embedding K.τ M.carrier M.carrier) : Prop :=
  (∀ β, β < δ → ∀ γ, γ < β → K.Strong (e β γ)) ∧
  (∀ β, β < δ → ∀ γ, γ < β → ∀ ε, ε < γ → (e β γ).comp (e γ ε) = e β ε)

/-- The strong union of a chain of at most `κ` self-maps of a model of size `κ` has size `κ`
(text.md 192: every large union has size `μ`). -/
theorem exists_selfChain_union (K : AbstractElementaryClass.{u}) {κ : Cardinal.{u}}
    (hκ : aleph0 ≤ κ) (M : Model K.τ) (hM : K.Mem M) (hc : Model.card M = κ)
    (δ : _root_.Ordinal.{u}) (hδ : δ ≠ 0) (hδκ : δ.card ≤ κ)
    (e : _root_.Ordinal.{u} → _root_.Ordinal.{u} →
      Language.Embedding K.τ M.carrier M.carrier)
    (hgood : SelfChainGood K M δ e) :
    ∃ U : ChainUnion (selfChain M δ hδ e), K.Mem U.obj ∧
      (∀ i hi, K.Strong (U.incl i hi)) ∧ Model.card U.obj = κ := by
  obtain ⟨U, hU, hincl⟩ := K.chain_union (selfChain M δ hδ e)
    (fun i j k hi hj hk hij hjk => hgood.2 k hk j hjk i hij)
    (fun i hi => hM)
    (fun i j hi hj hij => hgood.1 j hj i hij)
  refine ⟨U, hU, hincl, le_antisymm ?_ ?_⟩
  · let f : (Σ _ : δ.ToType, M.carrier) → U.obj.carrier := fun s =>
      U.incl (Ordinal.typein (α := δ.ToType) (· < ·) s.1) (Ordinal.typein_lt_self s.1) s.2
    have aux : ∀ (j : _root_.Ordinal.{u}) (hj : j < δ) (y : M.carrier) (s : δ.ToType),
        Ordinal.typein (α := δ.ToType) (· < ·) s = j → f ⟨s, y⟩ = U.incl j hj y := by
      intro j hj y s h
      subst h
      rfl
    have hf : Function.Surjective f := by
      intro x
      obtain ⟨i, hi, y, rfl⟩ := U.covers x
      have hi' : i < Ordinal.type (α := δ.ToType) (· < ·) := by
        rw [Ordinal.type_toType]; exact hi
      exact ⟨⟨Ordinal.enum (α := δ.ToType) (· < ·) ⟨i, hi'⟩, y⟩,
        aux i hi y _ (Ordinal.typein_enum _ hi')⟩
    have hle : #U.obj.carrier ≤ #(Σ _ : δ.ToType, M.carrier) := mk_le_of_surjective hf
    have hsig : #(Σ _ : δ.ToType, M.carrier) = δ.card * κ := by
      rw [mk_sigma, sum_const', mk_toType]
      exact congrArg _ hc
    calc Model.card U.obj ≤ δ.card * κ := hsig ▸ hle
      _ ≤ κ * κ := mul_le_mul' hδκ le_rfl
      _ = κ := mul_eq_self hκ
  · have h0 : (0 : _root_.Ordinal.{u}) < δ := pos_of_ne_zero hδ
    have h := mk_le_of_injective (U.incl 0 h0).injective
    rw [← hc]
    exact h

/-- Continue a coherent chain of strong self-maps of the categoricity model through its
strong union: the union is again a copy of `M`, and the stage maps into it are coherent
(text.md 192: strong unions at limit steps). -/
theorem exists_selfChain_base (K : AbstractElementaryClass.{u}) {κ : Cardinal.{u}}
    (hκ : aleph0 ≤ κ) (hcat : Categorical K κ)
    (M : Model K.τ) (hM : K.Mem M) (hc : Model.card M = κ)
    (δ : _root_.Ordinal.{u}) (hδ : δ ≠ 0) (hδκ : δ.card ≤ κ)
    (e : _root_.Ordinal.{u} → _root_.Ordinal.{u} →
      Language.Embedding K.τ M.carrier M.carrier)
    (hgood : SelfChainGood K M δ e) :
    ∃ b : _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier,
      (∀ β, β < δ → K.Strong (b β)) ∧
      ∀ β, β < δ → ∀ γ, γ < β → (b β).comp (e β γ) = b γ := by
  classical
  obtain ⟨U, hU, hincl, hUc⟩ := exists_selfChain_union K hκ M hM hc δ hδ hδκ e hgood
  obtain ⟨φ⟩ := hcat.unique_model U.obj M hU hM hUc hc
  refine ⟨fun β => if hβ : β < δ then φ.toEmbedding.comp (U.incl β hβ)
    else Language.Embedding.refl _ _, ?_, ?_⟩
  · intro β hβ
    simp only [hβ, ↓reduceDIte]
    exact K.strong_trans (U.incl β hβ) φ.toEmbedding (hincl β hβ) (strong_of_equiv K φ hU)
  · intro β hβ γ hγ
    have hγδ := hγ.trans hβ
    simp only [hβ, hγδ, ↓reduceDIte]
    rw [Language.Embedding.comp_assoc]
    exact congrArg (fun t => φ.toEmbedding.comp t) (U.compat γ β hγδ hβ hγ)

/-- One stage of the recursion: the earlier stages `e` are continued through their union by
maps `b β`, followed by the step map `k α (b 0)`, which may depend on the stage and on the
map from the base stage. -/
noncomputable def selfChainStep (K : AbstractElementaryClass.{u}) (M : Model K.τ)
    (k : _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier →
      Language.Embedding K.τ M.carrier M.carrier)
    (α : _root_.Ordinal.{u})
    (e : _root_.Ordinal.{u} → _root_.Ordinal.{u} →
      Language.Embedding K.τ M.carrier M.carrier) :
    _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier := by
  classical
  exact
    if h : ∃ b : _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier,
        (∀ β, β < α → K.Strong (b β)) ∧
        ∀ β, β < α → ∀ γ, γ < β → (b β).comp (e β γ) = b γ then
      fun β => (k α (Classical.choose h 0)).comp (Classical.choose h β)
    else fun _ => Language.Embedding.refl _ _

theorem selfChainStep_pos (K : AbstractElementaryClass.{u}) (M : Model K.τ)
    (k : _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier →
      Language.Embedding K.τ M.carrier M.carrier)
    (α : _root_.Ordinal.{u})
    (e : _root_.Ordinal.{u} → _root_.Ordinal.{u} →
      Language.Embedding K.τ M.carrier M.carrier)
    (h : ∃ b : _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier,
        (∀ β, β < α → K.Strong (b β)) ∧
        ∀ β, β < α → ∀ γ, γ < β → (b β).comp (e β γ) = b γ) (β : _root_.Ordinal.{u}) :
    selfChainStep K M k α e β = (k α (Classical.choose h 0)).comp (Classical.choose h β) := by
  unfold selfChainStep
  rw [dite_eq_left h]

/-- The transfinite chain of strong self-maps of `M` driven by the step maps `k`:
`selfChainRec K M k α β : M → M` is the transition map from stage `β` to stage `α > β`. -/
noncomputable def selfChainRec (K : AbstractElementaryClass.{u}) (M : Model K.τ)
    (k : _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier →
      Language.Embedding K.τ M.carrier M.carrier) :
    _root_.Ordinal.{u} → _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier := by
  classical
  exact WellFounded.fix
    (C := fun _ => _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier)
    (wellFounded_lt (α := _root_.Ordinal.{u}))
    (fun α rec => selfChainStep K M k α
      (fun β => if h : β < α then rec β h else fun _ => Language.Embedding.refl _ _))

theorem selfChainRec_eq (K : AbstractElementaryClass.{u}) (M : Model K.τ)
    (k : _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier →
      Language.Embedding K.τ M.carrier M.carrier) (α : _root_.Ordinal.{u}) :
    selfChainRec K M k α = selfChainStep K M k α
      (fun β => if β < α then selfChainRec K M k β
        else fun _ => Language.Embedding.refl _ _) := by
  classical
  unfold selfChainRec
  rw [WellFounded.fix_eq]
  rfl

/-- The chain `selfChainRec` is strong and coherent at every stage of cardinality at most `κ`,
and each transition map into a nonzero stage `α` is the step map `k α (b 0)` after the map
`b β` from stage `β` into the union of the earlier stages. -/
theorem selfChainRec_spec (K : AbstractElementaryClass.{u}) {κ : Cardinal.{u}}
    (hκ : aleph0 ≤ κ) (hcat : Categorical K κ)
    (M : Model K.τ) (hM : K.Mem M) (hc : Model.card M = κ)
    (k : _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier →
      Language.Embedding K.τ M.carrier M.carrier)
    (hk : ∀ α b, K.Strong (k α b)) (α : _root_.Ordinal.{u}) (hα : α.card ≤ κ) :
    (∀ γ, γ < α → K.Strong (selfChainRec K M k α γ)) ∧
    (∀ γ, γ < α → ∀ ε, ε < γ →
      (selfChainRec K M k α γ).comp (selfChainRec K M k γ ε) = selfChainRec K M k α ε) ∧
    (α ≠ 0 → ∃ b : _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier,
      (∀ β, β < α → K.Strong (b β)) ∧
      ∀ β, β < α → selfChainRec K M k α β = (k α (b 0)).comp (b β)) := by
  classical
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    by_cases h0 : α = 0
    · subst h0
      exact ⟨fun γ hγ => absurd hγ not_lt_zero,
        fun γ hγ => absurd hγ not_lt_zero, fun h => absurd rfl h⟩
    · have hcard : ∀ β, β < α → β.card ≤ κ := fun β hβ =>
        (Ordinal.card_le_card hβ.le).trans hα
      have he : ∀ β, β < α →
          (if β < α then selfChainRec K M k β
            else fun _ => Language.Embedding.refl _ _) = selfChainRec K M k β :=
        fun β hβ => ite_eq_left hβ
      have hgood : SelfChainGood K M α
          (fun β => if β < α then selfChainRec K M k β
            else fun _ => Language.Embedding.refl _ _) := by
        refine ⟨fun β hβ γ hγ => ?_, fun β hβ γ hγ ε hε => ?_⟩
        · simp only [he β hβ]
          exact (ih β hβ (hcard β hβ)).1 γ hγ
        · simp only [he β hβ, he γ (hγ.trans hβ)]
          exact (ih β hβ (hcard β hβ)).2.1 γ hγ ε hε
      have hex := exists_selfChain_base K hκ hcat M hM hc α h0 hα _ hgood
      have hF : ∀ β, selfChainRec K M k α β =
          (k α (Classical.choose hex 0)).comp (Classical.choose hex β) := by
        intro β
        rw [selfChainRec_eq]
        exact selfChainStep_pos K M k α _ hex β
      obtain ⟨hb1, hb2⟩ := Classical.choose_spec hex
      refine ⟨fun γ hγ => ?_, fun γ hγ ε hε => ?_,
        fun _ => ⟨Classical.choose hex, hb1, fun β _ => hF β⟩⟩
      · rw [hF γ]
        exact K.strong_trans _ _ (hb1 γ hγ) (hk α _)
      · rw [hF γ, hF ε, Language.Embedding.comp_assoc]
        have h2 := hb2 γ hγ ε hε
        rw [he γ hγ] at h2
        rw [h2]

/-! ### One round: the `a^θ` steps (text.md 190–192) -/

/-- In the model of size `μ`, one strong self-map sends every tuple of a family of at most `μ`
tuples to a tuple whose name cannot reach `p`.

The tuples are processed one per stage along a chain of strong self-maps. A processed tuple
keeps a name that cannot reach `p` at all later stages, because every transition is an arrow of
the relation at size `μ`. -/
theorem exists_dead_selfMap (K : AbstractElementaryClass.{u}) (θ μ : Cardinal.{u})
    (N : OrbitNaming K θ) (hle : max (ls K) (Order.succ θ) ≤ μ) (hcat : Categorical K μ)
    (p r : OrbitName K θ) (hpr : NamedArrow K θ μ N p r) (hrp : ¬ NamedArrow K θ μ N r p)
    {M : Model K.τ} (hM : K.Mem M) (hc : Model.card M = μ)
    {T : Type u} (hT : #T ≤ μ) (tup : T → Below θ → M.carrier) :
    ∃ g : Language.Embedding K.τ M.carrier M.carrier, K.Strong g ∧
      ∀ t, ¬ NamedArrow K θ μ N (N.name hM (fun i => g (tup t i)) (mk_below_le θ)) p := by
  classical
  have hμ : aleph0 ≤ μ := (isLSBound_ls K).1.trans ((le_max_left _ _).trans hle)
  -- The stage `σ t > 0` at which the tuple `t` is processed, and the final stage `Λ`.
  let σ : T → _root_.Ordinal.{u} := fun t =>
    Order.succ (Ordinal.typein (WellOrderingRel (α := T)) t)
  let Λ : _root_.Ordinal.{u} := Order.succ (Ordinal.type (WellOrderingRel (α := T)))
  have hσinj : Function.Injective σ := fun t t' h =>
    Ordinal.typein_injective _ (Order.succ_injective h)
  have hσlt : ∀ t, σ t < Λ := fun t =>
    Order.succ_lt_succ_iff.2 (Ordinal.typein_lt_type _ t)
  have hσpos : ∀ t, 0 < σ t := fun t => zero_le.trans_lt (Order.lt_succ _)
  have hΛpos : 0 < Λ := zero_le.trans_lt (Order.lt_succ _)
  have hΛ : Λ.card ≤ μ := by
    have hΛeq : Λ.card = #T + 1 := by
      change (Order.succ (Ordinal.type (WellOrderingRel (α := T)))).card = _
      rw [Order.succ_eq_add_one, Ordinal.card_add, Ordinal.card_type, Ordinal.card_one]
    rw [hΛeq]
    exact add_le_of_le hμ hT (one_le_aleph0.trans hμ)
  -- The tuple processed at a stage.
  let pick : _root_.Ordinal.{u} → Option T := fun α =>
    if h : ∃ t, σ t = α then some (Classical.choose h) else none
  have hpick : ∀ t, pick (σ t) = some t := by
    intro t
    have hex : ∃ t', σ t' = σ t := ⟨t, rfl⟩
    change (if h : ∃ t', σ t' = σ t then some (Classical.choose h) else none) = some t
    rw [dite_eq_left hex]
    exact congrArg some (hσinj (Classical.choose_spec hex))
  choose dm hdm1 hdm2 using fun xs : Below θ → M.carrier =>
    exists_dead_map K θ μ N hle hcat p r hpr hrp hM hc xs
  let k : _root_.Ordinal.{u} → Language.Embedding K.τ M.carrier M.carrier →
      Language.Embedding K.τ M.carrier M.carrier := fun α b =>
    (pick α).elim (Language.Embedding.refl _ _) (fun t => dm (fun i => b (tup t i)))
  have hk : ∀ α b, K.Strong (k α b) := by
    intro α b
    change K.Strong ((pick α).elim (Language.Embedding.refl _ _)
      (fun t => dm (fun i => b (tup t i))))
    cases pick α with
    | none => exact K.strong_refl M hM
    | some t => exact hdm1 _
  have hkσ : ∀ t b, k (σ t) b = dm (fun i => b (tup t i)) := by
    intro t b
    change (pick (σ t)).elim (Language.Embedding.refl _ _)
      (fun t => dm (fun i => b (tup t i))) = _
    rw [hpick t]
    rfl
  have hspec := fun α hα => selfChainRec_spec K hμ hcat M hM hc k hk α hα
  refine ⟨selfChainRec K M k Λ 0, (hspec Λ hΛ).1 0 hΛpos, fun t => ?_⟩
  have hαc : (σ t).card ≤ μ := (Ordinal.card_le_card (hσlt t).le).trans hΛ
  obtain ⟨b, hb, hFb⟩ := (hspec (σ t) hαc).2.2 (hσpos t).ne'
  -- Right after its own stage the tuple cannot reach `p`.
  have hdead : ¬ NamedArrow K θ μ N
      (N.name hM (fun i => selfChainRec K M k (σ t) 0 (tup t i)) (mk_below_le θ)) p := by
    rw [hFb 0 (hσpos t), hkσ t (b 0)]
    exact hdm2 (fun i => b 0 (tup t i))
  -- Persistence up to the final stage.
  have hcomp : (selfChainRec K M k Λ (σ t)).comp (selfChainRec K M k (σ t) 0) =
      selfChainRec K M k Λ 0 := (hspec Λ hΛ).2.1 (σ t) (hσlt t) 0 (hσpos t)
  have harrow := namedArrow_of_strong K θ μ N hcat hM hM hc hc
    (selfChainRec K M k Λ (σ t)) ((hspec Λ hΛ).1 (σ t) (hσlt t))
    (fun i => selfChainRec K M k (σ t) 0 (tup t i))
  intro hreach
  apply hdead
  refine namedArrow_trans K θ μ N hle hcat harrow ?_
  rw [← hcomp] at hreach
  exact hreach

/-! ### One round seen from the small model (text.md 188–190) -/

/-- A model of size `a` has a strong self-map sending every `θ`-tuple to a tuple whose name
cannot reach `p` in the arrow relation at size `μ`.

Place the small model strongly in the model of size `μ`, kill all its `a^θ ≤ μ` tuples there
by one strong self-map of the large model, and take an aligned small submodel around the
image. Coherence makes the small model strong in the aligned one, and alignment transfers the
large names to it. -/
theorem exists_small_dead_selfMap (K : AbstractElementaryClass.{u}) (θ a μ : Cardinal.{u})
    (N : OrbitNaming K θ) (hale : max (ls K) (Order.succ θ) ≤ a) (hlt : a < μ)
    (hpow : a ^ θ ≤ μ) (hcatA : Categorical K a) (hcatμ : Categorical K μ)
    (hAlign : AlignmentProperty K θ a μ N)
    (p r : OrbitName K θ) (hpr : NamedArrow K θ μ N p r) (hrp : ¬ NamedArrow K θ μ N r p)
    {A : Model K.τ} (hA : K.Mem A) (hAc : Model.card A = a) :
    ∃ h : Language.Embedding K.τ A.carrier A.carrier, K.Strong h ∧
      ∀ us : Below θ → A.carrier,
        ¬ NamedArrow K θ μ N (N.name hA (fun i => h (us i)) (mk_below_le θ)) p := by
  classical
  have hμle : max (ls K) (Order.succ θ) ≤ μ := hale.trans hlt.le
  obtain ⟨M, hM, hMc⟩ := hcatμ.exists_model
  -- A strong copy of `A` inside the large model.
  obtain ⟨A₀, f₀, hA₀, hf₀, hA₀c, -, -⟩ := hAlign M hM hMc ∅ (by simp)
  obtain ⟨ψ⟩ := hcatA.unique_model A A₀ hA hA₀ hAc hA₀c
  let f : Language.Embedding K.τ A.carrier M.carrier := f₀.comp ψ.toEmbedding
  have hf : K.Strong f := K.strong_trans _ _ (strong_of_equiv K ψ hA) hf₀
  -- Kill every tuple of `A` in the large model.
  have hT : #(Below θ → A.carrier) ≤ μ := by
    rw [← power_def, mk_ord_toType]
    change Model.card A ^ θ ≤ μ
    rw [hAc]
    exact hpow
  obtain ⟨g, hg, hdead⟩ := exists_dead_selfMap K θ μ N hμle hcatμ p r hpr hrp hM hMc hT
    (fun t i => f (t i))
  -- An aligned small submodel around the image of `A`.
  let S : Set M.carrier := Set.range (fun x => g (f x))
  have hS : #S ≤ a := by
    have h1 : #S ≤ #A.carrier := mk_range_le
    exact h1.trans hAc.le
  obtain ⟨A', k, hA', hk, hA'c, hcov, hnames⟩ := hAlign M hM hMc S hS
  obtain ⟨h₁, hh₁⟩ := exists_factor_embedding (g.comp f) k (fun x => hcov _ ⟨x, rfl⟩)
  have hh₁S : K.Strong h₁ :=
    K.coherence h₁ (g.comp f) k (K.strong_trans f g hf hg) hk hh₁
  obtain ⟨ψ'⟩ := hcatA.unique_model A' A hA' hA hA'c hAc
  refine ⟨ψ'.toEmbedding.comp h₁,
    K.strong_trans _ _ hh₁S (strong_of_equiv K ψ' hA'), fun us => ?_⟩
  have e1 : N.name hA (fun i => ψ' (h₁ (us i))) (mk_below_le θ) =
      N.name hA' (fun i => h₁ (us i)) (mk_below_le θ) :=
    (N.name_iso ψ' hA' hA (fun i => h₁ (us i)) (mk_below_le θ)).symm
  have e2 : N.name hA' (fun i => h₁ (us i)) (mk_below_le θ) =
      N.name hM (fun i => k (h₁ (us i))) (mk_below_le θ) := hnames _ _
  have e3 : (fun i => k (h₁ (us i))) = fun i => g (f (us i)) :=
    funext fun i => DFunLike.congr_fun hh₁ (us i)
  change ¬ NamedArrow K θ μ N (N.name hA (fun i => ψ' (h₁ (us i))) (mk_below_le θ)) p
  rw [e1, e2, e3]
  exact hdead us

/-! ### The `θ⁺` rounds and their union (text.md 188, 194–198) -/

/-- **The renaming kill.** Under alignment at sizes `a < μ` with `a^θ ≤ μ`, a named arrow
`p ⟶ r` at size `μ` with no reverse arrow, and transfer of arrows into `p` from size `a` to
size `μ` (the common profile), some model of size `a` has no `θ`-tuple named `p`.

The model is the union of a `θ⁺`-chain of strong self-maps of the model of size `a`, each
transition killing every tuple of the earlier stage. A `θ`-tuple of the union lies in one
stage since `cf(θ⁺) > θ`; one stage later its name cannot reach `p`, and the inclusion of that
stage in the union is an arrow of the relation at size `a`. -/
theorem exists_killed_copy (K : AbstractElementaryClass.{u}) (θ a μ : Cardinal.{u})
    (N : OrbitNaming K θ) (hθ : aleph0 ≤ θ)
    (hale : max (ls K) (Order.succ θ) ≤ a) (hlt : a < μ) (hpow : a ^ θ ≤ μ)
    (hcatA : Categorical K a) (hcatμ : Categorical K μ)
    (hAlign : AlignmentProperty K θ a μ N)
    (p r : OrbitName K θ) (hpr : NamedArrow K θ μ N p r) (hrp : ¬ NamedArrow K θ μ N r p)
    (hArrow : ∀ q, NamedArrow K θ a N q p → NamedArrow K θ μ N q p) :
    ∃ (A : Model K.τ) (hA : K.Mem A), Model.card A = a ∧
      ∀ xs : Below θ → A.carrier, N.name hA xs (mk_below_le θ) ≠ p := by
  classical
  have hsucc : Order.succ θ ≤ a := (le_max_right _ _).trans hale
  have haInf : aleph0 ≤ a := hθ.trans ((Order.le_succ θ).trans hsucc)
  obtain ⟨A, hA, hAc⟩ := hcatA.exists_model
  obtain ⟨h, hh, hdead⟩ := exists_small_dead_selfMap K θ a μ N hale hlt hpow hcatA hcatμ
    hAlign p r hpr hrp hA hAc
  -- `θ⁺` rounds, each applying `h`.
  let Λ : _root_.Ordinal.{u} := (Order.succ θ).ord
  have hΛc : Λ.card ≤ a := by
    change (Order.succ θ).ord.card ≤ a
    rw [card_ord]
    exact hsucc
  have hΛlim : Order.IsSuccLimit Λ := isSuccLimit_ord (hθ.trans (Order.le_succ θ))
  have hΛ0 : Λ ≠ 0 := hΛlim.bot_lt.ne'
  let k : _root_.Ordinal.{u} → Language.Embedding K.τ A.carrier A.carrier →
      Language.Embedding K.τ A.carrier A.carrier := fun _ _ => h
  have hspec := fun α (hα : α.card ≤ a) =>
    selfChainRec_spec K haInf hcatA A hA hAc k (fun _ _ => hh) α hα
  have hcardlt : ∀ α, α < Λ → α.card ≤ a := fun α hα =>
    (Ordinal.card_le_card hα.le).trans hΛc
  have hgood : SelfChainGood K A Λ (selfChainRec K A k) :=
    ⟨fun β hβ γ hγ => (hspec β (hcardlt β hβ)).1 γ hγ,
      fun β hβ γ hγ ε hε => (hspec β (hcardlt β hβ)).2.1 γ hγ ε hε⟩
  obtain ⟨U, hU, hincl, hUc⟩ :=
    exists_selfChain_union K haInf A hA hAc Λ hΛ0 hΛc (selfChainRec K A k) hgood
  refine ⟨U.obj, hU, hUc, fun xs hxs => ?_⟩
  -- Every coordinate of the tuple lies in a stage; all of them lie in one stage `j`.
  have hcov : ∀ b : Below θ, ∃ i : _root_.Ordinal.{u}, ∃ hi : i < Λ, ∃ y : A.carrier,
      U.incl i hi y = xs b := fun b => U.covers (xs b)
  choose idx hidx y hy using hcov
  have hsup : (⨆ b, idx b) < Λ := by
    refine Ordinal.iSup_lt_of_lt_cof ?_ hidx
    change #(Below θ) < (Order.succ θ).ord.cof
    rw [(isRegular_succ hθ).cof_ord, mk_ord_toType]
    exact Order.lt_succ θ
  have hj : Order.succ (⨆ b, idx b) < Λ := hΛlim.succ_lt hsup
  have hij : ∀ b, idx b < Order.succ (⨆ b, idx b) := fun b =>
    (Ordinal.le_iSup idx b).trans_lt (Order.lt_succ _)
  obtain ⟨bb, hbb, hFb⟩ := (hspec _ (hcardlt _ hj)).2.2 (zero_le.trans_lt (Order.lt_succ _)).ne'
  -- The tuple is the image of a killed tuple `h ∘ w'` of stage `j`.
  have hxs_eq : xs = fun b => U.incl _ hj (h (bb (idx b) (y b))) := by
    funext b
    rw [← hy b, ← U.compat (idx b) _ (hidx b) hj (hij b)]
    change U.incl _ hj (selfChainRec K A k _ (idx b) (y b)) = _
    rw [hFb (idx b) (hij b)]
    rfl
  subst hxs_eq
  have harrow := namedArrow_of_strong K θ a N hcatA hA hU hAc hUc (U.incl _ hj) (hincl _ hj)
    (fun b => h (bb (idx b) (y b)))
  rw [hxs] at harrow
  exact hdead (fun b => bb (idx b) (y b)) (hArrow _ harrow)

end
end AEC
