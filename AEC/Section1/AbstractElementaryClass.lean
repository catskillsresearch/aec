module

public import AEC.Section1.ChainUnion

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal
open scoped FirstOrder

/-- **Definition 1.1.** An abstract elementary class `K = (𝒞, ≤K)` in a fixed language `τ`.

`Mem` is membership in `𝒞`. `Strong f` means that the `τ`-embedding `f` is a strong
inclusion `M ≤K N`. The fields are isomorphism closure, the partial-order laws,
coherence, ordinal chain unions with the common-upper-bound clause, and a
Löwenheim–Skolem bound. No intersection axiom is included. -/
structure AbstractElementaryClass where
  τ : Tau.{u}
  Mem : Model τ → Prop
  Strong : ∀ {M N : Model τ}, Language.Embedding τ M.carrier N.carrier → Prop
  strong_mem_dom : ∀ {M N : Model τ} (f : Language.Embedding τ M.carrier N.carrier),
    Strong f → Mem M
  strong_mem_cod : ∀ {M N : Model τ} (f : Language.Embedding τ M.carrier N.carrier),
    Strong f → Mem N
  /-- `≤K` is reflexive on `𝒞`. -/
  strong_refl : ∀ M : Model τ, Mem M → Strong (Language.Embedding.refl τ M.carrier)
  /-- `≤K` is transitive. -/
  strong_trans : ∀ {M N P : Model τ}
    (f : Language.Embedding τ M.carrier N.carrier)
    (g : Language.Embedding τ N.carrier P.carrier),
    Strong f → Strong g → Strong (g.comp f)
  /-- `≤K` is antisymmetric: mutually inverse strong embeddings are inverse `τ`-isomorphisms. -/
  strong_antisymm : ∀ {M N : Model τ}
    (f : Language.Embedding τ M.carrier N.carrier)
    (g : Language.Embedding τ N.carrier M.carrier),
    Strong f → Strong g →
    (∀ x, g (f x) = x) → (∀ y, f (g y) = y) →
    ∃ e : M.carrier ≃[τ] N.carrier, e.toEmbedding = f
  /-- `𝒞` is closed under isomorphism. -/
  iso_closed : ∀ {M N : Model τ}, Nonempty (M.carrier ≃[τ] N.carrier) → Mem M → Mem N
  /-- If `f : N ≅ N'` and `M ≤K N`, then `f[M] ≤K N'`. -/
  transport_strong : ∀ {M N N' : Model τ}
    (f : Language.Embedding τ M.carrier N.carrier)
    (e : N.carrier ≃[τ] N'.carrier),
    Strong f → Strong (e.toEmbedding.comp f)
  /-- Coherence: if `M₀ ⊆ M₁` as `τ`-structures and both are strong in `M₂` by commuting
  embeddings, then `M₀ ≤K M₁`. -/
  coherence : ∀ {M₀ M₁ M₂ : Model τ}
    (f₀₁ : Language.Embedding τ M₀.carrier M₁.carrier)
    (f₀₂ : Language.Embedding τ M₀.carrier M₂.carrier)
    (f₁₂ : Language.Embedding τ M₁.carrier M₂.carrier),
    Strong f₀₂ → Strong f₁₂ → f₁₂.comp f₀₁ = f₀₂ → Strong f₀₁
  /-- The union of a coherent strong chain lies in `𝒞`, and each stage is strong in the union. -/
  chain_union : ∀ (C : OrdinalChain τ), OrdinalChain.map_comp_prop τ C →
    (∀ i hi, Mem (C.obj i hi)) →
    (∀ i j hi hj hij, Strong (C.map i j hi hj hij)) →
    ∃ U : ChainUnion C, Mem U.obj ∧ ∀ i hi, Strong (U.incl i hi)
  /-- A strong chain that embeds strongly into `N` has its union strong in `N`. -/
  chain_upper : ∀ (C : OrdinalChain τ) (U : ChainUnion C) (N : Model τ)
    (g : ∀ i (hi : i < C.δ), Language.Embedding τ (C.obj i hi).carrier N.carrier),
    OrdinalChain.map_comp_prop τ C →
    (∀ i hi, Mem (C.obj i hi)) →
    (∀ i j hi hj hij, Strong (C.map i j hi hj hij)) →
    (∀ i hi, Strong (U.incl i hi)) →
    Mem N →
    (∀ i hi, Strong (g i hi)) →
    (∀ i j hi hj hij, (g j hj).comp (C.map i j hi hj hij) = g i hi) →
    ∃ f : Language.Embedding τ U.obj.carrier N.carrier,
      Strong f ∧ ∀ i hi, f.comp (U.incl i hi) = g i hi
  /-- Some Löwenheim–Skolem bound `ℓ ≥ |τ| + ℵ₀`. -/
  lsBound : Cardinal.{u}
  lsBound_infinite : aleph0 ≤ lsBound
  lsBound_language : τ.card + aleph0 ≤ lsBound
  ls_axiom : ∀ (M : Model τ), Mem M → ∀ A : Set M.carrier,
    ∃ N : Model τ, ∃ f : Language.Embedding τ N.carrier M.carrier,
      Mem N ∧ Strong f ∧ (∀ a ∈ A, ∃ n, f n = a) ∧
      Model.card N ≤ mk A + lsBound

end
end AEC
