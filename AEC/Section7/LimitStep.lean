module

public import AEC.Section7.SuccessorStep

@[expose] public section

/-!
# Matrix limit step of Proposition 7.8: chain unions at a level (`infra_78_chain_union_kappa`)

A directed family of objects at an eligible level `κ` (at most `κ` indices, identity and
composition laws) has a union object at `κ` with commuting, jointly covering legs and the
universal property. This is the chain-union existence needed by `infra_78_matrix_limit_step`;
it comes from the chain axioms of `K` (`SingleModelData.exists_directed_union`, Lemma 2.1),
with no new axioms. The remaining limit-step pieces are tracked on the board:
`infra_78_limit_pair` (union pair, cocone arrows extending the composition law, commuting
square, continuity at the limit) and `infra_78_limit_invariant5` (invariant (5) at limits,
the bounded-mark Def 7.7 continuity).
-/

universe u

open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}

/-- **Chain unions at a level** (sub-tip of `infra_78_matrix_limit_step`). A directed family of
objects at an eligible level `κ`, indexed by at most `κ` indices, with arrows obeying the
identity and composition laws, has a union object at `κ`: legs commuting with the arrows,
jointly covering the union, and the universal property (existence and uniqueness of the induced
arrow into any object at any level). From the chain axioms of `K` via
`SingleModelData.exists_directed_union`; no new axioms. -/
theorem infra_78_chain_union_kappa {P : SingleModelData K} {κ : Cardinal.{u}}
    (hκ : κ ∈ P.eligible) {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (hι : #ι ≤ κ) (X : ι → P.scheme.Object κ hκ)
    (st : ∀ {a b : ι}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a)) (P.scheme.asSystem hκ (X b)))
    (hrefl : ∀ a, st (le_refl a) = SystemArrow.refl _)
    (htrans : ∀ {a b c : ι} (h₁ : a ≤ b) (h₂ : b ≤ c),
      st (h₁.trans h₂) = SystemArrow.comp (st h₁) (st h₂)) :
    ∃ (U : P.scheme.Object κ hκ)
      (leg : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a))
        (P.scheme.asSystem hκ U)),
      (∀ a, P.scheme.permitted (X := X a) (Y := U) (leg a)) ∧
      (∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (st h) (leg b) = leg a) ∧
      (∀ x : Occurrence K oneVertexShape (P.scheme.asSystem hκ U),
        ∃ a, ∃ y : Occurrence K oneVertexShape (P.scheme.asSystem hκ (X a)),
          pushOcc (leg a) y = x) ∧
      (∀ {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} (Z : P.scheme.Object ν hν)
        (g : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a))
          (P.scheme.asSystem hν Z)),
        (∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (st h) (g b) = g a) →
        ∃ f : SystemArrow K oneVertexShape (P.scheme.asSystem hκ U) (P.scheme.asSystem hν Z),
          P.scheme.permitted (X := U) (Y := Z) f ∧ ∀ a, SystemArrow.comp (leg a) f = g a) ∧
      (∀ {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} (Z : P.scheme.Object ν hν)
        (f f' : SystemArrow K oneVertexShape (P.scheme.asSystem hκ U) (P.scheme.asSystem hν Z)),
        (∀ a, SystemArrow.comp (leg a) f = SystemArrow.comp (leg a) f') → f = f') := by
  classical
  let S : DirectedSystem K.τ :=
    { ι := ι
      nonempty := inferInstance
      rel := (· ≤ ·)
      refl := le_refl
      trans := le_trans
      directed := fun a b => exists_ge_ge a b
      obj := fun a => (X a).model
      map := fun h => (st h).onVertex PUnit.unit
      map_refl := fun a => by
        rw [hrefl a]
        rfl
      map_trans := fun h₁ h₂ => by
        rw [htrans h₁ h₂]
        rfl }
  obtain ⟨U, incl, hincl, hcompat, hcover, huniv⟩ :=
    SingleModelData.exists_directed_union (P := P) hκ S (fun a => (X a).mem)
      (fun a => (X a).card) (fun h => (st h).onVertex_strong PUnit.unit) hι
  let leg : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a))
      (P.scheme.asSystem hκ U) := fun a =>
    oneVertexArrow (hM := (X a).mem) (hN := U.mem) (incl a) (hincl a)
  refine ⟨U, leg, fun _ => trivial, ?_, ?_, ?_, ?_⟩
  · intro a b h
    apply SystemArrow.ext
    intro v
    exact hcompat h
  · rintro ⟨v, x⟩
    obtain ⟨a, y, hy⟩ := hcover x
    cases v
    exact ⟨a, ⟨PUnit.unit, y⟩, by
      show (⟨PUnit.unit, incl a y⟩ : Occurrence K oneVertexShape (P.scheme.asSystem hκ U)) = _
      rw [hy]⟩
  · intro ν hν Z g hg
    obtain ⟨f, hf, hfg⟩ := huniv Z.model (fun a => (g a).onVertex PUnit.unit) Z.mem
      (fun a => (g a).onVertex_strong PUnit.unit)
      (fun h => congrArg (fun e => e.onVertex PUnit.unit) (hg h))
    refine ⟨oneVertexArrow (hM := U.mem) (hN := Z.mem) f hf, trivial, fun a => ?_⟩
    apply SystemArrow.ext
    intro v
    exact hfg a
  · intro ν hν Z f f' hff
    apply SystemArrow.ext
    intro v
    cases v
    ext x
    obtain ⟨a, y, hy⟩ := hcover x
    rw [← hy]
    exact DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hff a)) y

end AEC
