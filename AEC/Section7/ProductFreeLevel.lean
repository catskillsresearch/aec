module

public import AEC.Section7.TiedListChain

/-!
# Proposition 7.5(3), actual-coupling level form (statement)

English Proposition 7.5(3): "In an actual coupling, if a bounded tuple `x` has product with `b`
over `X`, then `tp(x/Y)` is free from `X`" (for `Y` all-dominated over `X + b`).

`infra_75_product_free_level_statement` is the narrowed form used by Lemma 7.11's successor
step: the coupling is actual (`x.ν = μ`), so `x`, the copy of `b` and their joint are all
hosted at the level `μ` of `X`, and the 6.12 product facts needed are exactly the proved
level-joint cases (`infra_612_tied_symm_level_joints`, `infra_612_tied_finite_proj_level`,
`infra_612_tied_base_change_level_joints`). The general clause (any bounded `x`, any host
level) stays tracked as `infra_75_product_free`.
-/

@[expose] public section

namespace AEC
noncomputable section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}

/-- The marks `b ⊆ Y`, read as a tuple over `X` hosted with `x`. -/
def infra_75_markOver {X Y : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (x : TupleOver K oneVertexShape P.scheme hμ Y) {bIdx : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)) :
    TupleOver K oneVertexShape P.scheme hμ X where
  ν := x.ν
  hν := x.hν
  host := x.host
  incl := SystemArrow.comp f x.incl
  incl_arrow := P.scheme.comp f x.incl hf x.incl_arrow
  idx := bIdx
  val := fun k => x.incl.mapOcc (b k)

/-- The joint `(x, b)` over `X`. -/
def infra_75_jointOver {X Y : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (x : TupleOver K oneVertexShape P.scheme hμ Y) {bIdx : Type u}
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)) :
    TupleOver K oneVertexShape P.scheme hμ X where
  ν := x.ν
  hν := x.hν
  host := x.host
  incl := SystemArrow.comp f x.incl
  incl_arrow := P.scheme.comp f x.incl hf x.incl_arrow
  idx := x.idx ⊕ bIdx
  val := fun
    | Sum.inl k => x.val k
    | Sum.inr k => x.incl.mapOcc (b k)

/-- **Proposition 7.5(3), actual coupling, level joints (statement; open tip
`infra_75_product_free_level`).** -/
def infra_75_product_free_level_statement (P : SingleModelData K) : Prop :=
  ∀ (σ : Cardinal.{u}), ℵ₀ ≤ σ → ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible),
    μ ∈ recursionClosedLevels P σ → Order.succ σ ≤ μ →
    ∀ (X Y : P.scheme.Object μ hμ)
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
      (hf : P.scheme.permitted (X := X) (Y := Y) f)
      (bIdx : Type u) (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      #bIdx ≤ σ → AllDominated f hf bIdx b →
      ∀ x : TupleOver K oneVertexShape P.scheme hμ Y, x.ν = μ → #x.idx ≤ σ →
        IsProductTied (x.restrict f hf) (infra_75_markOver f hf x b)
          (infra_75_jointOver f hf x b) (Equiv.refl _) →
        IsTiedFree f (x.restrict f hf) x (Equiv.refl _)

end
end AEC
