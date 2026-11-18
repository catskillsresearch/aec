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

set_option maxHeartbeats 1600000 in
/-- **Testing theorem for tied freeness.** If `q` over `B` agrees with the tied free lift `qB`
of `q ↾ A` on every bounded test `Z ⊆ B` of size `≤ g(σ) + LS(K)`, then `q` is tied-free from
`A` (Theorem 6.6 testing via `infra_73_differing_test`, then the free lift's answers carried to
`q`, as in `infra_78_tiedFree_of_upTo`). -/
theorem infra_75_tiedFree_of_tests
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ)
    (htest : ∀ (qB : TupleOver K oneVertexShape P.scheme hμ B)
      (eB : (q.restrict f hf).idx ≃ qB.idx), qB.ν = μ →
      IsTiedFree f (q.restrict f hf) qB eB →
      ∀ (β : Type u) (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
        #β ≤ P.g σ + ls K →
        P.scheme.DiagramEq (X := qB.host) (Y := q.host)
          (infra_612_anchored eB qB.incl qB.val Z)
          (infra_612_anchored (Equiv.refl q.idx) q.incl q.val Z)) :
    IsTiedFree f (q.restrict f hf) q (Equiv.refl _) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  have hidxμ : #q.idx < μ := hidx.trans_lt hσlt
  obtain ⟨qB, eB, hBν, -, hTB⟩ :=
    infra_610_tied_free_lift P σ hσ hμ hrec hσμ f hf (q.restrict f hf) hqν hidx
  have hidxB : #qB.idx ≤ σ := by rw [← Cardinal.mk_congr eB]; exact hidx
  have hS : SameGaloisType qB q eB.symm (Equiv.refl q.idx).symm := by
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ :=
      infra_73_differing_test P σ hσ hμ hrec hσμ qB q eB.symm (Equiv.refl q.idx).symm hBν hqν
        hidxB (hidxB.trans_lt hσlt) hneq
    apply hnot
    have d := htest qB eB hBν hTB β Y hβ
    exact infra_73_diagramEq_of_eq d (fun t => by cases t <;> rfl)
      (fun t => by cases t <;> rfl)
  intro seq' ι Z Z0' hlong' hι' hιμ hmv
  have dL := hTB seq' Z Z0' hlong' hι' hιμ hmv
  have dS := infra_72_diagramEq_of_sameGalois (P := P) hS Z hBν hqν hidxμ hιμ
  have dS' : P.scheme.DiagramEq (X := qB.host) (Y := q.host)
      (infra_612_anchored eB qB.incl qB.val Z)
      (infra_612_anchored (Equiv.refl q.idx) q.incl q.val Z) :=
    infra_73_diagramEq_of_eq dS (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  exact P.scheme.diagram_trans q.host qB.host q.host _ _ _ dL dS'

/-- **Prop 7.5(3), level form: free evaluation on bounded tests (statement; open tip
`infra_75_free_eval_level`).** Under the hypotheses of `infra_75_product_free_level_statement`,
`x` agrees with every tied free lift of `x ↾ X` on every bounded test `Z ⊆ Y` of size at most
the testing arity: the paper's "symmetry and projection give the free evaluation of `x` on
every bounded test `c` from `Y`". -/
def infra_75_free_eval_level_statement (P : SingleModelData K) : Prop :=
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
        ∀ (qB : TupleOver K oneVertexShape P.scheme hμ Y)
          (eB : (x.restrict f hf).idx ≃ qB.idx), qB.ν = μ →
          IsTiedFree f (x.restrict f hf) qB eB →
          ∀ (β : Type u) (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
            #β ≤ P.g σ + ls K →
            P.scheme.DiagramEq (X := qB.host) (Y := x.host)
              (infra_612_anchored eB qB.incl qB.val Z)
              (infra_612_anchored (Equiv.refl x.idx) x.incl x.val Z)

/-- **Prop 7.5(3), level form, from free evaluation on bounded tests** (testing theorem). -/
theorem infra_75_product_free_level_of_eval (P : SingleModelData K)
    (h : infra_75_free_eval_level_statement P) : infra_75_product_free_level_statement P :=
  fun σ hσ _ hμ hrec hσμ X Y f hf bIdx b hb hdom x hxν hxσ hprod =>
    infra_75_tiedFree_of_tests P σ hσ hμ hrec hσμ f hf x hxν hxσ
      (h σ hσ hμ hrec hσμ X Y f hf bIdx b hb hdom x hxν hxσ hprod)

end
end AEC
