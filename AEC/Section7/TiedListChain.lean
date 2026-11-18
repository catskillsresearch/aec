module

public import AEC.Section7.ListChain
public import AEC.Section6.ProductTied

/-!
# Tied list-linked witnessing chains (Definition 7.10, tied form)

`ListWitnessingChain` (in `ListChain.lean`) records "`tp(bᵢ/Mᵢ)` is the free lift of
`tp(bᵢ/A)`" with the untied `IsFreeFrom`, which is vacuous
(`AEC/Audit/FreeFromVacuous.lean`).  `TiedListWitnessingChain L` is the same configuration over
`SingleModelData`, with that clause read as tied freeness:
`IsTiedFree (A → Mᵢ) tp(bᵢ/A) tp(bᵢ/Mᵢ)`, i.e. `tp(bᵢ/Mᵢ) = tp(bᵢ/A)^fr_{Mᵢ}` (Theorem 6.10's
free lift).  Everything else (stages `M_j`, `j ≤ δ`, `M_0 = A`, continuity at limits, marks
coupled with the list `L` in one ambient) is as in `ListWitnessingChain`.
-/

@[expose] public section

namespace AEC
noncomputable section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}} {P : SingleModelData K}
  {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}

/-- **Definition 7.10 (list-linked, tied).** A witnessing chain for the list `L = (bᵢ)_{i<δ}`
over `A`: stages `M_j` (`j ≤ δ`) with `M_0 = A`, continuous at limits, `bᵢ ∈ M_j` for every
`j > i`, `tp(bᵢ/Mᵢ) = tp(bᵢ/A)^fr_{Mᵢ}` (tied), and the configuration coupled with `L` in one
ambient `top`. -/
structure TiedListWitnessingChain (L : TupleList P.scheme hμ A) [LinearOrder L.δ] where
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
  /-- `M_0 = A`: the first stage is `A` itself. -/
  first : ∀ i, (∀ k, i ≤ k) → ∀ v, Function.Bijective ((into i).onVertex v)
  /-- Continuity: at a stage that is neither first nor a successor, `M_j = ⋃_{i<j} M_i`. -/
  continuous : ∀ j, (∀ i, ¬ i ⋖ j) → (∃ i, i < j) →
    ∀ v (x : ((P.scheme.asSystem hμ (stage j)).obj v).carrier),
      ∃ i, ∃ h : i < j, ∃ y, (step h.le).onVertex v y = x
  /-- The ambient coupling the whole chain with the list. -/
  top : P.scheme.Object μ hμ
  toTop : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (stage ⊤)) (P.scheme.asSystem hμ top)
  toTop_arrow : P.scheme.permitted (X := stage ⊤) (Y := top) toTop
  listToTop : SystemArrow K oneVertexShape (P.scheme.asSystem hμ L.host) (P.scheme.asSystem hμ top)
  listToTop_arrow : P.scheme.permitted (X := L.host) (Y := top) listToTop
  comm_A : ∀ v, (toTop.onVertex v).comp ((into ⊤).onVertex v) =
    (listToTop.onVertex v).comp (L.incl.onVertex v)
  /-- `bᵢ` lies in every stage `M_j`, `j > i`. -/
  mark : ∀ (i : L.δ) (j : WithTop L.δ), (i : WithTop L.δ) < j →
    L.indexAt i → Occurrence K oneVertexShape (P.scheme.asSystem hμ (stage j))
  mark_step : ∀ (i : L.δ) {j k : WithTop L.δ} (hj : (i : WithTop L.δ) < j) (hjk : j ≤ k)
    (a : L.indexAt i), (step hjk).mapOcc (mark i j hj a) = mark i k (lt_of_lt_of_le hj hjk) a
  /-- The mark is the list entry, in the common ambient. -/
  mark_spec : ∀ (i : L.δ) (a : L.indexAt i),
    toTop.mapOcc (mark i ⊤ (WithTop.coe_lt_top i) a) = listToTop.mapOcc (L.val i a)
  /-- `tp(bᵢ/Mᵢ) = tp(bᵢ/A)^fr_{Mᵢ}`, tied (Theorem 6.10's free lift). -/
  free : ∀ i : L.δ,
    IsTiedFree (into (i : WithTop L.δ))
      ((asTuple (step (le_top : (i : WithTop L.δ) ≤ ⊤)) (step_arrow _)
          (mark i ⊤ (WithTop.coe_lt_top i))).restrict (into (i : WithTop L.δ)) (into_arrow _))
      (asTuple (step (le_top : (i : WithTop L.δ) ≤ ⊤)) (step_arrow _)
        (mark i ⊤ (WithTop.coe_lt_top i)))
      (Equiv.refl _)

namespace TiedListWitnessingChain

variable {L : TupleList P.scheme hμ A} [LinearOrder L.δ]

/-- **Definition 7.10.** All-dominated increments: `M_{i+1}` is all-dominated over `Mᵢ + bᵢ`. -/
def AllDominatedIncrement (C : TiedListWitnessingChain L) : Prop :=
  ∀ (i : L.δ) (j : WithTop L.δ) (h : (i : WithTop L.δ) ⋖ j),
    AllDominated (C.step h.le) (C.step_arrow h.le) (L.indexAt i) (C.mark i j h.lt)

/-- The finite selection `(b_{ix s})_s` of marks, as a tuple over `A` hosted with a coupled
tuple `x` over `M_δ`. -/
def selectionOver (C : TiedListWitnessingChain L)
    (x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤)) (n : ℕ)
    (ix : Fin n → L.δ) : TupleOver K oneVertexShape P.scheme hμ A where
  ν := x.ν
  hν := x.hν
  host := x.host
  incl := SystemArrow.comp (C.into ⊤) x.incl
  incl_arrow := P.scheme.comp (C.into ⊤) x.incl (C.into_arrow ⊤) x.incl_arrow
  idx := Σ s : Fin n, L.indexAt (ix s)
  val := fun p => x.incl.mapOcc (C.mark (ix p.1) ⊤ (WithTop.coe_lt_top _) p.2)

/-- Joint of a coupled tuple `x` with a finite selection of marks, over `A`. -/
def jointWith (C : TiedListWitnessingChain L)
    (x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤)) (n : ℕ)
    (ix : Fin n → L.δ) : TupleOver K oneVertexShape P.scheme hμ A where
  ν := x.ν
  hν := x.hν
  host := x.host
  incl := SystemArrow.comp (C.into ⊤) x.incl
  incl_arrow := P.scheme.comp (C.into ⊤) x.incl (C.into_arrow ⊤) x.incl_arrow
  idx := x.idx ⊕ (Σ s : Fin n, L.indexAt (ix s))
  val := fun
    | Sum.inl k => x.val k
    | Sum.inr p => x.incl.mapOcc (C.mark (ix p.1) ⊤ (WithTop.coe_lt_top _) p.2)

end TiedListWitnessingChain

end
end AEC
