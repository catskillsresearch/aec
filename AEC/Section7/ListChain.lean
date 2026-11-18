module

public import AEC.Section7.ProductIndependent
public import AEC.Section7.AllDominated
public import AEC.Section6.FreeExtension
public import AEC.Section5.NamedWorkingScheme

/-!
# List-linked witnessing chains (Definition 7.10, restated)

The original `WitnessingChain` carried its own marks with no link to a given `TupleList`, so
"`L` has a witnessing chain" was satisfied by the empty chain (see
`AEC/Audit/WitnessingChainVacuous.lean`).  `ListWitnessingChain L` fixes this: the chain is
indexed by the (well-ordered) positions of `L`, its stages are `M_j` for `j ≤ δ`
(`j : WithTop L.δ`, with `⊤` the final stage `M_δ`), `M_0 = A`, stages are continuous at limits,
and the whole configuration `(M_δ, (b_i)_i)` is coupled with the list `L` in one ambient
`top`, the mark of position `i` being sent to `L.val i`.
-/

@[expose] public section

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {A : W.Object μ hμ}

/-- The whole tuple of a list, indexed by `Σ i, L.indexAt i`. -/
def TupleList.whole (L : TupleList W hμ A) : TupleOver K S W hμ A where
  ν := μ
  hν := hμ
  host := L.host
  incl := L.incl
  incl_arrow := L.incl_arrow
  idx := Σ i, L.indexAt i
  val := fun p => L.val p.1 p.2

/-- **Definition 7.10 (list-linked).** A witnessing chain for the list `L = (bᵢ)_{i<δ}` over `A`:
stages `M_j` (`j ≤ δ`) with `M_0 = A`, continuous at limits, `bᵢ ∈ M_j` for every `j > i`,
`tp(bᵢ/Mᵢ)` free from `A`, and the configuration coupled with `L` in one ambient `top`. -/
structure ListWitnessingChain (L : TupleList W hμ A) [LinearOrder L.δ] where
  stage : WithTop L.δ → W.Object μ hμ
  into : ∀ j, SystemArrow K S (W.asSystem hμ A) (W.asSystem hμ (stage j))
  into_arrow : ∀ j, W.permitted (X := A) (Y := stage j) (into j)
  step : ∀ {i j : WithTop L.δ}, i ≤ j →
    SystemArrow K S (W.asSystem hμ (stage i)) (W.asSystem hμ (stage j))
  step_arrow : ∀ {i j : WithTop L.δ} (h : i ≤ j), W.permitted (X := stage i) (Y := stage j) (step h)
  step_comp : ∀ {i j k : WithTop L.δ} (hij : i ≤ j) (hjk : j ≤ k) (v : S.Vertex),
    ((step hjk).onVertex v).comp ((step hij).onVertex v) = (step (hij.trans hjk)).onVertex v
  into_step : ∀ {i j : WithTop L.δ} (h : i ≤ j) (v : S.Vertex),
    ((step h).onVertex v).comp ((into i).onVertex v) = (into j).onVertex v
  /-- `M_0 = A`: the first stage is `A` itself. -/
  first : ∀ i, (∀ k, i ≤ k) → ∀ v, Function.Bijective ((into i).onVertex v)
  /-- Continuity: at a stage that is neither first nor a successor, `M_j = ⋃_{i<j} M_i`. -/
  continuous : ∀ j, (∀ i, ¬ i ⋖ j) → (∃ i, i < j) → ∀ v (x : ((W.asSystem hμ (stage j)).obj v).carrier),
    ∃ i, ∃ h : i < j, ∃ y, (step h.le).onVertex v y = x
  /-- The ambient coupling the whole chain with the list. -/
  top : W.Object μ hμ
  toTop : SystemArrow K S (W.asSystem hμ (stage ⊤)) (W.asSystem hμ top)
  toTop_arrow : W.permitted (X := stage ⊤) (Y := top) toTop
  listToTop : SystemArrow K S (W.asSystem hμ L.host) (W.asSystem hμ top)
  listToTop_arrow : W.permitted (X := L.host) (Y := top) listToTop
  comm_A : ∀ v, (toTop.onVertex v).comp ((into ⊤).onVertex v) =
    (listToTop.onVertex v).comp (L.incl.onVertex v)
  /-- `bᵢ` lies in every stage `M_j`, `j > i`. -/
  mark : ∀ (i : L.δ) (j : WithTop L.δ), (i : WithTop L.δ) < j →
    L.indexAt i → Occurrence K S (W.asSystem hμ (stage j))
  mark_step : ∀ (i : L.δ) {j k : WithTop L.δ} (hj : (i : WithTop L.δ) < j) (hjk : j ≤ k)
    (a : L.indexAt i), (step hjk).mapOcc (mark i j hj a) = mark i k (lt_of_lt_of_le hj hjk) a
  /-- The mark is the list entry, in the common ambient. -/
  mark_spec : ∀ (i : L.δ) (a : L.indexAt i),
    toTop.mapOcc (mark i ⊤ (WithTop.coe_lt_top i) a) = listToTop.mapOcc (L.val i a)
  /-- `tp(bᵢ/Mᵢ)` is the free lift of `tp(bᵢ/A)`. -/
  free : ∀ i : L.δ, IsFreeFrom (into (i : WithTop L.δ)) (into_arrow _)
    (asTuple (step (le_top : (i : WithTop L.δ) ≤ ⊤)) (step_arrow _) (mark i ⊤ (WithTop.coe_lt_top i)))

namespace ListWitnessingChain

variable {L : TupleList W hμ A} [LinearOrder L.δ]

/-- **Definition 7.10.** All-dominated increments: `M_{i+1}` is all-dominated over `Mᵢ + bᵢ`. -/
def AllDominatedIncrement (C : ListWitnessingChain L) : Prop :=
  ∀ (i : L.δ) (j : WithTop L.δ) (h : (i : WithTop L.δ) ⋖ j),
    AllDominated (C.step h.le) (C.step_arrow h.le) (L.indexAt i) (C.mark i j h.lt)

/-- The finite selection `(b_{ix s})_s` of marks, as a tuple over `A` hosted with a coupled
tuple `x` over `M_δ`. -/
def selectionOver (C : ListWitnessingChain L) (x : TupleOver K S W hμ (C.stage ⊤)) (n : ℕ)
    (ix : Fin n → L.δ) : TupleOver K S W hμ A where
  ν := x.ν
  hν := x.hν
  host := x.host
  incl := SystemArrow.comp (C.into ⊤) x.incl
  incl_arrow := W.comp (C.into ⊤) x.incl (C.into_arrow ⊤) x.incl_arrow
  idx := Σ s : Fin n, L.indexAt (ix s)
  val := fun p => x.incl.mapOcc (C.mark (ix p.1) ⊤ (WithTop.coe_lt_top _) p.2)

/-- Joint of a coupled tuple `x` with a finite selection of marks, over `A`. -/
def jointWith (C : ListWitnessingChain L) (x : TupleOver K S W hμ (C.stage ⊤)) (n : ℕ)
    (ix : Fin n → L.δ) : TupleOver K S W hμ A where
  ν := x.ν
  hν := x.hν
  host := x.host
  incl := SystemArrow.comp (C.into ⊤) x.incl
  incl_arrow := W.comp (C.into ⊤) x.incl (C.into_arrow ⊤) x.incl_arrow
  idx := x.idx ⊕ (Σ s : Fin n, L.indexAt (ix s))
  val := fun
    | Sum.inl k => x.val k
    | Sum.inr p => x.incl.mapOcc (C.mark (ix p.1) ⊤ (WithTop.coe_lt_top _) p.2)

end ListWitnessingChain

end
end AEC
