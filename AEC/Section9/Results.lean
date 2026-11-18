module

public import AEC.Section5.EmptiedScheme
public import AEC.Section9.BoundaryMap
public import AEC.Section9.CubeScheme
public import AEC.Section9.Projection
public import AEC.Section6.Results
public import AEC.Section5.Results
public import AEC.Section4.StableDiagram

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Proposition 9.1** (Type correspondence under projection). Let `P : C → D` forget some
components, both schemes working packages, `P` taking objects and arrows (including mixed) to
objects and arrows, and the diagram comparison holding on bounded retained tuples. At
sufficiently closed levels, restriction induces a bijection `tp_C(v/X) ↦ tp_D(v/PX)` on types of
bounded tuples in retained sorts, commuting with free lifting along arrows, including mixed ones.

**Statement (restated, honest form, open):** the projection is explicit
(`AEC/Section9/Projection.lean`, `SchemeProjection`, `Comparison`). On a tail `T`:
(1) injectivity + well-definedness: two bounded retained tuples over `X` have the same `C`-type
iff their projections have the same `D`-type over `P X`; (2) surjectivity: every bounded `D`-type
over `P X` is the projection of a retained `C`-type over `X`; (3) free lifts correspond along
permitted arrows between levels of `T` with arities below the smaller level. Witnessed free
products and the commutation with isomorphisms are not stated. The former statement had no
projection (it only restated `diagram_preserved`) and was degenerate. -/
theorem proposition_9_1 {K : AbstractElementaryClass.{u}} {S S' : SystemShape.{u}}
    (C : WorkingScheme K S) (D : WorkingScheme K S')
    (hC : IsWorkingPackage C) (hD : IsWorkingPackage D)
    (P : SchemeProjection C D) (hP : P.Comparison) :
    ∃ T, ∃ hT : Tail C.eligible T,
      (∀ μ (hμ : μ ∈ T) (X : C.Object μ (Tail.mem hT hμ))
        (p q : P.RetainedOver (Tail.mem hT hμ) X) (e : p.idx ≃ q.idx), #q.idx < μ →
        (SameGaloisType p.toFull q.toFull e (Equiv.refl _) ↔
          SameGaloisType p.toProj q.toProj e (Equiv.refl _))) ∧
      (∀ μ (hμ : μ ∈ T) (X : C.Object μ (Tail.mem hT hμ))
        (q : TupleOver K S' D (P.levels (Tail.mem hT hμ)) (P.obj X)), #q.idx < μ →
        ∃ (p : P.RetainedOver (Tail.mem hT hμ) X) (e : p.idx ≃ q.idx),
          SameGaloisType p.toProj q e (Equiv.refl _)) ∧
      (∀ μ (hμ : μ ∈ T) ν (hν : ν ∈ T)
        (X : C.Object μ (Tail.mem hT hμ)) (Y : C.Object ν (Tail.mem hT hν))
        (f : SystemArrow K S (C.asSystem _ X) (C.asSystem _ Y))
        (hf : C.permitted (X := X) (Y := Y) f)
        (p : P.RetainedOver (Tail.mem hT hμ) X) (q : P.RetainedOver (Tail.mem hT hν) Y)
        (e : p.idx ≃ q.idx), #q.idx < min μ ν →
        (IsFreeLift p.toFull q.toFull f hf e ↔
          IsFreeLift p.toProj q.toProj (P.arr X Y f hf) (P.arr_permitted X Y f hf) e)) := by
  sorry

/-- **Corollary 9.2** (Lifting an extension of a projection). Under the hypotheses of
Proposition 9.1, let `X` and `Z` be at the same eligible level and `PX → Z` an arrow. There are a
`C`-extension `X → X*` and a `D`-arrow `Z → PX*` whose composite on `PX` is the projection of
`X → X*`.

**Statement (restated, honest form, open):** with the explicit `SchemeProjection`; `X*` is a
`C`-object at the same level, `g : X → X*` is `C`-permitted, `h : Z → P X*` is `D`-permitted and
`f ≫ h = P g` vertexwise. The former statement had no projection (witness `X' := Z`) and was
degenerate. -/
theorem corollary_9_2 {K : AbstractElementaryClass.{u}} {S S' : SystemShape.{u}}
    (C : WorkingScheme K S) (D : WorkingScheme K S')
    (hC : IsWorkingPackage C) (hD : IsWorkingPackage D)
    (P : SchemeProjection C D) (hP : P.Comparison) :
    ∃ T, ∃ hT : Tail C.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : C.Object μ (Tail.mem hT hμ))
        (Z : D.Object μ (P.levels (Tail.mem hT hμ)))
        (f : SystemArrow K S' (D.asSystem _ (P.obj X)) (D.asSystem _ Z)),
        D.permitted (X := P.obj X) (Y := Z) f →
        ∃ (Xs : C.Object μ (Tail.mem hT hμ))
          (g : SystemArrow K S (C.asSystem _ X) (C.asSystem _ Xs))
          (hg : C.permitted (X := X) (Y := Xs) g)
          (h : SystemArrow K S' (D.asSystem _ Z) (D.asSystem _ (P.obj Xs))),
          D.permitted (X := Z) (Y := P.obj Xs) h ∧
          ∀ v, (h.onVertex v).comp (f.onVertex v) = (P.arr X Xs g hg).onVertex v := by
  sorry

/-- **Theorem 9.3** (Finite marked systems). For each finite `n` the `n`-fold marked increment
of the single-model scheme is a working scheme at sufficiently closed levels.

**Statement (restated, honest form, open):** there is a cube scheme `C_n`
(`AEC/Section9/CubeScheme.lean`: a working scheme on the `n`-cube shape whose objects are face
families) that is a working package with objects at every eligible level (`CubeScheme.IsMarked`),
and whose increments are proper: along a strict inclusion of axis sets the specified map is not
onto (each new axis adds a realization of the prescribed mark). The object-free scheme no longer
satisfies it. Assumes `[CategoricalUnbounded K]` (without it the statement is false,
`AEC.Audit.theorem_9_3_unconditional_false`).

**Caveat:** the marked-increment construction itself (Definition 8.1 iterated over the axes) is
not yet formalized, so the link "`C_n` is the marked increment of the single-model scheme" is
captured only by the properness clause; the previous degenerate proof via
`WorkingScheme.emptied` is retired. -/
theorem theorem_9_3 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K] (n : ℕ) :
    ∃ C : CubeScheme K n, C.IsMarked ∧
      ∀ μ (hμ : μ ∈ C.W.eligible) (X : C.W.Object μ hμ) (s t : Set (Fin n)) (h : s ⊂ t),
        ¬ Function.Surjective ((C.faces hμ X).incl h.subset) := by
  sorry

/-- **Lemma 9.5** (Joint diagrams on the boundary). A boundary map between same-level `n`-axis
objects preserves bounded diagrams of their boundary unions. -/
theorem lemma_9_5 (K : AbstractElementaryClass.{u}) (n : ℕ)
    (J Kf : FaceFamily K n) (h : BoundaryMap K J Kf) (D : StableDiagram K)
    (hpres : ∀ {M N : Model K.τ} {β : Type u}
        (f : Language.Embedding K.τ M.carrier N.carrier) (zs : β → M.carrier)
        (σ : Cardinal.{u}) (hσ : #β ≤ σ) (hM : K.Mem M) (hN : K.Mem N)
        (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N),
        K.Strong f → D.same hσ hM hN hMcard hNcard zs (fun i => f (zs i)))
    (htrans : ∀ {M N P : Model K.τ} {β : Type u}
        (xs : β → M.carrier) (ys : β → N.carrier) (zs : β → P.carrier)
        (σ : Cardinal.{u}) (hσ : #β ≤ σ)
        (hM : K.Mem M) (hN : K.Mem N) (hP : K.Mem P)
        (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N)
        (hPcard : D.t σ ≤ Model.card P),
        D.same hσ hM hN hMcard hNcard xs ys →
        D.same hσ hN hP hNcard hPcard ys zs →
        D.same hσ hM hP hMcard hPcard xs zs) :
    ∀ {α : Type u} (s : Set (Fin n)) (hs : IsProper s)
      (xs : α → (J.obj s).carrier) (σ : Cardinal.{u})
      (hσ : #α ≤ σ)
      (hfaceJ : D.t σ ≤ Model.card (J.obj s))
      (hfaceK : D.t σ ≤ Model.card (Kf.obj s))
      (htopJ : D.t σ ≤ Model.card (J.obj Set.univ))
      (htopK : D.t σ ≤ Model.card (Kf.obj Set.univ)),
      D.same hσ (J.inK Set.univ) (Kf.inK Set.univ) htopJ htopK
        (fun i => J.incl (Set.subset_univ s) (xs i))
        (fun i => Kf.incl (Set.subset_univ s) (h.onFace hs (xs i))) := by
  intro α s hs xs σ hσ hfaceJ hfaceK htopJ htopK
  have h1 := hpres (J.incl (Set.subset_univ s)) xs σ hσ (J.inK s) (J.inK Set.univ)
    hfaceJ htopJ (J.incl_strong _)
  have h2 := hpres (h.onFace hs) xs σ hσ (J.inK s) (Kf.inK s) hfaceJ hfaceK
    (h.onFace_strong hs)
  have h3 := hpres (Kf.incl (Set.subset_univ s)) (fun i => h.onFace hs (xs i)) σ hσ
    (Kf.inK s) (Kf.inK Set.univ) hfaceK htopK (Kf.incl_strong _)
  exact htrans _ _ _ σ hσ _ _ _ _ _ _
    (htrans _ _ _ σ hσ _ _ _ _ _ _
      (D.symm hσ _ _ _ _ _ _ h1) h2) h3

/-- **Theorem 9.6** (Amalgamated boundary completion). For each finite `n`, at sufficiently
closed levels: if `J`, `K` are `C_n`-objects at the same level and `h : ∂J → ∂K` is a boundary
map, there are arrows `J → K*`, `K → K*` in `C_n` (same scheme, same level) such that the
first restricts to the composite of `h` with the second on every proper projection.

**Statement (restated, honest form, open):** `C_n` is a marked cube scheme
(`CubeScheme.IsMarked`), `J`, `Kf`, `Star` are its objects at one level, and `toJ`, `toK` are
permitted system arrows of the whole cube, tops included. The former statement asked only for
boundary maps into a face family (no top arrows) and was proved degenerately by `Star := Kf`. -/
theorem theorem_9_6 (K : AbstractElementaryClass.{u}) (n : ℕ) (C : CubeScheme K n)
    (hC : C.IsMarked) :
    ∃ T, ∃ hT : Tail C.W.eligible T,
      ∀ μ (hμ : μ ∈ T) (J Kf : C.W.Object μ (Tail.mem hT hμ))
        (h : BoundaryMap K (C.faces _ J) (C.faces _ Kf)),
        ∃ (Star : C.W.Object μ (Tail.mem hT hμ))
          (toJ : SystemArrow K (cubeShape.{u} n) (C.W.asSystem _ J) (C.W.asSystem _ Star))
          (toK : SystemArrow K (cubeShape.{u} n) (C.W.asSystem _ Kf) (C.W.asSystem _ Star)),
          C.W.permitted (X := J) (Y := Star) toJ ∧ C.W.permitted (X := Kf) (Y := Star) toK ∧
          ∀ (s : Set (Fin n)) (hs : IsProper s) (x : ((C.faces _ J).obj s).carrier),
            toJ.onVertex ⟨s⟩ x = toK.onVertex ⟨s⟩ (h.onFace hs x) := by
  sorry

/-- An element of a proper projection of a face family (a boundary element). -/
abbrev BoundaryElt {K : AbstractElementaryClass.{u}} {n : ℕ} (J : FaceFamily K n) : Type u :=
  Σ s : {s : Set (Fin n) // IsProper s}, (J.obj s.1).carrier

/-- **Lemma 9.7** (Fixed parameters for a boundary test function). Fix `n`. At further
sufficiently closed levels, let `J ∈ C_n`, `z` a bounded tuple of `J`, `σ` a bounded infinite
test arity. There is a bounded list `a` in `∂J` such that every boundary automorphism fixing
`a` pointwise satisfies `D_J(z, u) = D_J(z, α(u))` for every boundary tuple `u` of length at
most `σ`.

**Statement (restated, honest form, open):** `J` is an object of a marked cube scheme
(`CubeScheme.IsMarked`), boundary tuples are occurrences in proper projections, and `D_J` is the
scheme's `DiagramEq` on occurrences of `J`. The former statement was about an arbitrary
`FaceFamily` with a `StableDiagram` on its top, where faces can be glued along a non-face overlap
(`AEC.Audit.lemma_9_7_false`). -/
theorem lemma_9_7 (K : AbstractElementaryClass.{u}) (n : ℕ) (C : CubeScheme K n)
    (hC : C.IsMarked) :
    ∃ T, ∃ hT : Tail C.W.eligible T,
      ∀ μ (hμ : μ ∈ T) (J : C.W.Object μ (Tail.mem hT hμ)) {α : Type u}
        (z : α → Occurrence K (cubeShape.{u} n) (C.W.asSystem _ J)) (σ : Cardinal.{u}),
        #α < μ → aleph0 ≤ σ → σ < μ →
        ∃ (β : Type u) (a : β → BoundaryElt (C.faces _ J)), #β < μ ∧
          ∀ (h : BoundaryMap K (C.faces _ J) (C.faces _ J)), IsBoundaryIso h →
            (∀ i, h.onFace (a i).1.2 (a i).2 = (a i).2) →
            ∀ {ι : Type u} (t : ι → BoundaryElt (C.faces _ J)), #ι ≤ σ →
              C.W.DiagramEq (X := J) (Y := J)
                (Sum.elim z (fun k => C.boundaryOcc J (t k).1.1 (t k).2))
                (Sum.elim z (fun k => C.boundaryOcc J (t k).1.1 (h.onFace (t k).1.2 (t k).2))) := by
  sorry

/-- **Theorem 9.8** (Exact boundary lifting). For each finite `n`, at further sufficiently
closed levels every boundary isomorphism `h : ∂J ≃ ∂K` between `C_n`-objects at the same level
extends to an isomorphism `J ≃ K` onto the given target, preserving marks and named data.

**Statement (restated, honest form, open):** `J`, `Kf` are objects at one level of a marked
cube scheme (`CubeScheme.IsMarked`) and the extension is a structural isomorphism of the scheme
(`IsStructIso`, which carries the marks/names) agreeing with `h` on every proper projection.
The former statement was about arbitrary face families and failed already on `0` axes
(`AEC.Audit.theorem_9_8_arbitrary_false`). -/
theorem theorem_9_8 (K : AbstractElementaryClass.{u}) (n : ℕ) (C : CubeScheme K n)
    (hC : C.IsMarked) :
    ∃ T, ∃ hT : Tail C.W.eligible T,
      ∀ μ (hμ : μ ∈ T) (J Kf : C.W.Object μ (Tail.mem hT hμ))
        (h : BoundaryMap K (C.faces _ J) (C.faces _ Kf)), IsBoundaryIso h →
        ∃ e : SystemArrow K (cubeShape.{u} n) (C.W.asSystem _ J) (C.W.asSystem _ Kf),
          C.W.IsStructIso (X := J) (Y := Kf) e ∧
          ∀ (s : Set (Fin n)) (hs : IsProper s) (x : ((C.faces _ J).obj s).carrier),
            e.onVertex ⟨s⟩ x = h.onFace hs x := by
  sorry

end
end AEC
