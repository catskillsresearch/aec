module

public import AEC.Section5.EmptiedScheme
public import AEC.Section10.PointedModel
public import AEC.Section10.Forces
public import AEC.Section10.GeomClosure
public import AEC.Section10.ProductAxioms
public import AEC.Section6.FreeExtension
public import AEC.Section4.StableDiagram
public import AEC.Section6.Results
public import AEC.Section5.Results
public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Lemma 10.1** (Preservation of nonalgebraicity). Let `p` be a nonalgebraic singleton type
over an object `A` of a working scheme. Its free lift over an extension `B` is nonalgebraic. The
same holds for a mixed arrow whenever the input arity and the testing bounds lie below the
smaller level.

**Statement (restated, honest form, open):** `p` is an actual singleton type over `A`
(a `TupleOver` with one index) whose realization is not in the image of `A`; `q` over `B` is a
free lift of `p` along the permitted arrow `f : A → B` (`IsFreeLift`, which carries the
approximation sequence and hence the testing bounds, at the same or a mixed level); conclusion:
the realization of `q` is not in the image of `B`. The former statement quantified over every
strong `g` with `g a = b` and was proved from injectivity alone (degenerate). -/
theorem lemma_10_1 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (hW : IsWorkingPackage W)
    {μ ν : Cardinal.{u}} {hμ : μ ∈ W.eligible} {hν : ν ∈ W.eligible}
    {A : W.Object μ hμ} {B : W.Object ν hν}
    (f : SystemArrow K S (W.asSystem hμ A) (W.asSystem hν B))
    (hf : W.permitted (X := A) (Y := B) f)
    (p : TupleOver K S W hμ A) (q : TupleOver K S W hν B) (e : p.idx ≃ q.idx)
    (hsingle : Nonempty (p.idx ≃ PUnit.{u + 1}))
    (hp : ∀ i (x : ((W.asSystem hμ A).obj (p.val i).1).carrier),
      p.incl.onVertex (p.val i).1 x ≠ (p.val i).2)
    (hlift : IsFreeLift p q f hf e) :
    ∀ j (y : ((W.asSystem hν B).obj (q.val j).1).carrier),
      q.incl.onVertex (q.val j).1 y ≠ (q.val j).2 := by
  sorry

/-- **Proposition 10.2** (A minimal type). There is a sufficiently closed level `λ₀`, a model
`M₀` of that size, and a nonalgebraic singleton type over `M₀` with exactly one nonalgebraic
extension to any model of size `λ₀`.

**Statement change:** now assumes the paper's standing hypothesis `CategoricalUnbounded K`.
The unconditional form is false (`AEC.Audit.proposition_10_2_unconditional_false`: an AEC
whose models have at most one element). -/
theorem proposition_10_2 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K] :
    ∃ D : MinimalData K, aleph0 ≤ D.lam0 := by
  sorry

/-- **Lemma 10.4** (The containment test). For a finite independent set `S ⊆ P(M)` and
`x ∈ P(M)`, `S` fails to force `x` if and only if `S ∪ {x}` is independent with `x ∉ S`.

**Statement (restated, honest form, open):** adds the paper's standing hypotheses
(`CategoricalUnbounded K`, `M₀ ≤_K M` with `‖M‖ ≥ λ₀`), the product clauses of Definition 10.3
(`MinimalData.ProductAxioms`), and the missing hypothesis `x ∈ P(M)`. The former statement was
false for the abstract `productCopies` (`AEC.Audit.lemma_10_4_false`, `noPairs`, which violates
`ProductAxioms.step`). -/
theorem lemma_10_4 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K] (D : MinimalData K)
    (hD : D.ProductAxioms)
    (M : Model K.τ) (incl : Language.Embedding K.τ D.M0.carrier M.carrier)
    (hM : K.Mem M) (hincl : K.Strong incl) (hcard : D.lam0 ≤ Model.card M)
    (xs : List M.carrier) (x : M.carrier) (hI : FiniteIndependent D M incl xs)
    (hx : InPointSet D M incl x) :
    ¬ Forces D M incl {y | y ∈ xs} x ↔
      IndependentlyExtends (pointIndep D M incl) x {y | y ∈ xs} := by
  sorry

/-- **Theorem 10.5** (The geometry of the minimal type). On `P(M)`, for every `M₀ ≤_K M` of size
at least `λ₀`, finite independence is the independence relation of a finitary pregeometry whose
closure `cl_M` satisfies: (1) for finite `F ⊆ P(M)`, `cl_M(F)` is the set of points forced by `F`;
(2) `P(A)` is relatively closed in `P(M)` for `M₀ ≤ A ≤ M`; (3) `|cl_M(F)| ≤ λ₀` for finite `F`
and `|cl_M(F)| ≤ |F| + λ₀` for infinite `F`.

**Statement (restated, honest form, open):** standing hypotheses and `ProductAxioms` added
(the former statement was false: `AEC.Audit.theorem_10_5_false`); the closure is taken on points
(`pointClosure`); the former finite clause ("some finite `t ∋ x` has `#t ≤ λ₀`") was vacuous and
is replaced by `#cl_M(F) ≤ λ₀`; the pregeometry axioms (monotone, idempotent, exchange) and
clauses (1), (2) are now stated. Clause (2)'s preservation under strong maps is omitted. -/
theorem theorem_10_5 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms)
    (M : Model K.τ) (incl : Language.Embedding K.τ D.M0.carrier M.carrier)
    (hM : K.Mem M) (hstrong : K.Strong incl) (hcard : D.lam0 ≤ Model.card M) :
    let P := {x | InPointSet D M incl x}
    let cl := pointClosure D M incl
    -- pregeometry on `P(M)`
    (∀ F : Set M.carrier, F ⊆ P → F ⊆ cl F) ∧
    (∀ F G : Set M.carrier, F ⊆ G → cl F ⊆ cl G) ∧
    (∀ F : Set M.carrier, F ⊆ P → cl (cl F) ⊆ cl F) ∧
    (∀ (F : Set M.carrier) (x y : M.carrier), F ⊆ P →
      x ∈ cl (insert y F) → x ∉ cl F → y ∈ cl (insert x F)) ∧
    -- (1) finite closure is forcing
    (∀ F : Set M.carrier, F.Finite → F ⊆ P → ∀ x, x ∈ P → (x ∈ cl F ↔ Forces D M incl F x)) ∧
    -- (2) relative closedness of `P(A)`
    (∀ (A : Model K.τ) (fA : Language.Embedding K.τ D.M0.carrier A.carrier)
        (g : Language.Embedding K.τ A.carrier M.carrier),
        K.Mem A → K.Strong fA → K.Strong g → g.comp fA = incl → D.lam0 ≤ Model.card A →
        ∀ x, x ∈ cl (g '' {a | InPointSet D A fA a}) → ∃ a, InPointSet D A fA a ∧ g a = x) ∧
    -- (3) cardinality bounds
    (∀ F : Set M.carrier, F.Finite → F ⊆ P → #(cl F) ≤ D.lam0) ∧
    (∀ F : Set M.carrier, F ⊆ P → #(cl F) ≤ #F + D.lam0) := by
  sorry

/-- **Proposition 10.6** (Pointed working levels). At all sufficiently closed levels above the
bounds for `|m̄₀| = λ₀`, models with a distinguished strong copy of `M₀` whose enumeration has
diagram `Δ` form a categorical working scheme; `p₀` has a unique nonalgebraic extension over
each pointed model at such a level.

**Statement (restated, honest form, open):** a one-vertex working package whose eligible levels
lie above `λ₀`, with objects at every eligible level (no object-free vacuity), every object a
pointed model, every pointed model at an eligible level isomorphic over the copy to an object,
categorical (any two same-level objects are structurally isomorphic), and uniqueness of the
nonalgebraic extension of `p₀` over each object (any two realizations outside it amalgamate over
it, identified). The former statement was proved degenerately with `WorkingScheme.emptied`.
The free-lift clauses for `p^B` along (mixed) pointed arrows are not yet stated. -/
theorem proposition_10_6 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms) :
    ∃ W : WorkingScheme K oneVertexShape.{u}, IsWorkingPackage W ∧
      (∀ μ ∈ W.eligible, D.lam0 < μ) ∧
      (∀ μ (hμ : μ ∈ W.eligible), Nonempty (W.Object μ hμ)) ∧
      (∀ μ (hμ : μ ∈ W.eligible) (X : W.Object μ hμ),
        ∃ P : PointedModel K D, P.M = (W.asSystem hμ X).obj PUnit.unit) ∧
      (∀ μ (hμ : μ ∈ W.eligible) (P : PointedModel K D), Model.card P.M = μ →
        ∃ (X : W.Object μ hμ) (Q : PointedModel K D)
          (hQ : Q.M = (W.asSystem hμ X).obj PUnit.unit) (e : P.M.carrier ≃[K.τ] Q.M.carrier),
          ∀ a, e (P.copy a) = Q.copy a) ∧
      (∀ μ (hμ : μ ∈ W.eligible) (X Y : W.Object μ hμ),
        ∃ f : SystemArrow K oneVertexShape (W.asSystem hμ X) (W.asSystem hμ Y),
          W.IsStructIso (X := X) (Y := Y) f) ∧
      (∀ (B : PointedModel K D), (∃ μ, μ ∈ W.eligible ∧ Model.card B.M = μ) →
        ∀ (N1 N2 : Model K.τ) (g1 : Language.Embedding K.τ B.M.carrier N1.carrier)
          (g2 : Language.Embedding K.τ B.M.carrier N2.carrier) (a1 : N1.carrier)
          (a2 : N2.carrier),
          K.Mem N1 → K.Mem N2 → K.Strong g1 → K.Strong g2 →
          D.realizes N1 (g1.comp B.copy) a1 → D.realizes N2 (g2.comp B.copy) a2 →
          (∀ b, g1 b ≠ a1) → (∀ b, g2 b ≠ a2) →
          ∃ (N : Model K.τ) (h1 : Language.Embedding K.τ N1.carrier N.carrier)
            (h2 : Language.Embedding K.τ N2.carrier N.carrier),
            K.Mem N ∧ K.Strong h1 ∧ K.Strong h2 ∧ h1 a1 = h2 a2 ∧ ∀ x, h1 (g1 x) = h2 (g2 x)) := by
  sorry

/-- The type of the list `xs` over the pointed model `B` (embedded by `g`) is the product of
copies of `p^B`: each entry realizes `p₀` and, in some strong extension, lies outside a strong
submodel containing `B` and the earlier entries (successive free nonalgebraic realizations). -/
def IsProductOverBase {K : AbstractElementaryClass.{u}} (D : MinimalData K)
    (B : PointedModel K D) (N : Model K.τ) (g : Language.Embedding K.τ B.M.carrier N.carrier)
    (xs : List N.carrier) : Prop :=
  (∀ x ∈ xs, D.realizes N (g.comp B.copy) x) ∧
  ∀ i : Fin xs.length,
    ∃ (N' : Model K.τ) (h : Language.Embedding K.τ N.carrier N'.carrier) (M' : Model K.τ)
      (k : Language.Embedding K.τ M'.carrier N'.carrier)
      (b : Language.Embedding K.τ B.M.carrier M'.carrier),
      K.Mem N' ∧ K.Mem M' ∧ K.Strong h ∧ K.Strong k ∧ K.Strong b ∧
      (∀ x, k (b x) = h (g x)) ∧
      (∀ j : Fin xs.length, j < i → ∃ y, k y = h (xs.get j)) ∧
      ∀ y, k y ≠ h (xs.get i)

/-- **Proposition 10.7** (Change of base for the geometry). Let `B` be a pointed model at a
sufficiently closed level much larger than `λ₀`. A finite list of points in an extension of `B`
is independent over the closed set `P(B)` iff its type over `B` is the product of the
corresponding copies of `p^B`.

**Statement (restated, honest form, open):** standing hypotheses and `ProductAxioms` added (the
former abstract form was false: `AEC.Audit.proposition_10_7_false`, `[a, a]`); the former Lean
compared independence over `M₀` inside `B` with `productCopies` over `M₀` (not the English
claim). Now: `xs` lives in a strong extension `g : B → N`; "independent over `P(B)`" means
`F.map g ++ xs` is independent for every finite independent `F ⊆ P(B)`; the product over `B` is
`IsProductOverBase`. -/
theorem proposition_10_7 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms) :
    ∃ lam : Cardinal.{u}, D.lam0 < lam ∧
      ∀ (B : PointedModel K D) (N : Model K.τ)
        (g : Language.Embedding K.τ B.M.carrier N.carrier),
        K.Mem B.M → K.Mem N → K.Strong g → lam ≤ Model.card B.M →
        ∀ xs : List N.carrier, (∀ x ∈ xs, InPointSet D N (g.comp B.copy) x) →
          ((∀ F : List B.M.carrier, FiniteIndependent D B.M B.copy F →
              FiniteIndependent D N (g.comp B.copy) (F.map g ++ xs)) ↔
            IsProductOverBase D B N g xs) := by
  sorry

/-- **Lemma 10.8** (Anchoring a singleton type). There is a fixed cardinal `β` such that for a
sufficiently closed pointed model `A` and a nonalgebraic singleton type `r` over `A`, a list
`c ⊆ A` of length at most `β` can be named so that (1) the stabilized diagram of `c, m̄₀`
together with a prescription defines a unique nonalgebraic singleton type `r^B` over every
sufficiently closed pointed `B` with that named diagram; (2) the prescription at `A` is `r`, and
the family is compatible along name-preserving arrows.

**Statement (restated, honest form, open):** `r` is given by a realization `a` outside `A` in a
strong extension; the prescription `R` is a predicate on realizations over named pointed models;
the named diagram is equality in a stable diagram `SD` (Proposition 4.2) of `c ⊕ m̄₀`; (1)
existence and uniqueness (amalgamation identifying any two `R`-realizations) over every such `B`;
(2) `R` holds of `a` at `A`, and restriction along a strong name-preserving arrow `B → B'` takes
`R`-realizations over `B'` to `R`-realizations over `B` (free lifts restrict to the original).
The former conclusion ignored `c` and `β` (`AEC.Audit.lemma_10_8_statement_defect`). Clause 3
(the prescription recurs at arbitrarily large single-model levels) is not stated. -/
theorem lemma_10_8 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms) (SD : StableDiagram K) :
    ∃ β : Cardinal.{u}, aleph0 ≤ β ∧ D.lam0 ≤ β ∧ ∃ lam : Cardinal.{u}, ∃ hlam : SD.t β ≤ lam,
      ∀ (A : PointedModel K D) (A' : Model K.τ)
        (gA : Language.Embedding K.τ A.M.carrier A'.carrier) (a : A'.carrier)
        (hA : K.Mem A.M) (hAcard : lam ≤ Model.card A.M),
        K.Mem A' → K.Strong gA → (∀ x, gA x ≠ a) →
        ∃ (ι : Type u) (c : ι → A.M.carrier) (hι : #(ι ⊕ D.M0.carrier) ≤ β)
          (R : (B : PointedModel K D) → (N : Model K.τ) →
            Language.Embedding K.τ B.M.carrier N.carrier → N.carrier → Prop),
          R A A' gA a ∧
          (∀ (B : PointedModel K D) (cB : ι → B.M.carrier) (hB : K.Mem B.M)
              (hBcard : lam ≤ Model.card B.M),
              SD.same hι hA hB (hlam.trans hAcard) (hlam.trans hBcard)
                (Sum.elim c A.copy) (Sum.elim cB B.copy) →
              (∃ (N : Model K.τ) (g : Language.Embedding K.τ B.M.carrier N.carrier) (b : N.carrier),
                K.Mem N ∧ K.Strong g ∧ (∀ x, g x ≠ b) ∧ R B N g b) ∧
              ∀ (N1 N2 : Model K.τ) (g1 : Language.Embedding K.τ B.M.carrier N1.carrier)
                (g2 : Language.Embedding K.τ B.M.carrier N2.carrier) (b1 : N1.carrier)
                (b2 : N2.carrier),
                K.Mem N1 → K.Mem N2 → K.Strong g1 → K.Strong g2 →
                (∀ x, g1 x ≠ b1) → (∀ x, g2 x ≠ b2) → R B N1 g1 b1 → R B N2 g2 b2 →
                ∃ (N : Model K.τ) (h1 : Language.Embedding K.τ N1.carrier N.carrier)
                  (h2 : Language.Embedding K.τ N2.carrier N.carrier),
                  K.Mem N ∧ h1 b1 = h2 b2 ∧ ∀ x, h1 (g1 x) = h2 (g2 x)) ∧
          ∀ (B B' : PointedModel K D) (cB : ι → B.M.carrier) (cB' : ι → B'.M.carrier)
            (h : Language.Embedding K.τ B.M.carrier B'.M.carrier),
            K.Strong h → h.comp B.copy = B'.copy → (∀ i, h (cB i) = cB' i) →
            ∀ (N : Model K.τ) (g : Language.Embedding K.τ B'.M.carrier N.carrier) (b : N.carrier),
              R B' N g b → R B N (g.comp h) b := by
  sorry

/-- **Theorem 10.9** (No proper pair with unchanged points at one level). There is a cardinal
`λ > λ₀` at which no proper strong inclusion of pointed models of size `λ` preserves the
point set.

**Statement change:** the point-set hypothesis is now `P(B) = f[P(A)]`
(`∀ y, y ∈ P(B) ↔ ∃ x ∈ P(A), f x = y`). The original `∀ x, x ∈ P(A) ↔ f x ∈ P(B)` does not
say that the points are unchanged and is refuted in the AEC of all sets
(`AEC.Audit.theorem_10_9_original_false`, `AEC.Audit.corollary_10_10_original_false`).
**Standing hypotheses (grokbot_01):** `[CategoricalUnbounded K]` and the product clauses
`D.ProductAxioms` of Definition 10.3 are now explicit, as in the paper's Section 10 setting. -/
theorem theorem_10_9 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms) :
    ∃ lam : Cardinal.{u}, D.lam0 < lam ∧
      ∀ (A B : PointedModel K D) (f : Language.Embedding K.τ A.M.carrier B.M.carrier),
        K.Strong f → f.comp A.copy = B.copy →
        Model.card A.M = lam → Model.card B.M = lam →
        (∀ y, InPointSet D B.M B.copy y ↔ ∃ x, InPointSet D A.M A.copy x ∧ f x = y) →
        Function.Surjective f := by
  sorry

/-- **Corollary 10.10** (No-growth and rank on the entire tail). Above a threshold, a strong
inclusion of pointed models with the same point set is an isomorphism, and a pointed model
larger than the threshold has point-set cardinality equal to its own cardinality.

**Statement change:** the point-set hypothesis is now `P(B) = f[P(A)]`
(`∀ y, y ∈ P(B) ↔ ∃ x ∈ P(A), f x = y`). The original `∀ x, x ∈ P(A) ↔ f x ∈ P(B)` does not
say that the points are unchanged and is refuted in the AEC of all sets
(`AEC.Audit.theorem_10_9_original_false`, `AEC.Audit.corollary_10_10_original_false`).
**Standing hypotheses (grokbot_01):** `[CategoricalUnbounded K]` and the product clauses
`D.ProductAxioms` of Definition 10.3 are now explicit, as in the paper's Section 10 setting. -/
theorem corollary_10_10 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (D : MinimalData K) (hD : D.ProductAxioms) :
    ∃ lam : Cardinal.{u}, D.lam0 < lam ∧
      (∀ (A B : PointedModel K D) (f : Language.Embedding K.τ A.M.carrier B.M.carrier),
        K.Strong f → f.comp A.copy = B.copy → lam ≤ Model.card A.M →
        (∀ y, InPointSet D B.M B.copy y ↔ ∃ x, InPointSet D A.M A.copy x ∧ f x = y) →
        Function.Bijective f) ∧
      ∀ M : PointedModel K D, lam < Model.card M.M →
        #{x | InPointSet D M.M M.copy x} = Model.card M.M := by
  sorry

end
end AEC
