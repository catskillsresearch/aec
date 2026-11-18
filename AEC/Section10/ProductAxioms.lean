module

public import AEC.Section10.PointSet
public import AEC.Section10.Forces
public import AEC.Section10.GeomClosure

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- **Definition 10.3, product clauses.** The paper defines `productCopies` semantically: a list
has, over `M₀`, the product type of the corresponding copies of `p₀`, i.e. each entry realizes
the unique nonalgebraic extension of `p₀` over a model containing `M₀` and the earlier entries.
`MinimalData.productCopies` is abstract, so these are the facts of that definition used in the
paper (Definition 10.3 and the remarks after it):

* `nodup`: a product of copies of a nonalgebraic type has distinct entries;
* `perm`: products are permutation invariant;
* `sublist`: a sublist of a product is a product (restriction of parameters);
* `map_strong`: strong embeddings over `M₀` preserve and reflect products (types over `M₀`);
* `step`: (singleton-to-pair extension, definition of the product) if `xs` is a product in a
  section `N` of size `λ₀` and, in a strong extension `N'` of `N`, the point `x` realizes `p₀`
  and lies outside `N`, then `xs ++ [x]` is a product in `N'` (its type over `N` is the unique
  nonalgebraic extension of `p₀`, Proposition 10.2).

They exclude the abstract counterexamples `AEC.Audit.lemma_10_4_false` / `theorem_10_5_false`
(`noPairs`, violates `step`) and `AEC.Audit.proposition_10_7_false` (violates `nodup`). -/
structure MinimalData.ProductAxioms {K : AbstractElementaryClass.{u}} (D : MinimalData K) :
    Prop where
  nodup : ∀ (M : Model K.τ) (f : Language.Embedding K.τ D.M0.carrier M.carrier)
    (xs : List M.carrier), D.productCopies M f xs → xs.Nodup
  perm : ∀ (M : Model K.τ) (f : Language.Embedding K.τ D.M0.carrier M.carrier)
    (xs ys : List M.carrier), xs.Perm ys → D.productCopies M f xs → D.productCopies M f ys
  sublist : ∀ (M : Model K.τ) (f : Language.Embedding K.τ D.M0.carrier M.carrier)
    (xs ys : List M.carrier), xs.Sublist ys → D.productCopies M f ys → D.productCopies M f xs
  map_strong : ∀ (M N : Model K.τ) (f : Language.Embedding K.τ D.M0.carrier M.carrier)
    (g : Language.Embedding K.τ M.carrier N.carrier) (xs : List M.carrier),
    K.Mem M → K.Mem N → K.Strong f → K.Strong g →
    (D.productCopies M f xs ↔ D.productCopies N (g.comp f) (xs.map g))
  step : ∀ (N N' : Model K.τ) (f : Language.Embedding K.τ D.M0.carrier N.carrier)
    (g : Language.Embedding K.τ N.carrier N'.carrier) (xs : List N.carrier) (x : N'.carrier),
    K.Mem N → K.Mem N' → K.Strong f → K.Strong g → Model.card N = D.lam0 →
    D.productCopies N f xs → D.realizes N' (g.comp f) x → (∀ y, g y ≠ x) →
    D.productCopies N' (g.comp f) (xs.map g ++ [x])

/-- Finite independence on `P(M)` read as a predicate on sets (Definition 10.3). -/
def pointIndep {K : AbstractElementaryClass.{u}} (D : MinimalData K) (M : Model K.τ)
    (incl : Language.Embedding K.τ D.M0.carrier M.carrier) : Set M.carrier → Prop :=
  fun s => ∃ ys : List M.carrier, FiniteIndependent D M incl ys ∧ ∀ z, z ∈ s ↔ z ∈ ys

/-- The pregeometry closure on points: `x ∈ cl_M(F)` for a point `x ∈ P(M)`. Non-points are
excluded (the bare `InClosure` contains every non-point, which cannot independently extend). -/
def pointClosure {K : AbstractElementaryClass.{u}} (D : MinimalData K) (M : Model K.τ)
    (incl : Language.Embedding K.τ D.M0.carrier M.carrier) (F : Set M.carrier) : Set M.carrier :=
  {x | InPointSet D M incl x ∧ InClosure (pointIndep D M incl) F x}

end
end AEC
