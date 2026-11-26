module

public import AEC.Section5.WorkingScheme
public import AEC.Section2.SupportTerm

@[expose] public section

/-!
# Definition 5.2(2): the presentation clause

Paper (Definition 5.2(2)): "For every well-order `I` of eligible cardinality `µ`, `F(I)` is an
object of `C_µ`. Its elements are represented by labels applied to finite increasing lists from
`I`; equality, the symbols of the system structure, and the specified maps are evaluated from the
labels and the finite order and equality patterns. Substitution of positions along an order
embedding induces an arrow, including when the source and target levels differ. Every object at
a level is isomorphic to a well-ordered presentation." (The mixed downward clause of 5.2(2) is
`HasMixedDownward`.)

* `TermTemplate.FiniteSupport`: the finite-support term data of a template ("labels applied to
  finite increasing lists", evaluation from labels and patterns, substitution).
* `HasTermPresentations`: the clause for a working scheme and its template `W.template`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- **Finite-support term data of a template** (Definition 5.2(2)). At each vertex `v`, the
elements of `F(I)` are realizations of labels `Lab v` applied to finite increasing lists from
`I` (surjectively); substitution along an order embedding is `F(f)`; equality, the function and
relation symbols, and the specified maps are evaluated from the labels and the order and
equality pattern of the positions used. -/
structure TermTemplate.FiniteSupport {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (F : TermTemplate K S) where
  Lab : S.Vertex → Type u
  arity : ∀ v, Lab v → ℕ
  realize : ∀ {I : Type u} [LinearOrder I] [Nonempty I] (v : S.Vertex),
    SupportTerm (Lab v) (arity v) I → ((F.present I).obj v).carrier
  realize_surjective : ∀ {I : Type u} [LinearOrder I] [Nonempty I] (v : S.Vertex),
    Function.Surjective (realize (I := I) v)
  /-- Substitution of positions along an order embedding is `F(f)`. -/
  realize_map : ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (v : S.Vertex) (t : SupportTerm (Lab v) (arity v) I),
    (F.onOrder f).onVertex v (realize v t) =
      realize v ⟨t.label, f ∘ t.pos, f.strictMono.comp t.increasing⟩
  /-- Equality and the symbols of the vertex structures are evaluated from the labels and the
  order and equality pattern. -/
  pattern_vertex : ∀ {I : Type u} [LinearOrder I] [Nonempty I] (v : S.Vertex) {n : ℕ}
    (t s : Fin n → SupportTerm (Lab v) (arity v) I)
    (hlabel : ∀ i, (t i).label = (s i).label),
    (∀ i j (a : Fin (arity v (t i).label)) (b : Fin (arity v (t j).label)),
      (t i).pos a = (t j).pos b ↔
        (s i).pos (Fin.cast (congrArg (arity v) (hlabel i)) a) =
          (s j).pos (Fin.cast (congrArg (arity v) (hlabel j)) b)) →
    (∀ i j (a : Fin (arity v (t i).label)) (b : Fin (arity v (t j).label)),
      (t i).pos a < (t j).pos b ↔
        (s i).pos (Fin.cast (congrArg (arity v) (hlabel i)) a) <
          (s j).pos (Fin.cast (congrArg (arity v) (hlabel j)) b)) →
    (∀ i j, realize v (t i) = realize v (t j) ↔ realize v (s i) = realize v (s j)) ∧
    (∀ {k} (f : K.τ.Functions k) (idx : Fin k → Fin n) (j : Fin n),
      Language.Structure.funMap f (fun a => realize v (t (idx a))) = realize v (t j) ↔
        Language.Structure.funMap f (fun a => realize v (s (idx a))) = realize v (s j)) ∧
    (∀ {k₁ k₂ : ℕ} (f₁ : K.τ.Functions k₁) (f₂ : K.τ.Functions k₂)
      (idx₁ : Fin k₁ → Fin n) (idx₂ : Fin k₂ → Fin n),
      Language.Structure.funMap f₁ (fun a => realize v (t (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => realize v (t (idx₂ a))) ↔
        Language.Structure.funMap f₁ (fun a => realize v (s (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => realize v (s (idx₂ a)))) ∧
    (∀ {k} (r : K.τ.Relations k) (idx : Fin k → Fin n),
      Language.Structure.RelMap r (fun a => realize v (t (idx a))) ↔
        Language.Structure.RelMap r (fun a => realize v (s (idx a))))
  /-- The specified maps are evaluated from the labels and the joint order and equality
  pattern of the two position lists. -/
  pattern_edge : ∀ {I : Type u} [LinearOrder I] [Nonempty I] {i j : S.Vertex}
    (h : S.specified i j) (a : Lab i) (b : Lab j)
    (p p' : Fin (arity i a) → I) (q q' : Fin (arity j b) → I)
    (hp : StrictMono p) (hp' : StrictMono p') (hq : StrictMono q) (hq' : StrictMono q'),
    (∀ x y, (p x = q y ↔ p' x = q' y) ∧ (p x < q y ↔ p' x < q' y) ∧
      (q y < p x ↔ q' y < p' x)) →
    ((F.present I).edge h (realize i ⟨a, p, hp⟩) = realize j ⟨b, q, hq⟩ ↔
      (F.present I).edge h (realize i ⟨a, p', hp'⟩) = realize j ⟨b, q', hq'⟩)

/-- **Definition 5.2(2), the presentation clause** for a working scheme `W` and its template
`F = W.template`: `F` is a finite-support term template; for every well-order `I` of eligible
cardinality `µ`, `F(I)` is an object of `C_µ` (an object `pres I` with vertexwise identifications
commuting with the specified maps); substitution along an order embedding of such well-orders
induces an arrow, also between different eligible levels; and every object at a level is
isomorphic (by a structural isomorphism) to a well-ordered presentation. -/
class HasTermPresentations {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) : Prop where
  finiteSupport : Nonempty W.template.FiniteSupport
  present : ∃ (pres : ∀ {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (I : Type u) [LinearOrder I]
        [WellFoundedLT I] [Nonempty I], #I = μ → W.Object μ hμ)
      (e : ∀ {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (I : Type u) [LinearOrder I]
        [WellFoundedLT I] [Nonempty I] (hI : #I = μ) (v : S.Vertex),
        ((W.template.present I).obj v).carrier ≃[K.τ]
          ((W.asSystem hμ (pres hμ I hI)).obj v).carrier),
      (∀ {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (I : Type u) [LinearOrder I]
          [WellFoundedLT I] [Nonempty I] (hI : #I = μ) {i j : S.Vertex}
          (h : S.specified i j) (x : ((W.template.present I).obj i).carrier),
          (W.asSystem hμ (pres hμ I hI)).edge h (e hμ I hI i x) =
            e hμ I hI j ((W.template.present I).edge h x)) ∧
      (∀ {μ ν : Cardinal.{u}} (hμ : μ ∈ W.eligible) (hν : ν ∈ W.eligible)
          (I J : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
          [LinearOrder J] [WellFoundedLT J] [Nonempty J] (hI : #I = μ) (hJ : #J = ν)
          (f : I ↪o J),
          ∃ arr : SystemArrow K S (W.asSystem hμ (pres hμ I hI)) (W.asSystem hν (pres hν J hJ)),
            W.permitted (X := pres hμ I hI) (Y := pres hν J hJ) arr ∧
            ∀ v x, arr.onVertex v (e hμ I hI v x) =
              e hν J hJ v ((W.template.onOrder f).onVertex v x)) ∧
      (∀ {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (X : W.Object μ hμ),
          ∃ (I : Type u) (_ : LinearOrder I) (_ : WellFoundedLT I) (_ : Nonempty I)
            (hI : #I = μ)
            (φ : SystemArrow K S (W.asSystem hμ (pres hμ I hI)) (W.asSystem hμ X)),
            W.IsStructIso (X := pres hμ I hI) (Y := X) φ)

end
end AEC
