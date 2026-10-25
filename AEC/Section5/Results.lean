module

public import AEC.Section5.PackageClauses
public import AEC.Section5.PaddedOrder
public import AEC.Section5.EligibleSubclass
public import AEC.Section5.TermTemplate
public import AEC.Section4.CountableClosure
public import AEC.Section4.StableDiagram

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- The four working-package clauses of Definition 5.2 beyond the scheme data. -/
def IsWorkingPackage {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) : Prop :=
  HasChainUnions W ∧ HasMixedDownward W ∧ IsSaturated W ∧ SatisfiesExhaustion W

theorem EligibleSubclass.mem_source {S T : Set Cardinal.{u}} (h : EligibleSubclass S T)
    {μ : Cardinal.{u}} (hμ : μ ∈ T) : μ ∈ S := by
  dsimp [EligibleSubclass] at h
  exact h.1 hμ

/-- **Lemma 5.4** (Directed unions and padded presentations). Where chain unions are
available, the presentation of a padded order of eligible cardinality `μ` is an object at
`μ`, and an order embedding of padded orders induces a permitted arrow. -/
theorem lemma_5_4 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (F : TermTemplate K S) (hpack : HasChainUnions W)
    {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (I : Type u) [LinearOrder I] [Nonempty I]
    [IsPadded I] (hI : #I = μ) :
    ∃ X : W.Object μ hμ,
      (∀ v, Nonempty (((F.present I).obj v).carrier ≃[K.τ]
        ((W.asSystem hμ X).obj v).carrier)) ∧
      ∀ {ν : Cardinal.{u}} (hν : ν ∈ W.eligible) (J : Type u) [LinearOrder J] [Nonempty J]
        [IsPadded J] (f : I ↪o J), #J = ν →
        ∃ Y : W.Object ν hν,
          ∃ arr : SystemArrow K S (W.asSystem hμ X) (W.asSystem hν Y),
            W.permitted (X := X) (Y := Y) arr := by
  sorry

/-- **Lemma 5.5** (Rich padded orders). For infinite `η` there is a dense endpoint-free linear
order of cardinality `2^η` in which every cut given by at most `η` parameters on either side
is filled. A strong limit `μ > η` carries a padded order of cardinality `μ` with the same
property. -/
theorem lemma_5_5 (η : Cardinal.{u}) (hη : aleph0 ≤ η) :
    (∃ (Q : Type u) (_ : LinearOrder Q),
      #Q = (2 : Cardinal.{u}) ^ η ∧
      (∀ a b : Q, a < b → ∃ c, a < c ∧ c < b) ∧
      (∀ a : Q, ∃ b, b < a) ∧ (∀ a : Q, ∃ c, a < c) ∧
      ∀ (L R : Set Q), #L ≤ η → #R ≤ η → (∀ a ∈ L, ∀ b ∈ R, a < b) →
        ∃ x : Q, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b)) ∧
    ∀ μ : Cardinal.{u}, μ.IsStrongLimit → η < μ →
      ∃ (I : Type u) (_ : LinearOrder I) (_ : IsPadded I),
        #I = μ ∧
        (∀ a b : I, a < b → ∃ c, a < c ∧ c < b) ∧
        ∀ (L R : Set I), #L ≤ η → #R ≤ η → (∀ a ∈ L, ∀ b ∈ R, a < b) →
          ∃ x : I, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b) := by
  sorry

/-- **Proposition 5.6** (The package for single models). There is a one-vertex working scheme
whose eligible levels are an unbounded class of closure points for `t` and `g`. -/
theorem proposition_5_6 (K : AbstractElementaryClass.{u}) (D : StableDiagram K)
    (g : Cardinal.{u} → Cardinal.{u}) :
    ∃ S : SystemShape.{u}, ∃ W : WorkingScheme K S,
      IsWorkingPackage W ∧ Nonempty S.Vertex ∧ Subsingleton S.Vertex ∧
      (∀ κ, ∃ μ, κ ≤ μ ∧ μ ∈ W.eligible) ∧
      ∀ μ, μ ∈ W.eligible → IsClosurePoint {D.t, g} μ := by
  sorry

/-- **Proposition 5.7** (Naming bounded data). On an unbounded class of higher eligible levels,
the diagram of a fixed bounded list is realized, and those levels carry a working scheme. -/
theorem proposition_5_7 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (hpack : IsWorkingPackage W)
    {μ0 : Cardinal.{u}} (hμ0 : μ0 ∈ W.eligible) (X0 : W.Object μ0 hμ0)
    {ι : Type u} (c : ι → Occurrence K S (W.asSystem hμ0 X0)) (hι : #ι < μ0) :
    ∃ T : Set Cardinal.{u}, ∃ hT : EligibleSubclass W.eligible T,
      (∀ μ (hμ : μ ∈ T),
        ∃ Y : W.Object μ (EligibleSubclass.mem_source hT hμ),
          ∃ arr : SystemArrow K S (W.asSystem hμ0 X0)
            (W.asSystem (EligibleSubclass.mem_source hT hμ) Y),
            W.permitted (X := X0) (Y := Y) arr ∧
            W.DiagramEq (X := X0) (Y := Y) c
              (fun i => ⟨(c i).1, arr.onVertex (c i).1 (c i).2⟩)) ∧
      ∃ S' : SystemShape.{u}, ∃ W' : WorkingScheme K S',
        IsWorkingPackage W' ∧ W'.eligible = T := by
  sorry

/-- **Proposition 5.8** (Obtaining the diagram clause). On a countably closed unbounded supply
of levels at which objects are isomorphic by permitted arrows, equality of bounded diagrams is
exactly the existence of a structural isomorphism carrying one list to the other. -/
theorem proposition_5_8 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (T : Set Cardinal.{u})
    (hsub : EligibleSubclass W.eligible T)
    (hcat : ∀ μ (hμ : μ ∈ T), ∀ X Y : W.Object μ (EligibleSubclass.mem_source hsub hμ),
      ∃ f : SystemArrow K S (W.asSystem (EligibleSubclass.mem_source hsub hμ) X)
        (W.asSystem (EligibleSubclass.mem_source hsub hμ) Y),
        (∀ v, Function.Bijective (f.onVertex v)) ∧ W.permitted (X := X) (Y := Y) f) :
    ∀ μ (hμ : μ ∈ T) {α : Type u} (hα : #α < μ)
      (X Y : W.Object μ (EligibleSubclass.mem_source hsub hμ))
      (xs : α → Occurrence K S (W.asSystem (EligibleSubclass.mem_source hsub hμ) X))
      (ys : α → Occurrence K S (W.asSystem (EligibleSubclass.mem_source hsub hμ) Y)),
      W.DiagramEq (X := X) (Y := Y) xs ys ↔
        ∃ f : SystemArrow K S (W.asSystem (EligibleSubclass.mem_source hsub hμ) X)
          (W.asSystem (EligibleSubclass.mem_source hsub hμ) Y),
          (∀ v, Function.Bijective (f.onVertex v)) ∧
          W.permitted (X := X) (Y := Y) f ∧
          ∀ i, ys i = ⟨(xs i).1, f.onVertex (xs i).1 (xs i).2⟩ := by
  sorry

/-- **Proposition 5.9** (Uniform coding of working diagrams). A monotone bound `b` computes
working-diagram equality of lists of length at most `σ` by a back-and-forth of size `b(σ)`,
at every eligible level strictly above `b(σ)`. -/
theorem proposition_5_9 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (hpack : IsWorkingPackage W) :
    ∃ b : Cardinal.{u} → Cardinal.{u},
      (∀ σ τ, σ ≤ τ → b σ ≤ b τ) ∧
      ∀ (σ : Cardinal.{u}), aleph0 ≤ σ → ∀ μ (hμ : μ ∈ W.eligible), b σ < μ →
        ∀ {α : Type u} (hα : #α ≤ σ)
          (X Y : W.Object μ hμ)
          (xs : α → Occurrence K S (W.asSystem hμ X))
          (ys : α → Occurrence K S (W.asSystem hμ Y)),
          W.DiagramEq (X := X) (Y := Y) xs ys ↔
            (∀ {β : Type u} (Z : β → Occurrence K S (W.asSystem hμ X)), #β ≤ b σ →
              ∃ Z' : β → Occurrence K S (W.asSystem hμ Y),
                W.DiagramEq (X := X) (Y := Y)
                  (fun i : α ⊕ β => Sum.elim xs Z i) (fun i : α ⊕ β => Sum.elim ys Z' i)) ∧
            (∀ {β : Type u} (Z : β → Occurrence K S (W.asSystem hμ Y)), #β ≤ b σ →
              ∃ Z' : β → Occurrence K S (W.asSystem hμ X),
                W.DiagramEq (X := Y) (Y := X)
                  (fun i : α ⊕ β => Sum.elim ys Z i) (fun i : α ⊕ β => Sum.elim xs Z' i)) := by
  sorry

end
end AEC
