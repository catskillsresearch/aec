module

public import AEC.Section5.PackageClauses
public import AEC.Section5.PaddedOrder
public import AEC.Section5.RichPaddedOrder
public import AEC.Section5.EligibleSubclass
public import AEC.Section5.TermTemplate
public import AEC.Section4.CountableClosure
public import AEC.Section4.StableDiagram
public import Mathlib.Order.WellFoundedSet

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

/-- An empty-index chain union yields an object at every eligible level. -/
noncomputable def objectOfEmptyChain {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (hpack : HasChainUnions W)
    {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) : W.Object μ hμ := by
  classical
  have h :=
    hpack.union (hμ := hμ) (index := PEmpty.{u + 1})
      (obj := fun i => i.elim)
      (le := fun i => i.elim)
      (fun i => i.elim)
      (fun i => i.elim)
      (by simp [Cardinal.mk_eq_zero])
  exact h.choose

/-- Inclusion of a set as an order embedding of subtypes. -/
def setInclusionOrderEmbed {α : Type u} [Preorder α] {s t : Set α} (h : s ⊆ t) : s ↪o t where
  toFun := Set.inclusion h
  inj' := Set.inclusion_injective h
  map_rel_iff' := Iff.rfl

/-- An order embedding restricts to an order embedding onto the image of a subset. -/
def orderEmbedImage {α β : Type u} [LinearOrder α] [LinearOrder β] (f : α ↪o β) (s : Set α) :
    s ↪o (f '' s : Set β) where
  toFun x := ⟨f x.1, ⟨x.1, x.2, rfl⟩⟩
  inj' := by
    intro a b h
    exact Subtype.ext (f.injective (Subtype.ext_iff.mp h))
  map_rel_iff' := by
    intro a b
    exact f.map_rel_iff

/-- Convert subtype well-foundedness to `Set.IsWF`. -/
theorem isWF_of_subtype_wf {α : Type u} [LT α] {s : Set α}
    (hs : WellFounded ((· < ·) : s → s → Prop)) : s.IsWF := hs

/-- Convert `Set.IsWF` to subtype well-foundedness. -/
theorem subtype_wf_of_isWF {α : Type u} [LT α] {s : Set α}
    (hs : s.IsWF) : WellFounded ((· < ·) : s → s → Prop) := hs

/-- Order isomorphism between a set and its image under an order embedding. -/
noncomputable def orderIsoImage {α β : Type u} [LinearOrder α] [LinearOrder β]
    (f : α ↪o β) (s : Set α) : s ≃o (f '' s : Set β) where
  toEquiv := Equiv.ofBijective (orderEmbedImage f s) ⟨(orderEmbedImage f s).injective, by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
    exact hxy⟩
  map_rel_iff' := by
    intro a b
    exact (orderEmbedImage f s).map_rel_iff

/-- The image of a well-founded subset under an order embedding remains well-founded. -/
theorem wellFounded_image_orderEmbed {α β : Type u} [LinearOrder α] [LinearOrder β]
    (f : α ↪o β) {s : Set α} (hs : WellFounded ((· < ·) : s → s → Prop)) :
    WellFounded ((· < ·) : (f '' s : Set β) → (f '' s : Set β) → Prop) := by
  let _ : WellFoundedLT s := hs
  exact ((orderIsoImage f s).symm.toOrderEmbedding).strictMono.wellFoundedLT

/-- Union of two well-founded subsets of a linear order is well-founded on the subtype. -/
theorem wellFounded_union_subtype {α : Type u} [LinearOrder α] {s t : Set α}
    (hs : WellFounded ((· < ·) : s → s → Prop))
    (ht : WellFounded ((· < ·) : t → t → Prop)) :
    WellFounded ((· < ·) : (s ∪ t : Set α) → (s ∪ t : Set α) → Prop) :=
  subtype_wf_of_isWF (Set.IsWF.union (isWF_of_subtype_wf hs) (isWF_of_subtype_wf ht))

/-- **Lemma 5.4** (Directed unions and padded presentations). Where chain unions are
available, the presentation of a padded order of eligible cardinality `μ` is an object at
`μ`, and an order embedding of padded orders induces a permitted arrow. -/
theorem lemma_5_4 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (F : TermTemplate K S) (hpack : HasChainUnions W)
    [hpres : HasPresentations W F]
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
  classical
  let X : W.Object μ hμ := objectOfEmptyChain W hpack hμ
  refine ⟨X, ?_, ?_⟩
  · exact hpres.present_equiv hμ X I hI
  · intro ν hν J _ _ _ f hJ
    let Y : W.Object ν hν := objectOfEmptyChain W hpack hν
    obtain ⟨s, hsCard, hsWF⟩ := IsPadded.padded (I := I)
    obtain ⟨t, htCard, htWF⟩ := IsPadded.padded (I := J)
    have hsI : #s = μ := hsCard.trans hI
    have htJ : #t = ν := htCard.trans hJ
    have hsNe : Nonempty s := by
      rw [← Cardinal.mk_ne_zero_iff, hsI, ← hI]
      exact Cardinal.mk_ne_zero_iff.mpr inferInstance
    have htNe : Nonempty t := by
      rw [← Cardinal.mk_ne_zero_iff, htJ, ← hJ]
      exact Cardinal.mk_ne_zero_iff.mpr inferInstance
    let im : Set J := (↑f : I → J) '' s
    have himCard : #im = μ := by
      rw [Cardinal.mk_image_eq f.injective, hsI]
    have himWF : WellFounded ((· < ·) : im → im → Prop) :=
      wellFounded_image_orderEmbed f hsWF
    let u : Set J := im ∪ t
    have huWF : WellFounded ((· < ·) : u → u → Prop) :=
      wellFounded_union_subtype himWF htWF
    have huCard : #u = ν := by
      apply le_antisymm
      · calc
          #u ≤ #J := Cardinal.mk_subtype_le _
          _ = ν := hJ
      · calc
          ν = #t := htJ.symm
          _ ≤ #u := Cardinal.mk_le_mk_of_subset Set.subset_union_right
    let _ : WellFoundedLT s := hsWF
    let _ : WellFoundedLT u := huWF
    let _ : Nonempty s := hsNe
    let _ : Nonempty u :=
      let ⟨x⟩ := htNe
      ⟨⟨x.1, Or.inr x.2⟩⟩
    let emb : s ↪o u :=
      (orderEmbedImage f s).trans (setInclusionOrderEmbed (Set.subset_union_left (s := im) (t := t)))
    obtain ⟨arr, harr⟩ := hpres.wellOrder_arrow hμ hν s u X Y emb hsI huCard
    exact ⟨Y, arr, harr⟩

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
          ∃ x : I, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b) :=
  lemma_5_5_proof η hη

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
