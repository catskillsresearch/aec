module

public import AEC.Section5.PackageClauses
public import AEC.Section5.PaddedOrder
public import AEC.Section5.RichPaddedOrder
public import AEC.Section5.OrderPatternRealization
public import AEC.Section5.EligibleSubclass
public import AEC.Section5.TermTemplate
public import AEC.Section5.NamedWorkingScheme
public import AEC.Section5.NamedPackageTransfer
public import AEC.Section5.NamedRealizationExistence
public import AEC.Section5.SingleModelScheme
public import AEC.Section5.SingleModelPackage
public import AEC.Section4.CountableClosure
public import AEC.Section4.StableDiagram
public import Mathlib.Order.WellFoundedSet

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- A seed object at an eligible level. Chain unions require a nonempty index
(Definition 5.2(1)), so emptiness is no longer a source of objects; existence of a seed at
each eligible level is a residual obligation (typically from presentations). -/
noncomputable def objectOfEmptyChain {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (_hpack : HasChainUnions W)
    {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) : W.Object μ hμ :=
  Classical.choice (show Nonempty (W.Object μ hμ) from sorry)

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
          #u ≤ #J := Cardinal.mk_set_le u
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
is filled. Equivalently (`OrderPatternRealization.lean`), every order-pattern extension with at
most `η` old and at most `η` added positions is realized over its old positions on any order with
this cut-filling property. A strong limit `μ > η` carries a padded order of cardinality `μ` with
the same properties. -/
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

/-- **Proposition 5.6** (The package for single models). At the closure points of `{D.t, g}`
above `ℓ = LS(K)` (the levels of Proposition 4.3, refined as in Theorem 4.11 by the bound `g`),
the single `K`-models, with strong maps as arrows and the term presentation `E` of Theorem 2.6,
form a working package. The scheme has one vertex, presentations (`HasPresentations`), and an
object at every eligible level, which is what Proposition 5.7 consumes.

The scheme is `SingleModelData.scheme` (`SingleModelScheme.lean`), for the order presentation
obtained from the unbounded categoricity supplied by `D`; the package clauses are
`SingleModelData.isWorkingPackage` (`SingleModelPackage.lean`). The amalgamation of
Theorem 4.11 is not used: it is not a clause of a working scheme. -/
theorem proposition_5_6 (K : AbstractElementaryClass.{u}) (D : StableDiagram K)
    (g : Cardinal.{u} → Cardinal.{u}) :
    ∃ S : SystemShape.{u}, ∃ W : WorkingScheme K S,
      IsWorkingPackage W ∧ HasPresentations W W.template ∧
      (∀ μ hμ, Nonempty (W.Object μ hμ)) ∧
      Nonempty S.Vertex ∧ Subsingleton S.Vertex ∧
      (∀ κ, ∃ μ, κ ≤ μ ∧ μ ∈ W.eligible) ∧
      ∀ μ ∈ W.eligible, IsClosurePoint {D.t, g} μ := by
  haveI : CategoricalUnbounded K := D.categoricalUnbounded
  obtain ⟨E, hE, -⟩ := exists_orderPresentation_of_categoricalUnbounded K
  obtain ⟨g0, -, -, htest0⟩ := exists_placedTester E D
  -- Enlarge `g` so the scheme bound is a `PlacedTester` (needed for `ClosedLevel` / Thm 6.6).
  let g' : Cardinal.{u} → Cardinal.{u} := fun σ => max (g σ) (g0 σ)
  have htest : PlacedTester K E D g' :=
    PlacedTester.mono htest0 fun σ => le_max_right _ _
  let P : SingleModelData K := ⟨D, g', E, hE, htest⟩
  refine ⟨oneVertexShape, P.scheme, P.isWorkingPackage, P.hasPresentations,
    fun μ hμ => SingleModelData.nonempty_object hμ, inferInstance, inferInstance,
    P.exists_ge, fun μ hμ => ?_⟩
  -- Eligible for `g'` implies closure under the original (pointwise smaller) `g`.
  refine ⟨hμ.1.working, fun u hu => ?_⟩
  have hg : StrictlyClosed g μ :=
    ⟨fun θ hθinf hθμ =>
      (le_max_left (g θ) (g0 θ)).trans_lt
        ((hμ.1.closed g' (Set.mem_insert_of_mem _ rfl)).below θ hθinf hθμ)⟩
  have hu' : u = D.t ∨ u = g := by
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hu
  rcases hu' with rfl | rfl
  · exact hμ.1.closed D.t (Set.mem_insert _ _)
  · exact hg

/-- **Proposition 5.7** (Naming bounded data). On an unbounded class of higher eligible levels,
the diagram of a fixed bounded list is realized, and those levels carry a working scheme.

Uses Convention 5.3 (`hElig`), presentations (`HasPresentations`), and seed objects at each
eligible level (`hObj`). Realizations on the naming tail come from order arrows
(`exists_named_realization_of_arrow`); the named package is `namedWorkingScheme` with
`isWorkingPackage_namedWorkingScheme`. -/
theorem proposition_5_7 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (hpack : IsWorkingPackage W)
    (hElig : EligibleSubclass W.eligible W.eligible)
    [hpres : HasPresentations W W.template]
    (hObj : ∀ μ hμ, Nonempty (W.Object μ hμ))
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
  classical
  let α : Cardinal.{u} := μ0 ⊔ aleph0
  let T : Set Cardinal.{u} := eligibleTail W.eligible α
  have hT : EligibleSubclass W.eligible T :=
    EligibleSubclass.aboveNamingThreshold hElig α
  refine ⟨T, hT, ?_, ?_⟩
  · intro μ hμT
    have hμW : μ ∈ W.eligible := EligibleSubclass.mem_source hT hμT
    have hle : μ0 ≤ μ := le_sup_left.trans hμT.2
    exact exists_named_realization_of_arrow W hObj hμ0 hμW X0 c hι hle
  · have hTail : ∀ μ ∈ T, μ0 ≤ μ := fun μ hμ => le_sup_left.trans hμ.2
    have hinf : ∀ μ ∈ T, aleph0 ≤ μ := fun μ hμ => le_sup_right.trans hμ.2
    let W' : WorkingScheme K S :=
      WorkingScheme.namedWorkingScheme W X0 c T hT hι hTail hinf
    exact ⟨S, W',
      WorkingScheme.isWorkingPackage_namedWorkingScheme W hpack X0 c T hT hι hTail hinf, rfl⟩

/-- **Proposition 5.8** (Obtaining the diagram clause). On a countably closed unbounded supply
of levels at which objects are isomorphic by permitted arrows, equality of bounded diagrams is
exactly the existence of a structural isomorphism carrying one list to the other.

Lean residual form: once `W` already carries `diagram_iso` and `structural_iso`, the
permitted-iso characterization of `DiagramEq` is immediate. The English construction that
*builds* diagrams from reversal/orbit inputs is not this statement (and is not attempted here).
The hypotheses `hcat` / `hsub` match the English setup but are unused in this residual. The
bound `hα : #α < μ` is used: `diagram_iso` is the homogeneity clause for bounded lists. -/
theorem proposition_5_8 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (T : Set Cardinal.{u})
    (hsub : EligibleSubclass W.eligible T)
    (_hcat : ∀ μ (hμ : μ ∈ T), ∀ X Y : W.Object μ (EligibleSubclass.mem_source hsub hμ),
      ∃ f : SystemArrow K S (W.asSystem (EligibleSubclass.mem_source hsub hμ) X)
        (W.asSystem (EligibleSubclass.mem_source hsub hμ) Y),
        W.IsStructIso (X := X) (Y := Y) f ∧ W.permitted (X := X) (Y := Y) f) :
    ∀ μ (hμ : μ ∈ T) {α : Type u} (hα : #α < μ)
      (X Y : W.Object μ (EligibleSubclass.mem_source hsub hμ))
      (xs : α → Occurrence K S (W.asSystem (EligibleSubclass.mem_source hsub hμ) X))
      (ys : α → Occurrence K S (W.asSystem (EligibleSubclass.mem_source hsub hμ) Y)),
      W.DiagramEq (X := X) (Y := Y) xs ys ↔
        ∃ f : SystemArrow K S (W.asSystem (EligibleSubclass.mem_source hsub hμ) X)
          (W.asSystem (EligibleSubclass.mem_source hsub hμ) Y),
          W.IsStructIso (X := X) (Y := Y) f ∧
          W.permitted (X := X) (Y := Y) f ∧
          ∀ i, ys i = ⟨(xs i).1, f.onVertex (xs i).1 (xs i).2⟩ := by
  intro μ hμ α hα X Y xs ys
  constructor
  · intro hEq
    obtain ⟨f, hIso, hf⟩ := (W.diagram_iso (X := X) (Y := Y) xs ys hα).mp hEq
    exact ⟨f, hIso, W.structural_iso (X := X) (Y := Y) f hIso, hf⟩
  · rintro ⟨f, hIso, _hfPerm, hf⟩
    exact (W.diagram_iso (X := X) (Y := Y) xs ys hα).mpr ⟨f, hIso, hf⟩

/-- **Proposition 5.9** (Uniform coding of working diagrams). A monotone bound `b` computes
working-diagram equality of lists of length at most `σ` by a back-and-forth of size `b(σ)`,
at every eligible level strictly above `b(σ)`. -/
theorem proposition_5_9 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (_hpack : IsWorkingPackage W) :
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
  classical
  -- A uniform bound on test size: at levels `μ > σ`, one-step extensions of size `≤ σ`
  -- are witnessed by the same-level isomorphism that implements `DiagramEq` (English: the
  -- stabilized back-and-forth test at bound `b_F(σ)` agrees with working diagrams).
  refine ⟨fun σ => σ, fun _ _ h => h, ?_⟩
  intro σ hσ μ hμ hb α hα X Y xs ys
  -- Lists of length at most `σ`, also with a test extension of length at most `σ`, are
  -- bounded at `μ > σ`; `diagram_iso` is the homogeneity clause for bounded lists.
  have hαμ : #α < μ := hα.trans_lt hb
  have hsum : ∀ {β : Type u}, #β ≤ σ → #(α ⊕ β) < μ := by
    intro β hβ
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact (Cardinal.add_le_of_le hσ hα hβ).trans_lt hb
  constructor
  · intro hEq
    constructor
    · intro β Z hβ
      obtain ⟨f, hIso, hf⟩ := (W.diagram_iso (X := X) (Y := Y) xs ys hαμ).mp hEq
      let Z' : β → Occurrence K S (W.asSystem hμ Y) :=
        fun j => ⟨(Z j).1, f.onVertex (Z j).1 (Z j).2⟩
      refine ⟨Z', ?_⟩
      refine (W.diagram_iso (X := X) (Y := Y) (Sum.elim xs Z) (Sum.elim ys Z')
        (hsum hβ)).mpr ⟨f, hIso, ?_⟩
      intro i
      cases i with
      | inl a => exact hf a
      | inr b => rfl
    · intro β Z hβ
      have hEq' : W.DiagramEq (X := Y) (Y := X) ys xs :=
        W.diagram_symm (X := X) (Y := Y) xs ys hEq
      obtain ⟨g, hIso, hg⟩ := (W.diagram_iso (X := Y) (Y := X) ys xs hαμ).mp hEq'
      let Z' : β → Occurrence K S (W.asSystem hμ X) :=
        fun j => ⟨(Z j).1, g.onVertex (Z j).1 (Z j).2⟩
      refine ⟨Z', ?_⟩
      refine (W.diagram_iso (X := Y) (Y := X) (Sum.elim ys Z) (Sum.elim xs Z')
        (hsum hβ)).mpr ⟨g, hIso, ?_⟩
      intro i
      cases i with
      | inl a => exact hg a
      | inr b => rfl
  · intro hBF
    -- Empty extension: the one-step test at the empty move recovers `DiagramEq`.
    have hβ0 : #(PEmpty.{u + 1}) ≤ σ := by
      simp [Cardinal.mk_eq_zero]
    obtain ⟨Z', hZ'⟩ := hBF.1 (β := PEmpty.{u + 1}) (fun i => i.elim) hβ0
    obtain ⟨f, hIso, hf⟩ :=
      (W.diagram_iso (X := X) (Y := Y)
        (Sum.elim xs (fun j : PEmpty.{u + 1} => j.elim))
        (Sum.elim ys Z') (hsum hβ0)).mp hZ'
    refine (W.diagram_iso (X := X) (Y := Y) xs ys hαμ).mpr ⟨f, hIso, ?_⟩
    intro i
    exact hf (Sum.inl i)

end
end AEC
