module

public import AEC.Section8.Layout84Single
public import AEC.Section6.GaloisCrossLevel

@[expose] public section

/-!
# Lemma 8.4 for the Prop 5.6 scheme: term generation for the layout (cycle 101)

English (Lemma 8.4 proof): "Present (A, U, b) as F^b(H) on a well-order of size ν. ... The layout
has two well-ordered horizontal segments with designated term parts." In `P.scheme` every object
at level `ν` is charted onto an order presentation `P.E(J)`, `#J = ν` (categoricity), and every
element of `P.E(J)` is the value of a term with finite support in `J` (`supportTermOf`). This file
proves the term-generation step: bounded lists of a level-`ν` object are values of terms over a
bounded set of generator positions, and diagram agreement over all parameters with support in a
set of generator positions is placed agreement on that set (the transfer from generating
parameters to arbitrary parameters).
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Term generation for a level-`ν` object (P.scheme).** For an object `X` of `P.scheme` charted
onto `P.E(J)` by `e`, every list `Z` of `X` of length at most `θ` (`θ` infinite) consists of values
of terms over one nonempty set `S ⊆ J` of at most `θ` generator positions: each `Z b` is the image
under the chart of `P.E(S ↪ J)` applied to the value of a term of `P.E(S)`. -/
theorem infra_84_term_generation_single (P : SingleModelData K) {ν : Cardinal.{u}}
    {hν : ν ∈ P.eligible} (X : P.scheme.Object ν hν) (J : Type u) [LinearOrder J] [Nonempty J]
    (e : (P.E.obj J).carrier ≃[K.τ] (SMObject.model X).carrier)
    {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν X))
    {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (hβ : #β ≤ θ) :
    ∃ S : Set J, #S ≤ θ ∧ S.Nonempty ∧
      ∀ b, ∃ (_ : Nonempty S) (t : SupportTerm P.E.lab P.E.arity S),
        e (P.E.map (OrderEmbedding.subtype (· ∈ S)) (P.E.realize t)) = SMObject.val X (Z b) := by
  classical
  let R : Set (P.E.obj J).carrier := Set.range (fun b => e.symm (SMObject.val X (Z b)))
  have hR : #R ≤ θ := mk_range_le.trans hβ
  refine ⟨paramSupport P.E R, mk_paramSupport_le P.E hθ hR, paramSupport_nonempty P.E R,
    fun b => ?_⟩
  have hne : Nonempty (paramSupport P.E R) :=
    (paramSupport_nonempty P.E R).to_subtype
  have hx : e.symm (SMObject.val X (Z b)) ∈ R := ⟨b, rfl⟩
  have hsub := termSupport_subset_paramSupport P.E hx
  refine ⟨hne, (supportTermOf P.E (e.symm (SMObject.val X (Z b)))).restrict _ hsub, ?_⟩
  rw [infra_612_map_restrict P.E (paramSupport P.E R) _ hsub]
  exact e.apply_symm_apply _

/-- **Diagram transfer from generating positions to arbitrary parameters.** English (Lemma 8.4
proof): the layout has "two well-ordered horizontal segments with designated term parts", and
comparisons are placed comparisons over the layout. Over a well-ordered presentation `E(I)` at a
closed level `μ`, with placements `P₀`, `P₁` lifting the bounded diagrams of candidates `d₀ ∈ B₀`,
`d₁ ∈ B₁`: if the placed comparisons agree over a set `X ⊆ I` of generator positions, then `d₀`,
`d₁` have equal diagrams with every bounded parameter list of `E(I)` whose terms are supported in
`X`, however many parameters it has (term parameters, not only generators). -/
theorem infra_84_transfer_of_agreeOn {E : OrderPresentation K} {D : StableDiagram K}
    {g : Cardinal.{u} → Cardinal.{u}} {μ : Cardinal.{u}} {I : Type u} [LinearOrder I]
    [Nonempty I] {B₀ B₁ : Model K.τ} {hB₀ : K.Mem B₀} {hB₁ : K.Mem B₁}
    {incl₀ : Language.Embedding K.τ (E.obj I).carrier B₀.carrier}
    {incl₁ : Language.Embedding K.τ (E.obj I).carrier B₁.carrier} {α : Type u}
    (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    {d₀ : α → B₀.carrier} {d₁ : α → B₁.carrier} {P₀ P₁ : Placement E.lab E.arity I α}
    (h₀ : P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) (h₁ : P₁.LiftsBounded E D hB₁ incl₁ d₁ μ)
    (X : Set I) (hag : P₀.AgreeOn E D P₁ X) {β : Type u} (ρ : Cardinal.{u})
    (hρinf : aleph0 ≤ ρ) (hρ : ρ < μ) (p : β → (E.obj I).carrier)
    (hp : ∀ b, termSupport (supportTermOf E (p b)) ⊆ X) (hj : #(α ⊕ β) ≤ ρ)
    (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁) :
    D.same hj hB₀ hB₁ ht₀ ht₁ (Sum.elim d₀ (fun b => incl₀ (p b)))
      (Sum.elim d₁ (fun b => incl₁ (p b))) := by
  have hIc : Model.card (E.obj I) = μ :=
    orderPresentation_obj_card E hI hL.ls_lt.le hL.inf
  have hPμ : ∀ (Q : Placement E.lab E.arity I α), D.t ρ ≤ Model.card (E.obj Q.J) := fun Q =>
    ((hL.t_lt hρinf hρ).le.trans hIc.ge).trans (mk_le_of_injective (E.map Q.f).injective)
  have hJ0 := hPμ P₀
  have hJ1 := hPμ P₁
  have e0 := h₀ ρ hρinf hρ p hj ht₀ hJ0
  have e1 := h₁ ρ hρinf hρ p hj ht₁ hJ1
  have e2 := SameNaturalDiagram.same hρinf
    (hag (fun b => supportTermOf E (p b)) ρ hρinf hj hp) hJ0 hJ1
    (orderPresentation_obj_mem E P₀.J) (orderPresentation_obj_mem E P₁.J)
  exact D.trans hj hB₀ _ hB₁ ht₀ hJ0 ht₁ _ _ _ e0
    (D.trans hj _ _ hB₁ hJ0 hJ1 ht₁ _ _ _ e2 (D.symm hj hB₁ _ ht₁ hJ1 _ _ e1))

/-- **Generator tests determine the placed comparison over the generating positions.** The
converse direction of `infra_84_transfer_of_agreeOn`: if the candidates `d₀`, `d₁` have equal
diagrams with every list of at most `χ` parameters drawn from the sub-presentation
`E(X ∪ {i₀}) ⊆ E(I)` generated by the positions `X` (and `#X + 1 + LS ≤ χ`), then their lifting
placements agree over `X ∪ {i₀}` (hence over `X`). -/
theorem infra_84_agreeOn_of_generator_tests [CategoricalUnbounded K] {E : OrderPresentation K}
    {D : StableDiagram K}
    {g : Cardinal.{u} → Cardinal.{u}} {μ : Cardinal.{u}} {I : Type u} [LinearOrder I]
    [Nonempty I] {B₀ B₁ : Model K.τ} {hB₀ : K.Mem B₀} {hB₁ : K.Mem B₁}
    {incl₀ : Language.Embedding K.τ (E.obj I).carrier B₀.carrier}
    {incl₁ : Language.Embedding K.τ (E.obj I).carrier B₁.carrier} {α : Type u}
    (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    {d₀ : α → B₀.carrier} {d₁ : α → B₁.carrier} {P₀ P₁ : Placement E.lab E.arity I α}
    (h₀ : P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) (h₁ : P₁.LiftsBounded E D hB₁ incl₁ d₁ μ)
    (X : Set I) {ρ χ : Cardinal.{u}} (hρinf : aleph0 ≤ ρ) (hρ : ρ < μ)
    (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁)
    (hαχ : ∀ {β : Type u}, #β ≤ χ → #(α ⊕ β) ≤ ρ) (hX : #X + 1 + ls K ≤ χ)
    (htest : ∀ (Y : Set (E.obj I).carrier)
      (_ : Y ⊆ letI : Nonempty ↥(X ∪ {Classical.arbitrary I}) := ⟨⟨_, Or.inr rfl⟩⟩
        Set.range (E.map (OrderEmbedding.subtype (· ∈ X ∪ {Classical.arbitrary I}))))
      (hY : #Y ≤ χ), D.same (hαχ hY) hB₀ hB₁ ht₀ ht₁
        (Sum.elim d₀ (fun y : ↥Y => incl₀ y.1)) (Sum.elim d₁ (fun y : ↥Y => incl₁ y.1))) :
    P₀.AgreeOn E D P₁ (X ∪ {Classical.arbitrary I}) := by
  classical
  intro β par τ hτ hj hpar
  let X' : Set I := X ∪ {Classical.arbitrary I}
  have : Nonempty ↥X' := ⟨⟨Classical.arbitrary I, Or.inr rfl⟩⟩
  let iX : ↥X' ↪o I := OrderEmbedding.subtype (· ∈ X')
  let Y : Set (E.obj I).carrier := Set.range (fun b => E.realize (par b))
  have hYsub : Y ⊆ Set.range (E.map iX) := by
    rintro _ ⟨b, rfl⟩
    refine ⟨E.realize ((par b).restrict X' fun x hx => hpar b hx), ?_⟩
    rw [E.realize_along]
    rfl
  have hX'card : #↥X' ≤ #X + 1 := (mk_union_le _ _).trans (by simp)
  have hYcard : #Y ≤ χ :=
    calc #Y ≤ #(Set.range (E.map iX)) := mk_le_mk_of_subset hYsub
      _ ≤ Model.card (E.obj ↥X') := mk_range_le
      _ ≤ #↥X' + E.ell := E.card_upper
      _ ≤ #X + 1 + ls K := by rw [E.ell_eq]; exact add_le_add hX'card le_rfl
      _ ≤ χ := hX
  have hjY : #(α ⊕ ↥Y) ≤ ρ := hαχ hYcard
  have hIc : Model.card (E.obj I) = μ :=
    orderPresentation_obj_card E hI hL.ls_lt.le hL.inf
  have hPμ : ∀ (Q : Placement E.lab E.arity I α), D.t ρ ≤ Model.card (E.obj Q.J) := fun Q =>
    ((hL.t_lt hρinf hρ).le.trans hIc.ge).trans (mk_le_of_injective (E.map Q.f).injective)
  have hJc := hPμ P₀
  have hJc' := hPμ P₁
  have h1 := h₀ ρ hρinf hρ (Subtype.val : ↥Y → (E.obj I).carrier) hjY ht₀ hJc
  have h2 := h₁ ρ hρinf hρ (Subtype.val : ↥Y → (E.obj I).carrier) hjY ht₁ hJc'
  have hT := htest Y hYsub hYcard
  have h3 := D.trans hjY _ hB₀ _ hJc ht₀ hJc' _ _ _ (D.symm hjY hB₀ _ ht₀ hJc _ _ h1)
    (D.trans hjY hB₀ hB₁ _ ht₀ ht₁ hJc' _ _ _ hT h2)
  have h4 : SameNaturalDiagram K E D ρ hjY
      (P₀.joint (fun y : ↥Y => supportTermOf E y.1))
      (P₁.joint (fun y : ↥Y => supportTermOf E y.1)) :=
    sameNaturalDiagram_of_same_realize hρinf P₀.f P₁.f _ _ hJc hJc' _ _ h3
  have h5 := h4.relevel hρinf hτ hj
    (Sum.map id (Set.rangeFactorization (fun b => E.realize (par b))))
  have e1 : ∀ Q : Placement E.lab E.arity I α, SameNaturalDiagram K E D τ hj (Q.joint par)
      (fun c => Q.joint (fun y : ↥Y => supportTermOf E y.1)
        (Sum.map id (Set.rangeFactorization (fun b => E.realize (par b))) c)) := by
    intro Q
    refine sameNaturalDiagram_of_realize_eq _ _ ?_
    rintro (a | b)
    · rfl
    · change E.realize (SupportTerm.along Q.f (par b)) =
        E.realize (SupportTerm.along Q.f (supportTermOf E (E.realize (par b))))
      rw [← E.realize_along, ← E.realize_along, realize_supportTermOf]
  exact ((e1 P₀).trans hτ h5).trans hτ (sameNaturalDiagram_symm E D (e1 P₁))

/-- **Transfer to parameters drawn from a generated sub-presentation.** If the lifting placements
agree over a nonempty set `S ⊆ I` of positions, then `d₀`, `d₁` have equal diagrams with every
bounded parameter list whose values lie in the sub-presentation `E(S) ⊆ E(I)` (the elements
term-generated by the positions `S`). -/
theorem infra_84_transfer_of_agreeOn_values {E : OrderPresentation K} {D : StableDiagram K}
    {g : Cardinal.{u} → Cardinal.{u}} {μ : Cardinal.{u}} {I : Type u} [LinearOrder I]
    [Nonempty I] {B₀ B₁ : Model K.τ} {hB₀ : K.Mem B₀} {hB₁ : K.Mem B₁}
    {incl₀ : Language.Embedding K.τ (E.obj I).carrier B₀.carrier}
    {incl₁ : Language.Embedding K.τ (E.obj I).carrier B₁.carrier} {α : Type u}
    (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    {d₀ : α → B₀.carrier} {d₁ : α → B₁.carrier} {P₀ P₁ : Placement E.lab E.arity I α}
    (h₀ : P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) (h₁ : P₁.LiftsBounded E D hB₁ incl₁ d₁ μ)
    (S : Set I) [Nonempty S] (hag : P₀.AgreeOn E D P₁ S) {β : Type u} (ρ : Cardinal.{u})
    (hρinf : aleph0 ≤ ρ) (hρ : ρ < μ) (p : β → (E.obj I).carrier)
    (hp : ∀ b, p b ∈ Set.range (E.map (OrderEmbedding.subtype (· ∈ S)))) (hj : #(α ⊕ β) ≤ ρ)
    (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁) :
    D.same hj hB₀ hB₁ ht₀ ht₁ (Sum.elim d₀ (fun b => incl₀ (p b)))
      (Sum.elim d₁ (fun b => incl₁ (p b))) := by
  choose y hy using hp
  let par : β → SupportTerm E.lab E.arity I := fun b =>
    SupportTerm.along (OrderEmbedding.subtype (· ∈ S)) (supportTermOf E (y b))
  have hpar : ∀ b, termSupport (par b) ⊆ S := by
    rintro b _ ⟨k, rfl⟩
    exact ((supportTermOf E (y b)).pos k).2
  have hreal : ∀ b, E.realize (par b) = p b := by
    intro b
    rw [← E.realize_along, realize_supportTermOf, hy]
  have hQ : ∀ Q : Placement E.lab E.arity I α, (fun c => E.realize (Q.joint par c)) =
      fun c => E.realize (Q.joint (fun b => supportTermOf E (p b)) c) := by
    intro Q
    funext c
    rcases c with a | b
    · rfl
    · change E.realize (SupportTerm.along Q.f (par b)) =
        E.realize (SupportTerm.along Q.f (supportTermOf E (p b)))
      rw [← E.realize_along Q.f (par b), hreal, ← E.realize_along, realize_supportTermOf]
  have hIc : Model.card (E.obj I) = μ :=
    orderPresentation_obj_card E hI hL.ls_lt.le hL.inf
  have hPμ : ∀ (Q : Placement E.lab E.arity I α), D.t ρ ≤ Model.card (E.obj Q.J) := fun Q =>
    ((hL.t_lt hρinf hρ).le.trans hIc.ge).trans (mk_le_of_injective (E.map Q.f).injective)
  have hJ0 := hPμ P₀
  have hJ1 := hPμ P₁
  have e0 := h₀ ρ hρinf hρ p hj ht₀ hJ0
  have e1 := h₁ ρ hρinf hρ p hj ht₁ hJ1
  have e2 := SameNaturalDiagram.same hρinf (hag par ρ hρinf hj hpar) hJ0 hJ1
    (orderPresentation_obj_mem E P₀.J) (orderPresentation_obj_mem E P₁.J)
  rw [hQ P₀, hQ P₁] at e2
  exact D.trans hj hB₀ _ hB₁ ht₀ hJ0 ht₁ _ _ _ e0
    (D.trans hj _ _ hB₁ hJ0 hJ1 ht₁ _ _ _ e2 (D.symm hj hB₁ _ ht₁ hJ1 _ _ e1))

/-- **Generator tests ⇔ all term tests (EM-style transfer).** For candidates `d₀ ∈ B₀`, `d₁ ∈ B₁`
with lifting placements over `E(I)` at a closed level `μ`, and a set `X ⊆ I` of generator
positions with `#X + 1 + LS ≤ χ`: equal diagrams with every list of at most `χ` parameters from
the generated sub-presentation `E(X ∪ {i₀})` is equivalent to equal diagrams with every bounded
parameter list from `E(X ∪ {i₀})`, at every infinite bound below `μ` (arbitrarily many term
parameters over the generators). -/
theorem infra_84_generator_transfer_iff [CategoricalUnbounded K] {E : OrderPresentation K}
    {D : StableDiagram K}
    {g : Cardinal.{u} → Cardinal.{u}} {μ : Cardinal.{u}} {I : Type u} [LinearOrder I]
    [Nonempty I] {B₀ B₁ : Model K.τ} {hB₀ : K.Mem B₀} {hB₁ : K.Mem B₁}
    {incl₀ : Language.Embedding K.τ (E.obj I).carrier B₀.carrier}
    {incl₁ : Language.Embedding K.τ (E.obj I).carrier B₁.carrier} {α : Type u}
    (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    {d₀ : α → B₀.carrier} {d₁ : α → B₁.carrier} {P₀ P₁ : Placement E.lab E.arity I α}
    (h₀ : P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) (h₁ : P₁.LiftsBounded E D hB₁ incl₁ d₁ μ)
    (X : Set I) {ρ χ : Cardinal.{u}} (hρinf : aleph0 ≤ ρ) (hρ : ρ < μ)
    (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁)
    (hαχ : ∀ {β : Type u}, #β ≤ χ → #(α ⊕ β) ≤ ρ) (hX : #X + 1 + ls K ≤ χ) :
    (∀ (Y : Set (E.obj I).carrier)
      (_ : Y ⊆ letI : Nonempty ↥(X ∪ {Classical.arbitrary I}) := ⟨⟨_, Or.inr rfl⟩⟩
        Set.range (E.map (OrderEmbedding.subtype (· ∈ X ∪ {Classical.arbitrary I}))))
      (hY : #Y ≤ χ), D.same (hαχ hY) hB₀ hB₁ ht₀ ht₁
        (Sum.elim d₀ (fun y : ↥Y => incl₀ y.1)) (Sum.elim d₁ (fun y : ↥Y => incl₁ y.1))) ↔
    (∀ ⦃β : Type u⦄ (ρ' : Cardinal.{u}) (_ : aleph0 ≤ ρ') (_ : ρ' < μ)
      (p : β → (E.obj I).carrier)
      (_ : ∀ b, p b ∈ letI : Nonempty ↥(X ∪ {Classical.arbitrary I}) := ⟨⟨_, Or.inr rfl⟩⟩
        Set.range (E.map (OrderEmbedding.subtype (· ∈ X ∪ {Classical.arbitrary I}))))
      (hj : #(α ⊕ β) ≤ ρ') (ht₀' : D.t ρ' ≤ Model.card B₀) (ht₁' : D.t ρ' ≤ Model.card B₁),
      D.same hj hB₀ hB₁ ht₀' ht₁' (Sum.elim d₀ (fun b => incl₀ (p b)))
        (Sum.elim d₁ (fun b => incl₁ (p b)))) := by
  have : Nonempty ↥(X ∪ {Classical.arbitrary I}) := ⟨⟨_, Or.inr rfl⟩⟩
  constructor
  · intro htest β ρ' hρ'inf hρ' p hp hj ht₀' ht₁'
    have hag := infra_84_agreeOn_of_generator_tests hL hI h₀ h₁ X hρinf hρ ht₀ ht₁ hαχ hX htest
    exact infra_84_transfer_of_agreeOn_values hL hI h₀ h₁ _ hag ρ' hρ'inf hρ' p hp hj ht₀' ht₁'
  · intro hall Y hY hYc
    exact hall ρ hρinf hρ (Subtype.val : ↥Y → (E.obj I).carrier) (fun y => hY y.2) _ ht₀ ht₁

/-- **Sub-presentations are monotone in the generating positions.** If an order embedding
`f : A ↪o J` lands in a set `X ⊆ J`, then the image of `E(A)` in `E(J)` lies in the
sub-presentation `E(X)` generated by `X`. -/
theorem infra_84_range_map_subset (E : OrderPresentation K) {A J : Type u} [LinearOrder A]
    [LinearOrder J] [Nonempty A] [Nonempty J] (f : A ↪o J) (X : Set J) [Nonempty X]
    (h : ∀ a, f a ∈ X) :
    Set.range (E.map f) ⊆ Set.range (E.map (OrderEmbedding.subtype (· ∈ X))) := by
  let f' : A ↪o X := OrderEmbedding.ofStrictMono (fun a => (⟨f a, h a⟩ : X))
    (fun _ _ hab => f.strictMono hab)
  have hf : f = f'.trans (OrderEmbedding.subtype (· ∈ X)) := by ext; rfl
  rintro _ ⟨x, rfl⟩
  refine ⟨E.map f' x, ?_⟩
  rw [hf, E.map_comp]
  rfl

/-- **The pair is generated by its two segments (term generation of `U_{H'}` over
`U_H ∪ A_{H'}`).** For two order embeddings `f₁ : A₁ ↪o J` (the `U_H` segment) and
`f₂ : A₂ ↪o J` (the `A_{H'}` segment) into the index order of a presented object `E(J)`, the
images of `E(A₁)` and `E(A₂)` both lie in the sub-presentation generated by the union of the two
segments' positions, so joint parameter lists from `U_H` and `A_{H'}` are parameter lists from one
generated sub-presentation (the input to `infra_84_generator_transfer_iff`). -/
theorem infra_84_two_segment_generated (E : OrderPresentation K) {A₁ A₂ J : Type u}
    [LinearOrder A₁] [LinearOrder A₂] [LinearOrder J] [Nonempty A₁] [Nonempty A₂] [Nonempty J]
    (f₁ : A₁ ↪o J) (f₂ : A₂ ↪o J) :
    letI : Nonempty ↥(Set.range f₁ ∪ Set.range f₂) :=
      ⟨⟨f₁ (Classical.arbitrary A₁), Or.inl ⟨_, rfl⟩⟩⟩
    Set.range (E.map f₁) ∪ Set.range (E.map f₂) ⊆
      Set.range (E.map (OrderEmbedding.subtype (· ∈ Set.range f₁ ∪ Set.range f₂))) := by
  have : Nonempty ↥(Set.range f₁ ∪ Set.range f₂) :=
    ⟨⟨f₁ (Classical.arbitrary A₁), Or.inl ⟨_, rfl⟩⟩⟩
  exact Set.union_subset
    (infra_84_range_map_subset E f₁ _ fun a => Or.inl ⟨a, rfl⟩)
    (infra_84_range_map_subset E f₂ _ fun a => Or.inr ⟨a, rfl⟩)

/-- **Bounded generation in the two-segment presentation.** English (Lemma 8.4 proof): the pair
`U_{H'}` is presented on two well-ordered segments, the `U_H` segment `I₁` and the `A_{H'}`
segment `I₂`. Every list of at most `θ` elements of `E(I₁ +lex I₂)` (`θ` infinite) consists of
term values over at most `θ` generator positions in each segment: it lies in the sub-presentation
generated by `X₁ ⊆ I₁` and `X₂ ⊆ I₂` with `#X₁, #X₂ ≤ θ`. -/
theorem infra_84_pair_bounded_generation (E : OrderPresentation K) {I₁ I₂ : Type u}
    [LinearOrder I₁] [LinearOrder I₂] [Nonempty I₁] {β : Type u}
    (Z : β → (E.obj (Lex (I₁ ⊕ I₂))).carrier) {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ)
    (hβ : #β ≤ θ) :
    ∃ (X₁ : Set I₁) (X₂ : Set I₂), #X₁ ≤ θ ∧ #X₂ ≤ θ ∧
      ∃ (_ : Nonempty ↥((fun i => toLex (Sum.inl i)) '' X₁ ∪ (fun i => toLex (Sum.inr i)) '' X₂)),
        ∀ b, Z b ∈ Set.range (E.map (OrderEmbedding.subtype
          (· ∈ (fun i => toLex (Sum.inl i)) '' X₁ ∪ (fun i => toLex (Sum.inr i)) '' X₂))) := by
  classical
  have : Nonempty (Lex (I₁ ⊕ I₂)) := ⟨toLex (Sum.inl (Classical.arbitrary I₁))⟩
  let X : Set (Lex (I₁ ⊕ I₂)) := paramSupport E (Set.range Z)
  have hX : #X ≤ θ := mk_paramSupport_le E hθ (mk_range_le.trans hβ)
  have : Nonempty X := (paramSupport_nonempty E (Set.range Z)).to_subtype
  let X₁ : Set I₁ := {i | toLex (Sum.inl i) ∈ X}
  let X₂ : Set I₂ := {i | toLex (Sum.inr i) ∈ X}
  have h1 : #X₁ ≤ #X := Cardinal.mk_le_of_injective (f := fun i : X₁ => (⟨_, i.2⟩ : X))
    (fun a b h => Subtype.ext (by
      have := congrArg (fun x : X => ofLex x.1) h
      simpa using this))
  have h2 : #X₂ ≤ #X := Cardinal.mk_le_of_injective (f := fun i : X₂ => (⟨_, i.2⟩ : X))
    (fun a b h => Subtype.ext (by
      have := congrArg (fun x : X => ofLex x.1) h
      simpa using this))
  have hsub : X ⊆ (fun i => toLex (Sum.inl i)) '' X₁ ∪ (fun i => toLex (Sum.inr i)) '' X₂ := by
    intro x hx
    rcases hxs : ofLex x with i | i
    · left; exact ⟨i, by simp [X₁, ← hxs, hx], by simp [← hxs]⟩
    · right; exact ⟨i, by simp [X₂, ← hxs, hx], by simp [← hxs]⟩
  have hne : Nonempty ↥((fun i => toLex (Sum.inl i)) '' X₁ ∪ (fun i => toLex (Sum.inr i)) '' X₂) :=
    let ⟨x⟩ := ‹Nonempty X›; ⟨⟨x.1, hsub x.2⟩⟩
  refine ⟨X₁, X₂, h1.trans hX, h2.trans hX, hne, fun b => ?_⟩
  have hb : Z b ∈ Set.range Z := ⟨b, rfl⟩
  have hs := termSupport_subset_paramSupport E hb
  refine infra_84_range_map_subset E (OrderEmbedding.subtype (· ∈ X)) _ (fun x => hsub x.2) ?_
  exact ⟨_, infra_612_map_restrict E X (Z b) hs⟩

/-- **Generator tests on bounded segment parts determine the placed comparison over the pair.**
English (Lemma 8.4 proof): "If the two candidates disagree on the questioned test, their placed
comparisons disagree and yield a witness of size g(σ) + LS(K) in the two segments." Contrapositive,
with the transfer from generating parameters: there is `g` such that, for candidates over the
two-segment presentation `E(I₁ +lex I₂)` at a closed level, if the candidates have equal diagrams
with every list of at most `χ` parameters from each sub-presentation generated by `X₁ ⊆ I₁`,
`X₂ ⊆ I₂` with `#X₁, #X₂ ≤ g σ` (where `g σ + g σ + 1 + LS ≤ χ`), then their lifting placements
have the same full comparison over the pair. -/
theorem infra_84_pair_generator_tests_agree (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (D : StableDiagram K) :
    ∃ g : Cardinal.{u} → Cardinal.{u},
      ∀ (I₁ I₂ : Type u) [LinearOrder I₁] [WellFoundedLT I₁] [LinearOrder I₂]
        [WellFoundedLT I₂] [Nonempty I₁] (g' : Cardinal.{u} → Cardinal.{u}) {μ : Cardinal.{u}}
        (_ : ClosedLevel K E D g' μ) (_ : #(Lex (I₁ ⊕ I₂)) = μ)
        {B₀ B₁ : Model K.τ} (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁)
        (incl₀ : Language.Embedding K.τ (E.obj (Lex (I₁ ⊕ I₂))).carrier B₀.carrier)
        (incl₁ : Language.Embedding K.τ (E.obj (Lex (I₁ ⊕ I₂))).carrier B₁.carrier)
        {α : Type u} (σ : Cardinal.{u}) (_ : aleph0 ≤ σ) (_ : #α ≤ σ)
        (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier)
        (P₀ P₁ : Placement E.lab E.arity (Lex (I₁ ⊕ I₂)) α)
        (_ : P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) (_ : P₁.LiftsBounded E D hB₁ incl₁ d₁ μ)
        {ρ χ : Cardinal.{u}} (_ : aleph0 ≤ ρ) (_ : ρ < μ)
        (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁)
        (hαχ : ∀ {β : Type u}, #β ≤ χ → #(α ⊕ β) ≤ ρ) (_ : g σ + g σ + 1 + ls K ≤ χ),
        (∀ (X₁ : Set I₁) (X₂ : Set I₂), #X₁ ≤ g σ → #X₂ ≤ g σ →
          ∀ (Y : Set (E.obj (Lex (I₁ ⊕ I₂))).carrier)
            (_ : Y ⊆ letI : Nonempty ↥(((fun i => toLex (Sum.inl i)) '' X₁ ∪
                (fun i => toLex (Sum.inr i)) '' X₂) ∪
                {Classical.arbitrary (Lex (I₁ ⊕ I₂))}) := ⟨⟨_, Or.inr rfl⟩⟩
              Set.range (E.map (OrderEmbedding.subtype (· ∈ ((fun i => toLex (Sum.inl i)) '' X₁ ∪
                (fun i => toLex (Sum.inr i)) '' X₂) ∪ {Classical.arbitrary (Lex (I₁ ⊕ I₂))}))))
            (hY : #Y ≤ χ), D.same (hαχ hY) hB₀ hB₁ ht₀ ht₁
              (Sum.elim d₀ (fun y : ↥Y => incl₀ y.1)) (Sum.elim d₁ (fun y : ↥Y => incl₁ y.1))) →
        P₀.AgreeOn E D P₁ Set.univ := by
  obtain ⟨g, -, -, hwit⟩ := infra_84_two_segment_witness K E D
  refine ⟨g, fun I₁ I₂ _ _ _ _ _ g' μ hL hI B₀ B₁ hB₀ hB₁ incl₀ incl₁ α σ hσ hα d₀ d₁ P₀ P₁
    h₀ h₁ ρ χ hρinf hρ ht₀ ht₁ hαχ hgχ htests => ?_⟩
  have : Nonempty (Lex (I₁ ⊕ I₂)) := ⟨toLex (Sum.inl (Classical.arbitrary I₁))⟩
  by_contra hdis
  obtain ⟨X₁, X₂, hX₁, hX₂, hno⟩ := hwit I₁ I₂ σ hσ hα P₀ P₁ hdis
  apply hno
  let X : Set (Lex (I₁ ⊕ I₂)) :=
    (fun i => toLex (Sum.inl i)) '' X₁ ∪ (fun i => toLex (Sum.inr i)) '' X₂
  have hXc : #X + 1 + ls K ≤ χ := by
    refine le_trans ?_ hgχ
    refine add_le_add (add_le_add ?_ le_rfl) le_rfl
    exact (mk_union_le _ _).trans (add_le_add (mk_image_le.trans hX₁) (mk_image_le.trans hX₂))
  exact (infra_84_agreeOn_of_generator_tests hL hI h₀ h₁ X hρinf hρ ht₀ ht₁ hαχ hXc
    (htests X₁ X₂ hX₁ hX₂)).mono Set.subset_union_left

/-- **Mixed-term tests from a common amalgam over the presented pair.** English (Lemma 8.4 proof,
layout (8)): Lemma 7.2 determines the joint type of the candidate over the layout, so candidates
with the same type over `E(I)` agree on every test, in particular on parameters that are mixed
terms in both segments. Lean form: if strong maps `g₀ : B₀ → N`, `g₁ : B₁ → N` agree on `E(I)`
(through `incl₀`, `incl₁`) and identify `d₀` with `d₁`, then `d₀`, `d₁` have equal diagrams with
every bounded parameter list of `E(I)`. -/
theorem infra_84_mixed_tests_of_amalgam {E : OrderPresentation K} {D : StableDiagram K}
    {I : Type u} [LinearOrder I] [Nonempty I] {B₀ B₁ N : Model K.τ} (hB₀ : K.Mem B₀)
    (hB₁ : K.Mem B₁) (hN : K.Mem N)
    (incl₀ : Language.Embedding K.τ (E.obj I).carrier B₀.carrier)
    (incl₁ : Language.Embedding K.τ (E.obj I).carrier B₁.carrier)
    (g₀ : Language.Embedding K.τ B₀.carrier N.carrier)
    (g₁ : Language.Embedding K.τ B₁.carrier N.carrier) (hg₀ : K.Strong g₀) (hg₁ : K.Strong g₁)
    (hcomm : ∀ x, g₀ (incl₀ x) = g₁ (incl₁ x)) {α : Type u} (d₀ : α → B₀.carrier)
    (d₁ : α → B₁.carrier) (hd : ∀ a, g₀ (d₀ a) = g₁ (d₁ a)) {β : Type u}
    (p : β → (E.obj I).carrier) {ρ : Cardinal.{u}} (hρinf : aleph0 ≤ ρ) (hj : #(α ⊕ β) ≤ ρ)
    (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁) :
    D.same hj hB₀ hB₁ ht₀ ht₁ (Sum.elim d₀ (fun b => incl₀ (p b)))
      (Sum.elim d₁ (fun b => incl₁ (p b))) :=
  D.same_of_amalgam hB₀ hB₁ hN g₀ g₁ hg₀ hg₁ _ _
    (by rintro (a | b); exacts [hd a, hcomm (p b)]) hρinf hj ht₀ ht₁

/-- **Placed agreement over the pair from a common amalgam.** Candidates over a presented `E(I)` at
a closed level that are identified by strong maps into a common model agreeing on `E(I)` have
lifting placements with the same full comparison (via the generator tests of
`infra_84_generator_transfer_iff`, supplied by `infra_84_mixed_tests_of_amalgam`). -/
theorem infra_84_agree_of_amalgam [CategoricalUnbounded K] {E : OrderPresentation K}
    {D : StableDiagram K} {g : Cardinal.{u} → Cardinal.{u}} {μ : Cardinal.{u}} {I : Type u}
    [LinearOrder I] [Nonempty I] {B₀ B₁ N : Model K.τ} {hB₀ : K.Mem B₀} {hB₁ : K.Mem B₁}
    (hN : K.Mem N) {incl₀ : Language.Embedding K.τ (E.obj I).carrier B₀.carrier}
    {incl₁ : Language.Embedding K.τ (E.obj I).carrier B₁.carrier} {α : Type u}
    (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    {d₀ : α → B₀.carrier} {d₁ : α → B₁.carrier} {P₀ P₁ : Placement E.lab E.arity I α}
    (h₀ : P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) (h₁ : P₁.LiftsBounded E D hB₁ incl₁ d₁ μ)
    (g₀ : Language.Embedding K.τ B₀.carrier N.carrier)
    (g₁ : Language.Embedding K.τ B₁.carrier N.carrier) (hg₀ : K.Strong g₀) (hg₁ : K.Strong g₁)
    (hcomm : ∀ x, g₀ (incl₀ x) = g₁ (incl₁ x)) (hd : ∀ a, g₀ (d₀ a) = g₁ (d₁ a))
    (X : Set I) {ρ χ : Cardinal.{u}} (hρinf : aleph0 ≤ ρ) (hρ : ρ < μ)
    (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁)
    (hαχ : ∀ {β : Type u}, #β ≤ χ → #(α ⊕ β) ≤ ρ) (hX : #X + 1 + ls K ≤ χ) :
    P₀.AgreeOn E D P₁ X :=
  (infra_84_agreeOn_of_generator_tests hL hI h₀ h₁ X hρinf hρ ht₀ ht₁ hαχ hX
    (fun Y _ hY => infra_84_mixed_tests_of_amalgam hB₀ hB₁ hN incl₀ incl₁ g₀ g₁ hg₀ hg₁ hcomm
      d₀ d₁ hd (Subtype.val : ↥Y → (E.obj I).carrier) hρinf (hαχ hY) ht₀ ht₁)).mono
    Set.subset_union_left

/-- **Tests from equal Galois types (Theorem 6.6 form).** English (Lemma 8.4 proof): "Lemma 7.2
determines its joint type", and candidates of the same type over the layout agree on every test
over it. Lean form, at a vertex `v`: if two tuples over a base `A` (realized at `v` by `x₁`, `x₂`)
have the same Galois type, then they have equal diagrams together with every bounded parameter list
of `A` at `v` (pushed into the two hosts), including parameters that are mixed terms. -/
theorem infra_84_tests_of_sameGaloisType {S : SystemShape.{u}} {W : WorkingScheme K S}
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ} {idx : Type u}
    (t1 t2 : TupleOver K S W hμ base) (e1 : t1.idx ≃ idx) (e2 : t2.idx ≃ idx)
    (h : SameGaloisType t1 t2 e1 e2) (D : StableDiagram K) (v : S.Vertex)
    (x₁ : idx → ((W.asSystem t1.hν t1.host).obj v).carrier)
    (x₂ : idx → ((W.asSystem t2.hν t2.host).obj v).carrier)
    (hx₁ : ∀ i, t1.val (e1.symm i) = ⟨v, x₁ i⟩) (hx₂ : ∀ i, t2.val (e2.symm i) = ⟨v, x₂ i⟩)
    {β : Type u} (p : β → ((W.asSystem hμ base).obj v).carrier) {ρ : Cardinal.{u}}
    (hρinf : aleph0 ≤ ρ) (hj : #(idx ⊕ β) ≤ ρ)
    (ht₁ : D.t ρ ≤ Model.card ((W.asSystem t1.hν t1.host).obj v))
    (ht₂ : D.t ρ ≤ Model.card ((W.asSystem t2.hν t2.host).obj v)) :
    D.same hj ((W.asSystem t1.hν t1.host).inK v) ((W.asSystem t2.hν t2.host).inK v) ht₁ ht₂
      (Sum.elim x₁ (fun b => t1.incl.onVertex v (p b)))
      (Sum.elim x₂ (fun b => t2.incl.onVertex v (p b))) := by
  obtain ⟨ρ', hρ', top, f1, f2, -, -, hcomm, hval⟩ := h
  refine D.same_of_amalgam ((W.asSystem t1.hν t1.host).inK v)
    ((W.asSystem t2.hν t2.host).inK v) ((W.asSystem hρ' top).inK v) (f1.onVertex v)
    (f2.onVertex v) (f1.onVertex_strong v) (f2.onVertex_strong v) _ _ ?_ hρinf hj ht₁ ht₂
  rintro (i | b)
  · have := hval i
    rw [hx₁ i, hx₂ i] at this
    exact eq_of_heq (Sigma.mk.inj this).2
  · exact congrArg (fun φ => φ (p b)) (congrArg DFunLike.coe (hcomm v))

end AEC
