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

end AEC
