module

public import AEC.Section4.StableDiagram
public import AEC.Section3.UniformOrbitBound

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- Push a support term along an order embedding by substituting positions. -/
def SupportTerm.along {lab : Type u} {arity : lab → ℕ} {I J : Type u}
    [LinearOrder I] [LinearOrder J] (f : I ↪o J) (t : SupportTerm lab arity I) :
    SupportTerm lab arity J where
  label := t.label
  pos := fun a => f (t.pos a)
  increasing := f.strictMono.comp t.increasing

@[simp]
theorem SupportTerm.along_label {lab : Type u} {arity : lab → ℕ} {I J : Type u}
    [LinearOrder I] [LinearOrder J] (f : I ↪o J) (t : SupportTerm lab arity I) :
    (SupportTerm.along f t).label = t.label :=
  rfl

theorem SupportTerm.along_trans {lab : Type u} {arity : lab → ℕ} {I J K : Type u}
    [LinearOrder I] [LinearOrder J] [LinearOrder K]
    (f : I ↪o J) (g : J ↪o K) (t : SupportTerm lab arity I) :
    SupportTerm.along g (SupportTerm.along f t) = SupportTerm.along (f.trans g) t :=
  rfl

theorem SupportTerm.along_refl {lab : Type u} {arity : lab → ℕ} {I : Type u}
    [LinearOrder I] (t : SupportTerm lab arity I) :
    SupportTerm.along (OrderIso.refl I).toOrderEmbedding t = t := by
  cases t with
  | mk label pos increasing =>
    change SupportTerm.mk label (fun a => (OrderIso.refl I) (pos a))
        ((OrderIso.refl I).toOrderEmbedding.strictMono.comp increasing) =
      SupportTerm.mk label pos increasing
    simp [OrderIso.refl_apply]

/-- Realization is natural for `SupportTerm.along`. -/
theorem OrderPresentation.realize_along {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {I J : Type u}
    [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (t : SupportTerm E.lab E.arity I) :
    E.map f (E.realize t) = E.realize (SupportTerm.along f t) :=
  E.realize_map f t

/-- **Definition 4.4.** Two term lists have the same natural diagram when their
realizations have the same stable diagram in some common extension of the index orders
past the diagram threshold. -/
def SameNaturalDiagram (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) {I I' : Type u} [LinearOrder I] [LinearOrder I']
    [Nonempty I] [Nonempty I'] {α : Type u} (σ : Cardinal.{u}) (hσ : #α ≤ σ)
    (t : α → SupportTerm E.lab E.arity I) (s : α → SupportTerm E.lab E.arity I') : Prop :=
  ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (f : I ↪o J) (g : I' ↪o J)
    (hcard : D.t σ ≤ Model.card (E.obj J)) (hM : K.Mem (E.obj J)),
    D.same hσ (M := E.obj J) (N := E.obj J) hM hM hcard hcard
      (fun a => E.realize (SupportTerm.along f (t a)))
      (fun a => E.realize (SupportTerm.along g (s a)))

/-- Bridge: equal realized `D.same` lists on a common large presentation yield
`SameNaturalDiagram` (identity embeddings of the shared index). -/
theorem sameNaturalDiagram_of_D_same {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) (D : StableDiagram K)
    {I : Type u} [LinearOrder I] [Nonempty I] {α : Type u} {σ : Cardinal.{u}}
    (hσ : #α ≤ σ)
    (t s : α → SupportTerm E.lab E.arity I)
    (hcard : D.t σ ≤ Model.card (E.obj I))
    (hM : K.Mem (E.obj I))
    (hsame : D.same hσ hM hM hcard hcard
      (fun a => E.realize (t a)) (fun a => E.realize (s a))) :
    SameNaturalDiagram K E D σ hσ t s := by
  refine ⟨I, inferInstance, inferInstance,
    (OrderIso.refl I).toOrderEmbedding, (OrderIso.refl I).toOrderEmbedding, hcard, hM, ?_⟩
  have ht : (fun a => E.realize (SupportTerm.along (OrderIso.refl I).toOrderEmbedding (t a))) =
      fun a => E.realize (t a) := by
    funext a; simp [SupportTerm.along_refl]
  have hs : (fun a => E.realize (SupportTerm.along (OrderIso.refl I).toOrderEmbedding (s a))) =
      fun a => E.realize (s a) := by
    funext a; simp [SupportTerm.along_refl]
  rw [ht, hs]
  exact hsame

theorem sameNaturalDiagram_refl {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) (D : StableDiagram K)
    {I : Type u} [LinearOrder I] [Nonempty I] {α : Type u} {σ : Cardinal.{u}}
    (hσ : #α ≤ σ) (t : α → SupportTerm E.lab E.arity I)
    (hcard : D.t σ ≤ Model.card (E.obj I)) :
    SameNaturalDiagram K E D σ hσ t t := by
  have hM : K.Mem (E.obj I) := orderPresentation_obj_mem E I
  exact sameNaturalDiagram_of_D_same E D hσ t t hcard hM (D.refl hσ hM hcard _)

theorem sameNaturalDiagram_symm {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) (D : StableDiagram K)
    {I I' : Type u} [LinearOrder I] [LinearOrder I'] [Nonempty I] [Nonempty I']
    {α : Type u} {σ : Cardinal.{u}} {hσ : #α ≤ σ}
    {t : α → SupportTerm E.lab E.arity I} {s : α → SupportTerm E.lab E.arity I'}
    (h : SameNaturalDiagram K E D σ hσ t s) :
    SameNaturalDiagram K E D σ hσ s t := by
  obtain ⟨J, linJ, nonJ, f, g, hcard, hM, hsame⟩ := h
  exact ⟨J, linJ, nonJ, g, f, hcard, hM, D.symm hσ hM hM hcard hcard _ _ hsame⟩

/-- On a large enough presentation, a strong endomorphism matching the realized lists
witnesses `SameNaturalDiagram` via identity embeddings of the index. -/
theorem sameNaturalDiagram_of_strong_endomorphism {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) (D : StableDiagram K)
    {I : Type u} [LinearOrder I] [Nonempty I] {α : Type u} {σ : Cardinal.{u}}
    (hσ : #α ≤ σ) (hσinf : aleph0 ≤ σ)
    (t s : α → SupportTerm E.lab E.arity I)
    (hcard : D.t σ ≤ Model.card (E.obj I))
    (φ : Language.Embedding K.τ (E.obj I).carrier (E.obj I).carrier)
    (hφ : K.Strong φ)
    (hmatch : ∀ a, φ (E.realize (t a)) = E.realize (s a)) :
    SameNaturalDiagram K E D σ hσ t s := by
  have hM : K.Mem (E.obj I) := orderPresentation_obj_mem E I
  refine sameNaturalDiagram_of_D_same E D hσ t s hcard hM ?_
  exact D.of_strong hσ hM hM hcard hcard (fun a => E.realize (t a)) (fun a => E.realize (s a))
    φ hσinf hφ hmatch

/-- Package a `D.same` comparison of realized lists along embeddings as `SameNaturalDiagram`. -/
theorem sameNaturalDiagram_along {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) (D : StableDiagram K)
    {I I' J : Type u} [LinearOrder I] [LinearOrder I'] [LinearOrder J]
    [Nonempty I] [Nonempty I'] [Nonempty J]
    {α : Type u} {σ : Cardinal.{u}} {hσ : #α ≤ σ}
    (t : α → SupportTerm E.lab E.arity I) (s : α → SupportTerm E.lab E.arity I')
    (f : I ↪o J) (g : I' ↪o J) (hcard : D.t σ ≤ Model.card (E.obj J))
    (hM : K.Mem (E.obj J))
    (hsame : D.same hσ hM hM hcard hcard
      (fun a => E.realize (SupportTerm.along f (t a)))
      (fun a => E.realize (SupportTerm.along g (s a)))) :
    SameNaturalDiagram K E D σ hσ t s :=
  ⟨J, inferInstance, inferInstance, f, g, hcard, hM, hsame⟩

end
end AEC
