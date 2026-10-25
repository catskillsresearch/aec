module

public import AEC.Section4.StableDiagram

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

end
end AEC
