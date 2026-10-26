module

public import AEC.Section1.LoewenheimSkolem
public import AEC.Section2.SupportTerm
public import Mathlib.Order.Hom.Basic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- **Theorem 2.6.** An Ehrenfeucht–Mostowski order presentation for an AEC with
arbitrarily large models. `E` sends a nonempty linear order to a model, and an order
embedding to a strong map, by substituting indices in finitely supported labeled terms. -/
structure OrderPresentation (K : AbstractElementaryClass.{u}) where
  ell : Cardinal.{u}
  ell_eq : ell = ls K
  lab : Type u
  lab_small : #lab ≤ ell
  arity : lab → ℕ
  arity_pos : ∀ a, 0 < arity a
  obj : (I : Type u) → [LinearOrder I] → [Nonempty I] → Model K.τ
  map : ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J],
    (I ↪o J) → Language.Embedding K.τ (obj I).carrier (obj J).carrier
  map_strong : ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J), K.Strong (map f)
  map_id : ∀ {I : Type u} [LinearOrder I] [Nonempty I],
    map (OrderIso.refl I).toOrderEmbedding = Language.Embedding.refl K.τ (obj I).carrier
  map_comp : ∀ {I J P : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder P]
    [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P),
    map (f.trans g) = (map g).comp (map f)
  realize : ∀ {I : Type u} [LinearOrder I] [Nonempty I],
    SupportTerm lab arity I → (obj I).carrier
  realize_surjective : ∀ {I : Type u} [LinearOrder I] [Nonempty I],
    Function.Surjective (realize (I := I))
  /-- Realization is natural in the index order: substituting along an order embedding
  commutes with the induced strong map of models. -/
  realize_map : ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (t : SupportTerm lab arity I),
    map f (realize t) =
      realize ⟨t.label, f ∘ t.pos, f.strictMono.comp t.increasing⟩
  /-- Equality of realized elements, and the value of every function and relation symbol
  on them, depends only on the labels and the order/equality pattern of the indices. -/
  pattern_determines : ∀ {I : Type u} [LinearOrder I] [Nonempty I] {n : ℕ}
    (t s : Fin n → SupportTerm lab arity I)
    (hlabel : ∀ i, (t i).label = (s i).label),
    (∀ i j (a : Fin (arity (t i).label)) (b : Fin (arity (t j).label)),
      (t i).pos a = (t j).pos b ↔
        (s i).pos (Fin.cast (congrArg arity (hlabel i)) a) =
          (s j).pos (Fin.cast (congrArg arity (hlabel j)) b)) →
    (∀ i j (a : Fin (arity (t i).label)) (b : Fin (arity (t j).label)),
      (t i).pos a < (t j).pos b ↔
        (s i).pos (Fin.cast (congrArg arity (hlabel i)) a) <
          (s j).pos (Fin.cast (congrArg arity (hlabel j)) b)) →
    (∀ i j, realize (t i) = realize (t j) ↔ realize (s i) = realize (s j)) ∧
    (∀ {k} (f : K.τ.Functions k) (idx : Fin k → Fin n) (j : Fin n),
      Language.Structure.funMap f (fun a => realize (t (idx a))) = realize (t j) ↔
        Language.Structure.funMap f (fun a => realize (s (idx a))) = realize (s j)) ∧
    (∀ {k₁ k₂ : ℕ} (f₁ : K.τ.Functions k₁) (f₂ : K.τ.Functions k₂)
      (idx₁ : Fin k₁ → Fin n) (idx₂ : Fin k₂ → Fin n),
      Language.Structure.funMap f₁ (fun a => realize (t (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => realize (t (idx₂ a))) ↔
        Language.Structure.funMap f₁ (fun a => realize (s (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => realize (s (idx₂ a)))) ∧
    (∀ {k} (r : K.τ.Relations k) (idx : Fin k → Fin n),
      Language.Structure.RelMap r (fun a => realize (t (idx a))) ↔
        Language.Structure.RelMap r (fun a => realize (s (idx a))))
  skeleton : ∀ {I : Type u} [LinearOrder I] [Nonempty I], I ↪ (obj I).carrier
  skeleton_natural : ∀ {I J : Type u} [LinearOrder I] [LinearOrder J]
    [Nonempty I] [Nonempty J] (f : I ↪o J) (i : I),
    map f (skeleton i) = skeleton (f i)
  sub : ∀ {I : Type u} [LinearOrder I] [Nonempty I], Finset I → Model K.τ
  sub_incl : ∀ {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I),
    s.Nonempty → Language.Embedding K.τ (sub s).carrier (obj I).carrier
  sub_strong : ∀ {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I) (hs : s.Nonempty),
    K.Strong (sub_incl s hs)
  sub_card : ∀ {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I),
    s.Nonempty → Model.card (sub s) ≤ ell
  sub_mono : ∀ {I : Type u} [LinearOrder I] [Nonempty I] (s t : Finset I)
    (hs : s.Nonempty) (ht : t.Nonempty), s ⊆ t →
    ∃ g : Language.Embedding K.τ (sub s).carrier (sub t).carrier,
      K.Strong g ∧ (sub_incl t ht).comp g = sub_incl s hs
  sub_cover : ∀ {I : Type u} [LinearOrder I] [Nonempty I] (x : (obj I).carrier),
    ∃ s : Finset I, ∃ hs : s.Nonempty, ∃ y : (sub s).carrier, sub_incl s hs y = x
  card_lower : ∀ {I : Type u} [LinearOrder I] [Nonempty I], #I ≤ Model.card (obj I)
  card_upper : ∀ {I : Type u} [LinearOrder I] [Nonempty I],
    Model.card (obj I) ≤ #I + ell

end
end AEC
