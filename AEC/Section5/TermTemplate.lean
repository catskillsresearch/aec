module

public import AEC.Section5.SystemArrow
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order

@[expose] public section

namespace AEC
section

universe u

open FirstOrder
open Sum

/-- `J ⊕ₗ H` is nonempty whenever the left summand is. -/
instance nonempty_sumLex_of_left {J H : Type u} [Nonempty J] : Nonempty (J ⊕ₗ H) :=
  Nonempty.map (toLex ∘ inl) ‹Nonempty J›

/-- `J ⊕ₗ H` is nonempty whenever the right summand is. -/
instance nonempty_sumLex_of_right {J H : Type u} [Nonempty H] : Nonempty (J ⊕ₗ H) :=
  Nonempty.map (toLex ∘ inr) ‹Nonempty H›

/-- Order embedding of `J` as the left summand of the lexicographic sum `J ⊕ₗ H`. -/
def sumLexEmbedLeftIncl (J H : Type u) [LinearOrder J] [LinearOrder H] : J ↪o (J ⊕ₗ H) :=
  OrderEmbedding.ofStrictMono (fun j => inlₗ j) Lex.inl_strictMono

/-- Extend an order embedding on the right summand by the identity on the left:
`id ⊕ₗ f : (J ⊕ₗ H) ↪o (J ⊕ₗ H')`. -/
def sumLexEmbedRight {J H H' : Type u} [LinearOrder J] [LinearOrder H] [LinearOrder H']
    (f : H ↪o H') : (J ⊕ₗ H) ↪o (J ⊕ₗ H') :=
  OrderEmbedding.ofMapLEIff (fun x => toLex ((ofLex x).map id f)) fun a b => by
    rw [Lex.le_def, Lex.le_def]
    cases ofLex a <;> cases ofLex b
    · simp [Lex.toLex_le_toLex, Lex.inl_le_inl_iff]
    · simp [Lex.toLex_le_toLex, Lex.inl_le_inr, Lex.inl_le_inr]
    · simp [Lex.toLex_le_toLex, Lex.not_inr_le_inl, Lex.not_inr_le_inl]
    · simp [Lex.toLex_le_toLex, Lex.inr_le_inr_iff, f.map_rel_iff]

@[simp]
theorem sumLexEmbedRight_apply_inl {J H H' : Type u}
    [LinearOrder J] [LinearOrder H] [LinearOrder H'] (f : H ↪o H') (j : J) :
    sumLexEmbedRight (J := J) f (inlₗ j) = inlₗ j :=
  rfl

@[simp]
theorem sumLexEmbedRight_apply_inr {J H H' : Type u}
    [LinearOrder J] [LinearOrder H] [LinearOrder H'] (f : H ↪o H') (h : H) :
    sumLexEmbedRight (J := J) f (inrₗ h) = inrₗ (f h) :=
  rfl

theorem sumLexEmbedRight_refl {J H : Type u} [LinearOrder J] [LinearOrder H] :
    sumLexEmbedRight (J := J) (OrderIso.refl H).toOrderEmbedding =
      (OrderIso.refl (J ⊕ₗ H)).toOrderEmbedding := by
  refine RelEmbedding.ext fun x => ?_
  simp only [sumLexEmbedRight, OrderEmbedding.coe_ofMapLEIff, OrderIso.coe_toOrderEmbedding,
    OrderIso.refl_apply]
  rw [← toLex_ofLex x]
  cases ofLex x <;> rfl

theorem sumLexEmbedRight_trans {J H H' H'' : Type u}
    [LinearOrder J] [LinearOrder H] [LinearOrder H'] [LinearOrder H'']
    (f : H ↪o H') (g : H' ↪o H'') :
    sumLexEmbedRight (J := J) (f.trans g) =
      (sumLexEmbedRight (J := J) f).trans (sumLexEmbedRight (J := J) g) := by
  refine RelEmbedding.ext fun x => ?_
  simp only [sumLexEmbedRight, OrderEmbedding.coe_ofMapLEIff, RelEmbedding.trans_apply]
  rw [← toLex_ofLex x]
  cases ofLex x <;> rfl

/-- A finite-support term template: a system for every nonempty linear order, and a system
arrow for every order embedding, by substitution of positions. -/
structure TermTemplate (K : AbstractElementaryClass.{u}) (S : SystemShape.{u}) where
  present : ∀ (I : Type u) [LinearOrder I] [Nonempty I], SystemObject K S
  onOrder : ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J],
    (I ↪o J) → SystemArrow K S (present I) (present J)
  onOrder_id : ∀ {I : Type u} [LinearOrder I] [Nonempty I] (v : S.Vertex)
    (x : ((present I).obj v).carrier),
    (onOrder (OrderIso.refl I).toOrderEmbedding).onVertex v x = x
  onOrder_comp : ∀ {I J P : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder P]
    [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P) (v : S.Vertex)
    (x : ((present I).obj v).carrier),
    (onOrder (f.trans g)).onVertex v x =
      (onOrder g).onVertex v ((onOrder f).onVertex v x)

/-- Fix a nonempty linear order `J` of name-support and vary the remainder `H`: presentations
are `F` on `J ⊕ₗ H`, and order maps on `H` extend by `id` on `J`. -/
def TermTemplate.withFixedSupport (F : TermTemplate K S) (J : Type u)
    [LinearOrder J] [Nonempty J] : TermTemplate K S where
  present H := F.present (J ⊕ₗ H)
  onOrder f := F.onOrder (sumLexEmbedRight (J := J) f)
  onOrder_id := fun {_H} _ _ v x => by
    rw [sumLexEmbedRight_refl]
    exact F.onOrder_id v x
  onOrder_comp := fun {_H} {_H'} {_H''} _ _ _ _ _ _ f g v x => by
    rw [sumLexEmbedRight_trans f g]
    exact F.onOrder_comp _ _ v x

/-- Arrow placing the fixed-support presentation of `J` into the padded presentation on
`J ⊕ₗ H` (names live on the left summand). -/
def TermTemplate.fixedSupportArrow (F : TermTemplate K S) (J : Type u)
    [LinearOrder J] [Nonempty J] (H : Type u) [LinearOrder H] [Nonempty H] :
    SystemArrow K S (F.present J) (F.present (J ⊕ₗ H)) :=
  F.onOrder (sumLexEmbedLeftIncl J H)

end
end AEC
