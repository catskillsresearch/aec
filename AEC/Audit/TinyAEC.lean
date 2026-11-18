module

public import AEC.Section1.AbstractElementaryClass

@[expose] public section

/-!
# A tiny abstract elementary class (statement audit)

`tinyAEC`: empty language, members are the structures with at most one element, every
embedding between members is strong. It satisfies every axiom of
`AbstractElementaryClass` and has a non-surjective strong embedding (`∅ → pt`). It is used
only to show that some formal statements quantified over *every* AEC are false as written.
-/

namespace AEC
namespace Audit

universe u

open FirstOrder Cardinal

/-- The empty language in universe `u`. -/
def eL : Tau.{u} := ⟨fun _ => PEmpty, fun _ => PEmpty⟩

instance (n : ℕ) : IsEmpty (eL.{u}.Functions n) := inferInstanceAs (IsEmpty PEmpty)
instance (n : ℕ) : IsEmpty (eL.{u}.Relations n) := inferInstanceAs (IsEmpty PEmpty)

/-- The unique `eL`-structure. -/
@[reducible] def eStr (M : Type u) : eL.{u}.Structure M where
  funMap := fun f => isEmptyElim f
  RelMap := fun r => isEmptyElim r

/-- Embeddings in the empty language are injective maps. -/
def emb {M N : Type u} [eL.{u}.Structure M] [eL.{u}.Structure N]
    (f : M → N) (hf : Function.Injective f) : eL.{u}.Embedding M N where
  toFun := f
  inj' := hf
  map_fun' := fun {_} g => isEmptyElim g
  map_rel' := fun {_} r => isEmptyElim r

/-- The union carrier of a chain of at most one-element structures. -/
def unionCarrier (C : OrdinalChain (eL.{u})) : Type u :=
  {_x : PUnit.{u + 1} // ∃ i, ∃ hi : i < C.δ, Nonempty (C.obj i hi).carrier}

instance (C : OrdinalChain (eL.{u})) : Subsingleton (unionCarrier C) :=
  ⟨fun _ _ => Subtype.ext (Subsingleton.elim _ _)⟩

def unionModel (C : OrdinalChain (eL.{u})) : Model (eL.{u}) :=
  ⟨unionCarrier C, eStr _⟩

theorem subsingleton_of_card_le {α : Type u} (h : #α ≤ 1) : Subsingleton α :=
  Cardinal.le_one_iff_subsingleton.mp h

/-- The tiny AEC. -/
noncomputable def tinyAEC : AbstractElementaryClass.{u} where
  τ := eL.{u}
  Mem M := Subsingleton M.carrier
  Strong {M N} _ := Subsingleton M.carrier ∧ Subsingleton N.carrier
  strong_mem_dom _ h := h.1
  strong_mem_cod _ h := h.2
  strong_refl _ h := ⟨h, h⟩
  strong_trans _ _ h1 h2 := ⟨h1.1, h2.2⟩
  strong_antisymm {M N} f g _ _ hgf hfg := by
    refine ⟨⟨⟨f, g, hgf, hfg⟩, fun {_} h => isEmptyElim h, fun {_} r => isEmptyElim r⟩, ?_⟩
    ext x
    rfl
  iso_closed {M N} e h := by
    obtain ⟨e⟩ := e
    exact ⟨fun a b => e.symm.injective (Subsingleton.elim _ _)⟩
  transport_strong {M N N'} f e h := ⟨h.1, ⟨fun a b => e.symm.injective (h.2.elim _ _)⟩⟩
  coherence _ _ _ h0 h1 _ := ⟨h0.1, h1.1⟩
  chain_union C _ hmem _ := by
    refine ⟨⟨unionModel C, fun i hi => emb (fun y => ⟨PUnit.unit, i, hi, ⟨y⟩⟩)
      (fun a b _ => ?_), fun i j hi hj hij => ?_, fun x => ?_⟩, ?_, fun i hi => ?_⟩
    · exact (hmem i hi).elim a b
    · ext y
      exact Subsingleton.elim (α := unionCarrier C) _ _
    · obtain ⟨_, i, hi, ⟨y⟩⟩ := x
      exact ⟨i, hi, y, Subsingleton.elim (α := unionCarrier C) _ _⟩
    · exact (inferInstance : Subsingleton (unionCarrier C))
    · exact ⟨hmem i hi, (inferInstance : Subsingleton (unionCarrier C))⟩
  chain_upper C U N g _ _ _ hU hN hg _ := by
    classical
    have hUs : Subsingleton U.obj.carrier := by
      obtain ⟨i, hi⟩ : ∃ i, i < C.δ := ⟨0, pos_iff_ne_zero.mpr C.nonzero⟩
      exact (hU i hi).2
    let pick : U.obj.carrier → N.carrier := fun x =>
      g (Classical.choose (U.covers x)) (Classical.choose (Classical.choose_spec (U.covers x)))
        (Classical.choose (Classical.choose_spec (Classical.choose_spec (U.covers x))))
    refine ⟨emb pick (fun a b _ => hUs.elim a b), ⟨hUs, hN⟩, fun i hi => ?_⟩
    ext y
    exact hN.elim _ _
  lsBound := ℵ₀
  lsBound_infinite := le_rfl
  lsBound_language := by
    have : eL.{u}.card = 0 := by
      simp [Language.card, Language.Symbols, eL]
    simp [this]
  ls_axiom M hM A := by
    refine ⟨M, Language.Embedding.refl _ _, hM, ⟨hM, hM⟩, fun a _ => ⟨a, rfl⟩, ?_⟩
    have : #M.carrier ≤ 1 := Cardinal.le_one_iff_subsingleton.mpr hM
    exact (this.trans one_le_aleph0).trans le_add_self

/-- The empty AEC: no members, no strong embeddings. Every axiom holds vacuously
(`OrdinalChain`s are nonempty, so `chain_union` has a member hypothesis to refute). -/
def emptyAEC : AbstractElementaryClass.{u} where
  τ := eL.{u}
  Mem _ := False
  Strong _ := False
  strong_mem_dom _ h := h.elim
  strong_mem_cod _ h := h.elim
  strong_refl _ h := h.elim
  strong_trans _ _ h := h.elim
  strong_antisymm _ _ h := h.elim
  iso_closed _ h := h.elim
  transport_strong _ _ h := h.elim
  coherence _ _ _ h := h.elim
  chain_union C _ hmem _ := (hmem 0 (pos_iff_ne_zero.mpr C.nonzero)).elim
  chain_upper _ _ _ _ _ _ _ _ hN := hN.elim
  lsBound := ℵ₀
  lsBound_infinite := le_rfl
  lsBound_language := by
    have : eL.{u}.card = 0 := by
      simp [Language.card, Language.Symbols, eL]
    simp [this]
  ls_axiom _ hM := hM.elim

end Audit
end AEC
