module

public import AEC.Section8.HullPieces83
public import AEC.Section8.EMExtend83

/-!
# Lemma 8.3: from expanded-language hull pieces to finite pieces of `K`

The samples of Lemma 8.3 are structures in an expansion `L` of `K.τ` (along `φ : K.τ →ᴸ L`)
in which the term hull of every finite tuple is, after reduct, a strong submodel ("the
vertex LS witnesses", `HullStrong`).  Under that hypothesis on the admitted class, the hull
maps along position maps are strong `τ`-embeddings (coherence, isomorphism invariance), and
the pieces read off coherent types (`tpPiece`, `tpPieceMap`) form a `FinPieces K`, to which
the generic Ehrenfeucht–Mostowski construction (`FinPieces.limit`, `EM83.presentation`)
applies.
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {K : AbstractElementaryClass.{u}} {L : Language.{u, u}} (φ : K.τ →ᴸ L)

/-- The `τ`-reduct of an `L`-structure, as a model. -/
def red (M : Type u) [L.Structure M] : Model K.τ := ⟨M, φ.reduct M⟩

/-- The reduct of an `L`-embedding. -/
def redEmb {M N : Type u} [L.Structure M] [L.Structure N] (f : M ↪[L] N) :
    Language.Embedding K.τ (red φ M).carrier (red φ N).carrier where
  toFun := f
  inj' := f.injective
  map_fun' {n} g xs := f.map_fun (φ.onFunction g) xs
  map_rel' {n} r xs := f.map_rel (φ.onRelation r) xs

theorem redEmb_apply {M N : Type u} [L.Structure M] [L.Structure N] (f : M ↪[L] N) (x : M) :
    redEmb φ f x = f x := rfl

/-- The reduct of an `L`-isomorphism given by mutually inverse `L`-embeddings. -/
def redEquiv {M N : Type u} [L.Structure M] [L.Structure N] (f : M ↪[L] N) (g : N ↪[L] M)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) :
    (red φ M).carrier ≃[K.τ] (red φ N).carrier where
  toFun := f
  invFun := g
  left_inv := hgf
  right_inv := hfg
  map_fun' {n} h xs := f.map_fun (φ.onFunction h) xs
  map_rel' {n} r xs := f.map_rel (φ.onRelation r) xs

/-- **Vertex LS witnesses.**  In every admitted structure the reduct of the term hull of every
finite tuple is strong in the reduct of the structure. -/
def HullStrong (P : ∀ (M : Type u) [L.Structure M], Prop) : Prop :=
  ∀ (M : Type u) [L.Structure M], P M → ∀ {m : ℕ} (v : Fin m → M),
    K.Strong (redEmb φ (hullEmb (L := L) v))

variable {φ}

/-- **Hull maps are strong.**  Between admitted structures, the hull map along a position map
`g` with `tp(v') = tp(v ∘ g)` is a strong `τ`-embedding. -/
theorem hullMap_strong {P : ∀ (M : Type u) [L.Structure M], Prop} (hP : HullStrong φ P)
    {M N : Type u} [L.Structure M] [L.Structure N] (hM : P M) (hN : P N) {m m' : ℕ}
    {v' : Fin m' → N} {v : Fin m → M} (g : Fin m' → Fin m)
    (h : tpCode (L := L) v' = tpCode (v ∘ g)) :
    K.Strong (redEmb φ (hullMapEmb g h)) := by
  -- the sub-hull of `v ∘ g` inside the hull of `v`
  let j := hullMapEmb (L := L) (v' := v ∘ g) (v := v) g rfl
  have hj : K.Strong (redEmb φ j) := by
    refine K.coherence (redEmb φ j) (redEmb φ (hullEmb (L := L) (v ∘ g))) (redEmb φ (hullEmb (L := L) v))
      (hP M hM (v ∘ g)) (hP M hM v) ?_
    ext x
    exact (hullVal_hullMap (L := L) (v' := v ∘ g) g rfl (show Hull (L := L) (v ∘ g) from x)).trans
      (hullVal_out _ _).symm
  -- the hull of `v'` is isomorphic to the hull of `v ∘ g`
  let i := hullMapEmb (L := L) (v' := v') (v := v ∘ g) id h
  let i' := hullMapEmb (L := L) (v' := v ∘ g) (v := v') id h.symm
  have hii : ∀ x, i' (i x) = x := fun x => by
    show hullMap id h.symm (hullMap id h x) = x
    rw [hullMap_comp id id h h.symm rfl]
    exact hullMap_id v' rfl x
  have hii' : ∀ y, i (i' y) = y := fun y => by
    show hullMap id h (hullMap id h.symm y) = y
    rw [hullMap_comp id id h.symm h rfl]
    exact hullMap_id (v ∘ g) rfl y
  let e := redEquiv φ i i' hii hii'
  have hmem : K.Mem (red φ (Hull (L := L) v')) := K.strong_mem_dom _ (hP N hN v')
  have he : K.Strong e.toEmbedding := by
    have := K.transport_strong (Language.Embedding.refl K.τ _) e (K.strong_refl _ hmem)
    exact this
  have hcomp : redEmb φ (hullMapEmb g h) = (redEmb φ j).comp e.toEmbedding := by
    ext x
    exact (hullMap_comp (L := L) (v := v) id g h rfl h (show Hull (L := L) v' from x)).symm
  rw [hcomp]
  exact K.strong_trans _ _ he hj

section Pieces

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {c : (m : ℕ) → 0 < m → TpColor L m}
  (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSample P) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpRes f (c m hm))

include hcoh in
/-- **The finite pieces of `K`.**  For an admitted class with vertex LS witnesses, the
reducts of the pieces read off coherent types, with the reducts of the piece maps. -/
noncomputable def tpFinPieces (hP : HullStrong φ P) : EM83.FinPieces K where
  obj k := red φ (tpPiece hc k)
  mem k := K.strong_mem_dom _ (hP _ (wit hc k).mem (wit hc k).v)
  map e := redEmb φ (tpPieceMap hc hcoh e)
  map_refl k := by
    ext x
    exact hullMap_id _ (tpPiece_tp hc hcoh (k := k) (l := k) idEmb) x
  map_trans e f := by
    ext x
    exact tpPieceMap_trans hc hcoh e f x
  strong e := hullMap_strong hP (wit hc _).mem (wit hc _).mem e (tpPiece_tp hc hcoh e)

end Pieces

end Hull83
end AEC
