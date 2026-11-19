module

public import AEC.Section8.HullPieces83
public import AEC.Section8.EMPresent83
public import Mathlib.ModelTheory.Encoding

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
  ∀ (M : Type u) [L.Structure M], P M → ∀ {ι : Type} [Finite ι] (v : ι → M),
    K.Strong (redEmb φ (hullEmb (L := L) v))

variable {φ}

/-- **Hull maps are strong.**  Between admitted structures, the hull map along a position map
`g` with `tp(v') = tp(v ∘ g)` is a strong `τ`-embedding. -/
theorem hullMap_strong {P : ∀ (M : Type u) [L.Structure M], Prop} (hP : HullStrong φ P)
    {M N : Type u} [L.Structure M] [L.Structure N] (hM : P M) (hN : P N) {ι ι' : Type}
    [Finite ι] [Finite ι'] {v' : ι' → N} {v : ι → M} (g : ι' → ι)
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

theorem hullMap_mk {M N : Type u} [L.Structure M] [L.Structure N] {ι ι' : Type}
    {v' : ι' → N} {v : ι → M} (g : ι' → ι)
    (h : tpCode (L := L) v' = tpCode (v ∘ g)) (t : L.Term ι') :
    hullMap g h (Quotient.mk (hullSetoid v') t) = Quotient.mk (hullSetoid v) (t.relabel g) := rfl

/-- Terms in finitely many variables are few when the function symbols are. -/
theorem card_terms_le (hL : max ℵ₀ #(Σ i, L.Functions i) ≤ ls K) :
    #(Σ n, L.Term (Fin n)) ≤ ls K := by
  have e : (Σ n, L.Term (Empty ⊕ Fin n)) ≃ (Σ n, L.Term (Fin n)) :=
    Equiv.sigmaCongrRight fun n => Term.relabelEquiv (Equiv.emptySum Empty (Fin n))
  rw [← Cardinal.mk_congr e, Term.card_sigma, mk_sum]
  simpa using hL

section Enum

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {c : (m : ℕ) → 0 < m → TpColor L m}
  (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSample P) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpRes f (c m hm))

/-- The term enumeration of the hull pieces. -/
noncomputable def tpEnum (k : ℕ) (a : Σ n, L.Term (Fin n)) : tpPiece hc k :=
  if h : a.1 = k + 1 then Quotient.mk _ (a.2.relabel (Fin.cast h)) else Quotient.mk _ (Term.var 0)

theorem tpEnum_surj (k : ℕ) : Function.Surjective (tpEnum hc k) := by
  intro x
  induction x using Quotient.ind with
  | _ t =>
    refine ⟨⟨k + 1, t⟩, ?_⟩
    simp only [tpEnum, dite_true]
    congr 1
    have : (Fin.cast (rfl : k + 1 = k + 1)) = id := by funext i; rfl
    rw [this]
    exact Term.relabel_id t

include hcoh in
/-- **Enumeration data** for the hull pieces: labels are terms in finitely many variables,
and the skeleton is the first variable (distinct copies by injectivity of the witnesses). -/
noncomputable def tpPieceEnum (hP : HullStrong φ P) (hL : max ℵ₀ #(Σ i, L.Functions i) ≤ ls K) :
    EM83.PieceEnum (tpFinPieces hc hcoh hP) where
  Lab := Σ n, L.Term (Fin n)
  lab_small := card_terms_le hL
  enum k := tpEnum hc k
  surj k := tpEnum_surj hc k
  skelLab := ⟨1, Term.var 0⟩
  skel_distinct {l} e e' hne heq := by
    have h2 : hullVal (wit hc l).v (hullMap (L := L) (⇑e) (tpPiece_tp hc hcoh e)
        (Quotient.mk _ ((Term.var 0 : L.Term (Fin 1)).relabel (Fin.cast rfl)))) =
        hullVal (wit hc l).v (hullMap (L := L) (⇑e') (tpPiece_tp hc hcoh e')
        (Quotient.mk _ ((Term.var 0 : L.Term (Fin 1)).relabel (Fin.cast rfl)))) :=
      congrArg (hullVal (L := L) (wit hc l).v) heq
    rw [hullMap_mk, hullMap_mk, hullVal_mk, hullVal_mk] at h2
    simp only [Term.realize_relabel, Term.realize_var, Function.comp_apply] at h2
    exact hne (by simpa using (wit hc l).inj h2)

include hcoh in
/-- The Ehrenfeucht–Mostowski order presentation of the hull pieces read off coherent types
of an admitted class with vertex LS witnesses and a small expanded language. -/
noncomputable def tpPresentation (hP : HullStrong φ P)
    (hL : max ℵ₀ #(Σ i, L.Functions i) ≤ ls K) : OrderPresentation K :=
  EM83.presentation (tpPieceEnum hc hcoh hP hL)

/-- **Template from the expanded samples.**  An admitted class of `L`-structures with
arbitrarily large members, vertex LS witnesses, and a small expansion yields coherent types
whose hull pieces form an enumerated `FinPieces K`, hence an order presentation of `K`
whose finite pieces embed in actual homogeneous samples. -/
theorem exists_tp_presentation
    (hlarge : ∀ κ : Cardinal.{u}, ∃ (M : Type u) (_ : L.Structure M), P M ∧ κ ≤ #M)
    (hP : HullStrong φ P) (hL : max ℵ₀ #(Σ i, L.Functions i) ≤ ls K) :
    ∃ (c : (m : ℕ) → 0 < m → TpColor L m) (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Joint (TpSample P) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = tpRes f (c m hm)),
      ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        (tpPresentation hc hcoh hP hL).obj I = ((tpFinPieces hc hcoh hP).limit I).obj := by
  obtain ⟨c, hc, hcoh⟩ := tp_coherent_colors hlarge
  exact ⟨c, hc, hcoh, fun I _ _ => rfl⟩

end Enum

end Hull83
end AEC
