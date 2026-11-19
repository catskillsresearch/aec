module

public import AEC.Section8.HullExtract83
public import Mathlib.ModelTheory.Semantics

/-!
# Lemma 8.3: type colors for samples in an expanded language

The coloring layer of the hull extraction in Lemma 8.3, independent of the particular pair
samples.  A sample is an ordered injective sequence in a structure for an arbitrary
(expanded) first-order language `L`; a finite index set is colored by the complete type
(the set of true `L`-formulas) of the increasing tuple it enumerates.  The palette at each
arity is the set-sized `Set (L.Formula (Fin m))`.  The family is closed under thinning, the
color of a sub-tuple is the restriction (`relabel`) of the color of the tuple, and so the
generic tower (`coherent_colors`, `coherent_colors_compat`) gives coherent colors at all
arities with arbitrarily large homogeneous samples.  The labelled atomic diagram of the term
hull of a tuple, and the inclusions among the hulls of its subsets, are read off this type
(atomic formulas in the terms of `L`).
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {L : Language.{u, u}}

/-- The palette at arity `m`: sets of `L`-formulas in `m` variables. -/
abbrev TpColor (L : Language.{u, u}) (m : ℕ) : Type u := Set (L.Formula (Fin m))

/-- The type of a tuple. -/
def tpCode {M : Type u} [L.Structure M] {m : ℕ} (v : Fin m → M) : TpColor L m :=
  {φ | φ.Realize v}

/-- Restriction of a type along an increasing map of positions. -/
def tpRes {m m' : ℕ} (f : Fin m' ↪o Fin m) (c : TpColor L m) : TpColor L m' :=
  {φ | φ.relabel f ∈ c}

theorem tpRes_tpCode {M : Type u} [L.Structure M] {m m' : ℕ} (f : Fin m' ↪o Fin m)
    (v : Fin m → M) : tpRes f (tpCode (L := L) v) = tpCode (v ∘ f) := by
  ext φ
  exact Formula.realize_relabel

/-- The color of a finite index set: the type of its increasing enumeration. -/
noncomputable def tpCol {α : Type u} [LinearOrder α] {M : Type u} [L.Structure M]
    (base : α → M) (m : ℕ) (s : Finset α) : TpColor L m :=
  if h : s.card = m then tpCode (fun i => base (s.orderEmbOfFin h i)) else ∅

theorem tpCol_eq {α : Type u} [LinearOrder α] {M : Type u} [L.Structure M]
    (base : α → M) {m : ℕ} (s : Finset α) (h : s.card = m) :
    tpCol (L := L) base m s = tpCode (fun i => base (s.orderEmbOfFin h i)) := by
  simp [tpCol, h]

/-- Samples admitted by a property `P` of `L`-structures: an injective sequence in an
admitted structure, colored by types. -/
def TpSample (P : ∀ (M : Type u) [L.Structure M], Prop) (S : ColorSample (TpColor L)) :
    Prop :=
  ∃ (M : Type u) (_ : L.Structure M), P M ∧ ∃ base : S.α → M, Function.Injective base ∧
    ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m),
      S.col m s = tpCode (fun i => base (s.orderEmbOfFin h i))

/-- The increasing enumeration of an embedded finite set. -/
theorem orderEmbOfFin_map {α β : Type u} [LinearOrder α] [LinearOrder β] (e : β ↪o α)
    {m : ℕ} (s : Finset β) (h : s.card = m) (h' : (s.map e.toEmbedding).card = m) :
    (s.map e.toEmbedding).orderEmbOfFin h' = (s.orderEmbOfFin h).trans e :=
  (Finset.orderEmbOfFin_unique' h' (fun x => Finset.mem_map.mpr
    ⟨_, Finset.orderEmbOfFin_mem s h x, rfl⟩)).symm

theorem tpSample_reindex {P : ∀ (M : Type u) [L.Structure M], Prop}
    (S : ColorSample (TpColor L)) {β : Type u} [LinearOrder β] (e : β ↪o S.α)
    (hS : TpSample P S) : TpSample P (S.reindex e) := by
  obtain ⟨M, inst, hP, base, hinj, hcol⟩ := hS
  refine ⟨M, inst, hP, fun x => base (e x), hinj.comp e.injective, ?_⟩
  intro m s h
  have h' : (s.map e.toEmbedding).card = m := (Finset.card_map _).trans h
  show S.col m (s.map e.toEmbedding) = _
  rw [hcol m _ h', orderEmbOfFin_map e s h h']
  rfl

/-- Thinning closure. -/
theorem tpSample_restrict {P : ∀ (M : Type u) [L.Structure M], Prop}
    (S : ColorSample (TpColor L)) (H : Set S.α) (hS : TpSample P S) :
    TpSample P (S.restrict H) := by
  rw [ColorSample.restrict_eq_reindex]
  exact tpSample_reindex S _ hS

/-- Arbitrarily large samples from arbitrarily large admitted structures. -/
theorem tpSample_large {P : ∀ (M : Type u) [L.Structure M], Prop}
    (hlarge : ∀ κ : Cardinal.{u}, ∃ (M : Type u) (_ : L.Structure M), P M ∧ κ ≤ #M)
    (κ : Cardinal.{u}) : ∃ S, TpSample P S ∧ κ ≤ #S.α := by
  obtain ⟨M, inst, hP, hbig⟩ := hlarge κ
  let α := κ.ord.ToType
  have hα : #α = κ := Cardinal.mk_ord_toType _
  obtain ⟨emb⟩ := (le_def α M).mp (hα ▸ hbig)
  refine ⟨⟨α, fun m s => tpCol (L := L) emb m s⟩, ⟨M, inst, hP, emb, emb.injective, ?_⟩,
    le_of_eq hα.symm⟩
  intro m s h
  exact tpCol_eq emb s h

/-- Sub-tuple colors are restrictions of tuple colors in every sample. -/
theorem tpSample_compat {P : ∀ (M : Type u) [L.Structure M], Prop}
    (S : ColorSample (TpColor L)) (hS : TpSample P S) {m m' : ℕ} (f : Fin m' ↪o Fin m)
    (s : Finset S.α) (hs : s.card = m) :
    S.col m' (Finset.univ.map (f.trans (s.orderEmbOfFin hs)).toEmbedding) =
      tpRes f (S.col m s) := by
  obtain ⟨M, inst, hP, base, hinj, hcol⟩ := hS
  have hc : (Finset.univ.map (f.trans (s.orderEmbOfFin hs)).toEmbedding).card = m' := by simp
  rw [hcol m' _ hc, hcol m s hs, tpRes_tpCode]
  have : (Finset.univ.map (f.trans (s.orderEmbOfFin hs)).toEmbedding).orderEmbOfFin hc =
      f.trans (s.orderEmbOfFin hs) :=
    (Finset.orderEmbOfFin_unique' hc (fun x => Finset.mem_map.mpr
      ⟨x, Finset.mem_univ _, rfl⟩)).symm
  rw [this]
  rfl

/-- **Coherent type colors.**  For any class of `L`-structures with arbitrarily large
members, there are types at all positive arities, coherent under restriction to
sub-tuples, such that for every arity bound and size some admitted sample of at least that
size is homogeneous for them. -/
theorem tp_coherent_colors {P : ∀ (M : Type u) [L.Structure M], Prop}
    (hlarge : ∀ κ : Cardinal.{u}, ∃ (M : Type u) (_ : L.Structure M), P M ∧ κ ≤ #M) :
    ∃ c : (m : ℕ) → 0 < m → TpColor L m,
      (∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSample P) n c κ) ∧
      ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = tpRes f (c m hm) := by
  obtain ⟨c, hc⟩ := coherent_colors (P := TpSample P)
    (fun S H hS => tpSample_restrict S H hS) (tpSample_large hlarge)
  exact ⟨c, hc, fun hm' hm f =>
    coherent_colors_compat (P := TpSample P) (fun f c => tpRes f c)
      (fun S hS _ _ f s hs => tpSample_compat S hS f s hs) hc hm' hm f⟩

end Hull83
end AEC
