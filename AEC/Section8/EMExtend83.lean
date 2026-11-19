module

public import AEC.Section2.Presentation

/-!
# Lemma 8.3: generic Ehrenfeucht–Mostowski extension of finite pieces (first step)

Section 2 builds `emOrderPresentation` from one specific functor on finite nonempty orders:
`pieceSucc k` (the model coded by the standard color of arity `k + 1`) with the strong maps
`arityMapSucc`.  Everything downstream of `emSystem` uses only that functoriality.  For the
pair template of Lemma 8.3 the same extension is needed for the pieces coded by the coherent
pair colors.  Here the functor is abstracted (`FinPieces`) and the directed system and its
direct limit in `K` are built for any such functor; Section 2's pieces are an instance.
-/

@[expose] public section

namespace AEC
namespace EM83

universe u

open FirstOrder

variable {K : AbstractElementaryClass.{u}}

/-- A functor from the nonempty finite orders `Fin (k + 1)` (with order embeddings) into `K`
with strong embeddings. -/
structure FinPieces (K : AbstractElementaryClass.{u}) where
  obj : ℕ → Model K.τ
  mem : ∀ k, K.Mem (obj k)
  map : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) → (obj k).carrier ↪[K.τ] (obj l).carrier
  map_refl : ∀ k, map (idEmb (α := Fin (k + 1))) = Language.Embedding.refl K.τ (obj k).carrier
  map_trans : ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1)),
    map (e.trans f) = (map f).comp (map e)
  strong : ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)), K.Strong (map e)

/-- The directed system of finite-support copies of the pieces inside a nonempty order
(the generic `emSystem`). -/
noncomputable def FinPieces.system (F : FinPieces K) (I : Type u) [LinearOrder I] [Nonempty I] :
    DirectedSystem K.τ where
  ι := {s : Finset I // s.Nonempty}
  nonempty := ⟨⟨{Classical.choice ‹Nonempty I›}, Finset.singleton_nonempty _⟩⟩
  rel s t := s.1 ⊆ t.1
  refl s := Finset.Subset.refl s.1
  trans hsu hut := Finset.Subset.trans hsu hut
  directed s t :=
    ⟨⟨s.1 ∪ t.1, by
        obtain ⟨a, ha⟩ := s.2
        exact ⟨a, Finset.mem_union.mpr (Or.inl ha)⟩⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩
  obj s := F.obj s.1.card.pred
  map {s t} h := F.map (placeSucc h s.2 t.2)
  map_refl s := by
    have hp : placeSucc (Finset.Subset.refl s.1) s.2 s.2 =
        idEmb (α := Fin (s.1.card.pred + 1)) :=
      placeSucc_refl s.1 s.2
    simpa [hp] using F.map_refl s.1.card.pred
  map_trans {s t u} hij hjk := by
    have hp : placeSucc (Finset.Subset.trans hij hjk) s.2 u.2 =
        (placeSucc hij s.2 t.2).trans (placeSucc hjk t.2 u.2) :=
      placeSucc_trans hij hjk s.2 t.2 u.2
    simpa [hp] using F.map_trans (placeSucc hij s.2 t.2) (placeSucc hjk t.2 u.2)

/-- The generic EM value: a direct limit of the finite-support copies lying in `K`
(Lemma 2.1, `directLimit_in_class`). -/
theorem FinPieces.limit_exists (F : FinPieces K) (I : Type u) [LinearOrder I] [Nonempty I] :
    ∃ L : DirectLimit (F.system I), IsLimitInClass K L :=
  directLimit_in_class K (F.system I) (fun _ => F.mem _) (fun _ => F.strong _)

/-- Section 2's pieces form a `FinPieces` functor; `F.system` is then Section 2's `emSystem`. -/
noncomputable def section2Pieces (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K] :
    FinPieces K where
  obj k := pieceSucc (K := K) k
  mem k := pieceSucc_mem k
  map e := arityMapSucc (K := K) e
  map_refl k := arityMapSucc_refl k
  map_trans e f := arityMapSucc_trans e f
  strong e := arityMapSucc_strong e

theorem section2Pieces_system (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K]
    (I : Type u) [LinearOrder I] [Nonempty I] :
    (section2Pieces K).system I = emSystem (K := K) I := rfl

end EM83
end AEC
