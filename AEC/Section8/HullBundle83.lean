module

public import AEC.Section8.HullReduct83

/-!
# Lemma 8.3: finite pieces from bundled samples

The bundled version of `tpFinPieces`: witnesses of the coherent bundled types
(`tpB_coherent_colors`), their term hulls, and the hull maps along `Prod.map e id` form a
`FinPieces K` when the admitted class has vertex LS witnesses.
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {K : AbstractElementaryClass.{u}} {L : Language.{u, u}}

/-- A realization of a bundled type by bundles with injective sort sequences. -/
structure TpWitB (P : ∀ (M : Type u) [L.Structure M], Prop) {r m : ℕ} (c : TpColorB L r m) where
  M : Type u
  str : L.Structure M
  mem : @P M str
  v : Fin m × Fin r → M
  inj : ∀ i, Function.Injective fun a => v (a, i)
  tp : tpCode v = c

attribute [instance] TpWitB.str

section Pieces

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
  {c : (m : ℕ) → 0 < m → TpColorB L r m}

theorem tpWitB_nonempty (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
    {m : ℕ} (hm : 0 < m) : Nonempty (TpWitB P (c m hm)) := by
  obtain ⟨S, ⟨M, inst, hP, base, hinj, hcol⟩, hκ, hhom⟩ := hc m (m : Cardinal.{u})
  obtain ⟨s, hs⟩ : ∃ s : Finset S.α, s.card = m := by
    obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hκ
    have hfin : t.Finite :=
      Cardinal.lt_aleph0_iff_set_finite.mp (by rw [ht]; exact Cardinal.natCast_lt_aleph0)
    refine ⟨hfin.toFinset, ?_⟩
    have h1 : #(↥(hfin.toFinset : Set S.α)) = (hfin.toFinset.card : Cardinal) :=
      Cardinal.mk_coe_finset
    rw [Set.Finite.coe_toFinset, ht] at h1
    exact_mod_cast h1.symm
  refine ⟨⟨M, inst, hP, bundleOf base s hs, fun i => (hinj i).comp (s.orderEmbOfFin hs).injective,
    ?_⟩⟩
  rw [← hcol m s hs]
  exact hhom m hm le_rfl s hs

/-- The chosen bundled witness at arity `k + 1`. -/
noncomputable def witB (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
    (k : ℕ) : TpWitB P (c (k + 1) (Nat.succ_pos k)) :=
  Classical.choice (tpWitB_nonempty hc (Nat.succ_pos k))

variable (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpResB r f (c m hm))

include hcoh in
theorem tpPieceB_tp {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) :
    tpCode (L := L) (witB hc k).v = tpCode ((witB hc l).v ∘ Prod.map e id) := by
  calc tpCode (L := L) (witB hc k).v = c (k + 1) (Nat.succ_pos k) := (witB hc k).tp
    _ = tpResB r e (c (l + 1) (Nat.succ_pos l)) := hcoh (Nat.succ_pos k) (Nat.succ_pos l) e
    _ = tpResB r e (tpCode (L := L) (witB hc l).v) := by rw [(witB hc l).tp]
    _ = tpCode ((witB hc l).v ∘ Prod.map e id) := tpResB_tpCode e _

variable (φ : K.τ →ᴸ L)

include hcoh in
/-- **The finite pieces of `K` from bundled samples.** -/
noncomputable def tpFinPiecesB (hP : HullStrong φ P) : EM83.FinPieces K where
  obj k := red φ (Hull (L := L) (witB hc k).v)
  mem k := K.strong_mem_dom _ (hP _ (witB hc k).mem (witB hc k).v)
  map e := redEmb φ (hullMapEmb (Prod.map e id) (tpPieceB_tp hc hcoh e))
  map_refl k := by
    ext x
    exact hullMap_id _ (tpPieceB_tp hc hcoh (k := k) (l := k) idEmb) x
  map_trans e f := by
    ext x
    exact (hullMap_comp (Prod.map e id) (Prod.map f id) (tpPieceB_tp hc hcoh e)
      (tpPieceB_tp hc hcoh f) (tpPieceB_tp hc hcoh (e.trans f)) x).symm
  strong e := hullMap_strong hP (witB hc _).mem (witB hc _).mem _ (tpPieceB_tp hc hcoh e)

/-- **Template pieces from bundled samples exist.** -/
theorem exists_tpFinPiecesB (hP : HullStrong φ P)
    (hlarge : ∀ κ : Cardinal.{u}, ∃ (α : Type u) (_ : LinearOrder α) (M : Type u)
      (_ : L.Structure M), P M ∧ κ ≤ #α ∧
      ∃ base : α → Fin r → M, ∀ i, Function.Injective fun a => base a i) :
    ∃ (c : (m : ℕ) → 0 < m → TpColorB L r m) (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Joint (TpSampleB P r) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = tpResB r f (c m hm)),
      ∀ k, (tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP).obj k = red φ (Hull (L := L) (witB hc k).v) := by
  obtain ⟨c, hc, hcoh⟩ := tpB_coherent_colors hlarge
  exact ⟨c, hc, hcoh, fun k => rfl⟩

end Pieces

end Hull83
end AEC
