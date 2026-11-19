module

public import AEC.Section8.Lemma83Isolation
public import AEC.Section8.Lemma83TupleDominated

@[expose] public section

/-!
# Lemma 8.3: matching bounded-width template pieces into a bounded-arity homogeneous sample

Paper (proof of Lemma 8.3, "Bounded horizontal arity"): the sample need only be homogeneous at the
bounded arities used; the positions of the tested list are matched by an order map into the
sample order. Here the order map `e : D ↪o S.α` is arbitrary (e.g. obtained by order saturation,
`OrderSat83.extend_orderEmbedding_linear`) and homogeneity is assumed only through arity `n`.
-/

universe u

open Cardinal FirstOrder

namespace AEC

/-- **Bundle types along an order map at bounded arity (proved).** For a sample homogeneous
through arity `n` and any order embedding `e : D ↪o S.α`, every enumeration of at most `n` moved
bundles `base ∘ e` has the template color. -/
theorem infra_83_sample_tp_orderMap_bounded {L : FirstOrder.Language.{u, u}} {r : ℕ}
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    {S : Hull83.ColorSample (Hull83.TpColorB L r)} {M : Type u} [L.Structure M]
    (base : S.α → Fin r → M)
    (hcol : ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m),
      S.col m s = Hull83.tpCode (Hull83.bundleOf base s h))
    {n : ℕ} (hhom : Hull83.Homog S n c) {D : Type u} [LinearOrder D] (e : D ↪o S.α) :
    ∀ (k : ℕ) (s : Finset D) (h : s.card = k + 1), k + 1 ≤ n →
      Hull83.tpCode (L := L) (Hull83.bundleOf (fun i => base (e i)) s h) =
        c (k + 1) (Nat.succ_pos k) := by
  intro k s h hkn
  have h' : (s.map e.toEmbedding).card = k + 1 := (Finset.card_map _).trans h
  have hb : Hull83.bundleOf (fun i => base (e i)) s h =
      Hull83.bundleOf base (s.map e.toEmbedding) h' :=
    funext fun p => infra_83_bundleOf_orderMap base e s h h' p
  rw [hb, ← hcol]
  exact hhom (k + 1) (Nat.succ_pos k) hkn _ h'

/-- **Compatible matches of bounded-width pieces along an order map (proved).** For a sample
homogeneous through arity `n` and any order embedding `e : D ↪o S.α`, the template pieces on the
supports `s ⊆ D` with `|s| ≤ n` embed into the sample structure, generators going to the moved
bundles, compatibly along `s ⊆ t`. -/
theorem infra_83_piece_matches_bounded_along {L : FirstOrder.Language.{u, u}}
    {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    {S : Hull83.ColorSample (Hull83.TpColorB L r)} {M : Type u} [L.Structure M]
    (base : S.α → Fin r → M)
    (hcol : ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m),
      S.col m s = Hull83.tpCode (Hull83.bundleOf base s h))
    {n : ℕ} (hhom : Hull83.Homog S n c) {D : Type u} [LinearOrder D] (e : D ↪o S.α) :
    ∃ m : ∀ s : {s : Finset D // s.Nonempty ∧ s.card ≤ n},
        Hull83.Hull (L := L) (Hull83.witB hc s.1.card.pred).v ↪[L] M,
      (∀ s p, m s (Quotient.mk _ (FirstOrder.Language.Term.var p)) =
        Hull83.bundleOf (fun i => base (e i)) s.1
          (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2.1)).symm p) ∧
      ∀ {s t : {s : Finset D // s.Nonempty ∧ s.card ≤ n}} (h : s.1 ⊆ t.1),
        (m t).comp (Hull83.hullMapEmb (Prod.map (placeSucc h s.2.1 t.2.1) id)
          (Hull83.tpPieceB_tp hc hcoh (placeSucc h s.2.1 t.2.1))) = m s := by
  have htp := infra_83_sample_tp_orderMap_bounded base hcol hhom e
  have key : ∀ s : {s : Finset D // s.Nonempty ∧ s.card ≤ n}, ∃ f :
      Hull83.Hull (L := L) (Hull83.witB hc s.1.card.pred).v ↪[L] M, ∀ p,
        f (Quotient.mk _ (FirstOrder.Language.Term.var p)) =
          Hull83.bundleOf (fun i => base (e i)) s.1
            (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2.1)).symm p := by
    intro s
    have hs := (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2.1)).symm
    have h' : Hull83.tpCode (L := L) (Hull83.witB hc s.1.card.pred).v =
        Hull83.tpCode (Hull83.bundleOf (fun i => base (e i)) s.1 hs ∘ id) :=
      (Hull83.witB hc s.1.card.pred).tp.trans
        (htp _ s.1 hs ((Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2.1)).le.trans s.2.2)).symm
    exact ⟨(Hull83.hullEmb (Hull83.bundleOf (fun i => base (e i)) s.1 hs)).comp
      (Hull83.hullMapEmb id h'), fun p => rfl⟩
  choose m hm using key
  refine ⟨m, hm, fun {s t} h => ?_⟩
  exact infra_83_hull_match_compat _ _ (m s) (m t) _ _ (hm s) (hm t)
    (fun p => infra_83_bundleOf_placeSucc (fun i => base (e i)) h s.2.1 t.2.1 _ _ p)


section
variable {K : AbstractElementaryClass.{u}}

/-- **Galois-type match from an arrow of a piece (proved).** Paper (Lemma 8.3 proof): "F of that
order map embeds `X_H` into `X`, identifying `u` with `u*`". If a sub-object `Y_u` of the value
`Y_I` over `X_I` (`inclu ; j = inclI`) contains the tested tuple `d` and maps by `h` into the
sample's `U` over `toA` (`inclu ; h = toA ; incl`), then `tp(j(d)/X_I)` in `Y_I` equals the
restriction along `toA` of `tp(h(d)/A)`: the `SameGaloisType` input of
`infra_83_marked_of_marked_matches` needs only an arrow of the piece `Y_u`, not of `Y_I`. -/
theorem infra_83_sgt_of_piece_arrow (P : SingleModelData K) {ν l : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hl : l ∈ P.eligible}
    {X Yu YI : P.scheme.Object ν hν} {A U : P.scheme.Object l hl}
    (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hν Yu))
    (inclI : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hν YI))
    (j : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem hν YI))
    (hj : SystemArrow.comp inclu j = inclI)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hl A))
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hl A) (P.scheme.asSystem hl U))
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem hl U))
    (hh : SystemArrow.comp inclu h = SystemArrow.comp toA incl)
    {idx : Type u} (d : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν Yu))
    (hd : #idx < ν) :
    SameGaloisType (asTuple inclI trivial (fun k => j.mapOcc (d k)))
      ((asTuple incl trivial (fun k => h.mapOcc (d k))).restrict toA trivial)
      (Equiv.refl _) (Equiv.refl _) := by
  have h12 : SameGaloisType (asTuple inclu trivial d)
      ((asTuple incl trivial (fun k => h.mapOcc (d k))).restrict toA trivial)
      (Equiv.refl _) (Equiv.refl _) :=
    ⟨l, hl, U, h, SystemArrow.refl _, trivial, trivial,
      fun v => congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex v) hh,
      fun k => rfl⟩
  have h23 : SameGaloisType (asTuple inclu trivial d) (asTuple inclI trivial (fun k => j.mapOcc (d k)))
      (Equiv.refl _) (Equiv.refl _) :=
    ⟨ν, hν, YI, j, SystemArrow.refl _, trivial, trivial,
      fun v => congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex v) hj,
      fun k => rfl⟩
  have hσ : ℵ₀ ≤ max ℵ₀ #idx := le_max_left _ _
  have hσν : max ℵ₀ #idx < ν := max_lt (P.aleph0_lt hν) hd
  have T := infra_612_galois_trans_last_base h12.symm h23 (max ℵ₀ #idx) hσ hσν
    (le_max_right _ _) rfl
  exact T.symm
end

end AEC
