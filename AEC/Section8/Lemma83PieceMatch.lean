module

public import AEC.Section8.Lemma83Isolation
public import AEC.Section8.Lemma83TupleDominated
public import AEC.Section8.Lemma83SampleLike

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


section
variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 3200000 in
/-- **Marked from piece arrows into marked sample pairs (proved).** As
`infra_83_marked_of_marked_matches_card`, with the Galois-type match supplied by
`infra_83_sgt_of_piece_arrow`: for each bounded `c` it suffices to give a piece `Y_u` of `Y'` over
`X'` holding a preimage `d` of `(b, c)`, an arrow `h : Y_u → N.Y` over `toA : X' → N.X` sending the
mark part of `d` to the sample mark (along `τ`), and at least `ν` Cor 6.16 indices whose
retractions send `h(d)` into `toA[X']`. -/
theorem infra_83_marked_of_piece_arrows (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {ν : Cardinal.{u}}
    (hνC : ν ∈ infra_615_closed P) (hνT : ν ∈ infra_78_closedTail P)
    {X' Y' : P.scheme.Object ν hνC.1}
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X')
      (P.scheme.asSystem hνC.1 Y'))
    {bIdx : Type u} [Finite bIdx]
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y'))
    (hmatch : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y')),
      #cIdx < ν →
      ∃ (N : MarkedPair K oneVertexShape P.scheme Pr) (hlC : N.μ ∈ infra_615_closed P)
        (_ : N.μ ∈ infra_78_closedTail P) (_ : ν ≤ N.μ)
        (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X')
          (P.scheme.asSystem hlC.1 N.X))
        (R : ApproximateRetraction K oneVertexShape P.scheme N.hμ N.X N.Y N.incl)
        (τ : bIdx ≃ N.bIdx) (Yu : P.scheme.Object ν hνC.1)
        (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X')
          (P.scheme.asSystem hνC.1 Yu))
        (j : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 Yu)
          (P.scheme.asSystem hνC.1 Y'))
        (h : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 Yu)
          (P.scheme.asSystem hlC.1 N.Y))
        (d : bIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Yu)),
        SystemArrow.comp inclu j = incl' ∧
        SystemArrow.comp inclu h = SystemArrow.comp toA N.incl ∧
        (∀ s, j.mapOcc (d s) = seqJoint b c s) ∧
        (∀ a, h.mapOcc (d (Sum.inl a)) = N.b (τ a)) ∧
        ν ≤ #{i : R.index // ∀ s, ∃ y, toA.onVertex (d s).1 y =
          (R.retr i).onVertex (d s).1 (h.onVertex (d s).1 (d s).2)}) :
    (∃ realEq : bIdx ≃ (Pr.assign hνC.1 X').idx,
      SameGaloisType (asTuple incl' trivial b) (Pr.assign hνC.1 X') realEq (Equiv.refl _)) ∧
    AllDominated incl' trivial bIdx b := by
  refine infra_83_marked_of_marked_matches_card P Pr hνC hνT incl' trivial b
    (fun cIdx c hc => ?_)
  obtain ⟨N, hlC, hlT, hνl, toA, R, τ, Yu, inclu, j, h, d, hj, hh, hjd, hb, hcount⟩ :=
    hmatch cIdx c hc
  let cU : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 N.Y) :=
    fun k => h.mapOcc (d (Sum.inr k))
  have hx : seqJoint (fun a => N.b (τ a)) cU = fun s => h.mapOcc (d s) := by
    funext s
    rcases s with a | k
    · exact (hb a).symm
    · rfl
  have hy : seqJoint b c = fun s => j.mapOcc (d s) := by
    funext s
    exact (hjd s).symm
  have hd : #(bIdx ⊕ cIdx) < ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hνC.1)
      ((Cardinal.lt_aleph0_of_finite bIdx).trans_le (P.aleph0_le hνC.1)) hc
  refine ⟨N, hlC, hlT, hνl, toA, trivial, R, τ, cU, ?_, ?_⟩
  · rw [hx]
    exact hcount
  · rw [hx, hy]
    exact infra_83_sgt_of_piece_arrow P inclu incl' j hj toA N.incl h hh d hd
end


section
variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 3200000 in
/-- **Lemma 8.3 (P.scheme) reduced to piece arrows of the template values (proved reduction).**
For the constructed pair template, `Lemma83Conclusion` holds once, for every value on a well-order
`I` with `#I` in the closed tail and every bounded tuple `c` of `Y_I`, there are a marked sample
pair `N` at a closed level `≥ #I`, `toA : X_I → N.X`, a Cor 6.16 family `R`, a piece `Y_u` of
`Y_I` over `X_I` holding a preimage `d` of `(mk_I, c)`, and `h : Y_u → N.Y` over `toA` carrying the
mark part of `d` to `N.b ∘ τ`, with at least `#I` indices whose retractions send `h(d)` into
`toA[X_I]` (`infra_83_marked_of_piece_arrows`). -/
theorem infra_83_full_single_of_piece_arrows (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (X Y : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        P.scheme.Object #I hI)
      (incl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        SystemArrow K oneVertexShape (P.scheme.asSystem hI (X I hI))
          (P.scheme.asSystem hI (Y I hI)))
      (mk : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        Fin Pr.n → Occurrence K oneVertexShape (P.scheme.asSystem hI (Y I hI))),
      (∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
          (hI : #I ∈ infra_78_closedTail P ∩ infra_615_closed P)
          (cIdx : Type u)
          (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hI.2.1 (Y I hI.2.1))),
          #cIdx < #I →
          ∃ (N : MarkedPair K oneVertexShape P.scheme Pr) (hlC : N.μ ∈ infra_615_closed P)
            (_ : N.μ ∈ infra_78_closedTail P) (_ : #I ≤ N.μ)
            (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 (X I hI.2.1))
              (P.scheme.asSystem hlC.1 N.X))
            (R : ApproximateRetraction K oneVertexShape P.scheme N.hμ N.X N.Y N.incl)
            (τ : ULift.{u} (Fin Pr.n) ≃ N.bIdx) (Yu : P.scheme.Object #I hI.2.1)
            (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 (X I hI.2.1))
              (P.scheme.asSystem hI.2.1 Yu))
            (j : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 Yu)
              (P.scheme.asSystem hI.2.1 (Y I hI.2.1)))
            (h : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 Yu)
              (P.scheme.asSystem hlC.1 N.Y))
            (d : ULift.{u} (Fin Pr.n) ⊕ cIdx →
              Occurrence K oneVertexShape (P.scheme.asSystem hI.2.1 Yu)),
            SystemArrow.comp inclu j = incl I hI.2.1 ∧
            SystemArrow.comp inclu h = SystemArrow.comp toA N.incl ∧
            (∀ s, j.mapOcc (d s) =
              seqJoint (fun a : ULift.{u} (Fin Pr.n) => mk I hI.2.1 a.down) c s) ∧
            (∀ a, h.mapOcc (d (Sum.inl a)) = N.b (τ a)) ∧
            #I ≤ #{i : R.index // ∀ s, ∃ y, toA.onVertex (d s).1 y =
              (R.retr i).onVertex (d s).1 (h.onVertex (d s).1 (d s).2)}) →
      Lemma83Conclusion P.scheme Pr := by
  obtain ⟨F, X, Y, eX, eY, incl, mk, hincl, harr⟩ := infra_83_pair_template_clauses P Pr
  refine ⟨X, Y, incl, mk, fun hS => ?_⟩
  refine infra_83_conclusion_of_marked_values_idx P Pr F X Y eX eY incl mk hincl harr _
    (infra_83_closed_tail P) (fun I _ _ _ hI => ?_)
  obtain ⟨hR, hD⟩ := infra_83_marked_of_piece_arrows P Pr hI.2 hI.1 (incl I hI.2.1)
    (fun j : ULift.{u} (Fin Pr.n) => mk I hI.2.1 j.down) (hS I hI)
  obtain ⟨realEq, hr⟩ := hR
  exact ⟨ULift.{u} (Fin Pr.n), Equiv.refl _, realEq, hr, hD⟩
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **Tuple count from a piece-level count (proved).** If at least `ν` retractions send the whole
piece `h[Y_u]` into `toA[X']` (the form produced by `infra_83_retained_of_match_ret` with
`onX = toA`, `onY = h`), then at least `ν` send `h(d)` into `toA[X']` for any tuple `d` of `Y_u`:
the count clause of `infra_83_marked_of_piece_arrows`. -/
theorem infra_83_tuple_count_of_piece_count (P : SingleModelData K) {ν l : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hl : l ∈ P.eligible}
    {X' Yu : P.scheme.Object ν hν} {A U : P.scheme.Object l hl}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hl A))
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem hl U))
    {ι : Type u} (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem hl U)
      (P.scheme.asSystem hl A))
    {idx : Type u} (d : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν Yu))
    (hcount : ν ≤ #{i : ι // ∀ x, ∃ y, toA.onVertex PUnit.unit y =
      (r i).onVertex PUnit.unit (h.onVertex PUnit.unit x)}) :
    ν ≤ #{i : ι // ∀ s, ∃ y, toA.onVertex (d s).1 y =
      (r i).onVertex (d s).1 (h.onVertex (d s).1 (d s).2)} := by
  refine hcount.trans (Cardinal.mk_subtype_mono fun i hi s => ?_)
  obtain ⟨v, x⟩ := d s
  cases v
  exact hi x
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

/-- **The sample identification is a `τ`-isomorphism (proved).** In a sample-like structure
(`XSampleLike`: `g : N ≃ F(Jp)` preserving the `τ`-functions and relations of the reduct), `g`
is an isomorphism of `τ`-structures from the `τ`-reduct of `N` onto `F(Jp)`. -/
def infra_83_sample_tauEquiv (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] {Jp : Type u} [LinearOrder Jp] [Nonempty Jp]
    (g : N ≃ (E.obj Jp).carrier)
    (hfun : ∀ {k} (f : K.τ.Functions k) (x : Fin k → N),
      g (@Structure.funMap _ _ ((tauRed E n).reduct N) k f x) = Structure.funMap f (g ∘ x))
    (hrel : ∀ {k} (r : K.τ.Relations k) (x : Fin k → N),
      (@Structure.RelMap _ _ ((tauRed E n).reduct N) k r x ↔ Structure.RelMap r (g ∘ x))) :
    @Language.Equiv K.τ N (E.obj Jp).carrier ((tauRed E n).reduct N) _ :=
  letI := (tauRed E n).reduct N
  { toEquiv := g
    map_fun' := fun f x => hfun f x
    map_rel' := fun r x => (hrel r x).symm }

/-- **`X_H` into the sample's `X` along an order map (proved).** For a sample-like structure with
`g : N ≃ F(Jp)` and `X = g⁻¹[F(emb)[F(J)]]`, every order embedding `e : J₀ ↪o J` gives a
`τ`-embedding `F(J₀) → N` (into the `τ`-reduct) with image inside the sample's `X`: the paper's
"F of that order map embeds `X_H = F(J_H)` into `X = F(J)`". -/
theorem infra_83_sample_X_embedding (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] {J Jp J0 : Type u} [LinearOrder J] [Nonempty J]
    [LinearOrder Jp] [Nonempty Jp] [LinearOrder J0] [Nonempty J0]
    (emb : J ↪o Jp) (g : N ≃ (E.obj Jp).carrier)
    (hfun : ∀ {k} (f : K.τ.Functions k) (x : Fin k → N),
      g (@Structure.funMap _ _ ((tauRed E n).reduct N) k f x) = Structure.funMap f (g ∘ x))
    (hrel : ∀ {k} (r : K.τ.Relations k) (x : Fin k → N),
      (@Structure.RelMap _ _ ((tauRed E n).reduct N) k r x ↔ Structure.RelMap r (g ∘ x)))
    (e : J0 ↪o J) :
    ∃ φ : @Language.Embedding K.τ (E.obj J0).carrier N _ ((tauRed E n).reduct N),
      ∀ x, g (φ x) = E.map emb (E.map e x) := by
  letI := (tauRed E n).reduct N
  let G := infra_83_sample_tauEquiv E n g hfun hrel
  refine ⟨G.symm.toEmbedding.comp ((E.map emb).comp (E.map e)), fun x => ?_⟩
  show G (G.symm _) = _
  rw [Language.Equiv.apply_symm_apply]
  rfl
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

/-- **Pair square into a sample along order maps (proved).** In a sample-like structure with
`g : N ≃ F(Jp)`, order embeddings `e₀ : J₀ ↪o J` (the `X`-part) and `e : Z₀ ↪o Jp` (the `Y`-part)
with an inclusion `i₀ : J₀ ↪o Z₀` such that `e₀ ; emb = i₀ ; e` give `τ`-embeddings
`φX : F(J₀) → N`, `φY : F(Z₀) → N` with `φY ∘ F(i₀) = φX`, `φX` landing in the sample's `X`:
the square `inclu ; h = toA ; incl` of `infra_83_sgt_of_piece_arrow` at the level of carriers. -/
theorem infra_83_sample_pair_square (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] {J Jp J0 Z0 : Type u} [LinearOrder J] [Nonempty J]
    [LinearOrder Jp] [Nonempty Jp] [LinearOrder J0] [Nonempty J0] [LinearOrder Z0] [Nonempty Z0]
    (emb : J ↪o Jp) (g : N ≃ (E.obj Jp).carrier)
    (hfun : ∀ {k} (f : K.τ.Functions k) (x : Fin k → N),
      g (@Structure.funMap _ _ ((tauRed E n).reduct N) k f x) = Structure.funMap f (g ∘ x))
    (hrel : ∀ {k} (r : K.τ.Relations k) (x : Fin k → N),
      (@Structure.RelMap _ _ ((tauRed E n).reduct N) k r x ↔ Structure.RelMap r (g ∘ x)))
    (e0 : J0 ↪o J) (e : Z0 ↪o Jp) (i0 : J0 ↪o Z0) (hsq : e0.trans emb = i0.trans e) :
    ∃ (φX : @Language.Embedding K.τ (E.obj J0).carrier N _ ((tauRed E n).reduct N))
      (φY : @Language.Embedding K.τ (E.obj Z0).carrier N _ ((tauRed E n).reduct N)),
      (∀ x, g (φX x) = E.map emb (E.map e0 x)) ∧ (∀ y, g (φY y) = E.map e y) ∧
      ∀ x, φY (E.map i0 x) = φX x := by
  letI := (tauRed E n).reduct N
  let G := infra_83_sample_tauEquiv E n g hfun hrel
  refine ⟨G.symm.toEmbedding.comp ((E.map emb).comp (E.map e0)), G.symm.toEmbedding.comp (E.map e),
    fun x => ?_, fun y => ?_, fun x => ?_⟩
  · show G (G.symm _) = _
    rw [Language.Equiv.apply_symm_apply]
    rfl
  · show G (G.symm _) = _
    rw [Language.Equiv.apply_symm_apply]
  · apply G.injective
    show G (G.symm _) = G (G.symm _)
    rw [Language.Equiv.apply_symm_apply, Language.Equiv.apply_symm_apply]
    have h1 := congrArg (fun φ => φ x) (E.map_comp i0 e)
    have h2 := congrArg (fun φ => φ x) (E.map_comp e0 emb)
    simp only [Language.Embedding.comp_apply] at h1 h2
    show E.map e (E.map i0 x) = E.map emb (E.map e0 x)
    rw [← h1, ← h2, hsq]
end


/-- **Order maps for the pair square by saturation (proved).** Paper (Lemma 8.3 proof): "extend
these partial order maps to `J_H → J`, `W_H → W` by saturation". Given the `X`-part map
`e₀ : J₀ ↪o J`, an inclusion `i₀ : J₀ ↪o Z₀`, and a strictly increasing partial map `f` on
`D ⊆ Z₀` (the matched positions) that contains `i₀[J₀]` and agrees there with `emb ∘ e₀`, a
`κ`-order-saturated `Jp` with `|Z₀| < κ` admits `e : Z₀ ↪o Jp` extending `f` with
`e₀ ; emb = i₀ ; e` (the hypothesis `hsq` of `infra_83_sample_pair_square`). -/
theorem infra_83_square_extension {κ : Cardinal.{u}} {J Jp J0 Z0 : Type u} [LinearOrder J]
    [LinearOrder Jp] [LinearOrder J0] [LinearOrder Z0]
    (hsat : OrderSat83.OrderSaturated κ Jp) (hZ : #Z0 < κ)
    (emb : J ↪o Jp) (e0 : J0 ↪o J) (i0 : J0 ↪o Z0) (D : Set Z0) (f : D → Jp)
    (hf : StrictMono f) (hD : ∀ x, i0 x ∈ D) (hfa : ∀ x, f ⟨i0 x, hD x⟩ = emb (e0 x)) :
    ∃ e : Z0 ↪o Jp, (∀ d : D, e d = f d) ∧ e0.trans emb = i0.trans e := by
  obtain ⟨g, hg, hgf⟩ := OrderSat83.extend_strictMono_linear hsat hZ D f hf
  refine ⟨OrderEmbedding.ofStrictMono g hg, hgf, ?_⟩
  ext x
  show emb (e0 x) = g (i0 x)
  rw [← hfa x]
  exact (hgf ⟨i0 x, hD x⟩).symm

end AEC
