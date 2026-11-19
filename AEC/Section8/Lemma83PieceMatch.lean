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


section
variable {K : AbstractElementaryClass.{u}}

/-- **The sample's `X`-identification is bijective (proved).** In ret-sample data (`RetSampleLike`:
`eX : F(J) → X` surjective with `F (incl (eX x)) = F(emb) x`), `eX` is also injective, since
`F(emb)` is. So `X ≃ F(J)` as sets; the order maps `F(e₀)` of `infra_83_sample_pair_square`
transport to maps into `X`. -/
theorem infra_83_eX_bijective (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {M : MarkedPair K oneVertexShape P.scheme Pr}
    {J Jp : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jp] [Nonempty Jp] (emb : J ↪o Jp)
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jp).carrier)
    (hsurj : Function.Surjective eX)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x) :
    Function.Bijective eX := by
  refine ⟨fun x y hxy => (P.E.map emb).injective ?_, hsurj⟩
  rw [← hF x, ← hF y, hxy]
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **Ret-sample data carry strong `τ`-identifications (proved).** The strengthened
`RetSampleLike` (cycle 183; verified on the real samples in `infra_83_pairMS3_coherent_colors`)
records `eX : F(J) → X` as a strong bijective `τ`-embedding and `F : Y → F(Jp)` as a strong
`τ`-embedding with `F ∘ incl ∘ eX = F(emb)`: the inputs for turning the order-map embeddings of
`infra_83_sample_pair_square` into scheme arrows into the sample pair. -/
theorem infra_83_ret_sample_tau (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {N : Type u}
    [(LS83.pairLangM3 P.E Pr.n).Structure N] (h : RetSampleLike P Pr N) :
    ∃ (M : MarkedPair K oneVertexShape P.scheme Pr) (J Jp : Type u) (_ : LinearOrder J)
      (_ : Nonempty J) (_ : LinearOrder Jp) (_ : Nonempty Jp) (emb : J ↪o Jp)
      (eX : Language.Embedding K.τ (P.E.obj J).carrier
        ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
      (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
        (P.E.obj Jp).carrier),
      Function.Bijective eX ∧ K.Strong eX ∧ K.Strong F ∧
      ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x := by
  obtain ⟨M, J, Jp, i1, i2, i3, i4, emb, -, eX, F, -, -, hsurj, -, hsX, hsF, hF, -⟩ := h
  exact ⟨M, J, Jp, i1, i2, i3, i4, emb, eX, F,
    infra_83_eX_bijective P emb eX F hsurj hF, hsX, hsF, hF⟩
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **`X_H = F(J₀)` into the sample's `X` as a strong embedding (proved).** In ret-sample data,
for an order embedding `e₀ : J₀ ↪o J` the composite `eX ∘ F(e₀) : F(J₀) → X` is a strong
`τ`-embedding whose image read in `F(Jp)` is `F(emb) ∘ F(e₀)`: the carrier map of `toA` in the
paper's "F of that order map embeds `X_H` into `X`". -/
theorem infra_83_sample_toA (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {M : MarkedPair K oneVertexShape P.scheme Pr}
    {J Jp J0 : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jp] [Nonempty Jp]
    [LinearOrder J0] [Nonempty J0] (emb : J ↪o Jp)
    (eX : Language.Embedding K.τ (P.E.obj J).carrier
      ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
      (P.E.obj Jp).carrier)
    (hsX : K.Strong eX) (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (e0 : J0 ↪o J) :
    ∃ φ : Language.Embedding K.τ (P.E.obj J0).carrier
        ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier,
      K.Strong φ ∧ ∀ x, F (M.incl.onVertex PUnit.unit (φ x)) = P.E.map emb (P.E.map e0 x) :=
  ⟨eX.comp (P.E.map e0), K.strong_trans _ _ (P.E.map_strong e0) hsX, fun x => hF _⟩
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **`toA` as a scheme arrow (proved).** If the template-side base `X'` (a scheme object at a
level `ν`) is identified with `F(J₀)` by a strong `τ`-embedding `ψ` (as `X_I ≅ F(J_I)`,
`infra_83_X_hull_eq_FJ`), then for every order embedding `e₀ : J₀ ↪o J` into the `X`-order of a
ret-sample there is a scheme arrow `toA : X' → M.X` whose values read in `F(Jp)` are
`F(emb) (F(e₀) (ψ x))`. -/
theorem infra_83_toA_arrow (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {M : MarkedPair K oneVertexShape P.scheme Pr}
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} (X' : P.scheme.Object ν hν)
    {J Jp J0 : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jp] [Nonempty Jp]
    [LinearOrder J0] [Nonempty J0] (emb : J ↪o Jp)
    (eX : Language.Embedding K.τ (P.E.obj J).carrier
      ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
      (P.E.obj Jp).carrier)
    (hsX : K.Strong eX) (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (ψ : Language.Embedding K.τ ((P.scheme.asSystem hν X').obj PUnit.unit).carrier
      (P.E.obj J0).carrier) (hψ : K.Strong ψ) (e0 : J0 ↪o J) :
    ∃ toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem M.hμ M.X),
      ∀ x, F (M.incl.onVertex PUnit.unit (toA.onVertex PUnit.unit x)) =
        P.E.map emb (P.E.map e0 (ψ x)) := by
  obtain ⟨φ, hφ, hφF⟩ := infra_83_sample_toA P emb eX F hsX hF e0
  exact ⟨⟨fun _ => φ.comp ψ, fun _ => K.strong_trans _ _ hψ hφ, fun h => h.elim⟩,
    fun x => hφF (ψ x)⟩
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **The piece arrow `h` by factoring through the sample's `F` (proved).** If the piece `Y_u`
(a scheme object) maps by a strong `τ`-embedding `gY` into `F(Jp)` with image inside the copy
`F[M.Y]` of the sample's `Y` (e.g. `gY = F(e) ∘ ψ_Y` from the pair square), then there is a scheme
arrow `h : Y_u → M.Y` with `F ∘ h = gY`; strongness of `h` is AEC coherence. -/
theorem infra_83_piece_arrow_factor (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {M : MarkedPair K oneVertexShape P.scheme Pr}
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} (Yu : P.scheme.Object ν hν)
    {Jp : Type u} [LinearOrder Jp] [Nonempty Jp]
    (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
      (P.E.obj Jp).carrier) (hsF : K.Strong F)
    (gY : Language.Embedding K.τ ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier
      (P.E.obj Jp).carrier) (hgY : K.Strong gY)
    (hr : ∀ x, gY x ∈ Set.range F) :
    ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem M.hμ M.Y),
      ∀ x, F (h.onVertex PUnit.unit x) = gY x := by
  classical
  choose h0 hh0 using hr
  let hE : Language.Embedding K.τ ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier
      ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier :=
    { toFun := h0
      inj' := fun a b hab => gY.injective (by rw [← hh0 a, ← hh0 b, hab])
      map_fun' := fun {n} f x => F.injective (by
        rw [hh0, gY.map_fun, F.map_fun]
        congr 1
        funext i
        exact (hh0 (x i)).symm)
      map_rel' := fun {n} r x => by
        rw [← F.map_rel, ← gY.map_rel]
        have : (F ∘ (h0 ∘ x)) = gY ∘ x := funext fun i => hh0 (x i)
        rw [this] }
  have hcomp : F.comp hE = gY := by
    ext x
    exact hh0 x
  have hsh : K.Strong hE := K.coherence hE gY F hgY hsF hcomp
  exact ⟨⟨fun _ => hE, fun _ => hsh, fun h => h.elim⟩, fun x => hh0 x⟩
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **The pair square from the `F(Jp)` readings (proved).** If `toA : X' → M.X`,
`inclu : X' → Y_u` and `h : Y_u → M.Y` satisfy `F (h (inclu x)) = F (incl (toA x))` for every `x`
(as produced by `infra_83_toA_arrow`, `infra_83_piece_arrow_factor` and the order square
`infra_83_sample_pair_square`), then `inclu ; h = toA ; incl` as scheme arrows (`F` injective):
the hypothesis `hh` of `infra_83_sgt_of_piece_arrow`. -/
theorem infra_83_square_of_F (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {M : MarkedPair K oneVertexShape P.scheme Pr}
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {X' Yu : P.scheme.Object ν hν}
    {Jp : Type u} [LinearOrder Jp] [Nonempty Jp]
    (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
      (P.E.obj Jp).carrier)
    (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem M.hμ M.X))
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem M.hμ M.Y))
    (hpt : ∀ x, F (h.onVertex PUnit.unit (inclu.onVertex PUnit.unit x)) =
      F (M.incl.onVertex PUnit.unit (toA.onVertex PUnit.unit x))) :
    SystemArrow.comp inclu h = SystemArrow.comp toA M.incl := by
  apply SystemArrow.ext
  intro v
  cases v
  ext x
  exact F.injective (hpt x)
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **The arrow part of one bounded-list match from `F(Jp)` readings (proved).** In ret-sample
data (`infra_83_ret_sample_tau`), let the template-side base `X'` be identified with `F(J₀)` by a
strong `ψ`, let `e₀ : J₀ ↪o J`, and let the piece `Y_u ⊇ X'` (`inclu`) map by a strong `gY` into
`F(Jp)` inside `F[M.Y]`, agreeing on `X'` with `F(emb) ∘ F(e₀) ∘ ψ`. Then there are scheme arrows
`toA : X' → M.X` and `h : Y_u → M.Y` forming the pair square, with `F ∘ h = gY`: the arrow inputs
of `infra_83_marked_of_piece_arrows`. -/
theorem infra_83_piece_match_arrows (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {M : MarkedPair K oneVertexShape P.scheme Pr}
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {X' Yu : P.scheme.Object ν hν}
    {J Jp J0 : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jp] [Nonempty Jp]
    [LinearOrder J0] [Nonempty J0] (emb : J ↪o Jp)
    (eX : Language.Embedding K.τ (P.E.obj J).carrier
      ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
      (P.E.obj Jp).carrier)
    (hsX : K.Strong eX) (hsF : K.Strong F)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (ψ : Language.Embedding K.τ ((P.scheme.asSystem hν X').obj PUnit.unit).carrier
      (P.E.obj J0).carrier) (hψ : K.Strong ψ) (e0 : J0 ↪o J)
    (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
    (gY : Language.Embedding K.τ ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier
      (P.E.obj Jp).carrier) (hgY : K.Strong gY)
    (hr : ∀ x, gY x ∈ Set.range F)
    (hX : ∀ x, gY (inclu.onVertex PUnit.unit x) = P.E.map emb (P.E.map e0 (ψ x))) :
    ∃ (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν X')
        (P.scheme.asSystem M.hμ M.X))
      (h : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu)
        (P.scheme.asSystem M.hμ M.Y)),
      SystemArrow.comp inclu h = SystemArrow.comp toA M.incl ∧
      ∀ x, F (h.onVertex PUnit.unit x) = gY x := by
  obtain ⟨toA, htoA⟩ := infra_83_toA_arrow P X' emb eX F hsX hF ψ hψ e0
  obtain ⟨h, hh⟩ := infra_83_piece_arrow_factor P Yu F hsF gY hgY hr
  refine ⟨toA, h, infra_83_square_of_F P F inclu toA h fun x => ?_, hh⟩
  rw [hh, hX, htoA]
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

set_option maxHeartbeats 1600000 in
/-- **The count clause of one bounded-list match (proved).** For a piece `X' ≤ Y_u` with scheme
arrows `toA`, `h` into a ret-sample forming the pair square, an `L₀`-embedding `mY` of `Y_u`
reading `F ∘ h` with `ret` interpreted by the evaluation `G`, and the sort intersection `hmeet`
on the piece: at least `ν = |X'|` Cor 6.16 indices send `h(d)` into `toA[X']` for every tuple `d`
of `Y_u` (`infra_83_retained_of_match_ret` + `infra_83_tuple_count_of_piece_count`). -/
theorem infra_83_piece_count (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {J Jplus : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jplus] [Nonempty Jplus]
    {M : MarkedPair K oneVertexShape P.scheme Pr}
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (hsurj : Function.Surjective eX) (emb : J ↪o Jplus)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jplus).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (hFi : Function.Injective (fun z => F (M.incl.onVertex PUnit.unit z)))
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier) (hcode : Function.Bijective code)
    (G : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier)
    (heval : ∀ i y, G (P.E.map emb (code i)) (F y) =
      F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)))
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {X' Yu : P.scheme.Object ν hν}
    (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem M.hμ M.X))
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem M.hμ M.Y))
    (hsq : SystemArrow.comp inclu h = SystemArrow.comp toA M.incl)
    {L₀ : FirstOrder.Language.{u, u}} [L₀.Structure ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier]
    [L₀.Structure (P.E.obj Jplus).carrier]
    (mY : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier ↪[L₀] (P.E.obj Jplus).carrier)
    (hmY : ∀ y, mY y = F (h.onVertex PUnit.unit y))
    (ret : L₀.Functions 2) (hret : ∀ a b, Structure.funMap ret ![a, b] = G a b)
    (hmeet : ∀ (x' : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier)
      (z : ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier),
      F (h.onVertex PUnit.unit x') = F (M.incl.onVertex PUnit.unit z) →
        ∃ y, x' = inclu.onVertex PUnit.unit y)
    {idx : Type u} (d : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν Yu)) :
    ν ≤ #{i : R.index // ∀ s, ∃ y, toA.onVertex (d s).1 y =
      (R.retr i).onVertex (d s).1 (h.onVertex (d s).1 (d s).2)} := by
  have hcomm : ∀ x, h.onVertex PUnit.unit (inclu.onVertex PUnit.unit x) =
      M.incl.onVertex PUnit.unit (toA.onVertex PUnit.unit x) := fun x =>
    congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex PUnit.unit x) hsq
  have hFX : Function.Injective
      (fun x => F (M.incl.onVertex PUnit.unit (toA.onVertex PUnit.unit x))) :=
    hFi.comp (toA.onVertex PUnit.unit).injective
  have H := infra_83_retained_of_match_ret P eX hsurj emb F hF R code hcode G heval
    (toA.onVertex PUnit.unit) (h.onVertex PUnit.unit) (inclu.onVertex PUnit.unit) hcomm
    mY hmY ret hret hmeet hFX hFi
  have hcard : #((P.scheme.asSystem hν X').obj PUnit.unit).carrier = ν := X'.card
  rw [hcard] at H
  exact infra_83_tuple_count_of_piece_count P toA h R.retr d H
end

end AEC
