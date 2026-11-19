module

public import AEC.Section8.Lemma83Isolation
public import AEC.Section8.Lemma83TupleDominated
public import AEC.Section8.Lemma83SampleLike
public import AEC.Section8.Lemma83MarkValues

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


section
variable {K : AbstractElementaryClass.{u}}

/-- **The mark clause of one bounded-list match (proved).** If the piece arrow `h` reads the
template mark positions `m k` as the sample's mark values (`F (h (m k)) = F (markY M k)`, as
matches carry the mark constants, `infra_83_hull_emb_const`), then with the position
identification `τ` of the sample mark, `h` carries the mark part to `M.b ∘ τ`: the clause
`h.mapOcc (d (inl a)) = N.b (τ a)` of `infra_83_marked_of_piece_arrows`. -/
theorem infra_83_mark_clause (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {M : MarkedPair K oneVertexShape P.scheme Pr}
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {Yu : P.scheme.Object ν hν} {Jp : Type u}
    [LinearOrder Jp] [Nonempty Jp]
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jp).carrier)
    (hFi : Function.Injective F)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem M.hμ M.Y))
    (m : Fin Pr.n → ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier)
    (hm : ∀ k, F (h.onVertex PUnit.unit (m k)) = F (markY M k)) :
    ∃ τ : ULift.{u} (Fin Pr.n) ≃ M.bIdx, ∀ a : ULift.{u} (Fin Pr.n),
      h.mapOcc ⟨PUnit.unit, m a.down⟩ = M.b (τ a) := by
  refine ⟨Equiv.ulift.trans ((Pr.arity M.hμ M.X).symm.trans M.realEq.symm), fun a => ?_⟩
  apply Sigma.ext
  · exact Subsingleton.elim _ _
  · exact heq_of_eq (hFi (hm a.down))
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

set_option maxHeartbeats 3200000 in
/-- **One bounded-list match from template-side piece data (proved assembly).** In ret-sample data
(strong bijective `eX : F(J) → X`, strong `F : Y → F(Jp)` with `F ∘ incl ∘ eX = F(emb)`, a Cor 6.16
family `R` with bijective codes and evaluation `G`), suppose the template piece `X' ≤ Y_u` comes
with: a strong `ψ : X' → F(J₀)` and `e₀ : J₀ ↪o J`; a strong `gY : Y_u → F(Jp)` inside `F[M.Y]`
agreeing on `X'` with `F(emb) ∘ F(e₀) ∘ ψ`; an `L₀`-embedding reading `gY` with `ret` read as `G`;
the sort intersection on the piece (`gY x' = F(incl z) → x' ∈ X'`); and mark positions `m` read as
the sample marks. Then there are `toA`, `h` and `τ` with the square, the mark clause and the count
clause of `infra_83_marked_of_piece_arrows` for every tuple `d` whose mark part is `m`. -/
theorem infra_83_one_match_of_piece (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {M : MarkedPair K oneVertexShape P.scheme Pr}
    {J Jp J0 : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jp] [Nonempty Jp]
    [LinearOrder J0] [Nonempty J0] (emb : J ↪o Jp)
    (eX : Language.Embedding K.τ (P.E.obj J).carrier
      ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
      (P.E.obj Jp).carrier)
    (hsurj : Function.Surjective eX) (hsX : K.Strong eX) (hsF : K.Strong F)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier) (hcode : Function.Bijective code)
    (G : (P.E.obj Jp).carrier → (P.E.obj Jp).carrier → (P.E.obj Jp).carrier)
    (heval : ∀ i y, G (P.E.map emb (code i)) (F y) =
      F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)))
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {X' Yu : P.scheme.Object ν hν}
    (ψ : Language.Embedding K.τ ((P.scheme.asSystem hν X').obj PUnit.unit).carrier
      (P.E.obj J0).carrier) (hψ : K.Strong ψ) (e0 : J0 ↪o J)
    (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
    (gY : Language.Embedding K.τ ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier
      (P.E.obj Jp).carrier) (hgY : K.Strong gY)
    (hr : ∀ x, gY x ∈ Set.range F)
    (hX : ∀ x, gY (inclu.onVertex PUnit.unit x) = P.E.map emb (P.E.map e0 (ψ x)))
    {L₀ : FirstOrder.Language.{u, u}} [L₀.Structure ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier]
    [L₀.Structure (P.E.obj Jp).carrier]
    (mY : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier ↪[L₀] (P.E.obj Jp).carrier)
    (hmY : ∀ y, mY y = gY y)
    (ret : L₀.Functions 2) (hret : ∀ a b, Structure.funMap ret ![a, b] = G a b)
    (hmeet : ∀ (x' : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier)
      (z : ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier),
      gY x' = F (M.incl.onVertex PUnit.unit z) → ∃ y, x' = inclu.onVertex PUnit.unit y)
    (m : Fin Pr.n → ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier)
    (hm : ∀ k, gY (m k) = F (markY M k)) :
    ∃ (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν X')
        (P.scheme.asSystem M.hμ M.X))
      (h : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu)
        (P.scheme.asSystem M.hμ M.Y))
      (τ : ULift.{u} (Fin Pr.n) ≃ M.bIdx),
      SystemArrow.comp inclu h = SystemArrow.comp toA M.incl ∧
      (∀ a : ULift.{u} (Fin Pr.n), h.mapOcc ⟨PUnit.unit, m a.down⟩ = M.b (τ a)) ∧
      ∀ {idx : Type u} (d : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν Yu)),
        ν ≤ #{i : R.index // ∀ s, ∃ y, toA.onVertex (d s).1 y =
          (R.retr i).onVertex (d s).1 (h.onVertex (d s).1 (d s).2)} := by
  obtain ⟨toA, h, hsq, hh⟩ :=
    infra_83_piece_match_arrows P emb eX F hsX hsF hF ψ hψ e0 inclu gY hgY hr hX
  obtain ⟨τ, hτ⟩ := infra_83_mark_clause P F F.injective h m (fun k => by rw [hh, hm])
  have hFi : Function.Injective (fun z => F (M.incl.onVertex PUnit.unit z)) :=
    F.injective.comp (M.incl.onVertex PUnit.unit).injective
  refine ⟨toA, h, τ, hsq, hτ, fun d => ?_⟩
  exact infra_83_piece_count P eX hsurj emb F hF hFi R code hcode G heval inclu toA h hsq mY
    (fun y => by rw [hmY, hh]) ret hret (fun x' z hxz => hmeet x' z (by rw [← hh]; exact hxz)) d
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

set_option maxHeartbeats 3200000 in
/-- **One bounded-list match into an admitted ret-sample (proved assembly).** Every ret-admitted
sample `N` (`RetSampleLike`, verified on the real samples) supplies a marked pair `M` with
`ℵ₀ ≤ M.μ`, orders `J ↪o Jp`, the strong identifications `eX`, `F`, a Cor 6.16 family `R`, and the
`ret` evaluation `G a b = g (ret (g⁻¹ a) (g⁻¹ b))` read in `F(Jp)`, such that any template-side
piece data over it (as in `infra_83_one_match_of_piece`, with `ret` of the template read as `G`)
yield `toA`, `h`, `τ` with the square, mark and count clauses. -/
theorem infra_83_one_match_of_retSample (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {N : Type u}
    [(LS83.pairLangM3 P.E Pr.n).Structure N] (hN : RetSampleLike P Pr N) :
    ∃ (M : MarkedPair K oneVertexShape P.scheme Pr) (J Jp : Type u) (_ : LinearOrder J)
      (_ : Nonempty J) (_ : LinearOrder Jp) (_ : Nonempty Jp) (emb : J ↪o Jp)
      (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
        (P.E.obj Jp).carrier)
      (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
      (G : (P.E.obj Jp).carrier → (P.E.obj Jp).carrier → (P.E.obj Jp).carrier),
      ℵ₀ ≤ M.μ ∧
      ∀ {J0 : Type u} [LinearOrder J0] [Nonempty J0]
        {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {X' Yu : P.scheme.Object ν hν}
        (ψ : Language.Embedding K.τ ((P.scheme.asSystem hν X').obj PUnit.unit).carrier
          (P.E.obj J0).carrier) (_ : K.Strong ψ) (e0 : J0 ↪o J)
        (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
        (gY : Language.Embedding K.τ ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier
          (P.E.obj Jp).carrier) (_ : K.Strong gY)
        (_ : ∀ x, gY x ∈ Set.range F)
        (_ : ∀ x, gY (inclu.onVertex PUnit.unit x) = P.E.map emb (P.E.map e0 (ψ x)))
        {L₀ : FirstOrder.Language.{u, u}}
        [L₀.Structure ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier]
        [L₀.Structure (P.E.obj Jp).carrier]
        (mY : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier ↪[L₀] (P.E.obj Jp).carrier)
        (_ : ∀ y, mY y = gY y)
        (ret : L₀.Functions 2) (_ : ∀ a b, Structure.funMap ret ![a, b] = G a b)
        (_ : ∀ (x' : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier)
          (z : ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier),
          gY x' = F (M.incl.onVertex PUnit.unit z) → ∃ y, x' = inclu.onVertex PUnit.unit y)
        (m : Fin Pr.n → ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier)
        (_ : ∀ k, gY (m k) = F (markY M k)),
        ∃ (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν X')
            (P.scheme.asSystem M.hμ M.X))
          (h : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu)
            (P.scheme.asSystem M.hμ M.Y))
          (τ : ULift.{u} (Fin Pr.n) ≃ M.bIdx),
          SystemArrow.comp inclu h = SystemArrow.comp toA M.incl ∧
          (∀ a : ULift.{u} (Fin Pr.n), h.mapOcc ⟨PUnit.unit, m a.down⟩ = M.b (τ a)) ∧
          ∀ {idx : Type u} (d : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν Yu)),
            ν ≤ #{i : R.index // ∀ s, ∃ y, toA.onVertex (d s).1 y =
              (R.retr i).onVertex (d s).1 (h.onVertex (d s).1 (d s).2)} := by
  obtain ⟨M, J, Jp, i1, i2, i3, i4, emb, g, eX, F, R, code, hsurj, -, hsX, hsF, hF, hcode, hμ,
    -, -, -, hev⟩ := hN
  refine ⟨M, J, Jp, i1, i2, i3, i4, emb, F, R,
    fun a b => g (Structure.funMap (retM3 P.E Pr.n) ![g.symm a, g.symm b]), hμ, ?_⟩
  intro J0 _ _ ν hν X' Yu ψ hψ e0 inclu gY hgY hr hX L₀ _ _ mY hmY ret hret hmeet m hm
  exact infra_83_one_match_of_piece P emb eX F hsurj hsX hsF hF R code hcode _ hev ψ hψ e0
    inclu gY hgY hr hX mY hmY ret hret hmeet m hm
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

set_option maxHeartbeats 6400000 in
/-- **Marked from template-side piece data (proved reduction).** As
`infra_83_marked_of_piece_arrows` (with `bIdx = Fin n`), the per-`c` input now being template-side
piece data into ret-sample data (`infra_83_one_match_of_piece`): a marked pair `N` at a closed level
`≥ ν` with strong `eX`, `F`, a Cor 6.16 family with bijective codes and evaluation `G`; a piece
`X' ≤ Y_u ≤ Y'` holding a preimage `d` of `(b, c)` whose mark part is at positions `m`; a strong
`ψ : X' → F(J₀)`, `e₀ : J₀ ↪o J`; a strong `gY : Y_u → F(Jp)` inside `F[N.Y]` agreeing on `X'`; an
`L₀`-reading of `gY` with `ret` read as `G`; the sort intersection; and `gY ∘ m = F ∘ markY`. -/
theorem infra_83_marked_of_piece_data (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {ν : Cardinal.{u}}
    (hνC : ν ∈ infra_615_closed P) (hνT : ν ∈ infra_78_closedTail P)
    {X' Y' : P.scheme.Object ν hνC.1}
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X')
      (P.scheme.asSystem hνC.1 Y'))
    (b : ULift.{u} (Fin Pr.n) → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y'))
    (hmatch : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y')),
      #cIdx < ν →
      ∃ (N : MarkedPair K oneVertexShape P.scheme Pr) (hlC : N.μ ∈ infra_615_closed P)
        (_ : N.μ ∈ infra_78_closedTail P) (_ : ν ≤ N.μ)
        (J Jp J0 : Type u) (_ : LinearOrder J) (_ : Nonempty J) (_ : LinearOrder Jp)
        (_ : Nonempty Jp) (_ : LinearOrder J0) (_ : Nonempty J0) (emb : J ↪o Jp)
        (eX : Language.Embedding K.τ (P.E.obj J).carrier
          ((P.scheme.asSystem N.hμ N.X).obj PUnit.unit).carrier)
        (F : Language.Embedding K.τ ((P.scheme.asSystem N.hμ N.Y).obj PUnit.unit).carrier
          (P.E.obj Jp).carrier)
        (R : ApproximateRetraction K oneVertexShape P.scheme N.hμ N.X N.Y N.incl)
        (code : R.index → (P.E.obj J).carrier)
        (G : (P.E.obj Jp).carrier → (P.E.obj Jp).carrier → (P.E.obj Jp).carrier)
        (Yu : P.scheme.Object ν hνC.1)
        (ψ : Language.Embedding K.τ ((P.scheme.asSystem hνC.1 X').obj PUnit.unit).carrier
          (P.E.obj J0).carrier) (e0 : J0 ↪o J)
        (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X')
          (P.scheme.asSystem hνC.1 Yu))
        (j : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 Yu)
          (P.scheme.asSystem hνC.1 Y'))
        (gY : Language.Embedding K.τ ((P.scheme.asSystem hνC.1 Yu).obj PUnit.unit).carrier
          (P.E.obj Jp).carrier)
        (L₀ : FirstOrder.Language.{u, u})
        (_ : L₀.Structure ((P.scheme.asSystem hνC.1 Yu).obj PUnit.unit).carrier)
        (_ : L₀.Structure (P.E.obj Jp).carrier)
        (mY : ((P.scheme.asSystem hνC.1 Yu).obj PUnit.unit).carrier ↪[L₀] (P.E.obj Jp).carrier)
        (ret : L₀.Functions 2)
        (m : Fin Pr.n → ((P.scheme.asSystem hνC.1 Yu).obj PUnit.unit).carrier)
        (d : ULift.{u} (Fin Pr.n) ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Yu)),
        Function.Surjective eX ∧ K.Strong eX ∧ K.Strong F ∧
        (∀ x, F (N.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x) ∧
        Function.Bijective code ∧
        (∀ i y, G (P.E.map emb (code i)) (F y) =
          F (N.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y))) ∧
        K.Strong ψ ∧ K.Strong gY ∧ (∀ x, gY x ∈ Set.range F) ∧
        (∀ x, gY (inclu.onVertex PUnit.unit x) = P.E.map emb (P.E.map e0 (ψ x))) ∧
        (∀ y, mY y = gY y) ∧ (∀ a b, Structure.funMap ret ![a, b] = G a b) ∧
        (∀ (x' : ((P.scheme.asSystem hνC.1 Yu).obj PUnit.unit).carrier)
          (z : ((P.scheme.asSystem N.hμ N.X).obj PUnit.unit).carrier),
          gY x' = F (N.incl.onVertex PUnit.unit z) → ∃ y, x' = inclu.onVertex PUnit.unit y) ∧
        (∀ k, gY (m k) = F (markY N k)) ∧
        SystemArrow.comp inclu j = incl' ∧
        (∀ s, j.mapOcc (d s) = seqJoint b c s) ∧
        (∀ a, d (Sum.inl a) = ⟨PUnit.unit, m a.down⟩)) :
    (∃ realEq : ULift.{u} (Fin Pr.n) ≃ (Pr.assign hνC.1 X').idx,
      SameGaloisType (asTuple incl' trivial b) (Pr.assign hνC.1 X') realEq (Equiv.refl _)) ∧
    AllDominated incl' trivial (ULift.{u} (Fin Pr.n)) b := by
  refine infra_83_marked_of_piece_arrows P Pr hνC hνT incl' b (fun cIdx c hc => ?_)
  obtain ⟨N, hlC, hlT, hνl, J, Jp, J0, i1, i2, i3, i4, i5, i6, emb, eX, F, R, code, G, Yu, ψ, e0,
    inclu, j, gY, L₀, s1, s2, mY, ret, m, d, hsurj, hsX, hsF, hF, hcode, hev, hψ, hgY, hr, hX,
    hmY, hret, hmeet, hm, hj, hjd, hdm⟩ := hmatch cIdx c hc
  obtain ⟨toA, h, τ, hsq, hτ, hcount⟩ := infra_83_one_match_of_piece P emb eX F hsurj hsX hsF hF
    R code hcode G hev ψ hψ e0 inclu gY hgY hr hX mY hmY ret hret hmeet m hm
  refine ⟨N, hlC, hlT, hνl, toA, R, τ, Yu, inclu, j, h, d, hj, hsq, hjd, fun a => ?_, hcount d⟩
  rw [hdm]
  exact hτ a
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

set_option maxHeartbeats 6400000 in
/-- **Lemma 8.3 (P.scheme) reduced to template-side piece data (proved reduction).** As
`infra_83_full_single_of_piece_arrows`, with the per-`(I, c)` input being the template-side piece
data of `infra_83_marked_of_piece_data` (piece `X_I ≤ Y_u ≤ Y_I` holding a preimage of
`(mk_I, c)`, strong `ψ : X_I → F(J₀)` and `gY : Y_u → F(Jp)` into ret-sample data, the `L₀`-reading
with `ret`, the sort intersection, and the mark reading). -/
theorem infra_83_full_single_of_piece_data (P : SingleModelData K)
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
        (J Jp J0 : Type u) (_ : LinearOrder J) (_ : Nonempty J) (_ : LinearOrder Jp)
        (_ : Nonempty Jp) (_ : LinearOrder J0) (_ : Nonempty J0) (emb : J ↪o Jp)
        (eX : Language.Embedding K.τ (P.E.obj J).carrier
          ((P.scheme.asSystem N.hμ N.X).obj PUnit.unit).carrier)
        (F : Language.Embedding K.τ ((P.scheme.asSystem N.hμ N.Y).obj PUnit.unit).carrier
          (P.E.obj Jp).carrier)
        (R : ApproximateRetraction K oneVertexShape P.scheme N.hμ N.X N.Y N.incl)
        (code : R.index → (P.E.obj J).carrier)
        (G : (P.E.obj Jp).carrier → (P.E.obj Jp).carrier → (P.E.obj Jp).carrier)
        (Yu : P.scheme.Object #I hI.2.1)
        (ψ : Language.Embedding K.τ ((P.scheme.asSystem hI.2.1 (X I hI.2.1)).obj PUnit.unit).carrier
          (P.E.obj J0).carrier) (e0 : J0 ↪o J)
        (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 (X I hI.2.1))
          (P.scheme.asSystem hI.2.1 Yu))
        (j : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 Yu)
          (P.scheme.asSystem hI.2.1 (Y I hI.2.1)))
        (gY : Language.Embedding K.τ ((P.scheme.asSystem hI.2.1 Yu).obj PUnit.unit).carrier
          (P.E.obj Jp).carrier)
        (L₀ : FirstOrder.Language.{u, u})
        (_ : L₀.Structure ((P.scheme.asSystem hI.2.1 Yu).obj PUnit.unit).carrier)
        (_ : L₀.Structure (P.E.obj Jp).carrier)
        (mY : ((P.scheme.asSystem hI.2.1 Yu).obj PUnit.unit).carrier ↪[L₀] (P.E.obj Jp).carrier)
        (ret : L₀.Functions 2)
        (m : Fin Pr.n → ((P.scheme.asSystem hI.2.1 Yu).obj PUnit.unit).carrier)
        (d : ULift.{u} (Fin Pr.n) ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hI.2.1 Yu)),
        Function.Surjective eX ∧ K.Strong eX ∧ K.Strong F ∧
        (∀ x, F (N.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x) ∧
        Function.Bijective code ∧
        (∀ i y, G (P.E.map emb (code i)) (F y) =
          F (N.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y))) ∧
        K.Strong ψ ∧ K.Strong gY ∧ (∀ x, gY x ∈ Set.range F) ∧
        (∀ x, gY (inclu.onVertex PUnit.unit x) = P.E.map emb (P.E.map e0 (ψ x))) ∧
        (∀ y, mY y = gY y) ∧ (∀ a b, Structure.funMap ret ![a, b] = G a b) ∧
        (∀ (x' : ((P.scheme.asSystem hI.2.1 Yu).obj PUnit.unit).carrier)
          (z : ((P.scheme.asSystem N.hμ N.X).obj PUnit.unit).carrier),
          gY x' = F (N.incl.onVertex PUnit.unit z) → ∃ y, x' = inclu.onVertex PUnit.unit y) ∧
        (∀ k, gY (m k) = F (markY N k)) ∧
        SystemArrow.comp inclu j = incl I hI.2.1 ∧
        (∀ s, j.mapOcc (d s) = seqJoint (fun a : ULift.{u} (Fin Pr.n) => mk I hI.2.1 a.down) c s) ∧
        (∀ a, d (Sum.inl a) = ⟨PUnit.unit, m a.down⟩)) →
      Lemma83Conclusion P.scheme Pr := by
  obtain ⟨X, Y, incl, mk, H⟩ := infra_83_full_single_of_piece_arrows P Pr
  refine ⟨X, Y, incl, mk, fun hS => H fun I _ _ _ hI cIdx c hc => ?_⟩
  obtain ⟨N, hlC, hlT, hνl, J, Jp, J0, i1, i2, i3, i4, i5, i6, emb, eX, F, R, code, G, Yu, ψ, e0,
    inclu, j, gY, L₀, s1, s2, mY, ret, m, d, hsurj, hsX, hsF, hF, hcode, hev, hψ, hgY, hr, hX,
    hmY, hret, hmeet, hm, hj, hjd, hdm⟩ := hS I hI cIdx c hc
  obtain ⟨toA, h, τ, hsq, hτ, hcount⟩ := infra_83_one_match_of_piece P emb eX F hsurj hsX hsF hF
    R code hcode G hev ψ hψ e0 inclu gY hgY hr hX mY hmY ret hret hmeet m hm
  refine ⟨N, hlC, hlT, hνl, toA, R, τ, Yu, inclu, j, h, d, hj, hsq, hjd, fun a => ?_, ?_⟩
  · rw [hdm]
    exact hτ a
  · exact hcount d
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

/-- **Sort intersection on the piece from the `X`-sort reading (proved).** Paper (Lemma 8.3:
"`X_H` is the `X`-sort part of the hull"): if the image of the piece `gY[Y_u]` meets the `X`-copy
`F(emb)[F(J)]` only inside `gY[X']`, then the sort intersection clause of
`infra_83_marked_of_piece_data` holds: `gY x' = F(incl z)` forces `x' ∈ X'` (`gY` injective; every
`F(incl z)` lies in the `X`-copy since `eX` is onto). -/
theorem infra_83_piece_meet (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {M : MarkedPair K oneVertexShape P.scheme Pr}
    {J Jp : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jp] [Nonempty Jp] (emb : J ↪o Jp)
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (hsurj : Function.Surjective eX)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jp).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {X' Yu : P.scheme.Object ν hν}
    (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
    (gY : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier → (P.E.obj Jp).carrier)
    (hgi : Function.Injective gY)
    (hXH : ∀ x', gY x' ∈ Set.range (P.E.map emb) → ∃ y, gY x' = gY (inclu.onVertex PUnit.unit y)) :
    ∀ (x' : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier)
      (z : ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier),
      gY x' = F (M.incl.onVertex PUnit.unit z) → ∃ y, x' = inclu.onVertex PUnit.unit y := by
  intro x' z hxz
  obtain ⟨v, rfl⟩ := hsurj z
  obtain ⟨y, hy⟩ := hXH x' ⟨v, by rw [hxz, hF]⟩
  exact ⟨y, hgi hy⟩
end


section
open FirstOrder.Language

/-- **The `L₀`-reading of a piece by transport along the sample identification (proved).** If a
piece `A` embeds into a sample `N` in the pair language (`mN : A ↪[L] N`, e.g. from the hull
matches `infra_83_piece_matches_bounded_along`) and `g : N ≃ F(Jp)` is the sample's identification,
then `F(Jp)` carries the induced `L`-structure, `g ∘ mN` is an `L`-embedding into it, and a binary
symbol `r` is read there as `g (r (g⁻¹ a) (g⁻¹ b))`: the `mY`/`ret` clauses of
`infra_83_marked_of_piece_data`, with `G` the evaluation of `infra_83_one_match_of_retSample`. -/
theorem infra_83_L0_reading_transport {L : FirstOrder.Language.{u, u}} {A N B : Type u}
    [L.Structure A] [L.Structure N] (g : N ≃ B) (mN : A ↪[L] N) (r : L.Functions 2) :
    ∃ (_ : L.Structure B) (mY : A ↪[L] B), (∀ y, mY y = g (mN y)) ∧
      ∀ a b, Structure.funMap r ![a, b] = g (Structure.funMap r ![g.symm a, g.symm b]) := by
  letI : L.Structure B := g.inducedStructure
  refine ⟨g.inducedStructure, (g.inducedStructureEquiv.toEmbedding).comp mN, fun y => rfl,
    fun a b => ?_⟩
  show g (Structure.funMap r (g.symm ∘ ![a, b])) = _
  congr 2
  funext i
  fin_cases i <;> rfl
end

end AEC
