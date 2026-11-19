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
    -, -, -, hev, -⟩ := hN
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


section
open FirstOrder.Language

/-- **The mark reading of a piece from mark constants (proved).** Paper ("matches carry the mark
constants", `infra_83_hull_emb_const`): if the template mark positions are the interpretations of
constants `cst k` in the piece `A`, the piece embeds into the sample `N` by an `L`-embedding `mN`,
the sample reads `cst k` (through `g`) as `F(markY M k)`, and `gY = g ∘ mN`, then
`gY (m k) = F(markY M k)`: the mark clause of `infra_83_marked_of_piece_data`. -/
theorem infra_83_piece_mark_reading {L : FirstOrder.Language.{u, u}} {A N B : Type u}
    [L.Structure A] [L.Structure N] {n : ℕ} (cst : Fin n → L.Constants) (g : N ≃ B)
    (mN : A ↪[L] N) (gY : A → B) (hgY : ∀ y, gY y = g (mN y))
    (m : Fin n → A) (hm : ∀ k, m k = (cst k : A)) (FmarkY : Fin n → B)
    (hN : ∀ k, g (cst k : N) = FmarkY k) :
    ∀ k, gY (m k) = FmarkY k := by
  intro k
  rw [hgY, hm, HomClass.map_constants, hN]
end


section
open FirstOrder.Language

/-- **The `τ`-embedding `gY` of a piece from its pair-language match (proved).** If the piece `A`
carries an `L`-structure whose reduct along `φ : L' →ᴸ L` is its own `L'`-structure, the sample
identification `g : N ≃ B` carries the `φ`-reduct of `N` to the `L'`-structure of `B` (as
`YSampleLike` records for `τ`), and `mN : A ↪[L] N`, then `g ∘ mN` is an `L'`-embedding: the
`τ`-embedding `gY` of the piece data, read from the hull match. -/
theorem infra_83_tau_embedding_of_reading {L L' : FirstOrder.Language.{u, u}} {A N B : Type u}
    [L.Structure A] [L.Structure N] [L'.Structure A] [L'.Structure B] (φ : L' →ᴸ L)
    (hAf : ∀ {k} (f : L'.Functions k) (x : Fin k → A),
      Structure.funMap f x = Structure.funMap (φ.onFunction f) x)
    (hAr : ∀ {k} (r : L'.Relations k) (x : Fin k → A),
      Structure.RelMap r x ↔ Structure.RelMap (φ.onRelation r) x)
    (g : N ≃ B)
    (hgf : ∀ {k} (f : L'.Functions k) (x : Fin k → N),
      g (Structure.funMap (φ.onFunction f) x) = Structure.funMap f (g ∘ x))
    (hgr : ∀ {k} (r : L'.Relations k) (x : Fin k → N),
      Structure.RelMap (φ.onRelation r) x ↔ Structure.RelMap r (g ∘ x))
    (mN : A ↪[L] N) :
    ∃ gY : A ↪[L'] B, ∀ y, gY y = g (mN y) := by
  let gY : A ↪[L'] B :=
    { toFun := fun y => g (mN y)
      inj' := fun a b hab => mN.injective (g.injective hab)
      map_fun' := fun {k} f x => by
        show g (mN (Structure.funMap f x)) = Structure.funMap f (fun i => g (mN (x i)))
        rw [hAf, mN.map_fun, hgf]
        rfl
      map_rel' := fun {k} r x => by
        show Structure.RelMap r (fun i => g (mN (x i))) ↔ Structure.RelMap r x
        rw [hAr, ← mN.map_rel (φ.onRelation r) x, hgr]
        rfl }
  exact ⟨gY, fun y => rfl⟩
end


section
open FirstOrder.Language

/-- **The image of a hull piece stays in a closed set (proved).** If every element of the piece
`A` is a term in generators `v`, `mN : A ↪[L] N`, and `T ⊆ N` is closed under the `L`-functions and
contains the images of the generators, then `mN[A] ⊆ T`. With `T` the `Y`-copy (closed under the
`Y`-language, `YSampleLike`) this gives the range clause `gY x ∈ F[M.Y]` of the piece data. -/
theorem infra_83_hull_image_closed {L : FirstOrder.Language.{u, u}} {A N : Type u}
    [L.Structure A] [L.Structure N] (mN : A ↪[L] N) {ι : Type*} (v : ι → A)
    (hgen : ∀ a, ∃ t : L.Term ι, t.realize v = a) (T : Set N) (hv : ∀ i, mN (v i) ∈ T)
    (hT : ∀ {k} (f : L.Functions k) (x : Fin k → N), (∀ i, x i ∈ T) →
      Structure.funMap f x ∈ T) :
    ∀ a, mN a ∈ T := by
  intro a
  obtain ⟨t, rfl⟩ := hgen a
  induction t with
  | var i => exact hv i
  | func f ts ih =>
    simp only [Term.realize]
    rw [mN.map_fun]
    exact hT f _ fun i => ih i
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **Strongness of `gY` from a `Y_H = F(Z_H)` identification (proved).** Paper (Lemma 8.3:
`Y_H ≅ F(Z_H)`, matched by `F` of an order map): if the piece carrier is identified with `F(Z₀)`
by a strong `ψY` and `gY = F(e_Z) ∘ ψY` for an order embedding `e_Z : Z₀ ↪o Jp`, then `gY` is
strong (`map_strong` and `strong_trans`): the clause `K.Strong gY` of the piece data. -/
theorem infra_83_gY_strong_of_FZ (E : OrderPresentation K) {A : Model K.τ}
    {Z0 Jp : Type u} [LinearOrder Z0] [Nonempty Z0] [LinearOrder Jp] [Nonempty Jp]
    (ψY : Language.Embedding K.τ A.carrier (E.obj Z0).carrier) (hψY : K.Strong ψY) (eZ : Z0 ↪o Jp)
    (gY : Language.Embedding K.τ A.carrier (E.obj Jp).carrier)
    (hgY : ∀ y, gY y = E.map eZ (ψY y)) :
    K.Strong gY := by
  have : gY = (E.map eZ).comp ψY := by
    ext y
    exact hgY y
  rw [this]
  exact K.strong_trans ψY (E.map eZ) hψY (E.map_strong eZ)
end


section

/-- **The `X`-sort reading of a piece from its chart (proved).** Paper (Lemma 8.3: "`X_H = F(J_H)`",
`infra_83_XH_sort_sample`): if the image `gY[Y_u]` meets the `X`-copy `W` exactly in `F` of its own
`X`-chart (`gY[Y_u] ∩ W = C`) and that chart copy `C` lies in `gY[X']`, then every point of
`gY[Y_u]` in `W` is the image of a point of `X'`: the hypothesis `hXH` of `infra_83_piece_meet`. -/
theorem infra_83_piece_XH_of_chart {Yc Xc B : Type u} (gY : Yc → B) (inclu : Xc → Yc)
    (W C : Set B) (hS : Set.range gY ∩ W = C) (hsub : C ⊆ Set.range (gY ∘ inclu)) :
    ∀ x', gY x' ∈ W → ∃ y, gY x' = gY (inclu y) := by
  intro x' hx
  have : gY x' ∈ C := hS ▸ ⟨⟨x', rfl⟩, hx⟩
  obtain ⟨y, hy⟩ := hsub this
  exact ⟨y, hy.symm⟩
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

set_option maxHeartbeats 3200000 in
/-- **Piece clauses from one pair-language match of the piece (proved assembly).** Let the
template piece `X' ≤ Y_u` carry an `L`-structure whose `φ`-reduct is its `τ`-structure, and let
`mN : Y_u ↪[L] N` match it into a sample with identification `g : N ≃ F(Jp)` respecting the
`τ`-reduct. If `g ∘ mN = F(e_Z) ∘ ψY` for a strong `ψY : Y_u → F(Z₀)`, the piece is a term hull in
generators whose images lie in the `g`-preimage of `F[M.Y]` (closed under `L`), and `g ∘ mN` meets
the `X`-copy exactly in a chart copy lying in `g(mN[X'])`, then the piece data clauses hold: a strong
`τ`-embedding `gY = g ∘ mN` inside `F[M.Y]` with the sort intersection, and an `L`-reading of `gY`
with `r` read as `g (r (g⁻¹ a) (g⁻¹ b))`. -/
theorem infra_83_piece_clauses_of_match (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {M : MarkedPair K oneVertexShape P.scheme Pr}
    {J Jp Z0 : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jp] [Nonempty Jp]
    [LinearOrder Z0] [Nonempty Z0] (emb : J ↪o Jp)
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (hsurj : Function.Surjective eX)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jp).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {X' Yu : P.scheme.Object ν hν}
    (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
    {L : FirstOrder.Language.{u, u}} {N : Type u}
    [L.Structure ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier] [L.Structure N]
    (φ : K.τ →ᴸ L)
    (hAf : ∀ {k} (f : K.τ.Functions k) (x : Fin k → ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier),
      Structure.funMap f x = Structure.funMap (φ.onFunction f) x)
    (hAr : ∀ {k} (r : K.τ.Relations k) (x : Fin k → ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier),
      Structure.RelMap r x ↔ Structure.RelMap (φ.onRelation r) x)
    (g : N ≃ (P.E.obj Jp).carrier)
    (hgf : ∀ {k} (f : K.τ.Functions k) (x : Fin k → N),
      g (Structure.funMap (φ.onFunction f) x) = Structure.funMap f (g ∘ x))
    (hgr : ∀ {k} (r : K.τ.Relations k) (x : Fin k → N),
      Structure.RelMap (φ.onRelation r) x ↔ Structure.RelMap r (g ∘ x))
    (mN : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier ↪[L] N)
    (ψY : Language.Embedding K.τ ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier
      (P.E.obj Z0).carrier) (hψY : K.Strong ψY) (eZ : Z0 ↪o Jp)
    (hZ : ∀ y, g (mN y) = P.E.map eZ (ψY y))
    {ι : Type*} (v : ι → ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier)
    (hgen : ∀ a, ∃ t : L.Term ι, t.realize v = a)
    (hv : ∀ i, g (mN (v i)) ∈ Set.range F)
    (hT : ∀ {k} (f : L.Functions k) (x : Fin k → N), (∀ i, g (x i) ∈ Set.range F) →
      g (Structure.funMap f x) ∈ Set.range F)
    (C : Set (P.E.obj Jp).carrier)
    (hS : Set.range (fun y => g (mN y)) ∩ Set.range (P.E.map emb) = C)
    (hsub : C ⊆ Set.range (fun x => g (mN (inclu.onVertex PUnit.unit x))))
    (r : L.Functions 2) :
    ∃ gY : Language.Embedding K.τ ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier
        (P.E.obj Jp).carrier,
      (∀ y, gY y = g (mN y)) ∧ K.Strong gY ∧ (∀ x, gY x ∈ Set.range F) ∧
      (∀ (x' : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier)
        (z : ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier),
        gY x' = F (M.incl.onVertex PUnit.unit z) → ∃ y, x' = inclu.onVertex PUnit.unit y) ∧
      ∃ (_ : L.Structure (P.E.obj Jp).carrier)
        (mY : ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier ↪[L] (P.E.obj Jp).carrier),
        (∀ y, mY y = gY y) ∧
        ∀ a b, Structure.funMap r ![a, b] = g (Structure.funMap r ![g.symm a, g.symm b]) := by
  obtain ⟨gY, hgY⟩ := infra_83_tau_embedding_of_reading φ hAf hAr g hgf hgr mN
  have hs : K.Strong gY := infra_83_gY_strong_of_FZ P.E ψY hψY eZ gY (fun y => by rw [hgY, hZ])
  have hr : ∀ x, gY x ∈ Set.range F := by
    intro x
    rw [hgY]
    exact infra_83_hull_image_closed mN v hgen {w | g w ∈ Set.range F} hv
      (fun f x hx => hT f x hx) x
  have hXH := infra_83_piece_XH_of_chart gY (inclu.onVertex PUnit.unit) (Set.range (P.E.map emb)) C
    (by
      have : (gY : _ → _) = fun y => g (mN y) := funext hgY
      rw [this]; exact hS)
    (by
      intro w hw
      obtain ⟨x, hx⟩ := hsub hw
      exact ⟨x, by simp only [Function.comp_apply, hgY]; exact hx⟩)
  have hmeet := infra_83_piece_meet P emb eX hsurj F hF inclu gY gY.injective hXH
  obtain ⟨sB, mY, hmY, hret⟩ := infra_83_L0_reading_transport g mN r
  exact ⟨gY, hgY, hs, hr, hmeet, sB, mY, fun y => by rw [hmY, hgY], hret⟩
end


section
open FirstOrder.Language

/-- **Transport of a pair-language expansion along a `τ`-isomorphism (proved).** If `A₀` carries an
`L`-structure whose reduct along `φ : L' →ᴸ L` is its `L'`-structure (as the template's limit
values do: their `τ`-structure is the reduct of the pair language), and `e : A₀ ≃[L'] A`, then the
`L`-structure induced on `A` by `e` has `φ`-reduct equal to the `L'`-structure of `A`: the
hypotheses `hAf`, `hAr` of `infra_83_piece_clauses_of_match` for the scheme value `A`. -/
theorem infra_83_expansion_transport {L L' : FirstOrder.Language.{u, u}} {A₀ A : Type u}
    [L.Structure A₀] [L'.Structure A₀] [L'.Structure A] (φ : L' →ᴸ L)
    (hAf : ∀ {k} (f : L'.Functions k) (x : Fin k → A₀),
      Structure.funMap f x = Structure.funMap (φ.onFunction f) x)
    (hAr : ∀ {k} (r : L'.Relations k) (x : Fin k → A₀),
      Structure.RelMap r x ↔ Structure.RelMap (φ.onRelation r) x)
    (e : A₀ ≃[L'] A) :
    letI : L.Structure A := e.toEquiv.inducedStructure
    (∀ {k} (f : L'.Functions k) (x : Fin k → A),
      Structure.funMap f x = Structure.funMap (φ.onFunction f) x) ∧
    (∀ {k} (r : L'.Relations k) (x : Fin k → A),
      Structure.RelMap r x ↔ Structure.RelMap (φ.onRelation r) x) := by
  letI : L.Structure A := e.toEquiv.inducedStructure
  refine ⟨fun {k} f x => ?_, fun {k} r x => ?_⟩
  · show Structure.funMap f x = e.toEquiv (Structure.funMap (φ.onFunction f) (e.toEquiv.symm ∘ x))
    rw [← hAf, show e.toEquiv (Structure.funMap f (e.toEquiv.symm ∘ x)) =
      e (Structure.funMap f (e.symm ∘ x)) from rfl, e.map_fun]
    congr 1
    funext i
    exact (e.apply_symm_apply (x i)).symm
  · show Structure.RelMap r x ↔ Structure.RelMap (φ.onRelation r) (e.toEquiv.symm ∘ x)
    rw [← hAr, show (e.toEquiv.symm ∘ x) = (e.symm ∘ x) from rfl, ← e.map_rel]
    have : (e ∘ (e.symm ∘ x)) = x := funext fun i => e.apply_symm_apply (x i)
    rw [this]
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

set_option maxHeartbeats 1600000 in
/-- **A template piece between `X'` and `Y'` holding a small set (proved).** Paper (Lemma 8.3: the
hull `Y_H` of `X_H` and the list): for a scheme arrow `incl' : X' → Y'` at level `ν` and at most `ν`
points `s` of `Y'`, there is a scheme object `Y_u` at level `ν` with arrows `inclu : X' → Y_u`,
`j : Y_u → Y'`, `inclu ; j = incl'`, whose image under `j` contains every `s i` (Löwenheim–Skolem at
the exact cardinality `ν`, `exists_downward`; strongness of `inclu` by coherence). -/
theorem infra_83_piece_object (P : SingleModelData K) {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {X' Y' : P.scheme.Object ν hν}
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Y'))
    {ι : Type u} (s : ι → ((P.scheme.asSystem hν Y').obj PUnit.unit).carrier) (hι : #ι ≤ ν) :
    ∃ (Yu : P.scheme.Object ν hν)
      (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
      (j : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem hν Y')),
      SystemArrow.comp inclu j = incl' ∧ ∀ i, ∃ y, j.onVertex PUnit.unit y = s i := by
  classical
  let occ : ((P.scheme.asSystem hν X').obj PUnit.unit).carrier ⊕ ι →
      ((P.scheme.asSystem hν Y').obj PUnit.unit).carrier :=
    Sum.elim (incl'.onVertex PUnit.unit) s
  have hcX : #((P.scheme.asSystem hν X').obj PUnit.unit).carrier = ν := X'.card
  have hcard : #(((P.scheme.asSystem hν X').obj PUnit.unit).carrier ⊕ ι) ≤ ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, hcX]
    exact Cardinal.add_le_of_le (P.aleph0_le hν) le_rfl hι
  obtain ⟨Yu, f, hf, hcov⟩ := SingleModelData.exists_downward hν hν Y' occ le_rfl hcard
  choose h0 hh0' using fun x => hcov (Sum.inl x)
  let gY := incl'.onVertex PUnit.unit
  have hh0 : ∀ x, f (h0 x) = gY x := hh0'
  have hgY : K.Strong gY := incl'.onVertex_strong PUnit.unit
  let hE : Language.Embedding K.τ ((P.scheme.asSystem hν X').obj PUnit.unit).carrier
      Yu.model.carrier :=
    { toFun := h0
      inj' := fun a b hab => gY.injective (by
        rw [← hh0 a, ← hh0 b, hab])
      map_fun' := fun {n} g x => f.injective (by
        rw [hh0, f.map_fun]
        show gY (Structure.funMap g x) = _
        rw [gY.map_fun]
        congr 1
        funext i
        exact (hh0 (x i)).symm)
      map_rel' := fun {n} r x => by
        rw [← f.map_rel]
        have : (f ∘ (h0 ∘ x)) = gY ∘ x := funext fun i => hh0 (x i)
        rw [this]
        exact gY.map_rel r x }
  have hcomp : f.comp hE = gY := by
    ext x
    exact hh0 x
  have hsh : K.Strong hE := K.coherence hE gY f hgY hf hcomp
  refine ⟨Yu, ⟨fun _ => hE, fun _ => hsh, fun h => h.elim⟩,
    ⟨fun _ => f, fun _ => hf, fun h => h.elim⟩, ?_, fun i => hcov (Sum.inr i)⟩
  apply SystemArrow.ext
  intro v
  cases v
  ext x
  exact hh0 x
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **A template piece holding a preimage of a small tuple (proved).** For `incl' : X' → Y'` at
level `ν` and a tuple `w` of at most `ν` occurrences of `Y'` (e.g. `seqJoint b c` for the mark `b`
and a bounded `c`), there are a piece `X' ≤ Y_u ≤ Y'` (`inclu ; j = incl'`) and a tuple `d` of
`Y_u` with `j(d) = w`: the piece and preimage clauses of `infra_83_marked_of_piece_data`
(`infra_83_piece_object`). -/
theorem infra_83_piece_with_tuple (P : SingleModelData K) {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {X' Y' : P.scheme.Object ν hν}
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Y'))
    {idx : Type u} (w : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν Y'))
    (hidx : #idx ≤ ν) :
    ∃ (Yu : P.scheme.Object ν hν)
      (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
      (j : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem hν Y'))
      (d : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν Yu)),
      SystemArrow.comp inclu j = incl' ∧ ∀ i, j.mapOcc (d i) = w i := by
  obtain ⟨Yu, inclu, j, hj, hcov⟩ :=
    infra_83_piece_object P incl' (fun i => (w i).2) hidx
  choose y hy using hcov
  refine ⟨Yu, inclu, j, fun i => ⟨PUnit.unit, y i⟩, hj, fun i => ?_⟩
  apply Sigma.ext
  · exact Subsingleton.elim _ _
  · exact heq_of_eq (hy i)
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **Mark positions of a piece tuple (proved).** Every tuple `d` of a one-vertex piece indexed by
`Fin n ⊕ cIdx` has its mark part at positions `m k := (d (inl k)).2`, i.e.
`d (inl a) = ⟨*, m a⟩`: the clause `hdm` of `infra_83_marked_of_piece_data`. -/
theorem infra_83_mark_positions (P : SingleModelData K) {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {Yu : P.scheme.Object ν hν} {n : ℕ} {cIdx : Type u}
    (d : ULift.{u} (Fin n) ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν Yu)) :
    ∃ m : Fin n → ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier,
      ∀ a : ULift.{u} (Fin n), d (Sum.inl a) = ⟨PUnit.unit, m a.down⟩ := by
  refine ⟨fun k => (d (Sum.inl ⟨k⟩)).2, fun a => ?_⟩
  apply Sigma.ext
  · exact Subsingleton.elim _ _
  · rfl
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **All-domination from per-list arrows into isolating pairs (proved).** Local form of
`infra_83_dominated_pull` for `infra_83_arity_removal`: if for every bounded `c` there is an arrow
`h_c : Y → Y'_c` (depending on `c`) such that `tp(h_c(b), h_c(c) / X)` is isolated relative to
`h_c(b)` in `Y'_c` over the pushed inclusion, then `Y` is all-dominated over `X + b`. -/
theorem infra_83_dominated_of_local_arrows (P : SingleModelData K) {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hincl : P.scheme.permitted (X := X) (Y := Y) incl)
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (hb : #bIdx < μ)
    (hloc : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      #cIdx < μ →
      ∃ (Y' : P.scheme.Object μ hμ)
        (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ Y')),
        IsRelativelyIsolated (uIdx := bIdx) (cIdx := cIdx)
          (asTuple (SystemArrow.comp incl h) trivial (fun s => h.mapOcc (seqJoint b c s)))
          (Equiv.refl _)) :
    AllDominated incl hincl bIdx b := by
  intro cIdx c hc
  have hcard : #(bIdx ⊕ cIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_lt hμ).le hb hc
  obtain ⟨Y', h, H⟩ := hloc cIdx c hc
  exact infra_83_relIso_pull P incl hincl h (seqJoint b c) (Equiv.refl _) hcard H
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **All-domination from isolation on pieces (proved).** Localizes Definition 7.4 to pieces: if for
every bounded `c` there is a piece `X ≤ Y_u ≤ Y` (`inclu ; j = incl`) holding a preimage `d` of
`(b, c)` such that `tp(d/X)` in `Y_u` is isolated relative to its `b`-part, then `Y` is
all-dominated over `X + b` (`infra_83_relIso_push` along `j`). With `infra_83_piece_with_tuple`
the pieces exist; the isolation on the piece is the remaining content of
`infra_83_arity_removal`. -/
theorem infra_83_dominated_of_piece_isolation (P : SingleModelData K) {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (hb : #bIdx < μ)
    (hloc : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      #cIdx < μ →
      ∃ (Yu : P.scheme.Object μ hμ)
        (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Yu))
        (j : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Yu) (P.scheme.asSystem hμ Y))
        (d : bIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Yu)),
        SystemArrow.comp inclu j = incl ∧ (∀ s, j.mapOcc (d s) = seqJoint b c s) ∧
        IsRelativelyIsolated (uIdx := bIdx) (cIdx := cIdx) (asTuple inclu trivial d)
          (Equiv.refl _)) :
    AllDominated incl trivial bIdx b := by
  intro cIdx c hc
  have hcard : #(bIdx ⊕ cIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_lt hμ).le hb hc
  obtain ⟨Yu, inclu, j, d, hj, hjd, H⟩ := hloc cIdx c hc
  have H' := infra_83_relIso_push P inclu trivial j d (Equiv.refl _) hcard H
  have hx : (fun s => j.mapOcc (d s)) = seqJoint b c := funext hjd
  rw [hx, hj] at H'
  exact H'
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **Marked from pieces (proved).** `X ≤ Y` with mark `b` is marked (the mark realizes the
prescribed type and `Y` is all-dominated over `X + b`) once some piece `X ≤ Y₀ ≤ Y` holding a
preimage of `b` realizes the type there (`infra_83_realizes_push`), and every bounded `c` has a
piece holding a preimage of `(b, c)` with the relatively isolated type
(`infra_83_dominated_of_piece_isolation`). -/
theorem infra_83_marked_of_pieces (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (hb : #bIdx < μ) (realEq : bIdx ≃ (Pr.assign hμ X).idx)
    (Y0 : P.scheme.Object μ hμ)
    (incl0 : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y0))
    (j0 : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y0) (P.scheme.asSystem hμ Y))
    (b0 : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y0))
    (hj0 : SystemArrow.comp incl0 j0 = incl) (hb0 : ∀ i, j0.mapOcc (b0 i) = b i)
    (hr0 : SameGaloisType (asTuple incl0 trivial b0) (Pr.assign hμ X) realEq (Equiv.refl _))
    (hloc : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      #cIdx < μ →
      ∃ (Yu : P.scheme.Object μ hμ)
        (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Yu))
        (j : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Yu) (P.scheme.asSystem hμ Y))
        (d : bIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Yu)),
        SystemArrow.comp inclu j = incl ∧ (∀ s, j.mapOcc (d s) = seqJoint b c s) ∧
        IsRelativelyIsolated (uIdx := bIdx) (cIdx := cIdx) (asTuple inclu trivial d)
          (Equiv.refl _)) :
    SameGaloisType (asTuple incl trivial b) (Pr.assign hμ X) realEq (Equiv.refl _) ∧
      AllDominated incl trivial bIdx b := by
  refine ⟨?_, infra_83_dominated_of_piece_isolation P incl b hb hloc⟩
  have H := infra_83_realizes_push P Pr incl0 trivial j0 b0 realEq hr0
  have hx : (fun i => j0.mapOcc (b0 i)) = b := funext hb0
  rw [hx, hj0] at H
  exact H
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **Piece, preimage and mark positions for one bounded list (proved).** For `incl' : X' → Y'` at
level `ν`, a mark `b` indexed by `Fin n` and a bounded `c` (`#cIdx < ν`), there are a piece
`X' ≤ Y_u ≤ Y'`, a preimage `d` of `(b, c)` in `Y_u` and mark positions `m` with
`d (inl a) = ⟨*, m a⟩`: the clauses `hj`, `hjd`, `hdm` of `infra_83_marked_of_piece_data`
(`infra_83_piece_with_tuple`, `infra_83_mark_positions`). -/
theorem infra_83_piece_for_list (P : SingleModelData K) {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {X' Y' : P.scheme.Object ν hν}
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Y'))
    {n : ℕ} (b : ULift.{u} (Fin n) → Occurrence K oneVertexShape (P.scheme.asSystem hν Y'))
    {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν Y'))
    (hc : #cIdx < ν) :
    ∃ (Yu : P.scheme.Object ν hν)
      (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
      (j : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem hν Y'))
      (m : Fin n → ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier)
      (d : ULift.{u} (Fin n) ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν Yu)),
      SystemArrow.comp inclu j = incl' ∧ (∀ s, j.mapOcc (d s) = seqJoint b c s) ∧
      ∀ a, d (Sum.inl a) = ⟨PUnit.unit, m a.down⟩ := by
  have hcard : #(ULift.{u} (Fin n) ⊕ cIdx) ≤ ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_le_of_le (P.aleph0_le hν)
      ((Cardinal.lt_aleph0_of_finite _).le.trans (P.aleph0_le hν)) hc.le
  obtain ⟨Yu, inclu, j, d, hj, hjd⟩ := infra_83_piece_with_tuple P incl' (seqJoint b c) hcard
  obtain ⟨m, hm⟩ := infra_83_mark_positions P d
  exact ⟨Yu, inclu, j, m, d, hj, hjd, hm⟩
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **The prescribed-type clause is local to pieces (proved).** For a piece `X ≤ Y₀ ≤ Y`
(`incl0 ; j0 = incl`) holding a preimage `b₀` of the mark `b`, the mark realizes the prescribed
type over `X` in `Y` iff `b₀` does in `Y₀` (`infra_83_realizes_push`, `infra_83_realizes_pull`). -/
theorem infra_83_realizes_piece_iff (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y Y0 : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (incl0 : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y0))
    (j0 : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y0) (P.scheme.asSystem hμ Y))
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b0 : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y0))
    (hj0 : SystemArrow.comp incl0 j0 = incl) (hb0 : ∀ i, j0.mapOcc (b0 i) = b i)
    (realEq : bIdx ≃ (Pr.assign hμ X).idx) :
    SameGaloisType (asTuple incl trivial b) (Pr.assign hμ X) realEq (Equiv.refl _) ↔
      SameGaloisType (asTuple incl0 trivial b0) (Pr.assign hμ X) realEq (Equiv.refl _) := by
  have hx : (fun i => j0.mapOcc (b0 i)) = b := funext hb0
  constructor
  · intro H
    have H' : SameGaloisType (asTuple (SystemArrow.comp incl0 j0) trivial
        (fun i => j0.mapOcc (b0 i))) (Pr.assign hμ X) realEq (Equiv.refl _) := by
      rw [hx, hj0]; exact H
    exact infra_83_realizes_pull P Pr incl0 trivial j0 b0 realEq H'
  · intro H
    have H' := infra_83_realizes_push P Pr incl0 trivial j0 b0 realEq H
    rw [hx, hj0] at H'
    exact H'
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **Relative isolation is local to pieces (proved).** For a piece `X ≤ Y_u ≤ Y`
(`inclu ; j = incl`) holding a preimage `d` of `(b, c)`, `tp(b, c / X)` in `Y` is isolated relative
to `b` iff `tp(d / X)` in `Y_u` is (`infra_83_relIso_push`, `infra_83_relIso_pull`): the clause of
Definition 7.4 for one bounded `c` can be checked on any piece holding `(b, c)`. -/
theorem infra_83_relIso_piece_iff (P : SingleModelData K) {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y Yu : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Yu))
    (j : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Yu) (P.scheme.asSystem hμ Y))
    {bIdx cIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (d : bIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Yu))
    (hj : SystemArrow.comp inclu j = incl) (hjd : ∀ s, j.mapOcc (d s) = seqJoint b c s)
    (hcard : #(bIdx ⊕ cIdx) < μ) :
    IsRelativelyIsolated (uIdx := bIdx) (cIdx := cIdx) (asTuple incl trivial (seqJoint b c))
        (Equiv.refl _) ↔
      IsRelativelyIsolated (uIdx := bIdx) (cIdx := cIdx) (asTuple inclu trivial d)
        (Equiv.refl _) := by
  have hx : (fun s => j.mapOcc (d s)) = seqJoint b c := funext hjd
  constructor
  · intro H
    have H' : IsRelativelyIsolated (uIdx := bIdx) (cIdx := cIdx)
        (asTuple (SystemArrow.comp inclu j) trivial (fun s => j.mapOcc (d s))) (Equiv.refl _) := by
      rw [hx, hj]; exact H
    exact infra_83_relIso_pull P inclu trivial j d (Equiv.refl _) hcard H'
  · intro H
    have H' := infra_83_relIso_push P inclu trivial j d (Equiv.refl _) hcard H
    rw [hx, hj] at H'
    exact H'
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **All-domination checked on pieces (proved characterization).** `Y` is all-dominated over
`X + b` iff for every bounded `c` and every piece `X ≤ Y_u ≤ Y` holding a preimage `d` of `(b, c)`,
`tp(d/X)` in `Y_u` is isolated relative to its `b`-part (`infra_83_relIso_piece_iff`; such pieces
exist by `infra_83_piece_with_tuple`, so the condition is not vacuous). -/
theorem infra_83_dominated_iff_pieces (P : SingleModelData K) {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (hb : #bIdx < μ) :
    AllDominated incl trivial bIdx b ↔
      ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
        #cIdx < μ →
        ∀ (Yu : P.scheme.Object μ hμ)
          (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Yu))
          (j : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Yu) (P.scheme.asSystem hμ Y))
          (d : bIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Yu)),
          SystemArrow.comp inclu j = incl → (∀ s, j.mapOcc (d s) = seqJoint b c s) →
          IsRelativelyIsolated (uIdx := bIdx) (cIdx := cIdx) (asTuple inclu trivial d)
            (Equiv.refl _) := by
  constructor
  · intro hD cIdx c hc Yu inclu j d hj hjd
    have hcard : #(bIdx ⊕ cIdx) < μ := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.add_lt_of_lt (P.aleph0_lt hμ).le hb hc
    exact (infra_83_relIso_piece_iff P incl inclu j b c d hj hjd hcard).1 (hD cIdx c hc)
  · intro H
    refine infra_83_dominated_of_piece_isolation P incl b hb fun cIdx c hc => ?_
    have hcard : #(bIdx ⊕ cIdx) ≤ μ := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.add_le_of_le (P.aleph0_le hμ) (hb.le) hc.le
    obtain ⟨Yu, inclu, j, d, hj, hjd⟩ := infra_83_piece_with_tuple P incl (seqJoint b c) hcard
    exact ⟨Yu, inclu, j, d, hj, hjd, H cIdx c hc Yu inclu j d hj hjd⟩
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **Marked pairs checked on one piece holding the mark (proved).** For any piece
`X ≤ Y₀ ≤ Y` holding a preimage `b₀` of the mark `b`, `(X ≤ Y, b)` is marked (realizes the
prescribed type, all-dominated over `X + b`) iff `b₀` realizes the type in `Y₀` and every bounded
`c` of `Y` has its `(b, c)` type isolated on every piece holding a preimage
(`infra_83_realizes_piece_iff`, `infra_83_dominated_iff_pieces`). -/
theorem infra_83_marked_iff_pieces (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y Y0 : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (incl0 : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y0))
    (j0 : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y0) (P.scheme.asSystem hμ Y))
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b0 : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y0))
    (hj0 : SystemArrow.comp incl0 j0 = incl) (hb0 : ∀ i, j0.mapOcc (b0 i) = b i)
    (hb : #bIdx < μ) (realEq : bIdx ≃ (Pr.assign hμ X).idx) :
    (SameGaloisType (asTuple incl trivial b) (Pr.assign hμ X) realEq (Equiv.refl _) ∧
      AllDominated incl trivial bIdx b) ↔
    (SameGaloisType (asTuple incl0 trivial b0) (Pr.assign hμ X) realEq (Equiv.refl _) ∧
      ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
        #cIdx < μ →
        ∀ (Yu : P.scheme.Object μ hμ)
          (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Yu))
          (j : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Yu) (P.scheme.asSystem hμ Y))
          (d : bIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Yu)),
          SystemArrow.comp inclu j = incl → (∀ s, j.mapOcc (d s) = seqJoint b c s) →
          IsRelativelyIsolated (uIdx := bIdx) (cIdx := cIdx) (asTuple inclu trivial d)
            (Equiv.refl _)) := by
  rw [infra_83_realizes_piece_iff P Pr incl incl0 j0 b b0 hj0 hb0 realEq,
    infra_83_dominated_iff_pieces P incl b hb]
end


section
variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 3200000 in
/-- **Lemma 8.3 (P.scheme) reduced to realization plus isolation on pieces (proved reduction).**
For the constructed pair template, `Lemma83Conclusion` holds once, for every value on a well-order
`I` with `#I` in the closed tail, the mark realizes the prescribed type and every bounded `(mk_I, c)`
type is isolated on some piece `X_I ≤ Y_u ≤ Y_I` holding a preimage
(`infra_83_dominated_of_piece_isolation`). -/
theorem infra_83_full_single_of_pieces (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (X Y : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        P.scheme.Object #I hI)
      (incl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        SystemArrow K oneVertexShape (P.scheme.asSystem hI (X I hI))
          (P.scheme.asSystem hI (Y I hI)))
      (mk : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        Fin Pr.n → Occurrence K oneVertexShape (P.scheme.asSystem hI (Y I hI))),
      (∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
          (hI : #I ∈ infra_78_closedTail P ∩ infra_615_closed P),
          (∃ realEq : ULift.{u} (Fin Pr.n) ≃ (Pr.assign hI.2.1 (X I hI.2.1)).idx,
            SameGaloisType (asTuple (incl I hI.2.1) trivial
              (fun a : ULift.{u} (Fin Pr.n) => mk I hI.2.1 a.down))
              (Pr.assign hI.2.1 (X I hI.2.1)) realEq (Equiv.refl _)) ∧
          ∀ (cIdx : Type u)
            (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hI.2.1 (Y I hI.2.1))),
            #cIdx < #I →
            ∃ (Yu : P.scheme.Object #I hI.2.1)
              (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 (X I hI.2.1))
                (P.scheme.asSystem hI.2.1 Yu))
              (j : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 Yu)
                (P.scheme.asSystem hI.2.1 (Y I hI.2.1)))
              (d : ULift.{u} (Fin Pr.n) ⊕ cIdx →
                Occurrence K oneVertexShape (P.scheme.asSystem hI.2.1 Yu)),
              SystemArrow.comp inclu j = incl I hI.2.1 ∧
              (∀ s, j.mapOcc (d s) =
                seqJoint (fun a : ULift.{u} (Fin Pr.n) => mk I hI.2.1 a.down) c s) ∧
              IsRelativelyIsolated (uIdx := ULift.{u} (Fin Pr.n)) (cIdx := cIdx)
                (asTuple inclu trivial d) (Equiv.refl _)) →
      Lemma83Conclusion P.scheme Pr := by
  obtain ⟨F, X, Y, eX, eY, incl, mk, hincl, harr⟩ := infra_83_pair_template_clauses P Pr
  refine ⟨X, Y, incl, mk, fun hS => ?_⟩
  refine infra_83_conclusion_of_marked_values_idx P Pr F X Y eX eY incl mk hincl harr _
    (infra_83_closed_tail P) (fun I _ _ _ hI => ?_)
  obtain ⟨⟨realEq, hr⟩, hloc⟩ := hS I hI
  have hb : #(ULift.{u} (Fin Pr.n)) < #I :=
    (Cardinal.lt_aleph0_of_finite _).trans (P.aleph0_lt hI.2.1)
  exact ⟨ULift.{u} (Fin Pr.n), Equiv.refl _, realEq, hr,
    infra_83_dominated_of_piece_isolation P (incl I hI.2.1) _ hb hloc⟩
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **The sample's `F` is linked to its `Y`-copy (proved; class strengthened in cycle 216).** In a
ret-admitted sample, the copy `F[M.Y]` of the sample's `Y` (read through `g : N ≃ F(Jp)`) is closed
under the `Y`-language: the closure clause `hT` of `infra_83_piece_clauses_of_match` for the
`Y`-language reading. Verified on the real samples in `infra_83_pairMS3_coherent_colors`, where the
`Y`-copy `e₀ = F ∘ ι` has the same range as `F`. -/
theorem infra_83_retSample_Y_link (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {N : Type u}
    [(LS83.pairLangM3 P.E Pr.n).Structure N] (hN : RetSampleLike P Pr N) :
    ∃ (M : MarkedPair K oneVertexShape P.scheme Pr) (Jp : Type u) (_ : LinearOrder Jp)
      (_ : Nonempty Jp) (g : N ≃ (P.E.obj Jp).carrier)
      (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
        (P.E.obj Jp).carrier),
      ∀ {k} (f : (LS83.pairLangM2 P.E Pr.n).Functions k) (x : Fin k → N),
        (∀ i, g (x i) ∈ Set.range F) → g (yFun P.E Pr.n f x) ∈ Set.range F := by
  obtain ⟨M, J, Jp, i1, i2, i3, i4, emb, g, eX, F, R, code, -, -, -, -, -, -, -, -, -, -, -,
    hY⟩ := hN
  exact ⟨M, Jp, i3, i4, g, F, fun f x hx => hY f x hx⟩
end


section
variable {K : AbstractElementaryClass.{u}}
open FirstOrder.Language

set_option maxHeartbeats 1600000 in
/-- **A piece `Y_u ≅ F(Z_u)` from a sub-order (proved).** Paper (Lemma 8.3: `Y_H ≅ F(Z_H)`): let
`Y'` be identified with `F(Z)` by a `τ`-isomorphism `φ` (as the template values are,
`infra_83_Y_hull_eq_FZ`), let `s_Z : Z₀ ↪o Z` with `|F(Z₀)| = ν`, and suppose `φ ∘ incl'` lands in
`F(s_Z)[F(Z₀)]`. Then there is a scheme piece `X' ≤ Y_u ≤ Y'` (`inclu ; j = incl'`) with a strong
identification `ψY : Y_u → F(Z₀)` (onto) such that `φ ∘ j = F(s_Z) ∘ ψY`: input (ii) of the
piece clauses. -/
theorem infra_83_piece_of_suborder (P : SingleModelData K) {ν : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {X' Y' : P.scheme.Object ν hν}
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Y'))
    {Z Z0 : Type u} [LinearOrder Z] [Nonempty Z] [LinearOrder Z0] [Nonempty Z0]
    (φ : ((P.scheme.asSystem hν Y').obj PUnit.unit).carrier ≃[K.τ] (P.E.obj Z).carrier)
    (sZ : Z0 ↪o Z) (hc : Model.card (P.E.obj Z0) = ν)
    (hsub : ∀ x, φ (incl'.onVertex PUnit.unit x) ∈ Set.range (P.E.map sZ)) :
    ∃ (Yu : P.scheme.Object ν hν)
      (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
      (j : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem hν Y'))
      (ψY : Language.Embedding K.τ ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier
        (P.E.obj Z0).carrier),
      K.Strong ψY ∧ Function.Surjective ψY ∧ SystemArrow.comp inclu j = incl' ∧
      ∀ y, φ (j.onVertex PUnit.unit y) = P.E.map sZ (ψY y) := by
  classical
  let Yu : SMObject K ν := SMObject.ofModel (P.E.obj Z0) (P.hE Z0) hc
  let e := SMObject.ofModelEquiv (P.E.obj Z0) (P.hE Z0) hc
  let ψY : Language.Embedding K.τ Yu.model.carrier (P.E.obj Z0).carrier := e.symm.toEmbedding
  have hψ : K.Strong ψY := strong_of_equiv K e.symm Yu.mem
  let f : Language.Embedding K.τ Yu.model.carrier
      ((P.scheme.asSystem hν Y').obj PUnit.unit).carrier :=
    φ.symm.toEmbedding.comp ((P.E.map sZ).comp ψY)
  have hf : K.Strong f :=
    K.strong_trans _ _ (K.strong_trans _ _ hψ (P.E.map_strong sZ)) (strong_of_equiv K φ.symm (P.hE Z))
  have hfφ : ∀ y, φ (f y) = P.E.map sZ (ψY y) := fun y => φ.apply_symm_apply _
  have hcov : ∀ x, ∃ y, f y = incl'.onVertex PUnit.unit x := by
    intro x
    obtain ⟨z, hz⟩ := hsub x
    refine ⟨e z, φ.injective ?_⟩
    rw [hfφ]
    show P.E.map sZ (e.symm (e z)) = _
    rw [e.symm_apply_apply, hz]
  choose h0 hh0' using hcov
  let gY := incl'.onVertex PUnit.unit
  have hh0 : ∀ x, f (h0 x) = gY x := hh0'
  have hgY : K.Strong gY := incl'.onVertex_strong PUnit.unit
  let hE : Language.Embedding K.τ ((P.scheme.asSystem hν X').obj PUnit.unit).carrier
      Yu.model.carrier :=
    { toFun := h0
      inj' := fun a b hab => gY.injective (by rw [← hh0 a, ← hh0 b, hab])
      map_fun' := fun {n} g x => f.injective (by
        rw [hh0, f.map_fun]
        show gY (Structure.funMap g x) = _
        rw [gY.map_fun]
        congr 1
        funext i
        exact (hh0 (x i)).symm)
      map_rel' := fun {n} r x => by
        rw [← f.map_rel]
        have : (f ∘ (h0 ∘ x)) = gY ∘ x := funext fun i => hh0 (x i)
        rw [this]
        exact gY.map_rel r x }
  have hcomp : f.comp hE = gY := by
    ext x
    exact hh0 x
  have hsh : K.Strong hE := K.coherence hE gY f hgY hf hcomp
  refine ⟨Yu, ⟨fun _ => hE, fun _ => hsh, fun h => h.elim⟩,
    ⟨fun _ => f, fun _ => hf, fun h => h.elim⟩, ψY, hψ,
    fun z => ⟨e z, e.symm_apply_apply z⟩, ?_, hfφ⟩
  apply SystemArrow.ext
  intro v
  cases v
  ext x
  exact hh0 x
end


section
variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 1600000 in
/-- **Arity removal reduced to constructive primeness (proved reduction).** Paper (Lemma 8.3,
via Prop 7.5 / Theorem 7.9): on the Theorem 7.9 tail, `Y` is all-dominated over `X + b` (finite
`b`) as soon as `Y` maps over `X` onto `b'` into every all-dominated `V` over `X + b'` with
`tp(b'/X) = tp(b/X)`: Theorem 7.9 supplies such a `V`, and all-domination pulls back along the
arrow (`infra_83_dominated_pull`). No arity bound on the tuples `c` is involved. -/
theorem infra_83_dominated_of_primeness (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (X Y : P.scheme.Object μ (Tail.mem hT hμ))
        (incl : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y))
        {bIdx : Type u} [Finite bIdx]
        (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y)),
        (∀ (V : P.scheme.Object μ (Tail.mem hT hμ))
          (inclV : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ V))
          (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ V)),
          AllDominated inclV trivial bIdx b' →
          SameGaloisType (asTuple incl trivial b) (asTuple inclV trivial b')
            (Equiv.refl bIdx) (Equiv.refl bIdx) →
          ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem _ Y) (P.scheme.asSystem _ V),
            SystemArrow.comp incl h = inclV ∧ ∀ i, h.mapOcc (b i) = b' i) →
        AllDominated incl trivial bIdx b := by
  obtain ⟨T, hT, H79⟩ := theorem_7_9 P
  refine ⟨T, hT, fun μ hμ X Y incl bIdx _ b H => ?_⟩
  obtain ⟨⟨V, f, hf, b', hD, hS⟩, -⟩ :=
    (H79 μ hμ X (asTuple incl trivial b)).1 (inferInstanceAs (Finite bIdx))
  obtain ⟨h, hh, hb⟩ := H V f b' hD hS
  have hb' : b' = fun i => h.mapOcc (b i) := (funext hb).symm
  subst hb' hh
  exact infra_83_dominated_pull P incl trivial h b
    ((Cardinal.lt_aleph0_of_finite _).trans (P.aleph0_lt (Tail.mem hT hμ))) hD
end


section
variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 1600000 in
/-- **Arity removal via constructive primeness at a closed level (proved reduction).** Level-wise
form of `infra_83_dominated_of_primeness` on the Lemma 8.3 tail
(`infra_78_closedTail P ∩ infra_615_closed P`), using the Theorem 7.9 existence clause at that
level (`infra_79_existence_at`). -/
theorem infra_83_dominated_of_primeness_at (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ infra_78_closedTail P ∩ infra_615_closed P) {X Y : P.scheme.Object μ hμ.1.1}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y))
    {bIdx : Type u} [Finite bIdx]
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y))
    (H : ∀ (V : P.scheme.Object μ hμ.1.1)
      (inclV : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ V))
      (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ V)),
      AllDominated inclV trivial bIdx b' →
      SameGaloisType (asTuple incl trivial b) (asTuple inclV trivial b')
        (Equiv.refl bIdx) (Equiv.refl bIdx) →
      ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem _ Y) (P.scheme.asSystem _ V),
        SystemArrow.comp incl h = inclV ∧ ∀ i, h.mapOcc (b i) = b' i) :
    AllDominated incl trivial bIdx b := by
  obtain ⟨V, f, hf, b', hD, hS⟩ := infra_79_existence_at P
    ⟨infra_79_tail P, infra_79_retraction_pair P⟩ hμ X (asTuple incl trivial b)
    (inferInstanceAs (Finite bIdx))
  obtain ⟨h, hh, hb⟩ := H V f b' hD hS
  have hb' : b' = fun i => h.mapOcc (b i) := (funext hb).symm
  subst hb' hh
  exact infra_83_dominated_pull P incl trivial h b
    ((Cardinal.lt_aleph0_of_finite _).trans (P.aleph0_lt hμ.1.1)) hD
end


section
variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 3200000 in
/-- **Lemma 8.3 (P.scheme) reduced to realization plus constructive primeness (proved
reduction).** `Lemma83Conclusion` holds for the constructed pair template once, at every
closed-tail well-order `I`, the template mark realizes the prescribed type and `Y_I` maps over
`X_I` (carrying the mark) into every all-dominated realization of the mark's type at level `#I`
(`infra_83_dominated_of_primeness_at`): no bound on the width of the dominated tuples. -/
theorem infra_83_full_single_of_primeness (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (X Y : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        P.scheme.Object #I hI)
      (incl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        SystemArrow K oneVertexShape (P.scheme.asSystem hI (X I hI))
          (P.scheme.asSystem hI (Y I hI)))
      (mk : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
        Fin Pr.n → Occurrence K oneVertexShape (P.scheme.asSystem hI (Y I hI))),
      (∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
          (hI : #I ∈ infra_78_closedTail P ∩ infra_615_closed P),
          (∃ realEq : ULift.{u} (Fin Pr.n) ≃ (Pr.assign hI.2.1 (X I hI.2.1)).idx,
            SameGaloisType (asTuple (incl I hI.2.1) trivial
              (fun a : ULift.{u} (Fin Pr.n) => mk I hI.2.1 a.down))
              (Pr.assign hI.2.1 (X I hI.2.1)) realEq (Equiv.refl _)) ∧
          ∀ (V : P.scheme.Object #I hI.2.1)
            (inclV : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 (X I hI.2.1))
              (P.scheme.asSystem hI.2.1 V))
            (b' : ULift.{u} (Fin Pr.n) → Occurrence K oneVertexShape (P.scheme.asSystem hI.2.1 V)),
            AllDominated inclV trivial (ULift.{u} (Fin Pr.n)) b' →
            SameGaloisType (asTuple (incl I hI.2.1) trivial
                (fun a : ULift.{u} (Fin Pr.n) => mk I hI.2.1 a.down))
              (asTuple inclV trivial b') (Equiv.refl _) (Equiv.refl _) →
            ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem hI.2.1 (Y I hI.2.1))
                (P.scheme.asSystem hI.2.1 V),
              SystemArrow.comp (incl I hI.2.1) h = inclV ∧
              ∀ a, h.mapOcc (mk I hI.2.1 a.down) = b' a) →
      Lemma83Conclusion P.scheme Pr := by
  obtain ⟨F, X, Y, eX, eY, incl, mk, hincl, harr⟩ := infra_83_pair_template_clauses P Pr
  refine ⟨X, Y, incl, mk, fun hS => ?_⟩
  refine infra_83_conclusion_of_marked_values_idx P Pr F X Y eX eY incl mk hincl harr _
    (infra_83_closed_tail P) (fun I _ _ _ hI => ?_)
  obtain ⟨⟨realEq, hr⟩, hprime⟩ := hS I hI
  exact ⟨ULift.{u} (Fin Pr.n), Equiv.refl _, realEq, hr,
    infra_83_dominated_of_primeness_at P hI (incl I hI.2.1) _ hprime⟩
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **A piece `Y_u ≅ F(Z_u)` on a support set holding given points (proved).** For `Y'`
identified with `F(Z)` by `φ`, a support set `S ⊆ Z` with `#S = ν` (a level), `φ ∘ incl'` landing in
`F(S)`, and points `w` of `Y'` whose `φ`-images lie in `F(S)` (their supports are in `S`), there is a
piece `X' ≤ Y_u ≤ Y'` with a strong onto `ψY : Y_u → F(S)`, `φ ∘ j = F(S ↪ Z) ∘ ψY`, holding every
`w i` (`infra_83_piece_of_suborder`, `card_obj_eq`). -/
theorem infra_83_piece_of_support (P : SingleModelData K) {ν : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {X' Y' : P.scheme.Object ν hν}
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Y'))
    {Z : Type u} [LinearOrder Z] [Nonempty Z]
    (φ : ((P.scheme.asSystem hν Y').obj PUnit.unit).carrier ≃[K.τ] (P.E.obj Z).carrier)
    (S : Set Z) [Nonempty S] (hS : #S = ν)
    (hsub : ∀ x, φ (incl'.onVertex PUnit.unit x) ∈
      Set.range (P.E.map (OrderEmbedding.subtype (fun z => z ∈ S))))
    {ι : Type u} (w : ι → ((P.scheme.asSystem hν Y').obj PUnit.unit).carrier)
    (hw : ∀ i, φ (w i) ∈ Set.range (P.E.map (OrderEmbedding.subtype (fun z => z ∈ S)))) :
    ∃ (Yu : P.scheme.Object ν hν)
      (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
      (j : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem hν Y'))
      (ψY : Language.Embedding K.τ ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier
        (P.E.obj S).carrier),
      K.Strong ψY ∧ SystemArrow.comp inclu j = incl' ∧
      (∀ y, φ (j.onVertex PUnit.unit y) =
        P.E.map (OrderEmbedding.subtype (fun z => z ∈ S)) (ψY y)) ∧
      ∀ i, ∃ y, j.onVertex PUnit.unit y = w i := by
  obtain ⟨Yu, inclu, j, ψY, hψ, hsurj, hj, hφ⟩ := infra_83_piece_of_suborder P incl' φ
    (OrderEmbedding.subtype (fun z => z ∈ S)) (SingleModelData.card_obj_eq hν S hS) hsub
  refine ⟨Yu, inclu, j, ψY, hψ, hj, hφ, fun i => ?_⟩
  obtain ⟨z, hz⟩ := hw i
  obtain ⟨y, rfl⟩ := hsurj z
  exact ⟨y, φ.injective (by rw [hφ, hz])⟩
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **Finite supports in `F(Z)` (proved).** Every element of an order presentation value `F(Z)`
has a finite support `s ⊆ Z`: it lies in `F(S)` (image under `F(S ↪ Z)`) for every nonempty
`S ⊇ s` (`realize_surjective`, `realize_map`). This supplies the support sets of
`infra_83_piece_of_support` for a bounded list (union of the supports of its entries and of
`J_I`'s image). -/
theorem infra_83_finite_support (E : OrderPresentation K) {Z : Type u} [LinearOrder Z]
    [Nonempty Z] (x : (E.obj Z).carrier) :
    ∃ s : Finset Z, ∀ (S : Set Z) [Nonempty S], (↑s : Set Z) ⊆ S →
      x ∈ Set.range (E.map (OrderEmbedding.subtype (fun z => z ∈ S))) := by
  classical
  obtain ⟨t, rfl⟩ := E.realize_surjective x
  refine ⟨Finset.univ.image t.pos, fun S _ hS => ?_⟩
  have hmem : ∀ a, t.pos a ∈ S := fun a =>
    hS (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ a)))
  let t' : SupportTerm E.lab E.arity S :=
    ⟨t.label, fun a => ⟨t.pos a, hmem a⟩, fun a b hab => t.increasing hab⟩
  refine ⟨E.realize t', ?_⟩
  rw [E.realize_map]
  rfl
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **A support set of size `ν` for a base set and at most `ν` points (proved).** For `T ⊆ Z` with
`#T = ν ≥ ℵ₀` and at most `ν` elements `x i` of `F(Z)`, there is `S ⊇ T` with `#S = ν` and every
`x i ∈ F(S)`: the support set of `infra_83_piece_of_support` for `T` the support of `X_I` and `x`
the entries of `(mk_I, c)` (`infra_83_finite_support`). -/
theorem infra_83_support_set (E : OrderPresentation K) {Z : Type u} [LinearOrder Z]
    [Nonempty Z] {ν : Cardinal.{u}} (hν : ℵ₀ ≤ ν) (T : Set Z) (hT : #T = ν)
    {ι : Type u} (hι : #ι ≤ ν) (x : ι → (E.obj Z).carrier) :
    ∃ (S : Set Z) (_ : Nonempty S), T ⊆ S ∧ #S = ν ∧
      ∀ i, x i ∈ Set.range (E.map (OrderEmbedding.subtype (fun z => z ∈ S))) := by
  classical
  choose s hs using fun i => infra_83_finite_support E (x i)
  let S : Set Z := T ∪ ⋃ i, (↑(s i) : Set Z)
  have hTne : Nonempty T := by
    rw [← Cardinal.mk_ne_zero_iff, hT]
    exact (Cardinal.aleph0_pos.trans_le hν).ne'
  have hne : Nonempty S := ⟨⟨hTne.some.1, Or.inl hTne.some.2⟩⟩
  have hcard : #S = ν := by
    apply le_antisymm
    · have hU : #(⋃ i, (↑(s i) : Set Z)) ≤ ν :=
        calc #(⋃ i, (↑(s i) : Set Z)) ≤ #ι * ⨆ i, #(↑(s i) : Set Z) := Cardinal.mk_iUnion_le _
          _ ≤ ν * ν := mul_le_mul' hι
            (ciSup_le' fun i => (Cardinal.lt_aleph0_of_finite _).le.trans hν)
          _ = ν := Cardinal.mul_eq_self hν
      calc #S ≤ #T + #(⋃ i, (↑(s i) : Set Z)) := Cardinal.mk_union_le _ _
        _ ≤ ν + ν := add_le_add hT.le hU
        _ = ν := Cardinal.add_eq_self hν
    · rw [← hT]
      exact Cardinal.mk_le_mk_of_subset Set.subset_union_left
  refine ⟨S, hne, Set.subset_union_left, hcard, fun i => ?_⟩
  exact hs i S fun z hz => Or.inr (Set.mem_iUnion.mpr ⟨i, hz⟩)
end


section
variable {K : AbstractElementaryClass.{u}}

/-- **An `F(Z_u)` piece for one bounded list (proved).** For `Y'` identified with `F(Z)` by `φ`,
a set `T ⊆ Z` with `#T = ν` such that `φ ∘ incl'` lands in `F(T)`, and a tuple `w` of at most `ν`
occurrences of `Y'` (e.g. `seqJoint b c`), there are `S ⊇ T` with `#S = ν`, a piece
`X' ≤ Y_u ≤ Y'` with a strong `ψY : Y_u → F(S)`, `φ ∘ j = F(S ↪ Z) ∘ ψY`, and a preimage `d` of
`w` in `Y_u`: inputs (ii) and the piece clauses for the paper's `Y_H ≅ F(Z_H)`. -/
theorem infra_83_FZ_piece_for_list (P : SingleModelData K) {ν : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {X' Y' : P.scheme.Object ν hν}
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Y'))
    {Z : Type u} [LinearOrder Z] [Nonempty Z]
    (φ : ((P.scheme.asSystem hν Y').obj PUnit.unit).carrier ≃[K.τ] (P.E.obj Z).carrier)
    (T : Set Z) [Nonempty T] (hT : #T = ν)
    (hsub : ∀ x, φ (incl'.onVertex PUnit.unit x) ∈
      Set.range (P.E.map (OrderEmbedding.subtype (fun z => z ∈ T))))
    {idx : Type u} (w : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν Y'))
    (hidx : #idx ≤ ν) :
    ∃ (S : Set Z) (_ : Nonempty S) (Yu : P.scheme.Object ν hν)
      (inclu : SystemArrow K oneVertexShape (P.scheme.asSystem hν X') (P.scheme.asSystem hν Yu))
      (j : SystemArrow K oneVertexShape (P.scheme.asSystem hν Yu) (P.scheme.asSystem hν Y'))
      (ψY : Language.Embedding K.τ ((P.scheme.asSystem hν Yu).obj PUnit.unit).carrier
        (P.E.obj S).carrier)
      (d : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν Yu)),
      T ⊆ S ∧ K.Strong ψY ∧ SystemArrow.comp inclu j = incl' ∧
      (∀ y, φ (j.onVertex PUnit.unit y) =
        P.E.map (OrderEmbedding.subtype (fun z => z ∈ S)) (ψY y)) ∧
      ∀ i, j.mapOcc (d i) = w i := by
  obtain ⟨S, hne, hTS, hS, hx⟩ := infra_83_support_set P.E (P.aleph0_le hν) T hT hidx
    (fun i => φ (w i).2)
  have hsubS : ∀ x, φ (incl'.onVertex PUnit.unit x) ∈
      Set.range (P.E.map (OrderEmbedding.subtype (fun z => z ∈ S))) := by
    intro x
    obtain ⟨y, hy⟩ := hsub x
    let ι : T ↪o S := ⟨⟨fun t => ⟨t.1, hTS t.2⟩, by
      intro a b h; apply Subtype.ext; exact congrArg (fun p : S => (p : Z)) h⟩,
      Iff.rfl⟩
    refine ⟨P.E.map ι y, ?_⟩
    rw [← hy]
    have : ι.trans (OrderEmbedding.subtype (fun z => z ∈ S)) =
        OrderEmbedding.subtype (fun z => z ∈ T) := by
      ext t; rfl
    rw [← this, P.E.map_comp]
    rfl
  obtain ⟨Yu, inclu, j, ψY, hψ, hj, hφ, hcov⟩ :=
    infra_83_piece_of_support P incl' φ S hS hsubS (fun i => (w i).2) hx
  choose y hy using hcov
  refine ⟨S, hne, Yu, inclu, j, ψY, fun i => ⟨PUnit.unit, y i⟩, hTS, hψ, hj, hφ, fun i => ?_⟩
  apply Sigma.ext
  · exact Subsingleton.elim _ _
  · exact heq_of_eq (hy i)
end

end AEC
