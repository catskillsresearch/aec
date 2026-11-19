module

public import AEC.Section8.Lemma83Assembly
public import AEC.Section7.TiedDescent
public import AEC.Section6.DescentRetractionTied
public import AEC.Section7.Theorem79Existence

@[expose] public section

/-!
# Lemma 8.3 (P.scheme): "the actual sample pair is all-dominated" — isolation descends to pairs

English (proof of Lemma 8.3, "The actual sample pair is all-dominated"): "Apply Lemma 7.6 to (7);
its fragment bound is below λ by closure. It follows that tp(b, c/X_H) is isolated relative to b."
Here (7) is the statement that the type of the image `u_* = (b', c')` over the larger base is the
(tied) free extension of `tp(u/X_H)`.

`infra_83_isolation_descend_pair`: for an arrow of pairs `(X ≤ Y) → (X' ≤ Y')` at one level (of
the Lemma 7.6 tail for the bound `σ`) carrying the tuple `b` to the mark `b'`, with `Y'`
all-dominated over `X' + b'`, every `σ`-bounded tuple `c` from `Y` whose image lift is tied-free
(the (7) hypothesis) has `tp(b, c / X)` isolated relative to `b`.
-/

universe u

open Cardinal FirstOrder
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Isolation descends along an arrow of pairs (Lemma 7.6 applied to (7)).** -/
theorem infra_83_isolation_descend_pair (P : SingleModelData K) (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (X Y X' Y' : P.scheme.Object μ (Tail.mem hT hμ))
        (incl : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y))
        (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem _ X')
          (P.scheme.asSystem _ Y'))
        (onX : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ X'))
        (onY : SystemArrow K oneVertexShape (P.scheme.asSystem _ Y) (P.scheme.asSystem _ Y')),
        SystemArrow.comp incl onY = SystemArrow.comp onX incl' →
        ∀ {bIdx cIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y))
          (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y))
          (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y')),
          (∀ i, onY.mapOcc (b i) = b' i) →
          #(bIdx ⊕ cIdx) ≤ σ → #cIdx < μ →
          AllDominated incl' trivial bIdx b' →
          IsTiedFree onX (asTuple incl trivial (seqJoint b c))
            (asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j))))
            (Equiv.refl _) →
          IsRelativelyIsolated (asTuple incl trivial (seqJoint b c)) (Equiv.refl _) := by
  obtain ⟨T, hT, H⟩ := lemma_7_6_tied P σ hσ
  refine ⟨T, hT, fun μ hμ X Y X' Y' incl incl' onX onY hcomm bIdx cIdx b c b' hb hcard hc
    hdom htied => ?_⟩
  have hIso := hdom cIdx (fun j => onY.mapOcc (c j)) hc
  have hSGT : SameGaloisType (asTuple incl trivial (seqJoint b c))
      ((asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j)))).restrict onX trivial)
      (Equiv.refl _) (Equiv.refl _) := by
    refine ⟨μ, Tail.mem hT hμ, Y', onY, SystemArrow.refl _, trivial, trivial, fun v => ?_,
      fun s => ?_⟩
    · exact congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex v) hcomm
    · rcases s with i | j
      · exact hb i
      · rfl
  exact H μ hμ X X' onX trivial (asTuple incl trivial (seqJoint b c))
    (asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j)))) (Equiv.refl _)
    (Equiv.refl (bIdx ⊕ cIdx)) rfl rfl hcard hSGT htied hIso

/-- **All-domination descends along an arrow of pairs given (7) for every bounded tuple.** At a
level `μ` closed for Lemma 7.6 at every infinite bound below `μ`, if `(onX, onY)` is an arrow of
pairs at level `μ` carrying `b` to the mark `b'` of a pair all-dominated over `X' + b'`, and every
bounded tuple `c` from `Y` has a tied-free lift (the free-extension statement (7) of the proof of
Lemma 8.3), then `Y` is all-dominated over `X + b`. -/
theorem infra_83_dominated_descend_pair (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible)
    (hlev : ∀ σ : Cardinal.{u}, ℵ₀ ≤ σ → σ < μ →
      μ ∈ infra_73_tailSet P (infra_76_sigma2 P σ))
    {X Y X' Y' : P.scheme.Object μ hμ}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X') (P.scheme.asSystem hμ Y'))
    (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ X'))
    (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ Y'))
    (hcomm : SystemArrow.comp incl onY = SystemArrow.comp onX incl')
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y'))
    (hb : ∀ i, onY.mapOcc (b i) = b' i) (hbμ : #bIdx < μ)
    (hdom : AllDominated incl' trivial bIdx b')
    (htied : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      #cIdx < μ →
      IsTiedFree onX (asTuple incl trivial (seqJoint b c))
        (asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j)))) (Equiv.refl _)) :
    AllDominated incl trivial bIdx b := by
  intro cIdx c hc
  have hlt : ℵ₀ < μ := P.aleph0_lt hμ
  have hsum : #(bIdx ⊕ cIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hlt.le hbμ hc
  set σ : Cardinal.{u} := max ℵ₀ #(bIdx ⊕ cIdx)
  have hσ : ℵ₀ ≤ σ := le_max_left _ _
  have hσμ : σ < μ := max_lt hlt hsum
  have hIso := hdom cIdx (fun j => onY.mapOcc (c j)) hc
  have hSGT : SameGaloisType (asTuple incl trivial (seqJoint b c))
      ((asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j)))).restrict onX trivial)
      (Equiv.refl _) (Equiv.refl _) := by
    refine ⟨μ, hμ, Y', onY, SystemArrow.refl _, trivial, trivial, fun v => ?_, fun s => ?_⟩
    · exact congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex v) hcomm
    · rcases s with i | j
      · exact hb i
      · rfl
  exact infra_76_tied_descent P σ hσ (hlev σ hσ hσμ) onX trivial
    (asTuple incl trivial (seqJoint b c))
    (asTuple incl' trivial (seqJoint b' (fun j => onY.mapOcc (c j)))) (Equiv.refl _)
    (Equiv.refl (bIdx ⊕ cIdx)) rfl rfl (le_max_right _ _) hSGT (htied cIdx c hc) hIso

/-- At one level, mixed tied freeness is tied freeness (the two definitions coincide). -/
theorem infra_83_tiedFree_of_mixed {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B) (e : q.idx ≃ qB.idx)
    (h : IsTiedFreeMixed f q qB e) : IsTiedFree f q qB e := h

/-- **All-domination of a pair from a retraction family on an all-dominated pair (Lemma 8.3,
"bounded horizontal arity" (7) + "the actual sample pair is all-dominated").** At a level `μ`
closed for Corollary 6.15/6.16 and for Lemma 7.6 below `μ`, let `(onX, onY) : (X ≤ Y) → (X' ≤ Y')`
be an arrow of pairs carrying `b` to the mark `b'`, with `Y'` all-dominated over `X' + b'`, and
let `r_i : Y' → X'` (`|ι| = μ`) be retractions each moving any point of `X'` at only finitely many
indices and mapping the image of `Y` into the image of `X`. Then every bounded tuple from `Y`
has a tied-free lift (Lemma 6.17, giving (7)), so by Lemma 7.6 `Y` is all-dominated over `X + b`. -/
theorem infra_83_dominated_of_retraction_pair (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμC : μ ∈ infra_615_closed P)
    (hlev : ∀ σ : Cardinal.{u}, ℵ₀ ≤ σ → σ < μ →
      μ ∈ infra_73_tailSet P (infra_76_sigma2 P σ))
    {X Y X' Y' : P.scheme.Object μ hμC.1}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 X)
      (P.scheme.asSystem hμC.1 Y))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 X')
      (P.scheme.asSystem hμC.1 Y'))
    (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 X)
      (P.scheme.asSystem hμC.1 X'))
    (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 Y)
      (P.scheme.asSystem hμC.1 Y'))
    (hcomm : SystemArrow.comp incl onY = SystemArrow.comp onX incl')
    {ι : Type u}
    (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 Y')
      (P.scheme.asSystem hμC.1 X'))
    (hιcard : #ι = μ)
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 X'),
      Finite {i : ι // (r i).onVertex a.1 (incl'.onVertex a.1 a.2) ≠ a.2})
    (himg : ∀ i (x : Y.model.carrier),
      ∃ y : X.model.carrier,
        onX.onVertex PUnit.unit y = (r i).onVertex PUnit.unit (onY.onVertex PUnit.unit x))
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y'))
    (hb : ∀ i, onY.mapOcc (b i) = b' i) (hbμ : #bIdx < μ)
    (hdom : AllDominated incl' trivial bIdx b') :
    AllDominated incl trivial bIdx b := by
  refine infra_83_dominated_descend_pair P hμC.1 hlev incl incl' onX onY hcomm b b' hb hbμ hdom
    (fun cIdx c hc => ?_)
  have hsq : ∀ v, (incl'.onVertex v).comp (onX.onVertex v) =
      (onY.onVertex v).comp (incl.onVertex v) := fun v =>
    (congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex v) hcomm).symm
  have hsum : #(bIdx ⊕ cIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_lt hμC.1).le hbμ hc
  have H := infra_617_tied_from_retractions P hμC hμC le_rfl X' Y' X Y onX onY incl' incl
    trivial trivial trivial trivial hsq r hιcard halmost himg (seqJoint b c) hsum
  have hx : (fun j => (⟨(seqJoint b c j).1, onY.onVertex (seqJoint b c j).1 (seqJoint b c j).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y'))) =
      seqJoint b' (fun j => onY.mapOcc (c j)) := by
    funext s
    rcases s with i | j
    · exact hb i
    · rfl
  rw [hx] at H
  exact infra_83_tiedFree_of_mixed _ _ _ _ H

/-- **All-domination of a pair from a retraction-carrying arrow into a larger all-dominated pair,
across levels (Lemma 8.3 proof, (7) + "the actual sample pair is all-dominated").** A pair
`X ≤ Y` at a closed level `ν` with an arrow of pairs `(onX, onY)` into a pair `X' ≤ Y'` at a closed
level `l ≥ ν`, carrying the finite tuple `b` to the mark `b'`, where `Y'` is all-dominated over
`X' + b'` and `ν` retractions `r_i : Y' → X'` almost fix `X'` and send the image of `Y` into the
image of `X`: then `Y` is all-dominated over `X + b`. This is Theorem 7.9's descent step
(`infra_79_descent`: Lemma 6.17 tied + mixed Lemma 7.6) with the isolation input read off from the
all-domination of the larger pair. -/
theorem infra_83_dominated_of_retraction_pair_mixed (P : SingleModelData K) {ν l : Cardinal.{u}}
    (hνC : ν ∈ infra_615_closed P) (hlC : l ∈ infra_615_closed P)
    (hνT : ν ∈ infra_78_closedTail P) (hlT : l ∈ infra_78_closedTail P) (hνl : ν ≤ l)
    {X Y : P.scheme.Object ν hνC.1} {X' Y' : P.scheme.Object l hlC.1}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X)
      (P.scheme.asSystem hνC.1 Y))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hlC.1 X')
      (P.scheme.asSystem hlC.1 Y'))
    (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X)
      (P.scheme.asSystem hlC.1 X'))
    (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 Y)
      (P.scheme.asSystem hlC.1 Y'))
    (hcomm : SystemArrow.comp incl onY = SystemArrow.comp onX incl')
    {ι : Type u}
    (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem hlC.1 Y')
      (P.scheme.asSystem hlC.1 X'))
    (hιcard : #ι = ν)
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 X'),
      Finite {i : ι // (r i).onVertex a.1 (incl'.onVertex a.1 a.2) ≠ a.2})
    (himg : ∀ i (x : Y.model.carrier),
      ∃ y : X.model.carrier,
        onX.onVertex PUnit.unit y = (r i).onVertex PUnit.unit (onY.onVertex PUnit.unit x))
    {bIdx : Type u} [Finite bIdx]
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 Y'))
    (hb : ∀ i, onY.mapOcc (b i) = b' i)
    (hdom : AllDominated incl' trivial bIdx b') :
    AllDominated incl trivial bIdx b := by
  have hsq : ∀ v, (incl'.onVertex v).comp (onX.onVertex v) =
      (onY.onVertex v).comp (incl.onVertex v) := fun v =>
    (congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex v) hcomm).symm
  exact infra_79_descent P hνC hlC hνT hlT hνl X' Y' X Y onX onY incl' incl trivial trivial
    trivial trivial hsq r hιcard (fun _ => trivial) halmost himg b b' (fun k => (hb k).symm)
    (fun c hJ => hdom _ c (hJ.trans_le hνl))

/-- **A pair mapping into a marked sample pair with a retraction family is marked (Lemma 8.3).**
For `X ≤ Y` with finite tuple `b` at a closed level `ν`, a marked pair `N` at a closed level
`l ≥ ν`, an arrow of pairs `(onX, onY)` carrying `b` to `N.b` and `ν` retractions
`r_i : N.Y → N.X` almost fixing `N.X` and sending the image of `Y` into the image of `X`: `b`
realizes `p_X` (some position identification; `infra_83_realizes_descend`) and `Y` is
all-dominated over `X + b` (`infra_83_dominated_of_retraction_pair_mixed`). -/
theorem infra_83_marked_of_sample_arrow (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {ν : Cardinal.{u}}
    (hνC : ν ∈ infra_615_closed P) (hνT : ν ∈ infra_78_closedTail P)
    {X Y : P.scheme.Object ν hνC.1}
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X)
      (P.scheme.asSystem hνC.1 Y))
    (N : MarkedPair K oneVertexShape P.scheme Pr)
    (hlC : N.μ ∈ infra_615_closed P) (hlT : N.μ ∈ infra_78_closedTail P) (hνl : ν ≤ N.μ)
    (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X)
      (P.scheme.asSystem N.hμ N.X))
    (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 Y)
      (P.scheme.asSystem N.hμ N.Y))
    (hcomm : SystemArrow.comp incl onY = SystemArrow.comp onX N.incl)
    {ι : Type u}
    (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem N.hμ N.Y)
      (P.scheme.asSystem N.hμ N.X))
    (hιcard : #ι = ν)
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.X),
      Finite {i : ι // (r i).onVertex a.1 (N.incl.onVertex a.1 a.2) ≠ a.2})
    (himg : ∀ i (x : Y.model.carrier),
      ∃ y : X.model.carrier,
        onX.onVertex PUnit.unit y = (r i).onVertex PUnit.unit (onY.onVertex PUnit.unit x))
    (b : N.bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y))
    (hb : ∀ i, onY.mapOcc (b i) = N.b i) :
    (∃ realEq : N.bIdx ≃ (Pr.assign hνC.1 X).idx,
      SameGaloisType (asTuple incl trivial b) (Pr.assign hνC.1 X) realEq (Equiv.refl _)) ∧
    AllDominated incl trivial N.bIdx b := by
  have hfin : Finite N.bIdx := Finite.of_equiv _ (N.realEq.trans (Pr.arity N.hμ N.X)).symm
  refine ⟨infra_83_realizes_descend P Pr incl N.incl onX onY hcomm b N.b (Equiv.refl _) hb
    N.realEq N.realizes, ?_⟩
  obtain ⟨μ, hμ, NX, NY, nincl, hni, bIdx, nb, rE, hr, hd⟩ := N
  exact infra_83_dominated_of_retraction_pair_mixed P hνC hlC hνT hlT hνl incl nincl onX onY
    hcomm r hιcard halmost himg b nb hb hd

/-- **Assembly with per-value mark indexing (proved).** As `infra_83_conclusion_of_marked_values`,
but the value at `I` may index its marks by any type `bIdx_I` identified with the mark positions
(`σ_I : bIdx_I ≃ Fin n`), as for the marks of the sample pairs. -/
theorem infra_83_conclusion_of_marked_values_idx (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (F : TermTemplate K oneVertexShape.{u}.doubled)
    (X Y : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
      P.scheme.Object #I hI)
    (eX : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible) v,
      ((F.present I).obj (Sum.inl v)).carrier ≃[K.τ]
        ((P.scheme.asSystem hI (X I hI)).obj v).carrier)
    (eY : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible) v,
      ((F.present I).obj (Sum.inr v)).carrier ≃[K.τ]
        ((P.scheme.asSystem hI (Y I hI)).obj v).carrier)
    (incl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
      SystemArrow K oneVertexShape (P.scheme.asSystem hI (X I hI))
        (P.scheme.asSystem hI (Y I hI)))
    (mk : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
      Fin Pr.n → Occurrence K oneVertexShape (P.scheme.asSystem hI (Y I hI)))
    (hincl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible) v x,
      (incl I hI).onVertex v (eX I hI v x) =
        eY I hI v ((F.present I).edge
          (show (oneVertexShape.{u}).doubled.specified (Sum.inl v) (Sum.inr v) from rfl) x))
    (harr : ∀ (I J : Type u) [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J]
      (f : I ↪o J) (hI : #I ∈ P.eligible) (hJ : #J ∈ P.eligible),
      ∃ (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hI (X I hI))
          (P.scheme.asSystem hJ (X J hJ)))
        (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hI (Y I hI))
          (P.scheme.asSystem hJ (Y J hJ))),
        SystemArrow.comp (incl I hI) onY = SystemArrow.comp onX (incl J hJ) ∧
        (∀ v x, onX.onVertex v (eX I hI v x) =
          eX J hJ v ((F.onOrder f).onVertex (Sum.inl v) x)) ∧
        (∀ v x, onY.onVertex v (eY I hI v x) =
          eY J hJ v ((F.onOrder f).onVertex (Sum.inr v) x)) ∧
        ∀ i, (⟨(mk I hI i).1, onY.onVertex (mk I hI i).1 (mk I hI i).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hJ (Y J hJ))) = mk J hJ i)
    (T : Set Cardinal.{u}) (hT : Tail P.scheme.eligible T)
    (hmark : ∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I] (hI : #I ∈ T),
      ∃ (bIdx : Type u) (σ : bIdx ≃ ULift.{u} (Fin Pr.n))
        (realEq : bIdx ≃ (Pr.assign (Tail.mem hT hI) (X I (Tail.mem hT hI))).idx),
        SameGaloisType (asTuple (incl I (Tail.mem hT hI)) trivial
            (fun j => mk I (Tail.mem hT hI) (σ j).down))
          (Pr.assign (Tail.mem hT hI) (X I (Tail.mem hT hI))) realEq (Equiv.refl _) ∧
        AllDominated (incl I (Tail.mem hT hI)) trivial bIdx
          (fun j => mk I (Tail.mem hT hI) (σ j).down)) :
    Lemma83Conclusion P.scheme Pr := by
  classical
  choose bI σI rEI hr hd using hmark
  let val : (I : Type u) → [LinearOrder I] → [WellFoundedLT I] → [Nonempty I] →
      #I ∈ T → MarkedPair K oneVertexShape P.scheme Pr := fun I _ _ _ hI =>
    ⟨#I, Tail.mem hT hI, X I (Tail.mem hT hI), Y I (Tail.mem hT hI), incl I (Tail.mem hT hI),
      trivial, bI I hI, fun j => mk I (Tail.mem hT hI) (σI I hI j).down, rEI I hI,
      hr I hI, hd I hI⟩
  refine ⟨F, T, hT, val, fun I _ _ _ hI => eX I (Tail.mem hT hI),
    fun I _ _ _ hI => eY I (Tail.mem hT hI),
    fun I _ _ _ hI => ⟨rfl, fun v x => hincl I (Tail.mem hT hI) v x,
      fun _ _ h => h.elim, fun _ _ h => h.elim⟩,
    fun I J _ _ _ _ _ _ f hI hJ => ?_,
    infra_83_clause3_single P Pr T val (fun _ _ _ _ _ => rfl)⟩
  obtain ⟨onX, onY, hc, hX, hY, hm⟩ := harr I J f (Tail.mem hT hI) (Tail.mem hT hJ)
  refine ⟨⟨onX, onY, trivial, trivial, hc, (σI I hI).trans (σI J hJ).symm, fun j => ?_⟩, hX, hY⟩
  refine (hm _).trans ?_
  show mk J _ _ = mk J _ ((σI J hJ) ((σI J hJ).symm _)).down
  rw [Equiv.apply_symm_apply]

/-- **Lemma 8.3 (P.scheme) reduced to arrows into marked samples (proved reduction).** For the
constructed pair template (`infra_83_pair_template_clauses`), `Lemma83Conclusion` holds once every
value on a well-order `I` with `#I` in the Lemma 8.2 tail admits a mark-preserving arrow of pairs
into a marked pair `N` at a closed level `≥ #I` together with `#I` retractions `N.Y → N.X` almost
fixing `N.X` and sending the image of `Y_I` into the image of `X_I` — the paper's matching of the
value with an actual homogeneous sample ("bounded horizontal arity") with the Corollary 6.16
retractions of the sample (`infra_83_marked_of_sample_arrow`). -/
theorem infra_83_full_single_of_sample_arrows (P : SingleModelData K)
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
        ∃ (N : MarkedPair K oneVertexShape P.scheme Pr) (_ : N.μ ∈ infra_615_closed P)
          (_ : N.μ ∈ infra_78_closedTail P) (_ : #I ≤ N.μ)
          (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hI.1.1 (X I hI.1.1))
            (P.scheme.asSystem N.hμ N.X))
          (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hI.1.1 (Y I hI.1.1))
            (P.scheme.asSystem N.hμ N.Y))
          (ι : Type u) (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem N.hμ N.Y)
            (P.scheme.asSystem N.hμ N.X))
          (σ : N.bIdx ≃ ULift.{u} (Fin Pr.n)),
          SystemArrow.comp (incl I hI.1.1) onY = SystemArrow.comp onX N.incl ∧
          #ι = #I ∧
          (∀ a : Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.X),
            Finite {i : ι // (r i).onVertex a.1 (N.incl.onVertex a.1 a.2) ≠ a.2}) ∧
          (∀ i (x : (Y I hI.1.1).model.carrier), ∃ y : (X I hI.1.1).model.carrier,
            onX.onVertex PUnit.unit y = (r i).onVertex PUnit.unit (onY.onVertex PUnit.unit x)) ∧
          ∀ j, onY.mapOcc (mk I hI.1.1 (σ j).down) = N.b j) →
      Lemma83Conclusion P.scheme Pr := by
  obtain ⟨F, X, Y, eX, eY, incl, mk, hincl, harr⟩ := infra_83_pair_template_clauses P Pr
  refine ⟨X, Y, incl, mk, fun hS => ?_⟩
  refine infra_83_conclusion_of_marked_values_idx P Pr F X Y eX eY incl mk hincl harr _
    (infra_83_closed_tail P) (fun I _ _ _ hI => ?_)
  obtain ⟨N, hlC, hlT, hle, onX, onY, ι, r, σ, hc, hι, hal, him, hb⟩ := hS I hI
  obtain ⟨hR, hD⟩ := infra_83_marked_of_sample_arrow P Pr hI.2 hI.1 (incl I hI.1.1) N hlC hlT
    hle onX onY hc r hι hal him (fun j => mk I hI.1.1 (σ j).down) hb
  obtain ⟨realEq, hr⟩ := hR
  exact ⟨N.bIdx, σ, realEq, hr, hD⟩

/-- **Sub-families of an approximate retraction family (proved).** From a Corollary 6.16 family
`R` and a set of indices of size at least `ν`, one extracts a family of exactly `ν` retractions,
each a member of `R` with index in the set, still almost fixing the base. -/
theorem infra_83_retraction_subfamily {S : SystemShape.{u}} {W : WorkingScheme K S}
    {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {A B : W.Object μ hμ}
    {incl : SystemArrow K S (W.asSystem hμ A) (W.asSystem hμ B)}
    (R : ApproximateRetraction K S W hμ A B incl) (good : R.index → Prop) {ν : Cardinal.{u}}
    (hν : ν ≤ #{i // good i}) :
    ∃ (ι : Type u) (r : ι → SystemArrow K S (W.asSystem hμ B) (W.asSystem hμ A)),
      #ι = ν ∧
      (∀ a : Occurrence K S (W.asSystem hμ A),
        Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2}) ∧
      ∀ i, ∃ j, good j ∧ r i = R.retr j := by
  obtain ⟨s, hsub, hs⟩ := Cardinal.le_mk_iff_exists_subset.mp hν
  let g : s → R.index := fun i => i.1
  refine ⟨s, fun i => R.retr (g i), hs, fun a => ?_, fun i => ⟨g i, hsub i.2, rfl⟩⟩
  have := R.almost_id a
  have hg : Function.Injective g := fun x y h => Subtype.ext h
  refine Finite.of_injective
    (fun i : {i : s // (R.retr (g i)).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2} =>
      (⟨g i.1, i.2⟩ : {j : R.index // (R.retr j).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2}))
    ?_
  intro x y h
  exact Subtype.ext (hg (by simpa using congrArg Subtype.val h))

/-- **Lemma 8.3 (P.scheme) reduced to arrows into marked samples, Corollary 6.16 form (proved
reduction).** As `infra_83_full_single_of_sample_arrows`, with the retractions taken from an
approximate retraction family of the sample (Corollary 6.16, `infra_83_samples_retractions`): it
suffices that at least `#I` members of the family send the image of `Y_I` into the image of
`X_I`. -/
theorem infra_83_full_single_of_sample_families (P : SingleModelData K)
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
        ∃ (N : MarkedPair K oneVertexShape P.scheme Pr) (_ : N.μ ∈ infra_615_closed P)
          (_ : N.μ ∈ infra_78_closedTail P) (_ : #I ≤ N.μ)
          (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hI.1.1 (X I hI.1.1))
            (P.scheme.asSystem N.hμ N.X))
          (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hI.1.1 (Y I hI.1.1))
            (P.scheme.asSystem N.hμ N.Y))
          (R : ApproximateRetraction K oneVertexShape P.scheme N.hμ N.X N.Y N.incl)
          (σ : N.bIdx ≃ ULift.{u} (Fin Pr.n)),
          SystemArrow.comp (incl I hI.1.1) onY = SystemArrow.comp onX N.incl ∧
          #I ≤ #{i : R.index // ∀ x : (Y I hI.1.1).model.carrier, ∃ y : (X I hI.1.1).model.carrier,
            onX.onVertex PUnit.unit y = (R.retr i).onVertex PUnit.unit (onY.onVertex PUnit.unit x)} ∧
          ∀ j, onY.mapOcc (mk I hI.1.1 (σ j).down) = N.b j) →
      Lemma83Conclusion P.scheme Pr := by
  obtain ⟨X, Y, incl, mk, H⟩ := infra_83_full_single_of_sample_arrows P Pr
  refine ⟨X, Y, incl, mk, fun hS => H fun I _ _ _ hI => ?_⟩
  obtain ⟨N, hlC, hlT, hle, onX, onY, R, σ, hc, hgood, hb⟩ := hS I hI
  obtain ⟨ι, r, hι, hal, hr⟩ := infra_83_retraction_subfamily R _ hgood
  refine ⟨N, hlC, hlT, hle, onX, onY, ι, r, σ, hc, hι, hal, fun i x => ?_, hb⟩
  obtain ⟨j, hj, hrj⟩ := hr i
  rw [hrj]
  exact hj x

/-- **Good retraction indices from the retraction evaluation (proved).** English (Lemma 8.3 proof):
"Include a sort of retraction indices and an evaluation function for a family `r_i : Y → X`."
In a sample `X ≤ Y ↪ L` with evaluation `g` (`g(code_i, F y) = F(incl(r_i y))`,
`infra_83_ret_samples`), if the evaluation at `code_i` sends the image of `Y_I` into the image of
`X_I` then `r_i` does. -/
theorem infra_83_good_of_ret_eval {Xc Yc L XI YI : Type*} (incl : Xc → Yc)
    (hincl : Function.Injective incl) (F : Yc → L) (hF : Function.Injective F) (r : Yc → Xc)
    (onX : XI → Xc) (onY : YI → Yc) (g : L → L → L) (c : L)
    (hev : ∀ y, g c (F y) = F (incl (r y)))
    (h : ∀ x, ∃ y, g c (F (onY x)) = F (incl (onX y))) :
    ∀ x, ∃ y, onX y = r (onY x) := by
  intro x
  obtain ⟨y, hy⟩ := h x
  refine ⟨y, hincl (hF ?_)⟩
  rw [← hy, hev]

/-- **Lemma 8.3 (P.scheme) reduced to arrows into retraction-expanded samples (proved
reduction).** As `infra_83_full_single_of_sample_families`, with the good retraction indices
read off the evaluation function `g` of the retraction-expanded sample (`infra_83_ret_samples`):
it suffices that for at least `#I` indices `i` the evaluation `g(code_i, -)` sends the image of
`Y_I` in `L` into the image of `X_I`. -/
theorem infra_83_full_single_of_ret_evals (P : SingleModelData K)
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
        ∃ (N : MarkedPair K oneVertexShape P.scheme Pr) (_ : N.μ ∈ infra_615_closed P)
          (_ : N.μ ∈ infra_78_closedTail P) (_ : #I ≤ N.μ)
          (onX : SystemArrow K oneVertexShape (P.scheme.asSystem hI.1.1 (X I hI.1.1))
            (P.scheme.asSystem N.hμ N.X))
          (onY : SystemArrow K oneVertexShape (P.scheme.asSystem hI.1.1 (Y I hI.1.1))
            (P.scheme.asSystem N.hμ N.Y))
          (R : ApproximateRetraction K oneVertexShape P.scheme N.hμ N.X N.Y N.incl)
          (σ : N.bIdx ≃ ULift.{u} (Fin Pr.n)) (L : Type u)
          (F : ((P.scheme.asSystem N.hμ N.Y).obj PUnit.unit).carrier → L) (g : L → L → L)
          (code : R.index → L),
          SystemArrow.comp (incl I hI.1.1) onY = SystemArrow.comp onX N.incl ∧
          Function.Injective F ∧
          (∀ i y, g (code i) (F y) =
            F (N.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y))) ∧
          #I ≤ #{i : R.index // ∀ x : (Y I hI.1.1).model.carrier,
            ∃ y : (X I hI.1.1).model.carrier,
              g (code i) (F (onY.onVertex PUnit.unit x)) =
                F (N.incl.onVertex PUnit.unit (onX.onVertex PUnit.unit y))} ∧
          ∀ j, onY.mapOcc (mk I hI.1.1 (σ j).down) = N.b j) →
      Lemma83Conclusion P.scheme Pr := by
  obtain ⟨X, Y, incl, mk, H⟩ := infra_83_full_single_of_sample_families P Pr
  refine ⟨X, Y, incl, mk, fun hS => H fun I _ _ _ hI => ?_⟩
  obtain ⟨N, hlC, hlT, hle, onX, onY, R, σ, L, F, g, code, hc, hF, hev, hgood, hb⟩ := hS I hI
  refine ⟨N, hlC, hlT, hle, onX, onY, R, σ, hc, hgood.trans ?_, hb⟩
  exact Cardinal.mk_subtype_mono fun i hi =>
    infra_83_good_of_ret_eval _ (N.incl.onVertex PUnit.unit).injective F hF _ _ _ g (code i)
      (hev i) hi

/-- **Matching a template pair into a sample pair (proved).** English (Lemma 8.3 proof): the
partial matches of the template pieces into a homogeneous sample, made compatible, give the map
of the value pair `F_X(I) ≤ F_Y(I)` into the sample pair `M_X ≤ M_Y`. For piece functors
`F_X → F_Y` (`η`) and compatible strong families of piece embeddings `gX s : F_X(s) → M_X`,
`gY s : F_Y(s) → M_Y` with `gY s ∘ η_s = ι ∘ gX s`, there are strong embeddings of the EM
values extending them and commuting with `η` and `ι`. -/
theorem infra_83_pair_limit_desc {FX FY : EM83.FinPieces K} (η : EM83.PiecesHom FX FY)
    (I : Type u) [LinearOrder I] [Nonempty I] {MX MY : Model K.τ} (hMX : K.Mem MX)
    (hMY : K.Mem MY) (ι : MX.carrier ↪[K.τ] MY.carrier)
    (gX : ∀ s : (FX.system I).ι, ((FX.system I).obj s).carrier ↪[K.τ] MX.carrier)
    (gY : ∀ s : (FY.system I).ι, ((FY.system I).obj s).carrier ↪[K.τ] MY.carrier)
    (hgX : ∀ s, K.Strong (gX s)) (hgY : ∀ s, K.Strong (gY s))
    (hcX : ∀ {s t} (h : (FX.system I).rel s t), (gX t).comp ((FX.system I).map h) = gX s)
    (hcY : ∀ {s t} (h : (FY.system I).rel s t), (gY t).comp ((FY.system I).map h) = gY s)
    (hsq : ∀ (s : (FX.system I).ι) x, gY s (η.app s.1.card.pred x) = ι (gX s x)) :
    ∃ (onX : (FX.limit I).obj.carrier ↪[K.τ] MX.carrier)
      (onY : (FY.limit I).obj.carrier ↪[K.τ] MY.carrier),
      K.Strong onX ∧ K.Strong onY ∧
      (∀ s, onX.comp ((FX.limit I).canon s) = gX s) ∧
      (∀ s, onY.comp ((FY.limit I).canon s) = gY s) ∧
      ∀ x, onY (η.limMap I x) = ι (onX x) := by
  obtain ⟨onX, hsX, hX⟩ := (FX.limit_spec I).2.2 MX gX hMX hgX hcX
  obtain ⟨onY, hsY, hY⟩ := (FY.limit_spec I).2.2 MY gY hMY hgY hcY
  refine ⟨onX, onY, hsX, hsY, hX, hY, fun x => ?_⟩
  obtain ⟨s, y, rfl⟩ := (FX.limit I).joint x
  have h1 := congrFun (congrArg (⇑) (η.limMap_canon I s)) y
  have h2 := congrFun (congrArg (⇑) (hY s)) (η.app s.1.card.pred y)
  have h3 := congrFun (congrArg (⇑) (hX s)) y
  simp only [Language.Embedding.comp_apply, EM83.PiecesHom.cocone] at h1 h2 h3
  rw [h1]
  refine h2.trans ?_
  exact (hsq s y).trans (by rw [h3])

/-- **Hull elements are terms in the generators (proved).** -/
theorem infra_83_hull_mk_realize {L : FirstOrder.Language.{u, u}} {M : Type u} [L.Structure M] {ι : Type}
    (v : ι → M) (t : L.Term ι) :
    (Quotient.mk (Hull83.hullSetoid v) t : Hull83.Hull (L := L) v) =
      t.realize (fun p => (Quotient.mk (Hull83.hullSetoid v) (FirstOrder.Language.Term.var p) :
        Hull83.Hull (L := L) v)) := by
  apply Hull83.hullVal_injective (L := L) v
  rw [Hull83.hullVal_mk, ← Hull83.hullEmb_apply, ← FirstOrder.Language.HomClass.realize_term]
  rfl

/-- **Embeddings of a term hull are determined by the generators (proved).** English (Lemma 8.3
proof): the partial matches of the template pieces into a sample are determined by where the
skeleton goes; in particular the piece embeddings of `Hull83.piece_into_sample` for `s ⊆ t` are
compatible. -/
theorem infra_83_hull_emb_ext {L : FirstOrder.Language.{u, u}} {M N : Type u} [L.Structure M]
    [L.Structure N] {ι : Type} {v : ι → M} (f g : Hull83.Hull (L := L) v ↪[L] N)
    (h : ∀ p, f (Quotient.mk _ (FirstOrder.Language.Term.var p)) = g (Quotient.mk _ (FirstOrder.Language.Term.var p))) : f = g := by
  ext x
  induction x using Quotient.ind with
  | _ t =>
    rw [infra_83_hull_mk_realize v t, ← FirstOrder.Language.HomClass.realize_term,
      ← FirstOrder.Language.HomClass.realize_term]
    congr 1
    funext p
    exact h p

/-- **Compatibility of partial matches (proved).** Two hull embeddings into one sample `Q` whose
generator values agree along a position map `g` commute with the hull map along `g`: the
matches of the pieces on `s ⊆ t` into a homogeneous sample are compatible. -/
theorem infra_83_hull_match_compat {L : FirstOrder.Language.{u, u}} {M N Q : Type u}
    [L.Structure M] [L.Structure N] [L.Structure Q] {ι ι' : Type} {v' : ι' → N} {v : ι → M}
    (g : ι' → ι) (h : Hull83.tpCode (L := L) v' = Hull83.tpCode (v ∘ g))
    (fs : Hull83.Hull (L := L) v' ↪[L] Q) (ft : Hull83.Hull (L := L) v ↪[L] Q)
    (ws : ι' → Q) (wt : ι → Q)
    (hs : ∀ p, fs (Quotient.mk _ (FirstOrder.Language.Term.var p)) = ws p)
    (ht : ∀ p, ft (Quotient.mk _ (FirstOrder.Language.Term.var p)) = wt p)
    (hw : ∀ p, wt (g p) = ws p) :
    ft.comp (Hull83.hullMapEmb g h) = fs := by
  refine infra_83_hull_emb_ext _ _ fun p => ?_
  show ft (Quotient.mk _ (FirstOrder.Language.Term.var (g p))) = _
  rw [ht, hs, hw]

/-- **Enumerations along supports (proved).** The successor-length position map of `s ⊆ t`
commutes with the increasing enumerations of `s` and `t`. -/
theorem infra_83_orderEmbOfFin_placeSucc {α : Type*} [LinearOrder α] {s t : Finset α}
    (hst : s ⊆ t) (hs : s.Nonempty) (ht : t.Nonempty) (a : Fin (s.card.pred + 1))
    (h1 : s.card = s.card.pred + 1) (h2 : t.card = t.card.pred + 1) :
    t.orderEmbOfFin h2 (placeSucc hst hs ht a) = s.orderEmbOfFin h1 a := by
  have key := placeEmb_spec hst (Fin.cast h1.symm a)
  rw [Finset.orderEmbOfFin_apply, Finset.orderEmbOfFin_apply] at key ⊢
  simp only [Fin.getElem_fin, Fin.val_cast] at key ⊢
  have hv : ((placeSucc hst hs ht a) : ℕ) = (placeEmb hst (Fin.cast h1.symm a) : ℕ) := rfl
  simp only [hv]
  exact key

/-- **Sample bundles along supports (proved).** The bundles of a sample enumerated by `s ⊆ t`
agree along the position map: the generator values of the matches on `s` and `t` agree. -/
theorem infra_83_bundleOf_placeSucc {α : Type u} [LinearOrder α] {M : Type u} {r : ℕ}
    (base : α → Fin r → M) {s t : Finset α} (hst : s ⊆ t) (hs : s.Nonempty) (ht : t.Nonempty)
    (h1 : s.card = s.card.pred + 1) (h2 : t.card = t.card.pred + 1)
    (p : Fin (s.card.pred + 1) × Fin r) :
    Hull83.bundleOf base t h2 (Prod.map (placeSucc hst hs ht) id p) =
      Hull83.bundleOf base s h1 p := by
  simp only [Hull83.bundleOf, Prod.map_fst, Prod.map_snd, id_eq]
  rw [infra_83_orderEmbOfFin_placeSucc hst hs ht p.1 h1 h2]

/-- **Compatible partial matches of the template pieces into a homogeneous sample (proved).**
English (Lemma 8.3 proof): "the partial matches into a homogeneous sample". In a bundled sample
`S` (colors `tpCode` of the bundles) homogeneous in every arity for the template colors `c`, every
nonempty finite support `s` gives an embedding of the arity-`|s|` template piece into the sample
structure, sending the generators to the bundles enumerated by `s`; the embeddings are compatible
with the piece maps along `s ⊆ t`. -/
theorem infra_83_piece_matches {L : FirstOrder.Language.{u, u}}
    {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    {S : Hull83.ColorSample (Hull83.TpColorB L r)} {M : Type u} [L.Structure M]
    (base : S.α → Fin r → M)
    (hcol : ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m),
      S.col m s = Hull83.tpCode (Hull83.bundleOf base s h))
    (hhom : ∀ n, Hull83.Homog S n c) :
    ∃ m : ∀ s : {s : Finset S.α // s.Nonempty},
        Hull83.Hull (L := L) (Hull83.witB hc s.1.card.pred).v ↪[L] M,
      (∀ s p, m s (Quotient.mk _ (FirstOrder.Language.Term.var p)) =
        Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm p) ∧
      ∀ {s t : {s : Finset S.α // s.Nonempty}} (h : s.1 ⊆ t.1),
        (m t).comp (Hull83.hullMapEmb (Prod.map (placeSucc h s.2 t.2) id)
          (Hull83.tpPieceB_tp hc hcoh (placeSucc h s.2 t.2))) = m s := by
  have key : ∀ s : {s : Finset S.α // s.Nonempty}, ∃ f :
      Hull83.Hull (L := L) (Hull83.witB hc s.1.card.pred).v ↪[L] M, ∀ p,
        f (Quotient.mk _ (FirstOrder.Language.Term.var p)) =
          Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm p :=
    fun s => Hull83.piece_into_sample hc base hcol (hhom (s.1.card.pred + 1)) le_rfl s.1 _
  choose m hm using key
  refine ⟨m, hm, fun {s t} h => ?_⟩
  exact infra_83_hull_match_compat _ _ (m s) (m t) _ _ (hm s) (hm t)
    (fun p => infra_83_bundleOf_placeSucc base h s.2 t.2 _ _ p)

/-- **Compatible matches from bundle types (proved).** As `infra_83_piece_matches`, for any
ordered family of bundles `base : I → Fin r → M` whose finite enumerations all have the template
colors: the supports of `I` (the finite-support index of the EM system of `I`) give compatible
matches of the template pieces into `M`. -/
theorem infra_83_piece_matches_tp {L : FirstOrder.Language.{u, u}}
    {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    {I : Type u} [LinearOrder I] {M : Type u} [L.Structure M] (base : I → Fin r → M)
    (htp : ∀ (k : ℕ) (s : Finset I) (h : s.card = k + 1),
      Hull83.tpCode (L := L) (Hull83.bundleOf base s h) = c (k + 1) (Nat.succ_pos k)) :
    ∃ m : ∀ s : {s : Finset I // s.Nonempty},
        Hull83.Hull (L := L) (Hull83.witB hc s.1.card.pred).v ↪[L] M,
      (∀ s p, m s (Quotient.mk _ (FirstOrder.Language.Term.var p)) =
        Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm p) ∧
      ∀ {s t : {s : Finset I // s.Nonempty}} (h : s.1 ⊆ t.1),
        (m t).comp (Hull83.hullMapEmb (Prod.map (placeSucc h s.2 t.2) id)
          (Hull83.tpPieceB_tp hc hcoh (placeSucc h s.2 t.2))) = m s := by
  have key : ∀ s : {s : Finset I // s.Nonempty}, ∃ f :
      Hull83.Hull (L := L) (Hull83.witB hc s.1.card.pred).v ↪[L] M, ∀ p,
        f (Quotient.mk _ (FirstOrder.Language.Term.var p)) =
          Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm p := by
    intro s
    have hs := (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm
    have h' : Hull83.tpCode (L := L) (Hull83.witB hc s.1.card.pred).v =
        Hull83.tpCode (Hull83.bundleOf base s.1 hs ∘ id) :=
      (Hull83.witB hc s.1.card.pred).tp.trans (htp _ s.1 hs).symm
    exact ⟨(Hull83.hullEmb (Hull83.bundleOf base s.1 hs)).comp (Hull83.hullMapEmb id h'),
      fun p => rfl⟩
  choose m hm using key
  refine ⟨m, hm, fun {s t} h => ?_⟩
  exact infra_83_hull_match_compat _ _ (m s) (m t) _ _ (hm s) (hm t)
    (fun p => infra_83_bundleOf_placeSucc base h s.2 t.2 _ _ p)

/-- **Bundles along an order embedding (proved).** Enumerating a support of `I` and then moving
along `e : I ↪o α` gives the bundles of the image support. -/
theorem infra_83_bundleOf_orderMap {I α : Type u} [LinearOrder I] [LinearOrder α] {M : Type u}
    {r : ℕ} (base : α → Fin r → M) (e : I ↪o α) (s : Finset I) {m : ℕ} (h : s.card = m)
    (h' : (s.map e.toEmbedding).card = m) (p : Fin m × Fin r) :
    Hull83.bundleOf (fun i => base (e i)) s h p = Hull83.bundleOf base (s.map e.toEmbedding) h' p := by
  have hu := Finset.orderEmbOfFin_unique' (s := s.map e.toEmbedding) h'
    (f := (s.orderEmbOfFin h).trans e)
    (fun x => Finset.mem_map_of_mem _ (Finset.orderEmbOfFin_mem s h x))
  simp only [Hull83.bundleOf]
  rw [← hu]
  rfl

/-- **Homogeneous samples restricted along an order embedding have the template bundle types
(proved).** For a bundled sample homogeneous in every arity for `c` and `e : I ↪o S.α`, every
finite enumeration of the moved bundles `base ∘ e` has the template color. -/
theorem infra_83_sample_tp_orderMap {L : FirstOrder.Language.{u, u}} {r : ℕ}
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    {S : Hull83.ColorSample (Hull83.TpColorB L r)} {M : Type u} [L.Structure M]
    (base : S.α → Fin r → M)
    (hcol : ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m),
      S.col m s = Hull83.tpCode (Hull83.bundleOf base s h))
    (hhom : ∀ n, Hull83.Homog S n c) {I : Type u} [LinearOrder I] (e : I ↪o S.α) :
    ∀ (k : ℕ) (s : Finset I) (h : s.card = k + 1),
      Hull83.tpCode (L := L) (Hull83.bundleOf (fun i => base (e i)) s h) =
        c (k + 1) (Nat.succ_pos k) := by
  intro k s h
  have h' : (s.map e.toEmbedding).card = k + 1 := (Finset.card_map _).trans h
  have hb : Hull83.bundleOf (fun i => base (e i)) s h =
      Hull83.bundleOf base (s.map e.toEmbedding) h' :=
    funext fun p => infra_83_bundleOf_orderMap base e s h h' p
  rw [hb, ← hcol]
  exact hhom (k + 1) (k + 1) (Nat.succ_pos k) le_rfl _ h'

/-- **The template value of `I` maps into a homogeneous sample (proved).** English (Lemma 8.3
proof): the template value is matched into an actual sample. For bundle families `base : I → M`
in an admitted `L`-structure `M` (with `K`-reduct) whose finite enumerations have the template
colors (e.g. `infra_83_sample_tp_orderMap`), the EM value `F(I)` of the bundled pieces embeds
strongly into the reduct of `M`, sending the generators of every support `s` to the bundles of
`s`. -/
theorem infra_83_limit_into_sample {L : FirstOrder.Language.{u, u}}
    {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ} [NeZero r]
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    (φ : K.τ →ᴸ L) (hP : Hull83.HullStrong φ P)
    {I : Type u} [LinearOrder I] [Nonempty I] {M : Type u} [L.Structure M] (hPM : P M)
    (hMK : K.Mem (Hull83.red φ M)) (base : I → Fin r → M)
    (htp : ∀ (k : ℕ) (s : Finset I) (h : s.card = k + 1),
      Hull83.tpCode (L := L) (Hull83.bundleOf base s h) = c (k + 1) (Nat.succ_pos k)) :
    ∃ f : ((Hull83.tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP).limit I).obj.carrier
        ↪[K.τ] (Hull83.red φ M).carrier,
      K.Strong f ∧ ∀ (s : {s : Finset I // s.Nonempty}) p,
        f (((Hull83.tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP).limit I).canon s
          (Quotient.mk _ (FirstOrder.Language.Term.var p))) =
          Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm p := by
  classical
  let F := Hull83.tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP
  have hs : ∀ s : {s : Finset I // s.Nonempty}, s.1.card = s.1.card.pred + 1 :=
    fun s => (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm
  have h' : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.tpCode (L := L) (Hull83.witB hc s.1.card.pred).v =
        Hull83.tpCode (Hull83.bundleOf base s.1 (hs s) ∘ id) :=
    fun s => (Hull83.witB hc s.1.card.pred).tp.trans (htp _ s.1 (hs s)).symm
  let m : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.Hull (L := L) (Hull83.witB hc s.1.card.pred).v ↪[L] M :=
    fun s => (Hull83.hullEmb (Hull83.bundleOf base s.1 (hs s))).comp (Hull83.hullMapEmb id (h' s))
  let g : ∀ s : (F.system I).ι, ((F.system I).obj s).carrier ↪[K.τ] (Hull83.red φ M).carrier :=
    fun s => Hull83.redEmb φ (m s)
  have hg : ∀ s, K.Strong (g s) := by
    intro s
    have h1 := Hull83.hullMap_strong hP hPM (Hull83.witB hc s.1.card.pred).mem id (h' s)
    have h2 := hP M hPM (Hull83.bundleOf base s.1 (hs s))
    exact K.strong_trans _ _ h1 h2
  have hcompat : ∀ {s t} (h : (F.system I).rel s t), (g t).comp ((F.system I).map h) = g s := by
    intro s t h
    have := infra_83_hull_match_compat (Prod.map (placeSucc h s.2 t.2) id)
      (Hull83.tpPieceB_tp hc hcoh (placeSucc h s.2 t.2)) (m s) (m t) _ _
      (fun p => rfl) (fun p => rfl) (fun p => infra_83_bundleOf_placeSucc base h s.2 t.2 _ _ p)
    ext x
    exact congrFun (congrArg (⇑) this) x
  obtain ⟨f, hf, hfc⟩ := (F.limit_spec I).2.2 (Hull83.red φ M) g hMK hg hcompat
  refine ⟨f, hf, fun s p => ?_⟩
  exact congrFun (congrArg (⇑) (hfc s)) _

/-- **The template pair of `I` maps into a homogeneous sample (proved).** English (Lemma 8.3
proof): the value pair `X_I = F(J_I) ≤ Y_I` is matched into an actual sample. For the bundled
pieces (`Y`) and their sub-bundle on the coordinates `σ` (`X`, e.g. the `J`-coordinates) with
the sub-bundle inclusion `η`, bundle families of `I` in an admitted sample with the template
colors give strong embeddings of both EM values into the sample commuting with `η`, sending the
generators of every support to the bundles. -/
theorem infra_83_pair_into_sample {L : FirstOrder.Language.{u, u}}
    {P : ∀ (M : Type u) [L.Structure M], Prop} {r r₀ : ℕ} [NeZero r] [NeZero r₀]
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    (σ : Fin r₀ → Fin r) (φ : K.τ →ᴸ L) (hP : Hull83.HullStrong φ P)
    {I : Type u} [LinearOrder I] [Nonempty I] {M : Type u} [L.Structure M] (hPM : P M)
    (hMK : K.Mem (Hull83.red φ M)) (base : I → Fin r → M)
    (htp : ∀ (k : ℕ) (s : Finset I) (h : s.card = k + 1),
      Hull83.tpCode (L := L) (Hull83.bundleOf base s h) = c (k + 1) (Nat.succ_pos k)) :
    ∃ (onX : ((Hull83.subBundlePieces hc hcoh σ φ hP).limit I).obj.carrier
        ↪[K.τ] (Hull83.red φ M).carrier)
      (onY : ((Hull83.tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP).limit I).obj.carrier
        ↪[K.τ] (Hull83.red φ M).carrier),
      K.Strong onX ∧ K.Strong onY ∧
      (∀ x, onY ((Hull83.subBundleHom hc hcoh σ φ hP).limMap I x) = onX x) ∧
      ∀ (s : {s : Finset I // s.Nonempty}) p,
        onY (((Hull83.tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP).limit I).canon s
          (Quotient.mk _ (FirstOrder.Language.Term.var p))) =
          Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm p := by
  classical
  let FY := Hull83.tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP
  let FX := Hull83.subBundlePieces hc hcoh σ φ hP
  have hs : ∀ s : {s : Finset I // s.Nonempty}, s.1.card = s.1.card.pred + 1 :=
    fun s => (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm
  have h' : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.tpCode (L := L) (Hull83.witB hc s.1.card.pred).v =
        Hull83.tpCode (Hull83.bundleOf base s.1 (hs s) ∘ id) :=
    fun s => (Hull83.witB hc s.1.card.pred).tp.trans (htp _ s.1 (hs s)).symm
  have hσ : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.tpCode (L := L) ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ) =
        Hull83.tpCode ((Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ) ∘ id) :=
    fun s => Hull83.tpCode_comp (h' s) (Prod.map id σ)
  let mY : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.Hull (L := L) (Hull83.witB hc s.1.card.pred).v ↪[L] M :=
    fun s => (Hull83.hullEmb (Hull83.bundleOf base s.1 (hs s))).comp (Hull83.hullMapEmb id (h' s))
  let mX : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.Hull (L := L) ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ) ↪[L] M :=
    fun s => (Hull83.hullEmb (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ)).comp
      (Hull83.hullMapEmb id (hσ s))
  let gY : ∀ s : (FY.system I).ι, ((FY.system I).obj s).carrier ↪[K.τ] (Hull83.red φ M).carrier :=
    fun s => Hull83.redEmb φ (mY s)
  let gX : ∀ s : (FX.system I).ι, ((FX.system I).obj s).carrier ↪[K.τ] (Hull83.red φ M).carrier :=
    fun s => Hull83.redEmb φ (mX s)
  have hgY : ∀ s, K.Strong (gY s) := fun s =>
    K.strong_trans _ _ (Hull83.hullMap_strong hP hPM (Hull83.witB hc s.1.card.pred).mem id (h' s))
      (hP M hPM (Hull83.bundleOf base s.1 (hs s)))
  have hgX : ∀ s, K.Strong (gX s) := fun s =>
    K.strong_trans _ _ (Hull83.hullMap_strong hP hPM (Hull83.witB hc s.1.card.pred).mem id (hσ s))
      (hP M hPM (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ))
  have hcY : ∀ {s t} (h : (FY.system I).rel s t), (gY t).comp ((FY.system I).map h) = gY s := by
    intro s t h
    have := infra_83_hull_match_compat (Prod.map (placeSucc h s.2 t.2) id)
      (Hull83.tpPieceB_tp hc hcoh (placeSucc h s.2 t.2)) (mY s) (mY t) _ _
      (fun p => rfl) (fun p => rfl) (fun p => infra_83_bundleOf_placeSucc base h s.2 t.2 _ _ p)
    ext x
    exact congrFun (congrArg (⇑) this) x
  have hcX : ∀ {s t} (h : (FX.system I).rel s t), (gX t).comp ((FX.system I).map h) = gX s := by
    intro s t h
    have := infra_83_hull_match_compat (Prod.map (placeSucc h s.2 t.2) id)
      (Hull83.subBundle_tp hc hcoh σ (placeSucc h s.2 t.2)) (mX s) (mX t) _ _
      (fun p => rfl) (fun p => rfl)
      (fun p => infra_83_bundleOf_placeSucc base h s.2 t.2 _ _ (p.1, σ p.2))
    ext x
    exact congrFun (congrArg (⇑) this) x
  have hsq : ∀ (s : (FX.system I).ι) x,
      gY s ((Hull83.subBundleHom hc hcoh σ φ hP).app s.1.card.pred x) =
        (Language.Embedding.refl K.τ _) (gX s x) := by
    intro s x
    have : (mY s).comp (Hull83.hullMapEmb (v' := (Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ)
        (Prod.map id σ) rfl) = mX s :=
      infra_83_hull_emb_ext _ _ fun p => rfl
    exact congrFun (congrArg (⇑) this) x
  obtain ⟨onX, onY, h1, h2, -, hY, hc'⟩ := infra_83_pair_limit_desc
    (Hull83.subBundleHom hc hcoh σ φ hP) I hMK hMK (Language.Embedding.refl K.τ _) gX gY hgX hgY
    hcX hcY hsq
  exact ⟨onX, onY, h1, h2, hc', fun s p => congrFun (congrArg (⇑) (hY s)) _⟩

/-- **The template pair maps into any homogeneous sample along an order embedding (proved).**
English (Lemma 8.3 proof): "embed `I` into the order of a homogeneous sample (order saturation)
and match". For a bundled sample `S` with admitted structure `M`, homogeneous in every arity for
the template colors, and `e : I ↪o S.α`, the template pair of `I` maps strongly into `M`,
commuting with the inclusion, generators of a support `s` going to the bundles of `e(s)`. -/
theorem infra_83_pair_into_sample_along {L : FirstOrder.Language.{u, u}}
    {P : ∀ (M : Type u) [L.Structure M], Prop} {r r₀ : ℕ} [NeZero r] [NeZero r₀]
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    (σ : Fin r₀ → Fin r) (φ : K.τ →ᴸ L) (hP : Hull83.HullStrong φ P)
    {S : Hull83.ColorSample (Hull83.TpColorB L r)} {M : Type u} [L.Structure M] (hPM : P M)
    (hMK : K.Mem (Hull83.red φ M)) (base : S.α → Fin r → M)
    (hcol : ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m),
      S.col m s = Hull83.tpCode (Hull83.bundleOf base s h))
    (hhom : ∀ n, Hull83.Homog S n c) {I : Type u} [LinearOrder I] [Nonempty I] (e : I ↪o S.α) :
    ∃ (onX : ((Hull83.subBundlePieces hc hcoh σ φ hP).limit I).obj.carrier
        ↪[K.τ] (Hull83.red φ M).carrier)
      (onY : ((Hull83.tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP).limit I).obj.carrier
        ↪[K.τ] (Hull83.red φ M).carrier),
      K.Strong onX ∧ K.Strong onY ∧
      (∀ x, onY ((Hull83.subBundleHom hc hcoh σ φ hP).limMap I x) = onX x) ∧
      ∀ (s : {s : Finset I // s.Nonempty}) p,
        onY (((Hull83.tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP).limit I).canon s
          (Quotient.mk _ (FirstOrder.Language.Term.var p))) =
          Hull83.bundleOf (fun i => base (e i)) s.1
            (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm p :=
  infra_83_pair_into_sample hc hcoh σ φ hP hPM hMK (fun i => base (e i))
    (infra_83_sample_tp_orderMap base hcol hhom e)

/-- **Sublanguage template value of `I` maps into a homogeneous sample (proved).** As
`infra_83_limit_into_sample`, for the sublanguage pieces `Hull83.subLangPieces` (the `L₀`-hulls
of the `σ`-coordinates of the bundles) used by the Lemma 8.3 pair template: bundle families of
`I` in an admitted sample with the template colors give a strong embedding of the EM value into
the `L₀`-reduct of the sample, generators of a support going to the bundles. -/
theorem infra_83_subLang_limit_into_sample {L L₀ : FirstOrder.Language.{u, u}} (ψ : L₀ →ᴸ L)
    (φ₀ : K.τ →ᴸ L₀) {P : ∀ (M : Type u) [L.Structure M], Prop} {r r₁ : ℕ} [NeZero r]
    [NeZero r₁] {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    (σ : Fin r₁ → Fin r) (hP₀ : Hull83.SubHullStrong ψ φ₀ P)
    {I : Type u} [LinearOrder I] [Nonempty I] {M : Type u} [L.Structure M] (hPM : P M)
    (hMK : K.Mem (Hull83.subModel' ψ φ₀ M)) (base : I → Fin r → M)
    (htp : ∀ (k : ℕ) (s : Finset I) (h : s.card = k + 1),
      Hull83.tpCode (L := L) (Hull83.bundleOf base s h) = c (k + 1) (Nat.succ_pos k)) :
    ∃ f : ((Hull83.subLangPieces ψ φ₀ hc hcoh σ hP₀).limit I).obj.carrier
        ↪[K.τ] (Hull83.subModel' ψ φ₀ M).carrier,
      K.Strong f ∧ ∀ (s : {s : Finset I // s.Nonempty}) p,
        f (((Hull83.subLangPieces ψ φ₀ hc hcoh σ hP₀).limit I).canon s
          (Quotient.mk _ (FirstOrder.Language.Term.var p))) =
          (Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm ∘
            Prod.map id σ) p := by
  classical
  let F := Hull83.subLangPieces ψ φ₀ hc hcoh σ hP₀
  have hs : ∀ s : {s : Finset I // s.Nonempty}, s.1.card = s.1.card.pred + 1 :=
    fun s => (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm
  have h' : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.tpCode (L := L) (Hull83.witB hc s.1.card.pred).v =
        Hull83.tpCode (Hull83.bundleOf base s.1 (hs s) ∘ id) :=
    fun s => (Hull83.witB hc s.1.card.pred).tp.trans (htp _ s.1 (hs s)).symm
  have hσ : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.tpCode (L := L) ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ) =
        Hull83.tpCode ((Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ) ∘ id) :=
    fun s => Hull83.tpCode_comp (h' s) (Prod.map id σ)
  letI : L₀.Structure M := ψ.reduct M
  letI : ∀ k, L₀.Structure (Hull83.witB hc k).M := fun k => ψ.reduct _
  have hred : Hull83.reductClass ψ P M := ⟨_, hPM, rfl⟩
  have hP' := Hull83.hullStrong_reductClass ψ φ₀ hP₀
  let m : ∀ s : {s : Finset I // s.Nonempty},
      @Hull83.Hull L₀ _ (ψ.reduct _) _ ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ)
        ↪[L₀] M :=
    fun s => (Hull83.hullEmb (L := L₀) (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ)).comp
      (@Hull83.hullMapEmb L₀ M _ (ψ.reduct M) (ψ.reduct _) _ _
        ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ)
        (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ) id
        (Hull83.tpCode_reduct' ψ (hσ s)))
  let g : ∀ s : (F.system I).ι, ((F.system I).obj s).carrier ↪[K.τ]
      (Hull83.subModel' ψ φ₀ M).carrier :=
    fun s => @Hull83.redEmb K L₀ φ₀ _ M (@Hull83.hullStructure L₀ _ (ψ.reduct _) _ _)
      (ψ.reduct M) (m s)
  have hg : ∀ s, K.Strong (g s) := fun s => by
    refine (K.strong_trans _ _ ?_ ?_ : K.Strong ((Hull83.redEmb φ₀ (Hull83.hullEmb (L := L₀)
      (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ))).comp (Hull83.redEmb φ₀
        (@Hull83.hullMapEmb L₀ M _ (ψ.reduct M) (ψ.reduct _) _ _
        ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ)
        (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ) id
        (Hull83.tpCode_reduct' ψ (hσ s))))))
    · exact (@Hull83.hullMap_strong K L₀ φ₀ (Hull83.reductClass ψ P) hP' M _ (ψ.reduct _) _ hred
        ⟨_, (Hull83.witB hc s.1.card.pred).mem, rfl⟩ _ _ _ _ _ _ _ _ id
        (Hull83.tpCode_reduct' ψ (hσ s)))
    exact (hP' M hred (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ))
  have hcompat : ∀ {s t} (h : (F.system I).rel s t), (g t).comp ((F.system I).map h) = g s := by
    intro s t h
    have := infra_83_hull_match_compat (L := L₀) (Prod.map (placeSucc h s.2 t.2) id)
      (Hull83.tpCode_reduct' ψ (Hull83.subBundle_tp hc hcoh σ (placeSucc h s.2 t.2)))
      (m s) (m t) _ _ (fun p => rfl) (fun p => rfl)
      (fun p => infra_83_bundleOf_placeSucc base h s.2 t.2 _ _ (p.1, σ p.2))
    ext x
    exact congrFun (congrArg (⇑) this) x
  obtain ⟨f, hf, hfc⟩ := (F.limit_spec I).2.2 (Hull83.subModel' ψ φ₀ M) g hMK hg hcompat
  exact ⟨f, hf, fun s p => (congrFun (congrArg (⇑) (hfc s))
    (Quotient.mk _ (FirstOrder.Language.Term.var p))).trans rfl⟩

/-- **Matching the mixed-language sort map into a sample (proved).** The value in a sample of
the image of an `L₁`-hull element under the Lemma 8.3 mixed sort map `X_H → Y_H`
(`Hull83.mixMap`, the template's `ηXY`), transported by the `L₂`-match, equals the value of the
`L₁`-match: the matches of the `X` and `Y` pieces of the sublanguage pair template into a sample
commute with the template inclusion. -/
theorem infra_83_mix_hullVal_match {L₁ L₂ L : FirstOrder.Language.{u, u}} (χ : L₁ →ᴸ L₂) (ψ₂ : L₂ →ᴸ L) {M N : Type u} [L.Structure M]
    [L.Structure N] {ι ι₀ : Type} (w : ι → N) (v : ι → M) (τ : ι₀ → ι)
    (hY : @Hull83.tpCode L₂ N (ψ₂.reduct N) ι w = @Hull83.tpCode L₂ M (ψ₂.reduct M) ι (v ∘ id))
    (hX : @Hull83.tpCode L₁ N ((ψ₂.comp χ).reduct N) ι₀ (w ∘ τ) =
      @Hull83.tpCode L₁ M ((ψ₂.comp χ).reduct M) ι₀ ((v ∘ τ) ∘ id))
    (x : Hull83.subHull (ψ₂.comp χ) (w ∘ τ)) :
    @Hull83.hullVal L₂ M (ψ₂.reduct M) ι v
      (@Hull83.hullMap L₂ M N (ψ₂.reduct M) (ψ₂.reduct N) ι ι w v id hY
        (Hull83.mixMap χ ψ₂ w τ x)) =
    @Hull83.hullVal L₁ M ((ψ₂.comp χ).reduct M) ι₀ (v ∘ τ)
      (@Hull83.hullMap L₁ M N ((ψ₂.comp χ).reduct M) ((ψ₂.comp χ).reduct N) ι₀ ι₀ (w ∘ τ) (v ∘ τ) id hX x) := by
  induction x using Quotient.ind with
  | _ t =>
    letI := ψ₂.reduct M
    letI := χ.reduct M
    show (((χ.onTerm t).relabel τ).relabel id).realize v = (t.relabel id).realize (v ∘ τ)
    rw [FirstOrder.Language.Term.realize_relabel, FirstOrder.Language.Term.realize_relabel, FirstOrder.Language.Term.realize_relabel]
    simp only [Function.comp_id, FirstOrder.Language.LHom.realize_onTerm]

/-- **The mixed sublanguage template pair of `I` maps into a homogeneous sample (proved).**
English (Lemma 8.3 proof): the value pair `X_I ≤ Y_I` of the pair template (`X`: `L₁`-hulls of
the `σ ∘ τ`-coordinates, `Y`: `L₂`-hulls of the `σ`-coordinates, inclusion the mixed sort map
`Hull83.subLangMixHom`) is matched into an actual sample: bundle families of `I` in an admitted
sample with the template colors give strong embeddings of both EM values into the sample
commuting with the template inclusion. -/
theorem infra_83_mix_pair_into_sample {L₁ L₂ L : FirstOrder.Language.{u, u}} (χ : L₁ →ᴸ L₂)
    (ψ₂ : L₂ →ᴸ L) (φ₀ : K.τ →ᴸ L₁) {P : ∀ (M : Type u) [L.Structure M], Prop} {r r₁ r₀ : ℕ}
    [NeZero r] [NeZero r₁] [NeZero r₀] {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    (σ : Fin r₁ → Fin r) (τ : Fin r₀ → Fin r₁)
    (hPX : Hull83.SubHullStrong (ψ₂.comp χ) φ₀ P) (hPY : Hull83.SubHullStrong ψ₂ (χ.comp φ₀) P)
    {I : Type u} [LinearOrder I] [Nonempty I] {M : Type u} [L.Structure M] (hPM : P M)
    (hMK : K.Mem (Hull83.subModel' ψ₂ (χ.comp φ₀) M)) (base : I → Fin r → M)
    (htp : ∀ (k : ℕ) (s : Finset I) (h : s.card = k + 1),
      Hull83.tpCode (L := L) (Hull83.bundleOf base s h) = c (k + 1) (Nat.succ_pos k)) :
    ∃ (onX : ((Hull83.subLangPieces (ψ₂.comp χ) φ₀ hc hcoh (σ ∘ τ) hPX).limit I).obj.carrier
        ↪[K.τ] (Hull83.subModel' (ψ₂.comp χ) φ₀ M).carrier)
      (onY : ((Hull83.subLangPieces ψ₂ (χ.comp φ₀) hc hcoh σ hPY).limit I).obj.carrier
        ↪[K.τ] (Hull83.subModel' ψ₂ (χ.comp φ₀) M).carrier),
      K.Strong onX ∧ K.Strong onY ∧
      (∀ x, onY ((Hull83.subLangMixHom χ ψ₂ φ₀ hc hcoh σ τ hPX hPY).limMap I x) = onX x) ∧
      (∀ (s : {s : Finset I // s.Nonempty}) p,
        onY (((Hull83.subLangPieces ψ₂ (χ.comp φ₀) hc hcoh σ hPY).limit I).canon s
          (Quotient.mk _ (FirstOrder.Language.Term.var p))) =
          (Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm ∘
            Prod.map id σ) p) ∧
      ∀ (s : {s : Finset I // s.Nonempty}) p,
        onX (((Hull83.subLangPieces (ψ₂.comp χ) φ₀ hc hcoh (σ ∘ τ) hPX).limit I).canon s
          (Quotient.mk _ (FirstOrder.Language.Term.var p))) =
          (Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm ∘
            Prod.map id (σ ∘ τ)) p := by
  classical
  let FX := Hull83.subLangPieces (ψ₂.comp χ) φ₀ hc hcoh (σ ∘ τ) hPX
  let FY := Hull83.subLangPieces ψ₂ (χ.comp φ₀) hc hcoh σ hPY
  have hs : ∀ s : {s : Finset I // s.Nonempty}, s.1.card = s.1.card.pred + 1 :=
    fun s => (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm
  have h' : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.tpCode (L := L) (Hull83.witB hc s.1.card.pred).v =
        Hull83.tpCode (Hull83.bundleOf base s.1 (hs s) ∘ id) :=
    fun s => (Hull83.witB hc s.1.card.pred).tp.trans (htp _ s.1 (hs s)).symm
  have hσ : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.tpCode (L := L) ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ) =
        Hull83.tpCode ((Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ) ∘ id) :=
    fun s => Hull83.tpCode_comp (h' s) (Prod.map id σ)
  have hστ : ∀ s : {s : Finset I // s.Nonempty},
      Hull83.tpCode (L := L) ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id (σ ∘ τ)) =
        Hull83.tpCode ((Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id (σ ∘ τ)) ∘ id) :=
    fun s => Hull83.tpCode_comp (h' s) (Prod.map id (σ ∘ τ))
  have hMX : K.Mem (Hull83.subModel' (ψ₂.comp χ) φ₀ M) := hMK
  let ιXY : (Hull83.subModel' (ψ₂.comp χ) φ₀ M).carrier ↪[K.τ]
      (Hull83.subModel' ψ₂ (χ.comp φ₀) M).carrier :=
    @Language.Embedding.refl K.τ M (Hull83.subModel' (ψ₂.comp χ) φ₀ M).str
  letI : ∀ k, L₁.Structure (Hull83.witB hc k).M := fun k => (ψ₂.comp χ).reduct _
  letI : ∀ k, L₂.Structure (Hull83.witB hc k).M := fun k => ψ₂.reduct _
  letI : L₁.Structure M := (ψ₂.comp χ).reduct M
  letI : L₂.Structure M := ψ₂.reduct M
  have hredX : Hull83.reductClass (ψ₂.comp χ) P M := ⟨_, hPM, rfl⟩
  have hredY : Hull83.reductClass ψ₂ P M := ⟨_, hPM, rfl⟩
  have hPX' := Hull83.hullStrong_reductClass (ψ₂.comp χ) φ₀ hPX
  have hPY' := Hull83.hullStrong_reductClass ψ₂ (χ.comp φ₀) hPY
  let mX : ∀ s : {s : Finset I // s.Nonempty},
      @Hull83.Hull L₁ _ ((ψ₂.comp χ).reduct _) _
        ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id (σ ∘ τ)) ↪[L₁] M :=
    fun s => (Hull83.hullEmb (L := L₁) (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id (σ ∘ τ))).comp
      (@Hull83.hullMapEmb L₁ M _ ((ψ₂.comp χ).reduct M) ((ψ₂.comp χ).reduct _) _ _
        ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id (σ ∘ τ))
        (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id (σ ∘ τ)) id
        (Hull83.tpCode_reduct' (ψ₂.comp χ) (hστ s)))
  let mY : ∀ s : {s : Finset I // s.Nonempty},
      @Hull83.Hull L₂ _ (ψ₂.reduct _) _
        ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ) ↪[L₂] M :=
    fun s => (Hull83.hullEmb (L := L₂) (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ)).comp
      (@Hull83.hullMapEmb L₂ M _ (ψ₂.reduct M) (ψ₂.reduct _) _ _
        ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ)
        (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ) id
        (Hull83.tpCode_reduct' ψ₂ (hσ s)))
  let gX : ∀ s : (FX.system I).ι, ((FX.system I).obj s).carrier ↪[K.τ]
      (Hull83.subModel' (ψ₂.comp χ) φ₀ M).carrier :=
    fun s => @Hull83.redEmb K L₁ φ₀ _ M (@Hull83.hullStructure L₁ _ ((ψ₂.comp χ).reduct _) _ _)
      ((ψ₂.comp χ).reduct M) (mX s)
  let gY : ∀ s : (FY.system I).ι, ((FY.system I).obj s).carrier ↪[K.τ]
      (Hull83.subModel' ψ₂ (χ.comp φ₀) M).carrier :=
    fun s => @Hull83.redEmb K L₂ (χ.comp φ₀) _ M (@Hull83.hullStructure L₂ _ (ψ₂.reduct _) _ _)
      (ψ₂.reduct M) (mY s)
  have hgX : ∀ s, K.Strong (gX s) := fun s => by
    refine (K.strong_trans _ _ ?_ ?_ : K.Strong ((Hull83.redEmb φ₀ (Hull83.hullEmb (L := L₁)
      (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id (σ ∘ τ)))).comp (Hull83.redEmb φ₀
        (@Hull83.hullMapEmb L₁ M _ ((ψ₂.comp χ).reduct M) ((ψ₂.comp χ).reduct _) _ _
        ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id (σ ∘ τ))
        (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id (σ ∘ τ)) id
        (Hull83.tpCode_reduct' (ψ₂.comp χ) (hστ s))))))
    · exact (@Hull83.hullMap_strong K L₁ φ₀ (Hull83.reductClass (ψ₂.comp χ) P) hPX' M _
        ((ψ₂.comp χ).reduct _) _ hredX ⟨_, (Hull83.witB hc s.1.card.pred).mem, rfl⟩
        _ _ _ _ _ _ _ _ id (Hull83.tpCode_reduct' (ψ₂.comp χ) (hστ s)))
    exact (hPX' M hredX (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id (σ ∘ τ)))
  have hgY : ∀ s, K.Strong (gY s) := fun s => by
    refine (K.strong_trans _ _ ?_ ?_ : K.Strong ((Hull83.redEmb (χ.comp φ₀) (Hull83.hullEmb (L := L₂)
      (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ))).comp (Hull83.redEmb (χ.comp φ₀)
        (@Hull83.hullMapEmb L₂ M _ (ψ₂.reduct M) (ψ₂.reduct _) _ _
        ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ)
        (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ) id
        (Hull83.tpCode_reduct' ψ₂ (hσ s))))))
    · exact (@Hull83.hullMap_strong K L₂ (χ.comp φ₀) (Hull83.reductClass ψ₂ P) hPY' M _
        (ψ₂.reduct _) _ hredY ⟨_, (Hull83.witB hc s.1.card.pred).mem, rfl⟩
        _ _ _ _ _ _ _ _ id (Hull83.tpCode_reduct' ψ₂ (hσ s)))
    exact (hPY' M hredY (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ))
  have hcX : ∀ {s t} (h : (FX.system I).rel s t), (gX t).comp ((FX.system I).map h) = gX s := by
    intro s t h
    have := infra_83_hull_match_compat (L := L₁) (Prod.map (placeSucc h s.2 t.2) id)
      (Hull83.tpCode_reduct' (ψ₂.comp χ) (Hull83.subBundle_tp hc hcoh (σ ∘ τ) (placeSucc h s.2 t.2)))
      (mX s) (mX t) _ _ (fun p => rfl) (fun p => rfl)
      (fun p => infra_83_bundleOf_placeSucc base h s.2 t.2 _ _ (p.1, σ (τ p.2)))
    ext x
    exact congrFun (congrArg (⇑) this) x
  have hcY : ∀ {s t} (h : (FY.system I).rel s t), (gY t).comp ((FY.system I).map h) = gY s := by
    intro s t h
    have := infra_83_hull_match_compat (L := L₂) (Prod.map (placeSucc h s.2 t.2) id)
      (Hull83.tpCode_reduct' ψ₂ (Hull83.subBundle_tp hc hcoh σ (placeSucc h s.2 t.2)))
      (mY s) (mY t) _ _ (fun p => rfl) (fun p => rfl)
      (fun p => infra_83_bundleOf_placeSucc base h s.2 t.2 _ _ (p.1, σ p.2))
    ext x
    exact congrFun (congrArg (⇑) this) x
  have hsq : ∀ (s : (FX.system I).ι) x,
      gY s ((Hull83.subLangMixHom χ ψ₂ φ₀ hc hcoh σ τ hPX hPY).app s.1.card.pred x) =
        ιXY (gX s x) :=
    fun s x => infra_83_mix_hullVal_match χ ψ₂ ((Hull83.witB hc s.1.card.pred).v ∘ Prod.map id σ)
      (Hull83.bundleOf base s.1 (hs s) ∘ Prod.map id σ) (Prod.map id τ)
      (Hull83.tpCode_reduct' ψ₂ (hσ s)) (Hull83.tpCode_reduct' (ψ₂.comp χ) (hστ s)) x
  obtain ⟨onX, onY, h1, h2, hXc, hYc, hcomm⟩ := infra_83_pair_limit_desc
    (Hull83.subLangMixHom χ ψ₂ φ₀ hc hcoh σ τ hPX hPY) I hMX hMK
    ιXY gX gY hgX hgY
    hcX hcY hsq
  exact ⟨onX, onY, h1, h2, fun x => hcomm x, fun s p =>
    (congrFun (congrArg (⇑) (hYc s)) (Quotient.mk _ (FirstOrder.Language.Term.var p))).trans rfl,
    fun s p =>
    (congrFun (congrArg (⇑) (hXc s)) (Quotient.mk _ (FirstOrder.Language.Term.var p))).trans rfl⟩

/-- **The mixed sublanguage template pair maps into a homogeneous sample along an order
embedding (proved).** `infra_83_mix_pair_into_sample` for the bundles `base ∘ e` of a bundled
sample homogeneous in every arity for the template colors, along `e : I ↪o S.α` (order
saturation supplies such `e`). -/
theorem infra_83_mix_pair_into_sample_along {L₁ L₂ L : FirstOrder.Language.{u, u}}
    (χ : L₁ →ᴸ L₂) (ψ₂ : L₂ →ᴸ L) (φ₀ : K.τ →ᴸ L₁) {P : ∀ (M : Type u) [L.Structure M], Prop}
    {r r₁ r₀ : ℕ} [NeZero r] [NeZero r₁] [NeZero r₀]
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    (σ : Fin r₁ → Fin r) (τ : Fin r₀ → Fin r₁)
    (hPX : Hull83.SubHullStrong (ψ₂.comp χ) φ₀ P) (hPY : Hull83.SubHullStrong ψ₂ (χ.comp φ₀) P)
    {S : Hull83.ColorSample (Hull83.TpColorB L r)} {M : Type u} [L.Structure M] (hPM : P M)
    (hMK : K.Mem (Hull83.subModel' ψ₂ (χ.comp φ₀) M)) (base : S.α → Fin r → M)
    (hcol : ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m),
      S.col m s = Hull83.tpCode (Hull83.bundleOf base s h))
    (hhom : ∀ n, Hull83.Homog S n c) {I : Type u} [LinearOrder I] [Nonempty I] (e : I ↪o S.α) :
    ∃ (onX : ((Hull83.subLangPieces (ψ₂.comp χ) φ₀ hc hcoh (σ ∘ τ) hPX).limit I).obj.carrier
        ↪[K.τ] (Hull83.subModel' (ψ₂.comp χ) φ₀ M).carrier)
      (onY : ((Hull83.subLangPieces ψ₂ (χ.comp φ₀) hc hcoh σ hPY).limit I).obj.carrier
        ↪[K.τ] (Hull83.subModel' ψ₂ (χ.comp φ₀) M).carrier),
      K.Strong onX ∧ K.Strong onY ∧
      (∀ x, onY ((Hull83.subLangMixHom χ ψ₂ φ₀ hc hcoh σ τ hPX hPY).limMap I x) = onX x) ∧
      (∀ (s : {s : Finset I // s.Nonempty}) p,
        onY (((Hull83.subLangPieces ψ₂ (χ.comp φ₀) hc hcoh σ hPY).limit I).canon s
          (Quotient.mk _ (FirstOrder.Language.Term.var p))) =
          (Hull83.bundleOf (fun i => base (e i)) s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm ∘
            Prod.map id σ) p) ∧
      ∀ (s : {s : Finset I // s.Nonempty}) p,
        onX (((Hull83.subLangPieces (ψ₂.comp χ) φ₀ hc hcoh (σ ∘ τ) hPX).limit I).canon s
          (Quotient.mk _ (FirstOrder.Language.Term.var p))) =
          (Hull83.bundleOf (fun i => base (e i)) s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm ∘
            Prod.map id (σ ∘ τ)) p :=
  infra_83_mix_pair_into_sample χ ψ₂ φ₀ hc hcoh σ τ hPX hPY hPM hMK (fun i => base (e i))
    (infra_83_sample_tp_orderMap base hcol hhom e)

/-- **Small well-orders embed into order-saturated orders (proved).** English (Lemma 8.3 proof):
the sample order is order saturated, so every well-order `I` of size `< κ` embeds into it
(`OrderSat83.extend_strictMono` from the empty partial map); with
`infra_83_mix_pair_into_sample_along` this matches the template pair of `I` into the sample. -/
theorem infra_83_wellOrder_into_saturated {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) {J I : Type u}
    [LinearOrder J] [LinearOrder I] [WellFoundedLT I] (hJ : OrderSat83.OrderSaturated κ J)
    (hI : #I < κ) : Nonempty (I ↪o J) := by
  obtain ⟨g, hg, -⟩ := OrderSat83.extend_strictMono hκ hJ hI (∅ : Set I)
    (fun d => absurd d.2 (Set.notMem_empty _)) (fun a => absurd a.2 (Set.notMem_empty _))
  exact ⟨OrderEmbedding.ofStrictMono g hg⟩

/-- **The mixed template pair of a small well-order maps into an order-saturated homogeneous
sample (proved).** English (Lemma 8.3 proof): "the partial matches into a homogeneous sample,
extended by order saturation": for a bundled sample homogeneous in every arity whose order is
`κ`-order-saturated, every well-order `I` of size `< κ` embeds into the sample order and the
template pair `X_I ≤ Y_I` maps strongly into the sample along it. -/
theorem infra_83_mix_pair_into_saturated_sample {L₁ L₂ L : FirstOrder.Language.{u, u}}
    (χ : L₁ →ᴸ L₂) (ψ₂ : L₂ →ᴸ L) (φ₀ : K.τ →ᴸ L₁) {P : ∀ (M : Type u) [L.Structure M], Prop}
    {r r₁ r₀ : ℕ} [NeZero r] [NeZero r₁] [NeZero r₀]
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    (σ : Fin r₁ → Fin r) (τ : Fin r₀ → Fin r₁)
    (hPX : Hull83.SubHullStrong (ψ₂.comp χ) φ₀ P) (hPY : Hull83.SubHullStrong ψ₂ (χ.comp φ₀) P)
    {S : Hull83.ColorSample (Hull83.TpColorB L r)} {M : Type u} [L.Structure M] (hPM : P M)
    (hMK : K.Mem (Hull83.subModel' ψ₂ (χ.comp φ₀) M)) (base : S.α → Fin r → M)
    (hcol : ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m),
      S.col m s = Hull83.tpCode (Hull83.bundleOf base s h))
    (hhom : ∀ n, Hull83.Homog S n c) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (hsat : OrderSat83.OrderSaturated κ S.α) {I : Type u} [LinearOrder I] [WellFoundedLT I]
    [Nonempty I] (hI : #I < κ) :
    ∃ (e : I ↪o S.α) (onX : ((Hull83.subLangPieces (ψ₂.comp χ) φ₀ hc hcoh (σ ∘ τ) hPX).limit I).obj.carrier
        ↪[K.τ] (Hull83.subModel' (ψ₂.comp χ) φ₀ M).carrier)
      (onY : ((Hull83.subLangPieces ψ₂ (χ.comp φ₀) hc hcoh σ hPY).limit I).obj.carrier
        ↪[K.τ] (Hull83.subModel' ψ₂ (χ.comp φ₀) M).carrier),
      K.Strong onX ∧ K.Strong onY ∧
      (∀ x, onY ((Hull83.subLangMixHom χ ψ₂ φ₀ hc hcoh σ τ hPX hPY).limMap I x) = onX x) ∧
      (∀ (s : {s : Finset I // s.Nonempty}) p,
        onY (((Hull83.subLangPieces ψ₂ (χ.comp φ₀) hc hcoh σ hPY).limit I).canon s
          (Quotient.mk _ (FirstOrder.Language.Term.var p))) =
          (Hull83.bundleOf (fun i => base (e i)) s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm ∘
            Prod.map id σ) p) ∧
      ∀ (s : {s : Finset I // s.Nonempty}) p,
        onX (((Hull83.subLangPieces (ψ₂.comp χ) φ₀ hc hcoh (σ ∘ τ) hPX).limit I).canon s
          (Quotient.mk _ (FirstOrder.Language.Term.var p))) =
          (Hull83.bundleOf (fun i => base (e i)) s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2)).symm ∘
            Prod.map id (σ ∘ τ)) p  := by
  obtain ⟨e⟩ := infra_83_wellOrder_into_saturated hκ hsat hI
  exact ⟨e, infra_83_mix_pair_into_sample_along χ ψ₂ φ₀ hc hcoh σ τ hPX hPY hPM hMK base hcol
    hhom e⟩

/-- **Good evaluation indices from closure and the sort intersection (proved).** English (Lemma 8.3
proof, (7)): the evaluation `ret(code_i, -)` maps the sample's `Y` into its `X`; if the image of
`Y_I` in the sample is closed under `ret(code_i, -)` and meets the image of the sample's `X` only
in the image of `X_I` (the colors record that `Y`-terms landing in the `X` sort are `X`-terms),
then `ret(code_i, -)` sends the image of `Y_I` into the image of `X_I`. -/
theorem infra_83_good_of_closure {Xc Yc L XI YI : Type*} (incl : Xc → Yc) (F : Yc → L)
    (r : Yc → Xc) (onX : XI → Xc) (onY : YI → Yc) (inclI : XI → YI)
    (hcomm : ∀ x, onY (inclI x) = incl (onX x)) (g : L → L → L) (c : L)
    (hev : ∀ y, g c (F y) = F (incl (r y)))
    (hclosed : ∀ x, ∃ x', g c (F (onY x)) = F (onY x'))
    (hmeet : ∀ (x' : YI) (z : Xc), F (onY x') = F (incl z) → ∃ y, x' = inclI y) :
    ∀ x, ∃ y, g c (F (onY x)) = F (incl (onX y)) := by
  intro x
  obtain ⟨x', hx'⟩ := hclosed x
  obtain ⟨y, rfl⟩ := hmeet x' (r (onY x)) (hx'.symm.trans (hev _))
  exact ⟨y, hx'.trans (by rw [hcomm])⟩

/-- **Bounded-arity partial matches (proved).** English (Lemma 8.3 proof, "bounded horizontal
arity"): the samples supplied by the coherent colors (`Hull83.Joint … n c κ`) are homogeneous
only through a finite arity `n`; in such a sample the template pieces on supports of size at most
`n` embed compatibly, generators going to the bundles. -/
theorem infra_83_piece_matches_bounded {L : FirstOrder.Language.{u, u}}
    {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Hull83.Joint (Hull83.TpSampleB P r) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
      c m' hm' = Hull83.tpResB r f (c m hm))
    {S : Hull83.ColorSample (Hull83.TpColorB L r)} {M : Type u} [L.Structure M]
    (base : S.α → Fin r → M)
    (hcol : ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m),
      S.col m s = Hull83.tpCode (Hull83.bundleOf base s h))
    {n : ℕ} (hhom : Hull83.Homog S n c) :
    ∃ m : ∀ s : {s : Finset S.α // s.Nonempty ∧ s.card ≤ n},
        Hull83.Hull (L := L) (Hull83.witB hc s.1.card.pred).v ↪[L] M,
      (∀ s p, m s (Quotient.mk _ (FirstOrder.Language.Term.var p)) =
        Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2.1)).symm p) ∧
      ∀ {s t : {s : Finset S.α // s.Nonempty ∧ s.card ≤ n}} (h : s.1 ⊆ t.1),
        (m t).comp (Hull83.hullMapEmb (Prod.map (placeSucc h s.2.1 t.2.1) id)
          (Hull83.tpPieceB_tp hc hcoh (placeSucc h s.2.1 t.2.1))) = m s := by
  have key : ∀ s : {s : Finset S.α // s.Nonempty ∧ s.card ≤ n}, ∃ f :
      Hull83.Hull (L := L) (Hull83.witB hc s.1.card.pred).v ↪[L] M, ∀ p,
        f (Quotient.mk _ (FirstOrder.Language.Term.var p)) =
          Hull83.bundleOf base s.1 (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2.1)).symm p :=
    fun s => Hull83.piece_into_sample hc base hcol hhom
      ((Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr s.2.1)).le.trans s.2.2) s.1 _
  choose m hm using key
  refine ⟨m, hm, fun {s t} h => ?_⟩
  exact infra_83_hull_match_compat _ _ (m s) (m t) _ _ (hm s) (hm t)
    (fun p => infra_83_bundleOf_placeSucc base h s.2.1 t.2.1 _ _ p)

/-- **Matches carry designated constants (proved).** English (Lemma 8.3 proof): the marks of the
template are designated terms (mark constants); every match of a template hull into a sample
sends the hull element of a constant term to the constant of the sample. This is the
mark-preservation of the matches (`hb` of `infra_83_full_single_of_sample_arrows`). -/
theorem infra_83_hull_emb_const {L : FirstOrder.Language.{u, u}} {M N : Type u}
    [L.Structure M] [L.Structure N] {ι : Type} {v : ι → M}
    (f : Hull83.Hull (L := L) v ↪[L] N) (k : L.Constants) :
    f (Quotient.mk _ (FirstOrder.Language.Term.func k Fin.elim0)) =
      FirstOrder.Language.Structure.funMap k Fin.elim0 := by
  rw [infra_83_hull_mk_realize v, ← FirstOrder.Language.HomClass.realize_term]
  simp only [FirstOrder.Language.Term.realize]
  congr 1
  funext i
  exact Fin.elim0 i

/-- **Matches carry designated terms (proved).** More generally every match of a template hull
sends the class of a term to the term evaluated at the images of the generators. -/
theorem infra_83_hull_emb_term {L : FirstOrder.Language.{u, u}} {M N : Type u}
    [L.Structure M] [L.Structure N] {ι : Type} {v : ι → M}
    (f : Hull83.Hull (L := L) v ↪[L] N) (t : L.Term ι) :
    f (Quotient.mk _ t) =
      t.realize (fun p => f (Quotient.mk _ (FirstOrder.Language.Term.var p))) := by
  rw [infra_83_hull_mk_realize v, ← FirstOrder.Language.HomClass.realize_term]
  rfl

end AEC
