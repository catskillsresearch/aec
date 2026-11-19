module

public import AEC.Section8.Lemma83TupleDescent
public import AEC.Section8.Lemma83Isolation
public import AEC.Section7.IsolationTransfer
public import AEC.Section7.Prop78General
public import AEC.Section7.SeedStage
public import AEC.Section8.PairIsoSingle

@[expose] public section

/-!
# Lemma 8.3: all-domination from retraction images of bounded tuples only

Tuple form of `infra_83_dominated_of_retraction_pair`: the hypothesis that the retractions send
the image of the *whole* small upper object into the image of `X` is replaced by the paper's
"only images of the tested tuple have been placed in `X_H`".
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 3200000 in
/-- **All-domination from tuple retraction images (proved).** At a level `μ` closed for
Cor 6.15/6.16 and for Lemma 7.6 below `μ`, let `(onX, onY) : (X ≤ Y) → (X' ≤ Y')` be an arrow of
pairs carrying `b` to the mark `b'`, with `Y'` all-dominated over `X' + b'`, and let
`r_i : Y' → X'` (`|ι| = μ`) almost fix `X'`. If for every bounded tuple `c` of `Y` all retraction
images of `onY(b, c)` lie in `onX[X]`, then `Y` is all-dominated over `X + b`. -/
theorem infra_83_dominated_of_tuple_retractions (P : SingleModelData K) {μ : Cardinal.{u}}
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
    {bIdx : Type u} (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y))
    (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y'))
    (hb : ∀ i, onY.mapOcc (b i) = b' i) (hbμ : #bIdx < μ)
    (hdom : AllDominated incl' trivial bIdx b')
    (himg : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y)),
      #cIdx < μ → ∀ i (s : bIdx ⊕ cIdx), ∃ y : X.model.carrier,
        onX.onVertex (seqJoint b c s).1 y =
          (r i).onVertex (seqJoint b c s).1 (onY.onVertex (seqJoint b c s).1 (seqJoint b c s).2)) :
    AllDominated incl trivial bIdx b := by
  refine infra_83_dominated_descend_pair P hμC.1 hlev incl incl' onX onY hcomm b b' hb hbμ hdom
    (fun cIdx c hc => ?_)
  have hsum : #(bIdx ⊕ cIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_lt hμC.1).le hbμ hc
  let d : bIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 Y') :=
    fun s => ⟨(seqJoint b c s).1, onY.onVertex (seqJoint b c s).1 (seqJoint b c s).2⟩
  have H := infra_83_tied_from_retractions_tuple P hμC hμC le_rfl X' Y' X onX trivial incl'
    trivial r hιcard halmost d hsum (fun i s => himg cIdx c hc i s)
  have hx : d = seqJoint b' (fun j => onY.mapOcc (c j)) := by
    funext s
    rcases s with i | j
    · exact hb i
    · rfl
  have H2 := infra_78_tiedFreeMixed_host_transfer onX (asTuple incl trivial (seqJoint b c))
    ((asTuple incl' trivial d).restrict onX trivial) (asTuple incl' trivial d) (Equiv.refl _)
    onY trivial (Equiv.refl _)
    (fun x => (congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex PUnit.unit x)
      hcomm :))
    (fun k => rfl) hsum le_rfl le_rfl H
  rw [hx] at H2
  exact infra_83_tiedFree_of_mixed _ _ _ _ H2


set_option maxHeartbeats 3200000 in
/-- **Theorem 7.9 descent step from tuple retraction images (proved).** As
`infra_79_descent_bounded` (level-`l` pair `A ≤ U`, level-`ν` pair `A' ≤ U'`, `ν ≤ l`, commuting
square, `ν` retractions `r_i : U → A` almost fixing `A`, isolation of every `tp(b, c/A)` relative
to `b`), but with the whole-object hypothesis `r_i[toU[U']] ⊆ toA[A']` replaced by: for every
bounded tuple `c` of `U'`, the retraction images of `toU(b', c)` lie in `toA[A']`. -/
theorem infra_83_descent_of_tuple_retractions (P : SingleModelData K) {ν l : Cardinal.{u}}
    (hνC : ν ∈ infra_615_closed P) (hlC : l ∈ infra_615_closed P)
    (hνT : ν ∈ infra_78_closedTail P) (hlT : l ∈ infra_78_closedTail P) (hνl : ν ≤ l)
    (A U : P.scheme.Object l hlC.1) (A' U' : P.scheme.Object ν hνC.1)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A') (P.scheme.asSystem hlC.1 A))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 U') (P.scheme.asSystem hlC.1 U))
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hlC.1 A) (P.scheme.asSystem hlC.1 U))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A')
      (P.scheme.asSystem hνC.1 U'))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (htoU : P.scheme.permitted (X := U') (Y := U) toU)
    (hincl : P.scheme.permitted (X := A) (Y := U) incl)
    (hincl' : P.scheme.permitted (X := A') (Y := U') incl')
    (hsq : ∀ v, (incl.onVertex v).comp (toA.onVertex v) =
      (toU.onVertex v).comp (incl'.onVertex v))
    {ι : Type u} (r : ι → SystemArrow K oneVertexShape
      (P.scheme.asSystem hlC.1 U) (P.scheme.asSystem hlC.1 A))
    (hιcard : #ι = ν)
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 A),
      Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2})
    {uIdx : Type u} (huν : #uIdx < ν)
    (b' : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 U'))
    (bU : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U))
    (hbU : ∀ k, bU k = ⟨(b' k).1, toU.onVertex (b' k).1 (b' k).2⟩)
    (himg : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 U')),
      #cIdx < ν → ∀ i (s : uIdx ⊕ cIdx), ∃ y,
        toA.onVertex (seqJoint b' c s).1 y =
          (r i).onVertex (seqJoint b' c s).1 (toU.onVertex (seqJoint b' c s).1 (seqJoint b' c s).2))
    (hiso : ∀ {J : Type u} (c : J → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U)),
      #J < ν →
      IsRelativelyIsolated (uIdx := uIdx) (cIdx := J)
        (asTuple incl hincl (seqJoint bU c)) (Equiv.refl (uIdx ⊕ J))) :
    AllDominated incl' hincl' uIdx b' := by
  classical
  intro cIdx c hc
  have hν0 : ℵ₀ ≤ ν := P.aleph0_le hνC.1
  let d : uIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 U') := seqJoint b' c
  have hd : #(uIdx ⊕ cIdx) < ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hν0 huν hc
  let σ : Cardinal.{u} := max ℵ₀ #(uIdx ⊕ cIdx)
  have hσ : ℵ₀ ≤ σ := le_max_left _ _
  have hσν : σ < ν := max_lt (P.aleph0_lt hνC.1) hd
  let dU : uIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U) :=
    fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩
  have hT0 := infra_83_tied_from_retractions_tuple P hνC hlC hνl A U A' toA htoA incl hincl r
    hιcard halmost dU hd (fun i s => himg cIdx c hc i s)
  have hT := infra_78_tiedFreeMixed_host_transfer toA (asTuple incl' hincl' d)
    ((asTuple incl hincl dU).restrict toA htoA) (asTuple incl hincl dU) (Equiv.refl _)
    toU htoU (Equiv.refl _)
    (fun x => (congrArg (fun φ => φ x) (hsq PUnit.unit)).symm)
    (fun k => rfl) hd le_rfl hνl hT0
  have hS := infra_617_same_galois A U A' U' toA toU incl incl' htoA htoU hincl hincl' hsq d
  let c' : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U) :=
    fun j => ⟨(c j).1, toU.onVertex (c j).1 (c j).2⟩
  have hfun : dU = seqJoint bU c' := by
    funext j
    rcases j with k | j
    · exact (hbU k).symm
    · rfl
  have hI := hiso c' hc
  rw [← hfun] at hI
  exact infra_78_tied_descent_mixed P σ hσ hνC.1 (infra_79_closedTail_sigma2 hνT hσ hσν)
    (hlT.2.1 σ hσ (hσν.trans_le hνl)) hνl toA htoA (asTuple incl' hincl' d)
    (asTuple incl hincl _) (Equiv.refl _) (Equiv.refl _) rfl rfl (le_max_right _ _) hS hT hI


set_option maxHeartbeats 3200000 in
/-- **A pair mapping into a marked sample pair is marked, from tuple retraction images (proved).**
As `infra_83_marked_of_sample_arrow`, but the retractions need only send the image of each bounded
tuple `(b, c)` of `Y` into the image of `X` (the paper's "only images of the tested tuple have
been placed in `X_H`"). Conclusion: `b` realizes `p_X` and `Y` is all-dominated over `X + b`. -/
theorem infra_83_marked_of_sample_tuples (P : SingleModelData K)
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
    (b : N.bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y))
    (hb : ∀ i, onY.mapOcc (b i) = N.b i)
    (himg : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y)),
      #cIdx < ν → ∀ i (s : N.bIdx ⊕ cIdx), ∃ y,
        onX.onVertex (seqJoint b c s).1 y =
          (r i).onVertex (seqJoint b c s).1 (onY.onVertex (seqJoint b c s).1 (seqJoint b c s).2)) :
    (∃ realEq : N.bIdx ≃ (Pr.assign hνC.1 X).idx,
      SameGaloisType (asTuple incl trivial b) (Pr.assign hνC.1 X) realEq (Equiv.refl _)) ∧
    AllDominated incl trivial N.bIdx b := by
  have hfin : Finite N.bIdx := Finite.of_equiv _ (N.realEq.trans (Pr.arity N.hμ N.X)).symm
  refine ⟨infra_83_realizes_descend P Pr incl N.incl onX onY hcomm b N.b (Equiv.refl _) hb
    N.realEq N.realizes, ?_⟩
  obtain ⟨μ, hμ, NX, NY, nincl, hni, bIdx, nb, rE, hr, hd⟩ := N
  have hsq : ∀ v, (nincl.onVertex v).comp (onX.onVertex v) =
      (onY.onVertex v).comp (incl.onVertex v) := fun v =>
    (congrArg (fun φ : SystemArrow K oneVertexShape _ _ => φ.onVertex v) hcomm).symm
  have huν : #bIdx < ν :=
    (Cardinal.lt_aleph0_of_finite bIdx).trans_le (P.aleph0_le hνC.1)
  exact infra_83_descent_of_tuple_retractions P hνC hlC hνT hlT hνl NX NY X Y onX onY nincl incl
    trivial trivial trivial trivial hsq r hιcard halmost huν b nb (fun k => (hb k).symm) himg
    (fun c hJ => hd _ c (hJ.trans_le hνl))


set_option maxHeartbeats 3200000 in
/-- **The bounded-arity step of Lemma 8.3 for one matched tuple (proved).** Paper (proof of
Lemma 8.3, "Bounded horizontal arity"): `X_H` embeds into the sample's `X` by `toA`, the tested
list `u = (b, c)` of `Y_H` is identified with `u* = dU` of the sample (`tp(u/X_H) = tp(u*/X)`
restricted along `toA`: `hExt`), only the retraction images of `u*` are placed in `toA[X_H]`
(`himg`; (7) via Lemma 6.11), and `tp(u*/X)` is isolated relative to `b*` (all-domination of the
sample). Then Lemma 7.6 (mixed) gives that `tp(u/X_H)` is isolated relative to `b`. No arrow of
the whole of `Y_H` into the sample is used. -/
theorem infra_83_isolation_of_matched_tuple (P : SingleModelData K) {ν l : Cardinal.{u}}
    (hνC : ν ∈ infra_615_closed P) (hlC : l ∈ infra_615_closed P)
    (hνT : ν ∈ infra_78_closedTail P) (hlT : l ∈ infra_78_closedTail P) (hνl : ν ≤ l)
    (A U : P.scheme.Object l hlC.1) (A' Y' : P.scheme.Object ν hνC.1)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A') (P.scheme.asSystem hlC.1 A))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hlC.1 A) (P.scheme.asSystem hlC.1 U))
    (hincl : P.scheme.permitted (X := A) (Y := U) incl)
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A')
      (P.scheme.asSystem hνC.1 Y'))
    (hincl' : P.scheme.permitted (X := A') (Y := Y') incl')
    {ι : Type u} (r : ι → SystemArrow K oneVertexShape
      (P.scheme.asSystem hlC.1 U) (P.scheme.asSystem hlC.1 A))
    (hιcard : #ι = ν)
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 A),
      Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2})
    {uIdx cIdx : Type u}
    (d' : uIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y'))
    (dU : uIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U))
    (hd : #(uIdx ⊕ cIdx) < ν)
    (himg : ∀ i s, ∃ y, toA.onVertex (dU s).1 y = (r i).onVertex (dU s).1 (dU s).2)
    (hExt : SameGaloisType (asTuple incl' hincl' d')
      ((asTuple incl hincl dU).restrict toA htoA) (Equiv.refl _) (Equiv.refl _))
    (hIso : IsRelativelyIsolated (uIdx := uIdx) (cIdx := cIdx) (asTuple incl hincl dU)
      (Equiv.refl _)) :
    IsRelativelyIsolated (uIdx := uIdx) (cIdx := cIdx) (asTuple incl' hincl' d')
      (Equiv.refl _) := by
  classical
  have hν0 : ℵ₀ ≤ ν := P.aleph0_le hνC.1
  let σ : Cardinal.{u} := max ℵ₀ #(uIdx ⊕ cIdx)
  have hσ : ℵ₀ ≤ σ := le_max_left _ _
  have hσν : σ < ν := max_lt (P.aleph0_lt hνC.1) hd
  have hT0 := infra_83_tied_from_retractions_tuple P hνC hlC hνl A U A' toA htoA incl hincl r
    hιcard halmost dU hd himg
  have hT := infra_78_tiedFreeMixed_left_congr toA
    (q := (asTuple incl hincl dU).restrict toA htoA) (q' := asTuple incl' hincl' d')
    (Equiv.refl _) (Equiv.refl _) hT0 (fun {β} Z hβ => by
      have hsz : #((uIdx ⊕ cIdx) ⊕ β) < ν := by
        rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        exact Cardinal.add_lt_of_lt hν0 hd hβ
      have D := infra_78_diagramEq_of_sameGalois hExt Z hsz (hsz.trans_le hνl)
      exact infra_73_diagramEq_of_eq D (by rintro (k | x) <;> rfl) (by rintro (k | x) <;> rfl))
  exact infra_78_tied_descent_mixed P σ hσ hνC.1 (infra_79_closedTail_sigma2 hνT hσ hσν)
    (hlT.2.1 σ hσ (hσν.trans_le hνl)) hνl toA htoA (asTuple incl' hincl' d')
    (asTuple incl hincl dU) (Equiv.refl _) (Equiv.refl _) rfl rfl (le_max_right _ _) hExt hT hIso


/-- **All-domination from matched bounded tuples (proved).** Paper (Lemma 8.3, "the actual sample
pair is all-dominated" at bounded arity): if for every bounded tuple `c` of `Y'` there is a pair
`A ≤ U` at a closed level `l ≥ ν` (an actual sample pair) with an arrow `toA : X' → A`, `ν`
retractions `r_i : U → A` almost fixing `A`, and a tuple `u* = dU` of `U` identified with `(b, c)`
over `X'` (`SameGaloisType` along `toA`) whose retraction images lie in `toA[X']` and whose type
over `A` is isolated relative to its first part, then `Y'` is all-dominated over `X' + b`.
The matching data may vary with `c` (bounded lists; no arrow of the whole `Y'`). -/
theorem infra_83_dominated_of_matched_tuples (P : SingleModelData K) {ν : Cardinal.{u}}
    (hνC : ν ∈ infra_615_closed P) (hνT : ν ∈ infra_78_closedTail P)
    {X' Y' : P.scheme.Object ν hνC.1}
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X')
      (P.scheme.asSystem hνC.1 Y'))
    (hincl' : P.scheme.permitted (X := X') (Y := Y') incl')
    {bIdx : Type u} [Finite bIdx]
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y'))
    (hmatch : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y')),
      #cIdx < ν →
      ∃ (l : Cardinal.{u}) (hlC : l ∈ infra_615_closed P) (_ : l ∈ infra_78_closedTail P)
        (_ : ν ≤ l) (A U : P.scheme.Object l hlC.1)
        (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X')
          (P.scheme.asSystem hlC.1 A))
        (htoA : P.scheme.permitted (X := X') (Y := A) toA)
        (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hlC.1 A)
          (P.scheme.asSystem hlC.1 U))
        (hincl : P.scheme.permitted (X := A) (Y := U) incl)
        (ι : Type u) (r : ι → SystemArrow K oneVertexShape
          (P.scheme.asSystem hlC.1 U) (P.scheme.asSystem hlC.1 A))
        (_ : #ι = ν)
        (_ : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 A),
          Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2})
        (dU : bIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U)),
        (∀ i s, ∃ y, toA.onVertex (dU s).1 y = (r i).onVertex (dU s).1 (dU s).2) ∧
        SameGaloisType (asTuple incl' hincl' (seqJoint b c))
          ((asTuple incl hincl dU).restrict toA htoA) (Equiv.refl _) (Equiv.refl _) ∧
        IsRelativelyIsolated (uIdx := bIdx) (cIdx := cIdx) (asTuple incl hincl dU)
          (Equiv.refl _)) :
    AllDominated incl' hincl' bIdx b := by
  intro cIdx c hc
  obtain ⟨l, hlC, hlT, hνl, A, U, toA, htoA, incl, hincl, ι, r, hιcard, halmost, dU, himg, hExt,
    hIso⟩ := hmatch cIdx c hc
  have hν0 : ℵ₀ ≤ ν := P.aleph0_le hνC.1
  have hd : #(bIdx ⊕ cIdx) < ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hν0 ((Cardinal.lt_aleph0_of_finite bIdx).trans_le hν0) hc
  exact infra_83_isolation_of_matched_tuple P hνC hlC hνT hlT hνl A U X' Y' toA htoA incl hincl
    incl' hincl' r hιcard halmost (seqJoint b c) dU hd himg hExt hIso


set_option maxHeartbeats 3200000 in
/-- **All-domination from bounded matches into marked sample pairs (proved).** As
`infra_83_dominated_of_matched_tuples`, with each match landing in a marked pair `N` (closed level
`≥ ν`) with its Cor 6.16 family `R`: `ν` distinguished retraction indices send `u* = (N.b ∘ τ, c*)`
into `toA[X']`, and `u*` is identified with `(b, c)` over `X'`. Isolation of `tp(u*/N.X)` relative
to the mark is read off from the all-domination of `N` (reindexed along `τ`). -/
theorem infra_83_dominated_of_marked_matches (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {ν : Cardinal.{u}}
    (hνC : ν ∈ infra_615_closed P) (hνT : ν ∈ infra_78_closedTail P)
    {X' Y' : P.scheme.Object ν hνC.1}
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X')
      (P.scheme.asSystem hνC.1 Y'))
    (hincl' : P.scheme.permitted (X := X') (Y := Y') incl')
    {bIdx : Type u} [Finite bIdx]
    (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y'))
    (hmatch : ∀ (cIdx : Type u) (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 Y')),
      #cIdx < ν →
      ∃ (N : MarkedPair K oneVertexShape P.scheme Pr) (hlC : N.μ ∈ infra_615_closed P)
        (_ : N.μ ∈ infra_78_closedTail P) (_ : ν ≤ N.μ)
        (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 X')
          (P.scheme.asSystem hlC.1 N.X))
        (htoA : P.scheme.permitted (X := X') (Y := N.X) toA)
        (R : ApproximateRetraction K oneVertexShape P.scheme N.hμ N.X N.Y N.incl)
        (S : Set R.index) (_ : #S = ν) (τ : bIdx ≃ N.bIdx)
        (cU : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 N.Y)),
        (∀ i ∈ S, ∀ s, ∃ y, toA.onVertex (seqJoint (fun a => N.b (τ a)) cU s).1 y =
          (R.retr i).onVertex (seqJoint (fun a => N.b (τ a)) cU s).1
            (seqJoint (fun a => N.b (τ a)) cU s).2) ∧
        SameGaloisType (asTuple incl' hincl' (seqJoint b c))
          ((asTuple N.incl N.incl_arrow (seqJoint (fun a => N.b (τ a)) cU)).restrict toA htoA)
          (Equiv.refl _) (Equiv.refl _)) :
    AllDominated incl' hincl' bIdx b := by
  refine infra_83_dominated_of_matched_tuples P hνC hνT incl' hincl' b (fun cIdx c hc => ?_)
  obtain ⟨N, hlC, hlT, hνl, toA, htoA, R, S, hS, τ, cU, himg, hExt⟩ := hmatch cIdx c hc
  have hIso := infra_82_isolated_reindex_mark N.incl τ N.b cU
    (N.dominated cIdx cU (hc.trans_le hνl))
  refine ⟨N.μ, hlC, hlT, hνl, N.X, N.Y, toA, htoA, N.incl, N.incl_arrow, S,
    fun i => R.retr i.1, hS, fun a => ?_, seqJoint (fun a => N.b (τ a)) cU,
    fun i s => himg i.1 i.2 s, hExt, hIso⟩
  haveI := R.almost_id a
  exact Finite.of_injective (β := {i : R.index // (R.retr i).onVertex a.1
    (N.incl.onVertex a.1 a.2) ≠ a.2}) (fun i => ⟨i.1.1, i.2⟩)
    (fun x y h => Subtype.ext (Subtype.ext (congrArg Subtype.val h :)))

end
end AEC
