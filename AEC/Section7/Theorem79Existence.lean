module

public import AEC.Section7.Theorem79
public import AEC.Section6.DescentRetractionTied
public import AEC.Section7.MixedDescent

@[expose] public section

/-!
# Theorem 7.9, existence clause: split (cycle 70)

Paper proof of the existence clause: "Choose `λ > ν` sufficiently closed and lift `X` to level
`λ` (`lift_isolate`). Proposition 7.8 at `λ` with `θ = ν` gives `A ≤ U` and `b` with every
`tp(b, c/A)`, `|c| ≤ ν`, isolated relative to `b`. Corollary 6.16 gives `ν` approximate
retractions `r_i : U → A`; close a level-`ν` pair `A' ≤ U'` under them, containing the image of
`X` and `b` (`retraction_pair`). For `d ⊆ U'` with `|d| < ν`, Lemma 6.17 makes `tp(d/A)` the tied
free lift of `tp(d/A'; U')`, and mixed Lemma 7.6 descends isolation (`descent`). Retained anchors
and bounded diagram homogeneity identify `A'` with `X` carrying the marginal of `b` to `p`
(`identify`)."

* `infra_79_descent` (proved, this file): the descent step.
* `infra_79_lift_isolate`, `infra_79_retraction_pair`, `infra_79_identify`, `infra_79_tail`:
  open (tracked in HOLES.md under `infra_79_existence`).
-/

universe u

open Cardinal FirstOrder
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- Levels in `infra_78_closedTail` lie in the `σ₂(σ)`-tail for every infinite `σ` below them. -/
theorem infra_79_closedTail_sigma2 {P : SingleModelData K} {ν σ : Cardinal.{u}}
    (hν : ν ∈ infra_78_closedTail P) (hσ : ℵ₀ ≤ σ) (hσν : σ < ν) :
    ν ∈ infra_73_tailSet P (infra_76_sigma2 P σ) := by
  have h1 : infra_73_h P σ < ν :=
    (le_max_right _ _).trans_lt ((Order.lt_succ_of_not_isMax (not_isMax _)).trans_le
      (hν.2.1 σ hσ hσν).2)
  have hσ1 : ℵ₀ ≤ infra_73_h P σ := hσ.trans (infra_76_lt_h P σ).le
  have h2 : infra_73_h P (infra_73_h P σ) < ν :=
    (le_max_right _ _).trans_lt ((Order.lt_succ_of_not_isMax (not_isMax _)).trans_le
      (hν.2.1 _ hσ1 h1).2)
  exact hν.2.1 _ (hσ1.trans (infra_76_lt_h P _).le) h2

/-- **Theorem 7.9, descent step (proved).** Level-`λ` pair `A ≤ U`, level-`ν` pair `A' ≤ U'`
(`ν ≤ λ`, both closed levels) with a commuting square and `ν` approximate retractions
`r_i : U → A` that almost fix `A` and send `U'` into `A'`. If every `tp(b, c/A)` with `|c| < ν`
is isolated relative to `b` (the image of a finite `b'` in `U'`), then `U'` is all-dominated over
`A' + b'`. Lemma 6.17 (tied) gives the tied free lift; mixed Lemma 7.6
(`infra_78_tied_descent_mixed`) descends isolation, with fragment parameter `|b, c| < ν`. -/
theorem infra_79_descent (P : SingleModelData K) {ν l : Cardinal.{u}}
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
    (hιcard : #ι = ν) (_hr : ∀ i, P.scheme.permitted (X := U) (Y := A) (r i))
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 A),
      Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2})
    (himg : ∀ i (x : ((P.scheme.asSystem hνC.1 U').obj PUnit.unit).carrier),
      ∃ y, toA.onVertex PUnit.unit y = (r i).onVertex PUnit.unit (toU.onVertex PUnit.unit x))
    {uIdx : Type u} [Finite uIdx]
    (b' : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 U'))
    (bU : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U))
    (hbU : ∀ k, bU k = ⟨(b' k).1, toU.onVertex (b' k).1 (b' k).2⟩)
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
    exact Cardinal.add_lt_of_lt hν0 ((Cardinal.lt_aleph0_of_finite uIdx).trans_le hν0) hc
  let σ : Cardinal.{u} := max ℵ₀ #(uIdx ⊕ cIdx)
  have hσ : ℵ₀ ≤ σ := le_max_left _ _
  have hσν : σ < ν := max_lt (P.aleph0_lt hνC.1) hd
  have hT := infra_617_tied_from_retractions P hνC hlC hνl A U A' U' toA toU incl incl'
    htoA htoU hincl hincl' hsq r hιcard halmost himg d hd
  have hS := infra_617_same_galois A U A' U' toA toU incl incl' htoA htoU hincl hincl' hsq d
  let c' : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U) :=
    fun j => ⟨(c j).1, toU.onVertex (c j).1 (c j).2⟩
  have hfun : (fun j => (⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U))) = seqJoint bU c' := by
    funext j
    rcases j with k | j
    · exact (hbU k).symm
    · rfl
  have hI := hiso c' hc
  rw [← hfun] at hI
  exact infra_78_tied_descent_mixed P σ hσ hνC.1 (infra_79_closedTail_sigma2 hνT hσ hσν)
    (hlT.2.1 σ hσ (hσν.trans_le hνl)) hνl toA htoA (asTuple incl' hincl' d)
    (asTuple incl hincl _) (Equiv.refl _) (Equiv.refl _) rfl rfl (le_max_right _ _) hS hT hI

/-- **Right congruence of mixed tied freeness along a Galois type (proved).** The conclusion of
`IsTiedFreeMixed` only reads bounded diagrams of the upper tuple over its base, which a
`SameGaloisType` preserves (`infra_78_diagramEq_of_sameGalois`). -/
theorem infra_79_tiedFreeMixed_right_congr {P : SingleModelData K} {ν μ : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    {q : TupleOver K oneVertexShape P.scheme hν A}
    {qB qB' : TupleOver K oneVertexShape P.scheme hμ B} (eB : q.idx ≃ qB.idx)
    (e' : qB.idx ≃ qB'.idx) (H : IsTiedFreeMixed f q qB eB)
    (hS : SameGaloisType qB qB' e' (Equiv.refl _))
    (hidx : #q.idx < ν) (hν1 : ν ≤ qB.ν) (hν2 : ν ≤ qB'.ν) :
    IsTiedFreeMixed f q qB' (eB.trans e') := by
  classical
  intro seq ι Z Z0 hlen hιτ hιν hmove
  have d := H seq Z Z0 hlen hιτ hιν hmove
  have hsz : #(qB'.idx ⊕ ι) < ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id,
      ← Cardinal.mk_congr (eB.trans e')]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hν) hidx hιν
  have D := infra_78_diagramEq_of_sameGalois hS Z (hsz.trans_le hν1) (hsz.trans_le hν2)
  have D' := infra_612_dEq_transport D (Equiv.sumCongr (eB.trans e') (Equiv.refl ι))
    (xs' := infra_612_anchored eB qB.incl qB.val Z)
    (ys' := infra_612_anchored (eB.trans e') qB'.incl qB'.val Z)
    (by
      rintro (k | x)
      · change qB.val (eB k) = qB.val (e'.symm (e' (eB k)))
        rw [Equiv.symm_apply_apply]
      · rfl)
    (by rintro (k | x) <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ d D'

/-- **Theorem 7.9, lift and isolate (proved).** Paper: "lift `X` to a sufficiently closed level
`λ > ν` and apply Proposition 7.8 there with `θ = ν`." For `p` over `X` at its own level `ν`:
a presentation arrow `ι : X → B` to level `λ`, the mixed tied free lift of `p`
(`infra_78_tied_free_lift_mixed`), and Proposition 7.8 at `λ`
(`infra_78_marginal_general_level`) with `θ = ν`. Output in the form used by
`infra_78_marginal_identify_level`: the restriction of the upper mark to `X` has the bounded
diagrams of `p`, the upper mark is its mixed tied free lift, and every `tp(b, c/B)` with `|c| ≤ ν`
is isolated relative to `b`. -/
theorem infra_79_lift_isolate (P : SingleModelData K) {ν l : Cardinal.{u}}
    (hν : ν ∈ infra_78_closedTail P) (hl : l ∈ infra_78_closedTail P) (hνl : ν < l)
    (X : P.scheme.Object ν hν.1) (p : TupleOver K oneVertexShape P.scheme hν.1 X)
    (hpν : p.ν = ν) [Finite p.idx] :
    ∃ (B U : P.scheme.Object l hl.1)
      (ι : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 X) (P.scheme.asSystem hl.1 B))
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hl.1 B) (P.scheme.asSystem hl.1 U))
      (bU : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hl.1 U)),
      (∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν.1 X)), #β < ν →
        P.scheme.DiagramEq (X := p.host) (Y := U) (typeJoint (p := p) Z)
          (typeJoint (p := (asTuple f trivial bU).restrict ι trivial) Z)) ∧
      IsTiedFreeMixed ι ((asTuple f trivial bU).restrict ι trivial) (asTuple f trivial bU)
        (Equiv.refl _) ∧
      ∀ {J : Type u} (c : J → Occurrence K oneVertexShape (P.scheme.asSystem hl.1 U)),
        #J ≤ ν →
        IsRelativelyIsolated (uIdx := p.idx) (cIdx := J)
          (asTuple f trivial (seqJoint bU c)) (Equiv.refl (p.idx ⊕ J)) := by
  classical
  have hlt : ℵ₀ < ν := P.aleph0_lt hν.1
  have hν0 : ℵ₀ ≤ ν := hlt.le
  obtain ⟨B, ⟨ι⟩⟩ := infra_78_presentation_arrow hν.1 hl.1 hνl.le X
  have hrec : ν ∈ recursionClosedLevels P ℵ₀ := (hν.2.1 ℵ₀ le_rfl hlt).1
  have hrecl : l ∈ recursionClosedLevels P ℵ₀ := (hl.2.1 ℵ₀ le_rfl (hlt.trans hνl)).1
  have hidx : #p.idx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite p.idx).le
  obtain ⟨qB, eB, hqν, hD, hT⟩ := infra_78_tied_free_lift_mixed P ℵ₀ le_rfl hν.1 hrec
    (Order.succ_le_of_lt hlt) hl.1 hrecl hνl.le ι trivial p hpν hidx
  let q0 : TupleOver K oneVertexShape P.scheme hl.1 B :=
    ⟨qB.ν, qB.hν, qB.host, qB.incl, qB.incl_arrow, p.idx, fun k => qB.val (eB k)⟩
  have hT0 : IsTiedFreeMixed ι p q0 (Equiv.refl _) := by
    intro seq ι' Z Z0 hlen hιτ hιν hmove
    exact infra_73_diagramEq_of_eq (hT seq Z Z0 hlen hιτ hιν hmove) (fun _ => rfl)
      (by rintro (k | x) <;> rfl)
  have hD0 : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν.1 X)),
      #β < ν → P.scheme.DiagramEq (X := p.host) (Y := q0.host) (typeJoint (p := p) Z)
        (typeJoint (p := q0.restrict ι trivial) Z) := fun Z hβ =>
    infra_73_diagramEq_of_eq (hD Z hβ) (fun _ => rfl) (by
      rintro (k | x)
      · change qB.val (eB.symm.symm k) = qB.val (eB k)
        rfl
      · rfl)
  have : Finite q0.idx := inferInstanceAs (Finite p.idx)
  obtain ⟨U, f, hf, b, hgal, hiso⟩ :=
    infra_78_marginal_general_level P l hl B q0 ν inferInstance hν0 hνl
  let q : TupleOver K oneVertexShape P.scheme hl.1 B := asTuple f trivial b
  have hidxν : #p.idx < ν := (Cardinal.lt_aleph0_of_finite p.idx).trans hlt
  have hq0ν : ν ≤ q0.ν := by
    change ν ≤ qB.ν
    rw [hqν]; exact hνl.le
  have hgal' : SameGaloisType q0 q (Equiv.refl q0.idx) (Equiv.refl q.idx) := hgal
  have hqν' : ν ≤ q.ν := hνl.le
  have hTq : IsTiedFreeMixed ι p q ((Equiv.refl p.idx).trans (Equiv.refl q0.idx)) :=
    infra_79_tiedFreeMixed_right_congr (q := p) (qB := q0) (qB' := q) ι (Equiv.refl p.idx)
      (Equiv.refl q0.idx) hT0 hgal' hidxν hq0ν hqν'
  have hseed : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν.1 X)),
      #β < ν → P.scheme.DiagramEq (X := p.host) (Y := U) (typeJoint (p := p) Z)
        (typeJoint (p := q.restrict ι trivial) Z) := by
    intro β Z hβ
    have hsz : #(p.idx ⊕ β) < ν := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.add_lt_of_lt hν0 hidxν hβ
    let Z' : β → Occurrence K oneVertexShape (P.scheme.asSystem hl.1 B) :=
      fun j => ⟨(Z j).1, ι.onVertex (Z j).1 (Z j).2⟩
    have D2 := infra_78_diagramEq_of_sameGalois hgal Z' (hsz.trans_le hq0ν)
      (hsz.trans_le hνl.le)
    have D2' : P.scheme.DiagramEq (X := q0.host) (Y := U)
        (typeJoint (p := q0.restrict ι trivial) Z) (typeJoint (p := q.restrict ι trivial) Z) :=
      infra_73_diagramEq_of_eq D2 (by rintro (k | x) <;> rfl) (by rintro (k | x) <;> rfl)
    exact P.scheme.diagram_trans _ _ _ _ _ _ (hD0 Z hβ) D2'
  let qr : TupleOver K oneVertexShape P.scheme hν.1 X := q.restrict ι trivial
  have hTr : IsTiedFreeMixed ι qr q ((Equiv.refl p.idx).trans
      ((Equiv.refl p.idx).trans (Equiv.refl q0.idx))) :=
    infra_78_tiedFreeMixed_left_congr (q := p) (q' := qr) (qB := q) ι
      ((Equiv.refl p.idx).trans (Equiv.refl q0.idx)) (Equiv.refl p.idx) hTq (fun Z hβ => by
      refine P.scheme.diagram_symm _ _ _ _ ?_
      exact infra_73_diagramEq_of_eq (hseed Z hβ) (by rintro (k | x) <;> rfl)
        (fun _ => rfl))
  refine ⟨B, U, ι, f, b, hseed, hTr, ?_⟩
  intro J c hc
  exact hiso c hc

/-- **Theorem 7.9, identify (proved).** Paper: "Retained anchors and bounded diagram homogeneity
identify `A'` with `X` by an isomorphism carrying the marginal of `b` to `p`." Given the output of
`infra_79_lift_isolate` and a level-`ν` pair `A' ≤ U'` over `B ≤ U` (commuting square, `A'`
containing the image of `X`, `b'` in `U'` over the upper mark), there is a structural isomorphism
`φ : X ≅ A'` with `tp(b'/X; U')` (along `φ`) equal to `p`. Proof: a Lemma 6.9 approximation
sequence for `p` (`infra_78_tied_at_mixed`), transferred to the restricted upper mark, and
`infra_78_marginal_identify_level`. -/
theorem infra_79_identify (P : SingleModelData K) {ν l : Cardinal.{u}}
    (hν : ν ∈ infra_78_closedTail P) (hl : l ∈ P.eligible) (hνl : ν ≤ l)
    (X : P.scheme.Object ν hν.1) (p : TupleOver K oneVertexShape P.scheme hν.1 X)
    (hpν : p.ν = ν) [Finite p.idx]
    {B U : P.scheme.Object l hl}
    (ι : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 X) (P.scheme.asSystem hl B))
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hl B) (P.scheme.asSystem hl U))
    (bU : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hl U))
    (hseed : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν.1 X)),
      #β < ν →
      P.scheme.DiagramEq (X := p.host) (Y := U) (typeJoint (p := p) Z)
        (typeJoint (p := (asTuple f trivial bU).restrict ι trivial) Z))
    (hT : IsTiedFreeMixed ι ((asTuple f trivial bU).restrict ι trivial) (asTuple f trivial bU)
      (Equiv.refl _))
    {A' U' : P.scheme.Object ν hν.1}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 A') (P.scheme.asSystem hl B))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 U') (P.scheme.asSystem hl U))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 A')
      (P.scheme.asSystem hν.1 U'))
    (hsq : ∀ v, (f.onVertex v).comp (toA.onVertex v) = (toU.onVertex v).comp (incl'.onVertex v))
    (b' : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν.1 U'))
    (hbU : ∀ k, bU k = ⟨(b' k).1, toU.onVertex (b' k).1 (b' k).2⟩)
    (hX : ∀ x, ∃ y, toA.onVertex PUnit.unit y = ι.onVertex PUnit.unit x) :
    ∃ φ : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 X) (P.scheme.asSystem hν.1 A'),
      P.scheme.IsStructIso (X := X) (Y := A') φ ∧
      SameGaloisType p (asTuple (SystemArrow.comp φ incl') trivial b')
        (Equiv.refl p.idx) (Equiv.refl p.idx) := by
  classical
  have hlt : ℵ₀ < ν := P.aleph0_lt hν.1
  have hrec : ν ∈ recursionClosedLevels P ℵ₀ := (hν.2.1 ℵ₀ le_rfl hlt).1
  have hidx : #p.idx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite p.idx).le
  obtain ⟨seq, -, -, -, -, htest, hlong, hτν, -⟩ := infra_78_tied_at_mixed P ℵ₀ le_rfl hν.1 hrec
    (Order.succ_le_of_lt hlt) hl hνl ι trivial p hpν hidx ℵ₀ hlt
  let q : TupleOver K oneVertexShape P.scheme hl B := asTuple f trivial bU
  let seqq : ApproximationSequence (q.restrict ι trivial) :=
    infra_78_seq_diagram_transfer (t2 := q.restrict ι trivial) (Equiv.refl p.idx) seq
      (fun Z hZ => by
        refine infra_73_diagramEq_of_eq (hseed Z (hZ.trans_lt hτν)) (fun _ => rfl) ?_
        rintro (u | x) <;> rfl)
  have hseed' : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν.1 X)),
      #β < ν →
      P.scheme.DiagramEq (X := p.host) (Y := q.host)
        (alignJoint (Equiv.refl _) (typeJoint (p := p) Z))
        (typeJoint (p := q.restrict ι trivial) Z) := fun Z hβ =>
    infra_73_diagramEq_of_eq (hseed Z hβ) (by rintro (u | x) <;> rfl) (fun _ => rfl)
  have hanch : ∀ a k, ∃ y, toA.onVertex PUnit.unit y =
      ι.onVertex PUnit.unit (seqq.family a k).2 := fun a k => hX _
  have hsq' : ∀ x, toU.onVertex PUnit.unit (incl'.onVertex PUnit.unit x) =
      q.incl.onVertex PUnit.unit (toA.onVertex PUnit.unit x) := fun x =>
    (DFunLike.congr_fun (hsq PUnit.unit) x).symm
  obtain ⟨φ, hφ, -, hGal⟩ := infra_78_marginal_identify_level P ℵ₀ le_rfl hν.1 (hμ := hl) hrec
    hlt hνl (A := A') (U := U') p hpν hidx ι trivial q hνl (Equiv.refl _) hseed' hT seqq
    htest hlong toA hanch incl' toU hsq' b' hbU
  exact ⟨φ, hφ, hGal⟩

/-- **Theorem 7.9, retraction pair (open).** Paper: "Corollary 6.16 gives `ν` approximate
retractions `r_i : U → B` (each `a ∈ B` fixed by all but finitely many); close a level-`ν` pair
`A' ≤ U'` under them, containing the image of `X` and the mark." For a level-`λ` pair `B ≤ U`
(`λ` closed, `ν ≤ λ` eligible), a map `ι : X → B` from a level-`ν` object and a finite mark `bU`
in `U`: a level-`ν` pair `A' ≤ U'` with a commuting square into `B ≤ U`, `A' ⊇ ι[X]`, the mark
in `U'`, and `ν` arrows `U → B` almost fixing `B` and sending `U'` into `A'`. Planned proof:
`corollary_6_16_family` at `λ` (index of size `λ`; restrict to `ν` indices, which keeps the
almost-fixing property), then an `ω`-chain of `infra_78_mixed_ls_pair` hulls closed under the `ν`
retractions and its union (`infra_78_theta_union`). -/
def infra_79_retraction_pair_statement (P : SingleModelData K) : Prop :=
  ∀ ν l (hν : ν ∈ P.eligible) (hl : l ∈ infra_615_closed P), ν ≤ l →
    ∀ (X : P.scheme.Object ν hν) (B U : P.scheme.Object l hl.1)
      (ι : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hl.1 B))
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hl.1 B) (P.scheme.asSystem hl.1 U))
      {uIdx : Type u} [Finite uIdx]
      (bU : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hl.1 U)),
    ∃ (A' U' : P.scheme.Object ν hν)
      (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hl.1 B))
      (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hl.1 U))
      (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hν U'))
      (b' : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν U'))
      (ιs : Type u)
      (r : ιs → SystemArrow K oneVertexShape (P.scheme.asSystem hl.1 U) (P.scheme.asSystem hl.1 B)),
      (∀ v, (f.onVertex v).comp (toA.onVertex v) = (toU.onVertex v).comp (incl'.onVertex v)) ∧
      (∀ k, bU k = ⟨(b' k).1, toU.onVertex (b' k).1 (b' k).2⟩) ∧
      (∀ x, ∃ y, toA.onVertex PUnit.unit y = ι.onVertex PUnit.unit x) ∧
      #ιs = ν ∧
      (∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hl.1 B),
        Finite {i : ιs // (r i).onVertex a.1 (f.onVertex a.1 a.2) ≠ a.2}) ∧
      (∀ i (x : ((P.scheme.asSystem hν U').obj PUnit.unit).carrier),
        ∃ y, toA.onVertex PUnit.unit y = (r i).onVertex PUnit.unit (toU.onVertex PUnit.unit x))

/-- **Theorem 7.9 tail (open).** The closure tail of Proposition 7.8 and the closed levels of
Section 6 (Corollary 6.16 / Lemma 6.17) meet unboundedly ("sufficiently closed" in the paper means
all the finitely many closure conditions at once). Planned proof: interleave the two `ω`-towers
(`infra_78_closedTower`, `infra_615_tower`); the supremum lies in both. -/
def infra_79_tail_statement (P : SingleModelData K) : Prop :=
  ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ infra_78_closedTail P ∧ μ ∈ infra_615_closed P

/-- **Existence clause of Theorem 7.9 from its open parts (proved).** On the tail
`infra_78_closedTail P ∩ infra_615_closed P`: a level-`μ` copy `p'` of `p`
(`infra_612_exists_level_copy`), a closed `λ > μ`, `infra_79_lift_isolate`, the retraction pair,
`infra_79_descent` (all-dominated over `A' + b'`), `infra_79_identify` (`φ : X ≅ A'`), the renaming
`infra_78_iso_rename_asTuple`, and cross-level Galois transitivity `p ~ p' ~ b'`. -/
theorem infra_79_existence_of_parts (P : SingleModelData K)
    (h : infra_79_tail_statement P ∧ infra_79_retraction_pair_statement P) :
    infra_79_existence_statement P := by
  classical
  obtain ⟨htail, hrp⟩ := h
  have hT : Tail P.eligible (infra_78_closedTail P ∩ infra_615_closed P) :=
    ⟨fun μ hμ => hμ.1.1, fun κ => by
      obtain ⟨μ, hκμ, h1, h2⟩ := htail κ
      exact ⟨μ, hκμ, h1, h2⟩⟩
  refine ⟨_, hT, fun μ hμ X p hfin => ?_⟩
  have hlt : ℵ₀ < μ := P.aleph0_lt hμ.1.1
  have hidx0 : #p.idx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite p.idx).le
  obtain ⟨host, incl, hincl, val, h12⟩ :=
    infra_612_exists_level_copy p (hidx0.trans hlt.le)
  let p' : TupleOver K oneVertexShape P.scheme hμ.1.1 X := ⟨μ, hμ.1.1, host, incl, hincl, p.idx, val⟩
  have : Finite p'.idx := hfin
  obtain ⟨l, hμl', hlT, hlC⟩ := htail (Order.succ μ)
  have hμl : μ < l := (Order.lt_succ_of_not_isMax (not_isMax μ)).trans_le hμl'
  obtain ⟨B, U, ι, f, bU, hseed, hTf, hiso⟩ := infra_79_lift_isolate P hμ.1 hlT hμl X p' rfl
  obtain ⟨A', U', toA, toU, incl', b', ιs, r, hsq, hbU, hX, hcard, halmost, himg⟩ :=
    hrp μ l hμ.1.1 hlC hμl.le X B U ι f bU
  have hdom := infra_79_descent P hμ.2 hlC hμ.1 hlT hμl.le B U A' U' toA toU f incl' trivial
    trivial trivial trivial hsq r hcard (fun _ => trivial) halmost himg b' bU hbU
    (fun c hc => hiso c hc.le)
  obtain ⟨φ, hφ, hgal⟩ := infra_79_identify P hμ.1 hlT.1 hμl.le X p' rfl ι f bU hseed hTf toA toU
    incl' hsq b' hbU hX
  refine ⟨U', SystemArrow.comp φ incl', trivial, b', ?_, ?_⟩
  · intro cIdx c hc
    have hc' := hdom cIdx c hc
    have hv : (Sum.elim b' c : p.idx ⊕ cIdx → _) = seqJoint b' c := by
      funext s; rcases s with k | j <;> rfl
    apply infra_78_iso_rename_asTuple φ hφ incl' b' c
    rw [hv]
    exact hc'
  · have hrec : μ ∈ recursionClosedLevels P ℵ₀ := (hμ.1.2.1 ℵ₀ le_rfl hlt).1
    have h := infra_612_galois_trans_cross_level_right_base (t1 := p) (t2 := p')
      (t3 := asTuple (SystemArrow.comp φ incl') trivial b') (e12 := Equiv.refl p.idx)
      (e32 := (Equiv.refl p.idx).symm) h12 (SameGaloisType.swap_refl hgal) ℵ₀ le_rfl hlt hidx0
      hrec rfl rfl
    simp only [Equiv.refl_trans] at h
    exact h

end AEC
