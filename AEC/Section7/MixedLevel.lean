module

public import AEC.Section7.TiedDescent
public import AEC.Section7.TiedFreeLift
public import Mathlib.SetTheory.Cardinal.Cofinality.Club
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-!
# Mixed-level scaffolding for Proposition 7.8 (grokbot_01 Phase 1.2-1.3)

English Proposition 7.8 shrinks a `ρ⁺`-matrix at a large level `κ` to level-`λ` pairs and applies
Lemma 7.6 with the base at level `ν < μ`. The same-level infrastructure (`IsTiedFree`,
`infra_73_isMove`, `lemma_7_6_tied`, `infra_610_tied_free_lift`) needs `ν = μ`. This file holds the
sorry-free mixed-level move, sequence, majority and Galois helpers; the mixed tied free lift is
proved in `MixedTiedLift.lean`, and the mixed Lemma 7.6 descent, Fodor and the `ρ⁺` matrix data
are in `MixedDescent.lean` (split grokbot_02).
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

variable {K : AbstractElementaryClass.{u}}

/-- A **mixed-level sequence-move**: `Z` (in `B`, level `μ`) and `Z0` (in `A`, level `ν`) are
answered alike by every member of the approximation sequence, pushed along `f : A → B`. -/
def infra_78_isMoveMixed
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    {q : TupleOver K oneVertexShape P.scheme hν A}
    (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A)) : Prop :=
  ∀ i : seq.κIndex,
    P.scheme.DiagramEq (X := A) (Y := B)
      (seqJoint (seq.family i) Z0)
      (seqJoint
        (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
        Z)

/-- **Mixed-level tied freeness**: `IsTiedFree` with the base `A` at level `ν` and `B` at level
`μ` (queries bounded below the smaller level `ν`). For `ν = μ` it has the same shape as
`IsTiedFree`. -/
def IsTiedFreeMixed
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (q : TupleOver K oneVertexShape P.scheme hν A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx) : Prop :=
  ∀ (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
    seq.τ + ℵ₀ < #(seq.κIndex) →
    #ι ≤ seq.τ → #ι < ν →
    infra_78_isMoveMixed f seq Z Z0 →
    P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (typeJoint (p := q) Z0)
      (infra_612_anchored eB qB.incl qB.val Z)

/-- **Mixed-level move (proved).** Mixed analogue of the move step of `infra_73_move_iso`:
for `f : A → B` from level `ν ≤ μ`, a list `Z` from `B` bounded at `ν` has a copy `Z'` in `A`
with the same joint diagram over a bounded list `xs` of `A` (pushed along `f`). No structural
isomorphism `A ≅ B` is needed (it does not exist across levels): saturation at level `ν`
(`IsSaturated`, which is mixed-level) followed by same-level `diagram_iso` at `ν`. -/
theorem infra_78_move_mixed
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f) (hνμ : ν ≤ μ)
    {α ι : Type u}
    (xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hα : #α < ν) (hι : #ι < ν) :
    ∃ Z' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A),
      P.scheme.DiagramEq (X := A) (Y := B) (Sum.elim xs Z')
        (Sum.elim (fun a => ⟨(xs a).1, f.onVertex (xs a).1 (xs a).2⟩) Z) := by
  classical
  let base : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun a => ⟨(xs a).1, f.onVertex (xs a).1 (xs a).2⟩
  let ext : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    Sum.elim base Z
  have hEqPush : P.scheme.DiagramEq (X := A) (Y := B) xs base :=
    P.scheme.diagram_preserved A B f hf xs hα (hα.trans_le hνμ)
  obtain ⟨Zext, g, zs, hg, hzs, hzsEq⟩ :=
    (SingleModelData.isSaturated (P := P)).saturated
      A B xs base ext hα hι (fun _ => rfl) hEqPush
  have hPushG : P.scheme.DiagramEq (X := A) (Y := Zext) xs
      (fun a => ⟨(xs a).1, g.onVertex (xs a).1 (xs a).2⟩) :=
    P.scheme.diagram_preserved A Zext g hg xs hα hα
  have hxsZs : (fun a => ⟨(xs a).1, g.onVertex (xs a).1 (xs a).2⟩) =
      fun a => zs (Sum.inl a) := funext fun a => (hzs a).symm
  have hEqZsInl : P.scheme.DiagramEq (X := A) (Y := Zext) xs (fun a => zs (Sum.inl a)) := by
    rw [← hxsZs]
    exact hPushG
  obtain ⟨φ, hφiso, hφ⟩ :=
    (P.scheme.diagram_iso A Zext xs (fun a => zs (Sum.inl a)) hα).mp hEqZsInl
  have hφbij : Bijective (φ.onVertex PUnit.unit) := hφiso PUnit.unit
  let eφ : A.model.carrier ≃ Zext.model.carrier := Equiv.ofBijective _ hφbij
  let Z' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A) :=
    fun j => A.occ (eφ.symm (Zext.val (zs (Sum.inr j))))
  let jointA : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A) :=
    Sum.elim xs Z'
  have hφjoint : ∀ t, zs t =
      ⟨(jointA t).1, φ.onVertex (jointA t).1 (jointA t).2⟩ := by
    intro t
    cases t with
    | inl a =>
      exact hφ a
    | inr j =>
      have happly : φ.onVertex PUnit.unit (eφ.symm (Zext.val (zs (Sum.inr j)))) =
          Zext.val (zs (Sum.inr j)) := eφ.apply_symm_apply _
      refine Eq.trans (SMObject.occ_val Zext (zs (Sum.inr j))).symm ?_
      refine Eq.trans (congrArg Zext.occ happly.symm) ?_
      simp only [jointA, Z', SMObject.occ, oneVertexOcc, SMObject.val, oneVertexVal]
      rfl
  have hcard : #(α ⊕ ι) < ν := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hν) hα hι
  have hPushφ : P.scheme.DiagramEq (X := A) (Y := Zext) jointA zs := by
    have h := P.scheme.diagram_preserved A Zext φ trivial jointA hcard hcard
    have heq : (fun t => ⟨(jointA t).1, φ.onVertex (jointA t).1 (jointA t).2⟩) = zs :=
      funext fun t => (hφjoint t).symm
    rwa [heq] at h
  exact ⟨Z', P.scheme.diagram_trans A Zext B jointA zs ext hPushφ hzsEq⟩

set_option maxHeartbeats 800000 in
/-- **Same-level realization of a type over a smaller object (proved; Corollary 6.7 style).**
A bounded tuple over `A` (level `ν`) realized in a host at any level has the same Galois type as
a tuple realized at level `ν`: a strong hull of `A` and the tuple of size exactly `ν` inside the
host (downward Löwenheim-Skolem, `exists_strong_hull_exact_card`), coded as an object at `ν`. -/
theorem infra_78_same_level_realization
    {P : SingleModelData K} {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {A : P.scheme.Object ν hν}
    (q : TupleOver K oneVertexShape P.scheme hν A) (hidx : #q.idx < ν) :
    ∃ q' : TupleOver K oneVertexShape P.scheme hν A, ∃ e' : q'.idx ≃ q.idx,
      q'.ν = ν ∧ SameGaloisType q q' (Equiv.refl q.idx) e' := by
  classical
  have hνinf : ℵ₀ ≤ ν := P.aleph0_le hν
  let N : Model K.τ := q.host.model
  have hN : K.Mem N := q.host.mem
  let i : Language.Embedding K.τ A.model.carrier N.carrier := q.incl.onVertex PUnit.unit
  have hi : K.Strong i := q.incl.onVertex_strong PUnit.unit
  let x : q.idx → N.carrier := fun k => q.host.val (q.val k)
  have hνN : ν ≤ Model.card N := by
    have h1 : #A.model.carrier ≤ #N.carrier := Cardinal.mk_le_of_injective i.injective
    have h2 : #A.model.carrier = ν := A.card
    change ν ≤ #N.carrier
    rw [← h2]; exact h1
  have hS : #↥(Set.range i ∪ Set.range x) ≤ ν := by
    refine (mk_union_le _ _).trans ?_
    have h := add_le_add ((mk_range_le (f := i)).trans (le_of_eq A.card))
      ((mk_range_le (f := x)).trans hidx.le)
    rwa [add_eq_self hνinf] at h
  obtain ⟨M, j, hM, hj, hcM, hcov⟩ :=
    exists_strong_hull_exact_card K ν (P.ls_lt hν).le hνinf N hN hνN _ hS
  have himgA : ∀ a, ∃ t, j t = i a := fun a => hcov _ (Or.inl ⟨a, rfl⟩)
  have himgX : ∀ k, ∃ t, j t = x k := fun k => hcov _ (Or.inr ⟨k, rfl⟩)
  let i' : Language.Embedding K.τ A.model.carrier M.carrier := factorEmbedding i j himgA
  have hi' : K.Strong i' := strong_factorEmbedding i j hi hj himgA
  choose y hy using himgX
  let B : SMObject K ν := SMObject.ofModel M hM hcM
  let eB : M.carrier ≃[K.τ] B.model.carrier := SMObject.ofModelEquiv M hM hcM
  have heB : K.Strong eB.toEmbedding := strong_of_equiv K eB hM
  have heBs : K.Strong eB.symm.toEmbedding := strong_of_equiv K eB.symm B.mem
  let inclB : Language.Embedding K.τ A.model.carrier B.model.carrier :=
    eB.toEmbedding.comp i'
  have hinclB : K.Strong inclB := K.strong_trans i' eB.toEmbedding hi' heB
  let back : Language.Embedding K.τ B.model.carrier N.carrier := j.comp eB.symm.toEmbedding
  have hback : K.Strong back := K.strong_trans eB.symm.toEmbedding j heBs hj
  let q' : TupleOver K oneVertexShape P.scheme hν A :=
    ⟨ν, hν, B, oneVertexArrow inclB hinclB, trivial, q.idx, fun k => B.occ (eB (y k))⟩
  refine ⟨q', Equiv.refl _, rfl, ?_⟩
  refine ⟨q.ν, q.hν, q.host, SystemArrow.refl _, oneVertexArrow back hback, trivial, trivial,
    ?_, ?_⟩
  · intro v
    ext a
    change i a = j (eB.symm (eB (i' a)))
    rw [eB.symm_apply_apply]
    exact (factorEmbedding_apply i j himgA a).symm
  · intro k
    change q.val k = q.host.occ (j (eB.symm (eB (y k))))
    rw [eB.symm_apply_apply, hy k]
    rfl

/-- **Type-identifying amalgamation at one level (Prop 7.8 matrix step; proved).** Two
tuples over `A` (level `κ`) realized in hosts at level `κ` with the same Galois type have a
level-`κ` amalgam identifying them: the `SameGaloisType` witness `top` may sit at any level
`ρ`, so take a strong hull of size exactly `κ` of both host images inside `top`
(`exists_strong_hull_exact_card`) and factor both arrows through it. In Prop 7.8 this builds
`Y_{i+1}` at level `κ` from `Y_i` and the nonfree extension `X'` over `X_i`. -/
theorem infra_78_same_level_type_amalgam
    {P : SingleModelData K} {κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}
    {A : P.scheme.Object κ hκ} {idx : Type u}
    (t1 t2 : TupleOver K oneVertexShape P.scheme hκ A) (e1 : t1.idx ≃ idx) (e2 : t2.idx ≃ idx)
    (h1 : t1.ν = κ) (h2 : t2.ν = κ) (hS : SameGaloisType t1 t2 e1 e2) :
    ∃ (top : P.scheme.Object κ hκ)
      (f1 : SystemArrow K oneVertexShape (P.scheme.asSystem t1.hν t1.host) (P.scheme.asSystem hκ top))
      (f2 : SystemArrow K oneVertexShape (P.scheme.asSystem t2.hν t2.host) (P.scheme.asSystem hκ top)),
      P.scheme.permitted (X := t1.host) (Y := top) f1 ∧
      P.scheme.permitted (X := t2.host) (Y := top) f2 ∧
      (∀ v, (f1.onVertex v).comp (t1.incl.onVertex v) =
        (f2.onVertex v).comp (t2.incl.onVertex v)) ∧
      ∀ i : idx,
        (⟨(t1.val (e1.symm i)).1,
            f1.onVertex (t1.val (e1.symm i)).1 (t1.val (e1.symm i)).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hκ top)) =
        ⟨(t2.val (e2.symm i)).1,
            f2.onVertex (t2.val (e2.symm i)).1 (t2.val (e2.symm i)).2⟩ := by
  classical
  obtain ⟨ρ, hρ, T, g1, g2, -, -, hcomm, hval⟩ := hS
  have hκinf : ℵ₀ ≤ κ := P.aleph0_le hκ
  let N : Model K.τ := T.model
  have hN : K.Mem N := T.mem
  let i1 : Language.Embedding K.τ t1.host.model.carrier N.carrier := g1.onVertex PUnit.unit
  let i2 : Language.Embedding K.τ t2.host.model.carrier N.carrier := g2.onVertex PUnit.unit
  have hi1 : K.Strong i1 := g1.onVertex_strong PUnit.unit
  have hi2 : K.Strong i2 := g2.onVertex_strong PUnit.unit
  have hc1 : #t1.host.model.carrier = κ := t1.host.card.trans h1
  have hc2 : #t2.host.model.carrier = κ := t2.host.card.trans h2
  have hκN : κ ≤ Model.card N := by
    change κ ≤ #N.carrier
    rw [← hc1]; exact Cardinal.mk_le_of_injective i1.injective
  have hSz : #↥(Set.range i1 ∪ Set.range i2) ≤ κ := by
    refine (mk_union_le _ _).trans ?_
    have h := add_le_add ((mk_range_le (f := i1)).trans (le_of_eq hc1))
      ((mk_range_le (f := i2)).trans (le_of_eq hc2))
    rwa [add_eq_self hκinf] at h
  obtain ⟨M, j, hM, hj, hcM, hcov⟩ :=
    exists_strong_hull_exact_card K κ (P.ls_lt hκ).le hκinf N hN hκN _ hSz
  have him1 : ∀ a, ∃ t, j t = i1 a := fun a => hcov _ (Or.inl ⟨a, rfl⟩)
  have him2 : ∀ a, ∃ t, j t = i2 a := fun a => hcov _ (Or.inr ⟨a, rfl⟩)
  let i1' := factorEmbedding i1 j him1
  let i2' := factorEmbedding i2 j him2
  have hi1' : K.Strong i1' := strong_factorEmbedding i1 j hi1 hj him1
  have hi2' : K.Strong i2' := strong_factorEmbedding i2 j hi2 hj him2
  let B : SMObject K κ := SMObject.ofModel M hM hcM
  let eB : M.carrier ≃[K.τ] B.model.carrier := SMObject.ofModelEquiv M hM hcM
  have heB : K.Strong eB.toEmbedding := strong_of_equiv K eB hM
  have key1 : ∀ a, j (i1' a) = i1 a := factorEmbedding_apply i1 j him1
  have key2 : ∀ a, j (i2' a) = i2 a := factorEmbedding_apply i2 j him2
  refine ⟨B, oneVertexArrow (eB.toEmbedding.comp i1') (K.strong_trans i1' eB.toEmbedding hi1' heB),
    oneVertexArrow (eB.toEmbedding.comp i2') (K.strong_trans i2' eB.toEmbedding hi2' heB),
    trivial, trivial, ?_, ?_⟩
  · intro v
    ext a
    change eB (i1' _) = eB (i2' _)
    congr 1
    apply j.injective
    refine (key1 _).trans (Eq.trans ?_ (key2 _).symm)
    exact congrArg (fun e => e a) (hcomm v)
  · intro k
    have hk := hval k
    generalize t1.val (e1.symm k) = x1 at hk ⊢
    generalize t2.val (e2.symm k) = x2 at hk ⊢
    obtain ⟨⟨⟩, a1⟩ := x1
    obtain ⟨⟨⟩, a2⟩ := x2
    have hh : i1 a1 = i2 a2 := eq_of_heq (Sigma.mk.inj hk).2
    refine Sigma.ext rfl (heq_of_eq ?_)
    change eB (i1' a1) = eB (i2' a2)
    congr 1
    apply j.injective
    exact (key1 a1).trans (hh.trans (key2 a2).symm)

/-- `SameGaloisType` gives equality of the aligned type-joints over any bounded parameter list,
with no level restriction on the two hosts (only boundedness at both host levels). -/
theorem infra_78_diagramEq_of_sameGalois
    {P : SingleModelData K} {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {A : P.scheme.Object ν hν}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hν A} {ι : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι}
    (h : SameGaloisType t1 t2 e1 e2)
    {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (h1 : #(ι ⊕ β) < t1.ν) (h2 : #(ι ⊕ β) < t2.ν) :
    P.scheme.DiagramEq (X := t1.host) (Y := t2.host)
      (alignJoint e1 (typeJoint (p := t1) Z))
      (alignJoint e2 (typeJoint (p := t2) Z)) := by
  obtain ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩ := h
  have hρ1 : t1.ν ≤ ρ := by
    have a := P.scheme.vertex_card t1.hν t1.host PUnit.unit
    have b := P.scheme.vertex_card hρ top PUnit.unit
    rw [← a, ← b]
    exact Cardinal.mk_le_of_injective (f1.onVertex PUnit.unit).injective
  have hρ2 : t2.ν ≤ ρ := by
    have a := P.scheme.vertex_card t2.hν t2.host PUnit.unit
    have b := P.scheme.vertex_card hρ top PUnit.unit
    rw [← a, ← b]
    exact Cardinal.mk_le_of_injective (f2.onVertex PUnit.unit).injective
  have d1 := P.scheme.diagram_preserved t1.host top f1 hf1
    (alignJoint e1 (typeJoint (p := t1) Z)) h1 (h1.trans_le hρ1)
  have d2 := P.scheme.diagram_preserved t2.host top f2 hf2
    (alignJoint e2 (typeJoint (p := t2) Z)) h2 (h2.trans_le hρ2)
  have heq : ∀ s, (⟨(alignJoint e1 (typeJoint (p := t1) Z) s).1,
        f1.onVertex _ (alignJoint e1 (typeJoint (p := t1) Z) s).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hρ top)) =
      ⟨(alignJoint e2 (typeJoint (p := t2) Z) s).1,
        f2.onVertex _ (alignJoint e2 (typeJoint (p := t2) Z) s).2⟩ := by
    intro s
    cases s with
    | inl i => exact hval i
    | inr b =>
      have hc := DFunLike.congr_fun (hcomm (Z b).1) (Z b).2
      simp only [Language.Embedding.comp_apply] at hc
      change (⟨(Z b).1, f1.onVertex (Z b).1 (t1.incl.onVertex (Z b).1 (Z b).2)⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hρ top)) =
        ⟨(Z b).1, f2.onVertex (Z b).1 (t2.incl.onVertex (Z b).1 (Z b).2)⟩
      rw [hc]
  have d2' := infra_73_diagramEq_of_eq d2 (fun _ => rfl) (fun s => (heq s).symm)
  exact P.scheme.diagram_trans _ _ _ _ _ _ d1 (P.scheme.diagram_symm _ _ _ _ d2')

/-- **Approximation sequences for a type over a smaller object (proved).** A bounded type over
`A` (level `ν` in the `σ`-tail) realized in a host at any level has an approximation sequence
with the uniform bounds of `infra_73_sequence`: realize it at level `ν`
(`infra_78_same_level_realization`) and transport the same-level sequence along the Galois-type
equality. -/
theorem infra_78_sequence_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν : Cardinal.{u}} (hν : ν ∈ P.eligible) (hνT : ν ∈ infra_73_tailSet P σ)
    {A : P.scheme.Object ν hν}
    (q : TupleOver K oneVertexShape P.scheme hν A) (hidx : #q.idx ≤ σ) :
    ∃ seq : ApproximationSequence q,
      seq.τ = max σ (infra_73_chi P σ) ∧
      #(seq.κIndex) = infra_73_h P σ ∧
      P.g σ + ls K ≤ seq.τ ∧
      seq.τ + ℵ₀ < #(seq.κIndex) := by
  classical
  have hσlt : σ < ν := (Order.lt_succ σ).trans_le (infra_73_tail_succ hνT)
  have hhν : infra_73_h P σ < ν := infra_73_h_lt hν hνT
  obtain ⟨q', e', hq'ν, hSGT⟩ := infra_78_same_level_realization q (hidx.trans_lt hσlt)
  have hidx' : #q'.idx ≤ σ := by rw [Cardinal.mk_congr e']; exact hidx
  obtain ⟨seq', hτ, hκ, hg, hlong⟩ := infra_73_sequence P σ hσ hν hνT q' hq'ν hidx'
  have hτlt : seq'.τ < ν := (lt_of_le_of_lt le_self_add hlong).trans (hκ ▸ hhν)
  refine ⟨{ τ := seq'.τ
            κIndex := seq'.κIndex
            family := fun i k => seq'.family i (e'.symm k)
            concat_bounded := by
              rw [← Cardinal.mk_congr (Equiv.prodCongr (Equiv.refl _) e')]
              exact seq'.concat_bounded
            few_exceptions := ?_ }, hτ, hκ, hg, hlong⟩
  intro ι Z hZ
  refine le_trans (Cardinal.mk_subtype_mono (p := fun i => ¬ P.scheme.DiagramEq
      (X := q.host) (Y := A) (typeJoint (p := q) Z)
      (seqJoint (fun k => seq'.family i (e'.symm k)) Z))
    (q := fun i => ¬ P.scheme.DiagramEq (X := q'.host) (Y := A) (typeJoint (p := q') Z)
      (seqJoint (seq'.family i) Z)) ?_) (seq'.few_exceptions Z hZ)
  intro i hi hgood
  apply hi
  have hZν : #ι < ν := hZ.trans_lt hτlt
  have hb : #(q.idx ⊕ ι) < ν := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hν) (hidx.trans_lt hσlt) hZν
  have hqν : ν ≤ q.ν := by
    have a := P.scheme.vertex_card hν A PUnit.unit
    have b := P.scheme.vertex_card q.hν q.host PUnit.unit
    exact a.symm.le.trans
      ((Cardinal.mk_le_of_injective (q.incl.onVertex PUnit.unit).injective).trans b.le)
  have dG := infra_78_diagramEq_of_sameGalois hSGT Z (hb.trans_le hqν) (hb.trans_le hq'ν.ge)
  have dG' := infra_73_diagramEq_of_eq dG
    (xs' := typeJoint (p := q) Z)
    (ys' := fun s => typeJoint (p := q') Z (Sum.map e'.symm id s))
    (fun s => by cases s <;> rfl) (fun s => by cases s <;> rfl)
  have dS := infra_73_scheme_comp hgood (Sum.map e'.symm id)
  have dS' := infra_73_diagramEq_of_eq dS
    (xs' := fun s => typeJoint (p := q') Z (Sum.map e'.symm id s))
    (ys' := seqJoint (fun k => seq'.family i (e'.symm k)) Z)
    (fun s => rfl) (fun s => by cases s <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ dG' dS'

/-- Mixed-level moves of one query are answered alike by `q` (port of `infra_73_moves_agree`). -/
theorem infra_78_moves_agree_mixed
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    {q : TupleOver K oneVertexShape P.scheme hν A}
    (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0 Z1 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (hmove0 : infra_78_isMoveMixed f seq Z Z0)
    (hmove1 : infra_78_isMoveMixed f seq Z Z1)
    (hι : #ι ≤ seq.τ) (hκ : #ι + ℵ₀ < #(seq.κIndex)) :
    P.scheme.DiagramEq (X := q.host) (Y := q.host)
      (typeJoint (p := q) Z0) (typeJoint (p := q) Z1) := by
  classical
  let Exc0 : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := q.host)
      (seqJoint (seq.family i) Z0) (typeJoint (p := q) Z0)}
  let Exc1 : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := q.host)
      (seqJoint (seq.family i) Z1) (typeJoint (p := q) Z1)}
  have hExc0 : #Exc0 ≤ #ι + ℵ₀ := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := q.host)
          (seqJoint (seq.family i) Z0) (typeJoint (p := q) Z0)} ≤ _
    exact infra_610_majority_eq_type seq Z0 hι
  have hExc1 : #Exc1 ≤ #ι + ℵ₀ := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := q.host)
          (seqJoint (seq.family i) Z1) (typeJoint (p := q) Z1)} ≤ _
    exact infra_610_majority_eq_type seq Z1 hι
  have hinf : ℵ₀ ≤ #ι + ℵ₀ := le_add_self
  obtain ⟨i, hi0, hi1⟩ := infra_76_two_good Exc0 Exc1 hinf hExc0 hExc1 hκ
  have h0 : P.scheme.DiagramEq (X := A) (Y := q.host)
      (seqJoint (seq.family i) Z0) (typeJoint (p := q) Z0) := by
    simpa [Exc0] using hi0
  have h1 : P.scheme.DiagramEq (X := A) (Y := q.host)
      (seqJoint (seq.family i) Z1) (typeJoint (p := q) Z1) := by
    simpa [Exc1] using hi1
  have hJoint : P.scheme.DiagramEq (X := A) (Y := A)
      (seqJoint (seq.family i) Z0) (seqJoint (seq.family i) Z1) :=
    P.scheme.diagram_trans A B A _ _ _
      (hmove0 i) (P.scheme.diagram_symm A B _ _ (hmove1 i))
  exact P.scheme.diagram_trans q.host A q.host _ _ _
    (P.scheme.diagram_symm A q.host _ _ h0)
    (P.scheme.diagram_trans A A q.host _ _ _ hJoint h1)

/-- The list `Y` from `B` (level `μ`) as a tuple over `A` (level `ν`). -/
def infra_78_listTupleMixed
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) :
    TupleOver K oneVertexShape P.scheme hν A where
  ν := μ
  hν := hμ
  host := B
  incl := f
  incl_arrow := hf
  idx := β
  val := Y

set_option maxHeartbeats 1600000 in
/-- **Mixed-level symmetry of the tied answer (proved; port of `infra_76_tied_majority`).**
If `q_B` (level `μ`) is a mixed tied-free lift of `q_A` (level `ν ≤ μ`) and `S` is an
approximation list of `tp(Y/A)`, then off at most `h(σ)` indices `k`, `q_B` answers `Y` as `q_A`
answers `S_k`. The structural isomorphism `A ≅ B` of the same-level proof is replaced by
`infra_78_move_mixed`. -/
theorem infra_78_tied_majority_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible) (hνT : ν ∈ infra_73_tailSet P σ)
    (hμ : μ ∈ P.eligible) (hνμ : ν ≤ μ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (qA : TupleOver K oneVertexShape P.scheme hν A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : qA.idx ≃ qB.idx) (hqAν : qA.ν = ν) (hidx : #qA.idx ≤ σ)
    (hT : IsTiedFreeMixed f qA qB eB)
    {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hβ : #β ≤ σ)
    (S : ApproximationSequence (infra_78_listTupleMixed f hf Y))
    (hS : infra_73_h P σ ≤ S.τ) :
    ∃ E : Set S.κIndex, #E ≤ infra_73_h P σ ∧
      ∀ k, k ∉ E →
        P.scheme.DiagramEq (X := qA.host) (Y := qB.host)
          (typeJoint (p := qA) (S.family k))
          (infra_612_anchored eB qB.incl qB.val Y) := by
  classical
  have hσSucc : Order.succ σ ≤ ν := infra_73_tail_succ hνT
  have hσlt : σ < ν := (Order.lt_succ σ).trans_le hσSucc
  have hhν : infra_73_h P σ < ν := infra_73_h_lt hν hνT
  have hβν : #β < ν := hβ.trans_lt hσlt
  obtain ⟨seq, hτeq, hκ, -, hlong⟩ := infra_73_sequence P σ hσ hν hνT qA hqAν hidx
  have hβτ : #β ≤ seq.τ := hβ.trans (hτeq ▸ le_max_left _ _)
  have hhinf : ℵ₀ ≤ infra_73_h P σ :=
    hσ.trans ((le_max_left σ (infra_73_chi P σ)).trans (Order.le_succ _))
  have hβκ : #β + ℵ₀ < #(seq.κIndex) := by
    rw [hκ]
    have h1 : #β + ℵ₀ ≤ max σ (infra_73_chi P σ) :=
      (add_le_add (hβ.trans (le_max_left _ _)) (hσ.trans (le_max_left _ _))).trans
        (add_eq_self (hσ.trans (le_max_left _ _))).le
    exact h1.trans_lt (Order.lt_succ_of_not_isMax (not_isMax _))
  let FAM : seq.κIndex × qA.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν A) :=
    fun x => seq.family x.1 x.2
  have hFAM : #(seq.κIndex × qA.idx) ≤ infra_73_h P σ := infra_73_family_card seq hσ hidx hκ
  obtain ⟨Y0, hJ⟩ := infra_78_move_mixed f hf hνμ FAM Y (hFAM.trans_lt hhν) hβν
  have hmove0 : infra_78_isMoveMixed f seq Y Y0 := by
    intro i
    let ι : qA.idx ⊕ β → (seq.κIndex × qA.idx) ⊕ β := fun t =>
      match t with
      | Sum.inl j => Sum.inl (i, j)
      | Sum.inr b => Sum.inr b
    exact infra_73_diagramEq_of_eq (infra_73_scheme_comp hJ ι)
      (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  have hans := hT seq Y Y0 hlong hβτ hβν hmove0
  let E : Set S.κIndex := {k | ¬ P.scheme.DiagramEq (X := B) (Y := A)
    (typeJoint (p := infra_78_listTupleMixed f hf Y) FAM) (seqJoint (S.family k) FAM)}
  have hE : #E ≤ infra_73_h P σ :=
    (S.few_exceptions FAM (hFAM.trans hS)).trans
      ((add_le_add hFAM hhinf).trans (add_eq_self hhinf).le)
  refine ⟨E, hE, fun k hk => ?_⟩
  have hk : P.scheme.DiagramEq (X := B) (Y := A)
      (typeJoint (p := infra_78_listTupleMixed f hf Y) FAM) (seqJoint (S.family k) FAM) :=
    not_not.mp hk
  have hmove1 : infra_78_isMoveMixed f seq Y (S.family k) := by
    intro i
    let ι : qA.idx ⊕ β → β ⊕ (seq.κIndex × qA.idx) := fun t =>
      match t with
      | Sum.inl a => Sum.inr (i, a)
      | Sum.inr b => Sum.inl b
    have h := infra_73_scheme_comp hk ι
    have h' := P.scheme.diagram_symm B A _ _ h
    exact infra_73_diagramEq_of_eq h' (fun t => by cases t <;> rfl)
      (fun t => by cases t <;> rfl)
  have hagree := infra_78_moves_agree_mixed f seq Y Y0 (S.family k) hmove0 hmove1 hβτ hβκ
  exact P.scheme.diagram_trans qA.host qA.host qB.host _ _ _
    (P.scheme.diagram_symm qA.host qA.host _ _ hagree) hans

/-- **Galois-type transitivity through a middle tuple at a higher level (proved).** Port of
`SameGaloisType.trans_via` with the middle host at any level `≥ μ` (only its size is used). -/
theorem infra_78_trans_via_mixed
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {t1 t2 t3 : TupleOver K oneVertexShape P.scheme hμ A}
    {e12 : t1.idx ≃ t2.idx} {e32 : t3.idx ≃ t2.idx}
    (h12 : SameGaloisType t1 t2 e12 (Equiv.refl t2.idx))
    (h32 : SameGaloisType t2 t3 (Equiv.refl t2.idx) e32)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hσμ : σ < μ)
    (hidx : #t1.idx ≤ σ) (_hrec : μ ∈ recursionClosedLevels P σ)
    (hν1 : t1.ν = μ) (hν2 : μ ≤ t2.ν) (hν3 : t3.ν = μ) :
    SameGaloisType t1 t3 (e12.trans e32.symm) (Equiv.refl t3.idx) := by
  have hL := infra_610_closed_level P σ hσ hμ _hrec
  have hidx3 : #t3.idx ≤ σ := (Cardinal.mk_congr e32).trans_le
    ((Cardinal.mk_congr e12).symm.trans_le hidx)
  apply infra_612_same_galois t1 t3 (e12.trans e32.symm) σ hσ hσμ hidx hν1 hν3 hL
  intro β hβ ρ0 hρinf hρμ params hjnt h0 h1
  have hc2 : μ ≤ Model.card t2.host.model := by rw [t2.host.card]; exact hν2
  have h2 : P.D.t ρ0 ≤ Model.card t2.host.model :=
    (P.t_lt hμ hρinf hρμ).le.trans hc2
  have h23 : #t3.idx = #t2.idx := Cardinal.mk_congr e32
  have hj2 : #t2.idx + #β ≤ ρ0 := by simpa [h23] using hjnt
  have hab := SameGaloisType.to_sameD h12 params ρ0 hρinf (by simpa using hj2) h0 h2
  have hbc := SameGaloisType.to_sameD h32 params ρ0 hρinf (by simpa using hj2) h2 h1
  have hmid := P.D.trans hj2 t1.host.mem t2.host.mem t3.host.mem h0 h2 h1 _ _ _
    (by simpa [Equiv.refl_symm] using hab) (by simpa [Equiv.refl_symm] using hbc)
  have hc1 : Model.card t1.host.model = μ := by simpa [hν1] using t1.host.card
  have hc3 : Model.card t3.host.model = μ := by simpa [hν3] using t3.host.card
  let σ' : Cardinal.{u} := max ρ0 (ls K)
  have hσ'μ : σ' < μ := max_lt hρμ (P.ls_lt hμ)
  have hσ'inf : aleph0 ≤ σ' := hρinf.trans (le_max_left _ _)
  have ht' : P.D.t σ' ≤ μ := (P.t_lt hμ hσ'inf hσ'μ).le
  let hι : (t3.idx ⊕ β) → (t2.idx ⊕ β) := Sum.map e32 id
  have hL1 := P.D.same_relevel hj2 hρinf hρinf (le_max_left ρ0 (ls K)) (le_max_left ρ0 (ls K))
    (le_max_right ρ0 (ls K)) t1.host.mem t3.host.mem h0 h1
    (ht'.trans hc1.ge) (ht'.trans hc3.ge) h0 h1 _ _ hmid hjnt hι
  convert hL1 using 1
  · funext c
    cases c with
    | inl k =>
      dsimp [hι, Sum.map]
      rfl
    | inr b =>
      dsimp [hι, Sum.map]
      exact congrArg (fun v => t1.incl.onVertex v (params b)) (Subsingleton.elim _ _)
  · funext c
    cases c with
    | inl k =>
      change t3.host.val (t3.val k) = t3.host.val (t3.val (e32.symm (e32 k)))
      rw [Equiv.symm_apply_apply]
    | inr b =>
      dsimp [hι, Sum.map]
      exact congrArg (fun v => t3.incl.onVertex v (params b)) (Subsingleton.elim _ _)

/-- **Galois types from diagrams (proved).** At a closed level, two bounded tuples over `A`
realized at that level have the same Galois type when their aligned joints with every
Galois-test-sized parameter list have equal diagrams. -/
theorem infra_78_sameGalois_of_diagramEq
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : σ < μ)
    {A : P.scheme.Object μ hμ}
    (t1 t2 : TupleOver K oneVertexShape P.scheme hμ A) (e : t1.idx ≃ t2.idx)
    (hidx : #t1.idx ≤ σ) (hν1 : t1.ν = μ) (hν2 : t2.ν = μ)
    (hD : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #β ≤ P.g σ + ls K →
      P.scheme.DiagramEq (X := t1.host) (Y := t2.host)
        (alignJoint e (typeJoint (p := t1) Z)) (typeJoint (p := t2) Z)) :
    SameGaloisType t1 t2 e (Equiv.refl t2.idx) := by
  have hL := infra_610_closed_level P σ hσ hμ hrec
  apply infra_612_same_galois t1 t2 e σ hσ hσμ hidx hν1 hν2 hL
  intro β hβ ρ0 hρinf hρμ params hjnt h0 h1
  let Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) := fun b => A.occ (params b)
  have hDE := hD Z hβ
  have hc₁ : Model.card t1.host.model = μ := by simpa [hν1] using t1.host.card
  have hc₂ : Model.card t2.host.model = μ := by simpa [hν2] using t2.host.card
  have hα₁ : #(t2.idx ⊕ β) < t1.ν := by rw [hν1]; exact hjnt.trans_lt hρμ
  have hα₂ : #(t2.idx ⊕ β) < t2.ν := by rw [hν2]; exact hjnt.trans_lt hρμ
  have htest := infra_612_test_of_diagram
    (alignJoint e (typeJoint (p := t1) Z)) (typeJoint (p := t2) Z)
    hDE hα₁ hα₂ μ hμ hc₁ hc₂ hρinf hρμ hjnt id hjnt h0 h1
  convert htest using 1
  · funext c
    cases c with
    | inl k => rfl
    | inr b =>
      change t1.incl.onVertex PUnit.unit (params b) = t1.host.val
        ⟨(Z b).1, t1.incl.onVertex (Z b).1 (Z b).2⟩
      rfl
  · funext c
    cases c with
    | inl k => rfl
    | inr b =>
      change t2.incl.onVertex PUnit.unit (params b) = t2.host.val
        ⟨(Z b).1, t2.incl.onVertex (Z b).1 (Z b).2⟩
      rfl

end
end AEC
