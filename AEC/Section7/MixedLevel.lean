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
`infra_73_isMove`, `lemma_7_6_tied`, `infra_610_tied_free_lift`) needs `ν = μ`. This file states
the mixed-level analogues (open, `sorry`) and the pressing-down helper (proved from Mathlib).
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

/-- **Mixed-level tied free lift (open stub).** Mixed analogue of `infra_610_tied_free_lift`:
along a permitted arrow from a recursion-closed level `ν` to a level `μ ≥ ν`, a bounded type over
`A` realized at `ν` has a free lift to `B`, realized at `μ`, that is tied free across levels
(English Theorem 6.10: "in a mixed-level use the costs must remain below the level of `A`"). -/
theorem infra_78_tied_free_lift_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible)
    (hrec : ν ∈ recursionClosedLevels P σ) (hσν : Order.succ σ ≤ ν)
    (hμ : μ ∈ P.eligible) (hνμ : ν ≤ μ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hν A)
    (hpν : p.ν = ν) (hidx : #p.idx ≤ σ) :
    ∃ (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx), qB.ν = μ ∧
      SameGaloisType p (qB.restrict f hf) eB (Equiv.refl qB.idx) ∧
      IsTiedFreeMixed f p qB eB := by
  sorry

set_option maxHeartbeats 3200000 in
/-- **Mixed-level Lemma 7.6 descent (proved modulo `infra_78_tied_free_lift_mixed`).** Port of
`infra_76_tied_descent` with `A` at level `ν ≤ μ` and `B` at level `μ`: the same-level structural
isomorphism, approximation sequences and Galois-type transitivity are replaced by
`infra_78_move_mixed`, `infra_78_sequence_mixed` and a diagram-level chain
(`infra_78_diagramEq_of_sameGalois`, `infra_78_sameGalois_of_diagramEq`). The only open input is
the mixed tied free lift of the competitor `q_A'`. -/
theorem infra_78_tied_descent_mixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible)
    (hνT : ν ∈ infra_73_tailSet P (infra_76_sigma2 P σ))
    (hμT : μ ∈ infra_73_tailSet P σ) (hνμ : ν ≤ μ)
    {A : P.scheme.Object ν hν}
    {B : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (qA : TupleOver K oneVertexShape P.scheme _ A)
    (qB : TupleOver K oneVertexShape P.scheme _ B)
    (e : qA.idx ≃ qB.idx) {uIdx cIdx : Type u} (eA : qA.idx ≃ uIdx ⊕ cIdx)
    (hqAν : qA.ν = ν) (hqBν : qB.ν = μ) (hidx : #qA.idx ≤ σ)
    (hExt : SameGaloisType qA (qB.restrict f hf) e (Equiv.refl qB.idx))
    (hT : IsTiedFreeMixed f qA qB e)
    (hIso : IsRelativelyIsolated qB (e.symm.trans eA)) :
    IsRelativelyIsolated qA eA := by
  classical
  let σ1 : Cardinal.{u} := infra_73_h P σ
  let σ2 : Cardinal.{u} := infra_76_sigma2 P σ
  have hσ1 : ℵ₀ ≤ σ1 := hσ.trans (infra_76_lt_h P σ).le
  have hσ2 : ℵ₀ ≤ σ2 := hσ1.trans (infra_76_lt_h P σ1).le
  have hσσ1 : σ ≤ σ1 := (infra_76_lt_h P σ).le
  have hσ1σ2 : σ1 ≤ σ2 := (infra_76_lt_h P σ1).le
  have hT0 : ν ∈ infra_73_tailSet P σ := infra_76_tail_mono (le_trans hσ1σ2 le_rfl) hνT
  have hT1 : ν ∈ infra_73_tailSet P σ1 := infra_76_tail_mono le_rfl hνT
  have hμ : μ ∈ P.eligible := Tail.mem (infra_73_tail P σ hσ) hμT
  have hrec : ν ∈ recursionClosedLevels P σ := infra_73_tail_rec hT0
  have hrecμ : μ ∈ recursionClosedLevels P σ := infra_73_tail_rec hμT
  have hσSucc : Order.succ σ ≤ ν := infra_73_tail_succ hT0
  have hσSuccμ : Order.succ σ ≤ μ := infra_73_tail_succ hμT
  have hσlt : σ < ν := (Order.lt_succ σ).trans_le hσSucc
  have hσltμ : σ < μ := (Order.lt_succ σ).trans_le hσSuccμ
  have hidxμ : #qA.idx < ν := hidx.trans_lt hσlt
  have hidxB : #qB.idx ≤ σ := by rw [← Cardinal.mk_congr e]; exact hidx
  let eb : qB.idx ≃ uIdx ⊕ cIdx := e.symm.trans eA
  -- Proposition 7.3: a fragment of size at most `h(σ)`
  obtain ⟨ιW, W, hιW, hWiso⟩ := infra_73_uniform_of_block P σ hσ
    (infra_73_block_restriction P σ hσ) hμT qB eb hqBν hidxB (hidxB.trans_lt hσltμ) hIso
  -- an approximation list of `tp(W/A)`
  have hιW2 : #ιW ≤ σ2 := hιW.trans hσ1σ2
  obtain ⟨S, hSτ, hSκ, -, -⟩ := infra_78_sequence_mixed P σ2 hσ2 hν hνT
    (infra_78_listTupleMixed f hf W) hιW2
  have hS : infra_73_h P σ1 ≤ S.τ := hSτ ▸ le_max_left _ _
  have hSbig : σ2 < #S.κIndex := hSκ ▸ infra_76_lt_h P σ2
  let Z : S.κIndex × ιW → Occurrence K oneVertexShape (P.scheme.asSystem hν A) :=
    fun x => S.family x.1 x.2
  refine ⟨S.κIndex × ιW, Z, S.concat_bounded, ?_⟩
  intro qA' e' hqA'ν hMarg hDE
  have hidx' : #qA'.idx ≤ σ := by rw [← Cardinal.mk_congr (eA.trans e'.symm)]; exact hidx
  obtain ⟨qB', eB', hB'ν, hExt', hT'⟩ :=
    infra_78_tied_free_lift_mixed P σ hσ hν hrec hσSucc hμ hνμ f hf qA' hqA'ν hidx'
  let e'' : qB'.idx ≃ uIdx ⊕ cIdx := eB'.symm.trans e'
  -- the fragment `W`: both lifts answer it as their bases answer a good `w_k`
  obtain ⟨E1, hE1, hgood1⟩ := infra_78_tied_majority_mixed P σ1 hσ1 hν hT1 hμ hνμ f hf qA qB e hqAν
    (hidx.trans hσσ1) hT W hιW S hS
  obtain ⟨E2, hE2, hgood2⟩ := infra_78_tied_majority_mixed P σ1 hσ1 hν hT1 hμ hνμ f hf qA' qB' eB' hqA'ν
    (hidx'.trans hσσ1) hT' W hιW S hS
  obtain ⟨k, hk1, hk2⟩ := infra_76_two_good E1 E2 hσ2 hE1 hE2 hSbig
  have d1 := infra_73_diagramEq_of_eq (infra_73_scheme_comp (hgood1 k hk1) (Sum.map eA.symm id))
    (xs' := alignJoint eA (typeJoint (p := qA) (S.family k)))
    (ys' := alignJoint eb (typeJoint (p := qB) W))
    (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  have d2 := infra_73_diagramEq_of_eq (infra_73_scheme_comp (hgood2 k hk2) (Sum.map e'.symm id))
    (xs' := alignJoint e' (typeJoint (p := qA') (S.family k)))
    (ys' := alignJoint e'' (typeJoint (p := qB') W))
    (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  have dk := infra_73_diagramEq_of_eq
    (infra_73_scheme_comp hDE (Sum.map id (fun b : ιW => (k, b))))
    (xs' := alignJoint eA (typeJoint (p := qA) (S.family k)))
    (ys' := alignJoint e' (typeJoint (p := qA') (S.family k)))
    (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  have hPush : P.scheme.DiagramEq (X := qB.host) (Y := qB'.host)
      (alignJoint eb (typeJoint (p := qB) W)) (alignJoint e'' (typeJoint (p := qB') W)) :=
    P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d1)
      (P.scheme.diagram_trans _ _ _ _ _ _ dk d2)
  -- the `u`-marginals of the two lifts agree
  have hidxu : #uIdx ≤ σ := by
    have heq : #qA.idx = #(uIdx ⊕ cIdx) := Cardinal.mk_congr eA
    have hle : #uIdx ≤ #qA.idx := by
      rw [heq, mk_sum, lift_id]
      exact le_self_add
    exact hle.trans hidx
  have hMargB : SameGaloisType (qB.marginal eb) (qB'.marginal e'')
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ := infra_73_differing_test P σ hσ hμ hrecμ hσSuccμ
      (qB.marginal eb) (qB'.marginal e'') (Equiv.refl uIdx) (Equiv.refl uIdx) hqBν hB'ν
      hidxu (hidxu.trans_lt hσltμ) hneq
    apply hnot
    have hβ1 : #β ≤ σ1 := by
      refine hβ.trans (le_trans ?_ (le_max_right σ (infra_73_chi P σ))) |>.trans
        (Order.le_succ _)
      exact (add_le_add le_rfl (le_max_left _ _)).trans (le_max_right _ _)
    have hβμ : #β < ν := hβ1.trans_lt ((infra_76_lt_h P σ1).trans (infra_73_h_lt hν hT1))
    obtain ⟨SY, hSYτ, hSYκ, -, -⟩ := infra_78_sequence_mixed P σ2 hσ2 hν hνT
      (infra_78_listTupleMixed f hf Y) (hβ1.trans hσ1σ2)
    have hSY : infra_73_h P σ1 ≤ SY.τ := hSYτ ▸ le_max_left _ _
    have hSYbig : σ2 < #SY.κIndex := hSYκ ▸ infra_76_lt_h P σ2
    obtain ⟨F1, hF1, hg1⟩ := infra_78_tied_majority_mixed P σ1 hσ1 hν hT1 hμ hνμ f hf qA qB e hqAν
      (hidx.trans hσσ1) hT Y hβ1 SY hSY
    obtain ⟨F2, hF2, hg2⟩ := infra_78_tied_majority_mixed P σ1 hσ1 hν hT1 hμ hνμ f hf qA' qB' eB' hqA'ν
      (hidx'.trans hσσ1) hT' Y hβ1 SY hSY
    obtain ⟨j, hj1, hj2⟩ := infra_76_two_good F1 F2 hσ2 hF1 hF2 hSYbig
    have m1 := infra_73_diagramEq_of_eq
      (infra_73_scheme_comp (hg1 j hj1) (Sum.map (fun a => eA.symm (Sum.inl a)) id))
      (xs' := alignJoint (Equiv.refl uIdx) (typeJoint (p := qA.marginal eA) (SY.family j)))
      (ys' := alignJoint (Equiv.refl uIdx) (typeJoint (p := qB.marginal eb) Y))
      (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    have m2 := infra_73_diagramEq_of_eq
      (infra_73_scheme_comp (hg2 j hj2) (Sum.map (fun a => e'.symm (Sum.inl a)) id))
      (xs' := alignJoint (Equiv.refl uIdx) (typeJoint (p := qA'.marginal e') (SY.family j)))
      (ys' := alignJoint (Equiv.refl uIdx) (typeJoint (p := qB'.marginal e'') Y))
      (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    have mA := infra_72_diagramEq_of_sameGalois (P := P) hMarg (SY.family j) hqAν hqA'ν
      (hidxu.trans_lt hσlt) hβμ
    exact P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ m1)
      (P.scheme.diagram_trans _ _ _ _ _ _ mA m2)
  -- isolation of `q_B` and restriction to `A`
  have hSGTb := hWiso.2 qB' e'' hB'ν hMargB hPush
  have hRes : SameGaloisType (qB.restrict f hf) (qB'.restrict f hf) eb e'' := by
    rcases hSGTb with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, ?_, ?_⟩
    · intro v
      ext x
      simp only [TupleOver.restrict, SystemArrow.comp]
      exact DFunLike.congr_fun (hcomm v) (f.onVertex v x)
    · intro j
      exact hval j
  have hResRefl : SameGaloisType (qB.restrict f hf) (qB'.restrict f hf)
      (Equiv.refl qB.idx) (e''.trans eb.symm) := by
    rcases hRes with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
    intro i
    have hv := hval (eb i)
    have h1 : eb.symm (eb i) = i := Equiv.symm_apply_apply _ _
    have h2 : (e''.trans eb.symm).symm i = e''.symm (eb i) := rfl
    have hv' := h1 ▸ hv
    exact h2 ▸ hv'
  have hBack : SameGaloisType (qB'.restrict f hf) qA' (Equiv.refl _) eB' :=
    SameGaloisType.symm hExt'
  -- chain of diagrams through the two restrictions (no same-level transitivity needed)
  let E' : qB'.idx ≃ qB.idx := e''.trans eb.symm
  let G : qA'.idx ≃ qB.idx := eB'.trans E'
  have hgσ : P.g σ + ls K < ν :=
    (le_trans (add_le_add le_rfl (le_max_left _ _)) (le_max_right _ _) |>.trans
      (le_max_right σ (infra_73_chi P σ))).trans_lt
      ((Order.lt_succ_of_not_isMax (not_isMax _)).trans (infra_73_h_lt hν hT0))
  have hbd : ∀ {ι β : Type u}, #ι ≤ σ → #β ≤ P.g σ + ls K → #(ι ⊕ β) < ν := by
    intro ι β hι hβ
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hν) (hι.trans_lt hσlt) (hβ.trans_lt hgσ)
  have hRν : (qB.restrict f hf).ν = μ := by simpa [TupleOver.restrict] using hqBν
  have hR'ν : (qB'.restrict f hf).ν = μ := by simpa [TupleOver.restrict] using hB'ν
  have hSGT : SameGaloisType qA qA' (e.trans G.symm) (Equiv.refl qA'.idx) := by
    refine infra_78_sameGalois_of_diagramEq P σ hσ hν hrec hσlt qA qA' (e.trans G.symm)
      hidx hqAν hqA'ν ?_
    intro β Z hβ
    have b1 := hbd (ι := qB.idx) (β := β) hidxB hβ
    have b1μ : #(qB.idx ⊕ β) < μ := b1.trans_le hνμ
    have hidxB' : #qB'.idx ≤ σ := by
      rw [← Cardinal.mk_congr eB']; exact hidx'
    have b3 := hbd (ι := qB'.idx) (β := β) hidxB' hβ
    have d1 := infra_78_diagramEq_of_sameGalois hExt Z (by rw [hqAν]; exact b1) (by rw [hRν]; exact b1μ)
    have d2 := infra_78_diagramEq_of_sameGalois hResRefl Z (by rw [hRν]; exact b1μ)
      (by rw [hR'ν]; exact b1μ)
    have d3 := infra_78_diagramEq_of_sameGalois hBack Z (by rw [hR'ν]; exact b3.trans_le hνμ)
      (by rw [hqA'ν]; exact b3)
    have d3' := infra_73_diagramEq_of_eq (infra_73_scheme_comp d3 (Sum.map E'.symm id))
      (xs' := alignJoint E' (typeJoint (p := qB'.restrict f hf) Z))
      (ys' := alignJoint G (typeJoint (p := qA') Z))
      (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    have d := P.scheme.diagram_trans _ _ _ _ _ _ d1 (P.scheme.diagram_trans _ _ _ _ _ _ d2 d3')
    exact infra_73_diagramEq_of_eq (infra_73_scheme_comp d (Sum.map G id))
      (fun t => by cases t <;> simp [alignJoint, typeJoint])
      (fun t => by cases t <;> simp [alignJoint, typeJoint])
  have hEqv : e.trans G.symm = eA.trans e'.symm := by
    ext j
    simp [G, E', e'', eb, Equiv.trans_apply]
  rcases hEqv ▸ hSGT with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro k
  have hv := hval (e'.symm k)
  have hL : eA.symm (e' (e'.symm k)) = eA.symm k :=
    congrArg eA.symm (Equiv.apply_symm_apply e' k)
  have hR : (Equiv.refl qA'.idx).symm (e'.symm k) = e'.symm k := rfl
  exact hR ▸ hL ▸ hv

/-- **Mixed-level Lemma 7.6 (proved modulo `infra_78_tied_free_lift_mixed`).** Relative
isolation descends along a mixed-level tied-free lift (`A` at level `ν ≤ μ`, `B` at level `μ`).
Mirror of `lemma_7_6_tied`, via `infra_78_tied_descent_mixed`. -/
theorem infra_78_lemma_7_6_mixed (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ ν (hν : ν ∈ T) μ (hμ : μ ∈ T) (A : P.scheme.Object ν (Tail.mem hT hν))
        (B : P.scheme.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
        (hf : P.scheme.permitted (X := A) (Y := B) f)
        (qA : TupleOver K oneVertexShape P.scheme (Tail.mem hT hν) A)
        (qB : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
        (e : qA.idx ≃ qB.idx) {uIdx cIdx : Type u} (eA : qA.idx ≃ uIdx ⊕ cIdx),
        ν ≤ μ → qA.ν = ν → qB.ν = μ → #qA.idx ≤ σ →
        SameGaloisType qA (qB.restrict f hf) e (Equiv.refl qB.idx) →
        IsTiedFreeMixed f qA qB e →
        IsRelativelyIsolated qB (e.symm.trans eA) →
        IsRelativelyIsolated qA eA :=
  ⟨infra_73_tailSet P (infra_76_sigma2 P σ),
    infra_73_tail P _ ((hσ.trans (infra_76_lt_h P σ).le).trans (infra_76_lt_h P _).le),
    fun _ hν _ hμ _ _ f hf qA qB e _ _ eA hνμ hqA hqB hidx hExt hT hIso =>
      infra_78_tied_descent_mixed P σ hσ _ hν
        (infra_76_tail_mono (infra_76_lt_h P (infra_73_h P σ)).le hμ)
        hνμ f hf qA qB e eA hqA hqB hidx hExt hT hIso⟩

/-- The well-order of length `ρ⁺` is a regular-cardinal order. -/
theorem infra_78_succ_isRegularCardinalOrder (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ) :
    IsRegularCardinalOrder (Order.succ ρ).ord.ToType :=
  ⟨by rw [Ordinal.type_toType, Ordinal.cof_toType, (Cardinal.isRegular_succ hρ).cof_ord]⟩

theorem infra_78_succ_cof_ne (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ) :
    Order.cof (Order.succ ρ).ord.ToType ≠ ℵ₀ := by
  rw [Ordinal.cof_toType, (Cardinal.isRegular_succ hρ).cof_ord]
  exact ((Order.lt_succ_of_not_isMax (not_isMax ρ)).trans_le' hρ).ne'

/-- **Pressing down on `ρ⁺` (Fodor; proved, from Mathlib).** A regressive function on a
stationary subset of `ρ⁺` is constant on a stationary subset. Used for the `ρ⁺`-matrix of
Proposition 7.8. -/
theorem infra_78_fodor (ρ : Cardinal.{u}) (hρ : ℵ₀ ≤ ρ)
    {s : Set (Order.succ ρ).ord.ToType} (hs : IsStationary s)
    {g : (Order.succ ρ).ord.ToType → (Order.succ ρ).ord.ToType} (hg : ∀ x ∈ s, g x < x) :
    ∃ a, IsStationary (s ∩ g ⁻¹' {a}) :=
  haveI := infra_78_succ_isRegularCardinalOrder ρ hρ
  exists_isStationary_preimage_singleton (infra_78_succ_cof_ne ρ hρ) hs hg

/-- **The `ρ⁺` matrix (data of Proposition 7.8's proof).** An increasing `ρ⁺`-chain of
pairs `X_i ≤ Y_i` at one level `κ`, with permitted inclusions commuting with the pair arrows (continuity at limits, Def 7.7, is not
encoded here). -/
structure Infra78Matrix (P : SingleModelData K) (ρ : Cardinal.{u}) {κ : Cardinal.{u}}
    (hκ : κ ∈ P.eligible) where
  X : (Order.succ ρ).ord.ToType → P.scheme.Object κ hκ
  Y : (Order.succ ρ).ord.ToType → P.scheme.Object κ hκ
  pair : ∀ i, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X i)) (P.scheme.asSystem hκ (Y i))
  pair_permitted : ∀ i, P.scheme.permitted (X := X i) (Y := Y i) (pair i)
  stepX : ∀ {i j}, i ≤ j →
    SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X i)) (P.scheme.asSystem hκ (X j))
  stepY : ∀ {i j}, i ≤ j →
    SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y i)) (P.scheme.asSystem hκ (Y j))
  stepX_permitted : ∀ {i j} (h : i ≤ j), P.scheme.permitted (X := X i) (Y := X j) (stepX h)
  stepY_permitted : ∀ {i j} (h : i ≤ j), P.scheme.permitted (X := Y i) (Y := Y j) (stepY h)
  comm : ∀ {i j} (h : i ≤ j),
    SystemArrow.comp (pair i) (stepY h) = SystemArrow.comp (stepX h) (pair j)

end
end AEC
