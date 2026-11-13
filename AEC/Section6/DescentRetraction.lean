module

public import AEC.Section6.AverageDescent
public import AEC.Section6.LocalCharacter
public import AEC.Section6.LargerLevelRealization
public import AEC.Section6.FreshStrip
public import AEC.Section6.TestCardinal
public import AEC.Section7.AllDominated
public import AEC.Section2.FiniteHull
public import AEC.Section4.ClosedLevels

@[expose] public section

/-!
# Lemma 6.17: descent through approximate retractions

Given a commuting square `A' ≤ A`, `U' ≤ U` at levels `ν ≤ μ` and a `ν`-indexed family of
arrows `rᵢ : U → A` that almost-fix `A` and send `U'` into `A'`, every short tuple of `U'`
has actual type over `A` equal to the free lift of its type over `A'`.

The restriction of each `rᵢ` through `toA` is `factorEmbedding`. A short subsequence of those
restrictions is an `ApproximationSequence` for `tp(d/A'; U')`. Same Galois type with the large
tuple is the commuting square (`toU` and `id`). Majority on queries in `A` uses a mixed-level
saturation move (generalizing `infra_610_move_query`) plus the almost-identity exceptions.
When `ν = μ` this is the same-level Lemma 6.11 path; when `ν < μ` the move uses
`IsSaturated` across levels (Cor 6.7 / `exists_saturation`).
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-! ## Restricting approximate retractions -/

/-- Image of `U'` under `r ∘ toU` lands in `A'`, so `factorEmbedding` supplies `restr : U' → A'`
with `toA ∘ restr = r ∘ toU`. -/
noncomputable def infra_617_restrEmb
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (A : P.scheme.Object μ hμ) (U : P.scheme.Object μ hμ)
    (A' : P.scheme.Object ν hν) (U' : P.scheme.Object ν hν)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hμ U))
    (r : SystemArrow K oneVertexShape (P.scheme.asSystem hμ U) (P.scheme.asSystem hμ A))
    (himg : ∀ x : U'.model.carrier,
      ∃ y : A'.model.carrier,
        toA.onVertex PUnit.unit y = r.onVertex PUnit.unit (toU.onVertex PUnit.unit x)) :
    Language.Embedding K.τ U'.model.carrier A'.model.carrier :=
  factorEmbedding
    ((r.onVertex PUnit.unit).comp (toU.onVertex PUnit.unit))
    (toA.onVertex PUnit.unit) himg

theorem infra_617_restrEmb_strong
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (A : P.scheme.Object μ hμ) (U : P.scheme.Object μ hμ)
    (A' : P.scheme.Object ν hν) (U' : P.scheme.Object ν hν)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hμ U))
    (r : SystemArrow K oneVertexShape (P.scheme.asSystem hμ U) (P.scheme.asSystem hμ A))
    (himg : ∀ x : U'.model.carrier,
      ∃ y : A'.model.carrier,
        toA.onVertex PUnit.unit y = r.onVertex PUnit.unit (toU.onVertex PUnit.unit x)) :
    K.Strong (infra_617_restrEmb A U A' U' toA toU r himg) :=
  strong_factorEmbedding
    ((r.onVertex PUnit.unit).comp (toU.onVertex PUnit.unit))
    (toA.onVertex PUnit.unit)
    (K.strong_trans _ _ (toU.onVertex_strong PUnit.unit) (r.onVertex_strong PUnit.unit))
    (toA.onVertex_strong PUnit.unit) himg

/-- The factored system arrow `U' → A'`. -/
noncomputable def infra_617_restr
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (A : P.scheme.Object μ hμ) (U : P.scheme.Object μ hμ)
    (A' : P.scheme.Object ν hν) (U' : P.scheme.Object ν hν)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hμ U))
    (r : SystemArrow K oneVertexShape (P.scheme.asSystem hμ U) (P.scheme.asSystem hμ A))
    (himg : ∀ x : U'.model.carrier,
      ∃ y : A'.model.carrier,
        toA.onVertex PUnit.unit y = r.onVertex PUnit.unit (toU.onVertex PUnit.unit x)) :
    SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hν A') :=
  oneVertexArrow (infra_617_restrEmb A U A' U' toA toU r himg)
    (infra_617_restrEmb_strong A U A' U' toA toU r himg)

theorem infra_617_restr_comp
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (A : P.scheme.Object μ hμ) (U : P.scheme.Object μ hμ)
    (A' : P.scheme.Object ν hν) (U' : P.scheme.Object ν hν)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hμ U))
    (r : SystemArrow K oneVertexShape (P.scheme.asSystem hμ U) (P.scheme.asSystem hμ A))
    (himg : ∀ x : U'.model.carrier,
      ∃ y : A'.model.carrier,
        toA.onVertex PUnit.unit y = r.onVertex PUnit.unit (toU.onVertex PUnit.unit x))
    (x : U'.model.carrier) :
    toA.onVertex PUnit.unit
        ((infra_617_restr A U A' U' toA toU r himg).onVertex PUnit.unit x) =
      r.onVertex PUnit.unit (toU.onVertex PUnit.unit x) :=
  factorEmbedding_apply
    ((r.onVertex PUnit.unit).comp (toU.onVertex PUnit.unit))
    (toA.onVertex PUnit.unit) himg x

/-! ## Same Galois type from the square -/

/-- `tp(d/A'; U')` and `(tp(toU∘d/A)) ↾ toA` are identified by `toU` and `id` on `U`. -/
theorem infra_617_same_galois
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (A : P.scheme.Object μ hμ) (U : P.scheme.Object μ hμ)
    (A' : P.scheme.Object ν hν) (U' : P.scheme.Object ν hν)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hμ U))
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ U))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hν U'))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (htoU : P.scheme.permitted (X := U') (Y := U) toU)
    (hincl : P.scheme.permitted (X := A) (Y := U) incl)
    (hincl' : P.scheme.permitted (X := A') (Y := U') incl')
    (hsq : ∀ v, (incl.onVertex v).comp (toA.onVertex v) =
      (toU.onVertex v).comp (incl'.onVertex v))
    {dIdx : Type u} (d : dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν U')) :
    let p := asTuple incl' hincl' d
    let q := asTuple incl hincl
      (fun i => ⟨(d i).1, toU.onVertex (d i).1 (d i).2⟩)
    SameGaloisType p (q.restrict toA htoA) (Equiv.refl dIdx) (Equiv.refl dIdx) := by
  intro p q
  refine ⟨μ, hμ, U, toU, SystemArrow.refl (P.scheme.asSystem hμ U), htoU, trivial, ?_, ?_⟩
  · intro v
    simp only [SystemArrow.refl, TupleOver.restrict, SystemArrow.comp]
    exact (hsq v).symm
  · intro i
    rfl

/-! ## Mixed move-query -/

/-- Saturation moves a query `Z` from `A` at `μ` into `A'` at `ν` over the concatenated
sequence copies, generalizing `infra_610_move_query` to `ν ≤ μ`. -/
theorem infra_617_move_query
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (hνμ : ν ≤ μ)
    {A' : P.scheme.Object ν hν} {A : P.scheme.Object μ hμ}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    {p : TupleOver K oneVertexShape P.scheme hν A'}
    (seq : ApproximationSequence p)
    {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (_hι : #ι ≤ seq.τ) (hιμ : #ι < ν) :
    ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A'),
      ∀ i : seq.κIndex,
        P.scheme.DiagramEq (X := A') (Y := A)
          (seqJoint (seq.family i) Z0)
          (seqJoint
            (fun j =>
              ⟨(seq.family i j).1,
                toA.onVertex (seq.family i j).1 (seq.family i j).2⟩)
            Z) := by
  classical
  let α : Type u := seq.κIndex × p.idx
  let xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hν A') :=
    fun ij => seq.family ij.1 ij.2
  let base : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun ij => ⟨(xs ij).1, toA.onVertex (xs ij).1 (xs ij).2⟩
  let ext : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    Sum.elim base Z
  have hα : #α < ν := seq.concat_bounded
  have hαμ : #α < μ := hα.trans_le hνμ
  have hEqPush : P.scheme.DiagramEq (X := A') (Y := A) xs base :=
    P.scheme.diagram_preserved A' A toA htoA xs hα hαμ
  obtain ⟨Z', g, zs, -, hzs, hzsEq⟩ :=
    (SingleModelData.isSaturated (P := P)).saturated
      A' A xs base ext hα hιμ (fun i => rfl) hEqPush
  have hPushG : P.scheme.DiagramEq (X := A') (Y := Z') xs
      (fun ij => ⟨(xs ij).1, g.onVertex (xs ij).1 (xs ij).2⟩) :=
    P.scheme.diagram_preserved A' Z' g trivial xs hα hα
  have hxsZs : (fun ij => ⟨(xs ij).1, g.onVertex (xs ij).1 (xs ij).2⟩) =
      fun ij => zs (Sum.inl ij) := by
    funext ij
    exact (hzs ij).symm
  have hEqZsInl : P.scheme.DiagramEq (X := A') (Y := Z') xs (fun ij => zs (Sum.inl ij)) := by
    rw [← hxsZs]
    exact hPushG
  obtain ⟨φ, hφiso, hφ⟩ :=
    (P.scheme.diagram_iso A' Z' xs (fun ij => zs (Sum.inl ij)) hα).mp hEqZsInl
  have hφbij : Function.Bijective (φ.onVertex PUnit.unit) := hφiso PUnit.unit
  let eφ : A'.model.carrier ≃ Z'.model.carrier := Equiv.ofBijective _ hφbij
  let Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A') :=
    fun j => A'.occ (eφ.symm (Z'.val (zs (Sum.inr j))))
  let jointA : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A') :=
    Sum.elim xs Z0
  have hφjoint : ∀ t, zs t =
      ⟨(jointA t).1, φ.onVertex (jointA t).1 (jointA t).2⟩ := by
    intro t
    cases t with
    | inl ij =>
      change zs (Sum.inl ij) = ⟨(xs ij).1, φ.onVertex (xs ij).1 (xs ij).2⟩
      exact hφ ij
    | inr j =>
      have happly : φ.onVertex PUnit.unit (eφ.symm (Z'.val (zs (Sum.inr j)))) =
          Z'.val (zs (Sum.inr j)) := eφ.apply_symm_apply _
      change zs (Sum.inr j) = ⟨(Z0 j).1, φ.onVertex (Z0 j).1 (Z0 j).2⟩
      refine Eq.trans (SMObject.occ_val Z' (zs (Sum.inr j))).symm ?_
      refine Eq.trans (congrArg Z'.occ happly.symm) ?_
      simp only [Z0, SMObject.occ, oneVertexOcc, SMObject.val, oneVertexVal]
      rfl
  have hPushφ : P.scheme.DiagramEq (X := A') (Y := Z') jointA zs := by
    have hcard : #(α ⊕ ι) < ν := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact add_lt_of_lt (P.aleph0_le hν) hα hιμ
    have h := P.scheme.diagram_preserved A' Z' φ trivial jointA hcard hcard
    have heq : (fun t => ⟨(jointA t).1, φ.onVertex (jointA t).1 (jointA t).2⟩) = zs :=
      funext fun t => (hφjoint t).symm
    rwa [heq] at h
  have hJointExt : P.scheme.DiagramEq (X := A') (Y := A) jointA ext :=
    P.scheme.diagram_trans A' Z' A jointA zs ext hPushφ hzsEq
  refine ⟨Z0, fun i => ?_⟩
  let ρ : p.idx ⊕ ι → α ⊕ ι := fun t =>
    match t with
    | Sum.inl j => Sum.inl (i, j)
    | Sum.inr b => Sum.inr b
  have hρ : Function.Injective ρ := by
    intro x y hxy
    cases x with
    | inl j =>
      cases y with
      | inl j' =>
        simp only [ρ] at hxy
        exact congrArg Sum.inl (Prod.ext_iff.mp (Sum.inl.inj hxy)).2
      | inr k => simp [ρ] at hxy
    | inr k =>
      cases y with
      | inl j => simp [ρ] at hxy
      | inr k' =>
        simp only [ρ] at hxy
        exact congrArg Sum.inr (Sum.inr.inj hxy)
  have hL : (fun t => jointA (ρ t)) = seqJoint (seq.family i) Z0 := by
    funext t; cases t <;> rfl
  have hR : (fun t => ext (ρ t)) =
      seqJoint
        (fun j =>
          ⟨(seq.family i j).1, toA.onVertex (seq.family i j).1 (seq.family i j).2⟩) Z := by
    funext t; cases t <;> rfl
  have hpre :=
    WorkingScheme.diagramEq_precomp (W := P.scheme) A' A jointA ext ρ hρ hJointExt
  exact hL.symm ▸ hR.symm ▸ hpre

/-! ## Exception bounds from almost-identity -/

/-- Exception bound: indices that move some point of a short list in `A` have size at most
`|Z| + ℵ₀`. -/
theorem infra_617_almost_id_bound'
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A U : P.scheme.Object μ hμ}
    {ι : Type u}
    (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem hμ U) (P.scheme.asSystem hμ A))
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ U))
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
      Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2})
    {β : Type u}
    (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) :
    #{i : ι // ∃ b : β, (r i).onVertex (Z b).1 (incl.onVertex (Z b).1 (Z b).2) ≠ (Z b).2} ≤
      #β + aleph0 := by
  classical
  let hitSet : β → Set ι := fun z =>
    {i | (r i).onVertex (Z z).1 (incl.onVertex (Z z).1 (Z z).2) ≠ (Z z).2}
  have hpt : ∀ z, #(hitSet z) ≤ aleph0 :=
    fun z => by
      classical
      haveI := Fintype.ofFinite {i : ι //
          (r i).onVertex (Z z).1 (incl.onVertex (Z z).1 (Z z).2) ≠ (Z z).2}
      simpa [hitSet, mk_fintype, Fintype.card_fin] using Nat.cast_le.mpr (Fintype.card_lt _).le
  have hunion : #(⋃ z, hitSet z) ≤ #β * aleph0 := by
    calc #(⋃ z, hitSet z) ≤ sum fun z => #(hitSet z) := mk_iUnion_le_sum_mk
      _ ≤ #β * ⨆ z, #(hitSet z) := sum_le_mk_mul_iSup _
      _ ≤ #β * aleph0 := mul_le_mul' le_rfl (ciSup_le' hpt)
  have hsub :
      #{i : ι // ∃ b : β, (r i).onVertex (Z b).1 (incl.onVertex (Z b).1 (Z b).2) ≠ (Z b).2} ≤
        #(⋃ z, hitSet z) := by
    refine mk_le_of_injective (f := fun i =>
      (⟨i.1, ?_⟩ : ↥(⋃ z, hitSet z))) ?_
    · rcases i.2 with ⟨b, hp⟩
      exact Set.mem_iUnion.mpr ⟨b, hp⟩
    · rintro ⟨i, hi⟩ ⟨j, hj⟩ h
      exact Subtype.ext (congrArg Subtype.val (by simpa using h))
  have hmul : #β * aleph0 ≤ #β + aleph0 := by
    rcases eq_or_ne #β 0 with h0 | hne
    · simp [h0]
    · rcases le_or_gt #β aleph0 with hle | hgt
      · calc #β * aleph0 ≤ aleph0 * aleph0 :=
            mul_le_mul' hle le_rfl
        _ = aleph0 := aleph0_mul_aleph0
        _ ≤ #β + aleph0 := le_add_self
      · have hinf : aleph0 ≤ #β := le_of_lt hgt
        calc #β * aleph0 = #β := Cardinal.mul_eq_left hinf hinf aleph0_ne_zero
          _ ≤ #β + aleph0 := self_le_add_right _ aleph0
  exact hsub.trans (hunion.trans hmul)

/-! ## Approximation sequence scaffolding -/

theorem infra_617_pick_subindex {ι : Type u} {ν κ : Cardinal.{u}}
    (hι : #ι = ν) (hκ : κ ≤ ν) :
    ∃ (κIndex : Type u), ∃ (h : #κIndex = κ), ∃ (e : κIndex ↪ ι), True := by
  have hle : κ ≤ #ι := hι.symm ▸ hκ
  have hn : Nonempty (κ.ord.ToType ↪ ι) := by
    rwa [← Cardinal.le_def, Cardinal.mk_ord_toType]
  obtain ⟨e⟩ := hn
  exact ⟨κ.ord.ToType, Cardinal.mk_ord_toType κ, e, trivial⟩

theorem infra_615_recursionClosed
    (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ infra_615_closed P)
    {σ : Cardinal.{u}} (hσ : aleph0 ≤ σ) (hσμ : σ < μ) :
    μ ∈ recursionClosedLevels P σ :=
  ⟨hμ.1, fun β₀ hβ₀ => hμ.2 σ hσ hσμ β₀ hβ₀⟩

def infra_617_pushOcc
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A' : P.scheme.Object ν hν} {A : P.scheme.Object μ hμ}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    {ι : Type u}
    (a : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A')) :
    ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
  fun i => pushOcc toA (a i)

/-! ## Pull and large-sequence bounds -/

theorem infra_617_pull_exceptions
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible} (hνμ : ν ≤ μ)
    {A' : P.scheme.Object ν hν} {A : P.scheme.Object μ hμ}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence q)
    (family' : seq.κIndex → q.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν A'))
    (hpush : ∀ s j, pushOcc toA (family' s j) = seq.family s j)
    (hidxν : #q.idx < ν) (hτν : seq.τ < ν)
    {β : Type u}
    (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A'))
    (hβ : #β ≤ seq.τ) :
    # {s : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := (q.restrict toA htoA).host) (Y := A')
          (typeJoint (p := q.restrict toA htoA) Z0) (seqJoint (family' s) Z0)} ≤
      #β + aleph0 := by
  classical
  let pR := q.restrict toA htoA
  let Zp : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun b => pushOcc toA (Z0 b)
  have hjointν : #(q.idx ⊕ β) < ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact add_lt_of_lt (P.aleph0_le hν) hidxν (hβ.trans_lt hτν)
  have hjointμ : #(q.idx ⊕ β) < μ := hjointν.trans_le hνμ
  have htype : typeJoint (p := pR) Z0 = typeJoint (p := q) Zp := by
    funext t; cases t <;> rfl
  have hpres : ∀ s : seq.κIndex,
      P.scheme.DiagramEq (X := A') (Y := A)
        (seqJoint (family' s) Z0) (seqJoint (seq.family s) Zp) := by
    intro s
    have hraw :=
      P.scheme.diagram_preserved A' A toA htoA (seqJoint (family' s) Z0) hjointν hjointμ
    have hseq : seqJoint (fun j => pushOcc toA (family' s j)) Zp =
        seqJoint (seq.family s) Zp := by
      have hfam : (fun j => pushOcc toA (family' s j)) = seq.family s :=
        funext fun j => hpush s j
      rw [hfam]
    have hform : (fun i =>
        ⟨(seqJoint (family' s) Z0 i).1,
          toA.onVertex (seqJoint (family' s) Z0 i).1 (seqJoint (family' s) Z0 i).2⟩) =
        fun i => pushOcc toA (seqJoint (family' s) Z0 i) := by
      funext i; rfl
    rw [hform, seqJoint_pushOcc, hseq] at hraw
    exact hraw
  let φ :
      {s : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := pR.host) (Y := A')
          (typeJoint (p := pR) Z0) (seqJoint (family' s) Z0)} →
      {k : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
          (typeJoint (p := q) Zp) (seqJoint (seq.family k) Zp)} := by
    rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    intro hgood
    apply hs
    have hback :=
      P.scheme.diagram_trans q.host A A'
        (typeJoint (p := q) Zp) (seqJoint (seq.family s) Zp) (seqJoint (family' s) Z0)
        hgood (P.scheme.diagram_symm A' A _ _ (hpres s))
    rw [← htype] at hback
    exact hback
  have hφ : Function.Injective φ := by
    rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hv : (φ ⟨s, hs⟩).1 = (φ ⟨s', hs'⟩).1 := congrArg Subtype.val h
    exact Subtype.ext hv
  exact (Cardinal.mk_le_of_injective hφ).trans (seq.few_exceptions Zp hβ)

theorem infra_617_tuple_hit_bound
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A U : P.scheme.Object μ hμ}
    {ι : Type u}
    (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem hμ U) (P.scheme.asSystem hμ A))
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ U))
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
      Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2})
    {idx : Type u} (tuple : idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) :
    #(⋃ j, {i : ι |
        (r i).onVertex (tuple j).1 (incl.onVertex (tuple j).1 (tuple j).2) ≠ (tuple j).2}) ≤
      #idx * aleph0 := by
  classical
  let hitSet : idx → Set ι := fun j =>
    {i | (r i).onVertex (tuple j).1 (incl.onVertex (tuple j).1 (tuple j).2) ≠ (tuple j).2}
  have hpt : ∀ j, #(hitSet j) ≤ aleph0 := fun j => by
    classical
    haveI := Fintype.ofFinite {i : ι //
        (r i).onVertex (tuple j).1 (incl.onVertex (tuple j).1 (tuple j).2) ≠ (tuple j).2}
    simpa [hitSet, mk_fintype, Fintype.card_fin] using
      Nat.cast_le.mpr (Fintype.card_lt _).le
  have hunion :
      #(⋃ j, hitSet j) ≤ sum fun j => #(hitSet j) := mk_iUnion_le_sum_mk
  refine le_trans hunion ?_
  calc (sum fun j => #(hitSet j)) ≤ #idx * ⨆ j, #(hitSet j) := sum_le_mk_mul_iSup _
    _ ≤ #idx * aleph0 := mul_le_mul' le_rfl (ciSup_le' hpt)

/-! ## Approximation sequence from restricted copies -/

/-- `few_exceptions` for restrictions pulls back along `toA` from a large-host sequence. -/
noncomputable def infra_617_restrSequence
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible} (hνμ : ν ≤ μ)
    {A' : P.scheme.Object ν hν} {U' : P.scheme.Object ν hν}
    {A : P.scheme.Object μ hμ} {U : P.scheme.Object μ hμ}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hμ U))
    (htoU : P.scheme.permitted (X := U') (Y := U) toU)
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ U))
    (hincl : P.scheme.permitted (X := A) (Y := U) incl)
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hν U'))
    (hincl' : P.scheme.permitted (X := A') (Y := U') incl')
    {dIdx : Type u}
    (d : dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν U'))
    (hd : #dIdx < ν)
    (largeSeq : ApproximationSequence (asTuple incl hincl
      (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩)))
    (hτν : largeSeq.τ < ν)
    (hconcat : #(largeSeq.κIndex × dIdx) < ν)
    (familyS : largeSeq.κIndex → dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν A'))
    (hpush : ∀ k j, pushOcc toA (familyS k j) = largeSeq.family k j)
    (hfew : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A')),
      #ι ≤ largeSeq.τ →
      # {k : largeSeq.κIndex //
          ¬ P.scheme.DiagramEq (X := (asTuple incl' hincl' d).host) (Y := A')
            (typeJoint (p := asTuple incl' hincl' d) Z) (seqJoint (familyS k) Z)} ≤
        #ι + aleph0) :
    ApproximationSequence (asTuple incl' hincl' d) where
  τ := largeSeq.τ
  κIndex := largeSeq.κIndex
  family := familyS
  concat_bounded := hconcat
  few_exceptions := hfew

/-! ## Majority bridges (Lemma 6.11 style, mixed levels) -/

theorem infra_617_bridge
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A' : P.scheme.Object ν hν} {A : P.scheme.Object μ hμ}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence (q.restrict toA htoA))
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hmaj : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A'),
        IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z))
    {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hι : #ι ≤ seq.τ) :
    ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A'),
      P.scheme.DiagramEq (X := (q.restrict toA htoA).host) (Y := q.host)
        (typeJoint (p := q.restrict toA htoA) Z0) (typeJoint (p := q) Z) := by
  let p := q.restrict toA htoA
  obtain ⟨Z0, hQ⟩ := hmaj Z hι
  have hP : IsMajorityValue seq Z0 p.hν p.host (typeJoint (p := p) Z0) :=
    infra_610_majority_eq_type seq Z0 hι
  have hbound : #ι + aleph0 < #seq.κIndex := (add_le_add hι le_rfl).trans_lt hκ
  exact ⟨Z0, infra_610_majority_unique seq Z0
    (xs := typeJoint (p := p) Z0) (ys := typeJoint (p := q) Z) hP hQ hbound⟩

theorem infra_617_code_majority
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A' : P.scheme.Object ν hν} {A : P.scheme.Object μ hμ}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence (q.restrict toA htoA))
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hmaj : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A'),
        IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z))
    (code : ApproximationSequence (q.restrict toA htoA))
    (hτ : seq.τ ≤ code.τ)
    {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hι : #ι ≤ seq.τ) :
    ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A'),
      IsMajorityValue code Z0 q.hν q.host (typeJoint (p := q) Z) := by
  obtain ⟨Z0, hEq⟩ := infra_617_bridge toA htoA q seq hκ hmaj Z hι
  have hιcode : #ι ≤ code.τ := hι.trans hτ
  have hP : IsMajorityValue code Z0 (q.restrict toA htoA).hν (q.restrict toA htoA).host
      (typeJoint (p := q.restrict toA htoA) Z0) :=
    infra_610_majority_eq_type code Z0 hιcode
  exact ⟨Z0, infra_611_majority_transport code Z0
    (typeJoint (p := q.restrict toA htoA) Z0) (typeJoint (p := q) Z) hP hEq⟩

theorem infra_617_image_agree
    {P : SingleModelData K}
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible} (hνμ : ν ≤ μ)
    {A' : P.scheme.Object ν hν} {A : P.scheme.Object μ hμ}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (seq : ApproximationSequence (q.restrict toA htoA))
    (hidxν : #(q.restrict toA htoA).idx < ν)
    (hτν : seq.τ < ν)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hmaj : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A'),
        IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z))
    {β : Type u} (params : β → A'.model.carrier) (hβ : #β ≤ seq.τ) :
    P.scheme.DiagramEq (X := (q.restrict toA htoA).host) (Y := q.host)
      (typeJoint (p := q.restrict toA htoA) (fun b => A'.occ (params b)))
      (typeJoint (p := q) (fun b => pushOcc toA (A'.occ (params b)))) := by
  classical
  let p := q.restrict toA htoA
  let Zpar : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A') :=
    fun b => A'.occ (params b)
  let Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun b => pushOcc toA (Zpar b)
  have hιν : #β < ν := hβ.trans_lt hτν
  obtain ⟨Z0m, hmove⟩ := infra_617_move_query (P := P) hνμ toA htoA seq Z hβ hιν
  obtain ⟨Z0h, hBridge⟩ := infra_617_bridge toA htoA q seq hκ hmaj Z hβ
  have hidxμ : #(q.restrict toA htoA).idx < μ := hidxν.trans_le hνμ
  have hcard : #(p.idx ⊕ β) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hidxμ (hιν.trans_le hνμ)
  have hpres : ∀ i : seq.κIndex,
      P.scheme.DiagramEq (X := A') (Y := A)
        (seqJoint (seq.family i) Zpar)
        (seqJoint (fun j => pushOcc toA (seq.family i j)) Z) := by
    intro i
    have hjointν : #(p.idx ⊕ β) < ν := by
      rw [mk_sum, lift_id, lift_id]
      exact add_lt_of_lt (P.aleph0_le hν) hidxν hιν
    have hraw :=
      P.scheme.diagram_preserved A' A toA htoA (seqJoint (seq.family i) Zpar) hjointν hcard
    simpa [seqJoint_pushOcc] using hraw
  have hbound : #β + aleph0 < #seq.κIndex := (add_le_add hβ le_rfl).trans_lt hκ
  let ExcM : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A') (Y := p.host)
      (seqJoint (seq.family i) Z0m) (typeJoint (p := p) Z0m)}
  let ExcPar : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A') (Y := p.host)
      (seqJoint (seq.family i) Zpar) (typeJoint (p := p) Zpar)}
  have hExcM : #ExcM ≤ #β + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A') (Y := p.host)
          (seqJoint (seq.family i) Z0m) (typeJoint (p := p) Z0m)} ≤ _
    exact infra_610_majority_eq_type seq Z0m hβ
  have hExcPar : #ExcPar ≤ #β + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A') (Y := p.host)
          (seqJoint (seq.family i) Zpar) (typeJoint (p := p) Zpar)} ≤ _
    exact infra_610_majority_eq_type seq Zpar hβ
  have hex : ∃ i : seq.κIndex, i ∉ ExcM ∧ i ∉ ExcPar := by
    by_contra h
    have hall : (Set.univ : Set seq.κIndex) ⊆ ExcM ∪ ExcPar := by
      intro i _
      by_cases hi : i ∈ ExcM ∪ ExcPar
      · exact hi
      · exact False.elim (h ⟨i, by
          simp only [Set.mem_union, not_or] at hi ⊢
          exact hi⟩)
    have hinfκ : aleph0 ≤ #seq.κIndex :=
      (le_add_self (a := aleph0) (b := #β)).trans (le_of_lt hbound)
    have hle : #seq.κIndex ≤ (#β + aleph0) + (#β + aleph0) := by
      have huni : #(Set.univ : Set seq.κIndex) = #seq.κIndex := mk_univ
      rw [← huni]
      exact (mk_le_mk_of_subset hall).trans ((mk_union_le _ _).trans (add_le_add hExcM hExcPar))
    exact (not_le_of_gt (add_lt_of_lt hinfκ hbound hbound)) hle
  obtain ⟨i, hiM, hiPar⟩ := hex
  have hgoodM : P.scheme.DiagramEq (X := A') (Y := p.host)
      (seqJoint (seq.family i) Z0m) (typeJoint (p := p) Z0m) := by
    simpa [ExcM] using hiM
  have hgoodPar : P.scheme.DiagramEq (X := A') (Y := p.host)
      (seqJoint (seq.family i) Zpar) (typeJoint (p := p) Zpar) := by
    simpa [ExcPar] using hiPar
  have hJoint : P.scheme.DiagramEq (X := A') (Y := A')
      (seqJoint (seq.family i) Z0m) (seqJoint (seq.family i) Zpar) :=
    P.scheme.diagram_trans A' A A'
      (seqJoint (seq.family i) Z0m)
      (seqJoint (fun j => pushOcc toA (seq.family i j)) Z)
      (seqJoint (seq.family i) Zpar)
      (hmove i) (P.scheme.diagram_symm A' A _ _ (hpres i))
  have hTypes : P.scheme.DiagramEq (X := p.host) (Y := p.host)
      (typeJoint (p := p) Z0m) (typeJoint (p := p) Zpar) :=
    P.scheme.diagram_trans p.host A' p.host
      (typeJoint (p := p) Z0m) (seqJoint (seq.family i) Z0m) (typeJoint (p := p) Zpar)
      (P.scheme.diagram_symm A' p.host _ _ hgoodM)
      (P.scheme.diagram_trans A' A' p.host
        (seqJoint (seq.family i) Z0m) (seqJoint (seq.family i) Zpar)
        (typeJoint (p := p) Zpar) hJoint hgoodPar)
  have hEqFun : typeJoint (p := p) Zpar = typeJoint (p := q) Z := by
    funext t <;> cases t <;> rfl
  have hParQ : P.scheme.DiagramEq (X := p.host) (Y := q.host)
      (typeJoint (p := p) Zpar) (typeJoint (p := q) Z) := by
    rw [hEqFun]
    exact P.scheme.diagram_refl q.host _
  have hViaMove : P.scheme.DiagramEq (X := p.host) (Y := q.host)
      (typeJoint (p := p) Zpar) (typeJoint (p := q) Z) :=
    P.scheme.diagram_trans p.host p.host q.host
      (typeJoint (p := p) Zpar) (typeJoint (p := p) Z0m) (typeJoint (p := q) Z)
      (P.scheme.diagram_symm p.host p.host _ _ hTypes)
      (P.scheme.diagram_trans p.host p.host q.host
        (typeJoint (p := p) Z0m) (typeJoint (p := p) Zpar) (typeJoint (p := q) Z)
        hTypes hParQ)
  have hRound : P.scheme.DiagramEq (X := q.host) (Y := q.host)
      (typeJoint (p := q) Z) (typeJoint (p := q) Z) :=
    P.scheme.diagram_trans q.host p.host q.host
      (typeJoint (p := q) Z) (typeJoint (p := p) Z0h) (typeJoint (p := q) Z)
      (P.scheme.diagram_symm p.host q.host _ _ hBridge) hBridge
  exact P.scheme.diagram_trans p.host q.host q.host
    (typeJoint (p := p) Zpar) (typeJoint (p := q) Z) (typeJoint (p := q) Z)
    hViaMove hRound

/-! ## IsFreeLift -/

theorem infra_617_isFreeLift
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible} (hνμ : ν ≤ μ)
    (hrecν : ν ∈ recursionClosedLevels P σ) (hσSuccν : Order.succ σ ≤ ν)
    {A' : P.scheme.Object ν hν} {U' : P.scheme.Object ν hν}
    {A : P.scheme.Object μ hμ} {U : P.scheme.Object μ hμ}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hμ A))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hμ U))
    (htoU : P.scheme.permitted (X := U') (Y := U) toU)
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ U))
    (hincl : P.scheme.permitted (X := A) (Y := U) incl)
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν A') (P.scheme.asSystem hν U'))
    (hincl' : P.scheme.permitted (X := A') (Y := U') incl')
    (hsq : ∀ v, (incl.onVertex v).comp (toA.onVertex v) =
      (toU.onVertex v).comp (incl'.onVertex v))
    {dIdx : Type u}
    (d : dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν U'))
    (seq : ApproximationSequence (asTuple incl' hincl' d))
    (hidx : #dIdx ≤ σ) (hidxν : #dIdx < ν)
    (hτν : seq.τ < ν) (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hmaj : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A'),
        IsMajorityValue seq Z0
          (asTuple incl hincl (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩)).hν
          (asTuple incl hincl (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩)).host
          (typeJoint
            (p := asTuple incl hincl (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩)) Z)) :
    IsFreeLift
      (asTuple incl' hincl' d)
      (asTuple incl hincl (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩))
      toA htoA (Equiv.refl dIdx) := by
  let p := asTuple incl' hincl' d
  let q := asTuple incl hincl (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩)
  refine ⟨infra_617_same_galois A U A' U' toA toU incl incl' htoA htoU hincl hincl' hsq d,
    seq, ?_⟩
  intro ι Z hι
  obtain ⟨Z0, hm⟩ := hmaj Z hι
  exact ⟨Z0, typeJoint (p := q) Z, hm⟩

/-! ## Retraction family → free lift -/

/-- Build the free lift from a `ν`-indexed almost-identity family with image in `A'`. -/
theorem infra_617_from_retractions
    (P : SingleModelData K)
    {ν μ : Cardinal.{u}} (hνC : ν ∈ infra_615_closed P) (hμC : μ ∈ infra_615_closed P)
    (hνμ : ν ≤ μ)
    (A : P.scheme.Object μ hμC.1) (U : P.scheme.Object μ hμC.1)
    (A' : P.scheme.Object ν hνC.1) (U' : P.scheme.Object ν hνC.1)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A') (P.scheme.asSystem hμC.1 A))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 U') (P.scheme.asSystem hμC.1 U))
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 A) (P.scheme.asSystem hμC.1 U))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A') (P.scheme.asSystem hνC.1 U'))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (htoU : P.scheme.permitted (X := U') (Y := U) toU)
    (hincl : P.scheme.permitted (X := A) (Y := U) incl)
    (hincl' : P.scheme.permitted (X := A') (Y := U') incl')
    (hsq : ∀ v, (incl.onVertex v).comp (toA.onVertex v) =
      (toU.onVertex v).comp (incl'.onVertex v))
    {ι : Type u}
    (r : ι → SystemArrow K oneVertexShape (P.scheme.asSystem hμC.1 U) (P.scheme.asSystem hμC.1 A))
    (hιcard : #ι = ν)
    (_hr : ∀ i, P.scheme.permitted (X := U) (Y := A) (r i))
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hμC.1 A),
      Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2})
    (himg : ∀ i (x : U'.model.carrier),
      ∃ y : A'.model.carrier,
        toA.onVertex PUnit.unit y = (r i).onVertex PUnit.unit (toU.onVertex PUnit.unit x))
    {dIdx : Type u}
    (d : dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 U'))
    (hd : #dIdx < ν) :
    IsFreeLift
      (asTuple incl' hincl' d)
      (asTuple incl hincl (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩))
      toA htoA (Equiv.refl dIdx) := by
  classical
  let hν : ν ∈ P.eligible := hνC.1
  let hμ : μ ∈ P.eligible := hμC.1
  let p := asTuple incl' hincl' d
  let q := asTuple incl hincl (fun j => ⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩)
  let σ : Cardinal.{u} := max #dIdx aleph0
  have hσ : aleph0 ≤ σ := le_max_right _ _
  have hσν : σ < ν := max_lt hd (P.aleph0_lt hν)
  have hidx : #dIdx ≤ σ := le_max_left _ _
  have hrecν : ν ∈ recursionClosedLevels P σ :=
    infra_615_recursionClosed P hνC hσ hσν
  have hκ0 : Order.succ σ < ν :=
    (Order.succ_le_of_lt (cantor σ)).trans_lt
      (hν.1.working.strongLimit.isStrongPrelimit hσν)
  have hσSuccν : Order.succ σ ≤ ν := le_of_lt hκ0
  let τ : Cardinal.{u} := σ
  let κ : Cardinal.{u} := Order.succ τ
  have hτ : aleph0 ≤ τ := hσ
  have hτν : τ < ν := hσν
  have hκ : aleph0 ≤ κ := hτ.trans (Order.le_succ _)
  have hκν : κ < ν := hκ0
  have hlen : τ + aleph0 < κ := by
    have : τ + aleph0 = τ := add_eq_left hτ hτ
    exact this.symm ▸ Order.lt_succ τ
  obtain ⟨κIndex, hκcard, e, _⟩ := infra_617_pick_subindex (ι := ι) hιcard (le_of_lt hκν)
  have himg' : ∀ i, ∀ x : U'.model.carrier,
      ∃ y : A'.model.carrier,
        toA.onVertex PUnit.unit y =
          (r i).onVertex PUnit.unit (toU.onVertex PUnit.unit x) := himg
  let restr : κIndex →
      SystemArrow K oneVertexShape (P.scheme.asSystem hν U') (P.scheme.asSystem hν A') :=
    fun k => infra_617_restr A U A' U' toA toU (r (e k)) (himg' (e k))
  let familyS : κIndex → dIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν A') :=
    fun k j => ⟨(d j).1, (restr k).onVertex (d j).1 (d j).2⟩
  have hconcat : #(κIndex × dIdx) < ν := by
    rw [mk_prod, lift_id, lift_id, hκcard]
    have hmul : κ * #dIdx ≤ κ * σ := mul_le_mul' le_rfl hidx
    have heq : κ * σ = κ :=
      Cardinal.mul_eq_left hκ (Order.le_succ σ) (aleph0_pos.trans_le hσ).ne'
    exact (hmul.trans_eq heq).trans_lt hκν
  -- few_exceptions
  have hfew : ∀ {β : Type u}
      (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A')),
      #β ≤ τ →
      # {k : κIndex //
          ¬ P.scheme.DiagramEq (X := p.host) (Y := A')
            (typeJoint (p := p) Z) (seqJoint (familyS k) Z)} ≤ #β + aleph0 := by
    intro β Z hβ
    let Zp : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
      fun b => pushOcc toA (Z b)
    have hExc := infra_617_almost_id_bound' (P := P) r incl halmost Zp
    let Bad := {k : κIndex //
        ¬ P.scheme.DiagramEq (X := p.host) (Y := A')
          (typeJoint (p := p) Z) (seqJoint (familyS k) Z)}
    let Exc := {i : ι // ∃ b : β,
        (r i).onVertex (Zp b).1 (incl.onVertex (Zp b).1 (Zp b).2) ≠ (Zp b).2}
    have hgood : ∀ k : κIndex,
        (∀ b : β, (r (e k)).onVertex (Zp b).1 (incl.onVertex (Zp b).1 (Zp b).2) = (Zp b).2) →
        P.scheme.DiagramEq (X := p.host) (Y := A')
          (typeJoint (p := p) Z) (seqJoint (familyS k) Z) := by
      intro k hfix
      have hjointν : #(dIdx ⊕ β) < ν := by
        rw [mk_sum, lift_id, lift_id]
        exact add_lt_of_lt (P.aleph0_le hν) hd (hβ.trans_lt hτν)
      have hjointμ : #(dIdx ⊕ β) < μ := hjointν.trans_le hνμ
      -- typeJoint p Z  --toU→  typeJoint q Zp
      have hToU : P.scheme.DiagramEq (X := p.host) (Y := q.host)
          (typeJoint (p := p) Z) (typeJoint (p := q) Zp) := by
        have hpush :=
          P.scheme.diagram_preserved p.host q.host toU htoU
            (typeJoint (p := p) Z) hjointν hjointμ
        have heq : (fun i => toU.mapOcc (typeJoint (p := p) Z i)) = typeJoint (p := q) Zp := by
          funext i
          cases i with
          | inl j => rfl
          | inr b =>
            dsimp only [SystemArrow.mapOcc, typeJoint, Zp]
            congr 1
            exact (congrFun (congrArg DFunLike.coe (hsq (Z b).1)) (Z b).2).symm
        exact heq ▸ hpush
      -- typeJoint q Zp  --r→  (toA∘restr d) ++ Zp, using fix
      have hR : P.scheme.DiagramEq (X := q.host) (Y := A)
          (typeJoint (p := q) Zp)
          (seqJoint (fun j => pushOcc toA (familyS k j)) Zp) := by
        have hpush :=
          P.scheme.diagram_preserved q.host A (r (e k)) trivial
            (typeJoint (p := q) Zp) hjointμ hjointμ
        have heq : (fun i => (r (e k)).mapOcc (typeJoint (p := q) Zp i)) =
            seqJoint (fun j => pushOcc toA (familyS k j)) Zp := by
          funext i
          cases i with
          | inl j =>
            dsimp [SystemArrow.mapOcc, pushOcc, typeJoint, seqJoint, q, familyS]
            congr 1
            exact (infra_617_restr_comp A U A' U' toA toU (r (e k)) (himg' (e k))
              (d j).2).symm
          | inr b =>
            dsimp [SystemArrow.mapOcc, pushOcc, typeJoint, seqJoint, Zp]
            congr 1
            exact hfix b
        exact heq ▸ hpush
      -- seqJoint familyS Z  --toA→  push family ++ Zp
      have hToA : P.scheme.DiagramEq (X := A') (Y := A)
          (seqJoint (familyS k) Z)
          (seqJoint (fun j => pushOcc toA (familyS k j)) Zp) := by
        have hraw :=
          P.scheme.diagram_preserved A' A toA htoA
            (seqJoint (familyS k) Z) hjointν hjointμ
        simpa [seqJoint_pushOcc] using hraw
      -- chain
      exact P.scheme.diagram_trans p.host q.host A'
        (typeJoint (p := p) Z) (typeJoint (p := q) Zp) (seqJoint (familyS k) Z)
        hToU
        (P.scheme.diagram_trans q.host A A'
          (typeJoint (p := q) Zp)
          (seqJoint (fun j => pushOcc toA (familyS k j)) Zp)
          (seqJoint (familyS k) Z)
          hR (P.scheme.diagram_symm A' A _ _ hToA))
    let φ : Bad → Exc := fun ⟨k, hk⟩ =>
      ⟨e k, by
        by_contra hnone
        have hfix : ∀ b, (r (e k)).onVertex (Zp b).1
            (incl.onVertex (Zp b).1 (Zp b).2) = (Zp b).2 := fun b => by
          by_contra hne
          exact hnone ⟨b, hne⟩
        exact hk (hgood k hfix)⟩
    have hφ : Injective φ := by
      intro ⟨k, hk⟩ ⟨k', hk'⟩ h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    exact (mk_le_of_injective hφ).trans hExc
  let seq : ApproximationSequence p :=
    { τ := τ
      κIndex := κIndex
      family := familyS
      concat_bounded := hconcat
      few_exceptions := hfew }
  have hκbound : seq.τ + aleph0 < #seq.κIndex := by
    change τ + aleph0 < #κIndex
    rw [hκcard]
    exact hlen
  -- majority on queries in A
  have hmaj : ∀ {β : Type u}
      (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #β ≤ seq.τ →
      ∃ Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A'),
        IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z) := by
    intro β Z hβ
    have hβν : #β < ν := hβ.trans_lt hτν
    obtain ⟨Z0, hmove⟩ :=
      infra_617_move_query (P := P) hνμ toA htoA seq Z hβ hβν
    refine ⟨Z0, ?_⟩
    change # {k : κIndex //
        ¬ P.scheme.DiagramEq (X := A') (Y := q.host)
          (seqJoint (familyS k) Z0) (typeJoint (p := q) Z)} ≤ #β + aleph0
    let Exc := {i : ι // ∃ b : β,
        (r i).onVertex (Z b).1 (incl.onVertex (Z b).1 (Z b).2) ≠ (Z b).2}
    have hExc := infra_617_almost_id_bound' (P := P) r incl halmost Z
    let Bad := {k : κIndex //
        ¬ P.scheme.DiagramEq (X := A') (Y := q.host)
          (seqJoint (familyS k) Z0) (typeJoint (p := q) Z)}
    have hgood : ∀ k : κIndex,
        (∀ b : β, (r (e k)).onVertex (Z b).1 (incl.onVertex (Z b).1 (Z b).2) = (Z b).2) →
        P.scheme.DiagramEq (X := A') (Y := q.host)
          (seqJoint (familyS k) Z0) (typeJoint (p := q) Z) := by
      intro k hfix
      have hjointν : #(dIdx ⊕ β) < ν := by
        rw [mk_sum, lift_id, lift_id]
        exact add_lt_of_lt (P.aleph0_le hν) hd hβν
      have hjointμ : #(dIdx ⊕ β) < μ := hjointν.trans_le hνμ
      have hMove := hmove k
      have hR : P.scheme.DiagramEq (X := q.host) (Y := A)
          (typeJoint (p := q) Z)
          (seqJoint (fun j => pushOcc toA (familyS k j)) Z) := by
        have hpush :=
          P.scheme.diagram_preserved q.host A (r (e k)) trivial
            (typeJoint (p := q) Z) hjointμ hjointμ
        have heq : (fun i => (r (e k)).mapOcc (typeJoint (p := q) Z i)) =
            seqJoint (fun j => pushOcc toA (familyS k j)) Z := by
          funext i
          cases i with
          | inl j =>
            dsimp [SystemArrow.mapOcc, pushOcc, typeJoint, seqJoint, q, familyS]
            congr 1
            exact (infra_617_restr_comp A U A' U' toA toU (r (e k)) (himg' (e k))
              (d j).2).symm
          | inr b =>
            dsimp [SystemArrow.mapOcc, pushOcc, typeJoint, seqJoint]
            congr 1
            exact hfix b
        exact heq ▸ hpush
      exact P.scheme.diagram_trans A' A q.host
        (seqJoint (familyS k) Z0)
        (seqJoint (fun j => pushOcc toA (familyS k j)) Z)
        (typeJoint (p := q) Z)
        hMove (P.scheme.diagram_symm q.host A _ _ hR)
    let φ : Bad → Exc := fun ⟨k, hk⟩ =>
      ⟨e k, by
        by_contra hnone
        have hfix : ∀ b, (r (e k)).onVertex (Z b).1
            (incl.onVertex (Z b).1 (Z b).2) = (Z b).2 := fun b => by
          by_contra hne
          exact hnone ⟨b, hne⟩
        exact hk (hgood k hfix)⟩
    have hφ : Injective φ := by
      intro ⟨k, _⟩ ⟨k', _⟩ h
      exact Subtype.ext (e.injective (congrArg Subtype.val h))
    exact (mk_le_of_injective hφ).trans hExc
  exact infra_617_isFreeLift P σ hσ hνμ hrecν hσSuccν toA htoA toU htoU incl hincl
    incl' hincl' hsq d seq hidx hd hτν hκbound hmaj

end
end
end AEC
