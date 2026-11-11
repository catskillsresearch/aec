module

public import AEC.Section6.FreeExtension
public import AEC.Section6.TupleOver
public import AEC.Section6.UniformApproximations
public import AEC.Section6.TestCardinal

@[expose] public section

/-!
# Theorem 6.10 (Stationary free extension) — English gloss

English clauses (from `FreeExtension.md`):

1. **Existence.** At a sufficiently closed level, every type `p = tp(v/A)` with `|v| ≤ σ` has a
   specified actual free lift `p_B` over `B` extending `p` along `A → B`.
2. **Approximation transport.** At bounded query and testing cost at the level of `A`, the free
   lift is computed by transporting sufficiently long approximation sequences in `A`.
3. **Scope.** At one level this includes every bounded query size; in mixed-level use, costs must
   stay below the level of `A`. (Corollary 6.7 enters for independence of section in the English
   proof of clause 3.)
4. **Definition.** An actual type over `B` is *free from* `A` when it is that free lift of its
   restriction to `A` (`IsFreeFrom` in `FreeExtension.lean`).

**Statement repair.** Same packaging as Lemma 6.9: `SingleModelData` at recursion-closed levels,
with same-level host `p.ν = μ`. `IsFreeLift` queries are bounded by the sequence arity `I.τ`
(English testing cost), not every `#ι < ν`. Cross-scheme transfer is not used.

**Infra.** Majority uniqueness/existence and `infra_610_move_query` (saturate + `diagram_iso`
pullback into `A`) are proved. Open tips: `infra_610_majority_prescription` (English Lem 6.4
path: chart of `B`, DiagramEq→`D.same` prescriptions, place, wrap as `TupleOver`) and
`infra_610_same_galois`. `infra_610_place_on_B` is the packaging wrapper of that pin.
-/

namespace AEC
section

universe u

open Cardinal FirstOrder

variable {K : AbstractElementaryClass.{u}}

/-! ## Majority from few exceptions -/

/-- The actual joint `typeJoint Z` is always a majority value of `seq` on `Z` of size
`≤ seq.τ`, by `few_exceptions` and `diagram_symm`. -/
theorem infra_610_majority_eq_type
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hι : #ι ≤ seq.τ) :
    IsMajorityValue seq Z p.hν p.host (typeJoint (p := p) Z) := by
  have hfew := seq.few_exceptions Z hι
  change
    # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Z) (typeJoint (p := p) Z)} ≤ #ι + aleph0
  let e : {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Z) (typeJoint (p := p) Z)} ≃
      {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := p.host) (Y := A)
          (typeJoint (p := p) Z) (seqJoint (seq.family i) Z)} :=
    ⟨fun ⟨i, hi⟩ => ⟨i, fun h => hi (P.scheme.diagram_symm _ _ _ _ h)⟩,
      fun ⟨i, hi⟩ => ⟨i, fun h => hi (P.scheme.diagram_symm _ _ _ _ h)⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Cardinal.mk_congr e]
  exact hfew

/-- If two lists are majority values of `seq` on the same `Z` and the index is longer than
`|Z| + ℵ₀`, they are `DiagramEq`. -/
theorem infra_610_majority_unique
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    {ν₁ ν₂ : Cardinal.{u}} {hν₁ : ν₁ ∈ P.eligible} {hν₂ : ν₂ ∈ P.eligible}
    {repr₁ : P.scheme.Object ν₁ hν₁} {repr₂ : P.scheme.Object ν₂ hν₂}
    (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν₁ repr₁))
    (ys : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν₂ repr₂))
    (hx : IsMajorityValue seq Z hν₁ repr₁ xs)
    (hy : IsMajorityValue seq Z hν₂ repr₂ ys)
    (hκ : #ι + aleph0 < #seq.κIndex) :
    P.scheme.DiagramEq (X := repr₁) (Y := repr₂) xs ys := by
  classical
  by_contra hne
  let Exc₁ : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := repr₁) (seqJoint (seq.family i) Z) xs}
  let Exc₂ : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := repr₂) (seqJoint (seq.family i) Z) ys}
  have hcover : (Set.univ : Set seq.κIndex) ⊆ Exc₁ ∪ Exc₂ := by
    intro i _
    by_cases hxs : P.scheme.DiagramEq (X := A) (Y := repr₁)
        (seqJoint (seq.family i) Z) xs
    · by_cases hys : P.scheme.DiagramEq (X := A) (Y := repr₂)
          (seqJoint (seq.family i) Z) ys
      · exact False.elim (hne (P.scheme.diagram_trans _ _ _ _ _ _
          (P.scheme.diagram_symm _ _ _ _ hxs) hys))
      · exact Or.inr hys
    · exact Or.inl hxs
  have hExc₁ : #Exc₁ ≤ #ι + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := repr₁) (seqJoint (seq.family i) Z) xs} ≤ _
    exact hx
  have hExc₂ : #Exc₂ ≤ #ι + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := repr₂) (seqJoint (seq.family i) Z) ys} ≤ _
    exact hy
  have hle : #seq.κIndex ≤ (#ι + aleph0) + (#ι + aleph0) := by
    have huni : #(Set.univ : Set seq.κIndex) = #seq.κIndex := mk_univ
    rw [← huni]
    exact (mk_le_mk_of_subset hcover).trans ((mk_union_le _ _).trans (add_le_add hExc₁ hExc₂))
  have hinfκ : aleph0 ≤ #seq.κIndex :=
    (le_add_self (a := aleph0) (b := #ι)).trans (le_of_lt hκ)
  have hsum : (#ι + aleph0) + (#ι + aleph0) < #seq.κIndex :=
    add_lt_of_lt hinfκ hκ hκ
  exact not_le_of_gt hsum hle

/-- Canonical majority witness: `typeJoint` itself. -/
theorem infra_610_exists_majority
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hι : #ι ≤ seq.τ) :
    ∃ (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem p.hν p.host)),
      IsMajorityValue seq Z p.hν p.host xs :=
  ⟨typeJoint (p := p) Z, infra_610_majority_eq_type seq Z hι⟩

/-! ## Pinned free-lift bridges -/

/-- Concatenation of the approximation sequence in `A`, pushed along `f : A → B`, keeps
`DiagramEq`. Immediate from `diagram_preserved`. -/
theorem infra_610_concat_push_diagramEq
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p) :
    P.scheme.DiagramEq (X := A) (Y := B)
      (fun ij : seq.κIndex × p.idx => seq.family ij.1 ij.2)
      (fun ij =>
        ⟨(seq.family ij.1 ij.2).1,
          f.onVertex (seq.family ij.1 ij.2).1 (seq.family ij.1 ij.2).2⟩) :=
  P.scheme.diagram_preserved A B f hf
    (fun ij : seq.κIndex × p.idx => seq.family ij.1 ij.2)
    seq.concat_bounded seq.concat_bounded

/-- Saturation moves a query `Z` from `B` into `A` over the concatenated sequence: saturate to
a μ-extension, then `diagram_iso` pulls the query half back into `A` while fixing the concat. -/
theorem infra_610_move_query
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence p)
    {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hι : #ι ≤ seq.τ) (hιμ : #ι < μ) :
    ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
      ∀ i : seq.κIndex,
        P.scheme.DiagramEq (X := A) (Y := B)
          (seqJoint (seq.family i) Z0)
          (seqJoint
            (fun j =>
              ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
            Z) := by
  classical
  let α : Type u := seq.κIndex × p.idx
  let xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun ij => seq.family ij.1 ij.2
  let base : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun ij => ⟨(xs ij).1, f.onVertex (xs ij).1 (xs ij).2⟩
  let ext : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    Sum.elim base Z
  have hα : #α < μ := seq.concat_bounded
  have hEqPush : P.scheme.DiagramEq (X := A) (Y := B) xs base :=
    infra_610_concat_push_diagramEq f hf seq
  obtain ⟨Z', g, zs, -, hzs, hzsEq⟩ :=
    (SingleModelData.isSaturated (P := P)).saturated
      A B xs base ext hα hιμ (fun i => rfl) hEqPush
  have hPushG : P.scheme.DiagramEq (X := A) (Y := Z') xs
      (fun ij => ⟨(xs ij).1, g.onVertex (xs ij).1 (xs ij).2⟩) :=
    P.scheme.diagram_preserved A Z' g trivial xs hα hα
  have hxsZs : (fun ij => ⟨(xs ij).1, g.onVertex (xs ij).1 (xs ij).2⟩) =
      fun ij => zs (Sum.inl ij) := by
    funext ij
    exact (hzs ij).symm
  have hEqZsInl : P.scheme.DiagramEq (X := A) (Y := Z') xs (fun ij => zs (Sum.inl ij)) := by
    rw [← hxsZs]
    exact hPushG
  obtain ⟨φ, hφiso, hφ⟩ :=
    (P.scheme.diagram_iso A Z' xs (fun ij => zs (Sum.inl ij)) hα).mp hEqZsInl
  have hφbij : Function.Bijective (φ.onVertex PUnit.unit) := hφiso PUnit.unit
  let eφ : A.model.carrier ≃ Z'.model.carrier := Equiv.ofBijective _ hφbij
  let Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun j => A.occ (eφ.symm (Z'.val (zs (Sum.inr j))))
  let jointA : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
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
  have hPushφ : P.scheme.DiagramEq (X := A) (Y := Z') jointA zs := by
    have hcard : #(α ⊕ ι) < μ := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact add_lt_of_lt (P.aleph0_le hμ) hα hιμ
    have h := P.scheme.diagram_preserved A Z' φ trivial jointA hcard hcard
    have heq : (fun t => ⟨(jointA t).1, φ.onVertex (jointA t).1 (jointA t).2⟩) = zs :=
      funext fun t => (hφjoint t).symm
    rwa [heq] at h
  have hJointExt : P.scheme.DiagramEq (X := A) (Y := B) jointA ext :=
    P.scheme.diagram_trans A Z' B jointA zs ext hPushφ hzsEq
  refine ⟨Z0, fun i => ?_⟩
  let ρ : p.idx ⊕ ι → α ⊕ ι := fun t =>
    match t with
    | Sum.inl j => Sum.inl (i, j)
    | Sum.inr k => Sum.inr k
  have hρ : Function.Injective ρ := by
    intro x y hxy
    cases x with
    | inl j =>
      cases y with
      | inl j' =>
        simp only [ρ] at hxy
        exact congrArg Sum.inl (Prod.ext_iff.mp (Sum.inl.inj hxy)).2
      | inr k =>
        simp [ρ] at hxy
    | inr k =>
      cases y with
      | inl j =>
        simp [ρ] at hxy
      | inr k' =>
        simp only [ρ] at hxy
        exact congrArg Sum.inr (Sum.inr.inj hxy)
  have hpre :=
    WorkingScheme.diagramEq_precomp (W := P.scheme) A B jointA ext ρ hρ hJointExt
  convert hpre using 1 <;> funext t <;> cases t <;> rfl

/-! ## Place majority on `B` (plan `place_majority_on_b`)

English path: well-ordered chart of `B` → majority prescriptions via `move_query` →
`proposition_4_9` / `lemma_6_4` → wrap as `TupleOver` over `B`. The DiagramEq→`D.same`
prescription glue, the eligible-card wrap of `E(J)`, and the majority clause are one pin. -/

/-- **Pinned.** English Lem 6.4 free-lift placement on a chart of `B`.

1. Well-ordered chart `eB : E(I) ≃ B` (`#I = μ`), not a padded present.
2. `χ` via `exists_power_fixed_below` with `max seq.τ (ls K + σ) < χ < μ` and `χ ^ σ = χ`.
3. Majority prescriptions: push params to `B`, `infra_610_move_query` → `Z0`, good index
   outside `#β + ℵ₀` exceptions; `q X = Sum.elim (chart∘f∘vᵢ) X` (`hnat` / `hcoh` via
   majority uniqueness + `diagramEq_iff_sameD`).
4. `lemma_6_4` / `proposition_4_9` → `z` in an order enlargement `E(J)`.
5. Wrap as `TupleOver` over `B`; majority clause by move_query + uniqueness vs placed joints.

**Why pinned.** (i) Scheme `DiagramEq` majority classes → presentation `D.same` at every
`#β ≤ χ` (plan takes `χ > seq.τ`, while `few_exceptions` only covers `#ι ≤ seq.τ`).
(ii) `E(J)` typically has card a categoricity size `≥ μ` not necessarily in `P.eligible`, so
it is not an `SMObject` host without an extra hull/push. -/
theorem infra_610_majority_prescription
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B,
      ∃ e : p.idx ≃ q.idx,
        ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
          #ι ≤ seq.τ →
          ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
            IsMajorityValue seq Z0 q.hν q.host
              (typeJoint (p := q) Z ∘ Sum.map e id) := by
  sorry

/-- Packaging of `infra_610_majority_prescription` (English Lem 6.4 placement on a chart of
`B`). -/
theorem infra_610_place_on_B
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hidxμ : #p.idx < μ)
    (seq : ApproximationSequence p) (hτμ : seq.τ < μ) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B,
      ∃ e : p.idx ≃ q.idx,
        ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
          #ι ≤ seq.τ →
          ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
            IsMajorityValue seq Z0 q.hν q.host
              (typeJoint (p := q) Z ∘ Sum.map e id) :=
  infra_610_majority_prescription P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hτμ

/-- **Pinned.** Scheme-level `SameGaloisType` of `p` with `q.restrict f` on `P.scheme`.
English uses uniqueness of the actual type from testing at `τ ≥ g(σ)` (Theorem 6.6 /
`ClosedLevel.exists_tuple_amalgam`). Needs `PlacedTester` packaging beyond bare
`{D.t, g}`-eligibility, and test agreement from the majority placement. -/
theorem infra_610_same_galois
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (e : p.idx ≃ q.idx)
    (hνμ : p.ν = μ) :
    SameGaloisType p (q.restrict f hf) e (Equiv.refl q.idx) := by
  sorry

/-! ## Existence -/

/-- English clause 1: existence of a free lift along a permitted arrow of `P.scheme`.
Packaging matches Lemma 6.9 (`p.ν = μ`, recursion-closed level, code arity `c(σ)`).
Open tips are `infra_610_majority_prescription` / `infra_610_same_galois`. -/
theorem stationary_free_extension_exists
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσμ : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hidxμ : #p.idx < μ) :
    ∃ q : TupleOver K oneVertexShape P.scheme hμ B, ∃ e : p.idx ≃ q.idx,
      IsFreeLift p q f hf e := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσμ
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let τ : Cardinal.{u} := testCardinal b P.g σ
  let κ : Cardinal.{u} := Order.succ τ
  have hτ : ℵ₀ ≤ τ := by
    change ℵ₀ ≤ (2 : Cardinal.{u}) ^ (P.g σ + b + σ + aleph0)
    exact le_trans (cantor aleph0).le
      (power_le_power_left two_ne_zero
        (le_add_self : aleph0 ≤ (P.g σ + b + σ) + aleph0))
  have hexp : P.g σ + b + σ + aleph0 < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    have hb : b < μ := max_lt (P.ls_lt hμ) (P.aleph0_lt hμ)
    have h1 : P.g σ + b < μ := add_lt_of_lt (P.aleph0_le hμ) hg hb
    have h2 : P.g σ + b + σ < μ := add_lt_of_lt (P.aleph0_le hμ) h1 hσlt
    exact add_lt_of_lt (P.aleph0_le hμ) h2 (P.aleph0_lt hμ)
  have hτμ : τ < μ :=
    hμ.1.working.strongLimit.isStrongPrelimit hexp
  have hκ : ℵ₀ ≤ κ := hτ.trans (Order.le_succ _)
  have hκμ : κ < μ :=
    (Order.succ_le_of_lt (cantor τ)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hτμ)
  have hprod : κ * #p.idx < μ := by
    have hmul : κ * #p.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    have hκσ : κ * σ = κ := by
      refine mul_eq_left hκ ?_ (aleph0_pos.trans_le hσ).ne'
      have hστ : σ < τ := by
        change σ < (2 : Cardinal.{u}) ^ (P.g σ + b + σ + aleph0)
        exact lt_of_lt_of_le (cantor σ)
          (power_le_power_left two_ne_zero
            (le_trans (le_add_self : σ ≤ (P.g σ + b) + σ)
              (le_self_add : (P.g σ + b) + σ ≤ ((P.g σ + b) + σ) + aleph0)))
      exact hστ.le.trans (Order.le_succ _)
    exact hmul.trans_lt (by rw [hκσ]; exact hκμ)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ := by
    have hβ : max (max σ τ) (max (ls K) ℵ₀) < μ :=
      max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
    exact hrec.2 _ hβ
  obtain ⟨seq, hseqτ, _⟩ :=
    P.exists_approximationSequence hμ A p hνμ σ τ κ hσ hσlt hidx hτ hτμ hκ hκμ hprod hclosed
  have hseqτμ : seq.τ < μ := hseqτ ▸ hτμ
  obtain ⟨q, e, hmaj⟩ :=
    infra_610_place_on_B P σ hσ hμ hrec hσμ f hf p hνμ hidx hidxμ seq hseqτμ
  refine ⟨q, e, ⟨infra_610_same_galois f hf p q e hνμ, ⟨seq, ?_⟩⟩⟩
  intro ι Z hι
  obtain ⟨Z0, hZ0⟩ := hmaj Z hι
  refine ⟨Z0, typeJoint (p := q) Z ∘ Sum.map e id, hZ0, ?_⟩
  have hre : reindexJoint e (typeJoint (p := q) Z ∘ Sum.map e id) =
      typeJoint (p := q) Z := by
    funext t
    cases t with
    | inl i =>
      simp [reindexJoint, Function.comp, Sum.map, Equiv.symm_apply_apply]
    | inr j =>
      rfl
  rw [hre]
  exact P.scheme.diagram_refl q.host _

end
end AEC
