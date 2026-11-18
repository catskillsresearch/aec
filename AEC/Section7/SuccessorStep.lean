module

public import AEC.Section7.Bookkeeping

@[expose] public section

/-!
# Matrix successor step of Proposition 7.8 (`infra_78_matrix_successor_step`)

Host relations between tuples over the same base (`infra_78_HostRel`: a permitted host arrow
carrying inclusions and values) preserve type-joint diagram equality
(`infra_78_hostRel_diag`) and hence tied freeness, in the source tuple
(`infra_78_tiedFree_host_source`, `infra_78_tiedFree_host_source'`) and in the target tuple
(`infra_78_tiedFree_host_target`). With these, a failing stage of the `ρ⁺` matrix is extended
by `infra_78_nonfree_extension_tied` followed by `infra_78_same_level_type_amalgam`:
`infra_78_matrix_successor_step` produces the next pair, the commuting square, invariant (5)
(via `infra_78_tiedFree_trans`), the free `b`-marginal over the step and the nonfree extension.
Non-failing stages take the identity step (handled in `infra_78_matrix_recursion`).
-/

universe u

open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}
section HostRel
variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}

/-- Two tuples over the same base related by a host arrow `h` carrying inclusions and values
(along `e`). -/
def infra_78_HostRel {B : P.scheme.Object μ hμ} (p₁ p₂ : TupleOver K oneVertexShape P.scheme hμ B)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem p₁.hν p₁.host)
      (P.scheme.asSystem p₂.hν p₂.host)) (e : p₁.idx ≃ p₂.idx) : Prop :=
  (∀ v x, h.onVertex v (p₁.incl.onVertex v x) = p₂.incl.onVertex v x) ∧
  ∀ k, p₂.val (e k) = pushOcc h (p₁.val k)

theorem infra_78_hostRel_typeJoint {B : P.scheme.Object μ hμ}
    {p₁ p₂ : TupleOver K oneVertexShape P.scheme hμ B}
    {h : SystemArrow K oneVertexShape (P.scheme.asSystem p₁.hν p₁.host)
      (P.scheme.asSystem p₂.hν p₂.host)} {e : p₁.idx ≃ p₂.idx}
    (hR : infra_78_HostRel p₁ p₂ h e) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) (t : p₂.idx ⊕ ι) :
    typeJoint (p := p₂) Z t =
      pushOcc h (typeJoint (p := p₁) Z ((Equiv.sumCongr e (Equiv.refl ι)).symm t)) := by
  rcases t with k | j
  · show p₂.val k = pushOcc h (p₁.val (e.symm k))
    rw [← hR.2, Equiv.apply_symm_apply]
  · show (⟨(Z j).1, p₂.incl.onVertex (Z j).1 (Z j).2⟩ : Occurrence K oneVertexShape _) =
      ⟨(Z j).1, h.onVertex (Z j).1 (p₁.incl.onVertex (Z j).1 (Z j).2)⟩
    rw [hR.1]

/-- Diagram equality of the type joint transfers along a host relation. -/
theorem infra_78_hostRel_diag {B : P.scheme.Object μ hμ}
    {p₁ p₂ : TupleOver K oneVertexShape P.scheme hμ B}
    {h : SystemArrow K oneVertexShape (P.scheme.asSystem p₁.hν p₁.host)
      (P.scheme.asSystem p₂.hν p₂.host)} (hh : P.scheme.permitted (X := p₁.host) (Y := p₂.host) h)
    {e : p₁.idx ≃ p₂.idx} (hR : infra_78_HostRel p₁ p₂ h e) {ι : Type u}
    (hb₁ : #(p₁.idx ⊕ ι) < p₁.ν) (hb₂ : #(p₁.idx ⊕ ι) < p₂.ν)
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    {ν' : Cardinal.{u}} {hν' : ν' ∈ P.eligible} (W : P.scheme.Object ν' hν')
    (ys : p₁.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν' W))
    (ys' : p₂.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν' W))
    (hys : ∀ t, ys' t = ys ((Equiv.sumCongr e (Equiv.refl ι)).symm t)) :
    P.scheme.DiagramEq (X := p₁.host) (Y := W) (typeJoint (p := p₁) Z) ys ↔
      P.scheme.DiagramEq (X := p₂.host) (Y := W) (typeJoint (p := p₂) Z) ys' := by
  have pres := P.scheme.diagram_preserved p₁.host p₂.host h hh (typeJoint (p := p₁) Z) hb₁ hb₂
  constructor
  · intro hd
    have h1 := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ pres) hd
    exact infra_612_dEq_transport h1 (Equiv.sumCongr e (Equiv.refl ι)).symm
      (fun t => infra_78_hostRel_typeJoint hR Z t) hys
  · intro hd
    have h1 := infra_612_dEq_transport hd (Equiv.sumCongr e (Equiv.refl ι))
      (xs' := fun a => pushOcc h (typeJoint (p := p₁) Z a)) (ys' := ys)
      (fun a => by rw [infra_78_hostRel_typeJoint hR Z, Equiv.symm_apply_apply])
      (fun a => by rw [hys, Equiv.symm_apply_apply])
    exact P.scheme.diagram_trans _ _ _ _ _ _ pres h1

theorem infra_78_sum_lt {α ι : Type u} (hμinf : ℵ₀ ≤ μ) (hα : #α < μ) (hι : #ι < μ) :
    #(α ⊕ ι) < μ := by
  rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
  exact add_lt_of_lt hμinf hα hι

/-- **Tied freeness is invariant under a host relation of the target.** -/
theorem infra_78_tiedFree_host_target {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    {r₁ r₂ : TupleOver K oneVertexShape P.scheme hμ B}
    {h : SystemArrow K oneVertexShape (P.scheme.asSystem r₁.hν r₁.host)
      (P.scheme.asSystem r₂.hν r₂.host)} (hh : P.scheme.permitted (X := r₁.host) (Y := r₂.host) h)
    {e : r₁.idx ≃ r₂.idx} (hR : infra_78_HostRel r₁ r₂ h e)
    (h₁ : r₁.ν = μ) (h₂ : r₂.ν = μ) (hq : #q.idx < μ) (e₁ : q.idx ≃ r₁.idx)
    (e₂ : q.idx ≃ r₂.idx) (he : ∀ k, e₂ k = e (e₁ k)) :
    IsTiedFree f q r₁ e₁ ↔ IsTiedFree f q r₂ e₂ := by
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ
  have key : ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) t,
      infra_612_anchored e₂ r₂.incl r₂.val Z t =
        pushOcc h (infra_612_anchored e₁ r₁.incl r₁.val Z t) := by
    intro ι Z t
    rcases t with k | j
    · show r₂.val (e₂ k) = _
      rw [he]
      exact hR.2 (e₁ k)
    · show (⟨(Z j).1, r₂.incl.onVertex (Z j).1 (Z j).2⟩ : Occurrence K oneVertexShape _) =
        ⟨(Z j).1, h.onVertex (Z j).1 (r₁.incl.onVertex (Z j).1 (Z j).2)⟩
      rw [hR.1]
  constructor
  · intro H seq ι Z Z0 hκ hι hιμ hmove
    have hd := H seq Z Z0 hκ hι hιμ hmove
    have hb := infra_78_sum_lt (α := q.idx) (ι := ι) hμinf hq hιμ
    have pres := P.scheme.diagram_preserved r₁.host r₂.host h hh
      (infra_612_anchored e₁ r₁.incl r₁.val Z) (hb.trans_eq h₁.symm) (hb.trans_eq h₂.symm)
    exact infra_73_diagramEq_of_eq (P.scheme.diagram_trans _ _ _ _ _ _ hd pres)
      (fun _ => rfl) (fun t => (key Z t).symm)
  · intro H seq ι Z Z0 hκ hι hιμ hmove
    have hd := H seq Z Z0 hκ hι hιμ hmove
    have hb := infra_78_sum_lt (α := q.idx) (ι := ι) hμinf hq hιμ
    have pres := P.scheme.diagram_preserved r₁.host r₂.host h hh
      (infra_612_anchored e₁ r₁.incl r₁.val Z) (hb.trans_eq h₁.symm) (hb.trans_eq h₂.symm)
    have hd' := infra_73_diagramEq_of_eq hd (fun _ => rfl) (fun t => key Z t)
    exact P.scheme.diagram_trans _ _ _ _ _ _ hd' (P.scheme.diagram_symm _ _ _ _ pres)

/-- Approximation sequence with test size `#ι`, reindexed along `e` (helper). -/
noncomputable def infra_78_seq_reindex_host {B : P.scheme.Object μ hμ}
    {p₁ p₂ : TupleOver K oneVertexShape P.scheme hμ B}
    {h : SystemArrow K oneVertexShape (P.scheme.asSystem p₁.hν p₁.host)
      (P.scheme.asSystem p₂.hν p₂.host)} (hh : P.scheme.permitted (X := p₁.host) (Y := p₂.host) h)
    {e : p₁.idx ≃ p₂.idx} (hR : infra_78_HostRel p₁ p₂ h e)
    (h₁ : p₁.ν = μ) (h₂ : p₂.ν = μ) (hp : #p₁.idx < μ)
    (seq : ApproximationSequence p₂) (τ : Cardinal.{u}) (hτ : τ ≤ seq.τ) (hτμ : τ < μ) :
    ApproximationSequence p₁ where
  τ := τ
  κIndex := seq.κIndex
  family := fun j k => seq.family j (e k)
  concat_bounded := by
    rw [Cardinal.mk_congr (Equiv.prodCongr (Equiv.refl seq.κIndex) e)]
    exact seq.concat_bounded
  few_exceptions := fun {β} W hW => by
    classical
    refine le_trans ?_ (seq.few_exceptions W (hW.trans hτ))
    refine Cardinal.mk_le_of_injective (f := fun j => ⟨j.1, fun hgood => j.2 ?_⟩)
      (by
        intro j₁ j₂ hj
        apply Subtype.ext
        have := congrArg Subtype.val hj
        exact this)
    have hb := infra_78_sum_lt (α := p₁.idx) (ι := β) (P.aleph0_le hμ) hp (hW.trans_lt hτμ)
    refine (infra_78_hostRel_diag hh hR (hb.trans_eq h₁.symm) (hb.trans_eq h₂.symm) W B
      (seqJoint (fun k => seq.family j.1 (e k)) W) (seqJoint (seq.family j.1) W) ?_).2 hgood
    rintro (k | c)
    · show seq.family j.1 k = seq.family j.1 (e (e.symm k))
      rw [Equiv.apply_symm_apply]
    · rfl

/-- Reindexed approximation sequence in the other direction (helper). -/
noncomputable def infra_78_seq_reindex_host' {B : P.scheme.Object μ hμ}
    {p₁ p₂ : TupleOver K oneVertexShape P.scheme hμ B}
    {h : SystemArrow K oneVertexShape (P.scheme.asSystem p₁.hν p₁.host)
      (P.scheme.asSystem p₂.hν p₂.host)} (hh : P.scheme.permitted (X := p₁.host) (Y := p₂.host) h)
    {e : p₁.idx ≃ p₂.idx} (hR : infra_78_HostRel p₁ p₂ h e)
    (h₁ : p₁.ν = μ) (h₂ : p₂.ν = μ) (hp : #p₁.idx < μ)
    (seq : ApproximationSequence p₁) (τ : Cardinal.{u}) (hτ : τ ≤ seq.τ) (hτμ : τ < μ) :
    ApproximationSequence p₂ where
  τ := τ
  κIndex := seq.κIndex
  family := fun j k => seq.family j (e.symm k)
  concat_bounded := by
    rw [← Cardinal.mk_congr (Equiv.prodCongr (Equiv.refl seq.κIndex) e)]
    exact seq.concat_bounded
  few_exceptions := fun {β} W hW => by
    classical
    refine le_trans ?_ (seq.few_exceptions W (hW.trans hτ))
    refine Cardinal.mk_le_of_injective (f := fun j => ⟨j.1, fun hgood => j.2 ?_⟩)
      (by
        intro j₁ j₂ hj
        apply Subtype.ext
        have := congrArg Subtype.val hj
        exact this)
    have hb := infra_78_sum_lt (α := p₁.idx) (ι := β) (P.aleph0_le hμ) hp (hW.trans_lt hτμ)
    refine (infra_78_hostRel_diag hh hR (hb.trans_eq h₁.symm) (hb.trans_eq h₂.symm) W B
      (seqJoint (seq.family j.1) W) (seqJoint (fun k => seq.family j.1 (e.symm k)) W) ?_).1 hgood
    rintro (k | c) <;> rfl

/-- **Tied freeness is invariant under a host relation of the source tuple** (forward). -/
theorem infra_78_tiedFree_host_source {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    {p₁ p₂ : TupleOver K oneVertexShape P.scheme hμ A}
    {h : SystemArrow K oneVertexShape (P.scheme.asSystem p₁.hν p₁.host)
      (P.scheme.asSystem p₂.hν p₂.host)} (hh : P.scheme.permitted (X := p₁.host) (Y := p₂.host) h)
    {e : p₁.idx ≃ p₂.idx} (hR : infra_78_HostRel p₁ p₂ h e)
    (h₁ : p₁.ν = μ) (h₂ : p₂.ν = μ) (hp : #p₁.idx < μ)
    (r : TupleOver K oneVertexShape P.scheme hμ B) (e₁ : p₁.idx ≃ r.idx)
    (e₂ : p₂.idx ≃ r.idx) (he : ∀ k, e₂ k = e₁ (e.symm k)) :
    IsTiedFree f p₁ r e₁ → IsTiedFree f p₂ r e₂ := by
  intro H seq ι Z Z0 hκ hι hιμ hmove
  let s1 := infra_78_seq_reindex_host hh hR h₁ h₂ hp seq #ι hι hιμ
  have hκ1 : s1.τ + ℵ₀ < #s1.κIndex := (add_le_add hι le_rfl).trans_lt hκ
  have hmove1 : infra_73_isMove f s1 Z Z0 := by
    intro i
    exact infra_612_dEq_transport (hmove i) (Equiv.sumCongr e (Equiv.refl ι))
      (by rintro (k | c) <;> rfl) (by rintro (k | c) <;> rfl)
  have hd := H s1 Z Z0 hκ1 le_rfl hιμ hmove1
  have hb := infra_78_sum_lt (α := p₁.idx) (ι := ι) (P.aleph0_le hμ) hp hιμ
  exact (infra_78_hostRel_diag hh hR (hb.trans_eq h₁.symm) (hb.trans_eq h₂.symm) Z0 r.host
    (infra_612_anchored e₁ r.incl r.val Z) (infra_612_anchored e₂ r.incl r.val Z)
    (by
      rintro (k | c)
      · show r.val (e₂ k) = r.val (e₁ (e.symm k))
        rw [he]
      · rfl)).1 hd

/-- **Tied freeness is invariant under a host relation of the source tuple** (backward). -/
theorem infra_78_tiedFree_host_source' {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    {p₁ p₂ : TupleOver K oneVertexShape P.scheme hμ A}
    {h : SystemArrow K oneVertexShape (P.scheme.asSystem p₁.hν p₁.host)
      (P.scheme.asSystem p₂.hν p₂.host)} (hh : P.scheme.permitted (X := p₁.host) (Y := p₂.host) h)
    {e : p₁.idx ≃ p₂.idx} (hR : infra_78_HostRel p₁ p₂ h e)
    (h₁ : p₁.ν = μ) (h₂ : p₂.ν = μ) (hp : #p₁.idx < μ)
    (r : TupleOver K oneVertexShape P.scheme hμ B) (e₂ : p₂.idx ≃ r.idx)
    (e₁ : p₁.idx ≃ r.idx) (he : ∀ k, e₁ k = e₂ (e k)) :
    IsTiedFree f p₂ r e₂ → IsTiedFree f p₁ r e₁ := by
  intro H seq ι Z Z0 hκ hι hιμ hmove
  let s2 := infra_78_seq_reindex_host' hh hR h₁ h₂ hp seq #ι hι hιμ
  have hκ2 : s2.τ + ℵ₀ < #s2.κIndex := (add_le_add hι le_rfl).trans_lt hκ
  have hmove2 : infra_73_isMove f s2 Z Z0 := by
    intro i
    exact infra_612_dEq_transport (hmove i) (Equiv.sumCongr e.symm (Equiv.refl ι))
      (by rintro (k | c) <;> rfl) (by rintro (k | c) <;> rfl)
  have hd := H s2 Z Z0 hκ2 le_rfl hιμ hmove2
  have hb := infra_78_sum_lt (α := p₁.idx) (ι := ι) (P.aleph0_le hμ) hp hιμ
  refine (infra_78_hostRel_diag hh hR (hb.trans_eq h₁.symm) (hb.trans_eq h₂.symm) Z0 r.host
    (infra_612_anchored e₁ r.incl r.val Z) (infra_612_anchored e₂ r.incl r.val Z)
    ?_).2 hd
  rintro (k | c)
  · show r.val (e₂ k) = r.val (e₁ (e.symm k))
    rw [he, Equiv.apply_symm_apply]
  · rfl

end HostRel

section Successor
variable (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
  {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ)

/-- **Prop 7.8 matrix successor step.** Given the stage-`i` pair `pair_i : X → Y` presented as
the tuple `q = tp(b,d/X)` (host `Y`, inclusion `pair_i`) with invariant (5) for the `b`-marginal
(tied free along `g0 : X₀ → X`) and a failing list (`¬ IsRelativelyIsolated q e`), there are a
permitted `stepX : X → X'`, a stage-`(i+1)` tuple `q'` over `X'` (host `Y'`, inclusion
`pair_{i+1}`) at level `μ` and a permitted `stepY : Y → Y'` such that the square commutes,
`stepY` carries the values of `q` to those of `q'`, invariant (5) holds at `X'` (along
`stepX ∘ g0`), the `b`-marginal is tied free over the step, and `tp(b,d/X')` is **not** tied free
over `X` (a nonfree extension). -/
theorem infra_78_matrix_successor_step
    {X X0 : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)}
    (q : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) X)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx) (hqν : q.ν = μ) (hidx : #q.idx ≤ σ)
    (g0 : SystemArrow K oneVertexShape (P.scheme.asSystem _ X0) (P.scheme.asSystem _ X))
    (hg0 : P.scheme.permitted (X := X0) (Y := X) g0)
    (hinv : IsTiedFree g0 ((q.marginal e).restrict g0 hg0) (q.marginal e) (Equiv.refl _))
    (hnot : ¬ IsRelativelyIsolated q e) :
    ∃ (X' : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
      (stepX : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ X'))
      (hstepX : P.scheme.permitted (X := X) (Y := X') stepX)
      (q' : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) X')
      (hq'idx : q'.idx = q.idx)
      (stepY : SystemArrow K oneVertexShape (P.scheme.asSystem q.hν q.host)
        (P.scheme.asSystem q'.hν q'.host)),
      q'.ν = μ ∧
      P.scheme.permitted (X := q.host) (Y := q'.host) stepY ∧
      (∀ v x, stepY.onVertex v (q.incl.onVertex v x) =
        q'.incl.onVertex v (stepX.onVertex v x)) ∧
      (∀ k, q'.val (Equiv.cast hq'idx.symm k) = pushOcc stepY (q.val k)) ∧
      IsTiedFree (SystemArrow.comp g0 stepX)
        ((q'.marginal ((Equiv.cast hq'idx).trans e)).restrict (SystemArrow.comp g0 stepX)
          (P.scheme.comp g0 stepX hg0 hstepX))
        (q'.marginal ((Equiv.cast hq'idx).trans e)) (Equiv.refl _) ∧
      IsTiedFree stepX ((q'.marginal ((Equiv.cast hq'idx).trans e)).restrict stepX hstepX)
        (q'.marginal ((Equiv.cast hq'idx).trans e)) (Equiv.refl _) ∧
      ¬ IsTiedFree stepX (q'.restrict stepX hstepX) q' (Equiv.refl _) := by
  classical
  have hσμ : σ < μ :=
    (Order.lt_succ_iff.2 (le_max_left σ (infra_73_h P σ))).trans_le hμT.2
  have hqlt : #q.idx < μ := hidx.trans_lt hσμ
  have hult : #uIdx < μ :=
    (Cardinal.mk_le_of_injective (f := fun u => e.symm (Sum.inl u))
      (fun a b h => Sum.inl_injective (e.symm.injective h))).trans_lt hqlt
  obtain ⟨B, fB, hfB, qB, eB, hqBν, hS, hmarg, hnf⟩ :=
    infra_78_nonfree_extension_tied P σ hσ hμT q e hqν hidx hnot
  obtain ⟨top, f1, f2, hf1, hf2, hcomm, hvals⟩ :=
    infra_78_same_level_type_amalgam q (qB.restrict fB hfB) eB (Equiv.refl _) hqν hqBν hS
  let q' : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) B :=
    ⟨μ, Tail.mem (infra_73_tail P σ hσ) hμT, top, SystemArrow.comp qB.incl f2, P.scheme.comp _ _ qB.incl_arrow hf2, q.idx,
      fun k => pushOcc f1 (q.val k)⟩
  have hsq : ∀ v x, f1.onVertex v (q.incl.onVertex v x) =
      q'.incl.onVertex v (fB.onVertex v x) := fun v x => congrFun (congrArg DFunLike.coe
        (hcomm v)) x
  refine ⟨B, fB, hfB, q', rfl, f1, rfl, hf1, hsq, fun k => rfl, ?_⟩
  simp only [Equiv.cast_refl]
  -- host relations
  have hR1 : infra_78_HostRel q (q'.restrict fB hfB) f1 (Equiv.refl _) :=
    ⟨hsq, fun k => rfl⟩
  have hRm : infra_78_HostRel (q.marginal e) ((q'.marginal e).restrict fB hfB) f1
      (Equiv.refl _) := ⟨hsq, fun k => rfl⟩
  have hR2 : infra_78_HostRel qB q' f2 eB.symm := by
    refine ⟨fun v x => rfl, fun i => ?_⟩
    have := hvals i
    exact this
  have hR2m : infra_78_HostRel (qB.marginal (eB.symm.trans e)) (q'.marginal e) f2
      (Equiv.refl _) := by
    refine ⟨fun v x => rfl, fun k => ?_⟩
    have := hvals (eB (e.symm (Sum.inl k)))
    rw [Equiv.symm_apply_apply] at this
    exact this
  have hmargq' : IsTiedFree fB ((q'.marginal e).restrict fB hfB) (q'.marginal e)
      (Equiv.refl _) := by
    have h3 := (infra_78_tiedFree_host_target fB (q.marginal e) hf2 hR2m hqBν rfl hult
      (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 hmarg
    exact infra_78_tiedFree_host_source fB hf1 hRm hqν rfl hult (q'.marginal e) _ _
      (fun _ => rfl) h3
  refine ⟨?_, hmargq', ?_⟩
  · refine infra_78_tiedFree_trans g0 hg0 fB hfB (q'.marginal e) ?_ hmargq'
    have h3 := (infra_78_tiedFree_host_target g0 ((q.marginal e).restrict g0 hg0) hf1 hRm
      hqν rfl hult (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 hinv
    have hR' : infra_78_HostRel ((q.marginal e).restrict g0 hg0)
        (((q'.marginal e).restrict fB hfB).restrict g0 hg0) f1 (Equiv.refl _) :=
      ⟨fun v x => hsq v (g0.onVertex v x), fun k => rfl⟩
    exact infra_78_tiedFree_host_source g0 hf1 hR' hqν rfl hult _ _ _ (fun _ => rfl) h3
  · intro H
    have h1 := infra_78_tiedFree_host_source' fB hf1 hR1 hqν rfl hqlt q' _ (Equiv.refl _)
      (fun _ => rfl) H
    have h2 := (infra_78_tiedFree_host_target fB q hf2 hR2 hqBν rfl hqlt eB (Equiv.refl _)
      (fun k => (eB.symm_apply_apply k).symm)).2 h1
    exact hnf h2

end Successor

end AEC
