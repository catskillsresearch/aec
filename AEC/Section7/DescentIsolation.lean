module

public import AEC.Section7.RelativeIsolationTransfer
public import AEC.Section7.AllDominated

@[expose] public section

/-!
# Lemma 7.6 — descent of relative isolation

Path A close for `SingleModelData`: same-level hosts `ν = μ`. If the free lift of `q_A`
is isolated relative to `u` by the push of a list from `A`, then `q_A` is isolated
relative to `u` by that list.

Mixed levels `ν < μ` are demoted. An arbitrary isolating fragment `W ⊆ B` is demoted
with `same_head`: free lifts agree on a push, and moving that agreement onto a fragment
that is not a push is the demoted glue. The proved case applies isolation directly to
`pushParams f Z`. The competitor is realized in the amalgam of the shared `u`-marginal,
so the marginal identification is the amalgam, not `infra_612_freeLift_unique`.
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-! ## Tail -/

def infra_76_tailSet (P : SingleModelData K) (σ : Cardinal.{u}) : Set Cardinal.{u} :=
  {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ σ ≤ μ}

theorem infra_76_tail (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    Tail P.eligible (infra_76_tailSet P σ) := by
  refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
  obtain ⟨μ, hle, hμ, hrec⟩ :=
    (infra_69_recursion_tail P hσ).2 (max κ (Order.succ σ))
  exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩

/-! ## Small reindexings -/

theorem infra_76_marginal_restrict
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    {uIdx cIdx : Type u} (e : qB.idx ≃ uIdx ⊕ cIdx) :
    (qB.marginal e).restrict f hf = (qB.restrict f hf).marginal e := by
  rfl

def infra_76_pushCopy
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    {idx : Type u}
    (v : idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) :
    idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
  fun j => ⟨(v j).1, f.onVertex (v j).1 (v j).2⟩

theorem infra_76_pushCopy_eq_pushParams
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) :
    infra_76_pushCopy f Z = pushParams f Z := rfl

/-! ## Free-lift diagrams -/

/-- Galois identification with the restriction is the joint diagram against the push of
any parameter list from `A`. -/
theorem infra_76_diag_push
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (_hf : P.scheme.permitted (X := A) (Y := B) f)
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    {qB : TupleOver K oneVertexShape P.scheme hμ B}
    (eB : q.idx ≃ qB.idx)
    (hExt : SameGaloisType q (qB.restrict f _hf) eB (Equiv.refl qB.idx))
    (hqν : q.ν = μ) (hBν : qB.ν = μ) (hidxμ : #q.idx < μ)
    {ι : Type u} (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hιμ : #ι < μ) :
    P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (typeJoint (p := q) Z0)
      (infra_612_anchored eB qB.incl qB.val (pushParams f Z0)) := by
  have hAligned :=
    infra_72_diagramEq_of_sameGalois (P := P) hExt Z0 hqν hBν
      ((Cardinal.mk_congr eB).symm.trans_lt hidxμ) hιμ
  have hρ : Injective (Sum.map eB (id : ι → ι)) :=
    Sum.map_injective.mpr ⟨eB.injective, injective_id⟩
  have hpre :=
    WorkingScheme.diagramEq_precomp (W := P.scheme) q.host (qB.restrict f _hf).host
      (alignJoint eB (typeJoint (p := q) Z0))
      (alignJoint (Equiv.refl qB.idx) (typeJoint (p := qB.restrict f _hf) Z0))
      (Sum.map eB id) hρ hAligned
  have hL :
      (fun j => alignJoint eB (typeJoint (p := q) Z0) (Sum.map eB id j)) =
        typeJoint (p := q) Z0 := by
    funext t; cases t with
    | inl i => simp only [Sum.map_inl, alignJoint, typeJoint, Equiv.symm_apply_apply]
    | inr j => simp only [Sum.map_inr, alignJoint, typeJoint, id_eq]
  have hR :
      (fun j => alignJoint (Equiv.refl qB.idx)
          (typeJoint (p := qB.restrict f _hf) Z0) (Sum.map eB id j)) =
        infra_612_anchored eB qB.incl qB.val (pushParams f Z0) := by
    funext t; cases t with
    | inl i =>
      simp only [Sum.map_inl, alignJoint, Equiv.refl_symm, Equiv.refl_apply, typeJoint,
        TupleOver.restrict, infra_612_anchored, pushParams]
    | inr j =>
      simp only [Sum.map_inr, alignJoint, Equiv.refl_symm, Equiv.refl_apply, typeJoint,
        TupleOver.restrict, SystemArrow.comp, infra_612_anchored, pushParams, id_eq]
      rfl
  rw [← hL, ← hR]
  exact hpre

/-- The pushed good copy joint with the original query agrees with the free lift's joint
with the push of the moved query. -/
theorem infra_76_copy_bridge
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    {qB : TupleOver K oneVertexShape P.scheme hμ B}
    (eB : q.idx ≃ qB.idx)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    (seq : ApproximationSequence q)
    (hτμ : seq.τ < μ) (hκ : seq.τ + ℵ₀ < #seq.κIndex)
    (hqν : q.ν = μ) (hBν : qB.ν = μ) (hidxμ : #q.idx < μ)
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hι : #ι ≤ seq.τ) (hιμ : #ι < μ) :
    ∃ (W0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) (i : seq.κIndex),
      P.scheme.DiagramEq (X := B) (Y := qB.host)
        (seqJoint (infra_76_pushCopy f (seq.family i)) Z)
        (infra_612_anchored eB qB.incl qB.val (pushParams f W0)) ∧
      (∀ k : seq.κIndex,
        P.scheme.DiagramEq (X := A) (Y := B)
          (seqJoint (seq.family k) W0)
          (seqJoint (infra_76_pushCopy f (seq.family k)) Z)) ∧
      P.scheme.DiagramEq (X := A) (Y := q.host)
        (seqJoint (seq.family i) W0) (typeJoint (p := q) W0) := by
  obtain ⟨W0, i, hmove, hgood, _⟩ := infra_610_moved_majority f hf seq hτμ hκ Z hι
  have h722 := infra_76_diag_push f hf eB hExt hqν hBν hidxμ W0 hιμ
  have hbridge : P.scheme.DiagramEq (X := B) (Y := q.host)
      (seqJoint (infra_76_pushCopy f (seq.family i)) Z) (typeJoint (p := q) W0) :=
    P.scheme.diagram_trans B A q.host _ _ _
      (P.scheme.diagram_symm A B _ _ (hmove i)) hgood
  refine ⟨W0, i, ?_, hmove, hgood⟩
  exact P.scheme.diagram_trans B q.host qB.host _ _ _ hbridge h722

/-- Level-`μ` amalgam of a same-level Galois identification, with the vertex maps explicit.
`infra_610_same_galois` rebuilds the witness from its diagram tests, so the host is an
object at `μ` rather than an arbitrary eligible level. -/
theorem infra_76_amalgam
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (e : p.idx ≃ q.idx)
    (h : SameGaloisType p (q.restrict f hf) e (Equiv.refl q.idx))
    (hpν : p.ν = μ) (hqν : q.ν = μ)
    (hidx : #p.idx ≤ σ) :
    ∃ (top : P.scheme.Object μ hμ)
      (fp : SystemArrow K oneVertexShape (P.scheme.asSystem p.hν p.host)
        (P.scheme.asSystem hμ top))
      (fq : SystemArrow K oneVertexShape (P.scheme.asSystem q.hν q.host)
        (P.scheme.asSystem hμ top)),
      (∀ v, (fp.onVertex v).comp (p.incl.onVertex v) =
        (fq.onVertex v).comp ((q.restrict f hf).incl.onVertex v)) ∧
      (∀ i, fp.onVertex (p.val (e.symm i)).1 (p.val (e.symm i)).2 =
        fq.onVertex (q.val i).1 (q.val i).2) := by
  classical
  have : CategoricalUnbounded K := P.D.categoricalUnbounded
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hL := infra_610_closed_level P σ hσ hμ hrec
  have hcA : Model.card A.model = μ := A.card
  have hc₀ : Model.card p.host.model = μ := by simpa [hpν] using p.host.card
  have hc₁ : Model.card q.host.model = μ := by simpa [hqν] using q.host.card
  let f₀ : Language.Embedding K.τ A.model.carrier p.host.model.carrier :=
    p.incl.onVertex PUnit.unit
  let f₁ : Language.Embedding K.τ A.model.carrier q.host.model.carrier :=
    (q.restrict f hf).incl.onVertex PUnit.unit
  let d₀ : q.idx → p.host.model.carrier :=
    fun i => p.host.val (p.val (e.symm i))
  let d₁ : q.idx → q.host.model.carrier :=
    fun i => q.host.val (q.val i)
  have hα : #q.idx ≤ σ := (Cardinal.mk_congr e).symm.trans_le hidx
  have htest : ∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (params : β → A.model.carrier) (_ : #(q.idx ⊕ β) ≤ ρ)
      (_ : P.D.t ρ ≤ Model.card p.host.model)
      (_ : P.D.t ρ ≤ Model.card q.host.model),
      P.D.same (α := q.idx ⊕ β) (by assumption) p.host.mem q.host.mem
        (by assumption) (by assumption)
        (Sum.elim (fun i => p.host.val (p.val (e.symm i)))
          (fun b => p.incl.onVertex PUnit.unit (params b)))
        (Sum.elim (fun i => q.host.val (q.val i))
          (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b))) := by
    intro β _hβ ρ0 hρinf hρμ params hjnt h0 h1
    exact SameGaloisType.to_sameD (P := P) h params ρ0 hρinf hjnt h0 h1
  obtain ⟨P₀, g₀, g₁, hP₀, hg₀, hg₁, hcP₀, hbase, hd⟩ :=
    hL.exists_tuple_amalgam hσ hσlt hα A.model p.host.model q.host.model f₀ f₁ d₀ d₁
      A.mem p.host.mem q.host.mem (p.incl.onVertex_strong PUnit.unit)
      ((q.restrict f hf).incl.onVertex_strong PUnit.unit) hcA hc₀ hc₁ htest
  let top : SMObject K μ := SMObject.ofModel P₀ hP₀ hcP₀
  let φ : P₀.carrier ≃[K.τ] top.model.carrier := SMObject.ofModelEquiv P₀ hP₀ hcP₀
  have hφ : K.Strong φ.toEmbedding := strong_of_equiv K φ hP₀
  let emb₁ : Language.Embedding K.τ p.host.model.carrier top.model.carrier :=
    φ.toEmbedding.comp g₀
  let emb₂ : Language.Embedding K.τ q.host.model.carrier top.model.carrier :=
    φ.toEmbedding.comp g₁
  have hs₁ : K.Strong emb₁ := K.strong_trans _ _ hg₀ hφ
  have hs₂ : K.Strong emb₂ := K.strong_trans _ _ hg₁ hφ
  let arr₁ : SystemArrow K oneVertexShape (P.scheme.asSystem p.hν p.host)
      (P.scheme.asSystem hμ top) :=
    oneVertexArrow emb₁ hs₁
  let arr₂ : SystemArrow K oneVertexShape (P.scheme.asSystem q.hν q.host)
      (P.scheme.asSystem hμ top) :=
    oneVertexArrow emb₂ hs₂
  refine ⟨top, arr₁, arr₂, ?_, ?_⟩
  · intro v
    refine DFunLike.ext _ _ fun x => ?_
    have hv : v = PUnit.unit := Subsingleton.elim _ _
    subst hv
    change emb₁ (p.incl.onVertex PUnit.unit x) =
      emb₂ ((q.restrict f hf).incl.onVertex PUnit.unit x)
    change φ (g₀ (f₀ x)) = φ (g₁ (f₁ x))
    exact congrArg (⇑φ) (hbase x)
  · intro i
    have hv : (p.val (e.symm i)).1 = PUnit.unit := Subsingleton.elim _ _
    have hw : (q.val i).1 = PUnit.unit := Subsingleton.elim _ _
    simp only [hv, hw, arr₁, arr₂, oneVertexArrow]
    change emb₁ (p.val (e.symm i)).2 = emb₂ (q.val i).2
    change φ (g₀ (d₀ i)) = φ (g₁ (d₁ i))
    exact congrArg (⇑φ) (hd i)


/-! ## Descent -/

theorem infra_76_marginal_of_free
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    {qB : TupleOver K oneVertexShape P.scheme hμ B}
    (eB : q.idx ≃ qB.idx)
    (h : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx) :
    SameGaloisType (q.marginal e)
      ((qB.marginal (eB.symm.trans e)).restrict f hf)
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro a
  have hix : (eB.symm.trans e).symm (Sum.inl a) = eB (e.symm (Sum.inl a)) := by
    simp [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
  have hv := hval (eB (e.symm (Sum.inl a)))
  rw [Equiv.symm_apply_apply] at hv
  simp only [Equiv.refl_apply, TupleOver.marginal, TupleOver.restrict] at hv ⊢
  exact hv

/-- Align the free-lift push diagram onto the `u ⊕ c` decomposition. -/
theorem infra_76_aligned_push
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    {qB : TupleOver K oneVertexShape P.scheme hμ B}
    (eB : q.idx ≃ qB.idx) {uIdx cIdx : Type u} (eA : q.idx ≃ uIdx ⊕ cIdx)
    {ι : Type u} (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hDE : P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (typeJoint (p := q) Z0)
      (infra_612_anchored eB qB.incl qB.val (pushParams f Z0))) :
    P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (alignJoint eA (typeJoint (p := q) Z0))
      (alignJoint (eB.symm.trans eA) (typeJoint (p := qB) (pushParams f Z0))) := by
  have hEqL : alignJoint eA (typeJoint (p := q) Z0) =
      fun t => typeJoint (p := q) Z0 (Sum.map eA.symm id t) := by
    funext t; cases t <;> rfl
  have hEqR : alignJoint (eB.symm.trans eA) (typeJoint (p := qB) (pushParams f Z0)) =
      fun t => infra_612_anchored eB qB.incl qB.val (pushParams f Z0)
        (Sum.map eA.symm id t) := by
    funext t; cases t with
    | inl i =>
      simp only [alignJoint, typeJoint, infra_612_anchored, Sum.map_inl,
        Equiv.symm_trans_apply, Equiv.trans_apply, Equiv.symm_symm]
    | inr j =>
      simp only [alignJoint, typeJoint, infra_612_anchored, Sum.map_inr, pushParams, id_eq]
  have hρ : Injective (Sum.map eA.symm (id : ι → ι)) :=
    Sum.map_injective.mpr ⟨eA.symm.injective, injective_id⟩
  have hpre := WorkingScheme.diagramEq_precomp (W := P.scheme) q.host qB.host
    (typeJoint (p := q) Z0)
    (infra_612_anchored eB qB.incl qB.val (pushParams f Z0))
    (Sum.map eA.symm id) hρ hDE
  simpa [hEqL, hEqR] using hpre

/-- At a recursion-closed level, relative isolation descends along a same-level free lift
when the isolating fragment of `q_B` is the push of a list from `A`. -/
theorem infra_76_descent
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (qA : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (e : qA.idx ≃ qB.idx) {uIdx cIdx : Type u}
    (eA : qA.idx ≃ uIdx ⊕ cIdx)
    (hqAν : qA.ν = μ) (hqBν : qB.ν = μ)
    (hidx : #qA.idx ≤ σ) (hidxμ : #qA.idx < μ)
    (hFree : IsFreeLift qA qB f hf e)
    (hMargFree : IsFreeLift (qA.marginal eA) (qB.marginal (e.symm.trans eA)) f hf
      (Equiv.refl uIdx))
    {wIdx : Type u}
    (Z0 : wIdx → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hIso : IsIsolatingFragment qB (e.symm.trans eA) (pushParams f Z0)) :
    IsRelativelyIsolated qA eA := by
  have hWμ : #wIdx < μ := hIso.1
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  let eb : qB.idx ≃ uIdx ⊕ cIdx := e.symm.trans eA
  refine IsRelativelyIsolated.of_fragment (Z := Z0) ⟨hWμ, ?_⟩
  intro qA' e' hqA'ν hMarg hDE
  have hidx'μ : #qA'.idx < μ := by
    have hcongr : #qA'.idx = #(uIdx ⊕ cIdx) := Cardinal.mk_congr e'
    have hA : #qA.idx = #(uIdx ⊕ cIdx) := Cardinal.mk_congr eA
    simpa [hcongr, hA] using hidxμ
  have hidxu : #uIdx ≤ σ := by
    have heq : #qA.idx = #(uIdx ⊕ cIdx) := Cardinal.mk_congr eA
    have hle : #uIdx ≤ #qA.idx := by
      rw [heq, mk_sum, lift_id]
      exact le_self_add
    exact hle.trans hidx
  let mA := qA.marginal eA
  let mA' := qA'.marginal e'
  let mB := qB.marginal eb
  have hLink : SameGaloisType mA' (mB.restrict f hf)
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
    have hsym : SameGaloisType mA' mA (Equiv.refl uIdx) (Equiv.refl uIdx) :=
      SameGaloisType.symm hMarg
    have hVia := SameGaloisType.trans_via (P := P) hsym hMargFree.1 σ hσ hσlt hidxu hrec
      hqA'ν hqAν hqBν
    have hEq : (Equiv.refl uIdx).trans (Equiv.refl uIdx).symm = Equiv.refl uIdx := by
      ext i; rfl
    exact hEq ▸ hVia
  obtain ⟨top, fp, fq, hcomm, hpoint⟩ :=
    infra_76_amalgam P σ hσ hμ hrec hσSucc f hf mA' mB (Equiv.refl uIdx) hLink
      hqA'ν hqBν hidxu
  let qStar : TupleOver K oneVertexShape P.scheme hμ B :=
    { ν := μ
      hν := hμ
      host := top
      incl := SystemArrow.comp qB.incl fq
      incl_arrow := trivial
      idx := qA'.idx
      val := fun i => ⟨(qA'.val i).1, fp.onVertex (qA'.val i).1 (qA'.val i).2⟩ }
  let eL : qA'.idx ≃ qStar.idx := Equiv.refl _
  have hExtStar : SameGaloisType qA' (qStar.restrict f hf) eL
      (Equiv.refl (qStar.restrict f hf).idx) := by
    refine ⟨μ, hμ, top, fp, SystemArrow.refl (P.scheme.asSystem hμ top), trivial, trivial, ?_, ?_⟩
    · intro v
      ext x
      have hc := congrFun (congrArg DFunLike.coe (hcomm v)) x
      simp only [mA', mB, TupleOver.marginal, TupleOver.restrict, qStar, SystemArrow.comp,
        SystemArrow.refl, Language.Embedding.comp_apply, Language.Embedding.refl_apply] at hc ⊢
      exact hc
    · intro i
      refine Sigma.ext (Subsingleton.elim _ _) ?_
      simp only [eL, Equiv.refl_symm, Equiv.refl_apply, qStar, TupleOver.restrict,
        SystemArrow.refl, Language.Embedding.refl_apply]
      exact HEq.rfl
  have hMargB : SameGaloisType mB (qStar.marginal e')
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
    refine ⟨μ, hμ, top, fq, SystemArrow.refl (P.scheme.asSystem hμ top), trivial, trivial, ?_, ?_⟩
    · intro v
      ext x
      change (fq.onVertex v) (qB.incl.onVertex v x) =
        (SystemArrow.refl (P.scheme.asSystem hμ top)).onVertex v
          ((SystemArrow.comp qB.incl fq).onVertex v x)
      rfl
    · intro u
      have hp := hpoint u
      simp only [Equiv.refl_symm, Equiv.refl_apply, TupleOver.marginal, mA', mB, qStar,
        SystemArrow.refl, Language.Embedding.refl_apply] at hp ⊢
      refine Sigma.ext (Subsingleton.elim _ _) ?_
      exact heq_of_eq hp.symm
  let qB' := qStar
  have hqB'ν : qB'.ν = μ := rfl
  have hAlign := infra_76_aligned_push f hf e eA Z0
      (infra_76_diag_push f hf e hFree.1 hqAν hqBν hidxμ Z0 hWμ)
  have hAlign' := infra_76_aligned_push f hf eL e' Z0
      (infra_76_diag_push f hf eL hExtStar hqA'ν hqB'ν hidx'μ Z0 hWμ)
  have hPush : P.scheme.DiagramEq (X := qB.host) (Y := qB'.host)
      (alignJoint eb (typeJoint (p := qB) (pushParams f Z0)))
      (alignJoint e' (typeJoint (p := qB') (pushParams f Z0))) :=
    P.scheme.diagram_trans qB.host qA.host qB'.host _ _ _
      (P.scheme.diagram_symm qA.host qB.host _ _ hAlign)
      (P.scheme.diagram_trans qA.host qA'.host qB'.host _ _ _ hDE hAlign')
  have hSGTb := hIso.2 qB' e' hqB'ν hMargB hPush
  have hRes : SameGaloisType (qB.restrict f hf) (qB'.restrict f hf)
      (e.symm.trans eA) e' := by
    rcases hSGTb with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, ?_, ?_⟩
    · intro v
      ext x
      simp only [TupleOver.restrict, SystemArrow.comp, Language.Embedding.comp_apply]
      exact DFunLike.congr_fun (hcomm v) (f.onVertex v x)
    · intro j
      simp only [TupleOver.restrict, Equiv.symm_trans_apply, Equiv.symm_symm,
        Equiv.trans_apply]
      exact hval j
  -- `q_A` — free lift — restriction — competitor restriction — free lift — `q_A'`.
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  let e1 : qB.idx ≃ uIdx ⊕ cIdx := e.symm.trans eA
  let e2 : qB'.idx ≃ uIdx ⊕ cIdx := e'
  have hResRefl : SameGaloisType (qB.restrict f hf) (qB'.restrict f hf)
      (Equiv.refl qB.idx) (e2.trans e1.symm) := by
    rcases hRes with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
    intro i
    have hv := hval ((e.symm.trans eA) i)
    have hreduce : (e.symm.trans eA).symm ((e.symm.trans eA) i) = i :=
      Equiv.symm_apply_apply _ _
    have hright : (e2.trans e1.symm).symm i = e'.symm ((e.symm.trans eA) i) := by
      simp [e1, e2, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.trans_apply,
        Equiv.apply_symm_apply]
    simp only [Equiv.refl_symm, TupleOver.restrict] at ⊢
    have hv' := hreduce ▸ hv
    have hv'' := hright.symm ▸ hv'
    exact hv''
  have hMid : SameGaloisType qA (qB'.restrict f hf)
      (e.trans (e2.trans e1.symm).symm) (Equiv.refl (qB'.restrict f hf).idx) :=
    SameGaloisType.trans_via (P := P) hFree.1 hResRefl σ hσ hσlt hidx hrec hqAν
      (by simpa [TupleOver.restrict] using hqBν)
      (by simpa [TupleOver.restrict] using hqB'ν)
  have hBack : SameGaloisType (qB'.restrict f hf) qA' (Equiv.refl qB'.idx) eL :=
    SameGaloisType.symm hExtStar
  have hJoin : SameGaloisType qA qA'
      ((e.trans (e2.trans e1.symm).symm).trans eL.symm) (Equiv.refl qA'.idx) :=
    SameGaloisType.trans_via (P := P) (t2 := qB'.restrict f hf) hMid hBack σ hσ hσlt hidx hrec
      hqAν rfl hqA'ν
  have hEqv : ((e.trans (e2.trans e1.symm).symm).trans eL.symm) = eA.trans e'.symm := by
    ext j
    simp only [eL, e1, e2, Equiv.refl_symm, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_symm, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    exact Equiv.refl_apply _
  rcases hEqv ▸ hJoin with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro k
  have hv := hval (e'.symm k)
  have hL : eA.symm (e' (e'.symm k)) = eA.symm k :=
    congrArg eA.symm (Equiv.apply_symm_apply e' k)
  have hR : (Equiv.refl qA'.idx).symm (e'.symm k) = e'.symm k := rfl
  exact hR ▸ hL ▸ hv

/-- **Lemma 7.6.** If the free lift of `q_A` is isolated relative to `u` by the push of a
list from `A`, then `q_A` is isolated relative to `u` by that list. An arbitrary fragment
`W ⊆ B` is demoted with `same_head`. -/
theorem infra_76_lemma (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B : P.scheme.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
        (hf : P.scheme.permitted (X := A) (Y := B) f)
        (qA : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
        (qB : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
        (e : qA.idx ≃ qB.idx) {uIdx cIdx : Type u}
        (eA : qA.idx ≃ uIdx ⊕ cIdx),
        qA.ν = μ → qB.ν = μ →
        #qA.idx ≤ σ → #qA.idx < μ →
        IsFreeLift qA qB f hf e →
        IsFreeLift (qA.marginal eA) (qB.marginal (e.symm.trans eA)) f hf
          (Equiv.refl uIdx) →
        (∃ (wIdx : Type u)
          (Z0 : wIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ A)),
          IsIsolatingFragment qB (e.symm.trans eA) (pushParams f Z0)) →
        IsRelativelyIsolated qA eA := by
  refine ⟨infra_76_tailSet P σ, infra_76_tail P σ hσ, ?_⟩
  intro μ hμ A B f hf qA qB e uIdx cIdx eA hqAν hqBν hidx hidxμ hFree hMarg hFrag
  obtain ⟨wIdx, Z0, hIso⟩ := hFrag
  exact infra_76_descent P σ hσ (Tail.mem (infra_76_tail P σ hσ) hμ) hμ.1 hμ.2
    f hf qA qB e eA hqAν hqBν hidx hidxμ hFree hMarg Z0 hIso

end
end
end AEC
