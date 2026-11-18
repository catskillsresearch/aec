module

public import AEC.Section7.RelativeIsolationTransfer
public import AEC.Section6.ApproxRetractionProof
public import AEC.Section6.StationaryFreeExtension

@[expose] public section

/-!
# Proposition 7.3 — isolation bound

Path A close for `SingleModelData`: scheme-only `h(σ)` and the dichotomy — isolating
fragment of size `≤ h(σ)`, or a same-level extension with free `u`-marginal and
`¬ IsTiedFree`. At recursion-closed levels the untied `IsFreeLift` majority witness does
not mention the tuple values (`infra_73_ext_isFreeLift`); English “≠ free lift” is the
tied clause. `infra_73_alt2` builds alt 2 from a family-competitor (stand-in for the
English RetWell / free-block transport).

Tied freeness (English Lem 7.2.2): `infra_73_tied_of_isolated` — if `q` is relatively
isolated and the extension's `u`-marginal is tied free (`hMargTied`), the joint is tied free.
The untied `IsFreeLift` marginal is not enough (it follows from `hExt` alone, and a realized
forking extension refutes that form). Tied-free extensions are unique
(`infra_73_tied_unique`), which gives over-`B` isolation `infra_72_over_B_isolation`.

Uniform shrink `infra_73_uniform_of_isolated` is proved conditional on `hFreeTied`: the
alt-2 extensions must have tied-free `u`-marginal, which `infra_73_alt2` does not
provide. `AltTwoTied.lean` builds such an extension from the English block restriction
(`infra_73_alt2_tied`, `infra_73_uniform_of_block`; board: `infra_73_alt2_tied_marginal`
← `infra_73_block_restriction`).
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-! ## Bound and tail -/

/-- Testing / approximation cardinal used to size the uniform fragment. -/
noncomputable def infra_73_chi (P : SingleModelData K) (σ : Cardinal.{u}) : Cardinal.{u} :=
  max (testCardinal (max (ls K) ℵ₀) P.g σ) (P.g σ + max (ls K) ℵ₀)

/-- `h(σ)` dominates the approximation-family enumeration used as `Z₀`. -/
noncomputable def infra_73_h (P : SingleModelData K) (σ : Cardinal.{u}) : Cardinal.{u} :=
  Order.succ (max σ (infra_73_chi P σ))

def infra_73_tailSet (P : SingleModelData K) (σ : Cardinal.{u}) : Set Cardinal.{u} :=
  {μ | μ ∈ recursionClosedLevels P σ ∧ Order.succ (max σ (infra_73_h P σ)) ≤ μ}

theorem infra_73_tail (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    Tail P.eligible (infra_73_tailSet P σ) := by
  refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
  obtain ⟨μ, hle, hμ, hrec⟩ :=
    (infra_69_recursion_tail P hσ).2 (max κ (Order.succ (max σ (infra_73_h P σ))))
  exact ⟨μ, (le_max_left _ _).trans hle,
    ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩

theorem infra_73_tail_rec {P : SingleModelData K} {σ μ : Cardinal.{u}}
    (hμ : μ ∈ infra_73_tailSet P σ) : μ ∈ recursionClosedLevels P σ :=
  hμ.1

theorem infra_73_tail_succ {P : SingleModelData K} {σ μ : Cardinal.{u}}
    (hμ : μ ∈ infra_73_tailSet P σ) : Order.succ σ ≤ μ := by
  have h : Order.succ (max σ (infra_73_h P σ)) ≤ μ := hμ.2
  exact (Order.succ_le_succ (le_max_left σ (infra_73_h P σ))).trans h

theorem infra_73_h_lt {P : SingleModelData K} {σ μ : Cardinal.{u}}
    (_hμel : μ ∈ P.eligible) (hμ : μ ∈ infra_73_tailSet P σ) :
    infra_73_h P σ < μ := by
  have hs : Order.succ (infra_73_h P σ) ≤ μ :=
    (Order.succ_le_succ (le_max_right σ (infra_73_h P σ))).trans hμ.2
  exact (Order.lt_succ (infra_73_h P σ)).trans_le hs

/-! ## Tied freeness -/

/-- A parameter list `Z` in `B` is a sequence-move of `Z₀` in `A` when every copy of the
approximation family keeps its diagram. -/
def infra_73_isMove
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) : Prop :=
  ∀ i : seq.κIndex,
    P.scheme.DiagramEq (X := A) (Y := B)
      (seqJoint (seq.family i) Z0)
      (seqJoint
        (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
        Z)

/-- English free evaluation: on a long approximation sequence, every small sequence-move
`Z` of `Z₀` is answered by `q` on `Z₀`. The moved list `pushParams f Z₀` is what an
extension automatically matches; the clause here is the original query `Z`.

`SameDiagramAt` does not concatenate. A `DiagramEq` is one strong map of the hulls
matching that list (`SameStrongClass`), and `preserves_atomic` sees equalities only
inside the list. Separate equalities of a head and a tail therefore do not yield the
joint, so `DiagramEq (Sum.elim xs xs') (Sum.elim ys ys')` is not available from
`DiagramEq xs ys` and `DiagramEq xs' ys'`. The gap in `IsTiedFree` is exactly that
joint: `hExt` matches `typeJoint q Z₀` with `anchored (pushParams f Z₀)`, while a
sequence-move only identifies the parameter lists `Z₀` and `Z`. -/
def IsTiedFree
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx) : Prop :=
  ∀ (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
    seq.τ + ℵ₀ < #(seq.κIndex) →
    #ι ≤ seq.τ → #ι < μ →
    infra_73_isMove f seq Z Z0 →
    P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (typeJoint (p := q) Z0)
      (infra_612_anchored eB qB.incl qB.val Z)

/-! ## Extension yields untied freeness -/

set_option maxHeartbeats 800000 in
theorem infra_73_ext_isFreeLift
    {P : SingleModelData K} (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    (hqν : q.ν = μ) (hBν : qB.ν = μ)
    (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx)) :
    IsFreeLift q qB f hf eB := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  let b : Cardinal.{u} := max (ls K) ℵ₀
  let τ : Cardinal.{u} := max (max (P.g σ + ls K) (max (ls K) ℵ₀)) (max (testCardinal b P.g σ) ℵ₀)
  have hτ : ℵ₀ ≤ τ := (le_max_right _ _).trans (le_max_right _ _)
  have hτμ : τ < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    have hgls : P.g σ + ls K < μ := add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ)
    have hb : b < μ := max_lt (P.ls_lt hμ) (P.aleph0_lt hμ)
    have hexp : P.g σ + b + σ + ℵ₀ < μ := by
      have h1 : P.g σ + b < μ := add_lt_of_lt (P.aleph0_le hμ) hg hb
      have h2 : P.g σ + b + σ < μ := add_lt_of_lt (P.aleph0_le hμ) h1 hσlt
      exact add_lt_of_lt (P.aleph0_le hμ) h2 (P.aleph0_lt hμ)
    have htest : testCardinal b P.g σ < μ :=
      hμ.1.working.strongLimit.isStrongPrelimit hexp
    exact max_lt (max_lt hgls hb) (max_lt htest (P.aleph0_lt hμ))
  let κ : Cardinal.{u} := Order.succ τ
  have hκ : ℵ₀ ≤ κ := hτ.trans (Order.le_succ _)
  have hκμ : κ < μ :=
    (Order.succ_le_of_lt (cantor τ)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hτμ)
  have hprod : κ * #q.idx < μ := by
    have hmul : κ * #q.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    have hκσ : κ * σ = κ := by
      refine mul_eq_left hκ ?_ (aleph0_pos.trans_le hσ).ne'
      have hστ : σ < τ :=
        (lt_of_lt_of_le (cantor σ)
          (power_le_power_left two_ne_zero
            (le_trans (le_add_self : σ ≤ (P.g σ + b) + σ)
              (le_self_add : (P.g σ + b) + σ ≤ ((P.g σ + b) + σ) + ℵ₀)))).trans_le
          ((le_max_left _ _).trans (le_max_right _ _))
      exact hστ.le.trans (Order.le_succ _)
    exact hmul.trans_lt (by rw [hκσ]; exact hκμ)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ := by
    have hβ : max (max σ τ) (max (ls K) ℵ₀) < μ :=
      max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
    exact hrec.2 _ hβ
  obtain ⟨seq, hseqτ, _⟩ :=
    P.exists_approximationSequence hμ A q hqν σ τ κ hσ hσlt hidx hτ hτμ hκ hκμ hprod hclosed
  exact infra_722_isFreeLift_of_ext f hf q qB eB hqν hBν hidxμ hExt seq (hseqτ ▸ hτμ)

/-! ## Competitor from a non-isolating fragment -/

theorem infra_73_competitor
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hι : #ι < μ) (hnot : ¬ IsIsolatingFragment q e Z) :
    ∃ (q' : TupleOver K oneVertexShape P.scheme hμ A) (e' : q'.idx ≃ uIdx ⊕ cIdx),
      q'.ν = μ ∧
      SameGaloisType (q.marginal e) (q'.marginal e') (Equiv.refl uIdx) (Equiv.refl uIdx) ∧
      P.scheme.DiagramEq (X := q.host) (Y := q'.host)
        (alignJoint e (typeJoint (p := q) Z))
        (alignJoint e' (typeJoint (p := q') Z)) ∧
      ¬ SameGaloisType q q' e e' := by
  classical
  have hforall : ¬ ∀ (q' : TupleOver K oneVertexShape P.scheme hμ A)
      (e' : q'.idx ≃ uIdx ⊕ cIdx),
        q'.ν = μ →
        SameGaloisType (q.marginal e) (q'.marginal e') (Equiv.refl uIdx) (Equiv.refl uIdx) →
        P.scheme.DiagramEq (X := q.host) (Y := q'.host)
          (alignJoint e (typeJoint (p := q) Z))
          (alignJoint e' (typeJoint (p := q') Z)) →
        SameGaloisType q q' e e' := by
    intro hall
    exact hnot ⟨hι, hall⟩
  obtain ⟨q', hq'⟩ := not_forall.mp hforall
  obtain ⟨e', he'⟩ := not_forall.mp hq'
  obtain ⟨hν, he'⟩ := not_imp.mp he'
  obtain ⟨hm, he'⟩ := not_imp.mp he'
  obtain ⟨hde, hneq⟩ := not_imp.mp he'
  exact ⟨q', e', hν, hm, hde, hneq⟩

/-! ## Approximation family as a uniform fragment -/

theorem infra_73_sequence_rec
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ) :
    ∃ seq : ApproximationSequence q,
      seq.τ = max σ (infra_73_chi P σ) ∧
      #(seq.κIndex) = infra_73_h P σ ∧
      P.g σ + ls K ≤ seq.τ ∧
      seq.τ + ℵ₀ < #(seq.κIndex) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  let τ : Cardinal.{u} := max σ (infra_73_chi P σ)
  have hτ : ℵ₀ ≤ τ := le_trans hσ (le_max_left _ _)
  have hτμ : τ < μ := by
    have hχμ : infra_73_chi P σ < μ := by
      let b : Cardinal.{u} := max (ls K) ℵ₀
      have hg : P.g σ < μ :=
        (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
      have hb : b < μ := max_lt (P.ls_lt hμ) (P.aleph0_lt hμ)
      have hexp : P.g σ + b + σ + ℵ₀ < μ := by
        have h1 : P.g σ + b < μ := add_lt_of_lt (P.aleph0_le hμ) hg hb
        have h2 : P.g σ + b + σ < μ := add_lt_of_lt (P.aleph0_le hμ) h1 hσlt
        exact add_lt_of_lt (P.aleph0_le hμ) h2 (P.aleph0_lt hμ)
      have htest : testCardinal b P.g σ < μ :=
        hμ.1.working.strongLimit.isStrongPrelimit hexp
      have hgls : P.g σ + max (ls K) ℵ₀ < μ := add_lt_of_lt (P.aleph0_le hμ) hg hb
      exact max_lt htest hgls
    exact max_lt hσlt hχμ
  let κ : Cardinal.{u} := infra_73_h P σ
  have hκeq : κ = Order.succ τ := rfl
  have hκ : ℵ₀ ≤ κ := hτ.trans (Order.le_succ _)
  have hκμ : κ < μ := by
    rw [hκeq]
    exact (Order.succ_le_of_lt (cantor τ)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hτμ)
  have hprod : κ * #q.idx < μ := by
    have hmul : κ * #q.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    have hκσ : κ * σ = κ := by
      have hσle : σ ≤ κ := by
        change σ ≤ Order.succ (max σ (infra_73_chi P σ))
        exact (le_max_left _ _).trans (Order.le_succ _)
      exact Cardinal.mul_eq_left hκ hσle (aleph0_pos.trans_le hσ).ne'
    exact hmul.trans_lt (by rw [hκσ]; exact hκμ)
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) ℵ₀)
      (max (max σ τ) (max (ls K) ℵ₀)) μ := by
    have hβ : max (max σ τ) (max (ls K) ℵ₀) < μ :=
      max_lt (max_lt hσlt hτμ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
    exact hrec.2 _ hβ
  obtain ⟨seq, hseqτ, hseqκ⟩ :=
    P.exists_approximationSequence hμ A q hqν σ τ κ hσ hσlt hidx hτ hτμ hκ hκμ hprod hclosed
  refine ⟨seq, hseqτ, hseqκ, ?_, ?_⟩
  · rw [hseqτ]
    calc
      P.g σ + ls K ≤ P.g σ + max (ls K) ℵ₀ :=
        add_le_add_right (le_max_left (ls K) ℵ₀) (P.g σ)
      _ ≤ infra_73_chi P σ := le_max_right _ _
      _ ≤ max σ (infra_73_chi P σ) := le_max_right _ _
  · rw [hseqκ, hseqτ, hκeq, add_eq_left hτ hτ]
    exact Order.lt_succ τ

theorem infra_73_sequence
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible) (hμT : μ ∈ infra_73_tailSet P σ)
    {A : P.scheme.Object μ hμ}
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ) :
    ∃ seq : ApproximationSequence q,
      seq.τ = max σ (infra_73_chi P σ) ∧
      #(seq.κIndex) = infra_73_h P σ ∧
      P.g σ + ls K ≤ seq.τ ∧
      seq.τ + ℵ₀ < #(seq.κIndex) :=
  infra_73_sequence_rec P σ hσ hμ (infra_73_tail_rec hμT) (infra_73_tail_succ hμT) q hqν hidx

/-- The family enumeration, used as the uniform candidate fragment. -/
def infra_73_family
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q) :
    seq.κIndex × q.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
  fun ij => seq.family ij.1 ij.2

theorem infra_73_family_card
    {P : SingleModelData K} {σ μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q) (hσ : ℵ₀ ≤ σ) (hidx : #q.idx ≤ σ)
    (hκ : #(seq.κIndex) = infra_73_h P σ) :
    #(seq.κIndex × q.idx) ≤ infra_73_h P σ := by
  rw [mk_prod, lift_id, lift_id, hκ]
  rcases eq_or_ne (#q.idx) 0 with h0 | h0
  · simp [h0, mul_zero]
  · have hκle : ℵ₀ ≤ infra_73_h P σ :=
      hσ.trans ((le_max_left σ (infra_73_chi P σ)).trans (Order.le_succ _))
    have hidxle : #q.idx ≤ infra_73_h P σ :=
      hidx.trans ((le_max_left σ (infra_73_chi P σ)).trans (Order.le_succ _))
    exact (Cardinal.mul_eq_left hκle hidxle h0).le

/-! ## Tests separate distinct Galois types -/

theorem infra_73_sgt_restrict_refl
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hμ A}
    (e : t1.idx ≃ t2.idx)
    (h : SameGaloisType t1
      (t2.restrict (SystemArrow.refl (P.scheme.asSystem hμ A)) trivial) e (Equiv.refl t2.idx)) :
    SameGaloisType t1 t2 e (Equiv.refl t2.idx) := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, ?_, ?_⟩
  · intro v
    ext x
    have hc := DFunLike.congr_fun (hcomm v) x
    simp only [TupleOver.restrict, SystemArrow.comp, SystemArrow.refl,
      Language.Embedding.comp_apply, Language.Embedding.refl_apply] at hc
    exact hc
  · intro i
    have hv := hval i
    simp only [TupleOver.restrict, Equiv.refl_apply] at hv
    exact hv

theorem infra_73_sgt_common
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {q q' : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    (e : q.idx ≃ ι) (e' : q'.idx ≃ ι)
    (h : SameGaloisType q q' (e.trans e'.symm) (Equiv.refl q'.idx)) :
    SameGaloisType q q' e e' := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro k
  have hv := hval (e'.symm k)
  have hidx : (e.trans e'.symm).symm (e'.symm k) = e.symm k := by
    rw [Equiv.symm_trans_apply, Equiv.symm_symm, e'.apply_symm_apply]
  rw [hidx, Equiv.refl_symm, Equiv.refl_apply] at hv
  exact hv

set_option maxHeartbeats 800000 in
theorem infra_73_differing_test
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (q q' : TupleOver K oneVertexShape P.scheme hμ A) {ι : Type u}
    (e : q.idx ≃ ι) (e' : q'.idx ≃ ι)
    (hqν : q.ν = μ) (hq'ν : q'.ν = μ)
    (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (hneq : ¬ SameGaloisType q q' e e') :
    ∃ (β : Type u) (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      #β ≤ P.g σ + ls K ∧
      ¬ P.scheme.DiagramEq (X := q.host) (Y := q'.host)
        (alignJoint e (typeJoint (p := q) Z))
        (alignJoint e' (typeJoint (p := q') Z)) := by
  classical
  by_contra hall
  push Not at hall
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hL := infra_610_closed_level P σ hσ hμ hrec
  let fA := SystemArrow.refl (P.scheme.asSystem hμ A)
  have hExt : SameGaloisType q (q'.restrict fA trivial) (e.trans e'.symm) (Equiv.refl q'.idx) := by
    refine infra_610_same_galois fA trivial q q' (e.trans e'.symm) σ hσ hσlt hidx hqν hq'ν hL ?_
    intro β hβ ρ hρinf hρμ params hjoint h0 h1
    let Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
      fun b => A.occ (params b)
    have hDE := hall β Z hβ
    have hcong : #(ι ⊕ β) = #(q'.idx ⊕ β) :=
      (Cardinal.mk_congr (Equiv.sumCongr e' (Equiv.refl β))).symm
    have hαμ : #(ι ⊕ β) < μ := by
      rw [hcong]
      exact hjoint.trans_lt hρμ
    have hαle : #(ι ⊕ β) ≤ ρ := by
      rw [hcong]; exact hjoint
    convert infra_612_test_of_diagram
      (alignJoint e (typeJoint (p := q) Z))
      (alignJoint e' (typeJoint (p := q') Z)) hDE
      (by simpa [hqν] using hαμ) (by simpa [hq'ν] using hαμ)
      μ hμ (by simpa [hqν] using q.host.card) (by simpa [hq'ν] using q'.host.card)
      hρinf hρμ hjoint (Sum.map e' (fun b : β => b)) hαle h0 h1 using 2
    · next c =>
        cases c with
        | inl i =>
          simp only [Sum.map_inl, alignJoint, typeJoint, Equiv.symm_trans_apply,
            Equiv.symm_symm, Equiv.apply_symm_apply, Sum.elim_inl]
          rfl
        | inr b =>
          simp only [Sum.map_inr, alignJoint, typeJoint, Z, SMObject.val, oneVertexVal,
            SMObject.occ, Sum.elim_inr]
          rfl
    · next c =>
        cases c with
        | inl i =>
          simp only [Sum.map_inl, alignJoint, typeJoint, Equiv.symm_apply_apply,
            TupleOver.restrict, Sum.elim_inl]
          rfl
        | inr b =>
          simp only [Sum.map_inr, alignJoint, typeJoint, Z, TupleOver.restrict,
            SystemArrow.comp, SystemArrow.refl, fA, Language.Embedding.comp_apply,
            Language.Embedding.refl_apply, SMObject.val, oneVertexVal, SMObject.occ,
            Sum.elim_inr]
          rfl
  exact hneq (infra_73_sgt_common e e' (infra_73_sgt_restrict_refl _ hExt))

/-! ## Extension diagrams on moved parameters -/

set_option maxHeartbeats 800000 in
theorem infra_73_ext_anchored_push
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    (hqν : q.ν = μ) (hBν : qB.ν = μ)
    (hidxμ : #q.idx < μ)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    {ι : Type u} (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hιμ : #ι < μ) :
    P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (typeJoint (p := q) Z0)
      (infra_612_anchored eB qB.incl qB.val (pushParams f Z0)) := by
  have hidxB : #qB.idx < μ := (Cardinal.mk_congr eB).symm.trans_lt hidxμ
  have hAligned :=
    infra_72_diagramEq_of_sameGalois (P := P) hExt Z0 hqν hBν hidxB hιμ
  have hρ : Injective (Sum.map eB (id : ι → ι)) :=
    Sum.map_injective.mpr ⟨eB.injective, injective_id⟩
  have hpre :=
    WorkingScheme.diagramEq_precomp (W := P.scheme) q.host (qB.restrict f hf).host
      (alignJoint eB (typeJoint (p := q) Z0))
      (alignJoint (Equiv.refl qB.idx) (typeJoint (p := qB.restrict f hf) Z0))
      (Sum.map eB id) hρ hAligned
  have hL :
      (fun j => alignJoint eB (typeJoint (p := q) Z0) (Sum.map eB id j)) =
        typeJoint (p := q) Z0 := by
    funext t; cases t with
    | inl i => simp [Sum.map_inl, alignJoint, typeJoint, Equiv.symm_apply_apply]
    | inr j => simp [Sum.map_inr, alignJoint, typeJoint]
  have hR :
      (fun j => alignJoint (Equiv.refl qB.idx) (typeJoint (p := qB.restrict f hf) Z0)
        (Sum.map eB id j)) =
        infra_612_anchored eB qB.incl qB.val (pushParams f Z0) := by
    funext t; cases t with
    | inl i =>
      simp [Sum.map_inl, alignJoint, Equiv.refl_symm, Equiv.refl_apply, typeJoint,
        TupleOver.restrict, infra_612_anchored, pushParams]
    | inr j =>
      simp [Sum.map_inr, alignJoint, Equiv.refl_symm, Equiv.refl_apply, typeJoint,
        TupleOver.restrict, SystemArrow.comp, infra_612_anchored, pushParams]
      rfl
  rw [← hL, ← hR]
  exact hpre

/-- A sequence-move identifies the parameter lists themselves. -/
theorem infra_73_move_param
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hmove : infra_73_isMove f seq Z Z0)
    (i : seq.κIndex) :
    P.scheme.DiagramEq (X := A) (Y := B) Z0 Z := by
  have hL : seqJoint (seq.family i) Z0 = Sum.elim (seq.family i) Z0 := by
    funext t; cases t <;> rfl
  have hpush :
      seqJoint (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩) Z =
        Sum.elim (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩) Z := by
    funext t; cases t <;> rfl
  have hDE := hmove i
  rw [hL, hpush] at hDE
  exact (P.scheme.diagram_restrict A B (seq.family i)
      (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
      Z0 Z hDE).2

/-! ## Competitor transport

A same-level competitor has the same marginal and the same diagram on the approximation
family, and a small test where the two types differ. Recode both hosts on the carrier of
`μ`. Homogeneity supplies an isomorphism of those recodings sending the joint of `q` with
the family to the joint of the competitor. The composite arrow `A → B` is an extension of
`q`: on the family it agrees with the competitor's own inclusion, so the differing test is
a sequence-move, while the tuples still disagree on that test. The `u`-marginal of the
extension is an untied free lift because every extension is (`infra_73_ext_isFreeLift`).
-/

set_option maxHeartbeats 1600000 in
theorem infra_73_alt2
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (seq : ApproximationSequence q)
    (hτge : P.g σ + ls K ≤ seq.τ) (hlong : seq.τ + ℵ₀ < #(seq.κIndex)) (hτμ : seq.τ < μ)
    (hfamμ : #(seq.κIndex × q.idx) < μ)
    (q' : TupleOver K oneVertexShape P.scheme hμ A)
    (e' : q'.idx ≃ uIdx ⊕ cIdx) (hq'ν : q'.ν = μ)
    (hDE : P.scheme.DiagramEq (X := q.host) (Y := q'.host)
      (alignJoint e (typeJoint (p := q) (infra_73_family seq)))
      (alignJoint e' (typeJoint (p := q') (infra_73_family seq))))
    (hneq : ¬ SameGaloisType q q' e e') :
    ∃ (B : P.scheme.Object μ hμ)
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
      (hf : P.scheme.permitted (X := A) (Y := B) f)
      (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : q.idx ≃ qB.idx),
      qB.ν = μ ∧
      SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) ∧
      IsFreeLift (q.marginal e) (qB.marginal (eB.symm.trans e)) f hf (Equiv.refl uIdx) ∧
      ¬ IsTiedFree f q qB eB := by
  classical
  let F := infra_73_family seq
  let α := (uIdx ⊕ cIdx) ⊕ (seq.κIndex × q.idx)
  let alignQ : α → Occurrence K oneVertexShape (P.scheme.asSystem q.hν q.host) :=
    alignJoint e (typeJoint (p := q) F)
  let alignQ' : α → Occurrence K oneVertexShape (P.scheme.asSystem q'.hν q'.host) :=
    alignJoint e' (typeJoint (p := q') F)
  have hα : #α < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) ((Cardinal.mk_congr e).symm.trans_lt hidxμ) hfamμ
  have hαq : #α < q.ν := by simpa [hqν] using hα
  have hαq' : #α < q'.ν := by simpa [hq'ν] using hα
  have hcQsrc : Model.card q.host.model = μ := by simpa [hqν] using q.host.card
  have hcQ'src : Model.card q'.host.model = μ := by simpa [hq'ν] using q'.host.card
  let Q : P.scheme.Object μ hμ := SMObject.ofModel q.host.model q.host.mem hcQsrc
  let B : P.scheme.Object μ hμ := SMObject.ofModel q'.host.model q'.host.mem hcQ'src
  let eQ : q.host.model.carrier ≃[K.τ] Q.model.carrier :=
    SMObject.ofModelEquiv q.host.model q.host.mem hcQsrc
  let eBtr : q'.host.model.carrier ≃[K.τ] B.model.carrier :=
    SMObject.ofModelEquiv q'.host.model q'.host.mem hcQ'src
  have hSameHost : P.D.SameD q.host.model q'.host.model
      (fun i => q.host.val (alignQ i)) (fun i => q'.host.val (alignQ' i)) :=
    (SingleModelData.diagramEq_iff_sameD (P := P) q.hν q'.hν q.host q'.host
      (fun i => q.host.val (alignQ i)) (fun i => q'.host.val (alignQ' i)) hαq hαq').mp hDE
  have hToQ : P.D.SameD q.host.model Q.model
      (fun i => q.host.val (alignQ i)) (fun i => eQ (q.host.val (alignQ i))) :=
    SingleModelData.sameD_of_strong (P := P) hμ hμ hcQsrc Q.card eQ.toEmbedding
      (strong_of_equiv K eQ q.host.mem) _ _ (fun _ => rfl) hα hα
  have hToB : P.D.SameD q'.host.model B.model
      (fun i => q'.host.val (alignQ' i)) (fun i => eBtr (q'.host.val (alignQ' i))) :=
    SingleModelData.sameD_of_strong (P := P) hμ hμ hcQ'src B.card eBtr.toEmbedding
      (strong_of_equiv K eBtr q'.host.mem) _ _ (fun _ => rfl) hα hα
  have hSameQB : P.D.SameD Q.model B.model
      (fun i => eQ (q.host.val (alignQ i)))
      (fun i => eBtr (q'.host.val (alignQ' i))) :=
    (hToQ.symm.trans hSameHost).trans hToB
  let xsQ : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ Q) :=
    fun i => Q.occ (eQ (q.host.val (alignQ i)))
  let ysB : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun i => B.occ (eBtr (q'.host.val (alignQ' i)))
  have hCar : SingleModelData.DiagramEq hμ hμ Q B
      (fun i => Q.val (xsQ i)) (fun i => B.val (ysB i)) := by
    convert (SingleModelData.diagramEq_iff_sameD (P := P) hμ hμ Q B
        (fun i => eQ (q.host.val (alignQ i)))
        (fun i => eBtr (q'.host.val (alignQ' i))) hα hα).mpr hSameQB using 2
    · rw [SMObject.val_occ]
    · rw [SMObject.val_occ]
  have hDEQB : P.scheme.DiagramEq (X := Q) (Y := B) xsQ ysB := hCar
  obtain ⟨φ, -, hφ⟩ := (P.scheme.diagram_iso Q B xsQ ysB hα).mp hDEQB
  let arrQ : SystemArrow K oneVertexShape (P.scheme.asSystem q.hν q.host)
      (P.scheme.asSystem hμ Q) :=
    oneVertexArrow eQ.toEmbedding (strong_of_equiv K eQ q.host.mem)
  let f1 : SystemArrow K oneVertexShape (P.scheme.asSystem q.hν q.host)
      (P.scheme.asSystem hμ B) :=
    SystemArrow.comp arrQ φ
  let f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B) :=
    SystemArrow.comp q.incl f1
  let hf : P.scheme.permitted (X := A) (Y := B) f := trivial
  let eB : q.idx ≃ q'.idx := e.trans e'.symm
  let qB : TupleOver K oneVertexShape P.scheme hμ B :=
    { ν := μ
      hν := hμ
      host := B
      incl := SystemArrow.refl (P.scheme.asSystem hμ B)
      incl_arrow := trivial
      idx := q'.idx
      val := fun i => B.occ (eBtr (q'.host.val (q'.val i))) }
  have hφTuple : ∀ k : uIdx ⊕ cIdx,
      φ.onVertex (xsQ (Sum.inl k)).1 (xsQ (Sum.inl k)).2 =
        eBtr (q'.host.val (q'.val (e'.symm k))) := by
    intro k
    have hk := hφ (Sum.inl k)
    have hxs : xsQ (Sum.inl k) =
        Q.occ (eQ (q.host.val (q.val (e.symm k)))) := rfl
    have hys : ysB (Sum.inl k) =
        B.occ (eBtr (q'.host.val (q'.val (e'.symm k)))) := rfl
    rw [hxs, hys] at hk
    have hk' := congrArg B.val hk
    simp only [SMObject.val_occ, SMObject.val, oneVertexVal] at hk'
    rw [hxs]
    exact hk'.symm
  have hφFam : ∀ j : seq.κIndex × q.idx,
      φ.onVertex (xsQ (Sum.inr j)).1 (xsQ (Sum.inr j)).2 =
        eBtr (q'.incl.onVertex (F j).1 (F j).2) := by
    intro j
    have hj := hφ (Sum.inr j)
    have hxs : xsQ (Sum.inr j) =
        Q.occ (eQ (q.incl.onVertex (F j).1 (F j).2)) := rfl
    have hys : ysB (Sum.inr j) =
        B.occ (eBtr (q'.incl.onVertex (F j).1 (F j).2)) := rfl
    rw [hxs, hys] at hj
    have hj' := congrArg B.val hj
    simp only [SMObject.val_occ, SMObject.val, oneVertexVal] at hj'
    rw [hxs]
    exact hj'.symm
  have hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) := by
    refine ⟨μ, hμ, B, f1, SystemArrow.refl (P.scheme.asSystem hμ B), trivial, trivial, ?_, ?_⟩
    · intro v
      ext x
      simp only [f, f1, qB, TupleOver.restrict, SystemArrow.comp, SystemArrow.refl,
        Language.Embedding.comp_apply, Language.Embedding.refl_apply]
      rfl
    · intro i
      apply Sigma.ext
      · exact Subsingleton.elim _ _
      · have hidx : e.symm (e' i) = eB.symm i := by
          simp [eB, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
        have hφi := hφTuple (e' i)
        have hEl : f1.onVertex (q.val (eB.symm i)).1 (q.val (eB.symm i)).2 =
            eBtr (q'.host.val (q'.val i)) := by
          have hxs : xsQ (Sum.inl (e' i)) =
              Q.occ (eQ (q.host.val (q.val (e.symm (e' i))))) := rfl
          rw [hxs] at hφi
          simp only [SMObject.occ, oneVertexOcc, SMObject.val, oneVertexVal,
            Equiv.apply_symm_apply] at hφi
          show (φ.onVertex PUnit.unit).comp eQ.toEmbedding (q.val (eB.symm i)).2 =
            eBtr (q'.host.val (q'.val i))
          erw [Language.Embedding.comp_apply, ← hidx]
          change (φ.onVertex PUnit.unit) (eQ (q.val (e.symm (e' i))).2) =
            eBtr (q'.host.val (q'.val i))
          rw [Equiv.symm_apply_apply] at hφi
          simp only [SMObject.val, oneVertexVal] at hφi ⊢
          exact hφi
        have hEr : (SystemArrow.refl (P.scheme.asSystem hμ B)).onVertex (qB.val i).1
            (qB.val i).2 = eBtr (q'.host.val (q'.val i)) := by
          show (Language.Embedding.refl K.τ B.model.carrier) (qB.val i).2 =
            eBtr (q'.host.val (q'.val i))
          erw [Language.Embedding.refl_apply]
        exact heq_of_eq (hEl.trans hEr.symm)
  have hMargS : SameGaloisType (q.marginal e)
      ((qB.marginal (eB.symm.trans e)).restrict f hf)
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
    have hExt' := hExt
    rcases hExt' with ⟨ρ, hρ, top, fA, fB, hfA, hfB, hcomm, hval⟩
    refine ⟨ρ, hρ, top, fA, fB, hfA, hfB, hcomm, ?_⟩
    intro a
    have hix : (eB.symm.trans e).symm (Sum.inl a) = eB (e.symm (Sum.inl a)) := by
      simp [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    have hv := hval (eB (e.symm (Sum.inl a)))
    rw [Equiv.symm_apply_apply] at hv
    simp only [hix, TupleOver.marginal, TupleOver.restrict, Equiv.refl_symm,
      Equiv.refl_apply] at hv ⊢
    exact hv
  have hidxu : #uIdx ≤ σ := by
    have : #uIdx ≤ #q.idx := by
      rw [Cardinal.mk_congr e, mk_sum, lift_id]
      exact le_self_add
    exact this.trans hidx
  have hidxuμ : #uIdx < μ := by
    have : #uIdx ≤ #q.idx := by
      rw [Cardinal.mk_congr e, mk_sum, lift_id]
      exact le_self_add
    exact this.trans_lt hidxμ
  have hMargFree : IsFreeLift (q.marginal e) (qB.marginal (eB.symm.trans e)) f hf
      (Equiv.refl uIdx) :=
    infra_73_ext_isFreeLift σ hσ hμ hrec hσSucc f hf (q.marginal e)
      (qB.marginal (eB.symm.trans e)) (Equiv.refl uIdx)
      (by simpa [TupleOver.marginal] using hqν) rfl hidxu hidxuμ hMargS
  refine ⟨B, f, hf, qB, eB, rfl, hExt, hMargFree, ?_⟩
  intro hTied
  obtain ⟨β, Zt, hβ, hdiff⟩ :=
    infra_73_differing_test P σ hσ hμ hrec hσSucc q q' e e' hqν hq'ν hidx hidxμ hneq
  have hβτ : #β ≤ seq.τ := hβ.trans hτge
  have hβμ : #β < μ := hβτ.trans_lt hτμ
  let Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun j => B.occ (eBtr (q'.incl.onVertex (Zt j).1 (Zt j).2))
  have hmove : infra_73_isMove f seq Z Zt := by
    intro i
    let gEmb := eBtr.toEmbedding.comp (q'.incl.onVertex PUnit.unit)
    have hgStrong : K.Strong gEmb :=
      K.strong_trans _ _ (q'.incl.onVertex_strong PUnit.unit)
        (strong_of_equiv K eBtr q'.host.mem)
    let g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B) :=
      oneVertexArrow gEmb hgStrong
    have hcard : #(q.idx ⊕ β) < μ := by
      rw [mk_sum, lift_id, lift_id]
      exact add_lt_of_lt (P.aleph0_le hμ) hidxμ hβμ
    have hPres := P.scheme.diagram_preserved A B g trivial (seqJoint (seq.family i) Zt) hcard hcard
    have hRHS : (fun t => ⟨(seqJoint (seq.family i) Zt t).1,
        g.onVertex (seqJoint (seq.family i) Zt t).1
          (seqJoint (seq.family i) Zt t).2⟩) =
        seqJoint (fun j => ⟨(seq.family i j).1,
          f.onVertex (seq.family i j).1 (seq.family i j).2⟩) Z := by
      funext t
      cases t with
      | inl j =>
        have hpt := hφFam (i, j)
        simp [seqJoint, g, oneVertexArrow, f, f1, arrQ, F, infra_73_family,
          Language.Embedding.comp_apply, SMObject.occ] at hpt ⊢
        exact hpt.symm
      | inr b =>
        rfl
    rw [hRHS] at hPres
    exact hPres
  have hBad := hTied seq Z Zt hlong hβτ hβμ hmove
  let eRe : (q.idx ⊕ β) ≃ ((uIdx ⊕ cIdx) ⊕ β) := Equiv.sumCongr e (Equiv.refl β)
  have hReFun : alignJoint e (typeJoint (p := q) Zt) =
      fun t => typeJoint (p := q) Zt (eRe.symm t) := by
    funext t
    cases t with
    | inl k =>
      have hsym : eRe.symm (Sum.inl k) = Sum.inl (e.symm k) := rfl
      simp only [alignJoint, typeJoint, hsym]
    | inr b =>
      have hsym : eRe.symm (Sum.inr b) = Sum.inr b := rfl
      simp only [alignJoint, typeJoint, hsym]
  have hAlign : P.scheme.DiagramEq (X := q.host) (Y := B)
      (alignJoint e (typeJoint (p := q) Zt))
      (fun t => infra_612_anchored eB qB.incl qB.val Z (eRe.symm t)) := by
    rw [hReFun]
    exact (P.scheme.diagram_reindex q.host B eRe (typeJoint (p := q) Zt)
      (infra_612_anchored eB qB.incl qB.val Z)).mp hBad
  have hBack : P.scheme.DiagramEq (X := B) (Y := q'.host)
      (fun t => infra_612_anchored eB qB.incl qB.val Z (eRe.symm t))
      (alignJoint e' (typeJoint (p := q') Zt)) := by
    let backEmb := eBtr.symm.toEmbedding
    have hBackStrong : K.Strong backEmb := strong_of_equiv K eBtr.symm B.mem
    let back : SystemArrow K oneVertexShape (P.scheme.asSystem hμ B)
        (P.scheme.asSystem q'.hν q'.host) :=
      oneVertexArrow backEmb hBackStrong
    have hcard : #((uIdx ⊕ cIdx) ⊕ β) < μ := by
      rw [mk_sum, lift_id, lift_id]
      exact add_lt_of_lt (P.aleph0_le hμ) ((Cardinal.mk_congr e).symm.trans_lt hidxμ) hβμ
    have hcard' : #((uIdx ⊕ cIdx) ⊕ β) < q'.ν := by simpa [hq'ν] using hcard
    have hPres := P.scheme.diagram_preserved B q'.host back trivial
      (fun t => infra_612_anchored eB qB.incl qB.val Z (eRe.symm t)) hcard hcard'
    have hEq : (fun t => ⟨((infra_612_anchored eB qB.incl qB.val Z (eRe.symm t))).1,
        back.onVertex _ ((infra_612_anchored eB qB.incl qB.val Z (eRe.symm t))).2⟩) =
        alignJoint e' (typeJoint (p := q') Zt) := by
      funext t
      cases t with
      | inl k =>
        have hsym : eRe.symm (Sum.inl k) = Sum.inl (e.symm k) := rfl
        have hidx : eB (e.symm k) = e'.symm k := by
          simp [eB, Equiv.trans_apply, Equiv.apply_symm_apply]
        rw [hsym]
        apply Sigma.ext
        · exact Subsingleton.elim _ _
        · have hEl : backEmb (eBtr (q'.val (eB (e.symm k))).2) = (q'.val (e'.symm k)).2 := by
            rw [hidx]
            simp only [backEmb, Language.Equiv.coe_toEmbedding]
            exact Language.Equiv.symm_apply_apply eBtr _
          exact heq_of_eq hEl
      | inr b =>
        have hsym : eRe.symm (Sum.inr b) = Sum.inr b := rfl
        rw [hsym]
        apply Sigma.ext
        · exact Subsingleton.elim _ _
        · have hEl : backEmb (eBtr (q'.incl.onVertex (Zt b).1 (Zt b).2)) =
              q'.incl.onVertex (Zt b).1 (Zt b).2 := by
            simp only [backEmb, Language.Equiv.coe_toEmbedding]
            exact Language.Equiv.symm_apply_apply eBtr _
          exact heq_of_eq hEl
    rw [hEq] at hPres
    exact hPres
  exact hdiff (P.scheme.diagram_trans q.host B q'.host _ _ _ hAlign hBack)

/-! ## Isolation upgrades an extension to tied freeness

A sequence-move identifies each approximation copy jointly with `Z₀` and with `Z`.
Pushing the copy along `f` therefore answers `Z` and `f(Z₀)` the same way. The extension
identifies `q` with that answer on `f(Z₀)`. Isolation, applied to a saturation of the
actual joint over the isolating fragment, forces the same answer on `Z`.
-/

theorem infra_73_copy_tail_swap
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hmove : infra_73_isMove f seq Z Z0)
    (hidxμ : #q.idx < μ) (hιμ : #ι < μ)
    (i : seq.κIndex) :
    P.scheme.DiagramEq (X := B) (Y := B)
      (seqJoint
        (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩) Z)
      (seqJoint
        (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
        (pushParams f Z0)) := by
  have hcard : #(q.idx ⊕ ι) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hidxμ hιμ
  have hMove := hmove i
  have hPres :=
    P.scheme.diagram_preserved A B f hf (seqJoint (seq.family i) Z0) hcard hcard
  have hRewrite :
      (fun t => ⟨(seqJoint (seq.family i) Z0 t).1,
          f.onVertex (seqJoint (seq.family i) Z0 t).1
            (seqJoint (seq.family i) Z0 t).2⟩) =
        seqJoint
          (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
          (pushParams f Z0) := by
    funext t
    cases t with
    | inl _ => rfl
    | inr _ => rfl
  have hPush :
      P.scheme.DiagramEq (X := A) (Y := B)
        (seqJoint (seq.family i) Z0)
        (seqJoint
          (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
          (pushParams f Z0)) := by
    simpa [hRewrite] using hPres
  exact P.scheme.diagram_trans B A B _ _ _
    (P.scheme.diagram_symm A B _ _ hMove) hPush

theorem infra_73_moves_agree
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0 Z1 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hmove0 : infra_73_isMove f seq Z Z0)
    (hmove1 : infra_73_isMove f seq Z Z1)
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
  have hinf : ℵ₀ ≤ #(seq.κIndex) :=
    (le_add_self (a := ℵ₀) (b := #ι)).trans (le_of_lt hκ)
  have hex : ∃ i : seq.κIndex, i ∉ Exc0 ∧ i ∉ Exc1 := by
    by_contra h
    have hall : (Set.univ : Set seq.κIndex) ⊆ Exc0 ∪ Exc1 := by
      intro i _
      by_cases hi : i ∈ Exc0 ∪ Exc1
      · exact hi
      · exact False.elim (h ⟨i, by
          simp only [Set.mem_union, not_or] at hi
          exact hi⟩)
    have hle : #(seq.κIndex) ≤ (#ι + ℵ₀) + (#ι + ℵ₀) := by
      have huni : #(Set.univ : Set seq.κIndex) = #(seq.κIndex) := mk_univ
      rw [← huni]
      exact (mk_le_mk_of_subset hall).trans
        ((mk_union_le _ _).trans (add_le_add hExc0 hExc1))
    exact (not_le_of_gt (add_lt_of_lt hinf hκ hκ)) hle
  obtain ⟨i, hi0, hi1⟩ := hex
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

/-! ## Move a query over an isolating fragment

Saturation of one list `W ++ concat(seq) ++ Z`. `diagram_iso` pulls the query half back
into `A`, fixing `W` and the approximation concat. Each copy is then one `seqJoint`
(`diagramEq_precomp`); the fragment is not glued on afterwards.
-/

set_option maxHeartbeats 800000 in
theorem infra_73_move_over_fragment
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q)
    {wι ι : Type u}
    (W : wι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hW : #wι < μ) (hι : #ι < μ) :
    ∃ Z' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
      ∀ i : seq.κIndex,
        P.scheme.DiagramEq (X := A) (Y := B)
          (seqJoint (seq.family i) (Sum.elim W Z'))
          (seqJoint
            (fun j =>
              ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
            (Sum.elim (pushParams f W) Z)) := by
  classical
  let α : Type u := wι ⊕ (seq.κIndex × q.idx)
  let xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    Sum.elim W (fun ij => seq.family ij.1 ij.2)
  let base : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun a => ⟨(xs a).1, f.onVertex (xs a).1 (xs a).2⟩
  let ext : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    Sum.elim base Z
  have hα : #α < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hW seq.concat_bounded
  have hEqPush : P.scheme.DiagramEq (X := A) (Y := B) xs base :=
    P.scheme.diagram_preserved A B f hf xs hα hα
  obtain ⟨Zext, g, zs, -, hzs, hzsEq⟩ :=
    (SingleModelData.isSaturated (P := P)).saturated
      A B xs base ext hα hι (fun _ => rfl) hEqPush
  have hPushG : P.scheme.DiagramEq (X := A) (Y := Zext) xs
      (fun a => ⟨(xs a).1, g.onVertex (xs a).1 (xs a).2⟩) :=
    P.scheme.diagram_preserved A Zext g trivial xs hα hα
  have hxsZs : (fun a => ⟨(xs a).1, g.onVertex (xs a).1 (xs a).2⟩) =
      fun a => zs (Sum.inl a) := funext fun a => (hzs a).symm
  have hEqZsInl : P.scheme.DiagramEq (X := A) (Y := Zext) xs (fun a => zs (Sum.inl a)) := by
    rw [← hxsZs]
    exact hPushG
  obtain ⟨φ, hφiso, hφ⟩ :=
    (P.scheme.diagram_iso A Zext xs (fun a => zs (Sum.inl a)) hα).mp hEqZsInl
  have hφbij : Bijective (φ.onVertex PUnit.unit) := hφiso PUnit.unit
  let eφ : A.model.carrier ≃ Zext.model.carrier := Equiv.ofBijective _ hφbij
  let Z' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun j => A.occ (eφ.symm (Zext.val (zs (Sum.inr j))))
  let jointA : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
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
  have hPushφ : P.scheme.DiagramEq (X := A) (Y := Zext) jointA zs := by
    have hcard : #(α ⊕ ι) < μ := by
      rw [mk_sum, lift_id, lift_id]
      exact add_lt_of_lt (P.aleph0_le hμ) hα hι
    have h := P.scheme.diagram_preserved A Zext φ trivial jointA hcard hcard
    have heq : (fun t => ⟨(jointA t).1, φ.onVertex (jointA t).1 (jointA t).2⟩) = zs :=
      funext fun t => (hφjoint t).symm
    rwa [heq] at h
  have hJointExt : P.scheme.DiagramEq (X := A) (Y := B) jointA ext :=
    P.scheme.diagram_trans A Zext B jointA zs ext hPushφ hzsEq
  refine ⟨Z', fun i => ?_⟩
  let ρ : q.idx ⊕ (wι ⊕ ι) → α ⊕ ι := fun t =>
    match t with
    | Sum.inl j => Sum.inl (Sum.inr (i, j))
    | Sum.inr (Sum.inl w) => Sum.inl (Sum.inl w)
    | Sum.inr (Sum.inr k) => Sum.inr k
  have hρ : Injective ρ := by
    intro x y hxy
    cases x with
    | inl j =>
      cases y with
      | inl j' =>
        simp only [ρ] at hxy
        exact congrArg Sum.inl (Prod.ext_iff.mp (Sum.inr.inj (Sum.inl.inj hxy))).2
      | inr y' =>
        cases y' with
        | inl w => simp [ρ] at hxy
        | inr k => simp [ρ] at hxy
    | inr x' =>
      cases x' with
      | inl w =>
        cases y with
        | inl j => simp [ρ] at hxy
        | inr y' =>
          cases y' with
          | inl w' =>
            simp only [ρ] at hxy
            exact congrArg (Sum.inr ∘ Sum.inl) (Sum.inl.inj (Sum.inl.inj hxy))
          | inr k => simp [ρ] at hxy
      | inr k =>
        cases y with
        | inl j => simp [ρ] at hxy
        | inr y' =>
          cases y' with
          | inl w => simp [ρ] at hxy
          | inr k' =>
            simp only [ρ] at hxy
            exact congrArg (Sum.inr ∘ Sum.inr) (Sum.inr.inj hxy)
  have hpre :=
    WorkingScheme.diagramEq_precomp (W := P.scheme) A B jointA ext ρ hρ hJointExt
  have hLρ : (fun t => jointA (ρ t)) =
      seqJoint (seq.family i) (Sum.elim W Z') := by
    funext t
    cases t with
    | inl _ => rfl
    | inr t' =>
      cases t' <;> rfl
  have hRρ : (fun t => ext (ρ t)) =
      seqJoint
        (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
        (Sum.elim (pushParams f W) Z) := by
    funext t
    cases t with
    | inl _ => rfl
    | inr t' =>
      cases t' with
      | inl _ =>
        apply Sigma.ext
        · exact Subsingleton.elim _ _
        · rfl
      | inr _ => rfl
  rw [← hLρ, ← hRρ]
  exact hpre

/-- Transport a `DiagramEq` along pointwise equalities of both lists. -/
theorem infra_73_diagramEq_of_eq
    {P : SingleModelData K} {μ ν : Cardinal.{u}} {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {X : P.scheme.Object μ hμ} {Y : P.scheme.Object ν hν} {α : Type u}
    {xs xs' : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ X)}
    {ys ys' : α → Occurrence K oneVertexShape (P.scheme.asSystem hν Y)}
    (h : P.scheme.DiagramEq (X := X) (Y := Y) xs ys)
    (hx : ∀ t, xs t = xs' t) (hy : ∀ t, ys t = ys' t) :
    P.scheme.DiagramEq (X := X) (Y := Y) xs' ys' := by
  have h1 : xs = xs' := funext hx
  have h2 : ys = ys' := funext hy
  subst h1 h2
  exact h

/-! ## Move a query by one structural isomorphism

Saturation of one list `xs ++ Z` (`xs` in `A`, pushed to `B`), then homogeneity
(`diagram_iso`) between the two same-level objects: a single structural isomorphism
`ψ : A ≅ B` agrees with `f` on `xs` and carries the pulled-back query `Z'` onto `Z`.
-/

set_option maxHeartbeats 800000 in
theorem infra_73_move_iso
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    {α ι : Type u}
    (xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hα : #α < μ) (hι : #ι < μ) :
    ∃ (Z' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
      (ψ : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B)),
      P.scheme.IsStructIso (X := A) (Y := B) ψ ∧
      (∀ a, (⟨(xs a).1, ψ.onVertex (xs a).1 (xs a).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) =
        ⟨(xs a).1, f.onVertex (xs a).1 (xs a).2⟩) ∧
      ∀ j, Z j = ⟨(Z' j).1, ψ.onVertex (Z' j).1 (Z' j).2⟩ := by
  classical
  let base : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun a => ⟨(xs a).1, f.onVertex (xs a).1 (xs a).2⟩
  let ext : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    Sum.elim base Z
  have hEqPush : P.scheme.DiagramEq (X := A) (Y := B) xs base :=
    P.scheme.diagram_preserved A B f hf xs hα hα
  obtain ⟨Zext, g, zs, -, hzs, hzsEq⟩ :=
    (SingleModelData.isSaturated (P := P)).saturated
      A B xs base ext hα hι (fun _ => rfl) hEqPush
  have hPushG : P.scheme.DiagramEq (X := A) (Y := Zext) xs
      (fun a => ⟨(xs a).1, g.onVertex (xs a).1 (xs a).2⟩) :=
    P.scheme.diagram_preserved A Zext g trivial xs hα hα
  have hxsZs : (fun a => ⟨(xs a).1, g.onVertex (xs a).1 (xs a).2⟩) =
      fun a => zs (Sum.inl a) := funext fun a => (hzs a).symm
  have hEqZsInl : P.scheme.DiagramEq (X := A) (Y := Zext) xs (fun a => zs (Sum.inl a)) := by
    rw [← hxsZs]
    exact hPushG
  obtain ⟨φ, hφiso, hφ⟩ :=
    (P.scheme.diagram_iso A Zext xs (fun a => zs (Sum.inl a)) hα).mp hEqZsInl
  have hφbij : Bijective (φ.onVertex PUnit.unit) := hφiso PUnit.unit
  let eφ : A.model.carrier ≃ Zext.model.carrier := Equiv.ofBijective _ hφbij
  let Z' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun j => A.occ (eφ.symm (Zext.val (zs (Sum.inr j))))
  let jointA : α ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
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
  have hcard : #(α ⊕ ι) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hα hι
  have hPushφ : P.scheme.DiagramEq (X := A) (Y := Zext) jointA zs := by
    have h := P.scheme.diagram_preserved A Zext φ trivial jointA hcard hcard
    have heq : (fun t => ⟨(jointA t).1, φ.onVertex (jointA t).1 (jointA t).2⟩) = zs :=
      funext fun t => (hφjoint t).symm
    rwa [heq] at h
  have hJointExt : P.scheme.DiagramEq (X := A) (Y := B) jointA ext :=
    P.scheme.diagram_trans A Zext B jointA zs ext hPushφ hzsEq
  obtain ⟨ψ, hψiso, hψ⟩ :=
    (P.scheme.diagram_iso A B jointA ext hcard).mp hJointExt
  refine ⟨Z', ψ, hψiso, fun a => (hψ (Sum.inl a)).symm, fun j => hψ (Sum.inr j)⟩

/-! ## Tied answer on one sequence-move

One structural isomorphism `ψ : A ≅ B` (`infra_73_move_iso`) agrees with `f` on the
isolating fragment `W` and on both approximation families, and pulls the query `Z` back to
`Z'`. The competitor `qB.restrict ψ` has the `u`-marginal of `q` (tied free evaluation on
`ψ`-moved tests, `hMargTied`) and the diagram of `q` over `W` (`hExt`), so isolation makes
it `q`. Its joint with `Z'` is the anchored answer on `Z`, and `Z'` is a sequence-move of
`Z` like `Z₀` (`infra_73_moves_agree`). Every equality is one monolithic list.
-/

set_option maxHeartbeats 3200000 in
theorem infra_73_tied_answer
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hBν : qB.ν = μ)
    (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (hIso : IsRelativelyIsolated q e)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    (hMargTied : IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e))
      (Equiv.refl uIdx))
    (seq : ApproximationSequence q) {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hlong : seq.τ + ℵ₀ < #(seq.κIndex))
    (hιτ : #ι ≤ seq.τ) (hιμ : #ι < μ)
    (hmove : infra_73_isMove f seq Z Z0) :
    P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (typeJoint (p := q) Z0)
      (infra_612_anchored eB qB.incl qB.val Z) := by
  classical
  obtain ⟨wι, W, hIsoW⟩ := IsIsolatingFragment.of_relativelyIsolated hIso
  have hWμ : #wι < μ := hIsoW.1
  have hκadd : #ι + ℵ₀ < #(seq.κIndex) :=
    (add_le_add hιτ le_rfl).trans_lt hlong
  -- A long approximation sequence for the `u`-marginal, used as tied tests.
  let qu : TupleOver K oneVertexShape P.scheme hμ A := q.marginal e
  have huidx : #uIdx ≤ #q.idx :=
    Cardinal.mk_le_of_injective (f := fun i : uIdx => e.symm (Sum.inl i))
      (fun a b h => Sum.inl.inj (e.symm.injective h))
  obtain ⟨seqU, -, -, hτU, hlongU⟩ :=
    infra_73_sequence_rec P σ hσ hμ hrec hσSucc qu hqν (huidx.trans hidx)
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  -- One bounded list in `A`: fragment, both approximation families.
  let α : Type u := wι ⊕ ((seq.κIndex × q.idx) ⊕ (seqU.κIndex × uIdx))
  let xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    Sum.elim W (Sum.elim (fun ij => seq.family ij.1 ij.2) (fun ij => seqU.family ij.1 ij.2))
  have hα : #α < μ := by
    simp only [α, mk_sum, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hWμ
      (add_lt_of_lt (P.aleph0_le hμ) seq.concat_bounded seqU.concat_bounded)
  obtain ⟨Z', ψ, hψiso, hψxs, hψZ⟩ := infra_73_move_iso f hf xs Z hα hιμ
  have hψ : P.scheme.permitted (X := A) (Y := B) ψ :=
    P.scheme.structural_iso A B ψ hψiso
  have hψW : ∀ w, (⟨(W w).1, ψ.onVertex (W w).1 (W w).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) =
      ⟨(W w).1, f.onVertex (W w).1 (W w).2⟩ := fun w => hψxs (Sum.inl w)
  have hψF : ∀ i j, (⟨(seq.family i j).1, ψ.onVertex _ (seq.family i j).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) =
      ⟨(seq.family i j).1, f.onVertex _ (seq.family i j).2⟩ :=
    fun i j => hψxs (Sum.inr (Sum.inl (i, j)))
  have hψU : ∀ i j, (⟨(seqU.family i j).1, ψ.onVertex _ (seqU.family i j).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) =
      ⟨(seqU.family i j).1, f.onVertex _ (seqU.family i j).2⟩ :=
    fun i j => hψxs (Sum.inr (Sum.inr (i, j)))
  -- The competitor: `qB` read over `A` along `ψ`.
  let q' : TupleOver K oneVertexShape P.scheme hμ A := qB.restrict ψ hψ
  let e' : q'.idx ≃ uIdx ⊕ cIdx := eB.symm.trans e
  -- (1) Same `u`-marginal, by tied freeness on `ψ`-moved tests.
  have hMarg : SameGaloisType (q.marginal e) (q'.marginal e')
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ :=
      infra_73_differing_test P σ hσ hμ hrec hσSucc (q.marginal e) (q'.marginal e')
        (Equiv.refl uIdx) (Equiv.refl uIdx) hqν hBν (huidx.trans hidx)
        (huidx.trans_lt hidxμ) hneq
    apply hnot
    have hβτ : #β ≤ seqU.τ := hβ.trans hτU
    have hβμ : #β < μ := by
      have hgls : P.g σ + ls K < μ := by
        have hg : P.g σ < μ :=
          (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
        exact add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ)
      exact hβ.trans_lt hgls
    have hmoveU : infra_73_isMove f seqU (pushParams ψ Y) Y := by
      intro i
      have hcard : #(uIdx ⊕ β) < μ := by
        rw [mk_sum, lift_id, lift_id]
        exact add_lt_of_lt (P.aleph0_le hμ) (huidx.trans_lt hidxμ) hβμ
      have h := P.scheme.diagram_preserved A B ψ hψ (seqJoint (seqU.family i) Y) hcard hcard
      have heq : (fun t => (⟨(seqJoint (seqU.family i) Y t).1,
            ψ.onVertex _ (seqJoint (seqU.family i) Y t).2⟩ :
            Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) =
          seqJoint (fun j => ⟨(seqU.family i j).1, f.onVertex _ (seqU.family i j).2⟩)
            (pushParams ψ Y) := by
        funext t
        cases t with
        | inl j => exact hψU i j
        | inr k => rfl
      rw [heq] at h
      exact h
    have hT := hMargTied seqU (pushParams ψ Y) Y hlongU hβτ hβμ hmoveU
    have hL : alignJoint (Equiv.refl uIdx) (typeJoint (p := q.marginal e) Y) =
        typeJoint (p := q.marginal e) Y := by
      funext t; cases t <;> rfl
    have hR : alignJoint (Equiv.refl uIdx) (typeJoint (p := q'.marginal e') Y) =
        infra_612_anchored (Equiv.refl uIdx) (qB.marginal (eB.symm.trans e)).incl
          (qB.marginal (eB.symm.trans e)).val (pushParams ψ Y) := by
      funext t; cases t <;> rfl
    exact infra_73_diagramEq_of_eq hT (fun t => (congrFun hL t).symm)
      (fun t => (congrFun hR t).symm)
  -- (2) Same diagram over the isolating fragment, from `hExt` (ψ = f on `W`).
  have hqBidx : #qB.idx < μ := by
    rw [← Cardinal.mk_congr eB]; exact hidxμ
  have hWDE : P.scheme.DiagramEq (X := q.host) (Y := q'.host)
      (alignJoint e (typeJoint (p := q) W)) (alignJoint e' (typeJoint (p := q') W)) := by
    have h0 := infra_72_diagramEq_of_sameGalois (P := P) hExt W hqν hBν hqBidx hWμ
    let eq : qB.idx ⊕ wι ≃ (uIdx ⊕ cIdx) ⊕ wι := Equiv.sumCongr e' (Equiv.refl wι)
    have h1 := (P.scheme.diagram_reindex q.host qB.host eq _ _).mp h0
    have hL : (fun b => alignJoint eB (typeJoint (p := q) W) (eq.symm b)) =
        alignJoint e (typeJoint (p := q) W) := by
      funext b
      cases b with
      | inl k =>
        simp only [eq, e', alignJoint, typeJoint, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
          Sum.map_inl, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
          Equiv.symm_apply_apply]
      | inr w => rfl
    have hR : (fun b => alignJoint (Equiv.refl qB.idx)
          (typeJoint (p := qB.restrict f hf) W) (eq.symm b)) =
        alignJoint e' (typeJoint (p := q') W) := by
      funext b
      cases b with
      | inl k => rfl
      | inr w =>
        have hw : ψ.onVertex (W w).1 (W w).2 = f.onVertex (W w).1 (W w).2 :=
          eq_of_heq (Sigma.mk.inj_iff.mp (hψW w)).2
        show (⟨(W w).1, qB.incl.onVertex _ (f.onVertex (W w).1 (W w).2)⟩ :
            Occurrence K oneVertexShape (P.scheme.asSystem qB.hν qB.host)) =
          ⟨(W w).1, qB.incl.onVertex _ (ψ.onVertex (W w).1 (W w).2)⟩
        rw [hw]
    exact infra_73_diagramEq_of_eq h1 (congrFun hL) (congrFun hR)
  -- (3) Isolation identifies the competitor with `q`.
  have hSame : SameGaloisType q q' e e' := hIsoW.2 q' e' hBν hMarg hWDE
  -- (4) The answer on `Z'` is the anchored answer on `Z`.
  have hcIdx : #(uIdx ⊕ cIdx) < μ := by
    rw [← Cardinal.mk_congr e]; exact hidxμ
  have hAns : P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (typeJoint (p := q) Z') (infra_612_anchored eB qB.incl qB.val Z) := by
    have h0 := infra_72_diagramEq_of_sameGalois (P := P) hSame Z' hqν hBν hcIdx hιμ
    let eq : (uIdx ⊕ cIdx) ⊕ ι ≃ q.idx ⊕ ι := Equiv.sumCongr e.symm (Equiv.refl ι)
    have h1 := (P.scheme.diagram_reindex q.host qB.host eq _ _).mp h0
    have hL : (fun b => alignJoint e (typeJoint (p := q) Z') (eq.symm b)) =
        typeJoint (p := q) Z' := by
      funext b
      cases b with
      | inl k =>
        simp only [eq, alignJoint, typeJoint, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
          Sum.map_inl, Equiv.symm_symm, Equiv.symm_apply_apply]
      | inr w => rfl
    have hkey : ∀ k : q.idx, (eB.symm.trans e).symm (e k) = eB k := by
      intro k
      rw [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    have hR : (fun b => alignJoint e' (typeJoint (p := q') Z') (eq.symm b)) =
        infra_612_anchored eB qB.incl qB.val Z := by
      funext b
      cases b with
      | inl k =>
        simp only [eq, e', alignJoint, typeJoint, infra_612_anchored, Equiv.sumCongr_symm,
          Equiv.sumCongr_apply, Sum.map_inl, Equiv.symm_symm, Equiv.symm_trans_apply,
          Equiv.symm_apply_apply, q', TupleOver.restrict]
        exact congrArg qB.val (hkey k)
      | inr j =>
        simp only [eq, alignJoint, typeJoint, infra_612_anchored, Equiv.sumCongr_symm,
          Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_symm, Equiv.refl_apply, q',
          TupleOver.restrict, SystemArrow.comp, Language.Embedding.comp_apply]
        rw [hψZ j]
        rfl
    exact infra_73_diagramEq_of_eq h1 (congrFun hL) (congrFun hR)
  -- (5) `Z'` is itself a sequence-move of `Z`; moves agree on `q`.
  have hmove' : infra_73_isMove f seq Z Z' := by
    intro i
    have hcard : #(q.idx ⊕ ι) < μ := by
      rw [mk_sum, lift_id, lift_id]
      exact add_lt_of_lt (P.aleph0_le hμ) hidxμ hιμ
    have h := P.scheme.diagram_preserved A B ψ hψ (seqJoint (seq.family i) Z') hcard hcard
    have heq : (fun t => (⟨(seqJoint (seq.family i) Z' t).1,
          ψ.onVertex _ (seqJoint (seq.family i) Z' t).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) =
        seqJoint (fun j => ⟨(seq.family i j).1, f.onVertex _ (seq.family i j).2⟩) Z := by
      funext t
      cases t with
      | inl j => exact hψF i j
      | inr k => exact (hψZ k).symm
    rw [heq] at h
    exact h
  have hAgree : P.scheme.DiagramEq (X := q.host) (Y := q.host)
      (typeJoint (p := q) Z0) (typeJoint (p := q) Z') :=
    infra_73_moves_agree f seq Z Z0 Z' hmove hmove' hιτ hκadd
  exact P.scheme.diagram_trans q.host q.host qB.host _ _ _ hAgree hAns

theorem infra_73_tied_of_isolated
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hBν : qB.ν = μ)
    (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (hIso : IsRelativelyIsolated q e)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    (hMargTied : IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e))
      (Equiv.refl uIdx)) :
    IsTiedFree f q qB eB := by
  intro seq ι Z Z0 hlong hιτ hιμ hmove
  exact infra_73_tied_answer P σ hσ hμ hrec hσSucc f hf q qB eB e hqν hBν hidx hidxμ
    hIso hExt hMargTied seq Z Z0 hlong hιτ hιμ hmove

/-! ## Uniqueness of tied-free extensions and over-`B` isolation (English Lem 7.2 clause 2)

Every bounded query `Y` from `B` is a sequence-move of some `Y₀` in `A` (one structural
isomorphism, `infra_73_move_iso`), so two tied-free extensions answer every bounded test
alike; `infra_73_differing_test` turns that into one Galois type over `B`. With
`infra_73_tied_of_isolated` this gives full relative isolation of the free extension `qB`
over `B` by the pushed fragment.
-/

theorem infra_73_sgt_equiv_trans
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hμ A} {ι ι' : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι}
    (h : SameGaloisType t1 t2 e1 e2) (g : ι ≃ ι') :
    SameGaloisType t1 t2 (e1.trans g) (e2.trans g) := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  exact ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, fun i => hval (g.symm i)⟩

theorem infra_73_sgt_uncommon
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {q q' : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    {e : q.idx ≃ ι} {e' : q'.idx ≃ ι}
    (h : SameGaloisType q q' e e') :
    SameGaloisType q q' (e.trans e'.symm) (Equiv.refl q'.idx) := by
  rcases h with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, hval⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hcomm, ?_⟩
  intro k
  have hv := hval (e' k)
  rw [Equiv.symm_apply_apply] at hv
  exact hv

/-- Every bounded query from `B` is a sequence-move of a query from `A`, for some long
approximation sequence of `p`. -/
theorem infra_73_tied_move
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hpν : p.ν = μ) (hidx : #p.idx ≤ σ)
    {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hβ : #β ≤ P.g σ + ls K) :
    ∃ (seq : ApproximationSequence p)
      (Y0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A)),
      seq.τ + ℵ₀ < #(seq.κIndex) ∧ #β ≤ seq.τ ∧ #β < μ ∧ infra_73_isMove f seq Y Y0 := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #p.idx < μ := hidx.trans_lt hσlt
  obtain ⟨seq, -, -, hτ, hlong⟩ := infra_73_sequence_rec P σ hσ hμ hrec hσSucc p hpν hidx
  have hβμ : #β < μ := by
    have hg : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    exact hβ.trans_lt (add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ))
  let xs : seq.κIndex × p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun ij => seq.family ij.1 ij.2
  obtain ⟨Y0, ψ, hψiso, hψxs, hψY⟩ := infra_73_move_iso f hf xs Y seq.concat_bounded hβμ
  have hψ : P.scheme.permitted (X := A) (Y := B) ψ :=
    P.scheme.structural_iso A B ψ hψiso
  refine ⟨seq, Y0, hlong, hβ.trans hτ, hβμ, ?_⟩
  intro i
  have hcard : #(p.idx ⊕ β) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hidxμ hβμ
  have h := P.scheme.diagram_preserved A B ψ hψ (seqJoint (seq.family i) Y0) hcard hcard
  have heq : (fun t => (⟨(seqJoint (seq.family i) Y0 t).1,
        ψ.onVertex _ (seqJoint (seq.family i) Y0 t).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) =
      seqJoint (fun j => ⟨(seq.family i j).1, f.onVertex _ (seq.family i j).2⟩) Y := by
    funext t
    cases t with
    | inl j => exact hψxs (i, j)
    | inr k => exact (hψY k).symm
  rw [heq] at h
  exact h

/-- Two tied-free extensions of `p` over `B` have the same Galois type over `B`. -/
theorem infra_73_tied_unique
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hpν : p.ν = μ) (hidx : #p.idx ≤ σ)
    (pB1 pB2 : TupleOver K oneVertexShape P.scheme hμ B)
    (eB1 : p.idx ≃ pB1.idx) (eB2 : p.idx ≃ pB2.idx)
    (h1ν : pB1.ν = μ) (h2ν : pB2.ν = μ)
    (hT1 : IsTiedFree f p pB1 eB1) (hT2 : IsTiedFree f p pB2 eB2) :
    SameGaloisType pB1 pB2 eB1.symm eB2.symm := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidx1 : #pB1.idx ≤ σ := by rw [← Cardinal.mk_congr eB1]; exact hidx
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ :=
    infra_73_differing_test P σ hσ hμ hrec hσSucc pB1 pB2 eB1.symm eB2.symm h1ν h2ν
      hidx1 (hidx1.trans_lt hσlt) hneq
  apply hnot
  obtain ⟨seq, Y0, hlong, hβτ, hβμ, hmv⟩ :=
    infra_73_tied_move P σ hσ hμ hrec hσSucc f hf p hpν hidx Y hβ
  have d1 := hT1 seq Y Y0 hlong hβτ hβμ hmv
  have d2 := hT2 seq Y Y0 hlong hβτ hβμ hmv
  have d := P.scheme.diagram_trans pB1.host p.host pB2.host _ _ _
    (P.scheme.diagram_symm p.host pB1.host _ _ d1) d2
  exact infra_73_diagramEq_of_eq d (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)

/-- `hExt` read on any bounded parameter list of `A`, aligned along `e`. -/
theorem infra_73_ext_align
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hBν : qB.ν = μ) (hidxμ : #q.idx < μ)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    {γ : Type u} (Y : γ → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hγ : #γ < μ) :
    P.scheme.DiagramEq (X := q.host) (Y := qB.host)
      (alignJoint e (typeJoint (p := q) Y))
      (alignJoint (eB.symm.trans e) (typeJoint (p := qB.restrict f hf) Y)) := by
  have hqBidx : #qB.idx < μ := by
    rw [← Cardinal.mk_congr eB]; exact hidxμ
  have h0 := infra_72_diagramEq_of_sameGalois (P := P) hExt Y hqν hBν hqBidx hγ
  let eq : qB.idx ⊕ γ ≃ (uIdx ⊕ cIdx) ⊕ γ := Equiv.sumCongr (eB.symm.trans e) (Equiv.refl γ)
  have h1 := (P.scheme.diagram_reindex q.host qB.host eq _ _).mp h0
  have hL : (fun b => alignJoint eB (typeJoint (p := q) Y) (eq.symm b)) =
      alignJoint e (typeJoint (p := q) Y) := by
    funext b
    cases b with
    | inl k =>
      simp only [eq, alignJoint, typeJoint, Equiv.sumCongr_symm, Equiv.sumCongr_apply,
        Sum.map_inl, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
        Equiv.symm_apply_apply]
    | inr w => rfl
  have hR : (fun b => alignJoint (Equiv.refl qB.idx)
        (typeJoint (p := qB.restrict f hf) Y) (eq.symm b)) =
      alignJoint (eB.symm.trans e) (typeJoint (p := qB.restrict f hf) Y) := by
    funext b
    cases b <;> rfl
  exact infra_73_diagramEq_of_eq h1 (congrFun hL) (congrFun hR)

set_option maxHeartbeats 3200000 in
/-- **English Lemma 7.2, clause 2 (over-`B` isolation).** If `W` isolates `q` relative to
`u` and `qB` extends `q` with tied-free `u`-marginal, then the pushed fragment `f W`
isolates `qB` relative to `u` over `B`. -/
theorem infra_72_over_B_isolation
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hBν : qB.ν = μ)
    (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    {wι : Type u} (W : wι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hW : IsIsolatingFragment q e W)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    (hMargTied : IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e))
      (Equiv.refl uIdx)) :
    IsIsolatingFragment qB (eB.symm.trans e) (pushParams f W) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have huidx : #uIdx ≤ #q.idx :=
    Cardinal.mk_le_of_injective (f := fun i : uIdx => e.symm (Sum.inl i))
      (fun a b h => Sum.inl.inj (e.symm.injective h))
  have huμ : #uIdx < μ := huidx.trans_lt hidxμ
  refine ⟨hW.1, ?_⟩
  intro q'' e'' hν'' hMargB hDEW
  let qA : TupleOver K oneVertexShape P.scheme hμ A := q''.restrict f hf
  -- (a) Same `u`-marginal over `A`.
  have hMargA : SameGaloisType (q.marginal e) (qA.marginal e'')
      (Equiv.refl uIdx) (Equiv.refl uIdx) := by
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ :=
      infra_73_differing_test P σ hσ hμ hrec hσSucc (q.marginal e) (qA.marginal e'')
        (Equiv.refl uIdx) (Equiv.refl uIdx) hqν hν'' (huidx.trans hidx) huμ hneq
    apply hnot
    obtain ⟨seqU, -, -, hτU, hlongU⟩ :=
      infra_73_sequence_rec P σ hσ hμ hrec hσSucc (q.marginal e) hqν (huidx.trans hidx)
    have hβμ : #β < μ := by
      have hg : P.g σ < μ :=
        (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
      exact hβ.trans_lt (add_lt_of_lt (P.aleph0_le hμ) hg (P.ls_lt hμ))
    have hmv : infra_73_isMove f seqU (pushParams f Y) Y := by
      intro i
      have hcard : #(uIdx ⊕ β) < μ := by
        rw [mk_sum, lift_id, lift_id]
        exact add_lt_of_lt (P.aleph0_le hμ) huμ hβμ
      have h := P.scheme.diagram_preserved A B f hf (seqJoint (seqU.family i) Y) hcard hcard
      exact infra_73_diagramEq_of_eq h (fun _ => rfl) (fun t => by cases t <;> rfl)
    have d1 := hMargTied seqU (pushParams f Y) Y hlongU (hβ.trans hτU) hβμ hmv
    have d2 := infra_72_diagramEq_of_sameGalois (P := P) hMargB (pushParams f Y) hBν hν''
      huμ hβμ
    have d1' := infra_73_diagramEq_of_eq d1 (fun t => (by cases t <;> rfl :
        typeJoint (p := q.marginal e) Y t = alignJoint (Equiv.refl uIdx)
          (typeJoint (p := q.marginal e) Y) t))
      (fun t => (by cases t <;> rfl :
        infra_612_anchored (Equiv.refl uIdx) (qB.marginal (eB.symm.trans e)).incl
          (qB.marginal (eB.symm.trans e)).val (pushParams f Y) t =
        alignJoint (Equiv.refl uIdx) (typeJoint (p := qB.marginal (eB.symm.trans e))
          (pushParams f Y)) t))
    have d := P.scheme.diagram_trans q.host qB.host q''.host _ _ _ d1' d2
    exact infra_73_diagramEq_of_eq d (fun _ => rfl) (fun t => by cases t <;> rfl)
  -- (b) Same diagram over `W`.
  have hWA : P.scheme.DiagramEq (X := q.host) (Y := qA.host)
      (alignJoint e (typeJoint (p := q) W)) (alignJoint e'' (typeJoint (p := qA) W)) := by
    have d0 := infra_73_ext_align f hf q qB eB e hqν hBν hidxμ hExt W hW.1
    have d0' := infra_73_diagramEq_of_eq d0 (fun _ => rfl)
      (fun t => (by cases t <;> rfl :
        alignJoint (eB.symm.trans e) (typeJoint (p := qB.restrict f hf) W) t =
        alignJoint (eB.symm.trans e) (typeJoint (p := qB) (pushParams f W)) t))
    have d := P.scheme.diagram_trans q.host qB.host q''.host _ _ _ d0' hDEW
    exact infra_73_diagramEq_of_eq d (fun _ => rfl) (fun t => by cases t <;> rfl)
  -- (c) Isolation over `A`.
  have hSameA : SameGaloisType q qA e e'' := hW.2 qA e'' hν'' hMargA hWA
  let eB'' : q.idx ≃ q''.idx := e.trans e''.symm
  have hExt'' : SameGaloisType q (q''.restrict f hf) eB'' (Equiv.refl q''.idx) :=
    infra_73_sgt_uncommon hSameA
  have he'' : eB''.symm.trans e = e'' := by
    ext k
    simp [eB'']
  -- (d) The competitor's `u`-marginal is tied free.
  have hMargTied'' : IsTiedFree f (q.marginal e) (q''.marginal (eB''.symm.trans e))
      (Equiv.refl uIdx) := by
    rw [he'']
    intro seq ι Z Z0 hlong hιτ hιμ hmove
    have d1 := hMargTied seq Z Z0 hlong hιτ hιμ hmove
    have d2 := infra_72_diagramEq_of_sameGalois (P := P) hMargB Z hBν hν'' huμ hιμ
    have d1' := infra_73_diagramEq_of_eq d1 (fun _ => rfl)
      (fun t => (by cases t <;> rfl :
        infra_612_anchored (Equiv.refl uIdx) (qB.marginal (eB.symm.trans e)).incl
          (qB.marginal (eB.symm.trans e)).val Z t =
        alignJoint (Equiv.refl uIdx) (typeJoint (p := qB.marginal (eB.symm.trans e)) Z) t))
    have d := P.scheme.diagram_trans q.host qB.host q''.host _ _ _ d1' d2
    exact infra_73_diagramEq_of_eq d (fun _ => rfl) (fun t => by cases t <;> rfl)
  -- (e) Both extensions are tied free; tied-free extensions are unique.
  have hIso : IsRelativelyIsolated q e := IsRelativelyIsolated.of_fragment hW
  have hT : IsTiedFree f q qB eB :=
    infra_73_tied_of_isolated P σ hσ hμ hrec hσSucc f hf q qB eB e hqν hBν hidx hidxμ
      hIso hExt hMargTied
  have hT'' : IsTiedFree f q q'' eB'' :=
    infra_73_tied_of_isolated P σ hσ hμ hrec hσSucc f hf q q'' eB'' e hqν hν'' hidx hidxμ
      hIso hExt'' hMargTied''
  have hU := infra_73_tied_unique P σ hσ hμ hrec hσSucc f hf q hqν hidx qB q'' eB eB''
    hBν hν'' hT hT''
  have hU' := infra_73_sgt_equiv_trans hU e
  rw [he''] at hU'
  exact hU'

/-- Over-`B` relative isolation of a tied-free extension of a relatively isolated type. -/
theorem infra_72_over_B_isRelativelyIsolated
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : q.idx ≃ qB.idx)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hBν : qB.ν = μ)
    (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (hIso : IsRelativelyIsolated q e)
    (hExt : SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx))
    (hMargTied : IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e))
      (Equiv.refl uIdx)) :
    IsRelativelyIsolated qB (eB.symm.trans e) := by
  obtain ⟨wι, W, hW⟩ := IsIsolatingFragment.of_relativelyIsolated hIso
  exact IsRelativelyIsolated.of_fragment
    (infra_72_over_B_isolation P σ hσ hμ hrec hσSucc f hf q qB eB e hqν hBν hidx hidxμ W hW
      hExt hMargTied)

/-- **Lemma 7.2 (English form).** Projection of a relatively isolated type stays relatively
isolated; an extension `qB` of `q` whose `u`-marginal is tied free (the English free
extension `tp(u/A)_{B^{fr}}`) is itself tied free (`IsTiedFree`, the actual joint is the
free lift on every sequence-move) and is relatively isolated over `B`. -/
theorem infra_72_lemma_tied (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
        {uIdx c0Idx c1Idx : Type u}
        (e : q.idx ≃ uIdx ⊕ (c0Idx ⊕ c1Idx)),
        q.ν = μ → #q.idx ≤ σ → #q.idx < μ →
        IsRelativelyIsolated q e →
        IsRelativelyIsolated (q.projectUC0 e)
            (projectDecomp (uIdx := uIdx) (c0Idx := c0Idx)) ∧
          ∀ (B : P.scheme.Object μ (Tail.mem hT hμ))
            (f : SystemArrow K oneVertexShape
              (P.scheme.asSystem (Tail.mem hT hμ) A)
              (P.scheme.asSystem (Tail.mem hT hμ) B))
            (hf : P.scheme.permitted (X := A) (Y := B) f)
            (qB : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
            (eB : q.idx ≃ qB.idx),
            qB.ν = μ →
            SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) →
            IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e)) (Equiv.refl uIdx) →
            IsTiedFree f q qB eB ∧ IsRelativelyIsolated qB (eB.symm.trans e) := by
  refine ⟨infra_72_tailSet P σ, infra_72_tail P σ hσ, ?_⟩
  intro μ hμ A q uIdx c0Idx c1Idx e hqν hidx hidxμ hRel
  have hmem : μ ∈ infra_72_tailSet P σ := hμ
  have hrec : μ ∈ recursionClosedLevels P σ := hmem.1
  have hσSucc : Order.succ σ ≤ μ := hmem.2
  have hμel : μ ∈ P.eligible := Tail.mem (infra_72_tail P σ hσ) hμ
  obtain ⟨ι, Ziso, hFrag⟩ := IsIsolatingFragment.of_relativelyIsolated hRel
  have hιμ : #ι < μ := hFrag.1
  have huc0 : #(uIdx ⊕ c0Idx) < μ := by
    have hle : #(uIdx ⊕ c0Idx) ≤ #(uIdx ⊕ (c0Idx ⊕ c1Idx)) := mk_uc0_le_three
    exact (hle.trans (Cardinal.mk_congr e).symm.le).trans_lt hidxμ
  have hc1 : #c1Idx < μ := by
    have hle : #c1Idx ≤ #(uIdx ⊕ (c0Idx ⊕ c1Idx)) := mk_c1_le_three
    exact (hle.trans (Cardinal.mk_congr e).symm.le).trans_lt hidxμ
  refine ⟨?_, ?_⟩
  · exact IsRelativelyIsolated.of_fragment
      (infra_721_projection (P := P) q e Ziso hFrag hqν huc0 hc1 hιμ)
  · intro B f hf qB eB hBν hExt hMargTied
    exact ⟨infra_73_tied_of_isolated P σ hσ hμel hrec hσSucc f hf q qB eB e hqν hBν hidx
        hidxμ hRel hExt hMargTied,
      infra_72_over_B_isRelativelyIsolated P σ hσ hμel hrec hσSucc f hf q qB eB e hqν hBν
        hidx hidxμ hRel hExt hMargTied⟩

/-- Relative isolation at a tail level yields an isolating fragment of size at most `h(σ)`,
provided extensions with free marginal have tied-free `u`-marginal (`hFreeTied`). The
dichotomy's untied branch is an extension with free marginal and `¬ IsTiedFree`;
`infra_73_tied_of_isolated` forbids it once its marginal is tied free. Discharging
`hFreeTied` for the `infra_73_alt2` extension is open (`infra_73_alt2_tied_marginal`). -/
theorem infra_73_uniform_of_isolated
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ)
    {A : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)}
    (q : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) A)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (hIso : IsRelativelyIsolated q e)
    (hFreeTied : ∀ (B : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
      (hf : P.scheme.permitted (X := A) (Y := B) f)
      (qB : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) B)
      (eB : q.idx ≃ qB.idx), qB.ν = μ →
      SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) →
      IsFreeLift (q.marginal e) (qB.marginal (eB.symm.trans e)) f hf (Equiv.refl uIdx) →
      IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e)) (Equiv.refl uIdx)) :
    ∃ (ι : Type u)
      (Z : ι → Occurrence K oneVertexShape
        (P.scheme.asSystem (Tail.mem (infra_73_tail P σ hσ) hμT) A)),
      #ι ≤ infra_73_h P σ ∧ IsIsolatingFragment q e Z := by
  have hμel : μ ∈ P.eligible := Tail.mem (infra_73_tail P σ hσ) hμT
  have hrec : μ ∈ recursionClosedLevels P σ := infra_73_tail_rec hμT
  have hσSucc : Order.succ σ ≤ μ := infra_73_tail_succ hμT
  obtain ⟨seq, hτ, hκ, hτge, hlong⟩ :=
    infra_73_sequence P σ hσ hμel hμT q hqν hidx
  have hτμ : seq.τ < μ := by
    rw [hτ]
    exact (Order.lt_succ _).trans (infra_73_h_lt hμel hμT)
  have hfamμ : #(seq.κIndex × q.idx) < μ :=
    (infra_73_family_card seq hσ hidx hκ).trans_lt (infra_73_h_lt hμel hμT)
  by_cases hFam : IsIsolatingFragment q e (infra_73_family seq)
  · exact ⟨seq.κIndex × q.idx, infra_73_family seq,
      infra_73_family_card seq hσ hidx hκ, hFam⟩
  · obtain ⟨q', e', hq'ν, _, hDE, hneq⟩ :=
      infra_73_competitor q e (infra_73_family seq) hfamμ hFam
    obtain ⟨B, f, hf, qB, eB, hBν, hExt, hFree, hUntied⟩ :=
      infra_73_alt2 P σ hσ hμel hrec hσSucc q e hqν hidx hidxμ seq hτge hlong hτμ
        hfamμ q' e' hq'ν hDE hneq
    exact False.elim (hUntied (infra_73_tied_of_isolated P σ hσ hμel hrec hσSucc f hf q qB eB
      e hqν hBν hidx hidxμ hIso hExt (hFreeTied B f hf qB eB hBν hExt hFree)))

/-! ## Packaging -/

set_option maxHeartbeats 1600000 in
theorem infra_73_lemma
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ h : Cardinal.{u} → Cardinal.{u}, ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
        {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx),
        q.ν = μ → #q.idx ≤ σ → #q.idx < μ →
        (∃ (ι : Type u)
          (Z : ι → Occurrence K oneVertexShape
            (P.scheme.asSystem (Tail.mem hT hμ) A)),
          #ι ≤ h σ ∧ IsIsolatingFragment q e Z) ∨
        (∃ (B : P.scheme.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K oneVertexShape
            (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
          (hf : P.scheme.permitted (X := A) (Y := B) f)
          (qB : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
          (eB : q.idx ≃ qB.idx),
          SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) ∧
          IsFreeLift (q.marginal e) (qB.marginal (eB.symm.trans e)) f hf
            (Equiv.refl uIdx) ∧
          ¬ IsTiedFree f q qB eB) := by
  refine ⟨infra_73_h P, infra_73_tailSet P σ, infra_73_tail P σ hσ, ?_⟩
  intro μ hμ A q uIdx cIdx e hqν hidx hidxμ
  have hμel : μ ∈ P.eligible := Tail.mem (infra_73_tail P σ hσ) hμ
  have hrec : μ ∈ recursionClosedLevels P σ := infra_73_tail_rec hμ
  have hσSucc : Order.succ σ ≤ μ := infra_73_tail_succ hμ
  obtain ⟨seq, hτ, hκ, hτge, hlong⟩ :=
    infra_73_sequence P σ hσ hμel hμ q hqν hidx
  have hτμ : seq.τ < μ := by
    rw [hτ]
    exact (Order.lt_succ _).trans (infra_73_h_lt hμel hμ)
  have hfamμ : #(seq.κIndex × q.idx) < μ :=
    (infra_73_family_card seq hσ hidx hκ).trans_lt (infra_73_h_lt hμel hμ)
  by_cases hIso : IsIsolatingFragment q e (infra_73_family seq)
  · exact Or.inl ⟨seq.κIndex × q.idx, infra_73_family seq,
      infra_73_family_card seq hσ hidx hκ, hIso⟩
  · obtain ⟨q', e', hq'ν, _, hDE, hneq⟩ :=
      infra_73_competitor q e (infra_73_family seq) hfamμ hIso
    obtain ⟨B, f, hf, qB, eB, _, hExt, hFree, hUntied⟩ :=
      infra_73_alt2 P σ hσ hμel hrec hσSucc q e hqν hidx hidxμ seq hτge hlong hτμ
        hfamμ q' e' hq'ν hDE hneq
    exact Or.inr ⟨B, f, hf, qB, eB, hExt, hFree, hUntied⟩

end
end
end AEC
