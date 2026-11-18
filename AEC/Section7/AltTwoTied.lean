module

public import AEC.Section7.TiedFreeLift

@[expose] public section

/-!
# Proposition 7.3, alternative 2 from a block arrow

English Prop 7.3 (block proof): "Set `A* = F(J₀ ∪ J) ≤ A` … The restrictions of `q₀` and `q₁`
to `A*` are equal", then "`q₀` is the free extension of `q₀ ↾ A*`" while `q₁` is not.
Here the block restriction is given as an arrow `g : A → A` fixing an approximation sequence
pointwise, with `q ↾ g ≡ q' ↾ g`. From that:

* `infra_73_restrict_fixed`: an arrow fixing a long approximation sequence of `q` pointwise
  does not change the type: `q ↾ g ≡ q`.
* `infra_73_tied_of_fixed`: such an arrow makes `q` the tied free extension of `q ↾ g`.
* `infra_73_tied_congr`: tied freeness is invariant under Galois equality of the extension.
* `infra_73_alt2_tied`: alternative 2 with tied `u`-marginal (`B := A`, `f := g`, `qB := q'`).
* `infra_73_uniform_of_block`: the English uniform shrink of Prop 7.3, given the block
  restriction (`Infra73BlockRestriction`, open board tip `infra_73_block_restriction`).
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

attribute [local instance] Classical.propDecidable

noncomputable section

variable {K : AbstractElementaryClass.{u}}

/-- Two small exception sets of a long index set miss a common index. -/
theorem infra_73_common_good {κ : Type u} {c : Cardinal.{u}} (S1 S2 : Set κ)
    (h1 : #S1 ≤ c + ℵ₀) (h2 : #S2 ≤ c + ℵ₀) (hκ : c + ℵ₀ < #κ) :
    ∃ i, i ∉ S1 ∧ i ∉ S2 := by
  by_contra h
  have hall : (Set.univ : Set κ) ⊆ S1 ∪ S2 := by
    intro i _
    by_contra hi
    simp only [Set.mem_union, not_or] at hi
    exact h ⟨i, hi⟩
  have hinf : ℵ₀ ≤ #κ := (le_add_self (a := ℵ₀) (b := c)).trans (le_of_lt hκ)
  have hle : #κ ≤ (c + ℵ₀) + (c + ℵ₀) := by
    rw [← mk_univ (α := κ)]
    exact (mk_le_mk_of_subset hall).trans ((mk_union_le _ _).trans (add_le_add h1 h2))
  exact (not_le_of_gt (add_lt_of_lt hinf hκ hκ)) hle

/-- An arrow fixing the copies pointwise keeps their joint with a query and its image. -/
theorem infra_73_fixed_joint
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := A) (Y := A) g)
    {idx β : Type u} (v : idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hv : ∀ j, (⟨(v j).1, g.onVertex _ (v j).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) = v j)
    (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hcard : #(idx ⊕ β) < μ) :
    P.scheme.DiagramEq (X := A) (Y := A) (seqJoint v Y) (seqJoint v (pushParams g Y)) := by
  have h := P.scheme.diagram_preserved A A g hg (seqJoint v Y) hcard hcard
  refine infra_73_diagramEq_of_eq h (fun _ => rfl) ?_
  intro t
  cases t with
  | inl j => exact hv j
  | inr k => rfl

/-- Over a fixing arrow the type of `q` on a query and on its image agree. -/
theorem infra_73_type_fixed
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := A) (Y := A) g)
    (hfix : ∀ i j, (⟨(seq.family i j).1, g.onVertex _ (seq.family i j).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) = seq.family i j)
    {β : Type u} (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    (hidxμ : #q.idx < μ) (hβμ : #β < μ)
    (hβτ : #β ≤ seq.τ) (hκ : #β + ℵ₀ < #(seq.κIndex)) :
    P.scheme.DiagramEq (X := q.host) (Y := q.host)
      (typeJoint (p := q) (pushParams g Y)) (typeJoint (p := q) Y) := by
  classical
  have hcard : #(q.idx ⊕ β) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hidxμ hβμ
  apply infra_610_type_eq_majority seq (pushParams g Y) (typeJoint (p := q) Y) _ hβτ hκ
  have hfew := infra_610_majority_eq_type seq Y hβτ
  refine le_trans (mk_le_mk_of_subset (s := {i : seq.κIndex | ¬ P.scheme.DiagramEq
      (X := A) (Y := q.host) (seqJoint (seq.family i) (pushParams g Y))
      (typeJoint (p := q) Y)})
    (t := {i : seq.κIndex | ¬ P.scheme.DiagramEq (X := A) (Y := q.host)
      (seqJoint (seq.family i) Y) (typeJoint (p := q) Y)}) ?_) hfew
  intro i hi hgood
  apply hi
  exact P.scheme.diagram_trans A A q.host _ _ _
    (P.scheme.diagram_symm A A _ _
      (infra_73_fixed_joint g hg (seq.family i) (hfix i) Y hcard)) hgood

/-- An arrow fixing a long approximation sequence of `q` pointwise keeps the type of `q`. -/
theorem infra_73_restrict_fixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (q : TupleOver K oneVertexShape P.scheme hμ A) (hqν : q.ν = μ) (hidx : #q.idx ≤ σ)
    (seq : ApproximationSequence q) (hτge : P.g σ + ls K ≤ seq.τ)
    (hlong : seq.τ + ℵ₀ < #(seq.κIndex))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := A) (Y := A) g)
    (hfix : ∀ i j, (⟨(seq.family i j).1, g.onVertex _ (seq.family i j).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) = seq.family i j) :
    SameGaloisType q (q.restrict g hg) (Equiv.refl q.idx) (Equiv.refl q.idx) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #q.idx < μ := hidx.trans_lt hσlt
  by_contra hneq
  obtain ⟨β, Y, hβ, hnot⟩ := infra_73_differing_test P σ hσ hμ hrec hσSucc q
    (q.restrict g hg) (Equiv.refl _) (Equiv.refl _) hqν hqν hidx hidxμ hneq
  apply hnot
  have hβμ : #β < μ := by
    have hgσ : P.g σ < μ :=
      (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
    exact hβ.trans_lt (add_lt_of_lt (P.aleph0_le hμ) hgσ (P.ls_lt hμ))
  have hβτ : #β ≤ seq.τ := hβ.trans hτge
  have hκ : #β + ℵ₀ < #(seq.κIndex) := (add_le_add hβτ le_rfl).trans_lt hlong
  have h := infra_73_type_fixed seq g hg hfix Y hidxμ hβμ hβτ hκ
  exact infra_73_diagramEq_of_eq (P.scheme.diagram_symm _ _ _ _ h)
    (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)

/-- The `u`-copies of an approximation sequence approximate the `u`-marginal. -/
def ApproximationSequence.marginalSeq
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {q : TupleOver K oneVertexShape P.scheme hμ A} {uIdx cIdx : Type u}
    (e : q.idx ≃ uIdx ⊕ cIdx) (seq : ApproximationSequence q) :
    ApproximationSequence (q.marginal e) where
  τ := seq.τ
  κIndex := seq.κIndex
  family i k := seq.family i (e.symm (Sum.inl k))
  concat_bounded := by
    have hρ : Function.Injective (fun k : uIdx => e.symm (Sum.inl k)) :=
      fun a b h => Sum.inl_injective (e.symm.injective h)
    exact lt_of_le_of_lt
      (mk_le_of_injective (Function.Injective.prodMap (f := id) injective_id hρ))
      seq.concat_bounded
  few_exceptions := fun Z hι =>
    seq.subtuple_uniform (fun k => e.symm (Sum.inl k))
      (fun a b h => Sum.inl_injective (e.symm.injective h)) Z hι

/-- Tied freeness is invariant under Galois equality of the extension over `B`. -/
theorem infra_73_tied_congr
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (qB qB' : TupleOver K oneVertexShape P.scheme hμ B)
    (eB : p.idx ≃ qB.idx) (eB' : p.idx ≃ qB'.idx)
    (hBν : qB.ν = μ) (hB'ν : qB'.ν = μ) (hidxμ : #p.idx < μ)
    (hT : IsTiedFree f p qB eB) (hS : SameGaloisType qB qB' eB.symm eB'.symm) :
    IsTiedFree f p qB' eB' := by
  intro seq ι Z Z0 hlong hιτ hιμ hmv
  have d1 := hT seq Z Z0 hlong hιτ hιμ hmv
  have d2 := infra_72_diagramEq_of_sameGalois (P := P) hS Z hBν hB'ν hidxμ hιμ
  have d2' : P.scheme.DiagramEq (X := qB.host) (Y := qB'.host)
      (infra_612_anchored eB qB.incl qB.val Z) (infra_612_anchored eB' qB'.incl qB'.val Z) :=
    infra_73_diagramEq_of_eq d2 (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ d1 d2'

/-- **Fixed sequences make `q` tied free over its restriction.** If `g : A → A` fixes a long
approximation sequence of `p` pointwise, then `p` itself is the tied free extension of
`p ↾ g` along `g` (English Prop 7.3: "`q₀` is the free extension of `q₀ ↾ A*`"). -/
theorem infra_73_tied_of_fixed
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p : TupleOver K oneVertexShape P.scheme hμ A) (hpν : p.ν = μ) (hidx : #p.idx ≤ σ)
    (seq : ApproximationSequence p) (hτge : P.g σ + ls K ≤ seq.τ)
    (hlong : seq.τ + ℵ₀ < #(seq.κIndex))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := A) (Y := A) g)
    (hfix : ∀ i j, (⟨(seq.family i j).1, g.onVertex _ (seq.family i j).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) = seq.family i j) :
    IsTiedFree g p p (Equiv.refl p.idx) := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #p.idx < μ := hidx.trans_lt hσlt
  obtain ⟨pT, eT, hTν, -, hTt⟩ := infra_610_tied_free_lift P σ hσ hμ hrec hσSucc g hg p hpν hidx
  have hTidx : #pT.idx ≤ σ := by rw [← Cardinal.mk_congr eT]; exact hidx
  have hS : SameGaloisType pT p eT.symm (Equiv.refl p.idx).symm := by
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ := infra_73_differing_test P σ hσ hμ hrec hσSucc pT p eT.symm
      (Equiv.refl p.idx).symm hTν hpν hTidx (hTidx.trans_lt hσlt) hneq
    apply hnot
    obtain ⟨seq0, Y0, hlong0, hβτ0, hβμ, hmv0⟩ :=
      infra_73_tied_move P σ hσ hμ hrec hσSucc g hg p hpν hidx Y hβ
    have d1 := hTt seq0 Y Y0 hlong0 hβτ0 hβμ hmv0
    obtain ⟨Z1, hm0, hm1⟩ := infra_610_common_move g hg seq0 seq Y hidxμ hβμ
    have hκ0 : #β + ℵ₀ < #(seq0.κIndex) := (add_le_add hβτ0 le_rfl).trans_lt hlong0
    have d2 := infra_73_moves_agree g seq0 Y Y0 Z1 hmv0 hm0 hβτ0 hκ0
    have hβτ : #β ≤ seq.τ := hβ.trans hτge
    have hκ : #β + ℵ₀ < #(seq.κIndex) := (add_le_add hβτ le_rfl).trans_lt hlong
    have d3 : P.scheme.DiagramEq (X := p.host) (Y := p.host)
        (typeJoint (p := p) Z1) (typeJoint (p := p) Y) := by
      apply infra_610_type_eq_majority seq Z1 (typeJoint (p := p) Y) _ hβτ hκ
      refine le_trans (mk_le_mk_of_subset (s := {i : seq.κIndex | ¬ P.scheme.DiagramEq
          (X := A) (Y := p.host) (seqJoint (seq.family i) Z1) (typeJoint (p := p) Y)})
        (t := {i : seq.κIndex | ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Y) (typeJoint (p := p) Y)}) ?_)
        (infra_610_majority_eq_type seq Y hβτ)
      intro i hi hgood
      apply hi
      have hm' : P.scheme.DiagramEq (X := A) (Y := A)
          (seqJoint (seq.family i) Z1) (seqJoint (seq.family i) Y) :=
        infra_73_diagramEq_of_eq (hm1 i) (fun _ => rfl) (fun t => by
          cases t with
          | inl j => exact hfix i j
          | inr k => rfl)
      exact P.scheme.diagram_trans A A p.host _ _ _ hm' hgood
    have d := P.scheme.diagram_trans pT.host p.host p.host _ _ _
      (P.scheme.diagram_symm p.host pT.host _ _ d1)
      (P.scheme.diagram_trans p.host p.host p.host _ _ _ d2 d3)
    exact infra_73_diagramEq_of_eq d (fun t => by cases t <;> rfl)
      (fun t => by cases t <;> rfl)
  exact infra_73_tied_congr g p pT p eT (Equiv.refl p.idx) hTν hpν hidxμ hTt hS

/-- **Proposition 7.3, alternative 2 with tied marginal.** Let `q'` be a competitor of `q`
(same `u`-marginal, different type). If some arrow `g : A → A` fixes a long approximation
sequence of `q` pointwise and `q ↾ g ≡ q' ↾ g` (English: the restrictions to the block
`A* = F(J₀ ∪ J)` are equal), then `q'` over `A` is an extension of `q ↾ g` along `g` whose
`u`-marginal is the tied free extension while the joint is not tied free. -/
theorem infra_73_alt2_tied
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ)
    (seq : ApproximationSequence q) (hτge : P.g σ + ls K ≤ seq.τ)
    (hlong : seq.τ + ℵ₀ < #(seq.κIndex))
    (q' : TupleOver K oneVertexShape P.scheme hμ A) (e' : q'.idx ≃ uIdx ⊕ cIdx)
    (hq'ν : q'.ν = μ)
    (hMarg : SameGaloisType (q.marginal e) (q'.marginal e') (Equiv.refl uIdx) (Equiv.refl uIdx))
    (hneq : ¬ SameGaloisType q q' e e')
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := A) (Y := A) g)
    (hfix : ∀ i j, (⟨(seq.family i j).1, g.onVertex _ (seq.family i j).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ A)) = seq.family i j)
    (hres : SameGaloisType (q.restrict g hg) (q'.restrict g hg) e e') :
    ∃ (B : P.scheme.Object μ hμ)
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
      (hf : P.scheme.permitted (X := A) (Y := B) f)
      (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : q.idx ≃ qB.idx),
      qB.ν = μ ∧
      SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) ∧
      IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e)) (Equiv.refl uIdx) ∧
      ¬ IsTiedFree f q qB eB := by
  classical
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hidxμ : #q.idx < μ := hidx.trans_lt hσlt
  have hρ : Function.Injective (fun k : uIdx => e.symm (Sum.inl k)) :=
    fun a b h => Sum.inl_injective (e.symm.injective h)
  have hpidx : #uIdx ≤ σ := (mk_le_of_injective hρ).trans hidx
  let eB : q.idx ≃ q'.idx := e.trans e'.symm
  have heB : eB.symm.trans e = e' := by
    ext k
    simp [eB]
  refine ⟨A, g, hg, q', eB, hq'ν, ?_, ?_, ?_⟩
  · have h12 := infra_73_restrict_fixed P σ hσ hμ hrec hσSucc q hqν hidx seq hτge hlong g hg hfix
    have h32 : SameGaloisType (q.restrict g hg) (q'.restrict g hg) (Equiv.refl q.idx) eB.symm :=
      SameGaloisType.swap_refl (infra_73_sgt_uncommon hres)
    have h := SameGaloisType.trans_via (t1 := q) (t2 := q.restrict g hg)
      (t3 := q'.restrict g hg) h12 h32 σ hσ hσlt hidx hrec hqν hqν hq'ν
    exact h
  · rw [heB]
    have hTp := infra_73_tied_of_fixed P σ hσ hμ hrec hσSucc (q.marginal e) hqν hpidx
      (seq.marginalSeq e) hτge hlong g hg (fun i k => hfix i (e.symm (Sum.inl k)))
    exact infra_73_tied_congr g (q.marginal e) (q.marginal e) (q'.marginal e')
      (Equiv.refl uIdx) (Equiv.refl uIdx) hqν hq'ν (hpidx.trans_lt hσlt) hTp hMarg
  · intro hT
    have hTq := infra_73_tied_of_fixed P σ hσ hμ hrec hσSucc q hqν hidx seq hτge hlong g hg hfix
    have hU := infra_73_tied_unique P σ hσ hμ hrec hσSucc g hg q hqν hidx q' q eB
      (Equiv.refl q.idx) hq'ν hqν hT hTq
    apply hneq
    have h1 := infra_73_sgt_equiv_trans hU.symm e
    have hl : (Equiv.refl q.idx).symm.trans e = e := by
      ext k
      rfl
    rw [hl, heB] at h1
    exact h1

/-- **English Prop 7.3 block restriction** (open board tip `infra_73_block_restriction`).
At every tail level, `q` has a long approximation sequence and a fragment `Z₀` of size at
most `h(σ)` (English: the term values on `J₀`, which contains the supports of the
approximation lists and the initial segments of the candidate blocks) such that every
competitor `q'` agreeing with `q` on `Z₀` with the same `u`-marginal has the same
restriction as `q` to a block copy `A* = g(A)` of `A` containing the sequence pointwise. -/
def Infra73BlockRestriction (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) : Prop :=
  ∀ μ (hμT : μ ∈ infra_73_tailSet P σ)
    (A : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
    (q : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) A)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx),
    q.ν = μ → #q.idx ≤ σ →
    ∃ seq : ApproximationSequence q, P.g σ + ls K ≤ seq.τ ∧ seq.τ + ℵ₀ < #(seq.κIndex) ∧
    ∃ (ι : Type u) (Z : ι → Occurrence K oneVertexShape
        (P.scheme.asSystem (Tail.mem (infra_73_tail P σ hσ) hμT) A)),
      #ι ≤ infra_73_h P σ ∧
      ∀ (q' : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) A)
        (e' : q'.idx ≃ uIdx ⊕ cIdx), q'.ν = μ →
        SameGaloisType (q.marginal e) (q'.marginal e') (Equiv.refl uIdx) (Equiv.refl uIdx) →
        P.scheme.DiagramEq (X := q.host) (Y := q'.host)
          (alignJoint e (typeJoint (p := q) Z)) (alignJoint e' (typeJoint (p := q') Z)) →
        ∃ (g : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ A))
          (hg : P.scheme.permitted (X := A) (Y := A) g),
          (∀ i j, (⟨(seq.family i j).1, g.onVertex _ (seq.family i j).2⟩ :
              Occurrence K oneVertexShape (P.scheme.asSystem _ A)) = seq.family i j) ∧
          SameGaloisType (q.restrict g hg) (q'.restrict g hg) e e'

/-- **English Prop 7.3, uniform shrink, from the block restriction.** A relatively isolated
`q` at a tail level has an isolating fragment of size at most `h(σ)`. The untied
alternative is ruled out by `infra_73_tied_of_isolated`, since the block extension of
`infra_73_alt2_tied` has tied-free `u`-marginal. -/
theorem infra_73_uniform_of_block
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (hBlock : Infra73BlockRestriction P σ hσ)
    {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ)
    {A : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)}
    (q : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) A)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (hIso : IsRelativelyIsolated q e) :
    ∃ (ι : Type u)
      (Z : ι → Occurrence K oneVertexShape
        (P.scheme.asSystem (Tail.mem (infra_73_tail P σ hσ) hμT) A)),
      #ι ≤ infra_73_h P σ ∧ IsIsolatingFragment q e Z := by
  have hμel : μ ∈ P.eligible := Tail.mem (infra_73_tail P σ hσ) hμT
  have hrec : μ ∈ recursionClosedLevels P σ := infra_73_tail_rec hμT
  have hσSucc : Order.succ σ ≤ μ := infra_73_tail_succ hμT
  obtain ⟨seq, hτge, hlong, ι, Z, hι, hZ⟩ := hBlock μ hμT A q e hqν hidx
  have hιμ : #ι < μ := hι.trans_lt (infra_73_h_lt hμel hμT)
  by_cases hFrag : IsIsolatingFragment q e Z
  · exact ⟨ι, Z, hι, hFrag⟩
  · obtain ⟨q', e', hq'ν, hMarg, hDE, hneq⟩ := infra_73_competitor q e Z hιμ hFrag
    obtain ⟨g, hg, hfix, hres⟩ := hZ q' e' hq'ν hMarg hDE
    obtain ⟨B, f, hf, qB, eB, hBν, hExt, hTied, hUntied⟩ :=
      infra_73_alt2_tied P σ hσ hμel hrec hσSucc q e hqν hidx seq hτge hlong q' e' hq'ν
        hMarg hneq g hg hfix hres
    exact False.elim (hUntied (infra_73_tied_of_isolated P σ hσ hμel hrec hσSucc f hf q qB eB
      e hqν hBν hidx hidxμ hIso hExt hTied))

/-- **Proposition 7.3 (English uniform form), given the block restriction.** -/
theorem proposition_7_3_uniform_of_block
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (hBlock : Infra73BlockRestriction P σ hσ) :
    ∃ h : Cardinal.{u} → Cardinal.{u}, ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
        {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx),
        q.ν = μ → #q.idx ≤ σ → #q.idx < μ → IsRelativelyIsolated q e →
        ∃ (ι : Type u)
          (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem (Tail.mem hT hμ) A)),
          #ι ≤ h σ ∧ IsIsolatingFragment q e Z :=
  ⟨infra_73_h P, infra_73_tailSet P σ, infra_73_tail P σ hσ,
    fun _ hμ _ q _ _ e hqν hidx hidxμ hIso =>
      infra_73_uniform_of_block P σ hσ hBlock hμ q e hqν hidx hidxμ hIso⟩

end
end
end AEC
