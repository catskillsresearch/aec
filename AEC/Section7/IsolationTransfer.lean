module

public import AEC.Section7.ClosureLevel

@[expose] public section

/-!
# Prop 7.8: isolation transfer from `X_i` to the shrunk pair `A ≤ U` (`infra_78_isolation_transfer`)

Paper (Prop 7.8 proof, last paragraph): "The large type is isolated by the choice of `i`. Its
uniform fragment has size at most `h(|b,c| + ℵ₀) < λ`, so Lemma 7.6 gives isolation over `A`.
Finally, `I_p` still determines the marginal on `b` ... Bounded diagram homogeneity gives an
isomorphism `A ≃ X` carrying these anchors to themselves. Transport of approximation
evaluations carries `tp(b/A)` to `p`. Renaming `U` along this isomorphism gives the asserted
extension of the original `X`."

Cycle 61 tools (proved):
* `infra_78_tiedFreeMixed_host_transfer`: tied mixed freeness moves between two tuples over
  the same small base whose hosts are linked by a permitted arrow commuting with the base
  inclusions (here: `tp(b,c/A)` computed in the level-`λ` section `U` versus computed in `Y_i`).
  Only injective (equivalence) reindexing is used.
* `infra_78_anchor_iso`: bounded diagram homogeneity (`diagram_iso`): two same-level objects
  whose bounded anchor lists have the same image in a common object are isomorphic by a
  structural isomorphism carrying one anchor list to the other.
* `infra_78_isolation_over_shrink`, `infra_78_isolation_over_A`: Lemma 7.6 at the shrink —
  at the isolated stage, `tp(b, c / A)` (computed in the level-`λ` section `U`) is relatively
  isolated over `b` for every `c ⊆ U`, `|c| ≤ θ` (repetitions allowed).

Tracked elsewhere: `infra_78_iso_rename` (done, `IsoRename.lean`) and `infra_78_marginal_anchor`
(split cycle 63, `MarginalAnchor.lean`: done for `p` realized at the base level; the general host
level is `infra_78_marginal_general_level`).
-/

universe u

open Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Host transfer of mixed tied freeness (proved).** -/
theorem infra_78_tiedFreeMixed_host_transfer {P : SingleModelData K} {ν μ : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (p₁ p₂ : TupleOver K oneVertexShape P.scheme hν A)
    (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p₂.idx ≃ qB.idx)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem p₁.hν p₁.host)
      (P.scheme.asSystem p₂.hν p₂.host))
    (hh : P.scheme.permitted (X := p₁.host) (Y := p₂.host) h) (e : p₁.idx ≃ p₂.idx)
    (hincl : ∀ x, h.onVertex PUnit.unit (p₁.incl.onVertex PUnit.unit x) =
      p₂.incl.onVertex PUnit.unit x)
    (hval : ∀ k, p₂.val (e k) = ⟨(p₁.val k).1, h.onVertex (p₁.val k).1 (p₁.val k).2⟩)
    (hidx : #p₁.idx < ν) (hν₁ : ν ≤ p₁.ν) (hν₂ : ν ≤ p₂.ν)
    (H : IsTiedFreeMixed f p₂ qB eB) :
    IsTiedFreeMixed f p₁ qB (e.trans eB) := by
  classical
  intro seq ι Z Z0 hlen hιτ hιν hmove
  have hν0 : ℵ₀ ≤ ν := P.aleph0_le hν
  let seqW : ApproximationSequence p₁ :=
    { τ := #ι
      κIndex := seq.κIndex
      family := seq.family
      concat_bounded := seq.concat_bounded
      few_exceptions := fun Z' hZ' => seq.few_exceptions Z' (hZ'.trans hιτ) }
  have hsum : #p₁.idx + #ι < ν := Cardinal.add_lt_of_lt hν0 hidx hιν
  let s2 := infra_78_seq_host_transfer p₁ p₂ h hh e hincl hval seqW (hsum.trans_le hν₁)
    (hsum.trans_le hν₂)
  have hmove2 : infra_78_isMoveMixed f s2 Z Z0 := fun i =>
    infra_612_dEq_transport (hmove i) (Equiv.sumCongr e.symm (Equiv.refl ι))
      (fun b => by rcases b with k | j <;> rfl) (fun b => by rcases b with k | j <;> rfl)
  have hlen2 : s2.τ + ℵ₀ < #s2.κIndex :=
    (add_le_add (hιτ : #ι ≤ seq.τ) le_rfl).trans_lt hlen
  have key := H s2 Z Z0 hlen2 le_rfl hιν hmove2
  have hcard : #(p₁.idx ⊕ ι) < p₁.ν ∧ #(p₁.idx ⊕ ι) < p₂.ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact ⟨hsum.trans_le hν₁, hsum.trans_le hν₂⟩
  have hpres := P.scheme.diagram_preserved p₁.host p₂.host h hh
    (typeJoint (p := p₁) Z0) hcard.1 hcard.2
  let π : p₁.idx ⊕ ι ≃ p₂.idx ⊕ ι := Equiv.sumCongr e (Equiv.refl ι)
  have hpres' : P.scheme.DiagramEq (X := p₁.host) (Y := p₂.host) (typeJoint (p := p₁) Z0)
      (fun t => typeJoint (p := p₂) Z0 (π t)) := by
    refine infra_73_diagramEq_of_eq hpres (fun _ => rfl) ?_
    rintro (k | j)
    · exact (hval k).symm
    · show (⟨(Z0 j).1, h.onVertex (Z0 j).1 (p₁.incl.onVertex (Z0 j).1 (Z0 j).2)⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem p₂.hν p₂.host)) =
        ⟨(Z0 j).1, p₂.incl.onVertex (Z0 j).1 (Z0 j).2⟩
      rcases Z0 j with ⟨⟨⟩, z⟩
      rw [hincl]
  have key2 := infra_612_dEq_transport key π.symm.symm
    (xs' := fun t => typeJoint (p := p₂) Z0 (π t))
    (ys' := infra_612_anchored (e.trans eB) qB.incl qB.val Z)
    (fun _ => rfl) (fun b => by rcases b with k | j <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ hpres' key2

/-- **Anchor homogeneity (proved; `diagram_iso`).** Two objects at one level whose bounded
anchor lists have the same image in a common object are related by a structural isomorphism
carrying one anchor list to the other (paper: "Bounded diagram homogeneity gives an isomorphism
`A ≃ X` carrying these anchors to themselves"). -/
theorem infra_78_anchor_iso {P : SingleModelData K} {ℓ μ : Cardinal.{u}}
    {hℓ : ℓ ∈ P.eligible} {hμ : μ ∈ P.eligible}
    (X A : P.scheme.Object ℓ hℓ) (C : P.scheme.Object μ hμ)
    (gX : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem hμ C))
    (gA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ A) (P.scheme.asSystem hμ C))
    (hgX : P.scheme.permitted (X := X) (Y := C) gX)
    (hgA : P.scheme.permitted (X := A) (Y := C) gA) {α : Type u}
    (xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hℓ X))
    (ys : α → Occurrence K oneVertexShape (P.scheme.asSystem hℓ A))
    (hαℓ : #α < ℓ) (hαμ : #α < μ)
    (himg : ∀ i, (⟨(xs i).1, gX.onVertex (xs i).1 (xs i).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ C)) =
      ⟨(ys i).1, gA.onVertex (ys i).1 (ys i).2⟩) :
    ∃ φ : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem hℓ A),
      P.scheme.IsStructIso (X := X) (Y := A) φ ∧
      ∀ i, ys i = ⟨(xs i).1, φ.onVertex (xs i).1 (xs i).2⟩ := by
  have h1 := P.scheme.diagram_preserved X C gX hgX xs hαℓ hαμ
  have h2 := P.scheme.diagram_preserved A C gA hgA ys hαℓ hαμ
  have h1' := infra_73_diagramEq_of_eq h1 (fun _ => rfl) himg
  have h3 := P.scheme.diagram_trans _ _ _ _ _ _ h1' (P.scheme.diagram_symm _ _ _ _ h2)
  exact (P.scheme.diagram_iso X A xs ys hαℓ).1 h3

/-- **Lemma 7.6 at the shrink (proved).** Paper: "The large type is isolated by the choice of
`i`. Its uniform fragment has size at most `h(|b,c| + ℵ₀) < λ`, so Lemma 7.6 gives isolation over
`A`." Let `jA : A → B` (`A` at level `λ`, `B = X_i` at level `μ`), `q` a bounded tuple over `B`
(hosted at `μ`, e.g. `tp(b, c / X_i)`), and `qA` the same tuple over `A` computed in a level-`λ`
section `U` (`gu : A → U`, `jU : U → host q` with `jU ∘ gu = incl q ∘ jA` and `jU (qA) = q`).
If `q` is tied free over `A` along `jA` (`infra_78_theta_shrink`) and relatively isolated
(`infra_78_isolated_stage`), then `qA` is relatively isolated (`infra_78_tied_descent_mixed`
after `infra_78_tiedFreeMixed_host_transfer`). The level `λ` must be closed at
`infra_76_sigma2 σ` (`infra_78_closedTail` provides this at every `σ < λ`). -/
theorem infra_78_isolation_over_shrink (P : SingleModelData K) (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) {ℓ μ : Cardinal.{u}} (hℓ : ℓ ∈ P.eligible)
    (hℓT : ℓ ∈ infra_73_tailSet P (infra_76_sigma2 P σ)) (hμT : μ ∈ infra_73_tailSet P σ)
    (hℓμ : ℓ ≤ μ) {A U : P.scheme.Object ℓ hℓ}
    {B : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)}
    (jA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ A) (P.scheme.asSystem _ B))
    (hjA : P.scheme.permitted (X := A) (Y := B) jA)
    (q : TupleOver K oneVertexShape P.scheme _ B) (hqν : q.ν = μ)
    (gu : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ A) (P.scheme.asSystem hℓ U))
    (hgu : P.scheme.permitted (X := A) (Y := U) gu)
    (jU : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ U) (P.scheme.asSystem q.hν q.host))
    (hjU : P.scheme.permitted (X := U) (Y := q.host) jU)
    (hsq : ∀ x, jU.onVertex PUnit.unit (gu.onVertex PUnit.unit x) =
      q.incl.onVertex PUnit.unit (jA.onVertex PUnit.unit x))
    (vA : q.idx → Occurrence K oneVertexShape (P.scheme.asSystem hℓ U))
    (hvA : ∀ k, q.val k = ⟨(vA k).1, jU.onVertex (vA k).1 (vA k).2⟩)
    {uIdx cIdx : Type u} (eA : q.idx ≃ uIdx ⊕ cIdx) (hidx : #q.idx ≤ σ)
    (hT : IsTiedFreeMixed jA (q.restrict jA hjA) q (Equiv.refl _))
    (hIso : IsRelativelyIsolated q eA) :
    IsRelativelyIsolated (⟨ℓ, hℓ, U, gu, hgu, q.idx, vA⟩ :
      TupleOver K oneVertexShape P.scheme hℓ A) eA := by
  classical
  let qA : TupleOver K oneVertexShape P.scheme hℓ A := ⟨ℓ, hℓ, U, gu, hgu, q.idx, vA⟩
  have hσ2 : σ ≤ infra_76_sigma2 P σ :=
    (infra_76_lt_h P σ).le.trans (infra_76_lt_h P _).le
  have hidxℓ : #q.idx < ℓ :=
    hidx.trans_lt ((hσ2.trans_lt (Order.lt_succ_of_not_isMax (not_isMax _))).trans_le
      (infra_73_tail_succ hℓT))
  have hT' := infra_78_tiedFreeMixed_host_transfer jA qA (q.restrict jA hjA) q (Equiv.refl _)
    jU hjU (Equiv.refl _) hsq (fun k => hvA k) hidxℓ le_rfl (hℓμ.trans hqν.ge) hT
  have hperm : P.scheme.permitted (X := q.host) (Y := q.host)
      (SystemArrow.refl (P.scheme.asSystem q.hν q.host)) :=
    P.scheme.structural_iso q.host q.host (SystemArrow.refl _) (P.scheme.isStructIso_refl q.host)
  have hExt : SameGaloisType qA (q.restrict jA hjA) ((Equiv.refl _).trans (Equiv.refl _))
      (Equiv.refl _) := by
    refine ⟨q.ν, q.hν, q.host, jU, SystemArrow.refl _, hjU, hperm, ?_, ?_⟩
    · intro v
      cases v
      ext x
      exact hsq x
    · intro i
      exact (hvA i).symm
  have he : ((Equiv.refl q.idx).trans (Equiv.refl q.idx)).symm.trans eA = eA :=
    Equiv.ext fun _ => rfl
  have hIso' : IsRelativelyIsolated q
      (((Equiv.refl q.idx).trans (Equiv.refl q.idx)).symm.trans eA) := by
    rw [he]; exact hIso
  exact infra_78_tied_descent_mixed P σ hσ hℓ hℓT hμT hℓμ jA hjA qA q _ eA rfl hqν hidx hExt
    hT' hIso'

section OverA
variable (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
  {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ) {uIdx cIdx : Type u}
  {ρ : Cardinal.{u}} (hρκ : Order.succ ρ < μ)
  (Xb : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)) {ℓ : Cardinal.{u}}
  (hℓel : ℓ ∈ P.eligible)
  (s0 : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
  (e0 : Infra78MarkData μ uIdx)

include hρκ in
/-- **`infra_78_isolation_over_A`** (Prop 7.8 proof, "Lemma 7.6 gives isolation over `A`";
proved). In the recursion matrix (candidates from the `S`-part, `infra_78_candS`) there is a
stage `i` with `cf(i) > λ` (`infra_78_isolated_stage`) such that every small seed `s₀ ⊆ R_i`
containing the marked tuple `b` lies in a level-`λ` pair `gu : A → U` inside `X_i ≤ Y_i`
(`infra_78_theta_shrink`), `b` has preimages `bU` in `U`, and for EVERY list `c` of length `≤ θ`
from `U` (repetitions allowed) the type `tp(bU, c / A)` computed in the level-`λ` object `U` is
relatively isolated over `bU` (`infra_78_isolation_over_shrink`). Level hypotheses: the matrix
level `μ` is closed at `σ ≥ λ` and at the descent parameter `σd ≥ θ`, and `λ` is closed at
`infra_76_sigma2 σd` (all supplied by `infra_78_closedTail` for levels in that tail). -/
theorem infra_78_isolation_over_A (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (h5all : ∀ k : (Order.succ ρ).ord.ToType, infra_78_StageInv5 Xb (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 k))
    (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ) (hc : #cIdx ≤ ℓ) (h5seed : infra_78_StageInv5 Xb s0)
    (hS0 : ∃ y, (Sum.inr y : μ.ord.ToType ⊕ μ.ord.ToType) ∈ s0.e.R) (h0 : #s0.e.R ≤ ρ)
    (hseed : infra_78_PairClosed ρ hℓel (infra_78_toArr s0.hp) trivial s0.e.R)
    (hℓκ : ℓ ≤ μ) (hℓσ : ℓ ≤ σ) {θ : Cardinal.{u}} (hθ : ℵ₀ ≤ θ) (hθℓ : Order.succ θ ≤ ℓ)
    (hu : #uIdx ≤ θ) (hθc : θ ≤ #cIdx)
    (σd : Cardinal.{u}) (hσd : ℵ₀ ≤ σd) (hθσd : θ ≤ σd)
    (hℓT : ℓ ∈ infra_73_tailSet P (infra_76_sigma2 P σd)) (hμTd : μ ∈ infra_73_tailSet P σd) :
    ∃ i : (Order.succ ρ).ord.ToType, ℓ < Order.cof (Set.Iio i) ∧
      ∀ (s₀ : Set (infra_78_bkCarrier
          (infra_78_rcMatrix hρκ Xb hℓel (infra_78_candS cIdx) s0 e0) i)),
        s₀ ⊆ infra_78_rcSets hρκ Xb hℓel (infra_78_candS cIdx) s0 e0 i → #s₀ ≤ ℓ →
        (∀ k, (Sum.inr ((infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).e.b k) :
          infra_78_bkCarrier (infra_78_rcMatrix hρκ Xb hℓel (infra_78_candS cIdx) s0 e0) i) ∈
            s₀) →
        ∃ (A U : P.scheme.Object ℓ hℓel)
          (jA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A)
            (P.scheme.asSystem _
              ((infra_78_rcMatrix hρκ Xb hℓel (infra_78_candS cIdx) s0 e0).X i)))
          (jU : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel U)
            (P.scheme.asSystem _
              ((infra_78_rcMatrix hρκ Xb hℓel (infra_78_candS cIdx) s0 e0).Y i)))
          (gu : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A)
            (P.scheme.asSystem hℓel U))
          (bU : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hℓel U)),
          SystemArrow.comp gu jU =
            SystemArrow.comp jA ((infra_78_rcMatrix hρκ Xb hℓel (infra_78_candS cIdx) s0 e0).pair i) ∧
          s₀ ⊆ Sum.inl '' Set.range (jA.onVertex PUnit.unit) ∪
            Sum.inr '' Set.range (jU.onVertex PUnit.unit) ∧
          Sum.inl '' Set.range (jA.onVertex PUnit.unit) ⊆
            infra_78_rcSets hρκ Xb hℓel (infra_78_candS cIdx) s0 e0 i ∧
          Sum.inr '' Set.range (jU.onVertex PUnit.unit) ⊆
            infra_78_rcSets hρκ Xb hℓel (infra_78_candS cIdx) s0 e0 i ∧
          (∀ k, jU.onVertex PUnit.unit (bU k).2 =
            (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).e.b k) ∧
          ∀ (J : Type u), #J ≤ θ →
            ∀ c : J → Occurrence K oneVertexShape (P.scheme.asSystem hℓel U),
            IsRelativelyIsolated
              (⟨ℓ, hℓel, U, gu, trivial, uIdx ⊕ J, Sum.elim bU c⟩ :
                TupleOver K oneVertexShape P.scheme hℓel A)
              (Equiv.refl (uIdx ⊕ J)) := by
  classical
  have hpad := infra_78_padSeed_of_closed ρ hℓel s0 hseed
  obtain ⟨i, hi, hiso⟩ := infra_78_isolated_stage P σ hσ hμT hρκ Xb hℓel hidx hℓρ hpow hc
    s0 e0 h5seed h5all (hu.trans (((Order.le_succ θ).trans hθℓ).trans hℓρ.le)) hS0 h0 hpad
  have h5 := h5all
  refine ⟨i, hi, fun s₀ hs₀ hs₀l hb => ?_⟩
  obtain ⟨A, U, jA, jU, gu, hjA, hjU, hgu, hsq, hs0, hTA, hTU, hfree⟩ :=
    infra_78_theta_shrink P σ hσ hμT hρκ Xb hℓel (infra_78_candS cIdx) s0 e0 hidx h5 hℓκ hℓρ hpow
      h0 hseed hS0 hℓσ hθ hθℓ hu i hi s₀ hs₀ hs₀l hb
  have hbpre : ∀ k, ∃ y, jU.onVertex PUnit.unit y =
      (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).e.b k := by
    intro k
    rcases hs0 (hb k) with ⟨x, -, hxe⟩ | ⟨x, ⟨y, hy⟩, hxe⟩
    · exact (Sum.inl_ne_inr hxe).elim
    · exact ⟨y, hy.trans (Sum.inr_injective hxe)⟩
  choose bY hbY using hbpre
  let bU : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hℓel U) :=
    fun k => ⟨PUnit.unit, bY k⟩
  refine ⟨A, U, jA, jU, gu, bU, hsq, hs0, hTA, hTU, hbY, ?_⟩
  intro J hJ c
  let c' : J → μ.ord.ToType := fun x => jU.onVertex PUnit.unit (c x).2
  have hc'U : Set.range c' ⊆ Set.range (jU.onVertex PUnit.unit) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  have hc'S : Set.range c' ⊆
      infra_78_Spart (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i) := by
    rintro _ ⟨x, rfl⟩
    exact hTU ⟨_, ⟨(c x).2, rfl⟩, rfl⟩
  have hI := hiso J (hJ.trans hθc) c' hc'S
  have hT := hfree J hJ c' hc'U
  have hσd2 : σd ≤ infra_76_sigma2 P σd :=
    (infra_76_lt_h P σd).le.trans (infra_76_lt_h P _).le
  have hidxd : #(uIdx ⊕ J) ≤ σd := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact (add_le_add hu hJ).trans ((Cardinal.add_eq_self hθ).le.trans hθσd)
  have hsq' : ∀ x, jU.onVertex PUnit.unit (gu.onVertex PUnit.unit x) =
      (infra_78_toArr (infra_78_rcObj Xb hℓel (infra_78_candS cIdx) s0 e0 i).hp).onVertex
        PUnit.unit (jA.onVertex PUnit.unit x) := fun x =>
    DFunLike.congr_fun (congrArg (fun a => a.onVertex PUnit.unit) hsq) x
  refine infra_78_isolation_over_shrink P σd hσd hℓel hℓT hμTd hℓκ jA hjA _ rfl gu hgu jU hjU
    hsq' (Sum.elim bU c) ?_ (Equiv.refl _) hidxd hT hI
  rintro (k | x)
  · exact Sigma.ext rfl (heq_of_eq (hbY k).symm)
  · rcases hcx : c x with ⟨⟨⟩, z⟩
    refine Sigma.ext rfl (heq_of_eq ?_)
    show jU.onVertex PUnit.unit (c x).2 = jU.onVertex (c x).1 (c x).2
    rw [hcx]

end OverA

end AEC
