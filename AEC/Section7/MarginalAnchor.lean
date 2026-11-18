module

public import AEC.Section7.IsoRename

@[expose] public section

/-!
# Prop 7.8: `I_p` still determines the marginal (`infra_78_marginal_anchor`, split cycle 63)

Paper (Prop 7.8 proof): "Fix a bounded approximation list `I_p` in `X` which determines `p` at a
sufficient testing arity. ... Finally, `I_p` still determines the marginal on `b`: it did so at
`X_0`, the matrix preserved its free lift, and the same approximation answers hold on restriction
to `A`. Bounded diagram homogeneity gives an isomorphism `A ≃ X` carrying these anchors to
themselves. Transport of approximation evaluations carries `tp(b/A)` to `p`."

Proved here:
* `infra_78_anchor_answers`: if the mark `q` (over the level-`κ` stage `B`) is tied free across
  levels over `X` along `ι`, then for any second arrow `j : X → B` agreeing with `ι` on the
  anchors of an approximation sequence of `q ↾ ι`, the small-test diagrams of `q ↾ j` and of
  `q ↾ ι` agree ("the same approximation answers hold").
* `infra_78_anchor_transport`: with `I_p` inside the level-`λ` subobject `A` (`jA : A → B`),
  bounded diagram homogeneity gives `φ : X ≃ A` carrying the anchors, and `q ↾ (φ ≫ jA)` answers
  every small test as `q ↾ ι`.
* `infra_78_marginal_section`: the mark computed in the level-`λ` section `U` and renamed along
  `φ` has the Galois type of `q ↾ (φ ≫ jA)` over `X`.

Open (tracked): `infra_78_marginal_identify` — identify `p` with the renamed mark: the seed
realizes the mixed free lift of `p` (`infra_78_tied_free_lift_mixed`, which needs `p.ν = λ`),
invariant (5) and mixed transitivity keep it tied free over `X` at stage `i`, and the small-test
diagram agreement is turned into `SameGaloisType` across the levels `λ ≤ κ`
(`infra_78_cross_level_galois`, itself modulo `infra_78_tuple_amalgam_large`).
-/

universe u

open Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Same approximation answers (proved).** -/
theorem infra_78_anchor_answers {P : SingleModelData K} {ν μ : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {X : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (ι j : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hμ B))
    (hι : P.scheme.permitted (X := X) (Y := B) ι) (hj : P.scheme.permitted (X := X) (Y := B) j)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hT : IsTiedFreeMixed ι (q.restrict ι hι) q (Equiv.refl _))
    (seq : ApproximationSequence (q.restrict ι hι))
    (hagree : ∀ i k, (⟨(seq.family i k).1, ι.onVertex (seq.family i k).1 (seq.family i k).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) =
      ⟨(seq.family i k).1, j.onVertex (seq.family i k).1 (seq.family i k).2⟩)
    (hidx : #q.idx < ν) (hνμ : ν ≤ μ)
    (hlen : seq.τ + ℵ₀ < #seq.κIndex) {β : Type u}
    (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν X))
    (hβτ : #β ≤ seq.τ) (hβν : #β < ν) :
    P.scheme.DiagramEq (X := q.host) (Y := q.host)
      (typeJoint (p := q.restrict ι hι) Z0) (typeJoint (p := q.restrict j hj) Z0) := by
  classical
  have hν0 : ℵ₀ ≤ ν := P.aleph0_le hν
  have hsz : #(q.idx ⊕ β) < ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hν0 hidx hβν
  let Z' : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun x => ⟨(Z0 x).1, j.onVertex (Z0 x).1 (Z0 x).2⟩
  have hmove : infra_78_isMoveMixed ι seq Z' Z0 := by
    intro i
    have hp := P.scheme.diagram_preserved X B j hj (seqJoint (seq.family i) Z0) hsz
      (hsz.trans_le hνμ)
    refine infra_73_diagramEq_of_eq hp (fun _ => rfl) ?_
    rintro (k | x)
    · exact (hagree i k).symm
    · rfl
  have d := hT seq Z' Z0 hlen hβτ hβν hmove
  exact infra_73_diagramEq_of_eq d (fun _ => rfl) (fun t => by rcases t with k | x <;> rfl)

/-- **Anchor transport (proved).** With the anchors of an approximation sequence for `q ↾ ι`
inside the image of a level-`λ` subobject `jA : A → B`, bounded diagram homogeneity gives a
structural isomorphism `φ : X → A` carrying the anchors to their preimages, and `q ↾ (φ ≫ jA)`
answers every small test as `q ↾ ι`. -/
theorem infra_78_anchor_transport {P : SingleModelData K} {ν μ : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {X A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (ι : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hμ B))
    (jA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hι : P.scheme.permitted (X := X) (Y := B) ι)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hT : IsTiedFreeMixed ι (q.restrict ι hι) q (Equiv.refl _))
    (seq : ApproximationSequence (q.restrict ι hι))
    (hanch : ∀ i k, ∃ y, jA.onVertex PUnit.unit y =
      ι.onVertex PUnit.unit (seq.family i k).2)
    (hidx : #q.idx < ν) (hνμ : ν ≤ μ) (hlen : seq.τ + ℵ₀ < #seq.κIndex) :
    ∃ φ : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hν A),
      P.scheme.IsStructIso (X := X) (Y := A) φ ∧
      (∀ i k, jA.onVertex PUnit.unit (φ.onVertex PUnit.unit (seq.family i k).2) =
        ι.onVertex PUnit.unit (seq.family i k).2) ∧
      ∀ {β : Type u} (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν X)),
        #β ≤ seq.τ → #β < ν →
        P.scheme.DiagramEq (X := q.host) (Y := q.host)
          (typeJoint (p := q.restrict ι hι) Z0)
          (typeJoint (p := q.restrict (SystemArrow.comp φ jA) trivial) Z0) := by
  classical
  choose y hy using hanch
  let xs : seq.κIndex × q.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν X) :=
    fun ik => seq.family ik.1 ik.2
  let ys : seq.κIndex × q.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν A) :=
    fun ik => ⟨(seq.family ik.1 ik.2).1, y ik.1 ik.2⟩
  have hα : #(seq.κIndex × q.idx) < ν := seq.concat_bounded
  obtain ⟨φ, hφ, hys⟩ := infra_78_anchor_iso X A B ι jA hι trivial xs ys hα (hα.trans_le hνμ)
    (by
      rintro ⟨i, k⟩
      have h := hy i k
      show (⟨(seq.family i k).1, ι.onVertex (seq.family i k).1 (seq.family i k).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) =
        ⟨(seq.family i k).1, jA.onVertex (seq.family i k).1 (y i k)⟩
      generalize seq.family i k = f at h ⊢
      rcases f with ⟨⟨⟩, z⟩
      exact Sigma.ext rfl (heq_of_eq h.symm))
  have hcarry : ∀ i k, jA.onVertex PUnit.unit (φ.onVertex PUnit.unit (seq.family i k).2) =
      ι.onVertex PUnit.unit (seq.family i k).2 := by
    intro i k
    have h1 := hys (i, k)
    have h2 : φ.onVertex PUnit.unit (seq.family i k).2 = y i k := by
      simp only [xs, ys] at h1
      generalize seq.family i k = f at h1 ⊢
      rcases f with ⟨⟨⟩, z⟩
      exact (eq_of_heq (Sigma.mk.inj h1).2).symm
    rw [h2, hy i k]
  refine ⟨φ, hφ, hcarry, fun Z0 hβτ hβν => ?_⟩
  refine infra_78_anchor_answers ι (SystemArrow.comp φ jA) hι trivial q hT seq ?_ hidx hνμ hlen
    Z0 hβτ hβν
  intro i k
  generalize hf : seq.family i k = f
  rcases f with ⟨⟨⟩, z⟩
  have := hcarry i k
  rw [hf] at this
  exact Sigma.ext rfl (heq_of_eq this.symm)

/-- **Marginal through the section (proved).** For the level-`λ` pair `gu : A → U` inside the
stage `jA : A → B`, `jU : U → host q` (commuting square), a preimage `bU` of the mark, and any
arrow `φ : X → A`, the mark computed in `U` over `X` along `φ ≫ gu` has the Galois type of
`q ↾ (φ ≫ jA)`. -/
theorem infra_78_marginal_section {P : SingleModelData K} {ν μ : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {X A U : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (φ : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hν A))
    (jA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (gu : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hν U))
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (jU : SystemArrow K oneVertexShape (P.scheme.asSystem hν U) (P.scheme.asSystem q.hν q.host))
    (hsq : ∀ x, jU.onVertex PUnit.unit (gu.onVertex PUnit.unit x) =
      q.incl.onVertex PUnit.unit (jA.onVertex PUnit.unit x))
    (bU : q.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν U))
    (hbU : ∀ k, q.val k = ⟨(bU k).1, jU.onVertex (bU k).1 (bU k).2⟩) :
    SameGaloisType (⟨ν, hν, U, SystemArrow.comp φ gu, trivial, q.idx, bU⟩ :
        TupleOver K oneVertexShape P.scheme hν X)
      (q.restrict (SystemArrow.comp φ jA) trivial) (Equiv.refl _) (Equiv.refl _) := by
  have hperm : P.scheme.permitted (X := q.host) (Y := q.host)
      (SystemArrow.refl (P.scheme.asSystem q.hν q.host)) := trivial
  refine ⟨q.ν, q.hν, q.host, jU, SystemArrow.refl _, trivial, hperm, ?_, ?_⟩
  · intro v
    cases v
    ext x
    exact hsq (φ.onVertex PUnit.unit x)
  · intro i
    exact (hbU i).symm

/-- **Mixed transitivity of tied freeness (proved; port of `infra_78_tiedFree_trans`).** If
`q ↾ A` is tied free across levels from `X` (level `ν`) along `g : X → A` and `q` is tied free from
`A` along `f : A → B` (both at level `μ ≥ ν`), then `q` is tied free across levels from `X` along
`g ≫ f`. Paper: "the matrix preserved its free lift" (invariant (5) plus the seed). -/
theorem infra_78_tiedFreeMixed_trans
    {P : SingleModelData K} {ν μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {X : P.scheme.Object ν hν} {A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := X) (Y := A) g)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B) (hνμ : ν ≤ μ)
    (hXA : IsTiedFreeMixed g ((q.restrict f hf).restrict g hg) (q.restrict f hf) (Equiv.refl _))
    (hAB : IsTiedFree f (q.restrict f hf) q (Equiv.refl _)) :
    IsTiedFreeMixed (SystemArrow.comp g f) (q.restrict (SystemArrow.comp g f) trivial) q
      (Equiv.refl _) := by
  classical
  intro seq ι Z Z0 hκ hι hιν hmove
  let b : ApproximationSequence (q.restrict f hf) :=
    { τ := #ι
      κIndex := seq.κIndex
      family := fun j k => pushOcc g (seq.family j k)
      concat_bounded := seq.concat_bounded.trans_le hνμ
      few_exceptions := fun {β} W hW => by
        have hWτ : #β ≤ seq.τ := hW.trans hι
        obtain ⟨W0, hW0⟩ := infra_78_move_query_mixed g hg hνμ seq W (hW.trans_lt hιν)
        have ht := hXA seq W W0 hκ hWτ (hW.trans_lt hιν) hW0
        refine le_trans ?_ (seq.few_exceptions W0 hWτ)
        refine Cardinal.mk_le_of_injective (f := fun j => ⟨j.1, fun hgood => j.2 ?_⟩)
          (by
            intro j₁ j₂ hj
            apply Subtype.ext
            have := congrArg Subtype.val hj
            exact this)
        have e1 := P.scheme.diagram_symm _ _ _ _ ht
        have e2 := P.scheme.diagram_trans _ _ _ _ _ _ e1 hgood
        have e3 := P.scheme.diagram_trans _ _ _ _ _ _ e2 (hW0 j.1)
        erw [infra_78_anchored_refl (q.restrict f hf) W] at e3
        exact e3 }
  have hκb : b.τ + ℵ₀ < #b.κIndex := (add_le_add hι le_rfl).trans_lt hκ
  have hιb : #ι ≤ b.τ := le_rfl
  have hιμ : #ι < μ := hιν.trans_le hνμ
  obtain ⟨Z1, hZ1⟩ := infra_610_move_query f hf b Z hιb hιμ
  have hq := hAB b Z Z1 hκb hιb hιμ hZ1
  have hcι : ℵ₀ ≤ #ι + ℵ₀ := le_add_self
  obtain ⟨k, hk1, hk2⟩ := infra_78_exists_outside_two
    {k | ¬ P.scheme.DiagramEq (X := q.host) (Y := X)
      (typeJoint (p := q.restrict (SystemArrow.comp g f) trivial) Z0)
      (seqJoint (seq.family k) Z0)}
    {k | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q.restrict f hf) Z1) (seqJoint (b.family k) Z1)}
    hcι (seq.few_exceptions Z0 hι) (b.few_exceptions Z1 hιb) hκb
  simp only [Set.mem_ofPred_eq, not_not] at hk1 hk2
  have a1 := P.scheme.diagram_trans _ _ _ _ _ _ hk1 (hmove k)
  have a2 := P.scheme.diagram_trans _ _ _ _ _ _ a1 (P.scheme.diagram_symm _ _ _ _ (hZ1 k))
  have a3 := P.scheme.diagram_trans _ _ _ _ _ _ a2 (P.scheme.diagram_symm _ _ _ _ hk2)
  exact P.scheme.diagram_trans _ _ _ _ _ _ a3 hq

/-- **Marginal identification at the base level (proved; case `p.ν = λ`).** Paper: "`I_p` still
determines the marginal on `b`: it did so at `X_0`, the matrix preserved its free lift, and the
same approximation answers hold on restriction to `A`. Bounded diagram homogeneity gives an
isomorphism `A ≃ X` carrying these anchors to themselves. Transport of approximation evaluations
carries `tp(b/A)` to `p`." Here `p` is realized at the level `ν` of `X`; `q` is the mark over the
stage `B` (tied free across levels from `X` along `ι`, and answering small tests as `p` — the seed
and invariant (5), via `infra_78_tied_free_lift_mixed` and `infra_78_tiedFreeMixed_trans`); the
anchors `I_p` of an approximation sequence for `q ↾ ι` at the testing arity lie in the level-`ν`
subobject `jA : A → B`, and `gu : A → U`, `jU : U → host q`, `bU` are the shrink data. Then some
structural isomorphism `φ : X → A` makes the mark in `U`, over `X` along `φ ≫ gu`, realize `p`. -/
theorem infra_78_marginal_identify_level (P : SingleModelData K) (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible) {hμ : μ ∈ P.eligible}
    (hrec : ν ∈ recursionClosedLevels P σ) (hσν : σ < ν) (hνμ : ν ≤ μ)
    {X A U : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (p : TupleOver K oneVertexShape P.scheme hν X) (hpν : p.ν = ν) (hidx : #p.idx ≤ σ)
    (ι : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hμ B))
    (hι : P.scheme.permitted (X := X) (Y := B) ι)
    (q : TupleOver K oneVertexShape P.scheme hμ B) (hqν : ν ≤ q.ν) (e : p.idx ≃ q.idx)
    (hseed : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν X)),
      #β < ν →
      P.scheme.DiagramEq (X := p.host) (Y := q.host)
        (alignJoint e (typeJoint (p := p) Z)) (typeJoint (p := q.restrict ι hι) Z))
    (hT : IsTiedFreeMixed ι (q.restrict ι hι) q (Equiv.refl _))
    (seq : ApproximationSequence (q.restrict ι hι)) (hτ : P.g σ + ls K ≤ seq.τ)
    (hlen : seq.τ + ℵ₀ < #seq.κIndex)
    (jA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hanch : ∀ i k, ∃ y, jA.onVertex PUnit.unit y =
      ι.onVertex PUnit.unit (seq.family i k).2)
    (gu : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hν U))
    (jU : SystemArrow K oneVertexShape (P.scheme.asSystem hν U) (P.scheme.asSystem q.hν q.host))
    (hsq : ∀ x, jU.onVertex PUnit.unit (gu.onVertex PUnit.unit x) =
      q.incl.onVertex PUnit.unit (jA.onVertex PUnit.unit x))
    (bU : q.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν U))
    (hbU : ∀ k, q.val k = ⟨(bU k).1, jU.onVertex (bU k).1 (bU k).2⟩) :
    ∃ φ : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hν A),
      P.scheme.IsStructIso (X := X) (Y := A) φ ∧
      (∀ i k, jA.onVertex PUnit.unit (φ.onVertex PUnit.unit (seq.family i k).2) =
        ι.onVertex PUnit.unit (seq.family i k).2) ∧
      SameGaloisType p (⟨ν, hν, U, SystemArrow.comp φ gu, trivial, q.idx, bU⟩ :
        TupleOver K oneVertexShape P.scheme hν X) e (Equiv.refl _) := by
  classical
  have hν0 : ℵ₀ ≤ ν := P.aleph0_le hν
  have hg : P.g σ < ν := (hν.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσν
  have hgls : P.g σ + ls K < ν := add_lt_of_lt hν0 hg (P.ls_lt hν)
  have hqidx : #q.idx < ν := ((Cardinal.mk_congr e).symm.trans_le hidx).trans_lt hσν
  obtain ⟨φ, hφ, hcarry, hans⟩ :=
    infra_78_anchor_transport ι jA hι q hT seq hanch hqidx hνμ hlen
  refine ⟨φ, hφ, hcarry, ?_⟩
  have hsec := infra_78_marginal_section φ jA gu q jU hsq bU hbU
  refine infra_78_sameGalois_of_diagramEq P σ hσ hν hrec hσν p
    (⟨ν, hν, U, SystemArrow.comp φ gu, trivial, q.idx, bU⟩ :
      TupleOver K oneVertexShape P.scheme hν X) e hidx hpν rfl (fun {β} Z hβ => ?_)
  have hβν : #β < ν := hβ.trans_lt hgls
  have hsz : #(q.idx ⊕ β) < ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hν0 hqidx hβν
  have D1 := hseed Z hβν
  have D2 := hans Z (hβ.trans hτ) hβν
  have D3 := infra_78_diagramEq_of_sameGalois hsec Z hsz
    (hsz.trans_le hqν)
  have D3' := P.scheme.diagram_symm _ _ _ _ D3
  have D3'' : P.scheme.DiagramEq (X := q.host) (Y := U)
      (typeJoint (p := q.restrict (SystemArrow.comp φ jA) trivial) Z)
      (typeJoint (p := (⟨ν, hν, U, SystemArrow.comp φ gu, trivial, q.idx, bU⟩ :
        TupleOver K oneVertexShape P.scheme hν X)) Z) :=
    infra_73_diagramEq_of_eq D3' (fun t => by rcases t with k | x <;> rfl)
      (fun t => by rcases t with k | x <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_trans _ _ _ _ _ _ D1 D2) D3''

end AEC
