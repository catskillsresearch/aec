module

public import AEC.Section7.Theorem713
public import AEC.Section7.GeneralLevel

@[expose] public section

/-!
# Proposition 7.8, general bounded-mark form (`infra_78_general`, cycle 93)

English (Prop 7.8): "Let λ be a sufficiently closed eligible level, let X be an object there, and
let p = tp(b/X) be a finite-tuple type. For every infinite θ < λ there is a same-level extension
X ≤ U containing a realization of p such that tp(b, c/X) is isolated relative to b for every
c ∈ U with |c| ≤ θ. More generally the assertion holds for a bounded mark b satisfying
Definition 7.7, with |b| ≤ θ. The closure requirements at the output level are uniform functions
of bounded arities; they do not require θ to have been fixed before the level was chosen."

`infra_78_general_statement` is the "more generally" sentence on the same uniform tail as
`proposition_7_8` (`infra_78_closedTail`), with the tied Definition 7.7
(`SatisfiesContinuityTied`) and `#p.idx ≤ θ`.

Where the finite proof uses finiteness (cycle 93 scan):
* limit stages of the `ρ⁺` matrix: invariant (5) at a limit `δ` is `infra_78_limit_invariant5`
  when `|b| < cf δ` (finite marks: `infra_78_finite_lt_limit_cof`); for `cf δ ≤ |b|` the paper uses
  Definition 7.7 ("At limits use the working scheme's unions; Definition 7.7 preserves the marginal
  invariant"), with `κ` chosen in the Definition 7.7 tail (tracked: `infra_78_general_small_cof`);
* the joint arity of the isolation bounds: `|b, c| ≤ θ` instead of `ℵ₀ + θ`
  (tracked with the assembly: `infra_78_general_assembly`).
The finite-mark case of the general statement is proved here (`infra_78_general_finite`).
-/

universe u

open Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Prop 7.8, general bounded-mark form (statement; open tip `infra_78_general`).** -/
def infra_78_general_statement (P : SingleModelData K) : Prop :=
  ∀ μ (hμ : μ ∈ infra_78_closedTail P)
    (X : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
    (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X)
    (θ : Cardinal.{u}),
    #p.idx ≤ θ → SatisfiesContinuityTied p → aleph0 ≤ θ → θ < μ →
    ∃ (U : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ U))
      (hf : P.scheme.permitted (X := X) (Y := U) f)
      (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
      SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) ∧
      ∀ {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
        #cIdx ≤ θ →
        IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
          (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx))

/-- **Finite marks (proved, cycle 93).** The general statement for a finite mark holds without
Definition 7.7: it is `infra_78_marginal_general_level`. -/
theorem infra_78_general_finite (P : SingleModelData K) :
    ∀ μ (hμ : μ ∈ infra_78_closedTail P)
      (X : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
      (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X)
      (θ : Cardinal.{u}),
      Finite p.idx → #p.idx ≤ θ → SatisfiesContinuityTied p → aleph0 ≤ θ → θ < μ →
      ∃ (U : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ U))
        (hf : P.scheme.permitted (X := X) (Y := U) f)
        (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
        SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) ∧
        ∀ {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
          #cIdx ≤ θ →
          IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
            (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx)) :=
  fun μ hμ X p θ hfin _ _ hθ hθμ => infra_78_marginal_general_level P μ hμ X p θ hfin hθ hθμ

/-- **Invariant (5) at a matrix limit from freeness over some stage (proved, cycle 93).**
The step of `infra_78_tied_continuity` after local character: if the mark `p` over the union
`X_δ` is tied-free from some stage `X_i` (for `|b| < cf δ` this is local character,
`infra_78_tied_local`; for a bounded mark satisfying Definition 7.7 it is Def 7.7's conclusion at
`i = 0`, "Definition 7.7 preserves the marginal invariant"), and (5) holds at every stage, then
(5) holds at `δ`. No cofinality hypothesis. -/
theorem infra_78_general_limit_invariant {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} (C : SameLevelChain P hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ C.unionObj)
    (X : P.scheme.Object μ hμ)
    (g : SystemArrow K oneVertexShape
      (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ (C.obj 0 C.hlim.1)))
    (hg : P.scheme.permitted (X := X) (Y := C.obj 0 C.hlim.1) g)
    (hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree
        (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
          (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (P.scheme.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hg
            (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _))
    (hF : ∃ i : Ordinal.{u}, ∃ hi : i < C.δ,
      IsTiedFree (C.toUnion i hi)
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) p (Equiv.refl _)) :
    IsTiedFree (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
      (p.restrict (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
        (P.scheme.comp g (C.toUnion 0 C.hlim.1) hg (C.toUnion_arrow 0 C.hlim.1)))
      p (Equiv.refl _) := by
  obtain ⟨i, hi, hF⟩ := hF
  have hzero : (0 : Ordinal.{u}) ≤ i := bot_le
  have hgA := P.scheme.comp g (C.le C.hlim.1 hi hzero) hg (C.le_arrow C.hlim.1 hi hzero)
  have htrans := infra_78_tiedFree_trans (SystemArrow.comp g (C.le C.hlim.1 hi hzero)) hgA
    (C.toUnion i hi) (C.toUnion_arrow i hi) p (hAll i hi) hF
  exact infra_78_tiedFree_congr_arrow _ _ p (infra_613_cocone_arrow C g hi) htrans

/-- **Transitivity of tied freeness, general top (proved, cycle 93).** As
`infra_78_tiedFree_trans`, with the middle tuple `Q` over `A` arbitrary and the top `r` over `B`
any tied free lift of `Q` (index bijection `er`), not necessarily a tuple restricting to `Q`. -/
theorem infra_78_tiedFree_trans_gen
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := X) (Y := A) g)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (Q : TupleOver K oneVertexShape P.scheme hμ A)
    (r : TupleOver K oneVertexShape P.scheme hμ B) (er : Q.idx ≃ r.idx)
    (hXA : IsTiedFree g (Q.restrict g hg) Q (Equiv.refl _))
    (hAB : IsTiedFree f Q r er) :
    IsTiedFree (SystemArrow.comp g f) (Q.restrict g hg) r er := by
  classical
  intro seq ι Z Z0 hκ hι hιμ hmove
  let b : ApproximationSequence Q :=
    { τ := #ι
      κIndex := seq.κIndex
      family := fun j k => pushOcc g (seq.family j k)
      concat_bounded := seq.concat_bounded
      few_exceptions := fun {β} W hW => by
        have hWτ : #β ≤ seq.τ := hW.trans hι
        obtain ⟨W0, hW0⟩ := infra_610_move_query g hg seq W hWτ (hW.trans_lt hιμ)
        have ht := hXA seq W W0 hκ hWτ (hW.trans_lt hιμ) hW0
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
        erw [infra_78_anchored_refl Q W] at e3
        exact e3 }
  have hκb : b.τ + ℵ₀ < #b.κIndex := (add_le_add hι le_rfl).trans_lt hκ
  have hιb : #ι ≤ b.τ := le_rfl
  obtain ⟨Z1, hZ1⟩ := infra_610_move_query f hf b Z hιb hιμ
  have hq := hAB b Z Z1 hκb hιb hιμ hZ1
  have hcι : ℵ₀ ≤ #ι + ℵ₀ := le_add_self
  obtain ⟨k, hk1, hk2⟩ := infra_78_exists_outside_two
    {k | ¬ P.scheme.DiagramEq (X := Q.host) (Y := X)
      (typeJoint (p := Q.restrict g hg) Z0)
      (seqJoint (seq.family k) Z0)}
    {k | ¬ P.scheme.DiagramEq (X := Q.host) (Y := A)
      (typeJoint (p := Q) Z1) (seqJoint (b.family k) Z1)}
    hcι (seq.few_exceptions Z0 hι) (b.few_exceptions Z1 hιb) hκb
  simp only [Set.mem_ofPred_eq, not_not] at hk1 hk2
  have a1 := P.scheme.diagram_trans _ _ _ _ _ _ hk1 (hmove k)
  have a2 := P.scheme.diagram_trans _ _ _ _ _ _ a1 (P.scheme.diagram_symm _ _ _ _ (hZ1 k))
  have a3 := P.scheme.diagram_trans _ _ _ _ _ _ a2 (P.scheme.diagram_symm _ _ _ _ hk2)
  exact P.scheme.diagram_trans _ _ _ _ _ _ a3 hq

/-- **Cancellation of tied freeness (proved, cycle 93).** For `X → A → B` at one level, if
`q ↾ A` is tied free from `X` and `q` is tied free from `X` (along `X → B`), then `q` is tied
free from `A`. Proof: the tied free lift `r` of `q ↾ A` is tied free from `X` (transitivity),
so `r` and `q` have the same type over `B` (uniqueness, `infra_73_tied_unique`), and the tied
freeness of `r` transfers to `q` (Theorem 6.6 diagrams). -/
theorem infra_78_tiedFree_cancel
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {X A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := X) (Y := A) g)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B) (hqν : q.ν = μ) (hidx : #q.idx ≤ σ)
    (hXA : IsTiedFree g ((q.restrict f hf).restrict g hg) (q.restrict f hf) (Equiv.refl _))
    (hXB : IsTiedFree (SystemArrow.comp g f) ((q.restrict f hf).restrict g hg) q
      (Equiv.refl _)) :
    IsTiedFree f (q.restrict f hf) q (Equiv.refl _) := by
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  obtain ⟨r, er, hrν, -, hTr⟩ :=
    infra_610_tied_free_lift P σ hσ hμ hrec hσSucc f hf (q.restrict f hf) hqν hidx
  have hXr := infra_78_tiedFree_trans_gen g hg f hf (q.restrict f hf) r er hXA hTr
  have hU := infra_73_tied_unique P σ hσ hμ hrec hσSucc (SystemArrow.comp g f)
    (P.scheme.comp g f hg hf) ((q.restrict f hf).restrict g hg) hqν hidx r q er (Equiv.refl _)
    hrν hqν hXr hXB
  intro seq ι Z Z0 h1 h2 h3 hmove
  have D1 := hTr seq Z Z0 h1 h2 h3 hmove
  have D2 := infra_612_dEq_of_sameGalois hU Z (hidx.trans_lt hσlt) h3
  have D3 : P.scheme.DiagramEq (X := r.host) (Y := q.host)
      (infra_612_anchored er r.incl r.val Z)
      (infra_612_anchored (Equiv.refl q.idx) q.incl q.val Z) :=
    infra_73_diagramEq_of_eq D2 (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ D1 D3

section LimitAssemblyGen
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

/-- **Prop 7.8 matrix limit step for bounded marks (proved, cycle 93).** As
`infra_78_matrix_limit_step`, with the cofinality hypothesis `|b| < cf δ` replaced by the
continuity of the mark along same-level chains at `κ` (`hF`: if every stage restriction is tied
free from the base, the mark over the union is tied free from some stage). For `|b| < cf δ`, `hF`
is local character (`infra_78_tied_local`); for a bounded mark satisfying Definition 7.7 it is
Definition 7.7 at stage `0` (tracked: `infra_78_general_small_cof`). -/
theorem infra_78_matrix_limit_step_gen (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (hrec : κ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ κ)
    (hρκ : Order.succ ρ < κ) {δ : (Order.succ ρ).ord.ToType}
    (hδ : Order.IsSuccLimit δ) (X Y : Set.Iio δ → P.scheme.Object κ hκ)
    (pair : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
      (P.scheme.asSystem hκ (Y j)))
    (sX : ∀ {a b : Set.Iio δ}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a)) (P.scheme.asSystem hκ (X b)))
    (sY : ∀ {a b : Set.Iio δ}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y a)) (P.scheme.asSystem hκ (Y b)))
    (hXr : ∀ a, sX (le_refl a) = SystemArrow.refl _)
    (hYr : ∀ a, sY (le_refl a) = SystemArrow.refl _)
    (hXt : ∀ {a b c : Set.Iio δ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sX (h₁.trans h₂) = SystemArrow.comp (sX h₁) (sX h₂))
    (hYt : ∀ {a b c : Set.Iio δ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sY (h₁.trans h₂) = SystemArrow.comp (sY h₁) (sY h₂))
    (hcomm : ∀ {a b : Set.Iio δ} (h : a ≤ b),
      SystemArrow.comp (pair a) (sY h) = SystemArrow.comp (sX h) (pair b))
    (Xb : P.scheme.Object κ hκ)
    (g : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb) (P.scheme.asSystem hκ (X j)))
    (hg : ∀ {a b : Set.Iio δ} (h : a ≤ b), SystemArrow.comp (g a) (sX h) = g b)
    {uIdx : Type u} (b : ∀ j, uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ (Y j)))
    (hb : ∀ {a c : Set.Iio δ} (h : a ≤ c) k, b c k = pushOcc (sY h) (b a k))
    (hidx : #uIdx ≤ σ)
    (hF : ∀ (C : SameLevelChain P hκ) {Y' : P.scheme.Object κ hκ}
      (pr : SystemArrow K oneVertexShape (P.scheme.asSystem hκ C.unionObj)
        (P.scheme.asSystem hκ Y'))
      (bb : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Y'))
      (g0 : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb)
        (P.scheme.asSystem hκ (C.obj 0 C.hlim.1))),
      (∀ (i : Ordinal.{u}) (hi : i < C.δ),
        IsTiedFree
          (SystemArrow.comp g0 (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (((infra_78_markTuple pr bb).restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
            (SystemArrow.comp g0 (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
            (P.scheme.comp g0 (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) trivial
              (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
          ((infra_78_markTuple pr bb).restrict (C.toUnion i hi) (C.toUnion_arrow i hi))
          (Equiv.refl _)) →
      ∃ i : Ordinal.{u}, ∃ hi : i < C.δ,
        IsTiedFree (C.toUnion i hi)
          ((infra_78_markTuple pr bb).restrict (C.toUnion i hi) (C.toUnion_arrow i hi))
          (infra_78_markTuple pr bb) (Equiv.refl _))
    (h5 : ∀ j, IsTiedFree (g j) ((infra_78_markTuple (pair j) (b j)).restrict (g j) trivial)
      (infra_78_markTuple (pair j) (b j)) (Equiv.refl _)) :
    ∃ (Xδ Yδ : P.scheme.Object κ hκ)
      (lX : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
        (P.scheme.asSystem hκ Xδ))
      (lY : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y j))
        (P.scheme.asSystem hκ Yδ))
      (pδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xδ) (P.scheme.asSystem hκ Yδ))
      (gδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb) (P.scheme.asSystem hκ Xδ))
      (bδ : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Yδ)),
      (∀ {a c : Set.Iio δ} (h : a ≤ c), SystemArrow.comp (sX h) (lX c) = lX a) ∧
      (∀ {a c : Set.Iio δ} (h : a ≤ c), SystemArrow.comp (sY h) (lY c) = lY a) ∧
      (∀ j, SystemArrow.comp (pair j) (lY j) = SystemArrow.comp (lX j) pδ) ∧
      (∀ x : (Xδ.model).carrier, ∃ j y, (lX j).onVertex PUnit.unit y = x) ∧
      (∀ x : (Yδ.model).carrier, ∃ j y, (lY j).onVertex PUnit.unit y = x) ∧
      (∀ j, SystemArrow.comp (g j) (lX j) = gδ) ∧
      (∀ j k, bδ k = pushOcc (lY j) (b j k)) ∧
      IsTiedFree gδ ((infra_78_markTuple pδ bδ).restrict gδ trivial)
        (infra_78_markTuple pδ bδ) (Equiv.refl _) := by
  classical
  obtain ⟨Xδ, Yδ, lX, lY, pδ, -, -, -, hcX, hcY, hsq, hcovX, hcovY⟩ :=
    infra_78_limit_pair hρκ hδ X Y pair sX sY hXr hYr hXt hYt hcomm
  let C := infra_78_partialChain hδ X sX hXt Xδ lX hcX hcovX
  let j0 : Set.Iio δ := ⟨infra_78_stg δ 0 C.hlim.1, infra_78_stg_lt δ 0 C.hlim.1⟩
  let gδ := SystemArrow.comp (g j0) (lX j0)
  let bδ : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Yδ) :=
    fun k => pushOcc (lY j0) (b j0 k)
  have hgδ : ∀ j, SystemArrow.comp (g j) (lX j) = gδ := by
    intro j
    rcases le_total j j0 with h | h
    · show _ = SystemArrow.comp (g j0) (lX j0)
      rw [← hcX h, ← SystemArrow.comp_assoc, hg h]
    · show _ = SystemArrow.comp (g j0) (lX j0)
      rw [← hcX h, ← SystemArrow.comp_assoc, hg h]
  have hbδ : ∀ j k, bδ k = pushOcc (lY j) (b j k) := by
    intro j k
    rcases le_total j j0 with h | h
    · show pushOcc (lY j0) (b j0 k) = _
      rw [hb h k, ← pushOcc_comp, hcY h]
    · show pushOcc (lY j0) (b j0 k) = _
      rw [hb h k, ← pushOcc_comp, hcY h]
  refine ⟨Xδ, Yδ, lX, lY, pδ, gδ, bδ, hcX, hcY, hsq, hcovX, hcovY, hgδ, hbδ, ?_⟩
  have hqκ : #uIdx < κ := hidx.trans_lt (Order.succ_le_iff.1 hσSucc)
  let p : TupleOver K oneVertexShape P.scheme hκ C.unionObj := infra_78_markTuple pδ bδ
  have hsqx : ∀ j (x : (X j).model.carrier),
      (lY j).onVertex PUnit.unit ((pair j).onVertex PUnit.unit x) =
        pδ.onVertex PUnit.unit ((lX j).onVertex PUnit.unit x) := fun j x =>
    DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hsq j)) x
  have hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree
        (SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
          (SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (P.scheme.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) trivial
            (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _) := by
    intro i hi
    let ji : Set.Iio δ := ⟨infra_78_stg δ i hi, infra_78_stg_lt δ i hi⟩
    have e1 : SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) =
        g ji := hg _
    have hR : infra_78_HostRel (infra_78_markTuple (pair ji) (b ji))
        (p.restrict (lX ji) trivial) (lY ji) (Equiv.refl _) :=
      ⟨fun v x => by cases v; exact hsqx ji x, fun k => hbδ ji k⟩
    have hR' : infra_78_HostRel ((infra_78_markTuple (pair ji) (b ji)).restrict (g ji) trivial)
        ((p.restrict (lX ji) trivial).restrict (g ji) trivial) (lY ji) (Equiv.refl _) :=
      ⟨fun v x => by cases v; exact hsqx ji _, fun k => hbδ ji k⟩
    have h1 := (infra_78_tiedFree_host_target (g ji)
      ((infra_78_markTuple (pair ji) (b ji)).restrict (g ji) trivial) trivial hR rfl rfl hqκ
      (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 (h5 ji)
    have h2 := infra_78_tiedFree_host_source (g ji) trivial hR' rfl rfl hqκ
      (p.restrict (lX ji) trivial) (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) h1
    exact infra_78_tiedFree_congr_arrow trivial trivial (p.restrict (lX ji) trivial) e1.symm h2
  exact infra_78_general_limit_invariant C p Xb (g j0) trivial hAll (hF C pδ bδ (g j0) hAll)

end LimitAssemblyGen

/-- Restricting twice is restricting along the composite. -/
theorem infra_78_restrict_restrict_eq {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (hf : P.scheme.permitted (X := X) (Y := A) f)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hg : P.scheme.permitted (X := A) (Y := B) g)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ B))
    (hh : P.scheme.permitted (X := X) (Y := B) h) (heq : SystemArrow.comp f g = h) :
    (q.restrict g hg).restrict f hf = q.restrict h hh := by
  subst heq
  simp only [TupleOver.restrict, SystemArrow.comp_assoc]

/-- Transport of tied freeness along equalities of the tuples (with matching identifications). -/
theorem infra_78_tiedFree_congr {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X A : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    {qX qX' : TupleOver K oneVertexShape P.scheme hμ X}
    {qA qA' : TupleOver K oneVertexShape P.scheme hμ A}
    (hX : qX = qX') (hA : qA = qA') (e : qX.idx ≃ qA.idx) (e' : qX'.idx ≃ qA'.idx)
    (he : HEq e e') (H : IsTiedFree f qX qA e) : IsTiedFree f qX' qA' e' := by
  subst hX; subst hA; cases he; exact H

/-- **Stage freeness from base freeness (proved, cycle 93).** On a same-level chain, if the
mark `b` over the union has every stage restriction tied free from a base `X_b → X_0` (and the
stage-`0` restriction along `X_b → X_0` itself), then every stage restriction is tied free from
`X_0` (cancellation, `infra_78_tiedFree_cancel`). This is the stage hypothesis of Definition 7.7
(`SatisfiesContinuityTied`) obtained from invariant (5) of the Prop 7.8 matrix. -/
theorem infra_78_chain_stage_free
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {κ : Cardinal.{u}} (hκ : κ ∈ P.eligible)
    (hrec : κ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ κ)
    (C : SameLevelChain P hκ) (b : TupleOver K oneVertexShape P.scheme hκ C.unionObj)
    (hbν : b.ν = κ) (hidx : #b.idx ≤ σ)
    (Xb : P.scheme.Object κ hκ)
    (g0 : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb)
      (P.scheme.asSystem hκ (C.obj 0 C.hlim.1)))
    (hg0 : P.scheme.permitted (X := Xb) (Y := C.obj 0 C.hlim.1) g0)
    (h0 : IsTiedFree g0
      ((b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)).restrict g0 hg0)
      (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) (Equiv.refl _))
    (hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree
        (SystemArrow.comp g0 (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        ((b.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
          (SystemArrow.comp g0 (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (P.scheme.comp g0 (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hg0
            (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
        (b.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)) :
    ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))
        (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1))
        (b.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _) := by
  intro i hi
  have hle := C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)
  have hE : (b.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
      (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hle =
      b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1) :=
    infra_78_restrict_restrict_eq _ _ _ _ _ _ _ (C.toUnion_comp C.hlim.1 hi bot_le)
  have hE2 := infra_78_restrict_restrict_eq g0 hg0
    (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hle
    (b.restrict (C.toUnion i hi) (C.toUnion_arrow i hi))
    (SystemArrow.comp g0 (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
    (P.scheme.comp g0 _ hg0 hle) rfl
  have hc := infra_78_tiedFree_cancel P σ hσ hκ hrec hσSucc g0 hg0
    (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hle
    (b.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) hbν hidx
    (infra_78_tiedFree_congr g0 (congrArg (TupleOver.restrict g0 hg0) hE.symm) hE.symm
      _ _ HEq.rfl h0)
    (infra_78_tiedFree_congr _ hE2.symm rfl _ _ HEq.rfl (hAll i hi))
  exact infra_78_tiedFree_congr _ hE rfl _ _ HEq.rfl hc

/-- **Definition 7.7 gives the continuity oracle (proved, cycle 93).** For a mark `p` satisfying
Definition 7.7 (`SatisfiesContinuityTied`), there is a tail `T` such that at every recursion
level `κ ∈ T` above `|p|`'s level: for every same-level chain at `κ` and every bounded
realization `b` over its union whose stage-`0` restriction is the (mixed) tied free lift of `p`
along a base embedding `A → X₀`, if every stage restriction is tied free from a base `X_b → X₀`
(and so is the stage-`0` restriction), then `b` is tied free from `X₀` over the union. Stage
freeness from `X₀` comes from cancellation (`infra_78_chain_stage_free`). This discharges the
`hF` hypothesis of `infra_78_matrix_limit_step_gen` (with `i = 0`) once the matrix supplies the
stage-`0` seed. -/
theorem infra_78_hF_of_def77 (P : SingleModelData K) {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hp : SatisfiesContinuityTied p) :
    ∃ T, ∃ hT : Tail P.eligible T, ∀ κ (hκT : κ ∈ T), μ ≤ κ →
      ∀ (σ : Cardinal.{u}), ℵ₀ ≤ σ → κ ∈ recursionClosedLevels P σ → Order.succ σ ≤ κ →
      ∀ (C : SameLevelChain P (Tail.mem hT hκT))
        (b : TupleOver K oneVertexShape P.scheme (Tail.mem hT hκT) C.unionObj),
        b.ν = κ → #b.idx ≤ σ →
      ∀ (Xb : P.scheme.Object κ (Tail.mem hT hκT))
        (g0 : SystemArrow K oneVertexShape (P.scheme.asSystem (Tail.mem hT hκT) Xb)
          (P.scheme.asSystem (Tail.mem hT hκT) (C.obj 0 C.hlim.1)))
        (hg0 : P.scheme.permitted (X := Xb) (Y := C.obj 0 C.hlim.1) g0)
        (gA : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A)
          (P.scheme.asSystem (Tail.mem hT hκT) (C.obj 0 C.hlim.1)))
        (hgA : P.scheme.permitted (X := A) (Y := C.obj 0 C.hlim.1) gA)
        (e : p.idx ≃ b.idx),
        IsTiedFreeMixed gA p (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) e →
        IsTiedFree g0
          ((b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)).restrict g0 hg0)
          (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) (Equiv.refl _) →
        (∀ (i : Ordinal.{u}) (hi : i < C.δ),
          IsTiedFree
            (SystemArrow.comp g0 (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
            ((b.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
              (SystemArrow.comp g0 (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
              (P.scheme.comp g0 (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hg0
                (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
            (b.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)) →
        IsTiedFree (C.toUnion 0 C.hlim.1)
          (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) b (Equiv.refl _) := by
  obtain ⟨T, hT, H⟩ := hp
  refine ⟨T, hT, ?_⟩
  intro κ hκT hμκ σ hσ hrec hσSucc C b hbν hidx Xb g0 hg0 gA hgA e hmix h0 hAll
  exact H κ hκT hμκ C gA hgA b e hbν hmix
    (infra_78_chain_stage_free P σ hσ (Tail.mem hT hκT) hrec hσSucc C b hbν hidx Xb g0 hg0 h0 hAll)

/-- A host relation between two tuples over the same base is a same-Galois-type witness. -/
theorem infra_78_sameGalois_of_hostRel {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {B : P.scheme.Object μ hμ}
    {r₁ r₂ : TupleOver K oneVertexShape P.scheme hμ B}
    {h : SystemArrow K oneVertexShape (P.scheme.asSystem r₁.hν r₁.host)
      (P.scheme.asSystem r₂.hν r₂.host)} (hh : P.scheme.permitted (X := r₁.host) (Y := r₂.host) h)
    (hr : P.scheme.permitted (X := r₂.host) (Y := r₂.host) (SystemArrow.refl _))
    {e : r₁.idx ≃ r₂.idx} (hR : infra_78_HostRel r₁ r₂ h e) :
    SameGaloisType r₁ r₂ e (Equiv.refl _) := by
  refine ⟨r₂.ν, r₂.hν, r₂.host, h, SystemArrow.refl _, hh, hr, ?_, ?_⟩
  · intro v
    ext x
    exact hR.1 v x
  · intro i
    have := hR.2 (e.symm i)
    simp only [Equiv.apply_symm_apply] at this
    exact this.symm


section LimitAssemblyDef77
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

/-- **Prop 7.8 matrix limit step under Definition 7.7 (proved, cycle 93).** As
`infra_78_matrix_limit_step`, with no cofinality hypothesis: the mark `b` is bounded
(`|b| ≤ σ`), every stage carries the seed (the stage mark is the mixed tied free lift of `pA`
along `A → X_b → X_j`, "the matrix preserved its free lift"), and `hD` is Definition 7.7
(`SatisfiesContinuityTied pA`) at the level `κ`. Invariant (5) is preserved at the limit:
stage freeness from `X_0` by cancellation (`infra_78_chain_stage_free`), the seed transported to
the union stage by a host relation, then Definition 7.7 and `infra_78_general_limit_invariant`. -/
theorem infra_78_matrix_limit_step_def77 (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (hrec : κ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ κ)
    (hρκ : Order.succ ρ < κ) {δ : (Order.succ ρ).ord.ToType}
    (hδ : Order.IsSuccLimit δ) (X Y : Set.Iio δ → P.scheme.Object κ hκ)
    (pair : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
      (P.scheme.asSystem hκ (Y j)))
    (sX : ∀ {a b : Set.Iio δ}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a)) (P.scheme.asSystem hκ (X b)))
    (sY : ∀ {a b : Set.Iio δ}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y a)) (P.scheme.asSystem hκ (Y b)))
    (hXr : ∀ a, sX (le_refl a) = SystemArrow.refl _)
    (hYr : ∀ a, sY (le_refl a) = SystemArrow.refl _)
    (hXt : ∀ {a b c : Set.Iio δ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sX (h₁.trans h₂) = SystemArrow.comp (sX h₁) (sX h₂))
    (hYt : ∀ {a b c : Set.Iio δ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sY (h₁.trans h₂) = SystemArrow.comp (sY h₁) (sY h₂))
    (hcomm : ∀ {a b : Set.Iio δ} (h : a ≤ b),
      SystemArrow.comp (pair a) (sY h) = SystemArrow.comp (sX h) (pair b))
    (Xb : P.scheme.Object κ hκ)
    (g : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb) (P.scheme.asSystem hκ (X j)))
    (hg : ∀ {a b : Set.Iio δ} (h : a ≤ b), SystemArrow.comp (g a) (sX h) = g b)
    {uIdx : Type u} (b : ∀ j, uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ (Y j)))
    (hb : ∀ {a c : Set.Iio δ} (h : a ≤ c) k, b c k = pushOcc (sY h) (b a k))
    (hidx : #uIdx ≤ σ)
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {A : P.scheme.Object ν hν}
    (pA : TupleOver K oneVertexShape P.scheme hν A) (hνκ : ν ≤ κ) (hpA : #pA.idx < ν)
    (ι0 : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hκ Xb))
    (eA : pA.idx ≃ uIdx)
    (hseed : ∀ j, IsTiedFreeMixed (SystemArrow.comp ι0 (g j)) pA
      (infra_78_markTuple (pair j) (b j)) eA)
    (hD : ∀ (C : SameLevelChain P hκ)
      (gA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A)
        (P.scheme.asSystem hκ (C.obj 0 C.hlim.1)))
      (_hgA : P.scheme.permitted (X := A) (Y := C.obj 0 C.hlim.1) gA)
      (bU : TupleOver K oneVertexShape P.scheme hκ C.unionObj) (e : pA.idx ≃ bU.idx),
      bU.ν = κ →
      IsTiedFreeMixed gA pA (bU.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) e →
      (∀ (i : Ordinal.{u}) (hi : i < C.δ),
        IsTiedFree (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))
          (bU.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1))
          (bU.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)) →
      IsTiedFree (C.toUnion 0 C.hlim.1)
        (bU.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) bU (Equiv.refl _))
    (h5 : ∀ j, IsTiedFree (g j) ((infra_78_markTuple (pair j) (b j)).restrict (g j) trivial)
      (infra_78_markTuple (pair j) (b j)) (Equiv.refl _)) :
    ∃ (Xδ Yδ : P.scheme.Object κ hκ)
      (lX : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
        (P.scheme.asSystem hκ Xδ))
      (lY : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y j))
        (P.scheme.asSystem hκ Yδ))
      (pδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xδ) (P.scheme.asSystem hκ Yδ))
      (gδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb) (P.scheme.asSystem hκ Xδ))
      (bδ : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Yδ)),
      (∀ {a c : Set.Iio δ} (h : a ≤ c), SystemArrow.comp (sX h) (lX c) = lX a) ∧
      (∀ {a c : Set.Iio δ} (h : a ≤ c), SystemArrow.comp (sY h) (lY c) = lY a) ∧
      (∀ j, SystemArrow.comp (pair j) (lY j) = SystemArrow.comp (lX j) pδ) ∧
      (∀ x : (Xδ.model).carrier, ∃ j y, (lX j).onVertex PUnit.unit y = x) ∧
      (∀ x : (Yδ.model).carrier, ∃ j y, (lY j).onVertex PUnit.unit y = x) ∧
      (∀ j, SystemArrow.comp (g j) (lX j) = gδ) ∧
      (∀ j k, bδ k = pushOcc (lY j) (b j k)) ∧
      IsTiedFree gδ ((infra_78_markTuple pδ bδ).restrict gδ trivial)
        (infra_78_markTuple pδ bδ) (Equiv.refl _) := by
  classical
  obtain ⟨Xδ, Yδ, lX, lY, pδ, -, -, -, hcX, hcY, hsq, hcovX, hcovY⟩ :=
    infra_78_limit_pair hρκ hδ X Y pair sX sY hXr hYr hXt hYt hcomm
  let C := infra_78_partialChain hδ X sX hXt Xδ lX hcX hcovX
  let j0 : Set.Iio δ := ⟨infra_78_stg δ 0 C.hlim.1, infra_78_stg_lt δ 0 C.hlim.1⟩
  let gδ := SystemArrow.comp (g j0) (lX j0)
  let bδ : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Yδ) :=
    fun k => pushOcc (lY j0) (b j0 k)
  have hgδ : ∀ j, SystemArrow.comp (g j) (lX j) = gδ := by
    intro j
    rcases le_total j j0 with h | h
    · show _ = SystemArrow.comp (g j0) (lX j0)
      rw [← hcX h, ← SystemArrow.comp_assoc, hg h]
    · show _ = SystemArrow.comp (g j0) (lX j0)
      rw [← hcX h, ← SystemArrow.comp_assoc, hg h]
  have hbδ : ∀ j k, bδ k = pushOcc (lY j) (b j k) := by
    intro j k
    rcases le_total j j0 with h | h
    · show pushOcc (lY j0) (b j0 k) = _
      rw [hb h k, ← pushOcc_comp, hcY h]
    · show pushOcc (lY j0) (b j0 k) = _
      rw [hb h k, ← pushOcc_comp, hcY h]
  refine ⟨Xδ, Yδ, lX, lY, pδ, gδ, bδ, hcX, hcY, hsq, hcovX, hcovY, hgδ, hbδ, ?_⟩
  have hqκ : #uIdx < κ := hidx.trans_lt (Order.succ_le_iff.1 hσSucc)
  let p : TupleOver K oneVertexShape P.scheme hκ C.unionObj := infra_78_markTuple pδ bδ
  have hsqx : ∀ j (x : (X j).model.carrier),
      (lY j).onVertex PUnit.unit ((pair j).onVertex PUnit.unit x) =
        pδ.onVertex PUnit.unit ((lX j).onVertex PUnit.unit x) := fun j x =>
    DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hsq j)) x
  have hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree
        (SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
          (SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (P.scheme.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) trivial
            (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _) := by
    intro i hi
    let ji : Set.Iio δ := ⟨infra_78_stg δ i hi, infra_78_stg_lt δ i hi⟩
    have e1 : SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) =
        g ji := hg _
    have hR : infra_78_HostRel (infra_78_markTuple (pair ji) (b ji))
        (p.restrict (lX ji) trivial) (lY ji) (Equiv.refl _) :=
      ⟨fun v x => by cases v; exact hsqx ji x, fun k => hbδ ji k⟩
    have hR' : infra_78_HostRel ((infra_78_markTuple (pair ji) (b ji)).restrict (g ji) trivial)
        ((p.restrict (lX ji) trivial).restrict (g ji) trivial) (lY ji) (Equiv.refl _) :=
      ⟨fun v x => by cases v; exact hsqx ji _, fun k => hbδ ji k⟩
    have h1 := (infra_78_tiedFree_host_target (g ji)
      ((infra_78_markTuple (pair ji) (b ji)).restrict (g ji) trivial) trivial hR rfl rfl hqκ
      (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 (h5 ji)
    have h2 := infra_78_tiedFree_host_source (g ji) trivial hR' rfl rfl hqκ
      (p.restrict (lX ji) trivial) (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) h1
    exact infra_78_tiedFree_congr_arrow trivial trivial (p.restrict (lX ji) trivial) e1.symm h2
  have hR0 : infra_78_HostRel (infra_78_markTuple (pair j0) (b j0))
      (p.restrict (lX j0) trivial) (lY j0) (Equiv.refl _) :=
    ⟨fun v x => by cases v; exact hsqx j0 x, fun k => hbδ j0 k⟩
  have hR0' : infra_78_HostRel ((infra_78_markTuple (pair j0) (b j0)).restrict (g j0) trivial)
      ((p.restrict (lX j0) trivial).restrict (g j0) trivial) (lY j0) (Equiv.refl _) :=
    ⟨fun v x => by cases v; exact hsqx j0 _, fun k => hbδ j0 k⟩
  have h01 := (infra_78_tiedFree_host_target (g j0)
    ((infra_78_markTuple (pair j0) (b j0)).restrict (g j0) trivial) trivial hR0 rfl rfl hqκ
    (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 (h5 j0)
  have h0 := infra_78_tiedFree_host_source (g j0) trivial hR0' rfl rfl hqκ
    (p.restrict (lX j0) trivial) (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) h01
  have hS0 := infra_78_sameGalois_of_hostRel (P := P) trivial trivial hR0
  have hmix : IsTiedFreeMixed (SystemArrow.comp ι0 (g j0)) pA
      (p.restrict (lX j0) trivial) eA :=
    infra_79_tiedFreeMixed_right_congr (qB := infra_78_markTuple (pair j0) (b j0))
      (qB' := p.restrict (lX j0) trivial) (SystemArrow.comp ι0 (g j0)) eA (Equiv.refl _)
      (hseed j0) hS0 hpA hνκ hνκ
  have hstage := infra_78_chain_stage_free P σ hσ hκ hrec hσSucc C p rfl hidx Xb (g j0) trivial
    h0 hAll
  exact infra_78_general_limit_invariant C p Xb (g j0) trivial hAll
    ⟨0, C.hlim.1, hD C (SystemArrow.comp ι0 (g j0)) trivial p eA rfl hmix hstage⟩

end LimitAssemblyDef77


section LimitCoconeDef77
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

/-- **Invariant (5) at a limit for any covering cocone, under Definition 7.7 (proved, cycle
93).** As `infra_78_limit_inv5_cocone`, with the cofinality hypothesis replaced by the per-stage
seed and Definition 7.7 for `pA` at `κ` (as `infra_78_matrix_limit_step_def77`). -/
theorem infra_78_limit_inv5_cocone_def77 (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (hrec : κ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ κ)
    {δ : (Order.succ ρ).ord.ToType}
    (hδ : Order.IsSuccLimit δ) (X Y : Set.Iio δ → P.scheme.Object κ hκ)
    (pair : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
      (P.scheme.asSystem hκ (Y j)))
    (sX : ∀ {a b : Set.Iio δ}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a)) (P.scheme.asSystem hκ (X b)))
    (hXt : ∀ {a b c : Set.Iio δ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sX (h₁.trans h₂) = SystemArrow.comp (sX h₁) (sX h₂))
    (Xb : P.scheme.Object κ hκ)
    (g : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb) (P.scheme.asSystem hκ (X j)))
    (hg : ∀ {a b : Set.Iio δ} (h : a ≤ b), SystemArrow.comp (g a) (sX h) = g b)
    {uIdx : Type u} (b : ∀ j, uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ (Y j)))
    (hidx : #uIdx ≤ σ)
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {A : P.scheme.Object ν hν}
    (pA : TupleOver K oneVertexShape P.scheme hν A) (hνκ : ν ≤ κ) (hpA : #pA.idx < ν)
    (ι0 : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hκ Xb))
    (eA : pA.idx ≃ uIdx)
    (hseed : ∀ j, IsTiedFreeMixed (SystemArrow.comp ι0 (g j)) pA
      (infra_78_markTuple (pair j) (b j)) eA)
    (hD : ∀ (C : SameLevelChain P hκ)
      (gA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A)
        (P.scheme.asSystem hκ (C.obj 0 C.hlim.1)))
      (_hgA : P.scheme.permitted (X := A) (Y := C.obj 0 C.hlim.1) gA)
      (bU : TupleOver K oneVertexShape P.scheme hκ C.unionObj) (e : pA.idx ≃ bU.idx),
      bU.ν = κ →
      IsTiedFreeMixed gA pA (bU.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) e →
      (∀ (i : Ordinal.{u}) (hi : i < C.δ),
        IsTiedFree (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))
          (bU.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1))
          (bU.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)) →
      IsTiedFree (C.toUnion 0 C.hlim.1)
        (bU.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) bU (Equiv.refl _))
    (h5 : ∀ j, IsTiedFree (g j) ((infra_78_markTuple (pair j) (b j)).restrict (g j) trivial)
      (infra_78_markTuple (pair j) (b j)) (Equiv.refl _))
    (Xδ Yδ : P.scheme.Object κ hκ)
    (lX : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j)) (P.scheme.asSystem hκ Xδ))
    (lY : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y j)) (P.scheme.asSystem hκ Yδ))
    (pδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xδ) (P.scheme.asSystem hκ Yδ))
    (hcX : ∀ {a c : Set.Iio δ} (h : a ≤ c), SystemArrow.comp (sX h) (lX c) = lX a)
    (hsq : ∀ j, SystemArrow.comp (pair j) (lY j) = SystemArrow.comp (lX j) pδ)
    (hcovX : ∀ x : (Xδ.model).carrier, ∃ j y, (lX j).onVertex PUnit.unit y = x)
    (gδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb) (P.scheme.asSystem hκ Xδ))
    (hgδ : ∀ j, SystemArrow.comp (g j) (lX j) = gδ)
    (bδ : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Yδ))
    (hbδ : ∀ j k, bδ k = pushOcc (lY j) (b j k)) :
    IsTiedFree gδ ((infra_78_markTuple pδ bδ).restrict gδ trivial)
      (infra_78_markTuple pδ bδ) (Equiv.refl _) := by
  classical
  let C := infra_78_partialChain hδ X sX hXt Xδ lX hcX hcovX
  let j0 : Set.Iio δ := ⟨infra_78_stg δ 0 C.hlim.1, infra_78_stg_lt δ 0 C.hlim.1⟩
  obtain rfl : SystemArrow.comp (g j0) (lX j0) = gδ := hgδ j0
  have hqκ : #uIdx < κ := hidx.trans_lt (Order.succ_le_iff.1 hσSucc)
  let p : TupleOver K oneVertexShape P.scheme hκ C.unionObj := infra_78_markTuple pδ bδ
  have hsqx : ∀ j (x : (X j).model.carrier),
      (lY j).onVertex PUnit.unit ((pair j).onVertex PUnit.unit x) =
        pδ.onVertex PUnit.unit ((lX j).onVertex PUnit.unit x) := fun j x =>
    DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hsq j)) x
  have hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree
        (SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
          (SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (P.scheme.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) trivial
            (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _) := by
    intro i hi
    let ji : Set.Iio δ := ⟨infra_78_stg δ i hi, infra_78_stg_lt δ i hi⟩
    have e1 : SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) =
        g ji := hg _
    have hR : infra_78_HostRel (infra_78_markTuple (pair ji) (b ji))
        (p.restrict (lX ji) trivial) (lY ji) (Equiv.refl _) :=
      ⟨fun v x => by cases v; exact hsqx ji x, fun k => hbδ ji k⟩
    have hR' : infra_78_HostRel ((infra_78_markTuple (pair ji) (b ji)).restrict (g ji) trivial)
        ((p.restrict (lX ji) trivial).restrict (g ji) trivial) (lY ji) (Equiv.refl _) :=
      ⟨fun v x => by cases v; exact hsqx ji _, fun k => hbδ ji k⟩
    have h1 := (infra_78_tiedFree_host_target (g ji)
      ((infra_78_markTuple (pair ji) (b ji)).restrict (g ji) trivial) trivial hR rfl rfl hqκ
      (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 (h5 ji)
    have h2 := infra_78_tiedFree_host_source (g ji) trivial hR' rfl rfl hqκ
      (p.restrict (lX ji) trivial) (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) h1
    exact infra_78_tiedFree_congr_arrow trivial trivial (p.restrict (lX ji) trivial) e1.symm h2
  have hR0 : infra_78_HostRel (infra_78_markTuple (pair j0) (b j0))
      (p.restrict (lX j0) trivial) (lY j0) (Equiv.refl _) :=
    ⟨fun v x => by cases v; exact hsqx j0 x, fun k => hbδ j0 k⟩
  have hR0' : infra_78_HostRel ((infra_78_markTuple (pair j0) (b j0)).restrict (g j0) trivial)
      ((p.restrict (lX j0) trivial).restrict (g j0) trivial) (lY j0) (Equiv.refl _) :=
    ⟨fun v x => by cases v; exact hsqx j0 _, fun k => hbδ j0 k⟩
  have h01 := (infra_78_tiedFree_host_target (g j0)
    ((infra_78_markTuple (pair j0) (b j0)).restrict (g j0) trivial) trivial hR0 rfl rfl hqκ
    (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 (h5 j0)
  have h0 := infra_78_tiedFree_host_source (g j0) trivial hR0' rfl rfl hqκ
    (p.restrict (lX j0) trivial) (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) h01
  have hS0 := infra_78_sameGalois_of_hostRel (P := P) trivial trivial hR0
  have hmix : IsTiedFreeMixed (SystemArrow.comp ι0 (g j0)) pA
      (p.restrict (lX j0) trivial) eA :=
    infra_79_tiedFreeMixed_right_congr (qB := infra_78_markTuple (pair j0) (b j0))
      (qB' := p.restrict (lX j0) trivial) (SystemArrow.comp ι0 (g j0)) eA (Equiv.refl _)
      (hseed j0) hS0 hpA hνκ hνκ
  have hstage := infra_78_chain_stage_free P σ hσ hκ hrec hσSucc C p rfl hidx Xb (g j0) trivial
    h0 hAll
  exact infra_78_general_limit_invariant C p Xb (g j0) trivial hAll
    ⟨0, C.hlim.1, hD C (SystemArrow.comp ι0 (g j0)) trivial p eA rfl hmix hstage⟩

end LimitCoconeDef77


section SeedInv5Def77
variable {P : SingleModelData K} {κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}
variable (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
  {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ) {uIdx cIdx L : Type u}
  {ρ : Cardinal.{u}} (hρκ : Order.succ ρ < μ)
  (Xb : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)) {ℓ : Cardinal.{u}}
  (hℓel : ℓ ∈ P.eligible)
  (cand : (Order.succ ρ).ord.ToType →
    Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx) →
    L → cIdx → μ.ord.ToType)
  (s0 : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
  (e0 : Infra78MarkData μ uIdx)

include hρκ in
/-- **Invariant (5) at every stage under Definition 7.7 (proved, cycle 93).** As
`infra_78_rc_inv5_all`, with the cofinality hypothesis replaced by: every stage satisfying (5)
carries the seed (its mark is the mixed tied free lift of `pA` along `A → X_b → X_k`; in the
assembly this is `infra_78_stage_transport` + `infra_78_tiedFreeMixed_trans`), and Definition 7.7
for `pA` at the level `μ`. Limits use `infra_78_limit_inv5_cocone_def77`. -/
theorem infra_78_rc_inv5_all_def77 (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {A : P.scheme.Object ν hν}
    (pA : TupleOver K oneVertexShape P.scheme hν A) (hνκ : ν ≤ μ) (hpA : #pA.idx < ν)
    (ι0 : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem (Tail.mem (infra_73_tail P σ hσ) hμT) Xb))
    (eA : pA.idx ≃ uIdx)
    (hseed : ∀ (k : (Order.succ ρ).ord.ToType)
      (h : infra_78_StageInv5 Xb (infra_78_rcObj Xb hℓel cand s0 e0 k)),
      IsTiedFreeMixed (SystemArrow.comp ι0 (infra_78_toArr h.1)) pA
        (infra_78_markTuple (infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 k).hp)
          (infra_78_stageMark (infra_78_rcObj Xb hℓel cand s0 e0 k))) eA)
    (hD : ∀ (C : SameLevelChain P (Tail.mem (infra_73_tail P σ hσ) hμT))
      (gA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A)
        (P.scheme.asSystem (Tail.mem (infra_73_tail P σ hσ) hμT) (C.obj 0 C.hlim.1)))
      (_hgA : P.scheme.permitted (X := A) (Y := C.obj 0 C.hlim.1) gA)
      (bU : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) C.unionObj) (e : pA.idx ≃ bU.idx),
      bU.ν = μ →
      IsTiedFreeMixed gA pA (bU.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) e →
      (∀ (i : Ordinal.{u}) (hi : i < C.δ),
        IsTiedFree (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))
          (bU.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1))
          (bU.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)) →
      IsTiedFree (C.toUnion 0 C.hlim.1)
        (bU.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) bU (Equiv.refl _))
    (h5seed : infra_78_StageInv5 Xb s0) (k : (Order.succ ρ).ord.ToType) :
    infra_78_StageInv5 Xb (infra_78_rcObj Xb hℓel cand s0 e0 k) := by
  have hsop := infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand
  obtain ⟨hA, -, -⟩ := infra_78_pairChain_laws hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) hsop
  have hM := infra_78_pairMatrix_compLaw hρκ s0 (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand)
    (infra_78_limMarkE e0) hsop
  have hCont := infra_78_pairMatrix_contAtLimits hρκ s0
    (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand) (infra_78_limMarkE e0) hsop
  have hu : #uIdx ≤ σ := (Cardinal.mk_le_of_injective Sum.inl_injective).trans hidx
  induction k using WellFoundedLT.induction with
  | _ k IH =>
  rcases infra_78_stage_trichotomy k with hmin | ⟨β, hβ⟩ | hk
  · have h : infra_78_rcObj Xb hℓel cand s0 e0 k = s0 := infra_78_pairMatrix_min s0 _ _ hmin
    rw [h]; exact h5seed
  · obtain ⟨-, -, -, -, -, -, h5, -⟩ := infra_78_opMatrix_succ P σ hσ hμT hρκ Xb
      (infra_78_rcl ρ hℓel) cand hidx s0 (infra_78_limMarkE e0) hβ (IH β hβ.lt)
    exact h5
  -- limit stage
  have hsX : ∀ {i j : (Order.succ ρ).ord.ToType} (h : i ≤ j) x,
      ((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepX h).onVertex PUnit.unit x =
        (infra_78_rcMap Xb hℓel cand s0 e0 i j).1 x := fun h x =>
    infra_78_pairMatrix_stepX_apply hρκ s0 _ _ hsop h x
  have hsY : ∀ {i j : (Order.succ ρ).ord.ToType} (h : i ≤ j) x,
      ((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepY h).onVertex PUnit.unit x =
        (infra_78_rcMap Xb hℓel cand s0 e0 i j).2 x := fun h x =>
    infra_78_pairMatrix_stepY_apply hρκ s0 _ _ hsop h x
  have IH' : ∀ j : Set.Iio k, infra_78_StageInv5 Xb (infra_78_rcObj Xb hℓel cand s0 e0 j.1) := fun j => IH j.1 j.2
  have hcoh := infra_78_opMatrix_coherent hρκ Xb (infra_78_rcl ρ hℓel) cand s0 e0
  obtain ⟨j0, hj0⟩ := not_isMin_iff.1 hk.not_isMin
  have hgk : infra_78_IsArr Xb (infra_78_rcObj Xb hℓel cand s0 e0 k).X (infra_78_rcObj Xb hℓel cand s0 e0 k).e.g := by
    have e := (hcoh j0 k hj0.le).1
    have h := infra_78_isArr_comp (IH j0 hj0).1 (hA j0 k hj0.le).1
    change infra_78_IsArr Xb (infra_78_rcObj Xb hℓel cand s0 e0 k).X ((infra_78_rcMap Xb hℓel cand s0 e0 j0 k).1 ∘ (infra_78_rcObj Xb hℓel cand s0 e0 j0).e.g) at h
    rw [← e] at h
    exact h
  refine ⟨hgk, ?_⟩
  exact infra_78_limit_inv5_cocone_def77 σ hσ hμT.1 (infra_73_tail_succ hμT) hk
    (fun j => (infra_78_rcObj Xb hℓel cand s0 e0 j.1).X) (fun j => (infra_78_rcObj Xb hℓel cand s0 e0 j.1).Y) (fun j => infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 j.1).hp)
    (fun {a b} h => (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepX (show a.1 ≤ b.1 from h))
    (fun h₁ h₂ => hM.1 h₁ h₂) Xb
    (fun j => infra_78_toArr (IH' j).1)
    (fun {a b} h => infra_78_arrow_ext fun x =>
      ((hsX (show a.1 ≤ b.1 from h) _).trans ((congrArg _ (infra_78_toArr_apply _ x)).trans
        (congrFun (hcoh a.1 b.1 h).1 x).symm)).trans (infra_78_toArr_apply _ x).symm)
    (fun j => infra_78_stageMark (infra_78_rcObj Xb hℓel cand s0 e0 j.1)) hu
    pA hνκ hpA ι0 eA (fun j => hseed j.1 (IH' j)) hD
    (fun j => (IH' j).2)
    (infra_78_rcObj Xb hℓel cand s0 e0 k).X (infra_78_rcObj Xb hℓel cand s0 e0 k).Y (fun j => (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepX j.2.le) (fun j => (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepY j.2.le)
    (infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 k).hp)
    (fun {a c'} h => (hM.1 (show a.1 ≤ c'.1 from h) c'.2.le).symm)
    (fun j => (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).comm j.2.le)
    (fun x => by
      obtain ⟨j, hj, y, hy⟩ := hCont.1 k hk x
      exact ⟨⟨j, hj⟩, y, hy⟩)
    (infra_78_toArr hgk)
    (fun j => infra_78_arrow_ext fun x =>
      ((hsX j.2.le _).trans ((congrArg _ (infra_78_toArr_apply _ x)).trans
        (congrFun (hcoh j.1 k j.2.le).1 x).symm)).trans (infra_78_toArr_apply _ x).symm)
    (infra_78_stageMark (infra_78_rcObj Xb hℓel cand s0 e0 k))
    (fun j u => by
      show (⟨PUnit.unit, (infra_78_rcObj Xb hℓel cand s0 e0 k).e.b u⟩ : Occurrence K oneVertexShape _) =
        ⟨PUnit.unit, ((infra_78_rcMatrix hρκ Xb hℓel cand s0 e0).stepY j.2.le).onVertex PUnit.unit ((infra_78_rcObj Xb hℓel cand s0 e0 j.1).e.b u)⟩
      rw [(hcoh j.1 k j.2.le).2]
      exact congrArg (fun y => (⟨PUnit.unit, y⟩ : Occurrence K oneVertexShape
        (P.scheme.asSystem _ (infra_78_rcObj Xb hℓel cand s0 e0 k).Y))) (hsY j.2.le _).symm)

end SeedInv5Def77

section StageSeedDef77
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible} {uIdx cIdx L : Type u}
variable (hρκ : Order.succ ρ < κ) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
  (cand : (Order.succ ρ).ord.ToType → Infra78Stage P hκ (Infra78MarkData κ uIdx) →
    L → cIdx → κ.ord.ToType)
  (s0 : Infra78Stage P hκ (Infra78MarkData κ uIdx)) (e0 : Infra78MarkData κ uIdx)

include hρκ in
/-- **Every stage carries the seed (proved, cycle 93).** In the recursion matrix whose seed stage
has the identity base map, if the seed mark is the mixed tied free lift of its restriction along
`ι0 : A → X_0` and that restriction answers small tests as `pA` (`hDp`), then at every stage `k`
satisfying invariant (5) the stage mark is the mixed tied free lift of `pA` along `A → X_0 → X_k`
(`infra_78_stage_transport`, mixed transitivity `infra_78_tiedFreeMixed_trans`, and
`infra_78_tiedFreeMixed_left_congr`). This discharges the seed hypothesis of
`infra_78_rc_inv5_all_def77`. -/
theorem infra_78_rc_stage_seed {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {A : P.scheme.Object ν hν} (pA : TupleOver K oneVertexShape P.scheme hν A)
    (eA : pA.idx ≃ uIdx)
    (ι0 : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hκ s0.X))
    (hg0 : s0.e.g = id) (hidx : #uIdx < ν) (hνκ : ν ≤ κ)
    (H0 : IsTiedFreeMixed ι0
      ((infra_78_markTuple (infra_78_toArr s0.hp) (infra_78_stageMark s0)).restrict ι0 trivial)
      (infra_78_markTuple (infra_78_toArr s0.hp) (infra_78_stageMark s0)) (Equiv.refl _))
    (hDp : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      #β < ν →
      P.scheme.DiagramEq (X := pA.host) (Y := s0.Y) (typeJoint (p := pA) Z)
        (fun s => typeJoint (p := (infra_78_markTuple (infra_78_toArr s0.hp)
          (infra_78_stageMark s0)).restrict ι0 trivial) Z (Sum.map eA id s)))
    {i0 : (Order.succ ρ).ord.ToType} (hmin : IsMin i0) (k : (Order.succ ρ).ord.ToType)
    (h : infra_78_StageInv5 s0.X (infra_78_rcObj s0.X hℓel cand s0 e0 k)) :
    IsTiedFreeMixed (SystemArrow.comp ι0 (infra_78_toArr h.1)) pA
      (infra_78_markTuple (infra_78_toArr (infra_78_rcObj s0.X hℓel cand s0 e0 k).hp)
        (infra_78_stageMark (infra_78_rcObj s0.X hℓel cand s0 e0 k))) eA := by
  obtain ⟨-, -, F1, F2⟩ := infra_78_stage_transport hρκ s0.X hℓel cand s0 e0 ι0 hg0 hidx hνκ H0
    hmin k (infra_78_toArr h.1) (fun x => infra_78_toArr_apply h.1 x)
  have hT := infra_78_tiedFreeMixed_trans ι0 trivial (infra_78_toArr h.1) trivial _ hνκ F1 h.2
  let q := infra_78_markTuple (infra_78_toArr (infra_78_rcObj s0.X hℓel cand s0 e0 k).hp)
    (infra_78_stageMark (infra_78_rcObj s0.X hℓel cand s0 e0 k))
  have hD' : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      #β < ν →
      P.scheme.DiagramEq (X := pA.host) (Y := q.host) (typeJoint (p := pA) Z)
        (fun s => typeJoint (p := q.restrict (SystemArrow.comp ι0 (infra_78_toArr h.1)) trivial)
          Z (Sum.map eA id s)) := by
    intro β Z hβ
    refine P.scheme.diagram_trans _ _ _ _ _ _ (hDp Z hβ) ?_
    exact infra_612_dEq_comp (F2 Z hβ) (Sum.map eA id) (fun _ => rfl)
      (fun c => by rcases c with u | j <;> rfl)
  exact infra_78_tiedFreeMixed_left_congr
    (q := q.restrict (SystemArrow.comp ι0 (infra_78_toArr h.1)) trivial) (q' := pA) (qB := q)
    _ (Equiv.refl _) eA hT (fun Z hβ => hD' Z hβ)

end StageSeedDef77

/-- **Level choices for the Prop 7.8 matrix inside a given cofinal set of closed levels
(proved, cycle 93).** As `infra_78_assembly_levels`, with the matrix level `κ` taken in a
prescribed cofinal set `S ⊆ infra_78_closedTail P` (e.g. the Definition 7.7 levels of the mark). -/
theorem infra_78_assembly_levels_in (P : SingleModelData K) {lam : Cardinal.{u}}
    (hlam : lam ∈ infra_78_closedTail P) {θ : Cardinal.{u}} (hθ : ℵ₀ ≤ θ) (hθlam : θ < lam)
    (S : Set Cardinal.{u}) (hS : ∀ x, ∃ κ, x ≤ κ ∧ κ ∈ S) (hSC : S ⊆ infra_78_closedTail P) :
    ∃ ρ κ : Cardinal.{u}, lam < ρ ∧ ρ ^ lam = ρ ∧ Order.succ ρ < κ ∧ lam ≤ κ ∧
      κ ∈ infra_73_tailSet P lam ∧ κ ∈ infra_73_tailSet P θ ∧
      lam ∈ infra_73_tailSet P (infra_76_sigma2 P θ) ∧ Order.succ θ ≤ lam ∧ κ ∈ S := by
  obtain ⟨hel, htail, -⟩ := hlam
  have hlamInf : ℵ₀ ≤ lam := P.aleph0_le hel
  have hθT : lam ∈ infra_73_tailSet P θ := htail θ hθ hθlam
  have hhθ : infra_73_h P θ < lam := infra_73_h_lt hel hθT
  have hhθinf : ℵ₀ ≤ infra_73_h P θ := hθ.trans (infra_76_lt_h P θ).le
  have hh2T : lam ∈ infra_73_tailSet P (infra_73_h P θ) := htail _ hhθinf hhθ
  have h2 : infra_76_sigma2 P θ < lam := infra_73_h_lt hel hh2T
  have h2inf : ℵ₀ ≤ infra_76_sigma2 P θ := hhθinf.trans (infra_76_lt_h P _).le
  have hσ2T : lam ∈ infra_73_tailSet P (infra_76_sigma2 P θ) := htail _ h2inf h2
  obtain ⟨κ, hκle, hκS⟩ := hS (Order.succ (Order.succ (2 ^ lam)))
  have hρκ : Order.succ (2 ^ lam) < κ :=
    (Order.lt_succ_of_not_isMax (not_isMax _)).trans_le hκle
  have hlκ : lam < κ :=
    (cantor lam).trans ((Order.lt_succ_of_not_isMax (not_isMax _)).trans hρκ)
  have hκC := hSC hκS
  refine ⟨2 ^ lam, κ, cantor lam, ?_, hρκ, hlκ.le, hκC.2.1 lam hlamInf hlκ,
    hκC.2.1 θ hθ (hθlam.trans hlκ), hσ2T, Order.succ_le_of_lt hθlam, hκS⟩
  rw [← power_mul, mul_eq_self hlamInf]

/-- Definition 7.7 for `p` at one level `κ` (the body of `SatisfiesContinuityTied` at `κ`). -/
def infra_78_def77_at {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} (p : TupleOver K oneVertexShape P.scheme hμ A)
    (κ : Cardinal.{u}) (hκ : κ ∈ P.eligible) : Prop :=
  ∀ (C : SameLevelChain P hκ)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A)
      (P.scheme.asSystem hκ (C.obj 0 C.hlim.1)))
    (_hg : P.scheme.permitted (X := A) (Y := C.obj 0 C.hlim.1) g)
    (b : TupleOver K oneVertexShape P.scheme hκ C.unionObj) (e : p.idx ≃ b.idx),
    b.ν = κ →
    IsTiedFreeMixed g p (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) e →
    (∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))
        (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1))
        (b.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)) →
    IsTiedFree (C.toUnion 0 C.hlim.1)
      (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) b (Equiv.refl _)

/-- **Prop 7.8 assembly for bounded marks, closed-level reading of Definition 7.7 (proved,
cycle 93).** As `infra_78_matrix_assembly_level`, for a bounded mark `|p| ≤ θ` (no finiteness),
assuming Definition 7.7 for `p` at every matrix level `κ` closed at `λ` (`infra_73_tailSet P λ`;
English: "holds at every sufficiently closed eligible level to which `p` is freely lifted").
Limits of the recursion use Definition 7.7 (`infra_78_rc_inv5_all_def77`, seed per stage by
`infra_78_rc_stage_seed`); no cofinality hypothesis. Deriving the closed-level reading from
`SatisfiesContinuityTied` (whose tail `T` is only cofinal) is tracked as
`infra_78_def77_tail_meet`. -/
theorem infra_78_general_assembly_closed (P : SingleModelData K) :
    ∀ μ (hμ : μ ∈ infra_78_closedTail P)
      (X : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
      (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X)
      (θ : Cardinal.{u}),
      #p.idx ≤ θ → p.ν = μ → aleph0 ≤ θ → θ < μ →
      (∀ x, ∃ κ, x ≤ κ ∧ ∃ hκC : κ ∈ infra_78_closedTail P, infra_78_def77_at p κ hκC.1) →
      ∃ (U : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ U))
        (hf : P.scheme.permitted (X := X) (Y := U) f)
        (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
        SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) ∧
        ∀ {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
          #cIdx ≤ θ →
          IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
            (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx)) := by
  classical
  intro μ hμ X p θ hidxθ hpν hθ hθμ hcont
  have hel : μ ∈ P.eligible := Tail.mem (infra_78_closedTail_tail P) hμ
  have hμInf : ℵ₀ ≤ μ := P.aleph0_le hel
  obtain ⟨ρ, κ, hlρ, hpow, hρκ, hlκ, hκT, hκTθ, hlT2, hθsucc, ⟨hκC, hdef⟩⟩ :=
    infra_78_assembly_levels_in P hμ hθ hθμ
      {κ | ∃ hκC : κ ∈ infra_78_closedTail P, infra_78_def77_at p κ hκC.1}
      (fun x => by obtain ⟨κ, hx, h⟩ := hcont x; exact ⟨κ, hx, h⟩) (fun κ h => h.1)
  have hκel : κ ∈ P.eligible := Tail.mem (infra_73_tail P μ hμInf) hκT
  have hrecμθ : μ ∈ recursionClosedLevels P θ := (hμ.2.1 θ hθ hθμ).1
  have hrecκθ : κ ∈ recursionClosedLevels P θ := hκTθ.1
  have hidxμ : #p.idx < μ := hidxθ.trans_lt hθμ
  have hidxρ : #p.idx ≤ ρ := hidxμ.le.trans hlρ.le
  obtain ⟨X0, Y0, ι0, p0, hp0, b0, seq, ⟨-, htest, hlong, hτν⟩, hD, hT, hIcard, hS⟩ :=
    infra_78_seed_stage P θ hθ (hν := hel) hrecμθ hθsucc hκel hrecκθ hlκ X p hpν hidxθ θ hθμ
      ρ hel hlκ hlρ hpow hlρ.le hidxρ
  have hne : Nonempty κ.ord.ToType := by
    rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_ord_toType]
    exact (aleph0_pos.trans_le (P.aleph0_le hκel)).ne'
  obtain ⟨y⟩ := hne
  obtain ⟨hg0, h5seed, hsub, h0, hclosed, hS0⟩ := hS y
  set I := infra_78_anchorImage ι0 seq with hIdef
  set s0 := infra_78_seedStage ρ hel X0 Y0 p0 hp0 id b0 (infra_78_seedSet I b0 y) with hs0def
  have hc : #θ.ord.ToType ≤ μ := by rw [Cardinal.mk_ord_toType]; exact hθμ.le
  have hidx : #(p.idx ⊕ θ.ord.ToType) ≤ μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact (add_le_add hidxμ.le hc).trans (add_eq_self hμInf).le
  have hne0 : Nonempty (Order.succ ρ).ord.ToType := by
    rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_ord_toType]
    exact Cardinal.succ_ne_zero ρ
  obtain ⟨i00, -, hi00⟩ := (wellFounded_lt (α := (Order.succ ρ).ord.ToType)).has_min Set.univ
    ⟨Classical.arbitrary _, trivial⟩
  have hm00 : IsMin i00 := fun b _ => not_lt.1 (hi00 b trivial)
  have hDp : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hel X)),
      #β < μ →
      P.scheme.DiagramEq (X := p.host) (Y := s0.Y) (typeJoint (p := p) Z)
        (fun s => typeJoint (p := (infra_78_markTuple (infra_78_toArr s0.hp)
          (infra_78_stageMark s0)).restrict ι0 trivial) Z (Sum.map (Equiv.refl p.idx) id s)) := by
    intro β Z hβ
    refine infra_73_diagramEq_of_eq (hD Z hβ) ?_ ?_
    · rintro (u | x) <;> rfl
    · rintro (u | x) <;> rfl
  have h5all := infra_78_rc_inv5_all_def77 P μ hμInf hκT hρκ X0 hel (infra_78_candS θ.ord.ToType)
    s0 s0.e hidx p hlκ hidxμ ι0 (Equiv.refl _)
    (fun k h => infra_78_rc_stage_seed hρκ hel (infra_78_candS θ.ord.ToType) s0 s0.e p
      (Equiv.refl _) ι0 hg0 hidxμ hlκ hT hDp hm00 k h)
    hdef h5seed
  obtain ⟨i, -, hiso⟩ := infra_78_isolation_over_A P μ hμInf hκT (uIdx := p.idx)
    (cIdx := θ.ord.ToType) hρκ X0 hel s0 s0.e hidx h5all hlρ hpow hc h5seed hS0 h0 hclosed hlκ
    le_rfl hθ hθsucc hidxθ (Cardinal.mk_ord_toType θ).ge θ hθ le_rfl hlT2 hκTθ
  obtain ⟨i0, -, hi0⟩ := (wellFounded_lt (α := (Order.succ ρ).ord.ToType)).has_min Set.univ
    ⟨i, trivial⟩
  have hm : IsMin i0 := fun b _ => not_lt.1 (hi0 b trivial)
  have hii : i0 ≤ i := not_lt.1 (hi0 i trivial)
  have hmin0 : infra_78_rcObj X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i0 = s0 :=
    infra_78_pairMatrix_min s0 _ _ hm
  obtain ⟨hg, h5i⟩ := h5all i
  obtain ⟨hgx, hbu, F1, F2⟩ := infra_78_stage_transport hρκ X0 hel
    (infra_78_candS θ.ord.ToType) s0 s0.e ι0 rfl hidxμ hlκ hT hm i (infra_78_toArr hg)
    (fun x => infra_78_toArr_apply hg x)
  have hfwd := infra_78_rc_forward hρκ X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i0 i hii
  have hR0 : ∀ z, z ∈ infra_78_seedSet I b0 y →
      z ∈ (infra_78_rcObj X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i0).e.R := by
    intro z hz; rw [hmin0]; exact hsub hz
  let s₀ : Set (κ.ord.ToType ⊕ κ.ord.ToType) :=
    Sum.inl '' ((infra_78_rcMap X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i0 i).1 '' I) ∪
      Sum.inr '' Set.range (infra_78_rcObj X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i).e.b
  have hs₀R : s₀ ⊆ infra_78_rcSets hρκ X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i := by
    rintro z (⟨_, ⟨x, hx, rfl⟩, rfl⟩ | ⟨_, ⟨u, rfl⟩, rfl⟩)
    · exact hfwd ⟨Sum.inl x, hR0 _ (Or.inl ⟨x, hx, rfl⟩), rfl⟩
    · rw [hbu u]
      exact hfwd ⟨Sum.inr (b0 u), hR0 _ (Or.inr ⟨b0 u, Set.mem_insert_of_mem _ ⟨u, rfl⟩, rfl⟩),
        rfl⟩
  have hs₀card : #s₀ ≤ μ := by
    refine (Cardinal.mk_union_le _ _).trans ?_
    refine (add_le_add (Cardinal.mk_image_le.trans (Cardinal.mk_image_le.trans hIcard.le))
      (Cardinal.mk_image_le.trans (Cardinal.mk_range_le.trans hidxμ.le))).trans ?_
    exact (add_eq_self hμInf).le
  obtain ⟨A, U, jA, jU, gu, bU, hsq, hcov, -, -, hbY, hisoU⟩ :=
    hiso s₀ hs₀R hs₀card (fun k => Or.inr ⟨_, ⟨k, rfl⟩, rfl⟩)
  let q := infra_78_markTuple
    (infra_78_toArr (infra_78_rcObj X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i).hp)
    (infra_78_stageMark (infra_78_rcObj X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i))
  let ι := SystemArrow.comp ι0 (infra_78_toArr hg)
  have hTq : IsTiedFreeMixed ι (q.restrict ι trivial) q (Equiv.refl _) :=
    infra_78_tiedFreeMixed_trans ι0 trivial (infra_78_toArr hg) trivial q hlκ F1 h5i
  have hseedDE : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hel X)),
      #β < μ →
      P.scheme.DiagramEq (X := p.host) (Y := q.host)
        (alignJoint (Equiv.refl _) (typeJoint (p := p) Z)) (typeJoint (p := q.restrict ι trivial) Z) := by
    intro β Z hβ
    have h := P.scheme.diagram_trans _ _ _ _ _ _ (hD Z hβ) (F2 Z hβ)
    refine infra_73_diagramEq_of_eq h ?_ ?_
    · rintro (u | x) <;> rfl
    · rintro (u | x) <;> rfl
  let seqq : ApproximationSequence (q.restrict ι trivial) :=
    infra_78_seq_diagram_transfer (t2 := q.restrict ι trivial) (Equiv.refl p.idx) seq
      (fun Z hZ => by
        refine infra_73_diagramEq_of_eq (hseedDE Z (hZ.trans_lt hτν)) ?_ ?_
        · rintro (u | x) <;> rfl
        · rintro (u | x) <;> rfl)
  have hanch : ∀ a k, ∃ y, jA.onVertex PUnit.unit y =
      ι.onVertex PUnit.unit (seqq.family a k).2 := by
    intro a k
    have hmemI : ι0.onVertex PUnit.unit (seq.family a k).2 ∈ I :=
      ⟨(seq.family a k).2, ⟨(a, k), rfl⟩, rfl⟩
    have hval : ι.onVertex PUnit.unit (seqq.family a k).2 =
        (infra_78_rcMap X0 hel (infra_78_candS θ.ord.ToType) s0 s0.e i0 i).1
          (ι0.onVertex PUnit.unit (seq.family a k).2) := by
      show (infra_78_toArr hg).onVertex PUnit.unit (ι0.onVertex PUnit.unit (seq.family a k).2) = _
      rw [infra_78_toArr_apply hg]; exact hgx _
    rw [hval]
    rcases hcov (Or.inl ⟨_, ⟨_, hmemI, rfl⟩, rfl⟩) with ⟨_, ⟨y', hy⟩, he⟩ | ⟨_, -, he⟩
    · exact ⟨y', hy.trans (Sum.inl_injective he)⟩
    · exact (Sum.inr_ne_inl he).elim
  have hsq' : ∀ x, jU.onVertex PUnit.unit (gu.onVertex PUnit.unit x) =
      q.incl.onVertex PUnit.unit (jA.onVertex PUnit.unit x) := fun x =>
    congrArg (fun f => f.onVertex PUnit.unit x) hsq
  have hbU : ∀ k, q.val k = ⟨(bU k).1, jU.onVertex (bU k).1 (bU k).2⟩ := fun k => by
    show (⟨PUnit.unit, _⟩ : Occurrence K oneVertexShape _) =
      ⟨PUnit.unit, jU.onVertex PUnit.unit (bU k).2⟩
    rw [hbY k]
  obtain ⟨φ, hφ, -, hGal⟩ := infra_78_marginal_identify_level P θ hθ hel (hμ := hκel) hrecμθ
    hθμ hlκ (A := A) (U := U) p hpν hidxθ ι trivial q hlκ (Equiv.refl _) hseedDE hTq seqq
    htest hlong jA hanch gu jU hsq' bU hbU
  refine ⟨U, SystemArrow.comp φ gu, trivial, bU, hGal, ?_⟩
  intro cIdx c hc
  exact infra_78_iso_rename_asTuple φ hφ gu bU c (hisoU cIdx hc c)

/-- **Definition 7.7 is invariant under Galois type (proved, cycle 93).** Its hypotheses read `p`
only through mixed tied freeness, which depends only on small-test diagrams
(`infra_78_tiedFreeMixed_left_congr`, `infra_612_dEq_of_sameGalois`). -/
theorem infra_78_def77_at_congr {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {p p' : TupleOver K oneVertexShape P.scheme hμ A}
    (e2 : p'.idx ≃ p.idx)
    (h : SameGaloisType p p' (Equiv.refl p.idx) e2) (hidx : #p.idx < μ)
    {κ : Cardinal.{u}} {hκ : κ ∈ P.eligible} (H : infra_78_def77_at p κ hκ) :
    infra_78_def77_at p' κ hκ := by
  intro C g hg b e hbν hmix hst
  refine H C g hg b (e2.symm.trans e) hbν ?_ hst
  refine infra_78_tiedFreeMixed_left_congr (q := p') (q' := p)
    (qB := b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) g e
    e2.symm hmix ?_
  intro β Z hβ
  have D := infra_612_dEq_of_sameGalois h Z hidx hβ
  refine infra_73_diagramEq_of_eq D ?_ ?_
  · rintro (u | x) <;> rfl
  · rintro (u | x)
    · rfl
    · rfl

/-- **General Prop 7.8, closed-level reading of Definition 7.7 (proved, cycle 93).** The
`infra_78_general_statement` conclusion for every bounded mark `|p| ≤ θ` over `X`, hosted at any
eligible level, assuming Definition 7.7 for `p` at every level of `infra_73_tailSet P μ` (the
closed-level reading of "holds at every sufficiently closed eligible level"). Reduction to the
level copy as in `infra_78_marginal_general_level`, Definition 7.7 transported by
`infra_78_def77_at_congr`. Remaining for `infra_78_general` itself: `infra_78_def77_tail_meet`. -/
theorem infra_78_general_closed (P : SingleModelData K) :
    ∀ μ (hμ : μ ∈ infra_78_closedTail P)
      (X : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
      (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X)
      (θ : Cardinal.{u}),
      #p.idx ≤ θ →
      (∀ x, ∃ κ, x ≤ κ ∧ ∃ hκC : κ ∈ infra_78_closedTail P, infra_78_def77_at p κ hκC.1) →
      aleph0 ≤ θ → θ < μ →
      ∃ (U : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ U))
        (hf : P.scheme.permitted (X := X) (Y := U) f)
        (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
        SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) ∧
        ∀ {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
          #cIdx ≤ θ →
          IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
            (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx)) := by
  intro μ hμ X p θ hidxθ hcont hθ hθμ
  have hel : μ ∈ P.eligible := Tail.mem (infra_78_closedTail_tail P) hμ
  have hidxμ : #p.idx < μ := hidxθ.trans_lt hθμ
  obtain ⟨host, incl, hincl, val, h12⟩ := infra_612_exists_level_copy p hidxμ.le
  let p' : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X :=
    ⟨μ, Tail.mem (infra_78_closedTail_tail P) hμ, host, incl, hincl, p.idx, val⟩
  obtain ⟨U, f, hf, b, hgal, hiso⟩ :=
    infra_78_general_assembly_closed P μ hμ X p' θ hidxθ rfl hθ hθμ
      (fun x => by
        obtain ⟨κ, hx, hC, hd⟩ := hcont x
        exact ⟨κ, hx, hC, infra_78_def77_at_congr (p := p) (p' := p') (Equiv.refl _) h12 hidxμ hd⟩)
  refine ⟨U, f, hf, b, ?_, hiso⟩
  have hrec : μ ∈ recursionClosedLevels P θ := (hμ.2.1 θ hθ hθμ).1
  have h := infra_612_galois_trans_cross_level_right_base (t1 := p) (t2 := p')
    (t3 := asTuple f hf b) (e12 := Equiv.refl p.idx) (e32 := (Equiv.refl p.idx).symm) h12
    (SameGaloisType.swap_refl hgal) θ hθ hθμ hidxθ hrec rfl rfl
  simp only [Equiv.refl_trans] at h
  exact h

/-- **`infra_78_def77_tail_meet` (statement; open, needs a ruling).** Definition 7.7 as formalized
(`SatisfiesContinuityTied`, an existential cofinal set `T` of levels) yields Definition 7.7 at
every matrix level closed at `μ`. Not derivable as stated in general: `Tail` is only cofinality,
and `infra_73_tailSet P μ` is not upward closed, so the two sets may be disjoint. -/
def infra_78_def77_tail_meet_statement (P : SingleModelData K) : Prop :=
  ∀ μ (hμ : μ ∈ infra_78_closedTail P)
    (X : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
    (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X),
    SatisfiesContinuityTied p →
    ∀ x, ∃ κ, x ≤ κ ∧ ∃ hκC : κ ∈ infra_78_closedTail P, infra_78_def77_at p κ hκC.1

/-- **General Prop 7.8 from the tail meet (proved, cycle 93).** -/
theorem infra_78_general_of_tail_meet (P : SingleModelData K)
    (hmeet : infra_78_def77_tail_meet_statement P) : infra_78_general_statement P :=
  fun μ hμ X p θ hidxθ hp hθ hθμ =>
    infra_78_general_closed P μ hμ X p θ hidxθ (hmeet μ hμ X p hp) hθ hθμ

/-- **The tail meet when the Definition 7.7 levels are closed (proved, cycle 93).** If Definition
7.7 for `p` holds on a cofinal set `T` of levels contained in `infra_78_closedTail P` ("at every
sufficiently closed eligible level"; e.g. Theorem 7.13 (2), `infra_713_continuity`, produces
`T = infra_712_levels P ⊆ infra_78_closedTail P`), then the hypothesis of `infra_78_general_closed`
holds. Hence `infra_78_general` for every such mark. -/
theorem infra_78_def77_meet_of_closed {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}
    (p : TupleOver K oneVertexShape P.scheme hμ A) (T : Set Cardinal.{u})
    (hT : Tail P.eligible T) (hTC : T ⊆ infra_78_closedTail P)
    (H : ∀ μ' (hμ' : μ' ∈ T), μ ≤ μ' → infra_78_def77_at p μ' (Tail.mem hT hμ')) :
    ∀ x, ∃ κ, x ≤ κ ∧ ∃ hκC : κ ∈ infra_78_closedTail P, infra_78_def77_at p κ hκC.1 := by
  intro x
  obtain ⟨κ, hle, hκT⟩ := hT.2 (max x μ)
  exact ⟨κ, (le_max_left _ _).trans hle, hTC hκT, H κ hκT ((le_max_right _ _).trans hle)⟩

/-- **General Prop 7.8 for a mark whose Definition 7.7 levels are closed (proved, cycle 93).**
The `infra_78_general_statement` conclusion for a bounded mark `|p| ≤ θ` satisfying Definition 7.7
on a tail `T ⊆ infra_78_closedTail P` ("every sufficiently closed eligible level"). -/
theorem infra_78_general_of_closed_def77 (P : SingleModelData K) (μ : Cardinal.{u})
    (hμ : μ ∈ infra_78_closedTail P)
    (X : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
    (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X)
    (θ : Cardinal.{u}) (hidxθ : #p.idx ≤ θ) (T : Set Cardinal.{u}) (hT : Tail P.eligible T)
    (hTC : T ⊆ infra_78_closedTail P)
    (H : ∀ μ' (hμ' : μ' ∈ T), μ ≤ μ' → infra_78_def77_at p μ' (Tail.mem hT hμ'))
    (hθ : aleph0 ≤ θ) (hθμ : θ < μ) :
    ∃ (U : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ U))
      (hf : P.scheme.permitted (X := X) (Y := U) f)
      (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
      SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) ∧
      ∀ {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
        #cIdx ≤ θ →
        IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
          (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx)) :=
  infra_78_general_closed P μ hμ X p θ hidxθ (infra_78_def77_meet_of_closed p T hT hTC H) hθ hθμ

/-- **Theorem 7.9 descent step for a bounded mark (proved, cycle 93).** As `infra_79_descent`,
with the finite mark replaced by any mark of size `< ν` (finiteness was used only for
`|b, c| < ν`). Sub-step of `infra_79_general`. -/
theorem infra_79_descent_bounded (P : SingleModelData K) {ν l : Cardinal.{u}}
    (hνC : ν ∈ infra_615_closed P) (hlC : l ∈ infra_615_closed P)
    (hνT : ν ∈ infra_78_closedTail P) (hlT : l ∈ infra_78_closedTail P) (hνl : ν ≤ l)
    (A U : P.scheme.Object l hlC.1) (A' U' : P.scheme.Object ν hνC.1)
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A') (P.scheme.asSystem hlC.1 A))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 U') (P.scheme.asSystem hlC.1 U))
    (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hlC.1 A) (P.scheme.asSystem hlC.1 U))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hνC.1 A')
      (P.scheme.asSystem hνC.1 U'))
    (htoA : P.scheme.permitted (X := A') (Y := A) toA)
    (htoU : P.scheme.permitted (X := U') (Y := U) toU)
    (hincl : P.scheme.permitted (X := A) (Y := U) incl)
    (hincl' : P.scheme.permitted (X := A') (Y := U') incl')
    (hsq : ∀ v, (incl.onVertex v).comp (toA.onVertex v) =
      (toU.onVertex v).comp (incl'.onVertex v))
    {ι : Type u} (r : ι → SystemArrow K oneVertexShape
      (P.scheme.asSystem hlC.1 U) (P.scheme.asSystem hlC.1 A))
    (hιcard : #ι = ν) (_hr : ∀ i, P.scheme.permitted (X := U) (Y := A) (r i))
    (halmost : ∀ a : Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 A),
      Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2})
    (himg : ∀ i (x : ((P.scheme.asSystem hνC.1 U').obj PUnit.unit).carrier),
      ∃ y, toA.onVertex PUnit.unit y = (r i).onVertex PUnit.unit (toU.onVertex PUnit.unit x))
    {uIdx : Type u} (huν : #uIdx < ν)
    (b' : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 U'))
    (bU : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U))
    (hbU : ∀ k, bU k = ⟨(b' k).1, toU.onVertex (b' k).1 (b' k).2⟩)
    (hiso : ∀ {J : Type u} (c : J → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U)),
      #J < ν →
      IsRelativelyIsolated (uIdx := uIdx) (cIdx := J)
        (asTuple incl hincl (seqJoint bU c)) (Equiv.refl (uIdx ⊕ J))) :
    AllDominated incl' hincl' uIdx b' := by
  classical
  intro cIdx c hc
  have hν0 : ℵ₀ ≤ ν := P.aleph0_le hνC.1
  let d : uIdx ⊕ cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hνC.1 U') := seqJoint b' c
  have hd : #(uIdx ⊕ cIdx) < ν := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hν0 huν hc
  let σ : Cardinal.{u} := max ℵ₀ #(uIdx ⊕ cIdx)
  have hσ : ℵ₀ ≤ σ := le_max_left _ _
  have hσν : σ < ν := max_lt (P.aleph0_lt hνC.1) hd
  have hT := infra_617_tied_from_retractions P hνC hlC hνl A U A' U' toA toU incl incl'
    htoA htoU hincl hincl' hsq r hιcard halmost himg d hd
  have hS := infra_617_same_galois A U A' U' toA toU incl incl' htoA htoU hincl hincl' hsq d
  let c' : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U) :=
    fun j => ⟨(c j).1, toU.onVertex (c j).1 (c j).2⟩
  have hfun : (fun j => (⟨(d j).1, toU.onVertex (d j).1 (d j).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hlC.1 U))) = seqJoint bU c' := by
    funext j
    rcases j with k | j
    · exact (hbU k).symm
    · rfl
  have hI := hiso c' hc
  rw [← hfun] at hI
  exact infra_78_tied_descent_mixed P σ hσ hνC.1 (infra_79_closedTail_sigma2 hνT hσ hσν)
    (hlT.2.1 σ hσ (hσν.trans_le hνl)) hνl toA htoA (asTuple incl' hincl' d)
    (asTuple incl hincl _) (Equiv.refl _) (Equiv.refl _) rfl rfl (le_max_right _ _) hS hT hI

/-- **Theorem 7.9 identification step for a bounded mark (proved, cycle 93).** As
`infra_79_identify`, with the finite mark replaced by `|p| ≤ θ < ν` (`θ ≥ ℵ₀`): the testing
arity and recursion closure are taken at `θ` instead of `ℵ₀`. Sub-step of `infra_79_general`. -/
theorem infra_79_identify_bounded (P : SingleModelData K) {ν l : Cardinal.{u}}
    (hν : ν ∈ infra_78_closedTail P) (hl : l ∈ P.eligible) (hνl : ν ≤ l)
    (X : P.scheme.Object ν hν.1) (p : TupleOver K oneVertexShape P.scheme hν.1 X)
    (hpν : p.ν = ν) (θ : Cardinal.{u}) (hθ : ℵ₀ ≤ θ) (hθν : θ < ν) (hidxθ : #p.idx ≤ θ)
    {B U : P.scheme.Object l hl}
    (ι : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 X) (P.scheme.asSystem hl B))
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hl B) (P.scheme.asSystem hl U))
    (bU : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hl U))
    (hseed : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν.1 X)),
      #β < ν →
      P.scheme.DiagramEq (X := p.host) (Y := U) (typeJoint (p := p) Z)
        (typeJoint (p := (asTuple f trivial bU).restrict ι trivial) Z))
    (hT : IsTiedFreeMixed ι ((asTuple f trivial bU).restrict ι trivial) (asTuple f trivial bU)
      (Equiv.refl _))
    {A' U' : P.scheme.Object ν hν.1}
    (toA : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 A') (P.scheme.asSystem hl B))
    (toU : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 U') (P.scheme.asSystem hl U))
    (incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 A')
      (P.scheme.asSystem hν.1 U'))
    (hsq : ∀ v, (f.onVertex v).comp (toA.onVertex v) = (toU.onVertex v).comp (incl'.onVertex v))
    (b' : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν.1 U'))
    (hbU : ∀ k, bU k = ⟨(b' k).1, toU.onVertex (b' k).1 (b' k).2⟩)
    (hX : ∀ x, ∃ y, toA.onVertex PUnit.unit y = ι.onVertex PUnit.unit x) :
    ∃ φ : SystemArrow K oneVertexShape (P.scheme.asSystem hν.1 X) (P.scheme.asSystem hν.1 A'),
      P.scheme.IsStructIso (X := X) (Y := A') φ ∧
      SameGaloisType p (asTuple (SystemArrow.comp φ incl') trivial b')
        (Equiv.refl p.idx) (Equiv.refl p.idx) := by
  classical
  have hlt : ℵ₀ < ν := P.aleph0_lt hν.1
  have hrec : ν ∈ recursionClosedLevels P θ := (hν.2.1 θ hθ hθν).1
  have hidx : #p.idx ≤ θ := hidxθ
  obtain ⟨seq, -, -, -, -, htest, hlong, hτν, -⟩ := infra_78_tied_at_mixed P θ hθ hν.1 hrec
    (Order.succ_le_of_lt hθν) hl hνl ι trivial p hpν hidx ℵ₀ hlt
  let q : TupleOver K oneVertexShape P.scheme hl B := asTuple f trivial bU
  let seqq : ApproximationSequence (q.restrict ι trivial) :=
    infra_78_seq_diagram_transfer (t2 := q.restrict ι trivial) (Equiv.refl p.idx) seq
      (fun Z hZ => by
        refine infra_73_diagramEq_of_eq (hseed Z (hZ.trans_lt hτν)) (fun _ => rfl) ?_
        rintro (u | x) <;> rfl)
  have hseed' : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν.1 X)),
      #β < ν →
      P.scheme.DiagramEq (X := p.host) (Y := q.host)
        (alignJoint (Equiv.refl _) (typeJoint (p := p) Z))
        (typeJoint (p := q.restrict ι trivial) Z) := fun Z hβ =>
    infra_73_diagramEq_of_eq (hseed Z hβ) (by rintro (u | x) <;> rfl) (fun _ => rfl)
  have hanch : ∀ a k, ∃ y, toA.onVertex PUnit.unit y =
      ι.onVertex PUnit.unit (seqq.family a k).2 := fun a k => hX _
  have hsq' : ∀ x, toU.onVertex PUnit.unit (incl'.onVertex PUnit.unit x) =
      q.incl.onVertex PUnit.unit (toA.onVertex PUnit.unit x) := fun x =>
    (DFunLike.congr_fun (hsq PUnit.unit) x).symm
  obtain ⟨φ, hφ, -, hGal⟩ := infra_78_marginal_identify_level P θ hθ hν.1 (hμ := hl) hrec
    hθν hνl (A := A') (U := U') p hpν hidx ι trivial q hνl (Equiv.refl _) hseed' hT seqq
    htest hlong toA hanch incl' toU hsq' b' hbU
  exact ⟨φ, hφ, hGal⟩

/-- **Theorem 7.9 same-level primeness for a bounded mark (proved, cycle 93).** As
`infra_79_primeness_same_level`, with `|p| ≤ θ < μ` in place of finiteness. Sub-step of
`infra_79_general`. -/
theorem infra_79_primeness_same_level_bounded {P : SingleModelData K} {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (X : P.scheme.Object μ hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ X) (θ : Cardinal.{u}) (hθ : ℵ₀ ≤ θ) (hθμ : θ < μ)
    (hidxθ : #p.idx ≤ θ)
    (Y : P.scheme.Object μ hμ)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (hAll : AllDominated f hf p.idx b)
    (hp : SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx))
    (N : P.scheme.Object μ hμ)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hg : P.scheme.permitted (X := X) (Y := N) g)
    (b' : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (hN : SameGaloisType p (asTuple g hg b') (Equiv.refl p.idx) (Equiv.refl p.idx)) :
    ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ N),
      P.scheme.permitted (X := Y) (Y := N) h ∧
      SystemArrow.comp f h = g ∧
      ∀ i, h.onVertex (b i).1 (b i).2 = (b' i).2 := by
  have hYN := infra_612_galois_trans_mid_any (t1 := asTuple f hf b) (t2 := p)
    (t3 := asTuple g hg b') (e12 := Equiv.refl p.idx) (e32 := Equiv.refl p.idx)
    hp.symm hN θ hθ hθμ hidxθ rfl rfl
  exact infra_75_embed hμ X Y N f hf g hg b b'
    (hidxθ.trans_lt hθμ) hYN hAll

/-- **Primeness clause of `infra_79_general` (proved, cycle 93).** The second conjunct of
`infra_79_general_statement` for every mark with `|p| < μ` (Definition 7.7 is not needed for
primeness): `infra_79_primeness_same_level_bounded` at `θ = max ℵ₀ |p|`. -/
theorem infra_79_general_primeness (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (X : P.scheme.Object μ hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ X) (hidx : #p.idx < μ) :
    ∀ (Y : P.scheme.Object μ hμ)
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
      (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      AllDominated f trivial p.idx b →
      SameGaloisType p (asTuple f trivial b) (Equiv.refl _) (Equiv.refl _) →
      ∀ (N : P.scheme.Object μ hμ)
        (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
        (b' : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N)),
        SameGaloisType p (asTuple g trivial b') (Equiv.refl _) (Equiv.refl _) →
        ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ N),
          SystemArrow.comp f h = g ∧ ∀ i, h.onVertex (b i).1 (b i).2 = (b' i).2 := by
  intro Y f b hAll hp N g b' hN
  obtain ⟨h, -, hc, hv⟩ := infra_79_primeness_same_level_bounded hμ X p (max ℵ₀ #p.idx)
    (le_max_left _ _) (max_lt (P.aleph0_lt hμ) hidx) (le_max_right _ _) Y f trivial b hAll hp
    N g trivial b' hN
  exact ⟨h, hc, hv⟩

end AEC
