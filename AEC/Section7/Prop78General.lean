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

end AEC
