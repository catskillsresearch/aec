module

public import AEC.Section7.StageTransport

@[expose] public section

/-!
# Prop 7.8: the seed stage (`infra_78_seed_stage`)

Paper: "Extend `X` by a presentation arrow to a level-`κ` object `X_0`, and choose `Y_0 ≥ X_0`
containing a realization `b` of the free lift of `p` ... Fix a bounded approximation list `I_p`
in `X` which determines `p` at a sufficient testing arity ... put `I_p` and the coordinates of `b`
into `R_0`."

* `infra_78_presentation_arrow` (proved): a level-`κ` object `X_0` with an arrow `X → X_0`
  (chart of `X` followed by the order arrow `E(ν) → E(κ)`).
* `infra_78_tiedFreeMixed_left_congr` (proved): mixed tied freeness is invariant under replacing
  the restricted type by one with the same small-test diagrams over the base.
* `infra_78_seed_lift` (proved): `Y_0`, the pair `p0 : X_0 → Y_0` and the mark `b0`, with the
  mark restricted to `X` agreeing with `p` on small tests and tied free over `X` along `ι0`
  (mark form used by the matrix).
* `infra_78_seed_stage` (proved): the full seed — the above, a Lemma 6.9 approximation sequence
  for `p` at arity `≥ max(λ', g σ + ls K)` with long index, and for every seed set
  `infra_78_seedSet I b0 y` with `|I| ≤ ρ` (e.g. `ι0 '' anchors`, `infra_78_anchorSet_card`):
  base map the identity, invariant (5), seeds `⊆ R_0`, `|R_0| ≤ ρ`, `R_0` pair-closed, `S_0 ≠ ∅`.
-/

universe u

open Cardinal FirstOrder
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **A presentation arrow to a higher level (proved).** -/
theorem infra_78_presentation_arrow {P : SingleModelData K} {ν κ : Cardinal.{u}}
    (hν : ν ∈ P.eligible) (hκ : κ ∈ P.eligible) (hνκ : ν ≤ κ) (X : P.scheme.Object ν hν) :
    ∃ (X0 : P.scheme.Object κ hκ),
      Nonempty (SystemArrow K oneVertexShape (P.scheme.asSystem hν X)
        (P.scheme.asSystem hκ X0)) := by
  let X0 : SMObject K κ := SMObject.ofModel (P.G κ) (P.mem_G κ) (SingleModelData.card_G hκ)
  let f : Language.Embedding K.τ (SMObject.model (μ := ν) X).carrier X0.model.carrier :=
    (SMObject.ofModelEquiv (P.G κ) (P.mem_G κ) (SingleModelData.card_G hκ)).toEmbedding.comp
      (SingleModelData.push hν hνκ X)
  have hf : K.Strong f :=
    K.strong_trans _ _ (SingleModelData.push_strong hν hνκ X)
      (strong_of_equiv K _ (P.mem_G κ))
  exact ⟨X0, ⟨oneVertexArrow f hf⟩⟩

/-- **Mixed tied freeness depends only on the small-test diagrams of the restricted type
(proved).** -/
theorem infra_78_tiedFreeMixed_left_congr {P : SingleModelData K} {ν μ : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    {q q' : TupleOver K oneVertexShape P.scheme hν A}
    {qB : TupleOver K oneVertexShape P.scheme hμ B} (eB : q.idx ≃ qB.idx) (e : q'.idx ≃ q.idx)
    (H : IsTiedFreeMixed f q qB eB)
    (hD : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      #β < ν →
      P.scheme.DiagramEq (X := q'.host) (Y := q.host)
        (typeJoint (p := q') Z) (fun s => typeJoint (p := q) Z (Sum.map e id s))) :
    IsTiedFreeMixed f q' qB (e.trans eB) := by
  classical
  intro seq ι Z Z0 hlen hιτ hιν hmove
  let seqS : ApproximationSequence q' :=
    { τ := #ι
      κIndex := seq.κIndex
      family := seq.family
      concat_bounded := seq.concat_bounded
      few_exceptions := fun {β} W hW => seq.few_exceptions W (hW.trans hιτ) }
  let seqT : ApproximationSequence q :=
    infra_78_seq_diagram_transfer e seqS (fun Z hZ => hD Z (hZ.trans_lt hιν))
  have hlenT : seqT.τ + ℵ₀ < #seqT.κIndex := (add_le_add hιτ le_rfl).trans_lt hlen
  have hmoveT : infra_78_isMoveMixed f seqT Z Z0 := by
    intro i
    refine infra_612_dEq_transport (hmove i) (Equiv.sumCongr e.symm (Equiv.refl ι)) ?_ ?_
    · rintro (k | x) <;> rfl
    · rintro (k | x) <;> rfl
  have d := H seqT Z Z0 hlenT le_rfl hιν hmoveT
  have d' := infra_612_dEq_transport d (Equiv.sumCongr e (Equiv.refl ι))
    (xs' := fun s => typeJoint (p := q) Z0 (Sum.map e id s))
    (ys' := infra_612_anchored (e.trans eB) qB.incl qB.val Z)
    (fun _ => rfl) (by rintro (k | x) <;> rfl)
  exact P.scheme.diagram_trans _ _ _ _ _ _ (hD Z0 hιν) d'

/-- **The seed lift (proved).** `X_0` at level `κ` with `ι0 : X → X_0`, the mixed tied free lift
of `p` realized in `Y_0` (pair `p0 : X_0 → Y_0`, mark `b0`), in the mark form of the matrix. -/
theorem infra_78_seed_lift (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν κ : Cardinal.{u}} (hν : ν ∈ P.eligible)
    (hrec : ν ∈ recursionClosedLevels P σ) (hσν : Order.succ σ ≤ ν)
    (hκ : κ ∈ P.eligible) (hrecκ : κ ∈ recursionClosedLevels P σ) (hνκ : ν ≤ κ)
    (X : P.scheme.Object ν hν) (p : TupleOver K oneVertexShape P.scheme hν X)
    (hpν : p.ν = ν) (hidx : #p.idx ≤ σ) :
    ∃ (X0 Y0 : P.scheme.Object κ hκ)
      (ι0 : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hκ X0))
      (p0 : κ.ord.ToType → κ.ord.ToType) (hp0 : infra_78_IsArr X0 Y0 p0)
      (b0 : p.idx → κ.ord.ToType),
      (∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν X)), #β < ν →
        P.scheme.DiagramEq (X := p.host) (Y := Y0) (typeJoint (p := p) Z)
          (typeJoint (p := (infra_78_markTuple (infra_78_toArr hp0)
            (fun u => (⟨PUnit.unit, b0 u⟩ : Occurrence K oneVertexShape
              (P.scheme.asSystem hκ Y0)))).restrict ι0 trivial) Z)) ∧
      IsTiedFreeMixed ι0
        ((infra_78_markTuple (infra_78_toArr hp0)
          (fun u => (⟨PUnit.unit, b0 u⟩ : Occurrence K oneVertexShape
            (P.scheme.asSystem hκ Y0)))).restrict ι0 trivial)
        (infra_78_markTuple (infra_78_toArr hp0)
          (fun u => (⟨PUnit.unit, b0 u⟩ : Occurrence K oneVertexShape
            (P.scheme.asSystem hκ Y0)))) (Equiv.refl _) := by
  classical
  obtain ⟨X0, ⟨ι0⟩⟩ := infra_78_presentation_arrow hν hκ hνκ X
  obtain ⟨qB, eB, hqν, hD, hT⟩ :=
    infra_78_tied_free_lift_mixed P σ hσ hν hrec hσν hκ hrecκ hνκ ι0 trivial p hpν hidx
  rcases qB with ⟨ν', hν', host, incl, hincl, idx, val⟩
  dsimp only at hqν
  subst hqν
  have hp0 : infra_78_IsArr X0 host (fun x => incl.onVertex PUnit.unit x) := ⟨incl, fun _ => rfl⟩
  have hTA : infra_78_toArr hp0 = incl := infra_78_arrow_ext fun x => infra_78_toArr_apply hp0 x
  refine ⟨X0, host, ι0, _, hp0, fun u => (val (eB u)).2, ?_, ?_⟩
  · intro β Z hβ
    rw [hTA]
    refine infra_73_diagramEq_of_eq (hD Z hβ) (fun _ => rfl) ?_
    rintro (u | x) <;> rfl
  · rw [hTA]
    have H' := infra_78_tiedFreeMixed_left_congr ι0 (q' := (infra_78_markTuple incl
      (fun u => (⟨PUnit.unit, (val (eB u)).2⟩ : Occurrence K oneVertexShape
        (P.scheme.asSystem hν' host)))).restrict ι0 trivial) eB (Equiv.refl _) hT
      (fun Z hβ => by
        refine P.scheme.diagram_symm _ _ _ _ ?_
        refine infra_73_diagramEq_of_eq (hD Z hβ) ?_ ?_
        · rintro (u | x) <;> rfl
        · rintro (u | x) <;> rfl)
    intro seq ι Z Z0 hlen hιτ hιν hmove
    refine infra_73_diagramEq_of_eq (H' seq Z Z0 hlen hιτ hιν hmove) (fun _ => rfl) ?_
    rintro (u | x) <;> rfl

/-- The anchors of an approximation sequence (the coordinates of the list `I_p` in `X`). -/
def infra_78_anchorSet {P : SingleModelData K} {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {X : P.scheme.Object ν hν} {p : TupleOver K oneVertexShape P.scheme hν X}
    (seq : ApproximationSequence p) : Set ν.ord.ToType :=
  Set.range (fun ik : seq.κIndex × p.idx => (seq.family ik.1 ik.2).2)

theorem infra_78_anchorSet_card {P : SingleModelData K} {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {X : P.scheme.Object ν hν} {p : TupleOver K oneVertexShape P.scheme hν X}
    (seq : ApproximationSequence p) : #(infra_78_anchorSet seq) < ν :=
  Cardinal.mk_range_le.trans_lt seq.concat_bounded

/-- The anchors pushed into `X_0` along `ι0` (the `X`-side seeds `ι(I_p)`). -/
def infra_78_anchorImage {P : SingleModelData K} {ν κ : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {hκ : κ ∈ P.eligible} {X : P.scheme.Object ν hν} {X0 : P.scheme.Object κ hκ}
    (ι0 : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hκ X0))
    {p : TupleOver K oneVertexShape P.scheme hν X} (seq : ApproximationSequence p) :
    Set κ.ord.ToType :=
  (fun x => ι0.onVertex PUnit.unit x) '' infra_78_anchorSet seq

/-- **`infra_78_seed_stage` (proved).** The full seed of the Prop 7.8 matrix: `X_0`, `ι0`, `Y_0`,
`p0`, `b0` (`infra_78_seed_lift`); a Lemma 6.9 approximation sequence for `p` at testing arity
`≥ max(λ', g σ + ls K)` with long index (`infra_78_tied_at_mixed`); and the seed stage with base
map the identity and seeds `ι0(I_p) ∪ b ∪ {y}`: invariant (5), seeds in `R_0`, `|R_0| ≤ ρ`,
`R_0` pair-closed, `S_0 ≠ ∅`. -/
theorem infra_78_seed_stage (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν κ : Cardinal.{u}} (hν : ν ∈ P.eligible)
    (hrec : ν ∈ recursionClosedLevels P σ) (hσν : Order.succ σ ≤ ν)
    (hκ : κ ∈ P.eligible) (hrecκ : κ ∈ recursionClosedLevels P σ) (hνκ : ν ≤ κ)
    (X : P.scheme.Object ν hν) (p : TupleOver K oneVertexShape P.scheme hν X)
    (hpν : p.ν = ν) (hidx : #p.idx ≤ σ) (lam' : Cardinal.{u}) (hlam' : lam' < ν)
    (ρ : Cardinal.{u}) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible) (hℓκ : ℓ ≤ κ) (hℓρ : ℓ < ρ)
    (hpow : ρ ^ ℓ = ρ) (hνρ : ν ≤ ρ) (hidxρ : #p.idx ≤ ρ) :
    ∃ (X0 Y0 : P.scheme.Object κ hκ)
      (ι0 : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hκ X0))
      (p0 : κ.ord.ToType → κ.ord.ToType) (hp0 : infra_78_IsArr X0 Y0 p0)
      (b0 : p.idx → κ.ord.ToType) (seq : ApproximationSequence p),
      (lam' ≤ seq.τ ∧ P.g σ + ls K ≤ seq.τ ∧ seq.τ + ℵ₀ < #(seq.κIndex) ∧ seq.τ < ν) ∧
      (∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν X)), #β < ν →
        P.scheme.DiagramEq (X := p.host) (Y := Y0) (typeJoint (p := p) Z)
          (typeJoint (p := (infra_78_markTuple (infra_78_toArr hp0)
            (fun u => (⟨PUnit.unit, b0 u⟩ : Occurrence K oneVertexShape
              (P.scheme.asSystem hκ Y0)))).restrict ι0 trivial) Z)) ∧
      IsTiedFreeMixed ι0
        ((infra_78_markTuple (infra_78_toArr hp0)
          (fun u => (⟨PUnit.unit, b0 u⟩ : Occurrence K oneVertexShape
            (P.scheme.asSystem hκ Y0)))).restrict ι0 trivial)
        (infra_78_markTuple (infra_78_toArr hp0)
          (fun u => (⟨PUnit.unit, b0 u⟩ : Occurrence K oneVertexShape
            (P.scheme.asSystem hκ Y0)))) (Equiv.refl _) ∧
      #(infra_78_anchorImage ι0 seq) < ν ∧
      ∀ y : κ.ord.ToType,
        (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 id b0
          (infra_78_seedSet (infra_78_anchorImage ι0 seq) b0 y)).e.g = id ∧
        infra_78_StageInv5 X0 (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 id b0
          (infra_78_seedSet (infra_78_anchorImage ι0 seq) b0 y)) ∧
        infra_78_seedSet (infra_78_anchorImage ι0 seq) b0 y ⊆
          (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 id b0
            (infra_78_seedSet (infra_78_anchorImage ι0 seq) b0 y)).e.R ∧
        #(infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 id b0
          (infra_78_seedSet (infra_78_anchorImage ι0 seq) b0 y)).e.R ≤ ρ ∧
        infra_78_PairClosed ρ hℓel (infra_78_toArr (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 id b0
            (infra_78_seedSet (infra_78_anchorImage ι0 seq) b0 y)).hp) trivial
          (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 id b0
            (infra_78_seedSet (infra_78_anchorImage ι0 seq) b0 y)).e.R ∧
        ∃ y', (Sum.inr y' : κ.ord.ToType ⊕ κ.ord.ToType) ∈
          (infra_78_seedStage ρ hℓel X0 Y0 p0 hp0 id b0
            (infra_78_seedSet (infra_78_anchorImage ι0 seq) b0 y)).e.R := by
  classical
  obtain ⟨X0, Y0, ι0, p0, hp0, b0, hD, hT⟩ :=
    infra_78_seed_lift P σ hσ hν hrec hσν hκ hrecκ hνκ X p hpν hidx
  obtain ⟨seq, -, -, -, hlamτ, htest, hlong, hτν, -⟩ :=
    infra_78_tied_at_mixed P σ hσ hν hrec hσν hκ hνκ ι0 trivial p hpν hidx lam' hlam'
  have hρ : ℵ₀ ≤ ρ := (P.aleph0_le hℓel).trans hℓρ.le
  have hI : #(infra_78_anchorImage ι0 seq) < ν :=
    Cardinal.mk_image_le.trans_lt (infra_78_anchorSet_card seq)
  refine ⟨X0, Y0, ι0, p0, hp0, b0, seq, ⟨hlamτ, htest, hlong, hτν⟩, hD, hT, hI, fun y => ?_⟩
  have hs : #(infra_78_seedSet (infra_78_anchorImage ι0 seq) b0 y) ≤ ρ :=
    infra_78_seedSet_card hρ (hI.le.trans hνρ) hidxρ y
  refine ⟨rfl, infra_78_seedStage_inv5 ρ hℓel X0 Y0 p0 hp0 b0 _,
    infra_78_seedStage_seeds ρ hℓel X0 Y0 p0 hp0 id b0 _,
    infra_78_seedStage_card ρ hℓel X0 Y0 p0 hp0 id b0 _ hs,
    infra_78_seedStage_closed ρ hℓel X0 Y0 p0 hp0 id b0 _ hℓκ hℓρ hpow hs,
    infra_78_seedStage_S_nonempty ρ hℓel X0 Y0 p0 hp0 id b0 _ (y := y)
      (Or.inr ⟨y, Set.mem_insert _ _, rfl⟩)⟩

end AEC
