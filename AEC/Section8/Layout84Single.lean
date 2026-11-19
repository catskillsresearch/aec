module

public import AEC.Section8.Lemma84Single
public import AEC.Section7.RelativeIsolationTransfer
public import AEC.Section8.ReflectSingle
public import AEC.Section7.Lemma72Mixed

@[expose] public section

/-!
# Lemma 8.4 for the Prop 5.6 scheme: the natural layout (8), diagram level (cycle 100)

English (Lemma 8.4 proof): "The joint bounded diagrams of U and A_{H'} inside T are the diagrams of
the natural layout U_H ∪ A_{H'} inside U_{H'}. (8) Indeed, each bounded tuple of U, together with
b, is isolated over A, whereas the marginal of b over A_{H'} is the prescribed free extension.
Lemma 7.2 determines its joint type. The argument applies both to (8) and to the specified image
inside T'. It includes equalities between the two parts of the layout; an additional actual
overlap is not ignored."

Target (`infra_84_layout_amalgam`, diagram level): bounded joint diagrams of `U` (with the mark)
and the `C`-side read in `T` equal those read in `T′` through the specified map.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Layout (8), diagram level: equal types over `C` give equal bounded joint diagrams.**
If a list `w` in `T` and `w′` in `T′` (both over `C` at level `μ`) have the same Galois type over
`C`, then for every list `ZC` from `C` of size `< μ` the joint lists `w ⌢ cT ZC` and `w′ ⌢ cT′ ZC`
have equal diagrams. This includes equalities between the two parts (an actual overlap of `w` with
the image of `C` is recorded). Theorem 6.6 (`infra_72_diagramEq_of_sameGalois`). -/
theorem infra_84_layout_diagrams_of_type (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (C Tt Tt' : P.scheme.Object μ hμ)
    (cT : SystemArrow K oneVertexShape (P.scheme.asSystem hμ C) (P.scheme.asSystem hμ Tt))
    (cT' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ C) (P.scheme.asSystem hμ Tt'))
    (hcT : P.scheme.permitted (X := C) (Y := Tt) cT)
    (hcT' : P.scheme.permitted (X := C) (Y := Tt') cT')
    {κ : Type u} (w : κ → Occurrence K oneVertexShape (P.scheme.asSystem hμ Tt))
    (w' : κ → Occurrence K oneVertexShape (P.scheme.asSystem hμ Tt')) (hκ : #κ < μ)
    (h : SameGaloisType (⟨μ, hμ, Tt, cT, hcT, κ, w⟩ : TupleOver K oneVertexShape P.scheme hμ C)
      (⟨μ, hμ, Tt', cT', hcT', κ, w'⟩ : TupleOver K oneVertexShape P.scheme hμ C)
      (Equiv.refl _) (Equiv.refl _))
    {β : Type u} (ZC : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ C)) (hβ : #β < μ) :
    P.scheme.DiagramEq (X := Tt) (Y := Tt')
      (Sum.elim w (fun i => cT.mapOcc (ZC i))) (Sum.elim w' (fun i => cT'.mapOcc (ZC i))) := by
  have H := infra_72_diagramEq_of_sameGalois h ZC rfl rfl hκ hβ
  exact infra_73_diagramEq_of_eq H (fun x => by rcases x with i | j <;> rfl)
    (fun x => by rcases x with i | j <;> rfl)

/-- **Layout (8) for Lemma 8.4, diagram level (Lemma 7.2 step).** In the situation of Lemma 8.4
for `P.scheme`: if corresponding bounded tuples of `U`, `U′` jointly with the marks have equal
types over `C` (the hypothesis of Lemma 8.4, which the paper derives from Lemma 7.2: the tuple with
`b` is isolated over `A` and `b/C` is the prescribed free extension), then every bounded joint
diagram of `U` (with the mark) and `C` read in `T` equals the corresponding one read in `T′`
through the specified map. Tuple from `U` of size `< ν`, `C`-part of size `< μ`. -/
theorem infra_84_layout_diagrams_single (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (M M' : MarkedPair K oneVertexShape P.scheme Pr) (hνμ : M.μ < μ)
    (iso : MarkedArrow K oneVertexShape P.scheme Pr M M')
    (C Tt Tt' : P.scheme.Object μ hμ)
    (cT : SystemArrow K oneVertexShape (P.scheme.asSystem hμ C) (P.scheme.asSystem hμ Tt))
    (cT' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ C) (P.scheme.asSystem hμ Tt'))
    (hcT : P.scheme.permitted (X := C) (Y := Tt) cT)
    (hcT' : P.scheme.permitted (X := C) (Y := Tt') cT')
    (uT : SystemArrow K oneVertexShape (P.scheme.asSystem M.hμ M.Y) (P.scheme.asSystem hμ Tt))
    (uT' : SystemArrow K oneVertexShape (P.scheme.asSystem M'.hμ M'.Y)
      (P.scheme.asSystem hμ Tt'))
    (htypes : ∀ {ι : Type u} (t : ι → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y)),
      #ι < M.μ →
      SameGaloisType
        (⟨μ, hμ, Tt, cT, hcT, ι ⊕ M.bIdx,
          Sum.elim (fun i => uT.mapOcc (t i)) (fun j => uT.mapOcc (M.b j))⟩ :
          TupleOver K oneVertexShape P.scheme hμ C)
        (⟨μ, hμ, Tt', cT', hcT', ι ⊕ M.bIdx,
          Sum.elim (fun i => uT'.mapOcc (iso.onY.mapOcc (t i)))
            (fun j => uT'.mapOcc (iso.onY.mapOcc (M.b j)))⟩ :
          TupleOver K oneVertexShape P.scheme hμ C)
        (Equiv.refl _) (Equiv.refl _))
    {ιU ιC : Type u} (ZU : ιU → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y))
    (ZC : ιC → Occurrence K oneVertexShape (P.scheme.asSystem hμ C))
    (hU : #ιU < M.μ) (hC : #ιC < μ) :
    P.scheme.DiagramEq (X := Tt) (Y := Tt')
      (Sum.elim (Sum.elim (fun i => uT.mapOcc (ZU i)) (fun j => uT.mapOcc (M.b j)))
        (fun i => cT.mapOcc (ZC i)))
      (Sum.elim (Sum.elim (fun i => uT'.mapOcc (iso.onY.mapOcc (ZU i)))
          (fun j => uT'.mapOcc (iso.onY.mapOcc (M.b j))))
        (fun i => cT'.mapOcc (ZC i))) := by
  have hfinB : Finite M.bIdx :=
    Finite.of_equiv _ (M.realEq.trans (Pr.arity M.hμ M.X)).symm
  have hμ0 : ℵ₀ < M.μ := P.aleph0_lt M.hμ
  have hBlt : #M.bIdx < M.μ := (Cardinal.lt_aleph0_of_finite M.bIdx).trans hμ0
  have hκ : #(ιU ⊕ M.bIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact (add_lt_of_lt hμ0.le hU hBlt).trans hνμ
  exact infra_84_layout_diagrams_of_type P hμ C Tt Tt' cT cT' hcT hcT' _ _ hκ (htypes ZU hU) ZC hC

/-- **Corollary 6.7 strip step for Lemma 8.4, diagram level (P.scheme).** English (Lemma 8.4
proof): "Corollary 6.7 then embeds A_{H'} into C over this copy of V." For `A` at level `ν`, an
object `B` at level `ν` over `A` (the strip object `A_{H'}`) and `C` at level `μ > ν` over `A`:
every list `Y` of `B` of length `< μ` (in particular all of `B`) is realized inside `C` over any
bounded list `Z` of `A`, with the same joint diagram. Mixed saturation pulled inside `C`
(`infra_82_saturate_inside`). -/
theorem infra_84_strip_realize_single (P : SingleModelData K) {ν μ : Cardinal.{u}}
    (hν : ν ∈ P.eligible) (hμ : μ ∈ P.eligible) (hνμ : ν < μ)
    (A B : P.scheme.Object ν hν) (C : P.scheme.Object μ hμ)
    (aB : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hν B))
    (aC : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ C))
    (haB : P.scheme.permitted (X := A) (Y := B) aB)
    (haC : P.scheme.permitted (X := A) (Y := C) aC)
    {α β : Type u} (Z : α → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (Y : β → Occurrence K oneVertexShape (P.scheme.asSystem hν B)) (hα : #α < ν) (hβ : #β < μ) :
    ∃ ys : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ C),
      P.scheme.DiagramEq (X := C) (Y := B)
        (Sum.elim (fun i => aC.mapOcc (Z i)) ys) (Sum.elim (fun i => aB.mapOcc (Z i)) Y) := by
  have hαμ : #α < μ := hα.trans hνμ
  have d1 := P.scheme.diagram_preserved A C aC haC Z hα hαμ
  have d2 := P.scheme.diagram_preserved A B aB haB Z hα hα
  have hEq : P.scheme.DiagramEq (X := C) (Y := B) (fun i => aC.mapOcc (Z i))
      (fun i => aB.mapOcc (Z i)) :=
    P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d1) d2
  have hsat : IsSaturated P.scheme := P.isSaturated
  have hαβ : #(α ⊕ β) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hαμ hβ
  obtain ⟨ws, hws, hD⟩ := infra_82_saturate_inside C B (fun i => aC.mapOcc (Z i))
    (fun i => aB.mapOcc (Z i)) (Sum.elim (fun i => aB.mapOcc (Z i)) Y) hαμ hβ hαβ
    (fun _ => rfl) hEq
  refine ⟨fun j => ws (Sum.inr j), infra_73_diagramEq_of_eq hD ?_ (fun _ => rfl)⟩
  intro x; rcases x with i | j
  · exact hws i
  · rfl

/-- **Proposition 6.3 for the two-segment layout (8).** English (Lemma 8.4 proof): "The layout has
two well-ordered horizontal segments with designated term parts. Proposition 6.3 gives a bound
depending on the candidate arity and the fixed template, not on H, H' or V." One bound `g`
(Proposition 4.8 / 6.3) serves every two-segment layout `I₁ ⊕ₗ I₂` of well-orders: placements of a
tuple of length at most `σ` that agree on every parameter set of size at most `g σ` agree
everywhere. `g` depends only on the template (`E`, `D`), not on the segments. -/
theorem infra_84_two_segment_tester (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K) :
    ∃ g : Cardinal.{u} → Cardinal.{u},
      (∀ σ τ, σ ≤ τ → g σ ≤ g τ) ∧ (∀ σ, aleph0 ≤ g σ) ∧
      ∀ (I₁ I₂ : Type u) [LinearOrder I₁] [WellFoundedLT I₁] [LinearOrder I₂]
        [WellFoundedLT I₂] [Nonempty I₁] {α : Type u} (σ : Cardinal.{u}), aleph0 ≤ σ →
        #α ≤ σ → ∀ P P' : Placement E.lab E.arity (Lex (I₁ ⊕ I₂)) α,
          (∀ X : Set (Lex (I₁ ⊕ I₂)), #X ≤ g σ → P.AgreeOn E D P' X) →
          P.AgreeOn E D P' Set.univ := by
  obtain ⟨g, hmono, hinf, htest⟩ := proposition_4_8_over_base K E D
  refine ⟨g, hmono, hinf, fun I₁ I₂ _ _ _ _ _ α σ hσ hα P P' h => ?_⟩
  have : Nonempty (Lex (I₁ ⊕ I₂)) := ⟨toLex (Sum.inl (Classical.arbitrary I₁))⟩
  exact htest σ hσ hα P P' h

/-- **Lemma 6.4 over the two-segment layout (8).** English (Lemma 8.4 proof): "Apply Lemma 6.4 to
lift its comparisons to a placed comparison over (8)." Compact placement (Lemma 6.4 /
Proposition 4.9) for the well-ordered presentation `E(I₁ ⊕ₗ I₂)` of the two-segment layout:
coherent natural local prescriptions over parameter sets of size at most `χ` are realized by one
order enlargement. -/
theorem infra_84_two_segment_placement (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K) (I₁ I₂ : Type u) [LinearOrder I₁]
    [WellFoundedLT I₁] [LinearOrder I₂] [WellFoundedLT I₂] [Nonempty I₁]
    {α : Type u} (σ χ : Cardinal.{u}) (hσinf : aleph0 ≤ σ) (hσ : #α ≤ σ)
    (hχ : ls K + σ < χ) (hpow : χ ^ σ = χ) (hI : K.Mem (E.obj (Lex (I₁ ⊕ I₂))))
    (q : ∀ {β : Type u}, #β ≤ χ → (β → (E.obj (Lex (I₁ ⊕ I₂))).carrier) → α ⊕ β →
      (E.obj (Lex (I₁ ⊕ I₂))).carrier)
    (hnat : ∀ {β : Type u} (hβ : #β ≤ χ) (p : β → (E.obj (Lex (I₁ ⊕ I₂))).carrier)
      (hpar : #β ≤ σ + χ) (hcardI : D.t (σ + χ) ≤ Model.card (E.obj (Lex (I₁ ⊕ I₂)))),
      D.same hpar hI hI hcardI hcardI (fun b => q hβ p (Sum.inr b)) p)
    (hcoh : ∀ {β β' : Type u} (hβ : #β ≤ χ) (hβ' : #β' ≤ χ)
      (p : β → (E.obj (Lex (I₁ ⊕ I₂))).carrier)
      (ι : β' → β) (hjoint : #(α ⊕ β') ≤ σ + χ)
      (hcardI : D.t (σ + χ) ≤ Model.card (E.obj (Lex (I₁ ⊕ I₂)))),
      D.same hjoint hI hI hcardI hcardI
        (fun i => q hβ p (Sum.map id ι i)) (q hβ' (fun b => p (ι b)))) :
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (f : Lex (I₁ ⊕ I₂) ↪o J)
      (z : α → (E.obj J).carrier) (hJ : K.Mem (E.obj J)),
      ∀ {β : Type u} (hβ : #β ≤ χ) (p : β → (E.obj (Lex (I₁ ⊕ I₂))).carrier)
        (hjoint : #(α ⊕ β) ≤ σ + χ)
        (_hcardI : D.t (σ + χ) ≤ Model.card (E.obj (Lex (I₁ ⊕ I₂))))
        (hcardJ : D.t (σ + χ) ≤ Model.card (E.obj J)),
        D.same hjoint hJ hJ hcardJ hcardJ
          (Sum.elim z (fun b => E.map f (p b)))
          (Sum.elim (fun a => E.map f (q hβ p (Sum.inl a)))
            (fun b => E.map f (q hβ p (Sum.inr b)))) := by
  have : Nonempty (Lex (I₁ ⊕ I₂)) := ⟨toLex (Sum.inl (Classical.arbitrary I₁))⟩
  exact lemma_6_4 K E D σ χ hσinf hσ hχ hpow hI q hnat hcoh

/-- **Layout (8): moving the second ambient onto the first (diagram level).** English (Lemma 8.4
proof): "The argument applies both to (8) and to the specified image inside T'." If bounded lists
`L` in `T` and `L′` in `T′` (both at level `μ`) have equal diagrams (e.g. the layout lists of
`infra_84_layout_diagrams_single`), there is a structural isomorphism `h : T ≅ T′` with
`h ∘ L = L′`; then for candidates `v` in `T`, `v′` in `T′`, the comparison of `v ⌢ L` with
`v′ ⌢ L′` is the comparison of `h v ⌢ L′` with `v′ ⌢ L′` inside the single ambient `T′`
(bounded homogeneity, `diagram_iso`). -/
theorem infra_84_layout_one_ambient (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (Tt Tt' : P.scheme.Object μ hμ) {κ : Type u}
    (L : κ → Occurrence K oneVertexShape (P.scheme.asSystem hμ Tt))
    (L' : κ → Occurrence K oneVertexShape (P.scheme.asSystem hμ Tt')) (hκ : #κ < μ)
    (hL : P.scheme.DiagramEq (X := Tt) (Y := Tt') L L') :
    ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Tt) (P.scheme.asSystem hμ Tt'),
      (∀ i, L' i = h.mapOcc (L i)) ∧
      ∀ {α : Type u} (v : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ Tt))
        (v' : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ Tt')), #α < μ →
        (P.scheme.DiagramEq (X := Tt) (Y := Tt') (Sum.elim v L) (Sum.elim v' L') ↔
          P.scheme.DiagramEq (X := Tt') (Y := Tt')
            (Sum.elim (fun i => h.mapOcc (v i)) L') (Sum.elim v' L')) := by
  obtain ⟨h, _, hh⟩ := (P.scheme.diagram_iso Tt Tt' L L' hκ).mp hL
  refine ⟨h, hh, fun {α} v v' hα => ?_⟩
  have hακ : #(α ⊕ κ) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hα hκ
  have d := P.scheme.diagram_preserved Tt Tt' h trivial (Sum.elim v L) hακ hακ
  have d' : P.scheme.DiagramEq (X := Tt) (Y := Tt') (Sum.elim v L)
      (Sum.elim (fun i => h.mapOcc (v i)) L') :=
    infra_73_diagramEq_of_eq d (fun _ => rfl) (fun x => by
      rcases x with a | k
      · rfl
      · exact (hh k).symm)
  constructor
  · intro H
    exact P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d') H
  · intro H
    exact P.scheme.diagram_trans _ _ _ _ _ _ d' H

/-- **Layout (8): local realization of a bounded test at level `ν`.** English (Lemma 8.4 proof):
"For a bounded candidate tuple in either ambient, each bounded test over the layout has a local
realization in U_{H'}". Diagram-level form for `P.scheme`: any list `L` (candidate plus test
parameters) of size `< ν` in an ambient `T` at level `μ ≥ ν` over a level-`ν` object `A` lies in a
level-`ν` object `B₀` over `A` inside `T`, with the same diagram there as in `T`
(`infra_72_level_hull` and `diagram_preserved`). -/
theorem infra_84_local_realization_single (P : SingleModelData K) {ν μ : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible} (hνμ : ν ≤ μ)
    (A : P.scheme.Object ν hν) (Tt : P.scheme.Object μ hμ)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ Tt))
    {κ : Type u} (L : κ → Occurrence K oneVertexShape (P.scheme.asSystem hμ Tt)) (hκ : #κ < ν) :
    ∃ (B₀ : P.scheme.Object ν hν)
      (f₀ : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hν B₀))
      (j : SystemArrow K oneVertexShape (P.scheme.asSystem hν B₀) (P.scheme.asSystem hμ Tt))
      (L₀ : κ → Occurrence K oneVertexShape (P.scheme.asSystem hν B₀)),
      (∀ a, j.onVertex PUnit.unit (f₀.onVertex PUnit.unit a) = f.onVertex PUnit.unit a) ∧
      (∀ k, L k = j.mapOcc (L₀ k)) ∧
      P.scheme.DiagramEq (X := B₀) (Y := Tt) L₀ L := by
  obtain ⟨B₀, f₀, j, L₀, hcomm, hL⟩ := infra_72_level_hull f L hκ
  refine ⟨B₀, f₀, j, L₀, hcomm, hL, ?_⟩
  have d := P.scheme.diagram_preserved B₀ Tt j trivial L₀ hκ (hκ.trans_le hνμ)
  exact infra_73_diagramEq_of_eq d (fun _ => rfl) (fun k => (hL k).symm)

/-- **Layout (8): small witness split into the two parts.** English (Lemma 8.4 proof): "If the two
candidates disagree on the questioned test, their placed comparisons disagree and yield a witness
within that bound. Its second-part parameters lie in A_{H'} ...; its first-part parameters lie in
the original U." With the template-only bound `g` of `infra_84_two_segment_tester`: if two
placements over the two-segment layout `I₁ ⊕ₗ I₂` disagree somewhere, they disagree on a set
`X₁ ∪ X₂` with first-part parameters `X₁ ⊆ I₁` and second-part parameters `X₂ ⊆ I₂`, each of size
at most `g σ`. -/
theorem infra_84_two_segment_witness (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K) :
    ∃ g : Cardinal.{u} → Cardinal.{u},
      (∀ σ τ, σ ≤ τ → g σ ≤ g τ) ∧ (∀ σ, aleph0 ≤ g σ) ∧
      ∀ (I₁ I₂ : Type u) [LinearOrder I₁] [WellFoundedLT I₁] [LinearOrder I₂]
        [WellFoundedLT I₂] [Nonempty I₁] {α : Type u} (σ : Cardinal.{u}), aleph0 ≤ σ →
        #α ≤ σ → ∀ P P' : Placement E.lab E.arity (Lex (I₁ ⊕ I₂)) α,
          ¬ P.AgreeOn E D P' Set.univ →
          ∃ (X₁ : Set I₁) (X₂ : Set I₂), #X₁ ≤ g σ ∧ #X₂ ≤ g σ ∧
            ¬ P.AgreeOn E D P'
              ((fun i => toLex (Sum.inl i)) '' X₁ ∪ (fun i => toLex (Sum.inr i)) '' X₂) := by
  obtain ⟨g, hmono, hinf, htest⟩ := infra_84_two_segment_tester K E D
  refine ⟨g, hmono, hinf, fun I₁ I₂ _ _ _ _ _ α σ hσ hα P P' hdis => ?_⟩
  by_contra hno
  push Not at hno
  apply hdis
  refine htest I₁ I₂ σ hσ hα P P' (fun X hX => ?_)
  let X₁ : Set I₁ := {i | toLex (Sum.inl i) ∈ X}
  let X₂ : Set I₂ := {i | toLex (Sum.inr i) ∈ X}
  have h1 : #X₁ ≤ #X := Cardinal.mk_le_of_injective (f := fun i : X₁ => (⟨_, i.2⟩ : X))
    (fun a b h => Subtype.ext (by
      have := congrArg (fun x : X => ofLex x.1) h
      simpa using this))
  have h2 : #X₂ ≤ #X := Cardinal.mk_le_of_injective (f := fun i : X₂ => (⟨_, i.2⟩ : X))
    (fun a b h => Subtype.ext (by
      have := congrArg (fun x : X => ofLex x.1) h
      simpa using this))
  have hsub : X ⊆ (fun i => toLex (Sum.inl i)) '' X₁ ∪ (fun i => toLex (Sum.inr i)) '' X₂ := by
    intro x hx
    rcases hxs : ofLex x with i | i
    · left; exact ⟨i, by simp [X₁, ← hxs, hx], by simp [← hxs]⟩
    · right; exact ⟨i, by simp [X₂, ← hxs, hx], by simp [← hxs]⟩
  exact (hno X₁ X₂ (h1.trans hX) (h2.trans hX)).mono hsub

/-- **Layout (8): Lemma 7.2 determines the joint type (mixed level).** English (Lemma 8.4 proof):
"each bounded tuple of U, together with b, is isolated over A, whereas the marginal of b over
A_{H'} is the prescribed free extension. Lemma 7.2 determines its joint type." For a bounded tuple
`q` over `A` (level `ν`) isolated relative to its `u`-part (the marks) by a fragment `W`, any two
extensions `qB₁`, `qB₂` of `q` over `B` (level `μ ≥ ν`, hosts at `μ`) whose `u`-marginals are
tied free extensions of `q`'s `u`-marginal have the same Galois type over `B`. Here `B` may be
`A_{H'}` or `C`; the recursion closure at `μ` is that of the helper `infra_72_mixed_level_closed`
(the closure tail of Section 8). -/
theorem infra_84_layout_type_determined
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {ν μ : Cardinal.{u}} (hν : ν ∈ P.eligible) (hμ : μ ∈ P.eligible) (hνμ : ν ≤ μ)
    (hrec : ν ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ ν)
    (hrecμ : μ ∈ recursionClosedLevels P σ)
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hν A)
    (qB₁ qB₂ : TupleOver K oneVertexShape P.scheme hμ B)
    (eB₁ : q.idx ≃ qB₁.idx) (eB₂ : q.idx ≃ qB₂.idx)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = ν) (hB₁ν : qB₁.ν = μ) (hB₂ν : qB₂.ν = μ)
    (hidx : #q.idx ≤ σ) (hidxν : #q.idx < ν)
    {wι : Type u} (W : wι → Occurrence K oneVertexShape (P.scheme.asSystem hν A))
    (hW : IsIsolatingFragment q e W)
    (hExt₁ : SameGaloisType q (qB₁.restrict f hf) eB₁ (Equiv.refl qB₁.idx))
    (hExt₂ : SameGaloisType q (qB₂.restrict f hf) eB₂ (Equiv.refl qB₂.idx))
    (hMarg₁ : IsTiedFreeMixed f (q.marginal e) (qB₁.marginal (eB₁.symm.trans e))
      (Equiv.refl uIdx))
    (hMarg₂ : IsTiedFreeMixed f (q.marginal e) (qB₂.marginal (eB₂.symm.trans e))
      (Equiv.refl uIdx)) :
    SameGaloisType qB₁ qB₂ (eB₁.symm.trans e) (eB₂.symm.trans e) := by
  have hiso := infra_72_mixed_level_closed P σ hσ hν hμ hνμ hrec hσSucc hrecμ f hf q qB₁ eB₁ e
    hqν hB₁ν hidx hidxν W hW hExt₁ hMarg₁
  have huidx : #uIdx ≤ #q.idx :=
    Cardinal.mk_le_of_injective (f := fun i : uIdx => e.symm (Sum.inl i))
      (fun a b h => Sum.inl.inj (e.symm.injective h))
  have hmarg := infra_72_tied_unique_mixed_rec P σ hσ hν hrec hσSucc hμ hνμ hrecμ f hf
    (q.marginal e) hqν (huidx.trans hidx) (qB₁.marginal (eB₁.symm.trans e))
    (qB₂.marginal (eB₂.symm.trans e)) (Equiv.refl uIdx) (Equiv.refl uIdx) hB₁ν hB₂ν
    hMarg₁ hMarg₂
  have d₁ := infra_72_ext_align_mixed hνμ f hf q qB₁ eB₁ e hqν hB₁ν hidxν hExt₁ W hW.1
  have d₂ := infra_72_ext_align_mixed hνμ f hf q qB₂ eB₂ e hqν hB₂ν hidxν hExt₂ W hW.1
  have d₁' := infra_73_diagramEq_of_eq d₁ (fun _ => rfl)
    (fun t => (by cases t <;> rfl :
      alignJoint (eB₁.symm.trans e) (typeJoint (p := qB₁.restrict f hf) W) t =
      alignJoint (eB₁.symm.trans e) (typeJoint (p := qB₁) (pushParams f W)) t))
  have d₂' := infra_73_diagramEq_of_eq d₂ (fun _ => rfl)
    (fun t => (by cases t <;> rfl :
      alignJoint (eB₂.symm.trans e) (typeJoint (p := qB₂.restrict f hf) W) t =
      alignJoint (eB₂.symm.trans e) (typeJoint (p := qB₂) (pushParams f W)) t))
  have d := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d₁') d₂'
  exact hiso.2 qB₂ (eB₂.symm.trans e) hB₂ν hmarg d

/-- **Placed comparisons over the two-segment layout (8) (Lemma 6.5 at the layout level).**
English (Lemma 8.4 proof): "Apply Lemma 6.4 to lift its comparisons to a placed comparison over
(8). ... Proposition 6.3 gives a bound depending on the candidate arity and the fixed template."
For the well-ordered two-segment presentation `E(I₁ ⊕ₗ I₂)` of size `ν` at a closed level `ν`, and
candidates `d₀ ∈ B₀`, `d₁ ∈ B₁` (strong extensions of size `ν`) of length at most `σ < ν`: lifting
placements exist, and two lifted placements agree everywhere iff the candidates agree on all
parameter sets from the layout of size at most `g(σ) + LS(K)`. -/
theorem infra_84_two_segment_placed_comparison (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (D : StableDiagram K)
    (g : Cardinal.{u} → Cardinal.{u}) {ν : Cardinal.{u}} (hL : ClosedLevel K E D g ν)
    (I₁ I₂ : Type u) [LinearOrder I₁] [WellFoundedLT I₁] [LinearOrder I₂] [WellFoundedLT I₂]
    [Nonempty I₁] (hI : #(Lex (I₁ ⊕ I₂)) = ν)
    {B₀ B₁ : Model K.τ}
    (incl₀ : Language.Embedding K.τ (E.obj (Lex (I₁ ⊕ I₂))).carrier B₀.carrier)
    (incl₁ : Language.Embedding K.τ (E.obj (Lex (I₁ ⊕ I₂))).carrier B₁.carrier)
    (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁) (hs₀ : K.Strong incl₀) (hs₁ : K.Strong incl₁)
    (hc₀ : Model.card B₀ = ν) (hc₁ : Model.card B₁ = ν)
    {α : Type u} {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hσ : σ < ν) (hα : #α ≤ σ)
    (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier) :
    (∃ P₀ : Placement E.lab E.arity (Lex (I₁ ⊕ I₂)) α, P₀.LiftsBounded E D hB₀ incl₀ d₀ ν) ∧
    (∀ P₀ P₁ : Placement E.lab E.arity (Lex (I₁ ⊕ I₂)) α,
      P₀.LiftsBounded E D hB₀ incl₀ d₀ ν →
      P₁.LiftsBounded E D hB₁ incl₁ d₁ ν →
      (P₀.AgreeOn E D P₁ Set.univ ↔
        ∀ {β : Type u}, #β ≤ g σ + ls K → ∀ (ρ : Cardinal.{u}),
          aleph0 ≤ ρ → ρ < ν → ∀ (p : β → (E.obj (Lex (I₁ ⊕ I₂))).carrier)
            (hj : #(α ⊕ β) ≤ ρ)
            (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁),
          D.same hj hB₀ hB₁ ht₀ ht₁
            (Sum.elim d₀ (fun b => incl₀ (p b)))
            (Sum.elim d₁ (fun b => incl₁ (p b))))) := by
  have : Nonempty (Lex (I₁ ⊕ I₂)) := ⟨toLex (Sum.inl (Classical.arbitrary I₁))⟩
  obtain ⟨h1, _, h3⟩ := lemma_6_5 K E D g hL hI incl₀ incl₁ hB₀ hB₁ hs₀ hs₁ hc₀ hc₁ hσinf hσ hα
    d₀ d₁
  exact ⟨h1, h3⟩

/-- **Testing over the presented two-segment layout (8).** English (Lemma 8.4 proof): "If the two
candidates disagree on the questioned test, their placed comparisons disagree and yield a witness
within that bound." Over the well-ordered two-segment presentation `E(I₁ ⊕ₗ I₂)` of size `ν` at a
closed level `ν`: candidates `d₀ ∈ B₀`, `d₁ ∈ B₁` (strong extensions of size `ν`, length at most
`σ < ν`) that agree on all layout parameter sets of size at most `g(σ) + LS(K)` agree on every
bounded layout parameter set (Lemma 6.5: tester for sufficiency, placement lifting for
necessity). The bound depends only on `σ` and the template, not on the segments. -/
theorem infra_84_layout_testing_presented (K : AbstractElementaryClass.{u})
    [CategoricalUnbounded K] (E : OrderPresentation K) (D : StableDiagram K)
    (g : Cardinal.{u} → Cardinal.{u}) {ν : Cardinal.{u}} (hL : ClosedLevel K E D g ν)
    (I₁ I₂ : Type u) [LinearOrder I₁] [WellFoundedLT I₁] [LinearOrder I₂] [WellFoundedLT I₂]
    [Nonempty I₁] (hI : #(Lex (I₁ ⊕ I₂)) = ν)
    {B₀ B₁ : Model K.τ}
    (incl₀ : Language.Embedding K.τ (E.obj (Lex (I₁ ⊕ I₂))).carrier B₀.carrier)
    (incl₁ : Language.Embedding K.τ (E.obj (Lex (I₁ ⊕ I₂))).carrier B₁.carrier)
    (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁) (hs₀ : K.Strong incl₀) (hs₁ : K.Strong incl₁)
    (hc₀ : Model.card B₀ = ν) (hc₁ : Model.card B₁ = ν)
    {α : Type u} {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hσ : σ < ν) (hα : #α ≤ σ)
    (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier)
    (hsmall : ∀ {β : Type u}, #β ≤ g σ + ls K → ∀ (ρ : Cardinal.{u}),
      aleph0 ≤ ρ → ρ < ν → ∀ (p : β → (E.obj (Lex (I₁ ⊕ I₂))).carrier)
        (hj : #(α ⊕ β) ≤ ρ)
        (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁),
        D.same hj hB₀ hB₁ ht₀ ht₁
          (Sum.elim d₀ (fun b => incl₀ (p b))) (Sum.elim d₁ (fun b => incl₁ (p b))))
    {β : Type u} (ρ : Cardinal.{u}) (hρinf : aleph0 ≤ ρ) (hρ : ρ < ν)
    (p : β → (E.obj (Lex (I₁ ⊕ I₂))).carrier) (hj : #(α ⊕ β) ≤ ρ)
    (ht₀ : D.t ρ ≤ Model.card B₀) (ht₁ : D.t ρ ≤ Model.card B₁) :
    D.same hj hB₀ hB₁ ht₀ ht₁
      (Sum.elim d₀ (fun b => incl₀ (p b))) (Sum.elim d₁ (fun b => incl₁ (p b))) := by
  have : Nonempty (Lex (I₁ ⊕ I₂)) := ⟨toLex (Sum.inl (Classical.arbitrary I₁))⟩
  obtain ⟨⟨P₀, h₀⟩, _, _⟩ := lemma_6_5 K E D g hL hI incl₀ incl₁ hB₀ hB₁ hs₀ hs₁ hc₀ hc₁
    hσinf hσ hα d₀ d₁
  obtain ⟨⟨P₁, h₁⟩, _, _⟩ := lemma_6_5 K E D g hL hI incl₁ incl₀ hB₁ hB₀ hs₁ hs₀ hc₁ hc₀
    hσinf hσ hα d₁ d₀
  have hag : P₀.AgreeOn E D P₁ Set.univ :=
    ((placedComparison_agree_iff_tests hL hI hc₀ hc₁ hσinf hσ hα h₀ h₁).mpr
      (fun hβ ρ' h1 h2 p' hj' ht₀' ht₁' => hsmall hβ ρ' h1 h2 p' hj' ht₀' ht₁'))
  exact h₀.same_of_agreeOn hL hI h₁ hag ρ hρinf hρ p hj ht₀ ht₁

/-- Every eligible level of `P` is a closed level of its presentation data (`ClosedLevel K P.E P.D
P.g`), so Section 4/6 placed-comparison results apply at the levels of `P.scheme`. -/
theorem infra_84_closedLevel_single (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) : ClosedLevel K P.E P.D P.g μ := by
  have := P.D.categoricalUnbounded
  exact ClosedLevel.of_closurePoint P.tester hμ.1 hμ.2

/-- Change of bound for `D.same` in two models of an eligible size `ν`, between two infinite bounds
below `ν` (`StableDiagram.same_relevel`). -/
theorem infra_84_same_relevel_single (P : SingleModelData K) {ν : Cardinal.{u}}
    (hν : ν ∈ P.eligible) {M N : Model K.τ} (hM : K.Mem M) (hN : K.Mem N)
    (hcM : Model.card M = ν) (hcN : Model.card N = ν) {γ : Type u} {σ₁ τ₁ : Cardinal.{u}}
    (h1 : #γ ≤ σ₁) (h2 : #γ ≤ τ₁) (hσ₁ : aleph0 ≤ σ₁) (hτ₁ : aleph0 ≤ τ₁) (hσν : σ₁ < ν)
    (hτν : τ₁ < ν) (hMσ : P.D.t σ₁ ≤ Model.card M) (hNσ : P.D.t σ₁ ≤ Model.card N)
    (hMτ : P.D.t τ₁ ≤ Model.card M) (hNτ : P.D.t τ₁ ≤ Model.card N)
    (xs : γ → M.carrier) (ys : γ → N.carrier)
    (h : P.D.same h1 hM hN hMσ hNσ xs ys) : P.D.same h2 hM hN hMτ hNτ xs ys := by
  have hL := infra_84_closedLevel_single P hν
  set σ' := max (max σ₁ τ₁) (ls K)
  have hσ'ν : σ' < ν := max_lt (max_lt hσν hτν) hν.2
  have hσ'inf : aleph0 ≤ σ' := hσ₁.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hM' : P.D.t σ' ≤ Model.card M := (hL.t_lt hσ'inf hσ'ν).le.trans hcM.ge
  have hN' : P.D.t σ' ≤ Model.card N := (hL.t_lt hσ'inf hσ'ν).le.trans hcN.ge
  exact P.D.same_relevel h1 hσ₁ hτ₁ ((le_max_left _ _).trans (le_max_left _ _))
    ((le_max_right _ _).trans (le_max_left _ _)) (le_max_right _ _) hM hN hMσ hNσ hM' hN'
    hMτ hNτ xs ys h h2 id

/-- **Layout (8) testing for `P` (presented layout, canonical-bound form).** At an eligible level
`ν` of `P`, over the two-segment presentation `P.E(I₁ ⊕ₗ I₂)` of size `ν`: candidates `d₀ ∈ B₀`,
`d₁ ∈ B₁` (strong extensions of size `ν`, length at most `σ < ν`) whose `D`-diagrams with every
layout parameter list of size at most `g(σ) + LS(K)` agree have equal `D`-diagrams with every
layout parameter list of total size `< ν`. -/
theorem infra_84_layout_testing_single_presented (P : SingleModelData K) {ν : Cardinal.{u}}
    (hν : ν ∈ P.eligible)
    (I₁ I₂ : Type u) [LinearOrder I₁] [WellFoundedLT I₁] [LinearOrder I₂] [WellFoundedLT I₂]
    [Nonempty I₁] (hI : #(Lex (I₁ ⊕ I₂)) = ν)
    {B₀ B₁ : Model K.τ}
    (incl₀ : Language.Embedding K.τ (P.E.obj (Lex (I₁ ⊕ I₂))).carrier B₀.carrier)
    (incl₁ : Language.Embedding K.τ (P.E.obj (Lex (I₁ ⊕ I₂))).carrier B₁.carrier)
    (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁) (hs₀ : K.Strong incl₀) (hs₁ : K.Strong incl₁)
    (hc₀ : Model.card B₀ = ν) (hc₁ : Model.card B₁ = ν)
    {α : Type u} {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hσ : σ < ν) (hα : #α ≤ σ)
    (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier)
    (hsmall : ∀ {β : Type u}, #β ≤ P.g σ + ls K →
      ∀ (p : β → (P.E.obj (Lex (I₁ ⊕ I₂))).carrier),
        P.D.SameD B₀ B₁ (Sum.elim d₀ (fun b => incl₀ (p b))) (Sum.elim d₁ (fun b => incl₁ (p b))))
    {β : Type u} (p : β → (P.E.obj (Lex (I₁ ⊕ I₂))).carrier) (hj : #(α ⊕ β) < ν) :
    P.D.SameD B₀ B₁ (Sum.elim d₀ (fun b => incl₀ (p b))) (Sum.elim d₁ (fun b => incl₁ (p b))) := by
  have := P.D.categoricalUnbounded
  have hL := infra_84_closedLevel_single P hν
  have hρν : max #(α ⊕ β) ℵ₀ < ν := max_lt hj (P.aleph0_lt hν)
  have ht₀ : P.D.t (max #(α ⊕ β) ℵ₀) ≤ Model.card B₀ :=
    (hL.t_lt (le_max_right _ _) hρν).le.trans hc₀.ge
  have ht₁ : P.D.t (max #(α ⊕ β) ℵ₀) ≤ Model.card B₁ :=
    (hL.t_lt (le_max_right _ _) hρν).le.trans hc₁.ge
  refine ⟨hB₀, hB₁, ht₀, ht₁, ?_⟩
  refine infra_84_layout_testing_presented K P.E P.D P.g hL I₁ I₂ hI incl₀ incl₁ hB₀ hB₁ hs₀ hs₁
    hc₀ hc₁ hσinf hσ hα d₀ d₁ ?_ _ (le_max_right _ _) hρν p (le_max_left _ _) ht₀ ht₁
  intro β' hβ' ρ' hρ'inf hρ' p' hj' ht₀' ht₁'
  obtain ⟨_, _, hc0, hc1, hS⟩ := hsmall hβ' p'
  have hcan : max #(α ⊕ β') ℵ₀ < ν := lt_of_le_of_lt (max_le hj' hρ'inf) hρ'
  exact infra_84_same_relevel_single P hν hB₀ hB₁ hc₀ hc₁ (le_max_left _ _) hj'
    (le_max_right _ _) hρ'inf hcan hρ' hc0 hc1 ht₀' ht₁' _ _ hS

end AEC
