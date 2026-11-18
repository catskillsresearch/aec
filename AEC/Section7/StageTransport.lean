module

public import AEC.Section7.AssemblyLevel

@[expose] public section

/-!
# Prop 7.8: the seed mark carried to every matrix stage (`infra_78_stage_transport`)

Paper: "Extend `X` by a presentation arrow to a level-`κ` object `X_0`, and choose `Y_0 ≥ X_0`
containing a realization `b` of the free lift of `p`. We construct continuous pairs
`X_i ≤ Y_i` ... with a single fixed `b` in all the upper objects."

* `infra_78_tiedFreeMixed_forward` (generic): mixed tied freeness over `X` (along `ι0 : X → X_0`)
  of a mark `b1` in `Y_1 ≥ X_0` moves forward along an arrow `h : Y_1 → Y_2` over
  `g : X_0 → X_k` (commuting square, `h b1 = b2`) to the mark `b2` restricted to `X_0`; the small
  test diagrams over `X` are unchanged.
* `infra_78_stage_transport`: in the recursion matrix with seed base map the identity, at every
  stage `k` the base map is the `X`-step from the seed, the mark is the `Y`-step image of the seed
  mark, and the seed's mixed tied freeness over `X` and its small-test diagrams hold for the
  stage-`k` mark restricted to `X_0` along the base map.
-/

universe u

open Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Forward transport of mixed tied freeness along the upper arrow (proved).** -/
theorem infra_78_tiedFreeMixed_forward {P : SingleModelData K} {ν κ : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hκ : κ ∈ P.eligible}
    {X : P.scheme.Object ν hν} {B Y1 Xk Y2 : P.scheme.Object κ hκ}
    (ι0 : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hκ B))
    (pr1 : SystemArrow K oneVertexShape (P.scheme.asSystem hκ B) (P.scheme.asSystem hκ Y1))
    (pr2 : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xk) (P.scheme.asSystem hκ Y2))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hκ B) (P.scheme.asSystem hκ Xk))
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Y1) (P.scheme.asSystem hκ Y2))
    {uIdx : Type u} (b1 : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Y1))
    (b2 : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Y2))
    (hsq : ∀ x, h.onVertex PUnit.unit (pr1.onVertex PUnit.unit x) =
      pr2.onVertex PUnit.unit (g.onVertex PUnit.unit x))
    (hb : ∀ u, b2 u = ⟨(b1 u).1, h.onVertex (b1 u).1 (b1 u).2⟩)
    (hidx : #uIdx < ν) (hνκ : ν ≤ κ)
    (H : IsTiedFreeMixed ι0 ((infra_78_markTuple pr1 b1).restrict ι0 trivial)
      (infra_78_markTuple pr1 b1) (Equiv.refl _)) :
    IsTiedFreeMixed ι0 (((infra_78_markTuple pr2 b2).restrict g trivial).restrict ι0 trivial)
        ((infra_78_markTuple pr2 b2).restrict g trivial) (Equiv.refl _) ∧
      ∀ {β : Type u} (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν X)), #β < ν →
        P.scheme.DiagramEq (X := Y1) (Y := Y2)
          (typeJoint (p := (infra_78_markTuple pr1 b1).restrict ι0 trivial) Z0)
          (typeJoint (p := ((infra_78_markTuple pr2 b2).restrict g trivial).restrict ι0 trivial)
            Z0) := by
  classical
  have hν0 : ℵ₀ ≤ ν := P.aleph0_le hν
  have hsz : ∀ {β : Type u}, #β < ν → #(uIdx ⊕ β) < ν := fun hβ => by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hν0 hidx hβ
  have DT : ∀ {β : Type u} (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν X)),
      #β < ν →
      P.scheme.DiagramEq (X := Y1) (Y := Y2)
        (typeJoint (p := (infra_78_markTuple pr1 b1).restrict ι0 trivial) Z0)
        (typeJoint (p := ((infra_78_markTuple pr2 b2).restrict g trivial).restrict ι0 trivial)
          Z0) := by
    intro β Z0 hβ
    have hp := P.scheme.diagram_preserved Y1 Y2 h trivial
      (typeJoint (p := (infra_78_markTuple pr1 b1).restrict ι0 trivial) Z0) ((hsz hβ).trans_le hνκ)
      ((hsz hβ).trans_le hνκ)
    refine infra_73_diagramEq_of_eq hp (fun _ => rfl) ?_
    rintro (u | x)
    · exact (hb u).symm
    · show (⟨(Z0 x).1, h.onVertex (Z0 x).1 (pr1.onVertex (Z0 x).1
          (ι0.onVertex (Z0 x).1 (Z0 x).2))⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hκ Y2)) =
        ⟨(Z0 x).1, pr2.onVertex (Z0 x).1 (g.onVertex (Z0 x).1
          (ι0.onVertex (Z0 x).1 (Z0 x).2))⟩
      generalize Z0 x = z
      rcases z with ⟨⟨⟩, z⟩
      rw [hsq]
  refine ⟨?_, DT⟩
  intro seq ι Z Z0 hlen hιτ hιν hmove
  let seq1 : ApproximationSequence ((infra_78_markTuple pr1 b1).restrict ι0 trivial) :=
    { τ := #ι
      κIndex := seq.κIndex
      family := seq.family
      concat_bounded := seq.concat_bounded
      few_exceptions := fun {β} W hW => by
        refine le_trans ?_ (seq.few_exceptions W (hW.trans hιτ))
        refine Cardinal.mk_le_of_injective (f := fun j => ⟨j.1, fun hgood => j.2 ?_⟩)
          (by
            intro j₁ j₂ hj
            apply Subtype.ext
            have := congrArg Subtype.val hj
            exact this)
        exact P.scheme.diagram_trans _ _ _ _ _ _ (DT W (hW.trans_lt hιν)) hgood }
  have hlen1 : seq1.τ + ℵ₀ < #seq1.κIndex := (add_le_add hιτ le_rfl).trans_lt hlen
  have d := H seq1 Z Z0 hlen1 le_rfl hιν hmove
  have hA := P.scheme.diagram_preserved Y1 Y2 h trivial
    (infra_612_anchored (Equiv.refl _) (infra_78_markTuple pr1 b1).incl
      (infra_78_markTuple pr1 b1).val Z) ((hsz hιν).trans_le hνκ) ((hsz hιν).trans_le hνκ)
  have hA' : P.scheme.DiagramEq (X := Y1) (Y := Y2)
      (infra_612_anchored (Equiv.refl _) (infra_78_markTuple pr1 b1).incl
        (infra_78_markTuple pr1 b1).val Z)
      (infra_612_anchored (Equiv.refl _) ((infra_78_markTuple pr2 b2).restrict g trivial).incl
        ((infra_78_markTuple pr2 b2).restrict g trivial).val Z) := by
    refine infra_73_diagramEq_of_eq hA (fun _ => rfl) ?_
    rintro (u | j)
    · exact (hb u).symm
    · show (⟨(Z j).1, h.onVertex (Z j).1 (pr1.onVertex (Z j).1 (Z j).2)⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hκ Y2)) =
        ⟨(Z j).1, pr2.onVertex (Z j).1 (g.onVertex (Z j).1 (Z j).2)⟩
      generalize Z j = z
      rcases z with ⟨⟨⟩, z⟩
      rw [hsq]
  exact P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ (DT Z0 hιν))
    (P.scheme.diagram_trans _ _ _ _ _ _ d hA')

section Stage
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible} {uIdx cIdx L : Type u}
variable (hρκ : Order.succ ρ < κ) (Xb : P.scheme.Object κ hκ) {ℓ : Cardinal.{u}}
  (hℓel : ℓ ∈ P.eligible)
  (cand : (Order.succ ρ).ord.ToType → Infra78Stage P hκ (Infra78MarkData κ uIdx) →
    L → cIdx → κ.ord.ToType)
  (s0 : Infra78Stage P hκ (Infra78MarkData κ uIdx)) (e0 : Infra78MarkData κ uIdx)

include hρκ in
/-- **`infra_78_stage_transport` (proved).** In the recursion matrix whose seed has the identity
base map, at every stage `k` (from the least stage `i0`): the base map is the `X`-step, the mark is
the `Y`-step image of the seed mark ("a single fixed `b` in all the upper objects"), and the
seed's mixed tied freeness over `X` (along `ι0 : X → X_0`) and its small-test diagrams over `X`
hold for the stage-`k` mark restricted to `X_0` along the base map `g`. -/
theorem infra_78_stage_transport {ν : Cardinal.{u}} {hν : ν ∈ P.eligible}
    {X : P.scheme.Object ν hν}
    (ι0 : SystemArrow K oneVertexShape (P.scheme.asSystem hν X) (P.scheme.asSystem hκ s0.X))
    (hg0 : s0.e.g = id) (hidx : #uIdx < ν) (hνκ : ν ≤ κ)
    (H0 : IsTiedFreeMixed ι0
      ((infra_78_markTuple (infra_78_toArr s0.hp) (infra_78_stageMark s0)).restrict ι0 trivial)
      (infra_78_markTuple (infra_78_toArr s0.hp) (infra_78_stageMark s0)) (Equiv.refl _))
    {i0 : (Order.succ ρ).ord.ToType} (hmin : IsMin i0) (k : (Order.succ ρ).ord.ToType)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hκ s0.X)
      (P.scheme.asSystem hκ (infra_78_rcObj Xb hℓel cand s0 e0 k).X))
    (hg : ∀ x, g.onVertex PUnit.unit x = (infra_78_rcObj Xb hℓel cand s0 e0 k).e.g x) :
    (∀ x, (infra_78_rcObj Xb hℓel cand s0 e0 k).e.g x =
      (infra_78_rcMap Xb hℓel cand s0 e0 i0 k).1 x) ∧
    (∀ u, (infra_78_rcObj Xb hℓel cand s0 e0 k).e.b u =
      (infra_78_rcMap Xb hℓel cand s0 e0 i0 k).2 (s0.e.b u)) ∧
    IsTiedFreeMixed ι0
      (((infra_78_markTuple (infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 k).hp)
        (infra_78_stageMark (infra_78_rcObj Xb hℓel cand s0 e0 k))).restrict g trivial).restrict
          ι0 trivial)
      ((infra_78_markTuple (infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 k).hp)
        (infra_78_stageMark (infra_78_rcObj Xb hℓel cand s0 e0 k))).restrict g trivial)
      (Equiv.refl _) ∧
    ∀ {β : Type u} (Z0 : β → Occurrence K oneVertexShape (P.scheme.asSystem hν X)), #β < ν →
      P.scheme.DiagramEq (X := s0.Y) (Y := (infra_78_rcObj Xb hℓel cand s0 e0 k).Y)
        (typeJoint (p := (infra_78_markTuple (infra_78_toArr s0.hp)
          (infra_78_stageMark s0)).restrict ι0 trivial) Z0)
        (typeJoint (p := ((infra_78_markTuple
          (infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 k).hp)
          (infra_78_stageMark (infra_78_rcObj Xb hℓel cand s0 e0 k))).restrict g trivial).restrict
            ι0 trivial) Z0) := by
  classical
  have hsop := infra_78_succOp_stageArr Xb (infra_78_rcl ρ hℓel) cand
  obtain ⟨hA, -, -⟩ := infra_78_pairChain_laws hρκ s0
    (infra_78_succOp Xb (infra_78_rcl ρ hℓel) cand) (infra_78_limMarkE e0) hsop
  have hik : i0 ≤ k := (le_total i0 k).elim id (fun h => hmin h)
  have h0 : infra_78_rcObj Xb hℓel cand s0 e0 i0 = s0 := infra_78_pairMatrix_min s0 _ _ hmin
  obtain ⟨hcg, hcb⟩ := infra_78_opMatrix_coherent hρκ Xb (infra_78_rcl ρ hℓel) cand s0 e0 i0 k hik
  obtain ⟨-, hYarr, hcomm⟩ := hA i0 k hik
  rw [congrArg (fun s => s.e.g) h0, hg0] at hcg
  rw [congrArg (fun s => s.e.b) h0] at hcb
  rw [congrArg (fun s => s.p) h0] at hcomm
  have key : ∀ t : Infra78Stage P hκ (Infra78MarkData κ uIdx), t = s0 →
      infra_78_IsArr t.Y (infra_78_rcObj Xb hℓel cand s0 e0 k).Y
        (infra_78_rcMap Xb hℓel cand s0 e0 i0 k).2 →
      infra_78_IsArr s0.Y (infra_78_rcObj Xb hℓel cand s0 e0 k).Y
        (infra_78_rcMap Xb hℓel cand s0 e0 i0 k).2 := by
    rintro t rfl hh; exact hh
  have hY := key _ h0 hYarr
  have hgx : ∀ x, (infra_78_rcObj Xb hℓel cand s0 e0 k).e.g x =
      (infra_78_rcMap Xb hℓel cand s0 e0 i0 k).1 x := fun x => by rw [hcg]; rfl
  have hbu : ∀ u, (infra_78_rcObj Xb hℓel cand s0 e0 k).e.b u =
      (infra_78_rcMap Xb hℓel cand s0 e0 i0 k).2 (s0.e.b u) := fun u => by rw [hcb]; rfl
  have F := infra_78_tiedFreeMixed_forward ι0 (infra_78_toArr s0.hp)
    (infra_78_toArr (infra_78_rcObj Xb hℓel cand s0 e0 k).hp) g (infra_78_toArr hY)
    (infra_78_stageMark s0) (infra_78_stageMark (infra_78_rcObj Xb hℓel cand s0 e0 k))
    (fun x => by
      rw [infra_78_toArr_apply, infra_78_toArr_apply, infra_78_toArr_apply, hg]
      refine Eq.trans ?_ (congrArg (infra_78_rcObj Xb hℓel cand s0 e0 k).p (hgx x)).symm
      exact (congrFun hcomm x).symm)
    (fun u => by
      show (⟨PUnit.unit, (infra_78_rcObj Xb hℓel cand s0 e0 k).e.b u⟩ :
          Occurrence K oneVertexShape _) =
        ⟨PUnit.unit, (infra_78_toArr hY).onVertex PUnit.unit (s0.e.b u)⟩
      rw [hbu, infra_78_toArr_apply hY (s0.e.b u)])
    hidx hνκ H0
  exact ⟨hgx, hbu, F.1, F.2⟩

end Stage

end AEC
