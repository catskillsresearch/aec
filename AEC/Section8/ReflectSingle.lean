module

public import AEC.Section8.ComparisonSingle

@[expose] public section

/-!
# Lemma 8.2(5) reflection for P.scheme: realization inside the small base

Cycle 99. English (Lemma 8.2 proof): "Inside the second small base, realize a copy of this list
over the second small approximation list and the required base entries. This is a bounded
realization problem ... mixed saturation in the underlying scheme realizes the joint diagram.
Small-level homogeneity extends this match to an isomorphism of the small bases."
-/

namespace AEC
section

universe u
open Cardinal Classical FirstOrder Function
variable {K : AbstractElementaryClass.{u}}

/-- **Saturation inside the object (realization in the small base).** Definition 5.2(3)
saturation realizes a witnessed joint diagram over a bounded list of `X` in some extension `Z`
of `X` at the same level; bounded homogeneity (`diagram_iso`) at that level moves the
realization back into `X` over the original list. -/
theorem infra_82_saturate_inside {S : SystemShape.{u}} {W : WorkingScheme K S}
    [hS : IsSaturated W] {μ ν : Cardinal.{u}} {hμ : μ ∈ W.eligible} {hν : ν ∈ W.eligible}
    {α β : Type u} (X : W.Object μ hμ) (Y : W.Object ν hν)
    (xs : α → Occurrence K S (W.asSystem hμ X))
    (base : α → Occurrence K S (W.asSystem hν Y))
    (ext : α ⊕ β → Occurrence K S (W.asSystem hν Y))
    (hα : #α < μ) (hβ : #β < μ) (hαβ : #(α ⊕ β) < μ)
    (hext : ∀ i, ext (Sum.inl i) = base i)
    (hEq : W.DiagramEq (X := X) (Y := Y) xs base) :
    ∃ ws : α ⊕ β → Occurrence K S (W.asSystem hμ X),
      (∀ i, ws (Sum.inl i) = xs i) ∧ W.DiagramEq (X := X) (Y := Y) ws ext := by
  obtain ⟨Z, f, zs, hf, hzs, hD⟩ := hS.saturated X Y xs base ext hα hβ hext hEq
  have d1 := W.diagram_preserved X Z f hf xs hα hα
  obtain ⟨g, hg, hgx⟩ := (W.diagram_iso Z X _ xs hα).mp (W.diagram_symm _ _ _ _ d1)
  refine ⟨fun j => ⟨(zs j).1, g.onVertex (zs j).1 (zs j).2⟩, fun i => ?_, ?_⟩
  · show (⟨(zs (Sum.inl i)).1, g.onVertex (zs (Sum.inl i)).1 (zs (Sum.inl i)).2⟩ :
        Occurrence K S (W.asSystem hμ X)) = xs i
    rw [hzs i]
    exact (hgx i).symm
  · have d2 := W.diagram_preserved Z X g (W.structural_iso Z X g hg) zs hαβ hαβ
    exact W.diagram_trans _ _ _ _ _ _ (W.diagram_symm _ _ _ _ d2) hD

/-- **An isolated type is invariant under base automorphisms fixing the fragment.** If the
fragment `Wf` isolates `q` over `B` relative to the `u`-marginal, and a base self-arrow `h`
fixes `Wf` entrywise and preserves the `u`-marginal's type, then `q` read through `h` has the
type of `q`. (The approximation calculation of the Lemma 8.2 proof: the type is computed by the
isolating list.) -/
theorem infra_82_isolated_fixing_iso {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {B : P.scheme.Object μ hμ}
    (q : TupleOver K oneVertexShape P.scheme hμ B) {uIdx cIdx : Type u}
    (e : q.idx ≃ uIdx ⊕ cIdx) {ι : Type u}
    (Wf : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hW : IsIsolatingFragment q e Wf) (hqν : q.ν = μ)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ B) (P.scheme.asSystem hμ B))
    (hh : P.scheme.permitted (X := B) (Y := B) h)
    (hfix : ∀ j, h.mapOcc (Wf j) = Wf j)
    (hmarg : SameGaloisType (q.marginal e) ((q.restrict h hh).marginal e)
      (Equiv.refl uIdx) (Equiv.refl uIdx)) :
    SameGaloisType q (q.restrict h hh) e e := by
  refine hW.2 (q.restrict h hh) e hqν hmarg ?_
  have heq : alignJoint e (typeJoint (p := q.restrict h hh) Wf) =
      alignJoint e (typeJoint (p := q) Wf) := by
    funext x
    rcases x with i | j
    · rfl
    · change q.incl.mapOcc (h.mapOcc (Wf j)) = q.incl.mapOcc (Wf j)
      rw [hfix j]
  exact infra_73_diagramEq_of_eq (P.scheme.diagram_refl _ (alignJoint e (typeJoint (p := q) Wf)))
    (fun _ => rfl) (fun t => (congrFun heq t).symm)

/-- Positional self-matching through `arity` is the identity. -/
theorem infra_82_self_positional_eq {B A : Type u} {F : Type*} (r : B ≃ A) (a : A ≃ F) :
    r.trans ((a.trans a.symm).trans r.symm) = Equiv.refl B := by
  ext y
  simp

set_option maxHeartbeats 6400000 in
/-- **Realization in the small pair of a list of the large base (P.scheme; core of the 8.2(5)
reflection).** For a marked arrow `f : M → N` up a level (both levels on the closure tail), a
bounded tuple `t` of `M.Y` and a bounded list `Wl` of `N.X`, there is a list `V` of `M.X` such that
`(b, t, V)` in `M.Y` has the joint diagram of `(b′ ∘ markMap, f t, Wl)` in `N.Y`. English
(Lemma 8.2 proof): realize inside the small base a copy of the list over the small approximation
list (saturation, `infra_82_saturate_inside`); the approximation list isolates the free extension
over the large base (`infra_72_mixed_level_closed`), so an automorphism of the large base fixing
it and matching the copy with `Wl` transports the joint type (`infra_82_isolated_fixing_iso`). -/
theorem infra_82_reflect_realize_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme} (hiso : Pr.CommutesWithIso)
    (hTA : Pr.TiedAlong) {M N : MarkedPair K oneVertexShape P.scheme Pr}
    (f : MarkedArrow K oneVertexShape P.scheme Pr M N)
    (hM : M.μ ∈ infra_615_closed P) (hN : N.μ ∈ infra_615_closed P) (hlev : M.μ ≤ N.μ)
    {ι δ : Type u} (t : ι → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.Y))
    (hι : #ι < M.μ) (Wl : δ → Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.X))
    (hδ : #δ < M.μ) :
    ∃ V : δ → Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.X),
      P.scheme.DiagramEq (X := M.Y) (Y := N.Y)
        (seqJoint (seqJoint M.b t) (fun j => M.incl.mapOcc (V j)))
        (seqJoint (seqJoint (fun k => N.b (f.markMap k)) (fun i => f.onY.mapOcc (t i)))
          (fun j => N.incl.mapOcc (Wl j))) := by
  classical
  obtain ⟨γ, Z, hγ, HZ⟩ := M.dominated ι t hι
  have hfinB : Finite M.bIdx :=
    Finite.of_equiv _ (M.realEq.trans (Pr.arity M.hμ M.X)).symm
  have hμ0 : ℵ₀ < M.μ := P.aleph0_lt M.hμ
  have hBlt : #M.bIdx < M.μ := (Cardinal.lt_aleph0_of_finite M.bIdx).trans hμ0
  have hbι : #(M.bIdx ⊕ ι) < M.μ := by
    simp only [mk_sum, lift_id]
    exact add_lt_of_lt (P.aleph0_le M.hμ) hBlt hι
  have hγδ : #(γ ⊕ δ) < M.μ := by
    simp only [mk_sum, lift_id]
    exact add_lt_of_lt (P.aleph0_le M.hμ) hγ hδ
  have hbιδ : #((M.bIdx ⊕ ι) ⊕ δ) < M.μ := by
    simp only [mk_sum, lift_id] at hbι ⊢
    exact add_lt_of_lt (P.aleph0_le M.hμ) hbι hδ
  have hExt := infra_82_marked_arrow_ext_single f t
  have hTied := infra_82_mark_tied_along_mixed hTA f hlev
  let κ : Cardinal.{u} := max (#(M.bIdx ⊕ ι)) ℵ₀
  have hκ : ℵ₀ ≤ κ := le_max_right _ _
  have hκμ : κ < M.μ := max_lt hbι hμ0
  have hrec : M.μ ∈ recursionClosedLevels P κ :=
    ⟨hM.1, fun β₀ hβ => hM.2 κ hκ hκμ β₀ hβ⟩
  have hrecN : N.μ ∈ recursionClosedLevels P κ :=
    ⟨hN.1, fun β₀ hβ => hN.2 κ hκ (hκμ.trans_le hlev) β₀ hβ⟩
  have hκSucc : Order.succ κ ≤ M.μ := Order.succ_le_of_lt hκμ
  have hidx : #(M.bIdx ⊕ ι) ≤ κ := le_max_left _ _
  have hW := infra_72_mixed_level_closed P κ hκ M.hμ N.hμ hlev hrec hκSucc hrecN f.onX
    trivial (asTuple M.incl M.incl_arrow (seqJoint M.b t))
    (asTuple N.incl N.incl_arrow (seqJoint N.b (fun i => f.onY.mapOcc (t i))))
    (Equiv.sumCongr f.markMap (Equiv.refl ι)) (Equiv.refl _) rfl rfl hidx hbι Z ⟨hγ, HZ⟩
    hExt hTied
  -- realize a copy of `Wl` over `f Z` inside `M.X`
  have hsat : IsSaturated P.scheme := P.isSaturated
  obtain ⟨ws, hws, hD⟩ := infra_82_saturate_inside (W := P.scheme) M.X N.X Z
    (pushParams f.onX Z) (Sum.elim (pushParams f.onX Z) Wl) hγ hδ hγδ (fun _ => rfl)
    (P.scheme.diagram_preserved M.X N.X f.onX trivial Z hγ (hγ.trans_le hlev))
  have d1 := P.scheme.diagram_preserved M.X N.X f.onX trivial ws hγδ (hγδ.trans_le hlev)
  obtain ⟨h, hhiso, hhmap⟩ := (P.scheme.diagram_iso N.X N.X _ _ (hγδ.trans_le hlev)).mp
    (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d1) hD)
  have hh : P.scheme.permitted (X := N.X) (Y := N.X) h := P.scheme.structural_iso _ _ h hhiso
  have hbij := P.scheme.isStructIso_bijective _ _ h hhiso
  have hfix : ∀ j, h.mapOcc (pushParams f.onX Z j) = pushParams f.onX Z j := by
    intro j
    have e1 := hhmap (Sum.inl j)
    have e2 := hws j
    have e3 := congrArg (fun x => h.mapOcc (f.onX.mapOcc x)) e2
    exact (e1.trans e3).symm
  have MT0 := infra_82_mark_type_iso_single hiso N N rfl h hbij
  have MT := cast (congrArg (fun E => SameGaloisType (asTuple N.incl N.incl_arrow N.b)
    ((asTuple N.incl N.incl_arrow N.b).restrict h trivial) E (Equiv.refl _))
    (infra_82_self_positional_eq N.realEq (Pr.arity N.hμ N.X))) MT0
  have hmarg : SameGaloisType
      ((asTuple N.incl N.incl_arrow (seqJoint N.b (fun i => f.onY.mapOcc (t i)))).marginal
        ((Equiv.sumCongr f.markMap (Equiv.refl ι)).symm.trans (Equiv.refl _)))
      (((asTuple N.incl N.incl_arrow (seqJoint N.b (fun i => f.onY.mapOcc (t i)))).restrict
        h hh).marginal ((Equiv.sumCongr f.markMap (Equiv.refl ι)).symm.trans (Equiv.refl _)))
      (Equiv.refl _) (Equiv.refl _) := by
    rcases MT with ⟨ρ, hρ, top, g1, g2, h1, h2, hc, hv⟩
    refine ⟨ρ, hρ, top, g1, g2, h1, h2, hc, fun k => ?_⟩
    exact hv (f.markMap k)
  have S := infra_82_isolated_fixing_iso _ _ (pushParams f.onX Z) hW rfl h hh hfix hmarg
  have hN' : #((M.bIdx ⊕ ι) ⊕ δ) < N.μ := hbιδ.trans_le hlev
  have DD := infra_78_diagramEq_of_sameGalois S (fun j => f.onX.mapOcc (ws (Sum.inr j))) hN' hN'
  have dY := P.scheme.diagram_preserved M.Y N.Y f.onY trivial
    (seqJoint (seqJoint M.b t) (fun j => M.incl.mapOcc (ws (Sum.inr j)))) hbιδ hN'
  refine ⟨fun j => ws (Sum.inr j), ?_⟩
  have hcomm : ∀ x : Occurrence K oneVertexShape (P.scheme.asSystem M.hμ M.X),
      f.onY.mapOcc (M.incl.mapOcc x) = N.incl.mapOcc (f.onX.mapOcc x) := fun x =>
    congrArg (Sigma.mk x.1) (congrArg (fun g => SystemArrow.onVertex g x.1 x.2) f.comm)
  have dY' := infra_73_diagramEq_of_eq dY (fun _ => rfl)
    (ys' := alignJoint ((Equiv.sumCongr f.markMap (Equiv.refl ι)).symm.trans (Equiv.refl _))
      (typeJoint (p := asTuple N.incl N.incl_arrow (seqJoint N.b (fun i => f.onY.mapOcc (t i))))
        (fun j => f.onX.mapOcc (ws (Sum.inr j)))))
    (fun x => by
      rcases x with (k | i) | j
      · exact f.preserves_mark k
      · rfl
      · exact hcomm _)
  have d := P.scheme.diagram_trans _ _ _ _ _ _ dY' DD
  refine infra_73_diagramEq_of_eq d (fun _ => rfl) (fun x => ?_)
  rcases x with (k | i) | j
  · rfl
  · rfl
  · have e1 := hhmap (Sum.inr j)
    change Wl j = h.mapOcc (f.onX.mapOcc (ws (Sum.inr j))) at e1
    change N.incl.mapOcc (h.mapOcc (f.onX.mapOcc (ws (Sum.inr j)))) = N.incl.mapOcc (Wl j)
    rw [e1]

/-- Bounded homogeneity between objects at equal levels (P.scheme). -/
theorem infra_82_diagram_iso_cross {P : SingleModelData K} {μ ν : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible} (hμν : μ = ν)
    (X : P.scheme.Object μ hμ) (Y : P.scheme.Object ν hν) {α : Type u}
    (xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ X))
    (ys : α → Occurrence K oneVertexShape (P.scheme.asSystem hν Y)) (hα : #α < μ)
    (h : P.scheme.DiagramEq (X := X) (Y := Y) xs ys) :
    ∃ f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hν Y),
      (∀ v, Function.Bijective (f.onVertex v)) ∧ P.scheme.permitted (X := X) (Y := Y) f ∧
      ∀ i, ys i = f.mapOcc (xs i) := by
  subst hμν
  obtain ⟨f, hf, hmap⟩ := (P.scheme.diagram_iso X Y xs ys hα).mp h
  exact ⟨f, P.scheme.isStructIso_bijective _ _ f hf, P.scheme.structural_iso _ _ f hf, hmap⟩

/-- Diagram equality between objects at equal levels transfers equalities of entries. -/
theorem infra_82_diag_eq_transfer {P : SingleModelData K} {μ ν : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible} (hμν : μ = ν)
    {X : P.scheme.Object μ hμ} {Y : P.scheme.Object ν hν} {α : Type u}
    {xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ X)}
    {ys : α → Occurrence K oneVertexShape (P.scheme.asSystem hν Y)} (hα : #α < μ)
    (h : P.scheme.DiagramEq (X := X) (Y := Y) xs ys) (i j : α) (hij : xs i = xs j) :
    ys i = ys j := by
  obtain ⟨f, -, -, hmap⟩ := infra_82_diagram_iso_cross hμν X Y xs ys hα h
  rw [hmap i, hmap j, hij]

set_option maxHeartbeats 12800000 in
/-- **Lemma 8.2(5) for P.scheme, reflection direction (proved).** On the closure tail, if marked
arrows `f₁ : M₁ → N₁`, `f₂ : M₂ → N₂` (the `M`s at one level, the `N`s at one larger level) carry
bounded lists `t₁`, `t₂` to lists in the same pair orbit with the marks matched along
`f₁⁻¹ ∘ σ ∘ f₂`, then `t₁`, `t₂` are in the same pair orbit with the marks matched along `σ`.
English (Lemma 8.2 proof): the large pair isomorphism transports the first small approximation
list (with the base entries of `t₁`) into the second large base; a copy is realized inside the
second small base (`infra_82_reflect_realize_single`); small-level homogeneity gives an
isomorphism of the small bases; the approximation list isolates the joint type over the small
base relative to the marks, whose types match (`infra_82_mark_reflect_single`); then the small
pair isomorphism test. -/
theorem infra_82_comparison_reflection_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) (hiso : Pr.CommutesWithIso)
    (hTA : Pr.TiedAlong) :
      ∀ (M₁ M₂ N₁ N₂ : MarkedPair K oneVertexShape P.scheme Pr)
        (f₁ : MarkedArrow K oneVertexShape P.scheme Pr M₁ N₁)
        (f₂ : MarkedArrow K oneVertexShape P.scheme Pr M₂ N₂),
        M₁.μ ∈ infra_615_closed P → M₁.μ = M₂.μ → N₁.μ ∈ infra_615_closed P → N₁.μ = N₂.μ → M₁.μ < N₁.μ →
        ∀ {ι : Type u} (t₁ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M₁.hμ M₁.Y))
          (t₂ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M₂.hμ M₂.Y)), #ι < M₁.μ →
          ∀ σ : M₁.bIdx ≃ M₂.bIdx,
          PairOrbitEq N₁ N₂ (f₁.markMap.symm.trans (σ.trans f₂.markMap))
              (fun i => f₁.onY.mapOcc (t₁ i)) (fun i => f₂.onY.mapOcc (t₂ i)) →
            PairOrbitEq M₁ M₂ σ t₁ t₂ := by
  classical
  intro M₁ M₂ N₁ N₂ f₁ f₂ hM hMM hNT hNN hlt ι t₁ t₂ hι σ hO
  obtain ⟨β, hβσ, -, -, hβt⟩ := hO
  let ι₀ := {i : ι // ∃ x, t₁ i = M₁.incl.mapOcc x}
  let x₀ : ι₀ → Occurrence K oneVertexShape (P.scheme.asSystem M₁.hμ M₁.X) :=
    fun i => i.2.choose
  have hx₀ : ∀ i : ι₀, t₁ i.1 = M₁.incl.mapOcc (x₀ i) := fun i => i.2.choose_spec
  obtain ⟨γ, Z, hγ, HZ⟩ := M₁.dominated ι t₁ hι
  let L₁ : γ ⊕ ι₀ → Occurrence K oneVertexShape (P.scheme.asSystem M₁.hμ M₁.X) :=
    Sum.elim Z x₀
  have hfinB : Finite M₁.bIdx :=
    Finite.of_equiv _ (M₁.realEq.trans (Pr.arity M₁.hμ M₁.X)).symm
  have hμ0 : ℵ₀ < M₁.μ := P.aleph0_lt M₁.hμ
  have hBlt : #M₁.bIdx < M₁.μ := (Cardinal.lt_aleph0_of_finite M₁.bIdx).trans hμ0
  have hι₀ : #ι₀ < M₁.μ := (Cardinal.mk_subtype_le _).trans_lt hι
  have hδ : #(γ ⊕ ι₀) < M₁.μ := by
    simp only [mk_sum, lift_id]
    exact add_lt_of_lt (P.aleph0_le M₁.hμ) hγ hι₀
  have hbι : #(M₁.bIdx ⊕ ι) < M₁.μ := by
    simp only [mk_sum, lift_id]
    exact add_lt_of_lt (P.aleph0_le M₁.hμ) hBlt hι
  have hb : #((M₁.bIdx ⊕ ι) ⊕ (γ ⊕ ι₀)) < M₁.μ := by
    have h2 : #((M₁.bIdx ⊕ ι) ⊕ (γ ⊕ ι₀)) = #(M₁.bIdx ⊕ ι) + #(γ ⊕ ι₀) := by
      simp only [mk_sum, lift_id]
    rw [h2]
    exact add_lt_of_lt (P.aleph0_le M₁.hμ) hbι hδ
  have hM₂ : M₂.μ ∈ infra_615_closed P := hMM ▸ hM
  have hN₂ : N₂.μ ∈ infra_615_closed P := hNN ▸ hNT
  have hlev₂ : M₂.μ ≤ N₂.μ := hMM ▸ hNN ▸ hlt.le
  have hMrec0 : M₁.μ ∈ recursionClosedLevels P ℵ₀ :=
    ⟨hM.1, fun β₀ hβ => hM.2 ℵ₀ le_rfl hμ0 β₀ hβ⟩
  have hNrec0 : N₁.μ ∈ recursionClosedLevels P ℵ₀ :=
    ⟨hNT.1, fun β₀ hβ => hNT.2 ℵ₀ le_rfl (hμ0.trans hlt) β₀ hβ⟩
  obtain ⟨V, DR⟩ := infra_82_reflect_realize_single hiso hTA f₂ hM₂ hN₂ hlev₂ t₂ (hMM ▸ hι)
    (fun j => β.onX.mapOcc (f₁.onX.mapOcc (L₁ j))) (hMM ▸ hδ)
  have hcomm : ∀ {A B : MarkedPair K oneVertexShape P.scheme Pr}
      (g : MarkedArrow K oneVertexShape P.scheme Pr A B)
      (x : Occurrence K oneVertexShape (P.scheme.asSystem A.hμ A.X)),
      g.onY.mapOcc (A.incl.mapOcc x) = B.incl.mapOcc (g.onX.mapOcc x) := fun g x =>
    congrArg (Sigma.mk x.1) (congrArg (fun h => SystemArrow.onVertex h x.1 x.2) g.comm)
  have hbN : #((M₁.bIdx ⊕ ι) ⊕ (γ ⊕ ι₀)) < N₂.μ := hNN ▸ hb.trans hlt
  have dU := P.scheme.diagram_preserved M₁.Y N₂.Y (SystemArrow.comp f₁.onY β.onY) trivial
    (seqJoint (seqJoint M₁.b t₁) (fun j => M₁.incl.mapOcc (L₁ j))) hb hbN
  have dU' := infra_73_diagramEq_of_eq dU (fun _ => rfl)
    (ys' := seqJoint (seqJoint (fun k => N₂.b (f₂.markMap (σ k)))
      (fun i => f₂.onY.mapOcc (t₂ i)))
      (fun j => N₂.incl.mapOcc (β.onX.mapOcc (f₁.onX.mapOcc (L₁ j)))))
    (fun x => by
      rcases x with (k | i) | j
      · have h1 : β.onY.mapOcc (f₁.onY.mapOcc (M₁.b k)) =
            N₂.b (β.markMap (f₁.markMap k)) :=
          (congrArg β.onY.mapOcc (f₁.preserves_mark k)).trans (β.preserves_mark _)
        have hm : β.markMap (f₁.markMap k) = f₂.markMap (σ k) := by rw [hβσ]; simp
        rw [hm] at h1
        exact h1
      · exact hβt i
      · exact (congrArg β.onY.mapOcc (hcomm f₁ (L₁ j))).trans (hcomm β _))
  let ε : (M₂.bIdx ⊕ ι) ⊕ (γ ⊕ ι₀) ≃ (M₁.bIdx ⊕ ι) ⊕ (γ ⊕ ι₀) :=
    Equiv.sumCongr (Equiv.sumCongr σ.symm (Equiv.refl ι)) (Equiv.refl _)
  have DR1 := (P.scheme.diagram_reindex M₂.Y N₂.Y ε _ _).mp DR
  have DR' := infra_73_diagramEq_of_eq DR1
    (xs' := seqJoint (seqJoint (fun k => M₂.b (σ k)) t₂) (fun j => M₂.incl.mapOcc (V j)))
    (ys' := seqJoint (seqJoint (fun k => N₂.b (f₂.markMap (σ k)))
      (fun i => f₂.onY.mapOcc (t₂ i)))
      (fun j => N₂.incl.mapOcc (β.onX.mapOcc (f₁.onX.mapOcc (L₁ j)))))
    (fun x => by rcases x with (k | i) | j <;> simp [ε, seqJoint])
    (fun x => by rcases x with (k | i) | j <;> simp [ε, seqJoint])
  have Dfull := P.scheme.diagram_trans _ _ _ _ _ _ dU' (P.scheme.diagram_symm _ _ _ _ DR')
  -- base level
  have DE := infra_73_diagramEq_of_eq Dfull
    (xs' := Sum.elim (seqJoint M₁.b t₁) (fun j => M₁.incl.mapOcc (L₁ j)))
    (ys' := Sum.elim (seqJoint (fun k => M₂.b (σ k)) t₂) (fun j => M₂.incl.mapOcc (V j)))
    (fun x => by rcases x with x | j <;> rfl) (fun x => by rcases x with x | j <;> rfl)
  have DI := (P.scheme.diagram_restrict _ _ _ _ _ _ DE).2
  have hδ₂ : #(γ ⊕ ι₀) < M₂.μ := hMM ▸ hδ
  have dX := P.scheme.diagram_trans _ _ _ _ _ _
    (P.scheme.diagram_preserved M₁.X M₁.Y M₁.incl M₁.incl_arrow L₁ hδ hδ)
    (P.scheme.diagram_trans _ _ _ _ _ _ DI
      (P.scheme.diagram_symm _ _ _ _
        (P.scheme.diagram_preserved M₂.X M₂.Y M₂.incl M₂.incl_arrow V hδ₂ hδ₂)))
  obtain ⟨e, hbij, heP, he⟩ := infra_82_diagram_iso_cross hMM M₁.X M₂.X L₁ V hδ dX
  refine (fun H => ?_) (infra_82_pointed_all P Pr M₁ M₂ e hbij heP σ t₁ t₂ hι)
  have hbase : ∀ i (x : Occurrence K oneVertexShape (P.scheme.asSystem M₁.hμ M₁.X)),
      t₁ i = M₁.incl.mapOcc x → t₂ i = M₂.incl.mapOcc (e.mapOcc x) := by
    intro i x hx
    let i' : ι₀ := ⟨i, x, hx⟩
    have hxx : x₀ i' = x :=
      infra_82_mapOcc_injective M₁.incl ((hx₀ i').symm.trans hx)
    have hq := infra_82_diag_eq_transfer hMM hb Dfull (Sum.inl (Sum.inr i))
      (Sum.inr (Sum.inr i')) (hx₀ i')
    have hV : V (Sum.inr i') = e.mapOcc x := by rw [he, ← hxx]; rfl
    change t₂ i = M₂.incl.mapOcc (V (Sum.inr i')) at hq
    rw [hq, hV]
  -- isolation over the small base
  let q' : TupleOver K oneVertexShape P.scheme M₁.hμ M₁.X :=
    ⟨M₂.μ, M₂.hμ, M₂.Y, SystemArrow.comp e M₂.incl, trivial, M₁.bIdx ⊕ ι,
      seqJoint (fun k => M₂.b (σ k)) t₂⟩
  have hmk := infra_82_mark_reflect_single hiso hTA f₁ f₂ β σ hβσ hMM hNN hlt.le hMrec0 hNrec0
    e hbij
  have hmarg : SameGaloisType
      ((asTuple M₁.incl M₁.incl_arrow (seqJoint M₁.b t₁)).marginal (Equiv.refl _))
      (q'.marginal (Equiv.refl _)) (Equiv.refl _) (Equiv.refl _) := by
    rcases hmk with ⟨ρ, hρ, top, g1, g2, h1, h2, hc, hv⟩
    exact ⟨ρ, hρ, top, g1, g2, h1, h2, hc, fun k => hv k⟩
  let ε2 : ((M₁.bIdx ⊕ ι) ⊕ γ) ⊕ ι₀ ≃ (M₁.bIdx ⊕ ι) ⊕ (γ ⊕ ι₀) := Equiv.sumAssoc _ _ _
  have D2 := (P.scheme.diagram_reindex M₁.Y M₂.Y ε2.symm _ _).mp Dfull
  have D3 := infra_73_diagramEq_of_eq D2
    (xs' := Sum.elim (seqJoint (seqJoint M₁.b t₁) (fun j => M₁.incl.mapOcc (Z j)))
      (fun j => M₁.incl.mapOcc (x₀ j)))
    (ys' := Sum.elim (seqJoint (seqJoint (fun k => M₂.b (σ k)) t₂)
      (fun j => M₂.incl.mapOcc (V (Sum.inl j)))) (fun j => M₂.incl.mapOcc (V (Sum.inr j))))
    (fun x => by rcases x with ((k | i) | j) | j <;> rfl)
    (fun x => by rcases x with ((k | i) | j) | j <;> rfl)
  have D4 := (P.scheme.diagram_restrict _ _ _ _ _ _ D3).1
  have hdiag : P.scheme.DiagramEq (X := M₁.Y) (Y := q'.host)
      (alignJoint (Equiv.refl _)
        (typeJoint (p := asTuple M₁.incl M₁.incl_arrow (seqJoint M₁.b t₁)) Z))
      (alignJoint (Equiv.refl _) (typeJoint (p := q') Z)) := by
    refine infra_73_diagramEq_of_eq D4 ?_ ?_
    · intro x; rcases x with (k | i) | j <;> rfl
    · intro x
      rcases x with (k | i) | j
      · rfl
      · rfl
      · change M₂.incl.mapOcc (V (Sum.inl j)) = M₂.incl.mapOcc (e.mapOcc (Z j))
        rw [he]
        rfl
  have R := (⟨hγ, HZ⟩ : IsIsolatingFragment
    (asTuple M₁.incl M₁.incl_arrow (seqJoint M₁.b t₁)) (Equiv.refl _) Z).2 q' (Equiv.refl _)
    hMM.symm hmarg hdiag
  have hsgt : SameGaloisType (asTuple M₁.incl M₁.incl_arrow (Sum.elim t₁ M₁.b))
      (markedJointOver M₁ M₂ e heP σ t₂) (Equiv.refl _) (Equiv.refl _) := by
    rcases R with ⟨ρ, hρ, top, g1, g2, h1, h2, hc, hv⟩
    refine ⟨ρ, hρ, top, g1, g2, h1, h2, hc, fun x => ?_⟩
    rcases x with i | k
    · exact hv (Sum.inr i)
    · exact hv (Sum.inl k)
  obtain ⟨arr, hX, hσ', hY, hmap⟩ := H.mpr ⟨hbase, hsgt⟩
  exact ⟨arr, hσ', fun v => by rw [hX]; exact hbij v, hY, hmap⟩

/-- **Lemma 8.2(5) for P.scheme (proved).** English: "comparisons of bounded pair tuples are
preserved and reflected when two pairs at one common small level are mapped to two pairs at a
common larger eligible level. All tuple lengths and the bounds needed for the comparison are
strictly below the smaller level." For a Definition 8.1 prescription (commutes with isomorphisms;
tied free extension along arrows), on the tail `infra_615_closed`. -/
theorem infra_82_comparison_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) (hiso : Pr.CommutesWithIso)
    (hTA : Pr.TiedAlong) :
    ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∀ (M₁ M₂ N₁ N₂ : MarkedPair K oneVertexShape P.scheme Pr)
        (f₁ : MarkedArrow K oneVertexShape P.scheme Pr M₁ N₁)
        (f₂ : MarkedArrow K oneVertexShape P.scheme Pr M₂ N₂),
        M₁.μ ∈ T → M₁.μ = M₂.μ → N₁.μ ∈ T → N₁.μ = N₂.μ → M₁.μ < N₁.μ →
        ∀ {ι : Type u} (t₁ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M₁.hμ M₁.Y))
          (t₂ : ι → Occurrence K oneVertexShape (P.scheme.asSystem M₂.hμ M₂.Y)), #ι < M₁.μ →
          ∀ σ : M₁.bIdx ≃ M₂.bIdx,
          (PairOrbitEq M₁ M₂ σ t₁ t₂ ↔
            PairOrbitEq N₁ N₂ (f₁.markMap.symm.trans (σ.trans f₂.markMap))
              (fun i => f₁.onY.mapOcc (t₁ i)) (fun i => f₂.onY.mapOcc (t₂ i))) :=
  ⟨infra_615_closed P, infra_615_tail P,
    fun M₁ M₂ N₁ N₂ f₁ f₂ hM hMM hN hNN hlt _ t₁ t₂ hι σ =>
      ⟨infra_82_comparison_preservation_single P Pr hiso hTA M₁ M₂ N₁ N₂ f₁ f₂ hM hMM hN hNN
        hlt t₁ t₂ hι σ,
       infra_82_comparison_reflection_single P Pr hiso hTA M₁ M₂ N₁ N₂ f₁ f₂ hM hMM hN hNN
        hlt t₁ t₂ hι σ⟩⟩

end
end AEC
