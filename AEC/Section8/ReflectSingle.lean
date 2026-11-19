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

end
end AEC
