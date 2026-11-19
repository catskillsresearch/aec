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

end
end AEC
