module

public import AEC.Section7.MixedDescent

@[expose] public section

/-!
# Tied local character (`infra_78_tied_local_character`)

The untied `IsFreeFrom` is vacuous (`AEC/Audit/FreeFromVacuous.lean`), so Prop 6.13 and the
local-character contradiction of Prop 7.8 are run on tied freeness `IsTiedFree`.

* (c) `infra_78_tiedFree_restrict` (**proved**): tied freeness along `X → A → B` restricts to
  tied freeness along `X → A` of the restriction to `A`.
* (b) base monotonicity and (a) tied local character: open.
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- The tuple coordinates of an approximation sequence are below the level. -/
theorem infra_78_idx_lt_of_seq
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {q : TupleOver K oneVertexShape P.scheme hμ A}
    (seq : ApproximationSequence q) (hκ : seq.τ + ℵ₀ < #seq.κIndex) :
    #q.idx < μ := by
  have hne : Nonempty seq.κIndex := by
    rw [← Cardinal.mk_ne_zero_iff]
    exact (bot_le.trans_lt hκ).ne'
  obtain ⟨k⟩ := hne
  have hle : #q.idx ≤ #(seq.κIndex × q.idx) := by
    rw [← Cardinal.lift_id #q.idx, ← Cardinal.lift_id #(seq.κIndex × q.idx)]
    exact Cardinal.lift_mk_le'.2 ⟨⟨fun j => (k, j), fun a b h => (Prod.mk.inj h).2⟩⟩
  exact hle.trans_lt seq.concat_bounded

/-- **(c) Restriction of tied freeness (proved).** If `q` over `B` is tied free along
`X → A → B` from its restriction to `X`, then its restriction to `A` is tied free along
`X → A` from the same restriction to `X`. A move `Z ↦ Z₀` along `g` pushes along `f` to a
move along `g ≫ f` (`diagram_preserved` for the strong arrow `f`), and the anchored joint of
`q ↾ A` on `Z` is literally the anchored joint of `q` on `f(Z)`. -/
theorem infra_78_tiedFree_restrict
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X A B : P.scheme.Object μ hμ}
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ A))
    (hg : P.scheme.permitted (X := X) (Y := A) g)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (h : IsTiedFree (SystemArrow.comp g f)
      (q.restrict (SystemArrow.comp g f) (P.scheme.comp g f hg hf)) q (Equiv.refl _)) :
    IsTiedFree g ((q.restrict f hf).restrict g hg) (q.restrict f hf) (Equiv.refl _) := by
  intro seq ι Z Z0 hκ hι hιμ hmove
  have hidx : #q.idx < μ :=
    infra_78_idx_lt_of_seq (q := (q.restrict f hf).restrict g hg) seq hκ
  have hsum : #(q.idx ⊕ ι) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hidx hιμ
  let fZ : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) := fun b => pushOcc f (Z b)
  have hmove' : infra_73_isMove (SystemArrow.comp g f) seq fZ Z0 := by
    intro i
    have h1 := hmove i
    let ys := seqJoint
      (fun j => (⟨(seq.family i j).1, g.onVertex (seq.family i j).1 (seq.family i j).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ A))) Z
    have h2 := P.scheme.diagram_preserved A B f hf ys hsum hsum
    have hpush : (fun t => (⟨(ys t).1, f.onVertex (ys t).1 (ys t).2⟩ :
        Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) =
        seqJoint (fun j => (⟨(seq.family i j).1,
          (SystemArrow.comp g f).onVertex (seq.family i j).1 (seq.family i j).2⟩ :
            Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) fZ := by
      funext t
      cases t <;> rfl
    rw [hpush] at h2
    exact P.scheme.diagram_trans _ _ _ _ _ _ h1 h2
  have hres := h seq fZ Z0 hκ hι hιμ hmove'
  exact hres

end
end AEC
