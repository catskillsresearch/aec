module

public import AEC.Section7.AllDominated
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

/-!
# Prescribed bounded tuple matches (Proposition 7.5, clauses 1–2)

"A prescribed bounded tuple match can be retained whenever its joint type with `b` over `X`
already agrees." The key step: an object all-dominated over `X + b` is all-dominated over
`X + (b, x)` for every bounded `x` from it (relative isolation of `(b, x, c)` relative to `b`
implies relative isolation relative to `(b, x)`).
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible}

/-- All-domination over `X + b` gives all-domination over `X + (b, x)` for bounded `x`. -/
theorem AllDominated.append {X Y : W.Object μ hμ}
    {incl : SystemArrow K S (W.asSystem hμ X) (W.asSystem hμ Y)}
    {hincl : W.permitted (X := X) (Y := Y) incl} {bIdx : Type u}
    {b : bIdx → Occurrence K S (W.asSystem hμ Y)}
    (hAll : AllDominated incl hincl bIdx b) (hμ0 : ℵ₀ ≤ μ) {xIdx : Type u}
    (x : xIdx → Occurrence K S (W.asSystem hμ Y)) (hx : #xIdx < μ) :
    AllDominated incl hincl (bIdx ⊕ xIdx) (seqJoint b x) := by
  intro cIdx c hc
  have hxc : #(xIdx ⊕ cIdx) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hμ0 hx hc
  obtain ⟨ι, Z, hZ, H⟩ := hAll (xIdx ⊕ cIdx) (seqJoint x c) hxc
  refine ⟨ι, Z, hZ, fun q' e' hq'ν hmarg hdiag => ?_⟩
  let A := Equiv.sumAssoc bIdx xIdx cIdx
  have hmarg' : SameGaloisType
      ((asTuple incl hincl (seqJoint b (seqJoint x c))).marginal (Equiv.refl _))
      (q'.marginal (e'.trans A)) (Equiv.refl bIdx) (Equiv.refl bIdx) := by
    obtain ⟨ρ, hρ, top, f1, f2, h1, h2, h3, h4⟩ := hmarg
    exact ⟨ρ, hρ, top, f1, f2, h1, h2, h3, fun i => h4 (Sum.inl i)⟩
  have hdiag' := (W.diagram_reindex _ _ (Equiv.sumCongr A (Equiv.refl ι)) _ _).1 hdiag
  have e1 : (fun k => alignJoint (Equiv.refl _)
      (typeJoint (p := asTuple incl hincl (seqJoint (seqJoint b x) c)) Z)
      ((Equiv.sumCongr A (Equiv.refl ι)).symm k)) =
      alignJoint (Equiv.refl _) (typeJoint (p := asTuple incl hincl (seqJoint b (seqJoint x c))) Z) := by
    funext k
    rcases k with (i | i | i) | k <;> rfl
  have e2 : (fun k => alignJoint e' (typeJoint (p := q') Z)
      ((Equiv.sumCongr A (Equiv.refl ι)).symm k)) =
      alignJoint (e'.trans A) (typeJoint (p := q') Z) := by
    funext k
    rcases k with (i | i | i) | k <;> rfl
  have hdiag'' : W.DiagramEq (X := Y) (Y := q'.host)
      (alignJoint (Equiv.refl _) (typeJoint (p := asTuple incl hincl (seqJoint b (seqJoint x c))) Z))
      (alignJoint (e'.trans A) (typeJoint (p := q') Z)) := by
    have hd2 : W.DiagramEq (X := Y) (Y := q'.host)
        (fun k => alignJoint (Equiv.refl _)
          (typeJoint (p := asTuple incl hincl (seqJoint (seqJoint b x) c)) Z)
          ((Equiv.sumCongr A (Equiv.refl ι)).symm k))
        (fun k => alignJoint e' (typeJoint (p := q') Z)
          ((Equiv.sumCongr A (Equiv.refl ι)).symm k)) := hdiag'
    have tr : ∀ {α : Type u} {xs xs' : α → Occurrence K S (W.asSystem hμ Y)}
        {ys ys' : α → Occurrence K S (W.asSystem q'.hν q'.host)},
        xs = xs' → ys = ys' → W.DiagramEq (X := Y) (Y := q'.host) xs ys →
          W.DiagramEq (X := Y) (Y := q'.host) xs' ys' := by
      intro α xs xs' ys ys' h1 h2 h; subst h1; subst h2; exact h
    exact tr e1 e2 hd2
  obtain ⟨ρ, hρ, top, f1, f2, h1, h2, h3, h4⟩ := H q' (e'.trans A) hq'ν hmarg' hdiag''
  refine ⟨ρ, hρ, top, f1, f2, h1, h2, h3, fun i => ?_⟩
  have := h4 (A i)
  rcases i with (i | i) | i
  · exact this
  · exact this
  · exact this

end
end AEC
