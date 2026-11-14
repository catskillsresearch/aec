module

public import AEC.Section6.ApproximationSequence

@[expose] public section

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}

/-- Reindex a joint list along an identification of the tuple coordinates. -/
def alignJoint {idx idx' ι : Type u} {X : SystemObject K S} (e : idx ≃ idx')
    (xs : idx ⊕ ι → Occurrence K S X) : idx' ⊕ ι → Occurrence K S X
  | Sum.inl i => xs (Sum.inl (e.symm i))
  | Sum.inr j => xs (Sum.inr j)

/-- The marginal of a concatenated tuple on the first summand. -/
def TupleOver.marginal {uIdx cIdx : Type u} (q : TupleOver K S W hμ base)
    (e : q.idx ≃ uIdx ⊕ cIdx) : TupleOver K S W hμ base where
  ν := q.ν
  hν := q.hν
  host := q.host
  incl := q.incl
  incl_arrow := q.incl_arrow
  idx := uIdx
  val i := q.val (e.symm (Sum.inl i))

/-- Coordinate map keeping `u` and `c₀` from a three-way split. -/
def projectUC0ρ {uIdx c0Idx c1Idx idx : Type u}
    (e : idx ≃ uIdx ⊕ (c0Idx ⊕ c1Idx)) : uIdx ⊕ c0Idx → idx
  | Sum.inl i => e.symm (Sum.inl i)
  | Sum.inr j => e.symm (Sum.inr (Sum.inl j))

theorem projectUC0ρ_injective {uIdx c0Idx c1Idx idx : Type u}
    (e : idx ≃ uIdx ⊕ (c0Idx ⊕ c1Idx)) :
    Function.Injective (projectUC0ρ e) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl i' =>
      have := congrArg e hxy
      simp only [projectUC0ρ, Equiv.apply_symm_apply] at this
      exact congrArg Sum.inl (Sum.inl.inj this)
    | inr j =>
      have := congrArg e hxy
      simp only [projectUC0ρ, Equiv.apply_symm_apply] at this
      cases this
  | inr j =>
    cases y with
    | inl i =>
      have := congrArg e hxy
      simp only [projectUC0ρ, Equiv.apply_symm_apply] at this
      cases this
    | inr j' =>
      have := congrArg e hxy
      simp only [projectUC0ρ, Equiv.apply_symm_apply] at this
      exact congrArg Sum.inr (Sum.inl.inj (Sum.inr.inj this))

/-- Projection of `tp(u, c₀, c₁/A)` onto `tp(u, c₀/A)`. -/
def TupleOver.projectUC0 {uIdx c0Idx c1Idx : Type u} (q : TupleOver K S W hμ base)
    (e : q.idx ≃ uIdx ⊕ (c0Idx ⊕ c1Idx)) : TupleOver K S W hμ base :=
  q.reindex (projectUC0ρ e)

/-- Flat decomposition used when stating relative isolation of a three-way joint. -/
def flatUC {uIdx c0Idx c1Idx : Type u} :
    uIdx ⊕ (c0Idx ⊕ c1Idx) ≃ uIdx ⊕ (c0Idx ⊕ c1Idx) :=
  Equiv.refl _

/-- Decomposition of the projected tuple as `u ⊕ c₀`. -/
def projectDecomp {uIdx c0Idx : Type u} : uIdx ⊕ c0Idx ≃ uIdx ⊕ c0Idx :=
  Equiv.refl _

/-- The `u`-marginal of a three-way joint agrees with the `u`-marginal of its `(u,c₀)` projection. -/
theorem marginal_projectUC0 {uIdx c0Idx c1Idx : Type u}
    (q : TupleOver K S W hμ base) (e : q.idx ≃ uIdx ⊕ (c0Idx ⊕ c1Idx)) :
    (q.projectUC0 e).marginal (projectDecomp (uIdx := uIdx) (c0Idx := c0Idx)) =
      q.marginal e := by
  cases q
  rfl

/-- **Definition 7.1.** `q = tp(u, c/A)` is isolated relative to `u` when some bounded
`Z ⊆ A` isolates it: any same-level `q'` with the same marginal on `u` and the same diagram
over `Z` equals `q`. The set `Z` is an isolating fragment.

Path A packaging: displayed types sit at one eligible level (`q'.ν = μ`), matching the
convention of Section 6 (`p.ν = μ`) and the English “one eligible level” rule. -/
def IsRelativelyIsolated (q : TupleOver K S W hμ base) {uIdx cIdx : Type u}
    (e : q.idx ≃ uIdx ⊕ cIdx) : Prop :=
  ∃ (ι : Type u) (Z : ι → Occurrence K S (W.asSystem hμ base)),
    #ι < μ ∧
    ∀ (q' : TupleOver K S W hμ base) (e' : q'.idx ≃ uIdx ⊕ cIdx),
      q'.ν = μ →
      SameGaloisType (q.marginal e) (q'.marginal e') (Equiv.refl uIdx) (Equiv.refl uIdx) →
      W.DiagramEq (X := q.host) (Y := q'.host)
        (alignJoint e (typeJoint (p := q) Z)) (alignJoint e' (typeJoint (p := q') Z)) →
      SameGaloisType q q' e e'

/-- A parameter enumeration witnessing relative isolation. -/
def IsIsolatingFragment (q : TupleOver K S W hμ base) {uIdx cIdx : Type u}
    (e : q.idx ≃ uIdx ⊕ cIdx) {ι : Type u}
    (Z : ι → Occurrence K S (W.asSystem hμ base)) : Prop :=
  #ι < μ ∧
    ∀ (q' : TupleOver K S W hμ base) (e' : q'.idx ≃ uIdx ⊕ cIdx),
      q'.ν = μ →
      SameGaloisType (q.marginal e) (q'.marginal e') (Equiv.refl uIdx) (Equiv.refl uIdx) →
      W.DiagramEq (X := q.host) (Y := q'.host)
        (alignJoint e (typeJoint (p := q) Z)) (alignJoint e' (typeJoint (p := q') Z)) →
      SameGaloisType q q' e e'

theorem IsRelativelyIsolated.of_fragment {q : TupleOver K S W hμ base}
    {uIdx cIdx ι : Type u} {e : q.idx ≃ uIdx ⊕ cIdx}
    {Z : ι → Occurrence K S (W.asSystem hμ base)}
    (h : IsIsolatingFragment q e Z) : IsRelativelyIsolated q e :=
  ⟨ι, Z, h.1, h.2⟩

theorem IsIsolatingFragment.of_relativelyIsolated {q : TupleOver K S W hμ base}
    {uIdx cIdx : Type u} {e : q.idx ≃ uIdx ⊕ cIdx}
    (h : IsRelativelyIsolated q e) :
    ∃ (ι : Type u) (Z : ι → Occurrence K S (W.asSystem hμ base)),
      IsIsolatingFragment q e Z := by
  rcases h with ⟨ι, Z, hι, hfrag⟩
  exact ⟨ι, Z, hι, hfrag⟩

end
end AEC
