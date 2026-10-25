module

public import AEC.Section13.Adequacy
public import AEC.Section13.CommonMajorant
public import AEC.Section5.LevelHierarchy
public import AEC.Section5.EligibleSubclass

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open Cardinal

/-- **Proposition 13.1** (Uniform finite-depth definitions). There is a set of descriptors and
one adequacy predicate which, at eligible levels, defines the objects, arrows, and package
assertions used in either finite-depth application. -/
theorem proposition_13_1 (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) :
    ∃ A : Adequacy, ∃ d : SchemeDescriptor,
      ∀ μ : Cardinal.{u}, Adeq A d μ ↔ μ ∈ GOmega Φ := by
  sorry

/-- **Lemma 13.2** (The mixed-level interface). If the individual adequacy conditions hold on
a class `S` of levels, the mixed presentation, coherence, Löwenheim–Skolem, diagram,
saturation, and map conditions used above hold on `S`. -/
theorem lemma_13_2 (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u})
    (A : Adequacy) (d : SchemeDescriptor) (S : Set Cardinal.{u})
    (hchar : ∀ μ : Cardinal.{u}, Adeq A d μ ↔ μ ∈ GOmega Φ)
    (hS : ∀ μ ∈ S, Adeq A d μ) :
    ∀ μ ∈ S, IsWorkingLevel μ ∧ PhiClosed Φ μ := by
  sorry

/-- **Lemma 13.3** (Uniform bound register). Every bound request arising in one application of
the one-dimensional tools, one marked-increment step, or one geometric step has an ordinal
totalization. -/
theorem lemma_13_3 (request : _root_.Ordinal.{u} → Set _root_.Ordinal.{u}) :
    ∃ value : _root_.Ordinal.{u} → _root_.Ordinal.{u}, IsTotalization request value := by
  sorry

/-- **Lemma 13.4** (Closure and absorption). Each `Gⱼ` is unbounded and closed under strictly
increasing countable suprema, and `G_ω` is unbounded. Those two closure properties are what
let a finite sequence of bound-closures of a class containing `Gⱼ` retain some later `G_{j+m}`. -/
theorem lemma_13_4 (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (j : ℕ) :
    (∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ G Φ j) ∧
    CountablySupClosed (G Φ j) ∧
    ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ GOmega Φ := by
  sorry

/-- **Theorem 13.5** (Common levels for all finite depths). There is an unbounded class of
countable-cofinality strong limits at which every finite-depth conclusion of either
application holds, and one such level may be chosen above any specified threshold. -/
theorem theorem_13_5 (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (κ : Cardinal.{u}) :
    ∃ μ, κ ≤ μ ∧ μ ∈ GOmega Φ ∧ IsWorkingLevel μ := by
  sorry

end
end AEC
