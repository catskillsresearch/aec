module

public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace AEC
section

universe u

/-- `x` independently extends `S` when it lies outside `S` and `S ∪ {x}` is independent. -/
def IndependentlyExtends {α : Type u} (indep : Set α → Prop) (x : α) (S : Set α) : Prop :=
  x ∉ S ∧ indep (insert x S)

/-- `S` is a maximal independent subset of `F`. -/
def MaximallyIndependent {α : Type u} (indep : Set α → Prop) (F S : Set α) : Prop :=
  S ⊆ F ∧ indep S ∧ ∀ y ∈ F, ¬ IndependentlyExtends indep y S

/-- **Theorem 10.5.** For finite `F`, `x ∈ cl(F)` when `x` does not independently extend some
maximal independent subset of `F`. -/
def InFiniteClosure {α : Type u} (indep : Set α → Prop) (F : Set α) (x : α) : Prop :=
  ∃ S : Set α, MaximallyIndependent indep F S ∧ ¬ IndependentlyExtends indep x S

/-- Closure of an arbitrary set is the union of the closures of its finite subsets. -/
def InClosure {α : Type u} (indep : Set α → Prop) (A : Set α) (x : α) : Prop :=
  ∃ F : Set α, F ⊆ A ∧ F.Finite ∧ InFiniteClosure indep F x

theorem InClosure.mono {α : Type u} {indep : Set α → Prop} {A B : Set α} {x : α}
    (hAB : A ⊆ B) (hx : InClosure indep A x) : InClosure indep B x := by
  obtain ⟨F, hFA, hFin, hF⟩ := hx
  exact ⟨F, hFA.trans hAB, hFin, hF⟩

theorem IndependentlyExtends.image {α β : Type u} (f : α → β) (hf : Function.Injective f)
    {indepA : Set α → Prop} {indepB : Set β → Prop}
    (hpres : ∀ S : Set α, indepA S ↔ indepB (f '' S)) {x : α} {S : Set α} :
    IndependentlyExtends indepA x S ↔
      IndependentlyExtends indepB (f x) (f '' S) := by
  constructor
  · intro ⟨hx, hI⟩
    refine ⟨?_, ?_⟩
    · intro ⟨y, hyS, hyx⟩
      exact hx (hf hyx ▸ hyS)
    · rw [← Set.image_insert_eq]
      exact (hpres _).mp hI
  · intro ⟨hx, hI⟩
    refine ⟨fun hxS => hx ⟨x, hxS, rfl⟩, ?_⟩
    rw [← Set.image_insert_eq] at hI
    exact (hpres _).mpr hI

theorem MaximallyIndependent.image {α β : Type u} (f : α → β) (hf : Function.Injective f)
    {indepA : Set α → Prop} {indepB : Set β → Prop}
    (hpres : ∀ S : Set α, indepA S ↔ indepB (f '' S)) {F S : Set α} :
    MaximallyIndependent indepA F S ↔
      MaximallyIndependent indepB (f '' F) (f '' S) := by
  constructor
  · intro ⟨hSF, hI, hmax⟩
    refine ⟨Set.image_mono hSF, (hpres S).mp hI, ?_⟩
    intro y hy
    obtain ⟨x, hxF, rfl⟩ := hy
    exact (IndependentlyExtends.image f hf hpres).not.mp (hmax x hxF)
  · intro ⟨hSF, hI, hmax⟩
    refine ⟨(Set.image_subset_image_iff hf).mp hSF, (hpres S).mpr hI, ?_⟩
    intro y hyF
    exact (IndependentlyExtends.image f hf hpres).not.mpr
      (hmax (f y) ⟨y, hyF, rfl⟩)

theorem InFiniteClosure.image {α β : Type u} (f : α → β) (hf : Function.Injective f)
    {indepA : Set α → Prop} {indepB : Set β → Prop}
    (hpres : ∀ S : Set α, indepA S ↔ indepB (f '' S)) {F : Set α} {x : α}
    (hx : InFiniteClosure indepA F x) :
    InFiniteClosure indepB (f '' F) (f x) := by
  obtain ⟨S, hS, hxS⟩ := hx
  refine ⟨f '' S, (MaximallyIndependent.image f hf hpres).mp hS, ?_⟩
  exact (IndependentlyExtends.image f hf hpres).not.mp hxS

theorem InClosure.image {α β : Type u} (f : α → β) (hf : Function.Injective f)
    {indepA : Set α → Prop} {indepB : Set β → Prop}
    (hpres : ∀ S : Set α, indepA S ↔ indepB (f '' S)) {A : Set α} {x : α}
    (hx : InClosure indepA A x) :
    InClosure indepB (f '' A) (f x) := by
  obtain ⟨F, hFA, hFin, hF⟩ := hx
  refine ⟨f '' F, Set.image_mono hFA, hFin.image f, InFiniteClosure.image f hf hpres hF⟩

end
end AEC
