module

public import AEC.Audit.AllSets
public import AEC.Section10.Results

@[expose] public section

/-!
# Minimal data on the AEC of all sets (statement audit)

`setsMinimal`: `M₀ = ℕ`, `λ₀ = ℵ₀`, `realizes M f a := a ∉ range f` (the unique nonalgebraic
type), `Δ := True`, and `productCopies` chosen as `[]`, singletons that realize, or any list of
length `≥ 2`. Every `MinimalData` axiom holds; the abstract interface does not tie
`productCopies` to independence.
-/

namespace AEC
namespace Audit

universe u

open FirstOrder Cardinal

set_option linter.deprecated false

/-- `ℕ` as an `eL`-structure. -/
def natModel : Model eL.{u} := ⟨ULift.{u} ℕ, eStr _⟩

theorem card_natModel : Model.card natModel.{u} = ℵ₀ := by
  simp [Model.card, natModel]

theorem card_option {M : Model eL.{u}} (h : Model.card M = ℵ₀) :
    #(Option M.carrier) = ℵ₀ := by
  rw [Cardinal.mk_option]
  rw [show #M.carrier = ℵ₀ from h]
  exact Cardinal.add_one_of_aleph0_le le_rfl

/-- The amalgam carrier for `unique_ext`. -/
abbrev amalgCarrier {A N1 N2 : Type u} (g2 : A → N2) (a2 : N2) : Type u :=
  N1 ⊕ {y : N2 // (∀ x, g2 x ≠ y) ∧ y ≠ a2}

open Classical in
noncomputable def amalgRight {A N1 N2 : Type u} (g1 : A → N1) (g2 : A → N2) (a1 : N1) (a2 : N2)
    (y : N2) : amalgCarrier (N1 := N1) g2 a2 :=
  if hy : y = a2 then Sum.inl a1
  else if hx : ∃ x, g2 x = y then Sum.inl (g1 (Classical.choose hx))
  else Sum.inr ⟨y, fun x hx' => hx ⟨x, hx'⟩, hy⟩

theorem amalgRight_inj {A N1 N2 : Type u} (g1 : A → N1) (g2 : A → N2) (a1 : N1) (a2 : N2)
    (hg1 : Function.Injective g1) (_hg2 : Function.Injective g2) (hn1 : ∀ b, g1 b ≠ a1) :
    Function.Injective (amalgRight g1 g2 a1 a2) := by
  intro y y' h
  unfold amalgRight at h
  by_cases hy : y = a2 <;> by_cases hy' : y' = a2
  · rw [hy, hy']
  · rw [dif_pos hy, dif_neg hy'] at h
    by_cases hx' : ∃ x, g2 x = y'
    · rw [dif_pos hx'] at h
      exact absurd (Sum.inl_injective h).symm (hn1 _)
    · rw [dif_neg hx'] at h; cases h
  · rw [dif_neg hy, dif_pos hy'] at h
    by_cases hx : ∃ x, g2 x = y
    · rw [dif_pos hx] at h
      exact absurd (Sum.inl_injective h) (hn1 _)
    · rw [dif_neg hx] at h; cases h
  · rw [dif_neg hy, dif_neg hy'] at h
    by_cases hx : ∃ x, g2 x = y <;> by_cases hx' : ∃ x, g2 x = y'
    · rw [dif_pos hx, dif_pos hx'] at h
      rw [← Classical.choose_spec hx, ← Classical.choose_spec hx', hg1 (Sum.inl_injective h)]
    · rw [dif_pos hx, dif_neg hx'] at h; cases h
    · rw [dif_neg hx, dif_pos hx'] at h; cases h
    · rw [dif_neg hx, dif_neg hx'] at h
      exact congrArg Subtype.val (Sum.inr_injective h)

/-- Minimal data on `allSetsAEC`. -/
noncomputable abbrev setsMinimal : MinimalData allSetsAEC.{u} where
  lam0 := ℵ₀
  M0 := natModel
  inM0 := trivial
  card_eq := card_natModel
  realizes M f a := a ∉ Set.range f
  productCopies M f l := l = [] ∨ (∃ a, l = [a] ∧ a ∉ Set.range f) ∨ 2 ≤ l.length
  nonalgebraic a h := h ⟨a, rfl⟩
  singleton M f a := by
    constructor
    · rintro (h | ⟨b, hb, hr⟩ | h)
      · cases h
      · cases hb; exact hr
      · simp at h
    · intro h; exact Or.inr (Or.inl ⟨a, rfl, h⟩)
  empty _ _ := Or.inl rfl
  exists_ext A f _ _ hA := by
    refine ⟨⟨Option A.carrier, eStr _⟩,
      embOf (M := A) (N := ⟨Option A.carrier, eStr _⟩) some (Option.some_injective _), none,
      trivial, trivial, card_option hA, ?_, fun b h => by cases h⟩
    rintro ⟨x, hx⟩
    cases hx
  unique_ext A f N1 N2 g1 g2 a1 a2 _ _ _ _ _ _ _ _ _ hn1 hn2 := by
    classical
    let N : Model eL.{u} := ⟨amalgCarrier (N1 := N1.carrier) g2 a2, eStr _⟩
    refine ⟨N, embOf (M := N1) (N := N) Sum.inl Sum.inl_injective,
      embOf (M := N2) (N := N) (amalgRight g1 g2 a1 a2)
        (amalgRight_inj g1 g2 a1 a2 g1.injective g2.injective hn1), trivial, ?_, fun x => ?_⟩
    · show Sum.inl a1 = amalgRight g1 g2 a1 a2 a2
      unfold amalgRight
      simp
    · show Sum.inl (g1 x) = amalgRight g1 g2 a1 a2 (g2 x)
      have hx : ∃ x', g2 x' = g2 x := ⟨x, rfl⟩
      unfold amalgRight
      rw [dif_neg (hn2 x), dif_pos hx, g2.injective (Classical.choose_spec hx)]
  Delta _ _ := True
  Delta_base := trivial

/-- Points of `setsMinimal` are exactly the elements outside the copy of `M₀`. -/
theorem inPointSet_iff (M : Model eL.{u})
    (incl : Language.Embedding eL.{u} natModel.{u}.carrier M.carrier) (a : M.carrier) :
    InPointSet setsMinimal.{u} M incl a ↔ a ∉ Set.range incl := by
  classical
  constructor
  · rintro ⟨N, f, g, b, -, -, -, -, hgf, hgb, hr⟩ ⟨x, rfl⟩
    apply hr
    refine ⟨x, g.injective ?_⟩
    rw [hgb]
    exact (congrArg (fun e => e x) (congrArg DFunLike.coe hgf))
  · intro ha
    let N : Model eL.{u} := ⟨Option natModel.{u}.carrier, eStr _⟩
    let gf : N.carrier → M.carrier := fun o => o.elim a incl
    have hginj : Function.Injective gf := by
      rintro (_ | x) (_ | y) h
      · rfl
      · exact absurd ⟨y, h.symm⟩ ha
      · exact absurd ⟨x, h⟩ ha
      · exact congrArg some (incl.injective h)
    refine ⟨N, embOf (M := natModel) (N := N) some (Option.some_injective _),
      embOf (M := N) (N := M) gf hginj, none, trivial, trivial, trivial,
      card_option card_natModel, ?_, rfl, ?_⟩
    · exact Language.Embedding.ext fun x => rfl
    · rintro ⟨x, hx⟩
      cases hx

/-- A pointed model over `setsMinimal`. -/
noncomputable def ptd (X : Type u) : PointedModel allSetsAEC.{u} setsMinimal.{u} where
  M := ⟨ULift.{u} ℕ ⊕ X, eStr _⟩
  copy := embOf (M := natModel) (N := ⟨ULift.{u} ℕ ⊕ X, eStr _⟩) Sum.inl Sum.inl_injective
  copy_strong := trivial
  hasDiagram := trivial

/-- Proposition 10.7 as stated is false: `productCopies` (abstract) accepts `[a, a]`, but an
independent list is duplicate-free. -/
theorem proposition_10_7_false :
    ¬ ∀ (K : AbstractElementaryClass.{u}) (D : MinimalData K) (B : PointedModel K D)
      (xs : List B.M.carrier),
      FiniteIndependent D B.M B.copy xs ↔ D.productCopies B.M B.copy xs := by
  intro H
  let B := ptd.{u} PUnit
  have h := (H allSetsAEC setsMinimal B [Sum.inr PUnit.unit, Sum.inr PUnit.unit]).mpr
    (Or.inr (Or.inr le_rfl))
  exact (List.nodup_cons.mp h.nodup).1 (List.mem_singleton_self _)

/-- The shift on `T × ℕ`, identity on the copy of `ℕ`. -/
def shiftFun (T : Type u) : ULift.{u} ℕ ⊕ (T × ULift.{u} ℕ) → ULift.{u} ℕ ⊕ (T × ULift.{u} ℕ)
  | Sum.inl n => Sum.inl n
  | Sum.inr (t, n) => Sum.inr (t, ⟨n.down + 1⟩)

theorem shiftFun_inj (T : Type u) : Function.Injective (shiftFun T) := by
  rintro (n | ⟨t, n⟩) (m | ⟨s, m⟩) h <;> simp [shiftFun] at h
  · rw [h]
  · obtain ⟨rfl, h2⟩ := h
    rw [h2]

theorem shiftFun_not_surj (T : Type u) (t : T) :
    ¬ Function.Surjective (shiftFun T) := by
  intro hs
  obtain ⟨n | ⟨s, m⟩, h⟩ := hs (Sum.inr (t, ⟨0⟩))
  · simp [shiftFun] at h
  · simp [shiftFun] at h

theorem card_shiftModel {lam : Cardinal.{u}} (h : ℵ₀ < lam) :
    #(ULift.{u} ℕ ⊕ (lam.ord.ToType × ULift.{u} ℕ)) = lam := by
  rw [Cardinal.mk_sum, Cardinal.mk_prod, Cardinal.mk_ord_toType]
  simp only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_id, Cardinal.lift_aleph0,
]
  rw [Cardinal.mul_aleph0_eq h.le]
  exact Cardinal.add_eq_right h.le h.le

/-- The original hypothesis of Theorem 10.9 (`x ∈ P(A) ↔ f x ∈ P(B)`) does not force
`P(B) ⊆ f[A]`: at every `λ > ℵ₀` a shift is a counterexample. -/
theorem theorem_10_9_original_false :
    ¬ ∃ lam : Cardinal.{u}, setsMinimal.{u}.lam0 < lam ∧
      ∀ (A B : PointedModel allSetsAEC.{u} setsMinimal.{u})
        (f : Language.Embedding allSetsAEC.{u}.τ A.M.carrier B.M.carrier),
        allSetsAEC.Strong f → f.comp A.copy = B.copy →
        Model.card A.M = lam → Model.card B.M = lam →
        (∀ x, InPointSet setsMinimal A.M A.copy x ↔
          ∃ y, InPointSet setsMinimal B.M B.copy y ∧ f x = y) →
        Function.Surjective f := by
  rintro ⟨lam, hlam, H⟩
  let T := lam.ord.ToType
  have hT : Nonempty T := by
    rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_ord_toType]
    exact (aleph0_pos.trans hlam).ne'
  let A := ptd.{u} (T × ULift.{u} ℕ)
  let f := embOf (M := A.M) (N := A.M) (shiftFun T) (shiftFun_inj T)
  refine shiftFun_not_surj T hT.some (H A A f trivial ?_ (card_shiftModel hlam)
    (card_shiftModel hlam) fun x => ?_)
  · exact Language.Embedding.ext fun n => rfl
  · rw [inPointSet_iff]
    constructor
    · intro hx
      refine ⟨f x, ?_, rfl⟩
      rw [inPointSet_iff]
      rintro ⟨n, hn⟩
      apply hx
      rcases x with m | ⟨t, m⟩
      · exact ⟨m, rfl⟩
      · cases hn
    · rintro ⟨y, hy, rfl⟩ ⟨n, hn⟩
      rw [inPointSet_iff] at hy
      apply hy
      rcases x with m | ⟨t, m⟩
      · exact ⟨m, rfl⟩
      · cases hn

/-- The original first clause of Corollary 10.10 fails for the same reason. -/
theorem corollary_10_10_original_false :
    ¬ ∃ lam : Cardinal.{u}, setsMinimal.{u}.lam0 < lam ∧
      (∀ (A B : PointedModel allSetsAEC.{u} setsMinimal.{u})
        (f : Language.Embedding allSetsAEC.{u}.τ A.M.carrier B.M.carrier),
        allSetsAEC.Strong f → f.comp A.copy = B.copy → lam ≤ Model.card A.M →
        (∀ x, InPointSet setsMinimal A.M A.copy x ↔
          ∃ y, InPointSet setsMinimal B.M B.copy y ∧ f x = y) →
        Function.Bijective f) ∧
      ∀ M : PointedModel allSetsAEC.{u} setsMinimal.{u}, lam < Model.card M.M →
        #{x | InPointSet setsMinimal M.M M.copy x} = Model.card M.M := by
  rintro ⟨lam, hlam, H, -⟩
  exact theorem_10_9_original_false ⟨lam, hlam, fun A B f hf hc hA _ hP =>
    (H A B f hf hc hA.ge hP).2⟩

end Audit
end AEC
