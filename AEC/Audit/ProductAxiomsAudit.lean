module

public import AEC.Audit.NoPairs
public import AEC.Section10.ProductAxioms

@[expose] public section

/-!
# Product clauses of Definition 10.3 (statement audit)

* `setsProduct`: on the AEC of all sets, `p₀` = "a new element", products = duplicate-free lists
  of new elements. It satisfies `MinimalData.ProductAxioms` (`setsProduct_productAxioms`), so the
  axioms are consistent and non-vacuous.
* `noPairs_not_productAxioms`: the `noPairs` counterexample to the old Lemma 10.4 / Theorem 10.5
  violates `ProductAxioms.step`, so it is excluded by the restated hypotheses.
* `setsMinimal_not_productAxioms`: the counterexample to the old Proposition 10.7 (`[a, a]`)
  violates `ProductAxioms.nodup`.
-/

namespace AEC
namespace Audit

universe u

open FirstOrder Cardinal

set_option linter.unusedVariables false

/-- Honest product copies on the AEC of all sets. -/
noncomputable abbrev setsProduct : MinimalData allSetsAEC.{u} :=
  { setsMinimal.{u} with
    productCopies := fun M f l => l.Nodup ∧ ∀ a ∈ l, a ∉ Set.range f
    singleton := fun M f a => by
      constructor
      · rintro ⟨-, h⟩; exact h a (by simp)
      · intro h; exact ⟨List.nodup_singleton a, by simpa using h⟩
    empty := fun _ _ => ⟨List.nodup_nil, by simp⟩ }

theorem setsProduct_productAxioms : setsProduct.{u}.ProductAxioms where
  nodup _ _ _ h := h.1
  perm _ _ xs ys hp h := ⟨hp.nodup_iff.mp h.1, fun a ha => h.2 a (hp.mem_iff.mpr ha)⟩
  sublist _ _ xs ys hs h := ⟨h.1.sublist hs, fun a ha => h.2 a (hs.subset ha)⟩
  map_strong M N f g xs _ _ _ _ := by
    constructor
    · rintro ⟨hn, hr⟩
      refine ⟨(List.nodup_map_iff g.injective).mpr hn, ?_⟩
      intro b hb ⟨y, hy⟩
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
      exact hr a ha ⟨y, g.injective hy⟩
    · rintro ⟨hn, hr⟩
      refine ⟨(List.nodup_map_iff g.injective).mp hn, ?_⟩
      intro a ha ⟨y, hy⟩
      exact hr (g a) (List.mem_map_of_mem ha) ⟨y, by simp [hy]⟩
  step N N' f g xs x _ _ _ _ _ hxs hx hnew := by
    refine ⟨?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨(List.nodup_map_iff g.injective).mpr hxs.1, List.nodup_singleton x, ?_⟩
      intro a ha b hb hab
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
      rw [List.mem_singleton] at hb
      exact hnew c (hab.trans hb)
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
        rintro ⟨y, hy⟩
        exact hxs.2 a ha ⟨y, g.injective hy⟩
      · rw [List.mem_singleton] at hb
        subst hb
        exact hx

/-- `Option natModel`, a model of size `ℵ₀` with one new element over `M₀`. -/
noncomputable def optNat : Model eL.{u} := ⟨Option natModel.{u}.carrier, eStr _⟩

/-- `Option optNat`, one more new element. -/
noncomputable def optOptNat : Model eL.{u} := ⟨Option optNat.{u}.carrier, eStr _⟩

theorem noPairs_not_productAxioms : ¬ noPairs.{u}.ProductAxioms := by
  intro h
  let f := embOf (M := natModel.{u}) (N := optNat.{u}) some (Option.some_injective _)
  let g := embOf (M := optNat.{u}) (N := optOptNat.{u}) some (Option.some_injective _)
  have hxs : noPairs.{u}.productCopies optNat f [none] :=
    Or.inr ⟨none, rfl, by rintro ⟨x, hx⟩; cases hx⟩
  have hreal : noPairs.{u}.realizes optOptNat (g.comp f) none := by
    rintro ⟨x, hx⟩; cases hx
  have := h.step optNat optOptNat f g [none] none trivial trivial trivial trivial
    (card_option card_natModel) hxs hreal (fun y hy => by cases hy)
  rcases this with h0 | ⟨a, ha, -⟩
  · simp at h0
  · have := congrArg List.length ha
    simp only [List.length_append, List.length_map, List.length_singleton] at this
    omega

theorem setsMinimal_not_productAxioms : ¬ setsMinimal.{u}.ProductAxioms := by
  intro h
  have hp : setsMinimal.{u}.productCopies optNat
      (embOf (M := natModel.{u}) (N := optNat.{u}) some (Option.some_injective _))
      [none, none] := Or.inr (Or.inr (le_refl 2))
  have := h.nodup _ _ _ hp
  exact (List.nodup_cons.mp this).1 (List.mem_singleton_self _)

end Audit
end AEC
