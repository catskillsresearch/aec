module

public import AEC.Section7.Results

@[expose] public section

/-!
# Theorem 7.13, clause (1a) for lists of length at most the level (cycle 90)

`infra_713_unique_short`: at the 7.12 levels, a well-ordered product-independent list of finite
tuples with `|δ| ≤ μ` and total length `≤ μ` has its whole type determined by its marginals among
product-independent lists of finite tuples (any index bijection; the order is transported).
Lemma 7.12 (1) supplies witnessing chains for both lists, Lemma 7.12 (2) identifies the wholes.
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- **Theorem 7.13 (1a), `|δ| ≤ μ` (proved, cycle 90).** -/
theorem infra_713_unique_short (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : P.scheme.Object μ (Tail.mem hT hμ))
        (L L' : TupleList P.scheme (Tail.mem hT hμ) X) [LinearOrder L.δ] [L.FiniteEach]
        [WellFoundedLT L.δ] [L'.FiniteEach] (e : L.δ ≃ L'.δ)
        (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i)),
        #L.δ ≤ μ → #(Σ i, L.indexAt i) ≤ μ →
        ProductIndependentTied L → ProductIndependentTied L' →
        (∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) →
        SameGaloisType L.whole L'.whole (Equiv.sigmaCongr e ei) (Equiv.refl _) := by
  obtain ⟨T, hT, H⟩ := lemma_7_12 P
  refine ⟨T, hT, fun μ hμ X L L' _ _ _ _ e ei hδ hS1 hPI hPI' hm => ?_⟩
  letI : LinearOrder L'.δ := LinearOrder.lift' e.symm e.symm.injective
  let eo : L.δ ≃o L'.δ :=
    { e with
      map_rel_iff' := fun {a b} => by
        show e.symm (e a) ≤ e.symm (e b) ↔ a ≤ b
        simp }
  haveI : WellFoundedLT L'.δ := eo.symm.toOrderEmbedding.wellFoundedLT
  have hδ' : #L'.δ ≤ μ := (Cardinal.mk_congr e).symm.le.trans hδ
  have hS2 : #(Σ i, L'.indexAt i) ≤ μ :=
    (Cardinal.mk_congr (Equiv.sigmaCongr e ei)).symm.le.trans hS1
  obtain ⟨C, -⟩ := (H μ hμ X).1 L hδ hPI
  obtain ⟨C', -⟩ := (H μ hμ X).1 L' hδ' hPI'
  exact (H μ hμ X).2 L L' eo ei hS1 hS2 ⟨C⟩ ⟨C'⟩ hm

end
end AEC
