module

public import AEC.Section8.Lemma83Samples
public import AEC.Section8.LSNested83

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: LS-expanded samples

The large order-saturated samples `X = F(J) ≤ Y ≤ L = F(J⁺)` of `infra_83_large_saturated_samples`,
with `L` expanded by the vertex LS witnesses (`LS83.exists_chain_ls_expansion`): the expansion has
`τ(K)`-reduct `L`, every nonempty closed subset of `L` is strong, and the universes of `X` (the
image of `F(J)`) and of `Y` are closed under all functions of the expanded language.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **LS-expanded large samples** (Lemma 8.3, "The samples and their language", vertex LS
witnesses).  For every infinite `κ` and every bound `θ` there are a level `μ ≥ θ`, `μ > κ`, of the
tail, a dense `κ`-order-saturated order `J` of size `μ` (with a well-ordered subset of size `μ`),
a marked pair `X ≤ Y` with `X ≅ F(J)`, and a strong embedding of `Y` into `L = F(J⁺)` over `F(J)`,
together with an expansion of `L` by `LS(K)`-many witness functions of each positive arity
(`LS83.lsLang K`) whose `τ(K)`-reduct is `L`, all of whose nonempty substructures have strong
reduct, and in which the images of `X` and of `Y` are closed under every function. -/
theorem infra_83_ls_expanded_samples (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (θ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, θ ≤ μ ∧ κ < μ ∧ μ ∈ infra_78_closedTail P ∩ infra_615_closed P ∧
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J), OrderSat83.OrderSaturated κ J ∧
      DenselyOrdered J ∧ #J = μ ∧ (∃ S : Set J, #S = μ ∧ S.WellFoundedOn (· < ·)) ∧
    ∃ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ = μ ∧
      ∃ eX : Language.Embedding K.τ (P.E.obj J).carrier
          ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier,
        Function.Bijective eX ∧ K.Strong eX ∧
        (∀ (Z : Type u) [LinearOrder Z] [Nonempty Z], #Z = μ →
          Nonempty ((P.E.obj Z).carrier ≃[K.τ]
            ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier)) ∧
        ∃ (Jplus : Type u) (_ : LinearOrder Jplus) (_ : Nonempty Jplus) (emb : J ↪o Jplus)
          (strip : Set Jplus) (V : ℕ → Set Jplus),
          #Jplus = μ ∧ IsConvexRegion strip ∧ #strip = μ ∧
          (∀ n, IsConvexRegion (V n) ∧ #(V n) = μ ∧ V n ⊆ strip) ∧
          Pairwise (Function.onFun Disjoint V) ∧
          ∃ F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
              (P.E.obj Jplus).carrier,
            K.Strong F ∧ (∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x) ∧
            ∃ str : (LS83.lsLang K).Structure (P.E.obj Jplus).carrier,
              @Language.LHom.reduct _ _ (LS83.lsInl K) _ str = (P.E.obj Jplus).str ∧
              @LS83.LSClosed K _ str ∧
              (∀ {n} (f : (LS83.lsLang K).Functions n) (x : Fin n → (P.E.obj Jplus).carrier),
                (∀ i, x i ∈ Set.range (P.E.map emb)) →
                  @Language.Structure.funMap _ _ str n f x ∈ Set.range (P.E.map emb)) ∧
              (∀ {n} (f : (LS83.lsLang K).Functions n) (x : Fin n → (P.E.obj Jplus).carrier),
                (∀ i, x i ∈ Set.range F) →
                  @Language.Structure.funMap _ _ str n f x ∈ Set.range F) := by
  obtain ⟨μ, h1, h2, h3, J, i1, i2, h4, h5, h6, h7, M, h8, eX, h9, sX, h10, Jplus, i3, i4, emb,
    strip, V, h11, h12, h13, h14, h15, F, sF, hF⟩ := infra_83_large_saturated_samples P Pr hκ θ
  have hL : K.Mem (P.E.obj Jplus) := P.hE Jplus
  have hY : K.Mem ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit) :=
    (P.scheme.asSystem M.hμ M.Y).inK PUnit.unit
  let jX := F.comp ((M.incl.onVertex PUnit.unit).comp eX)
  have sjX : K.Strong jX :=
    K.strong_trans _ _ (K.strong_trans _ _ sX (M.incl.onVertex_strong PUnit.unit)) sF
  have hjX : ⇑jX = ⇑(P.E.map emb) := funext fun x => hF x
  have hXY : Set.range jX ⊆ Set.range F := by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨str, hred, hcl, hX', hY'⟩ :=
    LS83.exists_chain_ls_expansion hL (P.hE J) hY jX F sjX sF hXY
  refine ⟨μ, h1, h2, h3, J, i1, i2, h4, h5, h6, h7, M, h8, eX, h9, sX, h10, Jplus, i3, i4, emb,
    strip, V, h11, h12, h13, h14, h15, F, sF, hF, str, hred, hcl, ?_, hY'⟩
  intro n f x hx
  rw [← hjX] at hx ⊢
  exact hX' f x hx

end AEC
