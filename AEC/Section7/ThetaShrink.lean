module

public import AEC.Section7.IsolatedStage

@[expose] public section

/-!
# Prop 7.8: the `θ⁺` shrink to a level-`λ` pair `A ≤ U` (`infra_78_theta_shrink`)

Paper (Prop 7.8 proof): at the isolated stage `i`, build increasing level-`λ` pairs
`A_α ≤ U_α` (`α < θ⁺`) inside `R_i, S_i` (requirement 1 for the pairs, requirement 2 for the
approximation copies of an enumeration of `U_α`, placed in `A_{α+1}`), and take unions
`A ≤ U`; then for every `c ⊆ U` with `|c| ≤ θ` the majority characterization gives the tied
free-extension identity `tp(b, c / X_i) = tp(b, c / A)^{fr}_{X_i}` (`IsTiedFreeMixed`).

Cycle 57: `infra_78_theta_union` — the union step: a directed family (at most `λ` indices) of
level-`λ` pairs with compatible arrows into the level-`κ` pair `X_i → Y_i` has a union pair
`A → U` at level `λ`, with legs, arrows `A → X_i`, `U → Y_i` extending the given ones, and the
commuting square (the paper's "common upper bound clause gives `A ≤ U`").
-/

universe u

open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}

section ThetaUnion
variable {P : SingleModelData K}

/-- **`infra_78_theta_union`** (union step of the `θ⁺` shrink). -/
theorem infra_78_theta_union {ℓ κ : Cardinal.{u}} (hℓ : ℓ ∈ P.eligible) (hκ : κ ∈ P.eligible)
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] (hι : #ι ≤ ℓ)
    (A V : ι → P.scheme.Object ℓ hℓ)
    (g : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (A a)) (P.scheme.asSystem hℓ (V a)))
    (sA : ∀ {a b : ι}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (A a)) (P.scheme.asSystem hℓ (A b)))
    (sV : ∀ {a b : ι}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (V a)) (P.scheme.asSystem hℓ (V b)))
    (hAr : ∀ a, sA (le_refl a) = SystemArrow.refl _)
    (hVr : ∀ a, sV (le_refl a) = SystemArrow.refl _)
    (hAt : ∀ {a b c : ι} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sA (h₁.trans h₂) = SystemArrow.comp (sA h₁) (sA h₂))
    (hVt : ∀ {a b c : ι} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sV (h₁.trans h₂) = SystemArrow.comp (sV h₁) (sV h₂))
    (hcomm : ∀ {a b : ι} (h : a ≤ b),
      SystemArrow.comp (g a) (sV h) = SystemArrow.comp (sA h) (g b))
    {X Y : P.scheme.Object κ hκ}
    (pr : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y))
    (iA : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (A a)) (P.scheme.asSystem hκ X))
    (iV : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (V a)) (P.scheme.asSystem hκ Y))
    (hiA : ∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (sA h) (iA b) = iA a)
    (hiV : ∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (sV h) (iV b) = iV a)
    (hsq : ∀ a, SystemArrow.comp (g a) (iV a) = SystemArrow.comp (iA a) pr) :
    ∃ (Au Uu : P.scheme.Object ℓ hℓ)
      (lA : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (A a)) (P.scheme.asSystem hℓ Au))
      (lU : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (V a)) (P.scheme.asSystem hℓ Uu))
      (gu : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ Au) (P.scheme.asSystem hℓ Uu))
      (jA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ Au) (P.scheme.asSystem hκ X))
      (jU : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ Uu) (P.scheme.asSystem hκ Y)),
      P.scheme.permitted (X := Au) (Y := Uu) gu ∧
      P.scheme.permitted (X := Au) (Y := X) jA ∧
      P.scheme.permitted (X := Uu) (Y := Y) jU ∧
      (∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (sA h) (lA b) = lA a) ∧
      (∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (sV h) (lU b) = lU a) ∧
      (∀ a, SystemArrow.comp (g a) (lU a) = SystemArrow.comp (lA a) gu) ∧
      (∀ a, SystemArrow.comp (lA a) jA = iA a) ∧
      (∀ a, SystemArrow.comp (lU a) jU = iV a) ∧
      SystemArrow.comp gu jU = SystemArrow.comp jA pr ∧
      (∀ x : Occurrence K oneVertexShape (P.scheme.asSystem hℓ Au),
        ∃ a, ∃ y : Occurrence K oneVertexShape (P.scheme.asSystem hℓ (A a)), pushOcc (lA a) y = x) ∧
      (∀ x : Occurrence K oneVertexShape (P.scheme.asSystem hℓ Uu),
        ∃ a, ∃ y : Occurrence K oneVertexShape (P.scheme.asSystem hℓ (V a)), pushOcc (lU a) y = x) := by
  obtain ⟨Au, lA, -, hcA, hcovA, hunivA, huniqA⟩ := infra_78_chain_union_kappa hℓ hι A sA hAr hAt
  obtain ⟨Uu, lU, -, hcU, hcovU, hunivU, -⟩ := infra_78_chain_union_kappa hℓ hι V sV hVr hVt
  obtain ⟨gu, hgu, hguc⟩ := hunivA Uu (fun a => SystemArrow.comp (g a) (lU a)) (by
    intro a b h
    rw [← SystemArrow.comp_assoc, ← hcomm h, SystemArrow.comp_assoc, hcU h])
  obtain ⟨jA, hjA, hjAc⟩ := hunivA X iA hiA
  obtain ⟨jU, hjU, hjUc⟩ := hunivU Y iV hiV
  refine ⟨Au, Uu, lA, lU, gu, jA, jU, hgu, hjA, hjU, hcA, hcU, fun a => (hguc a).symm, hjAc, hjUc,
    ?_, hcovA, hcovU⟩
  apply huniqA Y
  intro a
  rw [← SystemArrow.comp_assoc, hguc a, SystemArrow.comp_assoc, hjUc a, hsq a,
    ← SystemArrow.comp_assoc, hjAc a]

end ThetaUnion
end AEC
