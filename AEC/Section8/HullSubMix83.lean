module

public import AEC.Section8.HullSubBundle83

/-!
# Lemma 8.3: sort maps between hulls in two nested sublanguages

For `χ : L₁ →ᴸ L₂` and `ψ₂ : L₂ →ᴸ L`, the `L₁`-hull of a sub-tuple maps into the `L₂`-hull of
the tuple (`X_H` in the `X`-sort language into `Y_H` in the `Y`-sort language).  For bundled
samples this is a strong natural map of finite pieces.
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {K : AbstractElementaryClass.{u}} {L₁ L₂ L : Language.{u, u}} (χ : L₁ →ᴸ L₂) (ψ₂ : L₂ →ᴸ L)

section Mix

variable {M : Type u} [L.Structure M] {ι ι' : Type} (v : ι → M) (g : ι' → ι)

/-- The `L₁`-hull of `v ∘ g` into the `L₂`-hull of `v`. -/
def mixMap : subHull (ψ₂.comp χ) (v ∘ g) → subHull ψ₂ v :=
  @Quotient.map _ _ (@hullSetoid L₁ M ((ψ₂.comp χ).reduct M) ι' (v ∘ g))
    (@hullSetoid L₂ M (ψ₂.reduct M) ι v) (fun t => (χ.onTerm t).relabel g)
    (fun t t' (htt : @Term.realize L₁ M ((ψ₂.comp χ).reduct M) _ (v ∘ g) t =
        @Term.realize L₁ M ((ψ₂.comp χ).reduct M) _ (v ∘ g) t') => by
      letI := ψ₂.reduct M
      letI := χ.reduct M
      show ((χ.onTerm t).relabel g).realize v = ((χ.onTerm t').relabel g).realize v
      rw [Term.realize_relabel, Term.realize_relabel, LHom.realize_onTerm, LHom.realize_onTerm]
      exact htt)

theorem hullVal_mixMap (x : subHull (ψ₂.comp χ) (v ∘ g)) :
    @hullVal L₂ M (ψ₂.reduct M) ι v (mixMap χ ψ₂ v g x) =
      @hullVal L₁ M ((ψ₂.comp χ).reduct M) ι' (v ∘ g) x := by
  letI := ψ₂.reduct M
  letI := χ.reduct M
  induction x using Quotient.ind with
  | _ t =>
    show ((χ.onTerm t).relabel g).realize v = t.realize (v ∘ g)
    rw [Term.realize_relabel, LHom.realize_onTerm]

variable (φ₀ : K.τ →ᴸ L₁)

/-- The mixed sort map as a `τ`-embedding. -/
noncomputable def mixEmb :
    (subHullModel (ψ₂.comp χ) φ₀ (v ∘ g)).carrier ↪[K.τ]
      (subHullModel ψ₂ (χ.comp φ₀) v).carrier :=
  embOfComp (subHullEmb ψ₂ (χ.comp φ₀) v) (subHullEmb (ψ₂.comp χ) φ₀ (v ∘ g))
    (mixMap χ ψ₂ v g) (fun x => hullVal_mixMap χ ψ₂ v g x)

theorem mixEmb_strong (hY : K.Strong (subHullEmb ψ₂ (χ.comp φ₀) v))
    (hX : K.Strong (subHullEmb (ψ₂.comp χ) φ₀ (v ∘ g))) : K.Strong (mixEmb χ ψ₂ v g φ₀) :=
  embOfComp_strong _ _ _ _ hY hX

end Mix

variable (φ₀ : K.τ →ᴸ L₁)

section MixBundle

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
  {c : (m : ℕ) → 0 < m → TpColorB L r m}
  (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpResB r f (c m hm))
  {r₁ r₀ : ℕ} (σ : Fin r₁ → Fin r) (τ : Fin r₀ → Fin r₁) [NeZero r] [NeZero r₁] [NeZero r₀]

include hcoh in
/-- **Mixed-language sort map of bundled pieces** `X_H` (`L₁`-hulls of the `σ ∘ τ`-coordinates)
`→ Y_H` (`L₂`-hulls of the `σ`-coordinates): strong and natural. -/
noncomputable def subLangMixHom (hPX : SubHullStrong (ψ₂.comp χ) φ₀ P)
    (hPY : SubHullStrong ψ₂ (χ.comp φ₀) P) :
    EM83.PiecesHom (subLangPieces (ψ₂.comp χ) φ₀ hc hcoh (σ ∘ τ) hPX)
      (subLangPieces ψ₂ (χ.comp φ₀) hc hcoh σ hPY) where
  app k := mixEmb χ ψ₂ ((witB hc k).v ∘ Prod.map id σ) (Prod.map id τ) φ₀
  strong k := mixEmb_strong χ ψ₂ _ _ φ₀ (hPY _ (witB hc k).mem _) (hPX _ (witB hc k).mem _)
  natural {k l} e := by
    ext x
    induction x using Quotient.ind with
    | _ t =>
      refine congrArg (Quotient.mk _) ?_
      show ((χ.onTerm (t.relabel (Prod.map e id))).relabel (Prod.map id τ)) =
        ((χ.onTerm t).relabel (Prod.map id τ)).relabel (Prod.map e id)
      rw [onTerm_relabel, Term.relabel_relabel, Term.relabel_relabel]
      rfl

end MixBundle

end Hull83
end AEC
