module

public import AEC.Section1.InfinitaryFragment

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- An embedding is elementary for a fragment when it preserves and reflects every
formula of the fragment. The paper orders models of an `L_{ω₁,ω}` sentence by
elementarity for a countable fragment containing that sentence. -/
def FragmentElementary {τ : Tau.{u}} (Φ : InfinitaryFragment τ)
    {M N : Model τ} (f : Language.Embedding τ M.carrier N.carrier) : Prop :=
  ∀ n (φ : Φ.Formula n) (v : Fin n → M.carrier),
    Φ.realize φ v ↔ Φ.realize φ (f ∘ v)

/-- A sentence of the fragment together with the class of models that realize it. -/
structure FragmentSentence (τ : Tau.{u}) where
  fragment : InfinitaryFragment τ
  sentence : fragment.Formula 0
  models : Model τ → Prop
  models_iff : ∀ M : Model τ,
    models M ↔ fragment.realize (M := M.carrier) sentence Fin.elim0

end
end AEC
