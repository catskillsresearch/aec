module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.Fin.Basic

@[expose] public section

namespace AEC
section

universe u

/-- A term in an order presentation: one label of positive finite arity, applied to a
strictly increasing finite list of positions from the index order. -/
@[ext]
structure SupportTerm (lab : Type u) (arity : lab → ℕ) (I : Type u) [LinearOrder I] where
  label : lab
  pos : Fin (arity label) → I
  increasing : StrictMono pos

theorem SupportTerm.ext_of_label_eq {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I]
    {t s : SupportTerm lab arity I} (h : t.label = s.label)
    (hpos : ∀ (a : Fin (arity t.label)), t.pos a = s.pos (Fin.cast (congrArg arity h) a)) : t = s := by
  rcases t with ⟨l₁, p₁, m₁⟩
  rcases s with ⟨l₂, p₂, m₂⟩
  dsimp at h
  subst h
  have : p₁ = p₂ := funext fun a => by simpa using hpos a
  subst this
  rfl

end
end AEC
