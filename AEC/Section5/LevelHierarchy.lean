module

public import AEC.Section5.EligibleLevel
public import AEC.Section5.Lim

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- A cardinal is strictly closed under an ordinal function `Φ`. -/
class PhiClosed (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) (μ : Cardinal.{u}) : Prop where
  below : ∀ α : _root_.Ordinal.{u}, α < μ.ord → Φ α < μ.ord

/-- Advance notation of §5.2, repeated in §13.3. `G₀` is the working levels strictly closed
under `Φ`, and `Gⱼ₊₁ = Gⱼ ∩ Lim(Gⱼ)`. -/
def G (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) : ℕ → Set Cardinal.{u}
  | 0 => {μ | IsWorkingLevel μ ∧ PhiClosed Φ μ}
  | n + 1 => G Φ n ∩ Lim (G Φ n)

/-- `G_ω = ⋂ⱼ Gⱼ`. -/
def GOmega (Φ : _root_.Ordinal.{u} → _root_.Ordinal.{u}) : Set Cardinal.{u} :=
  {μ | ∀ n, μ ∈ G Φ n}

end
end AEC
