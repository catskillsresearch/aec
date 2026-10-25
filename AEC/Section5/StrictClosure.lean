module

public import AEC.Section5.BoundedAt

@[expose] public section

namespace AEC
section

universe u


open Cardinal

/-- `μ` is strictly closed under a cardinal function `u` when `u(θ) < μ` for every
infinite `θ < μ`. -/
class StrictlyClosed (u : Cardinal.{u} → Cardinal.{u}) (μ : Cardinal.{u}) : Prop where
  below : ∀ θ : Cardinal.{u}, aleph0 ≤ θ → θ < μ → u θ < μ

end
end AEC
