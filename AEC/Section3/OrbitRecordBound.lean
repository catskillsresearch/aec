module

public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- The uniform bound `B(ℓ, θ) = 2^{2^{ℓ+θ}}` on the number of presentation records,
and hence on the number of automorphism orbits of `θ`-tuples, from Lemma 3.6. -/
noncomputable def orbitRecordBound (ell theta : Cardinal.{u}) : Cardinal.{u} :=
  (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ell + theta))

end
end AEC
