module

public import AEC.Section1.AbstractElementaryClass

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- An `n`-axis object: one `K`-model for each subset of the axes, with strong inclusions along
containment of subsets. -/
structure FaceFamily (K : AbstractElementaryClass.{u}) (n : ℕ) where
  obj : Set (Fin n) → Model K.τ
  inK : ∀ s, K.Mem (obj s)
  incl : ∀ {s t : Set (Fin n)}, s ⊆ t →
    Language.Embedding K.τ (obj s).carrier (obj t).carrier
  incl_strong : ∀ {s t : Set (Fin n)} (h : s ⊆ t), K.Strong (incl h)
  incl_refl : ∀ s, incl (Set.Subset.refl s) = Language.Embedding.refl K.τ (obj s).carrier
  incl_trans : ∀ {s t u : Set (Fin n)} (hst : s ⊆ t) (htu : t ⊆ u),
    incl (hst.trans htu) = (incl htu).comp (incl hst)

end
end AEC
