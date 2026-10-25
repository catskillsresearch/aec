module

public import AEC.Section11.AdmissibleFamily
public import AEC.Section10.GeomClosure
public import AEC.Section1.AbstractElementaryClass

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- **Definition 11.1.** A geometric system of shape `L`: pointed models `X_t` for each subset
of the axes, strong along inclusions, with a witnessing basis partition `(H_s)` of the top such
that `P(X_t)` is the closure of the pieces `H_s` for `s ⊆ t`. At a uniform level every piece has
cardinality `μ`. -/
structure GeometricSystem (K : AbstractElementaryClass.{u}) (n : ℕ)
    (L : Set (Finset (Fin n))) where
  admissible : Admissible n L
  level : Cardinal.{u}
  vertex : Finset (Fin n) → Model K.τ
  inK : ∀ t, K.Mem (vertex t)
  le : ∀ {s t : Finset (Fin n)}, s ⊆ t →
    Language.Embedding K.τ (vertex s).carrier (vertex t).carrier
  le_strong : ∀ {s t : Finset (Fin n)} (h : s ⊆ t), K.Strong (le h)
  le_refl : ∀ s, le (Finset.Subset.refl s) = Language.Embedding.refl K.τ (vertex s).carrier
  le_trans : ∀ {s t u : Finset (Fin n)} (hst : s ⊆ t) (htu : t ⊆ u),
    le (hst.trans htu) = (le htu).comp (le hst)
  indep : (t : Finset (Fin n)) → Set (vertex t).carrier → Prop
  inP : (t : Finset (Fin n)) → Set (vertex t).carrier
  piece : ∀ s, s ∈ L → Set (vertex s).carrier
  piece_card : ∀ s (hs : s ∈ L), #(piece s hs) = level
  lower : (t : Finset (Fin n)) → Set (vertex t).carrier :=
    fun t => {x | ∃ s, ∃ hs : s ∈ L, ∃ hst : s ⊆ t, ∃ y, y ∈ piece s hs ∧ le hst y = x}
  span : ∀ t, inP t = {x | InClosure (indep t) (lower t) x}

/-- The relative span `D_t(X) = cl(⋃_{r ⊂ t} P(X_r))`. -/
def RelativeSpan (K : AbstractElementaryClass.{u}) {n : ℕ} {L : Set (Finset (Fin n))}
    (X : GeometricSystem K n L) (t : Finset (Fin n)) : Set (X.vertex t).carrier :=
  {x | InClosure (X.indep t)
    {y | ∃ r, ∃ hrt : r ⊂ t, ∃ z, z ∈ X.inP r ∧ X.le (le_of_lt hrt) z = y} x}

/-- An arrow of geometric systems is a commuting family of strong embeddings carrying a
witnessing partition of the domain into a witnessing partition of the codomain. -/
structure GeometricArrow (K : AbstractElementaryClass.{u}) {n : ℕ} {L : Set (Finset (Fin n))}
    (X Y : GeometricSystem K n L) where
  onVertex : ∀ t, Language.Embedding K.τ (X.vertex t).carrier (Y.vertex t).carrier
  onVertex_strong : ∀ t, K.Strong (onVertex t)
  comm : ∀ {s t : Finset (Fin n)} (h : s ⊆ t),
    (onVertex t).comp (X.le h) = (Y.le h).comp (onVertex s)
  extends_piece : ∀ s (hs : s ∈ L),
    onVertex s '' X.piece s hs ⊆ Y.piece s hs

end
end AEC
