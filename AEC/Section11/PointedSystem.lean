module

public import AEC.Section11.GeometricSystem
public import AEC.Section11.JointFreshness
public import AEC.Section10.ProductAxioms
public import AEC.Section10.PointedModel

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- **Definition 11.1, pointed form.** A geometric system *of the minimal type `D`*: every
vertex is a pointed model (a strong copy of `M₀` with diagram `Δ`, compatible along the
inclusions), `P(X_t)` is the point set of `D`, independence is the finite independence of
Definition 10.3, the pieces are pairwise disjoint in the top and their union is independent there
(a partition of a basis). Uniformity (`|H_s| = μ`) is the separate predicate
`GeometricSystem.UniformAt`.

The bare `GeometricSystem` leaves `indep`, `inP` and the pieces unconstrained, which made
Proposition 11.6 degenerate and Claims 11.10, 11.13 and Theorem 11.9 false
(`AEC.Audit.claim_11_10_arbitrary_false`, `claim_11_13_false`, `theorem_11_9_arbitrary_false`). -/
structure GeometricSystem.IsPointed {K : AbstractElementaryClass.{u}} (D : MinimalData K)
    {n : ℕ} {L : Set (Finset (Fin n))} (X : GeometricSystem K n L) where
  copy : ∀ t, Language.Embedding K.τ D.M0.carrier (X.vertex t).carrier
  copy_strong : ∀ t, K.Strong (copy t)
  copy_delta : ∀ t, D.Delta (X.vertex t) (copy t)
  copy_comm : ∀ {s t : Finset (Fin n)} (h : s ⊆ t), (X.le h).comp (copy s) = copy t
  inP_eq : ∀ t, X.inP t = {x | InPointSet D (X.vertex t) (copy t) x}
  indep_eq : ∀ t (S : Set (X.vertex t).carrier), X.indep t S ↔ pointIndep D (X.vertex t) (copy t) S
  piece_disjoint : ∀ s (hs : s ∈ L) t (ht : t ∈ L), s ≠ t →
    Disjoint (X.le (Finset.subset_univ s) '' X.piece s hs)
      (X.le (Finset.subset_univ t) '' X.piece t ht)
  piece_indep : ∀ F : Set (X.vertex Finset.univ).carrier, F.Finite →
    F ⊆ {y | ∃ s, ∃ hs : s ∈ L, ∃ z, z ∈ X.piece s hs ∧ X.le (Finset.subset_univ s) z = y} →
    pointIndep D (X.vertex Finset.univ) (copy Finset.univ) F

/-- A geometric system is uniform at level `μ` (Definition 11.1): its level is `μ` and every
active piece has rank `μ`. Section 14 systems carry a cardinal assignment instead. -/
def GeometricSystem.UniformAt {K : AbstractElementaryClass.{u}} {n : ℕ}
    {L : Set (Finset (Fin n))} (X : GeometricSystem K n L) (μ : Cardinal.{u}) : Prop :=
  X.level = μ ∧ ∀ s (hs : s ∈ L), X.pieceRank s hs = μ

/-- An arrow of pointed geometric systems preserves the copies of `M₀` pointwise. -/
def GeometricArrow.IsPointed {K : AbstractElementaryClass.{u}} {D : MinimalData K}
    {n : ℕ} {L : Set (Finset (Fin n))} {X Y : GeometricSystem K n L}
    (PX : X.IsPointed D) (PY : Y.IsPointed D) (f : GeometricArrow K X Y) : Prop :=
  ∀ t, (f.onVertex t).comp (PX.copy t) = PY.copy t

/-- `U → Y` reflects pieces: a piece element of `Y` in the image comes from a piece of `U`. -/
def GeometricArrow.ReflectsPieces {K : AbstractElementaryClass.{u}} {n : ℕ}
    {L : Set (Finset (Fin n))} {U Y : GeometricSystem K n L} (h : GeometricArrow K U Y) : Prop :=
  ∀ s (hs : s ∈ L), h.onVertex s '' U.piece s hs = Y.piece s hs ∩ Set.range (h.onVertex s)

/-- `G_L` is categorical at `μ`: any two pointed systems of level `μ` are isomorphic by a pointed
arrow that is bijective at every vertex. -/
def GLCategoricalAt {K : AbstractElementaryClass.{u}} (D : MinimalData K) (n : ℕ)
    (L : Set (Finset (Fin n))) (μ : Cardinal.{u}) : Prop :=
  ∀ (X Y : GeometricSystem K n L) (PX : X.IsPointed D) (PY : Y.IsPointed D),
    X.UniformAt μ → Y.UniformAt μ →
    ∃ f : GeometricArrow K X Y, f.IsPointed PX PY ∧ ∀ t, Function.Bijective (f.onVertex t)

/-- Same type of finite labeled tuples over `X` inside pointed systems: a pair of pointed arrows
into a common pointed system identifies them and commutes with the inclusions of `X`. -/
def SamePointedGeometricType {K : AbstractElementaryClass.{u}} (D : MinimalData K)
    {n : ℕ} {L : Set (Finset (Fin n))}
    {k : ℕ} {X Y0 Y1 : GeometricSystem K n L} (P0 : Y0.IsPointed D) (P1 : Y1.IsPointed D)
    (f0 : GeometricArrow K X Y0) (f1 : GeometricArrow K X Y1) (labs : Fin k → Finset (Fin n))
    (b0 : ∀ i, (Y0.vertex (labs i)).carrier)
    (b1 : ∀ i, (Y1.vertex (labs i)).carrier) : Prop :=
  ∃ (Z : GeometricSystem K n L) (PZ : Z.IsPointed D)
    (g0 : GeometricArrow K Y0 Z) (g1 : GeometricArrow K Y1 Z),
    g0.IsPointed P0 PZ ∧ g1.IsPointed P1 PZ ∧
    (∀ t, (g0.onVertex t).comp (f0.onVertex t) = (g1.onVertex t).comp (f1.onVertex t)) ∧
    ∀ i, g0.onVertex (labs i) (b0 i) = g1.onVertex (labs i) (b1 i)

end
end AEC
