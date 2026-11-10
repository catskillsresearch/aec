module

public import AEC.Section2.OrderPresentation
public import AEC.Section1.Categorical

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- A stable-diagram function in the sense of Proposition 4.2. `t` is a nondecreasing
cardinal function, `t(σ)` is a categoricity cardinal above `ℓ + σ`, and `same σ xs ys`
is equality of the canonical diagrams `D(xs; M) = D(ys; N)` for tuples of length at most `σ`.

The operational clauses `of_strong`, `to_strong`, and `realize_joint` are Prop 4.2’s
Lean conjuncts (1)–(3); `to_strong` is the realize API needed by Prop 4.3
(`infra_stable_diagram_realize`). `trans` records that `same` is an equality of diagrams
(Prop 4.2 (2)); it does not follow from the other clauses, which relate models of different
sizes only through `of_strong`. -/
structure StableDiagram (K : AbstractElementaryClass.{u}) where
  t : Cardinal.{u} → Cardinal.{u}
  mono : ∀ σ τ, σ ≤ τ → t σ ≤ t τ
  above : ∀ σ, aleph0 ≤ σ → K.τ.card + σ < t σ
  categoricity : ∀ σ, aleph0 ≤ σ → Categorical K (t σ)
  same : ∀ {σ : Cardinal.{u}} {α : Type u} {M N : Model K.τ},
    #α ≤ σ → K.Mem M → K.Mem N → t σ ≤ Model.card M → t σ ≤ Model.card N →
    (α → M.carrier) → (α → N.carrier) → Prop
  refl : ∀ {σ α M} (hα : #α ≤ σ) (hM : K.Mem M) (hcard : t σ ≤ Model.card M)
    (xs : α → M.carrier), same hα hM hM hcard hcard xs xs
  symm : ∀ {σ α M N} (hα : #α ≤ σ) (hM : K.Mem M) (hN : K.Mem N)
    (hMcard : t σ ≤ Model.card M) (hNcard : t σ ≤ Model.card N)
    (xs : α → M.carrier) (ys : α → N.carrier),
    same hα hM hN hMcard hNcard xs ys → same hα hN hM hNcard hMcard ys xs
  /-- Diagram equality is an equality of canonical diagrams (Prop 4.2 (2)), hence transitive,
  also across ambient models of different sizes. Needed by Prop 4.3 to move a match between
  the `ζ`-models and their strong `t(σ)`-hulls. -/
  trans : ∀ {σ α M N P} (hα : #α ≤ σ) (hM : K.Mem M) (hN : K.Mem N) (hP : K.Mem P)
    (hMcard : t σ ≤ Model.card M) (hNcard : t σ ≤ Model.card N) (hPcard : t σ ≤ Model.card P)
    (xs : α → M.carrier) (ys : α → N.carrier) (zs : α → P.carrier),
    same hα hM hN hMcard hNcard xs ys → same hα hN hP hNcard hPcard ys zs →
    same hα hM hP hMcard hPcard xs zs
  preserves_atomic : ∀ {σ α M N} (hα : #α ≤ σ) (hM : K.Mem M) (hN : K.Mem N)
    (hMcard : t σ ≤ Model.card M) (hNcard : t σ ≤ Model.card N)
    (xs : α → M.carrier) (ys : α → N.carrier),
    same hα hM hN hMcard hNcard xs ys →
      ∀ i j, xs i = xs j ↔ ys i = ys j
  /-- Strong embeddings preserve diagram equality. -/
  of_strong : ∀ {σ : Cardinal.{u}} {α : Type u} {M N : Model K.τ} (hα : #α ≤ σ)
    (hM : K.Mem M) (hN : K.Mem N)
    (hMcard : t σ ≤ Model.card M) (hNcard : t σ ≤ Model.card N)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (f : Language.Embedding K.τ M.carrier N.carrier),
    aleph0 ≤ σ → K.Strong f → (∀ i, f (xs i) = ys i) →
    same hα hM hN hMcard hNcard xs ys
  /-- **Infra: D.same ⇒ strong map.** At equal categoricity size, diagram equality is
  implemented by a strong embedding matching the tuples. -/
  to_strong : ∀ {σ : Cardinal.{u}} {α : Type u} {M N : Model K.τ} (hα : #α ≤ σ)
    (hM : K.Mem M) (hN : K.Mem N)
    (xs : α → M.carrier) (ys : α → N.carrier),
    aleph0 ≤ σ → Categorical K (Model.card M) →
    Model.card M = Model.card N →
    (hMcard : t σ ≤ Model.card M) → (hNcard : t σ ≤ Model.card N) →
    same hα hM hN hMcard hNcard xs ys →
    ∃ f : Language.Embedding K.τ M.carrier N.carrier,
      K.Strong f ∧ ∀ i, f (xs i) = ys i
  /-- A possible joint diagram `(a, c)` realizes over a matching parameter tuple. -/
  realize_joint : ∀ {σ : Cardinal.{u}} {α γ : Type u} {M N : Model K.τ}
    (hαγ : #(α ⊕ γ) ≤ σ) (hα : #α ≤ σ)
    (hM : K.Mem M) (hN : K.Mem N)
    (hMcard : t σ ≤ Model.card M) (hNcard : t σ ≤ Model.card N)
    (ac : α ⊕ γ → M.carrier) (a : α → N.carrier),
    aleph0 ≤ σ → Categorical K (Model.card N) →
    same hαγ hM hM hMcard hMcard ac ac →
    same hα hM hN hMcard hNcard (fun i => ac (Sum.inl i)) a →
    ∃ (Q : Model K.τ) (f : Language.Embedding K.τ N.carrier Q.carrier)
      (c : γ → Q.carrier) (hQ : K.Mem Q) (hQcard : t σ ≤ Model.card Q),
      K.Strong f ∧
      same hαγ hM hQ hMcard hQcard ac (Sum.elim (fun i => f (a i)) c)

/-- Convenience alias for the Prop 4.3 realize step. -/
theorem StableDiagram.same_to_strong {K : AbstractElementaryClass.{u}} (D : StableDiagram K)
    {σ : Cardinal.{u}} {α : Type u} {M N : Model K.τ} (hα : #α ≤ σ)
    (hM : K.Mem M) (hN : K.Mem N)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (hσ : aleph0 ≤ σ) (hcat : Categorical K (Model.card M))
    (hc : Model.card M = Model.card N)
    (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N)
    (hsame : D.same hα hM hN hMcard hNcard xs ys) :
    ∃ f : Language.Embedding K.τ M.carrier N.carrier,
      K.Strong f ∧ ∀ i, f (xs i) = ys i :=
  D.to_strong hα hM hN xs ys hσ hcat hc hMcard hNcard hsame

end
end AEC
