module

public import AEC.Section6.FreeExtension
public import AEC.Section6.ProductType
public import AEC.Section6.SchemeAmalgam
public import AEC.Section6.ApproximateRetraction
public import AEC.Section7.AllDominated
public import AEC.Section6.TestingFunction
public import AEC.Section5.PackageClauses
public import AEC.Section3.OrderEqualityDiagram

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- `T` is an unbounded subclass of the eligible levels. -/
def Tail (S T : Set Cardinal.{u}) : Prop :=
  T ⊆ S ∧ ∀ κ : Cardinal.{u}, ∃ μ, κ ≤ μ ∧ μ ∈ T

theorem Tail.mem {S T : Set Cardinal.{u}} (h : Tail S T) {μ : Cardinal.{u}}
    (hμ : μ ∈ T) : μ ∈ S :=
  h.1 hμ

/-- **Lemma 6.1** (Parameter orbits for a scheme). If `χ ^ σ = χ` and `χ > b + σ`, then at
every sufficiently closed level there are at most `χ` diagrams of `σ`-tuples over a parameter
tuple of length at most `χ`. -/
theorem lemma_6_1 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (σ χ b : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hpow : χ ^ σ = χ) (hb : b + σ < χ) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : W.Object μ (Tail.mem hT hμ))
        {ι ρ : Type u} (hι : #ι ≤ σ) (hρ : #ρ ≤ χ)
        (params : ρ → Occurrence K S (W.asSystem _ X))
        (family : Set (ι → Occurrence K S (W.asSystem _ X))),
        ∃ reps : Set (ι → Occurrence K S (W.asSystem _ X)),
          #reps ≤ χ ∧ ∀ xs ∈ family, ∃ ys ∈ reps,
            W.DiagramEq (X := X) (Y := X)
              (fun i : ι ⊕ ρ => Sum.elim xs params i)
              (fun i : ι ⊕ ρ => Sum.elim ys params i) := by
  sorry

/-- **Proposition 6.3** (Uniform testing for natural layouts). For each fixed natural layout
there is a monotone `g` such that, at all sufficiently closed levels, two placed types of
length at most `σ` agree if and only if their diagrams agree on queries of size at most
`g(σ)`. -/
theorem proposition_6_3 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (layout : NaturalParameterLayout.{u}) :
    ∃ T, ∃ hT : Tail W.eligible T, ∃ g : TestingFunction layout,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (p q : TupleOver K S W (Tail.mem hT hμ) A) (e : p.idx ≃ q.idx) (σ : Cardinal.{u}),
        #p.idx ≤ σ →
        SameGaloisType p q (Equiv.refl p.idx) e.symm ↔
          ∀ {ι : Type u} (Z : ι → Occurrence K S (W.asSystem _ A)), #ι ≤ g.g σ →
            W.DiagramEq (X := p.host) (Y := q.host)
              (typeJoint (p := p) Z)
              (fun i => Sum.elim (fun j => q.val (e j))
                (fun k => ⟨(Z k).1, q.incl.onVertex (Z k).1 (Z k).2⟩) i) := by
  sorry

/-- **Lemma 6.4** (Compact placement for a scheme). Coherent locally possible prescriptions
of size at most `χ`, with `χ ^ σ = χ`, are realized by one placement at a sufficiently closed
level. -/
theorem lemma_6_4 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (σ χ b : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hb : b + σ < χ) (hpow : χ ^ σ = χ) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        {idx : Type u} (hidx : #idx ≤ σ)
        (q : ∀ {β : Type u}, #β ≤ χ →
          (β → Occurrence K S (W.asSystem _ A)) → idx ⊕ β → Occurrence K S (W.asSystem _ A)),
        (∀ {β : Type u} (hβ : #β ≤ χ) (p : β → Occurrence K S (W.asSystem _ A)),
          ∃ z : (idx → Occurrence K S (W.asSystem _ A)),
            W.DiagramEq (X := A) (Y := A) (Sum.elim z p) (q hβ p)) →
        ∃ (B : W.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B))
          (hf : W.permitted (X := A) (Y := B) f)
          (z : idx → Occurrence K S (W.asSystem _ B)),
          ∀ {β : Type u} (hβ : #β ≤ χ) (p : β → Occurrence K S (W.asSystem _ A)),
            W.DiagramEq (X := B) (Y := A)
              (Sum.elim z (fun b => ⟨(p b).1, f.onVertex (p b).1 (p b).2⟩))
              (q hβ p) := by
  sorry

/-- **Lemma 6.5** (Placed comparisons of actual tuples). The diagrams of a bounded tuple over
bounded subsets of the base have one placed comparison, and two tuples have the same
comparison if and only if their diagrams agree on queries of size at most `g(|v| + ℵ₀)`. -/
theorem lemma_6_5 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (g : Cardinal.{u} → Cardinal.{u})
    (hg : ∀ σ τ, σ ≤ τ → g σ ≤ g τ) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (p q : TupleOver K S W (Tail.mem hT hμ) A) (e : p.idx ≃ q.idx),
        #p.idx < μ →
        SameGaloisType p q (Equiv.refl p.idx) e.symm ↔
          ∀ {ι : Type u} (Z : ι → Occurrence K S (W.asSystem _ A)),
            #ι ≤ g (#p.idx + aleph0) →
            W.DiagramEq (X := p.host) (Y := q.host) (typeJoint (p := p) Z)
              (reindexJoint e.symm (typeJoint (p := q) Z)) := by
  sorry

/-- **Theorem 6.6** (Amalgamation and types for a scheme). At sufficiently closed levels the
scheme has amalgamation, and an amalgam identifying two bounded tuples exists if and only if
their diagrams agree on queries of size at most `g(|v| + ℵ₀)`. -/
theorem theorem_6_6 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (g : Cardinal.{u} → Cardinal.{u}) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B₀ B₁ : W.Object μ (Tail.mem hT hμ))
        (f₀ : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B₀))
        (f₁ : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B₁)),
        W.permitted (X := A) (Y := B₀) f₀ → W.permitted (X := A) (Y := B₁) f₁ →
        (∃ (C : W.Object μ (Tail.mem hT hμ))
            (g₀ : SystemArrow K S (W.asSystem _ B₀) (W.asSystem _ C))
            (g₁ : SystemArrow K S (W.asSystem _ B₁) (W.asSystem _ C)),
            W.permitted (X := B₀) (Y := C) g₀ ∧ W.permitted (X := B₁) (Y := C) g₁ ∧
            ∀ v, (g₀.onVertex v).comp (f₀.onVertex v) =
              (g₁.onVertex v).comp (f₁.onVertex v)) ∧
        ∀ {idx : Type u} (v₀ : idx → Occurrence K S (W.asSystem _ B₀))
          (v₁ : idx → Occurrence K S (W.asSystem _ B₁)),
          #idx < μ →
          (∃ (C : W.Object μ (Tail.mem hT hμ))
              (g₀ : SystemArrow K S (W.asSystem _ B₀) (W.asSystem _ C))
              (g₁ : SystemArrow K S (W.asSystem _ B₁) (W.asSystem _ C)),
              W.permitted (X := B₀) (Y := C) g₀ ∧ W.permitted (X := B₁) (Y := C) g₁ ∧
              (∀ v, (g₀.onVertex v).comp (f₀.onVertex v) =
                (g₁.onVertex v).comp (f₁.onVertex v)) ∧
              ∀ i, ∃ x, v₁ i = ⟨(v₀ i).1, x⟩ ∧
                g₀.onVertex (v₀ i).1 (v₀ i).2 = g₁.onVertex (v₀ i).1 x) ↔
          (∀ {ι : Type u} (Z : ι → Occurrence K S (W.asSystem _ A)), #ι ≤ g (#idx + aleph0) →
            W.DiagramEq (X := B₀) (Y := B₁)
              (fun j : idx ⊕ ι => Sum.elim v₀
                (fun k => ⟨(Z k).1, f₀.onVertex (Z k).1 (Z k).2⟩) j)
              (fun j : idx ⊕ ι => Sum.elim v₁
                (fun k => ⟨(Z k).1, f₁.onVertex (Z k).1 (Z k).2⟩) j)) := by
  sorry

/-- **Corollary 6.7** (Realization into a larger level). An arrow `A → B` at level `ν` and an
arrow `A → N` at a larger level `μ` extend to an arrow `B → N`. -/
theorem corollary_6_7 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ ν (hν : ν ∈ T) μ (hμ : μ ∈ T), ν < μ →
        ∀ (A : W.Object ν (Tail.mem hT hν)) (B : W.Object ν (Tail.mem hT hν))
          (N : W.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B))
          (g : SystemArrow K S (W.asSystem _ A) (W.asSystem _ N)),
          W.permitted (X := A) (Y := B) f → W.permitted (X := A) (Y := N) g →
          ∃ h : SystemArrow K S (W.asSystem _ B) (W.asSystem _ N),
            W.permitted (X := B) (Y := N) h ∧ SystemArrow.comp f h = g := by
  sorry

/-- **Lemma 6.9** (Uniform majority approximations). At sufficiently closed levels, a bounded
type has approximation sequences of every prescribed bounded infinite length. -/
theorem lemma_6_9 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (p : TupleOver K S W (Tail.mem hT hμ) A) (τ κ : Cardinal.{u}),
        #p.idx < μ → aleph0 ≤ τ → τ < μ → aleph0 ≤ κ → κ < μ →
        ∃ seq : ApproximationSequence p, seq.τ = τ ∧ #(seq.κIndex) = κ := by
  sorry

/-- **Theorem 6.10** (Stationary free extension). A type over `A` has a free lift to any arrow
`A → B` at a sufficiently closed level, and an actual type is free from `A` precisely when it
is that free lift. -/
theorem theorem_6_10 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B : W.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B))
        (hf : W.permitted (X := A) (Y := B) f)
        (p : TupleOver K S W (Tail.mem hT hμ) A),
        #p.idx < μ →
        ∃ q : TupleOver K S W (Tail.mem hT hμ) B, ∃ e : p.idx ≃ q.idx,
          IsFreeLift p q f hf e := by
  sorry

/-- **Lemma 6.11** (An average criterion for descent). A type whose restrictions to a long
sequence in `A` have the stated majority is the free lift of its restriction to `A`. -/
theorem lemma_6_11 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) ν (hν : ν ∈ T) (A : W.Object ν (Tail.mem hT hν))
        (B : W.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B))
        (hf : W.permitted (X := A) (Y := B) f)
        (q : TupleOver K S W (Tail.mem hT hμ) B)
        (seq : ApproximationSequence (q.restrict f hf)),
        ν ≤ μ → #q.idx < ν → seq.τ < ν → #(seq.κIndex) < ν →
        (∀ {ι : Type u} (Z : ι → Occurrence K S (W.asSystem _ B)), #ι ≤ seq.τ →
          ∃ Z0 : ι → Occurrence K S (W.asSystem _ A),
            IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z)) →
        IsFreeFrom f hf q := by
  sorry

/-- **Proposition 6.12** (Products of bounded types). Bounded types have a product over `A`,
independent of the choice of realization, symmetric, and commuting with free lifts. -/
theorem proposition_6_12 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (p q : TupleOver K S W (Tail.mem hT hμ) A),
        #p.idx < μ → #q.idx < μ →
        ∃ joint : TupleOver K S W (Tail.mem hT hμ) A,
          ∃ e : p.idx ⊕ q.idx ≃ joint.idx, IsProduct p q joint e := by
  sorry

/-- **Proposition 6.13** (Local character and continuity). A type over the union of a chain,
of length below the cofinality of the chain, is free from some stage. -/
theorem proposition_6_13 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (p : TupleOver K S W (Tail.mem hT hμ) A),
        #p.idx < μ →
        ∃ (ν : Cardinal.{u}) (hν : ν ∈ T) (A₀ : W.Object ν (Tail.mem hT hν))
          (f : SystemArrow K S (W.asSystem _ A₀) (W.asSystem _ A))
          (hf : W.permitted (X := A₀) (Y := A) f),
          ν ≤ μ ∧ IsFreeFrom f hf p := by
  sorry

/-- **Lemma 6.14** (Closure of a bounded support set). A bounded colored set of positions
outside a convex strip can be enlarged to a still bounded set that realizes every
order/equality/color pattern of length at most `χ` over its subsets of size at most `χ`. -/
theorem lemma_6_14 {J : Type u} [LinearOrder J] (color : J → ℕ)
    (χ lam : Cardinal.{u}) (hχ : aleph0 ≤ χ) (hlam : χ ≤ lam) :
    ∀ (S0 : Set J), #S0 ≤ lam →
      ∃ S : Set J, S0 ⊆ S ∧ #S ≤ (2 : Cardinal.{u}) ^ lam ∧
        ∀ {ι : Type u} (hι : #ι ≤ χ) (p : ι → J), (∀ i, p i ∈ S) →
          ∀ {n : ℕ} (q : Fin n → J), n ≤ χ →
            ∃ q' : Fin n → J, (∀ i, q' i ∈ S) ∧
              SameOrderDiagram (Sum.elim p q) (Sum.elim p q') ∧
              ∀ i, color (q i) = color (q' i) := by
  sorry

/-- **Proposition 6.15** (Universality of a fresh strip). Every same-level extension of a
presented object `A` embeds into the object obtained by inserting a fresh convex strip. -/
theorem proposition_6_15 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (hpack : HasChainUnions W) (hmix : HasMixedDownward W)
    (hsat : IsSaturated W) (hexh : SatisfiesExhaustion W) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ)),
        ∃ Ap : W.Object μ (Tail.mem hT hμ),
          ∃ incl : SystemArrow K S (W.asSystem _ A) (W.asSystem _ Ap),
            W.permitted (X := A) (Y := Ap) incl ∧
            ∀ (B : W.Object μ (Tail.mem hT hμ))
              (f : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B)),
              W.permitted (X := A) (Y := B) f →
              ∃ g : SystemArrow K S (W.asSystem _ B) (W.asSystem _ Ap),
                W.permitted (X := B) (Y := Ap) g ∧ SystemArrow.comp f g = incl := by
  sorry

/-- **Corollary 6.16** (Approximate retractions). For same-level `A ≤ B` there is a family of
arrows `B → A`, indexed by the level, such that each element of `A` is moved only finitely
often. -/
theorem corollary_6_16 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B : W.Object μ (Tail.mem hT hμ))
        (incl : SystemArrow K S (W.asSystem _ A) (W.asSystem _ B)),
        W.permitted (X := A) (Y := B) incl →
        Nonempty (ApproximateRetraction K S W (Tail.mem hT hμ) A B incl) := by
  sorry

/-- **Lemma 6.17** (Descent through approximate retractions). If retractions of `U` onto `A`
fix `A` up to a finite set and preserve a smaller pair `A' ≤ U'`, then a bounded tuple of `U'`
is free from `A'` over `A`. -/
theorem lemma_6_17 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) ν (hν : ν ∈ T)
        (A : W.Object μ (Tail.mem hT hμ)) (U : W.Object μ (Tail.mem hT hμ))
        (A' : W.Object ν (Tail.mem hT hν)) (U' : W.Object ν (Tail.mem hT hν))
        (toA : SystemArrow K S (W.asSystem _ A') (W.asSystem _ A))
        (toU : SystemArrow K S (W.asSystem _ U') (W.asSystem _ U))
        (incl : SystemArrow K S (W.asSystem _ A) (W.asSystem _ U))
        (incl' : SystemArrow K S (W.asSystem _ A') (W.asSystem _ U')),
        ν ≤ μ →
        (htoA : W.permitted (X := A') (Y := A) toA) →
        (htoU : W.permitted (X := U') (Y := U) toU) →
        (hincl : W.permitted (X := A) (Y := U) incl) →
        W.permitted (X := A') (Y := U') incl' →
        (∀ v, (incl.onVertex v).comp (toA.onVertex v) =
          (toU.onVertex v).comp (incl'.onVertex v)) →
        (∃ (ι : Type u) (r : ι → SystemArrow K S (W.asSystem _ U) (W.asSystem _ A)),
          #ι = ν ∧ (∀ i, W.permitted (X := U) (Y := A) (r i)) ∧
          (∀ a : Occurrence K S (W.asSystem _ A),
            Finite {i : ι // (r i).onVertex a.1 (incl.onVertex a.1 a.2) ≠ a.2}) ∧
          ∀ i v (x : ((W.asSystem _ U').obj v).carrier),
            ∃ y, toA.onVertex v y = (r i).onVertex v (toU.onVertex v x)) →
        ∀ {dIdx : Type u} (d : dIdx → Occurrence K S (W.asSystem _ U')),
          #dIdx < ν →
          IsFreeFrom toA htoA (asTuple incl hincl
            (fun i => ⟨(d i).1, toU.onVertex (d i).1 (d i).2⟩)) := by
  sorry

end
end AEC
