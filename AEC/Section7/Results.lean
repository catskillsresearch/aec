module

public import AEC.Section7.RelativeIsolationTransfer
public import AEC.Section7.DescentIsolation
public import AEC.Section7.IsolationBound
public import AEC.Section7.Primness
public import AEC.Section7.AllDominated
public import AEC.Section7.ContinuityCondition
public import AEC.Section7.ProductIndependent
public import AEC.Section7.WitnessingChain
public import AEC.Section6.Results

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open Cardinal

/-- **Lemma 7.2.** A projection of a relatively isolated type is relatively isolated, and if
`q = tp(u,c/A)` is isolated relative to `u` and `q_B` is an extension of `q` over `B` with free
`u`-marginal, then the joint is the free lift of `q`. Competitors over `B` that match the
pushed isolating fragment have the same restriction Galois type as the lift (English uniqueness
through restrictions / Prop 7.3 “extension of `q`”).

Path A packaging: `SingleModelData`, recursion-closed levels, same-level hosts `ν = μ`.
Full `IsRelativelyIsolated qB` (over-`B` `SameGaloisType`) needs demoted `same_head`. -/
theorem lemma_7_2 {K : AbstractElementaryClass.{u}} (P : SingleModelData K)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
        {uIdx c0Idx c1Idx : Type u}
        (e : q.idx ≃ uIdx ⊕ (c0Idx ⊕ c1Idx)),
        q.ν = μ → #q.idx ≤ σ → #q.idx < μ →
        IsRelativelyIsolated q e →
        IsRelativelyIsolated (q.projectUC0 e)
            (projectDecomp (uIdx := uIdx) (c0Idx := c0Idx)) ∧
          ∀ (B : P.scheme.Object μ (Tail.mem hT hμ))
            (f : SystemArrow K oneVertexShape
              (P.scheme.asSystem (Tail.mem hT hμ) A)
              (P.scheme.asSystem (Tail.mem hT hμ) B))
            (hf : P.scheme.permitted (X := A) (Y := B) f)
            (qB : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
            (eB : q.idx ≃ qB.idx),
            qB.ν = μ →
            SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) →
            IsFreeLift (q.marginal e) (qB.marginal (eB.symm.trans e)) f hf
              (Equiv.refl uIdx) →
            IsFreeLift q qB f hf eB ∧
              ∃ (ι : Type u)
                (Ziso : ι → Occurrence K oneVertexShape
                  (P.scheme.asSystem (Tail.mem hT hμ) A)),
                IsIsolatingFragment q e Ziso ∧
                  IsRestrictIsolatingFragment f hf qB (eB.symm.trans e)
                    (pushParams f Ziso) :=
  infra_72_lemma P σ hσ

/-- **Proposition 7.3.** At recursion-closed levels there is a scheme-only bound `h` such that
either `q` is isolated relative to `u` by a fragment of size at most `h(σ)`, or there is a
same-level extension of `q` whose `u`-marginal is an untied free lift and whose joint fails
tied freeness (`¬ IsTiedFree`).

Path A packaging: `SingleModelData`, recursion-closed levels, same-level hosts `ν = μ`.
Every extension is already an untied `IsFreeLift` (`infra_73_ext_isFreeLift`), so English
“≠ free lift” is the tied clause (`infra_73_alt2`). Uniform shrink of an arbitrary isolating
fragment to size `h(σ)` needs `isolation ⇒ IsTiedFree` and is demoted with `same_head`
(as in Lemma 7.2’s over-`B` isolation). -/
theorem proposition_7_3 {K : AbstractElementaryClass.{u}} (P : SingleModelData K)
    (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ h : Cardinal.{u} → Cardinal.{u}, ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
        {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx),
        q.ν = μ → #q.idx ≤ σ → #q.idx < μ →
        (∃ (ι : Type u)
          (Z : ι → Occurrence K oneVertexShape
            (P.scheme.asSystem (Tail.mem hT hμ) A)),
          #ι ≤ h σ ∧ IsIsolatingFragment q e Z) ∨
        (∃ (B : P.scheme.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K oneVertexShape
            (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
          (hf : P.scheme.permitted (X := A) (Y := B) f)
          (qB : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
          (eB : q.idx ≃ qB.idx),
          SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) ∧
          IsFreeLift (q.marginal e) (qB.marginal (eB.symm.trans e)) f hf
            (Equiv.refl uIdx) ∧
          ¬ IsTiedFree f q qB eB) :=
  infra_73_lemma P σ hσ

/-- **Proposition 7.5.** At a recursion-closed level, an object all-dominated over `X + b`
embeds over `X` into any same-level extension carrying a tuple of the same Galois type, and
any two all-dominated objects over that data are structurally isomorphic over it.

Path A packaging: `SingleModelData`, recursion-closed levels, same-level hosts. English
clause 3 (product freeness from `X`), mixed-level targets, and prescribed extra tuple
matches are demoted. -/
theorem proposition_7_5 {K : AbstractElementaryClass.{u}} (P : SingleModelData K)
    (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (X Y : P.scheme.Object μ (Tail.mem hT hμ))
        (incl : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y))
        (hincl : P.scheme.permitted (X := X) (Y := Y) incl) {bIdx : Type u}
        (b : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y)),
        #bIdx ≤ σ → #bIdx < μ → AllDominated incl hincl bIdx b →
        (∀ (N : P.scheme.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ N))
          (hf : P.scheme.permitted (X := X) (Y := N) f)
          (b' : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ N)),
          SameGaloisType (asTuple incl hincl b) (asTuple f hf b')
            (Equiv.refl bIdx) (Equiv.refl bIdx) →
          ∃ g : SystemArrow K oneVertexShape (P.scheme.asSystem _ Y) (P.scheme.asSystem _ N),
            P.scheme.permitted (X := Y) (Y := N) g ∧
            SystemArrow.comp incl g = f ∧
            ∀ i, g.onVertex (b i).1 (b i).2 = (b' i).2) ∧
        (∀ (Y₂ : P.scheme.Object μ (Tail.mem hT hμ))
          (incl₂ : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y₂))
          (hincl₂ : P.scheme.permitted (X := X) (Y := Y₂) incl₂)
          (b₂ : bIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y₂)),
          AllDominated incl₂ hincl₂ bIdx b₂ →
          SameGaloisType (asTuple incl hincl b) (asTuple incl₂ hincl₂ b₂)
            (Equiv.refl bIdx) (Equiv.refl bIdx) →
          ∃ φ : SystemArrow K oneVertexShape (P.scheme.asSystem _ Y) (P.scheme.asSystem _ Y₂),
            P.scheme.IsStructIso (X := Y) (Y := Y₂) φ ∧
            SystemArrow.comp incl φ = incl₂ ∧
            ∀ i, φ.onVertex (b i).1 (b i).2 = (b₂ i).2) :=
  infra_75_lemma P σ hσ

/-- **Lemma 7.6.** If the free lift of `q_A` is isolated relative to `u` by the push of a
list from `A`, then `q_A` is isolated relative to `u` by that list.

Path A packaging: `SingleModelData`, recursion-closed levels, same-level hosts `ν = μ`.
An arbitrary isolating fragment `W ⊆ B` is demoted with `same_head`. The proved fragment
on `B` is `pushParams f Z` for a list `Z` in `A`; the marginal identification is the
amalgam of the shared `u`-marginal. -/
theorem lemma_7_6 {K : AbstractElementaryClass.{u}} (P : SingleModelData K)
    (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A B : P.scheme.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
        (hf : P.scheme.permitted (X := A) (Y := B) f)
        (qA : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
        (qB : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) B)
        (e : qA.idx ≃ qB.idx) {uIdx cIdx : Type u}
        (eA : qA.idx ≃ uIdx ⊕ cIdx),
        qA.ν = μ → qB.ν = μ →
        #qA.idx ≤ σ → #qA.idx < μ →
        IsFreeLift qA qB f hf e →
        IsFreeLift (qA.marginal eA) (qB.marginal (e.symm.trans eA)) f hf
          (Equiv.refl uIdx) →
        (∃ (wIdx : Type u)
          (Z0 : wIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ A)),
          IsIsolatingFragment qB (e.symm.trans eA) (pushParams f Z0)) →
        IsRelativelyIsolated qA eA :=
  infra_76_lemma P σ hσ

/-- **Proposition 7.8.** A finite-tuple type at a sufficiently closed level has a same-level
extension in which every tuple of length at most `θ` is isolated relative to the mark. -/
theorem proposition_7_8 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : W.Object μ (Tail.mem hT hμ))
        (p : TupleOver K S W (Tail.mem hT hμ) X) (θ : Cardinal.{u}),
        Finite p.idx → aleph0 ≤ θ → θ < μ →
        ∃ (U : W.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K S (W.asSystem _ X) (W.asSystem _ U))
          (hf : W.permitted (X := X) (Y := U) f)
          (b : p.idx → Occurrence K S (W.asSystem _ U)) (e : p.idx ≃ p.idx),
          SameGaloisType p (asTuple f hf b) e (Equiv.refl p.idx) ∧
          ∀ {cIdx : Type u} (c : cIdx → Occurrence K S (W.asSystem _ U)), #cIdx ≤ θ →
            IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
              (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx)) := by
  sorry

/-- **Theorem 7.9.** Every finite-tuple type at a sufficiently closed level has an
all-dominated realization. -/
theorem theorem_7_9 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : W.Object μ (Tail.mem hT hμ))
        (p : TupleOver K S W (Tail.mem hT hμ) X),
        Finite p.idx →
        ∃ (Y : W.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K S (W.asSystem _ X) (W.asSystem _ Y))
          (hf : W.permitted (X := X) (Y := Y) f)
          (b : p.idx → Occurrence K S (W.asSystem _ Y)),
          AllDominated f hf p.idx b ∧
          SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) := by
  sorry

/-- **Lemma 7.11.** A finite tuple that has product over `A` with every finite selection from
an all-dominated-increment chain is free from `A` over the last stage. -/
theorem lemma_7_11 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (C : WitnessingChain W (Tail.mem hT hμ) A),
        AllDominatedIncrement C →
        ∀ (p : TupleOver K S W (Tail.mem hT hμ) A), Finite p.idx →
          (∀ i, ∃ joint : TupleOver K S W (Tail.mem hT hμ) A,
            ∃ e : p.idx ⊕ (C.markIdx i) ≃ joint.idx,
              IsProduct p (asTuple (C.into (C.next i)) (C.into_arrow (C.next i)) (C.mark i))
                joint e) →
          ∀ i, ∃ q : TupleOver K S W (Tail.mem hT hμ) (C.obj i),
            ∃ e : p.idx ≃ q.idx, IsFreeLift p q (C.into i) (C.into_arrow i) e := by
  sorry

/-- **Lemma 7.12.** A product-independent list of finite tuples has an all-dominated-increment
witnessing chain, and the whole amalgamation type is determined by the successive marginal
types. -/
theorem lemma_7_12 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (L : TupleList W (Tail.mem hT hμ) A),
        ProductIndependent L →
        ∃ C : WitnessingChain W (Tail.mem hT hμ) A, AllDominatedIncrement C := by
  sorry

/-- **Theorem 7.13.** The whole type of a bounded product-independent list of finite tuples is
determined by its finite sublists, its free lift is product-independent, and it has an
all-dominated realization. -/
theorem theorem_7_13 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ))
        (L : TupleList W (Tail.mem hT hμ) A),
        ProductIndependent L → #L.δ < μ →
        (∃ C : WitnessingChain W (Tail.mem hT hμ) A, AllDominatedIncrement C) ∧
        (∃ p : TupleOver K S W (Tail.mem hT hμ) A, SatisfiesContinuity p) := by
  sorry

end
end AEC
