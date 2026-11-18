module

public import AEC.Section7.RelativeIsolationTransfer
public import AEC.Section7.DescentIsolation
public import AEC.Section7.IsolationBound
public import AEC.Section7.Primness
public import AEC.Section7.FiniteIsolation
public import AEC.Section7.AllDominated
public import AEC.Section7.ContinuityCondition
public import AEC.Section7.ProductIndependent
public import AEC.Section7.WitnessingChain
public import AEC.Section7.ListChain
public import AEC.Section7.TiedListChain
public import AEC.Section7.Lemma711Induction
public import AEC.Section7.ProductFreeLevel
public import AEC.Section7.GeneralLevel
public import AEC.Section7.Theorem79
public import AEC.Section7.Theorem79Existence
public import AEC.Section7.RetractionPair
public import AEC.Section7.MixedDescent
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
Full `IsRelativelyIsolated qB` over `B` needs a tied-free `u`-marginal; see `lemma_7_2_tied`. -/
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

/-- **Lemma 7.2 (English-complete form).** Clause 1 as in `lemma_7_2`. Clause 2 with the
English free-extension hypothesis: if the `u`-marginal of `q_B` is tied free (the actual
answer on every sequence-move is the free evaluation), then `q_B` itself is tied free and is
relatively isolated over `B` (`infra_72_over_B_isolation`, by the pushed fragment). The
untied `IsFreeLift` marginal hypothesis of `lemma_7_2` is too weak for clause 2: it follows
from `hExt` alone. -/
theorem lemma_7_2_tied {K : AbstractElementaryClass.{u}} (P : SingleModelData K)
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
            IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e)) (Equiv.refl uIdx) →
            IsTiedFree f q qB eB ∧ IsRelativelyIsolated qB (eB.symm.trans e) :=
  infra_72_lemma_tied P σ hσ

/-- **Proposition 7.3.** At recursion-closed levels there is a scheme-only bound `h` such that
either `q` is isolated relative to `u` by a fragment of size at most `h(σ)`, or there is a
same-level extension of `q` whose `u`-marginal is an untied free lift and whose joint fails
tied freeness (`¬ IsTiedFree`).

Path A packaging: `SingleModelData`, recursion-closed levels, same-level hosts `ν = μ`.
Every extension is already an untied `IsFreeLift` (`infra_73_ext_isFreeLift`), so English
“≠ free lift” is the tied clause (`infra_73_alt2`). `isolation ⇒ IsTiedFree` is proved for a
tied-free `u`-marginal (`infra_73_tied_of_isolated`); uniform shrink to size `h(σ)`
(`infra_73_uniform_of_isolated`) still needs the alt-2 extension to have tied-free marginal
(`infra_73_alt2_tied_marginal`). That extension is built from the English block restriction
in `AltTwoTied.lean` (`infra_73_alt2_tied`), and the uniform form
`proposition_7_3_uniform_of_block` is proved there from `Infra73BlockRestriction`
(open board tip `infra_73_block_restriction`). -/
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
The proved fragment on `B` here is `pushParams f Z` for a list `Z` in `A`; the marginal
identification is the amalgam of the shared `u`-marginal. The English form for an arbitrary
isolating fragment `W ⊆ B` along a tied-free lift is `lemma_7_6_tied`
(`AEC/Section7/TiedDescent.lean`). -/
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

/-- **Proposition 7.8.** Let `λ` be a sufficiently closed eligible level, `X` an object there and
`p = tp(b/X)` a finite-tuple type. For every infinite `θ < λ` there is a same-level extension
`X ≤ U` containing a realization of `p` such that `tp(b, c/X)` is isolated relative to `b` for
every `c ∈ U` with `|c| ≤ θ`. The closure requirements are uniform (do not depend on `θ`).

**Statement (restated, grokbot_01 Phase 1.1):** over the single-model scheme `P.scheme` of
`SingleModelData` (the package on which Sections 6-7 are developed: `theorem_6_10`,
`proposition_6_13`, `proposition_7_3_uniform`, `lemma_7_6_tied`), instead of a bare
`WorkingScheme` with no working-package hypotheses. The tail `T` is chosen before `θ` (uniform
closure). The general bounded-mark form (marks satisfying Definition 7.7) is not stated.

**Proved (cycle 67).** The tail is `infra_78_closedTail P`; the conclusion is
`infra_78_marginal_general_level` (`AEC/Section7/GeneralLevel.lean`): a level-`λ` copy of `p`
(`infra_612_exists_level_copy`), the `ρ⁺` matrix argument for it (`infra_78_matrix_assembly_level`),
and cross-level Galois transitivity (`infra_612_galois_trans_cross_level_right_base`).
Finite-mark continuity (Def 7.7) is `infra_78_finite_continuity`. -/
theorem proposition_7_8 {K : AbstractElementaryClass.{u}} (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : P.scheme.Object μ (Tail.mem hT hμ))
        (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) X) (θ : Cardinal.{u}),
        Finite p.idx → aleph0 ≤ θ → θ < μ →
        ∃ (U : P.scheme.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ U))
          (hf : P.scheme.permitted (X := X) (Y := U) f)
          (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)) (e : p.idx ≃ p.idx),
          SameGaloisType p (asTuple f hf b) e (Equiv.refl p.idx) ∧
          ∀ {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
            #cIdx ≤ θ →
            IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
              (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx)) := by
  refine ⟨infra_78_closedTail P, infra_78_closedTail_tail P, fun μ hμ X p θ hfin hθ hθμ => ?_⟩
  obtain ⟨U, f, hf, b, hgal, hiso⟩ := infra_78_marginal_general_level P μ hμ X p θ hfin hθ hθμ
  exact ⟨U, f, hf, b, Equiv.refl _, hgal, hiso⟩

/-- **Theorem 7.9.** At sufficiently closed eligible levels, every finite-tuple type
`p = tp(b/X)` has an all-dominated realization: there is `Y ≥ X` all-dominated over `X + b`
realizing `p`. An all-dominated realization embeds over `X, b` into any actual ambient
containing a realization of that type, with the mixed-level conventions of Proposition 7.5
(the ambient `N` may sit at a larger eligible level `ν ≥ μ`).

**Statement (restated, grokbot_01 Phase 3.1; cycle 68 audit):** over `SingleModelData`
(the package on which Sections 6-7 are developed) instead of a bare `WorkingScheme`; `p` may be
hosted at any level. Cycle 68 restored the paper's embedding (primeness) clause, which the Phase
3.1 form had omitted. The "more generally ... bounded marginal satisfying Definition 7.7" form is
a paper hypothesis tracked by `infra_78_def77_bounded_marks` (as for `proposition_7_8`).
Split (`AEC/Section7/Theorem79.lean`): `infra_79_existence_statement` (open),
`infra_79_primeness_same_level` (proved), `infra_79_primeness_mixed` (proved, cycle 69),
`infra_79_assemble` (proved). The existence clause is split further
(`AEC/Section7/Theorem79Existence.lean`, cycle 70): `infra_79_lift_isolate`,
`infra_79_descent`, `infra_79_identify` and the assembly `infra_79_existence_of_parts` (proved);
`infra_79_tail` (proved, cycle 71); `infra_79_retraction_pair` (proved, cycle 72,
`AEC/Section7/RetractionPair.lean`). Sorry-free since cycle 72. -/
theorem theorem_7_9 {K : AbstractElementaryClass.{u}} (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : P.scheme.Object μ (Tail.mem hT hμ))
        (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) X),
        Finite p.idx →
        (∃ (Y : P.scheme.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y))
          (hf : P.scheme.permitted (X := X) (Y := Y) f)
          (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y)),
          AllDominated f hf p.idx b ∧
          SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx)) ∧
        ∀ (Y : P.scheme.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y))
          (hf : P.scheme.permitted (X := X) (Y := Y) f)
          (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y)),
          AllDominated f hf p.idx b →
          SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) →
          ∀ ν (hν : ν ∈ P.eligible) (N : P.scheme.Object ν hν)
            (g : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem hν N))
            (hg : P.scheme.permitted (X := X) (Y := N) g)
            (b' : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν N)),
            μ ≤ ν →
            SameGaloisType p (⟨ν, hν, N, g, hg, p.idx, b'⟩ :
              TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) X)
              (Equiv.refl p.idx) (Equiv.refl p.idx) →
            ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem _ Y) (P.scheme.asSystem hν N),
              P.scheme.permitted (X := Y) (Y := N) h ∧
              SystemArrow.comp f h = g ∧
              ∀ i, h.onVertex (b i).1 (b i).2 = (b' i).2 := by
  exact infra_79_of_existence P (infra_79_existence P)

/-- **Lemma 7.11** (tied, restated cycle 73). Suppose `(M_i)_{i ≤ δ}` is an all-dominated-increment
chain over `A` for finite tuples `(b_i)_{i < δ}` (`TiedListWitnessingChain`, Definition 7.10 with
`tp(bᵢ/Mᵢ) = tp(bᵢ/A)^fr_{Mᵢ}` tied). If a finite tuple `x` in an actual coupling (`x.ν = μ`) has
product over `A` (`IsProductTied`, Proposition 6.12's tied product) with every finite selection
of the accumulated `b_i`, then `tp(x/M_δ)` is free from `A`
(`IsTiedFree (A → M_δ) tp(x/A) tp(x/M_δ)`). The former statement used the vacuous untied
`IsFreeFrom` / `IsProduct` over an arbitrary `WorkingScheme`; nothing used it, so it was removed.
Proof: `infra_711_induction` (cycle 75: induction on the stage; first stage and limit stage
proved) reduces it to `infra_711_successor_statement` (open tip `infra_711_successor`), whose
English proof needs only level-joint products: Proposition 7.5(3) in the actual-coupling form
(`infra_75_product_free_level_statement`) and the proved level-joint cases of 6.12. -/
theorem lemma_7_11 {K : AbstractElementaryClass.{u}} (P : SingleModelData K) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (L : TupleList P.scheme (Tail.mem hT hμ) A) [LinearOrder L.δ] [WellFoundedLT L.δ]
        (C : TiedListWitnessingChain L),
        C.AllDominatedIncrement →
        ∀ (x : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) (C.stage ⊤)),
          Finite x.idx → x.ν = μ →
          (∀ (n : ℕ) (ix : Fin n → L.δ), Function.Injective ix →
            IsProductTied (x.restrict (C.into ⊤) (C.into_arrow ⊤)) (C.selectionOver x n ix)
              (C.jointWith x n ix) (Equiv.refl _)) →
          IsTiedFree (C.into ⊤) (x.restrict (C.into ⊤) (C.into_arrow ⊤)) x (Equiv.refl _) := by
  refine infra_711_induction P ?_
  sorry

/-- **Lemma 7.12.** (1) A product-independent list `L` of finite tuples over `A`, well-ordered,
has an all-dominated-increment witnessing chain linked to `L` (its marks are the entries of `L`
in a common ambient).  (2) Lists with witnessing chains are determined, as a whole, by their
successive marginal types over `A`. -/
theorem lemma_7_12 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : W.Object μ (Tail.mem hT hμ)),
        (∀ (L : TupleList W (Tail.mem hT hμ) A) [LinearOrder L.δ] [WellFoundedLT L.δ],
          ProductIndependent L →
          ∃ C : ListWitnessingChain L, C.AllDominatedIncrement) ∧
        (∀ (L L' : TupleList W (Tail.mem hT hμ) A) [LinearOrder L.δ] [WellFoundedLT L.δ]
            [LinearOrder L'.δ] [WellFoundedLT L'.δ]
            (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i)),
          Nonempty (ListWitnessingChain L) → Nonempty (ListWitnessingChain L') →
          (∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) →
          SameGaloisType L.whole L'.whole
            (Equiv.sigmaCongr e.toEquiv ei) (Equiv.refl _)) := by
  sorry

/-- **Theorem 7.13.** Let `L` be a bounded product-independent list of finite tuples over `X`.
(1) Its whole type is determined by its product data on finite sublists (equivalently, given
product independence, by its marginals), and every actual free lift of the whole type along
`X → B` is again product-independent: each finite sublist of the lift is the finite product of
the lifted marginals.  (2) The whole type satisfies the continuity condition.  (3) It is
realized all-dominated in an extension `Y` of `X`, and `Y` embeds over `X + b` into an ambient
containing the given list. -/
theorem theorem_7_13 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (X : W.Object μ (Tail.mem hT hμ))
        (L : TupleList W (Tail.mem hT hμ) X),
        ProductIndependent L → #(Σ i, L.indexAt i) < μ →
        -- (1a) uniqueness from finite product data
        (∀ (L' : TupleList W (Tail.mem hT hμ) X) (e : L.δ ≃ L'.δ)
            (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i)),
          ProductIndependent L' →
          (∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) →
          SameGaloisType L.whole L'.whole (Equiv.sigmaCongr e ei) (Equiv.refl _)) ∧
        -- (1b) free lifts stay product-independent
        (∀ (B : W.Object μ (Tail.mem hT hμ))
            (f : SystemArrow K S (W.asSystem _ X) (W.asSystem _ B))
            (hf : W.permitted (X := X) (Y := B) f)
            (q : TupleOver K S W (Tail.mem hT hμ) B) (eq : L.whole.idx ≃ q.idx),
          IsFreeLift L.whole q f hf eq → q.ν = μ →
          ∀ (n : ℕ) (ix : Fin n → L.δ), Function.Injective ix →
            IsFiniteProduct n
              (fun s => q.reindex (fun a : L.indexAt (ix s) => eq ⟨ix s, a⟩))
              (q.reindex (fun p : Σ s : Fin n, L.indexAt (ix s) => eq ⟨ix p.1, p.2⟩))) ∧
        -- (2) continuity
        SatisfiesContinuity L.whole ∧
        -- (3) all-dominated realization, prime over `X + b`
        (∃ (Y : W.Object μ (Tail.mem hT hμ))
          (f : SystemArrow K S (W.asSystem _ X) (W.asSystem _ Y))
          (hf : W.permitted (X := X) (Y := Y) f)
          (b : L.whole.idx → Occurrence K S (W.asSystem _ Y)),
          AllDominated f hf L.whole.idx b ∧
          SameGaloisType L.whole (asTuple f hf b) (Equiv.refl _) (Equiv.refl _) ∧
          ∃ (N : W.Object μ (Tail.mem hT hμ))
            (h : SystemArrow K S (W.asSystem _ L.host) (W.asSystem _ N))
            (_ : W.permitted (X := L.host) (Y := N) h)
            (g : SystemArrow K S (W.asSystem _ Y) (W.asSystem _ N))
            (_ : W.permitted (X := Y) (Y := N) g),
            (∀ v, (g.onVertex v).comp (f.onVertex v) = (h.onVertex v).comp (L.incl.onVertex v)) ∧
            ∀ a, g.mapOcc (b a) = h.mapOcc (L.whole.val a)) := by
  sorry

end
end AEC
