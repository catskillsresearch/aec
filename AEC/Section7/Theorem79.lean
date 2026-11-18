module

public import AEC.Section7.GeneralLevel
public import AEC.Section7.Primness

@[expose] public section

/-!
# Theorem 7.9 (all-dominated realizations): split (cycle 68)

Paper: "Theorem 7.9. At sufficiently closed eligible levels, every finite-tuple type
`p = tp(b/X)` has an all-dominated realization: there is `Y ≥ X` all-dominated over `X + b`
realizing `p`. More generally this holds for a bounded marginal satisfying Definition 7.7. An
all-dominated realization embeds over `X, b` into any actual ambient containing a realization of
that type, with the mixed-level conventions of Proposition 7.5."

`theorem_7_9` (Results.lean) states the existence clause and the embedding clause, with the
ambient at any eligible level `≥` the level of `X` (Prop 7.5: "The target may be at a larger
eligible level"). The bounded-marginal generalization is a paper hypothesis tracked by
`infra_78_def77_bounded_marks` (as for Prop 7.8). Split:

* `infra_79_existence_statement` (open): the existence clause.
* `infra_79_primeness_same_level` (proved): the embedding clause into an ambient at the level
  of `X` (Prop 7.5 (1) after cross-level Galois transitivity through `p`).
* `infra_79_primeness_mixed_statement` (proved, cycle 69, `infra_79_primeness_mixed`): the
  embedding clause into an ambient above the level of `X` (the mixed-level form of Prop 7.5 (1)).
* `infra_79_assemble` (proved): `theorem_7_9` from the open parts.
-/

universe u

open Cardinal FirstOrder
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Galois transitivity through a middle tuple hosted at any level (proved).** Ends at the
base level `μ`; the middle host may be at any eligible level. Tests pass through the middle host
by `to_sameD` and `D.trans`; Theorem 6.6 (`infra_612_same_galois`) at `μ` concludes. -/
theorem infra_612_galois_trans_mid_any
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {t1 t2 t3 : TupleOver K oneVertexShape P.scheme hμ A}
    {e12 : t1.idx ≃ t2.idx} {e32 : t3.idx ≃ t2.idx}
    (h12 : SameGaloisType t1 t2 e12 (Equiv.refl t2.idx))
    (h32 : SameGaloisType t2 t3 (Equiv.refl t2.idx) e32)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hσμ : σ < μ)
    (hidx : #t1.idx ≤ σ) (hν1 : t1.ν = μ) (hν3 : t3.ν = μ) :
    SameGaloisType t1 t3 (e12.trans e32.symm) (Equiv.refl t3.idx) := by
  have hL : ClosedLevel K P.E P.D P.g μ := by
    have : CategoricalUnbounded K := P.D.categoricalUnbounded
    exact ClosedLevel.of_closurePoint P.tester hμ.1 hμ.2
  apply infra_612_same_galois t1 t3 (e12.trans e32.symm) σ hσ hσμ hidx hν1 hν3 hL
  intro β hβ ρ0 hρinf hρμ params hjnt h0 h1
  have hμ2 : μ ≤ Model.card t2.host.model := by
    have h : #A.model.carrier ≤ #t2.host.model.carrier :=
      Cardinal.mk_le_of_injective (t2.incl.onVertex PUnit.unit).injective
    have e1 : #A.model.carrier = μ := A.card
    rw [e1] at h
    exact h
  have h2 : P.D.t ρ0 ≤ Model.card t2.host.model :=
    (P.t_lt hμ hρinf hρμ).le.trans hμ2
  have h23 : #t3.idx = #t2.idx := Cardinal.mk_congr e32
  have hj2 : #t2.idx + #β ≤ ρ0 := by simpa [h23] using hjnt
  have hab := SameGaloisType.to_sameD h12 params ρ0 hρinf (by simpa using hj2) h0 h2
  have hbc := SameGaloisType.to_sameD h32 params ρ0 hρinf (by simpa using hj2) h2 h1
  have hmid := P.D.trans hj2 t1.host.mem t2.host.mem t3.host.mem h0 h2 h1 _ _ _
    (by simpa [Equiv.refl_symm] using hab) (by simpa [Equiv.refl_symm] using hbc)
  have hc1 : Model.card t1.host.model = μ := by simpa [hν1] using t1.host.card
  have hc3 : Model.card t3.host.model = μ := by simpa [hν3] using t3.host.card
  let σ' : Cardinal.{u} := max ρ0 (ls K)
  have hσ'μ : σ' < μ := max_lt hρμ (P.ls_lt hμ)
  have hσ'inf : aleph0 ≤ σ' := hρinf.trans (le_max_left _ _)
  have ht' : P.D.t σ' ≤ μ := (P.t_lt hμ hσ'inf hσ'μ).le
  let hι : (t3.idx ⊕ β) → (t2.idx ⊕ β) := Sum.map e32 id
  have hL1 := P.D.same_relevel hj2 hρinf hρinf (le_max_left ρ0 (ls K)) (le_max_left ρ0 (ls K))
    (le_max_right ρ0 (ls K)) t1.host.mem t3.host.mem h0 h1
    (ht'.trans hc1.ge) (ht'.trans hc3.ge) h0 h1 _ _ hmid hjnt hι
  convert hL1 using 1
  · funext c
    cases c with
    | inl k =>
      dsimp [hι, Sum.map]
      rfl
    | inr b =>
      dsimp [hι, Sum.map]
      exact congrArg (fun v => t1.incl.onVertex v (params b)) (Subsingleton.elim _ _)
  · funext c
    cases c with
    | inl k =>
      change t3.host.val (t3.val k) = t3.host.val (t3.val (e32.symm (e32 k)))
      rw [Equiv.symm_apply_apply]
    | inr b =>
      dsimp [hι, Sum.map]
      exact congrArg (fun v => t3.incl.onVertex v (params b)) (Subsingleton.elim _ _)

/-- **Embedding clause of Theorem 7.9, ambient at the level of `X` (proved).** An
all-dominated realization `(Y, b)` of a finite-tuple type `p` (hosted at any level) embeds over
`X`, sending `b` to `b'`, into any same-level extension `N` of `X` containing a realization `b'`
of `p`. -/
theorem infra_79_primeness_same_level {P : SingleModelData K} {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (X : P.scheme.Object μ hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ X) (hfin : Finite p.idx)
    (Y : P.scheme.Object μ hμ)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
    (hAll : AllDominated f hf p.idx b)
    (hp : SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx))
    (N : P.scheme.Object μ hμ)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hg : P.scheme.permitted (X := X) (Y := N) g)
    (b' : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N))
    (hN : SameGaloisType p (asTuple g hg b') (Equiv.refl p.idx) (Equiv.refl p.idx)) :
    ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ N),
      P.scheme.permitted (X := Y) (Y := N) h ∧
      SystemArrow.comp f h = g ∧
      ∀ i, h.onVertex (b i).1 (b i).2 = (b' i).2 := by
  have hidx : #p.idx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite p.idx).le
  have hYN := infra_612_galois_trans_mid_any (t1 := asTuple f hf b) (t2 := p)
    (t3 := asTuple g hg b') (e12 := Equiv.refl p.idx) (e32 := Equiv.refl p.idx)
    hp.symm hN ℵ₀ le_rfl (P.aleph0_lt hμ) hidx rfl rfl
  exact infra_75_embed hμ X Y N f hf g hg b b'
    (hidx.trans_lt (P.aleph0_lt hμ)) hYN hAll

/-- **Existence clause of Theorem 7.9 (open).** -/
def infra_79_existence_statement (P : SingleModelData K) : Prop :=
  ∃ T, ∃ hT : Tail P.eligible T,
    ∀ μ (hμ : μ ∈ T) (X : P.scheme.Object μ (Tail.mem hT hμ))
      (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) X),
      Finite p.idx →
      ∃ (Y : P.scheme.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ Y))
        (hf : P.scheme.permitted (X := X) (Y := Y) f)
        (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ Y)),
        AllDominated f hf p.idx b ∧
        SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx)

/-- **Embedding clause of Theorem 7.9, ambient above the level of `X` (open).** The mixed-level
form of Proposition 7.5 (1) for an all-dominated realization of a finite-tuple type. -/
def infra_79_primeness_mixed_statement (P : SingleModelData K) : Prop :=
  ∀ μ (hμ : μ ∈ P.eligible) (X : P.scheme.Object μ hμ)
    (p : TupleOver K oneVertexShape P.scheme hμ X),
    Finite p.idx →
    ∀ (Y : P.scheme.Object μ hμ)
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
      (hf : P.scheme.permitted (X := X) (Y := Y) f)
      (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
      AllDominated f hf p.idx b →
      SameGaloisType p (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) →
      ∀ ν (hν : ν ∈ P.eligible) (N : P.scheme.Object ν hν)
        (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hν N))
        (hg : P.scheme.permitted (X := X) (Y := N) g)
        (b' : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν N)),
        μ < ν →
        SameGaloisType p (⟨ν, hν, N, g, hg, p.idx, b'⟩ :
          TupleOver K oneVertexShape P.scheme hμ X) (Equiv.refl p.idx) (Equiv.refl p.idx) →
        ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hν N),
          P.scheme.permitted (X := Y) (Y := N) h ∧
          SystemArrow.comp f h = g ∧
          ∀ i, h.onVertex (b i).1 (b i).2 = (b' i).2

/-- **The conclusion of `theorem_7_9`.** -/
def theorem_7_9_statement (P : SingleModelData K) : Prop :=
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
            ∀ i, h.onVertex (b i).1 (b i).2 = (b' i).2

/-- **Assembly of Theorem 7.9 from its open parts (proved).** -/
theorem infra_79_assemble (P : SingleModelData K)
    (h : infra_79_existence_statement P ∧ infra_79_primeness_mixed_statement P) :
    theorem_7_9_statement P := by
  obtain ⟨⟨T, hT, hE⟩, hM⟩ := h
  refine ⟨T, hT, fun μ hμ X p hfin => ⟨hE μ hμ X p hfin, ?_⟩⟩
  intro Y f hf b hAll hp ν hν N g hg b' hμν hN
  rcases hμν.lt_or_eq with hlt | heq
  · exact hM μ (Tail.mem hT hμ) X p hfin Y f hf b hAll hp ν hν N g hg b' hlt hN
  · subst heq
    exact infra_79_primeness_same_level (Tail.mem hT hμ) X p hfin Y f hf b hAll hp N g hg b' hN

/-- **Level-`μ` copy with its arrow (proved).** As `infra_612_exists_level_copy`, exposing the
arrow `r : copy host → t.host` over the base that carries the copied tuple onto `t`'s tuple. -/
theorem infra_612_exists_level_copy_arrow
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    (t : TupleOver K oneVertexShape P.scheme hμ A) (hidx : #t.idx ≤ μ) :
    ∃ (host : P.scheme.Object μ hμ)
      (incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ host))
      (hincl : P.scheme.permitted (X := A) (Y := host) incl)
      (val : t.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ host))
      (r : SystemArrow K oneVertexShape (P.scheme.asSystem hμ host)
        (P.scheme.asSystem t.hν t.host)),
      P.scheme.permitted (X := host) (Y := t.host) r ∧
      SystemArrow.comp incl r = t.incl ∧
      ∀ v i, r.onVertex v (val i).2 = (t.val i).2 := by
  classical
  have hν1 : t.ν ∈ P.eligible := t.hν
  let c : t.host.model.carrier ≃[K.τ] (P.G t.ν).carrier := SingleModelData.chart hν1 t.host
  have hc : K.Strong c.toEmbedding := strong_of_equiv K c t.host.mem
  let a1 : Language.Embedding K.τ A.model.carrier t.host.model.carrier :=
    t.incl.onVertex PUnit.unit
  have ha1 : K.Strong a1 := t.incl.onVertex_strong PUnit.unit
  let x1 : t.idx → t.host.model.carrier := fun i => t.host.val (t.val i)
  have hcA : Model.card A.model = μ := A.card
  have hc1 : Model.card t.host.model = t.ν := t.host.card
  have hμinf : aleph0 ≤ μ := SingleModelData.aleph0_le hμ
  have hμν : μ ≤ t.ν := by
    have h := Cardinal.mk_le_of_injective a1.injective
    have e1 : #A.model.carrier = μ := hcA
    have e2 : #t.host.model.carrier = t.ν := hc1
    rwa [e1, e2] at h
  let S : Set (P.G t.ν).carrier := Set.range (fun a => c (a1 a)) ∪ Set.range (fun i => c (x1 i))
  have hS : #S ≤ μ := by
    refine (mk_union_le _ _).trans ?_
    refine (add_le_add mk_range_le mk_range_le).trans ?_
    have h1 : #A.model.carrier = μ := hcA
    rw [h1]
    exact (add_le_add_right hidx μ).trans (add_eq_self hμinf).le
  have hJ : μ ≤ #(lvlOrder t.ν) := by
    rw [mk_lvlOrder (SingleModelData.aleph0_le hν1)]; exact hμν
  obtain ⟨I, hIμ, hIS⟩ := infra_612_small_support P.E hμinf hJ S hS
  have : Nonempty I := by
    rw [← Cardinal.mk_ne_zero_iff, hIμ]
    exact (aleph0_pos.trans_le hμinf).ne'
  let ι : I ↪o lvlOrder t.ν := OrderEmbedding.subtype (· ∈ I)
  have hpre : ∀ x ∈ S, ∃ y, P.E.map ι y = x := fun x hx =>
    ⟨_, infra_612_map_restrict P.E I x (hIS x hx)⟩
  have hB0 : K.Mem (P.E.obj I) := P.hE _
  have hcB0 : Model.card (P.E.obj I) = μ := SingleModelData.card_obj_eq hμ _ hIμ
  have hιs : K.Strong (P.E.map ι) := P.E.map_strong ι
  let f0 : Language.Embedding K.τ A.model.carrier (P.E.obj I).carrier :=
    factorEmbedding (c.toEmbedding.comp a1) (P.E.map ι) (fun a => hpre _ (Or.inl ⟨a, rfl⟩))
  have hf0 : ∀ a, P.E.map ι (f0 a) = c (a1 a) := fun a =>
    factorEmbedding_apply _ _ _ a
  have hf0s : K.Strong f0 :=
    strong_factorEmbedding _ _ (K.strong_trans _ _ ha1 hc) hιs _
  let d0 : t.idx → (P.E.obj I).carrier := fun i =>
    Classical.choose (hpre _ (Or.inr ⟨i, rfl⟩))
  have hd0 : ∀ i, P.E.map ι (d0 i) = c (x1 i) := fun i =>
    Classical.choose_spec (hpre _ (Or.inr ⟨i, rfl⟩))
  let host : SMObject K μ := SMObject.ofModel (P.E.obj I) hB0 hcB0
  let ψ : (P.E.obj I).carrier ≃[K.τ] host.model.carrier := SMObject.ofModelEquiv _ hB0 hcB0
  have hψ : K.Strong ψ.toEmbedding := strong_of_equiv K ψ hB0
  have hψs : K.Strong ψ.symm.toEmbedding := strong_of_equiv K ψ.symm host.mem
  let r : Language.Embedding K.τ host.model.carrier t.host.model.carrier :=
    c.symm.toEmbedding.comp ((P.E.map ι).comp ψ.symm.toEmbedding)
  have hr : K.Strong r := K.strong_trans _ _ (K.strong_trans _ _ hψs hιs)
    (strong_of_equiv K c.symm (P.mem_G _))
  have hrd : ∀ i, r (ψ (d0 i)) = x1 i := fun i => by
    change c.symm (P.E.map ι (ψ.symm (ψ (d0 i)))) = x1 i
    rw [ψ.symm_apply_apply, hd0]; exact c.symm_apply_apply _
  have hrf : ∀ a, r (ψ (f0 a)) = a1 a := fun a => by
    change c.symm (P.E.map ι (ψ.symm (ψ (f0 a)))) = a1 a
    rw [ψ.symm_apply_apply, hf0]; exact c.symm_apply_apply _
  let incl : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ host) :=
    oneVertexArrow (ψ.toEmbedding.comp f0) (K.strong_trans _ _ hf0s hψ)
  let val : t.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ host) :=
    fun i => ⟨PUnit.unit, ψ (d0 i)⟩
  refine ⟨host, incl, trivial, val, oneVertexArrow r hr, trivial, ?_, ?_⟩
  · apply SystemArrow.ext
    intro v
    refine DFunLike.ext _ _ fun x => ?_
    have hv : v = PUnit.unit := Subsingleton.elim _ _
    subst hv
    change r (ψ (f0 x)) = a1 x
    exact hrf x
  · intro v i
    change r (ψ (d0 i)) = (t.val i).2
    rw [hrd]
    rfl

/-- **Galois transitivity with the last host at the base level (proved).** First and middle
hosts at any eligible levels; tests pass through the middle host (`to_sameD`, `D.trans`) and
`infra_612_same_galois_left_large` concludes. -/
theorem infra_612_galois_trans_last_base
    {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {t1 t2 t3 : TupleOver K oneVertexShape P.scheme hμ A}
    {e12 : t1.idx ≃ t2.idx} {e32 : t3.idx ≃ t2.idx}
    (h12 : SameGaloisType t1 t2 e12 (Equiv.refl t2.idx))
    (h32 : SameGaloisType t2 t3 (Equiv.refl t2.idx) e32)
    (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hσμ : σ < μ)
    (hidx : #t1.idx ≤ σ) (hν3 : t3.ν = μ) :
    SameGaloisType t1 t3 (e12.trans e32.symm) (Equiv.refl t3.idx) := by
  have hL : ClosedLevel K P.E P.D P.g μ := by
    have : CategoricalUnbounded K := P.D.categoricalUnbounded
    exact ClosedLevel.of_closurePoint P.tester hμ.1 hμ.2
  apply infra_612_same_galois_left_large t1 t3 (e12.trans e32.symm) σ hσ hσμ hidx hν3 hL
  intro β hβ ρ0 hρinf hρμ params hjnt h0 h1
  have hμ2 : μ ≤ Model.card t2.host.model := by
    have h : #A.model.carrier ≤ #t2.host.model.carrier :=
      Cardinal.mk_le_of_injective (t2.incl.onVertex PUnit.unit).injective
    have e1 : #A.model.carrier = μ := A.card
    rw [e1] at h
    exact h
  have hμ1 : μ ≤ Model.card t1.host.model := by
    have h : #A.model.carrier ≤ #t1.host.model.carrier :=
      Cardinal.mk_le_of_injective (t1.incl.onVertex PUnit.unit).injective
    have e1 : #A.model.carrier = μ := A.card
    rw [e1] at h
    exact h
  have h2 : P.D.t ρ0 ≤ Model.card t2.host.model :=
    (P.t_lt hμ hρinf hρμ).le.trans hμ2
  have h23 : #t3.idx = #t2.idx := Cardinal.mk_congr e32
  have hj2 : #t2.idx + #β ≤ ρ0 := by simpa [h23] using hjnt
  have hab := SameGaloisType.to_sameD h12 params ρ0 hρinf (by simpa using hj2) h0 h2
  have hbc := SameGaloisType.to_sameD h32 params ρ0 hρinf (by simpa using hj2) h2 h1
  have hmid := P.D.trans hj2 t1.host.mem t2.host.mem t3.host.mem h0 h2 h1 _ _ _
    (by simpa [Equiv.refl_symm] using hab) (by simpa [Equiv.refl_symm] using hbc)
  have hc3 : Model.card t3.host.model = μ := by simpa [hν3] using t3.host.card
  let σ' : Cardinal.{u} := max ρ0 (ls K)
  have hσ'μ : σ' < μ := max_lt hρμ (P.ls_lt hμ)
  have hσ'inf : aleph0 ≤ σ' := hρinf.trans (le_max_left _ _)
  have ht' : P.D.t σ' ≤ μ := (P.t_lt hμ hσ'inf hσ'μ).le
  let hι : (t3.idx ⊕ β) → (t2.idx ⊕ β) := Sum.map e32 id
  have hL1 := P.D.same_relevel hj2 hρinf hρinf (le_max_left ρ0 (ls K)) (le_max_left ρ0 (ls K))
    (le_max_right ρ0 (ls K)) t1.host.mem t3.host.mem h0 h1
    (ht'.trans hμ1) (ht'.trans hc3.ge) h0 h1 _ _ hmid hjnt hι
  convert hL1 using 1
  · funext c
    cases c with
    | inl k =>
      dsimp [hι, Sum.map]
      rfl
    | inr b =>
      dsimp [hι, Sum.map]
      exact congrArg (fun v => t1.incl.onVertex v (params b)) (Subsingleton.elim _ _)
  · funext c
    cases c with
    | inl k =>
      change t3.host.val (t3.val k) = t3.host.val (t3.val (e32.symm (e32 k)))
      rw [Equiv.symm_apply_apply]
    | inr b =>
      dsimp [hι, Sum.map]
      exact congrArg (fun v => t3.incl.onVertex v (params b)) (Subsingleton.elim _ _)

/-- **Embedding clause of Theorem 7.9 into an ambient above the level of `X` (proved).** Take a
level-`μ` copy `N0 → N` over `X` of the realization `b'` (`infra_612_exists_level_copy_arrow`),
identify `(Y, b)` with the copy by Galois transitivity through `p` and `N`
(`infra_612_galois_trans_last_base`, twice), embed `Y` into `N0` (Prop 7.5 (1),
`infra_75_embed`) and compose with `N0 → N`. -/
theorem infra_79_primeness_mixed (P : SingleModelData K) :
    infra_79_primeness_mixed_statement P := by
  intro μ hμ X p hfin Y f hf b hAll hp ν hν N g hg b' _hμν hN
  have hlt : ℵ₀ < μ := P.aleph0_lt hμ
  have hidx : #p.idx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite p.idx).le
  let t : TupleOver K oneVertexShape P.scheme hμ X := ⟨ν, hν, N, g, hg, p.idx, b'⟩
  obtain ⟨N0, incl0, hincl0, val0, r, _hr, hcomp, hval⟩ :=
    infra_612_exists_level_copy_arrow t (hidx.trans (P.aleph0_le hμ))
  let c : TupleOver K oneVertexShape P.scheme hμ X := ⟨μ, hμ, N0, incl0, hincl0, p.idx, val0⟩
  have hct : SameGaloisType c t (Equiv.refl p.idx) (Equiv.refl p.idx) := by
    refine ⟨ν, hν, N, r, SystemArrow.refl _, trivial, trivial, ?_, ?_⟩
    · intro v
      have h := congrArg (fun a => SystemArrow.onVertex a v) hcomp
      refine DFunLike.ext _ _ fun x => ?_
      have hx := DFunLike.congr_fun h x
      exact hx
    · intro i
      have hv : (val0 i).1 = (b' i).1 := Subsingleton.elim _ _
      change (⟨(val0 i).1, r.onVertex (val0 i).1 (val0 i).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hν N)) = ⟨(b' i).1, (b' i).2⟩
      rw [hval]
      rw [hv]
  have h1 : SameGaloisType t (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) :=
    infra_612_galois_trans_last_base (t1 := t) (t2 := p) (t3 := asTuple f hf b)
      (e12 := Equiv.refl p.idx) (e32 := Equiv.refl p.idx) hN.symm hp ℵ₀ le_rfl hlt hidx rfl
  have h2 : SameGaloisType c (asTuple f hf b) (Equiv.refl p.idx) (Equiv.refl p.idx) :=
    infra_612_galois_trans_last_base (t1 := c) (t2 := t) (t3 := asTuple f hf b)
      (e12 := Equiv.refl p.idx) (e32 := Equiv.refl p.idx) hct h1 ℵ₀ le_rfl hlt hidx rfl
  obtain ⟨h0, _hh0, hcomp0, hb0⟩ := infra_75_embed hμ X Y N0 f hf incl0 hincl0 b val0
    (hidx.trans_lt hlt) h2.symm hAll
  refine ⟨SystemArrow.comp h0 r, trivial, ?_, ?_⟩
  · rw [← SystemArrow.comp_assoc, hcomp0]
    exact hcomp
  · intro i
    change r.onVertex (b i).1 (h0.onVertex (b i).1 (b i).2) = (b' i).2
    rw [hb0 i]
    exact hval _ i

/-- **Theorem 7.9 from its existence clause (proved).** -/
theorem infra_79_of_existence (P : SingleModelData K) (h : infra_79_existence_statement P) :
    theorem_7_9_statement P :=
  infra_79_assemble P ⟨h, infra_79_primeness_mixed P⟩

end AEC
