module

public import AEC.Section7.Theorem713Products

@[expose] public section

/-!
# Theorem 7.13, clause (1a) for lists of length at most the level (cycle 90)

`infra_713_unique_short`: at the 7.12 levels, a well-ordered product-independent list of finite
tuples with `|δ| ≤ μ` and total length `≤ μ` has its whole type determined by its marginals among
product-independent lists of finite tuples (any index bijection; the order is transported).
Lemma 7.12 (1) supplies witnessing chains for both lists, Lemma 7.12 (2) identifies the wholes.
-/

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- **Theorem 7.13 (1a), `|δ| ≤ μ` (proved, cycle 90; level-wise at the 7.12 levels, cycle 91).** -/
theorem infra_713_unique_short (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hl : μ ∈ infra_712_levels P) (X : P.scheme.Object μ hμ)
    (L L' : TupleList P.scheme hμ X) [LinearOrder L.δ] [L.FiniteEach]
    [WellFoundedLT L.δ] [L'.FiniteEach] (e : L.δ ≃ L'.δ)
    (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i))
    (hδ : #L.δ ≤ μ) (hS1 : #(Σ i, L.indexAt i) ≤ μ)
    (hPI : ProductIndependentTied L) (hPI' : ProductIndependentTied L')
    (hm : ∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) :
    SameGaloisType L.whole L'.whole (Equiv.sigmaCongr e ei) (Equiv.refl _) := by
  obtain ⟨ht, hc, hw⟩ := hl
  have hw0 : ℵ₀ ≤ infra_75_wide P ℵ₀ := le_self_add
  have h0lt : ℵ₀ < μ := hw0.trans_lt hw
  have h0 : μ ∈ recursionClosedLevels P ℵ₀ := infra_712_recursionClosed_of_615 hc le_rfl h0lt
  have hex := lemma_7_12_existence P hμ ht hc h0 (Order.succ_le_of_lt h0lt)
    (infra_712_recursionClosed_of_615 hc hw0 hw) (Order.succ_le_of_lt hw) X
  letI : LinearOrder L'.δ := LinearOrder.lift' e.symm e.symm.injective
  let eo : L.δ ≃o L'.δ :=
    { e with
      map_rel_iff' := fun {a b} => by
        show e.symm (e a) ≤ e.symm (e b) ↔ a ≤ b
        simp }
  haveI : WellFoundedLT L'.δ := eo.symm.toOrderEmbedding.wellFoundedLT
  have hδ' : #L'.δ ≤ μ := (Cardinal.mk_congr e).symm.le.trans hδ
  have hS2 : #(Σ i, L'.indexAt i) ≤ μ :=
    (Cardinal.mk_congr (Equiv.sigmaCongr e ei)).symm.le.trans hS1
  obtain ⟨C, -⟩ := hex L hδ hPI
  obtain ⟨C', -⟩ := hex L' hδ' hPI'
  have hb : ∀ i, #(L.indexAt i) < μ := fun i => haveI := L.finite_each i
    (Cardinal.lt_aleph0_of_finite _).trans h0lt
  have hM := infra_712u_marks P hμ ⟨ht, hc, hw⟩ X L L' eo ei hb hS1 hS2 C C' hm
  have hA' : SameGaloisType L.whole C.marksWhole (Equiv.sigmaCongr e ei)
      (Equiv.sigmaCongr e ei) :=
    infra_612_sameGalois_trans_equiv C.marksWhole_sameGalois.symm (Equiv.sigmaCongr e ei)
  have h1 := infra_712_trans_level P hμ h0 _ _ _ rfl rfl rfl hA' hM
  exact infra_712_trans_level P hμ h0 _ _ _ rfl rfl rfl h1 C'.marksWhole_sameGalois

section Nonempty
variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
  {A : P.scheme.Object μ hμ}

/-- The sublist of nonempty entries. -/
def TupleList.nonemptyPart (L : TupleList P.scheme hμ A) : TupleList P.scheme hμ A where
  δ := {i : L.δ // Nonempty (L.indexAt i)}
  host := L.host
  incl := L.incl
  incl_arrow := L.incl_arrow
  indexAt k := L.indexAt k.1
  val k := L.val k.1

instance TupleList.nonemptyPart_finiteEach (L : TupleList P.scheme hμ A) [L.FiniteEach] :
    L.nonemptyPart.FiniteEach := ⟨fun k => L.finite_each k.1⟩

instance TupleList.nonemptyPart_linearOrder (L : TupleList P.scheme hμ A) [LinearOrder L.δ] :
    LinearOrder L.nonemptyPart.δ := inferInstanceAs (LinearOrder {i : L.δ // Nonempty (L.indexAt i)})

instance TupleList.nonemptyPart_wellFoundedLT (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
    [WellFoundedLT L.δ] : WellFoundedLT L.nonemptyPart.δ :=
  inferInstanceAs (WellFoundedLT {i : L.δ // Nonempty (L.indexAt i)})

/-- The whole list re-indexed by its nonempty entries. -/
def TupleList.nonemptyEquiv (L : TupleList P.scheme hμ A) :
    (Σ i, L.indexAt i) ≃ (Σ k : L.nonemptyPart.δ, L.nonemptyPart.indexAt k) where
  toFun p := ⟨⟨p.1, ⟨p.2⟩⟩, p.2⟩
  invFun q := ⟨q.1.1, q.2⟩
  left_inv p := rfl
  right_inv q := rfl

theorem TupleList.nonemptyPart_card_le (L : TupleList P.scheme hμ A) :
    #L.nonemptyPart.δ ≤ #(Σ i, L.indexAt i) := by
  classical
  refine Cardinal.mk_le_of_injective (f := fun k : L.nonemptyPart.δ =>
    (⟨k.1, Classical.choice k.2⟩ : Σ i, L.indexAt i)) ?_
  intro a b h
  exact Subtype.ext (congrArg Sigma.fst h)

theorem TupleList.nonemptyPart_productIndependent (L : TupleList P.scheme hμ A)
    (h : ProductIndependentTied L) : ProductIndependentTied L.nonemptyPart := by
  intro n ix hix
  exact h n (fun s => (ix s).1) (fun a b hab => hix (Subtype.ext hab))

/-- Transport of `SameGaloisType` from the nonempty part to the whole list (left side). -/
theorem TupleList.sameGalois_of_nonemptyPart_left (L : TupleList P.scheme hμ A)
    {t : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    (e1 : (Σ k : L.nonemptyPart.δ, L.nonemptyPart.indexAt k) ≃ ι) (e2 : t.idx ≃ ι)
    (H : SameGaloisType L.nonemptyPart.whole t e1 e2) :
    SameGaloisType L.whole t (L.nonemptyEquiv.trans e1) e2 := by
  obtain ⟨ρ, hρ, top, f1, f2, h1, h2, hc, hv⟩ := H
  exact ⟨ρ, hρ, top, f1, f2, h1, h2, hc, fun i => hv i⟩

/-- Transport of `SameGaloisType` from the nonempty part to the whole list (right side). -/
theorem TupleList.sameGalois_of_nonemptyPart_right (L : TupleList P.scheme hμ A)
    {t : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    (e1 : t.idx ≃ ι) (e2 : (Σ k : L.nonemptyPart.δ, L.nonemptyPart.indexAt k) ≃ ι)
    (H : SameGaloisType t L.nonemptyPart.whole e1 e2) :
    SameGaloisType t L.whole e1 (L.nonemptyEquiv.trans e2) := by
  obtain ⟨ρ, hρ, top, f1, f2, h1, h2, hc, hv⟩ := H
  exact ⟨ρ, hρ, top, f1, f2, h1, h2, hc, fun i => hv i⟩

end Nonempty

/-- **Theorem 7.13 (1a), all lengths (proved, cycle 91; was tip `infra_713_unique_long`).** Total
length at most the level, any `|δ|`: the nonempty entries form a sublist of size `≤ μ` with the
same whole type (`nonemptyPart`), to which `infra_713_unique_short` applies. -/
theorem infra_713_unique (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hl : μ ∈ infra_712_levels P) (X : P.scheme.Object μ hμ)
    (L L' : TupleList P.scheme hμ X) [LinearOrder L.δ] [L.FiniteEach]
    [WellFoundedLT L.δ] [L'.FiniteEach] (e : L.δ ≃ L'.δ)
    (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i))
    (hS1 : #(Σ i, L.indexAt i) ≤ μ)
    (hPI : ProductIndependentTied L) (hPI' : ProductIndependentTied L')
    (hm : ∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) :
    SameGaloisType L.whole L'.whole (Equiv.sigmaCongr e ei) (Equiv.refl _) := by
  have hne : ∀ i, Nonempty (L.indexAt i) ↔ Nonempty (L'.indexAt (e i)) := fun i =>
    ⟨fun ⟨a⟩ => ⟨ei i a⟩, fun ⟨b⟩ => ⟨(ei i).symm b⟩⟩
  let en : L.nonemptyPart.δ ≃ L'.nonemptyPart.δ :=
    { toFun := fun k => ⟨e k.1, (hne k.1).1 k.2⟩
      invFun := fun k => ⟨e.symm k.1, (hne (e.symm k.1)).2 (by rw [e.apply_symm_apply]; exact k.2)⟩
      left_inv := fun k => Subtype.ext (e.symm_apply_apply k.1)
      right_inv := fun k => Subtype.ext (e.apply_symm_apply k.1) }
  let ein : ∀ k, L.nonemptyPart.indexAt k ≃ L'.nonemptyPart.indexAt (en k) := fun k => ei k.1
  have hδ : #L.nonemptyPart.δ ≤ μ := L.nonemptyPart_card_le.trans hS1
  have hS2 : #(Σ k, L.nonemptyPart.indexAt k) ≤ μ :=
    (Cardinal.mk_congr L.nonemptyEquiv).symm.le.trans hS1
  have Hn := infra_713_unique_short P hμ hl X L.nonemptyPart L'.nonemptyPart en ein hδ hS2
    (L.nonemptyPart_productIndependent hPI) (L'.nonemptyPart_productIndependent hPI')
    (fun k => hm k.1)
  have H1 := L.sameGalois_of_nonemptyPart_left _ _ Hn
  have H2 := L'.sameGalois_of_nonemptyPart_right _ _ H1
  have H3 := infra_612_sameGalois_trans_equiv H2 L'.nonemptyEquiv.symm
  exact infra_712u_sg_congr_right (infra_712_sg_congr_left H3 (fun _ => rfl)) (fun _ => rfl)

/-- **Definition 7.7, tied form (cycle 90; widened to the English level quantifier, cycle 91).**
English: "A bounded marginal type `p` satisfies the continuity condition used here if the
following holds at every sufficiently closed eligible level to which `p` is freely lifted.
Suppose `X₀ ≤ X₁ ≤ ⋯ (i < δ)` is a continuous chain at that level, its union is an object at that
level, and a fixed realization `b` in a coupled extension satisfies
`tp(b/Xᵢ) = tp(b/X₀)^fr_{Xᵢ}` (`i < δ`). Then the same equality holds over the union. The type at
`X₀` is required to be the appropriate free lift of `p`."
Formalized: there is a tail `T` of eligible levels ("sufficiently closed") such that at every
`μ' ∈ T` with `μ ≤ μ'` (a level to which `p`, at level `μ`, is freely lifted), for every
continuous same-level chain at `μ'` (`SameLevelChain`, union an object at `μ'`), every base arrow
`A → X₀` (mixed level `μ → μ'`), and every realization `b` over the union at `μ'`: if `tp(b/X₀)` is
the tied free lift of `p` (`IsTiedFreeMixed`; for `μ' = μ` the shape of `IsTiedFree`) and
`tp(b/Xᵢ) = tp(b/X₀)^fr_{Xᵢ}` (tied) for every `i < δ`, then the same holds over the union. -/
def SatisfiesContinuityTied {K : AbstractElementaryClass.{u}} {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}
    (p : TupleOver K oneVertexShape P.scheme hμ A) : Prop :=
  ∃ T, ∃ hT : Tail P.eligible T, ∀ μ' (hμ' : μ' ∈ T), μ ≤ μ' →
  ∀ (C : SameLevelChain P (Tail.mem hT hμ'))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A)
      (P.scheme.asSystem (Tail.mem hT hμ') (C.obj 0 C.hlim.1)))
    (b : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ') C.unionObj) (e : p.idx ≃ b.idx),
    b.ν = μ' →
    IsTiedFreeMixed g p (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) e →
    (∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))
        (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1))
        (b.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)) →
    IsTiedFree (C.toUnion 0 C.hlim.1)
      (b.restrict (C.toUnion 0 C.hlim.1) (C.toUnion_arrow 0 C.hlim.1)) b (Equiv.refl _)

/-- **Theorem 7.13 (1b), level-wise (statement; open tip `infra_713_lift`).** -/
def infra_713_lift_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_712_levels P →
    ∀ (X : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ X) [LinearOrder L.δ] [L.FiniteEach]
      [WellFoundedLT L.δ], ProductIndependentTied L → #(Σ i, L.indexAt i) < μ →
        (∀ (B : P.scheme.Object μ hμ)
            (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ B))
            (hf : P.scheme.permitted (X := X) (Y := B) f)
            (q : TupleOver K oneVertexShape P.scheme hμ B)
            (eq : L.whole.idx ≃ q.idx),
          IsTiedFree f L.whole q eq → q.ν = μ →
          (∀ (n : ℕ) (ix : Fin n → L.δ), Function.Injective ix →
            ∃ (joint : TupleOver K oneVertexShape P.scheme hμ B)
              (E : (Σ s, ((q.reindex (fun a : L.indexAt (ix s) => eq ⟨ix s, a⟩))).idx) ≃
                joint.idx),
              IsFiniteProductTied n (fun s => q.reindex (fun a : L.indexAt (ix s) => eq ⟨ix s, a⟩))
                joint E ∧
              SameGaloisType
                (q.reindex (fun p : Σ s : Fin n, L.indexAt (ix s) => eq ⟨ix p.1, p.2⟩)) joint E
                (Equiv.refl _)) ∧
          ∀ (q' : TupleOver K oneVertexShape P.scheme hμ B) (eq' : q.idx ≃ q'.idx),
            q'.ν = μ →
            (∀ (ι : Type u) [Finite ι] (ix : ι → q.idx), Function.Injective ix →
              SameGaloisType (q.reindex ix) (q'.reindex (fun s => eq' (ix s)))
                (Equiv.refl _) (Equiv.refl _)) →
            SameGaloisType q q' eq' (Equiv.refl _))

/-- **Theorem 7.13 (1b), product independence of the tied free lift (statement; open tip
`infra_713_lift_pi`).** English proof: "The finite projections of a free lift are the free lifts of
the finite projections, by Proposition 6.12. They are therefore the required products of the
lifted marginal types." -/
def infra_713_lift_pi_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_712_levels P →
    ∀ (X : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ X) [LinearOrder L.δ] [L.FiniteEach]
      [WellFoundedLT L.δ], ProductIndependentTied L → #(Σ i, L.indexAt i) < μ →
        ∀ (B : P.scheme.Object μ hμ)
            (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ B))
            (hf : P.scheme.permitted (X := X) (Y := B) f)
            (q : TupleOver K oneVertexShape P.scheme hμ B)
            (eq : L.whole.idx ≃ q.idx),
          IsTiedFree f L.whole q eq → q.ν = μ →
   ∀ (n : ℕ) (ix : Fin n → L.δ), Function.Injective ix →
             ∃ (joint : TupleOver K oneVertexShape P.scheme hμ B)
               (E : (Σ s, ((q.reindex (fun a : L.indexAt (ix s) => eq ⟨ix s, a⟩))).idx) ≃
                 joint.idx),
               IsFiniteProductTied n (fun s => q.reindex (fun a : L.indexAt (ix s) => eq ⟨ix s, a⟩))
                 joint E ∧
               SameGaloisType
                 (q.reindex (fun p : Σ s : Fin n, L.indexAt (ix s) => eq ⟨ix p.1, p.2⟩)) joint E
                 (Equiv.refl _)

/-- **Theorem 7.13 (1b), the tied free lift is determined by its finite data (statement; open tip
`infra_713_lift_det`).** English proof: "Applying witnessed uniqueness at the receiving base". -/
def infra_713_lift_det_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_712_levels P →
    ∀ (X : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ X) [LinearOrder L.δ] [L.FiniteEach]
      [WellFoundedLT L.δ], ProductIndependentTied L → #(Σ i, L.indexAt i) < μ →
        ∀ (B : P.scheme.Object μ hμ)
            (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ B))
            (hf : P.scheme.permitted (X := X) (Y := B) f)
            (q : TupleOver K oneVertexShape P.scheme hμ B)
            (eq : L.whole.idx ≃ q.idx),
          IsTiedFree f L.whole q eq → q.ν = μ →
          ∀ (q' : TupleOver K oneVertexShape P.scheme hμ B) (eq' : q.idx ≃ q'.idx),
            q'.ν = μ →
            (∀ (ι : Type u) [Finite ι] (ix : ι → q.idx), Function.Injective ix →
              SameGaloisType (q.reindex ix) (q'.reindex (fun s => eq' (ix s)))
                (Equiv.refl _) (Equiv.refl _)) →
            SameGaloisType q q' eq' (Equiv.refl _)

/-- **Theorem 7.13 (1b) from its two halves (proved glue, cycle 91).** -/
theorem infra_713_lift_of_parts (P : SingleModelData K) (h1 : infra_713_lift_pi_statement P)
    (h2 : infra_713_lift_det_statement P) : infra_713_lift_statement P :=
  fun hμ hl X L _ _ _ hPI hS B f hf q eq hq hqν =>
    ⟨h1 hμ hl X L hPI hS B f hf q eq hq hqν, h2 hμ hl X L hPI hS B f hf q eq hq hqν⟩

/-- **Theorem 7.13 (2), level-wise (statement; open tip `infra_713_continuity`).** -/
def infra_713_continuity_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_712_levels P →
    ∀ (X : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ X) [LinearOrder L.δ] [L.FiniteEach]
      [WellFoundedLT L.δ], ProductIndependentTied L → #(Σ i, L.indexAt i) < μ →
        SatisfiesContinuityTied L.whole

/-- **Theorem 7.13 (3), level-wise (statement; open tip `infra_713_realize`).** -/
def infra_713_realize_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_712_levels P →
    ∀ (X : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ X) [LinearOrder L.δ] [L.FiniteEach]
      [WellFoundedLT L.δ], ProductIndependentTied L → #(Σ i, L.indexAt i) < μ →
        (∃ (Y : P.scheme.Object μ hμ)
          (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
          (b : L.whole.idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)),
          AllDominated f trivial L.whole.idx b ∧
          SameGaloisType L.whole (asTuple f trivial b) (Equiv.refl _) (Equiv.refl _) ∧
          ∃ (N : P.scheme.Object μ hμ)
            (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ L.host)
              (P.scheme.asSystem hμ N))
            (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ N)),
            (∀ v, (g.onVertex v).comp (f.onVertex v) = (h.onVertex v).comp (L.incl.onVertex v)) ∧
            ∀ a, g.mapOcc (b a) = h.mapOcc (L.whole.val a))

/-- **Finite products from tied free factor and selection lifts (proved, cycle 92).** For a PI
list over `X` and an injective selection `ix`, if `qs s` are tied free lifts of the factors
`L.one (ix s)` and `qJ` one of the selection `L.subConcat n ix` along a permitted `f : X → B`
(all at the level), then `qJ` is the finite tied product of the `qs s`. -/
theorem infra_713_pi_core (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (hl : μ ∈ infra_712_levels P)
    (X : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ X) [LinearOrder L.δ] [L.FiniteEach]
    (hPI : ProductIndependentTied L) (hS : #(Σ i, L.indexAt i) < μ)
    (B : P.scheme.Object μ hμ)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := X) (Y := B) f)
    (n : ℕ) (ix : Fin n → L.δ) (hinj : Function.Injective ix)
    (qs : Fin n → TupleOver K oneVertexShape P.scheme hμ B)
    (es : ∀ s, L.indexAt (ix s) ≃ (qs s).idx) (hqs : ∀ s, (qs s).ν = μ)
    (hTs : ∀ s, IsTiedFree f (L.one (ix s)) (qs s) (es s))
    (qJ : TupleOver K oneVertexShape P.scheme hμ B) (eJ : (Σ s, L.indexAt (ix s)) ≃ qJ.idx)
    (hqJ : qJ.ν = μ) (hTJ : IsTiedFree f (L.subConcat n ix) qJ eJ) :
    IsFiniteProductTied n qs qJ ((Equiv.sigmaCongrRight es).symm.trans eJ) := by
  classical
  obtain ⟨ht, hc, hw⟩ := hl
  have hw0 : ℵ₀ ≤ infra_75_wide P ℵ₀ := le_self_add
  have h0lt : ℵ₀ < μ := hw0.trans_lt hw
  set σ : Cardinal.{u} := max ℵ₀ #(Σ i, L.indexAt i) with hσdef
  have hσ : ℵ₀ ≤ σ := le_max_left _ _
  have hσlt : σ < μ := max_lt h0lt hS
  have hrec : μ ∈ recursionClosedLevels P σ := infra_712_recursionClosed_of_615 hc hσ hσlt
  have hσμ : Order.succ σ ≤ μ := Order.succ_le_of_lt hσlt
  have hfin : ∀ s, Finite (L.indexAt (ix s)) := fun s => L.finite_each _
  have hb : ∀ s, (L.one (ix s)).ν = μ ∧ #(L.one (ix s)).idx ≤ σ := fun s =>
    ⟨rfl, (Cardinal.lt_aleph0_of_finite (L.indexAt (ix s))).le.trans hσ⟩
  obtain ⟨joint0, E0, hF0, hS0⟩ := hPI n ix hinj
  have hfS : Finite (Σ s : Fin n, L.indexAt (ix s)) := inferInstance
  have hfJ0 : Finite joint0.idx := Finite.of_equiv (Σ s : Fin n, L.indexAt (ix s)) E0
  obtain ⟨joint0', eJ0, r0, hJ0ν, hr0, hR0⟩ := infra_712_level_copy joint0 (infra_712_card_le_fin hμ)
  have hQ1 := (infra_712_sameGalois_pull hr0 hR0 hS0.symm).symm
  have hlev0 := infra_712_finiteProduct_toLevel n (fun s => L.one (ix s)) hfin joint0 E0 hF0
    joint0' eJ0 r0 hr0 hR0
  have hQ2 : SameGaloisType joint0' (L.subConcat n ix) (eJ0.trans E0.symm) (Equiv.refl _) := by
    have h := infra_612_sameGalois_trans_equiv hQ1.symm E0.symm
    exact infra_712u_sg_congr_right (infra_712_sg_congr_left h (fun t => rfl))
      (fun t => E0.symm_apply_apply t)
  have hsub : #(L.subConcat n ix).idx < μ :=
    (Cardinal.lt_aleph0_of_finite (Σ s : Fin n, L.indexAt (ix s))).trans h0lt
  have hTJ' : IsTiedFree f joint0' qJ ((eJ0.trans E0.symm).trans eJ) :=
    infra_712u_tiedFree_base_sameGalois f (L.subConcat n ix) joint0' rfl hJ0ν hsub
      (eJ0.trans E0.symm) hQ2 _ _ hTJ
  have H := infra_713_finite_base_change P σ hσ hμ hrec hσμ f hf n (fun s => L.one (ix s)) hb
    joint0' (E0.trans eJ0.symm) hJ0ν hlev0 qs es hqs hTs qJ _ hqJ hTJ'
  have hE : (Equiv.sigmaCongrRight es).symm.trans
      ((E0.trans eJ0.symm).trans ((eJ0.trans E0.symm).trans eJ)) =
      (Equiv.sigmaCongrRight es).symm.trans eJ := by
    ext t
    show eJ (E0.symm (eJ0 (eJ0.symm (E0 _)))) = eJ _
    exact congrArg eJ ((congrArg E0.symm (eJ0.apply_symm_apply _)).trans (E0.symm_apply_apply _))
  exact hE ▸ H.toPlain n _ _ _

/-- **Theorem 7.13 (1b), product independence, for a permitted base arrow (proved, cycle 92).**
The level copy of the PI product of the selection (`infra_712_finiteProduct_toLevel`) is a level
finite product with the selection's type; the projections of `q` are tied free lifts of the
factors and of the selection (`infra_713_tiedFree_reindex`, transferred along the Galois
identification by `infra_712u_tiedFree_base_sameGalois`), so `infra_713_finite_base_change`
makes the projection of `q` the finite product of the factor projections. -/
theorem infra_713_lift_pi_permitted (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (hl : μ ∈ infra_712_levels P)
    (X : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ X) [LinearOrder L.δ] [L.FiniteEach]
    (hPI : ProductIndependentTied L) (hS : #(Σ i, L.indexAt i) < μ)
    (B : P.scheme.Object μ hμ)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := X) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B) (eq : L.whole.idx ≃ q.idx)
    (hq : IsTiedFree f L.whole q eq) (hqν : q.ν = μ)
    (n : ℕ) (ix : Fin n → L.δ) (hinj : Function.Injective ix) :
    ∃ (joint : TupleOver K oneVertexShape P.scheme hμ B)
      (E : (Σ s, ((q.reindex (fun a : L.indexAt (ix s) => eq ⟨ix s, a⟩))).idx) ≃ joint.idx),
      IsFiniteProductTied n (fun s => q.reindex (fun a : L.indexAt (ix s) => eq ⟨ix s, a⟩))
        joint E ∧
      SameGaloisType
        (q.reindex (fun p : Σ s : Fin n, L.indexAt (ix s) => eq ⟨ix p.1, p.2⟩)) joint E
        (Equiv.refl _) := by
  classical
  obtain ⟨ht, hc, hw⟩ := hl
  have hw0 : ℵ₀ ≤ infra_75_wide P ℵ₀ := le_self_add
  have h0lt : ℵ₀ < μ := hw0.trans_lt hw
  set σ : Cardinal.{u} := max ℵ₀ #(Σ i, L.indexAt i) with hσdef
  have hσ : ℵ₀ ≤ σ := le_max_left _ _
  have hσlt : σ < μ := max_lt h0lt hS
  have hrec : μ ∈ recursionClosedLevels P σ := infra_712_recursionClosed_of_615 hc hσ hσlt
  have hσμ : Order.succ σ ≤ μ := Order.succ_le_of_lt hσlt
  have hwhole : #L.whole.idx ≤ σ := le_max_right _ _
  have hfin : ∀ s, Finite (L.indexAt (ix s)) := fun s => L.finite_each _
  have hb : ∀ s, (L.one (ix s)).ν = μ ∧ #(L.one (ix s)).idx ≤ σ := fun s =>
    ⟨rfl, (Cardinal.lt_aleph0_of_finite (L.indexAt (ix s))).le.trans hσ⟩
  -- tied free lifts of the factors and of the selection
  have hTs : ∀ s, IsTiedFree f (L.one (ix s))
      (q.reindex (fun a : L.indexAt (ix s) => eq ⟨ix s, a⟩)) (Equiv.refl _) := fun s =>
    infra_713_tiedFree_reindex P σ hσ hμ hrec hσμ f hf L.whole rfl hwhole q eq hqν hq
      (fun a : L.indexAt (ix s) => (⟨ix s, a⟩ : Σ i, L.indexAt i)) sigma_mk_injective
  have hinjJ : Function.Injective
      (fun p : Σ s : Fin n, L.indexAt (ix s) => (⟨ix p.1, p.2⟩ : Σ i, L.indexAt i)) := by
    rintro ⟨s, a⟩ ⟨t, b⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := hinj h1
    simp only [heq_eq_eq] at h2
    subst h2; rfl
  have hTJ : IsTiedFree f (L.subConcat n ix)
      (q.reindex (fun p : Σ s : Fin n, L.indexAt (ix s) => eq ⟨ix p.1, p.2⟩)) (Equiv.refl _) :=
    infra_713_tiedFree_reindex P σ hσ hμ hrec hσμ f hf L.whole rfl hwhole q eq hqν hq _ hinjJ
  -- the level product over `X`
  obtain ⟨joint0, E0, hF0, hS0⟩ := hPI n ix hinj
  have hfS : Finite (Σ s : Fin n, L.indexAt (ix s)) := inferInstance
  have hfJ0 : Finite joint0.idx := Finite.of_equiv (Σ s : Fin n, L.indexAt (ix s)) E0
  obtain ⟨joint0', eJ0, r0, hJ0ν, hr0, hR0⟩ := infra_712_level_copy joint0 (infra_712_card_le_fin hμ)
  have hQ1 := (infra_712_sameGalois_pull hr0 hR0 hS0.symm).symm
  have hlev0 := infra_712_finiteProduct_toLevel n (fun s => L.one (ix s)) hfin joint0 E0 hF0
    joint0' eJ0 r0 hr0 hR0
  have hQ2 : SameGaloisType joint0' (L.subConcat n ix) (eJ0.trans E0.symm) (Equiv.refl _) := by
    have h := infra_612_sameGalois_trans_equiv hQ1.symm E0.symm
    exact infra_712u_sg_congr_right (infra_712_sg_congr_left h (fun t => rfl))
      (fun t => E0.symm_apply_apply t)
  have hsub : #(L.subConcat n ix).idx < μ :=
    (Cardinal.lt_aleph0_of_finite (Σ s : Fin n, L.indexAt (ix s))).trans h0lt
  have hTJ' : IsTiedFree f joint0'
      (q.reindex (fun p : Σ s : Fin n, L.indexAt (ix s) => eq ⟨ix p.1, p.2⟩))
      ((eJ0.trans E0.symm).trans (Equiv.refl _)) :=
    infra_712u_tiedFree_base_sameGalois f (L.subConcat n ix) joint0' rfl hJ0ν hsub
      (eJ0.trans E0.symm) hQ2 _ _ hTJ
  have H := infra_713_finite_base_change P σ hσ hμ hrec hσμ f hf n (fun s => L.one (ix s)) hb
    joint0' (E0.trans eJ0.symm) hJ0ν hlev0
    (fun s => q.reindex (fun a : L.indexAt (ix s) => eq ⟨ix s, a⟩)) (fun s => Equiv.refl _)
    (fun s => hqν) hTs
    (q.reindex (fun p : Σ s : Fin n, L.indexAt (ix s) => eq ⟨ix p.1, p.2⟩)) _ hqν hTJ'
  refine ⟨_, _, H.toPlain n _ _ _, ?_⟩
  refine infra_712_sg_congr_left (SameGaloisType.refl _) (fun t => ?_)
  show t = E0.symm (eJ0 (eJ0.symm (E0 t)))
  exact ((congrArg E0.symm (eJ0.apply_symm_apply (E0 t))).trans (E0.symm_apply_apply t)).symm

/-- **Theorem 7.13 (1b), determinacy, for a permitted base arrow (proved, cycle 92).** English:
"Applying witnessed uniqueness at the receiving base". The coordinates of `q` and of `q'` form
lists over `B` indexed like `L`; the first is PI by `infra_713_lift_pi_permitted`, the second by
`infra_713_pi_core` (its finite projections have the types of those of `q`, hence are tied free
lifts too, `infra_79_tiedFreeMixed_right_congr`); 7.13(1a) at `B` (`infra_713_unique`) gives
equal whole types. -/
theorem infra_713_lift_det_permitted (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (hl : μ ∈ infra_712_levels P)
    (X : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ X) [LinearOrder L.δ] [L.FiniteEach]
    [WellFoundedLT L.δ] (hPI : ProductIndependentTied L) (hS : #(Σ i, L.indexAt i) < μ)
    (B : P.scheme.Object μ hμ)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := X) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B) (eq : L.whole.idx ≃ q.idx)
    (hq : IsTiedFree f L.whole q eq) (hqν : q.ν = μ)
    (q' : TupleOver K oneVertexShape P.scheme hμ B) (eq' : q.idx ≃ q'.idx) (hq'ν : q'.ν = μ)
    (hfin : ∀ (ι : Type u) [Finite ι] (ix : ι → q.idx), Function.Injective ix →
      SameGaloisType (q.reindex ix) (q'.reindex (fun s => eq' (ix s)))
        (Equiv.refl _) (Equiv.refl _)) :
    SameGaloisType q q' eq' (Equiv.refl _) := by
  classical
  have hpi := infra_713_lift_pi_permitted P hμ hl X L hPI hS B f hf q eq hq hqν
  obtain ⟨ht, hc, hw⟩ := hl
  have hw0 : ℵ₀ ≤ infra_75_wide P ℵ₀ := le_self_add
  have h0lt : ℵ₀ < μ := hw0.trans_lt hw
  set σ : Cardinal.{u} := max ℵ₀ #(Σ i, L.indexAt i) with hσdef
  have hσ : ℵ₀ ≤ σ := le_max_left _ _
  have hσlt : σ < μ := max_lt h0lt hS
  have hrec : μ ∈ recursionClosedLevels P σ := infra_712_recursionClosed_of_615 hc hσ hσlt
  have hσμ : Order.succ σ ≤ μ := Order.succ_le_of_lt hσlt
  have hwhole : #L.whole.idx ≤ σ := le_max_right _ _
  -- tied free projections of `q'`
  have hT' : ∀ {ι : Type u} [Finite ι] (ρ : ι → L.whole.idx), Function.Injective ρ →
      IsTiedFree f (L.whole.reindex ρ) (q'.reindex (fun j => eq' (eq (ρ j)))) (Equiv.refl ι) := by
    intro ι _ ρ hρ
    have h1 := infra_713_tiedFree_reindex P σ hσ hμ hrec hσμ f hf L.whole rfl hwhole q eq hqν hq
      ρ hρ
    have h2 := hfin ι (fun j => eq (ρ j)) (eq.injective.comp hρ)
    have hlt : #(L.whole.reindex ρ).idx < μ := (Cardinal.lt_aleph0_of_finite ι).trans h0lt
    have hM : IsTiedFreeMixed f (L.whole.reindex ρ) (q.reindex (fun j => eq (ρ j)))
        (Equiv.refl ι) := h1
    have H := infra_79_tiedFreeMixed_right_congr (q := L.whole.reindex ρ)
      (qB := q.reindex (fun j => eq (ρ j))) (qB' := q'.reindex (fun j => eq' (eq (ρ j)))) f
      (Equiv.refl ι) (Equiv.refl ι) hM h2 hlt (le_of_eq hqν.symm) (le_of_eq hq'ν.symm)
    exact H
  have hinjJ : ∀ (n : ℕ) (ix : Fin n → L.δ), Function.Injective ix → Function.Injective
      (fun p : Σ s : Fin n, L.indexAt (ix s) => (⟨ix p.1, p.2⟩ : Σ i, L.indexAt i)) := by
    intro n ix hinj
    rintro ⟨s, a⟩ ⟨t, b⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := hinj h1
    simp only [heq_eq_eq] at h2
    subst h2; rfl
  obtain ⟨ν1, hν1, host1, incl1, hincl1, idx1, val1⟩ := q
  obtain ⟨ν2, hν2, host2, incl2, hincl2, idx2, val2⟩ := q'
  dsimp only at hqν hq'ν
  subst ν1 ν2
  let LB : TupleList P.scheme hμ B :=
    { δ := L.δ, host := host1, incl := incl1, incl_arrow := hincl1, indexAt := L.indexAt,
      val := fun i a => val1 (eq ⟨i, a⟩) }
  let LB' : TupleList P.scheme hμ B :=
    { δ := L.δ, host := host2, incl := incl2, incl_arrow := hincl2, indexAt := L.indexAt,
      val := fun i a => val2 (eq' (eq ⟨i, a⟩)) }
  letI : LinearOrder LB.δ := inferInstanceAs (LinearOrder L.δ)
  haveI : WellFoundedLT LB.δ := inferInstanceAs (WellFoundedLT L.δ)
  haveI : LB.FiniteEach := ⟨fun i => L.finite_each i⟩
  haveI : LB'.FiniteEach := ⟨fun i => L.finite_each i⟩
  have hPIB : ProductIndependentTied LB := fun n ix hinj => hpi n ix hinj
  have hPIB' : ProductIndependentTied LB' := by
    intro n ix hinj
    haveI : ∀ s, Finite (L.indexAt (ix s)) := fun s => L.finite_each _
    exact ⟨LB'.subConcat n ix, _,
      infra_713_pi_core P hμ ⟨ht, hc, hw⟩ X L hPI hS B f hf n ix hinj (fun s => LB'.one (ix s))
        (fun s => Equiv.refl _) (fun s => rfl)
        (fun s => haveI := L.finite_each (ix s)
          hT' (fun a : L.indexAt (ix s) => (⟨ix s, a⟩ : Σ i, L.indexAt i)) sigma_mk_injective)
        (LB'.subConcat n ix) (Equiv.refl _) rfl (hT' _ (hinjJ n ix hinj)),
      infra_712_sg_congr_left (SameGaloisType.refl _) (fun t => rfl)⟩
  have hm : ∀ i, SameGaloisType (LB.one i) (LB'.one ((Equiv.refl L.δ) i)) (Equiv.refl _)
      (Equiv.refl _) := fun i => haveI := L.finite_each i
    hfin (L.indexAt i) (fun a => eq ⟨i, a⟩) (eq.injective.comp sigma_mk_injective)
  have H := infra_713_unique P hμ ⟨ht, hc, hw⟩ B LB LB' (Equiv.refl _) (fun i => Equiv.refl _)
    hS.le hPIB hPIB' hm
  have H' := infra_712_sg_congr_left H (f' := Equiv.refl _) (fun t => rfl)
  obtain ⟨ρ, hρ, top, f1, f2, h1, h2, hcomm, hv⟩ := H'
  refine ⟨ρ, hρ, top, f1, f2, h1, h2, hcomm, fun k => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, k = eq' (eq i) := ⟨eq.symm (eq'.symm k), by simp⟩
  have hk : eq'.symm (eq' (eq i)) = eq i := eq'.symm_apply_apply _
  rw [hk]
  exact hv i

/-- **Theorem 7.13 (1b), product independence (proved, cycle 92; was tip `infra_713_lift_pi`).** -/
theorem infra_713_lift_pi (P : SingleModelData K) : infra_713_lift_pi_statement P :=
  fun hμ hl X L _ _ _ hPI hS B f hf q eq hq hqν n ix hinj =>
    infra_713_lift_pi_permitted P hμ hl X L hPI hS B f hf q eq hq hqν n ix hinj

/-- **Theorem 7.13 (1b), determinacy (proved, cycle 92; was tip `infra_713_lift_det`).** -/
theorem infra_713_lift_det (P : SingleModelData K) : infra_713_lift_det_statement P :=
  fun hμ hl X L _ _ _ hPI hS B f hf q eq hq hqν q' eq' hq'ν hfin =>
    infra_713_lift_det_permitted P hμ hl X L hPI hS B f hf q eq hq hqν q' eq' hq'ν hfin

/-- **Theorem 7.13 (1b) (proved glue, cycle 91).** -/
theorem infra_713_lift (P : SingleModelData K) : infra_713_lift_statement P :=
  infra_713_lift_of_parts P (infra_713_lift_pi P) (infra_713_lift_det P)

/-- **Theorem 7.13 (2) (open tip `infra_713_continuity`).** -/
theorem infra_713_continuity (P : SingleModelData K) : infra_713_continuity_statement P := by
  sorry

/-- **Theorem 7.13 (3) (open tip `infra_713_realize`; needs the general bounded-mark forms of
Prop 7.8 / Thm 7.9, cf. `infra_78_def77_bounded_marks`).** -/
theorem infra_713_realize (P : SingleModelData K) : infra_713_realize_statement P := by
  sorry

end
end AEC
