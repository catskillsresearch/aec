module

public import AEC.Section7.Lemma712Common

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
  fun hμ hl X L _ _ _ hPI hS B f q eq hq hqν =>
    ⟨h1 hμ hl X L hPI hS B f q eq hq hqν, h2 hμ hl X L hPI hS B f q eq hq hqν⟩

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

/-- **Theorem 7.13 (1b), product independence (open tip `infra_713_lift_pi`).** -/
theorem infra_713_lift_pi (P : SingleModelData K) : infra_713_lift_pi_statement P := by
  sorry

/-- **Theorem 7.13 (1b), determinacy (open tip `infra_713_lift_det`).** -/
theorem infra_713_lift_det (P : SingleModelData K) : infra_713_lift_det_statement P := by
  sorry

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
