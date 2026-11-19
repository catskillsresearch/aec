module

public import AEC.Section8.Layout84Single

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: the samples (cycle 101)

English (Lemma 8.3 proof, "The samples and their language"): "Let F be the template of C. At
arbitrarily high closed input levels choose a pair X = F(J) ≤ Y, Y ≃ F(Z), with Y all-dominated
over X + b. ... Proposition 6.15, in its presentation-invariant form, puts Y over X into
L = F(J + W)."
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- The first-segment order embedding `J ↪o J +lex W`. -/
def infra_83_inlLex (J W : Type u) [LinearOrder J] [LinearOrder W] : J ↪o Lex (J ⊕ W) :=
  OrderEmbedding.ofStrictMono (fun j => toLex (Sum.inl j)) (fun _ _ h => by simpa using h)

/-- **The samples of the Lemma 8.3 proof (P.scheme), core form.** On a tail of eligible levels:
for every well-order `J` of the level size `μ` and every order `W` such that `P.E(J +lex W)` has a
categoricity cardinality at least `t(μ)`, there is a marked pair `M` at level `μ` whose base is
`P.E(J)` (a bijective strong map `eX`), whose extension `Y` is a copy of `P.E(Z)` for every `Z`
of size `μ`, and whose extension embeds strongly into `L = P.E(J +lex W)` over the base (the
inclusion followed by the embedding is `P.E(J ↪ J + W)`). The marked pair is all-dominated over
`X + b` by definition. -/
theorem infra_83_samples_core (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∀ μ (_ : μ ∈ T) (J : Type u) [LinearOrder J] [WellFoundedLT J] [Nonempty J]
        (_ : #J = μ) (W : Type u) [LinearOrder W] [Nonempty W]
        (_ : Categorical K (Model.card (P.E.obj (Lex (J ⊕ W)))))
        (_ : P.D.t μ ≤ Model.card (P.E.obj (Lex (J ⊕ W)))),
        ∃ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ = μ ∧
          ∃ eX : Language.Embedding K.τ (P.E.obj J).carrier
              ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier,
            Function.Bijective eX ∧ K.Strong eX ∧
            (∀ (Z : Type u) [LinearOrder Z] [Nonempty Z], #Z = μ →
              Nonempty ((P.E.obj Z).carrier ≃[K.τ]
                ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier)) ∧
            ∃ F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
                (P.E.obj (Lex (J ⊕ W))).carrier,
              K.Strong F ∧
                ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map (infra_83_inlLex J W) x := by
  classical
  have := P.D.categoricalUnbounded
  obtain ⟨T, hT, H⟩ := infra_82_marked_pair_exists P Pr
  refine ⟨T, hT, fun μ hμ J _ _ _ hJ W _ _ hcat hWc => ?_⟩
  have hμe : μ ∈ P.eligible := Tail.mem hT hμ
  have hcJ : Model.card (P.E.obj J) = μ := SingleModelData.card_obj_eq hμe J hJ
  let X0 : SMObject K μ := SMObject.ofModel (P.E.obj J) (P.hE J) hcJ
  obtain ⟨M, hM, e, -, hbij⟩ := H μ hμ X0
  let φ := SMObject.ofModelEquiv (P.E.obj J) (P.hE J) hcJ
  let eX : Language.Embedding K.τ (P.E.obj J).carrier
      ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier :=
    (e.onVertex PUnit.unit).comp φ.toEmbedding
  have heX : Function.Bijective eX := (hbij PUnit.unit).comp φ.bijective
  have hsX : K.Strong eX :=
    K.strong_trans _ _ (strong_of_equiv K φ (P.hE J)) (e.onVertex_strong PUnit.unit)
  have hcY : Model.card ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit) = μ :=
    (SMObject.card M.Y).trans hM
  refine ⟨M, hM, eX, heX, hsX, fun Z _ _ hZ => ?_, ?_⟩
  · have hcat' := SingleModelData.categorical (P := P) hμe
    exact hcat'.unique_model (P.E.obj Z) _ (P.hE Z) ((P.scheme.asSystem M.hμ M.Y).inK PUnit.unit)
      (SingleModelData.card_obj_eq hμe Z hZ) hcY
  · have hL := infra_84_closedLevel_single P hμe
    let incl := (M.incl.onVertex PUnit.unit).comp eX
    have hstrong : K.Strong incl := K.strong_trans _ _ hsX (M.incl.onVertex_strong PUnit.unit)
    have hIμ : ∀ ρ, aleph0 ≤ ρ → ρ < μ → P.D.t ρ ≤ Model.card (P.E.obj J) :=
      fun ρ h1 h2 => (hL.t_lt h1 h2).le.trans hcJ.ge
    have hz := liftsTuple_of_base (hB := (P.scheme.asSystem M.hμ M.Y).inK PUnit.unit)
      (μ := μ) (D := P.D) hstrong hIμ (infra_83_inlLex J W) (PEmpty.elim : PEmpty.{u+1} → _)
    obtain ⟨F, hF, hFi, -⟩ := exists_strong_embedding_over hL hJ hstrong hcY
      (infra_83_inlLex J W) hcat hWc _ (by rw [Cardinal.mk_eq_zero]; exact lt_of_lt_of_le Cardinal.aleph0_pos (P.aleph0_le hμe)) _ hz
    exact ⟨F, hF, hFi⟩

/-- **The hypotheses on `W` in `infra_83_samples_core` are satisfiable.** For a well-order `J` of
an eligible size `μ`, some `W` makes `P.E(J +lex W)` of a categoricity cardinality at least
`t(μ)` (unbounded categoricity). -/
theorem infra_83_samples_order_exists (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμe : μ ∈ P.eligible) (J : Type u) [LinearOrder J] [Nonempty J] (hJ : #J = μ) :
    ∃ (W : Type u) (_ : LinearOrder W) (_ : Nonempty W),
      Categorical K (Model.card (P.E.obj (Lex (J ⊕ W)))) ∧
        P.D.t μ ≤ Model.card (P.E.obj (Lex (J ⊕ W))) := by
  have := P.D.categoricalUnbounded
  have hL := infra_84_closedLevel_single P hμe
  obtain ⟨κ, hκ, hcat⟩ := CategoricalUnbounded.unbounded (K := K) (max μ (P.D.t μ))
  have hμκ : μ ≤ κ := (le_max_left _ _).trans hκ
  have htκ : P.D.t μ ≤ κ := (le_max_right _ _).trans hκ
  have hκinf : aleph0 ≤ κ := hL.inf.trans hμκ
  have : Nonempty κ.ord.ToType := by
    rw [← Cardinal.mk_ne_zero_iff, mk_ord_toType]
    exact (lt_of_lt_of_le Cardinal.aleph0_pos hκinf).ne'
  have hsum : #(Lex (J ⊕ κ.ord.ToType)) = κ := by
    change #(J ⊕ κ.ord.ToType) = κ
    rw [mk_sum, lift_id, lift_id, hJ, mk_ord_toType]
    exact add_eq_right hκinf hμκ
  have : Nonempty (Lex (J ⊕ κ.ord.ToType)) := ⟨toLex (Sum.inl (Classical.arbitrary J))⟩
  have hc : Model.card (P.E.obj (Lex (J ⊕ κ.ord.ToType))) = κ :=
    orderPresentation_obj_card P.E hsum (hL.ls_lt.le.trans hμκ) hκinf
  refine ⟨κ.ord.ToType, inferInstance, inferInstance, ?_, ?_⟩
  · rw [hc]; exact hcat
  · rw [hc]; exact htκ

/-- **The retraction family of the samples (P.scheme).** English (Lemma 8.3 proof): "Include a
sort of retraction indices and an evaluation function for a family r_i : Y → X from Corollary
6.16." Every marked pair at a level closed for Proposition 6.15 carries an approximate retraction
family of its extension onto its base along the inclusion. -/
theorem infra_83_samples_retractions (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (M : MarkedPair K oneVertexShape P.scheme Pr) (hM : M.μ ∈ infra_615_closed P) :
    Nonempty (ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl) :=
  corollary_6_16_family P hM M.X M.Y M.incl

/-- **Padded dense orders exist (Lemma 8.3 proof).** English: "We may take J, Z, and a further
order W, to be padded dense orders. Padding means that the order has a well-ordered subset of its
own cardinality." Every infinite cardinal `μ` is the size of a dense linear order with a
well-ordered subset of size `μ` (`μ ×lex ℚ`). -/
theorem infra_83_padded_dense_exists (μ : Cardinal.{u}) (hμ : aleph0 ≤ μ) :
    ∃ (J : Type u) (_ : LinearOrder J), DenselyOrdered J ∧ #J = μ ∧
      ∃ S : Set J, #S = μ ∧ S.WellFoundedOn (· < ·) := by
  have : DenselyOrdered (ULift.{u} ℚ) :=
    ⟨fun a b h => by
      obtain ⟨c, h1, h2⟩ := exists_between (show a.down < b.down from h)
      exact ⟨⟨c⟩, h1, h2⟩⟩
  have : NoMaxOrder (ULift.{u} ℚ) :=
    ⟨fun a => ⟨⟨a.down + 1⟩, show a.down < a.down + 1 by linarith⟩⟩
  have : NoMinOrder (ULift.{u} ℚ) :=
    ⟨fun a => ⟨⟨a.down - 1⟩, show a.down - 1 < a.down by linarith⟩⟩
  let A := μ.ord.ToType
  have hd : DenselyOrdered (Lex (A × ULift.{u} ℚ)) := inferInstance
  refine ⟨Lex (A × ULift.{u} ℚ), inferInstance, hd, ?_, ?_⟩
  · change #(A × ULift.{u} ℚ) = μ
    rw [mk_prod, lift_id, lift_id, mk_ord_toType, mk_uLift, Cardinal.mk_denumerable, lift_aleph0]
    exact mul_eq_left hμ hμ aleph0_ne_zero
  · refine ⟨Set.range (fun a : A => toLex (a, (⟨0⟩ : ULift.{u} ℚ))), ?_, ?_⟩
    · rw [Cardinal.mk_range_eq _ (fun a b h => by simpa using congrArg (fun x => (ofLex x).1) h),
        mk_ord_toType]
    · refine (Set.wellFoundedOn_range).mpr ?_
      have hwf : WellFounded (fun a b : A => a < b) := wellFounded_lt
      refine Subrelation.wf ?_ hwf
      intro a b h
      change toLex (a, (⟨0⟩ : ULift.{u} ℚ)) < toLex (b, (⟨0⟩ : ULift.{u} ℚ)) at h
      rcases Prod.Lex.toLex_lt_toLex.mp h with h | ⟨_, h⟩
      · exact h
      · exact absurd h (lt_irrefl _)

/-- **The samples of the Lemma 8.3 proof (P.scheme), presentation-invariant strip form.** English:
"choose a pair X = F(J) ≤ Y, Y ≃ F(Z), with Y all-dominated over X + b. ... We may take J, Z, and
a further order W, to be padded dense orders ... W has many disjoint convex substrips, each of the
level size. Proposition 6.15, in its presentation-invariant form, puts Y over X into L = F(J + W)."
On the tail `infra_78_closedTail P ∩ infra_615_closed P`, for **every** nonempty linear order `J`
of the level size (dense padded orders allowed): a marked pair with base `P.E(J)` (bijective strong
`eX`), extension a copy of `P.E(Z)` for every `Z` of the level size, and an order `J⁺ ⊇ J` with a
fresh convex strip carrying countably many disjoint convex level-size fibers (Proposition 6.15)
such that the extension embeds strongly into `L = P.E(J⁺)` over the base. -/
theorem infra_83_samples_strip (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {μ : Cardinal.{u}}
    (hμ : μ ∈ infra_78_closedTail P ∩ infra_615_closed P)
    (J : Type u) [LinearOrder J] [Nonempty J] (hJ : #J = μ) :
    ∃ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ = μ ∧
      ∃ eX : Language.Embedding K.τ (P.E.obj J).carrier
          ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier,
        Function.Bijective eX ∧ K.Strong eX ∧
        (∀ (Z : Type u) [LinearOrder Z] [Nonempty Z], #Z = μ →
          Nonempty ((P.E.obj Z).carrier ≃[K.τ]
            ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier)) ∧
        ∃ (Jplus : Type u) (_ : LinearOrder Jplus) (_ : Nonempty Jplus) (emb : J ↪o Jplus)
          (strip : Set Jplus) (V : ℕ → Set Jplus),
          #Jplus = μ ∧ IsConvexRegion strip ∧ #strip = μ ∧
          (∀ n, IsConvexRegion (V n) ∧ #(V n) = μ ∧ V n ⊆ strip) ∧
          Pairwise (Function.onFun Disjoint V) ∧
          ∃ F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
              (P.E.obj Jplus).carrier,
            K.Strong F ∧ ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x := by
  classical
  have htail := infra_79_tail P
  have hμe : μ ∈ P.eligible := hμ.1.1
  have hcJ : Model.card (P.E.obj J) = μ := SingleModelData.card_obj_eq hμe J hJ
  let X0 : SMObject K μ := SMObject.ofModel (P.E.obj J) (P.hE J) hcJ
  have hfin : Finite (Pr.assign hμe X0).idx :=
    Finite.of_equiv _ (Pr.arity hμe X0).symm
  obtain ⟨Y, f, hf, b, hAll, hS⟩ :=
    infra_79_existence_at P ⟨htail, infra_79_retraction_pair P⟩ hμ X0
      (Pr.assign hμe X0) hfin
  let M : MarkedPair K oneVertexShape P.scheme Pr :=
    ⟨μ, hμe, X0, Y, f, hf, _, b, Equiv.refl _, hS.symm, hAll⟩
  let φ := SMObject.ofModelEquiv (P.E.obj J) (P.hE J) hcJ
  have hsX : K.Strong φ.toEmbedding := strong_of_equiv K φ (P.hE J)
  have hcY : Model.card ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit) = μ := SMObject.card Y
  refine ⟨M, rfl, φ.toEmbedding, φ.bijective, hsX, fun Z _ _ hZ => ?_, ?_⟩
  · have hcat' := SingleModelData.categorical (P := P) hμe
    exact hcat'.unique_model (P.E.obj Z) _ (P.hE Z) ((P.scheme.asSystem M.hμ M.Y).inK PUnit.unit)
      (SingleModelData.card_obj_eq hμe Z hZ) hcY
  · obtain ⟨Jplus, l, n, emb, strip, V, h1, h2, h3, h4, h5, -, hemb⟩ :=
      infra_615_two_sided P hμ.2 J hJ
    obtain ⟨F, hF, hFi⟩ := hemb _ ((M.incl.onVertex PUnit.unit).comp φ.toEmbedding)
      ((P.scheme.asSystem M.hμ M.Y).inK PUnit.unit)
      (K.strong_trans _ _ hsX (M.incl.onVertex_strong PUnit.unit)) hcY
    exact ⟨Jplus, l, n, emb, strip, V, h1, h2, h3, h4, h5, F, hF, hFi⟩

end AEC
