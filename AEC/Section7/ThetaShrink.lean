module

public import AEC.Section7.IsolatedStage

@[expose] public section

/-!
# Prop 7.8: the `θ⁺` shrink to a level-`λ` pair `A ≤ U` (`infra_78_theta_shrink`)

Paper (Prop 7.8 proof): at the isolated stage `i`, build increasing level-`λ` pairs
`A_α ≤ U_α` (`α < θ⁺`) inside `R_i, S_i` (requirement 1 for the pairs, requirement 2 for the
approximation copies of an enumeration of `U_α`, placed in `A_{α+1}`), and take unions
`A ≤ U`; then for every `c ⊆ U` with `|c| ≤ θ` the majority characterization gives the tied
free-extension identity `tp(b, c / X_i) = tp(b, c / A)^{fr}_{X_i}` (`IsTiedFreeMixed`).

Cycle 57: `infra_78_theta_union` — the union step: a directed family (at most `λ` indices) of
level-`λ` pairs with compatible arrows into the level-`κ` pair `X_i → Y_i` has a union pair
`A → U` at level `λ`, with legs, arrows `A → X_i`, `U → Y_i` extending the given ones, and the
commuting square (the paper's "common upper bound clause gives `A ≤ U`").

Cycle 57b: `infra_78_theta_chain` — the `θ⁺` recursion itself (`infra_78_thetaD`,
`infra_78_theta_step`), with requirement-2 sequences cut to exactly `λ` copies
(`infra_78_seq_sub`), pairs linked by factorization arrows (`infra_78_factor_arrow`), the union
by `infra_78_theta_union`, and every top list of length `≤ θ` in `U` handled by restricting the
sequence of a single stage (`infra_78_succ_bounded`). `infra_78_theta_chain_rc` instantiates it
at the recursion matrix. Open: the tied free-extension identity
(`infra_78_theta_free_identity`).
-/

universe u

open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}

section ThetaUnion
variable {P : SingleModelData K}

/-- **`infra_78_theta_union`** (union step of the `θ⁺` shrink). -/
theorem infra_78_theta_union {ℓ κ : Cardinal.{u}} (hℓ : ℓ ∈ P.eligible) (hκ : κ ∈ P.eligible)
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] (hι : #ι ≤ ℓ)
    (A V : ι → P.scheme.Object ℓ hℓ)
    (g : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (A a)) (P.scheme.asSystem hℓ (V a)))
    (sA : ∀ {a b : ι}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (A a)) (P.scheme.asSystem hℓ (A b)))
    (sV : ∀ {a b : ι}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (V a)) (P.scheme.asSystem hℓ (V b)))
    (hAr : ∀ a, sA (le_refl a) = SystemArrow.refl _)
    (hVr : ∀ a, sV (le_refl a) = SystemArrow.refl _)
    (hAt : ∀ {a b c : ι} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sA (h₁.trans h₂) = SystemArrow.comp (sA h₁) (sA h₂))
    (hVt : ∀ {a b c : ι} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sV (h₁.trans h₂) = SystemArrow.comp (sV h₁) (sV h₂))
    (hcomm : ∀ {a b : ι} (h : a ≤ b),
      SystemArrow.comp (g a) (sV h) = SystemArrow.comp (sA h) (g b))
    {X Y : P.scheme.Object κ hκ}
    (pr : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y))
    (iA : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (A a)) (P.scheme.asSystem hκ X))
    (iV : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (V a)) (P.scheme.asSystem hκ Y))
    (hiA : ∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (sA h) (iA b) = iA a)
    (hiV : ∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (sV h) (iV b) = iV a)
    (hsq : ∀ a, SystemArrow.comp (g a) (iV a) = SystemArrow.comp (iA a) pr) :
    ∃ (Au Uu : P.scheme.Object ℓ hℓ)
      (lA : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (A a)) (P.scheme.asSystem hℓ Au))
      (lU : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hℓ (V a)) (P.scheme.asSystem hℓ Uu))
      (gu : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ Au) (P.scheme.asSystem hℓ Uu))
      (jA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ Au) (P.scheme.asSystem hκ X))
      (jU : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ Uu) (P.scheme.asSystem hκ Y)),
      P.scheme.permitted (X := Au) (Y := Uu) gu ∧
      P.scheme.permitted (X := Au) (Y := X) jA ∧
      P.scheme.permitted (X := Uu) (Y := Y) jU ∧
      (∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (sA h) (lA b) = lA a) ∧
      (∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (sV h) (lU b) = lU a) ∧
      (∀ a, SystemArrow.comp (g a) (lU a) = SystemArrow.comp (lA a) gu) ∧
      (∀ a, SystemArrow.comp (lA a) jA = iA a) ∧
      (∀ a, SystemArrow.comp (lU a) jU = iV a) ∧
      SystemArrow.comp gu jU = SystemArrow.comp jA pr ∧
      (∀ x : Occurrence K oneVertexShape (P.scheme.asSystem hℓ Au),
        ∃ a, ∃ y : Occurrence K oneVertexShape (P.scheme.asSystem hℓ (A a)), pushOcc (lA a) y = x) ∧
      (∀ x : Occurrence K oneVertexShape (P.scheme.asSystem hℓ Uu),
        ∃ a, ∃ y : Occurrence K oneVertexShape (P.scheme.asSystem hℓ (V a)), pushOcc (lU a) y = x) := by
  obtain ⟨Au, lA, -, hcA, hcovA, hunivA, huniqA⟩ := infra_78_chain_union_kappa hℓ hι A sA hAr hAt
  obtain ⟨Uu, lU, -, hcU, hcovU, hunivU, -⟩ := infra_78_chain_union_kappa hℓ hι V sV hVr hVt
  obtain ⟨gu, hgu, hguc⟩ := hunivA Uu (fun a => SystemArrow.comp (g a) (lU a)) (by
    intro a b h
    rw [← SystemArrow.comp_assoc, ← hcomm h, SystemArrow.comp_assoc, hcU h])
  obtain ⟨jA, hjA, hjAc⟩ := hunivA X iA hiA
  obtain ⟨jU, hjU, hjUc⟩ := hunivU Y iV hiV
  refine ⟨Au, Uu, lA, lU, gu, jA, jU, hgu, hjA, hjU, hcA, hcU, fun a => (hguc a).symm, hjAc, hjUc,
    ?_, hcovA, hcovU⟩
  apply huniqA Y
  intro a
  rw [← SystemArrow.comp_assoc, hguc a, SystemArrow.comp_assoc, hjUc a, hsq a,
    ← SystemArrow.comp_assoc, hjAc a]

end ThetaUnion

section ThetaTools
variable {P : SingleModelData K}

/-- Factorization through a range: an arrow into `X` whose image lies in the image of another
permitted arrow into `X` factors through it by a permitted arrow (coherence). -/
theorem infra_78_factor_arrow {ν ν' μ : Cardinal.{u}} {hν : ν ∈ P.eligible} {hν' : ν' ∈ P.eligible}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object ν hν} {B : P.scheme.Object ν' hν'}
    {X : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ X))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hν' B) (P.scheme.asSystem hμ X))
    (hf : P.scheme.permitted (X := A) (Y := X) f) (hg : P.scheme.permitted (X := B) (Y := X) g)
    (hr : Set.range (f.onVertex PUnit.unit) ⊆ Set.range (g.onVertex PUnit.unit)) :
    ∃ h : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hν' B),
      P.scheme.permitted (X := A) (Y := B) h ∧ SystemArrow.comp h g = f := by
  classical
  have himg : ∀ v (x : ((P.scheme.asSystem hν A).obj v).carrier),
      ∃ y, (g.onVertex v) y = (f.onVertex v) x := by
    intro v x
    cases v
    exact hr ⟨x, rfl⟩
  let h : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hν' B) :=
    { onVertex := fun v => factorEmbedding (f.onVertex v) (g.onVertex v) (himg v)
      onVertex_strong := fun v => strong_factorEmbedding _ _ (f.onVertex_strong v)
        (g.onVertex_strong v) (himg v)
      comm := fun h => h.elim }
  have hc : SystemArrow.comp h g = f := by
    apply SystemArrow.ext
    intro v
    exact DFunLike.ext _ _ (fun x => factorEmbedding_apply _ _ (himg v) x)
  refine ⟨h, P.scheme.coherent h f g hf hg (fun v => ?_), hc⟩
  exact congrArg (fun a => a.onVertex v) hc

/-- Arrows into an object are determined by their composite with an arrow out of it. -/
theorem infra_78_arrow_cancel {S : SystemShape.{u}} {A B X : SystemObject K S}
    (h h' : SystemArrow K S A B) (g : SystemArrow K S B X)
    (e : SystemArrow.comp h g = SystemArrow.comp h' g) : h = h' := by
  apply SystemArrow.ext
  intro v
  apply DFunLike.ext
  intro x
  apply (g.onVertex v).injective
  exact DFunLike.congr_fun (congrArg (fun a => a.onVertex v) e) x

theorem infra_78_refl_comp {S : SystemShape.{u}} {A B : SystemObject K S}
    (f : SystemArrow K S A B) : SystemArrow.comp (SystemArrow.refl A) f = f := by
  apply SystemArrow.ext
  intro v
  rfl

/-- Restriction of an approximation sequence to a subtuple and to a subfamily of its copies:
the subtuple bound (`ApproximationSequence.subtuple_uniform`) survives on any subfamily. -/
noncomputable def infra_78_seq_sub {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {base : P.scheme.Object μ hμ} {p : TupleOver K oneVertexShape P.scheme hμ base}
    (seq : ApproximationSequence p) (κ' : Set seq.κIndex) {ι : Type u} (ρ : ι → p.idx)
    (hρ : Function.Injective ρ) : ApproximationSequence (p.reindex ρ) where
  τ := seq.τ
  κIndex := κ'
  family := fun a j => seq.family a.1 (ρ j)
  concat_bounded := by
    refine lt_of_le_of_lt ?_ seq.concat_bounded
    exact Cardinal.mk_le_of_injective (f := Prod.map Subtype.val ρ)
      (Subtype.val_injective.prodMap hρ)
  few_exceptions := by
    intro β Z hβ
    refine le_trans ?_ (seq.subtuple_uniform ρ hρ Z hβ)
    exact Cardinal.mk_le_of_injective (f := fun a => ⟨a.1.1, a.2⟩)
      (fun a b hab => by
        have h1 := congrArg Subtype.val hab
        exact Subtype.ext (Subtype.ext h1))

end ThetaTools

section ThetaStep
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}
  (M : Infra78Matrix P ρ hκ) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
  (i : (Order.succ ρ).ord.ToType)

/-- `E` is exactly the bookkeeping image of a level-`ℓ` pair `A ≤ V` inside `X_i ≤ Y_i`. -/
def infra_78_PairRange (E : Set (infra_78_bkCarrier M i)) : Prop :=
  ∃ (A V : P.scheme.Object ℓ hℓel)
    (iA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hκ (M.X i)))
    (iV : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel V) (P.scheme.asSystem hκ (M.Y i)))
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hℓel V)),
    P.scheme.permitted (X := A) (Y := M.X i) iA ∧
    P.scheme.permitted (X := V) (Y := M.Y i) iV ∧
    P.scheme.permitted (X := A) (Y := V) g ∧
    SystemArrow.comp g iV = SystemArrow.comp iA (M.pair i) ∧
    E = Sum.inl '' Set.range (iA.onVertex PUnit.unit) ∪ Sum.inr '' Set.range (iV.onVertex PUnit.unit)

theorem infra_78_obj_card (A : P.scheme.Object ℓ hℓel) :
    #((P.scheme.asSystem hℓel A).obj PUnit.unit).carrier = ℓ :=
  P.scheme.vertex_card hℓel A PUnit.unit

/-- **One step of the `θ⁺` recursion.** A small `D ⊆ T` (closure requirements 1 and 2 on `T`)
lies in the image `E ⊆ T` of a level-`ℓ` pair, and `E` contains the copies of a requirement-2
approximation sequence for the top points of `D`, cut down to exactly `ℓ` copies. -/
theorem infra_78_theta_step (hℓ : ℵ₀ ≤ ℓ) (T : Set (infra_78_bkCarrier M i))
    (hR1 : ∀ s ⊆ T, #s ≤ ℓ → infra_78_bkReq1 M hℓel i s T)
    (hR2 : ∀ s ⊆ T, #s ≤ ℓ → ∃ seq : ApproximationSequence (infra_78_bkTuple M i s),
      seq.τ = ℓ ∧ ℓ + ℵ₀ < #seq.κIndex ∧
      ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ T)
    (D : Set (infra_78_bkCarrier M i)) (hD : D ⊆ T) (hDl : #D ≤ ℓ) :
    ∃ E ⊆ T, #E ≤ ℓ ∧ D ⊆ E ∧ infra_78_PairRange M hℓel i E ∧
      ∃ seq : ApproximationSequence (infra_78_bkTuple M i D), seq.τ = ℓ ∧ #seq.κIndex = ℓ ∧
        ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ E := by
  classical
  obtain ⟨seq0, hτ0, hlen0, hin0⟩ := hR2 D hD hDl
  obtain ⟨κ', hκ'⟩ := Cardinal.le_mk_iff_exists_set.1
    ((le_self_add.trans_lt hlen0).le : ℓ ≤ #seq0.κIndex)
  let seq : ApproximationSequence (infra_78_bkTuple M i D) :=
    infra_78_seq_sub seq0 κ' id Function.injective_id
  have hfam : ∀ a b, seq.family a b = seq0.family a.1 b := fun _ _ => rfl
  let Cp : Set (infra_78_bkCarrier M i) := Set.range
    (fun ab : κ' × (infra_78_bkTuple M i D).idx =>
      (Sum.inl ((M.X i).val (seq0.family ab.1.1 ab.2)) : infra_78_bkCarrier M i))
  have hidx : #(infra_78_bkTuple M i D).idx ≤ ℓ :=
    (Cardinal.mk_preimage_of_injective _ _ Sum.inr_injective).trans hDl
  have hCp : #Cp ≤ ℓ := by
    refine Cardinal.mk_range_le.trans ?_
    rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id, hκ']
    exact (mul_le_mul (le_refl ℓ) hidx zero_le zero_le).trans (Cardinal.mul_eq_self hℓ).le
  have hCpT : Cp ⊆ T := by
    rintro _ ⟨ab, rfl⟩
    exact hin0 _ _
  have hs : D ∪ Cp ⊆ T := Set.union_subset hD hCpT
  have hsl : #(D ∪ Cp : Set _) ≤ ℓ :=
    (Cardinal.mk_union_le _ _).trans ((add_le_add hDl hCp).trans (Cardinal.add_eq_self hℓ).le)
  obtain ⟨A, V, iA, iV, g, hiA, hiV, hg, hsq, hsA, hsV, hTA, hTV⟩ := hR1 _ hs hsl
  refine ⟨Sum.inl '' Set.range (iA.onVertex PUnit.unit) ∪
      Sum.inr '' Set.range (iV.onVertex PUnit.unit), Set.union_subset hTA hTV, ?_, ?_,
    ⟨A, V, iA, iV, g, hiA, hiV, hg, SystemArrow.ext hsq, rfl⟩, seq, hτ0, ?_, ?_⟩
  · refine (Cardinal.mk_union_le _ _).trans ((add_le_add ?_ ?_).trans (Cardinal.add_eq_self hℓ).le)
    · exact Cardinal.mk_image_le.trans (Cardinal.mk_range_le.trans
        (infra_78_obj_card hℓel A).le)
    · exact Cardinal.mk_image_le.trans (Cardinal.mk_range_le.trans
        (infra_78_obj_card hℓel V).le)
  · intro x hx
    rcases x with a | b
    · exact Or.inl ⟨a, hsA (Or.inl hx), rfl⟩
    · exact Or.inr ⟨b, hsV (Or.inl hx), rfl⟩
  · show #κ' = ℓ
    exact hκ'
  · intro a b
    rw [hfam]
    exact Or.inl ⟨_, hsA (Or.inr ⟨(a, b), rfl⟩), rfl⟩

end ThetaStep

section ThetaChain

/-- A family of at most `θ` points of `θ⁺` has a strict upper bound (regularity of `θ⁺`). -/
theorem infra_78_succ_bounded {θ : Cardinal.{u}} (hθ : ℵ₀ ≤ θ) {J : Type u} (hJ : #J ≤ θ)
    (f : J → (Order.succ θ).ord.ToType) : ∃ γ, ∀ j, f j < γ := by
  classical
  by_contra hcon0
  have hcon : ∀ γ, ∃ j, γ ≤ f j := fun γ => by
    obtain ⟨j, hj⟩ := not_forall.1 (not_exists.1 hcon0 γ)
    exact ⟨j, not_lt.1 hj⟩
  have hcov : (Set.univ : Set (Order.succ θ).ord.ToType) ⊆ ⋃ j, Set.Iic (f j) := by
    intro γ _
    obtain ⟨j, hj⟩ := hcon γ
    exact Set.mem_iUnion.2 ⟨j, hj⟩
  have hIic : ∀ x : (Order.succ θ).ord.ToType, #(Set.Iic x) ≤ θ := by
    intro x
    have h1 : #(Set.Iio x) < Order.succ θ := by
      have := Cardinal.mk_Iio_lt x (by simp)
      simpa using this
    rw [← Set.Iio_insert]
    exact Cardinal.mk_insert_le.trans ((add_le_add (Order.lt_succ_iff.1 h1) le_rfl).trans
      (Cardinal.add_one_eq hθ).le)
  have hle : #(Order.succ θ).ord.ToType ≤ θ := by
    rw [← Cardinal.mk_univ]
    refine (Cardinal.mk_le_mk_of_subset hcov).trans ?_
    refine Cardinal.mk_iUnion_le_sum_mk.trans ?_
    refine (Cardinal.sum_le_sum _ (fun _ => θ) (fun j => hIic (f j))).trans ?_
    rw [Cardinal.sum_const']
    exact (mul_le_mul hJ le_rfl zero_le zero_le).trans (Cardinal.mul_eq_self hθ).le
  rw [Cardinal.mk_ord_toType] at hle
  exact (Order.lt_succ_of_not_isMax (not_isMax θ)).not_ge hle

/-- The `θ⁺` recursion on bookkeeping sets: `D α = s₀ ∪ ⋃_{β<α} F (D β)`. -/
noncomputable def infra_78_thetaD {C ι : Type u} [LinearOrder ι] [WellFoundedLT ι]
    (s₀ : Set C) (F : Set C → Set C) : ι → Set C :=
  (wellFounded_lt (α := ι)).fix (fun α rec => s₀ ∪ ⋃ β : Set.Iio α, F (rec β.1 β.2))

theorem infra_78_thetaD_eq {C ι : Type u} [LinearOrder ι] [WellFoundedLT ι]
    (s₀ : Set C) (F : Set C → Set C) (α : ι) :
    infra_78_thetaD s₀ F α = s₀ ∪ ⋃ β : Set.Iio α, F (infra_78_thetaD s₀ F β.1) :=
  (wellFounded_lt (α := ι)).fix_eq _ α

variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}
  (M : Infra78Matrix P ρ hκ) {ℓ : Cardinal.{u}} (hℓel : ℓ ∈ P.eligible)
  (i : (Order.succ ρ).ord.ToType)

/-- Output of the `θ⁺` shrink construction at stage `i` (see `infra_78_theta_chain`). -/
def infra_78_ThetaChainOut (θ : Cardinal.{u}) (T s₀ : Set (infra_78_bkCarrier M i)) : Prop :=
    ∃ (A U : P.scheme.Object ℓ hℓel)
      (jA : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hκ (M.X i)))
      (jU : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel U) (P.scheme.asSystem hκ (M.Y i)))
      (gu : SystemArrow K oneVertexShape (P.scheme.asSystem hℓel A) (P.scheme.asSystem hℓel U)),
      P.scheme.permitted (X := A) (Y := M.X i) jA ∧
      P.scheme.permitted (X := U) (Y := M.Y i) jU ∧
      P.scheme.permitted (X := A) (Y := U) gu ∧
      SystemArrow.comp gu jU = SystemArrow.comp jA (M.pair i) ∧
      s₀ ⊆ Sum.inl '' Set.range (jA.onVertex PUnit.unit) ∪
        Sum.inr '' Set.range (jU.onVertex PUnit.unit) ∧
      Sum.inl '' Set.range (jA.onVertex PUnit.unit) ⊆ T ∧
      Sum.inr '' Set.range (jU.onVertex PUnit.unit) ⊆ T ∧
      ∀ s : Set (infra_78_bkCarrier M i),
        (Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) ⊆ Set.range (jU.onVertex PUnit.unit) →
        #(Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) ≤ θ →
        ∃ seq : ApproximationSequence (infra_78_bkTuple M i s), seq.τ = ℓ ∧ #seq.κIndex = ℓ ∧
          ∀ a b, (M.X i).val (seq.family a b) ∈ Set.range (jA.onVertex PUnit.unit)

/-- **`infra_78_theta_chain`** (Prop 7.8 proof, the `θ⁺` shrink construction). At a stage `i`
whose bookkeeping set `T ⊆ X_i ⊕ Y_i` satisfies closure requirement 1 (level-`λ` pairs) and
closure requirement 2 (approximation sequences of test size `λ` with more than `λ` copies, for
every small top list) — as `infra_78_rnext_closure` supplies at stages of cofinality `> λ` —
and for `ℵ₀ ≤ θ`, `θ⁺ ≤ λ`, every small seed `s₀ ⊆ T` (e.g. `I_p` and `b`) lies in a level-`λ`
pair `A ≤ U` inside `X_i ≤ Y_i` with images in `T`, such that every top list `c ⊆ U` of length
`≤ θ` has an approximation sequence over `X_i` (test size `λ`, exactly `λ` copies) all of whose
copies lie in `A`. -/
theorem infra_78_theta_chain {θ : Cardinal.{u}} (hθ : ℵ₀ ≤ θ) (hθℓ : Order.succ θ ≤ ℓ)
    (T : Set (infra_78_bkCarrier M i))
    (hR1 : ∀ s ⊆ T, #s ≤ ℓ → infra_78_bkReq1 M hℓel i s T)
    (hR2 : ∀ s ⊆ T, #s ≤ ℓ → ∃ seq : ApproximationSequence (infra_78_bkTuple M i s),
      seq.τ = ℓ ∧ ℓ + ℵ₀ < #seq.κIndex ∧
      ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ T)
    (s₀ : Set (infra_78_bkCarrier M i)) (hs₀ : s₀ ⊆ T) (hs₀l : #s₀ ≤ ℓ) :
    infra_78_ThetaChainOut M hℓel i θ T s₀ := by
  classical
  have hℓ : ℵ₀ ≤ ℓ := hθ.trans ((Order.le_succ θ).trans hθℓ)
  have step := infra_78_theta_step M hℓel i hℓ T hR1 hR2
  let F : Set (infra_78_bkCarrier M i) → Set (infra_78_bkCarrier M i) := fun D =>
    if h : D ⊆ T ∧ #D ≤ ℓ then Classical.choose (step D h.1 h.2) else D
  have hF : ∀ D (hD : D ⊆ T) (hDl : #D ≤ ℓ), F D ⊆ T ∧ #(F D) ≤ ℓ ∧ D ⊆ F D ∧
      infra_78_PairRange M hℓel i (F D) ∧
      ∃ seq : ApproximationSequence (infra_78_bkTuple M i D), seq.τ = ℓ ∧ #seq.κIndex = ℓ ∧
        ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ F D := by
    intro D hD hDl
    have e : F D = Classical.choose (step D hD hDl) := dif_pos ⟨hD, hDl⟩
    rw [e]
    obtain ⟨h1, h2⟩ := Classical.choose_spec (step D hD hDl)
    exact ⟨h1, h2⟩
  let ι := (Order.succ θ).ord.ToType
  have hιc : #ι = Order.succ θ := Cardinal.mk_ord_toType _
  have : Nonempty ι := Cardinal.mk_ne_zero_iff.1 (by
    rw [hιc]; exact (Cardinal.aleph0_pos.trans_le (hθ.trans (Order.le_succ θ))).ne')
  let D : ι → Set (infra_78_bkCarrier M i) := infra_78_thetaD s₀ F
  have hDeq : ∀ α, D α = s₀ ∪ ⋃ β : Set.Iio α, F (D β.1) := infra_78_thetaD_eq s₀ F
  have hgood : ∀ α, D α ⊆ T ∧ #(D α) ≤ ℓ := by
    intro α
    induction α using (wellFounded_lt (α := ι)).induction with
    | _ α ih =>
      rw [hDeq α]
      refine ⟨Set.union_subset hs₀ (Set.iUnion_subset fun β => (hF _ (ih β.1 β.2).1
        (ih β.1 β.2).2).1), ?_⟩
      refine (Cardinal.mk_union_le _ _).trans ((add_le_add hs₀l ?_).trans
        (Cardinal.add_eq_self hℓ).le)
      refine Cardinal.mk_iUnion_le_sum_mk.trans ?_
      refine (Cardinal.sum_le_sum (fun β : Set.Iio α => #(F (D β.1))) (fun _ => ℓ)
        (fun β : Set.Iio α => (hF _ (ih β.1 β.2).1 (ih β.1 β.2).2).2.1)).trans ?_
      rw [Cardinal.sum_const']
      have hI : #(Set.Iio α) ≤ ℓ := (Cardinal.mk_set_le _).trans (hιc.le.trans hθℓ)
      exact (mul_le_mul hI le_rfl zero_le zero_le).trans (Cardinal.mul_eq_self hℓ).le
  let E : ι → Set (infra_78_bkCarrier M i) := fun β => F (D β)
  have hE : ∀ β, E β ⊆ T ∧ #(E β) ≤ ℓ ∧ D β ⊆ E β ∧ infra_78_PairRange M hℓel i (E β) ∧
      ∃ seq : ApproximationSequence (infra_78_bkTuple M i (D β)), seq.τ = ℓ ∧
        #seq.κIndex = ℓ ∧
        ∀ a b, (Sum.inl ((M.X i).val (seq.family a b)) : infra_78_bkCarrier M i) ∈ E β :=
    fun β => hF _ (hgood β).1 (hgood β).2
  have hED : ∀ {β α : ι}, β < α → E β ⊆ D α := by
    intro β α h x hx
    rw [hDeq α]
    exact Or.inr (Set.mem_iUnion.2 ⟨⟨β, h⟩, hx⟩)
  have hEmono : ∀ {β γ : ι}, β ≤ γ → E β ⊆ E γ := by
    intro β γ h
    rcases h.lt_or_eq with h | h
    · exact (hED h).trans (hE γ).2.2.1
    · exact h ▸ le_rfl
  have hs₀D : ∀ α, s₀ ⊆ D α := fun α => by rw [hDeq α]; exact Set.subset_union_left
  choose A V iA iV g hiA hiV hg hsq hEr using fun β => (hE β).2.2.2.1
  have hinlE : ∀ β x, (Sum.inl x : infra_78_bkCarrier M i) ∈ E β →
      x ∈ Set.range ((iA β).onVertex PUnit.unit) := by
    intro β x hx
    rw [hEr β] at hx
    rcases hx with ⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩
    · exact Sum.inl_injective hyx ▸ hy
    · exact (Sum.inr_ne_inl hyx).elim
  have hinrE : ∀ β x, (Sum.inr x : infra_78_bkCarrier M i) ∈ E β →
      x ∈ Set.range ((iV β).onVertex PUnit.unit) := by
    intro β x hx
    rw [hEr β] at hx
    rcases hx with ⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩
    · exact (Sum.inl_ne_inr hyx).elim
    · exact Sum.inr_injective hyx ▸ hy
  have hAE : ∀ β x, x ∈ Set.range ((iA β).onVertex PUnit.unit) →
      (Sum.inl x : infra_78_bkCarrier M i) ∈ E β := fun β x hx => by
    rw [hEr β]; exact Or.inl ⟨x, hx, rfl⟩
  have hVE : ∀ β x, x ∈ Set.range ((iV β).onVertex PUnit.unit) →
      (Sum.inr x : infra_78_bkCarrier M i) ∈ E β := fun β x hx => by
    rw [hEr β]; exact Or.inr ⟨x, hx, rfl⟩
  have hfA : ∀ β γ : ι, β ≤ γ → ∃ st : SystemArrow K oneVertexShape
      (P.scheme.asSystem hℓel (A β)) (P.scheme.asSystem hℓel (A γ)),
      P.scheme.permitted (X := A β) (Y := A γ) st ∧ SystemArrow.comp st (iA γ) = iA β :=
    fun β γ h => infra_78_factor_arrow (iA β) (iA γ) (hiA β) (hiA γ)
      (fun x hx => hinlE γ x (hEmono h (hAE β x hx)))
  have hfV : ∀ β γ : ι, β ≤ γ → ∃ st : SystemArrow K oneVertexShape
      (P.scheme.asSystem hℓel (V β)) (P.scheme.asSystem hℓel (V γ)),
      P.scheme.permitted (X := V β) (Y := V γ) st ∧ SystemArrow.comp st (iV γ) = iV β :=
    fun β γ h => infra_78_factor_arrow (iV β) (iV γ) (hiV β) (hiV γ)
      (fun x hx => hinrE γ x (hEmono h (hVE β x hx)))
  choose sA hsAp hsAc using hfA
  choose sV hsVp hsVc using hfV
  obtain ⟨Au, Uu, lA, lU, gu, jA, jU, hgu, hjA, hjU, -, -, -, hjAc, hjUc, hsqu, hcovA, hcovU⟩ :=
    infra_78_theta_union hℓel hκ (ι := ι) (hιc.le.trans hθℓ) A V g
      (fun {a b} h => sA a b h) (fun {a b} h => sV a b h)
      (fun a => infra_78_arrow_cancel _ _ (iA a) (by rw [hsAc, infra_78_refl_comp]))
      (fun a => infra_78_arrow_cancel _ _ (iV a) (by rw [hsVc, infra_78_refl_comp]))
      (fun {a b c} h₁ h₂ => infra_78_arrow_cancel _ _ (iA c)
        (by rw [hsAc, SystemArrow.comp_assoc, hsAc, hsAc]))
      (fun {a b c} h₁ h₂ => infra_78_arrow_cancel _ _ (iV c)
        (by rw [hsVc, SystemArrow.comp_assoc, hsVc, hsVc]))
      (fun {a b} h => infra_78_arrow_cancel _ _ (iV b)
        (by rw [SystemArrow.comp_assoc, hsVc, hsq, SystemArrow.comp_assoc, hsq,
          ← SystemArrow.comp_assoc, hsAc]))
      (M.pair i) iA iV (fun {a b} h => hsAc a b h) (fun {a b} h => hsVc a b h) hsq
  -- images of the union arrows
  have hjA_apply : ∀ β y, jA.onVertex PUnit.unit ((lA β).onVertex PUnit.unit y) =
      (iA β).onVertex PUnit.unit y := fun β y =>
    DFunLike.congr_fun (congrArg (fun a => a.onVertex PUnit.unit) (hjAc β)) y
  have hjU_apply : ∀ β y, jU.onVertex PUnit.unit ((lU β).onVertex PUnit.unit y) =
      (iV β).onVertex PUnit.unit y := fun β y =>
    DFunLike.congr_fun (congrArg (fun a => a.onVertex PUnit.unit) (hjUc β)) y
  have hrA : ∀ x, x ∈ Set.range (jA.onVertex PUnit.unit) ↔
      ∃ β, x ∈ Set.range ((iA β).onVertex PUnit.unit) := by
    intro x
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨β, ⟨v, y⟩, hy⟩ := hcovA ⟨PUnit.unit, z⟩
      cases v
      have hz : (lA β).onVertex PUnit.unit y = z := eq_of_heq (Sigma.mk.inj hy).2
      exact ⟨β, y, by rw [← hz, hjA_apply]⟩
    · rintro ⟨β, y, rfl⟩
      exact ⟨_, hjA_apply β y⟩
  have hrU : ∀ x, x ∈ Set.range (jU.onVertex PUnit.unit) ↔
      ∃ β, x ∈ Set.range ((iV β).onVertex PUnit.unit) := by
    intro x
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨β, ⟨v, y⟩, hy⟩ := hcovU ⟨PUnit.unit, z⟩
      cases v
      have hz : (lU β).onVertex PUnit.unit y = z := eq_of_heq (Sigma.mk.inj hy).2
      exact ⟨β, y, by rw [← hz, hjU_apply]⟩
    · rintro ⟨β, y, rfl⟩
      exact ⟨_, hjU_apply β y⟩
  obtain ⟨β0⟩ := (inferInstance : Nonempty ι)
  refine ⟨Au, Uu, jA, jU, gu, hjA, hjU, hgu, hsqu, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' := (hE β0).2.2.1 (hs₀D β0 hx)
    rcases x with a | b
    · exact Or.inl ⟨a, (hrA a).2 ⟨β0, hinlE β0 a hx'⟩, rfl⟩
    · exact Or.inr ⟨b, (hrU b).2 ⟨β0, hinrE β0 b hx'⟩, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨β, hβ⟩ := (hrA x).1 hx
    exact (hE β).1 (hAE β x hβ)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨β, hβ⟩ := (hrU x).1 hx
    exact (hE β).1 (hVE β x hβ)
  · intro s hsU hsθ
    have hpick : ∀ y : (Sum.inr ⁻¹' s : Set (M.Y i).model.carrier), ∃ β : ι,
        y.1 ∈ Set.range ((iV β).onVertex PUnit.unit) := fun y => (hrU y.1).1 (hsU y.2)
    choose bf hbf using hpick
    obtain ⟨γ, hγ⟩ := infra_78_succ_bounded hθ hsθ bf
    have hsub : (Sum.inr ⁻¹' s : Set (M.Y i).model.carrier) ⊆ Sum.inr ⁻¹' (D γ) := by
      intro y hy
      exact hED (hγ ⟨y, hy⟩) (hVE _ y (hbf ⟨y, hy⟩))
    obtain ⟨seq0, hτ0, hlen0, hin0⟩ := (hE γ).2.2.2.2
    let seq : ApproximationSequence (infra_78_bkTuple M i s) :=
      infra_78_seq_sub seq0 Set.univ (Set.inclusion hsub) (Set.inclusion_injective hsub)
    refine ⟨seq, hτ0, ?_, ?_⟩
    · show #(Set.univ : Set seq0.κIndex) = ℓ
      rw [Cardinal.mk_univ, hlen0]
    · intro a b
      exact (hrA _).2 ⟨γ, hinlE γ _ (hin0 a.1 _)⟩

end ThetaChain

section ThetaChainRc
variable (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
  {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ) {uIdx cIdx L : Type u}
  {ρ : Cardinal.{u}} (hρκ : Order.succ ρ < μ)
  (Xb : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)) {ℓ : Cardinal.{u}}
  (hℓel : ℓ ∈ P.eligible)
  (cand : (Order.succ ρ).ord.ToType →
    Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx) →
    L → cIdx → μ.ord.ToType)
  (s0 : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
  (e0 : Infra78MarkData μ uIdx)

include hρκ in
/-- **`infra_78_theta_chain` at the recursion matrix.** At a stage `i` of cofinality `> λ` of the
recursion matrix, closure requirements 1 and 2 (`infra_78_rnext_closure`) feed
`infra_78_theta_chain` with `T = R_i`. Requirement 2 is used for top lists of length `≤ λ`, so
it is invoked at a recursion-closed `σ' ≥ λ` (the paper's "sufficiently closed" matrix level). -/
theorem infra_78_theta_chain_rc (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (h5 : ∀ β, infra_78_StageInv5 Xb (infra_78_rcObj Xb hℓel cand s0 e0 β))
    (hℓκ : ℓ ≤ μ) (hℓρ : ℓ < ρ) (hpow : ρ ^ ℓ = ρ) (h0 : #s0.e.R ≤ ρ)
    (hseed : infra_78_PairClosed ρ hℓel (infra_78_toArr s0.hp) trivial s0.e.R)
    (hS0 : ∃ y, (Sum.inr y : μ.ord.ToType ⊕ μ.ord.ToType) ∈ s0.e.R)
    (σ' : Cardinal.{u}) (hσ' : ℵ₀ ≤ σ') (hℓσ' : ℓ ≤ σ') (hrec : μ ∈ recursionClosedLevels P σ')
    (hσS : Order.succ σ' ≤ μ) (hℓμ : ℓ < μ)
    {θ : Cardinal.{u}} (hθ : ℵ₀ ≤ θ) (hθℓ : Order.succ θ ≤ ℓ)
    (i : (Order.succ ρ).ord.ToType) (hcof : ℓ < Order.cof (Set.Iio i))
    (s₀ : Set (infra_78_bkCarrier (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) i))
    (hs₀ : s₀ ⊆ infra_78_rcSets hρκ Xb hℓel cand s0 e0 i) (hs₀l : #s₀ ≤ ℓ) :
    infra_78_ThetaChainOut (infra_78_rcMatrix hρκ Xb hℓel cand s0 e0) hℓel i θ
      (infra_78_rcSets hρκ Xb hℓel cand s0 e0 i) s₀ := by
  obtain ⟨-, -, -, -, -, hR1, hR2⟩ :=
    infra_78_rnext_closure P σ hσ hμT hρκ Xb hℓel cand s0 e0 hidx h5 hℓκ hℓρ hpow h0 hseed hS0
  exact infra_78_theta_chain _ hℓel i hθ hθℓ _
    (fun s hs hsl => hR1 i (Or.inr hcof) s hs hsl)
    (fun s hs hsl => hR2 σ' hσ' hrec hσS hℓμ i (Or.inr hcof) s hs hsl
      ((Cardinal.mk_preimage_of_injective _ _ Sum.inr_injective).trans (hsl.trans hℓσ')))
    s₀ hs₀ hs₀l

end ThetaChainRc
end AEC
