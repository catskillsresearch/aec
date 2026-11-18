module

public import AEC.Section7.Theorem79Existence

@[expose] public section

/-!
# Theorem 7.9: the retraction-closed level-`ν` pair (`infra_79_retraction_pair`, cycle 72)

Paper (proof of Theorem 7.9): "Corollary 6.16 gives `ν` approximate retractions
`r_i : U → A`; close a level-`ν` pair `A' ≤ U'` under them, containing the image of `X` and `b`."

Construction: `corollary_6_16_family` at `λ` gives `λ` arrows almost fixing `B`; keep `ν` of
them (the finite-exception property survives). An `ω`-chain of level-`ν` pairs inside `B ≤ U`
(`infra_78_mixed_ls_pair`, chosen by `Classical.epsilon`): stage `n+1` covers stage `n` and the
images of its upper object under the `ν` retractions (size `ν · ν = ν`). Chain arrows by
`infra_78_factor_arrow`, the union by `infra_78_theta_union`.
-/

universe u

open Cardinal FirstOrder
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- A level-`ν` pair `A ≤ V` inside a level-`λ` pair `f : B → U`, with a commuting square. -/
structure Infra79Stage (P : SingleModelData K) {ν l : Cardinal.{u}} (hν : ν ∈ P.eligible)
    (hl : l ∈ P.eligible) (B U : P.scheme.Object l hl)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hl B) (P.scheme.asSystem hl U)) where
  A : P.scheme.Object ν hν
  V : P.scheme.Object ν hν
  iA : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hl B)
  iV : SystemArrow K oneVertexShape (P.scheme.asSystem hν V) (P.scheme.asSystem hl U)
  g : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hν V)
  sq : SystemArrow.comp g iV = SystemArrow.comp iA f

section Stages
variable {P : SingleModelData K} {ν l : Cardinal.{u}} (hν : ν ∈ P.eligible)
  {hl : l ∈ P.eligible} {B U : P.scheme.Object l hl}
  {f : SystemArrow K oneVertexShape (P.scheme.asSystem hl B) (P.scheme.asSystem hl U)}

theorem infra_79_stage_exists (hνl : ν ≤ l)
    (S : Set ((P.scheme.asSystem hl B).obj PUnit.unit).carrier)
    (T : Set ((P.scheme.asSystem hl U).obj PUnit.unit).carrier) (hS : #S ≤ ν) (hT : #T ≤ ν) :
    ∃ st : Infra79Stage P hν hl B U f, S ⊆ Set.range (st.iA.onVertex PUnit.unit) ∧
      T ⊆ Set.range (st.iV.onVertex PUnit.unit) := by
  obtain ⟨A, V, iA, iV, g, -, -, -, hsq, hS', hT'⟩ :=
    infra_78_mixed_ls_pair hν hl hνl f S T hS hT
  exact ⟨⟨A, V, iA, iV, g, SystemArrow.ext fun v => hsq v⟩, hS', hT'⟩

/-- A stage covering `S` and `T` (when one exists). -/
noncomputable def infra_79_pick (hνl : ν ≤ l)
    (S : Set ((P.scheme.asSystem hl B).obj PUnit.unit).carrier)
    (T : Set ((P.scheme.asSystem hl U).obj PUnit.unit).carrier) : Infra79Stage P hν hl B U f :=
  @Classical.epsilon _
    ⟨(infra_79_stage_exists hν (f := f) hνl ∅ ∅ (by simp) (by simp)).choose⟩
    (fun st => S ⊆ Set.range (st.iA.onVertex PUnit.unit) ∧
      T ⊆ Set.range (st.iV.onVertex PUnit.unit))

theorem infra_79_pick_spec (hνl : ν ≤ l)
    (S : Set ((P.scheme.asSystem hl B).obj PUnit.unit).carrier)
    (T : Set ((P.scheme.asSystem hl U).obj PUnit.unit).carrier) (hS : #S ≤ ν) (hT : #T ≤ ν) :
    S ⊆ Set.range ((infra_79_pick hν (f := f) hνl S T).iA.onVertex PUnit.unit) ∧
      T ⊆ Set.range ((infra_79_pick hν (f := f) hνl S T).iV.onVertex PUnit.unit) :=
  @Classical.epsilon_spec _ _ (infra_79_stage_exists hν hνl S T hS hT)

/-- The `ω`-chain of stages closed under the arrows `r`. -/
noncomputable def infra_79_stageSeq (hνl : ν ≤ l) {ιs : Type u}
    (r : ιs → SystemArrow K oneVertexShape (P.scheme.asSystem hl U) (P.scheme.asSystem hl B))
    (S0 : Set ((P.scheme.asSystem hl B).obj PUnit.unit).carrier)
    (T0 : Set ((P.scheme.asSystem hl U).obj PUnit.unit).carrier) :
    ℕ → Infra79Stage P hν hl B U f
  | 0 => infra_79_pick hν hνl S0 T0
  | n + 1 =>
      let st := infra_79_stageSeq hνl r S0 T0 n
      infra_79_pick hν hνl
        (Set.range (st.iA.onVertex PUnit.unit) ∪
          ⋃ i, (r i).onVertex PUnit.unit '' Set.range (st.iV.onVertex PUnit.unit))
        (Set.range (st.iV.onVertex PUnit.unit))

theorem infra_79_range_card {l' : Cardinal.{u}} {hl' : l' ∈ P.eligible}
    {Y : P.scheme.Object l' hl'} (A : P.scheme.Object ν hν)
    (h : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hl' Y)) :
    #(Set.range (h.onVertex PUnit.unit)) ≤ ν :=
  Cardinal.mk_range_le.trans (P.scheme.vertex_card hν A PUnit.unit).le

theorem infra_79_stageSeq_spec (hνl : ν ≤ l) {ιs : Type u} (hιs : #ιs ≤ ν)
    (r : ιs → SystemArrow K oneVertexShape (P.scheme.asSystem hl U) (P.scheme.asSystem hl B))
    (S0 : Set ((P.scheme.asSystem hl B).obj PUnit.unit).carrier)
    (T0 : Set ((P.scheme.asSystem hl U).obj PUnit.unit).carrier) (hS0 : #S0 ≤ ν)
    (hT0 : #T0 ≤ ν) :
    (S0 ⊆ Set.range ((infra_79_stageSeq hν (f := f) hνl r S0 T0 0).iA.onVertex PUnit.unit) ∧
      T0 ⊆ Set.range ((infra_79_stageSeq hν (f := f) hνl r S0 T0 0).iV.onVertex PUnit.unit)) ∧
    ∀ n, (Set.range ((infra_79_stageSeq hν (f := f) hνl r S0 T0 n).iA.onVertex PUnit.unit) ∪
        ⋃ i, (r i).onVertex PUnit.unit ''
          Set.range ((infra_79_stageSeq hν (f := f) hνl r S0 T0 n).iV.onVertex PUnit.unit)) ⊆
        Set.range ((infra_79_stageSeq hν (f := f) hνl r S0 T0 (n + 1)).iA.onVertex PUnit.unit) ∧
      Set.range ((infra_79_stageSeq hν (f := f) hνl r S0 T0 n).iV.onVertex PUnit.unit) ⊆
        Set.range ((infra_79_stageSeq hν (f := f) hνl r S0 T0 (n + 1)).iV.onVertex PUnit.unit) := by
  have hν0 : ℵ₀ ≤ ν := P.aleph0_le hν
  refine ⟨by rw [infra_79_stageSeq]; exact infra_79_pick_spec hν hνl S0 T0 hS0 hT0, fun n => ?_⟩
  let st := infra_79_stageSeq hν (f := f) hνl r S0 T0 n
  have hA := infra_79_range_card hν st.A st.iA
  have hV := infra_79_range_card hν st.V st.iV
  have hU : #↥(⋃ i, (r i).onVertex PUnit.unit '' Set.range (st.iV.onVertex PUnit.unit)) ≤ ν := by
    refine (Cardinal.mk_iUnion_le _).trans ?_
    refine (mul_le_mul' hιs (ciSup_le' fun i => Cardinal.mk_image_le.trans hV)).trans ?_
    exact (mul_eq_self hν0).le
  have hS : #↥(Set.range (st.iA.onVertex PUnit.unit) ∪
      ⋃ i, (r i).onVertex PUnit.unit '' Set.range (st.iV.onVertex PUnit.unit)) ≤ ν :=
    (Cardinal.mk_union_le _ _).trans ((add_le_add hA hU).trans (add_eq_self hν0).le)
  rw [infra_79_stageSeq]
  exact infra_79_pick_spec hν hνl _ _ hS hV

end Stages

/-- **`infra_79_retraction_pair` (proved).** The retraction-closed level-`ν` pair of the proof
of Theorem 7.9. -/
theorem infra_79_retraction_pair (P : SingleModelData K) :
    infra_79_retraction_pair_statement P := by
  classical
  intro ν l hν hl hνl X B U ι f uIdx _ bU
  have hν0 : ℵ₀ ≤ ν := P.aleph0_le hν
  obtain ⟨R⟩ := corollary_6_16_family P hl B U f
  have hνR : ν ≤ #R.index := R.index_card.symm ▸ hνl
  obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.mp hνR
  let r : s → SystemArrow K oneVertexShape (P.scheme.asSystem hl.1 U)
      (P.scheme.asSystem hl.1 B) := fun i => R.retr i.1
  have hιs : #s ≤ ν := hs.le
  have hx : ∀ k, ∃ x, bU k = ⟨PUnit.unit, x⟩ := fun k => by
    generalize bU k = o
    rcases o with ⟨⟨⟩, x⟩
    exact ⟨x, rfl⟩
  let T0 : Set ((P.scheme.asSystem hl.1 U).obj PUnit.unit).carrier :=
    Set.range fun k => (hx k).choose
  let S0 : Set ((P.scheme.asSystem hl.1 B).obj PUnit.unit).carrier :=
    Set.range (ι.onVertex PUnit.unit)
  have hS0 : #S0 ≤ ν := Cardinal.mk_range_le.trans (P.scheme.vertex_card hν X PUnit.unit).le
  have hT0 : #T0 ≤ ν :=
    Cardinal.mk_range_le.trans ((Cardinal.lt_aleph0_of_finite uIdx).le.trans hν0)
  let st : ℕ → Infra79Stage P hν hl.1 B U f := infra_79_stageSeq hν hνl r S0 T0
  obtain ⟨⟨h0A, h0V⟩, hstep⟩ := infra_79_stageSeq_spec hν hνl hιs r S0 T0 hS0 hT0
  have hmA : ∀ {a b : ℕ}, a ≤ b →
      Set.range ((st a).iA.onVertex PUnit.unit) ⊆ Set.range ((st b).iA.onVertex PUnit.unit) := by
    intro a b h
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans fun x hx => (hstep _).1 (Or.inl hx)
  have hmV : ∀ {a b : ℕ}, a ≤ b →
      Set.range ((st a).iV.onVertex PUnit.unit) ⊆ Set.range ((st b).iV.onVertex PUnit.unit) := by
    intro a b h
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hstep _).2
  let sA : ∀ {a b : ℕ}, a ≤ b → SystemArrow K oneVertexShape (P.scheme.asSystem hν (st a).A)
      (P.scheme.asSystem hν (st b).A) := fun h =>
    (infra_78_factor_arrow (st _).iA (st _).iA trivial trivial (hmA h)).choose
  have hsA : ∀ {a b : ℕ} (h : a ≤ b), SystemArrow.comp (sA h) (st b).iA = (st a).iA :=
    fun h => (infra_78_factor_arrow (st _).iA (st _).iA trivial trivial (hmA h)).choose_spec.2
  let sV : ∀ {a b : ℕ}, a ≤ b → SystemArrow K oneVertexShape (P.scheme.asSystem hν (st a).V)
      (P.scheme.asSystem hν (st b).V) := fun h =>
    (infra_78_factor_arrow (st _).iV (st _).iV trivial trivial (hmV h)).choose
  have hsV : ∀ {a b : ℕ} (h : a ≤ b), SystemArrow.comp (sV h) (st b).iV = (st a).iV :=
    fun h => (infra_78_factor_arrow (st _).iV (st _).iV trivial trivial (hmV h)).choose_spec.2
  have hAr : ∀ a, sA (le_refl a) = SystemArrow.refl _ := fun a =>
    infra_78_arrow_cancel _ _ (st a).iA ((hsA (le_refl a)).trans (infra_78_refl_comp _).symm)
  have hVr : ∀ a, sV (le_refl a) = SystemArrow.refl _ := fun a =>
    infra_78_arrow_cancel _ _ (st a).iV ((hsV (le_refl a)).trans (infra_78_refl_comp _).symm)
  have hAt : ∀ {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sA (h₁.trans h₂) = SystemArrow.comp (sA h₁) (sA h₂) := fun h₁ h₂ =>
    infra_78_arrow_cancel _ _ (st _).iA (by
      rw [hsA (h₁.trans h₂), SystemArrow.comp_assoc, hsA h₂, hsA h₁])
  have hVt : ∀ {a b c : ℕ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sV (h₁.trans h₂) = SystemArrow.comp (sV h₁) (sV h₂) := fun h₁ h₂ =>
    infra_78_arrow_cancel _ _ (st _).iV (by
      rw [hsV (h₁.trans h₂), SystemArrow.comp_assoc, hsV h₂, hsV h₁])
  have hcomm : ∀ {a b : ℕ} (h : a ≤ b),
      SystemArrow.comp (st a).g (sV h) = SystemArrow.comp (sA h) (st b).g := fun h =>
    infra_78_arrow_cancel _ _ (st _).iV (by
      rw [SystemArrow.comp_assoc, hsV h, (st _).sq, SystemArrow.comp_assoc, (st _).sq,
        ← SystemArrow.comp_assoc, hsA h])
  have hℕ : #(ULift.{u} ℕ) ≤ ν := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]; exact hν0
  obtain ⟨Au, Uu, lA', lU', gu, jA, jU, -, -, -, -, -, -, hlA0, hlU0, hsqU, -, hcovU⟩ :=
    infra_78_theta_union (ι := ULift.{u} ℕ) hν hl.1 hℕ (fun n => (st n.down).A)
      (fun n => (st n.down).V) (fun n => (st n.down).g)
      (fun {a b} h => sA (a := a.down) (b := b.down) h)
      (fun {a b} h => sV (a := a.down) (b := b.down) h)
      (fun a => hAr a.down) (fun a => hVr a.down)
      (fun {a b c} h₁ h₂ => hAt (a := a.down) (b := b.down) (c := c.down) h₁ h₂)
      (fun {a b c} h₁ h₂ => hVt (a := a.down) (b := b.down) (c := c.down) h₁ h₂)
      (fun {a b} h => hcomm (a := a.down) (b := b.down) h) f
      (fun n => (st n.down).iA) (fun n => (st n.down).iV)
      (fun {a b} h => hsA (a := a.down) (b := b.down) h)
      (fun {a b} h => hsV (a := a.down) (b := b.down) h)
      (fun n => (st n.down).sq)
  let lA := fun n : ℕ => lA' (ULift.up n)
  let lU := fun n : ℕ => lU' (ULift.up n)
  have hlA : ∀ n, SystemArrow.comp (lA n) jA = (st n).iA := fun n => hlA0 (ULift.up n)
  have hlU : ∀ n, SystemArrow.comp (lU n) jU = (st n).iV := fun n => hlU0 (ULift.up n)
  have hlA' : ∀ a z, jA.onVertex PUnit.unit ((lA a).onVertex PUnit.unit z) =
      (st a).iA.onVertex PUnit.unit z := fun a z =>
    DFunLike.congr_fun (congrArg (fun h => h.onVertex PUnit.unit) (hlA a)) z
  have hlU' : ∀ a z, jU.onVertex PUnit.unit ((lU a).onVertex PUnit.unit z) =
      (st a).iV.onVertex PUnit.unit z := fun a z =>
    DFunLike.congr_fun (congrArg (fun h => h.onVertex PUnit.unit) (hlU a)) z
  have hy : ∀ k, ∃ y, (st 0).iV.onVertex PUnit.unit y = (hx k).choose := fun k =>
    h0V ⟨k, rfl⟩
  let b' : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hν Uu) := fun k =>
    ⟨PUnit.unit, (lU 0).onVertex PUnit.unit (hy k).choose⟩
  refine ⟨Au, Uu, jA, jU, gu, b', s, r, fun v => ?_, fun k => ?_, fun x => ?_, hs,
    fun a => ?_, fun i x => ?_⟩
  · exact (congrArg (fun h => h.onVertex v) hsqU).symm
  · rw [(hx k).choose_spec]
    refine congrArg (Sigma.mk PUnit.unit) ?_
    exact ((hy k).choose_spec.symm.trans (hlU' 0 _).symm)
  · obtain ⟨z, hz⟩ := h0A ⟨x, rfl⟩
    exact ⟨(lA 0).onVertex PUnit.unit z, (hlA' 0 z).trans hz⟩
  · have := R.almost_id a
    exact Finite.of_injective
      (fun i => (⟨i.1.1, i.2⟩ : {j : R.index //
        (R.retr j).onVertex a.1 (f.onVertex a.1 a.2) ≠ a.2}))
      (fun i j h => by
        apply Subtype.ext; apply Subtype.ext
        have h' := congrArg Subtype.val h
        exact h')
  · obtain ⟨⟨a⟩, y, hya⟩ := hcovU ⟨PUnit.unit, x⟩
    rcases y with ⟨⟨⟩, y⟩
    have hyx : (lU a).onVertex PUnit.unit y = x := eq_of_heq (Sigma.mk.inj hya).2
    have hmem : (r i).onVertex PUnit.unit ((st a).iV.onVertex PUnit.unit y) ∈
        Set.range ((st (a + 1)).iA.onVertex PUnit.unit) :=
      (hstep a).1 (Or.inr (Set.mem_iUnion.2 ⟨i, ⟨_, ⟨y, rfl⟩, rfl⟩⟩))
    obtain ⟨z, hz⟩ := hmem
    refine ⟨(lA (a + 1)).onVertex PUnit.unit z, (hlA' _ z).trans (hz.trans ?_)⟩
    rw [← hyx, hlU']

/-- **Existence clause of Theorem 7.9 (proved, cycle 72).** -/
theorem infra_79_existence (P : SingleModelData K) : infra_79_existence_statement P :=
  infra_79_existence_of_parts P ⟨infra_79_tail P, infra_79_retraction_pair P⟩

end AEC
