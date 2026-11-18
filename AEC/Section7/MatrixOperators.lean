module

public import AEC.Section7.MatrixEngine

@[expose] public section

/-!
# Concrete operators for the Prop 7.8 matrix recursion (grokbot cycle 51)

Split of `infra_78_matrix_operators`; this file is the mark/base part (`infra_78_matrix_mark_ops`).
The extra stage data `Infra78MarkData` carries, as plain data on the fixed carrier, the base map
`g : X_b → X_i`, the mark `b` in `Y_i` and the bookkeeping set `R`.

* `infra_78_SuccSpec`: one successor step (commuting stage arrows, mark and base moved, `R` given
  by an update `Rnext`, invariant (5) at the new stage `infra_78_StageInv5`, and the successor
  dichotomy `infra_78_StageDich` for candidate lists `d`). `infra_78_succSpec_exists`: it exists
  at any stage with invariant (5) (`infra_78_recursion_succ_stage`).
* `infra_78_succOp`: the concrete successor operator (chosen spec, identity fallback), always a
  stage arrow (`infra_78_succOp_stageArr`, the `hsop` input of `infra_78_pairMatrix`).
* `infra_78_limMarkE`: limit data (mark and base moved along a cocone leg, `R` = union of images).
* `infra_78_opMatrix_succ`: successor stages of the resulting matrix meet the spec when the
  previous stage has invariant (5); `infra_78_opMatrix_coherent`: mark/base coherence along all
  chain steps.

The concrete bookkeeping update `Rnext` and candidate-list selection `cand`
(`infra_78_pair_bookkeeping_close` + failing lists from the `S`-part) are tracked as
`infra_78_matrix_bookkeeping_ops`.
-/

universe u
open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}

/-- Plain extra stage data for the Prop 7.8 recursion: base map `g` (from the fixed base
`X_b` into `X_i`), mark `b` (in `Y_i`) and bookkeeping set `R ⊆ |X_i| ⊕ |Y_i|`, all on the fixed
carrier. -/
structure Infra78MarkData (κ : Cardinal.{u}) (uIdx : Type u) where
  g : κ.ord.ToType → κ.ord.ToType
  b : uIdx → κ.ord.ToType
  R : Set (κ.ord.ToType ⊕ κ.ord.ToType)

section SuccOperator
variable {P : SingleModelData K} {κ : Cardinal.{u}} {hκ : κ ∈ P.eligible} {uIdx : Type u}

/-- The mark of a stage as occurrences in `Y`. -/
def infra_78_stageMark (s : Infra78Stage P hκ (Infra78MarkData κ uIdx)) :
    uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ s.Y) :=
  fun k => ⟨PUnit.unit, s.e.b k⟩

/-- Invariant (5) for a plain stage: the base map is an arrow `X_b → X_i` and the mark is tied
free over `X_b` along it. -/
def infra_78_StageInv5 (Xb : P.scheme.Object κ hκ)
    (s : Infra78Stage P hκ (Infra78MarkData κ uIdx)) : Prop :=
  ∃ hg : infra_78_IsArr Xb s.X s.e.g,
    IsTiedFree (infra_78_toArr hg)
      ((infra_78_markTuple (infra_78_toArr s.hp) (infra_78_stageMark s)).restrict
        (infra_78_toArr hg) trivial)
      (infra_78_markTuple (infra_78_toArr s.hp) (infra_78_stageMark s)) (Equiv.refl _)

/-- The successor dichotomy in plain form (identity-type case: all candidates isolated; or a
failing candidate with a nonfree extension along the `X`-step). -/
def infra_78_StageDich {cIdx L : Type u} (s t : Infra78Stage P hκ (Infra78MarkData κ uIdx))
    (stX : SystemArrow K oneVertexShape (P.scheme.asSystem hκ s.X) (P.scheme.asSystem hκ t.X))
    (fY : κ.ord.ToType → κ.ord.ToType) (d : L → cIdx → κ.ord.ToType) : Prop :=
  (∀ l, IsRelativelyIsolated (infra_78_markTuple (infra_78_toArr s.hp)
      (Sum.elim (infra_78_stageMark s) (fun c => ⟨PUnit.unit, d l c⟩)))
      (Equiv.refl (uIdx ⊕ cIdx))) ∨
  ∃ l, ¬ IsRelativelyIsolated (infra_78_markTuple (infra_78_toArr s.hp)
      (Sum.elim (infra_78_stageMark s) (fun c => ⟨PUnit.unit, d l c⟩)))
      (Equiv.refl (uIdx ⊕ cIdx)) ∧
    ¬ IsTiedFree stX
      ((infra_78_markTuple (infra_78_toArr t.hp)
        (fun k => (⟨PUnit.unit, fY (Sum.elim s.e.b (d l) k)⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hκ t.Y)))).restrict stX trivial)
      (infra_78_markTuple (infra_78_toArr t.hp)
        (fun k => (⟨PUnit.unit, fY (Sum.elim s.e.b (d l) k)⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hκ t.Y)))) (Equiv.refl _)

/-- Specification of one successor step of the plain recursion: commuting stage arrows, mark and
base moved along the step, bookkeeping set given by `Rnext`, invariant (5) at the new stage, and
the successor dichotomy for the candidate lists `d`. -/
def infra_78_SuccSpec {cIdx L : Type u} (Xb : P.scheme.Object κ hκ)
    (Rnext : Infra78Stage P hκ (Infra78MarkData κ uIdx) → Infra78Step κ →
      Set (κ.ord.ToType ⊕ κ.ord.ToType))
    (d : L → cIdx → κ.ord.ToType) (s : Infra78Stage P hκ (Infra78MarkData κ uIdx))
    (out : Infra78Stage P hκ (Infra78MarkData κ uIdx) × Infra78Step κ) : Prop :=
  ∃ (hX : infra_78_IsArr s.X out.1.X out.2.1) (_ : infra_78_IsArr s.Y out.1.Y out.2.2),
    out.1.p ∘ out.2.1 = out.2.2 ∘ s.p ∧ out.1.e.g = out.2.1 ∘ s.e.g ∧
    out.1.e.b = out.2.2 ∘ s.e.b ∧ out.1.e.R = Rnext s out.2 ∧
    infra_78_StageInv5 Xb out.1 ∧ infra_78_StageDich s out.1 (infra_78_toArr hX) out.2.2 d

theorem infra_78_succSpec_stageArr {cIdx L : Type u} {Xb : P.scheme.Object κ hκ}
    {Rnext : Infra78Stage P hκ (Infra78MarkData κ uIdx) → Infra78Step κ →
      Set (κ.ord.ToType ⊕ κ.ord.ToType)}
    {d : L → cIdx → κ.ord.ToType} {s : Infra78Stage P hκ (Infra78MarkData κ uIdx)}
    {out : Infra78Stage P hκ (Infra78MarkData κ uIdx) × Infra78Step κ}
    (h : infra_78_SuccSpec Xb Rnext d s out) : infra_78_StageArr s out.1 out.2 :=
  let ⟨hX, hY, hsq, _⟩ := h; ⟨hX, hY, hsq⟩


open Classical in
/-- **The concrete successor operator** of the Prop 7.8 recursion: a successor stage meeting
`infra_78_SuccSpec` for the candidate lists `cand β s` (chosen), or the identity step if none
exists (never used once invariant (5) is propagated). -/
noncomputable def infra_78_succOp {ι cIdx L : Type u} (Xb : P.scheme.Object κ hκ)
    (Rnext : Infra78Stage P hκ (Infra78MarkData κ uIdx) → Infra78Step κ →
      Set (κ.ord.ToType ⊕ κ.ord.ToType))
    (cand : ι → Infra78Stage P hκ (Infra78MarkData κ uIdx) → L → cIdx → κ.ord.ToType)
    (β : ι) (s : Infra78Stage P hκ (Infra78MarkData κ uIdx)) :
    Infra78Stage P hκ (Infra78MarkData κ uIdx) × Infra78Step κ :=
  if h : ∃ out, infra_78_SuccSpec Xb Rnext (cand β s) s out then Classical.choose h
  else (s, infra_78_stepId)

theorem infra_78_succOp_spec {ι cIdx L : Type u} (Xb : P.scheme.Object κ hκ)
    (Rnext : Infra78Stage P hκ (Infra78MarkData κ uIdx) → Infra78Step κ →
      Set (κ.ord.ToType ⊕ κ.ord.ToType))
    (cand : ι → Infra78Stage P hκ (Infra78MarkData κ uIdx) → L → cIdx → κ.ord.ToType)
    (β : ι) (s : Infra78Stage P hκ (Infra78MarkData κ uIdx))
    (h : ∃ out, infra_78_SuccSpec Xb Rnext (cand β s) s out) :
    infra_78_SuccSpec Xb Rnext (cand β s) s (infra_78_succOp Xb Rnext cand β s) := by
  unfold infra_78_succOp
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- The concrete successor operator always produces stage arrows (the `hsop` input of
`infra_78_pairMatrix`). -/
theorem infra_78_succOp_stageArr {ι cIdx L : Type u} (Xb : P.scheme.Object κ hκ)
    (Rnext : Infra78Stage P hκ (Infra78MarkData κ uIdx) → Infra78Step κ →
      Set (κ.ord.ToType ⊕ κ.ord.ToType))
    (cand : ι → Infra78Stage P hκ (Infra78MarkData κ uIdx) → L → cIdx → κ.ord.ToType)
    (β : ι) (s : Infra78Stage P hκ (Infra78MarkData κ uIdx)) :
    infra_78_StageArr s (infra_78_succOp Xb Rnext cand β s).1
      (infra_78_succOp Xb Rnext cand β s).2 := by
  by_cases h : ∃ out, infra_78_SuccSpec Xb Rnext (cand β s) s out
  · exact infra_78_succSpec_stageArr (infra_78_succOp_spec Xb Rnext cand β s h)
  · unfold infra_78_succOp
    rw [dif_neg h]
    exact infra_78_stageArr_id s


open Classical in
/-- **The concrete limit data**: at a limit `k`, the base and mark are moved along the cocone leg
of some earlier stage `j₀` (independent of `j₀` by coherence), and the bookkeeping set is the
union of the images of the earlier sets along the legs. `e0` is a dummy for empty index sets. -/
noncomputable def infra_78_limMarkE {ι : Type u} [Preorder ι] (e0 : Infra78MarkData κ uIdx) (k : ι)
    (cf : Set.Iio k → Infra78Stage P hκ (Infra78MarkData κ uIdx))
    (_mf : Set.Iio k → Set.Iio k → Infra78Step κ) (_Xδ _Yδ : P.scheme.Object κ hκ)
    (_pδ : κ.ord.ToType → κ.ord.ToType) (legs : Set.Iio k → Infra78Step κ) :
    Infra78MarkData κ uIdx :=
  if h : Nonempty (Set.Iio k) then
    ⟨(legs (Classical.choice h)).1 ∘ (cf (Classical.choice h)).e.g,
      (legs (Classical.choice h)).2 ∘ (cf (Classical.choice h)).e.b,
      ⋃ j, Sum.map (legs j).1 (legs j).2 '' (cf j).e.R⟩
  else e0

end SuccOperator

section SuccExists
variable (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
  {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ) {uIdx : Type u}

/-- **Concrete successor step exists** (from `infra_78_recursion_succ_stage`): at a stage with
invariant (5), for any candidate lists `d` with `|b| + |d_l| ≤ σ` and any bookkeeping update
`Rnext`, a successor stage meeting `infra_78_SuccSpec` exists. -/
theorem infra_78_succSpec_exists {cIdx L : Type u}
    (Xb : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
    (Rnext : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx) →
      Infra78Step μ → Set (μ.ord.ToType ⊕ μ.ord.ToType))
    (d : L → cIdx → μ.ord.ToType) (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (s : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
    (h5 : infra_78_StageInv5 Xb s) : ∃ out, infra_78_SuccSpec Xb Rnext d s out := by
  obtain ⟨hg, h5⟩ := h5
  obtain ⟨X', Y', stX, stY, pr', hsq, h5', hdich⟩ :=
    infra_78_recursion_succ_stage P σ hσ hμT (infra_78_toArr s.hp) (infra_78_toArr hg)
      (infra_78_stageMark s) (fun l c => ⟨PUnit.unit, d l c⟩) hidx h5
  let st : Infra78Step μ := (infra_78_plain stX, infra_78_plain stY)
  let t : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx) :=
    ⟨X', Y', infra_78_plain pr', infra_78_isArr_plain pr',
      ⟨infra_78_plain stX ∘ s.e.g, infra_78_plain stY ∘ s.e.b, Rnext s st⟩⟩
  have hpr : infra_78_toArr t.hp = pr' := infra_78_toArr_plain pr'
  have hstX : infra_78_toArr (infra_78_isArr_plain stX) = stX := infra_78_toArr_plain stX
  refine ⟨(t, st), infra_78_isArr_plain stX, infra_78_isArr_plain stY, ?_, rfl, rfl, rfl, ?_, ?_⟩
  · funext x
    have := DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) hsq) x
    show pr'.onVertex PUnit.unit (stX.onVertex PUnit.unit x) =
      stY.onVertex PUnit.unit (s.p x)
    rw [← infra_78_toArr_apply s.hp x]
    exact this.symm
  · have hg' : infra_78_IsArr Xb X' (infra_78_plain stX ∘ s.e.g) := infra_78_isArr_comp hg (infra_78_isArr_plain stX)
    refine ⟨hg', ?_⟩
    have hc : infra_78_toArr hg' = SystemArrow.comp (infra_78_toArr hg) stX := by
      rw [infra_78_toArr_comp hg (infra_78_isArr_plain stX) hg', hstX]
    rw [hc, hpr]
    exact h5'
  · rw [hstX]
    rcases hdich with hall | ⟨l, hl, hnf⟩
    · exact Or.inl hall
    · refine Or.inr ⟨l, hl, ?_⟩
      rw [hpr]
      have hf : (fun k => (⟨PUnit.unit, infra_78_plain stY (Sum.elim s.e.b (d l) k)⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem _ Y'))) =
          fun k => pushOcc stY (Sum.elim (infra_78_stageMark s)
            (fun c => (⟨PUnit.unit, d l c⟩ : Occurrence K oneVertexShape (P.scheme.asSystem _ s.Y))) k) := by
        funext k; cases k <;> rfl
      exact hf ▸ hnf


/-- At a stage with invariant (5) the concrete successor operator meets its specification. -/
theorem infra_78_succOp_spec_of_inv5 {ι cIdx L : Type u}
    (Xb : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
    (Rnext : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx) →
      Infra78Step μ → Set (μ.ord.ToType ⊕ μ.ord.ToType))
    (cand : ι → Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx) →
      L → cIdx → μ.ord.ToType) (hidx : #(uIdx ⊕ cIdx) ≤ σ) (β : ι)
    (s : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
    (h5 : infra_78_StageInv5 Xb s) :
    infra_78_SuccSpec Xb Rnext (cand β s) s (infra_78_succOp Xb Rnext cand β s) :=
  infra_78_succOp_spec Xb Rnext cand β s
    (infra_78_succSpec_exists P σ hσ hμT Xb Rnext (cand β s) hidx s h5)

/-- **Successor stages of the recursion matrix** built with the concrete successor operator:
if stage `β` has invariant (5) and `β ⋖ k`, then stage `k` is the specified successor of stage
`β` (commuting arrows, mark/base moved, `R = Rnext`, invariant (5), dichotomy). -/
theorem infra_78_opMatrix_succ {ρ : Cardinal.{u}} (hρκ : Order.succ ρ < μ) {cIdx L : Type u}
    (Xb : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
    (Rnext : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx) →
      Infra78Step μ → Set (μ.ord.ToType ⊕ μ.ord.ToType))
    (cand : (Order.succ ρ).ord.ToType →
      Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx) →
      L → cIdx → μ.ord.ToType) (hidx : #(uIdx ⊕ cIdx) ≤ σ)
    (s0 : Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx))
    (limE : (k : (Order.succ ρ).ord.ToType) →
      (Set.Iio k → Infra78Stage P (Tail.mem (infra_73_tail P σ hσ) hμT) (Infra78MarkData μ uIdx)) →
      (Set.Iio k → Set.Iio k → Infra78Step μ) → P.scheme.Object μ _ → P.scheme.Object μ _ →
      (μ.ord.ToType → μ.ord.ToType) → (Set.Iio k → Infra78Step μ) → Infra78MarkData μ uIdx)
    {β k : (Order.succ ρ).ord.ToType} (hβ : β ⋖ k)
    (h5 : infra_78_StageInv5 Xb (infra_78_pcObj s0 (infra_78_succOp Xb Rnext cand) limE β)) :
    infra_78_SuccSpec Xb Rnext (cand β (infra_78_pcObj s0 (infra_78_succOp Xb Rnext cand) limE β))
      (infra_78_pcObj s0 (infra_78_succOp Xb Rnext cand) limE β)
      (infra_78_pcObj s0 (infra_78_succOp Xb Rnext cand) limE k,
        infra_78_pcMap s0 (infra_78_succOp Xb Rnext cand) limE β k) := by
  obtain ⟨hc, hm⟩ := infra_78_pairMatrix_succ hρκ s0 (infra_78_succOp Xb Rnext cand) limE
    (infra_78_succOp_stageArr Xb Rnext cand) hβ
  rw [hc, hm]
  exact infra_78_succOp_spec_of_inv5 P σ hσ hμT Xb Rnext cand hidx β _ h5


end SuccExists

section Coherence
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible} {uIdx cIdx L : Type u}
variable (hρκ : Order.succ ρ < κ) (Xb : P.scheme.Object κ hκ)
  (Rnext : Infra78Stage P hκ (Infra78MarkData κ uIdx) → Infra78Step κ →
    Set (κ.ord.ToType ⊕ κ.ord.ToType))
  (cand : (Order.succ ρ).ord.ToType → Infra78Stage P hκ (Infra78MarkData κ uIdx) →
    L → cIdx → κ.ord.ToType)
  (s0 : Infra78Stage P hκ (Infra78MarkData κ uIdx)) (e0 : Infra78MarkData κ uIdx)

/-- The concrete operators move the mark and the base along each successor step (also in the
identity fallback). -/
theorem infra_78_succOp_moves {ι : Type u} (cand : ι → Infra78Stage P hκ (Infra78MarkData κ uIdx) →
    L → cIdx → κ.ord.ToType) (β : ι) (s : Infra78Stage P hκ (Infra78MarkData κ uIdx)) :
    (infra_78_succOp Xb Rnext cand β s).1.e.g = (infra_78_succOp Xb Rnext cand β s).2.1 ∘ s.e.g ∧
    (infra_78_succOp Xb Rnext cand β s).1.e.b = (infra_78_succOp Xb Rnext cand β s).2.2 ∘ s.e.b := by
  by_cases h : ∃ out, infra_78_SuccSpec Xb Rnext (cand β s) s out
  · obtain ⟨-, -, -, hg, hb, -⟩ := infra_78_succOp_spec Xb Rnext cand β s h
    exact ⟨hg, hb⟩
  · unfold infra_78_succOp
    rw [dif_neg h]
    exact ⟨rfl, rfl⟩

include hρκ in
/-- **Mark/base coherence** of the recursion matrix built from the concrete operators: for
`i ≤ k`, the base and mark at stage `k` are those at stage `i` moved along the chain step. -/
theorem infra_78_opMatrix_coherent (i k : (Order.succ ρ).ord.ToType) (hik : i ≤ k) :
    (infra_78_pcObj s0 (infra_78_succOp Xb Rnext cand) (infra_78_limMarkE e0) k).e.g =
      (infra_78_pcMap s0 (infra_78_succOp Xb Rnext cand) (infra_78_limMarkE e0) i k).1 ∘
        (infra_78_pcObj s0 (infra_78_succOp Xb Rnext cand) (infra_78_limMarkE e0) i).e.g ∧
    (infra_78_pcObj s0 (infra_78_succOp Xb Rnext cand) (infra_78_limMarkE e0) k).e.b =
      (infra_78_pcMap s0 (infra_78_succOp Xb Rnext cand) (infra_78_limMarkE e0) i k).2 ∘
        (infra_78_pcObj s0 (infra_78_succOp Xb Rnext cand) (infra_78_limMarkE e0) i).e.b := by
  have hsop := infra_78_succOp_stageArr Xb Rnext cand
  obtain ⟨-, hI, hC⟩ := infra_78_pairChain_laws hρκ s0 (infra_78_succOp Xb Rnext cand)
    (infra_78_limMarkE e0) hsop
  set c := infra_78_pcObj s0 (infra_78_succOp Xb Rnext cand) (infra_78_limMarkE e0) with hc
  set m := infra_78_pcMap s0 (infra_78_succOp Xb Rnext cand) (infra_78_limMarkE e0) with hm
  induction k using WellFoundedLT.induction generalizing i with
  | _ k IH =>
  rcases hik.lt_or_eq with hik | rfl
  swap
  · rw [hI]; exact ⟨rfl, rfl⟩
  by_cases hs : ∃ β, β ⋖ k
  · obtain ⟨β, hβ⟩ := hs
    obtain ⟨hck, hmk⟩ := infra_78_pairMatrix_succ hρκ s0 (infra_78_succOp Xb Rnext cand)
      (infra_78_limMarkE e0) hsop hβ
    have hck' : c k = (infra_78_succOp Xb Rnext cand β (c β)).1 := hck
    have hmk' : m β k = (infra_78_succOp Xb Rnext cand β (c β)).2 := hmk
    have hmv := infra_78_succOp_moves Xb Rnext cand β (c β)
    have hiβ : i ≤ β := hβ.le_of_lt hik
    obtain ⟨IHg, IHb⟩ := IH β hβ.lt i hiβ
    rw [hC i β k hiβ hβ.le, hck', hmk']
    refine ⟨?_, ?_⟩
    · rw [hmv.1, IHg]; rfl
    · rw [hmv.2, IHb]; rfl
  have hmin : ¬ IsMin k := fun h => absurd hik (not_lt.2 (h hik.le))
  have hk : Order.IsSuccLimit k := ⟨hmin, fun b hb => hs ⟨b, hb⟩⟩
  have hL := (infra_78_pairMatrix_limit hρκ s0 (infra_78_succOp Xb Rnext cand)
    (infra_78_limMarkE e0) hsop hk).2.2.1
  have hne : Nonempty (Set.Iio k) := ⟨⟨i, hik⟩⟩
  simp only [infra_78_limMarkE, dif_pos hne] at hL
  set j0 := Classical.choice hne
  have key : ∀ {D : Type u} (f : Infra78MarkData κ uIdx → D → κ.ord.ToType)
      (π : Infra78Step κ → κ.ord.ToType → κ.ord.ToType)
      (hπ : ∀ a b, π (infra_78_stepComp a b) = π b ∘ π a)
      (IHf : ∀ y, y < k → ∀ x, x ≤ y → f (c y).e = π (m x y) ∘ f (c x).e),
      π (m j0.1 k) ∘ f (c j0.1).e = π (m i k) ∘ f (c i).e := by
    intro D f π hπ IHf
    rcases le_total i j0.1 with h | h
    · rw [IHf j0.1 j0.2 i h, hC i j0.1 k h j0.2.le, hπ]; rfl
    · rw [IHf i hik j0.1 h, hC j0.1 i k h hik.le, hπ]; rfl
  refine ⟨?_, ?_⟩
  · rw [congrArg Infra78MarkData.g hL]
    exact key (fun e => e.g) (fun a => a.1) (fun _ _ => rfl) (fun y hy x hx => (IH y hy x hx).1)
  · rw [congrArg Infra78MarkData.b hL]
    exact key (fun e => e.b) (fun a => a.2) (fun _ _ => rfl) (fun y hy x hx => (IH y hy x hx).2)

end Coherence
end AEC
