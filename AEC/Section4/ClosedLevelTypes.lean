module

public import AEC.Section4.ClosedLevelAmalgam

@[expose] public section

/-!
# Amalgamation and singleton types over a `μ`-model (Theorem 4.11, the three clauses)

Let `μ` be a closed level (`ClosedLevel K E D g μ`). A `μ`-model `A` is identified with
`E(I)`, `I` the well-order `μ.ord.ToType`, by categoricity at `μ`.

* `ClosedLevel.amalgamation`: two `μ`-sized strong extensions of `A` have a strong amalgam of
  size `μ` (clause 1).
* `ClosedLevel.exists_tuple_amalgam`, `ClosedLevel.tuple_amalgamation_iff`: tuples of length
  at most `σ < μ` are identified in an amalgam over `A` exactly when their diagrams agree over
  the subsets of `A` of size at most `g(σ) + ℓ` (clause 2).
* `ClosedLevel.singleton_types`: the amalgam types over `A` of the elements of the `μ`-sized
  strong extensions of `A` are coded by `μ` codes (clause 3).

For clause 3: a placement of a singleton uses one label on a finite support; relative to the
well-order `I`, each support position is coded by the least old position at or above it and
the least old position strictly above it (`Placement.singletonCode`, at most `μ` codes,
`mk_singletonCode_le`). These data determine the placed comparison over `A`
(`Placement.AgreeOn.of_sameProfile_univ`, by `sameNaturalDiagram_of_pattern`). The code of an
element is the least code of a placement lifting its bounded diagrams; the placements lifting
them form one class of the placed comparison (Lemma 4.10), and clause 2 identifies exactly
the elements with equal comparison.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

/-! ## The support pattern over all of `I` determines the placed comparison -/

section Pattern

variable {E : OrderPresentation K} {D : StableDiagram K} {I : Type u} [LinearOrder I]
  [Nonempty I] {α : Type u}

/-- **The support profile over all old positions determines the placed comparison.** Two
placements with the same labels, the same order pattern of their supports, and the same
comparisons of every support position with every position of `I` have the same natural diagram
with every list of parameters of `E(I)`. -/
theorem Placement.AgreeOn.of_sameProfile_univ {P P' : Placement E.lab E.arity I α}
    (h : SameProfile Set.univ P P') : P.AgreeOn E D P' Set.univ := by
  intro β par τ _ hj _
  refine sameNaturalDiagram_of_pattern _ _ ?_ ?_
  · rintro (a | b)
    · exact h.1 a
    · rfl
  · rintro (a | b) (a' | b') k l hk hl hk' hl'
    · exact h.2.1 a a' k l hk hl hk' hl'
    · exact (h.2.2 a k hk hk' ((par b').pos ⟨l, hl⟩) (Set.mem_univ _)).2
    · exact (h.2.2 a' l hl hl' ((par b).pos ⟨k, hk⟩) (Set.mem_univ _)).1
    · exact P.f.lt_iff_lt.trans P'.f.lt_iff_lt.symm

end Pattern

/-! ## Codes of placements of a singleton -/

section SingletonCode

variable {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I] [WellFoundedLT I]

/-- Codes of placements of a singleton over the well-order `I`: the label, and for each of its
finitely many support positions the least old position at or above it and the least old
position strictly above it. -/
abbrev SingletonCode (lab : Type u) (arity : lab → ℕ) (I : Type u) : Type u :=
  Σ l : lab, Fin (arity l) → Option ↥(Set.univ : Set I) × Option ↥(Set.univ : Set I)

/-- The code of a placement of a singleton. -/
noncomputable def Placement.singletonCode (P : Placement lab arity I PUnit.{u + 1}) :
    SingletonCode lab arity I :=
  ⟨(P.z PUnit.unit).label, fun k => P.cutCode Set.univ ((P.z PUnit.unit).pos k)⟩

/-- Placements of a singleton with the same code have the same support profile over all old
positions. -/
theorem sameProfile_of_singletonCode_eq {P P' : Placement lab arity I PUnit.{u + 1}}
    (h : P.singletonCode = P'.singletonCode) : SameProfile Set.univ P P' := by
  have key : ∀ (t : SupportTerm lab arity P.J) (t' : SupportTerm lab arity P'.J),
      (⟨t.label, fun k => P.cutCode Set.univ (t.pos k)⟩ : SingletonCode lab arity I) =
          ⟨t'.label, fun k => P'.cutCode Set.univ (t'.pos k)⟩ →
        t.label = t'.label ∧ ∀ k (hk : k < arity t.label) (hk' : k < arity t'.label),
          P.cutCode Set.univ (t.pos ⟨k, hk⟩) = P'.cutCode Set.univ (t'.pos ⟨k, hk'⟩) := by
    rintro ⟨l, pos, inc⟩ ⟨l', pos', inc'⟩ h
    obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp h
    exact ⟨rfl, fun k hk hk' => congrFun (eq_of_heq h2) ⟨k, hk⟩⟩
  obtain ⟨hlab, hcut⟩ := key _ _ h
  refine ⟨fun _ => hlab, fun a b k l hk hl hk' hl' => ?_,
    fun a k hk hk' s hs => Placement.cutCode_eq (hcut k hk hk') hs⟩
  exact ((P.z a).increasing.lt_iff_lt.trans Fin.mk_lt_mk).trans
    ((P'.z a).increasing.lt_iff_lt.trans Fin.mk_lt_mk).symm

/-- **There are at most `μ` codes of singleton placements** over a well-order of size at most
`μ`, with at most `μ` labels. -/
theorem mk_singletonCode_le {μ : Cardinal.{u}} (hμ : aleph0 ≤ μ) (hlab : #lab ≤ μ)
    (hI : #I ≤ μ) : #(SingletonCode lab arity I) ≤ μ := by
  have hopt : #(Option ↥(Set.univ : Set I)) ≤ μ := by
    rw [mk_option, mk_univ]
    exact add_le_of_le hμ hI (one_le_aleph0.trans hμ)
  have hprod : #(Option ↥(Set.univ : Set I) × Option ↥(Set.univ : Set I)) ≤ μ :=
    mk_prod_le_of_le hμ hopt hopt
  have hfib : ∀ l : lab,
      #(Fin (arity l) → Option ↥(Set.univ : Set I) × Option ↥(Set.univ : Set I)) ≤ μ := by
    intro l
    have e : #(Fin (arity l) → Option ↥(Set.univ : Set I) × Option ↥(Set.univ : Set I)) =
        #(Option ↥(Set.univ : Set I) × Option ↥(Set.univ : Set I)) ^ (arity l) := by
      simp
    rw [e]
    exact (power_le_power_right hprod).trans (power_nat_le hμ)
  rw [mk_sigma]
  refine (sum_le_sum _ (fun _ => μ) hfib).trans ?_
  rw [sum_const', ]
  exact (mul_le_mul' hlab le_rfl).trans (mul_eq_self hμ).le

end SingletonCode

/-! ## Lifts and amalgams -/

section Amalgam

variable {E : OrderPresentation K} {D : StableDiagram K} {g : Cardinal.{u} → Cardinal.{u}}
  {μ : Cardinal.{u}} {I : Type u} [LinearOrder I] [Nonempty I]
  {B₀ B₁ : Model K.τ} {hB₀ : K.Mem B₀} {hB₁ : K.Mem B₁}
  {incl₀ : Language.Embedding K.τ (E.obj I).carrier B₀.carrier}
  {incl₁ : Language.Embedding K.τ (E.obj I).carrier B₁.carrier}
  {α : Type u}

/-- Necessity, for lifts: if an amalgam over `A` identifies `d₀` with `d₁`, a placement
lifting the bounded diagrams of `d₀` lifts those of `d₁`. -/
theorem Placement.LiftsBounded.of_amalgam {Q : Placement E.lab E.arity I α}
    {d₀ : α → B₀.carrier} {d₁ : α → B₁.carrier} (h : Q.LiftsBounded E D hB₀ incl₀ d₀ μ)
    (hB₀μ : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ Model.card B₀)
    {P : Model K.τ} (hP : K.Mem P) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
    (g₁ : Language.Embedding K.τ B₁.carrier P.carrier) (hg₀ : K.Strong g₀)
    (hg₁ : K.Strong g₁) (hincl : ∀ x, g₀ (incl₀ x) = g₁ (incl₁ x))
    (hd : ∀ i, g₀ (d₀ i) = g₁ (d₁ i)) :
    Q.LiftsBounded E D hB₁ incl₁ d₁ μ := by
  intro β ρ hρinf hρ p hj hBc₁ hJc
  have hBc₀ := hB₀μ ρ hρinf hρ
  have h1 := D.same_of_amalgam hB₁ hB₀ hP g₁ g₀ hg₁ hg₀
    (Sum.elim d₁ (fun b => incl₁ (p b))) (Sum.elim d₀ (fun b => incl₀ (p b))) (by
      rintro (a | b)
      · exact (hd a).symm
      · exact (hincl (p b)).symm) hρinf hj hBc₁ hBc₀
  exact D.trans hj hB₁ hB₀ _ hBc₁ hBc₀ hJc _ _ _ h1 (h ρ hρinf hρ p hj hBc₀ hJc)

end Amalgam

/-! ## The three clauses over a `μ`-model -/

section Base

variable [CategoricalUnbounded K] {E : OrderPresentation K} {D : StableDiagram K}
  {g : Cardinal.{u} → Cardinal.{u}} {μ : Cardinal.{u}}

theorem below_nonempty {μ : Cardinal.{u}} (hμ : aleph0 ≤ μ) : Nonempty (Below μ) :=
  mk_ne_zero_iff.mp (by rw [mk_ord_toType]; exact (aleph0_pos.trans_le hμ).ne')

/-- **Theorem 4.11 (1).** At a closed level `μ`, two `μ`-sized strong extensions of a
`μ`-model have a strong amalgam of size `μ`. -/
theorem ClosedLevel.amalgamation (hL : ClosedLevel K E D g μ) (A B₀ B₁ : Model K.τ)
    (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
    (f₁ : Language.Embedding K.τ A.carrier B₁.carrier)
    (hA : K.Mem A) (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁) (hf₀ : K.Strong f₀) (hf₁ : K.Strong f₁)
    (hcA : Model.card A = μ) (hc₀ : Model.card B₀ = μ) (hc₁ : Model.card B₁ = μ) :
    ∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
      (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
      K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧ Model.card P = μ ∧
      ∀ x, g₀ (f₀ x) = g₁ (f₁ x) := by
  haveI : Nonempty (Below μ) := below_nonempty hL.inf
  have hI : #(Below μ) = μ := mk_ord_toType μ
  have hEI : K.Mem (E.obj (Below μ)) := orderPresentation_obj_mem E _
  have hIc : Model.card (E.obj (Below μ)) = μ :=
    orderPresentation_obj_card E hI hL.ls_lt.le hL.inf
  obtain ⟨e⟩ := hL.cat.unique_model (E.obj (Below μ)) A hEI hA hIc hcA
  have he : K.Strong e.toEmbedding := strong_of_equiv K e hEI
  have hs₀ : K.Strong (f₀.comp e.toEmbedding) := K.strong_trans _ _ he hf₀
  have hs₁ : K.Strong (f₁.comp e.toEmbedding) := K.strong_trans _ _ he hf₁
  have hIμ : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ Model.card (E.obj (Below μ)) :=
    fun ρ h1 h2 => (hL.t_lt h1 h2).le.trans hIc.ge
  obtain ⟨L, linL, nonL, F, hLc, hcatL⟩ := exists_categorical_extension E (Below μ) (D.t μ)
  let a : PEmpty.{u + 1} → (E.obj (Below μ)).carrier := fun x => x.elim
  obtain ⟨P, g₀, g₁, hP, hg₀, hg₁, hcP, hincl, -⟩ :=
    exists_amalgam_of_common_lift (hB₀ := hB₀) (hB₁ := hB₁) hL hI hs₀ hs₁ hc₀ hc₁ F hcatL hLc
      (fun i => (f₀.comp e.toEmbedding) (a i)) (fun i => (f₁.comp e.toEmbedding) (a i))
      (by rw [mk_pempty]; exact aleph0_pos.trans_le hL.inf) (fun i => E.map F (a i))
      (liftsTuple_of_base hs₀ hIμ F a) (liftsTuple_of_base hs₁ hIμ F a)
  refine ⟨P, g₀, g₁, hP, hg₀, hg₁, hcP, fun x => ?_⟩
  have h := hincl (e.symm x)
  simpa [Language.Embedding.comp_apply] using h

/-- **Theorem 4.11 (2), sufficiency.** If the diagrams of `d₀` and `d₁` agree over the subsets
of `A` of size at most `g(σ) + ℓ`, an amalgam of size `μ` over `A` identifies `d₀` with `d₁`.

Proposition 4.8 identifies the placed lifts of `d₀`, `d₁` over `A`; the common lift is realized
once in `G`, and both extensions embed into `G` over `A` extending it. -/
theorem ClosedLevel.exists_tuple_amalgam (hL : ClosedLevel K E D g μ) {σ : Cardinal.{u}}
    (hσinf : aleph0 ≤ σ) (hσ : σ < μ) {α : Type u} (hα : #α ≤ σ) (A B₀ B₁ : Model K.τ)
    (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
    (f₁ : Language.Embedding K.τ A.carrier B₁.carrier)
    (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier)
    (hA : K.Mem A) (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁) (hf₀ : K.Strong f₀) (hf₁ : K.Strong f₁)
    (hcA : Model.card A = μ) (hc₀ : Model.card B₀ = μ) (hc₁ : Model.card B₁ = μ)
    (htest : ∀ {β : Type u} (_ : #β ≤ g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (p : β → A.carrier) (hjoint : #(α ⊕ β) ≤ ρ)
      (h₀ : D.t ρ ≤ Model.card B₀) (h₁ : D.t ρ ≤ Model.card B₁),
      D.same hjoint hB₀ hB₁ h₀ h₁
        (Sum.elim d₀ (fun b => f₀ (p b))) (Sum.elim d₁ (fun b => f₁ (p b)))) :
    ∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
      (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
      K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧ Model.card P = μ ∧
      (∀ x, g₀ (f₀ x) = g₁ (f₁ x)) ∧ ∀ i, g₀ (d₀ i) = g₁ (d₁ i) := by
  haveI : Nonempty (Below μ) := below_nonempty hL.inf
  have hI : #(Below μ) = μ := mk_ord_toType μ
  have hEI : K.Mem (E.obj (Below μ)) := orderPresentation_obj_mem E _
  have hIc : Model.card (E.obj (Below μ)) = μ :=
    orderPresentation_obj_card E hI hL.ls_lt.le hL.inf
  obtain ⟨e⟩ := hL.cat.unique_model (E.obj (Below μ)) A hEI hA hIc hcA
  have he : K.Strong e.toEmbedding := strong_of_equiv K e hEI
  have hs₀ : K.Strong (f₀.comp e.toEmbedding) := K.strong_trans _ _ he hf₀
  have hs₁ : K.Strong (f₁.comp e.toEmbedding) := K.strong_trans _ _ he hf₁
  obtain ⟨P₀, hP₀, -⟩ := exists_boundedDiagramLift (hB := hB₀)
    (incl := f₀.comp e.toEmbedding) (d := d₀) hL.tester hL.closure hσinf hσ hL.ls_lt hL.cat
    hI hs₀ hc₀ hα
  obtain ⟨P₁, hP₁, -⟩ := exists_boundedDiagramLift (hB := hB₁)
    (incl := f₁.comp e.toEmbedding) (d := d₁) hL.tester hL.closure hσinf hσ hL.ls_lt hL.cat
    hI hs₁ hc₁ hα
  have hag : P₀.AgreeOn E D P₁ Set.univ :=
    agreeOn_univ_of_tests hL hI hc₀ hc₁ hσinf hσ hα d₀ d₁ hP₀ hP₁
      (fun {β} hβ ρ hρinf hρ p hj hBc₀ hBc₁ =>
        htest hβ ρ hρinf hρ (fun b => e (p b)) hj hBc₀ hBc₁)
  obtain ⟨P, g₀, g₁, hP, hg₀, hg₁, hcP, hincl, hd⟩ :=
    exists_amalgam_of_agreeOn hL hI hs₀ hs₁ hc₀ hc₁ d₀ d₁ (hα.trans_lt hσ) hP₀ hP₁ hag
  refine ⟨P, g₀, g₁, hP, hg₀, hg₁, hcP, fun x => ?_, hd⟩
  have h := hincl (e.symm x)
  simpa [Language.Embedding.comp_apply] using h

/-- **Theorem 4.11 (2).** At a closed level `μ`, tuples `d₀`, `d₁` of length at most an
infinite `σ < μ` in two `μ`-sized strong extensions of a `μ`-model `A` are identified in an
amalgam over `A` if and only if their diagrams agree over the subsets of `A` of size at most
`g(σ) + ℓ`. -/
theorem ClosedLevel.tuple_amalgamation_iff (hL : ClosedLevel K E D g μ) {σ : Cardinal.{u}}
    (hσinf : aleph0 ≤ σ) (hσ : σ < μ) {α : Type u} (hα : #α ≤ σ) (A B₀ B₁ : Model K.τ)
    (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
    (f₁ : Language.Embedding K.τ A.carrier B₁.carrier)
    (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier)
    (hA : K.Mem A) (hB₀ : K.Mem B₀) (hB₁ : K.Mem B₁) (hf₀ : K.Strong f₀) (hf₁ : K.Strong f₁)
    (hcA : Model.card A = μ) (hc₀ : Model.card B₀ = μ) (hc₁ : Model.card B₁ = μ) :
    (∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
        (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
        K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧
        (∀ x, g₀ (f₀ x) = g₁ (f₁ x)) ∧ ∀ i, g₀ (d₀ i) = g₁ (d₁ i)) ↔
      ∀ {β : Type u} (_ : #β ≤ g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ) (_ : ρ < μ)
        (p : β → A.carrier) (hjoint : #(α ⊕ β) ≤ ρ)
        (h₀ : D.t ρ ≤ Model.card B₀) (h₁ : D.t ρ ≤ Model.card B₁),
        D.same hjoint hB₀ hB₁ h₀ h₁
          (Sum.elim d₀ (fun b => f₀ (p b))) (Sum.elim d₁ (fun b => f₁ (p b))) := by
  constructor
  · rintro ⟨P, g₀, g₁, hP, hg₀, hg₁, hbase, hd⟩ β _ ρ hρinf _ p hj h₀ h₁
    refine D.same_of_amalgam hB₀ hB₁ hP g₀ g₁ hg₀ hg₁ _ _ ?_ hρinf hj h₀ h₁
    rintro (a | b)
    · exact hd a
    · exact hbase (p b)
  · intro htest
    obtain ⟨P, g₀, g₁, hP, hg₀, hg₁, -, hbase, hd⟩ :=
      hL.exists_tuple_amalgam hσinf hσ hα A B₀ B₁ f₀ f₁ d₀ d₁ hA hB₀ hB₁ hf₀ hf₁ hcA hc₀ hc₁
        htest
    exact ⟨P, g₀, g₁, hP, hg₀, hg₁, hbase, hd⟩

open Classical in
/-- The least element of a nonempty set of a well-order (a default value otherwise). -/
noncomputable def leastCode {T : Type u} [LinearOrder T] [WellFoundedLT T] [Nonempty T]
    (S : Set T) : T :=
  if h : S.Nonempty then wellFounded_lt.min S h else Classical.arbitrary T

theorem leastCode_mem {T : Type u} [LinearOrder T] [WellFoundedLT T] [Nonempty T]
    {S : Set T} (h : S.Nonempty) : leastCode S ∈ S := by
  simp only [leastCode, h, ↓reduceDIte]
  exact wellFounded_lt.min_mem S h

/-- **Theorem 4.11 (3).** At a closed level `μ`, the amalgam types over a `μ`-model `A` of the
elements of the `μ`-sized strong extensions of `A` are coded by `μ` codes: two elements have
the same code if and only if an amalgam over `A` identifies them (and then one of size `μ`
does). -/
theorem ClosedLevel.singleton_types (hL : ClosedLevel K E D g μ) (A : Model K.τ)
    (hA : K.Mem A) (hcA : Model.card A = μ) :
    ∃ code : ∀ (B : Model K.τ), Language.Embedding K.τ A.carrier B.carrier →
        B.carrier → μ.ord.ToType,
      ∀ (B₀ B₁ : Model K.τ) (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
        (f₁ : Language.Embedding K.τ A.carrier B₁.carrier),
        K.Mem B₀ → K.Mem B₁ → K.Strong f₀ → K.Strong f₁ →
        Model.card B₀ = μ → Model.card B₁ = μ →
        ∀ (x : B₀.carrier) (y : B₁.carrier),
          (code B₀ f₀ x = code B₁ f₁ y →
            ∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
              (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
              K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧ Model.card P = μ ∧
              (∀ a, g₀ (f₀ a) = g₁ (f₁ a)) ∧ g₀ x = g₁ y) ∧
          ((∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
              (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
              K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧
              (∀ a, g₀ (f₀ a) = g₁ (f₁ a)) ∧ g₀ x = g₁ y) →
            code B₀ f₀ x = code B₁ f₁ y) := by
  classical
  haveI : Nonempty (Below μ) := below_nonempty hL.inf
  have hμinf := hL.inf
  have hI : #(Below μ) = μ := mk_ord_toType μ
  have hEI : K.Mem (E.obj (Below μ)) := orderPresentation_obj_mem E _
  have hIc : Model.card (E.obj (Below μ)) = μ :=
    orderPresentation_obj_card E hI hL.ls_lt.le hμinf
  obtain ⟨e⟩ := hL.cat.unique_model (E.obj (Below μ)) A hEI hA hIc hcA
  have he : K.Strong e.toEmbedding := strong_of_equiv K e hEI
  -- at most `μ` codes
  have hcodes : #(SingletonCode E.lab E.arity (Below μ)) ≤ #(Below μ) := by
    rw [hI]
    refine mk_singletonCode_le hμinf ?_ hI.le
    exact (E.lab_small.trans E.ell_eq.le).trans hL.ls_lt.le
  obtain ⟨enc⟩ := (Cardinal.le_def _ _).mp hcodes
  -- the codes of the placements lifting the bounded diagrams of an element
  let codes : ∀ (B : Model K.τ), Language.Embedding K.τ A.carrier B.carrier →
      B.carrier → Set (Below μ) := fun B f x =>
    {o | ∃ (hB : K.Mem B) (Q : Placement E.lab E.arity (Below μ) PUnit.{u + 1}),
      Q.LiftsBounded E D hB (f.comp e.toEmbedding) (fun _ => x) μ ∧
        enc Q.singletonCode = o}
  have hone : #PUnit.{u + 1} ≤ aleph0 := by
    rw [mk_punit]
    exact one_le_aleph0
  have hne : ∀ (B : Model K.τ) (f : Language.Embedding K.τ A.carrier B.carrier),
      K.Mem B → K.Strong f → Model.card B = μ → ∀ x, (codes B f x).Nonempty := by
    intro B f hB hf hc x
    obtain ⟨Q, hQ, -⟩ := exists_boundedDiagramLift (hB := hB)
      (incl := f.comp e.toEmbedding) (d := fun _ : PUnit.{u + 1} => x) hL.tester hL.closure
      le_rfl hL.aleph0_lt hL.ls_lt hL.cat hI (K.strong_trans _ _ he hf) hc hone
    exact ⟨_, hB, Q, hQ, rfl⟩
  have hsub : ∀ (B₀ B₁ : Model K.τ) (f₀ : Language.Embedding K.τ A.carrier B₀.carrier)
      (f₁ : Language.Embedding K.τ A.carrier B₁.carrier), K.Mem B₁ → Model.card B₀ = μ →
      ∀ (x : B₀.carrier) (y : B₁.carrier) (P : Model K.τ)
        (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
        (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
        K.Mem P → K.Strong g₀ → K.Strong g₁ → (∀ a, g₀ (f₀ a) = g₁ (f₁ a)) → g₀ x = g₁ y →
        codes B₀ f₀ x ⊆ codes B₁ f₁ y := by
    rintro B₀ B₁ f₀ f₁ hB₁ hc₀ x y P g₀ g₁ hP hg₀ hg₁ hbase hxy o ⟨hB₀, Q, hQ, rfl⟩
    refine ⟨hB₁, Q, ?_, rfl⟩
    exact hQ.of_amalgam (fun ρ h1 h2 => (hL.t_lt h1 h2).le.trans hc₀.ge) hP g₀ g₁ hg₀ hg₁
      (fun a => hbase (e a)) (fun _ => hxy)
  refine ⟨fun B f x => leastCode (codes B f x), ?_⟩
  intro B₀ B₁ f₀ f₁ hB₀ hB₁ hf₀ hf₁ hc₀ hc₁ x y
  constructor
  · intro hcode
    have h0 := leastCode_mem (hne B₀ f₀ hB₀ hf₀ hc₀ x)
    have h1 := leastCode_mem (hne B₁ f₁ hB₁ hf₁ hc₁ y)
    change leastCode (codes B₀ f₀ x) = leastCode (codes B₁ f₁ y) at hcode
    rw [← hcode] at h1
    obtain ⟨hB₀', Q₀, hQ₀, hq₀⟩ := h0
    obtain ⟨hB₁', Q₁, hQ₁, hq₁⟩ := h1
    have hsame : SameProfile Set.univ Q₀ Q₁ :=
      sameProfile_of_singletonCode_eq (enc.injective (hq₀.trans hq₁.symm))
    obtain ⟨P, g₀, g₁, hP, hg₀, hg₁, hcP, hincl, hd⟩ :=
      exists_amalgam_of_agreeOn hL hI (K.strong_trans _ _ he hf₀) (K.strong_trans _ _ he hf₁)
        hc₀ hc₁ (fun _ : PUnit.{u + 1} => x) (fun _ => y) (hone.trans_lt hL.aleph0_lt)
        hQ₀ hQ₁ (Placement.AgreeOn.of_sameProfile_univ hsame)
    refine ⟨P, g₀, g₁, hP, hg₀, hg₁, hcP, fun a => ?_, hd PUnit.unit⟩
    have h := hincl (e.symm a)
    simpa [Language.Embedding.comp_apply] using h
  · rintro ⟨P, g₀, g₁, hP, hg₀, hg₁, hbase, hxy⟩
    have hset : codes B₀ f₀ x = codes B₁ f₁ y :=
      Set.Subset.antisymm (hsub B₀ B₁ f₀ f₁ hB₁ hc₀ x y P g₀ g₁ hP hg₀ hg₁ hbase hxy)
        (hsub B₁ B₀ f₁ f₀ hB₀ hc₁ y x P g₁ g₀ hP hg₁ hg₀ (fun a => (hbase a).symm) hxy.symm)
    change leastCode (codes B₀ f₀ x) = leastCode (codes B₁ f₁ y)
    rw [hset]

end Base

end
end AEC
