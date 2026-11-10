module

public import AEC.Section4.PlacedTesting
public import AEC.Section4.CountableClosure
public import AEC.Section4.Prop43BAF

@[expose] public section

/-!
# Unique lifts of bounded diagrams (Lemma 4.10)

Let `μ > ℓ` be a strong limit of countable cofinality strictly closed under `t` and `g`, let
`A = E(I) ≤_K B` have size `μ` with `I` a well-order of size `μ`, and let `d` be a tuple of
`B` of length at most `σ < μ`. This file follows the proof of Lemma 4.10 in `text.md` §4.3.

* `Placement.Lifts`: a placement realizes the diagram `D(d, p; B)` of `d` with a parameter
  tuple `p` of `A`, at a bound `ρ`. `Placement.LiftsBounded`: it realizes all the bounded
  diagrams `D(d, X; B)`, `X ⊆ A`, `|X| < μ` (their thresholds lie below `μ`).
* `exists_power_fixed_below`: the cardinals `χ < μ` with `χ ^ σ = χ` are cofinal below `μ`
  (`χ = 2 ^ α` for `σ ≤ α < μ`).
* `exists_placement_lifting`: for such `χ > ℓ + σ`, Proposition 4.9 (`compact_placement`)
  gives a placement realizing the tests of size at most `χ`. The prescription for `p` is the
  diagram of `(φ ∘ d, p)`, where `φ : B → A` is a strong map fixing `p` (Proposition 4.2 at
  the categoricity cardinal `μ`); it agrees on the parameters with the natural diagrams and
  restricts coherently because it is the diagram of `(d, p)` in `B`.
* `agreeOn_univ_of_lifts`: once `χ ≥ g(σ)`, two placements realizing the tests of size at most
  `χ` have the same full comparison, by Proposition 4.8 (`PlacedTester`).
* `exists_boundedDiagramLift`: fix one of them; every bounded test is covered by a larger
  `χ`, whose placement has the same full comparison, so the fixed placement realizes every
  bounded test. `Placement.LiftsBounded.agreeOn_univ` is uniqueness.
* `boundedDiagramLift`: the statement in terms of a tuple `z` of `E(J)`, used by
  `lemma_4_10`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

/-! ## Diagram equality: change of bound -/

/-- Diagram equality passes to sublists and reindexings, and is compatible with a change of
the bound, in models above the larger threshold: the match is carried by a common strong hull
of size `t(σ')` (Proposition 4.2). -/
theorem StableDiagram.same_relevel (D : StableDiagram K) {σ τ σ' : Cardinal.{u}}
    {α γ : Type u} {M N : Model K.τ} (hα : #α ≤ σ) (hσ : aleph0 ≤ σ) (hτ : aleph0 ≤ τ)
    (hσσ' : σ ≤ σ') (hτσ' : τ ≤ σ') (hls : ls K ≤ σ') (hM : K.Mem M) (hN : K.Mem N)
    (hMc : D.t σ ≤ Model.card M) (hNc : D.t σ ≤ Model.card N)
    (hMc' : D.t σ' ≤ Model.card M) (hNc' : D.t σ' ≤ Model.card N)
    (hMcτ : D.t τ ≤ Model.card M) (hNcτ : D.t τ ≤ Model.card N)
    (xs : α → M.carrier) (ys : α → N.carrier)
    (hsame : D.same hα hM hN hMc hNc xs ys) (hγ : #γ ≤ τ) (ι : γ → α) :
    D.same hγ hM hN hMcτ hNcτ (fun c => xs (ι c)) (fun c => ys (ι c)) := by
  obtain ⟨A, i, r, hA, hAc, hi, hr, hhit, -⟩ :=
    D.exists_common_hull hα hσ hσσ' hls hM hN hMc hNc hMc' hNc' xs ys hsame ∅ (by simp)
  choose a ha using hhit
  have hAτ : D.t τ ≤ Model.card A := (D.mono τ σ' hτσ').trans hAc.ge
  exact D.same_of_common_hull hγ hτ hA hM hN hAτ hMcτ hNcτ i r hi hr (fun c => a (ι c)) _ _
    (fun c => (ha (ι c)).1) (fun c => (ha (ι c)).2)

/-! ## Cofinally many `χ < μ` with `χ ^ σ = χ` -/

/-- Below a strong limit `μ`, the cardinals `χ` with `χ ^ σ = χ` are cofinal: use
`χ = 2 ^ α` for `σ ≤ α < μ`. -/
theorem exists_power_fixed_below {μ σ κ : Cardinal.{u}} (hμ : μ.IsStrongLimit)
    (hσinf : aleph0 ≤ σ) (hσ : σ < μ) (hκ : κ < μ) :
    ∃ χ : Cardinal.{u}, κ < χ ∧ χ < μ ∧ χ ^ σ = χ := by
  refine ⟨2 ^ (κ ⊔ σ), ?_, hμ.isStrongPrelimit (max_lt hκ hσ), ?_⟩
  · exact (le_sup_left : κ ≤ κ ⊔ σ).trans_lt (cantor _)
  · rw [← power_mul, mul_eq_left (hσinf.trans le_sup_right) le_sup_right
      (aleph0_pos.trans_le hσinf).ne']

/-! ## Placements realizing the diagrams of a tuple of `B` -/

section Lift

variable {E : OrderPresentation K} {D : StableDiagram K}
  {I : Type u} [LinearOrder I] [Nonempty I]
  {B : Model K.τ} (hB : K.Mem B)
  (incl : Language.Embedding K.τ (E.obj I).carrier B.carrier)
  {α : Type u} (d : α → B.carrier)

variable (E D) in
/-- **The placement `P` realizes the test `p`.** The placed tuple of `P`, together with the
parameter tuple `p` of `A = E(I)`, has the diagram `D(d, p; B)`, at the bound `ρ`. (The size
hypotheses hold for every infinite `ρ` below a closure point `μ = ‖B‖`.) -/
def Placement.Lifts (P : Placement E.lab E.arity I α) (ρ : Cardinal.{u}) {β : Type u}
    (hj : #(α ⊕ β) ≤ ρ) (p : β → (E.obj I).carrier) : Prop :=
  ∀ (hBc : D.t ρ ≤ Model.card B) (hJc : D.t ρ ≤ Model.card (E.obj P.J)),
    D.same hj hB (orderPresentation_obj_mem E P.J) hBc hJc
      (Sum.elim d (fun b => incl (p b)))
      (fun c => E.realize (P.joint (fun b => supportTermOf E (p b)) c))

variable (E D) in
/-- **The placement `P` lifts the bounded diagrams of `d`**: it realizes `D(d, p; B)` for
every parameter tuple `p` of `A` and every infinite bound `ρ < μ`. -/
def Placement.LiftsBounded (μ : Cardinal.{u}) (P : Placement E.lab E.arity I α) : Prop :=
  ∀ ⦃β : Type u⦄ (ρ : Cardinal.{u}), aleph0 ≤ ρ → ρ < μ →
    ∀ (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ ρ), P.Lifts E D hB incl d ρ hj p

/-- The realized joint list of a placement with a parameter tuple of `E(I)`. -/
theorem Placement.realize_joint_eq (P : Placement E.lab E.arity I α) {β : Type u}
    (p : β → (E.obj I).carrier) :
    (fun c => E.realize (P.joint (fun b => supportTermOf E (p b)) c)) =
      Sum.elim (fun a => E.realize (P.z a)) (fun b => E.map P.f (p b)) := by
  funext c
  rcases c with a | b
  · rfl
  · change E.realize (SupportTerm.along P.f (supportTermOf E (p b))) = E.map P.f (p b)
    rw [← E.realize_along, realize_supportTermOf]

variable {hB incl d}

/-- Realizing a test is preserved by extending the order of the placement. -/
theorem Placement.Lifts.along {P Q : Placement E.lab E.arity I α} {ρ : Cardinal.{u}}
    {β : Type u} {hj : #(α ⊕ β) ≤ ρ} {p : β → (E.obj I).carrier}
    (hl : P.Lifts E D hB incl d ρ hj p) (hρinf : aleph0 ≤ ρ) (h : P.J ↪o Q.J)
    (hf : ∀ i, h (P.f i) = Q.f i) (hz : ∀ a, SupportTerm.along h (P.z a) = Q.z a)
    (hPc : D.t ρ ≤ Model.card (E.obj P.J)) :
    Q.Lifts E D hB incl d ρ hj p := by
  intro hBc hQc
  have h1 := hl hBc hPc
  have h2 := D.of_strong hj (orderPresentation_obj_mem E P.J) (orderPresentation_obj_mem E Q.J)
    hPc hQc (fun c => E.realize (P.joint (fun b => supportTermOf E (p b)) c))
    (fun c => E.realize (Q.joint (fun b => supportTermOf E (p b)) c)) (E.map h) hρinf
    (E.map_strong h) (by
      intro c
      rw [E.realize_along]
      congr 1
      rcases c with a | b
      · exact hz a
      · exact SupportTerm.ext_of_label_eq rfl fun k => hf _)
  exact D.trans hj hB _ _ hBc hPc hQc _ _ _ h1 h2

/-- Realizing a test realizes its restrictions and reindexings, at any other bound, when
`B` and the presentation of the placement are above the threshold of a common bound `σ'`. -/
theorem Placement.Lifts.relevel {P : Placement E.lab E.arity I α} {ρ ρ' σ' : Cardinal.{u}}
    {β β' : Type u} {hj : #(α ⊕ β) ≤ ρ} {p : β → (E.obj I).carrier}
    (hl : P.Lifts E D hB incl d ρ hj p) (hρinf : aleph0 ≤ ρ) (hρ'inf : aleph0 ≤ ρ')
    (hρσ' : ρ ≤ σ') (hρ'σ' : ρ' ≤ σ') (hls : ls K ≤ σ')
    (hBc : D.t σ' ≤ Model.card B) (hJc : D.t σ' ≤ Model.card (E.obj P.J))
    (hj' : #(α ⊕ β') ≤ ρ') (ι : β' → β) :
    P.Lifts E D hB incl d ρ' hj' (fun b => p (ι b)) := by
  intro hBc' hJc'
  have hBρ : D.t ρ ≤ Model.card B := (D.mono ρ σ' hρσ').trans hBc
  have hJρ : D.t ρ ≤ Model.card (E.obj P.J) := (D.mono ρ σ' hρσ').trans hJc
  have h1 := D.same_relevel hj hρinf hρ'inf hρσ' hρ'σ' hls hB
    (orderPresentation_obj_mem E P.J) hBρ hJρ hBc hJc hBc' hJc' _ _ (hl hBρ hJρ) hj'
    (Sum.map id ι)
  have e1 : (fun c => Sum.elim d (fun b => incl (p b)) (Sum.map id ι c)) =
      Sum.elim d (fun b => incl (p (ι b))) := by
    funext c
    rcases c with a | b <;> rfl
  have e2 : (fun c => E.realize (P.joint (fun b => supportTermOf E (p b)) (Sum.map id ι c))) =
      fun c => E.realize (P.joint (fun b => supportTermOf E (p (ι b))) c) := by
    funext c
    rcases c with a | b <;> rfl
  rw [e1, e2] at h1
  exact h1

/-! ### The prescriptions: strong maps `B → A` fixing a bounded parameter tuple -/

include hB in
/-- **Proposition 4.2 at `μ`.** A bounded parameter tuple of `A = E(I)` has the same diagram
in `A` and in `B`; at the categoricity cardinal `μ` a strong map `B → A` fixes it. -/
theorem exists_paramFixing {μ ρ : Cardinal.{u}} (hstrong : K.Strong incl)
    (hcat : Categorical K μ) (hBc : Model.card B = μ) (hIc : Model.card (E.obj I) = μ)
    (hρinf : aleph0 ≤ ρ) (hρ : D.t ρ ≤ μ) {β : Type u} (hβ : #β ≤ ρ)
    (p : β → (E.obj I).carrier) :
    ∃ φ : Language.Embedding K.τ B.carrier (E.obj I).carrier,
      K.Strong φ ∧ ∀ b, φ (incl (p b)) = p b := by
  have hI : K.Mem (E.obj I) := orderPresentation_obj_mem E I
  have hcB : D.t ρ ≤ Model.card B := hρ.trans hBc.ge
  have hcI : D.t ρ ≤ Model.card (E.obj I) := hρ.trans hIc.ge
  have h1 : D.same hβ hI hB hcI hcB p (fun b => incl (p b)) :=
    D.of_strong hβ hI hB hcI hcB p _ incl hρinf hstrong (fun _ => rfl)
  have h2 := D.symm hβ hI hB hcI hcB _ _ h1
  exact D.to_strong hβ hB hI _ _ hρinf (by rw [hBc]; exact hcat) (hBc.trans hIc.symm)
    hcB hcI h2

/-- **Proposition 4.9 on the diagrams of `d`.** For `χ > ℓ + σ` with `χ ^ σ = χ` and
`t(σ + χ) ≤ μ`, one placement realizes the tests of size at most `χ`. -/
theorem exists_placement_lifting [CategoricalUnbounded K] [WellFoundedLT I]
    {μ σ χ : Cardinal.{u}} (hstrong : K.Strong incl) (hcat : Categorical K μ)
    (hBc : Model.card B = μ) (hIc : Model.card (E.obj I) = μ)
    (hσinf : aleph0 ≤ σ) (hα : #α ≤ σ) (hχ : ls K + σ < χ) (hpow : χ ^ σ = χ)
    (hρ : D.t (σ + χ) ≤ μ) :
    ∃ P : Placement E.lab E.arity I α,
      ∀ {β : Type u} (_ : #β ≤ χ) (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ σ + χ),
        P.Lifts E D hB incl d (σ + χ) hj p := by
  classical
  have hI : K.Mem (E.obj I) := orderPresentation_obj_mem E I
  have hρinf : aleph0 ≤ σ + χ := hσinf.trans (self_le_add_right σ χ)
  have hcB : D.t (σ + χ) ≤ Model.card B := hρ.trans hBc.ge
  have hcI : D.t (σ + χ) ≤ Model.card (E.obj I) := hρ.trans hIc.ge
  have hex : ∀ (β : Type u) (_ : #β ≤ χ) (p : β → (E.obj I).carrier),
      ∃ φ : Language.Embedding K.τ B.carrier (E.obj I).carrier,
        K.Strong φ ∧ ∀ b, φ (incl (p b)) = p b :=
    fun β hβ p => exists_paramFixing (hB := hB) hstrong hcat hBc hIc hρinf hρ
      (hβ.trans (self_le_add_left χ σ)) p
  choose φ hφ hφp using hex
  -- the prescription for `p` is the diagram of `(d, p)` in `B`
  have hpres : ∀ {β : Type u} (hβ : #β ≤ χ) (p : β → (E.obj I).carrier)
      (hj : #(α ⊕ β) ≤ σ + χ),
      D.same hj hB hI hcB hcI (Sum.elim d (fun b => incl (p b)))
        (Sum.elim (fun a => φ β hβ p (d a)) p) := by
    intro β hβ p hj
    refine D.of_strong hj hB hI hcB hcI _ _ (φ β hβ p) hρinf (hφ β hβ p) ?_
    rintro (a | b)
    · rfl
    · exact hφp β hβ p b
  obtain ⟨P, hP⟩ := compact_placement E D σ χ hσinf hα hχ hpow hcI
    (fun {β} hβ p => Sum.elim (fun a => φ β hβ p (d a)) p)
    (fun {β} hβ p hβ' => D.refl hβ' hI hcI p)
    (fun {β β'} hβ hβ' p ι hj => by
      have h1 : D.same hj hB hI hcB hcI (Sum.elim d (fun b => incl (p (ι b))))
          (fun i => Sum.elim (fun a => φ β hβ p (d a)) p (Sum.map id ι i)) := by
        refine D.of_strong hj hB hI hcB hcI _ _ (φ β hβ p) hρinf (hφ β hβ p) ?_
        rintro (a | b)
        · rfl
        · exact hφp β hβ p (ι b)
      exact D.trans hj hI hB hI hcI hcB hcI _ _ _ (D.symm hj hB hI hcB hcI _ _ h1)
        (hpres hβ' (fun b => p (ι b)) hj))
  refine ⟨P, fun {β} hβ p hj hBc' hJc => ?_⟩
  have h1 := SameNaturalDiagram.same hρinf (hP hβ p hj) hJc hcI
    (orderPresentation_obj_mem E P.J) hI
  simp only [realize_supportTermOf] at h1
  exact D.trans hj hB hI _ hBc' hcI hJc _ _ _ (hpres hβ p hj)
    (D.symm hj _ hI hJc hcI _ _ h1)

/-! ### Proposition 4.8: tests of size `g(σ)` determine the full comparison -/

/-- Two placements realizing the tests of size at most `χ` agree on every set `X` of
positions whose terms give at most `χ` parameters. -/
theorem agreeOn_of_lifts [CategoricalUnbounded K] {P P' : Placement E.lab E.arity I α}
    {ρ χ : Cardinal.{u}} (hρinf : aleph0 ≤ ρ) (hBc : D.t ρ ≤ Model.card B)
    (hIc : D.t ρ ≤ Model.card (E.obj I))
    (hαχ : ∀ {β : Type u}, #β ≤ χ → #(α ⊕ β) ≤ ρ)
    (hP : ∀ {β : Type u} (_ : #β ≤ χ) (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ ρ),
      P.Lifts E D hB incl d ρ hj p)
    (hP' : ∀ {β : Type u} (_ : #β ≤ χ) (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ ρ),
      P'.Lifts E D hB incl d ρ hj p)
    (X : Set I) (hX : #X + 1 + ls K ≤ χ) : P.AgreeOn E D P' X := by
  classical
  intro β par τ hτ hj hpar
  -- the parameters are images of elements of `E(X ∪ {i₀})`
  let X' : Set I := X ∪ {Classical.arbitrary I}
  haveI : Nonempty ↥X' := ⟨⟨Classical.arbitrary I, Or.inr rfl⟩⟩
  let iX : ↥X' ↪o I := OrderEmbedding.subtype (· ∈ X')
  let Y : Set (E.obj I).carrier := Set.range (fun b => E.realize (par b))
  have hYsub : Y ⊆ Set.range (E.map iX) := by
    rintro _ ⟨b, rfl⟩
    refine ⟨E.realize ((par b).restrict X' fun x hx => Or.inl (hpar b hx)), ?_⟩
    rw [E.realize_along]
    rfl
  have hX'card : #↥X' ≤ #X + 1 := (mk_union_le _ _).trans (by simp)
  have hYcard : #Y ≤ χ :=
    calc #Y ≤ #(Set.range (E.map iX)) := mk_le_mk_of_subset hYsub
      _ ≤ Model.card (E.obj ↥X') := mk_range_le
      _ ≤ #↥X' + E.ell := E.card_upper
      _ ≤ #X + 1 + ls K := by rw [E.ell_eq]; exact add_le_add hX'card le_rfl
      _ ≤ χ := hX
  have hjY : #(α ⊕ ↥Y) ≤ ρ := hαχ hYcard
  have hJc : D.t ρ ≤ Model.card (E.obj P.J) :=
    hIc.trans (mk_le_of_injective (E.map P.f).injective)
  have hJc' : D.t ρ ≤ Model.card (E.obj P'.J) :=
    hIc.trans (mk_le_of_injective (E.map P'.f).injective)
  have h1 := hP hYcard (Subtype.val : ↥Y → (E.obj I).carrier) hjY hBc hJc
  have h2 := hP' hYcard (Subtype.val : ↥Y → (E.obj I).carrier) hjY hBc hJc'
  have h3 := D.trans hjY _ hB _ hJc hBc hJc' _ _ _ (D.symm hjY hB _ hBc hJc _ _ h1) h2
  have h4 : SameNaturalDiagram K E D ρ hjY
      (P.joint (fun y : ↥Y => supportTermOf E y.1))
      (P'.joint (fun y : ↥Y => supportTermOf E y.1)) :=
    sameNaturalDiagram_of_same_realize hρinf P.f P'.f _ _ hJc hJc' _ _ h3
  have h5 := h4.relevel hρinf hτ hj
    (Sum.map id (Set.rangeFactorization (fun b => E.realize (par b))))
  have e1 : ∀ Q : Placement E.lab E.arity I α, SameNaturalDiagram K E D τ hj (Q.joint par)
      (fun c => Q.joint (fun y : ↥Y => supportTermOf E y.1)
        (Sum.map id (Set.rangeFactorization (fun b => E.realize (par b))) c)) := by
    intro Q
    refine sameNaturalDiagram_of_realize_eq _ _ ?_
    rintro (a | b)
    · rfl
    · change E.realize (SupportTerm.along Q.f (par b)) =
        E.realize (SupportTerm.along Q.f (supportTermOf E (E.realize (par b))))
      rw [← E.realize_along, ← E.realize_along, realize_supportTermOf]
  exact ((e1 P).trans hτ h5).trans hτ (sameNaturalDiagram_symm E D (e1 P'))

/-- **Proposition 4.8 for lifts.** Once `χ ≥ g(σ)`, two placements realizing the tests of
size at most `χ` have the same full comparison over `A`. -/
theorem agreeOn_univ_of_lifts [CategoricalUnbounded K] [WellFoundedLT I]
    {g : Cardinal.{u} → Cardinal.{u}} (hg : PlacedTester K E D g)
    {P P' : Placement E.lab E.arity I α} {σ χ : Cardinal.{u}} (hσinf : aleph0 ≤ σ)
    (hα : #α ≤ σ) (hgχ : g σ ≤ χ) (hlsχ : ls K ≤ χ) (hσχ : σ ≤ χ)
    (hBc : D.t (σ + χ) ≤ Model.card B) (hIc : D.t (σ + χ) ≤ Model.card (E.obj I))
    (hP : ∀ {β : Type u} (_ : #β ≤ χ) (p : β → (E.obj I).carrier)
      (hj : #(α ⊕ β) ≤ σ + χ), P.Lifts E D hB incl d (σ + χ) hj p)
    (hP' : ∀ {β : Type u} (_ : #β ≤ χ) (p : β → (E.obj I).carrier)
      (hj : #(α ⊕ β) ≤ σ + χ), P'.Lifts E D hB incl d (σ + χ) hj p) :
    P.AgreeOn E D P' Set.univ := by
  have hχinf : aleph0 ≤ χ := hσinf.trans hσχ
  have hρinf : aleph0 ≤ σ + χ := hσinf.trans (self_le_add_right σ χ)
  refine hg σ hσinf hα P P' fun X hX => ?_
  refine agreeOn_of_lifts hρinf hBc hIc (fun {β} hβ => ?_) hP hP' X ?_
  · rw [mk_sum, lift_id, lift_id]
    exact add_le_add hα hβ
  · exact add_le_of_le hχinf (add_le_of_le hχinf (hX.trans hgχ) (one_le_aleph0.trans hχinf))
      hlsχ

/-! ### Existence and uniqueness of the lift -/

section Closure

variable [CategoricalUnbounded K] [WellFoundedLT I] {g : Cardinal.{u} → Cardinal.{u}}
  {μ σ : Cardinal.{u}}

/-- **Uniqueness of the lift.** Two placements lifting the bounded diagrams of `d` have the
same placed comparison over all of `A`. -/
theorem Placement.LiftsBounded.agreeOn_univ (hg : PlacedTester K E D g)
    (hμ : IsClosurePoint {D.t, g} μ) (hσinf : aleph0 ≤ σ) (hσ : σ < μ) (hℓ : ls K < μ)
    (hI : #I = μ) (hcard : Model.card B = μ) (hα : #α ≤ σ)
    {P P' : Placement E.lab E.arity I α}
    (h : P.LiftsBounded E D hB incl d μ) (h' : P'.LiftsBounded E D hB incl d μ) :
    P.AgreeOn E D P' Set.univ := by
  have hμinf : aleph0 ≤ μ := hμ.working.infinite
  have hIc : Model.card (E.obj I) = μ := orderPresentation_obj_card E hI hℓ.le hμinf
  have hgσ : g σ < μ :=
    (hμ.closed g (Set.mem_insert_of_mem _ rfl)).below σ hσinf hσ
  have hχμ : g σ ⊔ ls K ⊔ σ < μ := max_lt (max_lt hgσ hℓ) hσ
  have hρμ : σ + (g σ ⊔ ls K ⊔ σ) < μ := add_lt_of_lt hμinf hσ hχμ
  have hρinf : aleph0 ≤ σ + (g σ ⊔ ls K ⊔ σ) := hσinf.trans (self_le_add_right _ _)
  have ht : D.t (σ + (g σ ⊔ ls K ⊔ σ)) ≤ μ :=
    ((hμ.closed D.t (Set.mem_insert _ _)).below _ hρinf hρμ).le
  exact agreeOn_univ_of_lifts hg hσinf hα (le_sup_left.trans le_sup_left)
    (le_sup_right.trans le_sup_left) le_sup_right (ht.trans hcard.ge) (ht.trans hIc.ge)
    (fun _ p hj => h _ hρinf hρμ p hj) (fun _ p hj => h' _ hρinf hρμ p hj)

/-- **Lemma 4.10, in placement form.** The bounded diagrams of `d` lift to one placement over
`A = E(I)`, and any two lifts have the same placed comparison over all of `A`. -/
theorem exists_boundedDiagramLift (hg : PlacedTester K E D g)
    (hμ : IsClosurePoint {D.t, g} μ) (hσinf : aleph0 ≤ σ) (hσ : σ < μ) (hℓ : ls K < μ)
    (hcat : Categorical K μ) (hI : #I = μ) (hstrong : K.Strong incl)
    (hcard : Model.card B = μ) (hα : #α ≤ σ) :
    ∃ P : Placement E.lab E.arity I α, P.LiftsBounded E D hB incl d μ ∧
      ∀ P' : Placement E.lab E.arity I α, P'.LiftsBounded E D hB incl d μ →
        P.AgreeOn E D P' Set.univ := by
  have hμinf : aleph0 ≤ μ := hμ.working.infinite
  have hIc : Model.card (E.obj I) = μ := orderPresentation_obj_card E hI hℓ.le hμinf
  have hI' : K.Mem (E.obj I) := orderPresentation_obj_mem E I
  have ht : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ μ := fun ρ h1 h2 =>
    ((hμ.closed D.t (Set.mem_insert _ _)).below ρ h1 h2).le
  have hgσ : g σ < μ :=
    (hμ.closed g (Set.mem_insert_of_mem _ rfl)).below σ hσinf hσ
  have hJcard : ∀ (P : Placement E.lab E.arity I α) {ρ : Cardinal.{u}}, D.t ρ ≤ μ →
      D.t ρ ≤ Model.card (E.obj P.J) := fun P ρ h =>
    (h.trans hIc.ge).trans (mk_le_of_injective (E.map P.f).injective)
  -- one `χ₀ ≥ g(σ)` and its placement
  obtain ⟨χ₀, hχ₀, hχ₀μ, hpow₀⟩ := exists_power_fixed_below hμ.working.strongLimit hσinf hσ
    (max_lt hgσ (add_lt_of_lt hμinf hℓ hσ))
  have hlsσ₀ : ls K + σ < χ₀ := le_sup_right.trans_lt hχ₀
  have hσχ₀ : σ ≤ χ₀ := (self_le_add_left σ (ls K)).trans hlsσ₀.le
  have hlsχ₀ : ls K ≤ χ₀ := (self_le_add_right (ls K) σ).trans hlsσ₀.le
  have hρ₀inf : aleph0 ≤ σ + χ₀ := hσinf.trans (self_le_add_right σ χ₀)
  have hρ₀μ : σ + χ₀ < μ := add_lt_of_lt hμinf hσ hχ₀μ
  obtain ⟨P₀, hP₀⟩ := exists_placement_lifting (hB := hB) (d := d) hstrong hcat hcard hIc
    hσinf hα hlsσ₀ hpow₀ (ht _ hρ₀inf hρ₀μ)
  -- every bounded test is covered by a larger `χ`
  have hP₀b : P₀.LiftsBounded E D hB incl d μ := by
    intro β ρ hρinf hρ p hj
    obtain ⟨χ, hχ, hχμ, hpow⟩ := exists_power_fixed_below hμ.working.strongLimit hσinf hσ
      (max_lt hχ₀μ hρ)
    have hχ₀χ : χ₀ ≤ χ := le_sup_left.trans hχ.le
    have hρχ : ρ ≤ χ := le_sup_right.trans hχ.le
    have hlsσ : ls K + σ < χ := hlsσ₀.trans_le hχ₀χ
    have hρ₁inf : aleph0 ≤ σ + χ := hσinf.trans (self_le_add_right σ χ)
    have hρ₁μ : σ + χ < μ := add_lt_of_lt hμinf hσ hχμ
    have hls₁ : ls K ≤ σ + χ := (hlsχ₀.trans hχ₀χ).trans (self_le_add_left χ σ)
    have hBc₁ : D.t (σ + χ) ≤ Model.card B := (ht _ hρ₁inf hρ₁μ).trans hcard.ge
    obtain ⟨P₁, hP₁⟩ := exists_placement_lifting (hB := hB) (d := d) hstrong hcat hcard hIc
      hσinf hα hlsσ hpow (ht _ hρ₁inf hρ₁μ)
    -- the placement for `χ` realizes the tests of size at most `χ₀`, at the bound `σ + χ₀`
    have hP₁₀ : ∀ {β' : Type u} (_ : #β' ≤ χ₀) (p' : β' → (E.obj I).carrier)
        (hj' : #(α ⊕ β') ≤ σ + χ₀), P₁.Lifts E D hB incl d (σ + χ₀) hj' p' := by
      intro β' hβ' p' hj'
      have hj₁ : #(α ⊕ β') ≤ σ + χ := hj'.trans (add_le_add le_rfl hχ₀χ)
      exact (hP₁ (hβ'.trans hχ₀χ) p' hj₁).relevel hρ₁inf hρ₀inf le_rfl
        (add_le_add le_rfl hχ₀χ) hls₁ hBc₁ (hJcard P₁ (ht _ hρ₁inf hρ₁μ)) hj' id
    -- so it has the same full comparison as the fixed placement
    have hagree : P₀.AgreeOn E D P₁ Set.univ :=
      agreeOn_univ_of_lifts hg hσinf hα (le_sup_left.trans hχ₀.le) hlsχ₀ hσχ₀
        ((ht _ hρ₀inf hρ₀μ).trans hcard.ge) ((ht _ hρ₀inf hρ₀μ).trans hIc.ge) hP₀ hP₁₀
    -- the fixed placement realizes the test, at the bound `σ + χ`
    have hβ : #β ≤ χ := by
      refine le_trans ?_ (hj.trans hρχ)
      rw [mk_sum, lift_id, lift_id]
      exact self_le_add_left _ _
    have hj₁ : #(α ⊕ β) ≤ σ + χ := by
      rw [mk_sum, lift_id, lift_id]
      exact add_le_add hα hβ
    have hlift₁ : P₀.Lifts E D hB incl d (σ + χ) hj₁ p := by
      intro hBc hJc
      have hJc₁ := hJcard P₁ (ht _ hρ₁inf hρ₁μ)
      have h1 := hP₁ hβ p hj₁ hBc hJc₁
      have h2 := SameNaturalDiagram.same hρ₁inf
        (hagree (fun b => supportTermOf E (p b)) (σ + χ) hρ₁inf hj₁
          (fun b => Set.subset_univ _)) hJc hJc₁
        (orderPresentation_obj_mem E P₀.J) (orderPresentation_obj_mem E P₁.J)
      exact D.trans hj₁ hB _ _ hBc hJc₁ hJc _ _ _ h1
        (D.symm hj₁ _ _ hJc hJc₁ _ _ h2)
    exact hlift₁.relevel hρ₁inf hρinf le_rfl (hρχ.trans (self_le_add_left χ σ)) hls₁ hBc₁
      (hJcard P₀ (ht _ hρ₁inf hρ₁μ)) hj id
  exact ⟨P₀, hP₀b, fun P' hP' => hP₀b.agreeOn_univ hg hμ hσinf hσ hℓ hI hcard hα hP'⟩

/-- **Restricting a lifted tuple gives a lift of the restricted diagrams.** (By uniqueness it
is *the* lift of the restricted diagrams.) -/
theorem Placement.LiftsBounded.reindex {P : Placement E.lab E.arity I α}
    (h : P.LiftsBounded E D hB incl d μ) (hμinf : aleph0 ≤ μ) (hℓ : ls K < μ) (hαμ : #α < μ)
    (ht : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ μ) (hcard : Model.card B = μ)
    (hIc : Model.card (E.obj I) = μ) {α' : Type u} (ι : α' → α) :
    (P.reindex ι).LiftsBounded E D hB incl (fun a => d (ι a)) μ := by
  intro β ρ hρinf hρ p hj hBc hJc
  have hβ : #β ≤ ρ := by
    refine le_trans ?_ hj
    rw [mk_sum, lift_id, lift_id]
    exact self_le_add_left _ _
  have hρ₀inf : aleph0 ≤ #α + ρ := hρinf.trans (self_le_add_left _ _)
  have hρ₀μ : #α + ρ < μ := add_lt_of_lt hμinf hαμ hρ
  have hρ₁inf : aleph0 ≤ (#α + ρ) ⊔ ls K := hρ₀inf.trans le_sup_left
  have hρ₁μ : (#α + ρ) ⊔ ls K < μ := max_lt hρ₀μ hℓ
  have hj₀ : #(α ⊕ β) ≤ #α + ρ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_le_add le_rfl hβ
  have hJμ : ∀ {κ : Cardinal.{u}}, D.t κ ≤ μ → D.t κ ≤ Model.card (E.obj P.J) := fun hκ =>
    (hκ.trans hIc.ge).trans (mk_le_of_injective (E.map P.f).injective)
  have hBc₀ : D.t (#α + ρ) ≤ Model.card B := (ht _ hρ₀inf hρ₀μ).trans hcard.ge
  have h1 := D.same_relevel hj₀ hρ₀inf hρinf le_sup_left
    ((self_le_add_left ρ #α).trans le_sup_left) le_sup_right hB
    (orderPresentation_obj_mem E P.J) hBc₀ (hJμ (ht _ hρ₀inf hρ₀μ))
    ((ht _ hρ₁inf hρ₁μ).trans hcard.ge) (hJμ (ht _ hρ₁inf hρ₁μ)) hBc hJc _ _
    (h _ hρ₀inf hρ₀μ p hj₀ hBc₀ (hJμ (ht _ hρ₀inf hρ₀μ))) hj (Sum.map ι id)
  have e1 : (fun c => Sum.elim d (fun b => incl (p b)) (Sum.map ι id c)) =
      Sum.elim (fun a => d (ι a)) (fun b => incl (p b)) := by
    funext c
    rcases c with a | b <;> rfl
  have e2 : (fun c => E.realize (P.joint (fun b => supportTermOf E (p b)) (Sum.map ι id c))) =
      fun c => E.realize ((P.reindex ι).joint (fun b => supportTermOf E (p b)) c) := by
    funext c
    rcases c with a | b <;> rfl
  rw [e1, e2] at h1
  exact h1

/-- **Lemma 4.10** (Unique lifts of bounded diagrams), in terms of a tuple `z` of `E(J)`.
The bounded diagrams `D(d, p; B)` of `d` with the parameter tuples `p` of `A = E(I)` (at the
bounds `ρ < μ`, whose thresholds lie below `μ`) lift to one tuple `z` of `E(J)`, `J ⊇ I`,
where `E(J)` is above the threshold for diagrams of length `μ`; and any other such lift has
the same diagram with every parameter tuple of length at most `μ`, i.e. the same placed
comparison over all of `A`. -/
theorem boundedDiagramLift (hg : PlacedTester K E D g)
    (hμ : IsClosurePoint {D.t, g} μ) (hσinf : aleph0 ≤ σ) (hσ : σ < μ) (hℓ : ls K < μ)
    (hcat : Categorical K μ) (hI : #I = μ) (hstrong : K.Strong incl)
    (hcard : Model.card B = μ) (hα : #α ≤ σ) :
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (f : I ↪o J)
      (z : α → (E.obj J).carrier) (hJ : K.Mem (E.obj J)),
      D.t μ ≤ Model.card (E.obj J) ∧
      (∀ {β : Type u} (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ) (_ : ρ < μ)
          (p : β → (E.obj I).carrier) (hjoint : #(α ⊕ β) ≤ ρ)
          (hBcard : D.t ρ ≤ Model.card B) (hJcard : D.t ρ ≤ Model.card (E.obj J)),
          D.same hjoint hB hJ hBcard hJcard
            (Sum.elim d (fun b => incl (p b)))
            (Sum.elim z (fun b => E.map f (p b)))) ∧
      ∀ {J' : Type u} [LinearOrder J'] [Nonempty J'] (f' : I ↪o J')
        (z' : α → (E.obj J').carrier) (hJ' : K.Mem (E.obj J')),
        (∀ {β : Type u} (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ) (_ : ρ < μ)
            (p : β → (E.obj I).carrier) (hjoint : #(α ⊕ β) ≤ ρ)
            (hBcard : D.t ρ ≤ Model.card B) (hJcard : D.t ρ ≤ Model.card (E.obj J')),
            D.same hjoint hB hJ' hBcard hJcard
              (Sum.elim d (fun b => incl (p b)))
              (Sum.elim z' (fun b => E.map f' (p b)))) →
        ∀ {β : Type u} (p : β → (E.obj I).carrier)
          (hjoint : #(α ⊕ β) ≤ μ)
          (hJcard : D.t μ ≤ Model.card (E.obj J))
          (hJ'card : D.t μ ≤ Model.card (E.obj J')),
          D.same hjoint hJ hJ' hJcard hJ'card
            (Sum.elim z (fun b => E.map f (p b)))
            (Sum.elim z' (fun b => E.map f' (p b))) := by
  obtain ⟨P₀, hP₀, -⟩ := exists_boundedDiagramLift (hB := hB) (incl := incl) (d := d) hg hμ
    hσinf hσ hℓ hcat hI hstrong hcard hα
  have hμinf : aleph0 ≤ μ := hμ.working.infinite
  have hIc : Model.card (E.obj I) = μ := orderPresentation_obj_card E hI hℓ.le hμinf
  have ht : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ μ := fun ρ h1 h2 =>
    ((hμ.closed D.t (Set.mem_insert _ _)).below ρ h1 h2).le
  -- extend the order of the lift above the threshold for diagrams of length `μ`
  obtain ⟨L, linL, nonL, F, hL⟩ := exists_large_extension E P₀.J (D.t μ)
  have hQ : ({ J := L, f := P₀.f.trans F, z := fun a => SupportTerm.along F (P₀.z a) } :
      Placement E.lab E.arity I α).LiftsBounded E D hB incl d μ := by
    intro β ρ hρinf hρ p hj
    exact (hP₀ ρ hρinf hρ p hj).along hρinf F (fun i => rfl) (fun a => rfl)
      (((ht ρ hρinf hρ).trans hIc.ge).trans (mk_le_of_injective (E.map P₀.f).injective))
  refine ⟨L, linL, nonL, P₀.f.trans F, fun a => E.realize (SupportTerm.along F (P₀.z a)),
    orderPresentation_obj_mem E L, hL, ?_, ?_⟩
  · intro β ρ hρinf hρ p hjoint hBcard hJcard
    have h := hQ ρ hρinf hρ p hjoint hBcard hJcard
    rw [Placement.realize_joint_eq] at h
    exact h
  · intro J' _ _ f' z' hJ' hlift β p hjoint hJcard hJ'card
    have hQ' : ({ J := J', f := f', z := fun a => supportTermOf E (z' a) } :
        Placement E.lab E.arity I α).LiftsBounded E D hB incl d μ := by
      intro β ρ hρinf hρ p hj hBc hJc
      have h := hlift ρ hρinf hρ p hj hBc hJc
      rw [Placement.realize_joint_eq]
      simp only [realize_supportTermOf]
      exact h
    have hag := hQ.agreeOn_univ hg hμ hσinf hσ hℓ hI hcard hα hQ'
    have h := SameNaturalDiagram.same hμinf
      (hag (fun b => supportTermOf E (p b)) μ hμinf hjoint (fun b => Set.subset_univ _))
      hJcard hJ'card (orderPresentation_obj_mem E L) hJ'
    rw [Placement.realize_joint_eq, Placement.realize_joint_eq] at h
    simp only [realize_supportTermOf] at h
    exact h

end Closure

end Lift

end
end AEC
