module

public import AEC.Section4.ClosedLevels

@[expose] public section

/-!
# Amalgamation at closed levels (Theorem 4.11, clauses 1 and 2)

Let `μ > ℓ` be a closure point for `t` and a testing bound `g` (`ClosedLevel`), `I` a
well-order of size `μ`, `A = E(I)`, and `incl : A → B` a strong extension of size `μ`. This
file follows the proof of Theorem 4.11 in `text.md` §4.4.

* `LiftsTuple`: a tuple `z` of `G = E(J)`, `J ⊇ I`, lifts the bounded diagrams `D(d, X; B)`,
  `X ⊆ A`, `|X| < μ`, of a tuple `d` of `B` (the lift of Lemma 4.10, as a tuple of `G`).
* `LiftsTuple.same_of_lifts`: two lifts have the same diagram with all of `A` (uniqueness in
  Lemma 4.10).
* `exists_lift_extension`: *the realizations can retain the previous assignments.* If `z`
  lifts `d` in `G`, where `γ = ‖G‖ ≥ t(μ)` is a categoricity cardinal, and `d` is a sublist of
  `d'`, then some lift of `d'` in `G` extends `z`: the lift of `d'` given by Lemma 4.10, and
  then its tuple `(A, d)`, have the same diagram as the already assigned ones; their length is
  at most `μ`, so Proposition 4.2 at `γ` supplies a strong map realizing the new list while
  fixing these previous data.
* `exists_strong_tower`: `B` is the union of an increasing countable family of strong
  submodels of size less than `μ` (LS on a countable exhaustion of `B`).
* `exists_strong_of_liftsTuple`: the copy in `G` of a small strong submodel is a strong
  submodel: the copied and original lists have the same bounded diagram, so Proposition 4.2
  gives a strong map between strong `t(ρ)`-submodels with the prescribed values.
* `exists_strong_embedding_over`: `B` embeds strongly into `G` over `A`, extending any
  assigned lift of a bounded tuple.
* `exists_amalgam_of_common_lift`, `exists_amalgam_of_agreeOn`: two such extensions amalgamate
  over `A` in a strong `μ`-submodel of `G`, identifying tuples with a common lift.
* `agreeOn_univ_of_tests`: Proposition 4.8 identifies the placed lifts of two tuples whose
  diagrams agree over the subsets of `A` of size at most `g(σ) + ℓ`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- The standing hypotheses on a level of Theorem 4.11: `μ > ℓ` is a strong limit of
countable cofinality strictly closed under `t` and the testing bound `g`; it is then a
categoricity cardinal (Proposition 4.3, `categorical_of_closurePoint`). -/
structure ClosedLevel (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (D : StableDiagram K) (g : Cardinal.{u} → Cardinal.{u}) (μ : Cardinal.{u}) : Prop where
  tester : PlacedTester K E D g
  closure : IsClosurePoint {D.t, g} μ
  ls_lt : ls K < μ
  cat : Categorical K μ

namespace ClosedLevel

variable {E : OrderPresentation K} {D : StableDiagram K} {g : Cardinal.{u} → Cardinal.{u}}
  {μ : Cardinal.{u}}

theorem of_closurePoint [CategoricalUnbounded K] (hg : PlacedTester K E D g)
    (hμ : IsClosurePoint {D.t, g} μ) (hℓ : ls K < μ) : ClosedLevel K E D g μ :=
  ⟨hg, hμ, hℓ, categorical_of_closurePoint D hμ hℓ⟩

theorem inf (h : ClosedLevel K E D g μ) : aleph0 ≤ μ := h.closure.working.infinite

theorem aleph0_lt (h : ClosedLevel K E D g μ) : aleph0 < μ :=
  (isLSBound_ls K).1.trans_lt h.ls_lt

theorem t_lt (h : ClosedLevel K E D g μ) {ρ : Cardinal.{u}} (hρ : aleph0 ≤ ρ) (hρμ : ρ < μ) :
    D.t ρ < μ :=
  (h.closure.closed D.t (Set.mem_insert _ _)).below ρ hρ hρμ

theorem g_lt (h : ClosedLevel K E D g μ) {ρ : Cardinal.{u}} (hρ : aleph0 ≤ ρ) (hρμ : ρ < μ) :
    g ρ < μ :=
  (h.closure.closed g (Set.mem_insert_of_mem _ rfl)).below ρ hρ hρμ

theorem lt_t (h : ClosedLevel K E D g μ) : μ < D.t μ := sigma_lt_t D h.inf

end ClosedLevel

/-! ## Lifts of bounded diagrams, as tuples of `E(J)` -/

section Lift

variable {E : OrderPresentation K} {D : StableDiagram K} {g : Cardinal.{u} → Cardinal.{u}}
  {μ : Cardinal.{u}} {I : Type u} [LinearOrder I] [Nonempty I]
  {B : Model K.τ} (hB : K.Mem B)
  (incl : Language.Embedding K.τ (E.obj I).carrier B.carrier)

variable (E D) in
/-- **The tuple `z` of `E(J)`, `J ⊇ I`, lifts the bounded diagrams of `d`.** For every
parameter tuple `p` of `A = E(I)` and every infinite bound `ρ < μ`, the tuple `(z, p)` of
`E(J)` has the diagram `D(d, p; B)`. -/
def LiftsTuple (μ : Cardinal.{u}) {J : Type u} [LinearOrder J] [Nonempty J] (f : I ↪o J)
    {α : Type u} (d : α → B.carrier) (z : α → (E.obj J).carrier) : Prop :=
  ∀ ⦃β : Type u⦄ (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ) (_ : ρ < μ)
    (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ ρ)
    (hBc : D.t ρ ≤ Model.card B) (hJc : D.t ρ ≤ Model.card (E.obj J)),
    D.same hj hB (orderPresentation_obj_mem E J) hBc hJc
      (Sum.elim d (fun b => incl (p b))) (Sum.elim z (fun b => E.map f (p b)))

variable {hB incl}
variable {J L : Type u} [LinearOrder J] [Nonempty J] [LinearOrder L] [Nonempty L]
  {α α' : Type u}

/-- A lift stays a lift after extending the order of the presentation. -/
theorem LiftsTuple.map {f : I ↪o J} {d : α → B.carrier} {z : α → (E.obj J).carrier}
    (hz : LiftsTuple E D hB incl μ f d z)
    (hJμ : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ Model.card (E.obj J)) (F : J ↪o L) :
    LiftsTuple E D hB incl μ (f.trans F) d (fun a => E.map F (z a)) := by
  intro β ρ hρinf hρ p hj hBc hLc
  have hJc := hJμ ρ hρinf hρ
  have h1 := hz ρ hρinf hρ p hj hBc hJc
  have h2 := D.of_strong hj (orderPresentation_obj_mem E J) (orderPresentation_obj_mem E L)
    hJc hLc (Sum.elim z (fun b => E.map f (p b)))
    (Sum.elim (fun a => E.map F (z a)) (fun b => E.map (f.trans F) (p b)))
    (E.map F) hρinf (E.map_strong F) (by
      rintro (a | b)
      · rfl
      · change E.map F (E.map f (p b)) = E.map (f.trans F) (p b)
        rw [E.map_comp]
        rfl)
  exact D.trans hj hB _ _ hBc hJc hLc _ _ _ h1 h2

/-- A sublist (or reindexing) of a lift lifts the corresponding sublist. -/
theorem LiftsTuple.reindex {f : I ↪o J} {d : α → B.carrier} {z : α → (E.obj J).carrier}
    (hz : LiftsTuple E D hB incl μ f d z) (hμinf : aleph0 ≤ μ) (hℓ : ls K < μ)
    (hα : #α < μ) (hBμ : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ Model.card B)
    (hJμ : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ Model.card (E.obj J)) (ι : α' → α) :
    LiftsTuple E D hB incl μ f (fun a => d (ι a)) (fun a => z (ι a)) := by
  intro β ρ hρinf hρ p hj hBc hJc
  have hβ : #β ≤ ρ := by
    refine le_trans ?_ hj
    rw [mk_sum, lift_id, lift_id]
    exact self_le_add_left _ _
  have hρ₀inf : aleph0 ≤ #α + ρ := hρinf.trans (self_le_add_left _ _)
  have hρ₀μ : #α + ρ < μ := add_lt_of_lt hμinf hα hρ
  have hρ₁inf : aleph0 ≤ (#α + ρ) ⊔ ls K := hρ₀inf.trans le_sup_left
  have hρ₁μ : (#α + ρ) ⊔ ls K < μ := max_lt hρ₀μ hℓ
  have hj₀ : #(α ⊕ β) ≤ #α + ρ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_le_add le_rfl hβ
  have h1 := D.same_relevel hj₀ hρ₀inf hρinf le_sup_left
    ((self_le_add_left ρ #α).trans le_sup_left) le_sup_right hB
    (orderPresentation_obj_mem E J) (hBμ _ hρ₀inf hρ₀μ) (hJμ _ hρ₀inf hρ₀μ)
    (hBμ _ hρ₁inf hρ₁μ) (hJμ _ hρ₁inf hρ₁μ) hBc hJc _ _
    (hz _ hρ₀inf hρ₀μ p hj₀ (hBμ _ hρ₀inf hρ₀μ) (hJμ _ hρ₀inf hρ₀μ)) hj (Sum.map ι id)
  have e1 : (fun c => Sum.elim d (fun b => incl (p b)) (Sum.map ι id c)) =
      Sum.elim (fun a => d (ι a)) (fun b => incl (p b)) := by
    funext c
    rcases c with a | b <;> rfl
  have e2 : (fun c => Sum.elim z (fun b => E.map f (p b)) (Sum.map ι id c)) =
      Sum.elim (fun a => z (ι a)) (fun b => E.map f (p b)) := by
    funext c
    rcases c with a | b <;> rfl
  rw [e1, e2] at h1
  exact h1

/-- A tuple of `A` is lifted by its image under the order map. -/
theorem liftsTuple_of_base (hstrong : K.Strong incl)
    (hIμ : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ Model.card (E.obj I)) (f : I ↪o J)
    (a : α → (E.obj I).carrier) :
    LiftsTuple E D hB incl μ f (fun i => incl (a i)) (fun i => E.map f (a i)) := by
  intro β ρ hρinf hρ p hj hBc hJc
  have hIc := hIμ ρ hρinf hρ
  have hI' : K.Mem (E.obj I) := orderPresentation_obj_mem E I
  have h1 := D.of_strong hj hI' hB hIc hBc (Sum.elim a p)
    (Sum.elim (fun i => incl (a i)) (fun b => incl (p b))) incl hρinf hstrong (by
      rintro (i | b) <;> rfl)
  have h2 := D.of_strong hj hI' (orderPresentation_obj_mem E J) hIc hJc (Sum.elim a p)
    (Sum.elim (fun i => E.map f (a i)) (fun b => E.map f (p b))) (E.map f) hρinf
    (E.map_strong f) (by rintro (i | b) <;> rfl)
  exact D.trans hj hB hI' _ hBc hIc hJc _ _ _ (D.symm hj hI' hB hIc hBc _ _ h1) h2

/-- A placement lifting the bounded diagrams of `d` gives a lift in its own presentation. -/
theorem Placement.LiftsBounded.liftsTuple {P : Placement E.lab E.arity I α}
    {d : α → B.carrier} (h : P.LiftsBounded E D hB incl d μ) :
    LiftsTuple E D hB incl μ P.f d (fun a => E.realize (P.z a)) := by
  intro β ρ hρinf hρ p hj hBc hJc
  have h1 := h ρ hρinf hρ p hj hBc hJc
  rw [Placement.realize_joint_eq] at h1
  exact h1

/-- Lifting the bounded diagrams of `d` only depends on the placed comparison over `A`. -/
theorem Placement.LiftsBounded.of_agreeOn {P P' : Placement E.lab E.arity I α}
    {d : α → B.carrier} (h : P'.LiftsBounded E D hB incl d μ)
    (hag : P.AgreeOn E D P' Set.univ)
    (hP'μ : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ Model.card (E.obj P'.J)) :
    P.LiftsBounded E D hB incl d μ := by
  intro β ρ hρinf hρ p hj hBc hJc
  have hJc' := hP'μ ρ hρinf hρ
  have h1 := h ρ hρinf hρ p hj hBc hJc'
  have h2 := SameNaturalDiagram.same hρinf
    (hag (fun b => supportTermOf E (p b)) ρ hρinf hj (fun b => Set.subset_univ _)) hJc hJc'
    (orderPresentation_obj_mem E P.J) (orderPresentation_obj_mem E P'.J)
  exact D.trans hj hB _ _ hBc hJc' hJc _ _ _ h1 (D.symm hj _ _ hJc hJc' _ _ h2)

section Level

variable [CategoricalUnbounded K] [WellFoundedLT I]

/-- **Lemma 4.10, existence.** The bounded diagrams of a bounded tuple lift to a tuple of a
presentation `E(J)`, `J ⊇ I`, which can be taken above the threshold for diagrams of length
`μ` and of size at least any prescribed cardinal. -/
theorem exists_liftsTuple (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    (hstrong : K.Strong incl) (hcard : Model.card B = μ) (d : α → B.carrier) (hα : #α < μ)
    (κ : Cardinal.{u}) :
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (f : I ↪o J)
      (z : α → (E.obj J).carrier),
      D.t μ ≤ Model.card (E.obj J) ∧ κ ≤ Model.card (E.obj J) ∧
        LiftsTuple E D hB incl μ f d z := by
  obtain ⟨J, linJ, nonJ, f, z, hJ, hJc, hlift, -⟩ :=
    boundedDiagramLift (hB := hB) (incl := incl) (d := d) hL.tester hL.closure
      (le_sup_right : aleph0 ≤ #α ⊔ aleph0) (max_lt hα hL.aleph0_lt) hL.ls_lt hL.cat hI
      hstrong hcard le_sup_left
  obtain ⟨L, linL, nonL, F, hLκ⟩ := exists_large_extension E J κ
  have hJL : Model.card (E.obj J) ≤ Model.card (E.obj L) :=
    mk_le_of_injective (E.map F).injective
  have hz : LiftsTuple E D hB incl μ f d z :=
    fun β ρ h1 h2 p hj hBc hJc' => hlift ρ h1 h2 p hj hBc hJc'
  refine ⟨L, linL, nonL, f.trans F, fun a => E.map F (z a), hJc.trans hJL, hLκ, ?_⟩
  exact hz.map (fun ρ hρinf hρ => (D.mono ρ μ hρ.le).trans hJc) F

/-- **Lemma 4.10, uniqueness.** Two lifts of the bounded diagrams of a bounded tuple, in
presentations above the threshold for diagrams of length `μ`, have the same diagram with every
parameter tuple of `A` of length at most `μ`. -/
theorem LiftsTuple.same_of_lifts (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    (hstrong : K.Strong incl) (hcard : Model.card B = μ) {d : α → B.carrier} (hα : #α < μ)
    {f : I ↪o J} {f' : I ↪o L} {z : α → (E.obj J).carrier} {z' : α → (E.obj L).carrier}
    (hz : LiftsTuple E D hB incl μ f d z) (hz' : LiftsTuple E D hB incl μ f' d z')
    {β : Type u} (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ μ)
    (hJc : D.t μ ≤ Model.card (E.obj J)) (hLc : D.t μ ≤ Model.card (E.obj L)) :
    D.same hj (orderPresentation_obj_mem E J) (orderPresentation_obj_mem E L) hJc hLc
      (Sum.elim z (fun b => E.map f (p b))) (Sum.elim z' (fun b => E.map f' (p b))) := by
  obtain ⟨J₀, linJ₀, nonJ₀, f₀, z₀, hJ₀, hJ₀c, -, huniq⟩ :=
    boundedDiagramLift (hB := hB) (incl := incl) (d := d) hL.tester hL.closure
      (le_sup_right : aleph0 ≤ #α ⊔ aleph0) (max_lt hα hL.aleph0_lt) hL.ls_lt hL.cat hI
      hstrong hcard le_sup_left
  have h1 := huniq f z (orderPresentation_obj_mem E J)
    (fun {β} ρ a b p hj hBc hJc' => hz ρ a b p hj hBc hJc') p hj hJ₀c hJc
  have h2 := huniq f' z' (orderPresentation_obj_mem E L)
    (fun {β} ρ a b p hj hBc hJc' => hz' ρ a b p hj hBc hJc') p hj hJ₀c hLc
  exact D.trans hj _ hJ₀ _ hJc hJ₀c hLc _ _ _ (D.symm hj hJ₀ _ hJ₀c hJc _ _ h1) h2

/-- **The realizations can retain the previous assignments.** Let `G = E(J)`, where
`γ = ‖G‖ ≥ t(μ)` is a categoricity cardinal. If `z` lifts the bounded tuple `d` in `G`, and
`d` is a sublist of the bounded tuple `d'`, some lift of `d'` in `G` extends `z`.

The lift `z₁` of `d'` in a presentation `E(J₁)` of size at least `γ` (Lemma 4.10) restricts to
a lift of `d`; by uniqueness its tuple `(d, A)` has the diagram of the already assigned
`(z, A)`. Its length is at most `μ`, so Proposition 4.2 at `γ ≥ t(μ)` supplies a strong map
into `G` of a strong `γ`-submodel of `E(J₁)` through `z₁` and `A`, fixing these previous
data. -/
theorem exists_lift_extension (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    (hstrong : K.Strong incl) (hcard : Model.card B = μ) (f : I ↪o J)
    (hcatJ : Categorical K (Model.card (E.obj J))) (hJc : D.t μ ≤ Model.card (E.obj J))
    {d : α → B.carrier} {z : α → (E.obj J).carrier} (hz : LiftsTuple E D hB incl μ f d z)
    (hα : #α < μ) (d' : α' → B.carrier) (hα' : #α' < μ) (ι : α → α')
    (hι : ∀ a, d' (ι a) = d a) :
    ∃ z' : α' → (E.obj J).carrier,
      LiftsTuple E D hB incl μ f d' z' ∧ ∀ a, z' (ι a) = z a := by
  classical
  have hμinf := hL.inf
  have hIc : Model.card (E.obj I) = μ := orderPresentation_obj_card E hI hL.ls_lt.le hμinf
  have hG : K.Mem (E.obj J) := orderPresentation_obj_mem E J
  have ht : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ μ := fun ρ h1 h2 => (hL.t_lt h1 h2).le
  have hBμ : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ Model.card B := fun ρ h1 h2 =>
    (ht ρ h1 h2).trans hcard.ge
  obtain ⟨J₁, lin₁, non₁, f₁, z₁, hJ₁c, hJ₁G, hz₁⟩ :=
    exists_liftsTuple (hB := hB) (incl := incl) hL hI hstrong hcard d' hα'
      (Model.card (E.obj J))
  have hM₁ : K.Mem (E.obj J₁) := orderPresentation_obj_mem E J₁
  have hJ₁μ : ∀ ρ, aleph0 ≤ ρ → ρ < μ → D.t ρ ≤ Model.card (E.obj J₁) := fun ρ h1 h2 =>
    (D.mono ρ μ h2.le).trans hJ₁c
  have hz₁ι : LiftsTuple E D hB incl μ f₁ d (fun a => z₁ (ι a)) := by
    have h := hz₁.reindex hμinf hL.ls_lt hα' hBμ hJ₁μ ι
    have e : (fun a => d' (ι a)) = d := funext hι
    rwa [e] at h
  -- uniqueness at the level `μ`, over all of `A`
  have hj : #(α ⊕ (E.obj I).carrier) ≤ μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_le_of_le hμinf hα.le hIc.le
  have hsame := LiftsTuple.same_of_lifts hL hI hstrong hcard hα hz₁ι hz (fun x => x) hj
    hJ₁c hJc
  -- Proposition 4.2 at `γ = ‖G‖`
  have hμG : μ ≤ Model.card (E.obj J) := hL.lt_t.le.trans hJc
  obtain ⟨N, i, φ, hN, hcN, hi, hφ, hxs, hws⟩ := D.exists_transport hM₁ hG hμinf hj hcatJ
    (hL.ls_lt.le.trans hμG) hJc hJ₁G _ _ hsame z₁ (hα'.le.trans hμG)
  choose w hw using hws
  have hpar : ∀ a : (E.obj I).carrier, ∃ x, i x = E.map f₁ a ∧ φ x = E.map f a :=
    fun a => hxs (Sum.inr a)
  choose v hv using hpar
  refine ⟨fun b => φ (w b), ?_, fun a => ?_⟩
  · intro β ρ hρinf hρ p hjρ hBc hGc
    have hNc : D.t ρ ≤ Model.card N := hGc.trans hcN.ge
    have hJ₁ρ := hJ₁μ ρ hρinf hρ
    have h1 := hz₁ ρ hρinf hρ p hjρ hBc hJ₁ρ
    have h2 := D.of_strong hjρ hN hM₁ hNc hJ₁ρ (Sum.elim w (fun b => v (p b)))
      (Sum.elim z₁ (fun b => E.map f₁ (p b))) i hρinf hi (by
        rintro (a | b)
        · exact hw a
        · exact (hv (p b)).1)
    have h3 := D.of_strong hjρ hN hG hNc hGc (Sum.elim w (fun b => v (p b)))
      (Sum.elim (fun b => φ (w b)) (fun b => E.map f (p b))) φ hρinf hφ (by
        rintro (a | b)
        · rfl
        · exact (hv (p b)).2)
    exact D.trans hjρ hB hM₁ hG hBc hJ₁ρ hGc _ _ _ h1
      (D.trans hjρ hM₁ hN hG hJ₁ρ hNc hGc _ _ _ (D.symm hjρ hN hM₁ hNc hJ₁ρ _ _ h2) h3)
  · obtain ⟨x, hx1, hx2⟩ := hxs (Sum.inl a)
    have hx : x = w (ι a) := i.injective (hx1.trans (hw (ι a)).symm)
    change φ (w (ι a)) = z a
    rw [← hx]
    exact hx2

end Level

end Lift

/-! ## Countable towers of small strong submodels -/

/-- A strong submodel of `B` of size less than `μ`. -/
structure SmallStrongSub (K : AbstractElementaryClass.{u}) (B : Model K.τ)
    (μ : Cardinal.{u}) where
  obj : Model K.τ
  incl : Language.Embedding K.τ obj.carrier B.carrier
  strong : K.Strong incl
  card_lt : Model.card obj < μ

/-- **`B` is a countable union of small strong submodels.** If `‖B‖ = μ > ℓ` has countable
cofinality, `B` is the union of an increasing sequence of strong submodels of size less than
`μ`, the first of which contains a given bounded tuple: apply LS along a countable exhaustion
of `B`, containing the preceding submodel at each step. -/
theorem exists_strong_tower {B : Model K.τ} (hB : K.Mem B) {μ : Cardinal.{u}}
    (hμinf : aleph0 ≤ μ) (hcof : Ordinal.cof μ.ord = aleph0) (hℓ : ls K < μ)
    (hcard : Model.card B = μ) {α : Type u} (d : α → B.carrier) (hα : #α < μ) :
    ∃ (M : ℕ → Model K.τ) (j : ∀ n, Language.Embedding K.τ (M n).carrier B.carrier),
      (∀ n, K.Strong (j n)) ∧ (∀ n, Model.card (M n) < μ) ∧
      (∀ n x, ∃ y, j (n + 1) y = j n x) ∧ (∀ b, ∃ n x, j n x = b) ∧
      ∀ a, ∃ x, j 0 x = d a := by
  classical
  obtain ⟨A, hAcard, -, hAcov⟩ :=
    exists_countable_set_exhaustion (X := B.carrier) hcard hμinf hcof
  have hull : ∀ Y : Set B.carrier, #Y < μ →
      ∃ Q : SmallStrongSub K B μ, ∀ y ∈ Y, ∃ x, Q.incl x = y := by
    intro Y hY
    obtain ⟨N, i, -, hi, hcov, hc⟩ := (isLSBound_ls K).2.2 B hB Y
    exact ⟨⟨N, i, hi, hc.trans_lt (add_lt_of_lt hμinf hY hℓ)⟩, hcov⟩
  have hrange : ∀ P : SmallStrongSub K B μ, #(Set.range P.incl) < μ := fun P =>
    mk_range_le.trans_lt P.card_lt
  have hbase : ∃ Q : SmallStrongSub K B μ, ∀ y ∈ A 0 ∪ Set.range d, ∃ x, Q.incl x = y :=
    hull _ ((mk_union_le _ _).trans_lt
      (add_lt_of_lt hμinf (hAcard 0) (mk_range_le.trans_lt hα)))
  have hstep : ∀ (n : ℕ) (P : SmallStrongSub K B μ), ∃ Q : SmallStrongSub K B μ,
      ∀ y ∈ A (n + 1) ∪ Set.range P.incl, ∃ x, Q.incl x = y := fun n P =>
    hull _ ((mk_union_le _ _).trans_lt (add_lt_of_lt hμinf (hAcard (n + 1)) (hrange P)))
  let seq : ℕ → SmallStrongSub K B μ := fun n =>
    Nat.rec (Classical.choose hbase) (fun n P => Classical.choose (hstep n P)) n
  have hseq : ∀ n, ∀ y ∈ A (n + 1) ∪ Set.range (seq n).incl, ∃ x, (seq (n + 1)).incl x = y :=
    fun n => Classical.choose_spec (hstep n (seq n))
  have hseq0 : ∀ y ∈ A 0 ∪ Set.range d, ∃ x, (seq 0).incl x = y :=
    Classical.choose_spec hbase
  refine ⟨fun n => (seq n).obj, fun n => (seq n).incl, fun n => (seq n).strong,
    fun n => (seq n).card_lt, fun n x => hseq n _ (Or.inr ⟨x, rfl⟩), fun b => ?_,
    fun a => hseq0 _ (Or.inr ⟨a, rfl⟩)⟩
  obtain ⟨n, hn⟩ := hAcov b
  cases n with
  | zero =>
    obtain ⟨x, hx⟩ := hseq0 b (Or.inl hn)
    exact ⟨0, x, hx⟩
  | succ n =>
    obtain ⟨x, hx⟩ := hseq n b (Or.inl hn)
    exact ⟨n + 1, x, hx⟩

/-! ## The embedding of `B` into `G` over `A` -/

section Embedding

variable {E : OrderPresentation K} {D : StableDiagram K} {g : Cardinal.{u} → Cardinal.{u}}
  {μ : Cardinal.{u}} {I : Type u} [LinearOrder I] [Nonempty I]
  {B : Model K.τ} {hB : K.Mem B}
  {incl : Language.Embedding K.τ (E.obj I).carrier B.carrier}
  {J : Type u} [LinearOrder J] [Nonempty J]

/-- **The copied small models are strong submodels of `G`.** If `z` lifts an enumeration of a
strong submodel `M` of `B` of size less than `μ`, then `z` is a strong map `M → G`: the copied
and original lists have the same bounded diagram, and Proposition 4.2 gives a strong map
between strong `t(ρ)`-submodels of `B` and `G` with exactly the prescribed values; coherence
makes `M` strong in the first one. -/
theorem exists_strong_of_liftsTuple (hL : ClosedLevel K E D g μ) (hcard : Model.card B = μ)
    (f : I ↪o J) (hJμ : μ ≤ Model.card (E.obj J)) {M : Model K.τ}
    (j : Language.Embedding K.τ M.carrier B.carrier) (hj : K.Strong j)
    (hM : Model.card M < μ) {z : M.carrier → (E.obj J).carrier}
    (hz : LiftsTuple E D hB incl μ f (fun x => j x) z) :
    ∃ h : Language.Embedding K.τ M.carrier (E.obj J).carrier,
      K.Strong h ∧ ∀ x, h x = z x := by
  classical
  have hρinf : aleph0 ≤ Model.card M ⊔ ls K := (isLSBound_ls K).1.trans le_sup_right
  have hρμ : Model.card M ⊔ ls K < μ := max_lt hM hL.ls_lt
  have hjρ : #(M.carrier ⊕ PEmpty.{u + 1}) ≤ Model.card M ⊔ ls K := by
    rw [mk_sum, lift_id, lift_id, mk_pempty, add_zero]
    exact le_sup_left
  have hBc : D.t (Model.card M ⊔ ls K) ≤ Model.card B :=
    (hL.t_lt hρinf hρμ).le.trans hcard.ge
  have hGc : D.t (Model.card M ⊔ ls K) ≤ Model.card (E.obj J) :=
    (hL.t_lt hρinf hρμ).le.trans hJμ
  have h1 := hz _ hρinf hρμ (fun e : PEmpty.{u + 1} => e.elim) hjρ hBc hGc
  obtain ⟨A, i, r, hA, hAc, hi, hr, hhit, -⟩ := D.exists_common_hull hjρ hρinf le_rfl
    le_sup_right hB (orderPresentation_obj_mem E J) hBc hGc hBc hGc _ _ h1 ∅ (by simp)
  choose a ha using hhit
  have himg : ∀ x, ∃ y, i y = j x := fun x => ⟨a (Sum.inl x), (ha (Sum.inl x)).1⟩
  refine ⟨r.comp (factorEmbedding j i himg),
    K.strong_trans _ r (strong_factorEmbedding j i hj hi himg) hr, fun x => ?_⟩
  have e : factorEmbedding j i himg x = a (Sum.inl x) :=
    i.injective ((factorEmbedding_apply j i himg x).trans (ha (Sum.inl x)).1.symm)
  rw [Language.Embedding.comp_apply, e]
  exact (ha (Sum.inl x)).2

variable [CategoricalUnbounded K] [WellFoundedLT I]

/-- **Every `μ`-sized strong extension `B` of `A` embeds strongly into `G` over `A`**,
extending any assigned lift `z` of a bounded tuple `d` of `B`. Here `G = E(J)`, `J ⊇ I`, and
`γ = ‖G‖ ≥ t(μ)` is a categoricity cardinal.

Choose small strong submodels `M n` of `B`, increasing with union `B`, the first one
containing `d`. Lemma 4.10 assigns lifts to their enumerations, each retaining the previous
assignment (`exists_lift_extension`). The copied small models are strong submodels of `G`
(`exists_strong_of_liftsTuple`); they are nested, and their union is a strong map `B → G`
(`exists_strong_of_nat_exhaustion`). Every element of `A` occurs in some `M n`, and its
equality with that parameter is part of the lifted comparison, so the map fixes `A`. -/
theorem exists_strong_embedding_over (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    (hstrong : K.Strong incl) (hcard : Model.card B = μ) (f : I ↪o J)
    (hcatJ : Categorical K (Model.card (E.obj J))) (hJc : D.t μ ≤ Model.card (E.obj J))
    {α : Type u} (d : α → B.carrier) (hα : #α < μ) (z : α → (E.obj J).carrier)
    (hz : LiftsTuple E D hB incl μ f d z) :
    ∃ F : Language.Embedding K.τ B.carrier (E.obj J).carrier,
      K.Strong F ∧ (∀ a, F (incl a) = E.map f a) ∧ ∀ a, F (d a) = z a := by
  classical
  have hμinf := hL.inf
  have hG : K.Mem (E.obj J) := orderPresentation_obj_mem E J
  have hJμ : μ ≤ Model.card (E.obj J) := hL.lt_t.le.trans hJc
  obtain ⟨M, j, hj, hMc, hmono, hcov, hd⟩ :=
    exists_strong_tower hB hμinf hL.closure.working.countableCof hL.ls_lt hcard d hα
  choose ι₀ hι₀ using hd
  choose ι hι using hmono
  -- the lifts of the enumerations of the small submodels
  obtain ⟨z₀, hz₀, hz₀ι⟩ := exists_lift_extension hL hI hstrong hcard f hcatJ hJc hz hα
    (fun x => j 0 x) (hMc 0) ι₀ hι₀
  have hstep : ∀ n (zn : (M n).carrier → (E.obj J).carrier),
      LiftsTuple E D hB incl μ f (fun x => j n x) zn →
      ∃ z' : (M (n + 1)).carrier → (E.obj J).carrier,
        LiftsTuple E D hB incl μ f (fun x => j (n + 1) x) z' ∧ ∀ x, z' (ι n x) = zn x :=
    fun n zn hzn => exists_lift_extension hL hI hstrong hcard f hcatJ hJc hzn (hMc n)
      (fun x => j (n + 1) x) (hMc (n + 1)) (ι n) (hι n)
  let Z : ∀ n, {zn : (M n).carrier → (E.obj J).carrier //
      LiftsTuple E D hB incl μ f (fun x => j n x) zn} := fun n =>
    Nat.rec (motive := fun n => {zn : (M n).carrier → (E.obj J).carrier //
        LiftsTuple E D hB incl μ f (fun x => j n x) zn})
      ⟨z₀, hz₀⟩
      (fun n P => ⟨Classical.choose (hstep n P.1 P.2),
        (Classical.choose_spec (hstep n P.1 P.2)).1⟩) n
  have hZ : ∀ n x, (Z (n + 1)).1 (ι n x) = (Z n).1 x := fun n x =>
    (Classical.choose_spec (hstep n (Z n).1 (Z n).2)).2 x
  -- the copies are strong, nested, and their union is a strong map
  have hex : ∀ n, ∃ h : Language.Embedding K.τ (M n).carrier (E.obj J).carrier,
      K.Strong h ∧ ∀ x, h x = (Z n).1 x := fun n =>
    exists_strong_of_liftsTuple hL hcard f hJμ (j n) (hj n) (hMc n) (Z n).2
  choose h hh hhZ using hex
  obtain ⟨F, hF, hFj⟩ := exists_strong_of_nat_exhaustion hB hG M j hj
    (fun n x => ⟨ι n x, hι n x⟩) hcov h hh (by
      intro n x y hxy
      have hy : y = ι n x := (j (n + 1)).injective (hxy.trans (hι n x).symm)
      rw [hy, hhZ, hhZ, hZ])
  refine ⟨F, hF, fun a => ?_, fun a => ?_⟩
  · -- `A` is fixed: equality with a parameter is part of the lifted comparison
    obtain ⟨n, x, hx⟩ := hcov (incl a)
    rw [← hx, hFj, hhZ]
    have hρinf : aleph0 ≤ Model.card (M n) ⊔ aleph0 := le_sup_right
    have hρμ : Model.card (M n) ⊔ aleph0 < μ := max_lt (hMc n) hL.aleph0_lt
    have hjρ : #((M n).carrier ⊕ PUnit.{u + 1}) ≤ Model.card (M n) ⊔ aleph0 := by
      rw [mk_sum, lift_id, lift_id, mk_punit]
      exact add_le_of_le hρinf le_sup_left (one_le_aleph0.trans le_sup_right)
    have hBc : D.t (Model.card (M n) ⊔ aleph0) ≤ Model.card B :=
      (hL.t_lt hρinf hρμ).le.trans hcard.ge
    have hGc : D.t (Model.card (M n) ⊔ aleph0) ≤ Model.card (E.obj J) :=
      (hL.t_lt hρinf hρμ).le.trans hJμ
    have hsame := (Z n).2 _ hρinf hρμ (fun _ : PUnit.{u + 1} => a) hjρ hBc hGc
    exact (D.preserves_atomic hjρ hB hG hBc hGc _ _ hsame (Sum.inl x)
      (Sum.inr PUnit.unit)).mp hx
  · rw [← hι₀ a, hFj, hhZ]
    exact hz₀ι a

end Embedding

/-! ## Amalgams -/

section Amalgam

variable {E : OrderPresentation K} {D : StableDiagram K} {g : Cardinal.{u} → Cardinal.{u}}
  {μ : Cardinal.{u}} {I : Type u} [LinearOrder I] [Nonempty I] [WellFoundedLT I]
  {B₀ B₁ : Model K.τ} {hB₀ : K.Mem B₀} {hB₁ : K.Mem B₁}
  {incl₀ : Language.Embedding K.τ (E.obj I).carrier B₀.carrier}
  {incl₁ : Language.Embedding K.τ (E.obj I).carrier B₁.carrier}
  {α : Type u}

/-- **An amalgam identifying tuples with a common lift.** Embed both extensions into the same
`G` over `A`, extending the common lift; LS supplies a strong `μ`-submodel of `G` containing
both images, and coherence makes it a strong amalgam of the required size. -/
theorem exists_amalgam_of_common_lift [CategoricalUnbounded K]
    (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    (hs₀ : K.Strong incl₀) (hs₁ : K.Strong incl₁)
    (hc₀ : Model.card B₀ = μ) (hc₁ : Model.card B₁ = μ)
    {J : Type u} [LinearOrder J] [Nonempty J] (f : I ↪o J)
    (hcatJ : Categorical K (Model.card (E.obj J))) (hJc : D.t μ ≤ Model.card (E.obj J))
    (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier) (hα : #α < μ) (z : α → (E.obj J).carrier)
    (hz₀ : LiftsTuple E D hB₀ incl₀ μ f d₀ z) (hz₁ : LiftsTuple E D hB₁ incl₁ μ f d₁ z) :
    ∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
      (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
      K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧ Model.card P = μ ∧
      (∀ x, g₀ (incl₀ x) = g₁ (incl₁ x)) ∧ ∀ i, g₀ (d₀ i) = g₁ (d₁ i) := by
  obtain ⟨F₀, hF₀, hF₀i, hF₀d⟩ :=
    exists_strong_embedding_over hL hI hs₀ hc₀ f hcatJ hJc d₀ hα z hz₀
  obtain ⟨F₁, hF₁, hF₁i, hF₁d⟩ :=
    exists_strong_embedding_over hL hI hs₁ hc₁ f hcatJ hJc d₁ hα z hz₁
  have hG : K.Mem (E.obj J) := orderPresentation_obj_mem E J
  have hμG : μ ≤ Model.card (E.obj J) := hL.lt_t.le.trans hJc
  have hT : #↥(Set.range F₀ ∪ Set.range F₁) ≤ μ := by
    refine (mk_union_le _ _).trans ?_
    have h := add_le_add ((mk_range_le (f := F₀)).trans hc₀.le)
      ((mk_range_le (f := F₁)).trans hc₁.le)
    rwa [add_eq_self hL.inf] at h
  obtain ⟨P, i, hP, hi, hcP, hcov⟩ :=
    exists_strong_hull_exact_card K μ hL.ls_lt.le hL.inf (E.obj J) hG hμG _ hT
  have himg₀ : ∀ x, ∃ y, i y = F₀ x := fun x => hcov _ (Or.inl ⟨x, rfl⟩)
  have himg₁ : ∀ x, ∃ y, i y = F₁ x := fun x => hcov _ (Or.inr ⟨x, rfl⟩)
  refine ⟨P, factorEmbedding F₀ i himg₀, factorEmbedding F₁ i himg₁, hP,
    strong_factorEmbedding F₀ i hF₀ hi himg₀, strong_factorEmbedding F₁ i hF₁ hi himg₁, hcP,
    fun x => ?_, fun a => ?_⟩
  · apply i.injective
    rw [factorEmbedding_apply, factorEmbedding_apply, hF₀i, hF₁i]
  · apply i.injective
    rw [factorEmbedding_apply, factorEmbedding_apply, hF₀d, hF₁d]

/-- **An amalgam identifying tuples whose placed lifts have the same comparison over `A`.**
Realize the common lift once in a presentation `G` of categoricity size at least `t(μ)`. -/
theorem exists_amalgam_of_agreeOn [CategoricalUnbounded K]
    (hL : ClosedLevel K E D g μ) (hI : #I = μ)
    (hs₀ : K.Strong incl₀) (hs₁ : K.Strong incl₁)
    (hc₀ : Model.card B₀ = μ) (hc₁ : Model.card B₁ = μ)
    (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier) (hα : #α < μ)
    {P₀ P₁ : Placement E.lab E.arity I α}
    (h₀ : P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) (h₁ : P₁.LiftsBounded E D hB₁ incl₁ d₁ μ)
    (hag : P₀.AgreeOn E D P₁ Set.univ) :
    ∃ (P : Model K.τ) (g₀ : Language.Embedding K.τ B₀.carrier P.carrier)
      (g₁ : Language.Embedding K.τ B₁.carrier P.carrier),
      K.Mem P ∧ K.Strong g₀ ∧ K.Strong g₁ ∧ Model.card P = μ ∧
      (∀ x, g₀ (incl₀ x) = g₁ (incl₁ x)) ∧ ∀ i, g₀ (d₀ i) = g₁ (d₁ i) := by
  have hIc : Model.card (E.obj I) = μ :=
    orderPresentation_obj_card E hI hL.ls_lt.le hL.inf
  have hPμ : ∀ (P : Placement E.lab E.arity I α) ρ, aleph0 ≤ ρ → ρ < μ →
      D.t ρ ≤ Model.card (E.obj P.J) := fun P ρ h1 h2 =>
    ((hL.t_lt h1 h2).le.trans hIc.ge).trans (mk_le_of_injective (E.map P.f).injective)
  obtain ⟨L, linL, nonL, e, hLc, hcatL⟩ := exists_categorical_extension E P₀.J (D.t μ)
  have h₁' : P₀.LiftsBounded E D hB₁ incl₁ d₁ μ := h₁.of_agreeOn hag (hPμ P₁)
  exact exists_amalgam_of_common_lift hL hI hs₀ hs₁ hc₀ hc₁ (P₀.f.trans e) hcatL hLc d₀ d₁ hα
    (fun a => E.map e (E.realize (P₀.z a))) (h₀.liftsTuple.map (hPμ P₀) e)
    (h₁'.liftsTuple.map (hPμ P₀) e)

/-- **Proposition 4.8 identifies the placed lifts.** If the diagrams of `d₀` and `d₁` agree
over the subsets of `A` of size at most `g(σ) + ℓ` (the elements of `A` given by at most
`g(σ)` positions of `I`), their placed lifts have the same comparison over all of `A`. -/
theorem agreeOn_univ_of_tests [CategoricalUnbounded K]
    (hL : ClosedLevel K E D g μ) (hI : #I = μ) (hc₀ : Model.card B₀ = μ)
    (hc₁ : Model.card B₁ = μ) {σ : Cardinal.{u}} (hσinf : aleph0 ≤ σ) (hσ : σ < μ)
    (hα : #α ≤ σ) (d₀ : α → B₀.carrier) (d₁ : α → B₁.carrier)
    {P₀ P₁ : Placement E.lab E.arity I α}
    (h₀ : P₀.LiftsBounded E D hB₀ incl₀ d₀ μ) (h₁ : P₁.LiftsBounded E D hB₁ incl₁ d₁ μ)
    (htest : ∀ {β : Type u}, #β ≤ g σ + ls K → ∀ (ρ : Cardinal.{u}), aleph0 ≤ ρ → ρ < μ →
      ∀ (p : β → (E.obj I).carrier) (hj : #(α ⊕ β) ≤ ρ)
        (hBc₀ : D.t ρ ≤ Model.card B₀) (hBc₁ : D.t ρ ≤ Model.card B₁),
        D.same hj hB₀ hB₁ hBc₀ hBc₁ (Sum.elim d₀ (fun b => incl₀ (p b)))
          (Sum.elim d₁ (fun b => incl₁ (p b)))) :
    P₀.AgreeOn E D P₁ Set.univ := by
  have hμinf := hL.inf
  have hlsinf : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hIc : Model.card (E.obj I) = μ := orderPresentation_obj_card E hI hL.ls_lt.le hμinf
  have hχμ : g σ + ls K < μ := add_lt_of_lt hμinf (hL.g_lt hσinf hσ) hL.ls_lt
  have hρinf : aleph0 ≤ σ + (g σ + ls K) := hσinf.trans (self_le_add_right _ _)
  have hρμ : σ + (g σ + ls K) < μ := add_lt_of_lt hμinf hσ hχμ
  have ht : D.t (σ + (g σ + ls K)) ≤ μ := (hL.t_lt hρinf hρμ).le
  refine hL.tester σ hσinf hα P₀ P₁ fun X hX => ?_
  refine agreeOn_of_lifts (hB := hB₀) (incl := incl₀) (d := d₀) (χ := g σ + ls K) hρinf
    (ht.trans hc₀.ge)
    (ht.trans hIc.ge) (fun {β} hβ => ?_) (fun {β} _ p hj => h₀ _ hρinf hρμ p hj)
    (fun {β} hβ p hj => ?_) X ?_
  · rw [mk_sum, lift_id, lift_id]
    exact add_le_add hα hβ
  · intro hBc hJc
    have hBc₁ : D.t (σ + (g σ + ls K)) ≤ Model.card B₁ := ht.trans hc₁.ge
    exact D.trans hj hB₀ hB₁ _ hBc hBc₁ hJc _ _ _ (htest hβ _ hρinf hρμ p hj hBc hBc₁)
      (h₁ _ hρinf hρμ p hj hBc₁ hJc)
  · rw [add_assoc, add_eq_right hlsinf (one_le_aleph0.trans hlsinf)]
    exact add_le_add hX le_rfl

/-- Necessity: strong maps into a common model which identify two tuples give them the same
diagram. -/
theorem StableDiagram.same_of_amalgam (D : StableDiagram K) {M₀ M₁ P : Model K.τ}
    (hM₀ : K.Mem M₀) (hM₁ : K.Mem M₁) (hP : K.Mem P)
    (g₀ : Language.Embedding K.τ M₀.carrier P.carrier)
    (g₁ : Language.Embedding K.τ M₁.carrier P.carrier) (hg₀ : K.Strong g₀)
    (hg₁ : K.Strong g₁) {γ : Type u} (xs : γ → M₀.carrier) (ys : γ → M₁.carrier)
    (h : ∀ c, g₀ (xs c) = g₁ (ys c)) {ρ : Cardinal.{u}} (hρinf : aleph0 ≤ ρ) (hj : #γ ≤ ρ)
    (hc₀ : D.t ρ ≤ Model.card M₀) (hc₁ : D.t ρ ≤ Model.card M₁) :
    D.same hj hM₀ hM₁ hc₀ hc₁ xs ys := by
  have hPc : D.t ρ ≤ Model.card P := hc₀.trans (mk_le_of_injective g₀.injective)
  have h1 := D.of_strong hj hM₀ hP hc₀ hPc xs (fun c => g₀ (xs c)) g₀ hρinf hg₀ fun _ => rfl
  have h2 := D.of_strong hj hM₁ hP hc₁ hPc ys (fun c => g₀ (xs c)) g₁ hρinf hg₁
    fun c => (h c).symm
  exact D.trans hj hM₀ hP hM₁ hc₀ hPc hc₁ _ _ _ h1 (D.symm hj hM₁ hP hc₁ hPc _ _ h2)

end Amalgam

end
end AEC
