module

public import AEC.Section4.ClosedLevelTypes
public import AEC.Section4.StableDiagramConstruction

@[expose] public section

/-!
# Realization into a larger closed level (Corollary 6.7)

Let `ν < μ` be closed levels, `f : A → B` a strong map of `ν`-models and `i : A → N` a strong
map into a `μ`-model.

* `exists_suborder_cover`: at most `ν` elements of a presentation `E(J)` lie in `E(S)` for a
  suborder `S ⊆ J` of size exactly `ν`: collect the finite supports of their terms.
* `exists_strong_embedding_into_larger`: `B` embeds strongly into `N` over `A`, with a
  prescribed image `z` of a tuple `d` of length less than `ν` whose diagrams over the queries
  in `A` of size at most `g(|d| + ℵ₀) + ℓ` below `ν` already match.
* `exists_strong_embedding_into_larger_base`: the case of the empty tuple.
* `exists_actual_nu_type`: a tuple of `N` of length less than `ν` lies in a strong
  `ν`-submodel of `N` containing `A`, with the same diagrams over `A` (mixed comparisons).

Proof of the embedding. Identify `N` with its chart `E(Below μ)` (categoricity at `μ`). The
images of `A` and `z` use at most `ν` positions, so they lie in `N₀ = E(S)` for a well-ordered
suborder `S` of size `ν`; coherence makes `A → N₀` strong. Now `B` and `N₀` are `ν`-sized strong
extensions of `A` whose tuples `d`, `z` pass the tests, so Theorem 4.11 (2) at `ν`
(`ClosedLevel.exists_tuple_amalgam`) gives a `ν`-sized amalgam `P` over `A` identifying them.
Finally `N₀ = E(S) → E(Below μ)` is the order map of a presentation, and `μ ≥ t(ν)` is a
categoricity cardinal, so the countable tower of Theorem 4.11 at the source level `ν`
(`exists_strong_embedding_over`) embeds `P` strongly into the chart of `N` over `N₀`, without
enlarging the target.

No comparison of length `ν` is made in a `ν`-model (`t(ν) > ν`): the only ones are those of
`exists_strong_embedding_over`, between presentations of size at least `t(ν)`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}
variable [CategoricalUnbounded K] {E : OrderPresentation K} {D : StableDiagram K}
  {g : Cardinal.{u} → Cardinal.{u}}

/-- **A bounded set of a presentation lies in a suborder presentation of the same size.** At
most `ν` elements of `E(J)`, `ν ≤ |J|` infinite, are images of elements of `E(S)` for a
suborder `S ⊆ J` of size exactly `ν`. -/
theorem exists_suborder_cover {J : Type u} [LinearOrder J] [Nonempty J] {ν : Cardinal.{u}}
    (hνinf : aleph0 ≤ ν) (hνJ : ν ≤ #J) (T : Set (E.obj J).carrier) (hT : #↥T ≤ ν) :
    ∃ (S : Set J) (_ : Nonempty ↥S), #↥S = ν ∧
      ∀ x ∈ T, ∃ y, E.map (OrderEmbedding.subtype (· ∈ S)) y = x := by
  obtain ⟨S₁, hS₁⟩ := le_mk_iff_exists_set.mp hνJ
  let t : ↥T → SupportTerm E.lab E.arity J := fun x => supportTermOf E x.1
  have hS₀ : #↥(tupleSupport t) ≤ ν := (mk_tupleSupport_le hT t).trans (max_le hνinf le_rfl)
  have hSc : #↥(tupleSupport t ∪ S₁) = ν := by
    refine le_antisymm ((mk_union_le _ _).trans ?_)
      (hS₁.symm.trans_le (mk_le_mk_of_subset Set.subset_union_right))
    have h := add_le_add hS₀ hS₁.le
    rwa [add_eq_self hνinf] at h
  haveI hne : Nonempty ↥(tupleSupport t ∪ S₁) :=
    mk_ne_zero_iff.mp (by rw [hSc]; exact (aleph0_pos.trans_le hνinf).ne')
  refine ⟨tupleSupport t ∪ S₁, hne, hSc, fun x hx => ?_⟩
  have hsub : termSupport (supportTermOf E x) ⊆ tupleSupport t ∪ S₁ := fun _ h =>
    Or.inl (termSupport_subset_tupleSupport t ⟨x, hx⟩ h)
  refine ⟨E.realize ((supportTermOf E x).restrict _ hsub), ?_⟩
  rw [E.realize_along, SupportTerm.along_restrict, realize_supportTermOf]

/-- **Corollary 6.7, realization with a prescribed tuple.** Let `ν < μ` be closed levels,
`f : A → B` a strong map of `ν`-models and `i : A → N` a strong map into a `μ`-model. If the
tuples `d` of `B` and `z` of `N`, of length less than `ν`, have the same diagrams over the
queries in `A` of size at most `g(|d| + ℵ₀) + ℓ` at the bounds below `ν`, a strong map
`B → N` extends `i` and takes `d` to `z`. -/
theorem exists_strong_embedding_into_larger
    {ν μ : Cardinal.{u}} (hν : ClosedLevel K E D g ν) (hμ : ClosedLevel K E D g μ)
    (hlt : ν < μ) (A B N : Model K.τ)
    (f : Language.Embedding K.τ A.carrier B.carrier)
    (i : Language.Embedding K.τ A.carrier N.carrier)
    (hA : K.Mem A) (hB : K.Mem B) (hN : K.Mem N)
    (hf : K.Strong f) (hi : K.Strong i)
    (hcA : Model.card A = ν) (hcB : Model.card B = ν) (hcN : Model.card N = μ)
    {α : Type u} (d : α → B.carrier) (z : α → N.carrier) (hα : #α < ν)
    (htest : ∀ {β : Type u} (_ : #β ≤ g (#α ⊔ aleph0) + ls K) (ρ : Cardinal.{u})
      (_ : aleph0 ≤ ρ) (_ : ρ < ν) (p : β → A.carrier) (hjoint : #(α ⊕ β) ≤ ρ)
      (h₀ : D.t ρ ≤ Model.card B) (h₁ : D.t ρ ≤ Model.card N),
      D.same hjoint hB hN h₀ h₁
        (Sum.elim d (fun b => f (p b))) (Sum.elim z (fun b => i (p b)))) :
    ∃ F : Language.Embedding K.τ B.carrier N.carrier,
      K.Strong F ∧ (∀ a, F (f a) = i a) ∧ ∀ j, F (d j) = z j := by
  classical
  have hνinf := hν.inf
  have hμinf := hμ.inf
  -- the chart of `N`
  haveI : Nonempty (Below μ) := below_nonempty hμinf
  have hJ : #(Below μ) = μ := mk_ord_toType μ
  have hG : K.Mem (E.obj (Below μ)) := orderPresentation_obj_mem E _
  have hGc : Model.card (E.obj (Below μ)) = μ :=
    orderPresentation_obj_card E hJ hμ.ls_lt.le hμinf
  obtain ⟨eN⟩ := hμ.cat.unique_model (E.obj (Below μ)) N hG hN hGc hcN
  have heN : K.Strong eN.toEmbedding := strong_of_equiv K eN hG
  -- a suborder of size `ν` whose presentation contains the images of `A` and `z`
  have hT : #↥(Set.range (fun a => eN.symm (i a)) ∪ Set.range (fun a => eN.symm (z a))) ≤ ν := by
    refine (mk_union_le _ _).trans ?_
    have h := add_le_add (mk_range_le (f := fun a => eN.symm (i a))) 
      (mk_range_le (f := fun a => eN.symm (z a)))
    exact h.trans (add_le_of_le hνinf hcA.le hα.le)
  obtain ⟨S, hSne, hSc, hcov⟩ :=
    exists_suborder_cover (E := E) hνinf (hlt.le.trans_eq hJ.symm) _ hT
  haveI := hSne
  let φ : ↥S ↪o Below μ := OrderEmbedding.subtype (· ∈ S)
  have hN₀ : K.Mem (E.obj ↥S) := orderPresentation_obj_mem E _
  have hcN₀ : Model.card (E.obj ↥S) = ν := orderPresentation_obj_card E hSc hν.ls_lt.le hνinf
  let ι : Language.Embedding K.τ (E.obj ↥S).carrier N.carrier :=
    eN.toEmbedding.comp (E.map φ)
  have hι : K.Strong ι := K.strong_trans _ _ (E.map_strong φ) heN
  have himgA : ∀ a, ∃ x, ι x = i a := fun a => by
    obtain ⟨x, hx⟩ := hcov _ (Or.inl ⟨a, rfl⟩)
    refine ⟨x, ?_⟩
    change eN (E.map φ x) = i a
    rw [hx, Language.Equiv.apply_symm_apply]
  have himgZ : ∀ a, ∃ x, ι x = z a := fun a => by
    obtain ⟨x, hx⟩ := hcov _ (Or.inr ⟨a, rfl⟩)
    refine ⟨x, ?_⟩
    change eN (E.map φ x) = z a
    rw [hx, Language.Equiv.apply_symm_apply]
  let j : Language.Embedding K.τ A.carrier (E.obj ↥S).carrier := factorEmbedding i ι himgA
  have hj : K.Strong j := strong_factorEmbedding i ι hi hι himgA
  have hιj : ∀ a, ι (j a) = i a := factorEmbedding_apply i ι himgA
  choose y hy using himgZ
  -- Theorem 4.11 (2) at `ν`: an amalgam of `B` and `E(S)` over `A` identifying `d` with `z`
  have hσinf : aleph0 ≤ #α ⊔ aleph0 := le_sup_right
  have hσ : #α ⊔ aleph0 < ν := max_lt hα hν.aleph0_lt
  obtain ⟨P, g₀, g₁, hP, hg₀, hg₁, hcP, hbase, hd⟩ :=
    hν.exists_tuple_amalgam hσinf hσ (le_sup_left : #α ≤ #α ⊔ aleph0) A B (E.obj ↥S) f j d y
      hA hB hN₀ hf hj hcA hcB hcN₀ (fun {β} hβ ρ hρinf hρ p hjnt h₀ h₁ => by
        have hNc : D.t ρ ≤ Model.card N :=
          (hν.t_lt hρinf hρ).le.trans (hlt.le.trans_eq hcN.symm)
        exact D.trans hjnt hB hN hN₀ h₀ hNc h₁ _ _ _ (htest hβ ρ hρinf hρ p hjnt h₀ hNc)
          (D.symm hjnt hN₀ hN h₁ hNc _ _
            (D.of_strong hjnt hN₀ hN h₁ hNc (Sum.elim y (fun b => j (p b)))
              (Sum.elim z (fun b => i (p b))) ι hρinf hι (by
                rintro (a | b)
                · exact hy a
                · exact hιj (p b)))))
  -- the tower of Theorem 4.11 at `ν`: `P` embeds into the chart of `N` over `E(S)`
  have hcatJ : Categorical K (Model.card (E.obj (Below μ))) := by
    rw [hGc]
    exact hμ.cat
  have hJc : D.t ν ≤ Model.card (E.obj (Below μ)) := (hμ.t_lt hνinf hlt).le.trans hGc.ge
  have hSν : ∀ ρ, aleph0 ≤ ρ → ρ < ν → D.t ρ ≤ Model.card (E.obj ↥S) := fun ρ h1 h2 =>
    (hν.t_lt h1 h2).le.trans hcN₀.ge
  let a₀ : PEmpty.{u + 1} → (E.obj ↥S).carrier := fun x => x.elim
  obtain ⟨F₁, hF₁, hF₁g, -⟩ :=
    exists_strong_embedding_over (hB := hP) (incl := g₁) hν hSc hg₁ hcP φ hcatJ hJc
      (fun x => g₁ (a₀ x)) (by rw [mk_pempty]; exact aleph0_pos.trans_le hνinf)
      (fun x => E.map φ (a₀ x)) (liftsTuple_of_base hg₁ hSν φ a₀)
  refine ⟨eN.toEmbedding.comp (F₁.comp g₀),
    K.strong_trans _ _ (K.strong_trans _ _ hg₀ hF₁) heN, fun a => ?_, fun k => ?_⟩
  · change eN (F₁ (g₀ (f a))) = i a
    rw [hbase a, hF₁g]
    exact hιj a
  · change eN (F₁ (g₀ (d k))) = z k
    rw [hd k, hF₁g]
    exact hy k

/-- **Corollary 6.7, realization.** A strong map `A → B` of `ν`-models and a strong map
`A → N` into a `μ`-model, `ν < μ` closed levels, extend to a strong map `B → N`. -/
theorem exists_strong_embedding_into_larger_base
    {ν μ : Cardinal.{u}} (hν : ClosedLevel K E D g ν) (hμ : ClosedLevel K E D g μ)
    (hlt : ν < μ) (A B N : Model K.τ)
    (f : Language.Embedding K.τ A.carrier B.carrier)
    (i : Language.Embedding K.τ A.carrier N.carrier)
    (hA : K.Mem A) (hB : K.Mem B) (hN : K.Mem N)
    (hf : K.Strong f) (hi : K.Strong i)
    (hcA : Model.card A = ν) (hcB : Model.card B = ν) (hcN : Model.card N = μ) :
    ∃ F : Language.Embedding K.τ B.carrier N.carrier,
      K.Strong F ∧ ∀ a, F (f a) = i a := by
  let d : PEmpty.{u + 1} → B.carrier := fun x => x.elim
  let z : PEmpty.{u + 1} → N.carrier := fun x => x.elim
  have hα : #(PEmpty.{u + 1}) < ν := by
    rw [mk_pempty]
    exact aleph0_pos.trans_le hν.inf
  obtain ⟨F, hF, hFA, -⟩ := exists_strong_embedding_into_larger hν hμ hlt A B N f i
    hA hB hN hf hi hcA hcB hcN d z hα (fun {β} _ ρ hρinf hρ p hjnt h₀ h₁ => by
      have hAc : D.t ρ ≤ Model.card A := (hν.t_lt hρinf hρ).le.trans hcA.ge
      -- both lists are images of the parameter list of `A`
      exact D.trans hjnt hB hA hN h₀ hAc h₁ _ _ _
        (D.symm hjnt hA hB hAc h₀ _ _
          (D.of_strong hjnt hA hB hAc h₀
            (Sum.elim (fun a : PEmpty.{u + 1} => a.elim) p)
            (Sum.elim d (fun b => f (p b))) f hρinf hf (by
              rintro (a | b)
              · exact a.elim
              · rfl)))
        (D.of_strong hjnt hA hN hAc h₁
          (Sum.elim (fun a : PEmpty.{u + 1} => a.elim) p)
          (Sum.elim z (fun b => i (p b))) i hρinf hi (by
            rintro (a | b)
            · exact a.elim
            · rfl)))
  exact ⟨F, hF, hFA⟩

/-- **Corollary 6.7, actual `ν`-types.** A tuple `x` of the `μ`-model `N` of length less than
`ν` lies in a strong `ν`-submodel `B'` of `N` containing `A`; coherence makes `B'` a strong
extension of `A`, and the diagrams of the tuple with the parameters of `A` are the same in
`N` and in `B'`. -/
theorem exists_actual_nu_type
    {ν μ : Cardinal.{u}} (hν : ClosedLevel K E D g ν) (_hμ : ClosedLevel K E D g μ)
    (hlt : ν < μ) (A N : Model K.τ)
    (i : Language.Embedding K.τ A.carrier N.carrier)
    (_hA : K.Mem A) (hN : K.Mem N) (hi : K.Strong i)
    (hcA : Model.card A = ν) (hcN : Model.card N = μ)
    {α : Type u} (x : α → N.carrier) (hα : #α < ν) :
    ∃ (B' : Model K.τ) (hB' : K.Mem B')
      (j : Language.Embedding K.τ A.carrier B'.carrier)
      (y : α → B'.carrier),
      K.Strong j ∧ Model.card B' = ν ∧
      (∀ {β : Type u} (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ) (_ : ρ < ν)
        (p : β → A.carrier) (hjoint : #(α ⊕ β) ≤ ρ)
        (h₀ : D.t ρ ≤ Model.card N) (h₁ : D.t ρ ≤ Model.card B'),
        D.same hjoint hN hB' h₀ h₁
          (Sum.elim x (fun b => i (p b)))
          (Sum.elim y (fun b => j (p b)))) := by
  classical
  have hνinf := hν.inf
  have hT : #↥(Set.range i ∪ Set.range x) ≤ ν := by
    refine (mk_union_le _ _).trans ?_
    have h := add_le_add ((mk_range_le (f := i)).trans hcA.le)
      ((mk_range_le (f := x)).trans hα.le)
    rwa [add_eq_self hνinf] at h
  obtain ⟨B', j', hB', hj', hcB', hcov⟩ :=
    exists_strong_hull_exact_card K ν hν.ls_lt.le hνinf N hN (hlt.le.trans_eq hcN.symm) _ hT
  have himgA : ∀ a, ∃ t, j' t = i a := fun a => hcov _ (Or.inl ⟨a, rfl⟩)
  have himgX : ∀ a, ∃ t, j' t = x a := fun a => hcov _ (Or.inr ⟨a, rfl⟩)
  let j : Language.Embedding K.τ A.carrier B'.carrier := factorEmbedding i j' himgA
  have hj : K.Strong j := strong_factorEmbedding i j' hi hj' himgA
  choose y hy using himgX
  refine ⟨B', hB', j, y, hj, hcB', fun {β} ρ hρinf hρ p hjnt h₀ h₁ => ?_⟩
  exact D.symm hjnt hB' hN h₁ h₀ _ _
    (D.of_strong hjnt hB' hN h₁ h₀ (Sum.elim y (fun b => j (p b)))
      (Sum.elim x (fun b => i (p b))) j' hρinf hj' (by
        rintro (a | b)
        · exact hy a
        · exact factorEmbedding_apply i j' himgA (p b)))

end
end AEC
