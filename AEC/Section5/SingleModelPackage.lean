module

public import AEC.Section5.SingleModelScheme

@[expose] public section

/-!
# The single-model working package (Proposition 5.6, package clauses)

The package clauses of Definition 5.2 for `SingleModelData.scheme`.

* `nonempty_object`: every level carries an object, a copy of the presentation `E(μ)`.
* `hasPresentations`: by categoricity every object at `μ` is isomorphic to `E(I)` for every
  order `I` of cardinality `μ`, and `E.map` between such charts is an arrow.
* `hasMixedDownward`: a strong submodel of exact cardinality `ν` containing the requested
  occurrences (Löwenheim–Skolem), coded on the carrier of the level `ν`.
* `isSaturated`: compare the actual list and the witness inside one presentation `E(ρ)`,
  `ρ` the larger of the two levels. By Proposition 4.3 an automorphism of `E(ρ)` moves the base
  of the witness onto the actual list. A strong submodel of cardinality `μ` of `E(ρ)` containing
  the actual object and the moved witness realizes the joint diagram over the actual list.
* `satisfiesExhaustion`: arrows have only componentwise strongness as content.
* `hasChainUnions`: see the remark at `hasChainUnions`; `exists_directed_union` is the union of
  a directed family of objects along its arrows, from the chain axioms of `K`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

namespace SingleModelData

variable {P : SingleModelData K} {μ ν ρ : Cardinal.{u}}

/-! ## Seeds and presentations -/

/-- Every level carries an object: the presentation `E(μ)`, coded on the carrier of `μ`. -/
theorem nonempty_object (hμ : μ ∈ P.eligible) : Nonempty (SMObject K μ) :=
  ⟨SMObject.ofModel (P.G μ) (P.mem_G μ) (card_G hμ)⟩

/-- Categoricity at a level: an object at `μ` is isomorphic to `E(I)` whenever `#I = μ`. -/
theorem exists_present_equiv (hμ : μ ∈ P.eligible) (X : SMObject K μ)
    (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I = μ) :
    Nonempty ((P.E.obj I).carrier ≃[K.τ] X.model.carrier) :=
  (categorical hμ).unique_model (P.E.obj I) X.model (P.hE I) X.mem (card_obj_eq hμ I hI) X.card

/-- An order embedding of orders of the cardinalities of two levels induces a strong map
between any objects at those levels, through charts. -/
theorem exists_order_arrow (hμ : μ ∈ P.eligible) (hν : ν ∈ P.eligible)
    (I J : Type u) [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (X : SMObject K μ) (Y : SMObject K ν) (f : I ↪o J) (hI : #I = μ) (hJ : #J = ν) :
    ∃ F : Language.Embedding K.τ X.model.carrier Y.model.carrier, K.Strong F := by
  obtain ⟨eX⟩ := exists_present_equiv hμ X I hI
  obtain ⟨eY⟩ := exists_present_equiv hν Y J hJ
  exact ⟨eY.toEmbedding.comp ((P.E.map f).comp eX.symm.toEmbedding),
    K.strong_trans _ _
      (K.strong_trans _ _ (strong_of_equiv K eX.symm X.mem) (P.E.map_strong f))
      (strong_of_equiv K eY (P.hE J))⟩

variable (P) in
theorem hasPresentations : HasPresentations P.scheme P.scheme.template where
  present_equiv := fun {μ} hμ X I _ _ hI _ => exists_present_equiv hμ X I hI
  wellOrder_arrow := fun {μ ν} hμ hν I J _ _ _ _ _ _ X Y f hI hJ => by
    obtain ⟨F, hF⟩ := exists_order_arrow hμ hν I J X Y f hI hJ
    exact ⟨oneVertexArrow F hF, trivial⟩

/-! ## Mixed downward closure -/

/-- At most `ν` elements of an object at `μ ≥ ν` lie in the image of a strong map from an
object at `ν` (Löwenheim–Skolem at the exact cardinality `ν`). -/
theorem exists_downward (hμ : μ ∈ P.eligible) (hν : ν ∈ P.eligible) (X : SMObject K μ)
    {ι : Type u} (occ : ι → X.model.carrier) (hνμ : ν ≤ μ) (hι : #ι ≤ ν) :
    ∃ (Y : SMObject K ν) (f : Language.Embedding K.τ Y.model.carrier X.model.carrier),
      K.Strong f ∧ ∀ i, ∃ y, f y = occ i := by
  obtain ⟨N, f, hN, hf, hcN, hcov⟩ :=
    exists_strong_hull_exact_card K ν (ls_lt hν).le (aleph0_le hν) X.model X.mem
      (by rw [X.card]; exact hνμ) (Set.range occ) (mk_range_le.trans hι)
  let e := SMObject.ofModelEquiv N hN hcN
  refine ⟨SMObject.ofModel N hN hcN, f.comp e.symm.toEmbedding,
    K.strong_trans _ _ (strong_of_equiv K e.symm (SMObject.ofModel N hN hcN).mem) hf,
    fun i => ?_⟩
  obtain ⟨n, hn⟩ := hcov _ ⟨i, rfl⟩
  refine ⟨e n, ?_⟩
  change f (e.symm (e n)) = occ i
  rw [e.symm_apply_apply, hn]

variable (P) in
theorem hasMixedDownward : HasMixedDownward P.scheme where
  downward := fun {μ ν} hμ hν X ι occ hνμ hι => by
    obtain ⟨Y, f, hf, hcov⟩ :=
      exists_downward hμ hν X (fun i => SMObject.val X (occ i)) hνμ hι
    refine ⟨Y, oneVertexArrow f hf, trivial, fun i => ?_⟩
    obtain ⟨y, hy⟩ := hcov i
    exact ⟨Y.occ y, (congrArg (SMObject.occ X) hy).symm⟩

/-! ## Saturation -/

/-- **Saturation.** Let `xs` be a bounded list of an object `X` at `μ`, and let `ext` be a list
of an object `Y` at any level, of length bounded at `μ`, whose initial part `base` has the
diagram of `xs`. Then some object `Z` at `μ` with a strong map `f : X → Z` carries a list `zs`
extending `f ∘ xs` with the diagram of `ext`.

Both lists are compared in `E(ρ)`, `ρ = max μ ν`. Proposition 4.3 gives an automorphism of
`E(ρ)` taking the image of `base` to the image of `xs`; it moves the image of `ext` to a list
`w` extending the image of `xs`. A strong submodel of `E(ρ)` of cardinality `μ` containing the
image of `X` and `w` is the object `Z`. -/
theorem exists_saturation (hμ : μ ∈ P.eligible) (hν : ν ∈ P.eligible) {α β : Type u}
    (X : SMObject K μ) (Y : SMObject K ν)
    (xs : α → X.model.carrier) (base : α → Y.model.carrier) (ext : α ⊕ β → Y.model.carrier)
    (hα : #α < μ) (hβ : #β < μ) (hext : ∀ i, ext (Sum.inl i) = base i)
    (h : DiagramEq hμ hν X Y xs base) :
    ∃ (Z : SMObject K μ) (f : Language.Embedding K.τ X.model.carrier Z.model.carrier)
      (zs : α ⊕ β → Z.model.carrier),
      K.Strong f ∧ (∀ i, zs (Sum.inl i) = f (xs i)) ∧ DiagramEq hμ hν Z Y zs ext := by
  classical
  have hρ : max μ ν ∈ P.eligible := max_mem hμ hν
  have hμρ : μ ≤ max μ ν := le_max_left _ _
  have hνρ : ν ≤ max μ ν := le_max_right _ _
  have hinf : ℵ₀ ≤ μ := aleph0_le hμ
  have hαβ : #(α ⊕ β) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt hinf hα hβ
  -- an automorphism of `E(ρ)` taking the image of `base` to the image of `xs`
  obtain ⟨e, he⟩ := sameD_equiv hρ (card_G hρ) (card_G hρ)
    (h (max μ ν) hρ hμρ hνρ (hα.trans_le hμρ)) (hα.trans_le hμρ)
  let w : α ⊕ β → (P.G (max μ ν)).carrier := fun i => e.symm (push hν hνρ Y (ext i))
  have hw : ∀ i, w (Sum.inl i) = push hμ hμρ X (xs i) := by
    intro i
    change e.symm (push hν hνρ Y (ext (Sum.inl i))) = push hμ hμρ X (xs i)
    rw [hext, ← he i, e.symm_apply_apply]
  -- a strong submodel of `E(ρ)` of cardinality `μ` containing the image of `X` and `w`
  have hA : #(↥(Set.range (push hμ hμρ X) ∪ Set.range w)) ≤ μ := by
    refine (mk_union_le _ _).trans ?_
    have h1 : #(Set.range (push hμ hμρ X)) ≤ μ := mk_range_le.trans X.card.le
    have h2 : #(Set.range w) ≤ μ := mk_range_le.trans hαβ.le
    exact (add_le_add h1 h2).trans (Cardinal.add_eq_self hinf).le
  obtain ⟨N, j, hN, hj, hcN, hcov⟩ :=
    exists_strong_hull_exact_card K μ (ls_lt hμ).le hinf (P.G (max μ ν)) (P.mem_G _)
      (by rw [card_G hρ]; exact hμρ) _ hA
  let φ := SMObject.ofModelEquiv N hN hcN
  let Z : SMObject K μ := SMObject.ofModel N hN hcN
  let jZ : Language.Embedding K.τ Z.model.carrier (P.G (max μ ν)).carrier :=
    j.comp φ.symm.toEmbedding
  have hjZ : K.Strong jZ := K.strong_trans _ _ (strong_of_equiv K φ.symm Z.mem) hj
  have hcovZ : ∀ a ∈ Set.range (push hμ hμρ X) ∪ Set.range w, ∃ z, jZ z = a := by
    intro a ha
    obtain ⟨n, hn⟩ := hcov a ha
    refine ⟨φ n, ?_⟩
    change j (φ.symm (φ n)) = a
    rw [φ.symm_apply_apply, hn]
  have himg : ∀ x, ∃ z, jZ z = push hμ hμρ X x := fun x => hcovZ _ (Or.inl ⟨x, rfl⟩)
  have hfz : ∀ x, jZ (factorEmbedding (push hμ hμρ X) jZ himg x) = push hμ hμρ X x :=
    factorEmbedding_apply _ _ himg
  choose zs hzs using fun i => hcovZ (w i) (Or.inr ⟨i, rfl⟩)
  refine ⟨Z, factorEmbedding (push hμ hμρ X) jZ himg, zs,
    strong_factorEmbedding _ _ (push_strong hμ hμρ X) hjZ himg, fun i => ?_, ?_⟩
  · apply jZ.injective
    rw [hzs, hfz, hw]
  · refine DiagramEq.of_level hμ hν Z Y hρ hμρ hνρ (hαβ.trans_le hμρ) ?_
    have h1 := (sameD_push hμ hρ hμρ Z zs hαβ).symm
    have h2 : P.D.SameD Z.model (P.G (max μ ν)) zs w :=
      sameD_of_strong hμ hρ Z.card (card_G hρ) jZ hjZ zs w hzs hαβ (hαβ.trans_le hμρ)
    have h3 : P.D.SameD (P.G (max μ ν)) (P.G (max μ ν)) w
        (fun i => push hν hνρ Y (ext i)) :=
      sameD_of_strong hρ hρ (card_G hρ) (card_G hρ) e.toEmbedding
        (strong_of_equiv K e (P.mem_G _)) w _ (fun i => e.apply_symm_apply _)
        (hαβ.trans_le hμρ) (hαβ.trans_le hμρ)
    exact h1.trans (h2.trans h3)

variable (P) in
theorem isSaturated : IsSaturated P.scheme where
  saturated := fun {μ ν} {hμ} {hν} {α β} X Y xs base ext hα hβ hext hEq => by
    obtain ⟨Z, f, zs, hf, hzs, hD⟩ :=
      exists_saturation hμ hν X Y (fun i => SMObject.val X (xs i))
        (fun i => SMObject.val Y (base i)) (fun i => SMObject.val Y (ext i)) hα hβ
        (fun i => congrArg (SMObject.val Y) (hext i)) hEq
    exact ⟨Z, oneVertexArrow f hf, fun i => Z.occ (zs i), trivial,
      fun i => congrArg Z.occ (hzs i), hD⟩

/-! ## Exhaustion -/

variable (P) in
/-- Arrows of the single-model scheme have only componentwise strongness as content, which a
`SystemArrow` carries. -/
theorem satisfiesExhaustion : SatisfiesExhaustion P.scheme where
  exhaustion := fun _ _ _ _ => trivial

/-! ## Chain unions -/

variable (P) in
/-- The chain-union clause of `HasChainUnions`. The clause is stated for a family with an
arrow `le i j` for *every* ordered pair of indices, composing strictly; such a family consists
of mutually inverse isomorphisms, and any member is its union: the inclusions are the given
arrows into it, and a cocone `toZ` factors through its own component. The union of a family
with arrows only along a directed preorder is `exists_directed_union` below. -/
theorem hasChainUnions : HasChainUnions P.scheme where
  union := fun {μ} hμ index hne obj le _ hcomp _ => by
    obtain ⟨i₀⟩ := hne
    refine ⟨obj i₀, fun i => le i i₀, fun _ => trivial, fun i j => hcomp i j i₀, ?_⟩
    intro ν hν Z toZ _ hcocone _
    exact ⟨toZ i₀, trivial, fun i => hcocone i i₀⟩

/-- **Directed unions of objects** (Definition 5.2(1) for single models). A directed system of
`K`-models of cardinality `μ` with strong transition maps, indexed by at most `μ` indices, has
a union which is an object at `μ`: the inclusions are strong, cohere with the transition maps
and jointly cover the union, and a coherent family of strong maps into a model `N` of `K`
induces a strong map from the union. This is Lemma 2.1 (`directLimit_in_class`, from the chain
and common-upper-bound axioms of `K`) with the cardinality count `‖⋃‖ ≤ #ι · μ = μ`.

Unlike the clause `HasChainUnions.union`, the system has transition maps only along its
directed preorder, so that its members need not be isomorphic. -/
theorem exists_directed_union (hμ : μ ∈ P.eligible) (S : DirectedSystem K.τ)
    (hmem : ∀ i, K.Mem (S.obj i)) (hcard : ∀ i, Model.card (S.obj i) = μ)
    (hstrong : ∀ {i j} (hij : S.rel i j), K.Strong (S.map hij)) (hidx : #S.ι ≤ μ) :
    ∃ (U : SMObject K μ)
      (incl : ∀ i, Language.Embedding K.τ (S.obj i).carrier U.model.carrier),
      (∀ i, K.Strong (incl i)) ∧
      (∀ {i j} (hij : S.rel i j), (incl j).comp (S.map hij) = incl i) ∧
      (∀ x, ∃ i y, incl i y = x) ∧
      ∀ (N : Model K.τ) (g : ∀ i, Language.Embedding K.τ (S.obj i).carrier N.carrier),
        K.Mem N → (∀ i, K.Strong (g i)) →
        (∀ {i j} (hij : S.rel i j), (g j).comp (S.map hij) = g i) →
        ∃ f : Language.Embedding K.τ U.model.carrier N.carrier,
          K.Strong f ∧ ∀ i, f.comp (incl i) = g i := by
  have hinf : ℵ₀ ≤ μ := aleph0_le hμ
  obtain ⟨L, hL, hcanon, huniv⟩ := directLimit_in_class K S hmem hstrong
  obtain ⟨i₀⟩ := S.nonempty
  have hge : μ ≤ Model.card L.obj :=
    (hcard i₀).symm.le.trans (Cardinal.mk_le_of_injective (L.canon i₀).injective)
  have hle : Model.card L.obj ≤ μ := by
    have hsurj : Function.Surjective
        (fun p : Σ i, (S.obj i).carrier => L.canon p.1 p.2) := by
      intro x
      obtain ⟨i, y, h⟩ := L.joint x
      exact ⟨⟨i, y⟩, h⟩
    calc Model.card L.obj ≤ #(Σ i, (S.obj i).carrier) := Cardinal.mk_le_of_surjective hsurj
      _ = Cardinal.sum (fun i => #(S.obj i).carrier) := Cardinal.mk_sigma _
      _ = Cardinal.sum (fun _ : S.ι => μ) := by
        congr 1
        funext i
        exact hcard i
      _ = #S.ι * μ := Cardinal.sum_const' _ _
      _ ≤ μ * μ := mul_le_mul' hidx le_rfl
      _ = μ := Cardinal.mul_eq_self hinf
  have hcL : Model.card L.obj = μ := le_antisymm hle hge
  let φ := SMObject.ofModelEquiv L.obj hL hcL
  have hφ : K.Strong φ.toEmbedding := strong_of_equiv K φ hL
  have hφs : K.Strong φ.symm.toEmbedding :=
    strong_of_equiv K φ.symm (SMObject.ofModel L.obj hL hcL).mem
  refine ⟨SMObject.ofModel L.obj hL hcL, fun i => φ.toEmbedding.comp (L.canon i),
    fun i => K.strong_trans _ _ (hcanon i) hφ, ?_, ?_, ?_⟩
  · intro i j hij
    ext x
    have h := DFunLike.congr_fun (L.compat hij) x
    simp only [Language.Embedding.comp_apply] at h ⊢
    rw [h]
  · intro x
    obtain ⟨i, y, h⟩ := L.joint (φ.symm x)
    refine ⟨i, y, ?_⟩
    change φ (L.canon i y) = x
    rw [h, φ.apply_symm_apply]
  · intro N g hN hg hcomp
    obtain ⟨f, hf, hfg⟩ := huniv N g hN hg hcomp
    refine ⟨f.comp φ.symm.toEmbedding, K.strong_trans _ _ hφs hf, fun i => ?_⟩
    ext x
    have h := DFunLike.congr_fun (hfg i) x
    simp only [Language.Embedding.comp_apply] at h ⊢
    change f (φ.symm (φ (L.canon i x))) = g i x
    rw [φ.symm_apply_apply, h]

/-! ## The package -/

variable (P) in
/-- **Proposition 5.6.** The single-model scheme is a working package. -/
theorem isWorkingPackage : IsWorkingPackage P.scheme :=
  ⟨P.hasChainUnions, P.hasMixedDownward, P.isSaturated, P.satisfiesExhaustion⟩

end SingleModelData

end
end AEC
