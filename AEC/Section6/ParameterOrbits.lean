module

public import AEC.Section4.Results
public import AEC.Section5.WorkingScheme
public import AEC.Section5.SingleModelScheme
public import AEC.Section5.NamedWorkingScheme
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

/-!
# Parameter orbits for a scheme (Lemma 6.1)

Lemma 6.1 bounds by `χ` the number of `D`-diagrams of `σ`-tuples over a parameter list of
length at most `χ`, at the levels above `χ` and above the threshold of Lemma 4.5.

The count comes from Lemma 4.5, which produces automorphisms of the vertex models. A working
scheme compares bounded lists by its own structural isomorphisms (`WorkingScheme.diagram_iso`),
and nothing in `IsWorkingPackage` or `HasPresentations` makes an automorphism of a vertex model a
structural isomorphism: a scheme may carry marks that its isomorphisms respect (colours, names),
and then it has more diagrams than the vertex models have orbits. The link is the hypothesis
`AssemblesStructIso W b`: outside a set of at most `b` occurrences, commuting strong vertex
automorphisms assemble into structural isomorphisms. `b` is the bound of the English statement
(`χ > b + σ`): `0` for single-model schemes (`SingleModelData.assemblesStructIso`), the number of
names for named schemes (`WorkingScheme.assemblesStructIso_named`).

* `AssemblesStructIso`: the link between vertex automorphisms and structural isomorphisms.
* `assemblesStructIso_bijective`: it holds, with no exceptional occurrence, when every
  vertexwise bijective arrow is a structural isomorphism.
* `exists_vertexwise_orbit_reps`: Lemma 4.5 for a finite family of models. Tuples of occurrences
  of a system, over at most `χ` parameters, fall into at most `χ` orbits of the families of
  strong vertex automorphisms. The specified maps of the system play no role here.
* `WorkingScheme.exists_parameter_orbit_reps`: Lemma 6.1 with an explicit threshold, for shapes
  with no specified map.

Shapes with specified maps are not covered: a family of vertex automorphisms obtained from
Lemma 4.5 need not commute with the maps of the system, and `AssemblesStructIso` assembles
commuting families only.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}

/-- Structural isomorphisms include vertexwise language automorphisms that fix a bounded
set `B` of occurrences (empty for unmarked single-model schemes; the names for named schemes).

At every object there is a set `B` of at most `b` occurrences such that every family of strong
automorphisms of the vertex models that fixes `B` pointwise and commutes with the specified
maps is the family of vertex maps of a structural isomorphism of the object.

This is the hypothesis of Lemma 6.1 that turns the automorphism orbits of Lemma 4.5 into
`D`-diagrams. It does not follow from `IsWorkingPackage` and `HasPresentations`. -/
def AssemblesStructIso (W : WorkingScheme K S) (b : Cardinal.{u}) : Prop :=
  ∀ μ (hμ : μ ∈ W.eligible) (X : W.Object μ hμ),
    ∃ B : Set (Occurrence K S (W.asSystem hμ X)), #B ≤ b ∧
      ∀ (e : ∀ v, ((W.asSystem hμ X).obj v).carrier ≃[K.τ]
          ((W.asSystem hμ X).obj v).carrier),
        (∀ v, K.Strong (e v).toEmbedding) →
        (∀ o ∈ B, e o.1 o.2 = o.2) →
        (∀ {i j} (h : S.specified i j) (x),
          (e j) ((W.asSystem hμ X).edge h x) =
            (W.asSystem hμ X).edge h (e i x)) →
        ∃ f : SystemArrow K S (W.asSystem hμ X) (W.asSystem hμ X),
          W.IsStructIso (X := X) (Y := X) f ∧
          ∀ v x, f.onVertex v x = e v x

/-- The bound `b` of `AssemblesStructIso` may be enlarged. -/
theorem AssemblesStructIso.mono {W : WorkingScheme K S} {b b' : Cardinal.{u}}
    (h : AssemblesStructIso W b) (hb : b ≤ b') : AssemblesStructIso W b' := by
  intro μ hμ X
  obtain ⟨B, hB, hBiso⟩ := h μ hμ X
  exact ⟨B, hB.trans hb, hBiso⟩

/-- If every vertexwise bijective arrow of an object to itself is a structural isomorphism
(`IsStructIso := bijectiveStructIso`), then commuting strong vertex automorphisms assemble into
structural isomorphisms with no exceptional occurrence (`B = ∅`), for every bound `b`. -/
theorem assemblesStructIso_bijective (W : WorkingScheme K S)
    (hbij : ∀ {μ} {hμ : μ ∈ W.eligible} (X : W.Object μ hμ)
      (f : SystemArrow K S (W.asSystem hμ X) (W.asSystem hμ X)),
      (∀ v, Function.Bijective (f.onVertex v)) → W.IsStructIso (X := X) (Y := X) f)
    (b : Cardinal.{u}) : AssemblesStructIso W b := by
  intro μ hμ X
  refine ⟨∅, by simp, fun e hes _ hcomm => ?_⟩
  refine ⟨⟨fun v => (e v).toEmbedding, hes, fun {i j} h => ?_⟩,
    hbij X _ (fun v => (e v).bijective), fun v x => rfl⟩
  ext x
  exact hcomm h x

/-- The single-model scheme of Proposition 5.6 assembles structural isomorphisms from vertex
automorphisms, with no exceptional occurrence. -/
theorem SingleModelData.assemblesStructIso (P : SingleModelData K) (b : Cardinal.{u}) :
    AssemblesStructIso P.scheme b :=
  assemblesStructIso_bijective P.scheme (fun _ _ h => h) b

/-- The named scheme of Proposition 5.7 assembles structural isomorphisms from vertex
automorphisms that also fix the names: the bound grows by the number of names. -/
theorem WorkingScheme.assemblesStructIso_named (W : WorkingScheme K S) {μ0 : Cardinal.{u}}
    {hμ0 : μ0 ∈ W.eligible} (X0 : W.Object μ0 hμ0) {ι : Type u}
    (c : ι → Occurrence K S (W.asSystem hμ0 X0))
    (T : Set Cardinal.{u}) (hT : EligibleSubclass W.eligible T)
    (hι : #ι < μ0) (hTail : ∀ μ ∈ T, μ0 ≤ μ) (hinf : ∀ μ ∈ T, aleph0 ≤ μ)
    {b : Cardinal.{u}} (hiso : AssemblesStructIso W b) :
    AssemblesStructIso (W.namedWorkingScheme X0 c T hT hι hTail hinf) (b + #ι) := by
  intro μ hμ X
  obtain ⟨B, hB, hBiso⟩ := hiso μ (EligibleSubclass.mem_source hT hμ) X.base
  refine ⟨B ∪ Set.range X.names,
    (mk_union_le _ _).trans (add_le_add hB mk_range_le), fun e hes hfix hcomm => ?_⟩
  obtain ⟨f, hf, hfe⟩ := hBiso e hes (fun o ho => hfix o (Or.inl ho)) hcomm
  refine ⟨f, ⟨hf, fun i => ?_⟩, hfe⟩
  have h := hfix (X.names i) (Or.inr ⟨i, rfl⟩)
  exact Sigma.ext rfl (heq_of_eq ((hfe _ _).trans h).symm)

/-- **Lemma 4.5 for a finite family of models.** Let `σ` be infinite, `χ ^ σ = χ` and
`χ ≥ ℓ + 2^(2^σ)`. At every sufficiently large categoricity cardinal `μ`, for a system `X`
whose vertices have cardinality `μ` and a set `P` of at most `χ` occurrences of `X`, the
`σ`-tuples of occurrences of `X` fall into at most `χ` orbits of the families of strong
automorphisms of the vertex models that fix `P` pointwise.

The automorphisms of different vertices are independent, so the orbit of a tuple is determined
by the vertices of its entries and, at each vertex, by the orbit over `P` of the entries at
that vertex (Lemma 4.5 in that vertex model). The specified maps of `X` are not used, and the
families produced need not commute with them. -/
theorem exists_vertexwise_orbit_reps (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (S : SystemShape.{u}) (σ χ : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hpow : χ ^ σ = χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) :
    ∃ κ0 : Cardinal.{u}, ∀ μ, κ0 ≤ μ → Categorical K μ →
      ∀ X : SystemObject K S, (∀ v, Model.card (X.obj v) = μ) →
        ∀ P : Set (Occurrence K S X), #P ≤ χ →
          ∀ {ι : Type u}, #ι ≤ σ →
            ∃ reps : Set (ι → Occurrence K S X), #reps ≤ χ ∧
              ∀ xs : ι → Occurrence K S X, ∃ ys ∈ reps,
                ∃ e : ∀ v, (X.obj v).carrier ≃[K.τ] (X.obj v).carrier,
                  (∀ v, K.Strong (e v).toEmbedding) ∧ (∀ o ∈ P, e o.1 o.2 = o.2) ∧
                    ∀ i, ys i = ⟨(xs i).1, e (xs i).1 (xs i).2⟩ := by
  classical
  obtain ⟨κ0, h45⟩ := lemma_4_5 K σ χ hσ hpow hχ
  refine ⟨max κ0 1, fun μ hμ hcat X hcard P hP ι hι => ?_⟩
  have hκ0 : κ0 ≤ μ := (le_max_left _ _).trans hμ
  have hμ1 : (1 : Cardinal.{u}) ≤ μ := (le_max_right _ _).trans hμ
  have : Finite S.Vertex := S.vertexFinite
  have hχinf : aleph0 ≤ χ := (isLSBound_ls K).1.trans (le_self_add.trans hχ)
  have hσχ : σ ≤ χ := sigma_le_chi_of_lemma45 hσ (le_add_self.trans hχ)
  have hχ0 : χ ≠ 0 := (aleph0_pos.trans_le hχinf).ne'
  -- Each vertex model is nonempty, so a tuple of occurrences has a tuple of entries at each
  -- vertex: the entries at that vertex, and a fixed element elsewhere.
  have hne : ∀ v, Nonempty (X.obj v).carrier := fun v => by
    rw [← Cardinal.mk_ne_zero_iff]
    have h := hcard v
    unfold Model.card at h
    rw [h]
    exact (zero_lt_one.trans_le hμ1).ne'
  obtain ⟨loc, hloc⟩ : ∃ loc : (ι → Occurrence K S X) → ∀ v, ι → (X.obj v).carrier,
      ∀ xs i, loc xs (xs i).1 i = (xs i).2 :=
    ⟨fun xs v i => if h : (xs i).1 = v then h ▸ (xs i).2 else Classical.choice (hne v),
      fun xs i => by simp⟩
  -- Lemma 4.5 at each vertex, over the parameters at that vertex.
  let Pv : ∀ v, Set (X.obj v).carrier := fun v => {x | (⟨v, x⟩ : Occurrence K S X) ∈ P}
  have hPv : ∀ v, #(Pv v) ≤ χ := fun v =>
    (mk_preimage_of_injective (fun x : (X.obj v).carrier => (⟨v, x⟩ : Occurrence K S X)) P
      (fun _ _ hab => eq_of_heq (Sigma.mk.inj hab).2)).trans hP
  choose repsV hrepsV hR using fun v =>
    h45 μ hκ0 hcat (X.obj v) (X.inK v) (hcard v) (Pv v) (hPv v) (ι := ι) hι
  choose R hRmem e hes hefix hemap using hR
  -- The occurrences that are entries of the representatives.
  let C : Set (Occurrence K S X) :=
    Set.range fun q : (Σ v, repsV v × ι) => (⟨q.1, q.2.1.1 q.2.2⟩ : Occurrence K S X)
  have hC : #C ≤ χ := by
    refine mk_range_le.trans ?_
    rw [mk_sigma]
    calc Cardinal.sum (fun v => #(repsV v × ι))
        ≤ Cardinal.sum (fun _ : S.Vertex => χ) := by
          refine Cardinal.sum_le_sum _ _ fun v => ?_
          rw [mk_prod, lift_id, lift_id]
          exact mul_le_of_le hχinf (hrepsV v) (hι.trans hσχ)
      _ = #S.Vertex * χ := by simp
      _ ≤ χ := mul_le_of_le hχinf ((lt_aleph0_of_finite S.Vertex).le.trans hχinf) le_rfl
  refine ⟨{ys | ∀ i, ys i ∈ C}, ?_, fun xs => ?_⟩
  · have hinj : #{ys : ι → Occurrence K S X | ∀ i, ys i ∈ C} ≤ #(ι → C) := by
      refine mk_le_of_injective (f := fun ys i => ⟨ys.1 i, ys.2 i⟩) ?_
      intro a b hab
      apply Subtype.ext
      funext i
      exact congrArg Subtype.val (congrFun hab i)
    refine hinj.trans ?_
    rw [mk_arrow, lift_id, lift_id]
    calc #C ^ #ι ≤ χ ^ #ι := power_le_power_right hC
      _ ≤ χ ^ σ := power_le_power_left hχ0 hι
      _ = χ := hpow
  · refine ⟨fun i => ⟨(xs i).1, R (xs i).1 (loc xs (xs i).1) i⟩, fun i => ?_,
      fun v => e v (loc xs v), fun v => hes v _, fun o ho => hefix o.1 _ o.2 ho, fun i => ?_⟩
    · exact ⟨⟨(xs i).1, ⟨R (xs i).1 (loc xs (xs i).1), hRmem _ _⟩, i⟩, rfl⟩
    · exact congrArg (Sigma.mk (xs i).1)
        ((hemap (xs i).1 (loc xs (xs i).1) i).symm.trans
          (congrArg (e (xs i).1 (loc xs (xs i).1)) (hloc xs i)))

/-- **Lemma 6.1 with an explicit threshold.** Let `W` be a working scheme of a shape with no
specified map, categorical at its levels, in which vertex automorphisms fixing at most `b`
occurrences assemble into structural isomorphisms. Let `σ` be infinite, `χ ^ σ = χ`,
`χ > b + σ` and `χ ≥ ℓ + 2^(2^σ)`. Above a threshold `κ0` and above `χ`, at every object the
`σ`-tuples have at most `χ` diagrams over a fixed parameter list of length at most `χ`.

Proof: `exists_vertexwise_orbit_reps` over the parameters and the exceptional occurrences gives
at most `χ` representatives and, for every tuple, a family of strong vertex automorphisms that
fixes the parameters and moves the tuple to a representative. The family commutes with the
specified maps because there are none, so it is a structural isomorphism, and
`W.diagram_iso` applies to the list of length `#ι + #ρ ≤ χ < μ`. -/
theorem WorkingScheme.exists_parameter_orbit_reps [CategoricalUnbounded K]
    (W : WorkingScheme K S) (hedge : ∀ i j, ¬ S.specified i j)
    (hcat : ∀ μ ∈ W.eligible, Categorical K μ)
    (σ χ b : Cardinal.{u})
    (hσ : aleph0 ≤ σ) (hpow : χ ^ σ = χ)
    (hb : b + σ < χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ)
    (hiso : AssemblesStructIso W b) :
    ∃ κ0 : Cardinal.{u}, ∀ μ (hμ : μ ∈ W.eligible), κ0 ≤ μ → χ < μ →
      ∀ (X : W.Object μ hμ) {ι ρ : Type u}, #ι ≤ σ → #ρ ≤ χ →
        ∀ params : ρ → Occurrence K S (W.asSystem hμ X),
          ∃ reps : Set (ι → Occurrence K S (W.asSystem hμ X)), #reps ≤ χ ∧
            ∀ xs : ι → Occurrence K S (W.asSystem hμ X), ∃ ys ∈ reps,
              W.DiagramEq (X := X) (Y := X) (Sum.elim xs params) (Sum.elim ys params) := by
  obtain ⟨κ0, h⟩ := exists_vertexwise_orbit_reps K S σ χ hσ hpow hχ
  have hχinf : aleph0 ≤ χ := (isLSBound_ls K).1.trans (le_self_add.trans hχ)
  have hσχ : σ ≤ χ := le_add_self.trans hb.le
  have hbχ : b ≤ χ := le_self_add.trans hb.le
  refine ⟨κ0, fun μ hμ hκ hχμ X ι ρ hι hρ params => ?_⟩
  obtain ⟨B, hB, hBiso⟩ := hiso μ hμ X
  have hP : #(Set.range params ∪ B : Set (Occurrence K S (W.asSystem hμ X))) ≤ χ :=
    (mk_union_le _ _).trans (add_le_of_le hχinf (mk_range_le.trans hρ) (hB.trans hbχ))
  obtain ⟨reps, hreps, hrep⟩ :=
    h μ hκ (hcat μ hμ) (W.asSystem hμ X) (W.vertex_card hμ X) _ hP (ι := ι) hι
  have hlt : #(ι ⊕ ρ) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact (add_le_of_le hχinf (hι.trans hσχ) hρ).trans_lt hχμ
  refine ⟨reps, hreps, fun xs => ?_⟩
  obtain ⟨ys, hys, e, hes, hefix, hmap⟩ := hrep xs
  obtain ⟨f, hf, hfe⟩ := hBiso e hes (fun o ho => hefix o (Or.inr ho))
    (fun {i j} h => (hedge i j h).elim)
  refine ⟨ys, hys, (W.diagram_iso X X _ _ hlt).mpr ⟨f, hf, ?_⟩⟩
  rintro (i | k)
  · simp only [Sum.elim_inl]
    exact (hmap i).trans (Sigma.ext rfl (heq_of_eq (hfe _ _).symm))
  · simp only [Sum.elim_inr]
    have hk := hefix (params k) (Or.inl ⟨k, rfl⟩)
    exact Sigma.ext rfl (heq_of_eq ((hfe _ _).trans hk).symm)

/-- Lemma 6.1 for the single-model scheme of Proposition 5.6: the hypotheses on the scheme
(one vertex with no specified map, categoricity at the levels, `AssemblesStructIso` with
`b = 0`) hold, and `χ > σ` follows from `χ ≥ ℓ + 2^(2^σ)`. -/
theorem SingleModelData.exists_parameter_orbit_reps (P : SingleModelData K)
    (σ χ : Cardinal.{u}) (hσ : aleph0 ≤ σ) (hpow : χ ^ σ = χ)
    (hχ : ls K + (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ σ) ≤ χ) :
    ∃ κ0 : Cardinal.{u}, ∀ μ (hμ : μ ∈ P.scheme.eligible), κ0 ≤ μ → χ < μ →
      ∀ (X : P.scheme.Object μ hμ) {ι ρ : Type u}, #ι ≤ σ → #ρ ≤ χ →
        ∀ params : ρ → Occurrence K oneVertexShape (P.scheme.asSystem hμ X),
          ∃ reps : Set (ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ X)),
            #reps ≤ χ ∧
            ∀ xs : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ X), ∃ ys ∈ reps,
              P.scheme.DiagramEq (X := X) (Y := X) (Sum.elim xs params)
                (Sum.elim ys params) := by
  have := P.D.categoricalUnbounded
  have hlt : (0 : Cardinal.{u}) + σ < χ := by
    rw [zero_add]
    exact ((cantor σ).trans (cantor _)).trans_le (le_add_self.trans hχ)
  exact P.scheme.exists_parameter_orbit_reps (fun _ _ h => h)
    (fun μ hμ => SingleModelData.categorical hμ) σ χ 0 hσ hpow hlt hχ
    (P.assemblesStructIso 0)

end
end AEC
