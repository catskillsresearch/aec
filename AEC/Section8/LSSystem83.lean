module

public import AEC.Section2.FiniteHull
public import AEC.Section2.Results

/-!
# Lemma 8.3: a coherent finite-subset Löwenheim–Skolem system

Port of `AEC.Section2.FiniteHull` (the hull recursion on finite subsets of `Fin n`) to finite
subsets of an arbitrary index type: for `M ∈ K` and `base : α → M`, strong submodels `N_s`
for nonempty finite `s ⊆ α`, containing `base '' s`, of size at most `LS(K)`, with strong
factor maps `N_t → N_s` for `t ⊊ s`.  This is the directed system behind the LS witness
expansion (`infra_83_vertex_ls_expansion`).
-/

@[expose] public section

namespace AEC
namespace LS83

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

variable {M : Model K.τ} (hM : K.Mem M)

/-- The nonempty subsets of `s` of strictly smaller cardinality. -/
def properSubs {α : Type u} [DecidableEq α] (s : Finset α) : Finset (Finset α) :=
  s.powerset.filter fun t => t.Nonempty ∧ t.card < s.card

theorem mem_properSubs {α : Type u} [DecidableEq α] {s t : Finset α} :
    t ∈ properSubs s ↔ t ⊆ s ∧ t.Nonempty ∧ t.card < s.card := by
  simp [properSubs, Finset.mem_filter, Finset.mem_powerset]

variable {α : Type u} [DecidableEq α] (base : α → M.carrier)

/-- The displayed elements of `s`. -/
def displayed (s : {t : Finset α // t.Nonempty}) : Set M.carrier :=
  base '' (s.1 : Set α)

/-- The ranges of the hulls of the nonempty proper subsets of `s`. -/
def lowerRanges (s : {t : Finset α // t.Nonempty})
    (rec : ∀ t : {t : Finset α // t.Nonempty}, t.1.card < s.1.card →
      Σ A : Set M.carrier, ChosenHull K M A) : Set M.carrier :=
  Set.iUnion fun t : ULift.{u} ↥(properSubs s.1) =>
    let ht := mem_properSubs.mp t.down.2
    Set.range (rec ⟨t.down.1, ht.2.1⟩ ht.2.2).2.incl

/-- One step of the hull recursion: the displayed elements of `s`, together with the ranges
of the hulls of its nonempty proper subsets. -/
noncomputable def subHullStep (s : {t : Finset α // t.Nonempty})
    (rec : ∀ t : {t : Finset α // t.Nonempty}, t.1.card < s.1.card →
      Σ A : Set M.carrier, ChosenHull K M A) :
    Σ A : Set M.carrier, ChosenHull K M A :=
  ⟨displayed base s ∪ lowerRanges s rec, chosenHull hM (displayed base s ∪ lowerRanges s rec)⟩

omit [DecidableEq α] in
theorem cardRel_wf :
    WellFounded (fun a b : {t : Finset α // t.Nonempty} => a.1.card < b.1.card) :=
  InvImage.wf (fun s : {t : Finset α // t.Nonempty} => s.1.card) Nat.lt_wfRel.wf

/-- Hulls of the nonempty subsets of a finite set of displayed elements, built by recursion
on the size of the subset. -/
noncomputable def subHull :
    (s : {t : Finset α // t.Nonempty}) → Σ A : Set M.carrier, ChosenHull K M A :=
  WellFounded.fix cardRel_wf (subHullStep hM base)

theorem subHull_eq (s : {t : Finset α // t.Nonempty}) :
    subHull hM base s =
      subHullStep hM base s fun t _ => subHull hM base t :=
  WellFounded.fix_eq _ _ _

/-- The strong submodel assigned to a nonempty finite set of displayed elements. -/
noncomputable def subModel (s : {t : Finset α // t.Nonempty}) : Model K.τ :=
  (subHull hM base s).2.obj

noncomputable def subIncl (s : {t : Finset α // t.Nonempty}) :
    Language.Embedding K.τ (subModel hM base s).carrier M.carrier :=
  (subHull hM base s).2.incl

theorem subModel_mem (s : {t : Finset α // t.Nonempty}) :
    K.Mem (subModel hM base s) :=
  (subHull hM base s).2.mem

theorem subIncl_strong (s : {t : Finset α // t.Nonempty}) :
    K.Strong (subIncl hM base s) :=
  (subHull hM base s).2.strong

theorem subIncl_covers (s : {t : Finset α // t.Nonempty})
    {a : M.carrier} (ha : a ∈ (subHull hM base s).1) :
    ∃ x, subIncl hM base s x = a :=
  (subHull hM base s).2.covers a ha

/-- A smaller hull sits inside a larger one. The two inclusions into `M` determine the
factor, and coherence makes that factor strong. -/
noncomputable def subInclFactor
    (t s : {t : Finset α // t.Nonempty})
    (hsub : t.1 ⊆ s.1) (hlt : t.1.card < s.1.card) :
    Language.Embedding K.τ (subModel hM base t).carrier (subModel hM base s).carrier :=
  factorEmbedding (subIncl hM base t) (subIncl hM base s) fun x => by
    have htmem : t.1 ∈ properSubs s.1 := mem_properSubs.mpr ⟨hsub, t.2, hlt⟩
    have hrange : subIncl hM base t x ∈ (subHull hM base s).1 := by
      rw [subHull_eq hM base s]
      refine Or.inr ?_
      refine Set.mem_iUnion.mpr ?_
      refine ⟨ULift.up ⟨t.1, htmem⟩, ?_⟩
      exact ⟨x, rfl⟩
    exact subIncl_covers hM base s hrange

theorem subInclFactor_comp (t s : {t : Finset α // t.Nonempty})
    (hsub : t.1 ⊆ s.1) (hlt : t.1.card < s.1.card) :
    (subIncl hM base s).comp (subInclFactor hM base t s hsub hlt) = subIncl hM base t :=
  factorEmbedding_comp _ _ _

theorem subInclFactor_strong (t s : {t : Finset α // t.Nonempty})
    (hsub : t.1 ⊆ s.1) (hlt : t.1.card < s.1.card) :
    K.Strong (subInclFactor hM base t s hsub hlt) :=
  K.coherence (subInclFactor hM base t s hsub hlt) (subIncl hM base t) (subIncl hM base s)
    (subIncl_strong hM base t) (subIncl_strong hM base s)
    (subInclFactor_comp hM base t s hsub hlt)

/-- Finitely many smaller hulls, each of size at most `LS(K)`, still have size at most `LS(K)`. -/
theorem subModel_card (s : {t : Finset α // t.Nonempty}) :
    Model.card (subModel hM base s) ≤ ls K := by
  refine WellFounded.induction
    (C := fun s => Model.card (subModel hM base s) ≤ ls K) cardRel_wf s ?_
  intro s ih
  have hall : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hle : Model.card (subModel hM base s) ≤ mk (subHull hM base s).1 + ls K :=
    (subHull hM base s).2.card_le
  have hA : mk (subHull hM base s).1 ≤ ls K := by
    rw [subHull_eq hM base s]
    have hset :
        (subHullStep hM base s (fun t _ => subHull hM base t)).1 =
          displayed base s ∪ lowerRanges s (fun t _ => subHull hM base t) := rfl
    rw [hset]
    refine (mk_union_le _ _).trans ?_
    have himg : mk (displayed base s) ≤ ls K := by
      have hfin : (displayed base s).Finite := (s.1.finite_toSet).image base
      exact (mk_le_aleph0_iff.mpr hfin.countable).trans hall
    let recs : ∀ t : {t : Finset α // t.Nonempty}, t.1.card < s.1.card →
        Σ A : Set M.carrier, ChosenHull K M A := fun t _ => subHull hM base t
    have hpieces : mk (lowerRanges s recs) ≤ ls K := by
      let pieceSet : ULift.{u} ↥(properSubs s.1) → Set M.carrier := fun t =>
        let ht := mem_properSubs.mp t.down.2
        Set.range (recs ⟨t.down.1, ht.2.1⟩ ht.2.2).2.incl
      have hunion : lowerRanges s recs = Set.iUnion pieceSet := rfl
      rw [hunion]
      refine (mk_iUnion_le pieceSet).trans ?_
      have hone (t : ULift.{u} ↥(properSubs s.1)) : #(pieceSet t) ≤ ls K := by
        unfold pieceSet
        let ht := mem_properSubs.mp t.down.2
        refine mk_range_le.trans ?_
        exact ih ⟨t.down.1, ht.2.1⟩ ht.2.2
      have hsup : (⨆ t, #(pieceSet t)) ≤ ls K := ciSup_le' hone
      refine (mul_le_mul' mk_le_aleph0 hsup).trans ?_
      rw [aleph0_mul_eq hall]
    exact (add_le_add himg hpieces).trans <| by
      rw [add_eq_max hall, max_self]
  calc Model.card (subModel hM base s)
      ≤ mk (subHull hM base s).1 + ls K := hle
    _ = ls K + mk (subHull hM base s).1 := add_comm _ _
    _ = max (ls K) (mk (subHull hM base s).1) := add_eq_max hall
    _ = ls K := max_eq_left hA


section System

variable {α : Type u} [DecidableEq α] (base : α → M.carrier)

theorem subIncl_covers_sub (t s : {t : Finset α // t.Nonempty}) (hts : t.1 ⊆ s.1)
    (x : (subModel hM base t).carrier) : ∃ y, subIncl hM base s y = subIncl hM base t x := by
  by_cases hlt : t.1.card < s.1.card
  · exact ⟨subInclFactor hM base t s hts hlt x,
      congrFun (congrArg (⇑) (subInclFactor_comp hM base t s hts hlt)) x⟩
  · have hst : t = s := Subtype.ext (Finset.eq_of_subset_of_card_le hts (not_lt.mp hlt))
    subst hst
    exact ⟨x, rfl⟩

/-- The maps of the finite-subset system. -/
noncomputable def sysMap (t s : {t : Finset α // t.Nonempty}) (hts : t.1 ⊆ s.1) :
    (subModel hM base t).carrier ↪[K.τ] (subModel hM base s).carrier :=
  factorEmbedding (subIncl hM base t) (subIncl hM base s) (subIncl_covers_sub hM base t s hts)

theorem sysMap_spec (t s : {t : Finset α // t.Nonempty}) (hts : t.1 ⊆ s.1) (x) :
    subIncl hM base s (sysMap hM base t s hts x) = subIncl hM base t x :=
  congrFun (congrArg (⇑) (factorEmbedding_comp _ _ (subIncl_covers_sub hM base t s hts))) x

/-- **The finite-subset LS system** as a directed system of models of `K`. -/
noncomputable def lsSystem [Nonempty α] : DirectedSystem K.τ where
  ι := {t : Finset α // t.Nonempty}
  nonempty := ⟨⟨{Classical.arbitrary α}, Finset.singleton_nonempty _⟩⟩
  rel t s := t.1 ⊆ s.1
  refl t := Finset.Subset.refl _
  trans h h' := h.trans h'
  directed t s := ⟨⟨t.1 ∪ s.1, t.2.mono Finset.subset_union_left⟩,
    Finset.subset_union_left, Finset.subset_union_right⟩
  obj t := subModel hM base t
  map {t s} h := sysMap hM base t s h
  map_refl t := by
    ext x
    exact (subIncl hM base t).injective (sysMap_spec hM base t t _ x)
  map_trans {t s r} h h' := by
    ext x
    apply (subIncl hM base r).injective
    rw [sysMap_spec]
    simp only [Language.Embedding.comp_apply]
    rw [sysMap_spec, sysMap_spec]

theorem lsSystem_strong [Nonempty α] {t s : (lsSystem hM base).ι}
    (h : (lsSystem hM base).rel t s) : K.Strong ((lsSystem hM base).map h) :=
  K.coherence _ (subIncl hM base t) (subIncl hM base s) (subIncl_strong hM base t)
    (subIncl_strong hM base s) (by ext x; exact sysMap_spec hM base t s h x)

end System

/-- **Directed covers are strong.**  If a model `A` embedded in `N ∈ K` is covered by the
images of a directed system of models of `K` with strong maps, each strong in `N` through
`A`, then `A` is strong in `N` (Lemma 2.1 and isomorphism invariance).  This turns the
directed LS system into strongness of the closure under the witness functions. -/
theorem strong_of_directed_cover (S : DirectedSystem K.τ) (hmem : ∀ i, K.Mem (S.obj i))
    (hstrong : ∀ {i j} (hij : S.rel i j), K.Strong (S.map hij)) {A N : Model K.τ}
    (hN : K.Mem N) (incl : A.carrier ↪[K.τ] N.carrier)
    (g : ∀ i, (S.obj i).carrier ↪[K.τ] A.carrier)
    (hg : ∀ i, K.Strong (incl.comp (g i)))
    (hcompat : ∀ {i j} (hij : S.rel i j), (g j).comp (S.map hij) = g i)
    (hcover : ∀ a, ∃ i y, g i y = a) : K.Strong incl := by
  obtain ⟨L, hL, hcanon, huniv⟩ := lemma_2_1 K S hmem hstrong
  obtain ⟨f, hf, hfc⟩ := huniv N (fun i => incl.comp (g i)) hN hg (fun {i j} hij => by
    rw [Language.Embedding.comp_assoc, hcompat hij])
  have hrange : ∀ a, ∃ y, f y = incl a := fun a => by
    obtain ⟨i, y, rfl⟩ := hcover a
    exact ⟨L.canon i y, by
      have := congrFun (congrArg (⇑) (hfc i)) y
      simpa using this⟩
  let φ := factorEmbedding incl f hrange
  have hφ : f.comp φ = incl := factorEmbedding_comp incl f hrange
  have hsurj : Function.Surjective φ := fun x => by
    obtain ⟨i, y, rfl⟩ := L.joint x
    refine ⟨g i y, f.injective ?_⟩
    have h1 := congrFun (congrArg (⇑) hφ) (g i y)
    have h2 := congrFun (congrArg (⇑) (hfc i)) y
    simp only [Language.Embedding.comp_apply] at h1 h2
    rw [h1, h2]
  let e : A.carrier ≃[K.τ] L.obj.carrier :=
    { toEquiv := Equiv.ofBijective φ ⟨φ.injective, hsurj⟩
      map_fun' := fun F x => φ.map_fun F x
      map_rel' := fun r x => φ.map_rel r x }
  have hA : K.Mem A := K.iso_closed ⟨e.symm⟩ hL
  have he : K.Strong e.toEmbedding :=
    K.transport_strong (Language.Embedding.refl K.τ _) e (K.strong_refl _ hA)
  have : incl = f.comp e.toEmbedding := by
    rw [← hφ]; rfl
  rw [this]
  exact K.strong_trans _ _ he hf

open Classical in
/-- **Hull-closed submodels are strong.**  If a model `A` embedded in `M ∈ K` contains (through
the embedding) the LS hull `N_s` of every nonempty finite set `s` of its elements, then the
embedding is strong.  Closure under LS witness functions is exactly this condition. -/
theorem strong_of_hull_closed {A : Model K.τ} [Nonempty A.carrier]
    (incl : A.carrier ↪[K.τ] M.carrier)
    (hcl : ∀ (s : {t : Finset A.carrier // t.Nonempty}) (x : (subModel hM incl s).carrier),
      ∃ a, incl a = subIncl hM incl s x) :
    K.Strong incl := by
  let S := lsSystem hM incl
  let g : ∀ s : S.ι, (S.obj s).carrier ↪[K.τ] A.carrier := fun s =>
    factorEmbedding (subIncl hM incl s) incl (hcl s)
  have hg : ∀ s, incl.comp (g s) = subIncl hM incl s := fun s =>
    factorEmbedding_comp _ _ (hcl s)
  refine strong_of_directed_cover S (fun s => subModel_mem hM incl s)
    (fun h => lsSystem_strong hM incl h) hM incl g (fun s => by rw [hg]; exact subIncl_strong hM incl s)
    (fun {s t} hst => ?_) (fun a => ?_)
  · ext x
    apply incl.injective
    have h1 := congrFun (congrArg (⇑) (hg t)) (S.map hst x)
    have h2 := congrFun (congrArg (⇑) (hg s)) x
    exact h1.trans ((sysMap_spec hM incl s t hst x).trans h2.symm)
  · let s : S.ι := ⟨{a}, Finset.singleton_nonempty a⟩
    have hmem : incl a ∈ (subHull hM incl s).1 := by
      rw [subHull_eq hM incl s]
      exact Or.inl ⟨a, Finset.mem_singleton_self a, rfl⟩
    obtain ⟨x, hx⟩ := subIncl_covers hM incl s hmem
    refine ⟨s, x, incl.injective ?_⟩
    exact (congrFun (congrArg (⇑) (hg s)) x).trans hx

end LS83
end AEC
