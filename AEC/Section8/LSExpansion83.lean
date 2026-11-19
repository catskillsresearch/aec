module

public import AEC.Section8.LSSystem83
public import AEC.Section8.HullReduct83
public import AEC.Section2.Enumeration

/-!
# Lemma 8.3: the LS witness expansion

For `M ∈ K` we expand `M` by `LS(K)`-many functions of every positive arity (the witness
language `lsW K`, indexed by `Enum K`): on a tuple `x` the witness functions enumerate the LS
hull `N_s` of the finite set `s` of entries of `x` (`AEC.LS83.subModel`).  A nonempty subset
closed under the witness functions contains every such hull, so by the directed-cover
argument (`LS83.strong_of_directed_cover`) its reduct is a strong submodel.
-/

@[expose] public section

namespace AEC
namespace LS83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- The LS witness language: `LS(K)`-many function symbols of each positive arity. -/
def lsW (K : AbstractElementaryClass.{u}) : Language.{u, u} where
  Functions n := match n with
    | 0 => PEmpty
    | _ + 1 => Enum K
  Relations _ := PEmpty

/-- The expanded language `τ(K) + lsW K`. -/
abbrev lsLang (K : AbstractElementaryClass.{u}) : Language.{u, u} := K.τ.sum (lsW K)

/-- Code a witness symbol by its arity and index. -/
def lsWCode : (lsW K).Symbols → ULift.{u} ℕ × Enum K
  | Sum.inl ⟨0, f⟩ => PEmpty.elim f
  | Sum.inl ⟨n + 1, η⟩ => (ULift.up n, η)
  | Sum.inr ⟨_, r⟩ => PEmpty.elim r

theorem lsWCode_injective : Function.Injective (lsWCode (K := K)) := by
  rintro (⟨_ | n, f⟩ | ⟨_, r⟩) (⟨_ | m, g⟩ | ⟨_, r'⟩) h
  all_goals first
    | exact PEmpty.elim f
    | exact PEmpty.elim g
    | exact PEmpty.elim r
    | exact PEmpty.elim r'
    | skip
  simp only [lsWCode, Prod.mk.injEq, ULift.up.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- **The witness language has at most `LS(K)` symbols.** -/
theorem lsW_card_le : (lsW K).card ≤ ls K := by
  have hall : aleph0 ≤ ls K := (isLSBound_ls K).1
  calc (lsW K).card ≤ #(ULift.{u} ℕ × Enum K) := mk_le_of_injective lsWCode_injective
    _ = aleph0 * ls K := by rw [mk_prod, enum_card]; simp
    _ = ls K := aleph0_mul_eq hall

/-- **The expanded language has at most `LS(K)` symbols.** -/
theorem lsLang_card_le : (lsLang K).card ≤ ls K := by
  have hall : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hτ : K.τ.card ≤ ls K := le_trans le_self_add (isLSBound_ls K).2.1
  rw [Language.card_sum, lift_id, lift_id]
  exact (add_le_add hτ lsW_card_le).trans (by rw [add_eq_max hall, max_self])

section Pull

variable {M : Model K.τ} (hM : K.Mem M) [DecidableEq M.carrier]
variable {A : Model K.τ} (incl : A.carrier ↪[K.τ] M.carrier)

/-- The image in `M` of a nonempty finite set of elements of `A`. -/
def mapS (t : {t : Finset A.carrier // t.Nonempty}) : {t : Finset M.carrier // t.Nonempty} :=
  ⟨t.1.map incl.toEmbedding, t.2.map⟩

omit [DecidableEq M.carrier] in
theorem mapS_mono {t s : {t : Finset A.carrier // t.Nonempty}} (h : t.1 ⊆ s.1) :
    (mapS incl t).1 ⊆ (mapS incl s).1 :=
  Finset.map_subset_map.mpr h

/-- The `M`-indexed LS system pulled back to the nonempty finite subsets of `A`. -/
noncomputable def pullSystem [Nonempty A.carrier] : DirectedSystem K.τ where
  ι := {t : Finset A.carrier // t.Nonempty}
  nonempty := ⟨⟨{Classical.arbitrary A.carrier}, Finset.singleton_nonempty _⟩⟩
  rel t s := t.1 ⊆ s.1
  refl t := Finset.Subset.refl _
  trans h h' := h.trans h'
  directed t s := by
    classical
    exact ⟨⟨t.1 ∪ s.1, t.2.mono Finset.subset_union_left⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩
  obj t := subModel hM id (mapS incl t)
  map {t s} h := sysMap hM id (mapS incl t) (mapS incl s)
    (show (mapS incl t).1 ⊆ (mapS incl s).1 from Finset.map_subset_map.mpr h)
  map_refl t := by
    ext x
    exact (subIncl hM id _).injective (sysMap_spec hM id _ _ _ x)
  map_trans {t s r} h h' := by
    ext x
    apply (subIncl hM id (mapS incl r)).injective
    rw [sysMap_spec]
    simp only [Language.Embedding.comp_apply]
    rw [sysMap_spec, sysMap_spec]

theorem pullSystem_strong [Nonempty A.carrier] {t s : (pullSystem hM incl).ι}
    (h : (pullSystem hM incl).rel t s) : K.Strong ((pullSystem hM incl).map h) :=
  K.coherence _ (subIncl hM id (mapS incl t)) (subIncl hM id (mapS incl s))
    (subIncl_strong hM id _) (subIncl_strong hM id _)
    (by ext x; exact sysMap_spec hM id _ _ (mapS_mono incl h) x)

/-- **Hull-closed submodels are strong** (hulls computed in `M`).  If `A` embedded in `M ∈ K`
contains the `M`-hull `N_s` of the image of every nonempty finite set of its elements, then
the embedding is strong. -/
theorem strong_of_hull_closed' [Nonempty A.carrier]
    (hcl : ∀ (s : {t : Finset A.carrier // t.Nonempty})
      (x : (subModel hM id (mapS incl s)).carrier),
      ∃ a, incl a = subIncl hM id (mapS incl s) x) :
    K.Strong incl := by
  let S := pullSystem hM incl
  let g : ∀ s : S.ι, (S.obj s).carrier ↪[K.τ] A.carrier := fun s =>
    factorEmbedding (subIncl hM id (mapS incl s)) incl (hcl s)
  have hg : ∀ s, incl.comp (g s) = subIncl hM id (mapS incl s) := fun s =>
    factorEmbedding_comp _ _ (hcl s)
  refine strong_of_directed_cover S (fun s => subModel_mem hM id _)
    (fun h => pullSystem_strong hM incl h) hM incl g
    (fun s => by rw [hg]; exact subIncl_strong hM id _) (fun {s t} hst => ?_) (fun a => ?_)
  · ext x
    apply incl.injective
    have h1 := congrFun (congrArg (⇑) (hg t)) (S.map hst x)
    have h2 := congrFun (congrArg (⇑) (hg s)) x
    exact h1.trans ((sysMap_spec hM id _ _ (mapS_mono incl hst) x).trans h2.symm)
  · let s : S.ι := ⟨{a}, Finset.singleton_nonempty a⟩
    have hmem : incl a ∈ (subHull hM id (mapS incl s)).1 := by
      rw [subHull_eq hM id (mapS incl s)]
      refine Or.inl ⟨incl a, ?_, rfl⟩
      exact Finset.mem_map_of_mem _ (Finset.mem_singleton_self a)
    obtain ⟨x, hx⟩ := subIncl_covers hM id (mapS incl s) hmem
    refine ⟨s, x, incl.injective ?_⟩
    exact (congrFun (congrArg (⇑) (hg s)) x).trans hx

end Pull

section Witness

variable {M : Model K.τ} (hM : K.Mem M) [DecidableEq M.carrier]

/-- The finite set of entries of a tuple. -/
def entries {n : ℕ} (x : Fin (n + 1) → M.carrier) : {t : Finset M.carrier // t.Nonempty} :=
  ⟨Finset.univ.image x, Finset.univ_nonempty.image _⟩

theorem subModel_nonempty (s : {t : Finset M.carrier // t.Nonempty}) :
    Nonempty (subModel hM id s).carrier := by
  obtain ⟨a, ha⟩ := s.2
  have hmem : a ∈ (subHull hM id s).1 := by
    rw [subHull_eq hM id s]
    exact Or.inl ⟨a, ha, rfl⟩
  obtain ⟨x, -⟩ := subIncl_covers hM id s hmem
  exact ⟨x⟩

/-- An injection of a hull into `Enum K` (hulls have size at most `LS(K)`). -/
noncomputable def hullEnum (s : {t : Finset M.carrier // t.Nonempty}) :
    (subModel hM id s).carrier ↪ Enum K :=
  Classical.choice <| by
    rw [← Cardinal.le_def, enum_card]
    exact subModel_card hM id s

/-- Enumerate a hull by `Enum K`. -/
noncomputable def hullPt (s : {t : Finset M.carrier // t.Nonempty}) (η : Enum K) :
    (subModel hM id s).carrier :=
  haveI := subModel_nonempty hM s
  Function.invFun (hullEnum hM s) η

theorem hullPt_surj (s : {t : Finset M.carrier // t.Nonempty})
    (y : (subModel hM id s).carrier) : ∃ η, hullPt hM s η = y := by
  have := subModel_nonempty hM s
  exact ⟨hullEnum hM s y, Function.leftInverse_invFun (hullEnum hM s).injective y⟩

/-- The witness function `η` of arity `n + 1`: the `η`-th element of the hull of the
entries. -/
noncomputable def witFun {n : ℕ} (η : Enum K) (x : Fin (n + 1) → M.carrier) : M.carrier :=
  subIncl hM id (entries x) (hullPt hM (entries x) η)

theorem witFun_onto {n : ℕ} (x : Fin (n + 1) → M.carrier) (s : {t : Finset M.carrier // t.Nonempty})
    (hs : entries x = s) (y : (subModel hM id s).carrier) :
    ∃ η, witFun hM η x = subIncl hM id s y := by
  subst hs
  obtain ⟨η, hη⟩ := hullPt_surj hM (entries x) y
  exact ⟨η, by rw [witFun, hη]⟩

/-- The witness structure on `M`. -/
@[instance_reducible]
noncomputable def witStr : (lsW K).Structure M.carrier where
  funMap := fun {n} => match n with
    | 0 => fun f => PEmpty.elim f
    | _ + 1 => fun η x => witFun hM η x
  RelMap := fun r => PEmpty.elim r

/-- **Witness-closed submodels are strong.** -/
theorem strong_of_witness_closed {A : Model K.τ} [Nonempty A.carrier]
    (incl : A.carrier ↪[K.τ] M.carrier)
    (hcl : ∀ (n : ℕ) (η : Enum K) (x : Fin (n + 1) → A.carrier),
      ∃ a, incl a = witFun hM η (fun i => incl (x i))) :
    K.Strong incl := by
  refine strong_of_hull_closed' hM incl fun t y => ?_
  obtain ⟨k, hk⟩ : ∃ k, t.1.card = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero ((Finset.card_pos.mpr t.2).ne')
  let x : Fin (k + 1) → A.carrier := fun i => (t.1.equivFin.symm (Fin.cast hk.symm i)).1
  have himg : entries (fun i => incl (x i)) = mapS incl t := by
    apply Subtype.ext
    ext b
    simp only [entries, mapS, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_map]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨x i, (t.1.equivFin.symm (Fin.cast hk.symm i)).2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨Fin.cast hk (t.1.equivFin ⟨a, ha⟩), ?_⟩
      simp [x]
      rfl
  obtain ⟨η, hη⟩ := witFun_onto hM _ _ himg y
  obtain ⟨a, ha⟩ := hcl k η x
  exact ⟨a, ha.trans hη⟩

end Witness


section Expansion

open Hull83

/-- The language inclusion `τ(K) → τ(K) + lsW K`. -/
abbrev lsInl (K : AbstractElementaryClass.{u}) : K.τ →ᴸ lsLang K := LHom.sumInl

/-- **LS-closed expansions.**  An `lsLang K`-structure whose `τ(K)`-reduct is in `K` and in
which the reduct of every nonempty substructure (a nonempty set closed under the `τ(K)`
functions and the witness functions) is a strong submodel. -/
def LSClosed (N : Type u) [(lsLang K).Structure N] : Prop :=
  K.Mem (red (lsInl K) N) ∧
    ∀ A : (lsLang K).Substructure N, (A : Set N).Nonempty →
      K.Strong (redEmb (lsInl K) A.subtype)

/-- The witness expansion of `M ∈ K`. -/
@[instance_reducible]
noncomputable def lsStr {M : Model K.τ} (hM : K.Mem M) [DecidableEq M.carrier] :
    (lsLang K).Structure M.carrier :=
  @Language.sumStructure _ _ _ M.str (witStr hM)

/-- The witness expansion expands `M`: its `τ(K)`-reduct is `M`. -/
theorem lsStr_reduct {M : Model K.τ} (hM : K.Mem M) [DecidableEq M.carrier] :
    @LHom.reduct _ _ (lsInl K) M.carrier (lsStr hM) = M.str := rfl

/-- **Lemma 8.3 (LS witness expansion).**  Every `M ∈ K` has an expansion by `LS(K)`-many
functions of each positive arity in which every nonempty substructure has a strong reduct. -/
theorem exists_ls_expansion (M : Model K.τ) (hM : K.Mem M) :
    ∃ str : (lsLang K).Structure M.carrier,
      @LHom.reduct _ _ (lsInl K) M.carrier str = M.str ∧ @LSClosed K M.carrier str := by
  classical
  refine ⟨lsStr hM, rfl, hM, fun A hA => ?_⟩
  let _ := lsStr hM
  have : Nonempty (red (lsInl K) A).carrier := hA.to_subtype
  refine strong_of_witness_closed hM (A := red (lsInl K) A) (redEmb (lsInl K) A.subtype)
    fun n η x => ?_
  exact ⟨⟨_, A.fun_mem (Sum.inr η : (lsLang K).Functions (n + 1)) (fun i => (x i).1)
    (fun i => (x i).2)⟩, rfl⟩

/-- In LS-closed expansions the term hull of every nonempty finite tuple has strong reduct. -/
theorem hullStrong_lsClosed : HullStrong (lsInl K) (fun N _ => LSClosed (K := K) N) :=
  hullStrong_of_substructures (lsInl K) fun _ _ h A hA => h.2 A hA

end Expansion

end LS83
end AEC
