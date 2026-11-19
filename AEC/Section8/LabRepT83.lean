module

public import AEC.Section8.LabRep83

/-!
# Lemma 8.3: representation positions for the transported (`Y`-sort) labels

For an injection `e : E(I) → N` (`Y ≅ F(Z)` inside `L`), a set closed under the transported
labels and containing the `e`-images of the skeleton points at the chosen positions of its
`range e`-elements meets `range e` exactly in `e(F(Z_S))`, `Z_S` its chart.
-/

@[expose] public section

universe u

open FirstOrder FirstOrder.Language

namespace AEC
namespace Lab83

variable {K : AbstractElementaryClass.{u}} {E : OrderPresentation K}
  {I : Type u} [LinearOrder I] [Nonempty I] {N : Type u} (e : (E.obj I).carrier → N)

/-- Transported labels on `e`-images are `e` of the labels. -/
theorem labT_apply (he : Function.Injective e) {n : ℕ} (a : (labLang E).Functions n)
    (y : Fin n → (E.obj I).carrier) : labT e a (fun k => e (y k)) = e (labFun a y) := by
  have h : ∀ k, ∃ z, e z = e (y k) := fun k => ⟨_, rfl⟩
  unfold labT
  rw [dif_pos h]
  have hc : (fun k => (h k).choose) = y := funext fun k => he (h k).choose_spec
  rw [hc]

/-- Arity, label and positions of the chosen representation of an element of `E(I)`. -/
noncomputable def repTN (x : (E.obj I).carrier) : ℕ := (exists_label_value x).choose

noncomputable def repTA (x : (E.obj I).carrier) : (labLang E).Functions (repTN x) :=
  (exists_label_value x).choose_spec.choose

noncomputable def repTP (x : (E.obj I).carrier) : Fin (repTN x) → I :=
  (exists_label_value x).choose_spec.choose_spec.choose

theorem repTP_spec (x : (E.obj I).carrier) :
    labFun (repTA x) (fun k => E.skeleton (repTP x k)) = x :=
  (exists_label_value x).choose_spec.choose_spec.choose_spec.2

/-- The chart of `S ⊆ N` through `e`: positions whose transported skeleton points lie in `S`. -/
def chartT (S : Set N) : Set I := {z | e (E.skeleton z) ∈ S}

/-- **Both directions of generation for the `Y`-sort.** -/
theorem inter_eq_chartT (he : Function.Injective e) (S : Set N) [Nonempty (chartT e S)]
    (hlab : ∀ {n} (a : (labLang E).Functions n) (y : Fin n → N), (∀ k, y k ∈ S) →
      labT e a y ∈ S)
    (hrep : ∀ x : (E.obj I).carrier, e x ∈ S → ∀ k, e (E.skeleton (repTP x k)) ∈ S) :
    S ∩ Set.range e =
      Set.range (e ∘ E.map (OrderEmbedding.subtype (fun z => z ∈ chartT e S))) := by
  ext y
  constructor
  · rintro ⟨hyS, x, rfl⟩
    have hx : x ∈ Set.range (E.map (OrderEmbedding.subtype (fun z => z ∈ chartT e S))) := by
      rw [← repTP_spec x]
      refine labFun_mem_range _ _ _ fun k => ?_
      have hk : repTP x k ∈ chartT e S := hrep x hyS k
      exact ⟨E.skeleton (⟨repTP x k, hk⟩ : {z // z ∈ chartT e S}),
        E.skeleton_natural _ (⟨repTP x k, hk⟩ : {z // z ∈ chartT e S})⟩
    obtain ⟨w, hw⟩ := hx
    exact ⟨w, by simp only [Function.comp_apply, hw]⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨n, a, p, -, hv⟩ :=
      map_label_value (OrderEmbedding.subtype (fun z => z ∈ chartT e S)) x
    refine ⟨?_, ⟨_, rfl⟩⟩
    show e (E.map _ x) ∈ S
    rw [← hv, ← labT_apply e he]
    exact hlab a _ fun k => (p k).2

open Classical in
/-- `repT_i y`: the `e`-image of the `i`-th chosen position of `e⁻¹ y`; `y` otherwise. -/
noncomputable def repTFun (i : ℕ) (y : N) : N :=
  if h : ∃ x, e x = y then
    if hi : i < repTN h.choose then e (E.skeleton (repTP h.choose ⟨i, hi⟩)) else y
  else y

/-- The transported representation-position structure (on `repLang`). -/
@[instance_reducible]
noncomputable def repTStr : (repLang.{u}).Structure N where
  funMap := fun {n} f x => repTFun e f.1.down (x ⟨0, f.2 ▸ Nat.zero_lt_one⟩)
  RelMap := fun r => PEmpty.elim r

/-- Any set containing `range e` is closed under the transported representation positions. -/
theorem repTFun_mem {S : Set N} (hS : Set.range e ⊆ S) (i : ℕ) {y : N} (hy : y ∈ S) :
    repTFun e i y ∈ S := by
  unfold repTFun
  split_ifs with h hi
  · exact hS ⟨_, rfl⟩
  · exact hy
  · exact hy

/-- A set closed under the transported positions contains them for its `range e`-elements. -/
theorem repT_closed (he : Function.Injective e) {S : Set N}
    (hS : ∀ i y, y ∈ S → repTFun e i y ∈ S) (x : (E.obj I).carrier) (hx : e x ∈ S)
    (k : Fin (repTN x)) : e (E.skeleton (repTP x k)) ∈ S := by
  have h : ∃ x', e x' = e x := ⟨x, rfl⟩
  have hc : h.choose = x := he h.choose_spec
  have := hS k.1 _ hx
  unfold repTFun at this
  rw [dif_pos h] at this
  have hk : k.1 < repTN h.choose := by rw [hc]; exact k.2
  rw [dif_pos hk] at this
  have key : ∀ (z : (E.obj I).carrier) (hz : z = x) (hk : k.1 < repTN z),
      e (E.skeleton (repTP z ⟨k.1, hk⟩)) = e (E.skeleton (repTP x k)) := by
    rintro z rfl hk
    rfl
  rw [← key _ hc hk]
  exact this

end Lab83
end AEC
