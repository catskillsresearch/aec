module

public import AEC.Section8.LabLang83

/-!
# Lemma 8.3: representation positions and the chart of a closed set

"For each element of a chart choose a representing label and its finite list of positions."
For `X = E(emb)(E(J)) ⊆ E(Jp)` we choose, for each element of `X`, a label and increasing
positions in `J`.  A set `S` closed under the labels restricted to `X` and containing the
skeleton points at the chosen positions of its `X`-elements satisfies `S ∩ X = F(J_S)`, where
`J_S` is the chart of `S` (the positions whose skeleton points lie in `S`): both directions of
generation.
-/

@[expose] public section

universe u

open FirstOrder FirstOrder.Language

namespace AEC
namespace Lab83

variable {K : AbstractElementaryClass.{u}} {E : OrderPresentation K}
  {J Jp : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jp] [Nonempty Jp] (emb : J ↪o Jp)

/-- The chosen representation of an element of `E(J)` through `emb`. -/
theorem rep_exists (x : (E.obj J).carrier) :
    ∃ (n : ℕ) (a : (labLang E).Functions n) (p : Fin n → J), StrictMono p ∧
      labFun a (fun k => E.skeleton (emb (p k))) = E.map emb x :=
  map_label_value emb x

/-- Arity of the chosen representation. -/
noncomputable def repN (x : (E.obj J).carrier) : ℕ := (rep_exists emb x).choose

/-- Label of the chosen representation. -/
noncomputable def repA (x : (E.obj J).carrier) : (labLang E).Functions (repN emb x) :=
  (rep_exists emb x).choose_spec.choose

/-- Positions of the chosen representation. -/
noncomputable def repP (x : (E.obj J).carrier) : Fin (repN emb x) → J :=
  (rep_exists emb x).choose_spec.choose_spec.choose

theorem repP_spec (x : (E.obj J).carrier) :
    labFun (repA emb x) (fun k => E.skeleton (emb (repP emb x k))) = E.map emb x :=
  (rep_exists emb x).choose_spec.choose_spec.choose_spec.2

/-- The chart of a set `S ⊆ E(Jp)`: positions of `J` whose skeleton points lie in `S`. -/
def chart (S : Set (E.obj Jp).carrier) : Set J := {j | E.skeleton (emb j) ∈ S}

/-- The chart order embedding `J_S ↪o Jp`. -/
def chartEmb (S : Set (E.obj Jp).carrier) : chart emb S ↪o Jp :=
  (OrderEmbedding.subtype _).trans emb

/-- **Both directions of generation**: a set closed under the labels restricted to `X` and under
the chosen representation positions of its `X`-elements meets `X` exactly in `F(J_S)`. -/
theorem inter_eq_chart (S : Set (E.obj Jp).carrier) [Nonempty (chart emb S)]
    (hlab : ∀ {n} (a : (labLang E).Functions n) (y : Fin n → (E.obj Jp).carrier),
      (∀ k, y k ∈ S) → labR (Set.range (E.map emb)) a y ∈ S)
    (hrep : ∀ x : (E.obj J).carrier, E.map emb x ∈ S → ∀ k,
      E.skeleton (emb (repP emb x k)) ∈ S) :
    S ∩ Set.range (E.map emb) = Set.range (E.map (chartEmb emb S)) := by
  ext y
  constructor
  · rintro ⟨hyS, x, rfl⟩
    rw [← repP_spec emb x]
    refine labFun_mem_range (chartEmb emb S) _ _ fun k => ?_
    have hk : repP emb x k ∈ chart emb S := hrep x hyS k
    exact ⟨E.skeleton ⟨_, hk⟩, E.skeleton_natural (chartEmb emb S) ⟨_, hk⟩⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨n, a, p, -, hv⟩ := map_label_value (chartEmb emb S) x
    have hpos : ∀ k, E.skeleton (chartEmb emb S (p k)) = E.skeleton (emb (p k).1) := fun _ => rfl
    have hX : ∀ k, E.skeleton (chartEmb emb S (p k)) ∈ Set.range (E.map emb) := fun k =>
      ⟨E.skeleton (p k).1, E.skeleton_natural emb _⟩
    have hmem : labFun a (fun k => E.skeleton (chartEmb emb S (p k))) ∈ S := by
      rw [← labR_of_mem a _ hX]
      exact hlab a _ fun k => (p k).2
    refine ⟨hv ▸ hmem, ?_⟩
    rw [← hv]
    exact labFun_mem_range emb a _ hX

/-- The language of representation positions: unary symbols `rep_i`, `i : ℕ`. -/
def repLang : Language.{u, u} where
  Functions n := {_i : ULift.{u} ℕ // n = 1}
  Relations _ := PEmpty

open Classical in
/-- `rep_i y`: the `i`-th chosen representation position (as a skeleton point) of `y ∈ X`;
`y` itself otherwise. -/
noncomputable def repFun (i : ℕ) (y : (E.obj Jp).carrier) : (E.obj Jp).carrier :=
  if h : ∃ x, E.map emb x = y then
    if hi : i < repN emb h.choose then E.skeleton (emb (repP emb h.choose ⟨i, hi⟩)) else y
  else y

/-- The representation-position structure. -/
@[instance_reducible]
noncomputable def repStr : (repLang.{u}).Structure (E.obj Jp).carrier where
  funMap := fun {n} f x => repFun emb f.1.down (x ⟨0, f.2 ▸ Nat.zero_lt_one⟩)
  RelMap := fun r => PEmpty.elim r

/-- Any set containing `X` is closed under the representation positions. -/
theorem repFun_mem {S : Set (E.obj Jp).carrier} (hXS : Set.range (E.map emb) ⊆ S) (i : ℕ)
    {y : (E.obj Jp).carrier} (hy : y ∈ S) : repFun emb i y ∈ S := by
  unfold repFun
  split_ifs with h hi
  · exact hXS ⟨_, E.skeleton_natural emb _⟩
  · exact hy
  · exact hy

/-- A set closed under the representation positions contains the chosen positions of its
`X`-elements. -/
theorem rep_closed {S : Set (E.obj Jp).carrier}
    (hS : ∀ i y, y ∈ S → repFun emb i y ∈ S) (x : (E.obj J).carrier)
    (hx : E.map emb x ∈ S) (k : Fin (repN emb x)) : E.skeleton (emb (repP emb x k)) ∈ S := by
  have h : ∃ x', E.map emb x' = E.map emb x := ⟨x, rfl⟩
  have hc : h.choose = x := (E.map emb).injective h.choose_spec
  have := hS k.1 _ hx
  unfold repFun at this
  rw [dif_pos h] at this
  have hk : k.1 < repN emb h.choose := by rw [hc]; exact k.2
  rw [dif_pos hk] at this
  have key : ∀ (z : (E.obj J).carrier) (hz : z = x) (hk : k.1 < repN emb z),
      E.skeleton (emb (repP emb z ⟨k.1, hk⟩)) = E.skeleton (emb (repP emb x k)) := by
    rintro z rfl hk
    rfl
  rw [← key _ hc hk]
  exact this

/-- `repLang` has countably many function symbols. -/
theorem repLang_card : Cardinal.mk (Σ i, (repLang.{u}).Functions i) ≤ Cardinal.aleph0 := by
  refine (Cardinal.mk_le_of_injective (f := fun a : (Σ i, (repLang.{u}).Functions i) =>
    a.2.1) ?_).trans (by simp)
  rintro ⟨n, ⟨i⟩, hi⟩ ⟨m, ⟨j⟩, hj⟩ h
  simp only [ULift.up.injEq] at h
  subst h hi hj
  rfl

end Lab83
end AEC
