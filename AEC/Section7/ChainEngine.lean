module

public import Mathlib

@[expose] public section

/-!
# Generic coherent-chain engine (`infra_78_coherent_chain_engine`, grokbot cycle 49)

Split of `infra_78_recursion_plumbing`. Stages and maps are *non-dependent* data `S`, `M`
(for the Prop 7.8 matrix: objects on the fixed carrier `κ.ord.ToType` and raw maps between
carriers), so the transfinite recursion is a plain `WellFounded.fix` with constant motive and
needs no casts. A successor operator `sop` and a limit operator `lop` (fed the restricted earlier
stages) produce each stage together with the maps into it from all earlier stages; validity of
arrows (`Arr`), the identity law and the composition law are then proved by well-founded
induction. The matrix instantiation (`infra_78_engine_matrix_instantiate`) is tracked on the
board.
-/

open Classical

namespace AEC

section ChainEngine
variable {ι : Type*} [LinearOrder ι] [WellFoundedLT ι]
variable {S M : Type*}

/-- One step of the coherent-chain recursion: the stage at `k` and the maps into it from every
index, computed from the earlier stages. -/
noncomputable def infra_78_engineStep (s0 : S) (idM : M) (compM : M → M → M)
    (sop : ι → S → S × M)
    (lop : (k : ι) → (Set.Iio k → S) → (Set.Iio k → Set.Iio k → M) → S × (Set.Iio k → M))
    (k : ι) (prev : ∀ j, j < k → S × (ι → M)) : S × (ι → M) :=
  if hs : ∃ β, β ⋖ k then
    let β := Classical.choose hs
    let hβ : β < k := (Classical.choose_spec hs).lt
    let r := sop β (prev β hβ).1
    (r.1, fun i => if i < k then compM ((prev β hβ).2 i) r.2 else idM)
  else if IsMin k then (s0, fun _ => idM)
  else
    let r := lop k (fun j => (prev j.1 j.2).1) (fun i j => (prev j.1 j.2).2 i.1)
    (r.1, fun i => if hi : i < k then r.2 ⟨i, hi⟩ else idM)

noncomputable def infra_78_engine (s0 : S) (idM : M) (compM : M → M → M)
    (sop : ι → S → S × M)
    (lop : (k : ι) → (Set.Iio k → S) → (Set.Iio k → Set.Iio k → M) → S × (Set.Iio k → M)) :
    ι → S × (ι → M) :=
  (wellFounded_lt (α := ι)).fix (infra_78_engineStep s0 idM compM sop lop)

theorem infra_78_engine_eq (s0 : S) (idM : M) (compM : M → M → M)
    (sop : ι → S → S × M)
    (lop : (k : ι) → (Set.Iio k → S) → (Set.Iio k → Set.Iio k → M) → S × (Set.Iio k → M))
    (k : ι) :
    infra_78_engine s0 idM compM sop lop k =
      infra_78_engineStep s0 idM compM sop lop k
        (fun j _ => infra_78_engine s0 idM compM sop lop j) :=
  (wellFounded_lt (α := ι)).fix_eq _ k


section
variable (s0 : S) (idM : M) (compM : M → M → M) (sop : ι → S → S × M)
    (lop : (k : ι) → (Set.Iio k → S) → (Set.Iio k → Set.Iio k → M) → S × (Set.Iio k → M))

/-- The object at stage `k` of the engine chain. -/
noncomputable def infra_78_engineObj (k : ι) : S := (infra_78_engine s0 idM compM sop lop k).1
/-- The map from stage `i` into stage `k` (meaningful for `i ≤ k`). -/
noncomputable def infra_78_engineMap (i k : ι) : M := (infra_78_engine s0 idM compM sop lop k).2 i

omit [WellFoundedLT ι] in
theorem infra_78_covBy_unique {β β' k : ι} (h : β ⋖ k) (h' : β' ⋖ k) : β = β' := by
  rcases lt_trichotomy β β' with hlt | heq | hgt
  · exact absurd h'.lt (h.2 hlt)
  · exact heq
  · exact absurd h.lt (h'.2 hgt)

theorem infra_78_engine_succ_eq {β k : ι} (hβ : β ⋖ k) :
    infra_78_engineObj s0 idM compM sop lop k =
      (sop β (infra_78_engineObj s0 idM compM sop lop β)).1 ∧
    ∀ i, infra_78_engineMap s0 idM compM sop lop i k =
      if i < k then compM (infra_78_engineMap s0 idM compM sop lop i β)
        (sop β (infra_78_engineObj s0 idM compM sop lop β)).2 else idM := by
  have hs : ∃ β, β ⋖ k := ⟨β, hβ⟩
  have hc : Classical.choose hs = β := infra_78_covBy_unique (Classical.choose_spec hs) hβ
  unfold infra_78_engineObj infra_78_engineMap
  rw [infra_78_engine_eq]
  simp only [infra_78_engineStep, hs, ↓reduceDIte]
  rw [hc]
  exact ⟨rfl, fun i => rfl⟩

theorem infra_78_engine_min_eq {k : ι} (hk : IsMin k) :
    infra_78_engineObj s0 idM compM sop lop k = s0 ∧
    ∀ i, infra_78_engineMap s0 idM compM sop lop i k = idM := by
  have hs : ¬ ∃ β, β ⋖ k := fun ⟨β, hβ⟩ => hk.not_lt hβ.lt
  unfold infra_78_engineObj infra_78_engineMap
  rw [infra_78_engine_eq]
  simp [infra_78_engineStep, hs, hk]

theorem infra_78_engine_lim_eq {k : ι} (hk : ¬ IsMin k) (hs : ¬ ∃ β, β ⋖ k) :
    infra_78_engineObj s0 idM compM sop lop k =
      (lop k (fun j => infra_78_engineObj s0 idM compM sop lop j.1)
        (fun i j => infra_78_engineMap s0 idM compM sop lop i.1 j.1)).1 ∧
    ∀ i, infra_78_engineMap s0 idM compM sop lop i k =
      if hi : i < k then (lop k (fun j => infra_78_engineObj s0 idM compM sop lop j.1)
        (fun i j => infra_78_engineMap s0 idM compM sop lop i.1 j.1)).2 ⟨i, hi⟩ else idM := by
  unfold infra_78_engineObj infra_78_engineMap
  rw [infra_78_engine_eq]
  simp only [infra_78_engineStep, hs, hk, ↓reduceDIte, ↓reduceIte]
  exact ⟨trivial, fun i => trivial⟩

/-- **Generic coherent-chain engine.** From a successor operator `sop` and a limit operator
`lop` (each producing valid arrows when fed a valid chain), well-founded recursion yields a
total chain of stages with arrows for all `i ≤ k`, satisfying the arrow, identity and
composition laws, and computed by `sop` at successors and by `lop` at limits. Stages and maps
are non-dependent data (`S`, `M`), so no casts are needed. -/
theorem infra_78_coherent_chain_engine (Arr : S → S → M → Prop)
    (hArrId : ∀ s, Arr s s idM)
    (hArrComp : ∀ {s t u : S} {f g : M}, Arr s t f → Arr t u g → Arr s u (compM f g))
    (hidr : ∀ f, compM f idM = f)
    (hassoc : ∀ f g h, compM (compM f g) h = compM f (compM g h))
    (hsop : ∀ β s, Arr s (sop β s).1 (sop β s).2)
    (hlop : ∀ (k : ι) (cf : Set.Iio k → S) (mf : Set.Iio k → Set.Iio k → M),
      (∀ i j, i ≤ j → Arr (cf i) (cf j) (mf i j)) → (∀ i, mf i i = idM) →
      (∀ i j l, i ≤ j → j ≤ l → mf i l = compM (mf i j) (mf j l)) →
      (∀ j, Arr (cf j) (lop k cf mf).1 ((lop k cf mf).2 j)) ∧
      (∀ i j, i ≤ j → compM (mf i j) ((lop k cf mf).2 j) = (lop k cf mf).2 i)) :
    (∀ i k, i ≤ k → Arr (infra_78_engineObj s0 idM compM sop lop i)
      (infra_78_engineObj s0 idM compM sop lop k) (infra_78_engineMap s0 idM compM sop lop i k)) ∧
    (∀ k, infra_78_engineMap s0 idM compM sop lop k k = idM) ∧
    (∀ i j k, i ≤ j → j ≤ k → infra_78_engineMap s0 idM compM sop lop i k =
      compM (infra_78_engineMap s0 idM compM sop lop i j)
        (infra_78_engineMap s0 idM compM sop lop j k)) := by
  set c := infra_78_engineObj s0 idM compM sop lop with hc
  set m := infra_78_engineMap s0 idM compM sop lop with hm
  have key : ∀ k, (∀ i, i ≤ k → Arr (c i) (c k) (m i k)) ∧ m k k = idM ∧
      (∀ i j, i ≤ j → j ≤ k → m i k = compM (m i j) (m j k)) := by
    intro k
    induction k using WellFoundedLT.induction with
    | _ k IH =>
    by_cases hs : ∃ β, β ⋖ k
    · obtain ⟨β, hβ⟩ := hs
      obtain ⟨hck, hmk⟩ := infra_78_engine_succ_eq s0 idM compM sop lop hβ
      simp only [← hc, ← hm] at hck hmk
      have hle : ∀ i, i < k → i ≤ β := fun i hi => hβ.le_of_lt hi
      have hkk : m k k = idM := by rw [hmk]; simp
      refine ⟨fun i hi => ?_, hkk, fun i j hij hjk => ?_⟩
      · rcases hi.lt_or_eq with hi | rfl
        · rw [hmk, if_pos hi, hck]
          exact hArrComp ((IH β hβ.lt).1 i (hle i hi)) (hsop _ _)
        · rw [hkk]; exact hArrId _
      · rcases hjk.lt_or_eq with hjk | rfl
        · rw [hmk i, hmk j, if_pos (hij.trans_lt hjk), if_pos hjk,
            (IH β hβ.lt).2.2 i j hij (hle j hjk), hassoc]
        · rw [hkk, hidr]
    by_cases hmin : IsMin k
    · obtain ⟨hck, hmk⟩ := infra_78_engine_min_eq s0 idM compM sop lop hmin
      simp only [← hc, ← hm] at hck hmk
      have hkk : m k k = idM := hmk k
      refine ⟨fun i hi => ?_, hkk, fun i j hij hjk => ?_⟩
      · obtain rfl := le_antisymm hi (hmin hi); rw [hkk]; exact hArrId _
      · obtain rfl := le_antisymm hjk (hmin hjk)
        rw [hkk, hidr]
    obtain ⟨hck, hmk⟩ := infra_78_engine_lim_eq s0 idM compM sop lop hmin hs
    simp only [← hc, ← hm] at hck hmk
    have hkk : m k k = idM := by rw [hmk]; simp
    obtain ⟨hA, hC⟩ := hlop k (fun j => c j.1) (fun i j => m i.1 j.1)
      (fun i j hij => (IH j.1 j.2).1 i.1 hij) (fun i => (IH i.1 i.2).2.1)
      (fun i j l hij hjl => (IH l.1 l.2).2.2 i.1 j.1 hij hjl)
    refine ⟨fun i hi => ?_, hkk, fun i j hij hjk => ?_⟩
    · rcases hi.lt_or_eq with hi | rfl
      · rw [hmk, dif_pos hi, hck]; exact hA ⟨i, hi⟩
      · rw [hkk]; exact hArrId _
    · rcases hjk.lt_or_eq with hjk | rfl
      · rw [hmk i, hmk j, dif_pos (hij.trans_lt hjk), dif_pos hjk]
        exact (hC ⟨i, hij.trans_lt hjk⟩ ⟨j, hjk⟩ hij).symm
      · rw [hkk, hidr]
  exact ⟨fun i k hik => (key k).1 i hik, fun k => (key k).2.1,
    fun i j k hij hjk => (key k).2.2 i j hij hjk⟩

end

end ChainEngine
end AEC
