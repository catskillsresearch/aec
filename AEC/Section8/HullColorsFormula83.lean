module

public import AEC.Section8.HullBundle83

/-!
# Lemma 8.3: coherent colors whose coordinates satisfy prescribed formulas

If every coordinate of every long bundled sequence satisfies a prescribed formula `θ i` (e.g.
"is a chart point"), the extracted coherent colors record it, so the coordinates of every
witness bundle satisfy it too.
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {L : Language.{u, u}}

/-- Bundled samples whose coordinates satisfy `θ`. -/
def TpSampleBF (P : ∀ (M : Type u) [L.Structure M], Prop) {r : ℕ} (θ : Fin r → L.Formula (Fin 1))
    (S : ColorSample (TpColorB L r)) : Prop :=
  ∃ (M : Type u) (_ : L.Structure M), P M ∧ ∃ base : S.α → Fin r → M,
    (∀ i, Function.Injective fun a => base a i) ∧
    (∀ a i, (θ i).Realize fun _ => base a i) ∧
    ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m), S.col m s = tpCode (bundleOf base s h)

theorem tpSampleBF_reindex {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    {θ : Fin r → L.Formula (Fin 1)}
    (S : ColorSample (TpColorB L r)) {β : Type u} [LinearOrder β] (e : β ↪o S.α)
    (hS : TpSampleBF P θ S) : TpSampleBF P θ (S.reindex e) := by
  obtain ⟨M, inst, hP, base, hinj, hθ, hcol⟩ := hS
  refine ⟨M, inst, hP, fun x => base (e x), fun i => (hinj i).comp e.injective,
    fun a i => hθ (e a) i, ?_⟩
  intro m s h
  have h' : (s.map e.toEmbedding).card = m := (Finset.card_map _).trans h
  show S.col m (s.map e.toEmbedding) = _
  rw [hcol m _ h']
  unfold bundleOf
  rw [orderEmbOfFin_map e s h h']
  rfl

theorem tpSampleBF_toB {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    {θ : Fin r → L.Formula (Fin 1)} {S : ColorSample (TpColorB L r)}
    (hS : TpSampleBF P θ S) : TpSampleB P r S := by
  obtain ⟨M, inst, hP, base, hinj, -, hcol⟩ := hS
  exact ⟨M, inst, hP, base, hinj, hcol⟩

/-- **Coherent colors recording coordinate formulas.** -/
theorem tpB_coherent_colors_formula {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    (θ : Fin r → L.Formula (Fin 1))
    (hlarge : ∀ κ : Cardinal.{u}, ∃ (α : Type u) (_ : LinearOrder α) (M : Type u)
      (_ : L.Structure M), P M ∧ κ ≤ #α ∧
      ∃ base : α → Fin r → M, (∀ i, Function.Injective fun a => base a i) ∧
        ∀ a i, (θ i).Realize fun _ => base a i) :
    ∃ c : (m : ℕ) → 0 < m → TpColorB L r m,
      (∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ) ∧
      (∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = tpResB r f (c m hm)) ∧
      ∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin r),
        (θ i).relabel (fun _ => (a, i)) ∈ c m hm := by
  have hres : ∀ S (H : Set S.α), TpSampleBF P θ S → TpSampleBF P θ (S.restrict H) :=
    fun S H hS => by
      rw [ColorSample.restrict_eq_reindex]
      exact tpSampleBF_reindex S _ hS
  have hlarge' : ∀ κ : Cardinal.{u}, ∃ S, TpSampleBF P θ S ∧ κ ≤ #S.α := by
    intro κ
    obtain ⟨α, lin, M, inst, hP, hκ, base, hinj, hθ⟩ := hlarge κ
    exact ⟨⟨α, fun m s => if h : s.card = m then tpCode (bundleOf base s h) else ∅⟩,
      ⟨M, inst, hP, base, hinj, hθ, fun m s h => by simp [h]⟩, hκ⟩
  obtain ⟨c, hc⟩ := coherent_colors (P := TpSampleBF P θ) hres hlarge'
  have hcB : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ := fun n κ => by
    obtain ⟨S, hS, hκ, hhom⟩ := hc n κ
    exact ⟨S, tpSampleBF_toB hS, hκ, hhom⟩
  refine ⟨c, hcB, fun hm' hm f =>
    coherent_colors_compat (P := TpSampleB P r) (fun f c => tpResB r f c)
      (fun S hS _ _ f s hs => tpSampleB_compat S hS f s hs) hcB hm' hm f, ?_⟩
  intro m hm a i
  obtain ⟨S, ⟨M, inst, hP, base, hinj, hθ, hcol⟩, hκ, hhom⟩ := hc m (m : Cardinal.{u})
  obtain ⟨s, hs⟩ : ∃ s : Finset S.α, s.card = m := by
    obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hκ
    have hfin : t.Finite :=
      Cardinal.lt_aleph0_iff_set_finite.mp (by rw [ht]; exact Cardinal.natCast_lt_aleph0)
    refine ⟨hfin.toFinset, ?_⟩
    have h1 : #(↥(hfin.toFinset : Set S.α)) = (hfin.toFinset.card : Cardinal) :=
      Cardinal.mk_coe_finset
    rw [Set.Finite.coe_toFinset, ht] at h1
    exact_mod_cast h1.symm
  rw [← hhom m hm le_rfl s hs, hcol m s hs]
  show ((θ i).relabel _).Realize _
  rw [Formula.realize_relabel]
  exact hθ _ i

/-- Witness bundles satisfy the recorded coordinate formulas. -/
theorem witB_realize {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    {c : (m : ℕ) → 0 < m → TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
    {θ : Fin r → L.Formula (Fin 1)}
    (hθ : ∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin r),
      (θ i).relabel (fun _ => (a, i)) ∈ c m hm)
    (k : ℕ) (a : Fin (k + 1)) (i : Fin r) :
    (θ i).Realize fun _ => (witB hc k).v (a, i) := by
  have h := hθ (k + 1) (Nat.succ_pos k) a i
  rw [← (witB hc k).tp] at h
  have h' : ((θ i).relabel (fun _ => (a, i))).Realize (witB hc k).v := h
  rw [Formula.realize_relabel] at h'
  exact h'

/-! ### Two-variable formulas on increasing pairs -/

/-- Bundled samples whose coordinates satisfy `θ` and whose increasing pairs of same-sort
coordinates satisfy `ρ`. -/
def TpSampleBF2 (P : ∀ (M : Type u) [L.Structure M], Prop) {r : ℕ} (θ : Fin r → L.Formula (Fin 1))
    (ρ : Fin r → L.Formula (Fin 2)) (S : ColorSample (TpColorB L r)) : Prop :=
  ∃ (M : Type u) (_ : L.Structure M), P M ∧ ∃ base : S.α → Fin r → M,
    (∀ i, Function.Injective fun a => base a i) ∧
    (∀ a i, (θ i).Realize fun _ => base a i) ∧
    (∀ a b, a < b → ∀ i, (ρ i).Realize ![base a i, base b i]) ∧
    ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m), S.col m s = tpCode (bundleOf base s h)

theorem tpSampleBF2_reindex {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    {θ : Fin r → L.Formula (Fin 1)} {ρ : Fin r → L.Formula (Fin 2)}
    (S : ColorSample (TpColorB L r)) {β : Type u} [LinearOrder β] (e : β ↪o S.α)
    (hS : TpSampleBF2 P θ ρ S) : TpSampleBF2 P θ ρ (S.reindex e) := by
  obtain ⟨M, inst, hP, base, hinj, hθ, hρ, hcol⟩ := hS
  refine ⟨M, inst, hP, fun x => base (e x), fun i => (hinj i).comp e.injective,
    fun a i => hθ (e a) i, fun a b hab i => hρ (e a) (e b) (e.strictMono hab) i, ?_⟩
  intro m s h
  have h' : (s.map e.toEmbedding).card = m := (Finset.card_map _).trans h
  show S.col m (s.map e.toEmbedding) = _
  rw [hcol m _ h']
  unfold bundleOf
  rw [orderEmbOfFin_map e s h h']
  rfl

/-- **Coherent colors recording coordinate formulas and formulas on increasing pairs.** -/
theorem tpB_coherent_colors_formula2 {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    (θ : Fin r → L.Formula (Fin 1)) (ρ : Fin r → L.Formula (Fin 2))
    (hlarge : ∀ κ : Cardinal.{u}, ∃ (α : Type u) (_ : LinearOrder α) (M : Type u)
      (_ : L.Structure M), P M ∧ κ ≤ #α ∧
      ∃ base : α → Fin r → M, (∀ i, Function.Injective fun a => base a i) ∧
        (∀ a i, (θ i).Realize fun _ => base a i) ∧
        ∀ a b, a < b → ∀ i, (ρ i).Realize ![base a i, base b i]) :
    ∃ c : (m : ℕ) → 0 < m → TpColorB L r m,
      (∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ) ∧
      (∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = tpResB r f (c m hm)) ∧
      (∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin r),
        (θ i).relabel (fun _ => (a, i)) ∈ c m hm) ∧
      ∀ (m : ℕ) (hm : 0 < m) (a b : Fin m), a < b → ∀ i : Fin r,
        (ρ i).relabel ![(a, i), (b, i)] ∈ c m hm := by
  have hres : ∀ S (H : Set S.α), TpSampleBF2 P θ ρ S → TpSampleBF2 P θ ρ (S.restrict H) :=
    fun S H hS => by
      rw [ColorSample.restrict_eq_reindex]
      exact tpSampleBF2_reindex S _ hS
  have hlarge' : ∀ κ : Cardinal.{u}, ∃ S, TpSampleBF2 P θ ρ S ∧ κ ≤ #S.α := by
    intro κ
    obtain ⟨α, lin, M, inst, hP, hκ, base, hinj, hθ, hρ⟩ := hlarge κ
    exact ⟨⟨α, fun m s => if h : s.card = m then tpCode (bundleOf base s h) else ∅⟩,
      ⟨M, inst, hP, base, hinj, hθ, hρ, fun m s h => by simp [h]⟩, hκ⟩
  obtain ⟨c, hc⟩ := coherent_colors (P := TpSampleBF2 P θ ρ) hres hlarge'
  have hcB : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ := fun n κ => by
    obtain ⟨S, ⟨M, inst, hP, base, hinj, -, -, hcol⟩, hκ, hhom⟩ := hc n κ
    exact ⟨S, ⟨M, inst, hP, base, hinj, hcol⟩, hκ, hhom⟩
  have hsample : ∀ (m : ℕ) (hm : 0 < m), ∃ (S : ColorSample (TpColorB L r)) (M : Type u)
      (_ : L.Structure M) (base : S.α → Fin r → M) (s : Finset S.α) (hs : s.card = m),
      (∀ a i, (θ i).Realize fun _ => base a i) ∧
      (∀ a b, a < b → ∀ i, (ρ i).Realize ![base a i, base b i]) ∧
      c m hm = tpCode (bundleOf base s hs) := by
    intro m hm
    obtain ⟨S, ⟨M, inst, hP, base, hinj, hθ, hρ, hcol⟩, hκ, hhom⟩ := hc m (m : Cardinal.{u})
    obtain ⟨s, hs⟩ : ∃ s : Finset S.α, s.card = m := by
      obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hκ
      have hfin : t.Finite :=
        Cardinal.lt_aleph0_iff_set_finite.mp (by rw [ht]; exact Cardinal.natCast_lt_aleph0)
      refine ⟨hfin.toFinset, ?_⟩
      have h1 : #(↥(hfin.toFinset : Set S.α)) = (hfin.toFinset.card : Cardinal) :=
        Cardinal.mk_coe_finset
      rw [Set.Finite.coe_toFinset, ht] at h1
      exact_mod_cast h1.symm
    exact ⟨S, M, inst, base, s, hs, hθ, hρ, by rw [← hhom m hm le_rfl s hs, hcol m s hs]⟩
  refine ⟨c, hcB, fun hm' hm f =>
    coherent_colors_compat (P := TpSampleB P r) (fun f c => tpResB r f c)
      (fun S hS _ _ f s hs => tpSampleB_compat S hS f s hs) hcB hm' hm f, ?_, ?_⟩
  · intro m hm a i
    obtain ⟨S, M, inst, base, s, hs, hθ, -, hcm⟩ := hsample m hm
    rw [hcm]
    show ((θ i).relabel _).Realize _
    rw [Formula.realize_relabel]
    exact hθ _ i
  · intro m hm a b hab i
    obtain ⟨S, M, inst, base, s, hs, -, hρ, hcm⟩ := hsample m hm
    rw [hcm]
    show ((ρ i).relabel _).Realize _
    rw [Formula.realize_relabel]
    have := hρ _ _ ((s.orderEmbOfFin hs).strictMono hab) i
    convert this using 2
    funext q
    rcases q with ⟨_ | _ | _, hq⟩ <;> first | rfl | omega

/-- Witness bundles satisfy the recorded formulas on increasing pairs. -/
theorem witB_realize2 {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
    {c : (m : ℕ) → 0 < m → TpColorB L r m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
    {ρ : Fin r → L.Formula (Fin 2)}
    (hρ : ∀ (m : ℕ) (hm : 0 < m) (a b : Fin m), a < b → ∀ i : Fin r,
      (ρ i).relabel ![(a, i), (b, i)] ∈ c m hm)
    (k : ℕ) {a b : Fin (k + 1)} (hab : a < b) (i : Fin r) :
    (ρ i).Realize ![(witB hc k).v (a, i), (witB hc k).v (b, i)] := by
  have h := hρ (k + 1) (Nat.succ_pos k) a b hab i
  rw [← (witB hc k).tp] at h
  have h' : ((ρ i).relabel ![(a, i), (b, i)]).Realize (witB hc k).v := h
  rw [Formula.realize_relabel] at h'
  convert h' using 2
  funext q
  rcases q with ⟨_ | _ | _, hq⟩ <;> first | rfl | omega

end Hull83
end AEC
