module

public import AEC.Section2.Partition
public import Mathlib.Data.Set.Finite.Basic

/-!
# Lemma 8.3: generic coherent color extraction (hull extraction, combinatorial core)

The proof of Lemma 8.3 (Section 8, `text.md`) extracts the pair template "exactly as in
Theorem 2.6": it "chooses compatible colors at all finite arities while retaining arbitrarily
large homogeneous samples", where the color of an increasing tuple is the isomorphism type of
its displayed finite hull in the expanded pair sample.

The Section 2 formalization (`AEC.Section2.CoherentColor`, `exists_extend`, `colorTower`)
does this for `FamilyCode K n` colors read from samples of `K`.  Here the same argument is
stated once for an arbitrary family of samples closed under thinning, with set-sized
palettes, so that it can be instantiated for the expanded pair samples of Lemma 8.3 (whose
colors carry the mark, edge, chart and retraction data) instead of being redone.
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u v

open Cardinal

/-- An index-ordered sample colored at every arity: `col m s` is the color of the
increasing tuple enumerating `s` (only used when `s.card = m`). -/
structure ColorSample (C : ℕ → Type u) : Type (u + 1) where
  α : Type u
  [lo : LinearOrder α]
  col : (m : ℕ) → Finset α → C m

attribute [instance] ColorSample.lo

variable {C : ℕ → Type u}

/-- Thinning a sample to an index subset keeps each tuple's color. -/
def ColorSample.restrict (S : ColorSample C) (H : Set S.α) : ColorSample C where
  α := ↥H
  col m s := S.col m (s.map (Function.Embedding.subtype (· ∈ H)))

/-- Every positive tuple of arity at most `n` has the prescribed color. -/
def Homog (S : ColorSample C) (n : ℕ) (d : (m : ℕ) → 0 < m → C m) : Prop :=
  ∀ (m : ℕ) (hm0 : 0 < m), m ≤ n → ∀ s : Finset S.α, s.card = m → S.col m s = d m hm0

/-- Admissible samples of size at least `κ`, homogeneous through arity `n` for `d`. -/
def Joint (P : ColorSample C → Prop) (n : ℕ) (d : (m : ℕ) → 0 < m → C m)
    (κ : Cardinal.{u}) : Prop :=
  ∃ S : ColorSample C, P S ∧ κ ≤ #S.α ∧ Homog S n d

/-- Replace the color at arity `n + 1`. -/
def upd (n : ℕ) (d : (m : ℕ) → 0 < m → C m) (c : C (n + 1)) : (m : ℕ) → 0 < m → C m :=
  fun m hm0 => if h : m = n + 1 then cast (congrArg C h.symm) c else d m hm0

theorem upd_self (n : ℕ) (d : (m : ℕ) → 0 < m → C m) (c : C (n + 1)) (h : 0 < n + 1) :
    upd n d c (n + 1) h = c := by
  simp [upd]

theorem upd_of_le {n m : ℕ} (d : (m : ℕ) → 0 < m → C m) (c : C (n + 1)) (hm0 : 0 < m)
    (hm : m ≤ n) : upd n d c m hm0 = d m hm0 := by
  have : m ≠ n + 1 := by omega
  simp [upd, this]

theorem le_sum_apply' {ι : Type u} (f : ι → Cardinal.{u}) (i : ι) : f i ≤ sum f := by
  rw [sum, ← mk_out (f i)]
  refine mk_le_of_injective (f := fun x : (f i).out => (⟨i, x⟩ : Σ j, (f j).out)) ?_
  intro a b h
  exact eq_of_heq (Sigma.ext_iff.mp h).2

variable (P : ColorSample C → Prop)

/-- One step of the color tower (the analogue of Section 2's `exists_extend`): colors through
arity `n` with arbitrarily large homogeneous samples admit a color at arity `n + 1` with the
same property.  If every candidate color failed at some size, the successor of the sum of
those sizes would still carry a homogeneous thinning by the Erdős–Rado partition bound. -/
theorem exists_extend
    (hres : ∀ S (H : Set S.α), P S → P (S.restrict H))
    {n : ℕ} (d : (m : ℕ) → 0 < m → C m) (hd : ∀ κ, Joint P n d κ) :
    ∃ c : C (n + 1), ∀ κ, Joint P (n + 1) (upd n d c) κ := by
  by_contra hbad
  push Not at hbad
  let κc : C (n + 1) → Cardinal.{u} := fun c => Classical.choose (hbad c)
  have hκc : ∀ c, ¬ Joint P (n + 1) (upd n d c) (κc c) :=
    fun c => Classical.choose_spec (hbad c)
  let ν : Cardinal.{u} := Order.succ (max aleph0 (sum κc))
  have hν : aleph0 ≤ ν := (le_max_left _ _).trans (Order.le_succ _)
  let ξ : Cardinal.{u} := #(C (n + 1) ⊕ ULift.{u} ℕ)
  have hξ : aleph0 ≤ ξ := by
    have : #(ULift.{u} ℕ) ≤ ξ :=
      mk_le_of_injective (f := fun e : ULift.{u} ℕ => (Sum.inr e : C (n + 1) ⊕ ULift.{u} ℕ))
        Sum.inr_injective
    simpa using this
  let R := recursivePartitionBound (n + 1) ξ ν
  obtain ⟨S, hPS, hbig, hhom⟩ := hd (max R ν)
  have hαR : R ≤ #S.α := (le_max_left R ν).trans hbig
  let color : {s : Finset S.α // s.card = n + 1} → C (n + 1) ⊕ ULift.{u} ℕ :=
    fun s => Sum.inl (S.col (n + 1) s.1)
  obtain ⟨H, hH, paint, hpaint⟩ := erdos_color hξ hν (Nat.succ_pos n) hαR rfl color
  have hHinf : H.Infinite := aleph0_le_mk_set.mp (hν.trans hH)
  obtain ⟨t0, ht0sub, ht0card⟩ := Set.Infinite.exists_subset_card_eq (s := H) hHinf (n + 1)
  have hpaint0 : color ⟨t0, ht0card⟩ = paint := hpaint t0 ht0card fun x hx => ht0sub hx
  cases paint with
  | inr e =>
      have : (Sum.inl (S.col (n + 1) t0) : C (n + 1) ⊕ ULift.{u} ℕ) = Sum.inr e := hpaint0
      cases this
  | inl c =>
      apply hκc c
      refine ⟨S.restrict H, hres S H hPS, ?_, ?_⟩
      · have : κc c ≤ #H :=
          ((le_sum_apply' κc c).trans (le_max_right _ _)).trans (Order.le_succ _) |>.trans hH
        simpa [ColorSample.restrict] using this
      · intro m hm0 hm s hs
        let sα : Finset S.α := s.map (Function.Embedding.subtype (· ∈ H))
        have hsα : sα.card = m := (Finset.card_map _).trans hs
        show S.col m sα = _
        by_cases hle : m ≤ n
        · rw [upd_of_le d c hm0 hle]
          exact hhom m hm0 hle sα hsα
        · have hmeq : m = n + 1 := by omega
          subst hmeq
          rw [upd_self]
          have hsub : ∀ x ∈ sα, x ∈ H := by
            intro x hx
            obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
            rw [← hy]
            exact y.2
          have : color ⟨sα, hsα⟩ = Sum.inl c := hpaint sα hsα hsub
          simpa [color] using this

/-- Colors through arity `n` with arbitrarily large homogeneous samples. -/
structure Tower (n : ℕ) where
  d : (m : ℕ) → 0 < m → C m
  good : ∀ κ, Joint P n d κ

variable {P}

theorem joint_zero (hlarge : ∀ κ : Cardinal.{u}, ∃ S, P S ∧ κ ≤ #S.α)
    (d : (m : ℕ) → 0 < m → C m) (κ : Cardinal.{u}) : Joint P 0 d κ := by
  obtain ⟨S, hS, hκ⟩ := hlarge κ
  exact ⟨S, hS, hκ, fun m hm0 hm => absurd hm (by omega)⟩

variable (hres : ∀ S (H : Set S.α), P S → P (S.restrict H))
  (hlarge : ∀ κ : Cardinal.{u}, ∃ S, P S ∧ κ ≤ #S.α)

/-- Arbitrary default colors, read off some sample. -/
noncomputable def junk : (m : ℕ) → 0 < m → C m :=
  fun m _ => (Classical.choose (hlarge 0)).col m ∅

/-- The tower of coherent colors (the analogue of Section 2's `colorTower`). -/
noncomputable def tower : (n : ℕ) → Tower P n
  | 0 => ⟨junk hlarge, joint_zero hlarge _⟩
  | n + 1 =>
      let T := tower n
      let c := Classical.choose (exists_extend P hres T.d T.good)
      ⟨upd n T.d c, Classical.choose_spec (exists_extend P hres T.d T.good)⟩

theorem tower_stable {m : ℕ} (hm0 : 0 < m) :
    ∀ n, m ≤ n → (tower hres hlarge n).d m hm0 = (tower hres hlarge m).d m hm0 := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_ge n m with h | h
      · have : m = n + 1 := by omega
        subst this
        rfl
      · show upd n _ _ m hm0 = _
        rw [upd_of_le _ _ hm0 h]
        exact ih h

include hres hlarge in
/-- **Generic coherent color extraction.**  For any family of colored samples closed under
thinning to index subsets and containing arbitrarily large samples, there are colors at all
positive arities such that, for every arity bound `n` and every size `κ`, some admissible
sample of size at least `κ` is homogeneous for those colors through arity `n`.  This is the
combinatorial core of the extraction in Theorem 2.6, reused by Lemma 8.3. -/
theorem coherent_colors :
    ∃ c : (m : ℕ) → 0 < m → C m, ∀ (n : ℕ) (κ : Cardinal.{u}), Joint P n c κ := by
  refine ⟨fun m hm0 => (tower hres hlarge m).d m hm0, ?_⟩
  intro n κ
  obtain ⟨S, hS, hκ, hhom⟩ := (tower hres hlarge n).good κ
  refine ⟨S, hS, hκ, ?_⟩
  intro m hm0 hm s hs
  rw [hhom m hm0 hm s hs]
  exact tower_stable hres hlarge hm0 n hm


/-- Reindexing a sample along an order embedding of index orders. -/
def ColorSample.reindex (S : ColorSample C) {β : Type u} [LinearOrder β] (e : β ↪o S.α) :
    ColorSample C where
  α := β
  col m s := S.col m (s.map e.toEmbedding)

/-- Homogeneity survives reindexing along order embeddings: an `I`-indexed copy of a
homogeneous sample, for any order `I` embedding into its index order, has the same colors.
This is how the extracted colors are read on the index orders `J_H`, `W_H` of the template. -/
theorem Homog.reindex {S : ColorSample C} {n : ℕ} {d : (m : ℕ) → 0 < m → C m}
    (h : Homog S n d) {β : Type u} [LinearOrder β] (e : β ↪o S.α) :
    Homog (S.reindex e) n d := fun m hm0 hm s hs =>
  h m hm0 hm (s.map e.toEmbedding) ((Finset.card_map _).trans hs)

/-- Restriction is reindexing along the inclusion. -/
theorem ColorSample.restrict_eq_reindex (S : ColorSample C) (H : Set S.α) :
    S.restrict H = S.reindex (OrderEmbedding.subtype (· ∈ H)) := rfl


/-- **Coherence of the extracted colors.**  If the colors of sub-tuples are computed from the
color of a tuple by restriction maps `res` (as the finite-hull diagram of a sub-tuple is read
off the diagram of the tuple), then the extracted colors are coherent: the arity-`m'` color is
the restriction of the arity-`m` color along every increasing `Fin m' ↪o Fin m`.  This is the
compatibility the Ehrenfeucht–Mostowski limit of the template needs. -/
theorem coherent_colors_compat
    (res : ∀ {m m' : ℕ}, (Fin m' ↪o Fin m) → C m → C m')
    (hres : ∀ S, P S → ∀ {m m' : ℕ} (f : Fin m' ↪o Fin m) (s : Finset S.α) (hs : s.card = m),
      S.col m' (Finset.univ.map (f.trans (s.orderEmbOfFin hs)).toEmbedding) =
        res f (S.col m s))
    {c : (m : ℕ) → 0 < m → C m} (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint P n c κ)
    {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m) :
    c m' hm' = res f (c m hm) := by
  have hmm : m' ≤ m := by simpa using Fintype.card_le_of_embedding f.toEmbedding
  obtain ⟨S, hPS, hκ, hhom⟩ := hc m (m : Cardinal.{u})
  obtain ⟨s, hs⟩ : ∃ s : Finset S.α, s.card = m := by
    obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hκ
    have hfin : t.Finite :=
      Cardinal.lt_aleph0_iff_set_finite.mp (by rw [ht]; exact Cardinal.natCast_lt_aleph0)
    refine ⟨hfin.toFinset, ?_⟩
    have h1 : #(↥(hfin.toFinset : Set S.α)) = (hfin.toFinset.card : Cardinal) :=
      Cardinal.mk_coe_finset
    rw [Set.Finite.coe_toFinset, ht] at h1
    exact_mod_cast h1.symm
  have hsub : (Finset.univ.map (f.trans (s.orderEmbOfFin hs)).toEmbedding).card = m' := by
    simp
  rw [← hhom m' hm' hmm _ hsub, hres S hPS f s hs, hhom m _ le_rfl s hs]

end Hull83
end AEC
