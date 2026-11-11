module

public import AEC.Section4.BlockInterchange

@[expose] public section

/-!
# Off-hit copies as disjoint block interchanges

English Lemma 6.1, second sentence: natural diagrams are unchanged by simultaneous disjoint
block transpositions. In Lean that sentence is `lemma_4_6`. The orbit bound
`WorkingScheme.exists_parameter_orbit_reps` does not identify two diagrams.

`CopyInterchange` is the order data. Each cluster is one block, and the parameters it passes
are the other block of that region. Distinct slots do not share a crossed parameter, so the
transpositions are simultaneous.
-/

namespace AEC

open Cardinal

universe u

variable {Cl Parm Amb Slot : Type u}
  [LinearOrder Cl] [LinearOrder Parm] [LinearOrder Amb] [LinearOrder Slot]

/-- Placements of one tuple, the original and the copy, against a fixed list of parameter
positions. -/
structure CopyInterchange (Cl Parm Amb Slot : Type u)
    [LinearOrder Cl] [LinearOrder Parm] [LinearOrder Amb] [LinearOrder Slot] where
  embCl : Cl ↪o Amb
  embCopy : Cl ↪o Amb
  embParm : Parm ↪o Amb
  slot : Cl → Slot
  slot_mono : Monotone slot
  slot_reflect : ∀ {c₁ c₂}, slot c₁ < slot c₂ → c₁ < c₂
  disjCl : ∀ c p, embCl c ≠ embParm p
  disjCopy : ∀ c p, embCopy c ≠ embParm p
  blockOrig : ∀ {c₁ c₂}, slot c₁ = slot c₂ → ∀ p,
    embParm p < embCl c₁ ↔ embParm p < embCl c₂
  blockCopy : ∀ {c₁ c₂}, slot c₁ = slot c₂ → ∀ p,
    embParm p < embCopy c₁ ↔ embParm p < embCopy c₂
  stable : ∀ c₁ c₂ p,
    (embParm p < embCl c₁) ≠ (embParm p < embCopy c₁) →
    slot c₁ ≠ slot c₂ →
    (embParm p < embCl c₂ ↔ embParm p < embCopy c₂)

namespace CopyInterchange

variable (X : CopyInterchange Cl Parm Amb Slot)

def leftOrig (c : Cl) (p : Parm) : Prop := X.embParm p < X.embCl c

def leftCopy (c : Cl) (p : Parm) : Prop := X.embParm p < X.embCopy c

/-- `p` lies on different sides of `c` in the original order and in the copy. -/
def crosses (c : Cl) (p : Parm) : Prop := X.leftOrig c p ≠ X.leftCopy c p

theorem not_leftOrig_iff {c p} : ¬ X.leftOrig c p ↔ X.embCl c < X.embParm p := by
  constructor
  · intro h
    rcases lt_trichotomy (X.embCl c) (X.embParm p) with hlt | heq | hgt
    · exact hlt
    · exact (X.disjCl c p heq).elim
    · exact absurd hgt h
  · intro h hleft
    exact lt_asymm h hleft

theorem not_leftCopy_iff {c p} : ¬ X.leftCopy c p ↔ X.embCopy c < X.embParm p := by
  constructor
  · intro h
    rcases lt_trichotomy (X.embCopy c) (X.embParm p) with hlt | heq | hgt
    · exact hlt
    · exact (X.disjCopy c p heq).elim
    · exact absurd hgt h
  · intro h hleft
    exact lt_asymm h hleft

theorem leftCopy_of_cross_right {c p} (h : X.crosses c p) (hn : ¬ X.leftOrig c p) :
    X.leftCopy c p := by
  by_contra hc
  exact h (propext (iff_of_false hn hc))

theorem not_leftCopy_of_cross_left {c p} (h : X.crosses c p) (hl : X.leftOrig c p) :
    ¬ X.leftCopy c p := by
  intro hc
  exact h (propext (iff_of_true hl hc))

theorem blockOrig_lt {c₁ c₂} (hs : X.slot c₁ = X.slot c₂) (p) :
    X.embCl c₁ < X.embParm p ↔ X.embCl c₂ < X.embParm p := by
  rw [← X.not_leftOrig_iff, ← X.not_leftOrig_iff]
  exact not_congr (X.blockOrig hs p)

theorem blockCopy_lt {c₁ c₂} (hs : X.slot c₁ = X.slot c₂) (p) :
    X.embCopy c₁ < X.embParm p ↔ X.embCopy c₂ < X.embParm p := by
  rw [← X.not_leftCopy_iff, ← X.not_leftCopy_iff]
  exact not_congr (X.blockCopy hs p)

theorem crosses_slot {c₁ c₂} (hs : X.slot c₁ = X.slot c₂) {p} :
    X.crosses c₁ p ↔ X.crosses c₂ p := by
  simp only [crosses, leftOrig, leftCopy, X.blockOrig hs, X.blockCopy hs]

theorem stable_of_cross {c₁ c₂ p} (h : X.crosses c₁ p) (hs : X.slot c₁ ≠ X.slot c₂) :
    ¬ X.crosses c₂ p := by
  intro h₂
  have hne : (X.embParm p < X.embCl c₁) ≠ (X.embParm p < X.embCopy c₁) := by
    simpa [crosses, leftOrig, leftCopy] using h
  apply h₂
  apply propext
  simpa [leftOrig, leftCopy] using X.stable c₁ c₂ p hne hs

theorem crosses_same_side {c p q} (hp : X.crosses c p) (hq : X.crosses c q) :
    X.leftOrig c p ↔ X.leftOrig c q := by
  by_cases hpL : X.leftOrig c p <;> by_cases hqL : X.leftOrig c q
  · exact iff_of_true hpL hqL
  · have hpq : X.embParm p < X.embParm q := hpL.trans ((X.not_leftOrig_iff).mp hqL)
    have hcq : X.embParm q < X.embCopy c := X.leftCopy_of_cross_right hq hqL
    have hcp : X.embCopy c < X.embParm p :=
      (X.not_leftCopy_iff).mp (X.not_leftCopy_of_cross_left hp hpL)
    exact absurd hpq (lt_asymm (hcq.trans hcp))
  · have hqp : X.embParm q < X.embParm p := hqL.trans ((X.not_leftOrig_iff).mp hpL)
    have hcp : X.embParm p < X.embCopy c := X.leftCopy_of_cross_right hp hpL
    have hcq : X.embCopy c < X.embParm q :=
      (X.not_leftCopy_iff).mp (X.not_leftCopy_of_cross_left hq hqL)
    exact absurd hqp (lt_asymm (hcp.trans hcq))
  · exact iff_of_false hpL hqL

theorem slot_le_of_lt {c₁ c₂} (h : c₁ < c₂) : X.slot c₁ ≤ X.slot c₂ :=
  X.slot_mono h.le

theorem slot_lt_of_lt_of_ne {c₁ c₂} (h : c₁ < c₂) (hne : X.slot c₁ ≠ X.slot c₂) :
    X.slot c₁ < X.slot c₂ := by
  rcases (X.slot_le_of_lt h).lt_or_eq with hlt | heq
  · exact hlt
  · exact absurd heq hne

/-- A crossed parameter lies strictly left of every later cluster. -/
theorem parm_lt_later {c c' p} (h : X.crosses c p) (hs : X.slot c < X.slot c') :
    X.embParm p < X.embCl c' := by
  have hc : c < c' := X.slot_reflect hs
  by_cases hL : X.leftOrig c p
  · exact hL.trans ((X.embCl.lt_iff_lt).mpr hc)
  · have hp_copy : X.embParm p < X.embCopy c := X.leftCopy_of_cross_right h hL
    have hp_copy' : X.embParm p < X.embCopy c' :=
      hp_copy.trans ((X.embCopy.lt_iff_lt).mpr hc)
    by_contra hnot
    have hcross' : X.crosses c' p := by
      intro heq
      exact hnot (cast heq.symm hp_copy')
    exact X.stable_of_cross h (ne_of_lt hs) hcross'

/-- A crossed parameter lies strictly right of every earlier cluster. -/
theorem earlier_lt_parm {c c' p} (h : X.crosses c p) (hs : X.slot c' < X.slot c) :
    X.embCl c' < X.embParm p := by
  have hc : c' < c := X.slot_reflect hs
  by_cases hL : X.leftOrig c p
  · have hcopy' : X.embCopy c' < X.embParm p :=
      ((X.embCopy.lt_iff_lt).mpr hc).trans
        ((X.not_leftCopy_iff).mp (X.not_leftCopy_of_cross_left h hL))
    by_contra hnot
    have hLc' : X.leftOrig c' p := by
      rcases lt_trichotomy (X.embParm p) (X.embCl c') with hlt | heq | hgt
      · exact hlt
      · exact (X.disjCl c' p heq.symm).elim
      · exact absurd hgt hnot
    have hcross' : X.crosses c' p := by
      intro heq
      exact ((X.not_leftCopy_iff).mpr hcopy') (cast heq hLc')
    exact X.stable_of_cross h (Ne.symm (ne_of_lt hs)) hcross'
  · exact ((X.embCl.lt_iff_lt).mpr hc).trans ((X.not_leftOrig_iff).mp hL)

/-- A parameter strictly between a crossed parameter and its cluster is crossed as well. -/
theorem between_crosses_left {c p q} (h : X.crosses c p) (hL : X.leftOrig c p)
    (hpq : X.embParm p < X.embParm q) (hqc : X.embParm q < X.embCl c) :
    X.crosses c q := by
  have hcopy : X.embCopy c < X.embParm q :=
    ((X.not_leftCopy_iff).mp (X.not_leftCopy_of_cross_left h hL)).trans hpq
  intro heq
  exact ((X.not_leftCopy_iff).mpr hcopy) (cast heq hqc)

theorem between_crosses_right {c p q} (h : X.crosses c p) (hn : ¬ X.leftOrig c p)
    (hcq : X.embCl c < X.embParm q) (hqp : X.embParm q < X.embParm p) :
    X.crosses c q := by
  have hcopy : X.embParm q < X.embCopy c := hqp.trans (X.leftCopy_of_cross_right h hn)
  intro heq
  exact ((X.not_leftOrig_iff).mpr hcq) (cast heq.symm hcopy)

theorem orders_swap_of_cross {c p} (h : X.crosses c p) :
    X.leftOrig c p ↔ ¬ X.leftCopy c p := by
  constructor
  · exact X.not_leftCopy_of_cross_left h
  · intro hn
    by_contra hL
    exact h (propext (iff_of_false hL hn))

theorem orders_agree_of_not_cross {c p} (h : ¬ X.crosses c p) :
    X.leftOrig c p ↔ X.leftCopy c p := by
  constructor
  · intro hL
    by_contra hn
    exact h (fun heq => hn (cast heq hL))
  · intro hC
    by_contra hn
    exact h (fun heq => hn (cast heq.symm hC))

theorem not_left_agree_of_not_cross {c p} (h : ¬ X.crosses c p) :
    X.embCl c < X.embParm p ↔ X.embCopy c < X.embParm p := by
  rw [← X.not_leftOrig_iff, ← X.not_leftCopy_iff]
  exact not_congr (X.orders_agree_of_not_cross h)

variable [Nonempty Cl]

/-- One representative cluster point of each slot. -/
noncomputable def repOf (c : Cl) : Cl :=
  Classical.epsilon fun c' => X.slot c' = X.slot c

theorem repOf_spec (c : Cl) : X.slot (X.repOf c) = X.slot c :=
  Classical.epsilon_spec_aux inferInstance (fun c' => X.slot c' = X.slot c) ⟨c, rfl⟩

theorem repOf_congr {c₁ c₂ : Cl} (h : X.slot c₁ = X.slot c₂) : X.repOf c₁ = X.repOf c₂ := by
  simp only [repOf]
  have hpred : (fun c' => X.slot c' = X.slot c₁) = (fun c' => X.slot c' = X.slot c₂) := by
    funext c'
    exact propext ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩
  rw [hpred]

theorem rep_emb_lt {c₁ c₂ : Cl} (h : X.slot c₁ < X.slot c₂) :
    X.embCl (X.repOf c₁) < X.embCl (X.repOf c₂) := by
  have hslot : X.slot (X.repOf c₁) < X.slot (X.repOf c₂) := by
    simpa only [repOf_spec] using h
  exact (X.embCl.lt_iff_lt).mpr (X.slot_reflect hslot)

theorem choose_slot_unique {c₁ c₂ p} (h₁ : X.crosses c₁ p) (h₂ : X.crosses c₂ p) :
    X.slot c₁ = X.slot c₂ := by
  by_contra hne
  exact X.stable_of_cross h₁ hne h₂

noncomputable def chooseCross (p : Parm) (h : ∃ c, X.crosses c p) : Cl :=
  Classical.choose h

theorem chooseCross_spec (p : Parm) (h : ∃ c, X.crosses c p) :
    X.crosses (X.chooseCross p h) p :=
  Classical.choose_spec h

/-- Original position of a cluster point or a parameter. -/
def sumOrig (v : Cl ⊕ Parm) : Amb :=
  match v with
  | Sum.inl c => X.embCl c
  | Sum.inr p => X.embParm p

/-- Position after the clusters have moved to the copy. Parameters stay. -/
def sumCopy (v : Cl ⊕ Parm) : Amb :=
  match v with
  | Sum.inl c => X.embCopy c
  | Sum.inr p => X.embParm p

@[simp] theorem sumOrig_inl (c : Cl) : X.sumOrig (Sum.inl c) = X.embCl c := rfl

@[simp] theorem sumOrig_inr (p : Parm) : X.sumOrig (Sum.inr p) = X.embParm p := rfl

@[simp] theorem sumCopy_inl (c : Cl) : X.sumCopy (Sum.inl c) = X.embCopy c := rfl

@[simp] theorem sumCopy_inr (p : Parm) : X.sumCopy (Sum.inr p) = X.embParm p := rfl

theorem sumOrig_injective : Function.Injective (X.sumOrig) := by
  intro v w h
  cases v with
  | inl c =>
    cases w with
    | inl c' =>
      simp only [sumOrig] at h
      exact congrArg Sum.inl (X.embCl.injective h)
    | inr p =>
      simp only [sumOrig] at h
      exact (X.disjCl c p h).elim
  | inr p =>
    cases w with
    | inl c =>
      simp only [sumOrig] at h
      exact (X.disjCl c p h.symm).elim
    | inr q =>
      simp only [sumOrig] at h
      exact congrArg Sum.inr (X.embParm.injective h)

theorem sumCopy_injective : Function.Injective (X.sumCopy) := by
  intro v w h
  cases v with
  | inl c =>
    cases w with
    | inl c' =>
      simp only [sumCopy] at h
      exact congrArg Sum.inl (X.embCopy.injective h)
    | inr p =>
      simp only [sumCopy] at h
      exact (X.disjCopy c p h).elim
  | inr p =>
    cases w with
    | inl c =>
      simp only [sumCopy] at h
      exact (X.disjCopy c p h.symm).elim
    | inr q =>
      simp only [sumCopy] at h
      exact congrArg Sum.inr (X.embParm.injective h)

/-- Joint support in the original order. -/
@[ext]
structure Src (X : CopyInterchange Cl Parm Amb Slot) where
  val : Cl ⊕ Parm

/-- The same support, ordered as in the copy. -/
@[ext]
structure Dst (X : CopyInterchange Cl Parm Amb Slot) where
  val : Cl ⊕ Parm

instance : LinearOrder (Src X) :=
  LinearOrder.lift' (fun s : Src X => X.sumOrig s.val)
    (fun a b h => Src.ext (X.sumOrig_injective h))

instance : LinearOrder (Dst X) :=
  LinearOrder.lift' (fun d : Dst X => X.sumCopy d.val)
    (fun a b h => Dst.ext (X.sumCopy_injective h))

theorem src_lt_iff (x y : Src X) : x < y ↔ X.sumOrig x.val < X.sumOrig y.val := by
  rfl

theorem dst_lt_iff (x y : Dst X) : x < y ↔ X.sumCopy x.val < X.sumCopy y.val := by
  rfl

/-- Original positions of the joint support, in the ambient order. -/
def srcEmb : Src X ↪o Amb :=
  OrderEmbedding.ofStrictMono (fun s => X.sumOrig s.val)
    (fun a b hab => (X.src_lt_iff a b).mp hab)

/-- Copy positions of the joint support, in the ambient order. Parameters stay. -/
def dstEmb : Dst X ↪o Amb :=
  OrderEmbedding.ofStrictMono (fun d => X.sumCopy d.val)
    (fun a b hab => (X.dst_lt_iff a b).mp hab)

@[simp] theorem srcEmb_apply (s : Src X) : X.srcEmb s = X.sumOrig s.val := rfl

@[simp] theorem dstEmb_apply (d : Dst X) : X.dstEmb d = X.sumCopy d.val := rfl

def srcDstEquiv : Src X ≃ Dst X where
  toFun s := ⟨s.val⟩
  invFun d := ⟨d.val⟩
  left_inv s := by cases s; rfl
  right_inv d := by cases d; rfl

@[simp] theorem srcDstEquiv_val (s : Src X) : (X.srcDstEquiv s).val = s.val := rfl

noncomputable def keyCl (c : Cl) : Amb := X.embCl (X.repOf c)

noncomputable def keyParm (p : Parm) : Amb :=
  @dite _ (∃ c, X.crosses c p) (Classical.propDecidable _)
    (fun h => X.keyCl (X.chooseCross p h)) (fun _ => X.embParm p)

theorem keyParm_pos {p : Parm} (h : ∃ c, X.crosses c p) :
    X.keyParm p = X.keyCl (X.chooseCross p h) := by
  unfold keyParm
  rw [dite_eq_left (h := Classical.propDecidable _) h]

theorem keyParm_neg {p : Parm} (h : ¬ ∃ c, X.crosses c p) :
    X.keyParm p = X.embParm p := by
  unfold keyParm
  rw [dite_eq_right (h := Classical.propDecidable _) h]

theorem keyCl_le_keyCl {c c' : Cl} (h : X.embCl c < X.embCl c') :
    X.keyCl c ≤ X.keyCl c' := by
  have hc : c < c' := (X.embCl.lt_iff_lt).mp h
  by_cases hs : X.slot c = X.slot c'
  · exact le_of_eq (congrArg X.embCl (X.repOf_congr hs))
  · exact (X.rep_emb_lt (X.slot_lt_of_lt_of_ne hc hs)).le

theorem keyCl_le_keyParm {c : Cl} {p : Parm} (h : X.embCl c < X.embParm p) :
    X.keyCl c ≤ X.keyParm p := by
  by_cases hp : ∃ c', X.crosses c' p
  · rw [X.keyParm_pos hp]
    set c' := X.chooseCross p hp
    have hcr : X.crosses c' p := X.chooseCross_spec p hp
    have hsle : X.slot c ≤ X.slot c' := by
      by_contra hbad
      exact lt_asymm h (X.parm_lt_later hcr (not_le.mp hbad))
    rcases hsle.lt_or_eq with hlt | heq
    · exact (X.rep_emb_lt hlt).le
    · exact le_of_eq (congrArg X.embCl (X.repOf_congr heq))
  · rw [X.keyParm_neg hp]
    exact ((X.blockOrig_lt (X.repOf_spec c).symm p).mp h).le

theorem keyParm_le_keyCl {p : Parm} {c : Cl} (h : X.embParm p < X.embCl c) :
    X.keyParm p ≤ X.keyCl c := by
  by_cases hp : ∃ c', X.crosses c' p
  · rw [X.keyParm_pos hp]
    set c' := X.chooseCross p hp
    have hcr : X.crosses c' p := X.chooseCross_spec p hp
    have hsle : X.slot c' ≤ X.slot c := by
      by_contra hbad
      exact lt_asymm h (X.earlier_lt_parm hcr (not_le.mp hbad))
    rcases hsle.lt_or_eq with hlt | heq
    · exact (X.rep_emb_lt hlt).le
    · exact le_of_eq (congrArg X.embCl (X.repOf_congr heq))
  · rw [X.keyParm_neg hp]
    exact ((X.blockOrig (X.repOf_spec c).symm p).mp h).le

theorem keyParm_le_keyParm {p q : Parm} (h : X.embParm p < X.embParm q) :
    X.keyParm p ≤ X.keyParm q := by
  by_cases hp : ∃ c, X.crosses c p <;> by_cases hq : ∃ c, X.crosses c q
  · rw [X.keyParm_pos hp, X.keyParm_pos hq]
    set cp := X.chooseCross p hp
    set cq := X.chooseCross q hq
    have hcp : X.crosses cp p := X.chooseCross_spec p hp
    have hcq : X.crosses cq q := X.chooseCross_spec q hq
    rcases lt_trichotomy (X.slot cp) (X.slot cq) with hlt | heq | hgt
    · exact (X.rep_emb_lt hlt).le
    · exact le_of_eq (congrArg X.embCl (X.repOf_congr heq))
    · exfalso
      have hq_left : X.embParm q < X.embCl cp := X.parm_lt_later hcq hgt
      have hpL : X.leftOrig cp p := lt_trans h hq_left
      exact X.stable_of_cross hcq (ne_of_lt hgt)
        (X.between_crosses_left hcp hpL h hq_left)
  · rw [X.keyParm_pos hp, X.keyParm_neg hq]
    set c := X.chooseCross p hp
    have hc : X.crosses c p := X.chooseCross_spec p hp
    by_cases hL : X.leftOrig c p
    · have hqc : X.embCl c < X.embParm q := by
        rcases lt_trichotomy (X.embParm q) (X.embCl c) with hlt | heq | hgt
        · exact (hq ⟨c, X.between_crosses_left hc hL h hlt⟩).elim
        · exact (X.disjCl c q heq.symm).elim
        · exact hgt
      exact ((X.blockOrig_lt (X.repOf_spec c) q).mpr hqc).le
    · have hcp : X.embCl c < X.embParm p := (X.not_leftOrig_iff).mp hL
      exact (((X.blockOrig_lt (X.repOf_spec c) p).mpr hcp).trans h).le
  · rw [X.keyParm_neg hp, X.keyParm_pos hq]
    set c := X.chooseCross q hq
    have hc : X.crosses c q := X.chooseCross_spec q hq
    by_cases hL : X.leftOrig c q
    · exact ((X.blockOrig (X.repOf_spec c).symm p).mp (h.trans hL)).le
    · have hpc : X.embParm p < X.embCl c := by
        have hnot : ¬ X.embCl c < X.embParm p := by
          intro hlt
          exact hp ⟨c, X.between_crosses_right hc hL hlt h⟩
        rcases lt_trichotomy (X.embParm p) (X.embCl c) with hlt | heq | hgt
        · exact hlt
        · exact (X.disjCl c p heq.symm).elim
        · exact absurd hgt hnot
      exact ((X.blockOrig (X.repOf_spec c).symm p).mp hpc).le
  · rw [X.keyParm_neg hp, X.keyParm_neg hq]
    exact h.le

noncomputable def key (s : Src X) : Amb :=
  match s.val with
  | Sum.inl c => X.keyCl c
  | Sum.inr p => X.keyParm p

theorem key_inl (c : Cl) : X.key ⟨Sum.inl c⟩ = X.keyCl c := rfl

theorem key_inr_pos {p : Parm} (h : ∃ c, X.crosses c p) :
    X.key ⟨Sum.inr p⟩ = X.keyCl (X.chooseCross p h) := by
  simp only [key]
  exact X.keyParm_pos h

theorem key_inr_neg {p : Parm} (h : ¬ ∃ c, X.crosses c p) :
    X.key ⟨Sum.inr p⟩ = X.embParm p := by
  simp only [key]
  exact X.keyParm_neg h

theorem key_mono : Monotone (X.key) := by
  intro x y hxy
  rcases lt_or_eq_of_le hxy with hlt | rfl
  · rw [src_lt_iff] at hlt
    rcases x with ⟨vx⟩
    rcases y with ⟨vy⟩
    cases vx with
    | inl c =>
      cases vy with
      | inl c' =>
        simpa [key, sumOrig] using X.keyCl_le_keyCl hlt
      | inr p =>
        simpa [key, sumOrig] using X.keyCl_le_keyParm hlt
    | inr p =>
      cases vy with
      | inl c =>
        simpa [key, sumOrig] using X.keyParm_le_keyCl hlt
      | inr q =>
        simpa [key, sumOrig] using X.keyParm_le_keyParm hlt
  · rfl

/-- Cluster points: the blocks used by the tuple. -/
def firstSet : Set (Src X) := fun s => ∃ c, s.val = Sum.inl c

/-- Parameters that pass a cluster: the blocks used only on the other side of the copy. -/
def secondSet : Set (Src X) := fun s => ∃ p, s.val = Sum.inr p ∧ ∃ c, X.crosses c p

/-- Slots whose cluster sits to the right of the parameters it passes. -/
def firstOnRightSet : Set Amb :=
  fun r => ∃ c, r = X.keyCl c ∧ ∃ p, X.crosses c p ∧ X.leftOrig c p

theorem key_of_region {x : Src X} (hx : x ∈ X.firstSet ∪ X.secondSet) :
    ∃ c, X.key x = X.keyCl c := by
  rcases hx with ⟨c, hxc⟩ | ⟨p, hxp, h⟩
  · have hx' : x = ⟨Sum.inl c⟩ := Src.ext hxc
    subst hx'
    exact ⟨c, X.key_inl c⟩
  · have hx' : x = ⟨Sum.inr p⟩ := Src.ext hxp
    subst hx'
    exact ⟨X.chooseCross p h, X.key_inr_pos h⟩

theorem rep_eq_of_same_key {c p} (hp : ∃ c', X.crosses c' p)
    (hkey : X.key ⟨Sum.inl c⟩ = X.key ⟨Sum.inr p⟩) :
    X.repOf c = X.repOf (X.chooseCross p hp) := by
  apply X.embCl.injective
  have hkeys : X.keyCl c = X.keyCl (X.chooseCross p hp) := by
    rw [← X.key_inl, ← X.key_inr_pos hp]
    exact hkey
  simpa [keyCl] using hkeys

noncomputable def regions : BlockRegions (Src X) where
  Region := Amb
  key := X.key
  key_mono := X.key_mono
  first := X.firstSet
  second := X.secondSet
  firstOnRight := X.firstOnRightSet
  blocks_ordered := by
    intro x hx y hy hkey
    obtain ⟨c, hxc⟩ := hx
    obtain ⟨p, hyp, hp⟩ := hy
    have hx' : x = ⟨Sum.inl c⟩ := Src.ext hxc
    have hy' : y = ⟨Sum.inr p⟩ := Src.ext hyp
    subst hx' hy'
    have hcross : X.crosses c p := by
      have hspec : X.crosses (X.chooseCross p hp) p := X.chooseCross_spec p hp
      have hreps : X.repOf c = X.repOf (X.chooseCross p hp) :=
        X.rep_eq_of_same_key hp hkey
      have hslot : X.slot c = X.slot (X.chooseCross p hp) := by
        rw [← X.repOf_spec c, ← X.repOf_spec (X.chooseCross p hp), hreps]
      exact (X.crosses_slot hslot).mpr hspec
    refine ⟨?_, ?_⟩
    · intro hon
      obtain ⟨c0, hkey0, p0, hcross0, hL0⟩ := hon
      have hreps : X.repOf c = X.repOf c0 := X.embCl.injective (by
        have hkeys : X.keyCl c = X.keyCl c0 := (X.key_inl c).symm.trans hkey0
        simpa [keyCl] using hkeys)
      have hslot : X.slot c = X.slot c0 := by
        rw [← X.repOf_spec c, ← X.repOf_spec c0, hreps]
      have hcross0' : X.crosses c p0 := (X.crosses_slot hslot).mpr hcross0
      have hL0' : X.leftOrig c p0 := (X.blockOrig hslot p0).mpr hL0
      have hL : X.leftOrig c p := (X.crosses_same_side hcross hcross0').mpr hL0'
      simpa [leftOrig, src_lt_iff, sumOrig] using hL
    · intro hnot
      have hnL : ¬ X.leftOrig c p := by
        intro hL
        exact hnot ⟨c, (X.key_inl c).symm, p, hcross, hL⟩
      simpa [src_lt_iff, sumOrig] using (X.not_leftOrig_iff).mp hnL
  region_blocks := by
    intro x y hkey hx
    rcases y with ⟨vy⟩
    cases vy with
    | inl c =>
      exact Or.inl ⟨c, rfl⟩
    | inr p =>
      by_cases hp : ∃ c, X.crosses c p
      · exact Or.inr ⟨p, rfl, hp⟩
      · obtain ⟨c, hc⟩ := X.key_of_region hx
        have heq : X.embParm p = X.keyCl c := by
          rw [← X.key_inr_neg hp, ← hc]
          exact hkey.symm
        exact (X.disjCl (X.repOf c) p heq.symm).elim

theorem crossed_of_crosses {c p} (h : X.crosses c p) :
    X.regions.Crossed ⟨Sum.inl c⟩ ⟨Sum.inr p⟩ := by
  have hs : X.slot c = X.slot (X.chooseCross p ⟨c, h⟩) :=
    X.choose_slot_unique h (X.chooseCross_spec p ⟨c, h⟩)
  refine ⟨?_, Or.inl ⟨⟨c, rfl⟩, ⟨p, rfl, ⟨c, h⟩⟩⟩⟩
  have hkeys : X.key ⟨Sum.inl c⟩ = X.key ⟨Sum.inr p⟩ := by
    rw [X.key_inl, X.key_inr_pos ⟨c, h⟩, keyCl, keyCl, X.repOf_congr hs]
  simpa [regions] using hkeys

theorem regions_crossed_symm {x y : Src X} (h : X.regions.Crossed x y) :
    X.regions.Crossed y x :=
  ⟨h.1.symm, h.2.elim (fun h12 => Or.inr ⟨h12.2, h12.1⟩) (fun h21 => Or.inl ⟨h21.2, h21.1⟩)⟩

noncomputable def interchange : X.regions.Interchange (Dst X) where
  toEquiv := X.srcDstEquiv
  lt_iff_of_crossed := by
    intro x y hxy
    rw [dst_lt_iff, src_lt_iff]
    simp only [srcDstEquiv_val]
    rcases x with ⟨vx⟩
    rcases y with ⟨vy⟩
    rcases hxy with ⟨hkey, hmem | hmem⟩
    · obtain ⟨c, hxc⟩ := hmem.1
      obtain ⟨p, hyp, hp⟩ := hmem.2
      have hxv : vx = Sum.inl c := hxc
      have hyv : vy = Sum.inr p := hyp
      subst hxv hyv
      have hcross : X.crosses c p := by
        have hspec := X.chooseCross_spec p hp
        have hreps : X.repOf c = X.repOf (X.chooseCross p hp) :=
          X.rep_eq_of_same_key hp (by simpa [regions] using hkey)
        have hslot : X.slot c = X.slot (X.chooseCross p hp) := by
          rw [← X.repOf_spec c, ← X.repOf_spec (X.chooseCross p hp), hreps]
        exact (X.crosses_slot hslot).mpr hspec
      have hswap : X.leftOrig c p ↔ ¬ X.leftCopy c p := X.orders_swap_of_cross hcross
      constructor
      · intro hlt
        exact hswap.mpr ((X.not_leftCopy_iff).mpr hlt)
      · intro hlt
        exact (X.not_leftCopy_iff).mp (hswap.mp hlt)
    · obtain ⟨p, hxp, hp⟩ := hmem.1
      obtain ⟨c, hyc⟩ := hmem.2
      have hxv : vx = Sum.inr p := hxp
      have hyv : vy = Sum.inl c := hyc
      subst hxv hyv
      have hcross : X.crosses c p := by
        have hspec := X.chooseCross_spec p hp
        have hreps : X.repOf c = X.repOf (X.chooseCross p hp) :=
          X.rep_eq_of_same_key hp (by simpa [regions] using hkey.symm)
        have hslot : X.slot c = X.slot (X.chooseCross p hp) := by
          rw [← X.repOf_spec c, ← X.repOf_spec (X.chooseCross p hp), hreps]
        exact (X.crosses_slot hslot).mpr hspec
      have hswap : X.leftOrig c p ↔ ¬ X.leftCopy c p := X.orders_swap_of_cross hcross
      constructor
      · intro hlt
        apply (X.not_leftOrig_iff).mp
        intro hL
        exact (hswap.mp hL) hlt
      · intro hlt
        have hnL : ¬ X.leftOrig c p := (X.not_leftOrig_iff).mpr hlt
        by_contra hnC
        exact hnL (hswap.mpr hnC)
  lt_iff_of_not_crossed := by
    intro x y hnc
    rw [dst_lt_iff, src_lt_iff]
    simp only [srcDstEquiv_val]
    rcases x with ⟨vx⟩
    rcases y with ⟨vy⟩
    cases vx with
    | inl c =>
      cases vy with
      | inl c' =>
        simp only [sumOrig, sumCopy, X.embCl.lt_iff_lt, X.embCopy.lt_iff_lt]
      | inr p =>
        have hcross : ¬ X.crosses c p := by
          intro h
          exact hnc (X.crossed_of_crosses h)
        constructor
        · intro hlt
          exact (X.not_left_agree_of_not_cross hcross).mpr hlt
        · intro hlt
          exact (X.not_left_agree_of_not_cross hcross).mp hlt
    | inr p =>
      cases vy with
      | inl c =>
        have hcross : ¬ X.crosses c p := by
          intro h
          exact hnc (X.regions_crossed_symm (X.crossed_of_crosses h))
        constructor
        · intro hlt
          exact (X.orders_agree_of_not_cross hcross).mpr hlt
        · intro hlt
          exact (X.orders_agree_of_not_cross hcross).mp hlt
      | inr q =>
        simp [sumOrig, sumCopy]

instance : Nonempty (Src X) :=
  ⟨⟨Sum.inl (Classical.choice ‹Nonempty Cl›)⟩⟩

instance : Nonempty (Dst X) :=
  ⟨⟨Sum.inl (Classical.choice ‹Nonempty Cl›)⟩⟩

/-- The joint list after the block interchange: clusters move, parameters stay. -/
noncomputable def movedJoint {lab : Type u} {arity : lab → ℕ} {α β : Type u}
    (t : α → SupportTerm lab arity (Src X))
    (s : β → SupportTerm lab arity (Src X))
    (ht : ∀ a k, (t a).pos k ∉ X.regions.second)
    (hs : ∀ b k, (s b).pos k ∉ X.regions.first) :
    α ⊕ β → SupportTerm lab arity (Dst X) :=
  Sum.elim (fun a => X.interchange.move (t a) (Or.inl (ht a)))
    (fun b => X.interchange.move (s b) (Or.inr (hs b)))

/-- English Lemma 6.1, second sentence: natural diagrams are unchanged by simultaneous
disjoint block transpositions. Each slot is one region, and a parameter crosses at most
one slot, so the transpositions are simultaneous. In Lean that sentence is Lemma 4.6. -/
theorem sameNaturalDiagram (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K]
    (E : OrderPresentation K) (D : StableDiagram K)
    {α β : Type u} (σ : Cardinal.{u}) (hjoint : #(α ⊕ β) ≤ σ) (hσ : ℵ₀ ≤ σ)
    (t : α → SupportTerm E.lab E.arity (Src X))
    (s : β → SupportTerm E.lab E.arity (Src X))
    (ht : ∀ a k, (t a).pos k ∉ X.regions.second)
    (hs : ∀ b k, (s b).pos k ∉ X.regions.first) :
    SameNaturalDiagram K E D σ hjoint (Sum.elim t s)
      (Sum.elim (fun a => X.interchange.move (t a) (Or.inl (ht a)))
        (fun b => X.interchange.move (s b) (Or.inr (hs b)))) :=
  lemma_4_6_blockInterchange K E D σ hjoint hσ t s X.regions X.interchange ht hs

end CopyInterchange

end AEC
