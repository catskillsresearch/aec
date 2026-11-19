module

public import AEC.Section2.Partition
public import Mathlib.Order.PiLex
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Order.WellFoundedSet

/-!
# Lemma 8.3: order saturation of the sample orders

The proof of Lemma 8.3 (`text.md`, "Choose the sample with order saturation above λ. Extend
the partial matches to embeddings of the entire orders J_H, W_H into the respective sample
orders. In a recursion of at most λ steps, each next position specifies an order pattern over
at most λ earlier positions, and sample order saturation realizes it.") uses order saturation
of the sample orders only through this extension property.  Here we define `κ`-order
saturation and prove the extension lemma.
-/

@[expose] public section

namespace AEC
namespace OrderSat83

universe u

open Cardinal

/-- `J` is `κ`-order-saturated: every cut between two sets of size `< κ` is realized. -/
def OrderSaturated (κ : Cardinal.{u}) (J : Type u) [LinearOrder J] : Prop :=
  ∀ A B : Set J, #A < κ → #B < κ → (∀ a ∈ A, ∀ b ∈ B, a < b) →
    ∃ x, (∀ a ∈ A, a < x) ∧ ∀ b ∈ B, x < b

/-- **Extension through order saturation.**  If `J` is `κ`-order-saturated (`κ` infinite) and
`H` is a well-order of size `< κ`, every order embedding of a subset of `H` into `J` extends
to an order embedding of all of `H`: the recursion along `H` realizes, at each new position,
the cut over the earlier images and the prescribed values. -/
theorem extend_strictMono {κ : Cardinal.{u}} (hκ : aleph0 ≤ κ) {J H : Type u}
    [LinearOrder J] [LinearOrder H] [WellFoundedLT H] (hJ : OrderSaturated κ J)
    (hH : #H < κ) (D : Set H) (f : D → J) (hf : StrictMono f) :
    ∃ g : H → J, StrictMono g ∧ ∀ d : D, g d = f d := by
  classical
  have hκ0 : (0 : Cardinal) < κ := aleph0_pos.trans_le hκ
  have : Nonempty J := by
    obtain ⟨x, -⟩ := hJ ∅ ∅ (by simpa using hκ0) (by simpa using hκ0) (by simp)
    exact ⟨x⟩
  let Good : ∀ h : H, (∀ h' : H, h' < h → J) → J → Prop := fun h prev x =>
    (∀ h' (hh : h' < h), prev h' hh < x) ∧ (∀ d : D, (d : H) < h → f d < x) ∧
      (∀ d : D, h < d → x < f d)
  let step : ∀ h : H, (∀ h' : H, h' < h → J) → J := fun h prev =>
    if hD : h ∈ D then f ⟨h, hD⟩
    else if hx : ∃ x, Good h prev x then hx.choose else Classical.arbitrary J
  let g : H → J := (wellFounded_lt (α := H)).fix step
  have hg : ∀ h, g h = step h (fun h' _ => g h') := fun h =>
    (wellFounded_lt (α := H)).fix_eq step h
  have spec : ∀ h : H, (∀ h' < h, g h' < g h) ∧ (∀ d : D, (d : H) < h → f d < g h) ∧
      (∀ d : D, h < d → g h < f d) ∧ (∀ hD : h ∈ D, g h = f ⟨h, hD⟩) := by
    intro h
    induction h using WellFoundedLT.induction with
    | _ h ih =>
      by_cases hD : h ∈ D
      · have hgh : g h = f ⟨h, hD⟩ := by rw [hg]; simp [step, hD]
        refine ⟨?_, ?_, ?_, fun _ => hgh⟩
        · intro h' hh
          rw [hgh]
          exact (ih h' hh).2.2.1 ⟨h, hD⟩ hh
        · intro d hd
          rw [hgh]
          exact hf (show d < ⟨h, hD⟩ from hd)
        · intro d hd
          rw [hgh]
          exact hf (show (⟨h, hD⟩ : D) < d from hd)
      · let A : Set J := Set.range (fun h' : Set.Iio h => g h'.1) ∪
          Set.range (fun d : {d : D // (d : H) < h} => f d.1)
        let B : Set J := Set.range (fun d : {d : D // h < (d : H)} => f d.1)
        have hA : #A < κ := by
          refine (mk_union_le _ _).trans_lt (add_lt_of_lt hκ ?_ ?_)
          · exact mk_range_le.trans_lt ((mk_subtype_le _).trans_lt hH)
          · exact mk_range_le.trans_lt
              (((mk_subtype_le _).trans (mk_subtype_le _)).trans_lt hH)
        have hB : #B < κ := mk_range_le.trans_lt
          (((mk_subtype_le _).trans (mk_subtype_le _)).trans_lt hH)
        have hAB : ∀ a ∈ A, ∀ b ∈ B, a < b := by
          rintro a ha b ⟨d2, rfl⟩
          rcases ha with ⟨h', rfl⟩ | ⟨d1, rfl⟩
          · exact (ih h'.1 h'.2).2.2.1 d2.1 (lt_trans h'.2 d2.2)
          · exact hf (Subtype.coe_lt_coe.mp (lt_trans d1.2 d2.2))
        obtain ⟨x, hxA, hxB⟩ := hJ A B hA hB hAB
        have hx : ∃ x, Good h (fun h' _ => g h') x :=
          ⟨x, fun h' hh => hxA _ (Or.inl ⟨⟨h', hh⟩, rfl⟩),
            fun d hd => hxA _ (Or.inr ⟨⟨d, hd⟩, rfl⟩), fun d hd => hxB _ ⟨⟨d, hd⟩, rfl⟩⟩
        have hgh : g h = hx.choose := by rw [hg]; simp only [step, hD, hx, dite_true, dite_false]
        have hspec := hx.choose_spec
        rw [← hgh] at hspec
        exact ⟨hspec.1, hspec.2.1, hspec.2.2, fun h => absurd h hD⟩
  refine ⟨g, fun a b hab => (spec b).1 a hab, fun d => (spec d).2.2.2 d.2⟩

/-- **Saturation of a lexicographic product with a complete well-order.**  If `I` is a
well-order with a top element and `J₀` is `κ`-order-saturated, then `I ×ₗ J₀` is
`κ`-order-saturated: a cut is realized in the fiber over the least first coordinate of its
upper side (or over `⊤` when the upper side is empty).  Since the working levels have countable
cofinality, this is how saturated orders of the level size are obtained (`I` of the level
size, `J₀` small). -/
theorem orderSaturated_lex {κ : Cardinal.{u}} {I J₀ : Type u} [LinearOrder I] [WellFoundedLT I]
    [OrderTop I] [LinearOrder J₀] (h0 : OrderSaturated κ J₀) :
    OrderSaturated κ (Lex (I × J₀)) := by
  intro A B hA hB hAB
  have hlt : ∀ p q : Lex (I × J₀), p < q ↔ (ofLex p).1 < (ofLex q).1 ∨
      (ofLex p).1 = (ofLex q).1 ∧ (ofLex p).2 < (ofLex q).2 := fun p q =>
    Prod.Lex.toLex_lt_toLex (x := ofLex p) (y := ofLex q)
  obtain ⟨i, hiA, hiB⟩ : ∃ i : I, (∀ a ∈ A, (ofLex a).1 ≤ i) ∧ ∀ b ∈ B, i ≤ (ofLex b).1 := by
    by_cases hB0 : B.Nonempty
    · let FB : Set I := (fun b => (ofLex b).1) '' B
      have hne : FB.Nonempty := hB0.image _
      obtain ⟨b0, hb0, hb0i⟩ := (wellFounded_lt (α := I)).min_mem FB hne
      refine ⟨(wellFounded_lt (α := I)).min FB hne, fun a ha => ?_, fun b hb => ?_⟩
      · rw [← hb0i]
        rcases (hlt a b0).1 (hAB a ha b0 hb0) with h | h
        · exact h.le
        · exact h.1.le
      · exact not_lt.mp ((wellFounded_lt (α := I)).not_lt_min FB ⟨b, hb, rfl⟩)
    · exact ⟨⊤, fun a _ => le_top, fun b hb => absurd ⟨b, hb⟩ hB0⟩
  let A' : Set J₀ := (fun a => (ofLex a).2) '' {a | a ∈ A ∧ (ofLex a).1 = i}
  let B' : Set J₀ := (fun b => (ofLex b).2) '' {b | b ∈ B ∧ (ofLex b).1 = i}
  have hA' : #A' < κ := mk_image_le.trans_lt
    ((mk_le_mk_of_subset (s := {a | a ∈ A ∧ (ofLex a).1 = i}) (t := A) fun x hx => hx.1).trans_lt hA)
  have hB' : #B' < κ := mk_image_le.trans_lt
    ((mk_le_mk_of_subset (s := {b | b ∈ B ∧ (ofLex b).1 = i}) (t := B) fun x hx => hx.1).trans_lt hB)
  have hAB' : ∀ y ∈ A', ∀ z ∈ B', y < z := by
    rintro _ ⟨a, ⟨ha, hai⟩, rfl⟩ _ ⟨b, ⟨hb, hbi⟩, rfl⟩
    rcases (hlt a b).1 (hAB a ha b hb) with h | h
    · exact absurd (hai.trans hbi.symm) h.ne
    · exact h.2
  obtain ⟨y, hyA, hyB⟩ := h0 A' B' hA' hB' hAB'
  refine ⟨toLex (i, y), fun a ha => ?_, fun b hb => ?_⟩
  · rw [hlt]
    rcases (hiA a ha).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hyA _ ⟨a, ⟨ha, h⟩, rfl⟩⟩
  · rw [hlt]
    rcases (hiB b hb).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hyB _ ⟨b, ⟨hb, h.symm⟩, rfl⟩⟩

/-- **Saturation of a lexicographic power.**  Let `ι` be a well-order in which every set of
size `< κ` is strictly bounded, and `V` an order without endpoints in which any two sets
`S ≤ U` of size `< κ` are separated (non-strictly) by a point.  Then `Lex (ι → V)` is
`κ`-order-saturated: below a bound `γ` of all first differences inside `A ∪ B` the realizing
function follows the agreeing elements non-strictly, and at `γ` at most one element of
`A ∪ B` still agrees with it, so a strict step there suffices. -/
theorem orderSaturated_piLex {κ : Cardinal.{u}} (hκ : aleph0 ≤ κ) {ι V : Type u}
    [LinearOrder ι] [WellFoundedLT ι] [LinearOrder V] [NoMaxOrder V] [NoMinOrder V]
    [Nonempty V]
    (hbd : ∀ s : Set ι, #s < κ → ∃ γ, ∀ j ∈ s, j < γ)
    (hint : ∀ S U : Set V, #S < κ → #U < κ → (∀ a ∈ S, ∀ b ∈ U, a ≤ b) →
      ∃ v, (∀ a ∈ S, a ≤ v) ∧ ∀ b ∈ U, v ≤ b) :
    OrderSaturated κ (Lex (ι → V)) := by
  classical
  intro A B hA hB hAB
  have hlt : ∀ x y : Lex (ι → V), x < y ↔ ∃ i, (∀ j < i, x j = y j) ∧ x i < y i :=
    fun _ _ => Iff.rfl
  have hκ0 : (0 : Cardinal) < κ := aleph0_pos.trans_le hκ
  have : Nonempty ι := by
    obtain ⟨γ, -⟩ := hbd ∅ (by simpa using hκ0)
    exact ⟨γ⟩
  -- first differences
  let fd : Lex (ι → V) → Lex (ι → V) → ι := fun p q =>
    if h : ∃ j, p j ≠ q j then (wellFounded_lt (α := ι)).min {j | p j ≠ q j} h
    else Classical.arbitrary ι
  have hfd : ∀ p q : Lex (ι → V), p ≠ q → p (fd p q) ≠ q (fd p q) := by
    intro p q hpq
    have h : ∃ j, p j ≠ q j := by
      by_contra hc
      push Not at hc
      exact hpq (funext hc)
    simp only [fd, h, dite_true]
    exact (wellFounded_lt (α := ι)).min_mem {j | p j ≠ q j} h
  let C : Set (Lex (ι → V)) := A ∪ B
  have hC : #C < κ := (mk_union_le _ _).trans_lt (add_lt_of_lt hκ hA hB)
  let D : Set ι := Set.image2 fd C C
  have hD : #D < κ := by
    refine (mk_image2_le).trans_lt ?_
    exact mul_lt_of_lt hκ hC hC
  obtain ⟨γ, hγ⟩ := hbd D hD
  have hsep : ∀ p ∈ C, ∀ q ∈ C, p ≠ q → ∃ j < γ, p j ≠ q j := fun p hp q hq hpq =>
    ⟨fd p q, hγ _ (Set.mem_image2_of_mem hp hq), hfd p q hpq⟩
  -- the recursion
  let Ag : ∀ β : ι, (∀ j : ι, j < β → V) → Set (Lex (ι → V)) := fun β prev =>
    {a | a ∈ A ∧ ∀ j (h : j < β), a j = prev j h}
  let Bg : ∀ β : ι, (∀ j : ι, j < β → V) → Set (Lex (ι → V)) := fun β prev =>
    {b | b ∈ B ∧ ∀ j (h : j < β), b j = prev j h}
  let step : ∀ β : ι, (∀ j : ι, j < β → V) → V := fun β prev =>
    if β = γ then
      (if h : ∃ v, (∀ a ∈ Ag β prev, a β < v) ∧ ∀ b ∈ Bg β prev, v < b β then h.choose
        else Classical.arbitrary V)
    else
      (if h : ∃ v, (∀ a ∈ Ag β prev, a β ≤ v) ∧ ∀ b ∈ Bg β prev, v ≤ b β then h.choose
        else Classical.arbitrary V)
  let g : ι → V := (wellFounded_lt (α := ι)).fix step
  have hg : ∀ β, g β = step β (fun j _ => g j) := fun β =>
    (wellFounded_lt (α := ι)).fix_eq step β
  -- agreement and the pointwise order
  have hagree : ∀ β, ∀ a ∈ A, ∀ b ∈ B, (∀ j < β, a j = g j) → (∀ j < β, b j = g j) →
      a β ≤ b β := by
    intro β a ha b hb hab hbb
    obtain ⟨i, hi, hlti⟩ := (hlt a b).1 (hAB a ha b hb)
    rcases lt_trichotomy i β with h | h | h
    · exact absurd ((hab i h).trans (hbb i h).symm) hlti.ne
    · exact h ▸ hlti.le
    · exact (hi β h).le
  have hnonstrict : ∀ β, β ≠ γ → (∀ a ∈ A, (∀ j < β, a j = g j) → a β ≤ g β) ∧
      (∀ b ∈ B, (∀ j < β, b j = g j) → g β ≤ b β) := by
    intro β hβ
    have hex : ∃ v, (∀ a ∈ Ag β (fun j _ => g j), a β ≤ v) ∧
        ∀ b ∈ Bg β (fun j _ => g j), v ≤ b β := by
      obtain ⟨v, hv1, hv2⟩ := hint ((fun a : Lex (ι → V) => a β) '' Ag β (fun j _ => g j))
        ((fun b : Lex (ι → V) => b β) '' Bg β (fun j _ => g j))
        (mk_image_le.trans_lt ((mk_le_mk_of_subset
          (s := Ag β (fun j _ => g j)) (t := A) fun x hx => hx.1).trans_lt hA))
        (mk_image_le.trans_lt ((mk_le_mk_of_subset
          (s := Bg β (fun j _ => g j)) (t := B) fun x hx => hx.1).trans_lt hB))
        (by
          rintro _ ⟨a, ⟨ha, hag⟩, rfl⟩ _ ⟨b, ⟨hb, hbg⟩, rfl⟩
          exact hagree β a ha b hb hag hbg)
      exact ⟨v, fun a ha => hv1 _ ⟨a, ha, rfl⟩, fun b hb => hv2 _ ⟨b, hb, rfl⟩⟩
    have hgβ : g β = hex.choose := by
      rw [hg]
      simp only [step, hβ, hex, ite_false, dite_true]
    have hspec := hex.choose_spec
    rw [← hgβ] at hspec
    exact ⟨fun a ha hag => hspec.1 a ⟨ha, hag⟩, fun b hb hbg => hspec.2 b ⟨hb, hbg⟩⟩
  have hstrict : (∀ a ∈ A, (∀ j < γ, a j = g j) → a γ < g γ) ∧
      (∀ b ∈ B, (∀ j < γ, b j = g j) → g γ < b γ) := by
    have huniq : ∀ p ∈ C, ∀ q ∈ C, (∀ j < γ, p j = g j) → (∀ j < γ, q j = g j) → p = q := by
      intro p hp q hq hpg hqg
      by_contra hpq
      obtain ⟨j, hj, hne⟩ := hsep p hp q hq hpq
      exact hne ((hpg j hj).trans (hqg j hj).symm)
    have hex : ∃ v, (∀ a ∈ Ag γ (fun j _ => g j), a γ < v) ∧
        ∀ b ∈ Bg γ (fun j _ => g j), v < b γ := by
      by_cases hAn : (Ag γ (fun j _ => g j)).Nonempty
      · obtain ⟨a0, ha0, ha0g⟩ := hAn
        obtain ⟨v, hv⟩ := exists_gt (a0 γ)
        refine ⟨v, fun a ⟨ha, hag⟩ => ?_, fun b ⟨hb, hbg⟩ => ?_⟩
        · rw [huniq a (Or.inl ha) a0 (Or.inl ha0) hag ha0g]
          exact hv
        · have := huniq a0 (Or.inl ha0) b (Or.inr hb) ha0g hbg
          exact absurd (this ▸ hAB a0 ha0 b hb) (lt_irrefl _)
      · by_cases hBn : (Bg γ (fun j _ => g j)).Nonempty
        · obtain ⟨b0, hb0, hb0g⟩ := hBn
          obtain ⟨v, hv⟩ := exists_lt (b0 γ)
          refine ⟨v, fun a ha => absurd ⟨a, ha⟩ hAn, fun b ⟨hb, hbg⟩ => ?_⟩
          rw [huniq b (Or.inr hb) b0 (Or.inr hb0) hbg hb0g]
          exact hv
        · exact ⟨Classical.arbitrary V, fun a ha => absurd ⟨a, ha⟩ hAn,
            fun b hb => absurd ⟨b, hb⟩ hBn⟩
    have hgγ : g γ = hex.choose := by
      rw [hg]
      simp only [step, hex, ite_true, dite_true]
    have hspec := hex.choose_spec
    rw [← hgγ] at hspec
    exact ⟨fun a ha hag => hspec.1 a ⟨ha, hag⟩, fun b hb hbg => hspec.2 b ⟨hb, hbg⟩⟩
  -- the realizing point
  refine ⟨toLex g, fun a ha => ?_, fun b hb => ?_⟩
  · by_cases hN : ∃ j, a j ≠ g j
    · let i := (wellFounded_lt (α := ι)).min {j | a j ≠ g j} hN
      have hi : a i ≠ g i := (wellFounded_lt (α := ι)).min_mem {j | a j ≠ g j} hN
      have hbelow : ∀ j < i, a j = g j := fun j hj => by
        by_contra hne
        exact (wellFounded_lt (α := ι)).not_lt_min {j | a j ≠ g j} hne hj
      refine (hlt a (toLex g)).2 ⟨i, hbelow, ?_⟩
      by_cases hiγ : i = γ
      · rw [hiγ] at hbelow ⊢
        exact hstrict.1 a ha hbelow
      · exact lt_of_le_of_ne ((hnonstrict i hiγ).1 a ha hbelow) hi
    · push Not at hN
      exact absurd (hN γ ▸ hstrict.1 a ha fun j _ => hN j) (lt_irrefl _)
  · by_cases hN : ∃ j, b j ≠ g j
    · let i := (wellFounded_lt (α := ι)).min {j | b j ≠ g j} hN
      have hi : b i ≠ g i := (wellFounded_lt (α := ι)).min_mem {j | b j ≠ g j} hN
      have hbelow : ∀ j < i, b j = g j := fun j hj => by
        by_contra hne
        exact (wellFounded_lt (α := ι)).not_lt_min {j | b j ≠ g j} hne hj
      refine (hlt (toLex g) b).2 ⟨i, fun j hj => (hbelow j hj).symm, ?_⟩
      by_cases hiγ : i = γ
      · rw [hiγ] at hbelow ⊢
        exact hstrict.2 b hb hbelow
      · exact lt_of_le_of_ne ((hnonstrict i hiγ).2 b hb hbelow) (Ne.symm hi)
    · push Not at hN
      exact absurd (hN γ ▸ hstrict.2 b hb fun j _ => hN j) (lt_irrefl _)

/-- In `(succ κ).ord.ToType` (a regular well-order) every set of size `< κ` is strictly
bounded. -/
theorem succ_toType_bdd {κ : Cardinal.{u}} (hκ : aleph0 ≤ κ) (s : Set (Order.succ κ).ord.ToType)
    (hs : #s < κ) : ∃ γ, ∀ j ∈ s, j < γ := by
  have hcof : (Order.succ κ).ord.cof = Order.succ κ := (isRegular_succ hκ).cof_ord
  let f : s → Ordinal.{u} := fun x => Ordinal.typein (α := (Order.succ κ).ord.ToType) (· < ·) x.1
  have hf : ∀ x, f x < (Order.succ κ).ord := fun x => by
    simpa [f, Ordinal.type_toType] using
      Ordinal.typein_lt_type (α := (Order.succ κ).ord.ToType) (· < ·) x.1
  have hlt : ⨆ x, f x + 1 < (Order.succ κ).ord :=
    Ordinal.iSup_add_one_lt_of_lt_cof (by
      rw [hcof]; exact hs.trans (Order.lt_succ_of_not_isMax (not_isMax κ))) hf
  have hlt' : ⨆ x, f x + 1 < Ordinal.type (α := (Order.succ κ).ord.ToType) (· < ·) := by
    simpa [Ordinal.type_toType] using hlt
  refine ⟨Ordinal.enum (α := (Order.succ κ).ord.ToType) (· < ·) ⟨⨆ x, f x + 1, hlt'⟩,
    fun j hj => ?_⟩
  have hfj : f ⟨j, hj⟩ < ⨆ x, f x + 1 :=
    (Order.lt_add_one_iff.mpr le_rfl).trans_le (Ordinal.le_iSup (fun x => f x + 1) ⟨j, hj⟩)
  rw [← Ordinal.enum_typein (α := (Order.succ κ).ord.ToType) (· < ·) j]
  exact Ordinal.enum_lt_enum.mpr hfj

/-- The value order `ιᵒᵈ ×ₗ ι` separates (non-strictly) any two small sets `S ≤ U`, when small
subsets of the well-order `ι` are strictly bounded. -/
theorem dualLex_interp {κ : Cardinal.{u}} {ι : Type u} [LinearOrder ι] [WellFoundedLT ι]
    [Nonempty ι] (hbd : ∀ s : Set ι, #s < κ → ∃ γ, ∀ j ∈ s, j < γ)
    (S U : Set (Lex (ιᵒᵈ × ι))) (hS : #S < κ) (hU : #U < κ)
    (hSU : ∀ a ∈ S, ∀ b ∈ U, a ≤ b) :
    ∃ v, (∀ a ∈ S, a ≤ v) ∧ ∀ b ∈ U, v ≤ b := by
  classical
  have hle : ∀ p q : Lex (ιᵒᵈ × ι), p ≤ q ↔ (ofLex p).1 < (ofLex q).1 ∨
      (ofLex p).1 = (ofLex q).1 ∧ (ofLex p).2 ≤ (ofLex q).2 := fun p q =>
    Prod.Lex.toLex_le_toLex (x := ofLex p) (y := ofLex q)
  by_cases hSne : S.Nonempty
  · let F : Set ι := (fun s => OrderDual.ofDual (ofLex s).1) '' S
    have hFne : F.Nonempty := hSne.image _
    obtain ⟨c, hcF, hcmin⟩ : ∃ c ∈ F, ∀ x ∈ F, c ≤ x :=
      ⟨(wellFounded_lt (α := ι)).min F hFne, (wellFounded_lt (α := ι)).min_mem F hFne,
        fun x hx => not_lt.mp ((wellFounded_lt (α := ι)).not_lt_min F hx)⟩
    obtain ⟨s0, hs0, hs0c⟩ := hcF
    have hcle : ∀ s ∈ S, c ≤ OrderDual.ofDual (ofLex s).1 := fun s hs => hcmin _ ⟨s, hs, rfl⟩
    have hc0 : OrderDual.toDual c = (ofLex s0).1 := by rw [← hs0c]; rfl
    let T : Set ι := (fun s => (ofLex s).2) '' {s | s ∈ S ∧ OrderDual.ofDual (ofLex s).1 = c}
    have hT : #T < κ := mk_image_le.trans_lt
      ((mk_le_mk_of_subset (s := {s | s ∈ S ∧ OrderDual.ofDual (ofLex s).1 = c}) (t := S)
        fun x hx => hx.1).trans_lt hS)
    obtain ⟨γ, hγ⟩ := hbd T hT
    let UB : Set ι := {t | ∀ x ∈ T, x ≤ t}
    have hUB : UB.Nonempty := ⟨γ, fun x hx => (hγ x hx).le⟩
    let t := (wellFounded_lt (α := ι)).min UB hUB
    have ht : t ∈ UB := (wellFounded_lt (α := ι)).min_mem UB hUB
    refine ⟨toLex (OrderDual.toDual c, t), fun s hs => ?_, fun u hu => ?_⟩
    · rw [hle]
      rcases (hcle s hs).lt_or_eq with h | h
      · exact Or.inl h
      · refine Or.inr ⟨?_, ht _ ⟨s, ⟨hs, h.symm⟩, rfl⟩⟩
        exact congrArg OrderDual.toDual h.symm
    · have hsu := (hle s0 u).1 (hSU s0 hs0 u hu)
      rw [hle]
      rcases hsu with h | h
      · left
        rw [hc0]
        exact h
      · right
        refine ⟨?_, ?_⟩
        · rw [hc0]
          exact h.1
        · refine not_lt.mp ((wellFounded_lt (α := ι)).not_lt_min UB ?_)
          rintro x ⟨s, ⟨hs, hsc⟩, rfl⟩
          rcases (hle s u).1 (hSU s hs u hu) with h' | h'
          · exfalso
            have h1 : (ofLex u).1 = OrderDual.toDual c := by rw [← h.1, hc0]
            rw [h1] at h'
            exact (not_lt.mpr (hcle s hs)) (by
              have : OrderDual.toDual (OrderDual.ofDual (ofLex s).1) < OrderDual.toDual c := h'
              rw [hsc] at this
              exact absurd this (lt_irrefl _))
          · exact h'.2
  · let G : Set ι := (fun u => OrderDual.ofDual (ofLex u).1) '' U
    obtain ⟨γ, hγ⟩ := hbd G (mk_image_le.trans_lt hU)
    refine ⟨toLex (OrderDual.toDual γ, Classical.arbitrary ι),
      fun s hs => absurd ⟨s, hs⟩ hSne, fun u hu => ?_⟩
    rw [hle]
    exact Or.inl (hγ _ ⟨u, hu, rfl⟩)

/-- **Small saturated orders exist.**  For every infinite `κ` there is a `κ`-order-saturated
linear order of size `2 ^ κ⁺`: the lexicographic power `Lex (ι → ιᵒᵈ ×ₗ ι)`,
`ι = κ⁺.ord.ToType`. -/
theorem exists_orderSaturated {κ : Cardinal.{u}} (hκ : aleph0 ≤ κ) :
    ∃ (J : Type u) (_ : LinearOrder J), OrderSaturated κ J ∧ #J = 2 ^ Order.succ κ := by
  let ι := (Order.succ κ).ord.ToType
  have hbd : ∀ s : Set ι, #s < κ → ∃ γ, ∀ j ∈ s, j < γ := succ_toType_bdd hκ
  have hκ1 : (1 : Cardinal) < κ := one_lt_aleph0.trans_le hκ
  have : Nonempty ι := by
    obtain ⟨γ, -⟩ := hbd ∅ (by simpa using (zero_lt_one.trans hκ1))
    exact ⟨γ⟩
  have : NoMaxOrder ι := ⟨fun x => by
    obtain ⟨γ, hγ⟩ := hbd {x} (by simpa using hκ1)
    exact ⟨γ, hγ x rfl⟩⟩
  let V := Lex (ιᵒᵈ × ι)
  have : NoMaxOrder V := ⟨fun p => by
    obtain ⟨b, hb⟩ := exists_gt (ofLex p).2
    exact ⟨toLex ((ofLex p).1, b), Prod.Lex.toLex_lt_toLex.2 (Or.inr ⟨rfl, hb⟩)⟩⟩
  have : NoMinOrder V := ⟨fun p => by
    obtain ⟨b, hb⟩ := exists_gt (OrderDual.ofDual (ofLex p).1)
    exact ⟨toLex (OrderDual.toDual b, (ofLex p).2), Prod.Lex.toLex_lt_toLex.2 (Or.inl hb)⟩⟩
  have : Nonempty V := ⟨toLex (OrderDual.toDual (Classical.arbitrary ι), Classical.arbitrary ι)⟩
  refine ⟨Lex (ι → V), inferInstance, orderSaturated_piLex hκ hbd
    (fun S U hS hU hSU => dualLex_interp hbd S U hS hU hSU), ?_⟩
  have hι : #ι = Order.succ κ := Cardinal.mk_ord_toType _
  have hV : #V = Order.succ κ := by
    show #(ιᵒᵈ × ι) = _
    rw [mk_prod, lift_id, lift_id]
    show #ι * #ι = _
    rw [hι, mul_eq_self (hκ.trans (Order.le_succ κ))]
  show #(ι → V) = _
  rw [← power_def, hV, hι, power_self_eq (hκ.trans (Order.le_succ κ))]

/-- **Saturated padded dense orders at strong-limit levels.**  If `μ` is a strong limit above
`κ` (every working level is), there is a dense `κ`-order-saturated order of size `μ` containing
a well-ordered subset of size `μ`: `WithTop μ.ord.ToType ×ₗ J₀` with `J₀` the small saturated
order of `exists_orderSaturated`. -/
theorem exists_saturated_padded {κ μ : Cardinal.{u}} (hκ : aleph0 ≤ κ) (hμ : μ.IsStrongLimit)
    (hκμ : κ < μ) :
    ∃ (J : Type u) (_ : LinearOrder J), OrderSaturated κ J ∧ DenselyOrdered J ∧ #J = μ ∧
      ∃ S : Set J, #S = μ ∧ S.WellFoundedOn (· < ·) := by
  obtain ⟨J₀, _, hJ₀, hcard₀⟩ := exists_orderSaturated hκ
  have hμ0 : aleph0 ≤ μ := hμ.aleph0_le
  have hsucc : Order.succ κ < μ := hμ.isSuccLimit.succ_lt hκμ
  have hsmall : #J₀ < μ := hcard₀ ▸ hμ.2 hsucc
  have hne₀ : Nonempty J₀ := by
    rw [← Cardinal.mk_ne_zero_iff, hcard₀]
    exact (power_ne_zero _ two_ne_zero)
  let I := WithTop μ.ord.ToType
  let J := Lex (I × J₀)
  have hsat : OrderSaturated κ J := orderSaturated_lex hJ₀
  have hκ1 : (1 : Cardinal) < κ := one_lt_aleph0.trans_le hκ
  refine ⟨J, inferInstance, hsat, ⟨fun a b hab => ?_⟩, ?_, ?_⟩
  · obtain ⟨x, hx1, hx2⟩ := hsat {a} {b} (by simpa using hκ1) (by simpa using hκ1)
      (by simp [hab])
    exact ⟨x, hx1 a rfl, hx2 b rfl⟩
  · have hI : #I = μ := by
      show #(Option μ.ord.ToType) = μ
      rw [mk_option, Cardinal.mk_ord_toType]
      exact add_one_eq hμ0
    show #(I × J₀) = μ
    rw [mk_prod, lift_id, lift_id, hI]
    exact mul_eq_left hμ0 hsmall.le (Cardinal.mk_ne_zero _)
  · let j₀ := Classical.arbitrary J₀
    let f : μ.ord.ToType → J := fun i => toLex ((i : I), j₀)
    have hf : StrictMono f := fun a b hab =>
      Prod.Lex.toLex_lt_toLex.2 (Or.inl (WithTop.coe_lt_coe.2 hab))
    refine ⟨Set.range f, ?_, ?_⟩
    · rw [Cardinal.mk_range_eq f hf.injective, Cardinal.mk_ord_toType]
    · rw [Set.wellFoundedOn_range]
      have : Function.onFun (· < ·) f = (· < · : μ.ord.ToType → μ.ord.ToType → Prop) := by
        funext a b
        exact propext hf.lt_iff_lt
      rw [this]
      exact wellFounded_lt

end OrderSat83
end AEC
