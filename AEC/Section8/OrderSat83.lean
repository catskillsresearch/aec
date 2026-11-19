module

public import AEC.Section2.Partition

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

end OrderSat83
end AEC
