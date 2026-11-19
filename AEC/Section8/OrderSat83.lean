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

end OrderSat83
end AEC
