module

public import AEC.Section5.PresentationClause
public import AEC.Section5.TermTemplate

@[expose] public section

/-!
# Finite supports for the fixed-support template (proof of Proposition 5.7)

Paper (proof of Prop 5.7): "In the presentations `F (J + H)` name the terms representing `c` on
`J`. Regard this as a template in the variable order `H`: any term using positions from both
parts becomes a label recording its original label and its finitely many fixed positions from
`J`, applied to its remaining positions from `H`."

A split label at `v` is an original label `a`, a count `k ≤ arity a` and an increasing list
`p : Fin k → J` of fixed positions; its arity is `arity a - k`. The full position list on
`J ⊕ₗ H` is `p` followed by the `H`-positions (`splitPos`).
-/

namespace AEC
section

universe u

open Sum

/-- Split labels: an original label, the number `k` of fixed positions and the increasing list
of fixed positions in `J`. -/
structure SplitLabel (Lab : Type u) (arity : Lab → ℕ) (J : Type u) [LinearOrder J] where
  label : Lab
  k : ℕ
  hk : k ≤ arity label
  fixed : Fin k → J
  fixed_mono : StrictMono fixed

/-- Remaining arity of a split label. -/
def SplitLabel.arity' {Lab : Type u} {arity : Lab → ℕ} {J : Type u} [LinearOrder J]
    (b : SplitLabel Lab arity J) : ℕ :=
  arity b.label - b.k

/-- Full position list on `J ⊕ₗ H`: the fixed `J`-positions followed by the `H`-positions. -/
def splitPos {Lab : Type u} {arity : Lab → ℕ} {J H : Type u} [LinearOrder J] [LinearOrder H]
    (b : SplitLabel Lab arity J) (q : Fin b.arity' → H) : Fin (arity b.label) → J ⊕ₗ H :=
  fun i => if h : i.val < b.k then inlₗ (b.fixed ⟨i, h⟩)
    else inrₗ (q ⟨i - b.k, by unfold SplitLabel.arity'; omega⟩)

theorem splitPos_strictMono {Lab : Type u} {arity : Lab → ℕ} {J H : Type u} [LinearOrder J]
    [LinearOrder H] (b : SplitLabel Lab arity J) {q : Fin b.arity' → H} (hq : StrictMono q) :
    StrictMono (splitPos b q) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  unfold splitPos
  by_cases hi : i.val < b.k <;> by_cases hj : j.val < b.k
  · simp only [hi, hj, dite_true]
    exact Lex.inl_strictMono (b.fixed_mono (Fin.mk_lt_mk.2 hij'))
  · simp only [hi, hj, dite_true, dite_false]
    exact Lex.inl_lt_inr _ _
  · omega
  · simp only [hi, hj, dite_false]
    exact Lex.inr_strictMono (hq (Fin.mk_lt_mk.2 (by omega)))

theorem sumLexEmbedRight_splitPos {Lab : Type u} {arity : Lab → ℕ} {J H H' : Type u}
    [LinearOrder J] [LinearOrder H] [LinearOrder H'] (f : H ↪o H')
    (b : SplitLabel Lab arity J) (q : Fin b.arity' → H) :
    sumLexEmbedRight (J := J) f ∘ splitPos b q = splitPos b (f ∘ q) := by
  funext i
  unfold splitPos
  by_cases hi : i.val < b.k
  · simp only [Function.comp_apply, hi, dite_true, sumLexEmbedRight_apply_inl]
  · simp only [Function.comp_apply, hi, dite_false, sumLexEmbedRight_apply_inr]

/-- Every increasing list on `J ⊕ₗ H` splits as fixed `J`-positions followed by `H`-positions. -/
theorem exists_split {Lab : Type u} {arity : Lab → ℕ} {J H : Type u} [LinearOrder J]
    [LinearOrder H] (a : Lab) (pos : Fin (arity a) → J ⊕ₗ H) (hpos : StrictMono pos) :
    ∃ (b : SplitLabel Lab arity J) (q : Fin b.arity' → H) (hb : b.label = a),
      StrictMono q ∧ ∀ i, pos i = splitPos b q (Fin.cast (congrArg arity hb.symm) i) := by
  classical
  let L : Fin (arity a) → Prop := fun i => (ofLex (pos i)).isLeft = true
  have down : ∀ i j : Fin (arity a), i < j → L j → L i := by
    intro i j hij hj
    by_contra hi
    have hi' : (ofLex (pos i)).isRight = true := by simpa [L] using hi
    have e1 : pos i = toLex (inr ((ofLex (pos i)).getRight hi')) := by simp
    have e2 : pos j = toLex (inl ((ofLex (pos j)).getLeft hj)) := by simp
    have := hpos hij
    rw [e1, e2] at this
    exact Lex.not_inr_lt_inl this
  let P : ℕ → Prop := fun m => ∃ hm : m < arity a, ¬ L ⟨m, hm⟩
  let k : ℕ := if h : ∃ m, P m then Nat.find h else arity a
  have hk : k ≤ arity a := by
    simp only [k]; split_ifs with h
    · exact (Nat.find_spec h).1.le
    · exact le_rfl
  have hseg : ∀ i : Fin (arity a), L i ↔ i.val < k := by
    intro i
    constructor
    · intro hi
      simp only [k]; split_ifs with h
      · by_contra hlt
        push Not at hlt
        obtain ⟨hm, hnot⟩ := Nat.find_spec h
        rcases hlt.lt_or_eq with hlt | heq
        · exact hnot (down ⟨_, hm⟩ i hlt hi)
        · exact hnot (by have : (⟨Nat.find h, hm⟩ : Fin (arity a)) = i := Fin.ext heq; rw [this]; exact hi)
      · exact i.2
    · intro hi
      simp only [k] at hi; split_ifs at hi with h
      · have := Nat.find_min h hi
        by_contra hL
        exact this ⟨i.2, hL⟩
      · by_contra hL
        exact h ⟨i, i.2, hL⟩
  have hLm : ∀ (m : ℕ) (hm : m < k), L ⟨m, lt_of_lt_of_le hm hk⟩ := fun m hm => (hseg _).2 hm
  have hRm : ∀ (m : ℕ) (hm : m < arity a) (_ : k ≤ m),
      (ofLex (pos ⟨m, hm⟩)).isRight = true := by
    intro m hm hkm
    have : ¬ L ⟨m, hm⟩ := fun h => absurd ((hseg _).1 h) (by simp; omega)
    simpa [L] using this
  let b : SplitLabel _ arity J :=
    { label := a, k := k, hk := hk
      fixed := fun j => (ofLex (pos ⟨j, lt_of_lt_of_le j.2 hk⟩)).getLeft (hLm j j.2)
      fixed_mono := by
        intro j j' hjj
        have e1 := Sum.inl_getLeft _ (hLm j j.2)
        have e2 := Sum.inl_getLeft _ (hLm j' j'.2)
        have h := hpos (show (⟨j, lt_of_lt_of_le j.2 hk⟩ : Fin (arity a)) < ⟨j', lt_of_lt_of_le j'.2 hk⟩
          from hjj)
        rw [← toLex_ofLex (pos _), ← toLex_ofLex (pos ⟨j', _⟩), ← e1, ← e2] at h
        exact Lex.inl_lt_inl_iff.1 h }
  have hqlt : ∀ j : Fin b.arity', j.val + k < arity a := fun j => by
    have := j.2; simp only [SplitLabel.arity', b] at this; omega
  let q : Fin b.arity' → H := fun j =>
    (ofLex (pos ⟨j + k, hqlt j⟩)).getRight (hRm _ (hqlt j) (by omega))
  have hposR : ∀ (m : ℕ) (hm : m < arity a) (hkm : k ≤ m) (i : Fin (arity a)), i.val = m →
      pos i = toLex (inr ((ofLex (pos ⟨m, hm⟩)).getRight (hRm m hm hkm))) := by
    intro m hm hkm i hi
    obtain rfl : i = ⟨m, hm⟩ := Fin.ext hi
    simp
  have hposL : ∀ (m : ℕ) (hm : m < k) (i : Fin (arity a)), i.val = m →
      pos i = toLex (inl ((ofLex (pos ⟨m, lt_of_lt_of_le hm hk⟩)).getLeft (hLm m hm))) := by
    intro m hm i hi
    obtain rfl : i = ⟨m, lt_of_lt_of_le hm hk⟩ := Fin.ext hi
    simp
  refine ⟨b, q, rfl, ?_, ?_⟩
  · intro j j' hjj
    have h := hpos (show (⟨j + k, hqlt j⟩ : Fin (arity a)) < ⟨j' + k, hqlt j'⟩ from by
      simp only [Fin.mk_lt_mk]; have : j.val < j'.val := hjj; omega)
    have e1 : pos ⟨j + k, hqlt j⟩ = toLex (inr (q j)) := by simp only [q, Sum.inr_getRight, toLex_ofLex]
    have e2 : pos ⟨j' + k, hqlt j'⟩ = toLex (inr (q j')) := by simp only [q, Sum.inr_getRight, toLex_ofLex]
    rw [e1, e2] at h
    exact Lex.inr_lt_inr_iff.1 h
  · intro i
    unfold splitPos
    by_cases hi : i.val < k
    · have hi' : (Fin.cast (congrArg arity (rfl : b.label = a).symm) i).val < b.k := hi
      rw [dif_pos hi']
      exact hposL _ hi _ rfl
    · have hi' : ¬ (Fin.cast (congrArg arity (rfl : b.label = a).symm) i).val < b.k := hi
      rw [dif_neg hi']
      refine (hposR _ (hqlt _) (by omega) _ ?_)
      simp only [Fin.val_cast, b]; omega

/-- Split-label realization in `F (J ⊕ₗ H)`: realize the original label on the full list. -/
def splitRealize {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {F : TermTemplate K S}
    (Φ : F.FiniteSupport) (J : Type u) [LinearOrder J] [Nonempty J] {H : Type u} [LinearOrder H]
    [Nonempty H] (v : S.Vertex) (t : SupportTerm (SplitLabel (Φ.Lab v) (Φ.arity v) J) SplitLabel.arity' H) :
    ((F.withFixedSupport J).present H).obj v |>.carrier :=
  Φ.realize (I := J ⊕ₗ H) v ⟨t.label.label, splitPos t.label t.pos,
    splitPos_strictMono t.label t.increasing⟩

theorem splitRealize_surjective {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    {F : TermTemplate K S} (Φ : F.FiniteSupport) (J : Type u) [LinearOrder J] [Nonempty J]
    {H : Type u} [LinearOrder H] [Nonempty H] (v : S.Vertex) :
    Function.Surjective (splitRealize Φ J (H := H) v) := by
  intro x
  obtain ⟨t0, rfl⟩ := Φ.realize_surjective (I := J ⊕ₗ H) v x
  obtain ⟨b, q, hb, hq, heq⟩ := exists_split (arity := Φ.arity v) t0.label t0.pos t0.increasing
  refine ⟨⟨b, q, hq⟩, ?_⟩
  unfold splitRealize
  congr 1
  exact (SupportTerm.ext_of_label_eq hb.symm heq).symm

theorem splitRealize_map {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    {F : TermTemplate K S} (Φ : F.FiniteSupport) (J : Type u) [LinearOrder J] [Nonempty J]
    {H H' : Type u} [LinearOrder H] [LinearOrder H'] [Nonempty H] [Nonempty H']
    (f : H ↪o H') (v : S.Vertex)
    (t : SupportTerm (SplitLabel (Φ.Lab v) (Φ.arity v) J) SplitLabel.arity' H) :
    ((F.withFixedSupport J).onOrder f).onVertex v (splitRealize Φ J v t) =
      splitRealize Φ J v ⟨t.label, f ∘ t.pos, f.strictMono.comp t.increasing⟩ := by
  unfold splitRealize
  change (F.onOrder (sumLexEmbedRight (J := J) f)).onVertex v _ = _
  rw [Φ.realize_map]
  congr 1
  exact SupportTerm.ext_of_label_eq rfl (fun i => congrFun (sumLexEmbedRight_splitPos f t.label t.pos) i)

end
end AEC
