module

public import AEC.Section5.PackageClauses
public import AEC.Section5.RichPaddedOrder
public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

set_option linter.style.haveILetI false

/-!
# Order-pattern realization from cut filling (Lemma 5.5 equivalence)

English: every extension of an order pattern with at most `η` old and at most `η` added
positions can be realized over its old positions, given that cuts with at most `η` parameters on
each side are filled. The implication is discharged in `order_pattern_realized_over_old`.
-/

namespace AEC
section

universe u

open Cardinal Classical OrderEmbedding Set

/-- A linear order **fills `η`-bounded cuts** (Lemma 5.5, first clause). -/
def OrderFillsCuts (η : Cardinal.{u}) (Q : Type u) [LinearOrder Q] : Prop :=
  ∀ (L R : Set Q), #L ≤ η → #R ≤ η → (∀ a ∈ L, ∀ b ∈ R, a < b) →
    ∃ x : Q, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b)

/-- Data for an order-pattern extension (`η` old / `η` added positions). -/
structure OrderPattern (η : Cardinal.{u}) (Old Ext : Type u) [LinearOrder Old]
    [LinearOrder Ext] where
  emb : Old ↪o Ext
  card_old : #Old ≤ η
  cardAdded : #(Set.diff Set.univ (Set.range ⇑emb)) ≤ η

/-- Added positions of an order pattern. -/
def OrderPattern.added {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old] [LinearOrder Ext]
    (pat : OrderPattern η Old Ext) : Set Ext :=
  Set.diff Set.univ (Set.range ⇑pat.emb)

theorem OrderPattern.mem_added_iff {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) (x : Ext) :
    x ∈ pat.added ↔ x ∉ Set.range (⇑pat.emb) := by
  change (x ∈ Set.univ ∧ x ∉ Set.range ⇑pat.emb) ↔ x ∉ Set.range ⇑pat.emb
  simp

/-- Cut filling implies order-pattern realization (Lemma 5.5 equivalence, pattern direction). -/
def OrderPatternRealized (η : Cardinal.{u}) (Q : Type u) [LinearOrder Q] : Prop :=
  ∀ {Old Ext : Type u} [LinearOrder Old] [LinearOrder Ext]
    (pat : OrderPattern η Old Ext) (f : Old ↪o Q),
    ∃ g : Ext ↪o Q, ∀ a : Old, g (pat.emb a) = f a

/-! ### Infra: Lem 5.5 pattern direction (board `infra_55_*`)

The pattern direction places old positions by the given embedding, enumerates added positions in
a chosen well-order of cardinality at most `η`, and at each added point fills the cut determined
by the points already placed.
-/

/-- **Infra `infra_55_one_point_cut`:** an `η`-bounded cut in a partial order embedding is filled
by the image cut in `Q`. -/
theorem infra_55_one_point_cut {η : Cardinal.{u}} {Q : Type u} [LinearOrder Q]
    (hfill : OrderFillsCuts η Q) {Placed : Type u} [LinearOrder Placed] (g : Placed ↪o Q)
    (L R : Set Placed) (hL : #L ≤ η) (hR : #R ≤ η)
    (hcut : ∀ a ∈ L, ∀ b ∈ R, a < b) :
    ∃ x : Q, (∀ a ∈ L, g a < x) ∧ (∀ b ∈ R, x < g b) := by
  have hLimg : #(⇑g '' L) ≤ η := by
    calc
      #(⇑g '' L) ≤ #L := mk_image_le
      _ ≤ η := hL
  have hRimg : #(⇑g '' R) ≤ η := by
    calc
      #(⇑g '' R) ≤ #R := mk_image_le
      _ ≤ η := hR
  have himg : ∀ a ∈ ⇑g '' L, ∀ b ∈ ⇑g '' R, a < b := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (OrderEmbedding.lt_iff_lt g).2 (hcut a ha b hb)
  obtain ⟨x, hxL, hxR⟩ := hfill (⇑g '' L) (⇑g '' R) hLimg hRimg himg
  exact ⟨x, fun a ha => hxL (g a) ⟨a, ha, rfl⟩, fun b hb => hxR (g b) ⟨b, hb, rfl⟩⟩

/-- Carrier for a chosen well-ordering of added positions. It is not the subtype `pat.added`,
so the order induced by `Ext` does not shadow the well-order. -/
structure OrderAddedIndex {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) where
  val : Ext
  mem_added : val ∈ pat.added

/-- The index carrier is the added subtype. -/
def OrderAddedIndex.equivAdded {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) :
    OrderAddedIndex pat ≃ ↥pat.added where
  toFun i := ⟨i.val, i.mem_added⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Added positions, read off the index carrier. -/
def OrderAddedIndex.toExtEmbedding {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) : OrderAddedIndex pat ↪ Ext where
  toFun i := i.val
  inj' i j h := by
    cases i
    cases j
    cases h
    rfl

theorem OrderAddedIndex.range_toExtEmbedding {η : Cardinal.{u}} {Old Ext : Type u}
    [LinearOrder Old] [LinearOrder Ext] (pat : OrderPattern η Old Ext) :
    range (⇑(OrderAddedIndex.toExtEmbedding pat)) = pat.added := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact i.mem_added
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

/-- **Infra `infra_55_enumerate_added`:** added positions admit a well-ordered enumeration of
cardinality at most `η`. -/
theorem infra_55_enumerate_added {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) :
    ∃ (α : Type u) (_ : LinearOrder α) (_ : WellFoundedLT α) (enum : α ↪ Ext),
      #α ≤ η ∧ range (⇑enum) = pat.added := by
  obtain ⟨lo, wf⟩ := exists_wellFoundedLT (OrderAddedIndex pat)
  refine ⟨OrderAddedIndex pat, lo, wf, OrderAddedIndex.toExtEmbedding pat, ?_,
    OrderAddedIndex.range_toExtEmbedding pat⟩
  rw [mk_congr (OrderAddedIndex.equivAdded pat)]
  exact pat.cardAdded

/-- Cut inequalities for the value of one added point against old points and earlier added
points. -/
structure PatternCut {η : Cardinal.{u}} {Q Old Ext α : Type u} [LinearOrder Q] [LinearOrder Old]
    [LinearOrder Ext] [LinearOrder α] (pat : OrderPattern η Old Ext) (f : Old ↪o Q)
    (enum : α ↪ Ext) (i : α) (prev : ∀ j : α, j < i → Q) (x : Q) : Prop where
  lt_old : ∀ a : Old, pat.emb a < enum i → f a < x
  gt_old : ∀ a : Old, enum i < pat.emb a → x < f a
  lt_prev : ∀ j : α, (hj : j < i) → enum j < enum i → prev j hj < x
  gt_prev : ∀ j : α, (hj : j < i) → enum i < enum j → x < prev j hj

/-- Old points together with added points enumerated strictly before `i`.
A wrapper, rather than the raw sum, so the only order is the one pulled back from `Ext`. -/
structure PatternDomain {α : Type u} [LT α] (Old : Type u) (i : α) where
  toSum : Old ⊕ {j : α // j < i}

/-- Forget the wrapper. -/
def PatternDomain.sumEquiv {α : Type u} [LT α] {Old : Type u} (i : α) :
    PatternDomain Old i ≃ (Old ⊕ {j : α // j < i}) where
  toFun d := d.toSum
  invFun s := ⟨s⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Old points together with added points enumerated strictly before `i`, read in `Ext`. -/
def patternToExt {η : Cardinal.{u}} {Old Ext α : Type u} [LinearOrder Old] [LinearOrder Ext]
    [LinearOrder α] (pat : OrderPattern η Old Ext) (enum : α ↪ Ext) (i : α)
    (d : PatternDomain Old i) : Ext :=
  match d.toSum with
  | Sum.inl a => pat.emb a
  | Sum.inr ⟨j, _⟩ => enum j

@[simp] theorem patternToExt_old {η : Cardinal.{u}} {Old Ext α : Type u} [LinearOrder Old]
    [LinearOrder Ext] [LinearOrder α] (pat : OrderPattern η Old Ext) (enum : α ↪ Ext) (i : α)
    (a : Old) : patternToExt pat enum i ⟨Sum.inl a⟩ = pat.emb a := rfl

@[simp] theorem patternToExt_added {η : Cardinal.{u}} {Old Ext α : Type u} [LinearOrder Old]
    [LinearOrder Ext] [LinearOrder α] (pat : OrderPattern η Old Ext) (enum : α ↪ Ext) (i : α)
    (j : α) (hj : j < i) : patternToExt pat enum i ⟨Sum.inr ⟨j, hj⟩⟩ = enum j := rfl

/-- Values already chosen on `PatternDomain`. -/
def patternPlace {Q Old α : Type u} [LinearOrder Q] [LinearOrder Old] [LinearOrder α]
    (f : Old ↪o Q) (i : α) (prev : ∀ j : α, j < i → Q) (d : PatternDomain Old i) : Q :=
  match d.toSum with
  | Sum.inl a => f a
  | Sum.inr ⟨j, hj⟩ => prev j hj

@[simp] theorem patternPlace_old {Q Old α : Type u} [LinearOrder Q] [LinearOrder Old]
    [LinearOrder α] (f : Old ↪o Q) (i : α) (prev : ∀ j : α, j < i → Q) (a : Old) :
    patternPlace f i prev ⟨Sum.inl a⟩ = f a := rfl

@[simp] theorem patternPlace_added {Q Old α : Type u} [LinearOrder Q] [LinearOrder Old]
    [LinearOrder α] (f : Old ↪o Q) (i : α) (prev : ∀ j : α, j < i → Q) (j : α) (hj : j < i) :
    patternPlace f i prev ⟨Sum.inr ⟨j, hj⟩⟩ = prev j hj := rfl

theorem enum_not_range_emb {η : Cardinal.{u}} {Old Ext α : Type u} [LinearOrder Old]
    [LinearOrder Ext] [LinearOrder α] (pat : OrderPattern η Old Ext) (enum : α ↪ Ext)
    (hrange : range (⇑enum) = pat.added) (j : α) : enum j ∉ range (⇑pat.emb) := by
  rw [← OrderPattern.mem_added_iff, ← hrange]
  exact ⟨j, rfl⟩

theorem patternToExt_injective {η : Cardinal.{u}} {Old Ext α : Type u} [LinearOrder Old]
    [LinearOrder Ext] [LinearOrder α] (pat : OrderPattern η Old Ext) (enum : α ↪ Ext)
    (hrange : range (⇑enum) = pat.added) (i : α) :
    Function.Injective (patternToExt pat enum i) := by
  intro p q h
  cases p with
  | mk sp =>
    cases q with
    | mk sq =>
      match sp, sq with
      | Sum.inl a, Sum.inl b =>
        simp only [patternToExt_old] at h
        have : a = b := pat.emb.injective h
        subst this
        rfl
      | Sum.inl a, Sum.inr ⟨j, _⟩ =>
        simp only [patternToExt_old, patternToExt_added] at h
        exact absurd ⟨a, h⟩ (enum_not_range_emb pat enum hrange j)
      | Sum.inr ⟨j, _⟩, Sum.inl a =>
        simp only [patternToExt_old, patternToExt_added] at h
        exact absurd ⟨a, h.symm⟩ (enum_not_range_emb pat enum hrange j)
      | Sum.inr ⟨j, _⟩, Sum.inr ⟨k, _⟩ =>
        simp only [patternToExt_added] at h
        have hjk : j = k := enum.injective h
        subst hjk
        rfl

/-- Earlier cut specifications make the partial placement strictly monotone along `Ext`. -/
theorem patternPlace_lt_of_toExt_lt {η : Cardinal.{u}} {Q Old Ext α : Type u} [LinearOrder Q]
    [LinearOrder Old] [LinearOrder Ext] [LinearOrder α] (pat : OrderPattern η Old Ext)
    (f : Old ↪o Q) (enum : α ↪ Ext) (i : α) (prev : ∀ j : α, j < i → Q)
    (hspec : ∀ j (hj : j < i),
      PatternCut pat f enum j (fun k hk => prev k (lt_trans hk hj)) (prev j hj))
    {p q : PatternDomain Old i}
    (hpq : patternToExt pat enum i p < patternToExt pat enum i q) :
    patternPlace f i prev p < patternPlace f i prev q := by
  cases p with
  | mk sp =>
    cases q with
    | mk sq =>
      match sp, sq with
      | Sum.inl a, Sum.inl b =>
        have hab : pat.emb a < pat.emb b := by simpa [patternToExt_old] using hpq
        have hab' : a < b := (OrderEmbedding.lt_iff_lt pat.emb).1 hab
        simpa [patternPlace_old] using (OrderEmbedding.lt_iff_lt f).2 hab'
      | Sum.inl a, Sum.inr ⟨j, hj⟩ =>
        have hab : pat.emb a < enum j := by
          simpa [patternToExt_old, patternToExt_added] using hpq
        simpa [patternPlace_old, patternPlace_added] using (hspec j hj).lt_old a hab
      | Sum.inr ⟨j, hj⟩, Sum.inl b =>
        have hab : enum j < pat.emb b := by
          simpa [patternToExt_old, patternToExt_added] using hpq
        simpa [patternPlace_old, patternPlace_added] using (hspec j hj).gt_old b hab
      | Sum.inr ⟨j, hj⟩, Sum.inr ⟨k, hk⟩ =>
        have hab : enum j < enum k := by simpa [patternToExt_added] using hpq
        rcases lt_trichotomy j k with hjk | hjk | hkj
        · simpa [patternPlace_added] using (hspec k hk).lt_prev j hjk hab
        · subst hjk
          exact absurd hab (lt_irrefl _)
        · simpa [patternPlace_added] using (hspec j hj).gt_prev k hkj hab

theorem card_patternDomain_le {η : Cardinal.{u}} (hη : ℵ₀ ≤ η) {α : Type u} [LinearOrder α]
    (hcard : #α ≤ η) {Old : Type u} (hOld : #Old ≤ η) (i : α) :
    #(PatternDomain Old i) ≤ η := by
  rw [mk_congr (PatternDomain.sumEquiv i), mk_sum, lift_id, lift_id]
  calc
    #Old + #{j : α // j < i} ≤ #Old + #α :=
      add_le_add le_rfl (mk_subtype_le (fun j : α => j < i))
    _ ≤ η + η := add_le_add hOld hcard
    _ ≤ η := add_le_of_le hη le_rfl le_rfl

theorem orderFillsCuts_nonempty {η : Cardinal.{u}} {Q : Type u} [LinearOrder Q]
    (hfill : OrderFillsCuts η Q) : Nonempty Q := by
  have h0 : #(∅ : Set Q) ≤ η := by
    rw [mk_set_eq_zero_iff.mpr rfl]
    exact zero_le
  obtain ⟨x, -, -⟩ := hfill ∅ ∅ h0 h0 (fun a ha => ha.elim)
  exact ⟨x⟩

/-- One inductive step: the points placed before `i` form an order embedding into `Q`, and
`infra_55_one_point_cut` supplies a value for `enum i`. -/
theorem exists_patternCut_step {η : Cardinal.{u}} (hη : ℵ₀ ≤ η) {Q : Type u} [LinearOrder Q]
    (hfill : OrderFillsCuts η Q) {Old Ext : Type u} [LinearOrder Old] [LinearOrder Ext]
    (pat : OrderPattern η Old Ext) (f : Old ↪o Q) {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (enum : α ↪ Ext) (hrange : range (⇑enum) = pat.added) (hcard : #α ≤ η) (i : α)
    (prev : ∀ j : α, j < i → Q)
    (hspec : ∀ j (hj : j < i),
      PatternCut pat f enum j (fun k hk => prev k (lt_trans hk hj)) (prev j hj)) :
    ∃ x : Q, PatternCut pat f enum i prev x := by
  let Placed : Type u := PatternDomain Old i
  have hinj : Function.Injective (patternToExt pat enum i) :=
    patternToExt_injective pat enum hrange i
  letI : LinearOrder Placed := LinearOrder.lift' (patternToExt pat enum i) hinj
  have hmono : StrictMono (patternPlace f i prev) := by
    intro p q hpq
    exact patternPlace_lt_of_toExt_lt pat f enum i prev hspec hpq
  let g : Placed ↪o Q := OrderEmbedding.ofStrictMono (patternPlace f i prev) hmono
  let L : Set Placed := {p | patternToExt pat enum i p < enum i}
  let R : Set Placed := {p | enum i < patternToExt pat enum i p}
  have hPlaced : #Placed ≤ η := card_patternDomain_le hη hcard pat.card_old i
  have hL : #L ≤ η := by
    calc
      #L ≤ #(univ : Set Placed) := mk_le_mk_of_subset (subset_univ _)
      _ = #Placed := mk_univ
      _ ≤ η := hPlaced
  have hR : #R ≤ η := by
    calc
      #R ≤ #(univ : Set Placed) := mk_le_mk_of_subset (subset_univ _)
      _ = #Placed := mk_univ
      _ ≤ η := hPlaced
  have hsep : ∀ a ∈ L, ∀ b ∈ R, a < b := by
    intro a ha b hb
    have ha' : patternToExt pat enum i a < enum i := by simpa [L] using ha
    have hb' : enum i < patternToExt pat enum i b := by simpa [R] using hb
    have hlt : patternToExt pat enum i a < patternToExt pat enum i b := lt_trans ha' hb'
    change patternToExt pat enum i a < patternToExt pat enum i b
    exact hlt
  obtain ⟨x, hxL, hxR⟩ := infra_55_one_point_cut hfill g L R hL hR hsep
  refine ⟨x, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    have hmem : (⟨Sum.inl a⟩ : Placed) ∈ L := by
      change patternToExt pat enum i ⟨Sum.inl a⟩ < enum i
      simpa [patternToExt_old] using ha
    have hx := hxL _ hmem
    simpa [g, OrderEmbedding.coe_ofStrictMono, patternPlace_old] using hx
  · intro a ha
    have hmem : (⟨Sum.inl a⟩ : Placed) ∈ R := by
      change enum i < patternToExt pat enum i ⟨Sum.inl a⟩
      simpa [patternToExt_old] using ha
    have hx := hxR _ hmem
    simpa [g, OrderEmbedding.coe_ofStrictMono, patternPlace_old] using hx
  · intro j hj hlt
    have hmem : (⟨Sum.inr ⟨j, hj⟩⟩ : Placed) ∈ L := by
      change patternToExt pat enum i ⟨Sum.inr ⟨j, hj⟩⟩ < enum i
      simpa [patternToExt_added] using hlt
    have hx := hxL _ hmem
    simpa [g, OrderEmbedding.coe_ofStrictMono, patternPlace_added] using hx
  · intro j hj hlt
    have hmem : (⟨Sum.inr ⟨j, hj⟩⟩ : Placed) ∈ R := by
      change enum i < patternToExt pat enum i ⟨Sum.inr ⟨j, hj⟩⟩
      simpa [patternToExt_added] using hlt
    have hx := hxR _ hmem
    simpa [g, OrderEmbedding.coe_ofStrictMono, patternPlace_added] using hx

noncomputable section

/-- Value of an added position, chosen by filling the cut against everything placed earlier.
The `else` branch is a dummy point of `Q`; the specification proof shows the cut exists. -/
noncomputable abbrev patternAddedVal {η : Cardinal.{u}} {Q : Type u} [LinearOrder Q]
    (hfill : OrderFillsCuts η Q) {Old Ext : Type u} [LinearOrder Old] [LinearOrder Ext]
    (pat : OrderPattern η Old Ext) (f : Old ↪o Q) {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (enum : α ↪ Ext) : α → Q :=
  WellFoundedLT.fix fun i prev =>
    if h : ∃ x : Q, PatternCut pat f enum i prev x then
      Classical.choose h
    else
      Classical.choice (orderFillsCuts_nonempty hfill)

theorem patternAddedVal_spec {η : Cardinal.{u}} (hη : ℵ₀ ≤ η) {Q : Type u} [LinearOrder Q]
    (hfill : OrderFillsCuts η Q) {Old Ext : Type u} [LinearOrder Old] [LinearOrder Ext]
    (pat : OrderPattern η Old Ext) (f : Old ↪o Q) {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (enum : α ↪ Ext) (hrange : range (⇑enum) = pat.added) (hcard : #α ≤ η) (i : α) :
    PatternCut pat f enum i (fun j _ => patternAddedVal hfill pat f enum j)
      (patternAddedVal hfill pat f enum i) := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have hex : ∃ x : Q, PatternCut pat f enum i
        (fun j _ => patternAddedVal hfill pat f enum j) x :=
      exists_patternCut_step hη hfill pat f enum hrange hcard i
        (fun j _ => patternAddedVal hfill pat f enum j) ih
    unfold patternAddedVal
    rw [WellFoundedLT.fix_eq]
    rw [dite_eq_left hex]
    exact Classical.choose_spec hex

theorem patternAddedVal_lt_enum {η : Cardinal.{u}} (hη : ℵ₀ ≤ η) {Q : Type u} [LinearOrder Q]
    (hfill : OrderFillsCuts η Q) {Old Ext : Type u} [LinearOrder Old] [LinearOrder Ext]
    (pat : OrderPattern η Old Ext) (f : Old ↪o Q) {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (enum : α ↪ Ext) (hrange : range (⇑enum) = pat.added) (hcard : #α ≤ η) {i j : α}
    (hij : enum i < enum j) :
    patternAddedVal hfill pat f enum i < patternAddedVal hfill pat f enum j := by
  rcases lt_trichotomy i j with h | h | h
  · exact (patternAddedVal_spec hη hfill pat f enum hrange hcard j).lt_prev i h hij
  · subst h
    exact absurd hij (lt_irrefl _)
  · exact (patternAddedVal_spec hη hfill pat f enum hrange hcard i).gt_prev j h hij

theorem exists_addedIndex {η : Cardinal.{u}} {Old Ext α : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) (enum : α ↪ Ext)
    (hrange : range (⇑enum) = pat.added) {x : Ext} (hx : x ∈ pat.added) : ∃ i : α, enum i = x := by
  rw [← hrange] at hx
  exact hx

noncomputable def addedIndexOf {η : Cardinal.{u}} {Old Ext α : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) (enum : α ↪ Ext)
    (hrange : range (⇑enum) = pat.added) (x : Ext) (hx : x ∈ pat.added) : α :=
  Classical.choose (exists_addedIndex pat enum hrange hx)

theorem addedIndexOf_spec {η : Cardinal.{u}} {Old Ext α : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) (enum : α ↪ Ext)
    (hrange : range (⇑enum) = pat.added) (x : Ext) (hx : x ∈ pat.added) :
    enum (addedIndexOf pat enum hrange x hx) = x := by
  simpa [addedIndexOf] using Classical.choose_spec (exists_addedIndex pat enum hrange hx)

theorem exists_oldPreimage {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) {x : Ext} (hx : x ∉ pat.added) :
    ∃ a : Old, pat.emb a = x := by
  have hx' : x ∈ range (⇑pat.emb) := by
    by_contra hxr
    exact hx ((OrderPattern.mem_added_iff pat x).2 hxr)
  exact hx'

noncomputable def oldPreimageOf {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) (x : Ext) (hx : x ∉ pat.added) : Old :=
  Classical.choose (exists_oldPreimage pat hx)

theorem oldPreimageOf_spec {η : Cardinal.{u}} {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) (x : Ext) (hx : x ∉ pat.added) :
    pat.emb (oldPreimageOf pat x hx) = x := by
  simpa [oldPreimageOf] using Classical.choose_spec (exists_oldPreimage pat hx)

/-- The realized embedding on `Ext`: old points travel by `f`, added points by cut filling. -/
noncomputable def patternRealizeFun {η : Cardinal.{u}} {Q : Type u} [LinearOrder Q]
    (hfill : OrderFillsCuts η Q) {Old Ext : Type u} [LinearOrder Old] [LinearOrder Ext]
    (pat : OrderPattern η Old Ext) (f : Old ↪o Q) {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (enum : α ↪ Ext) (hrange : range (⇑enum) = pat.added) (x : Ext) : Q :=
  if hx : x ∈ pat.added then
    patternAddedVal hfill pat f enum (addedIndexOf pat enum hrange x hx)
  else
    f (oldPreimageOf pat x hx)

theorem patternRealizeFun_strictMono {η : Cardinal.{u}} (hη : ℵ₀ ≤ η) {Q : Type u}
    [LinearOrder Q] (hfill : OrderFillsCuts η Q) {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) (f : Old ↪o Q) {α : Type u} [LinearOrder α]
    [WellFoundedLT α] (enum : α ↪ Ext) (hrange : range (⇑enum) = pat.added) (hcard : #α ≤ η) :
    StrictMono (patternRealizeFun hfill pat f enum hrange) := by
  intro x y hxy
  by_cases hx : x ∈ pat.added <;> by_cases hy : y ∈ pat.added
  · have hxeq : patternRealizeFun hfill pat f enum hrange x =
        patternAddedVal hfill pat f enum (addedIndexOf pat enum hrange x hx) := by
      unfold patternRealizeFun
      rw [dite_eq_left hx]
    have hyeq : patternRealizeFun hfill pat f enum hrange y =
        patternAddedVal hfill pat f enum (addedIndexOf pat enum hrange y hy) := by
      unfold patternRealizeFun
      rw [dite_eq_left hy]
    have hxi : enum (addedIndexOf pat enum hrange x hx) = x :=
      addedIndexOf_spec pat enum hrange x hx
    have hyj : enum (addedIndexOf pat enum hrange y hy) = y :=
      addedIndexOf_spec pat enum hrange y hy
    have hij : enum (addedIndexOf pat enum hrange x hx) <
        enum (addedIndexOf pat enum hrange y hy) := by simpa [hxi, hyj] using hxy
    have hlt := patternAddedVal_lt_enum hη hfill pat f enum hrange hcard hij
    simpa [hxeq, hyeq] using hlt
  · have hxeq : patternRealizeFun hfill pat f enum hrange x =
        patternAddedVal hfill pat f enum (addedIndexOf pat enum hrange x hx) := by
      unfold patternRealizeFun
      rw [dite_eq_left hx]
    have hyeq : patternRealizeFun hfill pat f enum hrange y =
        f (oldPreimageOf pat y hy) := by
      unfold patternRealizeFun
      rw [dite_eq_right hy]
    have hxi : enum (addedIndexOf pat enum hrange x hx) = x :=
      addedIndexOf_spec pat enum hrange x hx
    have hpy : pat.emb (oldPreimageOf pat y hy) = y := oldPreimageOf_spec pat y hy
    have hlt_ext : enum (addedIndexOf pat enum hrange x hx) <
        pat.emb (oldPreimageOf pat y hy) := by simpa [hxi, hpy] using hxy
    have hlt :=
      (patternAddedVal_spec hη hfill pat f enum hrange hcard
          (addedIndexOf pat enum hrange x hx)).gt_old _ hlt_ext
    simpa [hxeq, hyeq] using hlt
  · have hxeq : patternRealizeFun hfill pat f enum hrange x =
        f (oldPreimageOf pat x hx) := by
      unfold patternRealizeFun
      rw [dite_eq_right hx]
    have hyeq : patternRealizeFun hfill pat f enum hrange y =
        patternAddedVal hfill pat f enum (addedIndexOf pat enum hrange y hy) := by
      unfold patternRealizeFun
      rw [dite_eq_left hy]
    have hpx : pat.emb (oldPreimageOf pat x hx) = x := oldPreimageOf_spec pat x hx
    have hyj : enum (addedIndexOf pat enum hrange y hy) = y :=
      addedIndexOf_spec pat enum hrange y hy
    have hlt_ext : pat.emb (oldPreimageOf pat x hx) <
        enum (addedIndexOf pat enum hrange y hy) := by simpa [hpx, hyj] using hxy
    have hlt :=
      (patternAddedVal_spec hη hfill pat f enum hrange hcard
          (addedIndexOf pat enum hrange y hy)).lt_old _ hlt_ext
    simpa [hxeq, hyeq] using hlt
  · have hxeq : patternRealizeFun hfill pat f enum hrange x =
        f (oldPreimageOf pat x hx) := by
      unfold patternRealizeFun
      rw [dite_eq_right hx]
    have hyeq : patternRealizeFun hfill pat f enum hrange y =
        f (oldPreimageOf pat y hy) := by
      unfold patternRealizeFun
      rw [dite_eq_right hy]
    have hpx : pat.emb (oldPreimageOf pat x hx) = x := oldPreimageOf_spec pat x hx
    have hpy : pat.emb (oldPreimageOf pat y hy) = y := oldPreimageOf_spec pat y hy
    have hab : pat.emb (oldPreimageOf pat x hx) < pat.emb (oldPreimageOf pat y hy) := by
      simpa [hpx, hpy] using hxy
    have hab' : oldPreimageOf pat x hx < oldPreimageOf pat y hy :=
      (OrderEmbedding.lt_iff_lt pat.emb).1 hab
    simpa [hxeq, hyeq] using (OrderEmbedding.lt_iff_lt f).2 hab'

theorem patternRealizeFun_emb {η : Cardinal.{u}} {Q : Type u} [LinearOrder Q]
    (hfill : OrderFillsCuts η Q) {Old Ext : Type u} [LinearOrder Old] [LinearOrder Ext]
    (pat : OrderPattern η Old Ext) (f : Old ↪o Q) {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (enum : α ↪ Ext) (hrange : range (⇑enum) = pat.added) (a : Old) :
    patternRealizeFun hfill pat f enum hrange (pat.emb a) = f a := by
  have hx : pat.emb a ∉ pat.added := by
    rw [OrderPattern.mem_added_iff]
    intro h
    exact h ⟨a, rfl⟩
  have hxeq : patternRealizeFun hfill pat f enum hrange (pat.emb a) =
      f (oldPreimageOf pat (pat.emb a) hx) := by
    unfold patternRealizeFun
    rw [dite_eq_right hx]
  have hpre : pat.emb (oldPreimageOf pat (pat.emb a) hx) = pat.emb a :=
    oldPreimageOf_spec pat (pat.emb a) hx
  have hpre' : oldPreimageOf pat (pat.emb a) hx = a := pat.emb.injective hpre
  simp [hxeq, hpre']

/-- **Infra `infra_55_pattern_realize`:** enumerate added positions and extend the partial order
embedding by filling one `η`-bounded cut at each step (English Lem 5.5, pattern direction). -/
theorem infra_55_pattern_realize {η : Cardinal.{u}} (hη : ℵ₀ ≤ η) {Q : Type u}
    [LinearOrder Q] (hfill : OrderFillsCuts η Q) {Old Ext : Type u} [LinearOrder Old]
    [LinearOrder Ext] (pat : OrderPattern η Old Ext) (f : Old ↪o Q) :
    ∃ g : Ext ↪o Q, ∀ a : Old, g (pat.emb a) = f a := by
  obtain ⟨α, lo, wf, enum, hcard, hrange⟩ := infra_55_enumerate_added pat
  letI : LinearOrder α := lo
  haveI : WellFoundedLT α := wf
  refine ⟨OrderEmbedding.ofStrictMono (patternRealizeFun hfill pat f enum hrange)
      (patternRealizeFun_strictMono hη hfill pat f enum hrange hcard), ?_⟩
  intro a
  simpa [OrderEmbedding.coe_ofStrictMono] using
    patternRealizeFun_emb hfill pat f enum hrange a

/-- Alias: prior name of `infra_55_pattern_realize`. -/
abbrev order_pattern_realized_over_old := @infra_55_pattern_realize

theorem orderPatternRealized_of_fillsCuts {η : Cardinal.{u}} (hη : ℵ₀ ≤ η) {Q : Type u}
    [LinearOrder Q] (hfill : OrderFillsCuts η Q) :
    OrderPatternRealized η Q :=
  fun pat f => infra_55_pattern_realize hη hfill pat f

/-- Every order from Lemma 5.5 fills cuts and hence realizes patterns. -/
theorem orderPatternRealized_of_lemma_5_5 (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) {Q : Type u}
    [LinearOrder Q] (hfill : OrderFillsCuts η Q) :
    OrderPatternRealized η Q :=
  orderPatternRealized_of_fillsCuts hη hfill

/-- A dense rich `Pt η` order (Lemma 5.5) fills cuts and realizes patterns. -/
theorem orderPatternRealized_pt (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) :
    OrderPatternRealized η (Pt η) :=
  orderPatternRealized_of_fillsCuts hη (by
    intro L R hL hR hcut
    obtain ⟨x, hxL, hxR⟩ := pt_fills_cuts η hη L R hL hR hcut
    exact ⟨x, hxL, hxR⟩)

end
end
end AEC
