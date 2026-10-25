module

public import AEC.Section2.PartitionBound
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Sort
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section

namespace AEC
section

universe u

open Cardinal

noncomputable local instance {α : Type u} : DecidableEq α := Classical.typeDecidableEq α

noncomputable local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-!
Lemma 2.5, first sentence of the proof. A set of cardinality greater than `ξ · ν` cannot be
partitioned into `ξ` sets each of cardinality less than `ν`, so a coloring of the singletons
has a monochromatic subset of cardinality `ν`.
-/

lemma singleton_homogeneous {ξ ν : Cardinal.{u}} (_hξ : aleph0 ≤ ξ) (_hν : aleph0 ≤ ν)
    {ι : Type u} (hι : Order.succ (ξ * ν) ≤ #ι)
    {C : Type u} (hC : #C = ξ)
    (color : {s : Finset ι // s.card = 1} → C) :
    ∃ H : Set ι, ν ≤ #H ∧ ∃ c : C,
      ∀ (s : Finset ι) (hs : s.card = 1),
        (∀ x ∈ s, x ∈ H) → color ⟨s, hs⟩ = c := by
  let fiber (c : C) : Set ι :=
    {x | color ⟨{x}, Finset.card_singleton x⟩ = c}
  have hcover : (Set.univ : Set ι) ⊆ ⋃ c, fiber c := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨color ⟨{x}, Finset.card_singleton x⟩, rfl⟩
  by_cases hbig : ∃ c : C, ν ≤ #(fiber c)
  · obtain ⟨c, hc⟩ := hbig
    refine ⟨fiber c, hc, c, ?_⟩
    intro s hs hsub
    obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hs
    have hx : x ∈ fiber c := hsub x (Finset.mem_singleton_self x)
    have hpr : hs = Finset.card_singleton x := Subsingleton.elim _ _
    simpa [fiber, hpr, Set.mem_ofPred] using hx
  · have hlt : ∀ c, #(fiber c) < ν := fun c =>
      lt_of_not_ge (fun hle => hbig ⟨c, hle⟩)
    have hle : ∀ c, #(fiber c) ≤ ν := fun c => (hlt c).le
    have hsum : #ι ≤ Cardinal.sum (fun c : C => #(fiber c)) := by
      have hunion : #ι ≤ #(⋃ c, fiber c) := by
        calc
          #ι = #(Set.univ : Set ι) := Cardinal.mk_univ.symm
          _ ≤ #(⋃ c, fiber c) := Cardinal.mk_le_mk_of_subset hcover
      exact hunion.trans Cardinal.mk_iUnion_le_sum_mk
    have hconst : Cardinal.sum (fun c : C => #(fiber c)) ≤ #C * ν := by
      have hstep := Cardinal.sum_le_sum (fun c : C => #(fiber c)) (fun _ : C => ν) hle
      have heq : Cardinal.sum (fun _ : C => ν) = #C * ν := Cardinal.sum_const' C ν
      exact hstep.trans_eq heq
    have hprod : #ι ≤ ξ * ν := by
      rw [hC] at hconst
      exact hsum.trans hconst
    have hstrict : ξ * ν < #ι := (Order.succ_le_iff).mp hι
    exfalso
    exact hstrict.not_ge hprod

/-- An infinite cardinal is unchanged by a positive finite power. -/
lemma pow_nat_eq_self {μ : Cardinal.{u}} (hμ : aleph0 ≤ μ) (m : ℕ) : μ ^ (m + 1) = μ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, pow_succ, ih, Cardinal.mul_eq_self hμ]

/-- There are at most `μ` many `n`-element subsets of a type of cardinality at most `μ`. -/
lemma card_ksubset {β : Type u} [LinearOrder β] {μ : Cardinal.{u}}
    (hμ : #β ≤ μ) (hinf : aleph0 ≤ μ) {n : ℕ} (hn : 0 < n) :
    # {s : Finset β // s.card = n} ≤ μ := by
  let f : {s : Finset β // s.card = n} → (Fin n → β) :=
    fun s i => s.1.orderEmbOfFin s.2 i
  have hinj : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    apply Finset.coe_injective
    rw [← Finset.range_orderEmbOfFin s.1 s.2, ← Finset.range_orderEmbOfFin t.1 t.2]
    exact congrArg Set.range (funext (congrFun hst))
  have hfun : #(Fin n → β) = #β ^ n := by
    have hequiv : #(Fin n → β) = #(ULift.{u} (Fin n) → β) :=
      Cardinal.mk_congr ((Equiv.ulift (α := Fin n)).symm.arrowCongr (Equiv.refl β))
    have hpow : #(ULift.{u} (Fin n) → β) = #β ^ #(ULift.{u} (Fin n)) :=
      (Cardinal.power_def β (ULift.{u} (Fin n))).symm
    have hidx : #(ULift.{u} (Fin n)) = n := by
      rw [Cardinal.mk_uLift, Cardinal.lift_mk_fin]
    rw [hequiv, hpow, hidx]
    rfl
  have hpow : #β ^ n ≤ μ ^ n := Cardinal.power_le_power_right hμ
  have hself : μ ^ n = μ := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn)
    have hm' : n = m + 1 := by simpa [Nat.succ_eq_add_one] using hm
    rw [hm']
    exact pow_nat_eq_self hinf m
  exact (Cardinal.mk_le_of_injective hinj).trans
    (hfun.trans_le (hpow.trans_eq hself))

/-- A finite tuple in a set with no last element, ordered by `e`, sits strictly below some
further element of the set. -/
lemma exists_above {α : Type u} (e : α ≃ (#α).ord.ToType) {H : Set α}
    (hlim : ∀ x ∈ H, ∃ y ∈ H, e x < e y)
    {s : Finset α} (hs : ∀ x ∈ s, x ∈ H) (hne : s.Nonempty) :
    ∃ y ∈ H, ∀ x ∈ s, e x < e y := by
  let image := s.image (fun x => e x)
  have himg : image.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp (image.max'_mem himg)
  obtain ⟨y, hy, hgt⟩ := hlim a (hs a ha)
  refine ⟨y, hy, ?_⟩
  intro x hx
  have hmem : e x ∈ image := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hle : e x ≤ image.max' himg := Finset.le_max' image (e x) hmem
  rw [← hae] at hle
  exact lt_of_le_of_lt hle hgt

/-- Inserting a point strictly above every element of a finite set raises the cardinality
by one. -/
lemma card_insert_above {α : Type u} (e : α ≃ (#α).ord.ToType)
    {s : Finset α} {y : α} (hy : ∀ x ∈ s, e x < e y) :
    (insert y s).card = s.card + 1 := by
  apply Finset.card_insert_of_notMem
  intro hyS
  exact (lt_irrefl (e y)) (hy y hyS)

/-- The color of a `(k + 1)`-tuple extended by any later point of an end-homogeneous set.
The choice of the later point does not matter, by the end-homogeneity hypothesis. -/
noncomputable def endColor {k : ℕ} {ξ : Cardinal.{u}} {α : Type u}
    (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = k + 2} → ξ.ord.ToType)
    {H : Set α} (hlim : ∀ x ∈ H, ∃ y ∈ H, e x < e y)
    (s : Finset α) (hs : s.card = k + 1) (hH : ∀ x ∈ s, x ∈ H) : ξ.ord.ToType :=
  let spec := exists_above e hlim hH (Finset.card_pos.mp (by rw [hs]; omega))
  color ⟨insert (Classical.choose spec) s,
    by rw [card_insert_above e (Classical.choose_spec spec).2, hs]⟩

lemma endColor_eq {k : ℕ} {ξ : Cardinal.{u}} {α : Type u}
    (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = k + 2} → ξ.ord.ToType)
    {H : Set α} (hlim : ∀ x ∈ H, ∃ y ∈ H, e x < e y)
    (hend : ∀ (s : Finset α) (_ : s.card = k + 1), (∀ x ∈ s, x ∈ H) →
      ∀ x y, x ∈ H → y ∈ H → (∀ z ∈ s, e z < e x) → (∀ z ∈ s, e z < e y) →
        ∀ (hx : (insert x s).card = k + 2) (hy : (insert y s).card = k + 2),
          color ⟨insert x s, hx⟩ = color ⟨insert y s, hy⟩)
    {s : Finset α} (hs : s.card = k + 1) (hH : ∀ x ∈ s, x ∈ H)
    {y : α} (hy : y ∈ H) (habove : ∀ x ∈ s, e x < e y) :
    endColor e color hlim s hs hH =
      color ⟨insert y s, by rw [card_insert_above e habove, hs]⟩ := by
  let spec := exists_above e hlim hH (Finset.card_pos.mp (by rw [hs]; omega))
  have hspec := Classical.choose_spec spec
  exact hend s hs hH (Classical.choose spec) y hspec.1 hy hspec.2 habove _ _

lemma endColor_congr {k : ℕ} {ξ : Cardinal.{u}} {α : Type u}
    (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = k + 2} → ξ.ord.ToType)
    {H : Set α} (hlim : ∀ x ∈ H, ∃ y ∈ H, e x < e y)
    {s s' : Finset α} (h : s = s')
    (hs : s.card = k + 1) (hs' : s'.card = k + 1)
    (hH : ∀ x ∈ s, x ∈ H) (hH' : ∀ x ∈ s', x ∈ H) :
    endColor e color hlim s hs hH = endColor e color hlim s' hs' hH' := by
  subst h
  congr

/-- The last sentence of the inductive step in Lemma 2.5. An end-homogeneous set of
cardinality at least the `k`-ary bound, with no last element, carries an induced coloring
of one lower arity, and a homogeneous subset for that coloring is homogeneous for the
original coloring. -/
lemma homogeneous_of_end {k : ℕ} {ξ ν : Cardinal.{u}}
    {α : Type u} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = k + 2} → ξ.ord.ToType)
    {H : Set α} (hlim : ∀ x ∈ H, ∃ y ∈ H, e x < e y)
    (hend : ∀ (s : Finset α) (_ : s.card = k + 1), (∀ x ∈ s, x ∈ H) →
      ∀ x y, x ∈ H → y ∈ H → (∀ z ∈ s, e z < e x) → (∀ z ∈ s, e z < e y) →
        ∀ (hx : (insert x s).card = k + 2) (hy : (insert y s).card = k + 2),
          color ⟨insert x s, hx⟩ = color ⟨insert y s, hy⟩)
    (ih : IsErdosRadoBound (k + 1) ξ ν (recursivePartitionBound (k + 1) ξ ν))
    (hcard : recursivePartitionBound (k + 1) ξ ν ≤ #H) :
    ∃ t : Set α, t ⊆ H ∧ ν ≤ #t ∧
      ∃ c : ξ.ord.ToType, ∀ (s : Finset α) (hs : s.card = k + 2),
        (∀ x ∈ s, x ∈ t) → color ⟨s, hs⟩ = c := by
  let colorH : {s : Finset (↥H) // s.card = k + 1} → ξ.ord.ToType := fun s =>
    let mapped : Finset α := s.1.map (Function.Embedding.subtype (fun x => x ∈ H))
    have hcardS : mapped.card = k + 1 := by
      rw [Finset.card_map, s.2]
    have hsub : ∀ x ∈ mapped, x ∈ H := by
      intro x hx
      obtain ⟨z, _, hz⟩ := Finset.mem_map.mp hx
      exact hz ▸ z.2
    endColor e color hlim mapped hcardS hsub
  obtain ⟨t0, ht0, c, hc⟩ := ih (↥H) (by
    simpa using hcard) colorH
  let t : Set α := (Subtype.val : ↥H → α) '' t0
  have htH : t ⊆ H := by
    intro x hx
    obtain ⟨z, _, rfl⟩ := hx
    exact z.2
  have htcard : ν ≤ #t :=
    ht0.trans_eq (Cardinal.mk_image_eq Subtype.val_injective).symm
  refine ⟨t, htH, htcard, c, ?_⟩
  intro s hs hsub
  classical
  let image := s.image (fun x => e x)
  have hne : s.Nonempty := Finset.card_pos.mp (by rw [hs]; omega)
  have himg : image.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨e x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  obtain ⟨m, hm, hme⟩ := Finset.mem_image.mp (image.max'_mem himg)
  have hbelow : ∀ x ∈ s.erase m, e x < e m := by
    intro x hx
    have hxS : x ∈ s := Finset.mem_of_mem_erase hx
    have hneX : x ≠ m := Finset.ne_of_mem_erase hx
    have hmem : e x ∈ image := Finset.mem_image.mpr ⟨x, hxS, rfl⟩
    have hle : e x ≤ image.max' himg := Finset.le_max' image (e x) hmem
    rw [← hme] at hle
    exact lt_of_le_of_ne hle (fun hEq => hneX (e.injective hEq))
  have hcard0 : (s.erase m).card = k + 1 := by
    rw [Finset.card_erase_of_mem hm, hs]
    omega
  have hsubH : ∀ x ∈ s.erase m, x ∈ H := fun x hx =>
    htH (hsub x (Finset.mem_of_mem_erase hx))
  have hfilter : (s.erase m).filter (fun x => x ∈ H) = s.erase m := by
    ext x
    constructor
    · intro hx
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact Finset.mem_filter.mpr ⟨hx, hsubH x hx⟩
  let s0 := (s.erase m).subtype (fun x => x ∈ H)
  have hs0 : s0.card = k + 1 := by
    rw [Finset.card_subtype, hfilter, hcard0]
  have hs0t : ∀ z ∈ s0, z ∈ t0 := by
    intro z hz
    have hzE : (z : α) ∈ s.erase m := (Finset.mem_subtype).mp hz
    have hzT : (z : α) ∈ t := hsub (z : α) (Finset.mem_of_mem_erase hzE)
    obtain ⟨w, hw, hwz⟩ := hzT
    have : w = z := Subtype.ext hwz
    exact this ▸ hw
  have hinduced : colorH ⟨s0, hs0⟩ = c := hc s0 hs0 hs0t
  have hmapped : s0.map (Function.Embedding.subtype (fun x => x ∈ H)) = s.erase m := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
      exact (Finset.mem_subtype).mp hz
    · intro hx
      refine Finset.mem_map.mpr ⟨⟨x, hsubH x hx⟩, ?_, rfl⟩
      exact (Finset.mem_subtype).mpr hx
  have hmH : m ∈ H := htH (hsub m hm)
  have hcolorM : endColor e color hlim (s.erase m) hcard0 hsubH = c := by
    have hsubMap : ∀ x ∈ s0.map (Function.Embedding.subtype (fun x => x ∈ H)), x ∈ H := by
      intro x hx
      obtain ⟨z, _, hz⟩ := Finset.mem_map.mp hx
      exact hz ▸ z.2
    have hcolorH : colorH ⟨s0, hs0⟩ =
        endColor e color hlim (s0.map (Function.Embedding.subtype (fun x => x ∈ H)))
          (by rw [Finset.card_map, hs0]) hsubMap := by
      dsimp [colorH]
    exact (endColor_congr e color hlim hmapped (by rw [Finset.card_map, hs0]) hcard0 hsubMap hsubH).symm.trans
      (hcolorH.symm.trans hinduced)
  have hset : insert m (s.erase m) = s := Finset.insert_erase hm
  have hsubeq : (⟨insert m (s.erase m), by rw [hset, hs]⟩ : {u : Finset α // u.card = k + 2}) =
      ⟨s, hs⟩ := Subtype.ext hset
  rw [← hsubeq]
  rw [← endColor_eq e color hlim hend hcard0 hsubH hmH hbelow]
  exact hcolorM

/-- The arity-one case of Lemma 2.5, at the bound written in `recursivePartitionBound`. -/
lemma erdos_one {ξ ν : Cardinal.{u}} (hξ : aleph0 ≤ ξ) (hν : aleph0 ≤ ν) :
    IsErdosRadoBound 1 ξ ν (recursivePartitionBound 1 ξ ν) := by
  intro α hα c
  have hR : recursivePartitionBound 1 ξ ν = Order.succ (ξ * ν) := rfl
  rw [hR] at hα
  exact singleton_homogeneous hξ hν hα (Cardinal.mk_ord_toType ξ) c

lemma partitionBound_infinite {n : ℕ} {ξ ν : Cardinal.{u}} (hn : 0 < n)
    (hξ : aleph0 ≤ ξ) (hν : aleph0 ≤ ν) : aleph0 ≤ recursivePartitionBound n ξ ν := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      have hmul : aleph0 ≤ ξ * ν :=
        hξ.trans (Cardinal.le_mul_right (aleph0_pos.trans_le hν).ne')
      exact hmul.trans (Order.le_succ (ξ * ν))
    | succ n =>
      have hprev : aleph0 ≤ recursivePartitionBound (n + 1) ξ ν := ih (Nat.succ_pos n)
      have hpow : aleph0 ≤ ξ ^ recursivePartitionBound (n + 1) ξ ν := by
        calc
          aleph0 ≤ ξ := hξ
          _ = ξ ^ (1 : Cardinal) := (Cardinal.power_one ξ).symm
          _ ≤ ξ ^ recursivePartitionBound (n + 1) ξ ν :=
            Cardinal.power_le_power_left (aleph0_pos.trans_le hξ).ne'
              (one_le_aleph0.trans hprev)
      exact hpow.trans (Order.le_succ _)

lemma bound_succ {ξ ν : Cardinal.{u}} {m : ℕ} (hm : 0 < m) :
    recursivePartitionBound (m + 1) ξ ν =
      Order.succ (ξ ^ recursivePartitionBound m ξ ν) := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
  rw [hn]
  rfl

lemma partition_power {ξ ρ : Cardinal.{u}} (hξ : aleph0 ≤ ξ) (hρ : aleph0 ≤ ρ) :
    ρ ≤ ξ ^ ρ ∧ (ξ ^ ρ) ^ ρ = ξ ^ ρ ∧ ρ * (ξ ^ ρ) = ξ ^ ρ := by
  have htwo : (2 : Cardinal) ≤ ξ := Cardinal.natCast_le_aleph0.trans hξ
  have hρb : ρ ≤ ξ ^ ρ := (Cardinal.cantor ρ).le.trans (Cardinal.power_le_power_right htwo)
  refine ⟨hρb, ?_, ?_⟩
  · rw [← Cardinal.power_mul, Cardinal.mul_eq_self hρ]
  · apply le_antisymm
    · exact (Cardinal.mul_le_max_of_aleph0_le_left hρ).trans (le_of_eq (max_eq_right hρb))
    · exact Cardinal.le_mul_left (aleph0_pos.trans_le hρ).ne'

/-- Least element of a nonempty set, in the well-order copied from the cardinal's initial
ordinal. -/
noncomputable def leastOf {α : Type u} (e : α ≃ (#α).ord.ToType) (s : Set α) (hs : s.Nonempty) : α :=
  e.symm (WellFoundedLT.min (e '' s) ⟨e (Classical.choose hs),
    Set.mem_image_of_mem e (Classical.choose_spec hs)⟩)

lemma leastOf_mem {α : Type u} (e : α ≃ (#α).ord.ToType) (s : Set α) (hs : s.Nonempty) :
    leastOf e s hs ∈ s := by
  have hmem := (wellFounded_lt (α := (#α).ord.ToType)).min_mem (e '' s) ⟨e (Classical.choose hs),
    Set.mem_image_of_mem e (Classical.choose_spec hs)⟩
  obtain ⟨x, hx, hxeq⟩ := hmem
  have hleast : leastOf e s hs = x :=
    (e.symm_apply_eq).mpr hxeq.symm
  exact hleast ▸ hx

lemma leastOf_le {α : Type u} (e : α ≃ (#α).ord.ToType) (s : Set α) (hs : s.Nonempty)
    {x : α} (hx : x ∈ s) : e (leastOf e s hs) ≤ e x := by
  let witness : (e '' s).Nonempty := ⟨e (Classical.choose hs),
    Set.mem_image_of_mem e (Classical.choose_spec hs)⟩
  have hspec := Classical.choose_spec ((wellFounded_lt (α := (#α).ord.ToType)).has_min (e '' s) witness)
  have hnot : ¬ e x < e (leastOf e s hs) := by
    have hmin : e (leastOf e s hs) =
        (wellFounded_lt (α := (#α).ord.ToType)).min (e '' s) witness := by
      unfold leastOf
      exact e.apply_symm_apply _
    rw [hmin]
    exact hspec.2 (e x) (Set.mem_image_of_mem e hx)
  exact le_of_not_gt hnot

lemma leastOf_eq {α : Type u} (e : α ≃ (#α).ord.ToType) (s : Set α)
    (h1 h2 : s.Nonempty) : leastOf e s h1 = leastOf e s h2 := by
  have h12 := leastOf_le e s h1 (leastOf_mem e s h2)
  have h21 := leastOf_le e s h2 (leastOf_mem e s h1)
  exact e.injective (le_antisymm h12 h21)

/-- Color of an index tuple read along a named branch, or a fixed default when the tuple does
not sit inside the named prefix. -/
noncomputable def subsetColor {m : ℕ} {idx α C : Type u} [LinearOrder idx]
    (color : {s : Finset α // s.card = m + 1} → C) (default : C)
    {i : idx} (g : {j : idx // j ≤ i} → α) (u : α)
    (s : {t : Finset idx // t.card = m}) : C :=
  if hsub : ∀ x ∈ s.1, x ≤ i then
    let gS : {x // x ∈ s.1} → α := fun z => g ⟨z.1, hsub z.1 z.2⟩
    if hinj : Function.Injective gS then
      let image := (s.1.attach).map ⟨gS, hinj⟩
      if hnot : u ∉ image then
        color ⟨insert u image, by
          rw [Finset.card_insert_of_notMem hnot, Finset.card_map, Finset.card_attach, s.2]⟩
      else
        default
    else
      default
  else
    default

/-- Named points on the branch up to and including the current node, read off earlier residuals. -/
noncomputable def nodePrefix {idx α : Type u} [LinearOrder idx]
    (e : α ≃ (#α).ord.ToType) (i : idx) (rec : ∀ j, j < i → Set α)
    (h : ({x | ∀ j (hj : j < i), x ∈ rec j hj} : Set α).Nonempty) :
    {j : idx // j ≤ i} → α :=
  let incoming : Set α := {x | ∀ j (hj : j < i), x ∈ rec j hj}
  let x := leastOf e incoming h
  fun z =>
    if hz : z.1 < i then
      leastOf e {y | ∀ t (ht : t < z.1), y ∈ rec t (lt_trans ht hz)}
        ⟨Classical.choose h, fun t ht => (Classical.choose_spec h) t (lt_trans ht hz)⟩
    else
      x

/-- One node of the residual tree. Name the least point of the incoming residual and keep the
child whose label, read from that named prefix, equals `f i`. -/
noncomputable def stageStep {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType))
    (i : idx) (rec : ∀ j, j < i → Set α) : Set α :=
  let incoming : Set α := {x | ∀ j (hj : j < i), x ∈ rec j hj}
  if h : incoming.Nonempty then
    let x := leastOf e incoming h
    let g := nodePrefix e i rec h
    {u | u ∈ incoming ∧ u ≠ x ∧ ∀ s, subsetColor color default g u s = f i s}
  else
    ∅

/-- Outgoing residual of the node at height `i` on the branch selected by `f`. The root residual
is the whole ground set, recovered as the empty intersection. -/
noncomputable def stage {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) : idx → Set α :=
  WellFounded.fix (inferInstance : WellFounded ((· < ·) : idx → idx → Prop))
    (fun i rec => stageStep e color default f i rec)

lemma stage_eq {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx) :
    stage e color default f i =
      stageStep e color default f i (fun j _hj => stage e color default f j) := by
  unfold stage
  exact WellFounded.fix_eq _ _ i

/-- The residual entering the node at height `i`: every earlier outgoing residual. -/
def incoming {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx) : Set α :=
  {x | ∀ j (hj : j < i), x ∈ stage e color default f j}

/-- The point named at height `i`, when the incoming residual is nonempty. -/
noncomputable def namedAt {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx) : Option α :=
  if h : (incoming e color default f i).Nonempty then
    some (leastOf e (incoming e color default f i) h)
  else
    none

lemma colorFun_le {idx : Type u} [LinearOrder idx] {ξ ρ : Cardinal.{u}}
    (hξ : aleph0 ≤ ξ) (hρ : aleph0 ≤ ρ) (hidx : #idx ≤ ρ) {m : ℕ} (hm : 0 < m) :
    #({t : Finset idx // t.card = m} → ξ.ord.ToType) ≤ ξ ^ ρ := by
  have hsub : #{t : Finset idx // t.card = m} ≤ ρ := card_ksubset hidx hρ hm
  have hfun : #({t : Finset idx // t.card = m} → ξ.ord.ToType) =
      #(ξ.ord.ToType) ^ #{t : Finset idx // t.card = m} :=
    (Cardinal.power_def (ξ.ord.ToType) _).symm
  rw [hfun, Cardinal.mk_ord_toType]
  exact Cardinal.power_le_power_left (aleph0_pos.trans_le hξ).ne' hsub

lemma branch_le {idx : Type u} [LinearOrder idx] {ξ ρ : Cardinal.{u}}
    (hξ : aleph0 ≤ ξ) (hρ : aleph0 ≤ ρ) (hidx : #idx = ρ) {m : ℕ} (hm : 0 < m) :
    #idx * #((idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType))) ≤ ξ ^ ρ := by
  have hfun : #({t : Finset idx // t.card = m} → ξ.ord.ToType) ≤ ξ ^ ρ :=
    colorFun_le hξ hρ hidx.le hm
  have hspace : #(idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) =
      #({t : Finset idx // t.card = m} → ξ.ord.ToType) ^ #idx :=
    (Cardinal.power_def _ idx).symm
  have hpow : #({t : Finset idx // t.card = m} → ξ.ord.ToType) ^ #idx ≤ (ξ ^ ρ) ^ #idx :=
    Cardinal.power_le_power_right hfun
  have hself : (ξ ^ ρ) ^ ρ = ξ ^ ρ := (partition_power hξ hρ).2.1
  have hprod : #idx * (ξ ^ ρ) = ξ ^ ρ := by
    simpa [hidx] using (partition_power hξ hρ).2.2
  calc
    #idx * #(idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType))
        = #idx * (#({t : Finset idx // t.card = m} → ξ.ord.ToType) ^ #idx) := by rw [hspace]
    _ ≤ #idx * ((ξ ^ ρ) ^ #idx) := mul_le_mul_of_nonneg_left hpow (Cardinal.zero_le _)
    _ = #idx * ((ξ ^ ρ) ^ ρ) := by rw [hidx]
    _ = #idx * (ξ ^ ρ) := by rw [hself]
    _ = ξ ^ ρ := hprod

lemma named_le {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ ρ : Cardinal.{u}} (hξ : aleph0 ≤ ξ) (hρ : aleph0 ≤ ρ) (hidx : #idx = ρ) (hm : 0 < m)
    (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType) :
    #{x : α | ∃ (p : (idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) × idx),
        namedAt e color default p.1 p.2 = some x} ≤ ξ ^ ρ := by
  let Removed := {x : α | ∃ (p : (idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) × idx),
    namedAt e color default p.1 p.2 = some x}
  let pick : ↥Removed →
      (idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) × idx :=
    fun z => Classical.choose z.2
  have hinj : Function.Injective pick := by
    intro a b hab
    have ha := Classical.choose_spec a.2
    have hb := Classical.choose_spec b.2
    dsimp [pick] at hab
    rw [hab] at ha
    have : some (a : α) = some (b : α) := ha.symm.trans hb
    exact Subtype.ext (Option.some.inj this)
  have hprod : #((idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) × idx) =
      #(idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) * #idx := by
    simpa using Cardinal.mk_prod _ _
  calc
    #Removed ≤ #((idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) × idx) :=
      Cardinal.mk_le_of_injective hinj
    _ = #(idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) * #idx := hprod
    _ = #idx * #(idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) := mul_comm _ _
    _ ≤ ξ ^ ρ := branch_le hξ hρ hidx hm

lemma exists_unremoved {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ ρ : Cardinal.{u}} (hξ : aleph0 ≤ ξ) (hρ : aleph0 ≤ ρ) (hidx : #idx = ρ) (hm : 0 < m)
    (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (hα : Order.succ (ξ ^ ρ) ≤ #α) :
    ∃ u : α, ∀ (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx),
      namedAt e color default f i ≠ some u := by
  by_contra h
  have hcov : ∀ u : α, ∃ p : (idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) × idx,
      namedAt e color default p.1 p.2 = some u := by
    intro u
    have hnot : ¬ ∀ (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx),
        namedAt e color default f i ≠ some u := by
      intro hall
      exact h ⟨u, hall⟩
    by_contra hnone
    exact hnot (fun f i hfi => hnone ⟨(f, i), hfi⟩)
  let Removed := {x : α | ∃ p : (idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) × idx,
    namedAt e color default p.1 p.2 = some x}
  have hsub : (Set.univ : Set α) ⊆ Removed := fun u _ => hcov u
  have hcard : #α ≤ #Removed := by
    calc
      #α = #(Set.univ : Set α) := Cardinal.mk_univ.symm
      _ ≤ #Removed := Cardinal.mk_le_mk_of_subset hsub
  have hlt : ξ ^ ρ < #α := (Order.succ_le_iff).mp hα
  exact not_le_of_gt hlt (hcard.trans (named_le hξ hρ hidx hm e color default))

/-- The branch that follows `u`: at each height, retain the child with `u`'s label. -/
noncomputable def follow {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (u : α) : idx → Set α :=
  WellFounded.fix (inferInstance : WellFounded ((· < ·) : idx → idx → Prop))
    (fun (i : idx) (rec : ∀ j, j < i → Set α) =>
      let incoming : Set α := {x | ∀ j (hj : j < i), x ∈ rec j hj}
      if h : incoming.Nonempty then
        let x := leastOf e incoming h
        let g := nodePrefix e i rec h
        let label : {t : Finset idx // t.card = m} → ξ.ord.ToType :=
          fun s => subsetColor color default g u s
        {v | v ∈ incoming ∧ v ≠ x ∧ ∀ s, subsetColor color default g v s = label s}
      else
        ∅)

lemma follow_eq {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (u : α) (i : idx) :
    follow e color default u i =
      (let incoming : Set α := {x | ∀ j (hj : j < i), x ∈ follow e color default u j}
       if h : incoming.Nonempty then
         let x := leastOf e incoming h
         let g := nodePrefix e i (fun j _hj => follow e color default u j) h
         let label : {t : Finset idx // t.card = m} → ξ.ord.ToType :=
           fun s => subsetColor color default g u s
         {v | v ∈ incoming ∧ v ≠ x ∧ ∀ s, subsetColor color default g v s = label s}
       else
         ∅) := by
  unfold follow
  exact WellFounded.fix_eq _ _ i

/-- Labels of `u` along the branch that follows `u`. -/
noncomputable def followLabel {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (u : α) (i : idx) : {t : Finset idx // t.card = m} → ξ.ord.ToType :=
  let incoming : Set α := {x | ∀ j (hj : j < i), x ∈ follow e color default u j}
  if h : incoming.Nonempty then
    fun s => subsetColor color default (nodePrefix e i (fun j _hj => follow e color default u j) h) u s
  else
    fun _ => default

lemma leastOf_of_eq {α : Type u} (e : α ≃ (#α).ord.ToType) {s1 s2 : Set α}
    (hset : s1 = s2) (h1 : s1.Nonempty) (h2 : s2.Nonempty) :
    leastOf e s1 h1 = leastOf e s2 h2 := by
  subst hset
  exact leastOf_eq e s1 h1 h2

lemma nodePrefix_congr {idx α : Type u} [LinearOrder idx]
    (e : α ≃ (#α).ord.ToType) {i : idx}
    {rec1 rec2 : ∀ j, j < i → Set α}
    (hrec : ∀ j (hj : j < i), rec1 j hj = rec2 j hj)
    (h1 : ({x | ∀ j (hj : j < i), x ∈ rec1 j hj} : Set α).Nonempty)
    (h2 : ({x | ∀ j (hj : j < i), x ∈ rec2 j hj} : Set α).Nonempty) :
    nodePrefix e i rec1 h1 = nodePrefix e i rec2 h2 := by
  have hset : ({x | ∀ j (hj : j < i), x ∈ rec1 j hj} : Set α) =
      {x | ∀ j (hj : j < i), x ∈ rec2 j hj} := by
    ext x
    constructor
    · intro hx j hj
      rw [← hrec j hj]
      exact hx j hj
    · intro hx j hj
      rw [hrec j hj]
      exact hx j hj
  funext z
  unfold nodePrefix
  by_cases hz : z.1 < i
  · simp only [hz, dite_true]
    have hsub : ({y | ∀ t (ht : t < z.1), y ∈ rec1 t (lt_trans ht hz)} : Set α) =
        {y | ∀ t (ht : t < z.1), y ∈ rec2 t (lt_trans ht hz)} := by
      ext y
      constructor
      · intro hy t ht
        rw [← hrec t (lt_trans ht hz)]
        exact hy t ht
      · intro hy t ht
        rw [hrec t (lt_trans ht hz)]
        exact hy t ht
    exact leastOf_of_eq e hsub
      ⟨Classical.choose h1, fun t ht => (Classical.choose_spec h1) t (lt_trans ht hz)⟩
      ⟨Classical.choose h2, fun t ht => (Classical.choose_spec h2) t (lt_trans ht hz)⟩
  · simp only [hz, dite_false]
    exact leastOf_of_eq e hset h1 h2

lemma follow_eq_stage {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (u : α) (i : idx) :
    stage e color default (followLabel e color default u) i = follow e color default u i := by
  induction i using WellFoundedLT.induction with
  | ind i IH =>
    have hrec : ∀ j (hj : j < i),
        stage e color default (followLabel e color default u) j = follow e color default u j :=
      fun j hj => IH j hj
    rw [stage_eq, follow_eq]
    unfold stageStep
    have hset : ({x | ∀ j (hj : j < i),
        x ∈ stage e color default (followLabel e color default u) j} : Set α) =
        {x | ∀ j (hj : j < i), x ∈ follow e color default u j} := by
      ext x
      constructor
      · intro hx j hj
        rw [← hrec j hj]
        exact hx j hj
      · intro hx j hj
        rw [hrec j hj]
        exact hx j hj
    by_cases h : ({x | ∀ j (hj : j < i), x ∈ follow e color default u j} : Set α).Nonempty
    · have h' : ({x | ∀ j (hj : j < i),
          x ∈ stage e color default (followLabel e color default u) j} : Set α).Nonempty :=
        hset.symm ▸ h
      simp only [dif_pos h, dif_pos h']
      ext v
      have hleast := leastOf_of_eq e hset h' h
      have hpre := nodePrefix_congr e (fun j hj => hrec j hj) h' h
      have hlabel : followLabel e color default u i =
          fun s => subsetColor color default
            (nodePrefix e i (fun j _hj => follow e color default u j) h) u s := by
        unfold followLabel
        rw [dif_pos h]
      constructor
      · intro hv
        refine ⟨hset ▸ hv.1, ?_, ?_⟩
        · intro heq
          exact hv.2.1 (heq.trans hleast.symm)
        · intro s
          have hvlabel := hv.2.2 s
          rw [hlabel] at hvlabel
          rw [hpre] at hvlabel
          exact hvlabel
      · intro hv
        refine ⟨hset.symm ▸ hv.1, ?_, ?_⟩
        · intro heq
          exact hv.2.1 (heq.trans hleast)
        · intro s
          have hvlabel := hv.2.2 s
          rw [hpre]
          rw [hlabel]
          exact hvlabel
    · have h' : ¬ ({x | ∀ j (hj : j < i),
          x ∈ stage e color default (followLabel e color default u) j} : Set α).Nonempty := by
        intro hne
        exact h (hset ▸ hne)
      simp only [dif_neg h, dif_neg h']

lemma survivor_in_follow {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    {u : α}
    (hu : ∀ (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx),
      namedAt e color default f i ≠ some u)
    (i : idx) : u ∈ follow e color default u i := by
  induction i using WellFoundedLT.induction with
  | ind i IH =>
    rw [follow_eq]
    have hinc : u ∈ ({x | ∀ j (hj : j < i), x ∈ follow e color default u j} : Set α) :=
      fun j hj => IH j hj
    have hne : ({x | ∀ j (hj : j < i), x ∈ follow e color default u j} : Set α).Nonempty :=
      ⟨u, hinc⟩
    simp only [dif_pos hne]
    refine ⟨hinc, ?_, fun s => rfl⟩
    intro heq
    have hstage : ({x | ∀ j (hj : j < i),
        x ∈ stage e color default (followLabel e color default u) j} : Set α) =
        {x | ∀ j (hj : j < i), x ∈ follow e color default u j} := by
      ext x
      constructor
      · intro hx j hj
        have hmem : x ∈ stage e color default (followLabel e color default u) j := hx j hj
        rw [follow_eq_stage e color default u j] at hmem
        exact hmem
      · intro hx j hj
        rw [follow_eq_stage e color default u j]
        exact hx j hj
    have hnamed : namedAt e color default (followLabel e color default u) i = some u := by
      unfold namedAt
      have hneS : (incoming e color default (followLabel e color default u) i).Nonempty := by
        unfold incoming
        exact hstage.symm ▸ hne
      rw [dif_pos hneS]
      exact congrArg some ((leastOf_of_eq e hstage hneS hne).trans heq.symm)
    exact hu (followLabel e color default u) i hnamed

/-- The point named at height `i` on the branch of a point that is never removed. -/
noncomputable def branchPoint {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    {u : α}
    (hu : ∀ (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx),
      namedAt e color default f i ≠ some u)
    (i : idx) : α :=
  leastOf e {x | ∀ j (hj : j < i), x ∈ follow e color default u j}
    ⟨u, fun j hj => survivor_in_follow e color default hu j⟩

lemma branchPoint_mem_follow {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    {u : α}
    (hu : ∀ (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx),
      namedAt e color default f i ≠ some u)
    {j i : idx} (hji : j < i) :
    branchPoint e color default hu i ∈ follow e color default u j := by
  have hmem := leastOf_mem e
    ({x | ∀ t (ht : t < i), x ∈ follow e color default u t} : Set α)
    ⟨u, fun t ht => survivor_in_follow e color default hu t⟩
  exact hmem j hji

lemma branchPoint_lt {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    {u : α}
    (hu : ∀ (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx),
      namedAt e color default f i ≠ some u)
    {j i : idx} (hji : j < i) :
    e (branchPoint e color default hu j) < e (branchPoint e color default hu i) := by
  have hmem : branchPoint e color default hu i ∈
      {x | ∀ t (ht : t < j), x ∈ follow e color default u t} := by
    intro t ht
    exact branchPoint_mem_follow e color default hu (lt_trans ht hji)
  have hne : branchPoint e color default hu i ≠ branchPoint e color default hu j := by
    intro heq
    have hfollow := branchPoint_mem_follow e color default hu hji
    rw [follow_eq] at hfollow
    have hneI : ({x | ∀ t (ht : t < j), x ∈ follow e color default u t} : Set α).Nonempty :=
      ⟨u, fun t ht => survivor_in_follow e color default hu t⟩
    simp only [dif_pos hneI] at hfollow
    exact hfollow.2.1 (heq.trans (leastOf_eq e _ hneI _).symm)
  exact lt_of_le_of_ne (leastOf_le e _ _ hmem) (fun hEq => hne (e.injective hEq).symm)

lemma branchPoint_injective {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    {u : α}
    (hu : ∀ (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx),
      namedAt e color default f i ≠ some u) :
    Function.Injective (branchPoint e color default hu) := by
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd hab (ne_of_apply_ne e (branchPoint_lt e color default hu h).ne)
  · exact h
  · exact absurd hab.symm (ne_of_apply_ne e (branchPoint_lt e color default hu h).ne)

lemma subsetColor_apply {m : ℕ} {idx α C : Type u} [LinearOrder idx]
    (color : {s : Finset α // s.card = m + 1} → C) (default : C)
    {i : idx} (g : {j : idx // j ≤ i} → α)
    (s : {t : Finset idx // t.card = m})
    (hsub : ∀ x ∈ s.1, x ≤ i)
    (hinj : Function.Injective (fun z : {x // x ∈ s.1} => g ⟨z.1, hsub z.1 z.2⟩))
    {v : α} (hnot : v ∉ (s.1.attach).map ⟨fun z => g ⟨z.1, hsub z.1 z.2⟩, hinj⟩) :
    subsetColor color default g v s =
      color ⟨insert v ((s.1.attach).map ⟨fun z => g ⟨z.1, hsub z.1 z.2⟩, hinj⟩), by
        rw [Finset.card_insert_of_notMem hnot, Finset.card_map, Finset.card_attach, s.2]⟩ := by
  unfold subsetColor
  rw [dif_pos hsub, dif_pos hinj, dif_pos hnot]

lemma nodePrefix_point {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx]
    {ξ : Cardinal.{u}} (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    {u : α}
    (hu : ∀ (f : idx → ({t : Finset idx // t.card = m} → ξ.ord.ToType)) (i : idx),
      namedAt e color default f i ≠ some u)
    {i j : idx} (hj : j ≤ i)
    (hinc : ({x | ∀ t (ht : t < i), x ∈ follow e color default u t} : Set α).Nonempty) :
    nodePrefix e i (fun t _ht => follow e color default u t) hinc ⟨j, hj⟩ =
      branchPoint e color default hu j := by
  unfold nodePrefix
  by_cases hlt : j < i
  · simp only [hlt, dite_true]
    exact leastOf_eq e
      ({y | ∀ t (ht : t < j), y ∈ follow e color default u t} : Set α)
      ⟨Classical.choose hinc, fun t ht => (Classical.choose_spec hinc) t (lt_trans ht hlt)⟩
      ⟨u, fun t ht => survivor_in_follow e color default hu t⟩
  · simp only [hlt, dite_false]
    have hji : j = i := le_antisymm hj (le_of_not_gt hlt)
    subst hji
    exact leastOf_eq e _ hinc ⟨u, fun t ht => survivor_in_follow e color default hu t⟩

lemma branch_end {m : ℕ} {idx α : Type u} [LinearOrder idx] [WellFoundedLT idx] [NoMaxOrder idx]
    {ξ ρ : Cardinal.{u}} (hξ : aleph0 ≤ ξ) (hρ : aleph0 ≤ ρ) (hidx : #idx = ρ) (hm : 0 < m)
    (e : α ≃ (#α).ord.ToType)
    (color : {s : Finset α // s.card = m + 1} → ξ.ord.ToType) (default : ξ.ord.ToType)
    (hα : Order.succ (ξ ^ ρ) ≤ #α) :
    ∃ H : Set α, (∀ x ∈ H, ∃ y ∈ H, e x < e y) ∧ ρ ≤ #H ∧
      ∀ (s : Finset α) (_hs : s.card = m), (∀ x ∈ s, x ∈ H) →
        ∀ x y, x ∈ H → y ∈ H → (∀ z ∈ s, e z < e x) → (∀ z ∈ s, e z < e y) →
          ∀ (hx : (insert x s).card = m + 1) (hy : (insert y s).card = m + 1),
            color ⟨insert x s, hx⟩ = color ⟨insert y s, hy⟩ := by
  obtain ⟨u, hu⟩ := exists_unremoved hξ hρ hidx hm e color default hα
  let point := branchPoint e color default hu
  let H : Set α := Set.range point
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hx
    obtain ⟨j, hji⟩ := exists_gt i
    exact ⟨point j, Set.mem_range_self j, branchPoint_lt e color default hu hji⟩
  · rw [← hidx]
    exact Cardinal.mk_le_of_injective (f := fun i => (⟨point i, Set.mem_range_self i⟩ : ↥H))
      (fun a b hab => branchPoint_injective e color default hu (congrArg Subtype.val hab))
  · intro s hs hH x y hx hy haboveX haboveY hcardX hcardY
    let idxOf : (p : α) → p ∈ H → idx := fun p hp => Classical.choose (Set.mem_range.mp hp)
    have hidxOf : ∀ p (hp : p ∈ H), point (idxOf p hp) = p :=
      fun p hp => Classical.choose_spec (Set.mem_range.mp hp)
    let heights : Finset idx := s.attach.map ⟨fun z => idxOf z.1 (hH z.1 z.2), by
      intro a b hab
      apply Subtype.ext
      have hpoints := congrArg point hab
      rw [hidxOf a.1 (hH a.1 a.2), hidxOf b.1 (hH b.1 b.2)] at hpoints
      exact hpoints⟩
    have hcardHeights : heights.card = m := by
      rw [Finset.card_map, Finset.card_attach, hs]
    have hneHeights : heights.Nonempty := Finset.card_pos.mp (by rw [hcardHeights]; omega)
    let i : idx := heights.max' hneHeights
    have hi : i ∈ heights := Finset.max'_mem heights hneHeights
    obtain ⟨z0, hz0, hz0i⟩ := Finset.mem_map.mp hi
    have hz0i' : idxOf z0.1 (hH z0.1 z0.2) = i := hz0i
    have hinc : ({p | ∀ t (ht : t < i), p ∈ follow e color default u t} : Set α).Nonempty :=
      ⟨u, fun t _ht => survivor_in_follow e color default hu t⟩
    let g := nodePrefix e i (fun t _ht => follow e color default u t) hinc
    have hbelowIdx : idxOf x hx > i ∧ idxOf y hy > i := by
      constructor
      · by_contra hle
        have hle' : idxOf x hx ≤ i := le_of_not_gt hle
        have hleE : e x ≤ e (point i) := by
          by_cases hlt : idxOf x hx < i
          · rw [← hidxOf x hx]
            exact (branchPoint_lt e color default hu hlt).le
          · have heqi : idxOf x hx = i := le_antisymm hle' (le_of_not_gt hlt)
            rw [← hidxOf x hx, heqi]
        have hzE : e (z0.1) < e x := haboveX z0.1 z0.2
        rw [← hidxOf z0.1 (hH z0.1 z0.2), hz0i'] at hzE
        exact (not_le_of_gt hzE) hleE
      · by_contra hle
        have hle' : idxOf y hy ≤ i := le_of_not_gt hle
        have hleE : e y ≤ e (point i) := by
          by_cases hlt : idxOf y hy < i
          · rw [← hidxOf y hy]
            exact (branchPoint_lt e color default hu hlt).le
          · have heqi : idxOf y hy = i := le_antisymm hle' (le_of_not_gt hlt)
            rw [← hidxOf y hy, heqi]
        have hzE : e (z0.1) < e y := haboveY z0.1 z0.2
        rw [← hidxOf z0.1 (hH z0.1 z0.2), hz0i'] at hzE
        exact (not_le_of_gt hzE) hleE
    have hxFollow : x ∈ follow e color default u i := by
      rw [← hidxOf x hx]
      exact branchPoint_mem_follow e color default hu hbelowIdx.1
    have hyFollow : y ∈ follow e color default u i := by
      rw [← hidxOf y hy]
      exact branchPoint_mem_follow e color default hu hbelowIdx.2
    rw [follow_eq] at hxFollow hyFollow
    simp only [dite_eq_left hinc] at hxFollow hyFollow
    let sIdx : {t : Finset idx // t.card = m} := ⟨heights, hcardHeights⟩
    have hsubIdx : ∀ j ∈ heights, j ≤ i := fun j hj => Finset.le_max' heights j hj
    have hprefix : ∀ j (hj : j ∈ heights), g ⟨j, hsubIdx j hj⟩ = point j :=
      fun j hj => nodePrefix_point e color default hu (hsubIdx j hj) hinc
    have hinjG : Function.Injective (fun z : {j // j ∈ heights} => g ⟨z.1, hsubIdx z.1 z.2⟩) := by
      intro a b hab
      have hpts : point a.1 = point b.1 := by
        rw [← hprefix a.1 a.2, ← hprefix b.1 b.2]
        exact hab
      exact Subtype.ext (branchPoint_injective e color default hu hpts)
    let image := (heights.attach).map ⟨fun z => g ⟨z.1, hsubIdx z.1 z.2⟩, hinjG⟩
    have himage : image = s := by
      ext p
      constructor
      · intro hp
        obtain ⟨z, hz, hpz⟩ := Finset.mem_map.mp hp
        have hpz' : g ⟨z.1, hsubIdx z.1 z.2⟩ = p := hpz
        have hpPoint : p = point z.1 := by rw [← hpz', hprefix z.1 z.2]
        obtain ⟨w, hw, hwz⟩ := Finset.mem_map.mp z.2
        have hwz' : idxOf w.1 (hH w.1 w.2) = z.1 := hwz
        have : p = w.1 := by
          rw [hpPoint, ← hwz', hidxOf w.1 (hH w.1 w.2)]
        exact this ▸ w.2
      · intro hp
        have hmem : idxOf p (hH p hp) ∈ heights :=
          Finset.mem_map.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩
        refine Finset.mem_map.mpr ⟨⟨idxOf p (hH p hp), hmem⟩, Finset.mem_attach _ _, ?_⟩
        have hgoal : g ⟨idxOf p (hH p hp), hsubIdx (idxOf p (hH p hp)) hmem⟩ = p := by
          rw [hprefix (idxOf p (hH p hp)) hmem, hidxOf p (hH p hp)]
        exact hgoal
    have hxNot : x ∉ image := by
      rw [himage]
      intro hxS
      exact (lt_irrefl (e x)) (haboveX x hxS)
    have hyNot : y ∉ image := by
      rw [himage]
      intro hyS
      exact (lt_irrefl (e y)) (haboveY y hyS)
    have hxColor := subsetColor_apply color default g sIdx hsubIdx hinjG hxNot
    have hyColor := subsetColor_apply color default g sIdx hsubIdx hinjG hyNot
    have hxLabel := hxFollow.2.2 sIdx
    have hyLabel := hyFollow.2.2 sIdx
    have hxy : subsetColor color default g x sIdx = subsetColor color default g y sIdx :=
      hxLabel.trans hyLabel.symm
    rw [hxColor, hyColor] at hxy
    have hxSet : (⟨insert x image, by
        rw [Finset.card_insert_of_notMem hxNot, Finset.card_map, Finset.card_attach, hcardHeights]⟩ :
        {t : Finset α // t.card = m + 1}) = ⟨insert x s, hcardX⟩ :=
      Subtype.ext (by
        show insert x image = insert x s
        rw [himage])
    have hySet : (⟨insert y image, by
        rw [Finset.card_insert_of_notMem hyNot, Finset.card_map, Finset.card_attach, hcardHeights]⟩ :
        {t : Finset α // t.card = m + 1}) = ⟨insert y s, hcardY⟩ :=
      Subtype.ext (by
        show insert y image = insert y s
        rw [himage])
    rw [hxSet, hySet] at hxy
    exact hxy

lemma erdos_step {k : ℕ} {ξ ν : Cardinal.{u}} (hξ : aleph0 ≤ ξ) (hν : aleph0 ≤ ν)
    (ih : IsErdosRadoBound (k + 1) ξ ν (recursivePartitionBound (k + 1) ξ ν)) :
    IsErdosRadoBound (k + 2) ξ ν (recursivePartitionBound (k + 2) ξ ν) := by
  intro α hα color
  have hm : 0 < k + 1 := Nat.succ_pos k
  have hbound : recursivePartitionBound (k + 2) ξ ν =
      Order.succ (ξ ^ recursivePartitionBound (k + 1) ξ ν) := by
    rw [show k + 2 = (k + 1) + 1 from rfl]
    exact bound_succ hm
  rw [hbound] at hα
  let ρ := recursivePartitionBound (k + 1) ξ ν
  have hρ : aleph0 ≤ ρ := partitionBound_infinite hm hξ hν
  let idx := ρ.ord.ToType
  have hidx : #idx = ρ := Cardinal.mk_ord_toType ρ
  haveI : NoMaxOrder idx := Cardinal.noMaxOrder hρ
  obtain ⟨e⟩ := Cardinal.eq.mp (Cardinal.mk_ord_toType (#α)).symm
  have hC : Nonempty (ξ.ord.ToType) := by
    rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_ord_toType]
    exact (aleph0_pos.trans_le hξ).ne'
  let default := Classical.choice hC
  obtain ⟨H, hlim, hcard, hend⟩ :=
    branch_end hξ hρ hidx hm e color default hα
  obtain ⟨t, _, ht, c, hc⟩ := homogeneous_of_end e color hlim hend ih (by
    simpa [hidx] using hcard)
  exact ⟨t, ht, c, hc⟩

lemma erdos_all {ξ ν : Cardinal.{u}} (hξ : aleph0 ≤ ξ) (hν : aleph0 ≤ ν) (n : ℕ) (hn : 0 < n) :
    IsErdosRadoBound n ξ ν (recursivePartitionBound n ξ ν) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => exact erdos_one hξ hν
    | succ k => exact erdos_step hξ hν (ih (Nat.succ_pos k))

lemma erdos_color {n : ℕ} {ξ ν : Cardinal.{u}} (hξ : aleph0 ≤ ξ) (hν : aleph0 ≤ ν) (hn : 0 < n)
    {α : Type u} (hα : recursivePartitionBound n ξ ν ≤ #α) {C : Type u} (hC : #C = ξ)
    (color : {s : Finset α // s.card = n} → C) :
    ∃ H : Set α, ν ≤ #H ∧ ∃ c : C,
      ∀ (s : Finset α) (hs : s.card = n), (∀ x ∈ s, x ∈ H) → color ⟨s, hs⟩ = c := by
  obtain ⟨e⟩ := Cardinal.eq.mp (hC.trans (Cardinal.mk_ord_toType ξ).symm)
  obtain ⟨H, hH, c, hc⟩ := erdos_all hξ hν n hn α hα (fun s => e (color s))
  refine ⟨H, hH, e.symm c, ?_⟩
  intro s hs hsub
  exact (e.eq_symm_apply).mpr (hc s hs hsub)

/-- Several arities at once, thinned from the last arity backward. A homogeneous set for an
earlier coloring stays homogeneous after a later thinning. -/
lemma joint_partition {ξ : Cardinal.{u}} (hξ : aleph0 ≤ ξ) (n : ℕ) {μ : Cardinal.{u}}
    (hμ : aleph0 ≤ μ) (arity : Fin n → ℕ) (hpos : ∀ i, 0 < arity i) :
    ∃ R' : Cardinal.{u}, aleph0 ≤ R' ∧
      ∀ (ι : Type u), R' ≤ #ι →
        ∀ (C : Fin n → Type u), (∀ i, #(C i) = ξ) →
          ∀ color : (i : Fin n) → {s : Finset ι // s.card = arity i} → C i,
            ∃ H : Set ι, μ ≤ #H ∧
              ∀ i, ∃ c : C i, ∀ (s : Finset ι) (hs : s.card = arity i),
                (∀ x ∈ s, x ∈ H) → color i ⟨s, hs⟩ = c := by
  induction n generalizing μ with
  | zero =>
    refine ⟨μ, hμ, ?_⟩
    intro ι hι _ _ _
    refine ⟨(Set.univ : Set ι), ?_, ?_⟩
    · rw [Cardinal.mk_univ]
      exact hι
    · intro i
      exact Fin.elim0 i
  | succ n ih =>
    let last := arity (Fin.last n)
    let σ := recursivePartitionBound last ξ μ
    have hσ : aleph0 ≤ σ := partitionBound_infinite (hpos (Fin.last n)) hξ hμ
    obtain ⟨Rtail, hRtail, htail⟩ := ih hσ (fun i => arity i.castSucc) (fun i => hpos i.castSucc)
    refine ⟨Rtail, hRtail, ?_⟩
    intro ι hι C hC color
    let Ctail : Fin n → Type u := fun i => C i.castSucc
    let colorTail : (i : Fin n) → {s : Finset ι // s.card = arity i.castSucc} → Ctail i :=
      fun i s => color i.castSucc s
    obtain ⟨H0, hH0, hfront⟩ := htail ι hι Ctail (fun i => hC i.castSucc) colorTail
    let colorLast : {s : Finset (↥H0) // s.card = last} → C (Fin.last n) := fun s =>
      color (Fin.last n) ⟨s.1.map (Function.Embedding.subtype (fun x => x ∈ H0)), by
        rw [Finset.card_map, s.2]⟩
    obtain ⟨t0, ht0, cLast, hcLast⟩ :=
      erdos_color hξ hμ (hpos (Fin.last n)) (by simpa using hH0) (hC (Fin.last n)) colorLast
    let H : Set ι := (Subtype.val : ↥H0 → ι) '' t0
    have hHH0 : H ⊆ H0 := by
      intro x hx
      obtain ⟨z, _, rfl⟩ := hx
      exact z.2
    refine ⟨H, ?_, ?_⟩
    · exact ht0.trans_eq (Cardinal.mk_image_eq Subtype.val_injective).symm
    · intro i
      cases i using Fin.lastCases with
      | last =>
        refine ⟨cLast, ?_⟩
        intro s hs hsub
        classical
        have hsub0 : ∀ x ∈ s, x ∈ H0 := fun x hx => hHH0 (hsub x hx)
        have hfilter : s.filter (fun x => x ∈ H0) = s := by
          ext x
          constructor
          · intro hx
            exact (Finset.mem_filter.mp hx).1
          · intro hx
            exact Finset.mem_filter.mpr ⟨hx, hsub0 x hx⟩
        let s0 := s.subtype (fun x => x ∈ H0)
        have hs0 : s0.card = last := by
          rw [Finset.card_subtype, hfilter, hs]
        have hs0t : ∀ z ∈ s0, z ∈ t0 := by
          intro z hz
          have hzS : (z : ι) ∈ s := (Finset.mem_subtype).mp hz
          have hzH : (z : ι) ∈ H := hsub _ hzS
          obtain ⟨w, hw, hwz⟩ := hzH
          exact (show w = z from Subtype.ext hwz) ▸ hw
        have hmapped : s0.map (Function.Embedding.subtype (fun x => x ∈ H0)) = s := by
          ext x
          constructor
          · intro hx
            obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
            exact (Finset.mem_subtype).mp hz
          · intro hx
            exact Finset.mem_map.mpr ⟨⟨x, hsub0 x hx⟩, (Finset.mem_subtype).mpr hx, rfl⟩
        have hcolor := hcLast s0 hs0 hs0t
        dsimp [colorLast] at hcolor
        have hcong : color (Fin.last n)
            ⟨s0.map (Function.Embedding.subtype (fun x => x ∈ H0)), by rw [Finset.card_map, hs0]⟩ =
            color (Fin.last n) ⟨s, hs⟩ := by
          suffices ∀ (t : Finset ι) (ht : t.card = last), t = s →
              color (Fin.last n) ⟨t, ht⟩ = color (Fin.last n) ⟨s, hs⟩ from
            this _ (by rw [Finset.card_map, hs0]) hmapped
          intro t ht htS
          subst htS
          congr
        exact hcong.symm.trans hcolor
      | cast i =>
        obtain ⟨c, hc⟩ := hfront i
        refine ⟨c, ?_⟩
        intro s hs hsub
        exact hc s hs (fun x hx => hHH0 (hsub x hx))

end
end AEC
