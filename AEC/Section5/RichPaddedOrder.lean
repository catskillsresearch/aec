module

public import AEC.Section5.PaddedOrder
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.PiLex
public import Mathlib.Order.Prod.Lex.Basic
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Ordinal
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Rich padded orders (Lemma 5.5)

Hausdorff eventually-zero `Fin 3`-sequences on `η⁺`, then lex sum along `μ · η⁺`.
-/

@[expose] public section

namespace AEC
section

universe u

open Cardinal Classical Set Function

noncomputable section

/-! ## Stages -/

structure Stage (η : Cardinal.{u}) where
  val : (Order.succ η).ord.ToType

def Stage.ord {η : Cardinal.{u}} (a : Stage η) : Ordinal.{u} :=
  (Ordinal.ToType.toOrd a.val).1

theorem Stage.ord_lt_succ {η : Cardinal.{u}} (a : Stage η) :
    a.ord < (Order.succ η).ord :=
  (Ordinal.ToType.toOrd a.val).2

theorem Stage.ord_injective (η : Cardinal.{u}) :
    Function.Injective (Stage.ord (η := η)) := by
  intro a b h
  have := Ordinal.ToType.mk.symm.injective (Subtype.ext h)
  cases a; cases b; simp_all

instance (η : Cardinal.{u}) : LinearOrder (Stage η) :=
  LinearOrder.lift' Stage.ord (Stage.ord_injective η)

instance (η : Cardinal.{u}) : WellFoundedLT (Stage η) :=
  show WellFounded _ from WellFounded.onFun (f := Stage.ord (η := η)) Ordinal.lt_wf

theorem Stage.exists_gt (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (a : Stage η) :
    ∃ b : Stage η, a < b := by
  have hlim := isSuccLimit_ord (hη.trans (Order.le_succ η))
  have hsucc := hlim.succ_lt a.ord_lt_succ
  refine ⟨⟨Ordinal.ToType.mk ⟨Order.succ a.ord, hsucc⟩⟩, ?_⟩
  change a.ord < Stage.ord _
  simp [Stage.ord, Ordinal.ToType.toOrd, Ordinal.ToType.mk, Order.lt_succ a.ord]

theorem Stage.nonempty (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) : Nonempty (Stage η) := by
  refine (Ordinal.nonempty_toType_iff.2 ?_).map Stage.mk
  intro heq
  apply (aleph0_pos.trans_le (hη.trans (Order.le_succ η))).ne'
  simpa [Ordinal.card_zero, card_ord] using congrArg Ordinal.card heq

theorem Stage.exists_bound (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) {ι : Type u}
    (f : ι → Stage η) (hι : #ι ≤ η) :
    ∃ α : Stage η, ∀ i, f i ≤ α := by
  have ha : #ι < Ordinal.cof (Order.succ η).ord := by
    rw [(isRegular_succ hη).cof_ord]
    exact hι.trans_lt (Order.lt_succ η)
  have hsup := Ordinal.iSup_lt_of_lt_cof ha fun i => (f i).ord_lt_succ
  exact ⟨⟨Ordinal.ToType.mk ⟨⨆ i, (f i).ord, hsup⟩⟩, fun i => by
    change (f i).ord ≤ _
    simp [Stage.ord, Ordinal.ToType.toOrd, Ordinal.ToType.mk]
    exact Ordinal.le_iSup (fun i => (f i).ord) i⟩

theorem Stage.mk_eq (η : Cardinal.{u}) : #(Stage η) = Order.succ η := by
  have e : Stage η ≃ (Order.succ η).ord.ToType :=
    ⟨fun a => a.val, fun v => ⟨v⟩, fun _ => rfl, fun _ => rfl⟩
  simpa using (mk_congr e).trans (mk_ord_toType _)

theorem Stage.mk_Iio_le (η : Cardinal.{u}) (β : Stage η) : #(Set.Iio β) ≤ η := by
  let g : Set.Iio β → β.ord.ToType := fun i =>
    Ordinal.ToType.mk ⟨Stage.ord i.1, i.2⟩
  have ginJ : Function.Injective g := fun a b h => by
    have := congrArg (fun t => (Ordinal.ToType.toOrd t).1) h
    simp only [g, Ordinal.ToType.toOrd, Ordinal.ToType.mk, OrderIso.symm_apply_apply] at this
    exact Subtype.ext (Stage.ord_injective η this)
  have hle : #(Set.Iio β) ≤ Ordinal.card β.ord :=
    (mk_le_of_injective ginJ).trans (by rw [mk_toType])
  have hcard : Ordinal.card β.ord ≤ η := by
    have : Ordinal.card β.ord < Order.succ η := by
      have h1 : (Ordinal.card β.ord).ord ≤ β.ord := ord_card_le _
      exact lt_of_not_ge fun hc => β.ord_lt_succ.not_ge ((ord_mono hc).trans h1)
    exact Order.lt_succ_iff.mp this
  exact hle.trans hcard

theorem Stage.mk_Iic_le (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (β : Stage η) :
    #(Set.Iic β) ≤ η := by
  have : Set.Iic β = Set.Iio β ∪ {β} := by
    ext x; simp [le_iff_lt_or_eq, or_comm]
  rw [this]
  refine (mk_union_le _ _).trans ?_
  simpa [mk_singleton] using
    add_le_of_le hη (Stage.mk_Iio_le η β) (one_lt_aleph0.le.trans hη)

/-! ## Signs -/

abbrev Sign : Type := Fin 3
def sNeg : Sign := ⟨0, by decide⟩
def sZero : Sign := ⟨1, by decide⟩
def sPos : Sign := ⟨2, by decide⟩

/-! ## Carrier -/

def Pt (η : Cardinal.{u}) : Type u :=
  { f : Stage η → Sign // ∃ β : Stage η, ∀ i ≥ β, f i = sZero }

instance (η : Cardinal.{u}) : LinearOrder (Pt η) :=
  LinearOrder.lift' (fun f : Pt η => toLex f.1)
    (fun _ _ h => Subtype.ext <| funext fun i => by
      simpa using congrArg (fun x : Lex (Stage η → Sign) => ofLex x i) h)

theorem Pt.lt_iff {η : Cardinal.{u}} {f g : Pt η} :
    f < g ↔ ∃ i, (∀ j < i, f.1 j = g.1 j) ∧ f.1 i < g.1 i := Iff.rfl

theorem exists_support (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (S : Set (Pt η)) (hS : #S ≤ η) :
    ∃ α : Stage η, ∀ f ∈ S, ∀ i ≥ α, f.1 i = sZero := by
  rcases isEmpty_or_nonempty S with hempty | _
  · exact ⟨Classical.choice (Stage.nonempty η hη), fun f hf => (hempty.false ⟨f, hf⟩).elim⟩
  · let b : S → Stage η := fun f => Classical.choose f.1.property
    obtain ⟨α, hα⟩ := Stage.exists_bound η hη b hS
    exact ⟨α, fun f hf i hi => Classical.choose_spec f.property i (hα ⟨f, hf⟩ |>.trans hi)⟩

def ptZero (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) : Pt η :=
  ⟨fun _ => sZero, ⟨Classical.choice (Stage.nonempty η hη), fun _ _ => rfl⟩⟩

theorem exists_below (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (R : Set (Pt η))
    (hR : #R ≤ η) (_hRne : R.Nonempty) :
    ∃ x : Pt η, ∀ f ∈ R, x < f := by
  obtain ⟨α, hα⟩ := exists_support η hη R hR
  have hαne : ∀ f : R, ({ξ | f.1.1 ξ ≠ sNeg} : Set (Stage η)).Nonempty := by
    intro f; refine ⟨α, ?_⟩
    have h := hα f.1 f.2 α le_rfl
    intro hh; exact absurd (h.symm.trans hh) (by decide : ¬sZero = sNeg)
  let νf : R → Stage η := fun f => WellFoundedLT.min {ξ | f.1.1 ξ ≠ sNeg} (hαne f)
  obtain ⟨ν0, hν0⟩ := Stage.exists_bound η hη νf hR
  obtain ⟨ν, hν⟩ := Stage.exists_gt η hη ν0
  let x : Pt η :=
    ⟨fun β => if β < ν then sNeg else sZero, ⟨ν, fun β hβ => ite_eq_right (not_lt.2 hβ)⟩⟩
  refine ⟨x, fun f hf => ?_⟩
  have hi := lt_of_le_of_lt (hν0 ⟨f, hf⟩) hν
  have hpre : ∀ j < νf ⟨f, hf⟩, f.1 j = sNeg := by
    intro j hj
    have := WellFounded.notMem_of_lt_min (hs := hαne ⟨f, hf⟩) hj
    simpa using this
  refine ⟨νf ⟨f, hf⟩, fun j hj => by simp [x, hj.trans hi, hpre j hj], ?_⟩
  change x.1 (νf ⟨f, hf⟩) < f.1 (νf ⟨f, hf⟩)
  have hx : x.1 (νf ⟨f, hf⟩) = sNeg := by simp [x, hi]
  have hmem : f.1 (νf ⟨f, hf⟩) ≠ (0 : Fin 3) := by
    have := wellFounded_lt.min_mem {ξ | f.1 ξ ≠ sNeg} (hαne ⟨f, hf⟩)
    simpa [sNeg, νf] using this
  rw [hx]; exact Fin.pos_of_ne_zero hmem

/-- Upper bound in a rich padded order; namespaced to avoid clashing with
`Partition.exists_above`. -/
theorem RichPaddedOrder.exists_above (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (L : Set (Pt η))
    (hL : #L ≤ η) (_hLne : L.Nonempty) :
    ∃ x : Pt η, ∀ f ∈ L, f < x := by
  obtain ⟨α, hα⟩ := exists_support η hη L hL
  have hαne : ∀ f : L, ({ξ | f.1.1 ξ ≠ sPos} : Set (Stage η)).Nonempty := by
    intro f; refine ⟨α, ?_⟩
    have h := hα f.1 f.2 α le_rfl
    intro hh; exact absurd (h.symm.trans hh) (by decide : ¬sZero = sPos)
  let νf : L → Stage η := fun f => WellFoundedLT.min {ξ | f.1.1 ξ ≠ sPos} (hαne f)
  obtain ⟨ν0, hν0⟩ := Stage.exists_bound η hη νf hL
  obtain ⟨ν, hν⟩ := Stage.exists_gt η hη ν0
  let x : Pt η :=
    ⟨fun β => if β < ν then sPos else sZero, ⟨ν, fun β hβ => ite_eq_right (not_lt.2 hβ)⟩⟩
  refine ⟨x, fun f hf => ?_⟩
  have hi := lt_of_le_of_lt (hν0 ⟨f, hf⟩) hν
  have hpre : ∀ j < νf ⟨f, hf⟩, f.1 j = sPos := by
    intro j hj
    have := WellFounded.notMem_of_lt_min (hs := hαne ⟨f, hf⟩) hj
    simpa using this
  refine ⟨νf ⟨f, hf⟩, fun j hj => by simp [x, hj.trans hi, hpre j hj], ?_⟩
  change f.1 (νf ⟨f, hf⟩) < x.1 (νf ⟨f, hf⟩)
  have hx : x.1 (νf ⟨f, hf⟩) = sPos := by simp [x, hi]
  have hmem : f.1 (νf ⟨f, hf⟩) ≠ (2 : Fin 3) := by
    have := wellFounded_lt.min_mem {ξ | f.1 ξ ≠ sPos} (hαne ⟨f, hf⟩)
    simpa [sPos, νf] using this
  rw [hx]; exact (Fin.lt_last_iff_ne_last (n := 2)).2 hmem

theorem pt_dense (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) {a b : Pt η} (hab : a < b) :
    ∃ c : Pt η, a < c ∧ c < b := by
  obtain ⟨i, hpre, hi⟩ := Pt.lt_iff.1 hab
  obtain ⟨α, hα⟩ := exists_support η hη ({a, b} : Set _) (by
    have h2 : #({a, b} : Set (Pt η)) ≤ (2 : Cardinal) := by
      calc
        #({a, b} : Set (Pt η)) ≤ #({a} : Set (Pt η)) + #({b} : Set (Pt η)) := mk_union_le _ _
        _ = 1 + 1 := by simp
        _ = 2 := by simp [one_add_one_eq_two]
    exact h2.trans (natCast_le_aleph0.trans hη))
  obtain ⟨ν, hν⟩ := Stage.exists_gt η hη (max i α)
  have hαν : α < ν := (le_max_right i α).trans_lt hν
  have hiν : i < ν := (le_max_left i α).trans_lt hν
  obtain ⟨ν', hν'⟩ := Stage.exists_gt η hη ν
  let c : Pt η :=
    ⟨fun β => if β < ν then a.1 β else if β = ν then sPos else sZero,
      ⟨ν', fun β hβ => by
        have h1 : ¬β < ν := fun h => (h.trans hν').not_ge hβ
        have h2 : β ≠ ν := fun he => by subst he; exact hν'.not_ge hβ
        simp [h1, h2]⟩⟩
  refine ⟨c, ?_, ?_⟩
  · have haν : a.1 ν = sZero := hα a (by simp) ν hαν.le
    refine ⟨ν, fun j hj => by simp [c, hj], ?_⟩
    change c.1 ν > a.1 ν
    simp [c, haν]; decide
  · refine ⟨i, fun j hj => by simp [c, hj.trans hiν, hpre j hj], ?_⟩
    simpa [c, hiν] using hi

/-! ## Two-sided fill via `fillSigns` -/

def activeL (η : Cardinal.{u}) (L : Set (Pt η)) (ξ : Stage η) (f : Stage η → Sign) :
    Set (Pt η) :=
  {a ∈ L | ∀ ζ < ξ, a.1 ζ = f ζ}

def activeR (η : Cardinal.{u}) (R : Set (Pt η)) (ξ : Stage η) (f : Stage η → Sign) :
    Set (Pt η) :=
  {b ∈ R | ∀ ζ < ξ, b.1 ζ = f ζ}

/-- Midpoint sign between nonempty active left/right value sets at a stage. -/
noncomputable def fillBetween (uF vF : Finset Sign) (huF : uF.Nonempty) (hvF : vF.Nonempty) :
    Sign :=
  let u := uF.max' huF
  let v := vF.min' hvF
  if hlt : u < v then
    if hroom : ∃ w : Sign, u < w ∧ w < v then Classical.choose hroom else u
  else u

noncomputable def fillSignAt (η : Cardinal.{u}) (L R : Set (Pt η)) (ξ : Stage η)
    (rec : ∀ ζ : Stage η, ζ < ξ → Sign) : Sign :=
  let f : Stage η → Sign := fun ζ => if h : ζ < ξ then rec ζ h else sZero
  let A := activeL η L ξ f
  let B := activeR η R ξ f
  if hA : A.Nonempty then
    if hB : B.Nonempty then
      fillBetween
        (Finset.univ.filter fun s => ∃ a ∈ A, a.1 ξ = s)
        (Finset.univ.filter fun s => ∃ b ∈ B, b.1 ξ = s)
        (by
          obtain ⟨a, ha⟩ := hA
          exact ⟨a.1 ξ, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨a, ha, rfl⟩⟩⟩)
        (by
          obtain ⟨b, hb⟩ := hB
          exact ⟨b.1 ξ, Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨b, hb, rfl⟩⟩⟩)
    else sPos
  else if B.Nonempty then sNeg
  else sZero

noncomputable def fillSigns (η : Cardinal.{u}) (L R : Set (Pt η)) : Stage η → Sign :=
  WellFoundedLT.fix (fillSignAt η L R)

theorem fillSigns_eq (η : Cardinal.{u}) (L R : Set (Pt η)) (ξ : Stage η) :
    fillSigns η L R ξ = fillSignAt η L R ξ fun ζ _ => fillSigns η L R ζ :=
  WellFoundedLT.fix_eq (fillSignAt η L R) ξ

noncomputable def mkFill (η : Cardinal.{u}) (L R : Set (Pt η)) (ν : Stage η) : Pt η :=
  ⟨fun ξ => if ξ < ν then fillSigns η L R ξ else sZero,
    ⟨ν, fun _ξ hξ => ite_eq_right (not_lt.2 hξ)⟩⟩

private theorem active_eq_rec {η : Cardinal.{u}} {L : Set (Pt η)} {ξ : Stage η}
    (f : Stage η → Sign) :
    activeL η L ξ (fun ζ => if _h : ζ < ξ then f ζ else sZero) = activeL η L ξ f := by
  ext a
  simp only [activeL, mem_setOf]
  constructor
  · exact fun ⟨ha, H⟩ => ⟨ha, fun ζ hζ => by simpa [hζ] using H ζ hζ⟩
  · exact fun ⟨ha, H⟩ => ⟨ha, fun ζ hζ => by simpa [hζ] using H ζ hζ⟩

private theorem activeR_eq_rec {η : Cardinal.{u}} {R : Set (Pt η)} {ξ : Stage η}
    (f : Stage η → Sign) :
    activeR η R ξ (fun ζ => if _h : ζ < ξ then f ζ else sZero) = activeR η R ξ f := by
  ext b
  simp only [activeR, mem_setOf]
  constructor
  · exact fun ⟨hb, H⟩ => ⟨hb, fun ζ hζ => by simpa [hζ] using H ζ hζ⟩
  · exact fun ⟨hb, H⟩ => ⟨hb, fun ζ hζ => by simpa [hζ] using H ζ hζ⟩

private theorem fillBetween_ge_of_mem (uF vF : Finset Sign) (huF : uF.Nonempty)
    (hvF : vF.Nonempty) {s : Sign} (hs : s ∈ uF) :
    s ≤ fillBetween uF vF huF hvF := by
  dsimp [fillBetween]
  split_ifs with hlt hroom
  · exact (Finset.le_max' uF s hs).trans (Classical.choose_spec hroom).1.le
  · exact Finset.le_max' uF s hs
  · exact Finset.le_max' uF s hs

private theorem fillBetween_le_of_mem (uF vF : Finset Sign) (huF : uF.Nonempty)
    (hvF : vF.Nonempty)
    (huv : uF.max' huF ≤ vF.min' hvF) {s : Sign} (hs : s ∈ vF) :
    fillBetween uF vF huF hvF ≤ s := by
  dsimp [fillBetween]
  split_ifs with hlt hroom
  · exact (Classical.choose_spec hroom).2.le.trans (Finset.min'_le vF s hs)
  · exact hlt.le.trans (Finset.min'_le vF s hs)
  · have heq : uF.max' huF = vF.min' hvF := le_antisymm huv (not_lt.mp hlt)
    exact heq.le.trans (Finset.min'_le vF s hs)

private theorem max_u_le_min_v_of_cut (η : Cardinal.{u}) (L R : Set (Pt η))
    (hcut : ∀ a ∈ L, ∀ b ∈ R, a < b) (ξ : Stage η) (f : Stage η → Sign)
    {A B : Set (Pt η)}
    (hAeq : A = activeL η L ξ f) (hBeq : B = activeR η R ξ f)
    (huF : (Finset.univ.filter fun s => ∃ a ∈ A, a.1 ξ = s).Nonempty)
    (hvF : (Finset.univ.filter fun s => ∃ b ∈ B, b.1 ξ = s).Nonempty) :
    (Finset.univ.filter fun s => ∃ a ∈ A, a.1 ξ = s).max' huF ≤
      (Finset.univ.filter fun s => ∃ b ∈ B, b.1 ξ = s).min' hvF := by
  set uF := Finset.univ.filter fun s => ∃ a ∈ A, a.1 ξ = s
  set vF := Finset.univ.filter fun s => ∃ b ∈ B, b.1 ξ = s
  obtain ⟨a, ha, hau⟩ := (Finset.mem_filter.1 (uF.max'_mem huF)).2
  obtain ⟨b', hb', hbv⟩ := (Finset.mem_filter.1 (vF.min'_mem hvF)).2
  have haAct : a ∈ activeL η L ξ f := by simpa [hAeq] using ha
  have hbAct : b' ∈ activeR η R ξ f := by simpa [hBeq] using hb'
  have hpref : ∀ j < ξ, a.1 j = b'.1 j := fun j hj =>
    (haAct.2 j hj).trans (hbAct.2 j hj).symm
  refine le_of_not_gt fun hvu => ?_
  have hsign : b'.1 ξ < a.1 ξ := by rwa [hbv, hau]
  exact lt_asymm (hcut a haAct.1 b' hbAct.1)
    (Pt.lt_iff.2 ⟨ξ, fun j hj => (hpref j hj).symm, hsign⟩)

private theorem fillSignAt_left_only {η : Cardinal.{u}} {L R : Set (Pt η)}
    {ξ : Stage η} {rec : ∀ ζ : Stage η, ζ < ξ → Sign}
    (hA : (activeL η L ξ fun ζ => if h : ζ < ξ then rec ζ h else sZero).Nonempty)
    (hB : ¬(activeR η R ξ fun ζ => if h : ζ < ξ then rec ζ h else sZero).Nonempty) :
    fillSignAt η L R ξ rec = sPos := by
  dsimp [fillSignAt]
  rw [dif_pos hA, dif_neg hB]

private theorem fillSignAt_right_only {η : Cardinal.{u}} {L R : Set (Pt η)}
    {ξ : Stage η} {rec : ∀ ζ : Stage η, ζ < ξ → Sign}
    (hA : ¬(activeL η L ξ fun ζ => if h : ζ < ξ then rec ζ h else sZero).Nonempty)
    (hB : (activeR η R ξ fun ζ => if h : ζ < ξ then rec ζ h else sZero).Nonempty) :
    fillSignAt η L R ξ rec = sNeg := by
  dsimp [fillSignAt]
  rw [dif_neg hA, if_pos hB]

theorem fill_ge_of_active_left (η : Cardinal.{u}) (L R : Set (Pt η)) (ξ : Stage η)
    (a : Pt η) (hA : a ∈ activeL η L ξ (fillSigns η L R)) :
    a.1 ξ ≤ fillSigns η L R ξ := by
  rw [fillSigns_eq]
  set f := fillSigns η L R
  let fRec : Stage η → Sign := fun ζ => if h : ζ < ξ then f ζ else sZero
  let A := activeL η L ξ fRec
  let B := activeR η R ξ fRec
  have hA' : a ∈ A := by simpa [A, fRec, active_eq_rec f] using hA
  dsimp [fillSignAt]
  -- After dsimp, the lets in fillSignAt become the same A/B as above definitionally
  -- via active_eq_rec; discharge by cases on Nonempty.
  -- After dsimp [fillSignAt], A/B match the local lets definitionally.
  -- Work with membership in the unfolded active sets.
  have hArec : a ∈ activeL η L ξ fRec := hA'
  split_ifs with hAne hBne
  · have hmem : a ∈ activeL η L ξ fun ζ => if h : ζ < ξ then
        (fun ζ _ => f ζ) ζ h else sZero := by
      simpa [fRec] using hArec
    refine fillBetween_ge_of_mem _ _ _ _ ?_
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨a, hmem, rfl⟩⟩
  · exact Fin.le_last _
  · exact (hAne ⟨a, by simpa [fRec] using hArec⟩).elim
  · exact (hAne ⟨a, by simpa [fRec] using hArec⟩).elim

theorem fill_gt_of_active_left (η : Cardinal.{u}) (L R : Set (Pt η)) (ξ : Stage η)
    (a : Pt η) (hA : a ∈ activeL η L ξ (fillSigns η L R))
    (hne : a.1 ξ ≠ fillSigns η L R ξ) :
    a.1 ξ < fillSigns η L R ξ :=
  lt_of_le_of_ne (fill_ge_of_active_left η L R ξ a hA) hne

theorem fill_le_of_active_right (η : Cardinal.{u}) (L R : Set (Pt η))
    (hcut : ∀ a ∈ L, ∀ b ∈ R, a < b) (ξ : Stage η) (b : Pt η)
    (hB : b ∈ activeR η R ξ (fillSigns η L R)) :
    fillSigns η L R ξ ≤ b.1 ξ := by
  rw [fillSigns_eq]
  set f := fillSigns η L R
  let fRec : Stage η → Sign := fun ζ => if h : ζ < ξ then f ζ else sZero
  have hBrec : b ∈ activeR η R ξ fRec := by
    simpa [fRec, ← activeR_eq_rec f] using hB
  dsimp [fillSignAt]
  split_ifs with hAne hBne
  · have hmem : b ∈ activeR η R ξ fun ζ => if h : ζ < ξ then
        (fun ζ _ => f ζ) ζ h else sZero := by
      simpa [fRec] using hBrec
    refine fillBetween_le_of_mem _ _ _ _ ?_
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨b, hmem, rfl⟩⟩)
    exact max_u_le_min_v_of_cut η L R hcut ξ
      (fun ζ => if h : ζ < ξ then (fun ζ _ => f ζ) ζ h else sZero)
      rfl rfl _ _
  · exact (hBne ⟨b, by simpa [fRec] using hBrec⟩).elim
  · exact Fin.zero_le _
  · exact ((show ¬(activeR η R ξ fun ζ => if h : ζ < ξ then
        (fun ζ _ => f ζ) ζ h else sZero).Nonempty from by assumption)
      ⟨b, by simpa [fRec] using hBrec⟩).elim

theorem fill_lt_of_active_right (η : Cardinal.{u}) (L R : Set (Pt η))
    (hcut : ∀ a ∈ L, ∀ b ∈ R, a < b) (ξ : Stage η) (b : Pt η)
    (hB : b ∈ activeR η R ξ (fillSigns η L R))
    (hne : fillSigns η L R ξ ≠ b.1 ξ) :
    fillSigns η L R ξ < b.1 ξ :=
  lt_of_le_of_ne (fill_le_of_active_right η L R hcut ξ b hB) hne

theorem pt_fills_cuts (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (L R : Set (Pt η))
    (hL : #L ≤ η) (hR : #R ≤ η) (hcut : ∀ a ∈ L, ∀ b ∈ R, a < b) :
    ∃ x : Pt η, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b) := by
  rcases eq_empty_or_nonempty L with hLe | hLne
  · rcases eq_empty_or_nonempty R with hRe | hRne
    · exact ⟨ptZero η hη, by simp [hLe], by simp [hRe]⟩
    · obtain ⟨x, hx⟩ := exists_below η hη R hR hRne
      exact ⟨x, by simp [hLe], hx⟩
  · rcases eq_empty_or_nonempty R with hRe | hRne
    · obtain ⟨x, hx⟩ := RichPaddedOrder.exists_above η hη L hL hLne
      exact ⟨x, hx, by simp [hRe]⟩
    · obtain ⟨α, hα⟩ := exists_support η hη (L ∪ R)
        ((mk_union_le _ _).trans (add_le_of_le hη hL hR))
      obtain ⟨ν, hν⟩ := Stage.exists_gt η hη α
      set f := fillSigns η L R
      set x := mkFill η L R ν
      refine ⟨x, fun a ha => ?_, fun b hb => ?_⟩
      · let D : Set (Stage η) := {ξ | ξ < ν ∧ a.1 ξ ≠ f ξ}
        have hD : D.Nonempty := by
          by_contra h
          have hempty : ∀ ξ, ¬(ξ < ν ∧ a.1 ξ ≠ f ξ) := fun ξ hξ => h ⟨ξ, hξ⟩
          have hEq : ∀ ξ < ν, a.1 ξ = f ξ := fun ξ hξ =>
            Classical.not_not.1 fun hne => hempty ξ ⟨hξ, hne⟩
          have hAα : a ∈ activeL η L α f :=
            ⟨ha, fun ζ hζ => hEq ζ (hζ.trans hν)⟩
          have hBempty : ∀ b ∈ R, b ∉ activeR η R α f := by
            intro b hb hbA
            obtain ⟨ξ, hpre, hlt⟩ := Pt.lt_iff.1 (hcut a ha b hb)
            have hξα : ξ ≤ α := le_of_not_gt fun hgt => by
              simp [hα a (Or.inl ha) ξ hgt.le, hα b (Or.inr hb) ξ hgt.le] at hlt
            rcases eq_or_lt_of_le hξα with he | hlt'
            · have ha0 : a.1 ξ = sZero := by
                rw [he]; exact hα a (Or.inl ha) α le_rfl
              have hb0 : b.1 ξ = sZero := by
                rw [he]; exact hα b (Or.inr hb) α le_rfl
              simp [ha0, hb0] at hlt
            · have haξ : a.1 ξ = f ξ := hEq ξ (hlt'.trans hν)
              have hbξ : b.1 ξ = f ξ := hbA.2 ξ hlt'
              exact hlt.ne (haξ.trans hbξ.symm)
          have hfα : f α = sPos := by
            change fillSigns η L R α = sPos
            rw [fillSigns_eq]
            refine fillSignAt_left_only
              ⟨a, (active_eq_rec f).symm ▸ hAα⟩
              (fun ⟨b', hb'⟩ =>
                hBempty b' ((activeR_eq_rec f ▸ hb').1) (activeR_eq_rec f ▸ hb'))
          have haα : a.1 α = sZero := hα a (Or.inl ha) α le_rfl
          have : a.1 α = f α := hEq α hν
          rw [haα, hfα] at this
          exact absurd this (by decide : ¬sZero = sPos)
        let ξ0 := WellFoundedLT.min D hD
        have m := wellFounded_lt.min_mem D hD
        have hAct : a ∈ activeL η L ξ0 f := by
          refine ⟨ha, fun ζ hζ => ?_⟩
          have : ¬(ζ < ν ∧ a.1 ζ ≠ f ζ) :=
            WellFounded.notMem_of_lt_min (hs := hD) hζ
          have hζν : ζ < ν := hζ.trans m.1
          exact Classical.not_not.1 fun hne => this ⟨hζν, hne⟩
        refine ⟨ξ0, fun j hj => ?_, ?_⟩
        · have hjν : j < ν := hj.trans m.1
          have : ¬(j < ν ∧ a.1 j ≠ f j) :=
            WellFounded.notMem_of_lt_min (hs := hD) hj
          have heq : a.1 j = f j := Classical.not_not.1 fun hne => this ⟨hjν, hne⟩
          change a.1 j = x.1 j
          have : x.1 j = f j := by
            change (if j < ν then fillSigns η L R j else sZero) = f j
            rw [if_pos hjν, show f = fillSigns η L R from rfl]
          exact heq.trans this.symm
        · have hltSign : a.1 ξ0 < f ξ0 := fill_gt_of_active_left η L R ξ0 a hAct m.2
          change a.1 ξ0 < x.1 ξ0
          have : x.1 ξ0 = f ξ0 := by
            change (if ξ0 < ν then fillSigns η L R ξ0 else sZero) = f ξ0
            rw [if_pos m.1, show f = fillSigns η L R from rfl]
          rwa [this]
      · let D : Set (Stage η) := {ξ | ξ < ν ∧ b.1 ξ ≠ f ξ}
        have hD : D.Nonempty := by
          by_contra h
          have hempty : ∀ ξ, ¬(ξ < ν ∧ b.1 ξ ≠ f ξ) := fun ξ hξ => h ⟨ξ, hξ⟩
          have hEq : ∀ ξ < ν, b.1 ξ = f ξ := fun ξ hξ =>
            Classical.not_not.1 fun hne => hempty ξ ⟨hξ, hne⟩
          have hBα : b ∈ activeR η R α f :=
            ⟨hb, fun ζ hζ => hEq ζ (hζ.trans hν)⟩
          have hAempty : ∀ a ∈ L, a ∉ activeL η L α f := by
            intro a ha haA
            obtain ⟨ξ, hpre, hlt⟩ := Pt.lt_iff.1 (hcut a ha b hb)
            have hξα : ξ ≤ α := le_of_not_gt fun hgt => by
              simp [hα a (Or.inl ha) ξ hgt.le, hα b (Or.inr hb) ξ hgt.le] at hlt
            rcases eq_or_lt_of_le hξα with he | hlt'
            · have ha0 : a.1 ξ = sZero := by
                rw [he]; exact hα a (Or.inl ha) α le_rfl
              have hb0 : b.1 ξ = sZero := by
                rw [he]; exact hα b (Or.inr hb) α le_rfl
              simp [ha0, hb0] at hlt
            · have hbξ : b.1 ξ = f ξ := hEq ξ (hlt'.trans hν)
              have haξ : a.1 ξ = f ξ := haA.2 ξ hlt'
              exact hlt.ne (haξ.trans hbξ.symm)
          have hfα : f α = sNeg := by
            change fillSigns η L R α = sNeg
            rw [fillSigns_eq]
            refine fillSignAt_right_only
              (fun ⟨a', ha'⟩ =>
                hAempty a' ((active_eq_rec f ▸ ha').1) (active_eq_rec f ▸ ha'))
              ⟨b, (activeR_eq_rec f).symm ▸ hBα⟩
          have hbα : b.1 α = sZero := hα b (Or.inr hb) α le_rfl
          have : b.1 α = f α := hEq α hν
          rw [hbα, hfα] at this
          exact absurd this (by decide : ¬sZero = sNeg)
        let ξ0 := WellFoundedLT.min D hD
        have m := wellFounded_lt.min_mem D hD
        have hAct : b ∈ activeR η R ξ0 f := by
          refine ⟨hb, fun ζ hζ => ?_⟩
          have : ¬(ζ < ν ∧ b.1 ζ ≠ f ζ) :=
            WellFounded.notMem_of_lt_min (hs := hD) hζ
          have hζν : ζ < ν := hζ.trans m.1
          exact Classical.not_not.1 fun hne => this ⟨hζν, hne⟩
        refine ⟨ξ0, fun j hj => ?_, ?_⟩
        · have hjν : j < ν := hj.trans m.1
          have : ¬(j < ν ∧ b.1 j ≠ f j) :=
            WellFounded.notMem_of_lt_min (hs := hD) hj
          have heq : b.1 j = f j := Classical.not_not.1 fun hne => this ⟨hjν, hne⟩
          change x.1 j = b.1 j
          have : x.1 j = f j := by
            change (if j < ν then fillSigns η L R j else sZero) = f j
            rw [if_pos hjν, show f = fillSigns η L R from rfl]
          exact this.trans heq.symm
        · have hltSign : f ξ0 < b.1 ξ0 :=
            fill_lt_of_active_right η L R hcut ξ0 b hAct m.2.symm
          change x.1 ξ0 < b.1 ξ0
          have : x.1 ξ0 = f ξ0 := by
            change (if ξ0 < ν then fillSigns η L R ξ0 else sZero) = f ξ0
            rw [if_pos m.1, show f = fillSigns η L R from rfl]
          rwa [this]

theorem one_le_of_aleph0 {κ : Cardinal.{u}} (h : ℵ₀ ≤ κ) : 1 ≤ κ :=
  one_lt_aleph0.le.trans h

theorem pt_noBot (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (a : Pt η) : ∃ b : Pt η, b < a := by
  obtain ⟨x, hx⟩ := pt_fills_cuts η hη ∅ {a} (by simp)
    (by simpa [mk_singleton] using one_le_of_aleph0 hη) (by simp)
  exact ⟨x, hx.2 a rfl⟩

theorem pt_noTop (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (a : Pt η) : ∃ c : Pt η, a < c := by
  obtain ⟨x, hx⟩ := pt_fills_cuts η hη {a} ∅
    (by simpa [mk_singleton] using one_le_of_aleph0 hη) (by simp) (by simp)
  exact ⟨x, hx.1 a rfl⟩

/-! ## Cardinality -/

theorem mk_pt_le (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) : #(Pt η) ≤ (2 : Cardinal.{u}) ^ η := by
  let S := Σ β : Stage η, Set.Iic β → Sign
  -- Evaluate a truncated function at a stage, returning `sZero` past the bound.
  let eval : S → Stage η → Sign := fun p x =>
    if hx : x ≤ p.1 then p.2 ⟨x, hx⟩ else sZero
  have inj : Function.Injective fun f : Pt η =>
      (⟨Classical.choose f.property, fun i => f.1 i.1⟩ : S) := by
    intro f g h
    have heval : eval ⟨Classical.choose f.property, fun i => f.1 i.1⟩ =
        eval ⟨Classical.choose g.property, fun i => g.1 i.1⟩ := congrArg eval h
    have hβ : Classical.choose f.property = Classical.choose g.property :=
      congrArg Sigma.fst h
    refine Subtype.ext (funext fun x => ?_)
    by_cases hx : x ≤ Classical.choose f.property
    · have hxg : x ≤ Classical.choose g.property := by rwa [← hβ]
      have hf : eval ⟨Classical.choose f.property, fun i => f.1 i.1⟩ x = f.1 x := by
        simp [eval, hx]
      have hg : eval ⟨Classical.choose g.property, fun i => g.1 i.1⟩ x = g.1 x := by
        simp [eval, hxg]
      exact hf.symm.trans (congrFun heval x |>.trans hg)
    · have hf := Classical.choose_spec f.property x (le_of_not_ge hx)
      have hg := Classical.choose_spec g.property x (le_of_not_ge (by simpa [hβ] using hx))
      rw [hf, hg]
  refine (mk_le_of_injective inj).trans ?_
  have h3ne : (3 : Cardinal) ≠ 0 := Nat.cast_ne_zero.2 (by decide : (3 : ℕ) ≠ 0)
  have hsum : #S = Cardinal.sum fun β : Stage η => (3 : Cardinal) ^ #(Set.Iic β) := by
    simp [S, mk_sigma, Fintype.card_fin]
  rw [hsum]
  refine (sum_le_sum _ _ fun β =>
    power_le_power_left h3ne (Stage.mk_Iic_le η hη β)).trans ?_
  rw [sum_const', Stage.mk_eq]
  have h3eq : (3 : Cardinal) ^ η = (2 : Cardinal) ^ η :=
    nat_power_eq hη (by decide : 2 ≤ (3 : ℕ))
  rw [h3eq]
  have h1 : Order.succ η ≤ (2 : Cardinal) ^ η := Order.succ_le_of_lt (cantor η)
  have hinf : ℵ₀ ≤ (2 : Cardinal) ^ η := hη.trans (cantor η).le
  exact (mul_le_mul' h1 le_rfl).trans (mul_eq_self hinf).le

theorem mk_pt_ge (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) : (2 : Cardinal.{u}) ^ η ≤ #(Pt η) := by
  have hle : #η.out ≤ #(Stage η) := by simpa [mk_out, Stage.mk_eq] using Order.le_succ η
  obtain ⟨e : η.out ↪ Stage η⟩ := (Cardinal.le_def _ _).1 hle
  obtain ⟨β, hβ⟩ := Stage.exists_bound η hη (fun x : η.out => e x) (by simpa [mk_out])
  obtain ⟨γ, hγ⟩ := Stage.exists_gt η hη β
  let enc : (η.out → Bool) → Pt η := fun f =>
    ⟨fun s => if hs : s ∈ Set.range e then (if f (Classical.choose hs) then sPos else sNeg)
      else sZero,
      ⟨γ, fun i hi => dif_neg fun ⟨x, hx⟩ =>
        ((hx.symm ▸ hβ x).trans_lt hγ).not_ge hi⟩⟩
  have hinj : Function.Injective enc := by
    intro f g h
    funext x
    have := congrFun (Subtype.ext_iff.1 h) (e x)
    have hr : e x ∈ Set.range e := ⟨x, rfl⟩
    simp only [enc, dif_pos hr] at this
    have hx : Classical.choose hr = x := e.injective (Classical.choose_spec hr)
    cases hf : f x <;> cases hg : g x <;> simp_all [sPos, sNeg, hx]
  have := mk_le_of_injective hinj
  simpa [mk_arrow, mk_out, Fintype.card_bool] using this

theorem mk_pt (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) : #(Pt η) = (2 : Cardinal.{u}) ^ η :=
  le_antisymm (mk_pt_le η hη) (mk_pt_ge η hη)

/-! ## Strong-limit padded lex sum -/

structure PadIndex (μ η : Cardinal.{u}) where
  val : (μ.ord * (Order.succ η).ord).ToType

def PadIndex.ord {μ η : Cardinal.{u}} (a : PadIndex μ η) : Ordinal.{u} :=
  (Ordinal.ToType.toOrd a.val).1

theorem PadIndex.ord_injective (μ η : Cardinal.{u}) :
    Function.Injective (PadIndex.ord (μ := μ) (η := η)) := by
  intro a b h
  have := Ordinal.ToType.mk.symm.injective (Subtype.ext h)
  cases a; cases b; simp_all

instance (μ η : Cardinal.{u}) : LinearOrder (PadIndex μ η) :=
  LinearOrder.lift' PadIndex.ord (PadIndex.ord_injective μ η)

instance (μ η : Cardinal.{u}) : WellFoundedLT (PadIndex μ η) :=
  show WellFounded _ from
    WellFounded.onFun (f := PadIndex.ord (μ := μ) (η := η)) Ordinal.lt_wf

theorem PadIndex.ord_lt_mul {μ η : Cardinal.{u}} (a : PadIndex μ η) :
    a.ord < μ.ord * (Order.succ η).ord :=
  (Ordinal.ToType.toOrd a.val).2

theorem PadIndex.exists_gt (μ η : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (hη : ℵ₀ ≤ η)
    (a : PadIndex μ η) : ∃ b : PadIndex μ η, a < b := by
  have h0 : 0 < μ.ord := ord_pos.2 (aleph0_pos.trans_le hμ)
  have hlim := Ordinal.isSuccLimit_mul_right h0
    (isSuccLimit_ord (hη.trans (Order.le_succ η)))
  have hsucc := hlim.succ_lt a.ord_lt_mul
  refine ⟨⟨Ordinal.ToType.mk ⟨Order.succ a.ord, hsucc⟩⟩, ?_⟩
  change a.ord < PadIndex.ord _
  simp [PadIndex.ord, Ordinal.ToType.toOrd, Ordinal.ToType.mk, Order.lt_succ a.ord]

theorem PadIndex.nonempty (μ η : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (hη : ℵ₀ ≤ η) :
    Nonempty (PadIndex μ η) := by
  refine (Ordinal.nonempty_toType_iff.2 ?_).map PadIndex.mk
  exact (mul_pos (ord_pos.2 (aleph0_pos.trans_le hμ))
    (ord_pos.2 (aleph0_pos.trans_le (hη.trans (Order.le_succ η))))).ne'

theorem PadIndex.exists_bound (μ η : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (hη : ℵ₀ ≤ η)
    {ι : Type u} (f : ι → PadIndex μ η) (hι : #ι ≤ η) :
    ∃ α : PadIndex μ η, ∀ i, f i ≤ α := by
  have ha : #ι < Ordinal.cof (μ.ord * (Order.succ η).ord) := by
    have h0 : μ.ord ≠ 0 := fun h => (aleph0_pos.trans_le hμ).ne' (ord_eq_zero.1 h)
    rw [Ordinal.cof_mul h0 (isSuccLimit_ord (hη.trans (Order.le_succ η))).isSuccPrelimit,
      (isRegular_succ hη).cof_ord]
    exact hι.trans_lt (Order.lt_succ η)
  have hsup := Ordinal.iSup_lt_of_lt_cof ha fun i => (f i).ord_lt_mul
  exact ⟨⟨Ordinal.ToType.mk ⟨⨆ i, (f i).ord, hsup⟩⟩, fun i => by
    change (f i).ord ≤ _
    simp [PadIndex.ord, Ordinal.ToType.toOrd, Ordinal.ToType.mk]
    exact Ordinal.le_iSup (fun i => (f i).ord) i⟩

theorem PadIndex.mk_eq (μ η : Cardinal.{u}) (hμ : ℵ₀ ≤ μ) (hημ : Order.succ η ≤ μ) :
    #(PadIndex μ η) = μ := by
  have e : PadIndex μ η ≃ (μ.ord * (Order.succ η).ord).ToType :=
    ⟨fun a => a.val, fun v => ⟨v⟩, fun _ => rfl, fun _ => rfl⟩
  have hmk := (mk_congr e).trans (mk_toType _)
  have hcard : (μ.ord * (Order.succ η).ord).card = μ * Order.succ η := by
    simp [Ordinal.card_mul, card_ord]
  rw [hmk, hcard, mul_eq_left hμ hημ (Cardinal.succ_ne_zero η)]

abbrev PadSum (μ η : Cardinal.{u}) : Type u := PadIndex μ η ×ₗ Pt η

theorem padSum_dense (μ η : Cardinal.{u}) (hη : ℵ₀ ≤ η) :
    ∀ a b : PadSum μ η, a < b → ∃ c, a < c ∧ c < b := by
  intro a b hab
  rw [Prod.Lex.lt_iff] at hab
  rcases hab with hα | ⟨hα, hfib⟩
  · obtain ⟨x, hx⟩ := pt_noTop η hη (ofLex a).2
    refine ⟨toLex ((ofLex a).1, x), ?_, ?_⟩
    · rw [Prod.Lex.lt_iff]; exact Or.inr ⟨rfl, hx⟩
    · rw [Prod.Lex.lt_iff]; exact Or.inl hα
  · obtain ⟨x, hx1, hx2⟩ := pt_dense η hη hfib
    refine ⟨toLex ((ofLex a).1, x), ?_, ?_⟩
    · rw [Prod.Lex.lt_iff]; exact Or.inr ⟨hα ▸ rfl, hx1⟩
    · rw [Prod.Lex.lt_iff]; exact Or.inr ⟨hα, hx2⟩

theorem padSum_fills (μ η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (hμ : ℵ₀ ≤ μ)
    (L R : Set (PadSum μ η)) (hL : #L ≤ η) (hR : #R ≤ η)
    (hcut : ∀ a ∈ L, ∀ b ∈ R, a < b) :
    ∃ x : PadSum μ η, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b) := by
  let idx : PadSum μ η → PadIndex μ η := fun p => (ofLex p).1
  rcases eq_empty_or_nonempty R with hRe | hRne
  · rcases eq_empty_or_nonempty L with hLe | hLne
    · exact ⟨toLex (Classical.choice (PadIndex.nonempty μ η hμ hη), ptZero η hη),
        by simp [hLe], by simp [hRe]⟩
    · obtain ⟨α, hα⟩ := PadIndex.exists_bound μ η hμ hη (fun a : L => idx a) hL
      obtain ⟨β, hβ⟩ := PadIndex.exists_gt μ η hμ hη α
      refine ⟨toLex (β, ptZero η hη), fun a ha => ?_, by simp [hRe]⟩
      rw [Prod.Lex.lt_iff]; exact Or.inl (lt_of_le_of_lt (hα ⟨a, ha⟩) hβ)
  · let βs : R → PadIndex μ η := fun b => idx b
    have hβne : (Set.range βs).Nonempty :=
      match hRne with | ⟨b, hb⟩ => ⟨βs ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩
    let β := WellFoundedLT.min (Set.range βs) hβne
    have hβmem := wellFounded_lt.min_mem (Set.range βs) hβne
    obtain ⟨⟨b0, hb0⟩, hb0eq⟩ := hβmem
    have hRβ : ∀ b ∈ R, β ≤ idx b := fun b hb =>
      not_lt.mp (wellFounded_lt.not_lt_min (Set.range βs) ⟨⟨b, hb⟩, rfl⟩)
    have hLβ : ∀ a ∈ L, idx a ≤ β := by
      intro a ha
      refine le_of_not_gt fun hlt => ?_
      have hidx : idx b0 < idx a := by
        simpa [βs, idx, hb0eq] using hlt
      have : b0 < a := Prod.Lex.lt_iff.2 (Or.inl hidx)
      exact lt_asymm (hcut a ha b0 hb0) this
    let Lf : Set (Pt η) := {x | ∃ a ∈ L, idx a = β ∧ (ofLex a).2 = x}
    let Rf : Set (Pt η) := {x | ∃ b ∈ R, idx b = β ∧ (ofLex b).2 = x}
    have hLf : #Lf ≤ η := by
      let φ : Lf → L := fun x => ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
      have : Function.Injective φ := by
        intro x y h
        have hx := Classical.choose_spec x.2
        have hy := Classical.choose_spec y.2
        have heq : Classical.choose x.2 = Classical.choose y.2 :=
          Subtype.ext_iff.mp h
        exact Subtype.ext (hx.2.2.symm.trans ((congrArg (fun p => (ofLex p).2) heq).trans hy.2.2))
      exact (mk_le_of_injective this).trans (by simpa using hL)
    have hRf : #Rf ≤ η := by
      let φ : Rf → R := fun x => ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
      have : Function.Injective φ := by
        intro x y h
        have hx := Classical.choose_spec x.2
        have hy := Classical.choose_spec y.2
        have heq : Classical.choose x.2 = Classical.choose y.2 :=
          Subtype.ext_iff.mp h
        exact Subtype.ext (hx.2.2.symm.trans ((congrArg (fun p => (ofLex p).2) heq).trans hy.2.2))
      exact (mk_le_of_injective this).trans (by simpa using hR)
    have hcutF : ∀ x ∈ Lf, ∀ y ∈ Rf, x < y := by
      intro x hx y hy
      obtain ⟨a, ha, haβ, rfl⟩ := hx
      obtain ⟨b, hb, hbβ, rfl⟩ := hy
      have hab := Prod.Lex.lt_iff.1 (hcut a ha b hb)
      rcases hab with hlt | ⟨_, hfib⟩
      · exact (hlt.ne (haβ.trans hbβ.symm)).elim
      · exact hfib
    obtain ⟨x, hxL, hxR⟩ := pt_fills_cuts η hη Lf Rf hLf hRf hcutF
    refine ⟨toLex (β, x), fun a ha => ?_, fun b hb => ?_⟩
    · rw [Prod.Lex.lt_iff]
      rcases lt_trichotomy (idx a) β with hlt | heq | hgt
      · exact Or.inl hlt
      · exact Or.inr ⟨by simpa [idx] using heq, hxL _ ⟨a, ha, heq, rfl⟩⟩
      · exact (hgt.not_ge (hLβ a ha)).elim
    · rw [Prod.Lex.lt_iff]
      rcases lt_trichotomy β (idx b) with hlt | heq | hgt
      · exact Or.inl hlt
      · exact Or.inr ⟨by simpa [idx] using heq,
          hxR _ ⟨b, hb, heq.symm, rfl⟩⟩
      · exact (hgt.not_ge (hRβ b hb)).elim

theorem mk_padSum (μ η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (hμ0 : ℵ₀ ≤ μ)
    (hημ : Order.succ η ≤ μ) (h2 : (2 : Cardinal) ^ η ≤ μ) :
    #(PadSum μ η) = μ := by
  have hmk : #(PadSum μ η) = #(PadIndex μ η × Pt η) :=
    mk_congr ⟨ofLex, toLex, ofLex_toLex, toLex_ofLex⟩
  rw [hmk, mk_prod, lift_id, lift_id, PadIndex.mk_eq μ η hμ0 hημ, mk_pt η hη]
  exact mul_eq_left hμ0 h2 (power_ne_zero η (Nat.cast_ne_zero.2 (by decide : (2 : ℕ) ≠ 0)))

theorem padSum_padded (μ η : Cardinal.{u}) (hη : ℵ₀ ≤ η) (hμ0 : ℵ₀ ≤ μ)
    (hημ : Order.succ η ≤ μ) (h2 : (2 : Cardinal) ^ η ≤ μ) :
    IsPadded (PadSum μ η) := by
  let q0 := ptZero η hη
  let s : Set (PadSum μ η) := Set.range fun α : PadIndex μ η => toLex (α, q0)
  refine ⟨s, ?_, ?_⟩
  · have e : PadIndex μ η ≃ s :=
      ⟨fun α => ⟨toLex (α, q0), α, rfl⟩, fun p => (ofLex p.1).1, fun _ => rfl,
        fun p => by obtain ⟨α, hα⟩ := p.2; exact Subtype.ext (by simp [← hα])⟩
    calc
      #s = #(PadIndex μ η) := (mk_congr e).symm
      _ = μ := PadIndex.mk_eq μ η hμ0 hημ
      _ = #(PadSum μ η) := (mk_padSum μ η hη hμ0 hημ h2).symm
  · let φ : s → PadIndex μ η := fun p => (ofLex p.1).1
    refine (InvImage.wf φ (wellFounded_lt (α := PadIndex μ η))).mono fun p q hpq => ?_
    obtain ⟨α, hα⟩ := p.2
    obtain ⟨β, hβ⟩ := q.2
    have hpq' : toLex (α, q0) < toLex (β, q0) := by
      change (p : PadSum μ η) < q at hpq
      rwa [← hα, ← hβ] at hpq
    rw [Prod.Lex.toLex_lt_toLex] at hpq'
    rcases hpq' with hlt | ⟨_, hf⟩
    · change φ p < φ q
      have hp : φ p = α := by simp [φ, ← hα]
      have hq : φ q = β := by simp [φ, ← hβ]
      rwa [hp, hq]
    · exact (lt_irrefl q0 hf).elim

theorem lemma_5_5_proof (η : Cardinal.{u}) (hη : ℵ₀ ≤ η) :
    (∃ (Q : Type u) (_ : LinearOrder Q),
      #Q = (2 : Cardinal.{u}) ^ η ∧
      (∀ a b : Q, a < b → ∃ c, a < c ∧ c < b) ∧
      (∀ a : Q, ∃ b, b < a) ∧ (∀ a : Q, ∃ c, a < c) ∧
      ∀ (L R : Set Q), #L ≤ η → #R ≤ η → (∀ a ∈ L, ∀ b ∈ R, a < b) →
        ∃ x : Q, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b)) ∧
    ∀ μ : Cardinal.{u}, μ.IsStrongLimit → η < μ →
      ∃ (I : Type u) (_ : LinearOrder I) (_ : IsPadded I),
        #I = μ ∧
        (∀ a b : I, a < b → ∃ c, a < c ∧ c < b) ∧
        ∀ (L R : Set I), #L ≤ η → #R ≤ η → (∀ a ∈ L, ∀ b ∈ R, a < b) →
          ∃ x : I, (∀ a ∈ L, a < x) ∧ (∀ b ∈ R, x < b) := by
  refine ⟨?_, ?_⟩
  · exact ⟨Pt η, inferInstance, mk_pt η hη, fun a b => pt_dense η hη,
      pt_noBot η hη, pt_noTop η hη, pt_fills_cuts η hη⟩
  · intro μ hμ hημ
    have hμ0 : ℵ₀ ≤ μ := hμ.aleph0_le
    have hsucc : Order.succ η ≤ μ := Order.succ_le_of_lt hημ
    have h2 : (2 : Cardinal) ^ η < μ := hμ.isStrongPrelimit hημ
    exact ⟨PadSum μ η, inferInstance, padSum_padded μ η hη hμ0 hsucc h2.le,
      mk_padSum μ η hη hμ0 hsucc h2.le, padSum_dense μ η hη, padSum_fills μ η hη hμ0⟩

end
end
end AEC
