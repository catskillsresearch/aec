module

public import AEC.Section3.Elimination
public import AEC.Section3.Lemma310
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Pigeonhole
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

/-!
# Common profiles for the elimination argument (text.md §3.5, lines 184–188)

This file produces the `CommonProfileSetup` consumed by Proposition 3.9 from unboundedly many
failing categoricity cardinals.

* `OrbitNaming.normalize` reindexes every tuple along the fixed `embedBelow` before naming it.
  A record-to-name function `CanonicalRecord → Option OrbitName` only sees the index set
  `range (embedBelow hι) ⊆ θ`, so it can compute the names of `ι`-tuples only for a naming
  that factors through this reindexing. (The paper indexes all tuples by `θ` itself.)
* `recordAssign` is the function `F_{κ,δ}` of the paper for a presentation `E(I)`,
  `I ≃o H(δ)`; `deltaAssign` is its value on a fixed soft copy of `H(δ)`.
* `exists_recurring_assign`: at each size one `F` recurs cofinally in `κ⁺` among the
  indecomposable ordinals of Lemma 3.10 with a prescribed regular cofinality `τ`.
* `exists_common_profile_setup`: two sizes `a < μ` sharing a cofinally recurring `F`, with
  `θ < τ_a` and `a < τ_μ`, give a `CommonProfileSetup`.
* `exists_asymmetric_common_setup`: the `P⁺`-sequence pigeonhole, delivering the setup together
  with the common named arrow relation and an asymmetric arrow in it.

The profile at the single ordinal `κ + θ⁺` (`failProfileAt` in `Elimination.lean`) is not enough
here: Proposition 3.9 needs an indecomposable `β` with `cf(β) > a` and a cofinal family of `δ`.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal Set

set_option linter.unusedVariables false

/-! ### Index-normalized orbit namings -/

theorem mk_subBelow_le {θ : Cardinal.{u}} (S : Set (Below θ)) : #(↥S) ≤ θ := by
  have h := Cardinal.mk_subtype_le S
  rw [mk_ord_toType] at h
  exact h

/-- The fixed bijection of an index type of size `≤ θ` with a subset of `θ`. This is the
index equivalence of `canonicalOfTuple`. -/
noncomputable def normIndexEquiv {ι : Type u} {θ : Cardinal.{u}} (hι : #ι ≤ θ) :
    ι ≃ ↥(Set.range (embedBelow hι)) :=
  Equiv.ofInjective (embedBelow hι).1 (embedBelow hι).2

/-- A tuple reindexed by the subset `range (embedBelow hι)` of `θ`. -/
noncomputable def normTuple {α ι : Type u} {θ : Cardinal.{u}} (hι : #ι ≤ θ) (xs : ι → α) :
    ↥(Set.range (embedBelow hι)) → α :=
  fun j => xs ((normIndexEquiv hι).symm j)

/-- Reindexing both tuples along one bijection does not change orbit equality. -/
theorem sameAutOrbit_reindex (K : AbstractElementaryClass.{u}) {M : Model K.τ}
    {ι ι' : Type u} (e : ι' ≃ ι) (xs ys : ι → M.carrier) :
    SameAutOrbit K M (fun j => xs (e j)) (fun j => ys (e j)) ↔ SameAutOrbit K M xs ys := by
  constructor
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, fun i => ?_⟩
    simpa using h (e.symm i)
  · rintro ⟨g, hg, h⟩
    exact ⟨g, hg, fun j => h (e j)⟩

/-- Name a tuple by the `N₀`-name of its reindexing along `embedBelow`. Tuples of every index
type are thereby named through index sets `S ⊆ θ`, which is what a record-to-name function
on canonical records can see. -/
noncomputable def OrbitNaming.normalize {K : AbstractElementaryClass.{u}} {θ : Cardinal.{u}}
    (N₀ : OrbitNaming K θ) : OrbitNaming K θ where
  name hM xs hι := N₀.name hM (normTuple hι xs) (mk_subBelow_le _)
  name_spec hM xs ys hι hle hcat :=
    (N₀.name_spec hM (normTuple hι xs) (normTuple hι ys) (mk_subBelow_le _) hle hcat).trans
      (sameAutOrbit_reindex K (normIndexEquiv hι).symm xs ys)
  name_iso {M₁ M₂} φ hM₁ hM₂ {ι} xs hι :=
    N₀.name_iso φ hM₁ hM₂ (normTuple hι xs) (mk_subBelow_le _)

/-- In a presentation, the normalized name of `xs` is the base name of the canonically
reindexed tuple `canonicalTupleReindex xs`.

The identity `N.name (canonicalTupleReindex xs) = N.name xs` with one naming `N` on both
sides is not available: the two tuples have different index types, and the axioms of
`OrbitNaming` relate only tuples over one index type. -/
theorem OrbitNaming.normalize_name_eq {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K) {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (N₀ : OrbitNaming K θ)
    {I : Type u} [LinearOrder I] [Nonempty I] {ι : Type u} (hι : #ι ≤ θ)
    (xs : ι → (E.obj I).carrier) :
    N₀.normalize.name (orderPresentation_obj_mem E I) xs hι =
      N₀.name (orderPresentation_obj_mem E I) (canonicalTupleReindex E hθ hι xs)
        (canonical_record_card_index (canonicalOfTuple E hθ hι xs)) :=
  rfl

/-- Names of tuples indexed by equal subsets of `θ` agree when the tuples agree. -/
theorem OrbitNaming.name_congr_set {K : AbstractElementaryClass.{u}} {θ : Cardinal.{u}}
    (N₀ : OrbitNaming K θ) {M : Model K.τ} (hM : K.Mem M) {S T : Set (Below θ)} (h : S = T)
    (zs : ↥S → M.carrier) (ws : ↥T → M.carrier)
    (hzw : ∀ j : ↥S, zs j = ws ⟨j.1, h ▸ j.2⟩) (hS : #(↥S) ≤ θ) (hT : #(↥T) ≤ θ) :
    N₀.name hM zs hS = N₀.name hM ws hT := by
  subst h
  have hfun : zs = ws := funext hzw
  subst hfun
  rfl

/-! ### The record-to-name function of a presentation -/

/-- An order isomorphism of index orders carries realizations to realizations. -/
theorem realizes_orderIso {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J] (ψ : I ≃o J)
    (rec : OrbitRecord E.lab E.arity) (place : rec.slot → I)
    (zs : rec.index → (E.obj I).carrier)
    (h : RealizesOrbitRecord (I := I) E rec place zs) :
    RealizesOrbitRecord (I := J) E rec (fun s => ψ (place s))
      (fun j => E.map ψ.toOrderEmbedding (zs j)) := by
  refine ⟨fun a b hab => h.1 (ψ.injective hab),
    fun a b => (h.2.1 a b).trans ψ.lt_iff_lt.symm, ?_, ?_⟩
  · intro j
    obtain ⟨pos, hinc, hpos, hxs⟩ := h.2.2.1 j
    refine ⟨ψ.toOrderEmbedding ∘ pos, ψ.toOrderEmbedding.strictMono.comp hinc,
      fun a => congrArg ψ (hpos a), ?_⟩
    dsimp only
    rw [hxs]
    exact E.realize_map ψ.toOrderEmbedding ⟨_, pos, hinc⟩
  · intro L U
    rw [h.2.2.2 L U, occupied_orderIso ψ, Set.image_image, Set.image_image]

/-- The partial function `F` of Section 3.3 for the presentation `E(I)`: a canonical record
realized in `E(I)` is sent to the `N₀`-name of a realizing tuple, indexed by the record's own
index set. -/
noncomputable def recordAssign {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {θ : Cardinal.{u}} (N₀ : OrbitNaming K θ) (I : Type u) [LinearOrder I] [Nonempty I]
    (r : CanonicalRecord E.lab E.arity θ) : Option (OrbitName K θ) := by
  classical
  exact
    if h : ∃ (place : (CanonicalRecord.toOrbitRecord r).slot → I)
        (zs : (CanonicalRecord.toOrbitRecord r).index → (E.obj I).carrier),
        RealizesOrbitRecord (I := I) E (CanonicalRecord.toOrbitRecord r) place zs then
      some (N₀.name (orderPresentation_obj_mem E I)
        (Classical.choose (Classical.choose_spec h)) (canonical_record_card_index r))
    else
      none

/-- A soft copy of `H(δ)` has cardinality `|δ|`. -/
theorem mk_of_horderIso {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ)
    {I : Type u} [LinearOrder I] (e : HOrder δ ≃o I) : #I = δ.card := by
  have h1 : #(ULift.{u + 1} I) = #(HOrder δ) :=
    Cardinal.mk_congr (Equiv.ulift.trans e.symm.toEquiv)
  rw [mk_uLift, ← HOrder.card_eq hδ] at h1
  exact Cardinal.lift_injective h1

theorem card_obj_of_horderIso {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {θ κ : Cardinal.{u}} (hle : max (ls K) (Order.succ θ) ≤ κ)
    {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ) (hδcard : δ.card = κ)
    {I : Type u} [LinearOrder I] [Nonempty I] (e : HOrder δ ≃o I) :
    Model.card (E.obj I) = κ := by
  have hls : ls K ≤ κ := (le_max_left _ _).trans hle
  exact orderPresentation_obj_card E ((mk_of_horderIso hδ e).trans hδcard) hls
    ((isLSBound_ls K).1.trans hls)

/-- In a presentation over a copy of `H(δ)` with `cf(δ) > θ` of a large categoricity size,
`recordAssign` returns the name of every realizing tuple (they all lie in one orbit). -/
theorem recordAssign_of_realizes {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (N₀ : OrbitNaming K θ) {κ : Cardinal.{u}}
    (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ) (hcf : θ < Ordinal.cof δ)
    {I : Type u} [LinearOrder I] [Nonempty I] (e : HOrder δ ≃o I)
    (hcard : Model.card (E.obj I) = κ)
    (r : CanonicalRecord E.lab E.arity θ)
    (place : (CanonicalRecord.toOrbitRecord r).slot → I)
    (zs : (CanonicalRecord.toOrbitRecord r).index → (E.obj I).carrier)
    (hreal : RealizesOrbitRecord (I := I) E (CanonicalRecord.toOrbitRecord r) place zs) :
    recordAssign E N₀ I r =
      some (N₀.name (orderPresentation_obj_mem E I) zs (canonical_record_card_index r)) := by
  classical
  unfold recordAssign
  split_ifs with hne
  · have hys := Classical.choose_spec (Classical.choose_spec hne)
    have horb := same_record_sameAutOrbit E δ θ hδ hθ hcf e
      (CanonicalRecord.toOrbitRecord r) (canonical_record_card_slot r)
      (Classical.choose hne) place (Classical.choose (Classical.choose_spec hne)) zs hys hreal
    have hleM : max (ls K) (Order.succ θ) ≤ Model.card (E.obj I) := by rw [hcard]; exact hle
    have hcatM : Categorical K (Model.card (E.obj I)) := by rw [hcard]; exact hcat
    exact congrArg some
      ((N₀.name_spec (orderPresentation_obj_mem E I) _ zs (canonical_record_card_index r)
        hleM hcatM).2 horb)
  · exact (hne ⟨place, zs, hreal⟩).elim

/-- A record with no realization in `E(I)` is outside the domain of `recordAssign`. -/
theorem recordAssign_eq_none {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {θ : Cardinal.{u}} (N₀ : OrbitNaming K θ) {I : Type u} [LinearOrder I] [Nonempty I]
    (r : CanonicalRecord E.lab E.arity θ)
    (h : ¬ ∃ (place : (CanonicalRecord.toOrbitRecord r).slot → I)
      (zs : (CanonicalRecord.toOrbitRecord r).index → (E.obj I).carrier),
      RealizesOrbitRecord (I := I) E (CanonicalRecord.toOrbitRecord r) place zs) :
    recordAssign E N₀ I r = none := by
  classical
  unfold recordAssign
  split_ifs
  rfl

/-- `recordAssign` does not depend on the chosen copy of `H(δ)`. -/
theorem recordAssign_congr_orderIso {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K)
    {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (N₀ : OrbitNaming K θ) {κ : Cardinal.{u}}
    (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ) (hcf : θ < Ordinal.cof δ)
    {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (e : HOrder δ ≃o I) (ψ : I ≃o J)
    (hI : Model.card (E.obj I) = κ) (hJ : Model.card (E.obj J) = κ)
    (r : CanonicalRecord E.lab E.arity θ) :
    recordAssign E N₀ I r = recordAssign E N₀ J r := by
  classical
  by_cases h : ∃ (place : (CanonicalRecord.toOrbitRecord r).slot → I)
      (zs : (CanonicalRecord.toOrbitRecord r).index → (E.obj I).carrier),
      RealizesOrbitRecord (I := I) E (CanonicalRecord.toOrbitRecord r) place zs
  · obtain ⟨place, zs, hreal⟩ := h
    rw [recordAssign_of_realizes E hθ N₀ hle hcat hδ hcf e hI r place zs hreal,
      recordAssign_of_realizes E hθ N₀ hle hcat hδ hcf (e.trans ψ) hJ r _ _
        (realizes_orderIso E ψ _ place zs hreal)]
    exact congrArg some
      (N₀.name_iso (orderPresentationMapEquiv E ψ) (orderPresentation_obj_mem E I)
        (orderPresentation_obj_mem E J) zs (canonical_record_card_index r))
  · have h' : ¬ ∃ (place : (CanonicalRecord.toOrbitRecord r).slot → J)
        (zs : (CanonicalRecord.toOrbitRecord r).index → (E.obj J).carrier),
        RealizesOrbitRecord (I := J) E (CanonicalRecord.toOrbitRecord r) place zs := by
      rintro ⟨place, zs, hreal⟩
      exact h ⟨_, _, realizes_orderIso E ψ.symm _ place zs hreal⟩
    rw [recordAssign_eq_none E N₀ r h, recordAssign_eq_none E N₀ r h']

/-- The canonical record of a tuple is assigned the normalized name of that tuple. -/
theorem recordAssign_canonicalOfTuple {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K)
    {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (N₀ : OrbitNaming K θ) {κ : Cardinal.{u}}
    (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ) (hcf : θ < Ordinal.cof δ)
    {I : Type u} [LinearOrder I] [Nonempty I] (e : HOrder δ ≃o I)
    (hcard : Model.card (E.obj I) = κ)
    {ι : Type u} (hι : #ι ≤ θ) (xs : ι → (E.obj I).carrier) :
    recordAssign E N₀ I (canonicalOfTuple E hθ hι xs) =
      some (N₀.normalize.name (orderPresentation_obj_mem E I) xs hι) :=
  recordAssign_of_realizes E hθ N₀ hle hcat hδ hcf e hcard _ _ _
    (realizes_canonicalOfTuple E hθ hι xs)

/-- A canonical record realized by the canonical reindexing of `xs` is assigned the
normalized name of `xs`. -/
theorem recordAssign_of_realizes_reindex {K : AbstractElementaryClass.{u}}
    (E : OrderPresentation K)
    {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (N₀ : OrbitNaming K θ) {κ : Cardinal.{u}}
    (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ) (hcf : θ < Ordinal.cof δ)
    {I : Type u} [LinearOrder I] [Nonempty I] (e : HOrder δ ≃o I)
    (hcard : Model.card (E.obj I) = κ)
    {ι : Type u} (hι : #ι ≤ θ) (xs : ι → (E.obj I).carrier)
    (r : CanonicalRecord E.lab E.arity θ)
    (place : (CanonicalRecord.toOrbitRecord r).slot → I)
    (reindex : (CanonicalRecord.toOrbitRecord r).index ≃ ι)
    (hre : ∀ j : (CanonicalRecord.toOrbitRecord r).index, embedBelow hι (reindex j) = j.val)
    (hreal : RealizesOrbitRecord (I := I) E (CanonicalRecord.toOrbitRecord r) place
      (fun j => xs (reindex j))) :
    recordAssign E N₀ I r =
      some (N₀.normalize.name (orderPresentation_obj_mem E I) xs hι) := by
  rw [recordAssign_of_realizes E hθ N₀ hle hcat hδ hcf e hcard r place _ hreal]
  have hset : r.idx = Set.range (embedBelow hι) := by
    ext b
    constructor
    · intro hb
      exact ⟨reindex ⟨b, hb⟩, hre ⟨b, hb⟩⟩
    · rintro ⟨i, rfl⟩
      have hi := hre (reindex.symm i)
      rw [Equiv.apply_symm_apply] at hi
      rw [hi]
      exact (reindex.symm i).2
  refine congrArg some
    (N₀.name_congr_set (orderPresentation_obj_mem E I) hset
      (fun j => xs (reindex j)) (normTuple hι xs) (fun j => ?_) _ _)
  change xs (reindex j) = xs ((normIndexEquiv hι).symm ⟨j.1, hset ▸ j.2⟩)
  congr 1
  apply (normIndexEquiv hι).injective
  rw [Equiv.apply_symm_apply]
  exact Subtype.ext (hre j)

/-! ### Profiles indexed by ordinals -/

/-- A linear order in the universe of `δ` isomorphic to `H(δ)`. -/
structure SoftCopy (δ : _root_.Ordinal.{u}) where
  I : Type u
  lin : LinearOrder I
  non : Nonempty I
  e : HOrder δ ≃o I

attribute [instance] SoftCopy.lin SoftCopy.non

/-- The fixed soft copy of `H(δ)` for a limit ordinal `δ`. -/
noncomputable def softCopy {δ : _root_.Ordinal.{u}} (h : Order.IsSuccLimit δ) : SoftCopy δ :=
  ⟨(horderSmallCopy h (rfl : δ.card = δ.card)).1,
    (horderSmallCopy h (rfl : δ.card = δ.card)).2.1,
    (horderSmallCopy h (rfl : δ.card = δ.card)).2.2.1,
    (horderSmallCopy h (rfl : δ.card = δ.card)).2.2.2.1⟩

/-- The record-to-name function `F_{κ,δ}` of the fixed soft copy of `H(δ)`, `κ = |δ|`.
For a non-limit `δ` it is the empty function. -/
noncomputable def deltaAssign {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {θ : Cardinal.{u}} (N₀ : OrbitNaming K θ) (δ : _root_.Ordinal.{u}) :
    CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ) := by
  classical
  exact
    if h : Order.IsSuccLimit δ then recordAssign E N₀ (softCopy h).I else fun _ => none

/-- `deltaAssign` is the record-to-name function of every copy of `H(δ)`. -/
theorem deltaAssign_eq {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {θ : Cardinal.{u}} (hθ : aleph0 ≤ θ) (N₀ : OrbitNaming K θ) {κ : Cardinal.{u}}
    (hle : max (ls K) (Order.succ θ) ≤ κ) (hcat : Categorical K κ)
    {δ : _root_.Ordinal.{u}} (hδ : Order.IsSuccLimit δ) (hcf : θ < Ordinal.cof δ)
    (hδcard : δ.card = κ)
    {I : Type u} [LinearOrder I] [Nonempty I] (e : HOrder δ ≃o I) :
    deltaAssign E N₀ δ = recordAssign E N₀ I := by
  classical
  unfold deltaAssign
  split_ifs
  funext r
  exact recordAssign_congr_orderIso E hθ N₀ hle hcat hδ hcf (softCopy hδ).e
    ((softCopy hδ).e.symm.trans e)
    (card_obj_of_horderIso E hle hδ hδcard (softCopy hδ).e)
    (card_obj_of_horderIso E hle hδ hδcard e) r

/-- `F` is the record-to-name function of cofinally many presentations of the model of size
`κ`, over the indecomposable ordinals of size `κ` and cofinality `τ` from Lemma 3.10. -/
def RecursCofinally {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {θ : Cardinal.{u}} (N₀ : OrbitNaming K θ) (κ τ : Cardinal.{u})
    (F : CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ)) : Prop :=
  ∀ η : _root_.Ordinal.{u}, η < (Order.succ κ).ord →
    ∃ δ : _root_.Ordinal.{u}, η ≤ δ ∧ δ < (Order.succ κ).ord ∧
      AdditivelyIndecomposable δ ∧ δ.card = κ ∧ Ordinal.cof δ = τ ∧
      deltaAssign E N₀ δ = F

/-- There are at most `P = 2^B` record-to-name functions. -/
theorem mk_assign_le (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) :
    #(CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ)) ≤ profilePaletteBound K θ := by
  refine le_trans (mk_le_of_injective
    (f := fun F => (⟨fun _ _ => false, F⟩ : FailProfile K E θ)) ?_)
    (mk_failProfile_le K E θ hθ)
  intro F G h
  exact congrArg FailProfile.assign h

/-- One record-to-name function recurs cofinally in `κ⁺` (text.md 186): otherwise the
supremum of at most `P < κ⁺` bounded fibers would be below the regular cardinal `κ⁺`. -/
theorem exists_recurring_assign (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (N₀ : OrbitNaming K θ) (κ τ : Cardinal.{u})
    (hκ : aleph0 ≤ κ) (hτ : aleph0 ≤ τ) (hreg : Cardinal.IsRegular τ) (hle : τ ≤ κ)
    (hP : profilePaletteBound K θ < κ) :
    ∃ F, RecursCofinally E N₀ κ τ F := by
  classical
  by_contra hno
  have hno' : ∀ F : CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ),
      ∃ η : _root_.Ordinal.{u}, η < (Order.succ κ).ord ∧
        ∀ δ : _root_.Ordinal.{u}, η ≤ δ → δ < (Order.succ κ).ord →
          AdditivelyIndecomposable δ → δ.card = κ → Ordinal.cof δ = τ →
          deltaAssign E N₀ δ ≠ F := by
    intro F
    by_contra hF
    apply hno
    refine ⟨F, fun η hη => ?_⟩
    by_contra hη'
    exact hF ⟨η, hη, fun δ h1 h2 h3 h4 h5 h6 => hη' ⟨δ, h1, h2, h3, h4, h5, h6⟩⟩
  choose η hη hbad using hno'
  have hcof : Ordinal.cof (Order.succ κ).ord = Order.succ κ := (isRegular_succ hκ).cof_ord
  have hsup : (⨆ F, η F) < (Order.succ κ).ord := by
    apply Ordinal.iSup_lt_of_lt_cof _ hη
    rw [hcof]
    exact (mk_assign_le K E θ hθ).trans_lt (hP.trans (Order.lt_succ κ))
  obtain ⟨δ, hδge, hδlt, hind, hcard, hcofδ⟩ :=
    indecomposable_cofinal κ τ hκ hτ hreg hle _ hsup
  exact hbad (deltaAssign E N₀ δ) δ ((Ordinal.le_iSup η _).trans hδge) hδlt hind hcard hcofδ rfl

/-! ### Building the common profile setup (text.md 186–188) -/

/-- Two categoricity sizes `a < μ` sharing one cofinally recurring record-to-name function,
at cofinalities `τ_a > θ` and `τ_μ > a`, carry the common-profile data of Proposition 3.9
for the normalized naming. -/
theorem exists_common_profile_setup (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (N₀ : OrbitNaming K θ) (a μ : Cardinal.{u})
    (hale : max (ls K) (Order.succ θ) ≤ a) (hμle : max (ls K) (Order.succ θ) ≤ μ)
    (hcatA : Categorical K a) (hcatμ : Categorical K μ)
    (τa τμ : Cardinal.{u}) (hθτa : θ < τa) (haτμ : a < τμ)
    (F : CanonicalRecord E.lab E.arity θ → Option (OrbitName K θ))
    (hFa : RecursCofinally E N₀ a τa F) (hFμ : RecursCofinally E N₀ μ τμ F) :
    Nonempty (CommonProfileSetup K E θ a μ N₀.normalize hθ) := by
  classical
  have hθa : θ < a := (Order.lt_succ θ).trans_le ((le_max_right _ _).trans hale)
  have hμinf : aleph0 ≤ μ := (isLSBound_ls K).1.trans ((le_max_left _ _).trans hμle)
  have h0 : (0 : _root_.Ordinal.{u}) < (Order.succ μ).ord :=
    (Cardinal.isSuccLimit_ord (hμinf.trans (Order.le_succ μ))).bot_lt
  obtain ⟨β, -, -, hβind, hβcard, hβcof, hβF⟩ := hFμ 0 h0
  have hβa : a < Ordinal.cof β := by rw [hβcof]; exact haτμ
  have hβθ : θ < Ordinal.cof β := hθa.trans hβa
  have hβlim : Order.IsSuccLimit β :=
    Ordinal.one_lt_cof_iff.1 (lt_of_le_of_lt (one_le_aleph0.trans hθ) hβθ)
  have hlimOf : ∀ δ : _root_.Ordinal.{u}, Ordinal.cof δ = τa → Order.IsSuccLimit δ := by
    intro δ hcof
    refine Ordinal.one_lt_cof_iff.1 (lt_of_le_of_lt (one_le_aleph0.trans hθ) ?_)
    rw [hcof]; exact hθτa
  refine ⟨{
    β := β
    β_indecomposable := hβind
    β_card := hβcard
    β_cof := hβθ
    β_cof_a := hβa
    Deltas := {δ | δ < (Order.succ a).ord ∧ AdditivelyIndecomposable δ ∧ δ.card = a ∧
      Ordinal.cof δ = τa ∧ deltaAssign E N₀ δ = F}
    deltas_spec := ?_
    deltas_cofinal := ?_
    assign := F
    assign_large := ?_
    assign_small := ?_
    assign_realizes_large := ?_ }⟩
  · rintro δ ⟨hlt, hind, hcard, hcof, -⟩
    exact ⟨hind, hcard, by rw [hcof]; exact hθτa, hlt⟩
  · intro η hη
    obtain ⟨δ, hge, hlt, hind, hcard, hcof, hF⟩ := hFa η hη
    exact ⟨δ, ⟨hlt, hind, hcard, hcof, hF⟩, hge⟩
  · intro I _ _ e ι hι xs
    have hF : F = recordAssign E N₀ I :=
      hβF.symm.trans (deltaAssign_eq E hθ N₀ hμle hcatμ hβlim hβθ hβcard e)
    exact (congrFun hF _).trans
      (recordAssign_canonicalOfTuple E hθ N₀ hμle hcatμ hβlim hβθ e
        (card_obj_of_horderIso E hμle hβlim hβcard e) hι xs)
  · rintro δ ⟨hlt, hind, hcard, hcof, hδF⟩ I _ _ e ι hι xs
    have hδθ : θ < Ordinal.cof δ := by rw [hcof]; exact hθτa
    have hδlim := hlimOf δ hcof
    have hF : F = recordAssign E N₀ I :=
      hδF.symm.trans (deltaAssign_eq E hθ N₀ hale hcatA hδlim hδθ hcard e)
    exact (congrFun hF _).trans
      (recordAssign_canonicalOfTuple E hθ N₀ hale hcatA hδlim hδθ e
        (card_obj_of_horderIso E hale hδlim hcard e) hι xs)
  · intro I _ _ e ι hι xs r place reindex hre hreal
    have hF : F = recordAssign E N₀ I :=
      hβF.symm.trans (deltaAssign_eq E hθ N₀ hμle hcatμ hβlim hβθ hβcard e)
    exact (congrFun hF _).trans
      (recordAssign_of_realizes_reindex E hθ N₀ hμle hcatμ hβlim hβθ e
        (card_obj_of_horderIso E hμle hβlim hβcard e) hι xs r place reindex hre hreal)

/-! ### The regular cofinalities `τ_i` along the failing sequence (text.md 182) -/

/-- The regular cardinal `τ_i ≤ κ_i` exceeding `θ` and every earlier `κ_j`. -/
noncomputable def failingCof (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    (i : Below (Order.succ (profilePaletteBound K θ))) : Cardinal.{u} :=
  Order.succ (max θ
    (failingPriorBound θ fun j : {j : Below (Order.succ (profilePaletteBound K θ)) // j < i} =>
      failingSequence K θ hUnb j.1))

theorem failingCof_isRegular (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hθ : aleph0 ≤ θ)
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    (i : Below (Order.succ (profilePaletteBound K θ))) :
    Cardinal.IsRegular (failingCof K θ hUnb i) :=
  isRegular_succ (hθ.trans (le_max_left _ _))

theorem lt_failingCof (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    (i : Below (Order.succ (profilePaletteBound K θ))) :
    θ < failingCof K θ hUnb i :=
  (le_max_left _ _).trans_lt (Order.lt_succ _)

theorem failingCof_le (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    (i : Below (Order.succ (profilePaletteBound K θ))) :
    failingCof K θ hUnb i ≤ failingSequence K θ hUnb i := by
  rw [failingSequence_eq K θ hUnb i]
  have h := Classical.choose_spec (exists_fail_above K θ hUnb
    (failingPriorBound θ fun j : {j // j < i} => failingSequence K θ hUnb j.1))
  refine Order.succ_le_of_lt (max_lt ?_ h.2.1)
  exact (Order.lt_succ θ).trans_le ((le_max_right _ _).trans h.2.2.1)

theorem failingSequence_lt_failingCof (K : AbstractElementaryClass.{u}) (θ : Cardinal.{u})
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    {i j : Below (Order.succ (profilePaletteBound K θ))} (hij : i < j) :
    failingSequence K θ hUnb i < failingCof K θ hUnb j := by
  have hle : failingSequence K θ hUnb i ≤
      failingPriorBound θ fun k : {k // k < j} => failingSequence K θ hUnb k.1 := by
    dsimp [failingPriorBound]
    exact (le_max_left _ _).trans <| (Order.le_succ _).trans
      (Cardinal.le_sum (fun k : {k // k < j} =>
        Order.succ (max (failingSequence K θ hUnb k.1)
          (failingSequence K θ hUnb k.1 ^ θ))) ⟨i, hij⟩)
  exact (hle.trans (le_max_right _ _)).trans_lt (Order.lt_succ _)

/-- The recurring record-to-name function at stage `i` of the failing sequence. -/
theorem failing_recurring (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (N₀ : OrbitNaming K θ)
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ)
    (i : Below (Order.succ (profilePaletteBound K θ))) :
    ∃ F, RecursCofinally E N₀ (failingSequence K θ hUnb i) (failingCof K θ hUnb i) F := by
  have hspec := failingSequence_spec K θ hUnb i
  have hκ : aleph0 ≤ failingSequence K θ hUnb i :=
    (isLSBound_ls K).1.trans ((le_max_left _ _).trans hspec.2.1)
  exact exists_recurring_assign K E θ hθ N₀ _ _ hκ
    (hθ.trans (lt_failingCof K θ hUnb i).le) (failingCof_isRegular K θ hθ hUnb i)
    (failingCof_le K θ hUnb i) hspec.2.2

/-! ### Pigeonhole over the failing sizes (text.md 186) -/

/-- Any `P⁺`-indexed family of coded profiles repeats a value. -/
theorem exists_pair_same_profile (K : AbstractElementaryClass.{u}) (E : OrderPresentation K)
    (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ)
    (f : Below (Order.succ (profilePaletteBound K θ)) → FailProfile K E θ) :
    ∃ i j, i < j ∧ f i = f j := by
  classical
  let P := profilePaletteBound K θ
  let Idx := Below (Order.succ P)
  have hIdx : #Idx = Order.succ P := mk_ord_toType _
  have hPinf : aleph0 ≤ P := profilePaletteBound_aleph0_le K θ hθ
  have hIdxinf : aleph0 ≤ #Idx := by
    rw [hIdx]; exact hPinf.trans (Order.le_succ P)
  have hcod : #(FailProfile K E θ) < (#Idx).ord.cof := by
    rw [hIdx, (isRegular_succ hPinf).cof_ord]
    exact lt_of_le_of_lt (mk_failProfile_le K E θ hθ) (Order.lt_succ P)
  obtain ⟨Φ, hfiber⟩ := infinite_pigeonhole f hIdxinf hcod
  have h2 : (2 : Cardinal.{u}) ≤ #(f ⁻¹' {Φ}) := by
    rw [hfiber, hIdx]
    exact (le_of_lt (Nat.cast_lt.mpr (by decide : 2 < 3))).trans
      ((natCast_le_aleph0 (n := 3)).trans (hPinf.trans (Order.le_succ P)))
  have hnontriv : Nontrivial (f ⁻¹' {Φ}) :=
    Cardinal.one_lt_iff_nontrivial.mp (lt_of_lt_of_le one_lt_two h2)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (f ⁻¹' {Φ})
  have hfx : f x.1 = Φ := x.2
  have hfy : f y.1 = Φ := y.2
  have hne : x.1 ≠ y.1 := fun heq => hxy (Subtype.ext heq)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ⟨x.1, y.1, hlt, hfx.trans hfy.symm⟩
  · exact ⟨y.1, x.1, hgt, hfy.trans hfx.symm⟩

/-- From unboundedly many failing categoricity cardinals: two failing sizes `a < μ` with
`a^θ ≤ μ`, a `CommonProfileSetup` for the normalized naming, a common asymmetric named
arrow `p ⟶ r` whose source name occurs at size `a`, and one named arrow relation at both
sizes (text.md 186–188). -/
theorem exists_asymmetric_common_setup (K : AbstractElementaryClass.{u})
    (E : OrderPresentation K) (θ : Cardinal.{u}) (hθ : aleph0 ≤ θ) (N₀ : OrbitNaming K θ)
    (hUnb : ∀ B : Cardinal.{u}, ∃ κ, FailsReversal K θ κ ∧ B < κ) :
    ∃ (a μ : Cardinal.{u}) (haFail : FailsReversal K θ a) (hμFail : FailsReversal K θ μ)
      (hale : max (ls K) (Order.succ θ) ≤ a) (hμle : max (ls K) (Order.succ θ) ≤ μ),
      a < μ ∧ a ^ θ ≤ μ ∧
        Nonempty (CommonProfileSetup K E θ a μ N₀.normalize hθ) ∧
        ∃ p r : OrbitName K θ,
          NamedArrow K θ a N₀.normalize p r ∧ ¬ NamedArrow K θ a N₀.normalize r p ∧
            NamedArrow K θ μ N₀.normalize p r ∧ ¬ NamedArrow K θ μ N₀.normalize r p ∧
            (∃ (M : Model K.τ) (hM : K.Mem M), Model.card M = a ∧
              ∃ xs : Below θ → M.carrier,
                N₀.normalize.name hM xs (by rw [mk_ord_toType]) = p) ∧
            ∀ q q' : OrbitName K θ,
              NamedArrow K θ a N₀.normalize q q' ↔ NamedArrow K θ μ N₀.normalize q q' := by
  classical
  let N := N₀.normalize
  let f : Below (Order.succ (profilePaletteBound K θ)) → FailProfile K E θ := fun i =>
    { arrow := fun p r =>
        (Classical.dec (NamedArrow K θ (failingSequence K θ hUnb i) N p r)).decide
      assign := Classical.choose (failing_recurring K E θ hθ N₀ hUnb i) }
  obtain ⟨i, j, hij, hf⟩ := exists_pair_same_profile K E θ hθ f
  have hi := failingSequence_spec K θ hUnb i
  have hj := failingSequence_spec K θ hUnb j
  have hFa := Classical.choose_spec (failing_recurring K E θ hθ N₀ hUnb i)
  have hFμ := Classical.choose_spec (failing_recurring K E θ hθ N₀ hUnb j)
  have hassign : Classical.choose (failing_recurring K E θ hθ N₀ hUnb i) =
      Classical.choose (failing_recurring K E θ hθ N₀ hUnb j) :=
    congrArg FailProfile.assign hf
  rw [← hassign] at hFμ
  have harrow : ∀ p r : OrbitName K θ,
      NamedArrow K θ (failingSequence K θ hUnb i) N p r ↔
        NamedArrow K θ (failingSequence K θ hUnb j) N p r := by
    intro p r
    have h := congrFun (congrFun (congrArg FailProfile.arrow hf) p) r
    exact decide_eq_decide.mp h
  have hsetup := exists_common_profile_setup K E θ hθ N₀
    (failingSequence K θ hUnb i) (failingSequence K θ hUnb j) hi.2.1 hj.2.1 hi.1.1 hj.1.1
    (failingCof K θ hUnb i) (failingCof K θ hUnb j) (lt_failingCof K θ hUnb i)
    (failingSequence_lt_failingCof K θ hUnb hij) _ hFa hFμ
  obtain ⟨p, r, hpr, hrp, hpOcc⟩ :=
    exists_asymmetric_namedArrow K θ (failingSequence K θ hUnb i) N hθ hi.1 hi.2.1
  exact ⟨failingSequence K θ hUnb i, failingSequence K θ hUnb j, hi.1, hj.1, hi.2.1, hj.2.1,
    failingSequence_strict K θ hUnb hij, failingSequence_power_le K θ hUnb hij, hsetup,
    p, r, hpr, hrp, (harrow p r).1 hpr, fun h => hrp ((harrow r p).2 h), hpOcc, harrow⟩

end
end AEC
