module

public import AEC.Section2.CoherentColor
public import AEC.Section2.DirectedLimit
public import AEC.Section2.OrderPresentation
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Fin.Basic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- The position of each element of `s` inside the increasing enumeration of `t`. -/
noncomputable def placeEmb {I : Type u} [LinearOrder I] {s t : Finset I} (hsub : s ⊆ t) :
    Fin s.card ↪o Fin t.card :=
  OrderEmbedding.ofStrictMono
    (fun i => (t.orderIsoOfFin rfl).symm
      ⟨s.orderEmbOfFin rfl i, hsub (Finset.orderEmbOfFin_mem s rfl i)⟩)
    (fun i j hij => (t.orderIsoOfFin rfl).symm.strictMono <| by
      simpa using (s.orderEmbOfFin rfl).strictMono hij)

theorem placeEmb_apply {I : Type u} [LinearOrder I] {s t : Finset I} (hsub : s ⊆ t)
    (i : Fin s.card) :
    placeEmb hsub i =
      (t.orderIsoOfFin rfl).symm
        ⟨s.orderEmbOfFin rfl i, hsub (Finset.orderEmbOfFin_mem s rfl i)⟩ := rfl

theorem placeEmb_spec {I : Type u} [LinearOrder I] {s t : Finset I} (hsub : s ⊆ t)
    (i : Fin s.card) :
    t.orderEmbOfFin rfl (placeEmb hsub i) = s.orderEmbOfFin rfl i := by
  rw [placeEmb_apply, ← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

/-- The identity order embedding. -/
def idEmb {α : Type*} [LE α] : α ↪o α :=
  (OrderIso.refl α).toOrderEmbedding

theorem idEmb_apply {α : Type*} [LE α] (x : α) : idEmb x = x := by
  simp [idEmb, OrderIso.refl_apply]

theorem placeEmb_refl {I : Type u} [LinearOrder I] (s : Finset I) :
    placeEmb (Finset.Subset.refl s) = idEmb (α := Fin s.card) := by
  apply RelEmbedding.ext
  intro i
  apply (s.orderEmbOfFin rfl).injective
  rw [placeEmb_spec]
  rfl

theorem placeEmb_trans {I : Type u} [LinearOrder I] {s u t : Finset I}
    (hsu : s ⊆ u) (hut : u ⊆ t) :
    placeEmb (hsu.trans hut) = (placeEmb hsu).trans (placeEmb hut) := by
  apply RelEmbedding.ext
  intro i
  apply (t.orderEmbOfFin rfl).injective
  rw [RelEmbedding.trans_apply, placeEmb_spec, placeEmb_spec, placeEmb_spec]

theorem subModel_of_eq {M : Model K.τ} (hM : K.Mem M) {n : ℕ} (base : Fin n → M.carrier)
    {t u : {s : Finset (Fin n) // s.Nonempty}} (h : t = u) :
    subModel hM base t = subModel hM base u := by
  subst h
  rfl

theorem subIncl_of_eq {M : Model K.τ} (hM : K.Mem M) {n : ℕ} (base : Fin n → M.carrier)
    {t u : {s : Finset (Fin n) // s.Nonempty}} (h : t = u) :
    HEq (subIncl hM base t) (subIncl hM base u) := by
  subst h
  rfl

theorem subsetEnumerated_of_eq {M : Model K.τ} (hM : K.Mem M) {n : ℕ}
    (base : Fin n → M.carrier) (hbase : Function.Injective base)
    {t u : {s : Finset (Fin n) // s.Nonempty}} (h : t = u) :
    subsetEnumerated hM base hbase t = subsetEnumerated hM base hbase u := by
  subst h
  rfl

variable [ArbitrarilyLarge K]

/-- A realized sample of the standard color `dₙ`. -/
structure ColorWitness (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K]
    (n : ℕ) (hn : 0 < n) where
  model : Model K.τ
  mem : K.Mem model
  base : Fin n → model.carrier
  inj : Function.Injective base
  read : readFamily mem base inj = standardColor (K := K) n hn

theorem colorWitness_nonempty (n : ℕ) (hn : 0 < n) : Nonempty (ColorWitness K n hn) := by
  obtain ⟨α, lin, M, hM, ambient, hambient, hcard, hhom⟩ :=
    standardColor_unbounded (K := K) n hn aleph0 (le_refl _)
  letI : LinearOrder α := lin
  haveI : Infinite α := Cardinal.aleph0_le_mk_iff.mp hcard
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
  let base' : Fin n → M.carrier := fun i => ambient (s.orderEmbOfFin hs i)
  have hinj : Function.Injective base' :=
    fun i j hij => (s.orderEmbOfFin hs).injective (hambient hij)
  have hread : readFamily hM base' hinj = standardColor (K := K) n hn := by
    have htuple : tupleCode hM ambient hambient s hs = standardColor (K := K) n hn :=
      hhom s hs
    have heq : readFamily hM base' hinj = tupleCode hM ambient hambient s hs := by
      simp only [tupleCode, base']
    exact heq.trans htuple
  exact ⟨⟨M, hM, base', hinj, hread⟩⟩

noncomputable def colorWitness (n : ℕ) (hn : 0 < n) : ColorWitness K n hn :=
  Classical.choice (colorWitness_nonempty n hn)

theorem colorWitness_irrel {n : ℕ} (hn hn' : 0 < n) :
    HEq (colorWitness (K := K) n hn) (colorWitness (K := K) n hn') := by
  have h := Subsingleton.elim hn hn'
  subst h
  rfl

/-- The whole index `Fin n`, as a nonempty set of positions. -/
def fullSet (n : ℕ) (hn : 0 < n) : {t : Finset (Fin n) // t.Nonempty} :=
  ⟨Finset.univ, Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩⟩

/-- The hull of the whole realized `n`-tuple, enumerated by `Enum K`. -/
noncomputable def pieceEnum (n : ℕ) (hn : 0 < n) : Enumerated K :=
  subsetEnumerated (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (colorWitness (K := K) n hn).inj
    (fullSet n hn)

noncomputable def pieceModel (n : ℕ) (hn : 0 < n) : Model K.τ :=
  (pieceEnum (K := K) n hn).model

/-- The same hull, indexed by `n = k + 1`, so equal cardinals share one model. -/
noncomputable def pieceSucc (k : ℕ) : Model K.τ :=
  pieceModel (K := K) (k + 1) (Nat.succ_pos k)

theorem pieceSucc_mem (k : ℕ) : K.Mem (pieceSucc (K := K) k) := by
  unfold pieceSucc pieceModel pieceEnum subsetEnumerated
  exact subModel_mem (colorWitness (K := K) (k + 1) (Nat.succ_pos k)).mem
    (colorWitness (K := K) (k + 1) (Nat.succ_pos k)).base
    (fullSet (k + 1) (Nat.succ_pos k))

/-- The positions occupied by an order-embedded `m`-tuple. -/
def rangeSet {m n : ℕ} (hm : 0 < m) (e : Fin m ↪o Fin n) :
    {t : Finset (Fin n) // t.Nonempty} :=
  mapped e (fullSet m hm)

noncomputable def subsetEnum {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (e : Fin m ↪o Fin n) :
    Enumerated K :=
  subsetEnumerated (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (colorWitness (K := K) n hn).inj
    (rangeSet hm e)

theorem piece_subset_read {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (e : Fin m ↪o Fin n) :
    AtomCode.read (pieceEnum (K := K) m hm) = AtomCode.read (subsetEnum (K := K) hm hn e) := by
  have hrest : FamilyCode.pull e (standardColor (K := K) n hn) =
      standardColor (K := K) m hm :=
    standardColor_restrict (K := K) hm hn e
  have hcode := congrArg (fun c : FamilyCode K m => c.code (fullSet m hm)) hrest
  simp only [FamilyCode.pull, rangeSet] at hcode
  have hpiece : AtomCode.read (pieceEnum (K := K) m hm) =
      (standardColor (K := K) m hm).code (fullSet m hm) := by
    rw [← (colorWitness (K := K) m hm).read]
    rfl
  have hsub : AtomCode.read (subsetEnum (K := K) hm hn e) =
      (standardColor (K := K) n hn).code (rangeSet hm e) := by
    rw [← (colorWitness (K := K) n hn).read]
    rfl
  rw [hpiece, hsub]
  exact hcode.symm

/-- The copy of the `m`-hull inside the realized `n`-tuple, along `e`. -/
noncomputable def arityIso {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (e : Fin m ↪o Fin n) :
    (pieceEnum (K := K) m hm).model.carrier ≃[K.τ] (subsetEnum (K := K) hm hn e).model.carrier :=
  codeEquiv (piece_subset_read hm hn e)

theorem codeEquiv_enum {E F : Enumerated K} (h : AtomCode.read E = AtomCode.read F) (η : Enum K) :
    codeEquiv h (E.enum η) = F.enum η := by
  change codeEmbedding h (E.enum η) = F.enum η
  show F.enum (E.name (E.enum η)) = F.enum η
  exact (AtomCode.same_iff h _ _).mp (E.enum_name (E.enum η))

theorem codeEquiv_of_eq {E F : Enumerated K} (h : AtomCode.read E = AtomCode.read F)
    (hEF : E = F) (x : E.model.carrier) : HEq (codeEquiv h x) x := by
  subst hEF
  apply heq_of_eq
  show codeEmbedding h x = x
  show E.enum (E.name x) = x
  exact E.enum_name x

/-- An order embedding `Fin n ↪o Fin n` covers every index. -/
theorem rangeSet_endo {n : ℕ} (hn : 0 < n) (e : Fin n ↪o Fin n) :
    rangeSet hn e = fullSet n hn := by
  apply Subtype.ext
  refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
  simp [rangeSet, mapped, fullSet, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem subsetEnum_endo {n : ℕ} (hn : 0 < n) (e : Fin n ↪o Fin n) :
    subsetEnum (K := K) hn hn e = pieceEnum (K := K) n hn :=
  subsetEnumerated_of_eq (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
    (colorWitness (K := K) n hn).inj (rangeSet_endo hn e)

/-- Every name from the embedded `m`-hull lands in the `n`-hull. -/
theorem arityCovered {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (e : Fin m ↪o Fin n)
    (x : (pieceModel (K := K) m hm).carrier) :
    ∃ b : (pieceModel (K := K) n hn).carrier,
      subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn) b =
        subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)
          ((arityIso (K := K) hm hn e) x) := by
  by_cases hlt : m < n
  · have hsub : (rangeSet hm e).1 ⊆ (fullSet n hn).1 := fun _ _ => Finset.mem_univ _
    have hcard : (rangeSet hm e).1.card < (fullSet n hn).1.card := by
      have hleft : (rangeSet hm e).1.card = m := by
        simp [rangeSet, mapped, fullSet, Finset.card_map, Finset.card_univ, Fintype.card_fin]
      have hright : (fullSet n hn).1.card = n := by
        simp [fullSet, Finset.card_univ, Fintype.card_fin]
      rw [hleft, hright]
      exact hlt
    have htmem : (rangeSet hm e).1 ∈ properSubs (fullSet n hn).1 :=
      mem_properSubs.mpr ⟨hsub, (rangeSet hm e).2, hcard⟩
    have hrange : subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)
        ((arityIso (K := K) hm hn e) x) ∈
        (subHull (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn)).1 := by
      rw [subHull_eq (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn)]
      refine Or.inr ?_
      refine Set.mem_iUnion.mpr ?_
      refine ⟨ULift.up ⟨(rangeSet hm e).1, htmem⟩, ?_⟩
      exact ⟨(arityIso (K := K) hm hn e) x, rfl⟩
    exact subIncl_covers (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
      (fullSet n hn) hrange
  · have hmn : m = n := le_antisymm (orderEmb_card_le e) (not_lt.mp hlt)
    have htu : rangeSet hm e = fullSet n hn := by
      apply Subtype.ext
      refine Finset.eq_of_subset_of_card_le (fun _ _ => Finset.mem_univ _) ?_
      simp [rangeSet, mapped, fullSet, Finset.card_map, Finset.card_univ,
        Fintype.card_fin, hmn]
    have hmodel : subModel (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
          (fullSet n hn) =
        subModel (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
          (rangeSet hm e) :=
      (subModel_of_eq (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base htu).symm
    have hincl : HEq
        (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn))
        (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
          (rangeSet hm e)) :=
      HEq.symm (subIncl_of_eq (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base htu)
    refine ⟨cast (congrArg Model.carrier hmodel).symm ((arityIso (K := K) hm hn e) x), ?_⟩
    exact cast_incl_apply
      (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn))
      (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e))
      hmodel hincl ((arityIso (K := K) hm hn e) x)

/-- The strong map from the `m`-copy to the `n`-copy along an order embedding of indices. -/
noncomputable def arityMap {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (e : Fin m ↪o Fin n) :
    (pieceModel (K := K) m hm).carrier ↪[K.τ] (pieceModel (K := K) n hn).carrier :=
  factorEmbedding
    ((subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)).comp
      (arityIso (K := K) hm hn e).toEmbedding)
    (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn))
    (arityCovered hm hn e)

theorem arityMap_incl {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (e : Fin m ↪o Fin n)
    (x : (pieceModel (K := K) m hm).carrier) :
    subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn) (arityMap (K := K) hm hn e x) =
      subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)
        ((arityIso (K := K) hm hn e) x) := by
  unfold arityMap
  exact congrFun (congrArg (⇑)
    (factorEmbedding_comp
      ((subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
        (rangeSet hm e)).comp (arityIso (K := K) hm hn e).toEmbedding)
      (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
        (fullSet n hn))
      (arityCovered hm hn e))) x

theorem arityMap_strong {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (e : Fin m ↪o Fin n) :
    K.Strong (arityMap (K := K) hm hn e) := by
  have hcomp :
      (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn)).comp
          (arityMap (K := K) hm hn e) =
        (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)).comp
          (arityIso (K := K) hm hn e).toEmbedding :=
    factorEmbedding_comp _ _ _
  have hthrough : K.Strong
      ((subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)).comp
        (arityIso (K := K) hm hn e).toEmbedding) :=
    K.strong_trans (arityIso (K := K) hm hn e).toEmbedding
      (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e))
      (codeStrong (subModel_mem (colorWitness (K := K) m hm).mem (colorWitness (K := K) m hm).base (fullSet m hm))
        (piece_subset_read hm hn e))
      (subIncl_strong (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e))
  exact K.coherence (arityMap (K := K) hm hn e)
    ((subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)).comp
      (arityIso (K := K) hm hn e).toEmbedding)
    (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn))
    hthrough
    (subIncl_strong (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn))
    hcomp

theorem arityMap_enum_incl {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (e : Fin m ↪o Fin n)
    (η : Enum K) :
    subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn)
        (arityMap (K := K) hm hn e ((pieceEnum (K := K) m hm).enum η)) =
      subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)
        ((subsetEnum (K := K) hm hn e).enum η) := by
  refine (arityMap_incl hm hn e ((pieceEnum (K := K) m hm).enum η)).trans ?_
  exact congrArg
    (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e))
    (codeEquiv_enum (piece_subset_read hm hn e) η)

theorem standard_link_iff {n : ℕ} (hn : 0 < n)
    (t u : {s : Finset (Fin n) // s.Nonempty}) (η ζ : Enum K) :
    (standardColor (K := K) n hn).link t u η ζ ↔
      subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base t
          ((subsetEnumerated (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
            (colorWitness (K := K) n hn).inj t).enum η) =
        subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base u
          ((subsetEnumerated (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
            (colorWitness (K := K) n hn).inj u).enum ζ) := by
  rw [← (colorWitness (K := K) n hn).read]
  rfl

theorem standard_link_pull {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (e : Fin m ↪o Fin n)
    (t u : {s : Finset (Fin m) // s.Nonempty}) (η ζ : Enum K) :
    (standardColor (K := K) m hm).link t u η ζ ↔
      (standardColor (K := K) n hn).link (mapped e t) (mapped e u) η ζ := by
  have h := congrArg (fun c : FamilyCode K m => c.link t u η ζ)
    (standardColor_restrict (K := K) hm hn e)
  simpa [FamilyCode.pull] using h.symm

theorem mapped_trans {a b c : ℕ} (e : Fin a ↪o Fin b) (f : Fin b ↪o Fin c)
    (t : {s : Finset (Fin a) // s.Nonempty}) :
    mapped f (mapped e t) = mapped (e.trans f) t := by
  apply Subtype.ext
  simp only [mapped]
  rw [Finset.map_map]
  congr 1

theorem rangeSet_trans {m p n : ℕ} (hm : 0 < m) (e : Fin m ↪o Fin p) (f : Fin p ↪o Fin n) :
    rangeSet hm (e.trans f) = mapped f (rangeSet hm e) := by
  simp only [rangeSet]
  exact (mapped_trans e f (fullSet m hm)).symm

theorem rangeSet_full {n : ℕ} (hn : 0 < n) (e : Fin n ↪o Fin n) :
    mapped e (fullSet n hn) = rangeSet hn e := rfl

/-- Passing to a larger index set and then to a still larger one is the direct passage. -/
theorem arityMap_trans {m p n : ℕ} (hm : 0 < m) (hp : 0 < p) (hn : 0 < n)
    (e : Fin m ↪o Fin p) (f : Fin p ↪o Fin n) :
    arityMap (K := K) hm hn (e.trans f) = (arityMap (K := K) hp hn f).comp (arityMap (K := K) hm hp e) := by
  ext x
  set η : Enum K := (pieceEnum (K := K) m hm).name x
  have hx : (pieceEnum (K := K) m hm).enum η = x := (pieceEnum (K := K) m hm).enum_name x
  have hleft := arityMap_enum_incl hm hn (e.trans f) η
  set y : (pieceModel (K := K) p hp).carrier :=
    arityMap (K := K) hm hp e ((pieceEnum (K := K) m hm).enum η)
  set ζ : Enum K := (pieceEnum (K := K) p hp).name y
  have hy : (pieceEnum (K := K) p hp).enum ζ = y := (pieceEnum (K := K) p hp).enum_name y
  have hmid := arityMap_enum_incl hm hp e η
  have hright := arityMap_incl hp hn f y
  have hlinkp : (standardColor (K := K) p hp).link (rangeSet hm e) (fullSet p hp) η ζ := by
    rw [standard_link_iff]
    exact hmid.symm.trans (congrArg
      (subIncl (colorWitness (K := K) p hp).mem (colorWitness (K := K) p hp).base (fullSet p hp)) hy).symm
  have hlinkn : (standardColor (K := K) n hn).link
      (mapped f (rangeSet hm e)) (mapped f (fullSet p hp)) η ζ :=
    (standard_link_pull hp hn f (rangeSet hm e) (fullSet p hp) η ζ).mp hlinkp
  have hrange : mapped f (rangeSet hm e) = rangeSet hm (e.trans f) :=
    (rangeSet_trans hm e f).symm
  have hfull : mapped f (fullSet p hp) = rangeSet hp f := rfl
  rw [hrange, hfull] at hlinkn
  rw [standard_link_iff] at hlinkn
  have hcode : (arityIso (K := K) hp hn f) y = (subsetEnum (K := K) hp hn f).enum ζ := by
    rw [← hy]
    exact codeEquiv_enum (piece_subset_read hp hn f) ζ
  have himages : subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
        (fullSet n hn) (arityMap (K := K) hm hn (e.trans f) x) =
      subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
        (fullSet n hn) (((arityMap (K := K) hp hn f).comp
          (arityMap (K := K) hm hp e)) x) := by
    have harg : arityMap (K := K) hm hn (e.trans f) x =
        arityMap (K := K) hm hn (e.trans f) ((pieceEnum (K := K) m hm).enum η) :=
      congrArg _ hx.symm
    refine (congrArg _ harg).trans (hleft.trans (hlinkn.trans ?_))
    refine (congrArg
      (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hp f))
      hcode.symm).trans (hright.symm.trans ?_)
    refine congrArg _ ?_
    have hcomp : ((arityMap (K := K) hp hn f).comp (arityMap (K := K) hm hp e)) x =
        arityMap (K := K) hp hn f y := by
      rw [← hx]
      rfl
    exact hcomp.symm
  exact (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
    (fullSet n hn)).injective himages

theorem arityMap_refl {n : ℕ} (hn : 0 < n) :
    arityMap (K := K) hn hn (idEmb (α := Fin n)) =
      Language.Embedding.refl K.τ (pieceModel (K := K) n hn).carrier := by
  ext x
  apply (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn)).injective
  rw [arityMap_incl, Language.Embedding.refl_apply]
  have htu : rangeSet hn (idEmb (α := Fin n)) = fullSet n hn :=
    rangeSet_endo hn (idEmb (α := Fin n))
  have henum : subsetEnum (K := K) hn hn (idEmb (α := Fin n)) = pieceEnum (K := K) n hn :=
    subsetEnum_endo hn (idEmb (α := Fin n))
  have hmodel : subModel (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hn
      (idEmb (α := Fin n))) =
      subModel (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn) :=
    subModel_of_eq (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base htu
  have hxy : HEq ((arityIso (K := K) hn hn (idEmb (α := Fin n))) x) x :=
    codeEquiv_of_eq (piece_subset_read hn hn (idEmb (α := Fin n))) henum.symm x
  exact incl_heq_apply hmodel
    (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base
      (rangeSet hn (idEmb (α := Fin n))))
    (subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn))
    (subIncl_of_eq (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base htu)
    ((arityIso (K := K) hn hn (idEmb (α := Fin n))) x) x hxy

noncomputable def arityMapSucc {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) :
    (pieceSucc (K := K) k).carrier ↪[K.τ] (pieceSucc (K := K) l).carrier :=
  arityMap (K := K) (Nat.succ_pos k) (Nat.succ_pos l) e

theorem arityMapSucc_refl (k : ℕ) :
    arityMapSucc (K := K) (idEmb (α := Fin (k + 1))) =
      Language.Embedding.refl K.τ (pieceSucc (K := K) k).carrier :=
  arityMap_refl (Nat.succ_pos k)

theorem arityMapSucc_trans {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1))
    (f : Fin (l + 1) ↪o Fin (m + 1)) :
    arityMapSucc (K := K) (e.trans f) = (arityMapSucc (K := K) f).comp (arityMapSucc (K := K) e) :=
  arityMap_trans (Nat.succ_pos k) (Nat.succ_pos l) (Nat.succ_pos m) e f

theorem arityMapSucc_strong {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) :
    K.Strong (arityMapSucc (K := K) e) :=
  arityMap_strong (Nat.succ_pos k) (Nat.succ_pos l) e

/-- Positions of `s` inside `t`, written on the successor lengths `card.pred + 1`. -/
noncomputable def placeSucc {I : Type u} [LinearOrder I] {s t : Finset I}
    (hsub : s ⊆ t) (hs : s.Nonempty) (ht : t.Nonempty) :
    Fin (s.card.pred + 1) ↪o Fin (t.card.pred + 1) :=
  (Fin.castOrderIso (Nat.succ_pred (Finset.card_pos.mpr hs).ne')).toOrderEmbedding.trans
    ((placeEmb hsub).trans
      (Fin.castOrderIso (Nat.succ_pred (Finset.card_pos.mpr ht).ne')).symm.toOrderEmbedding)

theorem placeSucc_refl {I : Type u} [LinearOrder I] (s : Finset I) (hs : s.Nonempty) :
    placeSucc (Finset.Subset.refl s) hs hs =
      idEmb (α := Fin (s.card.pred + 1)) := by
  have hplace : placeEmb (Finset.Subset.refl s) = idEmb (α := Fin s.card) := placeEmb_refl s
  apply RelEmbedding.ext
  intro i
  rw [placeSucc, hplace, RelEmbedding.trans_apply, RelEmbedding.trans_apply, idEmb_apply,
    OrderIso.coe_toOrderEmbedding, OrderIso.coe_toOrderEmbedding]
  exact OrderIso.symm_apply_apply _ i

theorem placeSucc_trans {I : Type u} [LinearOrder I] {s u t : Finset I}
    (hsu : s ⊆ u) (hut : u ⊆ t) (hs : s.Nonempty) (hu : u.Nonempty) (ht : t.Nonempty) :
    placeSucc (hsu.trans hut) hs ht =
      (placeSucc hsu hs hu).trans (placeSucc hut hu ht) := by
  have hplace : placeEmb (hsu.trans hut) = (placeEmb hsu).trans (placeEmb hut) :=
    placeEmb_trans hsu hut
  ext i
  simp only [placeSucc, hplace, RelEmbedding.trans_apply, OrderIso.coe_toOrderEmbedding,
    OrderIso.apply_symm_apply, Fin.castOrderIso_apply, Fin.val_cast]

/-- The directed system of finite-support copies inside a nonempty linear order. -/
noncomputable def emSystem (I : Type u) [LinearOrder I] [Nonempty I] : DirectedSystem K.τ where
  ι := {s : Finset I // s.Nonempty}
  nonempty := ⟨⟨{Classical.choice ‹Nonempty I›}, Finset.singleton_nonempty _⟩⟩
  rel s t := s.1 ⊆ t.1
  refl s := Finset.Subset.refl s.1
  trans hsu hut := Finset.Subset.trans hsu hut
  directed s t :=
    ⟨⟨s.1 ∪ t.1, by
        obtain ⟨a, ha⟩ := s.2
        exact ⟨a, Finset.mem_union.mpr (Or.inl ha)⟩⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩
  obj s := pieceSucc (K := K) s.1.card.pred
  map {s t} h := arityMapSucc (K := K) (placeSucc h s.2 t.2)
  map_refl s := by
    have hp : placeSucc (Finset.Subset.refl s.1) s.2 s.2 =
        idEmb (α := Fin (s.1.card.pred + 1)) :=
      placeSucc_refl s.1 s.2
    simpa [hp] using arityMapSucc_refl s.1.card.pred
  map_trans {s t u} hij hjk := by
    have hp : placeSucc (Finset.Subset.trans hij hjk) s.2 u.2 =
        (placeSucc hij s.2 t.2).trans (placeSucc hjk t.2 u.2) :=
      placeSucc_trans hij hjk s.2 t.2 u.2
    simpa [hp] using
      arityMapSucc_trans (placeSucc hij s.2 t.2) (placeSucc hjk t.2 u.2)

theorem emSystem_mem {I : Type u} [LinearOrder I] [Nonempty I]
    (s : (emSystem (K := K) I).ι) : K.Mem ((emSystem (K := K) I).obj s) :=
  pieceSucc_mem s.1.card.pred

theorem emSystem_strong {I : Type u} [LinearOrder I] [Nonempty I]
    {s t : (emSystem (K := K) I).ι} (h : (emSystem (K := K) I).rel s t) :
    K.Strong ((emSystem (K := K) I).map h) :=
  arityMapSucc_strong (placeSucc h s.2 t.2)

/-- The direct limit of the finite-support copies. Lemma 2.1 puts it in `K`. -/
noncomputable def emLimit (I : Type u) [LinearOrder I] [Nonempty I] :
    DirectLimit (emSystem (K := K) I) :=
  Classical.choose (directLimit_in_class K (emSystem (K := K) I) emSystem_mem
    (fun {_ _} h => emSystem_strong (I := I) h))

theorem emLimit_spec (I : Type u) [LinearOrder I] [Nonempty I] :
    IsLimitInClass K (emLimit (K := K) I) :=
  Classical.choose_spec (directLimit_in_class K (emSystem (K := K) I) emSystem_mem
    (fun {_ _} h => emSystem_strong (I := I) h))

/-- The image of a nonempty finite set under an order embedding. -/
def imageIndex {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    (s : {t : Finset I // t.Nonempty}) : {t : Finset J // t.Nonempty} :=
  ⟨s.1.map f.toEmbedding, Finset.map_nonempty.mpr s.2⟩

theorem imageIndex_card {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    (s : {t : Finset I // t.Nonempty}) : (imageIndex f s).1.card = s.1.card := by
  simp [imageIndex, Finset.card_map]

theorem orderEmbOfFin_orderMap {I J : Type u} [LinearOrder I] [LinearOrder J]
    (f : I ↪o J) (s : Finset I) (i : Fin s.card) :
    (s.map f.toEmbedding).orderEmbOfFin (Finset.card_map f.toEmbedding) i =
      f (s.orderEmbOfFin rfl i) := by
  have hmono : StrictMono (fun j : Fin s.card => f (s.orderEmbOfFin rfl j)) :=
    fun j k hjk => (f.lt_iff_lt).mpr ((s.orderEmbOfFin rfl).strictMono hjk)
  have hfun :
      (fun j : Fin s.card => f (s.orderEmbOfFin rfl j)) =
        ⇑((s.map f.toEmbedding).orderEmbOfFin (Finset.card_map f.toEmbedding)) :=
    Finset.orderEmbOfFin_unique (Finset.card_map f.toEmbedding)
      (fun j => Finset.mem_map.mpr ⟨s.orderEmbOfFin rfl j, Finset.orderEmbOfFin_mem s rfl j, rfl⟩)
      hmono
  exact (congrFun hfun i).symm

/-- Relative positions are preserved by an order embedding of the ambient order. -/
theorem placeEmb_map {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    {s t : Finset I} (hsub : s ⊆ t) :
    let hs : (s.map f.toEmbedding).card = s.card := Finset.card_map f.toEmbedding
    let ht : (t.map f.toEmbedding).card = t.card := Finset.card_map f.toEmbedding
    (placeEmb hsub).trans (Fin.castOrderIso ht.symm).toOrderEmbedding =
      (Fin.castOrderIso hs.symm).toOrderEmbedding.trans
        (placeEmb (Finset.map_subset_map.mpr hsub)) := by
  intro hs ht
  apply RelEmbedding.ext
  intro i
  apply ((t.map f.toEmbedding).orderEmbOfFin rfl).injective
  simp only [RelEmbedding.trans_apply, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply]
  rw [orderEmbOfFin_cast (t.map f.toEmbedding) ht ((placeEmb hsub) i)]
  rw [orderEmbOfFin_orderMap f t ((placeEmb hsub) i), placeEmb_spec hsub i]
  rw [← orderEmbOfFin_orderMap f s i]
  rw [← orderEmbOfFin_cast (s.map f.toEmbedding) hs i]
  rw [placeEmb_spec (Finset.map_subset_map.mpr hsub) (Fin.cast hs.symm i)]

/-- The order-isomorphism `Fin (card.pred + 1) ≃o Fin (image.card.pred + 1)`. -/
noncomputable def indexCast {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    (s : {t : Finset I // t.Nonempty}) :
    Fin (s.1.card.pred + 1) ↪o Fin ((imageIndex f s).1.card.pred + 1) :=
  (Fin.castOrderIso (congrArg (fun n : ℕ => n.pred + 1) (imageIndex_card f s)).symm).toOrderEmbedding

/-- Substitution preserves the passage from a subset to a larger finite set. -/
theorem placeSucc_map {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    {s t : Finset I} (hsub : s ⊆ t) (hs : s.Nonempty) (ht : t.Nonempty) :
    (placeSucc hsub hs ht).trans (indexCast f ⟨t, ht⟩) =
      (indexCast f ⟨s, hs⟩).trans
        (placeSucc (Finset.map_subset_map.mpr hsub)
          (Finset.map_nonempty.mpr hs) (Finset.map_nonempty.mpr ht)) := by
  ext i
  simp only [placeSucc, indexCast, RelEmbedding.trans_apply, OrderIso.coe_toOrderEmbedding,
    Fin.castOrderIso_apply, Fin.coe_cast, OrderIso.apply_symm_apply]
  have hnat := congrFun (congrArg (⇑) (placeEmb_map f hsub))
    (Fin.cast (Nat.succ_pred (Finset.card_pos.mpr hs).ne') i)
  exact congrArg Fin.val hnat

theorem imageIndex_mono {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    {s t : {u : Finset I // u.Nonempty}} (h : s.1 ⊆ t.1) :
    (imageIndex f s).1 ⊆ (imageIndex f t).1 :=
  Finset.map_subset_map.mpr h

theorem imageIndex_trans {I J P : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder P]
    (f : I ↪o J) (g : J ↪o P) (s : {t : Finset I // t.Nonempty}) :
    imageIndex (f.trans g) s = imageIndex g (imageIndex f s) := by
  apply Subtype.ext
  simp only [imageIndex, RelEmbedding.trans_apply]
  rw [Finset.map_map]
  rfl

/-- The copy of a finite set, transported along an order embedding to the copy of its image. -/
noncomputable def componentMap {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    (s : {t : Finset I // t.Nonempty}) :
    (pieceSucc (K := K) s.1.card.pred).carrier ↪[K.τ]
      (pieceSucc (K := K) (imageIndex f s).1.card.pred).carrier :=
  arityMapSucc (K := K) (indexCast f s)

theorem componentMap_strong {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    (s : {t : Finset I // t.Nonempty}) : K.Strong (componentMap (K := K) f s) :=
  arityMapSucc_strong (indexCast f s)

/-- The image of a system index, kept at the system’s own index type. -/
def systemImage {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (s : (emSystem (K := K) I).ι) : (emSystem (K := K) J).ι :=
  ⟨s.1.map f.toEmbedding, Finset.map_nonempty.mpr s.2⟩

theorem systemImage_mono {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) {s t : (emSystem (K := K) I).ι}
    (h : (emSystem (K := K) I).rel s t) :
    (emSystem (K := K) J).rel (systemImage (K := K) f s) (systemImage (K := K) f t) :=
  Finset.map_subset_map.mpr h

noncomputable def systemComponent {I J : Type u} [LinearOrder I] [LinearOrder J]
    [Nonempty I] [Nonempty J] (f : I ↪o J) (s : (emSystem (K := K) I).ι) :
    ((emSystem (K := K) I).obj s).carrier ↪[K.τ]
      ((emSystem (K := K) J).obj (systemImage (K := K) f s)).carrier :=
  componentMap (K := K) f s

noncomputable def substAt {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) (s : (emSystem (K := K) I).ι) :
    ((emSystem (K := K) I).obj s).carrier ↪[K.τ] (emLimit (K := K) J).obj.carrier :=
  ((emLimit (K := K) J).canon (systemImage (K := K) f s)).comp
    (systemComponent (K := K) f s)

theorem systemComponent_strong {I J : Type u} [LinearOrder I] [LinearOrder J]
    [Nonempty I] [Nonempty J] (f : I ↪o J) (s : (emSystem (K := K) I).ι) :
    K.Strong (systemComponent (K := K) f s) := by
  unfold systemComponent
  exact componentMap_strong (K := K) f s

theorem substAt_strong {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) (s : (emSystem (K := K) I).ι) :
    K.Strong (substAt (K := K) f s) :=
  K.strong_trans (systemComponent (K := K) f s)
    ((emLimit (K := K) J).canon (systemImage (K := K) f s))
    (systemComponent_strong (K := K) f s)
    ((emLimit_spec (K := K) J).2.1 (systemImage (K := K) f s))

theorem component_square {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    {s t : {u : Finset I // u.Nonempty}} (h : s.1 ⊆ t.1) :
    (componentMap (K := K) f t).comp (arityMapSucc (placeSucc h s.2 t.2)) =
      (arityMapSucc (placeSucc (imageIndex_mono f h) (imageIndex f s).2 (imageIndex f t).2)).comp
        (componentMap (K := K) f s) := by
  have horder : (placeSucc h s.2 t.2).trans (indexCast f t) =
      (indexCast f s).trans
        (placeSucc (imageIndex_mono f h) (imageIndex f s).2 (imageIndex f t).2) :=
    placeSucc_map f h s.2 t.2
  unfold componentMap
  rw [← arityMapSucc_trans (placeSucc h s.2 t.2) (indexCast f t), horder, arityMapSucc_trans]

theorem system_component_square {I J : Type u} [LinearOrder I] [LinearOrder J]
    [Nonempty I] [Nonempty J] (f : I ↪o J) {s t : (emSystem (K := K) I).ι}
    (h : (emSystem (K := K) I).rel s t) :
    (systemComponent (K := K) f t).comp ((emSystem (K := K) I).map h) =
      ((emSystem (K := K) J).map (systemImage_mono (K := K) f h)).comp
        (systemComponent (K := K) f s) := by
  unfold systemComponent
  rw [show (emSystem (K := K) I).map h = arityMapSucc (placeSucc h s.2 t.2) from rfl]
  rw [show (emSystem (K := K) J).map (systemImage_mono (K := K) f h) =
      arityMapSucc (placeSucc (imageIndex_mono f h) (imageIndex f s).2 (imageIndex f t).2) from rfl]
  exact component_square (K := K) f h

theorem substAt_compat {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) {s t : (emSystem (K := K) I).ι}
    (h : (emSystem (K := K) I).rel s t) :
    (substAt (K := K) f t).comp ((emSystem (K := K) I).map h) = substAt (K := K) f s := by
  ext x
  rw [substAt, substAt, Language.Embedding.comp_apply, Language.Embedding.comp_apply,
    Language.Embedding.comp_apply]
  have happ := congrFun (congrArg (⇑) (system_component_square (K := K) f h)) x
  rw [Language.Embedding.comp_apply, Language.Embedding.comp_apply] at happ
  rw [happ]
  have hcan := congrFun (congrArg (⇑)
      ((emLimit (K := K) J).compat (systemImage_mono (K := K) f h)))
    (systemComponent (K := K) f s x)
  rw [Language.Embedding.comp_apply] at hcan
  exact hcan

/-- `E(f)`, induced by substitution on every finite-support copy. -/
noncomputable def emMap {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) :
    (emLimit (K := K) I).obj.carrier ↪[K.τ] (emLimit (K := K) J).obj.carrier :=
  Classical.choose ((emLimit_spec (K := K) I).2.2 (emLimit (K := K) J).obj
    (substAt (K := K) f) (emLimit_spec (K := K) J).1
    (substAt_strong (K := K) f) (fun h => substAt_compat (K := K) f h))

theorem emMap_strong {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) : K.Strong (emMap (K := K) f) :=
  (Classical.choose_spec ((emLimit_spec (K := K) I).2.2 (emLimit (K := K) J).obj
    (substAt (K := K) f) (emLimit_spec (K := K) J).1
    (substAt_strong (K := K) f) (fun h => substAt_compat (K := K) f h))).1

theorem emMap_canon {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) (s : (emSystem (K := K) I).ι) :
    (emMap (K := K) f).comp ((emLimit (K := K) I).canon s) = substAt (K := K) f s :=
  (Classical.choose_spec ((emLimit_spec (K := K) I).2.2 (emLimit (K := K) J).obj
    (substAt (K := K) f) (emLimit_spec (K := K) J).1
    (substAt_strong (K := K) f) (fun h => substAt_compat (K := K) f h))).2 s

/-- Two maps out of the limit that agree on every finite-support copy are equal. -/
theorem em_agreed {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (φ ψ : (emLimit (K := K) I).obj.carrier ↪[K.τ] (emLimit (K := K) J).obj.carrier)
    (h : ∀ s : (emSystem (K := K) I).ι,
      φ.comp ((emLimit (K := K) I).canon s) = ψ.comp ((emLimit (K := K) I).canon s)) :
    φ = ψ := by
  ext x
  obtain ⟨s, y, rfl⟩ := (emLimit (K := K) I).joint x
  exact congrFun (congrArg (⇑) (h s)) y ▸ rfl

theorem systemImage_refl {I : Type u} [LinearOrder I] [Nonempty I]
    (s : (emSystem (K := K) I).ι) :
    systemImage (K := K) (OrderIso.refl I).toOrderEmbedding s = s := by
  apply Subtype.ext
  ext x
  simp [systemImage, OrderIso.refl_apply]

theorem eqMp_proof_irrel {α β : Sort _} {h₁ h₂ : α = β} (x : α) : Eq.mp h₁ x = Eq.mp h₂ x := by
  have : h₁ = h₂ := Subsingleton.elim h₁ h₂
  rw [this]

theorem arityMapSucc_cast {k l : ℕ} (h : k + 1 = l + 1) (x : (pieceSucc (K := K) k).carrier) :
    arityMapSucc (K := K) (Fin.castOrderIso h).toOrderEmbedding x =
      Eq.mp (congrArg (fun n => (pieceSucc (K := K) n).carrier) (Nat.succ_injective h)) x := by
  have hkl : k = l := Nat.succ_injective h
  subst hkl
  have hid : (Fin.castOrderIso h).toOrderEmbedding = idEmb (α := Fin (k + 1)) := by
    ext i
    simp [idEmb, Fin.castOrderIso_apply, Fin.val_cast]
  rw [hid, arityMapSucc_refl, eqMp_id, Language.Embedding.refl_apply]

theorem systemComponent_refl_apply {I : Type u} [LinearOrder I] [Nonempty I]
    (s : (emSystem (K := K) I).ι) (x : ((emSystem (K := K) I).obj s).carrier) :
    systemComponent (K := K) (OrderIso.refl I).toOrderEmbedding s x =
      Eq.mp (congrArg (fun i => ((emSystem (K := K) I).obj i).carrier)
        (systemImage_refl s).symm) x := by
  unfold systemComponent componentMap
  let hlen := (congrArg (fun n : ℕ => n.pred + 1)
    (imageIndex_card (OrderIso.refl I).toOrderEmbedding s)).symm
  have hmap := arityMapSucc_cast (K := K) hlen x
  exact hmap.trans (eqMp_proof_irrel x)

theorem substAt_refl {I : Type u} [LinearOrder I] [Nonempty I]
    (s : (emSystem (K := K) I).ι) :
    substAt (K := K) (OrderIso.refl I).toOrderEmbedding s =
      (emLimit (K := K) I).canon s := by
  ext x
  rw [substAt, Language.Embedding.comp_apply, systemComponent_refl_apply s x]
  exact canon_transport (emLimit (K := K) I) (systemImage_refl s).symm x

theorem emMap_id {I : Type u} [LinearOrder I] [Nonempty I] :
    emMap (K := K) (OrderIso.refl I).toOrderEmbedding =
      Language.Embedding.refl K.τ (emLimit (K := K) I).obj.carrier :=
  em_agreed (emMap (K := K) (OrderIso.refl I).toOrderEmbedding)
    (Language.Embedding.refl K.τ (emLimit (K := K) I).obj.carrier)
    (fun s => by rw [emMap_canon, substAt_refl, Language.Embedding.refl_comp])

theorem systemImage_trans {I J P : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder P]
    [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P)
    (s : (emSystem (K := K) I).ι) :
    systemImage (K := K) (f.trans g) s =
      systemImage (K := K) g (systemImage (K := K) f s) := by
  apply Subtype.ext
  ext x
  simp only [systemImage, Finset.mem_map, RelEmbedding.coe_toEmbedding, RelEmbedding.trans_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem eqMp_trans {α β γ : Sort _} (h : α = β) (k : β = γ) (x : α) :
    Eq.mp k (Eq.mp h x) = Eq.mp (h.trans k) x := by
  subst h
  subst k
  rfl

theorem eqMp_triple {α β γ δ : Sort _} (h₁ : α = β) (h₂ : β = γ) (h₃ : γ = δ) (h : α = δ)
    (x : α) : Eq.mp h x = Eq.mp h₃ (Eq.mp h₂ (Eq.mp h₁ x)) := by
  subst h₁
  subst h₂
  subst h₃
  rw [eqMp_id, eqMp_id, eqMp_id]

theorem systemComponent_apply {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) (s : (emSystem (K := K) I).ι)
    (x : ((emSystem (K := K) I).obj s).carrier) :
    systemComponent (K := K) f s x =
      Eq.mp (congrArg (fun n => (pieceSucc (K := K) n).carrier)
        (Nat.succ_injective (congrArg (fun n : ℕ => n.pred + 1)
          (imageIndex_card f s)).symm)) x := by
  unfold systemComponent componentMap
  exact arityMapSucc_cast (K := K)
    (congrArg (fun n : ℕ => n.pred + 1) (imageIndex_card f s)).symm x

theorem systemComponent_trans_apply {I J P : Type u} [LinearOrder I] [LinearOrder J]
    [LinearOrder P] [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P)
    (s : (emSystem (K := K) I).ι) (x : ((emSystem (K := K) I).obj s).carrier) :
    systemComponent (K := K) (f.trans g) s x =
      Eq.mp (congrArg (fun i => ((emSystem (K := K) P).obj i).carrier)
        (systemImage_trans (K := K) f g s).symm)
        (systemComponent (K := K) g (systemImage (K := K) f s)
          (systemComponent (K := K) f s x)) := by
  have hfg := systemComponent_apply (K := K) (f.trans g) s x
  have hf := systemComponent_apply (K := K) f s x
  have hg := systemComponent_apply (K := K) g (systemImage (K := K) f s)
    (systemComponent (K := K) f s x)
  rw [hfg, hg, hf]
  exact eqMp_triple _ _ _ _ x

theorem substAt_trans {I J P : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder P]
    [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P)
    (s : (emSystem (K := K) I).ι) :
    substAt (K := K) (f.trans g) s =
      (substAt (K := K) g (systemImage (K := K) f s)).comp (systemComponent (K := K) f s) := by
  ext x
  rw [substAt, substAt, Language.Embedding.comp_apply, Language.Embedding.comp_apply,
    Language.Embedding.comp_apply, systemComponent_trans_apply]
  exact canon_transport (emLimit (K := K) P) (systemImage_trans (K := K) f g s).symm
    (systemComponent (K := K) g (systemImage (K := K) f s)
      (systemComponent (K := K) f s x))

theorem emMap_comp {I J P : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder P]
    [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P) :
    emMap (K := K) (f.trans g) = (emMap (K := K) g).comp (emMap (K := K) f) :=
  em_agreed (emMap (K := K) (f.trans g)) ((emMap (K := K) g).comp (emMap (K := K) f))
    (fun s => by
      ext x
      have hleft := congrFun (congrArg (⇑) (emMap_canon (K := K) (f.trans g) s)) x
      have htrans := congrFun (congrArg (⇑) (substAt_trans (K := K) f g s)) x
      have hf := congrFun (congrArg (⇑) (emMap_canon (K := K) f s)) x
      have hg := congrFun (congrArg (⇑) (emMap_canon (K := K) g (systemImage (K := K) f s)))
        (systemComponent (K := K) f s x)
      simp only [Language.Embedding.comp_apply] at hleft htrans hf hg ⊢
      rw [hleft, htrans, hf]
      exact hg.symm)

/-- The labels in the order presentation: a positive finite arity and an enumeration name. -/
def EMLab (K : AbstractElementaryClass.{u}) : Type u :=
  ULift {n : ℕ // 0 < n} × Enum K

def emArity (K : AbstractElementaryClass.{u}) (l : EMLab K) : ℕ :=
  l.1.down.1

theorem emArity_pos (K : AbstractElementaryClass.{u}) (l : EMLab K) : 0 < emArity K l :=
  l.1.down.2

theorem emLab_small : #(EMLab K) ≤ ls K := by
  rw [EMLab, mk_prod, lift_id, lift_id, enum_card]
  have hpos : #{n : ℕ // 0 < n} ≤ aleph0 := (mk_subtype_le _).trans_eq mk_nat
  have hlift : lift.{u, 0} #{n : ℕ // 0 < n} ≤ aleph0 := by
    rw [← lift_aleph0.{u, 0}]
    exact lift_le.mpr hpos
  have hinf : aleph0 ≤ ls K := (isLSBound_ls K).1
  calc
    lift.{u, 0} #{n : ℕ // 0 < n} * ls K ≤ aleph0 * ls K :=
      mul_le_mul' hlift (le_refl _)
    _ = max aleph0 (ls K) := mul_eq_max (le_refl _) hinf
    _ = ls K := max_eq_right hinf

/-- The finite set of indices supporting a term. -/
def termIndex {I : Type u} [LinearOrder I] [Nonempty I]
    (t : SupportTerm (EMLab K) (emArity K) I) : (emSystem (K := K) I).ι :=
  haveI : Nonempty (Fin (emArity K t.label)) := ⟨⟨0, emArity_pos K t.label⟩⟩
  ⟨Finset.univ.map ⟨t.pos, t.increasing.injective⟩,
   Finset.map_nonempty.mpr Finset.univ_nonempty⟩

theorem termIndex_card {I : Type u} [LinearOrder I] [Nonempty I]
    (t : SupportTerm (EMLab K) (emArity K) I) :
    (termIndex (K := K) t).1.card = emArity K t.label := by
  haveI : Nonempty (Fin (emArity K t.label)) := ⟨⟨0, emArity_pos K t.label⟩⟩
  simp [termIndex, Finset.card_map]

/-- The element of the small model named by the term's label. -/
noncomputable def termElem {I : Type u} [LinearOrder I] [Nonempty I]
    (t : SupportTerm (EMLab K) (emArity K) I) :
    ((emSystem (K := K) I).obj (termIndex (K := K) t)).carrier :=
  (pieceEnum ((termIndex (K := K) t).1.card.pred + 1)
    (Nat.succ_pos (termIndex (K := K) t).1.card.pred)).enum t.label.2

/-- The realization of a support term in the direct limit. -/
noncomputable def emRealize {I : Type u} [LinearOrder I] [Nonempty I]
    (t : SupportTerm (EMLab K) (emArity K) I) : (emLimit (K := K) I).obj.carrier :=
  (emLimit (K := K) I).canon (termIndex (K := K) t) (termElem (K := K) t)

lemma canon_congr {τ : Tau.{u}} {S : DirectedSystem τ} (L : DirectLimit S)
    {i j : S.ι} (h : i = j) (x : (S.obj i).carrier) (y : (S.obj j).carrier)
    (hxy : HEq x y) : L.canon i x = L.canon j y := by
  subst h
  have : x = y := eq_of_heq hxy
  subst this
  rfl

lemma pieceEnum_enum_heq (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hnm : n = m) (η : Enum K) :
    HEq ((pieceEnum (K := K) n hn).enum η) ((pieceEnum (K := K) m hm).enum η) := by
  subst hnm
  have : hn = hm := Subsingleton.elim hn hm
  subst this
  rfl

theorem emRealize_surjective {I : Type u} [LinearOrder I] [Nonempty I] :
    Function.Surjective (emRealize (K := K) (I := I)) := by
  intro x
  obtain ⟨s, y, rfl⟩ := (emLimit (K := K) I).joint x
  set k := s.1.card.pred
  have hpos : 0 < k + 1 := Nat.succ_pos k
  obtain ⟨η, hη⟩ := (pieceEnum (k + 1) hpos).surj y
  have hcard : k + 1 = s.1.card := (Nat.succ_pred (Finset.card_pos.mpr s.2).ne')
  let pos : Fin (k + 1) → I := fun i => s.1.orderEmbOfFin rfl (Fin.cast hcard i)
  have hmono : StrictMono pos := fun a b hab =>
    (s.1.orderEmbOfFin rfl).strictMono ((Fin.castOrderIso hcard).strictMono hab)
  let lab : EMLab K := ⟨ULift.up ⟨k + 1, hpos⟩, η⟩
  let t : SupportTerm (EMLab K) (emArity K) I := ⟨lab, pos, hmono⟩
  have hrange : Finset.univ.map ⟨pos, hmono.injective⟩ = s.1 := by
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, pos]
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.orderEmbOfFin_mem s.1 rfl _
    · intro ha
      obtain ⟨j, hj⟩ := (s.1.orderIsoOfFin rfl).surjective ⟨a, ha⟩
      refine ⟨(Fin.castOrderIso hcard).symm j, ?_⟩
      have hcast_id : Fin.cast hcard ((Fin.castOrderIso hcard).symm j) = j :=
        OrderIso.apply_symm_apply (Fin.castOrderIso hcard) j
      exact hcast_id.symm ▸ congrArg Subtype.val hj
  have hidx : termIndex (K := K) t = s := Subtype.ext hrange
  refine ⟨t, ?_⟩
  unfold emRealize
  have helem : HEq (termElem (K := K) t) y := by
    rw [← hη]
    unfold termElem
    have hpred : (termIndex (K := K) t).1.card.pred = k := congrArg (fun u : (emSystem (K := K) I).ι => u.1.card.pred) hidx
    exact pieceEnum_enum_heq _ _ _ hpos (congrArg (· + 1) hpred) η
  exact canon_congr (emLimit (K := K) I) hidx (termElem (K := K) t) y helem

/-- The finite-support model associated with a subset of the linear order. -/
noncomputable def emSub {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I) : Model K.τ :=
  if hs : s.Nonempty then (emSystem (K := K) I).obj ⟨s, hs⟩ else pieceSucc (K := K) 0

theorem emSub_eq {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I) (hs : s.Nonempty) :
    emSub (K := K) s = (emSystem (K := K) I).obj ⟨s, hs⟩ :=
  dif_pos hs

/-- Inclusion of the small finite-support model into the limit. -/
noncomputable def emSubIncl {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I)
    (hs : s.Nonempty) : Language.Embedding K.τ (emSub (K := K) s).carrier (emLimit (K := K) I).obj.carrier :=
  ((emLimit (K := K) I).canon ⟨s, hs⟩).comp (embeddingOfEq (emSub_eq s hs))

theorem pieceModel_card (n : ℕ) (hn : 0 < n) : Model.card (pieceModel (K := K) n hn) ≤ ls K :=
  subModel_card (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (fullSet n hn)

theorem pieceSucc_card (k : ℕ) : Model.card (pieceSucc (K := K) k) ≤ ls K :=
  pieceModel_card (k + 1) (Nat.succ_pos k)

theorem emSubStrong {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I)
    (hs : s.Nonempty) : K.Strong (emSubIncl (K := K) s hs) := by
  have hmem : K.Mem (emSub (K := K) s) := by
    rw [emSub_eq s hs]
    exact emSystem_mem (K := K) ⟨s, hs⟩
  have hequiv : K.Strong (embeddingOfEq (emSub_eq s hs)) :=
    strong_of_equiv K (equivOfEq (emSub_eq s hs)) hmem
  exact K.strong_trans (embeddingOfEq (emSub_eq s hs)) ((emLimit (K := K) I).canon ⟨s, hs⟩)
    hequiv ((emLimit_spec (K := K) I).2.1 ⟨s, hs⟩)

theorem emSubCard {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I)
    (hs : s.Nonempty) : Model.card (emSub (K := K) s) ≤ ls K := by
  rw [emSub_eq s hs]
  exact pieceSucc_card s.card.pred

lemma embeddingOfEq_cancel {τ : Tau.{u}} {M N : Model τ} (h : M = N) (y : N.carrier) :
    embeddingOfEq h (embeddingOfEq h.symm y) = y := by
  subst h
  rfl

theorem emSubMono {I : Type u} [LinearOrder I] [Nonempty I] (s t : Finset I)
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) :
    ∃ g : Language.Embedding K.τ (emSub (K := K) s).carrier (emSub (K := K) t).carrier,
      K.Strong g ∧ (emSubIncl (K := K) t ht).comp g = emSubIncl (K := K) s hs := by
  have hrel : (emSystem (K := K) I).rel ⟨s, hs⟩ ⟨t, ht⟩ := hst
  let g := (embeddingOfEq (emSub_eq t ht).symm).comp
    (((emSystem (K := K) I).map hrel).comp (embeddingOfEq (emSub_eq s hs)))
  have hmem_s_obj : K.Mem ((emSystem (K := K) I).obj ⟨s, hs⟩) :=
    emSystem_mem (K := K) ⟨s, hs⟩
  have hmem_s : K.Mem (emSub (K := K) s) := by
    rw [emSub_eq s hs]; exact hmem_s_obj
  have hequiv_s : K.Strong (embeddingOfEq (emSub_eq s hs)) :=
    strong_of_equiv K (equivOfEq (emSub_eq s hs)) hmem_s
  have hmap : K.Strong ((emSystem (K := K) I).map hrel) :=
    emSystem_strong (K := K) (I := I) hrel
  have hmem_t_obj : K.Mem ((emSystem (K := K) I).obj ⟨t, ht⟩) :=
    emSystem_mem (K := K) ⟨t, ht⟩
  have hequiv_t : K.Strong (embeddingOfEq (emSub_eq t ht).symm) :=
    strong_of_equiv K (equivOfEq (emSub_eq t ht).symm) hmem_t_obj
  have hg : K.Strong g :=
    K.strong_trans _ _ (K.strong_trans _ _ hequiv_s hmap) hequiv_t
  refine ⟨g, hg, ?_⟩
  ext x
  have hcancel := embeddingOfEq_cancel (emSub_eq t ht)
    (((emSystem (K := K) I).map hrel) (embeddingOfEq (emSub_eq s hs) x))
  have hcan := congrFun (congrArg (⇑) ((emLimit (K := K) I).compat hrel))
    (embeddingOfEq (emSub_eq s hs) x)
  simp only [g, emSubIncl, Language.Embedding.comp_apply]
  rw [hcancel]
  exact hcan

theorem emSubCover {I : Type u} [LinearOrder I] [Nonempty I]
    (x : (emLimit (K := K) I).obj.carrier) :
    ∃ s : Finset I, ∃ hs : s.Nonempty, ∃ y : (emSub (K := K) s).carrier,
      emSubIncl (K := K) s hs y = x := by
  obtain ⟨⟨s, hs⟩, y, rfl⟩ := (emLimit (K := K) I).joint x
  refine ⟨s, hs, embeddingOfEq (emSub_eq s hs).symm y, ?_⟩
  unfold emSubIncl
  rw [Language.Embedding.comp_apply, embeddingOfEq_cancel (emSub_eq s hs) y]

/-- An order embedding transports a support term by substituting indices. -/
def mapTerm {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    (t : SupportTerm (EMLab K) (emArity K) I) :
    SupportTerm (EMLab K) (emArity K) J where
  label := t.label
  pos := f ∘ t.pos
  increasing := f.strictMono.comp t.increasing

theorem termIndex_mapTerm {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (t : SupportTerm (EMLab K) (emArity K) I) :
    termIndex (K := K) (mapTerm f t) = systemImage (K := K) f (termIndex (K := K) t) := by
  apply Subtype.ext
  simp only [termIndex, mapTerm, systemImage, Finset.map_map]
  rfl

lemma eqMp_heq {α β : Sort _} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
  subst h
  rfl

theorem emRealize_mapTerm {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (t : SupportTerm (EMLab K) (emArity K) I) :
    emMap (K := K) f (emRealize (K := K) t) = emRealize (K := K) (mapTerm f t) := by
  have hcanon := congrFun (congrArg (⇑) (emMap_canon (K := K) f (termIndex (K := K) t)))
    (termElem (K := K) t)
  simp only [Language.Embedding.comp_apply] at hcanon
  rw [emRealize, hcanon, substAt, Language.Embedding.comp_apply, emRealize]
  have hidx : systemImage (K := K) f (termIndex (K := K) t) = termIndex (K := K) (mapTerm f t) :=
    (termIndex_mapTerm f t).symm
  have helem : HEq (systemComponent (K := K) f (termIndex (K := K) t) (termElem (K := K) t))
      (termElem (K := K) (mapTerm f t)) := by
    rw [systemComponent_apply]
    have hcast : (termIndex (K := K) t).1.card.pred =
        (termIndex (K := K) (mapTerm f t)).1.card.pred := by
      rw [termIndex_mapTerm]
      simp [systemImage, Finset.card_map]
    have h1 : HEq (Eq.mp (congrArg (fun n => (pieceSucc (K := K) n).carrier)
        (Nat.succ_injective (congrArg (fun n : ℕ => n.pred + 1)
          (imageIndex_card f (termIndex (K := K) t))).symm)) (termElem (K := K) t))
        (termElem (K := K) t) := eqMp_heq _ _
    have h2 : HEq (termElem (K := K) t) (termElem (K := K) (mapTerm f t)) := by
      dsimp [termElem, mapTerm]
      exact pieceEnum_enum_heq (K := K) _ _ (Nat.succ_pos _) (Nat.succ_pos _)
        (congrArg (· + 1) hcast) t.label.2
    exact h1.trans h2
  exact canon_congr (emLimit (K := K) J) hidx _ _ helem

/-- The distinguished element on a singleton order. -/
noncomputable def emSkeletonElem :
    (pieceSucc (K := K) 0).carrier :=
  (pieceEnum (K := K) 1 (Nat.succ_pos 0)).enum (slot K 1 ⟨0, Nat.succ_pos 0⟩)

noncomputable def emSkeletonFun
    {I : Type u} [LinearOrder I] [Nonempty I] (i : I) :
    (emLimit (K := K) I).obj.carrier :=
  (emLimit (K := K) I).canon ⟨{i}, Finset.singleton_nonempty i⟩ emSkeletonElem

/-- The singleton support term. -/
noncomputable def skeletonTerm {I : Type u} [LinearOrder I] (i : I) :
    SupportTerm (EMLab K) (emArity K) I where
  label := ⟨ULift.up ⟨1, Nat.succ_pos 0⟩, slot K 1 ⟨0, Nat.succ_pos 0⟩⟩
  pos := fun _ => i
  increasing := fun a b hab => by
    have ha : a.1 < 1 := a.2
    have hb : b.1 < 1 := b.2
    have h : a.1 < b.1 := hab
    omega

theorem termIndex_skeletonTerm {I : Type u} [LinearOrder I] [Nonempty I] (i : I) :
    termIndex (K := K) (skeletonTerm i) = ⟨{i}, Finset.singleton_nonempty i⟩ := by
  apply Subtype.ext
  ext a
  simp only [termIndex, skeletonTerm, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Finset.mem_singleton]
  constructor
  · rintro ⟨j, -, rfl⟩
    rfl
  · rintro rfl
    exact ⟨⟨0, Nat.succ_pos 0⟩, Finset.mem_univ _, rfl⟩

theorem emRealize_skeletonTerm {I : Type u} [LinearOrder I] [Nonempty I] (i : I) :
    emRealize (K := K) (skeletonTerm i) = emSkeletonFun i := by
  unfold emRealize emSkeletonFun
  have hidx : termIndex (K := K) (skeletonTerm i) = ⟨{i}, Finset.singleton_nonempty i⟩ :=
    termIndex_skeletonTerm i
  have helem : HEq (termElem (K := K) (skeletonTerm i)) (emSkeletonElem (K := K)) := by
    dsimp [termElem, emSkeletonElem, skeletonTerm]
    have hcast : (termIndex (K := K) (skeletonTerm i)).1.card.pred = 0 := by
      rw [hidx]
      rfl
    exact pieceEnum_enum_heq (K := K) _ _ _ (Nat.succ_pos _) (congrArg (· + 1) hcast) _
  exact canon_congr (emLimit (K := K) I) hidx _ _ helem

theorem emSkeleton_natural {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (i : I) :
    emMap (K := K) f (emSkeletonFun (K := K) i) = emSkeletonFun (K := K) (f i) := by
  have hmap : mapTerm (K := K) f (skeletonTerm i) = skeletonTerm (f i) := by
    apply SupportTerm.ext_of_label_eq (h := rfl)
    intro a; rfl
  have h0 : emSkeletonFun (K := K) i = emRealize (K := K) (skeletonTerm i) :=
    (emRealize_skeletonTerm (I := I) i).symm
  have h1 : emMap (K := K) f (emRealize (K := K) (skeletonTerm i)) =
      emRealize (K := K) (mapTerm (K := K) f (skeletonTerm i)) :=
    emRealize_mapTerm f (skeletonTerm i)
  have h2 : emRealize (K := K) (mapTerm (K := K) f (skeletonTerm i)) =
      emRealize (K := K) (skeletonTerm (f i)) :=
    congrArg (emRealize (K := K)) hmap
  have h3 : emRealize (K := K) (skeletonTerm (f i)) = emSkeletonFun (K := K) (f i) :=
    emRealize_skeletonTerm (I := J) (f i)
  exact (congrArg (emMap (K := K) f) h0).trans (h1.trans (h2.trans h3))

/-- The unique order embedding sending `0 ↦ i` and `1 ↦ j` when `i < j`. -/
def embFin2 {I : Type u} [LinearOrder I] (i j : I) (hij : i < j) : ULift.{u, 0} (Fin 2) ↪o I :=
  OrderEmbedding.ofStrictMono
    (fun x => if x.down = 0 then i else j)
    (by
      intro a b hab
      have ha2 := a.down.2
      have hb2 := b.down.2
      have hlt : a.down.1 < b.down.1 := hab
      have ha_val : a.down.1 = 0 := by omega
      have hb_val : b.down.1 = 1 := by omega
      have ha : a.down = 0 := Fin.ext ha_val
      have hb : b.down = 1 := Fin.ext hb_val
      have ha' : a = ULift.up (0 : Fin 2) := by cases a; congr
      have hb' : b = ULift.up (1 : Fin 2) := by cases b; congr
      subst ha'; subst hb'
      change i < j
      exact hij)

theorem embFin2_zero {I : Type u} [LinearOrder I] (i j : I) (hij : i < j) :
    embFin2 i j hij (ULift.up 0) = i := rfl

theorem embFin2_one {I : Type u} [LinearOrder I] (i j : I) (hij : i < j) :
    embFin2 i j hij (ULift.up 1) = j := rfl

lemma orderEmbOfFin_univ {m : ℕ} (i : Fin m) :
    (Finset.univ : Finset (Fin m)).orderEmbOfFin (by simp) i = i := by
  have h := Finset.orderEmbOfFin_unique (s := (Finset.univ : Finset (Fin m)))
    (by simp) (fun _ => Finset.mem_univ _) strictMono_id
  exact congrFun h.symm i

lemma subIncl_subsetEnum_slot0 {n : ℕ} (hn : 0 < n) {m : ℕ} (hm : 0 < m) (e : Fin m ↪o Fin n) :
    subIncl (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)
      ((subsetEnum (K := K) hm hn e).enum (slot K m ⟨0, hm⟩)) =
    (colorWitness (K := K) n hn).base (e ⟨0, hm⟩) := by
  unfold subsetEnum subsetEnumerated
  dsimp only
  have hc : (rangeSet hm e).1.card = m := by
    simp [rangeSet, mapped, fullSet, Finset.card_map]
  haveI : Nonempty (subModel (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)).carrier :=
    subModel_nonempty _ _ _
  have hslot : enumOf (subModel_card (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e))
      (subsetPreimage (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e))
      (subsetPreimage_injective (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (colorWitness (K := K) n hn).inj _)
      (slot K m ⟨0, hm⟩) =
    subsetPreimage (colorWitness (K := K) n hn).mem (colorWitness (K := K) n hn).base (rangeSet hm e)
      ⟨0, by rw [hc]; exact hm⟩ :=
    enumOf_slot _ _ _ ⟨0, by rw [hc]; exact hm⟩
  rw [hslot, subsetPreimage_spec]
  have hpos_full : 0 < (fullSet m hm).1.card := Finset.card_pos.mpr (fullSet m hm).2
  have hmap := orderEmbOfFin_mapped e (fullSet m hm).1 (fullSet m hm).2 ⟨0, hpos_full⟩
  have hcast := orderEmbOfFin_cast ((fullSet m hm).1.map e.toEmbedding)
    (Finset.card_map e.toEmbedding) ⟨0, hpos_full⟩
  have huniv := orderEmbOfFin_univ (m := m) ⟨0, hm⟩
  have hidx :
      ((rangeSet hm e).1.orderEmbOfFin rfl)
          (Fin.cast (Finset.card_map e.toEmbedding).symm ⟨0, hpos_full⟩) =
        (((fullSet m hm).1.map e.toEmbedding).orderEmbOfFin rfl)
          (Fin.cast (Finset.card_map e.toEmbedding).symm ⟨0, hpos_full⟩) := rfl
  have hpos : ((rangeSet hm e).1.orderEmbOfFin rfl ⟨0, by rw [hc]; exact hm⟩) = e ⟨0, hm⟩ := by
    have h0_eq : (⟨0, by rw [hc]; exact hm⟩ : Fin (rangeSet hm e).1.card) =
        Fin.cast (Finset.card_map e.toEmbedding).symm ⟨0, hpos_full⟩ := by
      ext; rfl
    have hstep0 := congrArg ((rangeSet hm e).1.orderEmbOfFin rfl) h0_eq
    have hstep1 := hidx
    have hstep2 := hcast
    have hstep3 := hmap
    have hstep4 : e ((fullSet m hm).1.orderEmbOfFin rfl ⟨0, hpos_full⟩) = e ⟨0, hm⟩ :=
      congrArg e huniv
    exact hstep0.trans (hstep1.trans (hstep2.trans (hstep3.trans hstep4)))
  rw [hpos]

theorem emSkeletonFun_fin2_distinct (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K] :
    emSkeletonFun (K := K) (I := ULift.{u, 0} (Fin 2)) (ULift.up 0) ≠
    emSkeletonFun (K := K) (I := ULift.{u, 0} (Fin 2)) (ULift.up 1) := by
  intro h
  let u : (emSystem (K := K) (ULift.{u, 0} (Fin 2))).ι := ⟨Finset.univ, Finset.univ_nonempty⟩
  have hu0 : (emSystem (K := K) (ULift.{u, 0} (Fin 2))).rel ⟨{ULift.up 0}, Finset.singleton_nonempty _⟩ u := Finset.subset_univ _
  have hu1 : (emSystem (K := K) (ULift.{u, 0} (Fin 2))).rel ⟨{ULift.up 1}, Finset.singleton_nonempty _⟩ u := Finset.subset_univ _
  have hcan0 := congrFun (congrArg (⇑) ((emLimit (K := K) (ULift.{u, 0} (Fin 2))).compat hu0)) (emSkeletonElem (K := K))
  have hcan1 := congrFun (congrArg (⇑) ((emLimit (K := K) (ULift.{u, 0} (Fin 2))).compat hu1)) (emSkeletonElem (K := K))
  have h_eq : (emSystem (K := K) (ULift.{u, 0} (Fin 2))).map hu0 (emSkeletonElem (K := K)) =
      (emSystem (K := K) (ULift.{u, 0} (Fin 2))).map hu1 (emSkeletonElem (K := K)) := by
    apply (emLimit (K := K) (ULift.{u, 0} (Fin 2))).canon u |>.injective
    have hcan0' : (emLimit (K := K) (ULift.{u, 0} (Fin 2))).canon u ((emSystem (K := K) (ULift.{u, 0} (Fin 2))).map hu0 (emSkeletonElem (K := K))) =
        emSkeletonFun (ULift.up 0) := hcan0
    have hcan1' : (emLimit (K := K) (ULift.{u, 0} (Fin 2))).canon u ((emSystem (K := K) (ULift.{u, 0} (Fin 2))).map hu1 (emSkeletonElem (K := K))) =
        emSkeletonFun (ULift.up 1) := hcan1
    rw [hcan0', hcan1']
    exact h
  have h0_incl := arityMap_enum_incl (Nat.succ_pos 0) (Nat.succ_pos 1)
    (placeSucc hu0 (Finset.singleton_nonempty _) Finset.univ_nonempty)
    (slot K 1 ⟨0, Nat.succ_pos 0⟩)
  have h1_incl := arityMap_enum_incl (Nat.succ_pos 0) (Nat.succ_pos 1)
    (placeSucc hu1 (Finset.singleton_nonempty _) Finset.univ_nonempty)
    (slot K 1 ⟨0, Nat.succ_pos 0⟩)
  have hboth := h0_incl.symm.trans
    ((congrArg (subIncl (colorWitness (K := K) 2 (Nat.succ_pos 1)).mem (colorWitness (K := K) 2 (Nat.succ_pos 1)).base (fullSet 2 (Nat.succ_pos 1))) h_eq).trans h1_incl)
  rw [subIncl_subsetEnum_slot0 (Nat.succ_pos 1) (Nat.succ_pos 0) (placeSucc hu0 (Finset.singleton_nonempty _) Finset.univ_nonempty),
      subIncl_subsetEnum_slot0 (Nat.succ_pos 1) (Nat.succ_pos 0) (placeSucc hu1 (Finset.singleton_nonempty _) Finset.univ_nonempty)] at hboth
  have hbase_eq := (colorWitness (K := K) 2 (Nat.succ_pos 1)).inj hboth
  have hspec0 := placeEmb_spec hu0 ⟨0, Nat.succ_pos 0⟩
  have hspec1 := placeEmb_spec hu1 ⟨0, Nat.succ_pos 0⟩
  have h_val0 : ({ULift.up (0 : Fin 2)} : Finset (ULift (Fin 2))).orderEmbOfFin rfl ⟨0, Nat.succ_pos 0⟩ = ULift.up 0 :=
    Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ rfl _)
  have h_val1 : ({ULift.up (1 : Fin 2)} : Finset (ULift (Fin 2))).orderEmbOfFin rfl ⟨0, Nat.succ_pos 0⟩ = ULift.up 1 :=
    Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ rfl _)
  have h0_eq : (Finset.univ : Finset (ULift (Fin 2))).orderEmbOfFin rfl
      (placeEmb hu0 ⟨0, Nat.succ_pos 0⟩) = ULift.up 0 := by
    rw [hspec0, h_val0]
  have h1_eq : (Finset.univ : Finset (ULift (Fin 2))).orderEmbOfFin rfl
      (placeEmb hu1 ⟨0, Nat.succ_pos 0⟩) = ULift.up 1 := by
    rw [hspec1, h_val1]
  have hplace_eq : placeEmb hu0 ⟨0, Nat.succ_pos 0⟩ = placeEmb hu1 ⟨0, Nat.succ_pos 0⟩ := by
    have hcast_eq : (placeSucc hu0 (Finset.singleton_nonempty _) Finset.univ_nonempty) ⟨0, Nat.succ_pos 0⟩ =
        (placeSucc hu1 (Finset.singleton_nonempty _) Finset.univ_nonempty) ⟨0, Nat.succ_pos 0⟩ := hbase_eq
    unfold placeSucc at hcast_eq
    dsimp only [RelEmbedding.trans_apply, OrderIso.coe_toOrderEmbedding] at hcast_eq
    have h_inj := (Fin.castOrderIso (Nat.succ_pred (Finset.card_pos.mpr (Finset.univ_nonempty (α := ULift (Fin 2)))).ne')).symm.injective hcast_eq
    exact h_inj
  have h_contra : (ULift.up (0 : Fin 2)) = (ULift.up (1 : Fin 2)) := by
    rw [← h0_eq, ← h1_eq, hplace_eq]
  have h01 : (0 : Fin 2) = (1 : Fin 2) := by
    injection h_contra
  have h01_nat : (0 : ℕ) = 1 := congrArg Fin.val h01
  exact Nat.zero_ne_one h01_nat

theorem emSkeletonFun_injective (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K]
    {I : Type u} [LinearOrder I] [Nonempty I] :
    Function.Injective (emSkeletonFun (K := K) (I := I)) := by
  intro i j hij
  by_contra hne
  obtain (hlt | hgt) := lt_or_gt_of_ne hne
  · have hnat := emSkeleton_natural (K := K) (embFin2 i j hlt)
    have h0 : embFin2 i j hlt (ULift.up 0) = i := embFin2_zero i j hlt
    have h1 : embFin2 i j hlt (ULift.up 1) = j := embFin2_one i j hlt
    have h_eq : emMap (K := K) (embFin2 i j hlt) (emSkeletonFun (ULift.up 0)) =
        emMap (K := K) (embFin2 i j hlt) (emSkeletonFun (ULift.up 1)) := by
      rw [hnat (ULift.up 0), hnat (ULift.up 1), h0, h1, hij]
    have h_dis := (emMap (K := K) (embFin2 i j hlt)).injective h_eq
    exact emSkeletonFun_fin2_distinct K h_dis
  · have hnat := emSkeleton_natural (K := K) (embFin2 j i hgt)
    have h0 : embFin2 j i hgt (ULift.up 0) = j := embFin2_zero j i hgt
    have h1 : embFin2 j i hgt (ULift.up 1) = i := embFin2_one j i hgt
    have h_eq : emMap (K := K) (embFin2 j i hgt) (emSkeletonFun (ULift.up 0)) =
        emMap (K := K) (embFin2 j i hgt) (emSkeletonFun (ULift.up 1)) := by
      rw [hnat (ULift.up 0), hnat (ULift.up 1), h0, h1, hij]
    have h_dis := (emMap (K := K) (embFin2 j i hgt)).injective h_eq
    exact emSkeletonFun_fin2_distinct K h_dis

noncomputable def emSkeleton (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K]
    {I : Type u} [LinearOrder I] [Nonempty I] : I ↪ (emLimit (K := K) I).obj.carrier where
  toFun := emSkeletonFun
  inj' := emSkeletonFun_injective K

theorem emCardLower {I : Type u} [LinearOrder I] [Nonempty I] :
    #I ≤ Model.card (emLimit (K := K) I).obj :=
  Cardinal.mk_le_of_injective (emSkeletonFun_injective K)

/-- Injecting support terms into pairs of a label and a finite support set. -/
def supportTermToProd {I : Type u} [LinearOrder I]
    (t : SupportTerm (EMLab K) (emArity K) I) : EMLab K × Finset I :=
  (t.label, Finset.univ.map ⟨t.pos, t.increasing.injective⟩)

theorem supportTermToProd_injective {I : Type u} [LinearOrder I] :
    Function.Injective (supportTermToProd (K := K) (I := I)) := by
  rintro ⟨l₁, p₁, m₁⟩ ⟨l₂, p₂, m₂⟩ h
  simp only [supportTermToProd, Prod.mk.injEq] at h
  obtain ⟨rfl, hset⟩ := h
  have hp : p₁ = p₂ := by
    have hs : Finset.card (Finset.map (⟨p₁, m₁.injective⟩ : Fin (emArity K l₁) ↪ I) Finset.univ) = emArity K l₁ := by simp
    have h1 : p₁ = ⇑((Finset.map ⟨p₁, m₁.injective⟩ Finset.univ).orderEmbOfFin hs) :=
      Finset.orderEmbOfFin_unique hs (fun j => Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩) m₁
    have h2 : p₂ = ⇑((Finset.map ⟨p₂, m₂.injective⟩ Finset.univ).orderEmbOfFin (hset ▸ hs)) :=
      Finset.orderEmbOfFin_unique (hset ▸ hs) (fun j => Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩) m₂
    rw [h1, h2]
    congr
  have : (⟨l₁, p₁, m₁⟩ : SupportTerm (EMLab K) (emArity K) I) = ⟨l₁, p₂, m₂⟩ := by
    subst hp; rfl
  exact this

/-- The upper bound on the cardinality of the model. -/
theorem emCardUpper {I : Type u} [LinearOrder I] [Nonempty I] :
    Model.card (emLimit (K := K) I).obj ≤ #I + ls K := by
  have h_surj : Model.card (emLimit (K := K) I).obj ≤ #(SupportTerm (EMLab K) (emArity K) I) :=
    Cardinal.mk_le_of_surjective emRealize_surjective
  have h_inj : #(SupportTerm (EMLab K) (emArity K) I) ≤ #(EMLab K × Finset I) :=
    Cardinal.mk_le_of_injective supportTermToProd_injective
  have h_prod : #(EMLab K × Finset I) = #(EMLab K) * #(Finset I) := by
    rw [mk_prod, lift_id, lift_id]
  have h_lab := emLab_small (K := K)
  have h_ls : aleph0 ≤ ls K := (isLSBound_ls K).1
  by_cases hI : Infinite I
  · have h_fin : #(Finset I) = #I := mk_finset_of_infinite I
    have h_I_inf : aleph0 ≤ #I := Cardinal.aleph0_le_mk I
    have h_mul : ls K * #I = max (ls K) #I := mul_eq_max h_ls h_I_inf
    calc
      Model.card (emLimit (K := K) I).obj ≤ #(EMLab K × Finset I) := h_surj.trans h_inj
      _ = #(EMLab K) * #(Finset I) := h_prod
      _ ≤ ls K * #I := mul_le_mul' h_lab (le_of_eq h_fin)
      _ = max (ls K) #I := h_mul
      _ = max #I (ls K) := max_comm _ _
      _ ≤ #I + ls K := max_le le_self_add le_add_self
  · have h_fin : ¬ Infinite I := hI
    haveI : Finite I := not_infinite_iff_finite.mp h_fin
    haveI : Fintype I := Fintype.ofFinite I
    have h_finset : #(Finset I) < aleph0 := Cardinal.lt_aleph0_of_finite (Finset I)
    have h_finset_le : #(Finset I) ≤ aleph0 := le_of_lt h_finset
    have h_mul : ls K * aleph0 = max (ls K) aleph0 := mul_eq_max h_ls (le_refl _)
    calc
      Model.card (emLimit (K := K) I).obj ≤ #(EMLab K × Finset I) := h_surj.trans h_inj
      _ = #(EMLab K) * #(Finset I) := h_prod
      _ ≤ ls K * aleph0 := mul_le_mul' h_lab h_finset_le
      _ = max (ls K) aleph0 := h_mul
      _ = ls K := max_eq_left h_ls
      _ ≤ #I + ls K := le_add_self

theorem pattern_equiv_of_embeddings {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f_t : J ↪o I) (f_s : J ↪o I) {n : ℕ}
    (u : Fin n → SupportTerm (EMLab K) (emArity K) J)
    (t s : Fin n → SupportTerm (EMLab K) (emArity K) I)
    (ht : ∀ i, mapTerm f_t (u i) = t i)
    (hs : ∀ i, mapTerm f_s (u i) = s i) :
    (∀ i j, emRealize (K := K) (t i) = emRealize (K := K) (t j) ↔
            emRealize (K := K) (s i) = emRealize (K := K) (s j)) ∧
    (∀ {k} (f : K.τ.Functions k) (idx : Fin k → Fin n) (j : Fin n),
      Language.Structure.funMap f (fun a => emRealize (K := K) (t (idx a))) = emRealize (K := K) (t j) ↔
        Language.Structure.funMap f (fun a => emRealize (K := K) (s (idx a))) = emRealize (K := K) (s j)) ∧
    (∀ {k₁ k₂ : ℕ} (f₁ : K.τ.Functions k₁) (f₂ : K.τ.Functions k₂)
      (idx₁ : Fin k₁ → Fin n) (idx₂ : Fin k₂ → Fin n),
      Language.Structure.funMap f₁ (fun a => emRealize (K := K) (t (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => emRealize (K := K) (t (idx₂ a))) ↔
        Language.Structure.funMap f₁ (fun a => emRealize (K := K) (s (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => emRealize (K := K) (s (idx₂ a)))) ∧
    (∀ {k} (r : K.τ.Relations k) (idx : Fin k → Fin n),
      Language.Structure.RelMap r (fun a => emRealize (K := K) (t (idx a))) ↔
        Language.Structure.RelMap r (fun a => emRealize (K := K) (s (idx a)))) := by
  have ht_eval : ∀ i, emRealize (K := K) (t i) = emMap (K := K) f_t (emRealize (K := K) (u i)) := by
    intro i; rw [← ht i, emRealize_mapTerm]
  have hs_eval : ∀ i, emRealize (K := K) (s i) = emMap (K := K) f_s (emRealize (K := K) (u i)) := by
    intro i; rw [← hs i, emRealize_mapTerm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    rw [ht_eval i, ht_eval j, hs_eval i, hs_eval j]
    rw [(emMap (K := K) f_t).injective.eq_iff, (emMap (K := K) f_s).injective.eq_iff]
  · intro k f idx j
    have ht_fun : (fun a => emRealize (K := K) (t (idx a))) =
        (⇑(emMap (K := K) f_t)) ∘ (fun a => emRealize (K := K) (u (idx a))) := funext (fun a => ht_eval (idx a))
    have hs_fun : (fun a => emRealize (K := K) (s (idx a))) =
        (⇑(emMap (K := K) f_s)) ∘ (fun a => emRealize (K := K) (u (idx a))) := funext (fun a => hs_eval (idx a))
    rw [ht_eval j, hs_eval j, ht_fun, hs_fun]
    rw [← (emMap (K := K) f_t).map_fun, ← (emMap (K := K) f_s).map_fun]
    rw [(emMap (K := K) f_t).injective.eq_iff, (emMap (K := K) f_s).injective.eq_iff]
  · intro k₁ k₂ f₁ f₂ idx₁ idx₂
    have ht_fun₁ : (fun a => emRealize (K := K) (t (idx₁ a))) =
        (⇑(emMap (K := K) f_t)) ∘ (fun a => emRealize (K := K) (u (idx₁ a))) := funext (fun a => ht_eval (idx₁ a))
    have ht_fun₂ : (fun a => emRealize (K := K) (t (idx₂ a))) =
        (⇑(emMap (K := K) f_t)) ∘ (fun a => emRealize (K := K) (u (idx₂ a))) := funext (fun a => ht_eval (idx₂ a))
    have hs_fun₁ : (fun a => emRealize (K := K) (s (idx₁ a))) =
        (⇑(emMap (K := K) f_s)) ∘ (fun a => emRealize (K := K) (u (idx₁ a))) := funext (fun a => hs_eval (idx₁ a))
    have hs_fun₂ : (fun a => emRealize (K := K) (s (idx₂ a))) =
        (⇑(emMap (K := K) f_s)) ∘ (fun a => emRealize (K := K) (u (idx₂ a))) := funext (fun a => hs_eval (idx₂ a))
    rw [ht_fun₁, ht_fun₂, hs_fun₁, hs_fun₂]
    rw [← (emMap (K := K) f_t).map_fun, ← (emMap (K := K) f_t).map_fun,
        ← (emMap (K := K) f_s).map_fun, ← (emMap (K := K) f_s).map_fun]
    rw [(emMap (K := K) f_t).injective.eq_iff, (emMap (K := K) f_s).injective.eq_iff]
  · intro k r idx
    have ht_fun : (fun a => emRealize (K := K) (t (idx a))) =
        (⇑(emMap (K := K) f_t)) ∘ (fun a => emRealize (K := K) (u (idx a))) := funext (fun a => ht_eval (idx a))
    have hs_fun : (fun a => emRealize (K := K) (s (idx a))) =
        (⇑(emMap (K := K) f_s)) ∘ (fun a => emRealize (K := K) (u (idx a))) := funext (fun a => hs_eval (idx a))
    rw [ht_fun, hs_fun]
    rw [(emMap (K := K) f_t).map_rel, (emMap (K := K) f_s).map_rel]

/-- Equality, function values, and relations on realized terms are determined by the order pattern. -/
theorem emPatternDetermines {I : Type u} [LinearOrder I] [Nonempty I] {n : ℕ}
    (t s : Fin n → SupportTerm (EMLab K) (emArity K) I)
    (hlabel : ∀ i, (t i).label = (s i).label)
    (heq : ∀ i j (a : Fin (emArity K (t i).label)) (b : Fin (emArity K (t j).label)),
      (t i).pos a = (t j).pos b ↔
        (s i).pos (Fin.cast (congrArg (emArity K) (hlabel i)) a) =
          (s j).pos (Fin.cast (congrArg (emArity K) (hlabel j)) b))
    (hlt : ∀ i j (a : Fin (emArity K (t i).label)) (b : Fin (emArity K (t j).label)),
      (t i).pos a < (t j).pos b ↔
        (s i).pos (Fin.cast (congrArg (emArity K) (hlabel i)) a) <
          (s j).pos (Fin.cast (congrArg (emArity K) (hlabel j)) b)) :
    (∀ i j, emRealize (K := K) (t i) = emRealize (K := K) (t j) ↔
            emRealize (K := K) (s i) = emRealize (K := K) (s j)) ∧
    (∀ {k} (f : K.τ.Functions k) (idx : Fin k → Fin n) (j : Fin n),
      Language.Structure.funMap f (fun a => emRealize (K := K) (t (idx a))) = emRealize (K := K) (t j) ↔
        Language.Structure.funMap f (fun a => emRealize (K := K) (s (idx a))) = emRealize (K := K) (s j)) ∧
    (∀ {k₁ k₂ : ℕ} (f₁ : K.τ.Functions k₁) (f₂ : K.τ.Functions k₂)
      (idx₁ : Fin k₁ → Fin n) (idx₂ : Fin k₂ → Fin n),
      Language.Structure.funMap f₁ (fun a => emRealize (K := K) (t (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => emRealize (K := K) (t (idx₂ a))) ↔
        Language.Structure.funMap f₁ (fun a => emRealize (K := K) (s (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => emRealize (K := K) (s (idx₂ a)))) ∧
    (∀ {k} (r : K.τ.Relations k) (idx : Fin k → Fin n),
      Language.Structure.RelMap r (fun a => emRealize (K := K) (t (idx a))) ↔
        Language.Structure.RelMap r (fun a => emRealize (K := K) (s (idx a)))) := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨fun i => Fin.elim0 i, fun _ _ j => Fin.elim0 j, ?_, ?_⟩
    · intro k₁ k₂ f₁ f₂ idx₁ idx₂
      by_cases hk₁ : k₁ = 0
      · subst hk₁
        by_cases hk₂ : k₂ = 0
        · subst hk₂
          have h1 : (fun a => emRealize (K := K) (t (idx₁ a))) = (fun a => emRealize (K := K) (s (idx₁ a))) :=
            funext (fun a => Fin.elim0 a)
          have h2 : (fun a => emRealize (K := K) (t (idx₂ a))) = (fun a => emRealize (K := K) (s (idx₂ a))) :=
            funext (fun a => Fin.elim0 a)
          rw [h1, h2]
        · exact False.elim (Fin.elim0 (idx₂ ⟨0, Nat.pos_of_ne_zero hk₂⟩))
      · exact False.elim (Fin.elim0 (idx₁ ⟨0, Nat.pos_of_ne_zero hk₁⟩))
    · intro k r idx
      by_cases hk : k = 0
      · subst hk
        have h1 : (fun a => emRealize (K := K) (t (idx a))) = (fun a => emRealize (K := K) (s (idx a))) :=
          funext (fun a => Fin.elim0 a)
        rw [h1]
      · exact False.elim (Fin.elim0 (idx ⟨0, Nat.pos_of_ne_zero hk⟩))
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    let Idx := Σ i : Fin n, Fin (emArity K (t i).label)
    let pos_t : Idx → I := fun ⟨i, a⟩ => (t i).pos a
    let pos_s : Idx → I := fun ⟨i, a⟩ => (s i).pos (Fin.cast (congrArg (emArity K) (hlabel i)) a)
    let Pt : Finset I := Finset.image pos_t Finset.univ
    have hPt_nonempty : Pt.Nonempty := by
      refine ⟨pos_t ⟨⟨0, hn_pos⟩, ⟨0, emArity_pos K _⟩⟩, ?_⟩
      simp only [Pt, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨⟨0, hn_pos⟩, ⟨0, emArity_pos K _⟩⟩, rfl⟩
    let J := {x : I // x ∈ Pt}
    let linJ : LinearOrder J := Subtype.instLinearOrder _
    obtain ⟨x0, hx0⟩ := hPt_nonempty
    haveI : Nonempty J := ⟨⟨x0, hx0⟩⟩
    let f_t : J ↪o I := OrderEmbedding.subtype _
    let pick (x : J) : Idx := Classical.choose (Finset.mem_image.mp x.2)
    have pick_spec (x : J) : pos_t (pick x) = x.1 :=
      (Classical.choose_spec (Finset.mem_image.mp x.2)).2
    let f_s_fun (x : J) : I := pos_s (pick x)
    have f_s_mono : StrictMono f_s_fun := by
      intro x y hxy
      have hlt_xy : x.1 < y.1 := hxy
      have hlt_pos : pos_t (pick x) < pos_t (pick y) := by
        rw [pick_spec x, pick_spec y]
        exact hlt_xy
      rcases hx : pick x with ⟨i, a⟩
      rcases hy : pick y with ⟨j, b⟩
      rw [hx, hy] at hlt_pos
      dsimp [f_s_fun]
      rw [hx, hy]
      exact (hlt i j a b).mp hlt_pos
    let f_s : J ↪o I := @OrderEmbedding.ofStrictMono J I linJ _ f_s_fun f_s_mono
    have f_s_apply (p : Idx) : f_s ⟨pos_t p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩ = pos_s p := by
      dsimp [f_s, f_s_fun]
      obtain ⟨i, a⟩ := p
      set x : J := ⟨pos_t ⟨i, a⟩, Finset.mem_image.mpr ⟨⟨i, a⟩, Finset.mem_univ _, rfl⟩⟩
      rcases hpk : pick x with ⟨j, b⟩
      have h_eq : pos_t ⟨j, b⟩ = pos_t ⟨i, a⟩ := by
        have hspec := pick_spec x
        rw [hpk] at hspec
        exact hspec
      exact (heq j i b a).mp h_eq
    let u (i : Fin n) : SupportTerm (EMLab K) (emArity K) J := {
      label := (t i).label
      pos := fun a => ⟨(t i).pos a, Finset.mem_image.mpr ⟨⟨i, a⟩, Finset.mem_univ _, rfl⟩⟩
      increasing := fun a b hab => Subtype.mk_lt_mk.mpr ((t i).increasing hab)
    }
    have ht (i : Fin n) : @mapTerm K J I linJ _ f_t (u i) = t i := by
      apply SupportTerm.ext_of_label_eq (t := @mapTerm K J I linJ _ f_t (u i)) (s := t i) rfl
      intro a; rfl
    have hs (i : Fin n) : @mapTerm K J I linJ _ f_s (u i) = s i := by
      apply SupportTerm.ext_of_label_eq (t := @mapTerm K J I linJ _ f_s (u i)) (s := s i) (hlabel i)
      intro a
      exact f_s_apply ⟨i, a⟩
    exact @pattern_equiv_of_embeddings K _ I J _ linJ _ _ f_t f_s n u t s ht hs

/-- The Ehrenfeucht–Mostowski order presentation for an AEC with arbitrarily large models. -/
noncomputable def emOrderPresentation (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K] :
    OrderPresentation K where
  ell := ls K
  ell_eq := rfl
  lab := EMLab K
  lab_small := emLab_small
  arity := emArity K
  arity_pos := emArity_pos K
  obj I lin non := (emLimit (K := K) I).obj
  map {I J} linI linJ nonI nonJ f := emMap (K := K) f
  map_strong {I J} linI linJ nonI nonJ f := emMap_strong (K := K) f
  map_id {I} lin non := emMap_id (K := K)
  map_comp {I J P} linI linJ linP nonI nonJ nonP f g := emMap_comp (K := K) f g
  realize {I} lin non t := emRealize (K := K) t
  realize_surjective {I} lin non := emRealize_surjective (K := K)
  pattern_determines {I} lin non n t s hlabel heq hlt :=
    emPatternDetermines (K := K) t s hlabel heq hlt
  skeleton {I} lin non := emSkeleton K
  skeleton_natural {I J} linI linJ nonI nonJ f i :=
    emSkeleton_natural (K := K) f i
  sub {I} lin non s := emSub (K := K) s
  sub_incl {I} lin non s hs := emSubIncl (K := K) s hs
  sub_strong {I} lin non s hs := emSubStrong (K := K) s hs
  sub_card {I} lin non s hs := emSubCard (K := K) s hs
  sub_mono {I} lin non s t hs ht hst := emSubMono (K := K) s t hs ht hst
  sub_cover {I} lin non x := emSubCover (K := K) x
  card_lower {I} lin non := emCardLower (K := K)
  card_upper {I} lin non := emCardUpper (K := K)

end
end AEC
