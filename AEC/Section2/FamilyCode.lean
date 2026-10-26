module

public import AEC.Section2.AtomCode
public import Mathlib.Data.Finset.Sort

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}} {M : Model K.τ} (hM : K.Mem M)

/-- The atomic diagrams of the hulls of all nonempty subsets of an `n`-tuple, together with
the equalities between names drawn from different hulls. Those cross-equalities are the
atomic formulas that mention entries of more than one enumeration. -/
@[ext]
structure FamilyCode (K : AbstractElementaryClass.{u}) (n : ℕ) where
  code : {t : Finset (Fin n) // t.Nonempty} → AtomCode K
  link : (t u : {s : Finset (Fin n) // s.Nonempty}) → Enum K → Enum K → Prop

variable {n : ℕ} (base : Fin n → M.carrier)

/-- The displayed elements of a nonempty subset, in increasing position. -/
def subsetSeed (t : {s : Finset (Fin n) // s.Nonempty}) : Fin t.1.card → M.carrier :=
  fun i => base (t.1.orderEmbOfFin rfl i)

theorem subsetSeed_injective (hbase : Function.Injective base)
    (t : {s : Finset (Fin n) // s.Nonempty}) :
    Function.Injective (subsetSeed base t) := by
  intro i j hij
  exact (t.1.orderEmbOfFin rfl).injective (hbase hij)

theorem displayed_covered (t : {s : Finset (Fin n) // s.Nonempty}) {i : Fin n}
    (hi : i ∈ t.1) : base i ∈ (subHull hM base t).1 := by
  rw [subHull_eq hM base t]
  exact Or.inl ⟨i, hi, rfl⟩

/-- A preimage, in the hull, of each displayed element. -/
noncomputable def subsetPreimage (t : {s : Finset (Fin n) // s.Nonempty})
    (i : Fin t.1.card) : (subModel hM base t).carrier :=
  Classical.choose (subIncl_covers hM base t
    (displayed_covered hM base t (Finset.orderEmbOfFin_mem t.1 rfl i)))

theorem subsetPreimage_spec (t : {s : Finset (Fin n) // s.Nonempty}) (i : Fin t.1.card) :
    subIncl hM base t (subsetPreimage hM base t i) = base (t.1.orderEmbOfFin rfl i) :=
  Classical.choose_spec (subIncl_covers hM base t
    (displayed_covered hM base t (Finset.orderEmbOfFin_mem t.1 rfl i)))

theorem subsetPreimage_injective (hbase : Function.Injective base)
    (t : {s : Finset (Fin n) // s.Nonempty}) :
    Function.Injective (subsetPreimage hM base t) := by
  intro i j hij
  apply (t.1.orderEmbOfFin rfl).injective
  apply hbase
  rw [← subsetPreimage_spec hM base t i, ← subsetPreimage_spec hM base t j, hij]

theorem subModel_nonempty (t : {s : Finset (Fin n) // s.Nonempty}) :
    Nonempty (subModel hM base t).carrier :=
  ⟨subsetPreimage hM base t ⟨0, Finset.card_pos.mpr t.2⟩⟩

/-- The hull of a nonempty subset, enumerated so that the first names are its displayed
elements. -/
noncomputable def subsetEnumerated (hbase : Function.Injective base)
    (t : {s : Finset (Fin n) // s.Nonempty}) :
    Enumerated K :=
  let seed := subsetPreimage hM base t
  let hseed := subsetPreimage_injective hM base hbase t
  let hcard := subModel_card hM base t
  haveI : Nonempty (subModel hM base t).carrier := subModel_nonempty hM base t
  { model := subModel hM base t
    enum := enumOf (n := t.1.card) hcard seed hseed
    surj := enumOf_surjective (n := t.1.card) hcard seed hseed }

/-- The color of an `n`-tuple is the diagram of every nonempty subtuple, with names from
different subtuples identified when they name the same element of `M`. -/
noncomputable def readFamily (hbase : Function.Injective base) : FamilyCode K n where
  code t := AtomCode.read (subsetEnumerated hM base hbase t)
  link t u η ζ :=
    subIncl hM base t ((subsetEnumerated hM base hbase t).enum η) =
      subIncl hM base u ((subsetEnumerated hM base hbase u).enum ζ)

end
end AEC
