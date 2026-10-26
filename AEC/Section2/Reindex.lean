module

public import AEC.Section2.FamilyCode
public import Mathlib.Data.Finset.Preimage

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- The image of a nonempty index set under an order embedding. -/
def mapped {m n : ℕ} (e : Fin m ↪o Fin n)
    (t : {s : Finset (Fin m) // s.Nonempty}) :
    {s : Finset (Fin n) // s.Nonempty} :=
  ⟨t.1.map e.toEmbedding, Finset.map_nonempty.mpr t.2⟩

/-- A diagram transported along an order embedding of the index set. The atomic codes
themselves are indexed by enumeration names, so only the subset that carries each code moves. -/
def FamilyCode.pull {m n : ℕ} (e : Fin m ↪o Fin n) (c : FamilyCode K n) : FamilyCode K m where
  code t := c.code (mapped e t)
  link t u η ζ := c.link (mapped e t) (mapped e u) η ζ

theorem mapped_mem_properSubs {m n : ℕ} (e : Fin m ↪o Fin n) {t v : Finset (Fin m)}
    (hv : v ∈ properSubs t) :
    v.map e.toEmbedding ∈ properSubs (t.map e.toEmbedding) := by
  have h := mem_properSubs.mp hv
  refine mem_properSubs.mpr ⟨?_, ?_, ?_⟩
  · exact Finset.map_subset_map.mpr h.1
  · exact Finset.map_nonempty.mpr h.2.1
  · rw [Finset.card_map, Finset.card_map]
    exact h.2.2

/-- Every nonempty proper subset of an embedded index set is the embedded image of one. -/
theorem exists_proper_preimage {m n : ℕ} (e : Fin m ↪o Fin n) {t : Finset (Fin m)}
    {u : Finset (Fin n)} (hu : u ∈ properSubs (t.map e.toEmbedding)) :
    ∃ v : Finset (Fin m), v ∈ properSubs t ∧ v.map e.toEmbedding = u := by
  have hmem := mem_properSubs.mp hu
  let f : Fin m ↪ Fin n := e.toEmbedding
  let v := u.preimage f f.injective.injOn
  have hvmap : v.map f = u := by
    ext b
    constructor
    · intro hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
      exact Finset.mem_preimage.mp ha
    · intro hb
      have hb' : b ∈ t.map f := hmem.1 hb
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb'
      exact Finset.mem_map.mpr ⟨a, Finset.mem_preimage.mpr hb, rfl⟩
  have hvsub : v ⊆ t := by
    intro a ha
    have ha' : f a ∈ u := Finset.mem_preimage.mp ha
    obtain ⟨a', ha', he⟩ := Finset.mem_map.mp (hmem.1 ha')
    have heq : a' = a := f.injective he
    rw [← heq]
    exact ha'
  have hvne : v.Nonempty := by
    rw [← Finset.map_nonempty (f := f), hvmap]
    exact hmem.2.1
  have hvcard : v.card < t.card := by
    have hcard : v.card = u.card := by
      rw [← hvmap, Finset.card_map]
    rw [hcard]
    have htu : u.card < (t.map f).card := hmem.2.2
    rwa [Finset.card_map] at htu
  exact ⟨v, mem_properSubs.mpr ⟨hvsub, hvne, hvcard⟩, hvmap⟩

variable {M : Model K.τ} (hM : K.Mem M)

theorem displayed_mapped {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (t : {s : Finset (Fin m) // s.Nonempty}) :
    displayed (fun i => base (e i)) t = displayed base (mapped e t) := by
  ext a
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨e i, Finset.mem_map.mpr ⟨i, hi, rfl⟩, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact ⟨i, hi, rfl⟩

theorem subHull_congr {n : ℕ} (base : Fin n → M.carrier)
    {t₁ t₂ : {s : Finset (Fin n) // s.Nonempty}} (h : t₁ = t₂) :
    subHull hM base t₁ = subHull hM base t₂ := by
  rw [h]

theorem lowerRanges_mapped {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (t : {s : Finset (Fin m) // s.Nonempty})
    (ih : ∀ u : {s : Finset (Fin m) // s.Nonempty}, u.1.card < t.1.card →
      subHull hM (fun i => base (e i)) u = subHull hM base (mapped e u)) :
    lowerRanges t (fun u _ => subHull hM (fun i => base (e i)) u) =
      lowerRanges (mapped e t) (fun u _ => subHull hM base u) := by
  unfold lowerRanges
  ext a
  constructor
  · intro ha
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp ha
    have ht := mem_properSubs.mp w.down.2
    let v : {s : Finset (Fin m) // s.Nonempty} := ⟨w.down.1, ht.2.1⟩
    have hvlt : v.1.card < t.1.card := ht.2.2
    have hih := ih v hvlt
    have hmem : (mapped e v).1 ∈ properSubs (mapped e t).1 := by
      simpa [mapped] using mapped_mem_properSubs e w.down.2
    have hleft : a ∈ Set.range (subHull hM (fun i => base (e i)) v).2.incl := by
      simpa [v] using hw
    have hright : a ∈ Set.range (subHull hM base (mapped e v)).2.incl := by
      rw [← hih]
      exact hleft
    refine Set.mem_iUnion.mpr ⟨ULift.up ⟨(mapped e v).1, hmem⟩, ?_⟩
    change a ∈ Set.range (subHull hM base
      ⟨(mapped e v).1, (mem_properSubs.mp hmem).2.1⟩).2.incl
    rw [subHull_congr hM base (Subtype.ext rfl)]
    exact hright
  · intro ha
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp ha
    have ht := mem_properSubs.mp w.down.2
    have hu : w.down.1 ∈ properSubs (t.1.map e.toEmbedding) := by
      simpa [mapped] using w.down.2
    obtain ⟨v, hvmem, hvmap⟩ := exists_proper_preimage e hu
    have hvne : v.Nonempty := (mem_properSubs.mp hvmem).2.1
    have hvlt : v.card < t.1.card := (mem_properSubs.mp hvmem).2.2
    let vsub : {s : Finset (Fin m) // s.Nonempty} := ⟨v, hvne⟩
    have hih := ih vsub hvlt
    have hright : a ∈ Set.range (subHull hM base ⟨w.down.1, ht.2.1⟩).2.incl := by
      simpa using hw
    have himage : mapped e vsub = ⟨w.down.1, ht.2.1⟩ := by
      apply Subtype.ext
      simpa [mapped] using hvmap
    have hmid : a ∈ Set.range (subHull hM base (mapped e vsub)).2.incl := by
      rw [himage]
      exact hright
    have hleft : a ∈ Set.range (subHull hM (fun i => base (e i)) vsub).2.incl := by
      rw [hih]
      exact hmid
    refine Set.mem_iUnion.mpr ⟨ULift.up ⟨v, hvmem⟩, ?_⟩
    change a ∈ Set.range (subHull hM (fun i => base (e i))
      ⟨v, (mem_properSubs.mp hvmem).2.1⟩).2.incl
    rw [subHull_congr hM (fun i => base (e i)) (Subtype.ext rfl)]
    exact hleft

/-- The hull of an embedded tuple is the hull of its image. The covered set of elements of `M`
depends on the tuple only through the set of displayed elements and the smaller hulls. -/
theorem subHull_mapped {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (t : {s : Finset (Fin m) // s.Nonempty}) :
    subHull hM (fun i => base (e i)) t = subHull hM base (mapped e t) := by
  refine WellFounded.induction
    (C := fun t => subHull hM (fun i => base (e i)) t = subHull hM base (mapped e t))
    cardRel_wf t ?_
  intro t ih
  rw [subHull_eq hM (fun i => base (e i)) t, subHull_eq hM base (mapped e t)]
  have hset :
      displayed (fun i => base (e i)) t ∪
          lowerRanges t (fun u _ => subHull hM (fun i => base (e i)) u) =
        displayed base (mapped e t) ∪
          lowerRanges (mapped e t) (fun u _ => subHull hM base u) := by
    rw [displayed_mapped e base t, lowerRanges_mapped hM e base t ih]
  simp only [subHullStep]
  exact Sigma.ext hset (hset ▸ HEq.rfl)

theorem orderEmbOfFin_mapped {m n : ℕ} (e : Fin m ↪o Fin n) (s : Finset (Fin m))
    (_hs : s.Nonempty) (i : Fin s.card) :
    (s.map e.toEmbedding).orderEmbOfFin (Finset.card_map e.toEmbedding) i =
      e (s.orderEmbOfFin rfl i) := by
  have hmono : StrictMono (fun j : Fin s.card => e (s.orderEmbOfFin rfl j)) :=
    fun j k hjk => (e.lt_iff_lt).mpr ((s.orderEmbOfFin rfl).strictMono hjk)
  have hfun :
      (fun j : Fin s.card => e (s.orderEmbOfFin rfl j)) =
        ⇑((s.map e.toEmbedding).orderEmbOfFin (Finset.card_map e.toEmbedding)) :=
    Finset.orderEmbOfFin_unique (Finset.card_map e.toEmbedding)
      (fun j => Finset.mem_map.mpr
        ⟨s.orderEmbOfFin rfl j, Finset.orderEmbOfFin_mem s rfl j, rfl⟩)
      hmono
  exact (congrFun hfun i).symm

/-- Moving along a proof that two finite cardinals agree does not change the increasing
enumeration. -/
theorem orderEmbOfFin_cast {α : Type u} [LinearOrder α] (s : Finset α) {k : ℕ}
    (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin rfl (Fin.cast h.symm i) = s.orderEmbOfFin h i := by
  have hmono : StrictMono (fun j : Fin k => s.orderEmbOfFin rfl (Fin.cast h.symm j)) := by
    intro a b hab
    apply (s.orderEmbOfFin rfl).strictMono
    rw [Fin.lt_def] at hab ⊢
    simpa [Fin.val_cast] using hab
  have hfun :
      (fun j : Fin k => s.orderEmbOfFin rfl (Fin.cast h.symm j)) =
        ⇑(s.orderEmbOfFin h) :=
    Finset.orderEmbOfFin_unique h
      (fun j => Finset.orderEmbOfFin_mem s rfl (Fin.cast h.symm j))
      hmono
  exact congrFun hfun i

/-- The displayed element named by position `i` is unchanged when the index set is embedded. -/
theorem subsetPreimage_mapped_ambient {m n : ℕ} (e : Fin m ↪o Fin n)
    (base : Fin n → M.carrier) (t : {s : Finset (Fin m) // s.Nonempty})
    (i : Fin t.1.card) :
    subIncl hM (fun j => base (e j)) t
        (subsetPreimage hM (fun j => base (e j)) t i) =
      subIncl hM base (mapped e t)
        (subsetPreimage hM base (mapped e t)
          (Fin.cast (Finset.card_map e.toEmbedding).symm i)) := by
  rw [subsetPreimage_spec, subsetPreimage_spec]
  have hmap := orderEmbOfFin_mapped e t.1 t.2 i
  have hcast := orderEmbOfFin_cast (t.1.map e.toEmbedding)
    (Finset.card_map e.toEmbedding) i
  have hidx :
      ((mapped e t).1.orderEmbOfFin rfl)
          (Fin.cast (Finset.card_map e.toEmbedding).symm i) =
        ((t.1.map e.toEmbedding).orderEmbOfFin rfl)
          (Fin.cast (Finset.card_map e.toEmbedding).symm i) := by
    simp only [mapped]
    congr 1
  rw [hidx, hcast, hmap]

theorem subIncl_mapped_heq {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (t : {s : Finset (Fin m) // s.Nonempty}) :
    HEq (subIncl hM (fun i => base (e i)) t) (subIncl hM base (mapped e t)) := by
  generalize hp : subHull hM (fun i => base (e i)) t = p
  generalize hq : subHull hM base (mapped e t) = q
  have hsig : p = q := by
    simpa [hp, hq] using subHull_mapped hM e base t
  subst hsig
  have hfields : HEq (subHull hM (fun i => base (e i)) t).2.incl
      (subHull hM base (mapped e t)).2.incl := by
    rw [hp, hq]
  unfold subIncl subModel
  exact hfields

theorem subModel_mapped {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (t : {s : Finset (Fin m) // s.Nonempty}) :
    subModel hM (fun i => base (e i)) t = subModel hM base (mapped e t) := by
  generalize hp : subHull hM (fun i => base (e i)) t = p
  generalize hq : subHull hM base (mapped e t) = q
  have hsig : p = q := by
    simpa [hp, hq] using subHull_mapped hM e base t
  subst hsig
  unfold subModel
  rw [hp, hq]

/-- An inclusion transported along an equality of models is the other inclusion. -/
theorem cast_incl_apply {L R : Model K.τ}
    (f : L.carrier ↪[K.τ] M.carrier) (g : R.carrier ↪[K.τ] M.carrier)
    (hmodel : L = R) (hincl : HEq f g) (x : R.carrier) :
    f (cast (congrArg Model.carrier hmodel).symm x) = g x := by
  subst hmodel
  exact congrFun (congrArg (⇑) (eq_of_heq hincl)) x

/-- Transport of an inclusion along the equality of the two hulls. -/
theorem subIncl_cast_apply {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (t : {s : Finset (Fin m) // s.Nonempty})
    (x : (subModel hM base (mapped e t)).carrier) :
    subIncl hM (fun i => base (e i)) t
        (cast (congrArg Model.carrier (subModel_mapped hM e base t)).symm x) =
      subIncl hM base (mapped e t) x :=
  cast_incl_apply (subIncl hM (fun i => base (e i)) t) (subIncl hM base (mapped e t))
    (subModel_mapped hM e base t) (subIncl_mapped_heq hM e base t) x

theorem subsetPreimage_mapped {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (t : {s : Finset (Fin m) // s.Nonempty}) (i : Fin t.1.card) :
    HEq (subsetPreimage hM (fun j => base (e j)) t i)
      (subsetPreimage hM base (mapped e t)
        (Fin.cast (Finset.card_map e.toEmbedding).symm i)) := by
  apply heq_of_eq_cast (congrArg Model.carrier (subModel_mapped hM e base t)).symm
  apply (subIncl hM (fun j => base (e j)) t).injective
  rw [subIncl_cast_apply hM e base t]
  exact subsetPreimage_mapped_ambient hM e base t i

/-- Values that correspond across an equality of models have the same image when the
inclusions correspond. -/
theorem incl_heq_apply {L R : Model K.τ} (hmodel : L = R)
    (f : L.carrier ↪[K.τ] M.carrier) (g : R.carrier ↪[K.τ] M.carrier) (hf : HEq f g)
    (x : L.carrier) (y : R.carrier) (hxy : HEq x y) : f x = g y := by
  subst hmodel
  rw [eq_of_heq hxy]
  exact congrFun (congrArg (⇑) (eq_of_heq hf)) y

theorem subsetEnum_heq {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (hbase : Function.Injective base) (t : {s : Finset (Fin m) // s.Nonempty}) (η : Enum K) :
    HEq ((subsetEnumerated hM (fun i => base (e i)) (hbase.comp e.injective) t).enum η)
      ((subsetEnumerated hM base hbase (mapped e t)).enum η) := by
  haveI : Nonempty (subModel hM (fun i => base (e i)) t).carrier :=
    subModel_nonempty hM (fun i => base (e i)) t
  haveI : Nonempty (subModel hM base (mapped e t)).carrier :=
    subModel_nonempty hM base (mapped e t)
  unfold subsetEnumerated
  exact enumOf_point_heq (congrArg Model.carrier (subModel_mapped hM e base t))
    (Finset.card_map e.toEmbedding).symm
    (subModel_card hM (fun i => base (e i)) t)
    (subModel_card hM base (mapped e t))
    (subsetPreimage_injective hM (fun i => base (e i)) (hbase.comp e.injective) t)
    (subsetPreimage_injective hM base hbase (mapped e t))
    (fun i => subsetPreimage_mapped hM e base t i) η

/-- The atomic diagram of a subset, read from the embedded indices, is the atomic diagram of
the image subset. -/
theorem atom_mapped {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (hbase : Function.Injective base) (t : {s : Finset (Fin m) // s.Nonempty}) :
    AtomCode.read (subsetEnumerated hM (fun i => base (e i)) (hbase.comp e.injective) t) =
      AtomCode.read (subsetEnumerated hM base hbase (mapped e t)) :=
  AtomCode.read_congr (subModel_mapped hM e base t)
    (subsetEnumerated hM (fun i => base (e i)) (hbase.comp e.injective) t).enum
    (subsetEnumerated hM base hbase (mapped e t)).enum
    (subsetEnumerated hM (fun i => base (e i)) (hbase.comp e.injective) t).surj
    (subsetEnumerated hM base hbase (mapped e t)).surj
    (subsetEnum_heq hM e base hbase t)

theorem ambient_enum_mapped {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (hbase : Function.Injective base) (t : {s : Finset (Fin m) // s.Nonempty}) (η : Enum K) :
    subIncl hM (fun i => base (e i)) t
        ((subsetEnumerated hM (fun i => base (e i)) (hbase.comp e.injective) t).enum η) =
      subIncl hM base (mapped e t)
        ((subsetEnumerated hM base hbase (mapped e t)).enum η) :=
  incl_heq_apply (subModel_mapped hM e base t)
    (subIncl hM (fun i => base (e i)) t) (subIncl hM base (mapped e t))
    (subIncl_mapped_heq hM e base t)
    ((subsetEnumerated hM (fun i => base (e i)) (hbase.comp e.injective) t).enum η)
    ((subsetEnumerated hM base hbase (mapped e t)).enum η)
    (subsetEnum_heq hM e base hbase t η)

/-- The color of an embedded tuple is the reindexing of the color of the original tuple.
This is the restriction of an n-color to an m-subset. -/
theorem readFamily_pull {m n : ℕ} (e : Fin m ↪o Fin n) (base : Fin n → M.carrier)
    (hbase : Function.Injective base) :
    readFamily hM (fun i => base (e i)) (hbase.comp e.injective) =
      FamilyCode.pull e (readFamily hM base hbase) := by
  refine FamilyCode.ext ?_ ?_
  · funext t
    simp only [readFamily, FamilyCode.pull]
    exact atom_mapped hM e base hbase t
  · funext t u η ζ
    simp only [readFamily, FamilyCode.pull]
    apply propext
    constructor
    · intro h
      rw [← ambient_enum_mapped hM e base hbase t η,
        ← ambient_enum_mapped hM e base hbase u ζ, h]
    · intro h
      rw [ambient_enum_mapped hM e base hbase t η,
        ambient_enum_mapped hM e base hbase u ζ, h]

end
end AEC
