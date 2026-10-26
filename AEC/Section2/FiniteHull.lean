module

public import AEC.Section1.LoewenheimSkolem
public import Mathlib.Data.Finset.Powerset
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- When the image of `f` lies in the image of `g`, injectivity of `g` produces the unique
factor `A ↪ B`. It preserves and reflects the language because both outer maps do. -/
noncomputable def factorEmbedding {L : Tau.{u}} {A B C : Type u}
    [L.Structure A] [L.Structure B] [L.Structure C]
    (f : A ↪[L] C) (g : B ↪[L] C) (himg : ∀ a, ∃ b, g b = f a) : A ↪[L] B where
  toFun a := Classical.choose (himg a)
  inj' a₁ a₂ h₁₂ := by
    apply f.injective
    have h₁ := Classical.choose_spec (himg a₁)
    have h₂ := Classical.choose_spec (himg a₂)
    have : Classical.choose (himg a₁) = Classical.choose (himg a₂) := by simpa using h₁₂
    rw [← h₁, ← h₂, this]
  map_fun' {n} φ x := by
    apply g.injective
    have happ (a : A) : g (Classical.choose (himg a)) = f a := Classical.choose_spec (himg a)
    rw [happ, f.map_fun, g.map_fun]
    congr 1
    funext i
    exact (happ (x i)).symm
  map_rel' {n} r x := by
    have happ (a : A) : g (Classical.choose (himg a)) = f a := Classical.choose_spec (himg a)
    rw [← g.map_rel, ← f.map_rel]
    congr! 1
    funext i
    exact happ (x i)

theorem factorEmbedding_comp {L : Tau.{u}} {A B C : Type u}
    [L.Structure A] [L.Structure B] [L.Structure C]
    (f : A ↪[L] C) (g : B ↪[L] C) (himg : ∀ a, ∃ b, g b = f a) :
    g.comp (factorEmbedding f g himg) = f := by
  ext a
  show g (factorEmbedding f g himg a) = f a
  exact Classical.choose_spec (himg a)

/-- One application of the Löwenheim–Skolem axiom: a strong submodel through `A`. -/
structure ChosenHull (K : AbstractElementaryClass.{u}) (M : Model K.τ) (A : Set M.carrier) where
  obj : Model K.τ
  incl : Language.Embedding K.τ obj.carrier M.carrier
  mem : K.Mem obj
  strong : K.Strong incl
  covers : ∀ a ∈ A, ∃ n, incl n = a
  card_le : Model.card obj ≤ mk A + ls K

variable {M : Model K.τ} (hM : K.Mem M)

noncomputable def chosenHull (A : Set M.carrier) : ChosenHull K M A := by
  let spec := (isLSBound_ls K).2.2 M hM A
  let N := Classical.choose spec
  let rest := Classical.choose_spec spec
  let f := Classical.choose rest
  let data := Classical.choose_spec rest
  exact
    { obj := N
      incl := f
      mem := data.1
      strong := data.2.1
      covers := data.2.2.1
      card_le := data.2.2.2 }

/-- The nonempty subsets of `s` of strictly smaller cardinality. -/
def properSubs {n : ℕ} (s : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  s.powerset.filter fun t => t.Nonempty ∧ t.card < s.card

theorem mem_properSubs {n : ℕ} {s t : Finset (Fin n)} :
    t ∈ properSubs s ↔ t ⊆ s ∧ t.Nonempty ∧ t.card < s.card := by
  simp [properSubs, Finset.mem_filter, Finset.mem_powerset]

variable {n : ℕ} (base : Fin n → M.carrier)

/-- The displayed elements of `s`. -/
def displayed (s : {t : Finset (Fin n) // t.Nonempty}) : Set M.carrier :=
  base '' (s.1 : Set (Fin n))

/-- The ranges of the hulls of the nonempty proper subsets of `s`. -/
def lowerRanges (s : {t : Finset (Fin n) // t.Nonempty})
    (rec : ∀ t : {t : Finset (Fin n) // t.Nonempty}, t.1.card < s.1.card →
      Σ A : Set M.carrier, ChosenHull K M A) : Set M.carrier :=
  Set.iUnion fun t : ULift.{u} ↥(properSubs s.1) =>
    let ht := mem_properSubs.mp t.down.2
    Set.range (rec ⟨t.down.1, ht.2.1⟩ ht.2.2).2.incl

/-- One step of the hull recursion: the displayed elements of `s`, together with the ranges
of the hulls of its nonempty proper subsets. -/
noncomputable def subHullStep (s : {t : Finset (Fin n) // t.Nonempty})
    (rec : ∀ t : {t : Finset (Fin n) // t.Nonempty}, t.1.card < s.1.card →
      Σ A : Set M.carrier, ChosenHull K M A) :
    Σ A : Set M.carrier, ChosenHull K M A :=
  ⟨displayed base s ∪ lowerRanges s rec, chosenHull hM (displayed base s ∪ lowerRanges s rec)⟩

theorem cardRel_wf :
    WellFounded (fun a b : {t : Finset (Fin n) // t.Nonempty} => a.1.card < b.1.card) :=
  InvImage.wf (fun s : {t : Finset (Fin n) // t.Nonempty} => s.1.card) Nat.lt_wfRel.wf

/-- Hulls of the nonempty subsets of a finite set of displayed elements, built by recursion
on the size of the subset. -/
noncomputable def subHull :
    (s : {t : Finset (Fin n) // t.Nonempty}) → Σ A : Set M.carrier, ChosenHull K M A :=
  WellFounded.fix cardRel_wf (subHullStep hM base)

theorem subHull_eq (s : {t : Finset (Fin n) // t.Nonempty}) :
    subHull hM base s =
      subHullStep hM base s fun t _ => subHull hM base t :=
  WellFounded.fix_eq _ _ _

/-- The strong submodel assigned to a nonempty finite set of displayed elements. -/
noncomputable def subModel (s : {t : Finset (Fin n) // t.Nonempty}) : Model K.τ :=
  (subHull hM base s).2.obj

noncomputable def subIncl (s : {t : Finset (Fin n) // t.Nonempty}) :
    Language.Embedding K.τ (subModel hM base s).carrier M.carrier :=
  (subHull hM base s).2.incl

theorem subModel_mem (s : {t : Finset (Fin n) // t.Nonempty}) :
    K.Mem (subModel hM base s) :=
  (subHull hM base s).2.mem

theorem subIncl_strong (s : {t : Finset (Fin n) // t.Nonempty}) :
    K.Strong (subIncl hM base s) :=
  (subHull hM base s).2.strong

theorem subIncl_covers (s : {t : Finset (Fin n) // t.Nonempty})
    {a : M.carrier} (ha : a ∈ (subHull hM base s).1) :
    ∃ x, subIncl hM base s x = a :=
  (subHull hM base s).2.covers a ha

/-- A smaller hull sits inside a larger one. The two inclusions into `M` determine the
factor, and coherence makes that factor strong. -/
noncomputable def subInclFactor
    (t s : {t : Finset (Fin n) // t.Nonempty})
    (hsub : t.1 ⊆ s.1) (hlt : t.1.card < s.1.card) :
    Language.Embedding K.τ (subModel hM base t).carrier (subModel hM base s).carrier :=
  factorEmbedding (subIncl hM base t) (subIncl hM base s) fun x => by
    have htmem : t.1 ∈ properSubs s.1 := mem_properSubs.mpr ⟨hsub, t.2, hlt⟩
    have hrange : subIncl hM base t x ∈ (subHull hM base s).1 := by
      rw [subHull_eq hM base s]
      refine Or.inr ?_
      refine Set.mem_iUnion.mpr ?_
      refine ⟨ULift.up ⟨t.1, htmem⟩, ?_⟩
      exact ⟨x, rfl⟩
    exact subIncl_covers hM base s hrange

theorem subInclFactor_comp (t s : {t : Finset (Fin n) // t.Nonempty})
    (hsub : t.1 ⊆ s.1) (hlt : t.1.card < s.1.card) :
    (subIncl hM base s).comp (subInclFactor hM base t s hsub hlt) = subIncl hM base t :=
  factorEmbedding_comp _ _ _

theorem subInclFactor_strong (t s : {t : Finset (Fin n) // t.Nonempty})
    (hsub : t.1 ⊆ s.1) (hlt : t.1.card < s.1.card) :
    K.Strong (subInclFactor hM base t s hsub hlt) :=
  K.coherence (subInclFactor hM base t s hsub hlt) (subIncl hM base t) (subIncl hM base s)
    (subIncl_strong hM base t) (subIncl_strong hM base s)
    (subInclFactor_comp hM base t s hsub hlt)

/-- Finitely many smaller hulls, each of size at most `LS(K)`, still have size at most `LS(K)`. -/
theorem subModel_card (s : {t : Finset (Fin n) // t.Nonempty}) :
    Model.card (subModel hM base s) ≤ ls K := by
  refine WellFounded.induction
    (C := fun s => Model.card (subModel hM base s) ≤ ls K) cardRel_wf s ?_
  intro s ih
  have hall : aleph0 ≤ ls K := (isLSBound_ls K).1
  have hle : Model.card (subModel hM base s) ≤ mk (subHull hM base s).1 + ls K :=
    (subHull hM base s).2.card_le
  have hA : mk (subHull hM base s).1 ≤ ls K := by
    rw [subHull_eq hM base s]
    have hset :
        (subHullStep hM base s (fun t _ => subHull hM base t)).1 =
          displayed base s ∪ lowerRanges s (fun t _ => subHull hM base t) := rfl
    rw [hset]
    refine (mk_union_le _ _).trans ?_
    have himg : mk (displayed base s) ≤ ls K := by
      have hfin : (displayed base s).Finite := (s.1.finite_toSet).image base
      exact (mk_le_aleph0_iff.mpr hfin.countable).trans hall
    let recs : ∀ t : {t : Finset (Fin n) // t.Nonempty}, t.1.card < s.1.card →
        Σ A : Set M.carrier, ChosenHull K M A := fun t _ => subHull hM base t
    have hpieces : mk (lowerRanges s recs) ≤ ls K := by
      let pieceSet : ULift.{u} ↥(properSubs s.1) → Set M.carrier := fun t =>
        let ht := mem_properSubs.mp t.down.2
        Set.range (recs ⟨t.down.1, ht.2.1⟩ ht.2.2).2.incl
      have hunion : lowerRanges s recs = Set.iUnion pieceSet := rfl
      rw [hunion]
      refine (mk_iUnion_le pieceSet).trans ?_
      have hone (t : ULift.{u} ↥(properSubs s.1)) : #(pieceSet t) ≤ ls K := by
        unfold pieceSet
        let ht := mem_properSubs.mp t.down.2
        refine mk_range_le.trans ?_
        exact ih ⟨t.down.1, ht.2.1⟩ ht.2.2
      have hsup : (⨆ t, #(pieceSet t)) ≤ ls K := ciSup_le' hone
      refine (mul_le_mul' mk_le_aleph0 hsup).trans ?_
      rw [aleph0_mul_eq hall]
    exact (add_le_add himg hpieces).trans <| by
      rw [add_eq_max hall, max_self]
  calc Model.card (subModel hM base s)
      ≤ mk (subHull hM base s).1 + ls K := hle
    _ = ls K + mk (subHull hM base s).1 := add_comm _ _
    _ = max (ls K) (mk (subHull hM base s).1) := add_eq_max hall
    _ = ls K := max_eq_left hA

end
end AEC
