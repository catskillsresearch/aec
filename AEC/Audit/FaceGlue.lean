module

public import AEC.Audit.EqPattern
public import AEC.Section9.Results

@[expose] public section

/-!
# Boundary automorphisms need not respect the gluing of faces in the top (statement audit)

A face family on two axes in the AEC of all sets: the top is `Fin 3 × W` (`#W = ℵ₁`), face
`{0}` is `{k ≠ 2}`, face `{1}` is `{k ≠ 0}`, and face `∅` is empty, so the two faces overlap in
the top although their formal intersection is empty. A boundary automorphism may swap a point
of face `{0}` with a point of the overlap and, independently, a point of face `{1}` with the
same overlap point. This refutes Lemma 9.7 as formalized.
-/

namespace AEC
namespace Audit

universe u

open FirstOrder Cardinal

set_option linter.deprecated false

open Classical

/-- The fixed large type `W`, of size `ℵ₁`. -/
def Wbig : Type u := (Order.succ ℵ₀ : Cardinal.{u}).out

abbrev UG : Type u := ULift.{u} (Fin 3) × Wbig.{u}

def VG (s : Set (Fin 2)) : Set UG.{u} :=
  {u | (u.1.down ≠ 2 ∧ (0 : Fin 2) ∈ s) ∨ (u.1.down ≠ 0 ∧ (1 : Fin 2) ∈ s)}

theorem VG_mono {s t : Set (Fin 2)} (h : s ⊆ t) : VG.{u} s ⊆ VG.{u} t := by
  rintro u (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl ⟨h1, h h2⟩
  · exact Or.inr ⟨h1, h h2⟩

/-- The glued face family. -/
noncomputable def glueFamily : FaceFamily allSetsAEC.{u} 2 where
  obj s := bareModel (VG s)
  inK _ := trivial
  incl h := embOf (M := bareModel _) (N := bareModel _) (Set.inclusion (VG_mono h))
    (Set.inclusion_injective _)
  incl_strong _ := trivial
  incl_refl _ := Language.Embedding.ext fun _ => rfl
  incl_trans _ _ := Language.Embedding.ext fun _ => rfl

theorem fin2_cases (c : Fin 2) : c = 0 ∨ c = 1 := by
  have key : ∀ c : Fin 2, c = 0 ∨ c = 1 := by decide
  exact key c

theorem not_both_of_proper {s : Set (Fin 2)} (hs : IsProper s) :
    ¬ ((0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∈ s) := by
  rintro ⟨h0, h1⟩
  apply hs
  refine Set.eq_univ_of_forall fun c => ?_
  rcases fin2_cases c with rfl | rfl
  · exact h0
  · exact h1

/-- The face maps. -/
noncomputable def faceMap (t1 x t2 : UG.{u}) (s : Set (Fin 2)) : UG.{u} → UG.{u} :=
  if (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∉ s then Equiv.swap t1 x
  else if (1 : Fin 2) ∈ s ∧ (0 : Fin 2) ∉ s then Equiv.swap t2 x
  else id

theorem faceMap_involutive (t1 x t2 : UG.{u}) (s : Set (Fin 2)) :
    Function.Involutive (faceMap t1 x t2 s) := by
  intro u
  unfold faceMap
  split_ifs
  · exact Equiv.swap_apply_self _ _ _
  · exact Equiv.swap_apply_self _ _ _
  · rfl

theorem swap_mem {S : Set UG.{u}} {a b u : UG.{u}} (ha : a ∈ S) (hb : b ∈ S) (hu : u ∈ S) :
    Equiv.swap a b u ∈ S := by
  rw [Equiv.swap_apply_def]
  split_ifs
  · exact hb
  · exact ha
  · exact hu

theorem faceMap_mem (w : Wbig.{u}) (s : Set (Fin 2)) {u : UG.{u}} (hu : u ∈ VG s) :
    faceMap (⟨0⟩, w) (⟨1⟩, w) (⟨2⟩, w) s u ∈ VG s := by
  unfold faceMap
  split_ifs with hA hB
  · exact swap_mem (a := (⟨0⟩, w)) (b := (⟨1⟩, w)) (Or.inl ⟨(by decide : (0 : Fin 3) ≠ 2), hA.1⟩)
      (Or.inl ⟨(by decide : (1 : Fin 3) ≠ 2), hA.1⟩) hu
  · exact swap_mem (a := (⟨2⟩, w)) (b := (⟨1⟩, w)) (Or.inr ⟨(by decide : (2 : Fin 3) ≠ 0), hB.1⟩)
      (Or.inr ⟨(by decide : (1 : Fin 3) ≠ 0), hB.1⟩) hu
  · exact hu

theorem faceMap_congr (t1 x t2 : UG.{u}) {s t : Set (Fin 2)} (h0 : (0 : Fin 2) ∈ s ↔ (0 : Fin 2) ∈ t)
    (h1 : (1 : Fin 2) ∈ s ↔ (1 : Fin 2) ∈ t) : faceMap t1 x t2 s = faceMap t1 x t2 t := by
  have : s = t := by
    ext c
    rcases fin2_cases c with rfl | rfl
    · exact h0
    · exact h1
  rw [this]

/-- The face map restricted to a face. -/
noncomputable def faceRestrict (w : Wbig.{u}) (s : Set (Fin 2)) : VG.{u} s → VG.{u} s :=
  fun y => ⟨faceMap (⟨0⟩, w) (⟨1⟩, w) (⟨2⟩, w) s y.1, faceMap_mem w s y.2⟩

theorem faceRestrict_involutive (w : Wbig.{u}) (s : Set (Fin 2)) :
    Function.Involutive (faceRestrict w s) :=
  fun y => Subtype.ext (faceMap_involutive _ _ _ s y.1)

/-- The boundary automorphism swapping `(0,w) ↔ (1,w)` on face `{0}` and `(2,w) ↔ (1,w)` on
face `{1}`. -/
noncomputable def glueSwap (w : Wbig.{u}) : BoundaryMap allSetsAEC.{u} glueFamily.{u} glueFamily.{u} where
  onFace {s} _ := embOf (M := bareModel (VG s)) (N := bareModel (VG s)) (faceRestrict w s)
    (faceRestrict_involutive w s).injective
  onFace_strong _ := trivial
  compat {s t} _ ht hst := by
    apply Language.Embedding.ext
    intro y
    apply Subtype.ext
    have hor : (0 : Fin 2) ∈ s ∨ (1 : Fin 2) ∈ s := by
      rcases y.2 with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    have hnt := not_both_of_proper ht
    have h0 : (0 : Fin 2) ∈ t ↔ (0 : Fin 2) ∈ s := by
      constructor
      · intro h; rcases hor with h' | h'
        · exact h'
        · exact absurd ⟨h, hst h'⟩ hnt
      · exact fun h => hst h
    have h1 : (1 : Fin 2) ∈ t ↔ (1 : Fin 2) ∈ s := by
      constructor
      · intro h; rcases hor with h' | h'
        · exact absurd ⟨hst h', h⟩ hnt
        · exact h'
      · exact fun h => hst h
    show faceMap _ _ _ t y.1 = faceMap _ _ _ s y.1
    rw [faceMap_congr _ _ _ h0 h1]

theorem glueSwap_iso (w : Wbig.{u}) : IsBoundaryIso (glueSwap.{u} w) :=
  fun {s} _ => (faceRestrict_involutive w s).bijective

set_option linter.unusedVariables false in
/-- **Lemma 9.7 is false as formalized.** -/
theorem lemma_9_7_false :
    ¬ ∀ (K : AbstractElementaryClass.{u}) {n : ℕ} (J : FaceFamily K n)
    (D : StableDiagram K) {α : Type u} (z : α → (J.obj Set.univ).carrier)
    (σ : Cardinal.{u}),
    ∃ (β : Type u) (a : β → (J.obj Set.univ).carrier), #β ≤ σ + #α ∧
      ∀ (h : BoundaryMap K J J), IsBoundaryIso h →
        (∀ i, ∃ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
          a i = J.incl (Set.subset_univ s) x ∧ h.onFace hs x = x) →
        ∀ {ι : Type u} (t : ι → (J.obj Set.univ).carrier), #ι ≤ σ →
          (∀ k, ∃ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
            t k = J.incl (Set.subset_univ s) x) →
          ∃ t' : ι → (J.obj Set.univ).carrier,
            (∀ k, ∃ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
              t k = J.incl (Set.subset_univ s) x ∧
              t' k = J.incl (Set.subset_univ s) (h.onFace hs x)) ∧
            ∀ (hσ : #(α ⊕ ι) ≤ σ + #α)
              (hcard : D.t (σ + #α) ≤ Model.card (J.obj Set.univ)),
              D.same hσ (J.inK Set.univ) (J.inK Set.univ) hcard hcard
                (Sum.elim z t) (Sum.elim z t')  := by
  intro H
  obtain ⟨β, a, hβ, ha⟩ := H allSetsAEC.{u} glueFamily.{u} eqDiagram.{u} (α := PEmpty.{u + 1})
    isEmptyElim ℵ₀
  have hW : #Wbig.{u} = Order.succ ℵ₀ := Cardinal.mk_out _
  have hlt : #(Set.range fun i => (a i).1.2) < #Wbig.{u} := by
    rw [hW]
    refine lt_of_le_of_lt (Cardinal.mk_range_le.trans hβ) ?_
    rw [Cardinal.mk_eq_zero PEmpty.{u + 1}, add_zero]
    exact Order.lt_succ _
  obtain ⟨w, hw⟩ : (Set.range fun i => (a i).1.2)ᶜ.Nonempty := by
    rw [Set.nonempty_compl]
    intro h
    rw [h, Cardinal.mk_univ] at hlt
    exact lt_irrefl _ hlt
  let p : Fin 3 → UG.{u} := fun k => (⟨k⟩, w)
  have hfix : ∀ i, ∃ (s : Set (Fin 2)) (hs : IsProper s) (x : (glueFamily.{u}.obj s).carrier),
      a i = glueFamily.incl (Set.subset_univ s) x ∧ (glueSwap w).onFace hs x = x := by
    intro i
    have hne : ∀ k, (a i).1 ≠ p k := fun k h => hw ⟨i, congrArg Prod.snd h⟩
    by_cases h2 : (a i).1.1.down = 2
    · have hm : (a i).1 ∈ VG.{u} {1} := Or.inr ⟨by rw [h2]; decide, rfl⟩
      have hp : IsProper ({1} : Set (Fin 2)) := fun h => by
        have : (0 : Fin 2) ∈ ({1} : Set (Fin 2)) := h ▸ Set.mem_univ _
        exact absurd this (by decide)
      refine ⟨{1}, hp, ⟨(a i).1, hm⟩, rfl, Subtype.ext ?_⟩
      show faceMap (p 0) (p 1) (p 2) {1} (a i).1 = (a i).1
      have hc : ¬ ((0 : Fin 2) ∈ ({1} : Set (Fin 2)) ∧ (1 : Fin 2) ∉ ({1} : Set (Fin 2))) :=
        fun h => absurd h.1 (by decide)
      have hd : (1 : Fin 2) ∈ ({1} : Set (Fin 2)) ∧ (0 : Fin 2) ∉ ({1} : Set (Fin 2)) :=
        ⟨rfl, by decide⟩
      simp only [faceMap, if_neg hc, if_pos hd]
      exact Equiv.swap_apply_of_ne_of_ne (hne 2) (hne 1)
    · have hm : (a i).1 ∈ VG.{u} {0} := Or.inl ⟨h2, rfl⟩
      have hp : IsProper ({0} : Set (Fin 2)) := fun h => by
        have : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := h ▸ Set.mem_univ _
        exact absurd this (by decide)
      refine ⟨{0}, hp, ⟨(a i).1, hm⟩, rfl, Subtype.ext ?_⟩
      show faceMap (p 0) (p 1) (p 2) {0} (a i).1 = (a i).1
      have hc : (0 : Fin 2) ∈ ({0} : Set (Fin 2)) ∧ (1 : Fin 2) ∉ ({0} : Set (Fin 2)) :=
        ⟨rfl, by decide⟩
      simp only [faceMap, if_pos hc]
      exact Equiv.swap_apply_of_ne_of_ne (hne 0) (hne 1)
  have hp0 : IsProper ({0} : Set (Fin 2)) := fun h => by
    have : (1 : Fin 2) ∈ ({0} : Set (Fin 2)) := h ▸ Set.mem_univ _
    exact absurd this (by decide)
  have hp1 : IsProper ({1} : Set (Fin 2)) := fun h => by
    have : (0 : Fin 2) ∈ ({1} : Set (Fin 2)) := h ▸ Set.mem_univ _
    exact absurd this (by decide)
  let tv : ULift.{u} Bool → (glueFamily.{u}.obj Set.univ).carrier := fun b =>
    if b.down then (⟨p 2, Or.inr ⟨(by decide : (2 : Fin 3) ≠ 0), Set.mem_univ _⟩⟩ : ↥(VG.{u} Set.univ))
    else (⟨p 0, Or.inl ⟨(by decide : (0 : Fin 3) ≠ 2), Set.mem_univ _⟩⟩ : ↥(VG.{u} Set.univ))
  have htv : ∀ k, ∃ (s : Set (Fin 2)) (hs : IsProper s) (x : (glueFamily.{u}.obj s).carrier),
      tv k = glueFamily.incl (Set.subset_univ s) x := by
    rintro ⟨b⟩
    cases b
    · exact ⟨{0}, hp0, ⟨p 0, Or.inl ⟨(by decide : (0 : Fin 3) ≠ 2), rfl⟩⟩, rfl⟩
    · exact ⟨{1}, hp1, ⟨p 2, Or.inr ⟨(by decide : (2 : Fin 3) ≠ 0), rfl⟩⟩, rfl⟩
  have hcardι : #(ULift.{u} Bool) ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite _).le
  obtain ⟨t', ht', hsame⟩ := ha (glueSwap w) (glueSwap_iso w) hfix tv hcardι htv
  -- every admissible image of `tv k` is the overlap point `p 1`
  have himg : ∀ k, (t' k).1 = p 1 := by
    rintro ⟨b⟩
    obtain ⟨s, hs, y, hy1, hy2⟩ := ht' ⟨b⟩
    rw [hy2]
    show faceMap (p 0) (p 1) (p 2) s y.1 = p 1
    have hyv : y.1 = (tv ⟨b⟩).1 := (congrArg Subtype.val hy1).symm
    have hmem := y.2
    rw [hyv] at hmem
    have hnb := not_both_of_proper hs
    cases b
    · have h0 : (0 : Fin 2) ∈ s := by
        rcases hmem with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · exact absurd rfl h
      have hc : (0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∉ s := ⟨h0, fun h1 => hnb ⟨h0, h1⟩⟩
      simp only [faceMap, if_pos hc]
      rw [hyv]
      exact Equiv.swap_apply_left _ _
    · have h1 : (1 : Fin 2) ∈ s := by
        rcases hmem with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd rfl h
        · exact h
      have hc : ¬ ((0 : Fin 2) ∈ s ∧ (1 : Fin 2) ∉ s) := fun h => h.2 h1
      have hd : (1 : Fin 2) ∈ s ∧ (0 : Fin 2) ∉ s := ⟨h1, fun h0 => hnb ⟨h0, h1⟩⟩
      simp only [faceMap, if_neg hc, if_pos hd]
      rw [hyv]
      exact Equiv.swap_apply_left _ _
  have hσ : #(PEmpty.{u + 1} ⊕ ULift.{u} Bool) ≤ ℵ₀ + #PEmpty.{u + 1} :=
    (Cardinal.lt_aleph0_of_finite _).le.trans le_self_add
  have hcard : eqDiagram.{u}.t (ℵ₀ + #PEmpty.{u + 1}) ≤ Model.card (glueFamily.{u}.obj Set.univ) := by
    show Order.succ (ℵ₀ + #PEmpty.{u + 1}) ≤ #(VG.{u} Set.univ)
    rw [Cardinal.mk_eq_zero PEmpty.{u + 1}, add_zero, ← hW]
    refine Cardinal.mk_le_of_injective (f := fun v : Wbig.{u} =>
      (⟨(⟨0⟩, v), Or.inl ⟨(by decide : (0 : Fin 3) ≠ 2), Set.mem_univ _⟩⟩ : ↥(VG.{u} Set.univ)))
      fun v v' h => congrArg (fun z : ↥(VG.{u} Set.univ) => z.1.2) h
  have hxx := (hsame hσ hcard (Sum.inr ⟨false⟩) (Sum.inr ⟨true⟩)).mpr
    (Subtype.ext ((himg _).trans (himg _).symm))
  have h02 : (0 : Fin 3) = 2 := congrArg (fun z : ↥(VG.{u} Set.univ) => z.1.1.down) hxx
  exact absurd h02 (by decide)

end Audit
end AEC
