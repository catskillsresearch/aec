module

public import AEC.Audit.EqPattern

@[expose] public section

/-!
# Boundary gluing is not determined by the faces (statement audit)

Two geometric systems on two axes in the AEC of all sets, with the same faces (`Fin 3` on each
singleton face, empty at `∅`) but different tops: in `X` the two faces sit disjointly in
`Fin 2 × Fin 3`, in `Y` both faces are the whole top `Fin 3`. The identity on faces is a
`PrescribedBoundaryIso`, yet the diagram of a boundary tuple is not preserved. This refutes
Lemma 12.3 as formalized (nothing ties the top vertex to the free amalgam of its faces).
-/

namespace AEC
namespace Audit

universe u

open FirstOrder Cardinal

set_option linter.deprecated false

/-- An admissible family on two axes. -/
def L2 : Set (Finset (Fin 2)) := extendFamily 1 (extendFamily 0 {∅} ∅) ∅

theorem admissible_L2 : Admissible 2 L2 :=
  Admissible.step (Admissible.step Admissible.nil (Set.empty_subset _) (fun _ _ h => h.elim))
    (Set.empty_subset _) (fun _ _ h => h.elim)

/-- A geometric system of subsets of a fixed type, with inclusion maps and no pieces. -/
noncomputable def subsetSystem {n : ℕ} {L : Set (Finset (Fin n))} (hL : Admissible n L)
    (U : Type u) (V : Finset (Fin n) → Set U) (hV : ∀ {s t}, s ⊆ t → V s ⊆ V t) :
    GeometricSystem allSetsAEC.{u} n L where
  admissible := hL
  level := 0
  vertex t := bareModel (V t)
  inK _ := trivial
  le h := embOf (M := bareModel _) (N := bareModel _) (Set.inclusion (hV h))
    (Set.inclusion_injective _)
  le_strong _ := trivial
  le_refl _ := Language.Embedding.ext fun _ => rfl
  le_trans _ _ := Language.Embedding.ext fun _ => rfl
  indep _ _ := True
  inP t := {x | InClosure (fun _ => True) {y | ∃ s, ∃ hs : s ∈ L, ∃ hst : s ⊆ t, ∃ z,
    z ∈ (∅ : Set (V s)) ∧ Set.inclusion (hV hst) z = y} x}
  piece _ _ := ∅
  pieceRank _ _ := 0
  piece_card _ _ := by simp
  span _ := rfl

def VX (t : Finset (Fin 2)) : Set (ULift.{u} (Fin 2 × Fin 3)) := {u | u.down.1 ∈ t}
def VY (t : Finset (Fin 2)) : Set (ULift.{u} (Fin 3)) := {_v | t.Nonempty}

theorem memVX {t : Finset (Fin 2)} {a : Fin 2} (k : Fin 3) (h : a ∈ t) :
    (⟨(a, k)⟩ : ULift.{u} (Fin 2 × Fin 3)) ∈ VX.{u} t := h

theorem VX_mono {s t : Finset (Fin 2)} (h : s ⊆ t) : VX.{u} s ⊆ VX.{u} t := fun _ hu => h hu
theorem VY_mono {s t : Finset (Fin 2)} (h : s ⊆ t) : VY.{u} s ⊆ VY.{u} t := fun _ hn => hn.mono h

noncomputable abbrev sysX : GeometricSystem allSetsAEC.{u} 2 L2 :=
  subsetSystem admissible_L2 _ VX.{u} VX_mono
noncomputable abbrev sysY : GeometricSystem allSetsAEC.{u} 2 L2 :=
  subsetSystem admissible_L2 _ VY.{u} VY_mono

theorem fin2_uniq {s : Finset (Fin 2)} (hs : s ≠ Finset.univ) {a b : Fin 2} (ha : a ∈ s)
    (hb : b ∈ s) : a = b := by
  by_contra hab
  apply hs
  ext c
  simp only [Finset.mem_univ, iff_true]
  have key : ∀ a b c : Fin 2, a ≠ b → c = a ∨ c = b := by decide
  rcases key a b c hab with rfl | rfl <;> assumption

/-- The identity on faces. -/
noncomputable def faceEquiv (s : Finset (Fin 2)) (hs : s ≠ Finset.univ) :
    ↥(VX.{u} s) ≃ ↥(VY.{u} s) where
  toFun x := ⟨⟨x.1.down.2⟩, ⟨_, x.2⟩⟩
  invFun y := ⟨⟨(Classical.choose y.2, y.1.down)⟩, Classical.choose_spec y.2⟩
  left_inv x := by
    apply Subtype.ext
    apply ULift.ext
    exact Prod.ext (fin2_uniq hs (Classical.choose_spec _) x.2) rfl
  right_inv _ := rfl

noncomputable def boundaryIso : PrescribedBoundaryIso allSetsAEC.{u} sysX.{u} sysY.{u} where
  onFace s hs := ⟨faceEquiv s hs, fun {_} f => isEmptyElim (α := eL.{u}.Functions _) f,
    fun {_} r => isEmptyElim (α := eL.{u}.Relations _) r⟩
  onFace_strong _ _ := trivial
  comm _ _ _ _ _ := Language.Embedding.ext fun _ => rfl

theorem three_le_mk {T : Type u} (f : ULift.{u} (Fin 3) → T) (hf : Function.Injective f) :
    (3 : Cardinal.{u}) ≤ #T := by
  simpa using Cardinal.mk_le_of_injective hf

theorem succ_two_le {T : Type u} (f : ULift.{u} (Fin 3) → T) (hf : Function.Injective f) :
    Order.succ (2 : Cardinal.{u}) ≤ #T :=
  Order.succ_le_of_lt (lt_of_lt_of_le (by exact_mod_cast (show (2 : ℕ) < 3 by norm_num))
    (three_le_mk f hf))

def bit (b : ULift.{u} Bool) : Fin 2 := if b.down then 1 else 0

theorem singleton_ne_univ (a : Fin 2) : ({a} : Finset (Fin 2)) ≠ Finset.univ := fun h => by
  have := congrArg Finset.card h
  simp at this

set_option linter.unusedVariables false in
/-- **Lemma 12.3 is false as formalized.** -/
theorem lemma_12_3_false :
    ¬ ∀ (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (X Y : GeometricSystem K n L)
    (h : PrescribedBoundaryIso K X Y) (D : StableDiagram K) {α : Type u}
    (xs : α → (X.vertex Finset.univ).carrier)
    (hfrom : ∀ i, ∃ (s : Finset (Fin n)) (hs : s ≠ Finset.univ) (x : (X.vertex s).carrier),
      xs i = X.le (Finset.subset_univ s) x)
    (hpres : ∀ {M N : Model K.τ} {β : Type u}
        (f : Language.Embedding K.τ M.carrier N.carrier) (zs : β → M.carrier)
        (σ : Cardinal.{u}) (hσ : #β ≤ σ) (hM : K.Mem M) (hN : K.Mem N)
        (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N),
        K.Strong f → D.same hσ hM hN hMcard hNcard zs (fun i => f (zs i)))
    (htrans : ∀ {M N P : Model K.τ} {β : Type u}
        (as : β → M.carrier) (bs : β → N.carrier) (cs : β → P.carrier)
        (σ : Cardinal.{u}) (hσ : #β ≤ σ)
        (hM : K.Mem M) (hN : K.Mem N) (hP : K.Mem P)
        (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N)
        (hPcard : D.t σ ≤ Model.card P),
        D.same hσ hM hN hMcard hNcard as bs →
        D.same hσ hN hP hNcard hPcard bs cs →
        D.same hσ hM hP hMcard hPcard as cs),
    ∃ ys : α → (Y.vertex Finset.univ).carrier,
      (∀ i, ∃ (s : Finset (Fin n)) (hs : s ≠ Finset.univ) (x : (X.vertex s).carrier),
        xs i = X.le (Finset.subset_univ s) x ∧
        ys i = Y.le (Finset.subset_univ s) ((h.onFace s hs) x)) ∧
      ∀ (σ : Cardinal.{u}) (hσ : #α ≤ σ)
        (hX : D.t σ ≤ Model.card (X.vertex Finset.univ))
        (hY : D.t σ ≤ Model.card (Y.vertex Finset.univ)),
        (∀ i, ∃ (s : Finset (Fin n)) (hs : s ≠ Finset.univ) (x : (X.vertex s).carrier),
          xs i = X.le (Finset.subset_univ s) x ∧
          D.t σ ≤ Model.card (X.vertex s) ∧ D.t σ ≤ Model.card (Y.vertex s)) →
        D.same hσ (X.inK Finset.univ) (Y.inK Finset.univ) hX hY xs ys  := by
  intro H
  let xs : ULift.{u} Bool → (sysX.{u}.vertex Finset.univ).carrier :=
    fun b => (⟨⟨(bit b, 0)⟩, memVX _ (Finset.mem_univ _)⟩ : ↥(VX.{u} Finset.univ))
  have hfrom : ∀ i, ∃ (s : Finset (Fin 2)) (hs : s ≠ Finset.univ)
      (x : (sysX.{u}.vertex s).carrier), xs i = sysX.le (Finset.subset_univ s) x :=
    fun i => ⟨{bit i}, singleton_ne_univ _,
      (⟨⟨(bit i, 0)⟩, memVX _ (Finset.mem_singleton_self _)⟩ : ↥(VX.{u} {bit i})), rfl⟩
  obtain ⟨ys, hys1, hys2⟩ := H allSetsAEC.{u} sysX.{u} sysY.{u} boundaryIso eqDiagram.{u} xs hfrom
    (fun f zs _ _ _ _ _ _ _ => fun i j => f.injective.eq_iff.symm)
    (fun _ _ _ _ _ _ _ _ _ _ _ h1 h2 => fun i j => (h1 i j).trans (h2 i j))
  have hy0 : ∀ i, (ys i).1.down = 0 := by
    intro i
    obtain ⟨s, hs, x, hx1, hx2⟩ := hys1 i
    rw [hx2]
    show x.1.down.2 = 0
    exact (congrArg (fun z : ↥(VX.{u} Finset.univ) => z.1.down.2) hx1).symm
  have hcard := hys2 2 (by simp) ?_ ?_ ?_
  · have hyy : ys ⟨false⟩ = ys ⟨true⟩ := Subtype.ext (ULift.ext ((hy0 _).trans (hy0 _).symm))
    have hxx := (hcard ⟨false⟩ ⟨true⟩).mpr hyy
    have := congrArg (fun z : ↥(VX.{u} Finset.univ) => z.1.down.1) hxx
    simp [xs, bit] at this
  · exact succ_two_le (fun k => (⟨⟨(0, k.down)⟩, memVX _ (Finset.mem_univ _)⟩ : ↥(VX.{u} Finset.univ)))
      (fun a b h => ULift.ext (congrArg (fun z : ↥(VX.{u} Finset.univ) => z.1.down.2) h))
  · exact succ_two_le (fun k => (⟨k, Finset.univ_nonempty⟩ : ↥(VY.{u} Finset.univ)))
      (fun a b h => congrArg Subtype.val h)
  · intro i
    refine ⟨{bit i}, singleton_ne_univ _,
      (⟨⟨(bit i, 0)⟩, memVX _ (Finset.mem_singleton_self _)⟩ : ↥(VX.{u} {bit i})), rfl, ?_, ?_⟩
    · exact succ_two_le (fun k => (⟨⟨(bit i, k.down)⟩, memVX _ (Finset.mem_singleton_self _)⟩ :
          ↥(VX.{u} {bit i})))
        (fun a b h => ULift.ext (congrArg (fun z : ↥(VX.{u} {bit i}) => z.1.down.2) h))
    · exact succ_two_le (fun k => (⟨k, Finset.singleton_nonempty _⟩ : ↥(VY.{u} {bit i})))
        (fun a b h => congrArg Subtype.val h)

end Audit
end AEC
