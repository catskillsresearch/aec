module

public import AEC.Section2.Results
public import AEC.Section4.RankSlice
public import AEC.Section4.PairColoringGlue
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Data.Finset.Card

/-!
# Type-u witness packaging for Lemma 4.7

Assembles rank-slice + pair-color glue into a `Type u` dominating family
(`ι`, `v : ι → C → Ordinal`), matching the mermaid “Type u set of witnesses” node.
-/

@[expose] public section

namespace AEC
section

universe u

open Classical Cardinal Ordinal

/-- Empty-coordinate case: domination is vacuous, so one (or no) holds-vector packages. -/
theorem type_u_witness_set_of_isEmpty {C : Type u} [IsEmpty C]
    (holds : (C → Ordinal.{u}) → Prop) :
    ∃ (ι : Type u) (v : ι → C → Ordinal.{u}),
      (∀ i, holds (v i)) ∧
      ∀ f, holds f → ∃ i, ∀ c, v i c ≤ f c := by
  by_cases hocc : ∃ f, holds f
  · obtain ⟨f0, hf0⟩ := hocc
    refine ⟨PUnit, fun _ => f0, fun _ => hf0, fun f _ => ⟨⟨⟩, fun c => (IsEmpty.elim ‹_› c)⟩⟩
  · refine ⟨ULift.{u} Empty, fun i => (Equiv.ulift i).elim,
      fun i => (Equiv.ulift i).elim, fun f hf => (hocc ⟨f, hf⟩).elim⟩

/-- Transport `holds` along an equivalence of coordinate types. -/
def holdsCongr {C D : Type u} (e : D ≃ C) (holds : (C → Ordinal.{u}) → Prop) :
    (D → Ordinal.{u}) → Prop :=
  fun f => holds (f ∘ e.symm)

/-- If no slice generates, a large enough well-order still cannot carry a descent family. -/
theorem not_none_generates {C : Type u}
    [LinearOrder C] [WellFoundedLT C] [Nonempty C]
    (holds : (C → Ordinal.{u}) → Prop)
    (hnone : ∀ β, ¬ GeneratesFromSlice holds β) : False := by
  classical
  let ξ : Cardinal.{u} := #C ⊔ aleph0
  have hξ : aleph0 ≤ ξ := le_max_right _ _
  obtain ⟨R, _hRinf, hpart, _⟩ := lemma_2_5 ξ aleph0 2 hξ le_rfl (Nat.succ_pos 1)
  let ι : Type u := R.ord.ToType
  have hι : #ι = R := mk_ord_toType _
  have hRι : R ≤ #ι := hι.symm.le
  obtain ⟨u, _hu, hdesc⟩ := ladder_descent_family holds hnone (ι := ι)
  let D := ξ.ord.ToType
  have hD : #D = ξ := mk_ord_toType _
  obtain ⟨emb : C ↪ D⟩ := (le_def C D).mp (by rw [hD]; exact le_max_left _ _)
  let color : {s : Finset ι // s.card = 2} → D :=
    fun s => emb (pairDescentColor u hdesc s)
  obtain ⟨H, hH, d0, hc⟩ := hpart ι hRι D hD color
  have : Infinite ↥H := Cardinal.infinite_iff.mpr (by simpa using hH)
  obtain ⟨f₀, hmono | hanti⟩ := Infinite.exists_strictMono_or_strictAnti ↥H
  · let f : ℕ → ι := fun n => (f₀ n).1
    have hfH (n : ℕ) : f n ∈ H := (f₀ n).2
    have hfmono : StrictMono f := fun n m hnm => Subtype.coe_lt_coe.mpr (hmono hnm)
    have hfm01 : f 0 < f 1 := hfmono Nat.zero_lt_one
    have hsub01 : ∀ x ∈ ({f 0, f 1} : Finset ι), x ∈ H := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> [exact hfH 0; exact hfH 1]
    have hcol01 : color ⟨{f 0, f 1}, card_two_pair (ne_of_lt hfm01)⟩ = d0 :=
      hc _ _ hsub01
    set c₀ : C := pairDescentColor u hdesc ⟨{f 0, f 1}, card_two_pair (ne_of_lt hfm01)⟩
    have hd0 : emb c₀ = d0 := by simpa [color, c₀] using hcol01
    have hantiOrd : StrictAnti (fun n : ℕ => u (f n) c₀) := by
      intro n m hnm
      have hfm : f n < f m := hfmono hnm
      have hsub : ∀ x ∈ ({f n, f m} : Finset ι), x ∈ H := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> [exact hfH n; exact hfH m]
      have hcolor : color ⟨{f n, f m}, card_two_pair (ne_of_lt hfm)⟩ = d0 :=
        hc _ _ hsub
      have hcEq :
          emb (pairDescentColor u hdesc ⟨{f n, f m}, card_two_pair (ne_of_lt hfm)⟩) =
            emb c₀ :=
        hcolor.trans hd0.symm
      have hpc :
          pairDescentColor u hdesc ⟨{f n, f m}, card_two_pair (ne_of_lt hfm)⟩ = c₀ :=
        emb.injective hcEq
      have hEq := pairDescentColor_of_lt u hdesc hfm
      have hmem := firstDescentCoord_mem u (hdesc hfm)
      rw [← hEq, hpc] at hmem
      exact hmem
    exact (not_strictAnti_of_wellFoundedLT (fun n => u (f n) c₀) hantiOrd).elim
  · exact (not_strictAnti_of_wellFoundedLT (fun n => (f₀ n : ι))
      (fun n m hnm => Subtype.coe_lt_coe.mpr (hanti hnm))).elim

/-- **Infra: Type-u witness set.** A definable class of ordinal vectors on a `Type u`
coordinate set is dominated by a `Type u` family. -/
theorem type_u_witness_set {C : Type u} (holds : (C → Ordinal.{u}) → Prop) :
    ∃ (ι : Type u) (v : ι → C → Ordinal.{u}),
      (∀ i, holds (v i)) ∧
      ∀ f, holds f → ∃ i, ∀ c, v i c ≤ f c := by
  classical
  cases isEmpty_or_nonempty C with
  | inl hempty =>
    have : IsEmpty C := hempty
    exact type_u_witness_set_of_isEmpty holds
  | inr hne =>
    -- Move to a canonically well-ordered coordinate type of the same cardinality.
    let D := (#C).ord.ToType
    have hDcard : #D = #C := mk_ord_toType _
    let e : D ≃ C := Classical.choice (Cardinal.eq.mp hDcard)
    let holdsD : (D → Ordinal.{u}) → Prop := holdsCongr e holds
    by_contra hno
    have hnoD :
        ¬ ∃ (ι : Type u) (v : ι → D → Ordinal.{u}),
            (∀ i, holdsD (v i)) ∧
            ∀ f, holdsD f → ∃ i, ∀ d, v i d ≤ f d := by
      intro ⟨ι, v, hv, hdom⟩
      apply hno
      refine ⟨ι, fun i => (v i) ∘ e.symm, fun i => ?_, fun f hf => ?_⟩
      · simpa [holdsD, holdsCongr] using hv i
      · have hfD : holdsD (f ∘ e) := by
          simpa [holdsD, holdsCongr, Function.comp_assoc, e.symm_comp_self] using hf
        obtain ⟨i, hi⟩ := hdom (f ∘ e) hfD
        exact ⟨i, fun c => by simpa [Function.comp] using hi (e.symm c)⟩
    have hnone := not_generates_of_no_type_u_witnesses holdsD hnoD
    have : Nonempty D := by
      rw [← Cardinal.mk_ne_zero_iff, hDcard, Cardinal.mk_ne_zero_iff]
      exact hne
    exact not_none_generates holdsD hnone

/-- Parameterized form used by `lemma_4_7`. -/
theorem type_u_witness_set_param {C parameter : Type u}
    (holds : parameter → (C → Ordinal.{u}) → Prop) (a : parameter) :
    ∃ (ι : Type u) (v : ι → C → Ordinal.{u}),
      (∀ i, holds a (v i)) ∧
      ∀ f, holds a f → ∃ i, ∀ c, v i c ≤ f c :=
  type_u_witness_set (holds a)

end
end AEC
