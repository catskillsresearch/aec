module

public import AEC.Audit.AllSetsMinimal

@[expose] public section

/-!
# A `MinimalData` with no independent pairs (statement audit)

`noPairs` is `setsMinimal` with `productCopies` restricted to `[]` and realized singletons.
All `MinimalData` axioms still hold, but no two points are independent, so the closure of one
point is the whole point set. This refutes Theorem 10.5 (closure cardinality bound) as stated.
-/

namespace AEC
namespace Audit

universe u

open FirstOrder Cardinal

set_option linter.deprecated false
set_option linter.unusedVariables false

/-- `setsMinimal` without independent pairs. -/
noncomputable abbrev noPairs : MinimalData allSetsAEC.{u} :=
  { setsMinimal.{u} with
    productCopies := fun M f l => l = [] ∨ ∃ a, l = [a] ∧ a ∉ Set.range f
    singleton := fun M f a => by
      constructor
      · rintro (h | ⟨b, hb, hr⟩)
        · cases h
        · cases hb; exact hr
      · intro h; exact Or.inr ⟨a, rfl, h⟩
    empty := fun _ _ => Or.inl rfl }

theorem noPairs_length {M : Model allSetsAEC.{u}.τ} {f} {l : List M.carrier}
    (h : noPairs.{u}.productCopies M f l) : l.length ≤ 1 := by
  rcases h with rfl | ⟨a, rfl, -⟩ <;> simp

/-- The countable section of `M` spanned by the copy of `ℕ` and a finite list. -/
def sectionOf (M : Model allSetsAEC.{u}.τ)
    (incl : Language.Embedding allSetsAEC.{u}.τ natModel.{u}.carrier M.carrier)
    (ys : List M.carrier) : Model allSetsAEC.{u}.τ :=
  ⟨{z : M.carrier // z ∈ Set.range incl ∨ z ∈ ys}, eStr _⟩

theorem card_sectionOf (M : Model allSetsAEC.{u}.τ)
    (incl : Language.Embedding allSetsAEC.{u}.τ natModel.{u}.carrier M.carrier)
    (ys : List M.carrier) : Model.card (sectionOf M incl ys) = ℵ₀ := by
  apply le_antisymm
  · have : Countable natModel.{u}.carrier := inferInstanceAs (Countable (ULift.{u} ℕ))
    have hc : (Set.range incl ∪ {z | z ∈ ys}).Countable :=
      (Set.countable_range _).union (ys.finite_toSet.countable)
    exact hc.le_aleph0
  · have : Function.Injective (fun n : natModel.{u}.carrier =>
        (⟨incl n, Or.inl ⟨n, rfl⟩⟩ : {z : M.carrier // z ∈ Set.range incl ∨ z ∈ ys})) :=
      fun a b h => incl.injective (congrArg Subtype.val h)
    have h1 := Cardinal.mk_le_of_injective this
    have h2 : #natModel.{u}.carrier = ℵ₀ := card_natModel
    exact h2 ▸ h1

/-- Under `noPairs`, no list of length `≥ 2` is independent. -/
theorem noPairs_not_indep (M : Model allSetsAEC.{u}.τ)
    (incl : Language.Embedding allSetsAEC.{u}.τ natModel.{u}.carrier M.carrier)
    (ys : List M.carrier) (hlen : 2 ≤ ys.length) :
    ¬ FiniteIndependent noPairs.{u} M incl ys := by
  intro hI
  let N := sectionOf M incl ys
  let f0 := embOf (M := natModel) (N := N) (fun n => ⟨incl n, Or.inl ⟨n, rfl⟩⟩)
    (fun a b h => incl.injective (congrArg Subtype.val h))
  let g := embOf (M := N) (N := M) Subtype.val Subtype.val_injective
  let ys' : List N.carrier := ys.attach.map (fun z => ⟨z.1, Or.inr z.2⟩)
  have hmap : ys'.map g = ys := by
    exact List.map_map.trans (List.attach_map_subtype_val ys)
  have h := hI.product N f0 g ys' trivial trivial trivial (card_sectionOf M incl ys)
    (Language.Embedding.ext fun n => rfl) hmap
  have := noPairs_length h
  have hl : ys'.length = ys.length := by rw [← hmap, List.length_map]
  omega

/-- Under `noPairs`, a single point is independent. -/
theorem noPairs_indep_single (M : Model allSetsAEC.{u}.τ)
    (incl : Language.Embedding allSetsAEC.{u}.τ natModel.{u}.carrier M.carrier)
    (p : M.carrier) (hp : p ∉ Set.range incl) :
    FiniteIndependent noPairs.{u} M incl [p] where
  nodup := List.nodup_singleton p
  inP a ha := by
    rw [List.mem_singleton] at ha
    subst ha
    exact (inPointSet_iff M incl a).mpr hp
  product N f g ys _ _ _ _ hgf hys := by
    match ys, hys with
    | [b], hb =>
      refine Or.inr ⟨b, rfl, ?_⟩
      rintro ⟨n, rfl⟩
      apply hp
      refine ⟨n, ?_⟩
      have h1 : g (f n) = p := by simpa using hb
      rw [← h1]
      exact (congrArg (fun e => e n) (congrArg DFunLike.coe hgf)).symm

theorem two_le_length_of_mem {α : Type*} {l : List α} {x p : α} (hx : x ∈ l) (hp : p ∈ l)
    (hne : x ≠ p) : 2 ≤ l.length := by
  match l, hx, hp with
  | [], hx, _ => simp at hx
  | [a], hx, hp => simp at hx hp; exact absurd (hx.trans hp.symm) hne
  | _ :: _ :: _, _, _ => simp

/-- Under `noPairs`, one point spans every element in the closure. -/
theorem noPairs_mem_closure (M : Model allSetsAEC.{u}.τ)
    (incl : Language.Embedding allSetsAEC.{u}.τ natModel.{u}.carrier M.carrier)
    (p : M.carrier) (hp : p ∉ Set.range incl) (x : M.carrier) :
    InClosure (fun s => ∃ ys : List M.carrier,
        FiniteIndependent noPairs.{u} M incl ys ∧ ∀ z, z ∈ s ↔ z ∈ ys) {p} x := by
  refine ⟨{p}, subset_rfl, Set.finite_singleton p, {p}, ⟨subset_rfl,
    ⟨[p], noPairs_indep_single M incl p hp, fun z => by simp⟩, ?_⟩, ?_⟩
  · intro y hy hIE
    exact hIE.1 hy
  · rintro ⟨hx, ys, hI, hys⟩
    have hxne : x ≠ p := fun h => hx (h ▸ rfl)
    exact noPairs_not_indep M incl ys
      (two_le_length_of_mem ((hys x).mp (Set.mem_insert _ _))
        ((hys p).mp (Set.mem_insert_of_mem _ rfl)) hxne) hI

/-- Theorem 10.5 as stated is false: with `noPairs`, the closure of one point in a model of
size `ℵ₁` is uncountable. -/
theorem theorem_10_5_false :
    ¬ ∀ (K : AbstractElementaryClass.{u}) (D : MinimalData K)
      (M : Model K.τ) (incl : Language.Embedding K.τ D.M0.carrier M.carrier)
      (hM : K.Mem M) (hstrong : K.Strong incl) (hcard : D.lam0 ≤ Model.card M),
      (∀ (F : Set M.carrier), F.Finite →
        ∀ x, InClosure (fun s => ∃ ys : List M.carrier,
          FiniteIndependent D M incl ys ∧ ∀ z, z ∈ s ↔ z ∈ ys) F x →
          ∃ t : Set M.carrier, t.Finite ∧ x ∈ t ∧ #t ≤ D.lam0) ∧
      (∀ F : Set M.carrier,
        #{x | InClosure (fun s => ∃ ys : List M.carrier,
          FiniteIndependent D M incl ys ∧ ∀ z, z ∈ s ↔ z ∈ ys) F x} ≤ #F + D.lam0) := by
  intro H
  let T := (Order.succ ℵ₀ : Cardinal.{u}).ord.ToType
  have hT : #T = Order.succ ℵ₀ := Cardinal.mk_ord_toType _
  let A := ptd.{u} T
  have hne : Nonempty T := by
    rw [← Cardinal.mk_ne_zero_iff, hT]; exact (lt_of_le_of_lt (zero_le (a := ℵ₀)) (Order.lt_succ ℵ₀)).ne'
  let p : A.M.carrier := Sum.inr hne.some
  have hp : p ∉ Set.range A.copy := fun ⟨n, hn⟩ => Sum.inl_ne_inr hn
  have hcard : noPairs.{u}.lam0 ≤ Model.card A.M := by
    show ℵ₀ ≤ #(ULift.{u} ℕ ⊕ T)
    rw [Cardinal.mk_sum]
    simp
  have h2 := (H allSetsAEC noPairs A.M A.copy trivial trivial hcard).2 {p}
  have hsub : Set.range (fun t : T => (Sum.inr t : A.M.carrier)) ⊆
      {x | InClosure (fun s => ∃ ys : List A.M.carrier,
        FiniteIndependent noPairs A.M A.copy ys ∧ ∀ z, z ∈ s ↔ z ∈ ys) {p} x} :=
    fun x _ => noPairs_mem_closure A.M A.copy p hp x
  have h3 : #T ≤ #{x | InClosure (fun s => ∃ ys : List A.M.carrier,
        FiniteIndependent noPairs A.M A.copy ys ∧ ∀ z, z ∈ s ↔ z ∈ ys) {p} x} := by
    have := Cardinal.mk_le_mk_of_subset hsub
    rwa [Cardinal.mk_range_eq _ Sum.inr_injective] at this
  have h4 : #({p} : Set A.M.carrier) + noPairs.{u}.lam0 = ℵ₀ := by
    show #({p} : Set A.M.carrier) + ℵ₀ = ℵ₀
    rw [Cardinal.mk_singleton]
    exact Cardinal.add_eq_right le_rfl one_le_aleph0
  have := (h3.trans h2).trans h4.le
  rw [hT] at this
  exact absurd this (not_le.mpr (Order.lt_succ _))

/-- A point outside `{p}` and the copy of `ℕ` is not forced by `{p}` (any `MinimalData` on the
AEC of all sets with `M₀ = ℕ`, `λ₀ = ℵ₀`; here `noPairs`). -/
theorem noPairs_not_forces (M : Model allSetsAEC.{u}.τ)
    (incl : Language.Embedding allSetsAEC.{u}.τ natModel.{u}.carrier M.carrier)
    (p q : M.carrier) (hq : q ∉ Set.range incl) (hqp : q ≠ p) :
    ¬ Forces noPairs.{u} M incl {y | y ∈ [p]} q := by
  intro hF
  let N := sectionOf M incl [q, p]
  let f0 : Language.Embedding allSetsAEC.{u}.τ natModel.{u}.carrier N.carrier :=
    embOf (M := natModel) (N := N) (fun n => ⟨incl n, Or.inl ⟨n, rfl⟩⟩)
      (fun a b h => incl.injective (congrArg Subtype.val h))
  let g : Language.Embedding allSetsAEC.{u}.τ N.carrier M.carrier :=
    embOf (M := N) (N := M) Subtype.val Subtype.val_injective
  let b : N.carrier := ⟨q, Or.inr (by simp)⟩
  let pN : N.carrier := ⟨p, Or.inr (by simp)⟩
  let Dm := sectionOf N f0 [pN]
  let d0 : Language.Embedding allSetsAEC.{u}.τ natModel.{u}.carrier Dm.carrier :=
    embOf (M := natModel) (N := Dm) (fun n => ⟨f0 n, Or.inl ⟨n, rfl⟩⟩)
    (fun a b h => f0.injective (congrArg Subtype.val h))
  let dW : Language.Embedding allSetsAEC.{u}.τ Dm.carrier N.carrier :=
    embOf (M := Dm) (N := N) Subtype.val Subtype.val_injective
  obtain ⟨d, hd⟩ := hF N g f0 b trivial trivial trivial (card_sectionOf M incl _)
    (Language.Embedding.ext fun n => rfl) rfl
    (fun a ha => ⟨pN, by simp at ha; exact ha.symm⟩)
    N (Language.Embedding.refl _ _) Dm d0 dW trivial trivial trivial trivial
    (card_sectionOf M incl _) (card_sectionOf N f0 _)
    (Language.Embedding.ext fun n => rfl)
    (fun a ha c hc => ⟨⟨c, Or.inr (by
      simp at ha
      have : c = pN := Subtype.ext (hc.trans ha)
      simp [this])⟩, rfl⟩)
  rcases d.2 with ⟨n, hn⟩ | hmem
  · apply hq
    refine ⟨n, ?_⟩
    have := congrArg Subtype.val (hn.trans hd)
    exact this
  · simp at hmem
    apply hqp
    have := congrArg Subtype.val (hmem.symm.trans hd)
    exact this.symm

/-- Lemma 10.4 as stated is false (`noPairs`): `{p}` does not force a second point `q`, but
`q` does not independently extend `{p}`. -/
theorem lemma_10_4_false :
    ¬ ∀ (K : AbstractElementaryClass.{u}) (D : MinimalData K)
      (M : Model K.τ) (incl : Language.Embedding K.τ D.M0.carrier M.carrier)
      (xs : List M.carrier) (x : M.carrier) (hI : FiniteIndependent D M incl xs),
      ¬ Forces D M incl {y | y ∈ xs} x ↔
        IndependentlyExtends (fun s => ∃ ys : List M.carrier,
          FiniteIndependent D M incl ys ∧ ∀ z, z ∈ s ↔ z ∈ ys) x {y | y ∈ xs} := by
  intro H
  let A := ptd.{u} (ULift.{u} Bool)
  let p : A.M.carrier := Sum.inr ⟨false⟩
  let q : A.M.carrier := Sum.inr ⟨true⟩
  have hp : p ∉ Set.range A.copy := fun ⟨n, hn⟩ => Sum.inl_ne_inr hn
  have hq : q ∉ Set.range A.copy := fun ⟨n, hn⟩ => Sum.inl_ne_inr hn
  have hqp : q ≠ p := fun h => Bool.noConfusion (congrArg ULift.down (Sum.inr_injective h))
  obtain ⟨-, ys, hI, hys⟩ := (H allSetsAEC noPairs A.M A.copy [p] q
    (noPairs_indep_single A.M A.copy p hp)).mp (noPairs_not_forces A.M A.copy p q hq hqp)
  exact noPairs_not_indep A.M A.copy ys
    (two_le_length_of_mem ((hys q).mp (Set.mem_insert _ _))
      ((hys p).mp (Set.mem_insert_of_mem _ (by simp))) hqp) hI

end Audit
end AEC
