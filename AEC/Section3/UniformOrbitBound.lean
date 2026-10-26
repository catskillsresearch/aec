import AEC.Section3.Results
import AEC.Section2.SmallModel

namespace AEC
universe u

open FirstOrder Cardinal

structure CanonicalRecord (lab : Type u) (arity : lab → ℕ) (θ : Cardinal.{u}) where
  idx : Set (Below θ)
  slt : Set (Below θ)
  label : ↥idx → lab
  arg : ∀ i, Fin (arity (label i)) → ↥slt
  lt : ↥slt → ↥slt → Prop
  arg_strict : ∀ i {a b : Fin (arity (label i))}, a < b → lt (arg i a) (arg i b)
  arg_surj : ∀ x : ↥slt, ∃ i, ∃ a, arg i a = x
  occupied : Set (↥slt) → Set (↥slt) → Prop

def CanonicalRecord.toOrbitRecord {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (r : CanonicalRecord lab arity θ) : OrbitRecord lab arity where
  index := ↥r.idx
  slot := ↥r.slt
  label := r.label
  arg := r.arg
  lt := r.lt
  arg_strict := r.arg_strict
  arg_surj := r.arg_surj
  occupied := r.occupied

theorem canonical_record_card_index {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (r : CanonicalRecord lab arity θ) :
    # ((CanonicalRecord.toOrbitRecord r).index) ≤ θ := by
  dsimp [CanonicalRecord.toOrbitRecord]
  have h := Cardinal.mk_subtype_le r.idx
  rw [mk_ord_toType] at h
  exact h

theorem canonical_record_card_slot {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (r : CanonicalRecord lab arity θ) :
    # ((CanonicalRecord.toOrbitRecord r).slot) ≤ θ := by
  dsimp [CanonicalRecord.toOrbitRecord]
  have h := Cardinal.mk_subtype_le r.slt
  rw [mk_ord_toType] at h
  exact h

theorem fin_cast_arg_rec {lab : Type u} {arity : lab → ℕ} {index slot : Type u}
    (label : index → lab) (arg : ∀ i, Fin (arity (label i)) → slot)
    (i j : index) (h : i = j) (a : Fin (arity (label i))) :
    arg i a = arg j (Fin.cast (congrArg arity (congrArg label h)) a) := by
  subst h
  rfl

theorem canonical_record_covers {lab : Type u} {arity : lab → ℕ} {θ : Cardinal.{u}}
    (rec : OrbitRecord lab arity) (hidx : # rec.index ≤ θ) (hslt : # rec.slot ≤ θ) :
    ∃ r : CanonicalRecord lab arity θ, OrbitRecord.Same rec (CanonicalRecord.toOrbitRecord r) := by
  have h_below : # (Below θ) = θ := mk_ord_toType θ
  have h_idx_le : # rec.index ≤ # (Below θ) := by rw [h_below]; exact hidx
  have h_slt_le : # rec.slot ≤ # (Below θ) := by rw [h_below]; exact hslt
  rw [le_def] at h_idx_le h_slt_le
  obtain ⟨e_idx⟩ := h_idx_le
  obtain ⟨e_slt⟩ := h_slt_le
  let idx : Set (Below θ) := Set.range e_idx
  let slt : Set (Below θ) := Set.range e_slt
  let e_i : rec.index ≃ ↥idx := Equiv.ofInjective e_idx.1 e_idx.2
  let e_s : rec.slot ≃ ↥slt := Equiv.ofInjective e_slt.1 e_slt.2
  have he_i_symm_apply (i : rec.index) : e_i.symm (e_i i) = i := e_i.symm_apply_apply i
  have he_s_symm_apply (s : rec.slot) : e_s.symm (e_s s) = s := e_s.symm_apply_apply s
  let r : CanonicalRecord lab arity θ := {
    idx := idx
    slt := slt
    label := fun i => rec.label (e_i.symm i)
    arg := fun i a => e_s (rec.arg (e_i.symm i) a)
    lt := fun a b => rec.lt (e_s.symm a) (e_s.symm b)
    arg_strict := fun i a b hab => by
      rw [he_s_symm_apply, he_s_symm_apply]
      exact rec.arg_strict (e_i.symm i) hab
    arg_surj := fun x => by
      obtain ⟨i, a, ha⟩ := rec.arg_surj (e_s.symm x)
      have hcast : i = e_i.symm (e_i i) := (he_i_symm_apply i).symm
      refine ⟨e_i i, Fin.cast (congrArg arity (congrArg rec.label hcast)) a, ?_⟩
      have h_app := fin_cast_arg_rec rec.label rec.arg i (e_i.symm (e_i i)) hcast a
      rw [← h_app, ha, Equiv.apply_symm_apply]
    occupied := fun lower upper => rec.occupied (e_s.symm '' lower) (e_s.symm '' upper)
  }
  have hlabel : ∀ i, rec.label i = (CanonicalRecord.toOrbitRecord r).label (e_i i) := by
    intro i
    change rec.label i = rec.label (e_i.symm (e_i i))
    rw [he_i_symm_apply]
  refine ⟨r, e_i, e_s, hlabel, ?_, ?_, ?_⟩
  · intro a b
    change rec.lt a b ↔ rec.lt (e_s.symm (e_s a)) (e_s.symm (e_s b))
    rw [he_s_symm_apply, he_s_symm_apply]
  · intro i a
    change e_s (rec.arg i a) = e_s (rec.arg (e_i.symm (e_i i)) (Fin.cast (congrArg arity (hlabel i)) a))
    congr 1
    have he : i = e_i.symm (e_i i) := (he_i_symm_apply i).symm
    exact fin_cast_arg_rec rec.label rec.arg i (e_i.symm (e_i i)) he a
  · intro lower upper
    change rec.occupied lower upper ↔ rec.occupied (e_s.symm '' (e_s '' lower)) (e_s.symm '' (e_s '' upper))
    have h1 : e_s.symm '' (e_s '' lower) = lower := by
      rw [← Set.image_comp, Equiv.symm_comp_self, Set.image_id]
    have h2 : e_s.symm '' (e_s '' upper) = upper := by
      rw [← Set.image_comp, Equiv.symm_comp_self, Set.image_id]
    rw [h1, h2]

/-- An order isomorphism induces an isomorphism of models in an order presentation. -/
def orderPresentationMapEquiv {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (e : I ≃o J) : (E.obj I).carrier ≃[K.τ] (E.obj J).carrier where
  toFun := E.map e.toOrderEmbedding
  invFun := E.map e.symm.toOrderEmbedding
  left_inv x := by
    have hcomp := E.map_comp e.toOrderEmbedding e.symm.toOrderEmbedding
    have htrans : e.toOrderEmbedding.trans e.symm.toOrderEmbedding = (OrderIso.refl I).toOrderEmbedding := by
      ext; exact e.symm_apply_apply _
    rw [htrans, E.map_id] at hcomp
    have h_app := congrFun (congrArg (⇑) hcomp.symm) x
    simp only [Language.Embedding.comp_apply, Language.Embedding.refl_apply] at h_app
    exact h_app
  right_inv y := by
    have hcomp := E.map_comp e.symm.toOrderEmbedding e.toOrderEmbedding
    have htrans : e.symm.toOrderEmbedding.trans e.toOrderEmbedding = (OrderIso.refl J).toOrderEmbedding := by
      ext; exact e.apply_symm_apply _
    rw [htrans, E.map_id] at hcomp
    have h_app := congrFun (congrArg (⇑) hcomp.symm) y
    simp only [Language.Embedding.comp_apply, Language.Embedding.refl_apply] at h_app
    exact h_app
  map_fun' {n} f xs := (E.map e.toOrderEmbedding).map_fun' f xs
  map_rel' {n} r xs := (E.map e.toOrderEmbedding).map_rel' r xs

theorem orderPresentationMapEquiv_strong {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)
    {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (e : I ≃o J) : K.Strong (orderPresentationMapEquiv E e).toEmbedding := by
  have heq : (orderPresentationMapEquiv E e).toEmbedding = E.map e.toOrderEmbedding := by
    ext x; rfl
end AEC
