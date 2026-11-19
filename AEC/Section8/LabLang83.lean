module

public import AEC.Section2.OrderPresentation

/-!
# Lemma 8.3: the old template labels as function symbols

"The language of the samples contains the labels of the old template."  For an order
presentation `E`, each label `a` of arity `n` becomes an `n`-ary function symbol; on `E(I)` it
sends the skeleton entries at increasing positions `p` to the realization of `(a, p)` (and any
other tuple to its first entry).  Every element of `E(I)` is a label value on skeleton
elements, so the skeleton generates `E(I)` in the label language.
-/

@[expose] public section

namespace AEC
namespace Lab83

universe u

open FirstOrder FirstOrder.Language

variable {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)

/-- The label language of an order presentation. -/
def labLang : Language.{u, u} where
  Functions n := {a : E.lab // E.arity a = n}
  Relations _ := PEmpty

variable {E} {I : Type u} [LinearOrder I] [Nonempty I]

open Classical in
/-- The interpretation of a label symbol on `E(I)`. -/
noncomputable def labFun {n : ℕ} (a : (labLang E).Functions n) (x : Fin n → (E.obj I).carrier) :
    (E.obj I).carrier :=
  if h : ∃ p : Fin n → I, StrictMono p ∧ ∀ k, E.skeleton (p k) = x k then
    E.realize ⟨a.1, fun k => h.choose (Fin.cast a.2 k),
      fun _ _ hkl => h.choose_spec.1 (show Fin.cast a.2 _ < Fin.cast a.2 _ from hkl)⟩
  else x ⟨0, a.2 ▸ E.arity_pos a.1⟩

/-- The label structure on `E(I)`. -/
@[instance_reducible]
noncomputable def labStr : (labLang E).Structure (E.obj I).carrier where
  funMap := fun a x => labFun a x
  RelMap := fun r => PEmpty.elim r

/-- **Labels realize support terms on the skeleton.** -/
theorem labFun_skeleton (t : SupportTerm E.lab E.arity I) :
    labFun (n := E.arity t.label) ⟨t.label, rfl⟩ (fun k => E.skeleton (t.pos k)) = E.realize t := by
  have h : ∃ p : Fin (E.arity t.label) → I, StrictMono p ∧
      ∀ k, E.skeleton (p k) = E.skeleton (t.pos k) := ⟨t.pos, t.increasing, fun _ => rfl⟩
  unfold labFun
  rw [dif_pos h]
  have hp : h.choose = t.pos := funext fun k => E.skeleton.injective (h.choose_spec.2 k)
  congr 1
  exact SupportTerm.ext_of_label_eq rfl fun k => by simp [hp]

/-- **The skeleton generates `E(I)` in the label language.** -/
theorem exists_label_value (x : (E.obj I).carrier) :
    ∃ (n : ℕ) (a : (labLang E).Functions n) (p : Fin n → I), StrictMono p ∧
      labFun a (fun k => E.skeleton (p k)) = x := by
  obtain ⟨t, rfl⟩ := E.realize_surjective x
  exact ⟨_, ⟨t.label, rfl⟩, t.pos, t.increasing, labFun_skeleton t⟩

end Lab83
end AEC
