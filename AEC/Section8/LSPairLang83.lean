module

public import AEC.Section8.LSNested83

/-!
# Lemma 8.3: LS-closed structures in further expansions

The pair language of Lemma 8.3 extends the LS witness language `lsLang K` by further symbols
(template labels, retractions, ...).  Substructures in the larger language are closed under the
witness functions, so `HullStrong` passes to every further expansion; and the term hull of a
tuple from a set closed under all functions stays inside that set (sorts `X ⊆ Y ⊆ L`).
-/

@[expose] public section

namespace AEC
namespace LS83

universe u

open FirstOrder FirstOrder.Language Cardinal Hull83

variable {K : AbstractElementaryClass.{u}} {L' : Language.{u, u}} (ψ : lsLang K →ᴸ L')

/-- An `L'`-substructure is closed under the functions of `lsLang K` (via `ψ`). -/
def subOfExp {N : Type u} [L'.Structure N] (A : L'.Substructure N) :
    @Substructure (lsLang K) N (ψ.reduct N) :=
  letI := ψ.reduct N
  { carrier := A
    fun_mem := fun f x hx => A.fun_mem (ψ.onFunction f) x hx }

/-- **LS-closed reducts give hull-strong expansions.**  If the `lsLang K`-reduct of an
`L'`-structure is LS-closed, then the term hull (in `L'`) of every nonempty finite tuple has
strong `τ(K)`-reduct. -/
theorem hullStrong_exp :
    HullStrong (ψ.comp (lsInl K)) (fun N _ => @LSClosed K N (ψ.reduct N)) := by
  refine hullStrong_of_substructures _ fun N _ h A hA => ?_
  let _ := ψ.reduct N
  exact h.2 (subOfExp ψ A) hA

variable {L : Language.{u, u}}

/-- **Hulls stay in closed sets.**  The term hull of a tuple from a set closed under all
functions lies in that set. -/
theorem hull_range_sub {N : Type u} [L.Structure N] {ι : Type} (v : ι → N) {R : Set N}
    (hR : ∀ {n} (f : L.Functions n) (x : Fin n → N), (∀ i, x i ∈ R) → Structure.funMap f x ∈ R)
    (hv : ∀ i, v i ∈ R) : Set.range (hullEmb (L := L) v) ⊆ R := by
  rintro _ ⟨t, rfl⟩
  induction t using Quotient.inductionOn with
  | h t =>
    show t.realize v ∈ R
    induction t with
    | var i => exact hv i
    | func f ts ih => exact hR f _ ih
