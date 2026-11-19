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

/-- The function symbols of `lsLang K` number at most `LS(K)`. -/
theorem lsLang_functions_le : max ℵ₀ #(Σ i, (lsLang K).Functions i) ≤ ls K := by
  refine max_le (isLSBound_ls K).1 (le_trans ?_ lsLang_card_le)
  exact mk_le_of_injective (f := fun a : (Σ i, (lsLang K).Functions i) =>
    (Sum.inl a : (lsLang K).Symbols)) Sum.inl_injective

/-- Arbitrarily large models of `K` give arbitrarily large LS-closed expansions. -/
theorem large_lsClosed
    (hlarge : ∀ κ : Cardinal.{u}, ∃ M : Model K.τ, K.Mem M ∧ κ ≤ Model.card M) (κ : Cardinal.{u}) :
    ∃ (N : Type u) (_ : (lsLang K).Structure N), LSClosed (K := K) N ∧ κ ≤ #N := by
  obtain ⟨M, hM, hκ⟩ := hlarge κ
  obtain ⟨str, -, hcl⟩ := exists_ls_expansion M hM
  exact ⟨M.carrier, str, hcl, hκ⟩

/-- **An Ehrenfeucht–Mostowski presentation from the LS witness expansion** (the single-sort
case of the Lemma 8.3 construction, Shelah's presentation route).  If `K` has arbitrarily large
models, coherent types of the LS-closed expansions give an order presentation of `K` whose
models are the direct limits of the hull pieces. -/
theorem exists_ls_tp_presentation
    (hlarge : ∀ κ : Cardinal.{u}, ∃ M : Model K.τ, K.Mem M ∧ κ ≤ Model.card M) :
    ∃ (c : (m : ℕ) → 0 < m → TpColor (lsLang K) m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSample (fun N _ => LSClosed (K := K) N)) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = tpRes f (c m hm)),
      ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        (tpPresentation hc hcoh hullStrong_lsClosed lsLang_functions_le).obj I =
          ((tpFinPieces hc hcoh hullStrong_lsClosed).limit I).obj :=
  exists_tp_presentation (large_lsClosed hlarge) hullStrong_lsClosed lsLang_functions_le
