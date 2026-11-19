module

public import AEC.Section8.LSPairLang83

/-!
# Lemma 8.3: adding a retraction-evaluation symbol to the LS language

"Include a sort of retraction indices and an evaluation function for a family `r_i : Y → X`."
We add one binary function symbol `ret` to `lsLang K`.  Any interpretation keeps the hulls
strong (`LS83.hullStrong_exp`), and an interpretation preserving the closed sorts keeps them
closed under all functions of the larger language.
-/

@[expose] public section

namespace AEC
namespace LS83

universe u

open FirstOrder FirstOrder.Language Cardinal Hull83

variable {K : AbstractElementaryClass.{u}}

/-- One binary function symbol. -/
def retSym : Language.{u, u} where
  Functions n := match n with
    | 2 => PUnit
    | _ => PEmpty
  Relations _ := PEmpty

/-- The LS language with the retraction-evaluation symbol. -/
abbrev retLang (K : AbstractElementaryClass.{u}) : Language.{u, u} := (lsLang K).sum retSym

/-- Interpretation of `ret` by a binary operation. -/
@[instance_reducible]
def retStr {N : Type u} (g : N → N → N) : retSym.Structure N where
  funMap := fun {n} f x => match n, f with
    | 2, _ => g (x 0) (x 1)
  RelMap := fun r => PEmpty.elim r

/-- The expansion of an `lsLang K`-structure by `ret`. -/
@[instance_reducible]
noncomputable def retExp {N : Type u} (str : (lsLang K).Structure N) (g : N → N → N) :
    (retLang K).Structure N :=
  @Language.sumStructure _ _ _ str (retStr g)

/-- The `lsLang K`-reduct of the expansion is the original structure. -/
theorem retExp_reduct {N : Type u} (str : (lsLang K).Structure N) (g : N → N → N) :
    @LHom.reduct _ _ (LHom.sumInl : lsLang K →ᴸ retLang K) N (retExp str g) = str := rfl

/-- **Hulls stay strong after adding `ret`.** -/
theorem hullStrong_ret :
    HullStrong ((LHom.sumInl : lsLang K →ᴸ retLang K).comp (lsInl K))
      (fun N _ => @LSClosed K N ((LHom.sumInl : lsLang K →ᴸ retLang K).reduct N)) :=
  hullStrong_exp _

/-- **Closed sorts stay closed** if `ret` preserves them. -/
theorem retExp_closed {N : Type u} (str : (lsLang K).Structure N) (g : N → N → N) {R : Set N}
    (hR : ∀ {n} (f : (lsLang K).Functions n) (x : Fin n → N), (∀ i, x i ∈ R) →
      @Structure.funMap _ N str n f x ∈ R)
    (hg : ∀ a b, a ∈ R → b ∈ R → g a b ∈ R) {n : ℕ} (f : (retLang K).Functions n)
    (x : Fin n → N) (hx : ∀ i, x i ∈ R) :
    @Structure.funMap _ N (retExp str g) n f x ∈ R := by
  rcases f with f | f
  · exact hR f x hx
  · match n, f with
    | 2, _ => exact hg _ _ (hx 0) (hx 1)

/-- Code a `retSym` symbol (there is exactly one). -/
def retCode : (retSym : Language.{u, u}).Symbols → PUnit.{u + 1}
  | _ => PUnit.unit

theorem retCode_injective : Function.Injective retCode := by
  rintro (⟨n, f⟩ | ⟨_, r⟩) (⟨m, g⟩ | ⟨_, r'⟩) -
  · match n, f, m, g with
    | 2, _, 2, _ => rfl
  · exact PEmpty.elim r'
  · exact PEmpty.elim r
  · exact PEmpty.elim r

/-- **The retraction-expanded language has at most `LS(K)` function symbols.** -/
theorem retLang_functions_le : max ℵ₀ #(Σ i, (retLang K).Functions i) ≤ ls K := by
  have hall : ℵ₀ ≤ ls K := (isLSBound_ls K).1
  have hret : (retSym : Language.{u, u}).card ≤ ls K :=
    (mk_le_of_injective retCode_injective).trans (by simpa using one_le_aleph0.trans hall)
  have hcard : (retLang K).card ≤ ls K := by
    rw [Language.card_sum, lift_id, lift_id]
    exact (add_le_add lsLang_card_le hret).trans (by rw [add_eq_max hall, max_self])
  refine max_le hall (le_trans ?_ hcard)
  exact mk_le_of_injective (f := fun a : (Σ i, (retLang K).Functions i) =>
    (Sum.inl a : (retLang K).Symbols)) Sum.inl_injective
