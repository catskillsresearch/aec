module

public import AEC.Section8.PairLangR83

/-!
# Lemma 8.3: chart relations (skeleton predicates and chart orders)

A purely relational language recording which elements are chart (skeleton) points of `X` and
of `Y`, and the chart orders between them.  Relations do not change term hulls, but they are
recorded in the hull types, so a homogeneous witness bundle carries the chart of each hull and
its order (needed to read `X_H = F(J_H)`, `Y_H ≅ F(Z_H)` and the order-saturation demand off
the colors).
-/

@[expose] public section

universe u

open FirstOrder FirstOrder.Language Cardinal

namespace AEC
namespace Lab83

/-- Chart relations: unary `isChart_s` and binary `chartLt_s` for the two sorts `s : Fin 2`. -/
def chartLang : Language.{u, u} where
  Functions _ := PEmpty
  Relations n := {_s : ULift.{u} (Fin 2) // n = 1} ⊕ {_s : ULift.{u} (Fin 2) // n = 2}

variable {K : AbstractElementaryClass.{u}} {E : OrderPresentation K}
  {J Z Jp : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Z] [Nonempty Z]
  [LinearOrder Jp] [Nonempty Jp]

open Classical in
/-- Interpretation on `L = E(J⁺)`: sort `0` is the `X`-chart `skeleton ∘ emb`, sort `1` the
`Y`-chart `e ∘ skeleton`, each with its chart order. -/
@[instance_reducible]
noncomputable def chartStr (emb : J ↪o Jp) (e : (E.obj Z).carrier → (E.obj Jp).carrier) :
    (chartLang.{u}).Structure (E.obj Jp).carrier where
  funMap := fun f => PEmpty.elim f
  RelMap := fun {n} r x => match r with
    | Sum.inl ⟨⟨s⟩, h⟩ =>
      if s = 0 then ∃ j, E.skeleton (emb j) = x ⟨0, by omega⟩
      else ∃ z, e (E.skeleton z) = x ⟨0, by omega⟩
    | Sum.inr ⟨⟨s⟩, h⟩ =>
      if s = 0 then ∃ j j', j < j' ∧ E.skeleton (emb j) = x ⟨0, by omega⟩ ∧
        E.skeleton (emb j') = x ⟨1, by omega⟩
      else ∃ z z', z < z' ∧ e (E.skeleton z) = x ⟨0, by omega⟩ ∧
        e (E.skeleton z') = x ⟨1, by omega⟩

/-- `chartLang` has no function symbols. -/
theorem chartLang_functions : #(Σ i, (chartLang.{u}).Functions i) = 0 := by
  rw [Cardinal.mk_eq_zero_iff]
  exact ⟨fun ⟨_, f⟩ => PEmpty.elim f⟩

end Lab83
namespace LS83

open Hull83

variable {K : AbstractElementaryClass.{u}} (E : OrderPresentation K)

/-- The full language with chart relations. -/
abbrev pairLangR4 : Language.{u, u} := (pairLangR3 E).sum Lab83.chartLang

abbrev pairInlR4 : lsLang K →ᴸ pairLangR4 E :=
  (LHom.sumInl : pairLangR3 E →ᴸ pairLangR4 E).comp (pairInlR3 E)

theorem hullStrong_pairR4 :
    HullStrong ((pairInlR4 E).comp (lsInl K)) (fun N _ => @LSClosed K N ((pairInlR4 E).reduct N)) :=
  hullStrong_exp _

theorem pairLangR4_functions_le : max ℵ₀ #(Σ i, (pairLangR4 E).Functions i) ≤ ls K :=
  sum_functions_le (pairLangR3_functions_le E) (by rw [Lab83.chartLang_functions]; exact zero_le)

end LS83

end AEC
