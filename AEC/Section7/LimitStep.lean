module

public import AEC.Section7.SuccessorStep

@[expose] public section

/-!
# Matrix limit step of Proposition 7.8: chain unions at a level (`infra_78_chain_union_kappa`)

A directed family of objects at an eligible level `κ` (at most `κ` indices, identity and
composition laws) has a union object at `κ` with commuting, jointly covering legs and the
universal property. This is the chain-union existence needed by `infra_78_matrix_limit_step`;
it comes from the chain axioms of `K` (`SingleModelData.exists_directed_union`, Lemma 2.1),
with no new axioms. `infra_78_limit_pair` (cycle 45) builds the union pair at a limit stage
`δ < ρ⁺` (cocone arrows extending the composition law, commuting squares, continuity at `δ`)
under the paper's hypothesis `ρ⁺ < κ`; `Infra78Matrix.IdLaw` is the identity law, a tracked
output of `infra_78_matrix_construction`. `infra_78_limit_invariant5` (cycle 46) is
invariant (5) at limits for marks shorter than the cofinality, in particular finite marks
(`infra_78_tied_continuity`, English Prop 6.13). For bounded marks at small cofinality the paper
assumes Def 7.7 as a hypothesis on the mark; that case is tracked separately on the board.
-/

universe u

open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}

/-- **Chain unions at a level** (sub-tip of `infra_78_matrix_limit_step`). A directed family of
objects at an eligible level `κ`, indexed by at most `κ` indices, with arrows obeying the
identity and composition laws, has a union object at `κ`: legs commuting with the arrows,
jointly covering the union, and the universal property (existence and uniqueness of the induced
arrow into any object at any level). From the chain axioms of `K` via
`SingleModelData.exists_directed_union`; no new axioms. -/
theorem infra_78_chain_union_kappa {P : SingleModelData K} {κ : Cardinal.{u}}
    (hκ : κ ∈ P.eligible) {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (hι : #ι ≤ κ) (X : ι → P.scheme.Object κ hκ)
    (st : ∀ {a b : ι}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a)) (P.scheme.asSystem hκ (X b)))
    (hrefl : ∀ a, st (le_refl a) = SystemArrow.refl _)
    (htrans : ∀ {a b c : ι} (h₁ : a ≤ b) (h₂ : b ≤ c),
      st (h₁.trans h₂) = SystemArrow.comp (st h₁) (st h₂)) :
    ∃ (U : P.scheme.Object κ hκ)
      (leg : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a))
        (P.scheme.asSystem hκ U)),
      (∀ a, P.scheme.permitted (X := X a) (Y := U) (leg a)) ∧
      (∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (st h) (leg b) = leg a) ∧
      (∀ x : Occurrence K oneVertexShape (P.scheme.asSystem hκ U),
        ∃ a, ∃ y : Occurrence K oneVertexShape (P.scheme.asSystem hκ (X a)),
          pushOcc (leg a) y = x) ∧
      (∀ {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} (Z : P.scheme.Object ν hν)
        (g : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a))
          (P.scheme.asSystem hν Z)),
        (∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (st h) (g b) = g a) →
        ∃ f : SystemArrow K oneVertexShape (P.scheme.asSystem hκ U) (P.scheme.asSystem hν Z),
          P.scheme.permitted (X := U) (Y := Z) f ∧ ∀ a, SystemArrow.comp (leg a) f = g a) ∧
      (∀ {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} (Z : P.scheme.Object ν hν)
        (f f' : SystemArrow K oneVertexShape (P.scheme.asSystem hκ U) (P.scheme.asSystem hν Z)),
        (∀ a, SystemArrow.comp (leg a) f = SystemArrow.comp (leg a) f') → f = f') := by
  classical
  let S : DirectedSystem K.τ :=
    { ι := ι
      nonempty := inferInstance
      rel := (· ≤ ·)
      refl := le_refl
      trans := le_trans
      directed := fun a b => exists_ge_ge a b
      obj := fun a => (X a).model
      map := fun h => (st h).onVertex PUnit.unit
      map_refl := fun a => by
        rw [hrefl a]
        rfl
      map_trans := fun h₁ h₂ => by
        rw [htrans h₁ h₂]
        rfl }
  obtain ⟨U, incl, hincl, hcompat, hcover, huniv⟩ :=
    SingleModelData.exists_directed_union (P := P) hκ S (fun a => (X a).mem)
      (fun a => (X a).card) (fun h => (st h).onVertex_strong PUnit.unit) hι
  let leg : ∀ a, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a))
      (P.scheme.asSystem hκ U) := fun a =>
    oneVertexArrow (hM := (X a).mem) (hN := U.mem) (incl a) (hincl a)
  refine ⟨U, leg, fun _ => trivial, ?_, ?_, ?_, ?_⟩
  · intro a b h
    apply SystemArrow.ext
    intro v
    exact hcompat h
  · rintro ⟨v, x⟩
    obtain ⟨a, y, hy⟩ := hcover x
    cases v
    exact ⟨a, ⟨PUnit.unit, y⟩, by
      show (⟨PUnit.unit, incl a y⟩ : Occurrence K oneVertexShape (P.scheme.asSystem hκ U)) = _
      rw [hy]⟩
  · intro ν hν Z g hg
    obtain ⟨f, hf, hfg⟩ := huniv Z.model (fun a => (g a).onVertex PUnit.unit) Z.mem
      (fun a => (g a).onVertex_strong PUnit.unit)
      (fun h => congrArg (fun e => e.onVertex PUnit.unit) (hg h))
    refine ⟨oneVertexArrow (hM := U.mem) (hN := Z.mem) f hf, trivial, fun a => ?_⟩
    apply SystemArrow.ext
    intro v
    exact hfg a
  · intro ν hν Z f f' hff
    apply SystemArrow.ext
    intro v
    cases v
    ext x
    obtain ⟨a, y, hy⟩ := hcover x
    rw [← hy]
    exact DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hff a)) y


section LimitPair
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

/-- **Identity law of the matrix** (tracked obligation of `infra_78_matrix_construction`,
cycle 45): `stepX (le_refl i)` and `stepY (le_refl i)` are identities. -/
def Infra78Matrix.IdLaw (M : Infra78Matrix P ρ hκ) : Prop :=
  (∀ i, M.stepX (le_refl i) = SystemArrow.refl _) ∧
  (∀ i, M.stepY (le_refl i) = SystemArrow.refl _)

/-- Union pair of a directed family of pairs at level `κ` (generic index). -/
theorem infra_78_limit_pair_gen {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (hι : #ι ≤ κ) (X Y : ι → P.scheme.Object κ hκ)
    (pair : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
      (P.scheme.asSystem hκ (Y j)))
    (sX : ∀ {a b : ι}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a)) (P.scheme.asSystem hκ (X b)))
    (sY : ∀ {a b : ι}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y a)) (P.scheme.asSystem hκ (Y b)))
    (hXr : ∀ a, sX (le_refl a) = SystemArrow.refl _)
    (hYr : ∀ a, sY (le_refl a) = SystemArrow.refl _)
    (hXt : ∀ {a b c : ι} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sX (h₁.trans h₂) = SystemArrow.comp (sX h₁) (sX h₂))
    (hYt : ∀ {a b c : ι} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sY (h₁.trans h₂) = SystemArrow.comp (sY h₁) (sY h₂))
    (hcomm : ∀ {a b : ι} (h : a ≤ b),
      SystemArrow.comp (pair a) (sY h) = SystemArrow.comp (sX h) (pair b)) :
    ∃ (Xδ Yδ : P.scheme.Object κ hκ)
      (lX : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
        (P.scheme.asSystem hκ Xδ))
      (lY : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y j))
        (P.scheme.asSystem hκ Yδ))
      (pδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xδ) (P.scheme.asSystem hκ Yδ)),
      (∀ j, P.scheme.permitted (X := X j) (Y := Xδ) (lX j)) ∧
      (∀ j, P.scheme.permitted (X := Y j) (Y := Yδ) (lY j)) ∧
      P.scheme.permitted (X := Xδ) (Y := Yδ) pδ ∧
      (∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (sX h) (lX b) = lX a) ∧
      (∀ {a b : ι} (h : a ≤ b), SystemArrow.comp (sY h) (lY b) = lY a) ∧
      (∀ j, SystemArrow.comp (pair j) (lY j) = SystemArrow.comp (lX j) pδ) ∧
      (∀ x : (Xδ.model).carrier, ∃ j y, (lX j).onVertex PUnit.unit y = x) ∧
      (∀ x : (Yδ.model).carrier, ∃ j y, (lY j).onVertex PUnit.unit y = x) := by
  obtain ⟨Xδ, lX, hlX, hcX, hcovX, hunivX, -⟩ := infra_78_chain_union_kappa hκ hι X sX hXr hXt
  obtain ⟨Yδ, lY, hlY, hcY, hcovY, -, -⟩ := infra_78_chain_union_kappa hκ hι Y sY hYr hYt
  obtain ⟨pδ, hpδ, hpδc⟩ := hunivX Yδ (fun j => SystemArrow.comp (pair j) (lY j)) (by
    intro a b h
    rw [← SystemArrow.comp_assoc, ← hcomm h, SystemArrow.comp_assoc, hcY h])
  refine ⟨Xδ, Yδ, lX, lY, pδ, hlX, hlY, hpδ, hcX, hcY, fun j => (hpδc j).symm, ?_, ?_⟩
  · intro x
    obtain ⟨j, ⟨v, y⟩, hy⟩ := hcovX ⟨PUnit.unit, x⟩
    exact ⟨j, y, by cases v; exact congrArg Sigma.snd hy⟩
  · intro x
    obtain ⟨j, ⟨v, y⟩, hy⟩ := hcovY ⟨PUnit.unit, x⟩
    exact ⟨j, y, by cases v; exact congrArg Sigma.snd hy⟩

/-- **Prop 7.8 matrix limit pair** (`infra_78_limit_pair`). At a limit stage `δ < ρ⁺` of a
partial matrix (pairs `X_j → Y_j` for `j < δ` at level `κ`, with the identity and composition
laws and commuting squares), under the paper's hypothesis `ρ⁺ < κ`, the unions
`X_δ`, `Y_δ` at level `κ` exist (`infra_78_chain_union_kappa`) together with cocone arrows
extending the composition law, a pair arrow `X_δ → Y_δ` with commuting squares, and continuity
at `δ` (every element of `X_δ`, `Y_δ` comes from an earlier stage). -/
theorem infra_78_limit_pair (hρκ : Order.succ ρ < κ) {δ : (Order.succ ρ).ord.ToType}
    (hδ : Order.IsSuccLimit δ) (X Y : Set.Iio δ → P.scheme.Object κ hκ)
    (pair : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
      (P.scheme.asSystem hκ (Y j)))
    (sX : ∀ {a b : Set.Iio δ}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a)) (P.scheme.asSystem hκ (X b)))
    (sY : ∀ {a b : Set.Iio δ}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y a)) (P.scheme.asSystem hκ (Y b)))
    (hXr : ∀ a, sX (le_refl a) = SystemArrow.refl _)
    (hYr : ∀ a, sY (le_refl a) = SystemArrow.refl _)
    (hXt : ∀ {a b c : Set.Iio δ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sX (h₁.trans h₂) = SystemArrow.comp (sX h₁) (sX h₂))
    (hYt : ∀ {a b c : Set.Iio δ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sY (h₁.trans h₂) = SystemArrow.comp (sY h₁) (sY h₂))
    (hcomm : ∀ {a b : Set.Iio δ} (h : a ≤ b),
      SystemArrow.comp (pair a) (sY h) = SystemArrow.comp (sX h) (pair b)) :
    ∃ (Xδ Yδ : P.scheme.Object κ hκ)
      (lX : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
        (P.scheme.asSystem hκ Xδ))
      (lY : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y j))
        (P.scheme.asSystem hκ Yδ))
      (pδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xδ) (P.scheme.asSystem hκ Yδ)),
      (∀ j, P.scheme.permitted (X := X j) (Y := Xδ) (lX j)) ∧
      (∀ j, P.scheme.permitted (X := Y j) (Y := Yδ) (lY j)) ∧
      P.scheme.permitted (X := Xδ) (Y := Yδ) pδ ∧
      (∀ {a b : Set.Iio δ} (h : a ≤ b), SystemArrow.comp (sX h) (lX b) = lX a) ∧
      (∀ {a b : Set.Iio δ} (h : a ≤ b), SystemArrow.comp (sY h) (lY b) = lY a) ∧
      (∀ j, SystemArrow.comp (pair j) (lY j) = SystemArrow.comp (lX j) pδ) ∧
      (∀ x : (Xδ.model).carrier, ∃ j y, (lX j).onVertex PUnit.unit y = x) ∧
      (∀ x : (Yδ.model).carrier, ∃ j y, (lY j).onVertex PUnit.unit y = x) := by
  obtain ⟨j0, hj0⟩ := not_isMin_iff.1 hδ.not_isMin
  have : Nonempty (Set.Iio δ) := ⟨⟨j0, hj0⟩⟩
  have hι : #(Set.Iio δ) ≤ κ := by
    refine (Cardinal.mk_le_of_injective Subtype.val_injective).trans ?_
    rw [Cardinal.mk_ord_toType]
    exact hρκ.le
  exact infra_78_limit_pair_gen hι X Y pair sX sY hXr hYr hXt hYt hcomm

end LimitPair
section Invariant5

/-- **Invariant (5) at limits for marks shorter than the cofinality** (`infra_78_limit_invariant5`,
the form of Def 7.7 that Prop 7.8 uses for a finite mark). At a level `μ` of the Prop 7.3 tail,
let `C` be a same-level chain with union `X_δ`, `p = tp(b/X_δ)` a mark with `|b| ≤ σ` and
`|b| < cf δ` (e.g. `b` finite), and `g : X → X₀` the base. If (5) holds at every stage
(`tp(b/X_i)` is the tied free lift of `tp(b/X)` along `X → X_i`), it holds over the union.
Proof: `infra_78_tied_continuity` (local character + transitivity, English Prop 6.13). -/
theorem infra_78_limit_invariant5 (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ)
    (C : SameLevelChain P (Tail.mem (infra_73_tail P σ hσ) hμT))
    (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) C.unionObj)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ) (hcof : #p.idx < C.δ.cof)
    (X : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
    (g : SystemArrow K oneVertexShape
      (P.scheme.asSystem _ X) (P.scheme.asSystem _ (C.obj 0 C.hlim.1)))
    (hg : P.scheme.permitted (X := X) (Y := C.obj 0 C.hlim.1) g)
    (hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree
        (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
          (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (P.scheme.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hg
            (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)) :
    IsTiedFree (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
      (p.restrict (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
        (P.scheme.comp g (C.toUnion 0 C.hlim.1) hg (C.toUnion_arrow 0 C.hlim.1)))
      p (Equiv.refl _) :=
  infra_78_tied_continuity P σ hσ _ hμT.1
    ((Order.succ_le_succ (le_max_left σ (infra_73_h P σ))).trans hμT.2) C p hνμ hidx hcof
    X g hg hAll

/-- Finite marks (the case of the Lean `proposition_7_8`): `|b| < ℵ₀ ≤ cf δ`. -/
theorem infra_78_limit_invariant5_finite (P : SingleModelData K) (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ)
    (C : SameLevelChain P (Tail.mem (infra_73_tail P σ hσ) hμT))
    (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) C.unionObj)
    (hνμ : p.ν = μ) (hFin : Finite p.idx)
    (X : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
    (g : SystemArrow K oneVertexShape
      (P.scheme.asSystem _ X) (P.scheme.asSystem _ (C.obj 0 C.hlim.1)))
    (hg : P.scheme.permitted (X := X) (Y := C.obj 0 C.hlim.1) g)
    (hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree
        (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
          (SystemArrow.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (P.scheme.comp g (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) hg
            (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _)) :
    IsTiedFree (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
      (p.restrict (SystemArrow.comp g (C.toUnion 0 C.hlim.1))
        (P.scheme.comp g (C.toUnion 0 C.hlim.1) hg (C.toUnion_arrow 0 C.hlim.1)))
      p (Equiv.refl _) := by
  have hlt : #p.idx < ℵ₀ := mk_lt_aleph0_iff.2 hFin
  exact infra_78_limit_invariant5 P σ hσ hμT C p hνμ (hlt.le.trans hσ)
    (hlt.trans_le (SameLevelChain.cof_aleph0 C)) X g hg hAll

end Invariant5

end AEC
