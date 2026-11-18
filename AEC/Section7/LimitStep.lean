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
`infra_78_matrix_limit_step` (cycle 47) assembles these: the stages below `δ` form a
`SameLevelChain` over `X_δ` (`infra_78_partialChain`), invariant (5) moves between the hosts
`Y_j` and `Y_δ` by the host-relation lemmas, and tied continuity gives (5) at `δ`.
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


section LimitAssembly
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

/-- The mark `b` at stage `j` as a tuple over `X_j` (host `Y_j`, inclusion `pair_j`). -/
def infra_78_markTuple {X Y : P.scheme.Object κ hκ}
    (pr : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y))
    {uIdx : Type u} (b : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Y)) :
    TupleOver K oneVertexShape P.scheme hκ X :=
  ⟨κ, hκ, Y, pr, trivial, uIdx, b⟩

/-- The stages below a limit `δ` of a partial matrix, as a `SameLevelChain` over a given union
with covering legs. -/
noncomputable def infra_78_partialChain {δ : (Order.succ ρ).ord.ToType}
    (hδ : Order.IsSuccLimit δ) (X : Set.Iio δ → P.scheme.Object κ hκ)
    (sX : ∀ {a b : Set.Iio δ}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X a)) (P.scheme.asSystem hκ (X b)))
    (hXt : ∀ {a b c : Set.Iio δ} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sX (h₁.trans h₂) = SystemArrow.comp (sX h₁) (sX h₂))
    (U : P.scheme.Object κ hκ)
    (l : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j)) (P.scheme.asSystem hκ U))
    (hl : ∀ {a b : Set.Iio δ} (h : a ≤ b), SystemArrow.comp (sX h) (l b) = l a)
    (hcov : ∀ x : U.model.carrier, ∃ j y, (l j).onVertex PUnit.unit y = x) :
    SameLevelChain P hκ where
  δ := (Ordinal.ToType.toOrd δ).1
  hlim := infra_78_stg_ord_limit δ hδ
  obj α hα := X ⟨infra_78_stg δ α hα, infra_78_stg_lt δ α hα⟩
  le hα hβ h := sX (show (⟨_, infra_78_stg_lt δ _ hα⟩ : Set.Iio δ) ≤ ⟨_, infra_78_stg_lt δ _ hβ⟩
    from infra_78_stg_mono δ hα hβ h)
  le_arrow _ _ _ := trivial
  le_comp hα hβ hγ h₁ h₂ := (hXt _ _).symm
  unionObj := U
  toUnion α hα := l ⟨infra_78_stg δ α hα, infra_78_stg_lt δ α hα⟩
  toUnion_arrow _ _ := trivial
  toUnion_comp hα hβ h := hl _
  joint x := by
    obtain ⟨⟨j, hj⟩, y, hy⟩ := hcov x.2
    obtain ⟨α, hα, rfl⟩ := infra_78_stg_surj δ j hj
    exact ⟨α, hα, ⟨PUnit.unit, y⟩, by
      show (⟨PUnit.unit, _⟩ : Σ _ : PUnit, _) = x
      rw [hy]
      rfl⟩

/-- **Prop 7.8 matrix limit step** (`infra_78_matrix_limit_step`). Let `κ` be a recursion-closed
level with `σ⁺ ≤ κ` and `ρ⁺ < κ`, `δ < ρ⁺` a limit stage, and a partial matrix below `δ`
(pairs `X_j → Y_j`, identity and composition laws, commuting squares), a base `g_j : X_b → X_j`
compatible with the steps, and a fixed mark `b` (`b_j` in `Y_j`, moved by the steps) with
`|b| ≤ σ` and `|b| < cf δ` (every finite mark), satisfying invariant (5) at every stage. Then the
union pair `X_δ → Y_δ` exists with cocone arrows extending the laws, commuting squares and
continuity at `δ`, the mark has a single image `b_δ` in `Y_δ`, the base has a single image
`g_δ : X_b → X_δ`, and invariant (5) holds at `δ`. -/
theorem infra_78_matrix_limit_step (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    (hrec : κ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ κ)
    (hρκ : Order.succ ρ < κ) {δ : (Order.succ ρ).ord.ToType}
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
      SystemArrow.comp (pair a) (sY h) = SystemArrow.comp (sX h) (pair b))
    (Xb : P.scheme.Object κ hκ)
    (g : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb) (P.scheme.asSystem hκ (X j)))
    (hg : ∀ {a b : Set.Iio δ} (h : a ≤ b), SystemArrow.comp (g a) (sX h) = g b)
    {uIdx : Type u} (b : ∀ j, uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ (Y j)))
    (hb : ∀ {a c : Set.Iio δ} (h : a ≤ c) k, b c k = pushOcc (sY h) (b a k))
    (hidx : #uIdx ≤ σ) (hcof : #uIdx < (Ordinal.ToType.toOrd δ).1.cof)
    (h5 : ∀ j, IsTiedFree (g j) ((infra_78_markTuple (pair j) (b j)).restrict (g j) trivial)
      (infra_78_markTuple (pair j) (b j)) (Equiv.refl _)) :
    ∃ (Xδ Yδ : P.scheme.Object κ hκ)
      (lX : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (X j))
        (P.scheme.asSystem hκ Xδ))
      (lY : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hκ (Y j))
        (P.scheme.asSystem hκ Yδ))
      (pδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xδ) (P.scheme.asSystem hκ Yδ))
      (gδ : SystemArrow K oneVertexShape (P.scheme.asSystem hκ Xb) (P.scheme.asSystem hκ Xδ))
      (bδ : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Yδ)),
      (∀ {a c : Set.Iio δ} (h : a ≤ c), SystemArrow.comp (sX h) (lX c) = lX a) ∧
      (∀ {a c : Set.Iio δ} (h : a ≤ c), SystemArrow.comp (sY h) (lY c) = lY a) ∧
      (∀ j, SystemArrow.comp (pair j) (lY j) = SystemArrow.comp (lX j) pδ) ∧
      (∀ x : (Xδ.model).carrier, ∃ j y, (lX j).onVertex PUnit.unit y = x) ∧
      (∀ x : (Yδ.model).carrier, ∃ j y, (lY j).onVertex PUnit.unit y = x) ∧
      (∀ j, SystemArrow.comp (g j) (lX j) = gδ) ∧
      (∀ j k, bδ k = pushOcc (lY j) (b j k)) ∧
      IsTiedFree gδ ((infra_78_markTuple pδ bδ).restrict gδ trivial)
        (infra_78_markTuple pδ bδ) (Equiv.refl _) := by
  classical
  obtain ⟨Xδ, Yδ, lX, lY, pδ, -, -, -, hcX, hcY, hsq, hcovX, hcovY⟩ :=
    infra_78_limit_pair hρκ hδ X Y pair sX sY hXr hYr hXt hYt hcomm
  let C := infra_78_partialChain hδ X sX hXt Xδ lX hcX hcovX
  let j0 : Set.Iio δ := ⟨infra_78_stg δ 0 C.hlim.1, infra_78_stg_lt δ 0 C.hlim.1⟩
  let gδ := SystemArrow.comp (g j0) (lX j0)
  let bδ : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hκ Yδ) :=
    fun k => pushOcc (lY j0) (b j0 k)
  have hgδ : ∀ j, SystemArrow.comp (g j) (lX j) = gδ := by
    intro j
    rcases le_total j j0 with h | h
    · show _ = SystemArrow.comp (g j0) (lX j0)
      rw [← hcX h, ← SystemArrow.comp_assoc, hg h]
    · show _ = SystemArrow.comp (g j0) (lX j0)
      rw [← hcX h, ← SystemArrow.comp_assoc, hg h]
  have hbδ : ∀ j k, bδ k = pushOcc (lY j) (b j k) := by
    intro j k
    rcases le_total j j0 with h | h
    · show pushOcc (lY j0) (b j0 k) = _
      rw [hb h k, ← pushOcc_comp, hcY h]
    · show pushOcc (lY j0) (b j0 k) = _
      rw [hb h k, ← pushOcc_comp, hcY h]
  refine ⟨Xδ, Yδ, lX, lY, pδ, gδ, bδ, hcX, hcY, hsq, hcovX, hcovY, hgδ, hbδ, ?_⟩
  have hqκ : #uIdx < κ := hidx.trans_lt (Order.succ_le_iff.1 hσSucc)
  let p : TupleOver K oneVertexShape P.scheme hκ C.unionObj := infra_78_markTuple pδ bδ
  have hsqx : ∀ j (x : (X j).model.carrier),
      (lY j).onVertex PUnit.unit ((pair j).onVertex PUnit.unit x) =
        pδ.onVertex PUnit.unit ((lX j).onVertex PUnit.unit x) := fun j x =>
    DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hsq j)) x
  have hAll : ∀ (i : Ordinal.{u}) (hi : i < C.δ),
      IsTiedFree
        (SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
        ((p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)).restrict
          (SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)))
          (P.scheme.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) trivial
            (C.le_arrow C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i))))
        (p.restrict (C.toUnion i hi) (C.toUnion_arrow i hi)) (Equiv.refl _) := by
    intro i hi
    let ji : Set.Iio δ := ⟨infra_78_stg δ i hi, infra_78_stg_lt δ i hi⟩
    have e1 : SystemArrow.comp (g j0) (C.le C.hlim.1 hi (bot_le : (0 : Ordinal.{u}) ≤ i)) =
        g ji := hg _
    have hR : infra_78_HostRel (infra_78_markTuple (pair ji) (b ji))
        (p.restrict (lX ji) trivial) (lY ji) (Equiv.refl _) :=
      ⟨fun v x => by cases v; exact hsqx ji x, fun k => hbδ ji k⟩
    have hR' : infra_78_HostRel ((infra_78_markTuple (pair ji) (b ji)).restrict (g ji) trivial)
        ((p.restrict (lX ji) trivial).restrict (g ji) trivial) (lY ji) (Equiv.refl _) :=
      ⟨fun v x => by cases v; exact hsqx ji _, fun k => hbδ ji k⟩
    have h1 := (infra_78_tiedFree_host_target (g ji)
      ((infra_78_markTuple (pair ji) (b ji)).restrict (g ji) trivial) trivial hR rfl rfl hqκ
      (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).1 (h5 ji)
    have h2 := infra_78_tiedFree_host_source (g ji) trivial hR' rfl rfl hqκ
      (p.restrict (lX ji) trivial) (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) h1
    exact infra_78_tiedFree_congr_arrow trivial trivial (p.restrict (lX ji) trivial) e1.symm h2
  exact infra_78_tied_continuity P σ hσ hκ hrec hσSucc C p rfl hidx hcof Xb (g j0) trivial hAll

/-- A limit stage has cofinality at least `ℵ₀`, so every finite mark satisfies the cofinality
hypothesis of `infra_78_matrix_limit_step`. -/
theorem infra_78_finite_lt_limit_cof {δ : (Order.succ ρ).ord.ToType}
    (hδ : Order.IsSuccLimit δ) {uIdx : Type u} (hFin : Finite uIdx) :
    #uIdx < (Ordinal.ToType.toOrd δ).1.cof :=
  (mk_lt_aleph0_iff.2 hFin).trans_le
    (Ordinal.aleph0_le_cof_iff.mpr (Ordinal.one_lt_cof_iff.mpr (infra_78_stg_ord_limit δ hδ).2))

end LimitAssembly
end AEC
