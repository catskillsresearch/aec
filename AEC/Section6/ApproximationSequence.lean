module

public import AEC.Section6.TupleOver
public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}} {W : WorkingScheme K S}
  {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {base : W.Object μ hμ}

/-- The joint list of a tuple in `X` with an enumerated parameter set in `X`. -/
def seqJoint {idx ι : Type u} {X : SystemObject K S}
    (v : idx → Occurrence K S X) (Z : ι → Occurrence K S X) :
    idx ⊕ ι → Occurrence K S X
  | Sum.inl i => v i
  | Sum.inr j => Z j

/-- The joint list of an actual type with parameters from its base, pushed along the inclusion. -/
def typeJoint {p : TupleOver K S W hμ base} {ι : Type u}
    (Z : ι → Occurrence K S (W.asSystem hμ base)) :
    p.idx ⊕ ι → Occurrence K S (W.asSystem p.hν p.host)
  | Sum.inl i => p.val i
  | Sum.inr j => ⟨(Z j).1, p.incl.onVertex (Z j).1 (Z j).2⟩

/-- Reindex the tuple summand of a joint list along `ρ`, leaving the parameter summand fixed. -/
def jointReindex {α ι β : Type u} (ρ : ι → α) : ι ⊕ β → α ⊕ β :=
  Sum.map ρ id

theorem jointReindex_injective {α ι β : Type u} (ρ : ι → α) (hρ : Function.Injective ρ) :
    Function.Injective (jointReindex (β := β) ρ) :=
  Sum.map_injective.mpr ⟨hρ, Function.injective_id⟩

/-- The subtuple (coordinate reindexing) of an actual type. -/
def TupleOver.reindex {ι : Type u} (p : TupleOver K S W hμ base) (ρ : ι → p.idx) :
    TupleOver K S W hμ base where
  ν := p.ν
  hν := p.hν
  host := p.host
  incl := p.incl
  incl_arrow := p.incl_arrow
  idx := ι
  val := fun j => p.val (ρ j)

theorem typeJoint_reindex {p : TupleOver K S W hμ base} {ι β : Type u}
    (ρ : ι → p.idx) (Z : β → Occurrence K S (W.asSystem hμ base)) :
    typeJoint (p := p.reindex ρ) Z = typeJoint (p := p) Z ∘ jointReindex ρ := by
  funext t
  cases t <;> rfl

theorem seqJoint_reindex {idx ι β : Type u} {X : SystemObject K S}
    (v : idx → Occurrence K S X) (ρ : ι → idx) (Z : β → Occurrence K S X) :
    seqJoint (fun j => v (ρ j)) Z = seqJoint v Z ∘ jointReindex ρ := by
  funext t
  cases t <;> rfl

/-- Diagram equality passes to an injective reindexing of the index.
The reindexed lists are the range summand of the lists transported along
`Equiv.Set.sumCompl` (`WorkingScheme.diagram_reindex`, `WorkingScheme.diagram_restrict`). -/
theorem WorkingScheme.diagramEq_precomp
    {α γ : Type u} {νX νY : Cardinal.{u}} {hνX : νX ∈ W.eligible} {hνY : νY ∈ W.eligible}
    (X : W.Object νX hνX) (Y : W.Object νY hνY)
    (xs : α → Occurrence K S (W.asSystem hνX X))
    (ys : α → Occurrence K S (W.asSystem hνY Y))
    (ρ : γ → α) (hρ : Function.Injective ρ)
    (h : W.DiagramEq (X := X) (Y := Y) xs ys) :
    W.DiagramEq (X := X) (Y := Y) (fun j => xs (ρ j)) (fun j => ys (ρ j)) := by
  classical
  let s : Set α := Set.range ρ
  haveI : DecidablePred (· ∈ s) := Classical.decPred (· ∈ s)
  let eα : s ⊕ ↥(sᶜ) ≃ α := Equiv.Set.sumCompl s
  have hRe : W.DiagramEq (X := X) (Y := Y) (fun t => xs (eα t)) (fun t => ys (eα t)) :=
    (W.diagram_reindex X Y eα.symm xs ys).mp h
  let xsL : s → Occurrence K S (W.asSystem hνX X) := fun i => xs i.1
  let ysL : s → Occurrence K S (W.asSystem hνY Y) := fun i => ys i.1
  let xsR : ↥(sᶜ) → Occurrence K S (W.asSystem hνX X) := fun c => xs c.1
  let ysR : ↥(sᶜ) → Occurrence K S (W.asSystem hνY Y) := fun c => ys c.1
  have hEqX : (fun t => xs (eα t)) = Sum.elim xsL xsR := by
    funext t
    cases t with
    | inl i =>
      unfold eα xsL
      rw [Equiv.Set.sumCompl_apply_inl]
      rfl
    | inr c =>
      unfold eα xsR
      rw [Equiv.Set.sumCompl_apply_inr]
      rfl
  have hEqY : (fun t => ys (eα t)) = Sum.elim ysL ysR := by
    funext t
    cases t with
    | inl i =>
      unfold eα ysL
      rw [Equiv.Set.sumCompl_apply_inl]
      rfl
    | inr c =>
      unfold eα ysR
      rw [Equiv.Set.sumCompl_apply_inr]
      rfl
  have hSum : W.DiagramEq (X := X) (Y := Y) (Sum.elim xsL xsR) (Sum.elim ysL ysR) := by
    rw [← hEqX, ← hEqY]
    exact hRe
  have hL : W.DiagramEq (X := X) (Y := Y) xsL ysL :=
    (W.diagram_restrict X Y xsL ysL xsR ysR hSum).1
  let eγ : γ ≃ s := Equiv.ofInjective ρ hρ
  refine (W.diagram_reindex X Y eγ (fun j => xs (ρ j)) (fun j => ys (ρ j))).mpr ?_
  have hX : (fun b : s => xs (ρ (eγ.symm b))) = xsL := by
    funext b
    have hb : ρ (eγ.symm b) = b.1 := congrFun (Equiv.self_comp_ofInjective_symm hρ) b
    rw [hb]
  have hY : (fun b : s => ys (ρ (eγ.symm b))) = ysL := by
    funext b
    have hb : ρ (eγ.symm b) = b.1 := congrFun (Equiv.self_comp_ofInjective_symm hρ) b
    rw [hb]
  rw [hX, hY]
  exact hL

/-- **Definition 6.8.** An approximation sequence for `p = tp(v/A)` at query size `τ` is an
indexed family `(vᵢ : i < κ)` in `A`, each of the same index set as `v`, with bounded
concatenation, such that for every parameter enumeration `Z` of size at most `τ` the set of
indices whose joint diagram with `Z` differs from `p ↾ Z` has size at most `|Z| + ℵ₀`.
The same bound holds for every subtuple of the displayed tuple
(`ApproximationSequence.subtuple_uniform`). -/
structure ApproximationSequence (p : TupleOver K S W hμ base) where
  τ : Cardinal.{u}
  κIndex : Type u
  family : κIndex → p.idx → Occurrence K S (W.asSystem hμ base)
  concat_bounded : #(κIndex × p.idx) < μ
  few_exceptions : ∀ {ι : Type u}
    (Z : ι → Occurrence K S (W.asSystem hμ base)),
    #ι ≤ τ →
    # {i : κIndex // ¬ W.DiagramEq (X := p.host) (Y := base)
        (typeJoint Z) (seqJoint (family i) Z)} ≤ #ι + aleph0

/-- **Lemma 6.9, subtuples (S3).** Definition 6.8(2) for every subtuple of the displayed
tuple. For an injective reindexing `ρ : ι → p.idx` (a subtuple embedding; every inclusion
`Subtype.val` is one), the restricted copies `fun i j => seq.family i (ρ j)` disagree with
the reindexed type on at most `|Z| + ℵ₀` indices of any parameter query of size at most
`seq.τ`. The joint of the subtuple is a summand of a reindexing of the full joint, so
`DiagramEq` of the full joint implies `DiagramEq` of the restriction. -/
abbrev ApproximationSequence.HasSubtupleBound {p : TupleOver K S W hμ base}
    (seq : ApproximationSequence p) : Prop :=
  ∀ {ι : Type u} (ρ : ι → p.idx), Function.Injective ρ →
    ∀ {β : Type u} (Z : β → Occurrence K S (W.asSystem hμ base)),
      #β ≤ seq.τ →
      # {i : seq.κIndex // ¬ W.DiagramEq (X := p.host) (Y := base)
          (typeJoint (p := p.reindex ρ) Z)
          (seqJoint (fun j => seq.family i (ρ j)) Z)} ≤ #β + aleph0

theorem ApproximationSequence.subtuple_uniform {p : TupleOver K S W hμ base}
    (seq : ApproximationSequence p) : seq.HasSubtupleBound := by
  intro ι ρ hρ β Z hβ
  have hsub : ∀ i : seq.κIndex,
      ¬ W.DiagramEq (X := p.host) (Y := base)
          (typeJoint (p := p.reindex ρ) Z)
          (seqJoint (fun j => seq.family i (ρ j)) Z) →
      ¬ W.DiagramEq (X := p.host) (Y := base)
          (typeJoint (p := p) Z)
          (seqJoint (seq.family i) Z) := by
    intro i hbad hfull
    apply hbad
    have hpre :=
      WorkingScheme.diagramEq_precomp p.host base
        (typeJoint (p := p) Z) (seqJoint (seq.family i) Z)
        (jointReindex ρ) (jointReindex_injective ρ hρ) hfull
    have hL := typeJoint_reindex (p := p) ρ Z
    have hR := seqJoint_reindex (seq.family i) ρ Z
    unfold TupleOver.reindex at hL ⊢
    exact hL.symm ▸ hR.symm ▸ hpre
  exact (mk_subtype_mono hsub).trans (seq.few_exceptions Z hβ)

end
end AEC
