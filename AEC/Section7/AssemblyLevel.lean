module

public import AEC.Section7.MarginalAnchor

@[expose] public section

/-!
# Prop 7.8 assembly for `p` realized at the level of `X` (`infra_78_matrix_assembly_level`)

`infra_78_matrix_assembly_level_statement` is the full claim: the `proposition_7_8` conclusion,
on the tail `infra_78_closedTail P`, for every finite-tuple `p` over `X` realized at the level of
`X` (`p.ν = λ`). Split (cycle 64):

* `infra_78_assembly_levels` (proved): the paper's level choices. For `λ` in the closed tail and
  infinite `θ < λ`: `ρ = 2^λ` (`λ < ρ = ρ^λ`), a matrix level `κ > ρ⁺` closed at `λ` and at `θ`,
  and `λ` closed at `infra_76_sigma2 θ` (the descent parameter `σd = θ`).
* `infra_78_seq_diagram_transfer` (proved): an approximation sequence for `p` (the list `I_p`,
  fixed in `X` before the matrix) is one for any tuple with the same small-test diagrams (the mark
  restricted to `X` at the isolated stage).
* Open (tracked on the board): `infra_78_seed_stage` (seed `X → X_0`, `Y_0` with the mixed free
  lift of `p`, `R_0 ⊇ ι(I_p) ∪ b`, closed, `≤ ρ`), `infra_78_stage_transport` (at every stage the
  mark is the seed mark, `Y_0 → Y_i` commutes with the base maps, `R_0 ⊆ R_i`), and the final glue
  `infra_78_assembly_glue`.
-/

universe u

open Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Full claim of `infra_78_matrix_assembly_level`** (statement only; open). The
`proposition_7_8` conclusion on the tail `infra_78_closedTail P` for `p` realized at the level of
`X`. -/
def infra_78_matrix_assembly_level_statement (P : SingleModelData K) : Prop :=
  ∀ μ (hμ : μ ∈ infra_78_closedTail P)
    (X : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
    (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X)
    (θ : Cardinal.{u}),
    Finite p.idx → p.ν = μ → aleph0 ≤ θ → θ < μ →
    ∃ (U : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ U))
      (hf : P.scheme.permitted (X := X) (Y := U) f)
      (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)) (e : p.idx ≃ p.idx),
      SameGaloisType p (asTuple f hf b) e (Equiv.refl p.idx) ∧
      ∀ {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
        #cIdx ≤ θ →
        IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
          (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx))

/-- **Level choices for the Prop 7.8 matrix (proved).** Paper: "Choose a much larger eligible
level `κ` and a cardinal `ρ` such that `λ < ρ = ρ^λ`, `ρ⁺ < κ` ... first choose a sufficiently
large power `2^ξ` with `ξ ≥ λ` for `ρ`, and then choose an eligible `κ` above `ρ⁺` and all
remaining bounds." Here `ξ = λ`, `σ = λ` and the descent parameter `σd = θ`. -/
theorem infra_78_assembly_levels (P : SingleModelData K) {lam : Cardinal.{u}}
    (hlam : lam ∈ infra_78_closedTail P) {θ : Cardinal.{u}} (hθ : ℵ₀ ≤ θ) (hθlam : θ < lam) :
    ∃ ρ κ : Cardinal.{u}, lam < ρ ∧ ρ ^ lam = ρ ∧ Order.succ ρ < κ ∧ lam ≤ κ ∧
      κ ∈ infra_73_tailSet P lam ∧ κ ∈ infra_73_tailSet P θ ∧
      lam ∈ infra_73_tailSet P (infra_76_sigma2 P θ) ∧ Order.succ θ ≤ lam := by
  obtain ⟨hel, htail, -⟩ := hlam
  have hlamInf : ℵ₀ ≤ lam := P.aleph0_le hel
  have hθT : lam ∈ infra_73_tailSet P θ := htail θ hθ hθlam
  have hhθ : infra_73_h P θ < lam := infra_73_h_lt hel hθT
  have hhθinf : ℵ₀ ≤ infra_73_h P θ := hθ.trans (infra_76_lt_h P θ).le
  have hh2T : lam ∈ infra_73_tailSet P (infra_73_h P θ) := htail _ hhθinf hhθ
  have h2 : infra_76_sigma2 P θ < lam := infra_73_h_lt hel hh2T
  have h2inf : ℵ₀ ≤ infra_76_sigma2 P θ := hhθinf.trans (infra_76_lt_h P _).le
  have hσ2T : lam ∈ infra_73_tailSet P (infra_76_sigma2 P θ) := htail _ h2inf h2
  obtain ⟨κ, hκle, hκT⟩ :=
    (infra_73_tail P lam hlamInf).2 (Order.succ (Order.succ (2 ^ lam)))
  refine ⟨2 ^ lam, κ, cantor lam, ?_, ?_, ?_, hκT, infra_76_tail_mono hhθ.le hκT, hσ2T,
    Order.succ_le_of_lt hθlam⟩
  · rw [← power_mul, mul_eq_self hlamInf]
  · exact (Order.lt_succ_of_not_isMax (not_isMax _)).trans_le hκle
  · exact (Order.le_succ lam).trans (infra_73_tail_succ hκT)

/-- **Approximation sequences transfer along equal small-test diagrams (proved).** Paper: "Fix
a bounded approximation list `I_p` in `X` which determines `p` at a sufficient testing arity";
the same list is an approximation sequence for any tuple over `X` with the same diagrams on tests
of size `≤ τ` (here: the mark restricted to `X` at the isolated stage). -/
noncomputable def infra_78_seq_diagram_transfer {P : SingleModelData K} {ν : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {X : P.scheme.Object ν hν}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hν X} (e : t1.idx ≃ t2.idx)
    (seq : ApproximationSequence t1)
    (hD : ∀ {β : Type u} (Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hν X)),
      #β ≤ seq.τ →
      P.scheme.DiagramEq (X := t1.host) (Y := t2.host)
        (typeJoint (p := t1) Z) (fun s => typeJoint (p := t2) Z (Sum.map e id s))) :
    ApproximationSequence t2 where
  τ := seq.τ
  κIndex := seq.κIndex
  family := fun i k => seq.family i (e.symm k)
  concat_bounded := by
    have : #(seq.κIndex × t2.idx) = #(seq.κIndex × t1.idx) :=
      Cardinal.mk_congr (Equiv.prodCongr (Equiv.refl _) e.symm)
    rw [this]; exact seq.concat_bounded
  few_exceptions := fun {β} Z hZ => by
    refine le_trans ?_ (seq.few_exceptions Z hZ)
    refine Cardinal.mk_le_of_injective (f := fun j => ⟨j.1, fun hgood => j.2 ?_⟩)
      (by
        intro j₁ j₂ hj
        apply Subtype.ext
        have := congrArg Subtype.val hj
        exact this)
    have d1 := P.scheme.diagram_trans _ _ _ _ _ _
      (P.scheme.diagram_symm _ _ _ _ (hD Z hZ)) hgood
    refine infra_612_dEq_transport d1 (Equiv.sumCongr e.symm (Equiv.refl β)) ?_ ?_
    · rintro (k | x)
      · show t2.val k = t2.val (e (e.symm k))
        rw [Equiv.apply_symm_apply]
      · rfl
    · rintro (k | x) <;> rfl

end AEC
