module

public import AEC.Section7.AssemblyGlue
public import AEC.Section6.GaloisCrossLevel

@[expose] public section

/-!
# Prop 7.8 for `p` hosted at any level (`infra_78_marginal_general_level`)

`proposition_7_8` allows `p` over `X` with any host level `p.ν ≥ λ`. Reduction (cycle 67):
`infra_612_exists_level_copy` gives `p'` with the same index type, host at `λ`, and
`SameGaloisType p p'` by a direct witness (a sub-presentation of the chart of `p.host`);
`infra_78_matrix_assembly_level` gives the extension `X ≤ U` for `p'`; and
`infra_612_galois_trans_cross_level_right_base` (first host at any level, middle and last at `λ`)
composes `p ~ p' ~ (mark in U)`. The isolation clause does not mention `p`.
-/

universe u

open Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **`infra_78_marginal_general_level` (proved).** The `proposition_7_8` conclusion on the tail
`infra_78_closedTail P` for every finite-tuple `p` over `X`, hosted at any eligible level. -/
theorem infra_78_marginal_general_level (P : SingleModelData K) :
    ∀ μ (hμ : μ ∈ infra_78_closedTail P)
      (X : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
      (p : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X)
      (θ : Cardinal.{u}),
      Finite p.idx → aleph0 ≤ θ → θ < μ →
      ∃ (U : P.scheme.Object μ (Tail.mem (infra_78_closedTail_tail P) hμ))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ X) (P.scheme.asSystem _ U))
        (hf : P.scheme.permitted (X := X) (Y := U) f)
        (b : p.idx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)) (e : p.idx ≃ p.idx),
        SameGaloisType p (asTuple f hf b) e (Equiv.refl p.idx) ∧
        ∀ {cIdx : Type u} (c : cIdx → Occurrence K oneVertexShape (P.scheme.asSystem _ U)),
          #cIdx ≤ θ →
          IsRelativelyIsolated (uIdx := p.idx) (cIdx := cIdx)
            (asTuple f hf (seqJoint b c)) (Equiv.refl (p.idx ⊕ cIdx)) := by
  intro μ hμ X p θ hfin hθ hθμ
  have hel : μ ∈ P.eligible := Tail.mem (infra_78_closedTail_tail P) hμ
  have hlt : ℵ₀ < μ := P.aleph0_lt hel
  have hidx0 : #p.idx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite p.idx).le
  obtain ⟨host, incl, hincl, val, h12⟩ :=
    infra_612_exists_level_copy p (hidx0.trans (P.aleph0_le hel))
  let p' : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_78_closedTail_tail P) hμ) X :=
    ⟨μ, Tail.mem (infra_78_closedTail_tail P) hμ, host, incl, hincl, p.idx, val⟩
  obtain ⟨U, f, hf, b, e, hgal, hiso⟩ :=
    infra_78_matrix_assembly_level P μ hμ X p' θ hfin rfl hθ hθμ
  refine ⟨U, f, hf, b, e, ?_, hiso⟩
  have hrec : μ ∈ recursionClosedLevels P ℵ₀ := (hμ.2.1 ℵ₀ le_rfl hlt).1
  have h := infra_612_galois_trans_cross_level_right_base (t1 := p) (t2 := p')
    (t3 := asTuple f hf b) (e12 := Equiv.refl p.idx) (e32 := e.symm) h12
    (SameGaloisType.swap_refl hgal) ℵ₀ le_rfl hlt hidx0 hrec rfl rfl
  simp only [Equiv.refl_trans] at h
  exact h

end AEC
