module

public import AEC.Section7.Lemma712Recursion

/-!
# Lemma 7.12 (1): toward `infra_712_products` (cycle 86)

Product independence (`ProductIndependentTied`) gives *plain* finite tied products, whose partial
products may be hosted at any level. `infra_712_finiteProduct_toLevel` converts them to level
products (`IsFiniteProductTiedLevel`, where the proved level-joint symmetry / associativity /
permutation lemmas of Proposition 6.12 apply) by replacing every partial product with its
level-`μ` copy (`infra_612_exists_level_copy_arrow`). The Galois identifications pull back along
the copy's host arrow *inside the same amalgam* (`infra_712_sameGalois_pull`), so this uses no
cross-level transitivity and in particular not `infra_612_galois_trans_cross_level_both_off`.
-/

@[expose] public section

namespace AEC
noncomputable section
open Cardinal
variable {K : AbstractElementaryClass.{u}}
variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
  {A : P.scheme.Object μ hμ}

/-- Galois identifications pull back along a host relation (one amalgam, no transitivity). -/
theorem infra_712_sameGalois_pull {t' t s : TupleOver K oneVertexShape P.scheme hμ A}
    {r : SystemArrow K oneVertexShape (P.scheme.asSystem t'.hν t'.host)
      (P.scheme.asSystem t.hν t.host)} (hr : P.scheme.permitted (X := t'.host) (Y := t.host) r)
    {e : t'.idx ≃ t.idx} (hR : infra_78_HostRel t' t r e) {ι : Type u}
    {e1 : t.idx ≃ ι} {e2 : s.idx ≃ ι} (h : SameGaloisType t s e1 e2) :
    SameGaloisType t' s (e.trans e1) e2 := by
  obtain ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩ := h
  refine ⟨ρ, hρ, top, SystemArrow.comp r f1, f2, P.scheme.comp r f1 hr hf1, hf2, fun v => ?_,
    fun i => ?_⟩
  · rw [← hc v]
    ext x
    show f1.onVertex v (r.onVertex v (t'.incl.onVertex v x)) = _
    rw [hR.1 v x]; rfl
  · rw [← hv i]
    have hk := hR.2 (e.symm (e1.symm i))
    rw [Equiv.apply_symm_apply] at hk
    show (⟨(t'.val (e.symm (e1.symm i))).1, f1.onVertex _ (r.onVertex _
      (t'.val (e.symm (e1.symm i))).2)⟩ : Occurrence K oneVertexShape _) = _
    rw [hk]

/-- A level-`μ` copy with its host relation. -/
theorem infra_712_level_copy (t : TupleOver K oneVertexShape P.scheme hμ A) (hidx : #t.idx ≤ μ) :
    ∃ (t' : TupleOver K oneVertexShape P.scheme hμ A) (e : t'.idx ≃ t.idx)
      (r : SystemArrow K oneVertexShape (P.scheme.asSystem t'.hν t'.host)
        (P.scheme.asSystem t.hν t.host)),
      t'.ν = μ ∧ P.scheme.permitted (X := t'.host) (Y := t.host) r ∧ infra_78_HostRel t' t r e := by
  obtain ⟨host, incl, hincl, val, r, hr, hcomp, hval⟩ := infra_612_exists_level_copy_arrow t hidx
  refine ⟨⟨μ, hμ, host, incl, hincl, t.idx, val⟩, Equiv.refl _, r, rfl, hr, fun v x => ?_,
    fun k => ?_⟩
  · exact DFunLike.congr_fun (congrArg (fun f => f.onVertex v) hcomp) x
  · exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (hval _ k).symm)

/-- Tied products pull back along a host relation of the joint. -/
theorem infra_712_productTied_pull_joint {p q j j' : TupleOver K oneVertexShape P.scheme hμ A}
    {e : p.idx ⊕ q.idx ≃ j.idx}
    {r : SystemArrow K oneVertexShape (P.scheme.asSystem j'.hν j'.host)
      (P.scheme.asSystem j.hν j.host)} (hr : P.scheme.permitted (X := j'.host) (Y := j.host) r)
    {eJ : j'.idx ≃ j.idx} (hR : infra_78_HostRel j' j r eJ) (h : IsProductTied p q j e) :
    IsProductTied p q j' (e.trans eJ.symm) := by
  obtain ⟨x, ex, hS, y, ey, hT, hJ⟩ := h
  refine ⟨x, ex, hS, y, ey, hT, ?_⟩
  exact infra_712_sameGalois_pull hr hR hJ

/-- Tied products pull back along a host relation of the first factor. -/
theorem infra_712_productTied_pull_left {p p' q j : TupleOver K oneVertexShape P.scheme hμ A}
    {e : p.idx ⊕ q.idx ≃ j.idx}
    {r : SystemArrow K oneVertexShape (P.scheme.asSystem p'.hν p'.host)
      (P.scheme.asSystem p.hν p.host)} (hr : P.scheme.permitted (X := p'.host) (Y := p.host) r)
    {ep : p'.idx ≃ p.idx} (hR : infra_78_HostRel p' p r ep) (h : IsProductTied p q j e) :
    IsProductTied p' q j ((Equiv.sumCongr ep (Equiv.refl _)).trans e) := by
  obtain ⟨x, ex, hS, y, ey, hT, hJ⟩ := h
  refine ⟨x, ep.trans ex, infra_712_sameGalois_pull hr hR hS, y, ey, hT, ?_⟩
  have heq : ((Equiv.sumCongr ep (Equiv.refl q.idx)).trans e).symm.trans
      (Equiv.sumCongr (ep.trans ex) ey) = e.symm.trans (Equiv.sumCongr ex ey) := by
    ext k
    rcases hk : e.symm k with a | b <;> simp [hk]
  rw [heq]
  exact hJ

/-- **Plain finite tied products of finite factors are level products (proved, cycle 86).**
Every partial product (and the joint) is replaced by its level-`μ` copy
(`infra_612_exists_level_copy_arrow`); Galois identifications pull back along the copy's host
arrow inside the same amalgam, so no cross-level transitivity is used. -/
theorem infra_712_finiteProduct_toLevel :
    ∀ (n : ℕ) (b : Fin n → TupleOver K oneVertexShape P.scheme hμ A),
      (∀ i, Finite (b i).idx) →
      ∀ (j : TupleOver K oneVertexShape P.scheme hμ A) (E : (Σ i, (b i).idx) ≃ j.idx),
      IsFiniteProductTied n b j E →
      ∀ (j' : TupleOver K oneVertexShape P.scheme hμ A) (eJ : j'.idx ≃ j.idx)
        (r : SystemArrow K oneVertexShape (P.scheme.asSystem j'.hν j'.host)
          (P.scheme.asSystem j.hν j.host)),
        P.scheme.permitted (X := j'.host) (Y := j.host) r → infra_78_HostRel j' j r eJ →
        IsFiniteProductTiedLevel n b j' (E.trans eJ.symm)
  | 0, _, _, _, _, h, _, eJ, _, _, _ => ⟨fun k => h.false (eJ k)⟩
  | n + 1, b, hb, j, E, h, j', eJ, r, hr, hR => by
    obtain ⟨left, El, hL, e, hP, h1, h2⟩ := h
    have hfin : Finite left.idx := by
      have : Finite (Σ i : Fin n, (b i.castSucc).idx) := by
        have := fun i : Fin n => hb i.castSucc
        exact inferInstance
      exact Finite.of_equiv _ El
    obtain ⟨left', eL, rL, hν, hrL, hRL⟩ :=
      infra_712_level_copy left ((Cardinal.lt_aleph0_of_finite _).le.trans (P.aleph0_le hμ))
    have hIH : IsFiniteProductTiedLevel n (fun i => b i.castSucc) left' (El.trans eL.symm) :=
      infra_712_finiteProduct_toLevel n (fun i => b i.castSucc) (fun i => hb _) left El hL left'
        eL rL hrL hRL
    have hP1 : IsProductTied left' (b (Fin.last n)) j
        ((Equiv.sumCongr eL (Equiv.refl _)).trans e) :=
      infra_712_productTied_pull_left (p := left) (p' := left') (q := b (Fin.last n)) (j := j)
        (e := e) hrL hRL hP
    have hP2 : IsProductTied left' (b (Fin.last n)) j'
        (((Equiv.sumCongr eL (Equiv.refl _)).trans e).trans eJ.symm) :=
      infra_712_productTied_pull_joint (p := left') (q := b (Fin.last n)) (j := j) (j' := j')
        (e := (Equiv.sumCongr eL (Equiv.refl _)).trans e) hr hR hP1
    refine ⟨left', El.trans eL.symm, hν, hIH,
      ((Equiv.sumCongr eL (Equiv.refl _)).trans e).trans eJ.symm, hP2, fun i k => ?_, fun k => ?_⟩
    · show eJ.symm (E ⟨i.castSucc, k⟩) = eJ.symm (e (Sum.inl (eL (eL.symm (El ⟨i, k⟩)))))
      rw [Equiv.apply_symm_apply, h1]
    · show eJ.symm (E ⟨Fin.last n, k⟩) = eJ.symm (e (Sum.inr k))
      rw [h2]

end
end AEC
