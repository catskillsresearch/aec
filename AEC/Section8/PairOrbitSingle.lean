module

public import AEC.Section8.PairPointedSingle

@[expose] public section

/-!
# Lemma 8.2, clause (4), for the Prop 5.6 scheme: reduction pieces (cycle 96)

English (Lemma 8.2): "Same-level arrows preserve bounded pair orbits." Pair orbits are pair
isomorphism orbits (Section 8.4: "Define comparison of bounded term patterns by their pair
isomorphism orbits at any eligible level"). The proof (paper lines 3010–3018) produces a base
automorphism matching bounded approximation lists "by bounded diagram homogeneity in C" and then
applies the pair isomorphism test (clause 3). This file proves the reduction: an automorphism of
the base that keeps the prescribed type of the mark (positionwise) and matches the diagram of a
bounded isolating fragment extends to a pair automorphism taking `s` to `s′`
(`infra_82_orbit_criterion_single`). Bounded diagram homogeneity for `P.scheme` is the
`diagram_iso` field (Definition 5.2(3): "At each level, two bounded lists have the same diagram
if and only if a structural isomorphism between their objects takes one list to the other").
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Lemma 8.2(4) reduction for the Prop 5.6 scheme.** On the clause-(3) tail, for a marked pair
`N` and a bounded tuple `s` of `N.Y`, there is a bounded isolating fragment `Z` of the base such
that every automorphism `e` of the base that (a) matches the base entries of `s` with those of
`s′`, (b) keeps the prescribed type of the mark positionwise, and (c) carries the diagram of
`(b, s, Z)` to that of `(b, s′, e Z)`, extends to a pair automorphism (marks fixed positionwise)
taking `s` to `s′`. -/
theorem infra_82_orbit_criterion_single (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ T, ∃ _hT : Tail P.scheme.eligible T,
      ∀ (N : MarkedPair K oneVertexShape P.scheme Pr), N.μ ∈ T →
      ∀ {ι : Type u} (s : ι → Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y)),
        #ι < N.μ →
        ∃ (γ : Type u) (Z : γ → Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.X)),
          #γ < N.μ ∧
          ∀ (e : SystemArrow K oneVertexShape (P.scheme.asSystem N.hμ N.X)
              (P.scheme.asSystem N.hμ N.X))
            (_he : P.scheme.permitted (X := N.X) (Y := N.X) e),
            (∀ v, Function.Bijective (e.onVertex v)) →
            ∀ s' : ι → Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.Y),
            (∀ i (x : Occurrence K oneVertexShape (P.scheme.asSystem N.hμ N.X)),
                s i = N.incl.mapOcc x → s' i = N.incl.mapOcc (e.mapOcc x)) →
            SameGaloisType (asTuple N.incl N.incl_arrow N.b)
              (⟨N.μ, N.hμ, N.Y, SystemArrow.comp e N.incl, trivial, N.bIdx, N.b⟩ :
                TupleOver K oneVertexShape P.scheme N.hμ N.X) (Equiv.refl _) (Equiv.refl _) →
            P.scheme.DiagramEq (X := N.Y) (Y := N.Y)
              (seqJoint (seqJoint N.b s) (fun j => N.incl.mapOcc (Z j)))
              (seqJoint (seqJoint N.b s') (fun j => N.incl.mapOcc (e.mapOcc (Z j)))) →
            ∃ arr : MarkedArrow K oneVertexShape P.scheme Pr N N, arr.onX = e ∧
              arr.markMap = Equiv.refl _ ∧ (∀ v, Function.Bijective (arr.onY.onVertex v)) ∧
              ∀ i, arr.onY.mapOcc (s i) = s' i := by
  obtain ⟨T, hT, H3⟩ := infra_82_pointed_single P Pr
  refine ⟨T, hT, fun N hN ι s hι => ?_⟩
  obtain ⟨γ, Z, hγ, HZ⟩ := N.dominated ι s hι
  refine ⟨γ, Z, hγ, fun e he hbij s' hbase hb hd => ?_⟩
  let q' : TupleOver K oneVertexShape P.scheme N.hμ N.X :=
    ⟨N.μ, N.hμ, N.Y, SystemArrow.comp e N.incl, trivial, N.bIdx ⊕ ι, seqJoint N.b s'⟩
  have hd' : P.scheme.DiagramEq (X := N.Y) (Y := q'.host)
      (alignJoint (Equiv.refl _)
        (typeJoint (p := asTuple N.incl N.incl_arrow (seqJoint N.b s)) Z))
      (alignJoint (Equiv.refl _) (typeJoint (p := q') Z)) := by
    have key : ∀ {α : Type u} (xs xs' ys ys' : α → Occurrence K oneVertexShape
        (P.scheme.asSystem N.hμ N.Y)), xs = xs' → ys = ys' →
        P.scheme.DiagramEq (X := N.Y) (Y := N.Y) xs ys →
        P.scheme.DiagramEq (X := N.Y) (Y := N.Y) xs' ys' := by
      intro _ _ _ _ _ h1 h2 h; subst h1 h2; exact h
    refine key _ _ _ _ ?_ ?_ hd
    · funext x; rcases x with (j | j) | j <;> rfl
    · funext x; rcases x with (j | j) | j <;> rfl
  have hm : SameGaloisType
      ((asTuple N.incl N.incl_arrow (seqJoint N.b s)).marginal (Equiv.refl _))
      (q'.marginal (Equiv.refl _)) (Equiv.refl _) (Equiv.refl _) := by
    rcases hb with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
    exact ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun j => hv j⟩
  have hG := HZ q' (Equiv.refl _) rfl hm hd'
  refine (H3 N N e hN hN hbij he (Equiv.refl _) s s' hι).mpr ⟨hbase, ?_⟩
  rcases hG with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun i => ?_⟩
  rcases i with i | j
  · exact hv (Sum.inr i)
  · exact hv (Sum.inl j)

/-- **Base automorphisms keep the mark's type (P.scheme).** If the prescription commutes with
isomorphisms (Definition 8.1), every structural automorphism `e` of the base of a marked pair keeps
`tp(b/X)` position by position. This is hypothesis (b) of `infra_82_orbit_criterion_single`. -/
theorem infra_82_mark_type_auto_single {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme} (hiso : Pr.CommutesWithIso)
    (N : MarkedPair K oneVertexShape P.scheme Pr)
    (e : SystemArrow K oneVertexShape (P.scheme.asSystem N.hμ N.X) (P.scheme.asSystem N.hμ N.X))
    (hbij : ∀ v, Function.Bijective (e.onVertex v)) :
    SameGaloisType (asTuple N.incl N.incl_arrow N.b)
      (⟨N.μ, N.hμ, N.Y, SystemArrow.comp e N.incl, trivial, N.bIdx, N.b⟩ :
        TupleOver K oneVertexShape P.scheme N.hμ N.X) (Equiv.refl _) (Equiv.refl _) := by
  obtain ⟨eb, hR⟩ := N.realizes
  have hk := hiso N.X N.X e trivial hbij
  have hκ : (Pr.arity N.hμ N.X).trans (Pr.arity N.hμ N.X).symm = Equiv.refl _ := by
    ext i; simp
  rw [hκ] at hk
  -- restrict the realization along `e`
  have hRe : SameGaloisType
      ((asTuple N.incl N.incl_arrow N.b).restrict e trivial)
      ((Pr.assign N.hμ N.X).restrict e trivial) eb (Equiv.refl _) := by
    rcases hR with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, fun v => ?_, hv⟩
    change (f1.onVertex v).comp ((N.incl.onVertex v).comp (e.onVertex v)) =
      (f2.onVertex v).comp (((Pr.assign N.hμ N.X).incl.onVertex v).comp (e.onVertex v))
    have h := congrArg (fun g => FirstOrder.Language.Embedding.comp g (e.onVertex v)) (hc v)
    simp only [FirstOrder.Language.Embedding.comp_assoc] at h ⊢
    exact h
  have hμ0 : ℵ₀ < N.μ := P.aleph0_lt N.hμ
  have hfinA : Finite (Pr.assign N.hμ N.X).idx := Finite.of_equiv _ (Pr.arity N.hμ N.X).symm
  have hfinB : Finite N.bIdx := Finite.of_equiv _ eb.symm
  have hA : #(Pr.assign N.hμ N.X).idx ≤ ℵ₀ :=
    (Cardinal.lt_aleph0_of_finite (Pr.assign N.hμ N.X).idx).le
  have hB : #N.bIdx ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite N.bIdx).le
  -- assign → assign∘e → (b over X via e)
  have h24 := infra_612_galois_trans_last_base hk hRe.symm ℵ₀ le_rfl hμ0 hA rfl
  have h24' := SameGaloisType.swap_refl h24
  have h14 := infra_612_galois_trans_last_base hR h24' ℵ₀ le_rfl hμ0 hB rfl
  rcases h14 with ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, fun i => ?_⟩
  have h := hv i
  have hidx : ∀ j : N.bIdx,
      (eb.trans ((Equiv.refl (Pr.assign N.hμ N.X).idx).trans eb.symm).symm.symm).symm j = j :=
    fun j => by simp
  erw [hidx i] at h
  exact h

end AEC
