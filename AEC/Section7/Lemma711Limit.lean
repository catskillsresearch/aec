module

public import AEC.Section7.TiedListChain
public import AEC.Section6.LocalCharacterTied

/-!
# Lemma 7.11, limit step (tied)

At a limit stage `j` of a `TiedListWitnessingChain` (no predecessor, not the first stage), if a
finite tuple `p` over `M_j` (realized at the base level) has `tp(p/Mᵢ)` free from `A` for every
`i < j`, then `tp(p/M_j)` is free from `A`.  The paper: "local character for the finite tuple
`x` gives a proper stage `i < j` from which `x/M_j` is free; the induction hypothesis and
transitivity give freeness from `A`."  This is exactly the second clause of the tied
Proposition 6.13 (`proposition_6_13`, which packages local character + transitivity), applied to
the stages below `j` re-indexed by their order type (`Ordinal.enum`), with union `M_j`
(the `continuous` field of the chain).
-/

@[expose] public section

namespace AEC
noncomputable section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- Tied freeness only depends on the arrow, not on the way it is written. -/
theorem infra_711_tiedFree_arrow_congr {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y : P.scheme.Object μ hμ}
    {f f' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y)}
    (h : f = f') (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (hf' : P.scheme.permitted (X := X) (Y := Y) f')
    (q : TupleOver K oneVertexShape P.scheme hμ Y) :
    IsTiedFree f (q.restrict f hf) q (Equiv.refl _) →
      IsTiedFree f' (q.restrict f' hf') q (Equiv.refl _) := by
  subst h; exact id

/-- **Lemma 7.11, limit step (statement).** -/
def infra_711_limit_statement (P : SingleModelData K) : Prop :=
  ∃ T, ∃ hT : Tail P.eligible T,
    ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
      (L : TupleList P.scheme (Tail.mem hT hμ) A) [LinearOrder L.δ] [L.FiniteEach] [WellFoundedLT L.δ]
      (C : TiedListWitnessingChain L) (j : WithTop L.δ),
      (∀ i, ¬ i ⋖ j) → (∃ i, i < j) →
      ∀ (p : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) (C.stage j)),
        p.ν = μ → Finite p.idx →
        (∀ (i : WithTop L.δ) (h : i < j),
          IsTiedFree (C.into i)
            ((p.restrict (C.step h.le) (C.step_arrow h.le)).restrict (C.into i) (C.into_arrow i))
            (p.restrict (C.step h.le) (C.step_arrow h.le)) (Equiv.refl _)) →
        IsTiedFree (C.into j) (p.restrict (C.into j) (C.into_arrow j)) p (Equiv.refl _)

/-- The stages below a limit stage `j`, as a `SameLevelChain` with union `M_j`. -/
def infra_711_belowChain {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {L : TupleList P.scheme hμ A} [LinearOrder L.δ] [L.FiniteEach]
    [WellFoundedLT L.δ] (C : TiedListWitnessingChain L) (j : WithTop L.δ)
    (hnc : ∀ i, ¬ i ⋖ j) (hex : ∃ i, i < j) : SameLevelChain P hμ := by
  classical
  let α := {i : WithTop L.δ // i < j}
  let r : α → α → Prop := (· < ·)
  let e : (k : Ordinal.{u}) → k < Ordinal.type r → α := fun k hk => Ordinal.enum r ⟨k, hk⟩
  have emono : ∀ {k k' : Ordinal.{u}} (hk : k < Ordinal.type r) (hk' : k' < Ordinal.type r),
      k ≤ k' → (e k hk).1 ≤ (e k' hk').1 := by
    intro k k' hk hk' hkk'
    have := (Ordinal.enum_le_enum r (o₁ := ⟨k', hk'⟩) (o₂ := ⟨k, hk⟩)).2 hkk'
    exact not_lt.1 this
  exact
  { δ := Ordinal.type r
    hlim := by
      obtain ⟨i0, hi0⟩ := hex
      have hne : Nonempty α := ⟨⟨i0, hi0⟩⟩
      have hpos : (0 : Ordinal.{u}) < Ordinal.type r :=
        pos_iff_ne_zero.2 (Ordinal.type_ne_zero_iff_nonempty.2 hne)
      refine ⟨hpos, (Order.isSuccLimit_iff _).2 ⟨not_isMin_iff.2 ⟨0, hpos⟩, ?_⟩⟩
      intro b hb
      let m : α := e b hb.lt
      apply hnc m.1
      refine ⟨m.2, fun y hmy hyj => ?_⟩
      let a : α := ⟨y, hyj⟩
      have hta : Ordinal.typein r a ≤ b := hb.le_of_lt (Ordinal.typein_lt_type r a)
      have h1 : (e _ (Ordinal.typein_lt_type r a)).1 ≤ m.1 := emono _ _ hta
      have h2 : e _ (Ordinal.typein_lt_type r a) = a := Ordinal.enum_typein r a
      rw [h2] at h1
      exact absurd hmy (not_lt.2 h1)
    obj := fun k hk => C.stage (e k hk).1
    le := fun hk hk' hkk' => C.step (emono hk hk' hkk')
    le_arrow := fun hk hk' hkk' => C.step_arrow _
    le_comp := fun hi hj hk hij hjk => by
      apply SystemArrow.ext; intro v; exact C.step_comp _ _ v
    unionObj := C.stage j
    toUnion := fun k hk => C.step (e k hk).2.le
    toUnion_arrow := fun k hk => C.step_arrow _
    toUnion_comp := fun hi hj hij => by
      apply SystemArrow.ext; intro v; exact C.step_comp _ _ v
    joint := fun x => by
      obtain ⟨v, y⟩ := x
      obtain ⟨i, h, y', hy⟩ := C.continuous j hnc hex v y
      let a : α := ⟨i, h⟩
      refine ⟨Ordinal.typein r a, Ordinal.typein_lt_type r a, ?_⟩
      have key : ∀ b : α, b = a → ∃ z : Occurrence K oneVertexShape
          (P.scheme.asSystem hμ (C.stage b.1)), pushOcc (C.step b.2.le) z = ⟨v, y⟩ := by
        rintro b rfl
        exact ⟨⟨v, y'⟩, by rw [← hy]⟩
      exact key _ (Ordinal.enum_typein r a) }

/-- **Lemma 7.11, limit step (proved).** -/
theorem infra_711_limit (P : SingleModelData K) : infra_711_limit_statement P := by
  classical
  obtain ⟨T, hT, H⟩ := proposition_6_13 P aleph0 le_rfl
  refine ⟨T, hT, fun μ hμ A L _ _ _ C j hnc hex p hpν hfin hfree => ?_⟩
  let D := infra_711_belowChain C j hnc hex
  have hcard : #p.idx ≤ aleph0 := Cardinal.mk_le_aleph0
  have hcof : #p.idx < D.δ.cof :=
    lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite _) D.cof_aleph0
  obtain ⟨-, H2⟩ := H μ hμ D p hpν hcard hcof
  have h0 := D.hlim.1
  let g := C.into (Ordinal.enum (α := {i : WithTop L.δ // i < j}) (· < ·) ⟨0, h0⟩).1
  have hgen := H2 A g (C.into_arrow _) (fun k hk => by
    let ek := Ordinal.enum (α := {i : WithTop L.δ // i < j}) (· < ·) ⟨k, hk⟩
    refine infra_711_tiedFree_arrow_congr ?_ (C.into_arrow _) _ _ (hfree ek.1 ek.2)
    apply SystemArrow.ext; intro v; exact (C.into_step _ v).symm)
  refine infra_711_tiedFree_arrow_congr ?_ _ (C.into_arrow j) p hgen
  apply SystemArrow.ext; intro v; exact C.into_step _ v

end
end AEC
