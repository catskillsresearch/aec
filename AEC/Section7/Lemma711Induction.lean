module

public import AEC.Section7.Lemma711Limit
public import AEC.Section7.ProductFreeLevel
public import AEC.Section7.TiedDescent

/-!
# Lemma 7.11, induction on the stage (tied)

The paper proves Lemma 7.11 by induction on the stage `j ≤ δ` of the chain. The claim at stage
`j` (`TiedListWitnessingChain.Claim`) reads: every finite `x` over `M_δ` in the actual coupling
whose products with finite selections of marks `bᵢ`, `i < j`, are the tied products has
`tp(x/M_j)` free from `A`.

* First stage (`M_0 = A`): tied freeness along a bijective arrow
  (`infra_711_tiedFree_of_bijective`).
* Limit stage: `infra_711_limit_claim` (the tied Proposition 6.13 continuity on the stages below
  `j`, as in `infra_711_limit`).
* Successor stage: the hypothesis `infra_711_successor_statement` (open tip
  `infra_711_successor`).

`infra_711_induction` derives the full Lemma 7.11 statement from the successor statement.
-/

@[expose] public section

namespace AEC
noncomputable section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

section
variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}

/-- **Tied freeness along a bijective arrow** (`M_0 = A`). Same argument as
`infra_78_tiedFree_of_id`, reading the query through the inverse of the arrow. -/
theorem infra_711_tiedFree_of_bijective {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hbij : ∀ v, Function.Bijective (f.onVertex v))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B) :
    IsTiedFree f (q.restrict f hf) q (Equiv.refl _) := by
  intro seq ι Z Z0 hκI hι hιμ hmove
  let Z' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun t => ⟨(Z t).1, Function.surjInv (hbij (Z t).1).2 (Z t).2⟩
  have hZ' : ∀ t, (⟨(Z' t).1, f.onVertex (Z' t).1 (Z' t).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) = Z t := by
    intro t
    show (⟨(Z t).1, f.onVertex (Z t).1 (Function.surjInv (hbij (Z t).1).2 (Z t).2)⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ B)) = Z t
    exact Sigma.ext rfl (heq_of_eq (Function.surjInv_eq (hbij (Z t).1).2 (Z t).2))
  have hb0 := seq.few_exceptions Z0 hι
  have hb1 := seq.few_exceptions Z' hι
  have hex : ∃ i, P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q.restrict f hf) Z0) (seqJoint (seq.family i) Z0) ∧
      P.scheme.DiagramEq (X := q.host) (Y := A)
      (typeJoint (p := q.restrict f hf) Z') (seqJoint (seq.family i) Z') := by
    by_contra hno
    have hsub : (Set.univ : Set seq.κIndex) ⊆
        {i | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
          (typeJoint (p := q.restrict f hf) Z0) (seqJoint (seq.family i) Z0)} ∪
        {i | ¬ P.scheme.DiagramEq (X := q.host) (Y := A)
          (typeJoint (p := q.restrict f hf) Z') (seqJoint (seq.family i) Z')} := by
      intro i _
      by_cases h0 : P.scheme.DiagramEq (X := q.host) (Y := A)
          (typeJoint (p := q.restrict f hf) Z0) (seqJoint (seq.family i) Z0)
      · exact Or.inr fun h1 => hno ⟨i, h0, h1⟩
      · exact Or.inl h0
    have hc := (Cardinal.mk_le_mk_of_subset hsub).trans (Cardinal.mk_union_le _ _)
    rw [Cardinal.mk_univ] at hc
    have hτ : #ι + ℵ₀ ≤ seq.τ + ℵ₀ := add_le_add hι le_rfl
    have h2 : #seq.κIndex ≤ seq.τ + ℵ₀ :=
      hc.trans ((add_le_add (hb0.trans hτ) (hb1.trans hτ)).trans
        (Cardinal.add_eq_self ((le_add_left le_rfl : ℵ₀ ≤ seq.τ + ℵ₀))).le)
    exact absurd hκI (not_lt.2 h2)
  obtain ⟨i, h0, h1⟩ := hex
  have hmv := hmove i
  have hidx : #q.idx < μ := infra_78_idx_lt_of_seq (q := q.restrict f hf) seq hκI
  have hsum : #(q.idx ⊕ ι) < μ := by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hidx hιμ
  let ys := seqJoint (seq.family i) Z'
  have h2 := P.scheme.diagram_preserved A B f hf ys hsum hsum
  have hpush : (fun t => (⟨(ys t).1, f.onVertex (ys t).1 (ys t).2⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) =
      seqJoint (fun j => (⟨(seq.family i j).1,
        f.onVertex (seq.family i j).1 (seq.family i j).2⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ B))) Z := by
    funext t
    cases t with
    | inl a => rfl
    | inr t => exact hZ' t
  rw [hpush] at h2
  have hJ : typeJoint (p := q.restrict f hf) Z' =
      infra_612_anchored (Equiv.refl (q.restrict f hf).idx) q.incl q.val Z := by
    funext t
    cases t with
    | inl a => rfl
    | inr t =>
      show (⟨(Z' t).1, q.incl.onVertex (Z' t).1 (f.onVertex (Z' t).1 (Z' t).2)⟩ :
        Occurrence K oneVertexShape _) = ⟨(Z t).1, q.incl.onVertex (Z t).1 (Z t).2⟩
      have := hZ' t
      rw [← this]
  have key := P.scheme.diagram_trans _ _ _ _ _ _ h0
    (P.scheme.diagram_trans _ _ _ _ _ _ hmv
      (P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ h2)
        (P.scheme.diagram_symm _ _ _ _ h1)))
  exact hJ ▸ key

/-- Transport of tied freeness along equal tuples and equal arrows. -/
theorem infra_711_tiedFree_transport {X Y : P.scheme.Object μ hμ}
    {f f' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y)}
    {q q' : TupleOver K oneVertexShape P.scheme hμ Y} (hq : q = q') (hff : f = f')
    (hf : P.scheme.permitted (X := X) (Y := Y) f)
    (hf' : P.scheme.permitted (X := X) (Y := Y) f') :
    IsTiedFree f (q.restrict f hf) q (Equiv.refl _) →
      IsTiedFree f' (q'.restrict f' hf') q' (Equiv.refl _) := by
  subst hq; subst hff; exact id

/-- Restricting twice is restricting along the composite. -/
theorem infra_711_restrict_restrict {X Y Z : P.scheme.Object μ hμ}
    (q : TupleOver K oneVertexShape P.scheme hμ Z)
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ Z))
    (hf : P.scheme.permitted (X := Y) (Y := Z) f)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
    (hg : P.scheme.permitted (X := X) (Y := Y) g)
    (k : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Z))
    (hk : P.scheme.permitted (X := X) (Y := Z) k) (h : SystemArrow.comp g f = k) :
    (q.restrict f hf).restrict g hg = q.restrict k hk := by
  subst h; rfl

end

namespace TiedListWitnessingChain

variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
  {A : P.scheme.Object μ hμ} {L : TupleList P.scheme hμ A} [LinearOrder L.δ]

/-- `x` has the tied product with every finite injective selection of marks below stage `k`. -/
def prodBelow (C : TiedListWitnessingChain L)
    (x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤)) (k : WithTop L.δ) : Prop :=
  ∀ (n : ℕ) (ix : Fin n → L.δ), Function.Injective ix →
    (∀ s, ((ix s : L.δ) : WithTop L.δ) < k) →
    IsProductTied (x.restrict (C.into ⊤) (C.into_arrow ⊤)) (C.selectionOver x n ix)
      (C.jointWith x n ix) (Equiv.refl _)

/-- `tp(x/M_k)` is free from `A` (tied). -/
def freeAt (C : TiedListWitnessingChain L)
    (x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤)) (k : WithTop L.δ) : Prop :=
  IsTiedFree (C.into k)
    ((x.restrict (C.step (le_top : k ≤ ⊤)) (C.step_arrow _)).restrict (C.into k) (C.into_arrow k))
    (x.restrict (C.step (le_top : k ≤ ⊤)) (C.step_arrow _)) (Equiv.refl _)

/-- The induction claim of Lemma 7.11 at stage `k`. -/
def Claim (C : TiedListWitnessingChain L) (k : WithTop L.δ) : Prop :=
  ∀ x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤),
    Finite x.idx → x.ν = μ → C.prodBelow x k → C.freeAt x k

theorem prodBelow_mono (C : TiedListWitnessingChain L)
    {x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤)} {i j : WithTop L.δ} (hij : i ≤ j)
    (h : C.prodBelow x j) : C.prodBelow x i :=
  fun n ix hinj hlt => h n ix hinj (fun s => (hlt s).trans_le hij)

/-- First stage: `M_0 = A`. -/
theorem claim_first (C : TiedListWitnessingChain L) (j : WithTop L.δ) (hmin : ∀ k, j ≤ k) :
    C.Claim j := fun _ _ _ _ =>
  infra_711_tiedFree_of_bijective (C.into j) (C.first j hmin) (C.into_arrow j) _

/-- Limit stage (tied Proposition 6.13 continuity on the stages below `j`). -/
theorem claim_limit [WellFoundedLT L.δ] (hrec : μ ∈ recursionClosedLevels P ℵ₀)
    (hσμ : Order.succ ℵ₀ ≤ μ) (C : TiedListWitnessingChain L) (j : WithTop L.δ)
    (hnc : ∀ i, ¬ i ⋖ j) (hex : ∃ i, i < j) (IH : ∀ i, i < j → C.Claim i) : C.Claim j := by
  classical
  intro x hfin hxν hprod
  let p := x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)
  have : Finite p.idx := hfin
  let D := infra_711_belowChain C j hnc hex
  have hcard : #p.idx ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hcof : #p.idx < D.δ.cof :=
    lt_of_lt_of_le (Cardinal.lt_aleph0_of_finite _) D.cof_aleph0
  have h0 := D.hlim.1
  let e0 := Ordinal.enum (α := {i : WithTop L.δ // i < j}) (· < ·) ⟨0, h0⟩
  have hres := infra_78_tied_continuity P ℵ₀ le_rfl hμ hrec hσμ D p hxν hcard hcof A
    (C.into e0.1) (C.into_arrow _) (fun k hk => by
      let ek := Ordinal.enum (α := {i : WithTop L.δ // i < j}) (· < ·) ⟨k, hk⟩
      have hc : C.freeAt x ek.1 := IH ek.1 ek.2 x hfin hxν (C.prodBelow_mono ek.2.le hprod)
      refine infra_711_tiedFree_transport ?_ ?_ (C.into_arrow _) _ hc
      · refine (infra_711_restrict_restrict x _ _ _ _ _ _ ?_).symm
        apply SystemArrow.ext; intro v; exact C.step_comp _ _ v
      · apply SystemArrow.ext; intro v; exact (C.into_step _ v).symm)
  refine infra_711_tiedFree_transport rfl ?_ _ (C.into_arrow j) hres
  apply SystemArrow.ext; intro v; exact C.into_step _ v

/-- The induction over the stages, given the successor step. -/
theorem claim_all [WellFoundedLT L.δ] (hrec : μ ∈ recursionClosedLevels P ℵ₀)
    (hσμ : Order.succ ℵ₀ ≤ μ) (C : TiedListWitnessingChain L)
    (hsucc : ∀ i j : WithTop L.δ, i ⋖ j → C.Claim i → C.Claim j) (j : WithTop L.δ) :
    C.Claim j := by
  classical
  induction j using WellFoundedLT.induction with
  | _ j IH =>
    by_cases hmin : ∀ k, j ≤ k
    · exact C.claim_first j hmin
    · by_cases hs : ∃ i, i ⋖ j
      · obtain ⟨i, hi⟩ := hs
        exact hsucc i j hi (IH i hi.lt)
      · push Not at hs hmin
        obtain ⟨k, hk⟩ := hmin
        exact C.claim_limit hrec hσμ j hs ⟨k, hk⟩ IH

end TiedListWitnessingChain

/-- **Lemma 7.11, successor step (statement).** At a successor stage `j` (`i ⋖ j`) of a tied
chain with all-dominated increments, the induction claim passes from `i` to `j`. -/
def infra_711_successor_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ] (C : TiedListWitnessingChain L), C.AllDominatedIncrement →
      ∀ i j : WithTop L.δ, i ⋖ j → C.Claim i → C.Claim j

/-- **Lemma 7.11 from its successor step** (`infra_711_induction`). The conclusion is
literally the statement of `lemma_7_11`. -/
theorem infra_711_induction (P : SingleModelData K) (hsucc : infra_711_successor_statement P) :
    ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (L : TupleList P.scheme (Tail.mem hT hμ) A) [LinearOrder L.δ] [WellFoundedLT L.δ]
        (C : TiedListWitnessingChain L),
        C.AllDominatedIncrement →
        ∀ (x : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) (C.stage ⊤)),
          Finite x.idx → x.ν = μ →
          (∀ (n : ℕ) (ix : Fin n → L.δ), Function.Injective ix →
            IsProductTied (x.restrict (C.into ⊤) (C.into_arrow ⊤)) (C.selectionOver x n ix)
              (C.jointWith x n ix) (Equiv.refl _)) →
          IsTiedFree (C.into ⊤) (x.restrict (C.into ⊤) (C.into_arrow ⊤)) x (Equiv.refl _) := by
  classical
  let w : Cardinal.{u} := infra_75_wide P ℵ₀
  have hw : ℵ₀ ≤ w := le_self_add
  let T : Set Cardinal.{u} :=
    {μ | μ ∈ recursionClosedLevels P w ∧ Order.succ w ≤ μ}
  have hT : Tail P.eligible T := by
    refine ⟨fun μ hμ => hμ.1.1, fun κ => ?_⟩
    obtain ⟨μ, hle, hμ, hrec⟩ :=
      (infra_69_recursion_tail P hw).2 (max κ (Order.succ w))
    exact ⟨μ, (le_max_left _ _).trans hle, ⟨⟨hμ, hrec⟩, (le_max_right _ _).trans hle⟩⟩
  refine ⟨T, hT, fun μ hμ A L _ _ C hinc x hfin hxν hprod => ?_⟩
  have h0 : μ ∈ recursionClosedLevels P ℵ₀ := infra_76_rec_mono hw hμ.1
  have h1 : Order.succ ℵ₀ ≤ μ := (Order.succ_le_succ hw).trans hμ.2
  have hall := C.claim_all h0 h1
    (fun i j h => hsucc (Tail.mem hT hμ) h0 h1 hμ.1 hμ.2 A L C hinc i j h) ⊤
  have hfree := hall x hfin hxν (fun n ix hinj _ => hprod n ix hinj)
  have hid : ∀ v y, (C.step (le_top : (⊤ : WithTop L.δ) ≤ ⊤)).onVertex v y = y := by
    intro v y
    have hc := C.step_comp (le_top : (⊤ : WithTop L.δ) ≤ ⊤) (le_top : (⊤ : WithTop L.δ) ≤ ⊤) v
    have hy := congrArg (fun e => e y) hc
    exact (C.step (le_top : (⊤ : WithTop L.δ) ≤ ⊤)).onVertex v |>.injective hy
  have hx : x.restrict (C.step (le_top : (⊤ : WithTop L.δ) ≤ ⊤)) (C.step_arrow _) = x := by
    cases x with
    | mk ν hν host incl incl_arrow idx val =>
      have : SystemArrow.comp (C.step (le_top : (⊤ : WithTop L.δ) ≤ ⊤)) incl = incl := by
        apply SystemArrow.ext; intro v
        ext y
        exact congrArg (fun z => incl.onVertex v z) (hid v y)
      simp only [TupleOver.restrict, this]
  exact infra_711_tiedFree_transport hx rfl _ _ hfree

end
end AEC
