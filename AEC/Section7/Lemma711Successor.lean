module

public import AEC.Section7.Lemma711Induction
public import AEC.Section6.GaloisCrossLevel

/-!
# Lemma 7.11, successor step (tied)

At a successor stage `j` (`i ⋖ j`) the paper argues: by induction `tp(x/Mᵢ)` is free from `A`;
`x` and `bᵢ` have product over `Mᵢ` (induction applied to `(x, bᵢ)` and free base change of the
products over `A`); `M_{i+1}` is all-dominated over `Mᵢ + bᵢ`, so Proposition 7.5(3) makes
`tp(x/M_{i+1})` free from `Mᵢ`; transitivity gives freeness from `A`.

`infra_711_successor_of_product` proves the step from the product over `Mᵢ`
(`infra_711_succ_product_statement`), using the proved level form of 7.5(3)
(`infra_75_product_free_level`) and tied transitivity (`infra_78_tiedFree_trans`). The product
over `Mᵢ` is `infra_711_succ_product` (cycle 83): `infra_711_succ_pair` (level-joint symmetry and
associativity) and `infra_711_succ_base_change` (level-joint 6.12 base change).
-/

@[expose] public section

namespace AEC
noncomputable section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- **Lemma 7.11 successor: the product over `Mᵢ` (statement; proved cycle 83 as
`infra_711_succ_product`).** Under the induction claim at `i`, a finite `x` in the actual coupling
with tied products with every finite selection of marks below `j = i + 1` has, over `Mᵢ`, the tied
product of `tp(x/Mᵢ)` with `tp(bᵢ/Mᵢ)` (`bᵢ` read in `M_j`, hosted with `x`). -/
def infra_711_succ_product_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ] (C : TiedListWitnessingChain L), C.AllDominatedIncrement →
      ∀ (i0 : L.δ) (j : WithTop L.δ) (h : (i0 : WithTop L.δ) ⋖ j),
        C.Claim (i0 : WithTop L.δ) →
        ∀ x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤), Finite x.idx → x.ν = μ →
          C.prodBelow x j →
          IsProductTied
            ((x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)).restrict
              (C.step h.le) (C.step_arrow h.le))
            (infra_75_markOver (C.step h.le) (C.step_arrow h.le)
              (x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)) (C.mark i0 j h.lt))
            (infra_75_jointOver (C.step h.le) (C.step_arrow h.le)
              (x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)) (C.mark i0 j h.lt))
            (Equiv.refl _)

/-- **Lemma 7.11 successor step from the product over `Mᵢ` (proved).** -/
theorem infra_711_successor_of_product (P : SingleModelData K)
    (hS : infra_711_succ_product_statement P) : infra_711_successor_statement P := by
  intro μ hμ h0 h1 hw1 hw2 A L _ _ C hinc i j hij hCi
  induction i using WithTop.recTopCoe with
  | top => exact absurd hij.lt (not_top_lt)
  | coe i0 =>
  intro x hfin hxν hprod
  have : Finite x.idx := hfin
  let xj := x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)
  have hP := hS hμ h0 h1 hw1 hw2 A L C hinc i0 j hij hCi x hfin hxν hprod
  have hb : #(L.indexAt i0) ≤ ℵ₀ := by
    have := L.finite_each i0
    exact Cardinal.mk_le_aleph0
  have hx : #xj.idx ≤ ℵ₀ := by
    have : Finite xj.idx := hfin
    exact Cardinal.mk_le_aleph0
  have h75 := infra_75_product_free_level P ℵ₀ le_rfl hμ h0 h1 hw1 hw2 (C.stage i0) (C.stage j)
    (C.step hij.le) (C.step_arrow _) (L.indexAt i0) (C.mark i0 j hij.lt) hb (hinc i0 j hij)
    xj hxν hx hP
  have IH := hCi x hfin hxν (C.prodBelow_mono hij.le hprod)
  have hXA : IsTiedFree (C.into (i0 : WithTop L.δ))
      ((xj.restrict (C.step hij.le) (C.step_arrow _)).restrict (C.into _) (C.into_arrow _))
      (xj.restrict (C.step hij.le) (C.step_arrow _)) (Equiv.refl _) := by
    refine infra_711_tiedFree_transport ?_ rfl (C.into_arrow _) (C.into_arrow _) IH
    refine (infra_711_restrict_restrict x _ _ _ _ _ _ ?_).symm
    apply SystemArrow.ext; intro v; exact C.step_comp _ _ v
  have htr := infra_78_tiedFree_trans (C.into (i0 : WithTop L.δ)) (C.into_arrow _)
    (C.step hij.le) (C.step_arrow _) xj hXA h75
  refine infra_711_tiedFree_transport rfl ?_ _ (C.into_arrow j) htr
  apply SystemArrow.ext; intro v; exact C.into_step _ v

/-- A one-block sigma over a finite type is finite. -/
theorem infra_711_finite_sigma1 {I : Type u} (h : Finite I) : Finite (Σ _s : Fin 1, I) :=
  Finite.of_injective (fun p : (Σ _s : Fin 1, I) => p.2) (by
    rintro ⟨a, x⟩ ⟨b, y⟩ hxy
    obtain rfl : a = b := Subsingleton.elim a b
    cases hxy; rfl)

/-- The pair `(x, bᵢ)` as a tuple over `M_δ` hosted with `x`. -/
def infra_711_pairUp {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} {L : TupleList P.scheme hμ A} [LinearOrder L.δ]
    (C : TiedListWitnessingChain L) (x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤))
    (i0 : L.δ) : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤) where
  ν := x.ν
  hν := x.hν
  host := x.host
  incl := x.incl
  incl_arrow := x.incl_arrow
  idx := (C.jointWith x 1 (fun _ => i0)).idx
  val := (C.jointWith x 1 (fun _ => i0)).val

/-- **7.11 successor, finite product rules (statement; proved cycle 83 as `infra_711_succ_pair`).**
`(x, bᵢ)` has the tied product with every finite selection of marks below `i` (from `x`'s
products with the selections together with `bᵢ`, `tp(bᵢ/Mᵢ)` free from `A`, and the level-joint
6.12 rules). -/
def infra_711_succ_pair_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ] (C : TiedListWitnessingChain L), C.AllDominatedIncrement →
      ∀ (i0 : L.δ) (j : WithTop L.δ), (i0 : WithTop L.δ) ⋖ j →
        ∀ x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤), Finite x.idx → x.ν = μ →
          C.prodBelow x j → C.prodBelow (infra_711_pairUp C x i0) (i0 : WithTop L.δ)

/-- **7.11 successor, free base change (statement; proved cycle 83 as `infra_711_succ_base_change`).**
With `tp(x/Mᵢ)` and `tp(x, bᵢ/Mᵢ)` free from `A` and `tp(bᵢ/Mᵢ)` free (the chain), the product
`x ⊗ bᵢ` over `A` lifts to the product over `Mᵢ` (Proposition 6.12, products lift freely). -/
def infra_711_succ_base_change_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ] (C : TiedListWitnessingChain L), C.AllDominatedIncrement →
      ∀ (i0 : L.δ) (j : WithTop L.δ) (h : (i0 : WithTop L.δ) ⋖ j),
        ∀ x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤), Finite x.idx → x.ν = μ →
          C.prodBelow x j → C.freeAt x (i0 : WithTop L.δ) →
          C.freeAt (infra_711_pairUp C x i0) (i0 : WithTop L.δ) →
          IsProductTied
            ((x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)).restrict
              (C.step h.le) (C.step_arrow h.le))
            (infra_75_markOver (C.step h.le) (C.step_arrow h.le)
              (x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)) (C.mark i0 j h.lt))
            (infra_75_jointOver (C.step h.le) (C.step_arrow h.le)
              (x.restrict (C.step (le_top : j ≤ ⊤)) (C.step_arrow _)) (C.mark i0 j h.lt))
            (Equiv.refl _)

/-- **The product over `Mᵢ` from its two parts (proved glue).** The induction claim at `i` is
applied to `x` and to `(x, bᵢ)`. -/
theorem infra_711_succ_product_of_parts (P : SingleModelData K)
    (h1 : infra_711_succ_pair_statement P) (h2 : infra_711_succ_base_change_statement P) :
    infra_711_succ_product_statement P := by
  intro μ hμ h0 h1' hw1 hw2 A L _ _ C hinc i0 j h hCi x hfin hxν hprod
  have hfin' : Finite (infra_711_pairUp C x i0).idx := by
    have h1 : Finite x.idx := hfin
    have h2 : Finite (Σ _s : Fin 1, L.indexAt i0) :=
      infra_711_finite_sigma1 (L.finite_each i0)
    change Finite (x.idx ⊕ (Σ _s : Fin 1, L.indexAt i0))
    infer_instance
  exact h2 hμ h0 h1' hw1 hw2 A L C hinc i0 j h x hfin hxν hprod
    (hCi x hfin hxν (C.prodBelow_mono h.le hprod))
    (hCi _ hfin' hxν (h1 hμ h0 h1' hw1 hw2 A L C hinc i0 j h x hfin hxν hprod))

/-- Tied freeness transports along a reindexing of the base tuple with diagram-equal joints. -/
theorem infra_711_tiedFree_base_equiv {P : SingleModelData K} {ν μ : Cardinal.{u}}
    {hν : ν ∈ P.eligible} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object ν hν} {B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hν A) (P.scheme.asSystem hμ B))
    (p p' : TupleOver K oneVertexShape P.scheme hν A) (φ : p'.idx ≃ p.idx)
    (qB : TupleOver K oneVertexShape P.scheme hμ B) (eB : p.idx ≃ qB.idx)
    (hD : ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hν A)),
      #ι < ν → P.scheme.DiagramEq (X := p'.host) (Y := p.host)
        (typeJoint (p := p') Z) (fun t => typeJoint (p := p) Z (Sum.map φ id t)))
    (hT : IsTiedFreeMixed f p qB eB) : IsTiedFreeMixed f p' qB (φ.trans eB) := by
  intro seq' ι Z Z0 hlong hι hιν hmv
  let seq : ApproximationSequence p :=
    { τ := #ι
      κIndex := seq'.κIndex
      family := fun i k => seq'.family i (φ.symm k)
      concat_bounded := by
        have h := seq'.concat_bounded
        rwa [Cardinal.mk_congr (Equiv.prodCongr (Equiv.refl seq'.κIndex) φ)] at h
      few_exceptions := fun {ι'} Z' h' => by
        have h0 := seq'.few_exceptions Z' (h'.trans hι)
        refine le_trans (Cardinal.mk_le_of_injective (f := fun s => (⟨s.1, ?_⟩ :
          {i : seq'.κIndex // ¬ P.scheme.DiagramEq (X := p'.host) (Y := A)
            (typeJoint (p := p') Z') (seqJoint (seq'.family i) Z')})) ?_) h0
        · intro hc
          apply s.2
          have d := hD Z' (h'.trans_lt hιν)
          have e := P.scheme.diagram_trans _ _ _ _ _ _ (P.scheme.diagram_symm _ _ _ _ d) hc
          have e2 := infra_73_scheme_comp e (Sum.map φ.symm id)
          refine infra_73_diagramEq_of_eq e2 ?_ ?_
          · rintro (k | z) <;> simp [typeJoint]
          · rintro (k | z) <;> rfl
        · intro s1 s2 h
          have h2 := congrArg Subtype.val h
          exact Subtype.ext h2 }
  have hlong' : seq.τ + ℵ₀ < #seq.κIndex :=
    show #ι + ℵ₀ < #seq'.κIndex from (add_le_add hι le_rfl).trans_lt hlong
  have hmv' : infra_78_isMoveMixed f seq Z Z0 := by
    intro i
    exact infra_73_diagramEq_of_eq (infra_73_scheme_comp (hmv i) (Sum.map φ.symm id))
      (by rintro (k | z) <;> rfl) (by rintro (k | z) <;> rfl)
  have T := hT seq Z Z0 hlong' le_rfl hιν hmv'
  have T2 := infra_73_scheme_comp T (Sum.map φ id)
  have d := hD Z0 hιν
  refine P.scheme.diagram_trans _ _ _ _ _ _ d (infra_73_diagramEq_of_eq T2 ?_ ?_)
  · intro t; rfl
  · rintro (k | z) <;> rfl

/-- Products are insensitive to a propositional change of the two inclusions. -/
theorem infra_711_isProductTied_incl_congr {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}
    {ν : Cardinal.{u}} {hν : ν ∈ P.eligible} {H : P.scheme.Object ν hν}
    {incl incl' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hν H)}
    {hi : P.scheme.permitted (X := A) (Y := H) incl}
    {hi' : P.scheme.permitted (X := A) (Y := H) incl'} {idx : Type u}
    {val : idx → Occurrence K oneVertexShape (P.scheme.asSystem hν H)}
    (q : TupleOver K oneVertexShape P.scheme hμ A)
    {val2 : idx ⊕ q.idx → Occurrence K oneVertexShape (P.scheme.asSystem hν H)}
    (h1 : incl = incl')
    (h : IsProductTied (⟨ν, hν, H, incl, hi, idx, val⟩ : TupleOver K oneVertexShape P.scheme hμ A)
      q (⟨ν, hν, H, incl, hi, idx ⊕ q.idx, val2⟩ : TupleOver K oneVertexShape P.scheme hμ A) (Equiv.refl _))
    : IsProductTied (⟨ν, hν, H, incl', hi', idx, val⟩ : TupleOver K oneVertexShape P.scheme hμ A)
      q (⟨ν, hν, H, incl', hi', idx ⊕ q.idx, val2⟩ : TupleOver K oneVertexShape P.scheme hμ A)
      (Equiv.refl _) := by
  subst h1; exact h

theorem infra_711_succ_base_change (P : SingleModelData K) :
    infra_711_succ_base_change_statement P := by
  intro μ hμ h0 h1 _ _ A L _ _ C _ i0 j h x hfin hxν hprod hFx hFxb
  classical
  have hσμ : ℵ₀ < μ := (Order.lt_succ ℵ₀).trans_le h1
  have hfinI : Finite (L.indexAt i0) := L.finite_each i0
  have hfinS : Finite (Σ _s : Fin 1, L.indexAt i0) := infra_711_finite_sigma1 hfinI
  rcases x with ⟨ν, hν, H, xi, hxi, idx, val⟩
  simp only at hxν
  subst hxν
  have hfinx : Finite idx := hfin
  set x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤) := ⟨ν, hν, H, xi, hxi, idx, val⟩
    with hxdef
  let ix1 : Fin 1 → L.δ := fun _ => i0
  have hinj : Function.Injective ix1 := fun a b _ => Subsingleton.elim a b
  have hprodA := hprod 1 ix1 hinj (fun _ => h.lt)
  let s0 := C.step (le_top : (i0 : WithTop L.δ) ≤ ⊤)
  let sj := C.step (le_top : j ≤ ⊤)
  let sij := C.step h.le
  have hs : ∀ v a, sj.onVertex v (sij.onVertex v a) = s0.onVertex v a := fun v a =>
    congrArg (fun e => e a) (C.step_comp h.le le_top v)
  let pB := x.restrict s0 (C.step_arrow _)
  let jB := (infra_711_pairUp C x i0).restrict s0 (C.step_arrow _)
  have hIncl : SystemArrow.comp (C.into ⊤) xi = SystemArrow.comp (C.into i0) (SystemArrow.comp s0 xi) := by
    apply SystemArrow.ext; intro v; ext a
    show xi.onVertex v ((C.into ⊤).onVertex v a) = xi.onVertex v (s0.onVertex v ((C.into i0).onVertex v a))
    rw [← C.into_step (le_top : (i0 : WithTop L.δ) ≤ ⊤) v]; rfl
  have hprodA' : IsProductTied (pB.restrict (C.into i0) (C.into_arrow _)) (C.selectionOver x 1 ix1)
      (jB.restrict (C.into i0) (C.into_arrow _)) (Equiv.refl _) :=
    infra_711_isProductTied_incl_congr (C.selectionOver x 1 ix1) hIncl hprodA
  -- the mark side: `tp(bᵢ/Mᵢ)` free from `A`, pushed into `x`'s host and reindexed
  let bT := asTuple s0 (C.step_arrow _) (C.mark i0 ⊤ (WithTop.coe_lt_top i0))
  have hfree : IsTiedFree (C.into (i0 : WithTop L.δ)) (bT.restrict (C.into i0) (C.into_arrow _))
      bT (Equiv.refl _) := C.free i0
  have hIμ : #(L.indexAt i0) < ν := Cardinal.mk_le_aleph0.trans_lt hσμ
  have hpush := infra_75_tiedFree_target_push (C.into (i0 : WithTop L.δ))
    (bT.restrict (C.into i0) (C.into_arrow _)) hIμ bT (Equiv.refl _) rfl xi hxi hfree
  let qB0 : TupleOver K oneVertexShape P.scheme hμ (C.stage (i0 : WithTop L.δ)) :=
    ⟨ν, hμ, H, SystemArrow.comp s0 xi, P.scheme.comp s0 xi (C.step_arrow _) hxi,
      L.indexAt i0, fun k => xi.mapOcc (C.mark i0 ⊤ (WithTop.coe_lt_top i0) k)⟩
  have hpush' : IsTiedFreeMixed (C.into (i0 : WithTop L.δ))
      (bT.restrict (C.into i0) (C.into_arrow _)) qB0 (Equiv.refl _) := hpush
  let sel := C.selectionOver x 1 ix1
  let φ : sel.idx ≃ L.indexAt i0 :=
    { toFun := fun p => p.2
      invFun := fun k => ⟨0, k⟩
      left_inv := by
        rintro ⟨a, k⟩
        obtain rfl : a = 0 := Subsingleton.elim a 0
        rfl
      right_inv := fun _ => rfl }
  have hα : ∀ {ι : Type u}, #ι < ν → #(L.indexAt i0 ⊕ ι) < ν := fun hι => by
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) hIμ hι
  have hQ : IsTiedFreeMixed (C.into (i0 : WithTop L.δ)) sel qB0 (φ.trans (Equiv.refl _)) := by
    refine infra_711_tiedFree_base_equiv _ (bT.restrict (C.into i0) (C.into_arrow _)) sel φ qB0
      (Equiv.refl _) ?_ hpush'
    intro ι Z hι
    have d := P.scheme.diagram_preserved (C.stage ⊤) H xi hxi
      (fun t => typeJoint (p := bT.restrict (C.into i0) (C.into_arrow _)) Z (Sum.map φ id t))
      (by
        have : Finite sel.idx := hfinS
        rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) (Cardinal.mk_le_aleph0.trans_lt hσμ) hι)
      (by
        have : Finite sel.idx := hfinS
        rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
        exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) (Cardinal.mk_le_aleph0.trans_lt hσμ) hι)
    refine P.scheme.diagram_symm _ _ _ _ (infra_73_diagramEq_of_eq d (fun t => rfl) ?_)
    rintro (k | z)
    · rfl
    · show (⟨(Z z).1, xi.onVertex (Z z).1 (s0.onVertex (Z z).1 ((C.into i0).onVertex (Z z).1 (Z z).2))⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ H)) =
        ⟨(Z z).1, xi.onVertex (Z z).1 ((C.into ⊤).onVertex (Z z).1 (Z z).2)⟩
      rw [← C.into_step (le_top : (i0 : WithTop L.δ) ≤ ⊤) (Z z).1]
      rfl
  -- the product over `Mᵢ`: a tied free lift of the mark over `x`'s host
  have hIσ : #(L.indexAt i0) ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hselσ : #sel.idx ≤ ℵ₀ := by
    have : Finite sel.idx := hfinS
    exact Cardinal.mk_le_aleph0
  have hxσ : #(pB.restrict (C.into i0) (C.into_arrow _)).idx ≤ ℵ₀ := by
    have : Finite (pB.restrict (C.into i0) (C.into_arrow _)).idx := hfinx
    exact Cardinal.mk_le_aleph0
  obtain ⟨y, ey, hyν, _, hyT⟩ :=
    infra_610_tied_free_lift P ℵ₀ le_rfl hμ h0 h1 (B := H) pB.incl pB.incl_arrow qB0 rfl hIσ
  have hprodB : IsProductTied pB qB0 (pB.join y) (Equiv.sumCongr (Equiv.refl _) ey) := by
    refine ⟨pB, Equiv.refl _, SameGaloisType.refl pB, y, ey, hyT, ?_⟩
    have hh : (Equiv.sumCongr (Equiv.refl pB.idx) ey).symm.trans
        (Equiv.sumCongr (Equiv.refl pB.idx) ey) = Equiv.refl (pB.idx ⊕ y.idx) :=
      Equiv.symm_trans_self _
    exact hh ▸ SameGaloisType.refl (pB.join y)
  have S := infra_612_tied_base_change_level_joints P ℵ₀ le_rfl hμ h0 h1
    (pB.restrict (C.into i0) (C.into_arrow _)) sel rfl rfl hxσ hselσ hμ h0 h1 le_rfl (C.stage (i0 : WithTop L.δ)) (C.into i0) (C.into_arrow _)
    (jB.restrict (C.into i0) (C.into_arrow _)) (Equiv.refl _) pB qB0 jB (pB.join y)
    (Equiv.refl _) (φ.trans (Equiv.refl _)) (Equiv.refl _) (Equiv.sumCongr (Equiv.refl _) ey)
    hprodA' hFx hQ hFxb hprodB rfl rfl hyν
  -- transport to the displayed tuples over `Mᵢ`
  have hinc : ∀ v a, sj.onVertex v (sij.onVertex v a) = s0.onVertex v a := hs
  refine ⟨pB, Equiv.refl _, ?_, y, ey, ?_, ?_⟩
  · have hperm := P.scheme.structural_iso H H (SystemArrow.refl _) (P.scheme.isStructIso_refl H)
    refine ⟨ν, hμ, H, SystemArrow.refl _, SystemArrow.refl _, hperm, hperm, ?_, fun _ => rfl⟩
    intro v
    ext a
    show xi.onVertex v (sj.onVertex v (sij.onVertex v a)) = xi.onVertex v (s0.onVertex v a)
    rw [hinc]
  · have hD : ∀ {ι : Type u} (Z : ι → Occurrence K oneVertexShape
        (P.scheme.asSystem hμ (C.stage (i0 : WithTop L.δ)))), #ι < ν →
        P.scheme.DiagramEq (X := H) (Y := H)
          (typeJoint (p := infra_75_markOver sij (C.step_arrow h.le)
            (x.restrict sj (C.step_arrow _)) (C.mark i0 j h.lt)) Z)
          (fun t => typeJoint (p := qB0) Z (Sum.map (Equiv.refl _) id t)) := by
      intro ι Z _
      refine infra_73_diagramEq_of_eq (P.scheme.diagram_refl H
        (fun t => typeJoint (p := qB0) Z (Sum.map (Equiv.refl _) id t))) ?_ (fun t => rfl)
      rintro (k | z)
      · show xi.mapOcc (C.mark i0 ⊤ _ k) = xi.mapOcc (sj.mapOcc (C.mark i0 j h.lt k))
        exact (congrArg xi.mapOcc (C.mark_step i0 h.lt le_top k)).symm
      · show (⟨(Z z).1, xi.onVertex (Z z).1 (s0.onVertex (Z z).1 (Z z).2)⟩ :
            Occurrence K oneVertexShape (P.scheme.asSystem hμ H)) =
          ⟨(Z z).1, xi.onVertex (Z z).1 (sj.onVertex (Z z).1 (sij.onVertex (Z z).1 (Z z).2))⟩
        rw [hinc]
    exact infra_711_tiedFree_base_equiv _ qB0 (infra_75_markOver sij (C.step_arrow h.le)
      (x.restrict sj (C.step_arrow _)) (C.mark i0 j h.lt)) (Equiv.refl _) y ey hD hyT
  · obtain ⟨ρ, hρ, top, f1, f2, hf1, hf2, hc, hv⟩ := S
    refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, ?_, ?_⟩
    · intro v
      have hv' := hc v
      have he : (infra_75_jointOver sij (C.step_arrow h.le) (x.restrict sj (C.step_arrow _))
          (C.mark i0 j h.lt)).incl.onVertex v = jB.incl.onVertex v := by
        ext a
        show xi.onVertex v (sj.onVertex v (sij.onVertex v a)) = xi.onVertex v (s0.onVertex v a)
        rw [hinc]
      rw [he]
      exact hv'
    · rintro (k | w)
      · exact hv (Sum.inl k)
      · have hw := hv (Sum.inr ⟨0, ey.symm w⟩)
        have hJv : (infra_75_jointOver sij (C.step_arrow h.le) (x.restrict sj (C.step_arrow _))
            (C.mark i0 j h.lt)).val (Sum.inr (ey.symm w)) =
            jB.val (Sum.inr ⟨0, ey.symm w⟩) := by
          show xi.mapOcc (sj.mapOcc (C.mark i0 j h.lt (ey.symm w))) =
            xi.mapOcc (C.mark i0 ⊤ _ (ey.symm w))
          exact congrArg xi.mapOcc (C.mark_step i0 h.lt le_top _)
        have hYv : (Sum.inr (ey (ey.symm w)) : pB.idx ⊕ y.idx) = Sum.inr w := by
          rw [Equiv.apply_symm_apply]
        change (⟨_, f1.onVertex _ ((infra_75_jointOver sij (C.step_arrow h.le)
            (x.restrict sj (C.step_arrow _)) (C.mark i0 j h.lt)).val (Sum.inr (ey.symm w))).2⟩ :
              Occurrence K oneVertexShape (P.scheme.asSystem hρ top)) =
          ⟨_, f2.onVertex _ ((pB.join y).val (Sum.inr w)).2⟩
        rw [hJv, ← hYv]
        exact hw

/-- A tied product with a level-`μ` joint exists for a base-level first factor. -/
theorem infra_711_product_exists_level (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
    {A : P.scheme.Object μ hμ} (p q : TupleOver K oneVertexShape P.scheme hμ A)
    (hp : p.ν = μ) (hq : q.ν = μ) (hqσ : #q.idx ≤ ℵ₀) :
    ∃ (jt : TupleOver K oneVertexShape P.scheme hμ A) (e : p.idx ⊕ q.idx ≃ jt.idx),
      jt.ν = μ ∧ IsProductTied p q jt e := by
  rcases p with ⟨ν, hν, H, incl, hi, idx, val⟩
  simp only at hp
  subst hp
  obtain ⟨y, ey, hyν, _, hyT⟩ :=
    infra_610_tied_free_lift P ℵ₀ le_rfl hμ h0 h1 (B := H) incl hi q hq hqσ
  let p : TupleOver K oneVertexShape P.scheme hμ A := ⟨ν, hν, H, incl, hi, idx, val⟩
  refine ⟨p.join y, Equiv.sumCongr (Equiv.refl _) ey, hyν, p, Equiv.refl _,
    SameGaloisType.refl p, y, ey, hyT, ?_⟩
  have hh : (Equiv.sumCongr (Equiv.refl p.idx) ey).symm.trans
      (Equiv.sumCongr (Equiv.refl p.idx) ey) = Equiv.refl (p.idx ⊕ y.idx) :=
    Equiv.symm_trans_self _
  exact hh ▸ SameGaloisType.refl (p.join y)

/-- Normalize a Galois identification so that the first side carries the identity. -/
theorem infra_711_sameGalois_normalize {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {A : P.scheme.Object μ hμ}
    {t1 t2 : TupleOver K oneVertexShape P.scheme hμ A} {ι : Type u}
    {e1 : t1.idx ≃ ι} {e2 : t2.idx ≃ ι} (h : SameGaloisType t1 t2 e1 e2) :
    SameGaloisType t2 t1 (Equiv.refl _) (e1.trans e2.symm) := by
  have h' := infra_612_sameGalois_trans_equiv (SameGaloisType.symm h) e2.symm
  rw [Equiv.self_trans_symm] at h'
  exact h'

theorem infra_711_equiv_aux {X Y Z J : Type u} (e' : X ⊕ Y ≃ J) (φ : X ≃ Z) (s : X ⊕ Y) :
    ((e'.symm.trans (Equiv.sumComm X Y)).trans
      (Equiv.sumCongr (Equiv.refl Y) (φ.trans (Equiv.refl Z)))).symm
      ((Equiv.sumCongr φ (Equiv.refl Y)).trans (Equiv.sumComm Z Y) s) = e' s := by
  rcases s with s | s <;> simp

theorem infra_711_equiv_aux2 {X Y Z J S : Type u} (e1 : (X ⊕ Y) ⊕ Z ≃ J) (c : Y ⊕ Z ≃ S)
    (s : (X ⊕ Y) ⊕ Z) :
    ((e1.symm.trans ((Equiv.sumCongr (Equiv.refl (X ⊕ Y)).symm (Equiv.refl Z)).trans
        (Equiv.sumAssoc X Y Z))).trans
      ((Equiv.refl (X ⊕ S)).symm.trans (Equiv.sumCongr (Equiv.refl X) c.symm)).symm).symm
      (((Equiv.sumAssoc X Y Z).trans (Equiv.sumCongr (Equiv.refl X) c)) s) = e1 s := by
  rcases s with (s | s) | s <;> simp

/-- A product's joint may be replaced by any base-level tuple of the same Galois type. -/
theorem infra_711_product_joint_transfer (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
    {A : P.scheme.Object μ hμ} {p q jt jt' : TupleOver K oneVertexShape P.scheme hμ A}
    {e : p.idx ⊕ q.idx ≃ jt.idx} (h : IsProductTied p q jt e)
    (e' : p.idx ⊕ q.idx ≃ jt'.idx) (g : jt'.idx ≃ jt.idx)
    (hS : SameGaloisType jt' jt g (Equiv.refl jt.idx)) (hg : ∀ s, g (e' s) = e s)
    (hj : jt.ν = μ) (hj' : jt'.ν = μ) (hidx : #jt'.idx ≤ ℵ₀) :
    IsProductTied p q jt' e' := by
  obtain ⟨x, ex, hSx, y, ey, hT, hJ⟩ := h
  refine ⟨x, ex, hSx, y, ey, hT, ?_⟩
  have hJ' := infra_612_sameGalois_trans_equiv hJ (e.symm.trans (Equiv.sumCongr ex ey)).symm
  rw [Equiv.self_trans_symm] at hJ'
  have R := infra_612_galois_trans_cross_level_of_base_end P ℵ₀ le_rfl hμ h0 h1 A jt' jt
    (x.join y) g _ hidx hj (Or.inl hj') hS hJ'
  have hE : g.trans ((Equiv.refl (x.idx ⊕ y.idx)).trans
      (e.symm.trans (Equiv.sumCongr ex ey)).symm).symm =
      e'.symm.trans (Equiv.sumCongr ex ey) := by
    ext t
    obtain ⟨s, rfl⟩ := e'.surjective t
    simp [hg]
  rw [← hE]
  exact R

/-- Reindexing `b_{i₀}` followed by a selection as the selection `Fin.cons i₀ ix`. -/
def infra_711_consEquiv {δ : Type*} (I : δ → Type u) (i0 : δ) {n : ℕ} (ix : Fin n → δ) :
    (Σ _s : Fin 1, I i0) ⊕ (Σ s : Fin n, I (ix s)) ≃
      Σ s : Fin (n + 1), I ((Fin.cons i0 ix : Fin (n + 1) → δ) s) where
  toFun
    | Sum.inl p => ⟨0, p.2⟩
    | Sum.inr p => ⟨p.1.succ, p.2⟩
  invFun p := Fin.cases (motive := fun s => I ((Fin.cons i0 ix : Fin (n + 1) → δ) s) →
      (Σ _s : Fin 1, I i0) ⊕ (Σ s : Fin n, I (ix s)))
    (fun a => Sum.inl ⟨0, a⟩) (fun s a => Sum.inr ⟨s, a⟩) p.1 p.2
  left_inv := by
    rintro (⟨a, x⟩ | ⟨s, x⟩)
    · obtain rfl : a = 0 := Subsingleton.elim a 0
      rfl
    · rfl
  right_inv := by
    rintro ⟨s, x⟩
    induction s using Fin.cases with
    | zero => rfl
    | succ s => rfl

theorem infra_711_succ_pair (P : SingleModelData K) : infra_711_succ_pair_statement P := by
  intro μ hμ h0 h1 _ _ A L _ _ C _ i0 j h x hfin hxν hprod n ix hinj hlt
  classical
  have hσμ : ℵ₀ < μ := (Order.lt_succ ℵ₀).trans_le h1
  have hfinI : ∀ i, Finite (L.indexAt i) := L.finite_each
  rcases x with ⟨ν, hν, H, xi, hxi, idx, val⟩
  simp only at hxν
  subst hxν
  have hfinx : Finite idx := hfin
  set x : TupleOver K oneVertexShape P.scheme hμ (C.stage ⊤) := ⟨ν, hν, H, xi, hxi, idx, val⟩
    with hxdef
  let ix1 : Fin 1 → L.δ := fun _ => i0
  let ixc : Fin (n + 1) → L.δ := Fin.cons i0 ix
  have hlt0 : ∀ s, ix s < i0 := fun s => WithTop.coe_lt_coe.mp (hlt s)
  have hinjc : Function.Injective ixc :=
    Fin.cons_injective_iff.mpr ⟨fun ⟨s, hs⟩ => (hlt0 s).ne hs, hinj⟩
  have hltj : ∀ s, ((ixc s : L.δ) : WithTop L.δ) < j := by
    intro s
    induction s using Fin.cases with
    | zero => exact h.lt
    | succ s => exact (hlt s).trans h.lt
  have hPQ := hprod 1 ix1 (fun a b _ => Subsingleton.elim a b) (fun _ => h.lt)
  have h₂ := hprod (n + 1) ixc hinjc hltj
  let s0 := C.step (le_top : (i0 : WithTop L.δ) ≤ ⊤)
  have hcnt : ∀ {m : ℕ} (ix' : Fin m → L.δ), #(Σ s : Fin m, L.indexAt (ix' s)) ≤ ℵ₀ :=
    fun _ => Cardinal.mk_le_aleph0
  have hxc : #idx ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hperm := P.scheme.structural_iso H H (SystemArrow.refl _) (P.scheme.isStructIso_refl H)
  have hcomm0 : ∀ v a, xi.onVertex v ((C.into ⊤).onVertex v a) =
      xi.onVertex v (s0.onVertex v ((C.into i0).onVertex v a)) := by
    intro v a
    rw [← C.into_step (le_top : (i0 : WithTop L.δ) ≤ ⊤) v]
    rfl
  -- `tp(b_{i₀}/M_{i₀})` free from `A`, pushed into `x`'s host
  let bT := asTuple s0 (C.step_arrow _) (C.mark i0 ⊤ (WithTop.coe_lt_top i0))
  have hfree : IsTiedFree (C.into (i0 : WithTop L.δ)) (bT.restrict (C.into i0) (C.into_arrow _))
      bT (Equiv.refl _) := C.free i0
  have hIμ : #(L.indexAt i0) < ν := Cardinal.mk_le_aleph0.trans_lt hσμ
  have hpush := infra_75_tiedFree_target_push (C.into (i0 : WithTop L.δ))
    (bT.restrict (C.into i0) (C.into_arrow _)) hIμ bT (Equiv.refl _) rfl xi hxi hfree
  let qB0 : TupleOver K oneVertexShape P.scheme hμ (C.stage (i0 : WithTop L.δ)) :=
    ⟨ν, hμ, H, SystemArrow.comp s0 xi, P.scheme.comp s0 xi (C.step_arrow _) hxi,
      L.indexAt i0, fun k => xi.mapOcc (C.mark i0 ⊤ (WithTop.coe_lt_top i0) k)⟩
  have hpush' : IsTiedFreeMixed (C.into (i0 : WithTop L.δ))
      (bT.restrict (C.into i0) (C.into_arrow _)) qB0 (Equiv.refl _) := hpush
  let B0 := C.selectionOver x 1 ix1
  let Bb := C.selectionOver x n ix
  let S2 := C.selectionOver x (n + 1) ixc
  let φ : B0.idx ≃ L.indexAt i0 :=
    { toFun := fun p => p.2
      invFun := fun k => ⟨0, k⟩
      left_inv := by
        rintro ⟨a, k⟩
        obtain rfl : a = 0 := Subsingleton.elim a 0
        rfl
      right_inv := fun _ => rfl }
  have hQ : IsTiedFreeMixed (C.into (i0 : WithTop L.δ)) B0 qB0 (φ.trans (Equiv.refl _)) := by
    refine infra_711_tiedFree_base_equiv _ (bT.restrict (C.into i0) (C.into_arrow _)) B0 φ qB0
      (Equiv.refl _) ?_ hpush'
    intro ι Z hι
    have hα : #(B0.idx ⊕ ι) < ν := by
      rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
      exact Cardinal.add_lt_of_lt (P.aleph0_le hμ) ((hcnt ix1).trans_lt hσμ) hι
    have d := P.scheme.diagram_preserved (C.stage ⊤) H xi hxi
      (fun t => typeJoint (p := bT.restrict (C.into i0) (C.into_arrow _)) Z (Sum.map φ id t))
      hα hα
    refine P.scheme.diagram_symm _ _ _ _ (infra_73_diagramEq_of_eq d (fun t => rfl) ?_)
    rintro (k | z)
    · rfl
    · show (⟨(Z z).1, xi.onVertex (Z z).1 (s0.onVertex (Z z).1
          ((C.into i0).onVertex (Z z).1 (Z z).2))⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem hμ H)) =
        ⟨(Z z).1, xi.onVertex (Z z).1 ((C.into ⊤).onVertex (Z z).1 (Z z).2)⟩
      rw [hcomm0]
  -- `b̄` realized in `M_{i₀}`: `b̄ ⊗ b_{i₀}`
  let xb : TupleOver K oneVertexShape P.scheme hμ A :=
    ⟨ν, hμ, C.stage (i0 : WithTop L.δ), C.into i0, C.into_arrow _, Bb.idx,
      fun p => C.mark (ix p.1) i0 (hlt p.1) p.2⟩
  have hSxb : SameGaloisType Bb xb (Equiv.refl _) (Equiv.refl _) := by
    refine ⟨ν, hμ, H, SystemArrow.refl _, SystemArrow.comp s0 xi, hperm,
      P.scheme.comp s0 xi (C.step_arrow _) hxi, ?_, ?_⟩
    · intro v; ext a; exact hcomm0 v a
    · intro p
      show xi.mapOcc (C.mark (ix p.1) ⊤ _ p.2) =
        xi.mapOcc (s0.mapOcc (C.mark (ix p.1) i0 (hlt p.1) p.2))
      exact congrArg xi.mapOcc (C.mark_step (ix p.1) (hlt p.1) le_top p.2).symm
  let e₁ : Bb.idx ⊕ B0.idx ≃ (xb.join qB0).idx :=
    Equiv.sumCongr (Equiv.refl _) (φ.trans (Equiv.refl _))
  have hprodBB0 : IsProductTied Bb B0 (xb.join qB0) e₁ := by
    refine ⟨xb, Equiv.refl _, hSxb, qB0, φ.trans (Equiv.refl _), hQ, ?_⟩
    have hh : e₁.symm.trans e₁ = Equiv.refl _ := Equiv.symm_trans_self _
    exact hh ▸ SameGaloisType.refl (xb.join qB0)
  obtain ⟨J', e', hJ'ν, hJ'⟩ := infra_711_product_exists_level P hμ h0 h1 B0 Bb rfl rfl (hcnt ix)
  have Sy := infra_612_tied_symm_level_joints P ℵ₀ le_rfl hμ h0 h1 Bb B0 rfl rfl (hcnt ix)
    (hcnt ix1) (xb.join qB0) J' e₁ e' hprodBB0 hJ' rfl hJ'ν
  have Sy' := infra_612_sameGalois_trans_equiv Sy e₁
  rw [Equiv.symm_trans_self] at Sy'
  -- the selection `S2` is `xb.join qB0` reindexed
  let consE : B0.idx ⊕ Bb.idx ≃ S2.idx := infra_711_consEquiv L.indexAt i0 ix
  let κ : S2.idx ≃ (xb.join qB0).idx :=
    consE.symm.trans ((Equiv.sumCongr φ (Equiv.refl _)).trans (Equiv.sumComm _ _))
  have D1 : SameGaloisType S2 (xb.join qB0) κ (Equiv.refl _) := by
    refine ⟨ν, hμ, H, SystemArrow.refl _, SystemArrow.refl _, hperm, hperm, ?_, ?_⟩
    · intro v; ext a; exact hcomm0 v a
    · rintro (p | a)
      · show xi.mapOcc (C.mark (ix p.1) ⊤ _ p.2) =
          xi.mapOcc (s0.mapOcc (C.mark (ix p.1) i0 (hlt p.1) p.2))
        exact congrArg xi.mapOcc (C.mark_step (ix p.1) (hlt p.1) le_top p.2).symm
      · rfl
  have T := infra_612_galois_trans_cross_level_of_base_end P ℵ₀ le_rfl hμ h0 h1 A S2
    (xb.join qB0) J' κ _ (hcnt ixc) rfl (Or.inl rfl) D1 Sy'
  have hQR : IsProductTied B0 Bb S2 consE :=
    infra_711_product_joint_transfer P hμ h0 h1 hJ' consE _ T
      (by
        intro s
        have hc : consE.symm (consE s) = s := Equiv.symm_apply_apply _ _
        refine Eq.trans ?_ (infra_711_equiv_aux e' φ s)
        exact congrArg (fun t => ((e'.symm.trans (Equiv.sumComm _ _)).trans e₁).symm
          (((Equiv.sumCongr φ (Equiv.refl _)).trans (Equiv.sumComm _ _)) t)) hc) hJ'ν rfl (hcnt ixc)
  -- `(x, b_{i₀}) ⊗ b̄` by associativity
  let PQ := C.jointWith x 1 ix1
  let J2 := C.jointWith x (n + 1) ixc
  obtain ⟨J1, e1, hJ1ν, hJ1⟩ := infra_711_product_exists_level P hμ h0 h1 PQ Bb rfl rfl (hcnt ix)
  have As := infra_612_tied_assoc_level_joints P ℵ₀ le_rfl hμ h0 h1
    (x.restrict (C.into ⊤) (C.into_arrow ⊤)) B0 Bb rfl rfl rfl hxc (hcnt ix1) (hcnt ix)
    PQ S2 J1 J2 (Equiv.refl _) consE e1 (Equiv.refl _) hPQ hJ1 hQR h₂ rfl rfl hJ1ν rfl
  have As' := infra_711_sameGalois_normalize As
  let Jg := C.jointWith (infra_711_pairUp C x i0) n ix
  let m : Jg.idx ≃ J2.idx :=
    (Equiv.sumAssoc _ _ _).trans (Equiv.sumCongr (Equiv.refl _) consE)
  have D2 : SameGaloisType Jg J2 m (Equiv.refl _) := by
    refine ⟨ν, hμ, H, SystemArrow.refl _, SystemArrow.refl _, hperm, hperm, fun v => rfl, ?_⟩
    rintro (k | ⟨s, a⟩)
    · rfl
    · induction s using Fin.cases with
      | zero => rfl
      | succ s => rfl
  have hJgc : #Jg.idx ≤ ℵ₀ :=
    (Cardinal.mk_le_aleph0 : #((idx ⊕ (Σ _s : Fin 1, L.indexAt i0)) ⊕
      (Σ s : Fin n, L.indexAt (ix s))) ≤ ℵ₀)
  have T2 := infra_612_galois_trans_cross_level_of_base_end P ℵ₀ le_rfl hμ h0 h1 A Jg J2 J1 m _
    hJgc
    rfl (Or.inl rfl) D2 As'
  have F : IsProductTied PQ Bb Jg (Equiv.refl _) :=
    infra_711_product_joint_transfer (p := PQ) (q := Bb) (jt := J1) (jt' := Jg) P hμ h0 h1 hJ1
      (Equiv.refl (PQ.idx ⊕ Bb.idx)) _ T2
      (fun s => infra_711_equiv_aux2 e1 consE s) hJ1ν rfl hJgc
  exact F

/-- **The product over `Mᵢ` (proved, cycle 83).** -/
theorem infra_711_succ_product (P : SingleModelData K) : infra_711_succ_product_statement P :=
  infra_711_succ_product_of_parts P (infra_711_succ_pair P) (infra_711_succ_base_change P)

/-- **Lemma 7.11 successor step (proved, cycle 83).** -/
theorem infra_711_successor (P : SingleModelData K) : infra_711_successor_statement P :=
  infra_711_successor_of_product P (infra_711_succ_product P)

end
end AEC
