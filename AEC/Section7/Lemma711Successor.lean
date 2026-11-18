module

public import AEC.Section7.Lemma711Induction

/-!
# Lemma 7.11, successor step (tied)

At a successor stage `j` (`i ⋖ j`) the paper argues: by induction `tp(x/Mᵢ)` is free from `A`;
`x` and `bᵢ` have product over `Mᵢ` (induction applied to `(x, bᵢ)` and free base change of the
products over `A`); `M_{i+1}` is all-dominated over `Mᵢ + bᵢ`, so Proposition 7.5(3) makes
`tp(x/M_{i+1})` free from `Mᵢ`; transitivity gives freeness from `A`.

`infra_711_successor_of_product` proves the step from the product over `Mᵢ`
(`infra_711_succ_product_statement`, open tip `infra_711_succ_product`), using the proved level
form of 7.5(3) (`infra_75_product_free_level`) and tied transitivity (`infra_78_tiedFree_trans`).
-/

@[expose] public section

namespace AEC
noncomputable section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- **Lemma 7.11 successor: the product over `Mᵢ` (statement; open tip
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

/-- **7.11 successor, finite product rules (statement; open tip `infra_711_succ_pair`).**
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

end
end AEC
