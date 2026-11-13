module

public import AEC.Section6.StationaryFreeExtension

@[expose] public section

/-!
# Lemma 6.11 (average criterion for descent)

Same-level packaging for `SingleModelData`, in the style of Theorem 6.10.
Mixed levels `ν < μ` stay deferred with E8–E11.

English proof. Let `p = q ↾ A` and let `J` be a fresh Lemma 6.9 code for `p` at the
query size of the given sequence `I`. On a short query `Z ⊆ B`, the hypothesis says `I`
has majority value `q ↾ Z`. `infra_610_majority_eq_type` says the same index computes
`p` on that query in `A`, so `infra_610_majority_unique` identifies the two answers.
The fresh code computes `p` there as well, and the identification transports the majority
onto `q ↾ Z`. Saturation (`infra_610_move_query`) moves parameter queries from `B` into
`A`; diagram preservation matches them with the parameters of the restriction. Theorem 6.6
(`infra_610_same_galois`) is the testing criterion. `IsFreeFrom` is `IsFreeLift` of this
restriction along the fresh code, not a reflexive reading of `p = q.restrict` alone.
-/

namespace AEC
section

universe u

open Cardinal FirstOrder

variable {K : AbstractElementaryClass.{u}}

/-! ## Fresh Lemma 6.9 code -/

/-- A Lemma 6.9 code for `p` at query size `χ`, long enough that `χ + ℵ₀` does not exhaust
the index. Built at `max χ ℵ₀` and read back at `χ`, so a finite English query size is still
a code. -/
theorem infra_611_fresh_code
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A : P.scheme.Object μ hμ}
    (p : TupleOver K oneVertexShape P.scheme hμ A)
    (hνμ : p.ν = μ) (hidx : #p.idx ≤ σ)
    (χ : Cardinal.{u}) (hχμ : χ < μ) :
    ∃ code : ApproximationSequence p,
      code.τ = χ ∧ χ + aleph0 < #code.κIndex ∧ #code.κIndex < μ := by
  let τ0 : Cardinal.{u} := max χ aleph0
  let κ : Cardinal.{u} := Order.succ τ0
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hτ0 : aleph0 ≤ τ0 := le_max_right _ _
  have hτ0μ : τ0 < μ := max_lt hχμ (P.aleph0_lt hμ)
  have hκ : aleph0 ≤ κ := hτ0.trans (Order.le_succ _)
  have hκμ : κ < μ :=
    (Order.succ_le_of_lt (cantor τ0)).trans_lt
      (hμ.1.working.strongLimit.isStrongPrelimit hτ0μ)
  have hprod : κ * #p.idx < μ := by
    have hmul : κ * #p.idx ≤ κ * σ := mul_le_mul' le_rfl hidx
    rcases le_total σ κ with hσκ | hκσ
    · have heq : κ * σ = κ :=
        mul_eq_left hκ hσκ (aleph0_pos.trans_le hσ).ne'
      rw [heq] at hmul
      exact hmul.trans_lt hκμ
    · have heq : κ * σ = σ := by
        rw [mul_comm]
        exact mul_eq_left hσ hκσ (aleph0_pos.trans_le hκ).ne'
      rw [heq] at hmul
      exact hmul.trans_lt hσlt
  have hβ : max (max σ τ0) (max (ls K) aleph0) < μ :=
    max_lt (max_lt hσlt hτ0μ) (max_lt (P.ls_lt hμ) (P.aleph0_lt hμ))
  have hclosed : infra_69_pad_recursion_closed σ (max (ls K) aleph0)
      (max (max σ τ0) (max (ls K) aleph0)) μ :=
    hrec.2 _ hβ
  obtain ⟨code0, hτeq, hκeq⟩ :=
    P.exists_approximationSequence hμ A p hνμ σ τ0 κ hσ hσlt hidx hτ0 hτ0μ hκ hκμ hprod
      hclosed
  have hχτ : χ ≤ code0.τ := by
    rw [hτeq]
    exact le_max_left _ _
  let code : ApproximationSequence p :=
    { τ := χ
      κIndex := code0.κIndex
      family := code0.family
      concat_bounded := code0.concat_bounded
      few_exceptions := fun {ι} Z hι => code0.few_exceptions Z (hι.trans hχτ) }
  refine ⟨code, rfl, ?_, ?_⟩
  · have hκcard : #code.κIndex = Order.succ τ0 := hκeq
    rw [hκcard]
    have hsum : τ0 + aleph0 = τ0 := add_eq_left hτ0 hτ0
    have hlt : τ0 + aleph0 < Order.succ τ0 := hsum.symm ▸ Order.lt_succ τ0
    exact (add_le_add (le_max_left χ aleph0) le_rfl).trans_lt hlt
  · have hκcard : #code.κIndex = κ := hκeq
    exact hκcard ▸ hκμ

/-! ## Majority bridge -/

/-- The given sequence computes both `q ↾ Z` and `p ↾ Z₀`. The length gap makes the two
majority values the same diagram. -/
theorem infra_611_bridge
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (seq : ApproximationSequence (q.restrict f hf))
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hmaj : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z))
    {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hι : #ι ≤ seq.τ) :
    ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
      P.scheme.DiagramEq (X := (q.restrict f hf).host) (Y := q.host)
        (typeJoint (p := q.restrict f hf) Z0) (typeJoint (p := q) Z) := by
  obtain ⟨Z0, hQ⟩ := hmaj Z hι
  have hP : IsMajorityValue seq Z0 (q.restrict f hf).hν (q.restrict f hf).host
      (typeJoint (p := q.restrict f hf) Z0) :=
    infra_610_majority_eq_type seq Z0 hι
  have hbound : #ι + aleph0 < #seq.κIndex := (add_le_add hι le_rfl).trans_lt hκ
  exact ⟨Z0, infra_610_majority_unique seq Z0
    (xs := typeJoint (p := q.restrict f hf) Z0) (ys := typeJoint (p := q) Z)
    hP hQ hbound⟩

/-- A majority value stays a majority after `DiagramEq`. -/
theorem infra_611_majority_transport
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ}
    {p : TupleOver K oneVertexShape P.scheme hμ A}
    (code : ApproximationSequence p)
    {ι : Type u}
    (Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A))
    {ν₁ ν₂ : Cardinal.{u}} {hν₁ : ν₁ ∈ P.eligible} {hν₂ : ν₂ ∈ P.eligible}
    {repr₁ : P.scheme.Object ν₁ hν₁} {repr₂ : P.scheme.Object ν₂ hν₂}
    (xs : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν₁ repr₁))
    (ys : p.idx ⊕ ι → Occurrence K oneVertexShape (P.scheme.asSystem hν₂ repr₂))
    (hxs : IsMajorityValue code Z0 hν₁ repr₁ xs)
    (hEq : P.scheme.DiagramEq (X := repr₁) (Y := repr₂) xs ys) :
    IsMajorityValue code Z0 hν₂ repr₂ ys := by
  change # {i : code.κIndex //
      ¬ P.scheme.DiagramEq (X := A) (Y := repr₂) (seqJoint (code.family i) Z0) ys} ≤ _
  have hmono : ∀ i,
      ¬ P.scheme.DiagramEq (X := A) (Y := repr₂) (seqJoint (code.family i) Z0) ys →
      ¬ P.scheme.DiagramEq (X := A) (Y := repr₁) (seqJoint (code.family i) Z0) xs := by
    intro i hbad hgood
    exact hbad (P.scheme.diagram_trans A repr₁ repr₂ _ _ _ hgood hEq)
  exact (mk_subtype_mono hmono).trans hxs

/-- The fresh code has majority value `q ↾ Z`, by transporting `p ↾ Z₀` along the bridge. -/
theorem infra_611_code_majority
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (seq : ApproximationSequence (q.restrict f hf))
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hmaj : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z))
    (code : ApproximationSequence (q.restrict f hf))
    (hτ : seq.τ ≤ code.τ)
    {ι : Type u}
    (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B))
    (hι : #ι ≤ seq.τ) :
    ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
      IsMajorityValue code Z0 q.hν q.host (typeJoint (p := q) Z) := by
  obtain ⟨Z0, hEq⟩ := infra_611_bridge f hf q seq hκ hmaj Z hι
  have hιcode : #ι ≤ code.τ := hι.trans hτ
  have hP : IsMajorityValue code Z0 (q.restrict f hf).hν (q.restrict f hf).host
      (typeJoint (p := q.restrict f hf) Z0) :=
    infra_610_majority_eq_type code Z0 hιcode
  exact ⟨Z0, infra_611_majority_transport code Z0
    (typeJoint (p := q.restrict f hf) Z0) (typeJoint (p := q) Z) hP hEq⟩

/-! ## Moved parameter queries -/

/-- For parameters from `A`, saturation of `Z = f(Zpar)` and the bridge identify the
restriction joint with `q`'s joint. The length gap supplies an index good for both queries. -/
theorem infra_611_image_agree
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (seq : ApproximationSequence (q.restrict f hf))
    (hidxμ : #(q.restrict f hf).idx < μ)
    (hτμ : seq.τ < μ)
    (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hmaj : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z))
    {β : Type u} (params : β → A.model.carrier) (hβ : #β ≤ seq.τ) :
    P.scheme.DiagramEq (X := (q.restrict f hf).host) (Y := q.host)
      (typeJoint (p := q.restrict f hf) (fun b => A.occ (params b)))
      (typeJoint (p := q) (fun b =>
        ⟨(A.occ (params b)).1,
          f.onVertex (A.occ (params b)).1 (A.occ (params b)).2⟩)) := by
  classical
  let p := q.restrict f hf
  let Zpar : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun b => A.occ (params b)
  let Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun b => ⟨(Zpar b).1, f.onVertex (Zpar b).1 (Zpar b).2⟩
  have hιμ : #β < μ := hβ.trans_lt hτμ
  obtain ⟨Z0m, hmove⟩ := infra_610_move_query f hf seq Z hβ hιμ
  obtain ⟨Z0h, hBridge⟩ := infra_611_bridge f hf q seq hκ hmaj Z hβ
  have hcard : #(p.idx ⊕ β) < μ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_lt_of_lt (P.aleph0_le hμ) hidxμ hιμ
  have hpres : ∀ i : seq.κIndex,
      P.scheme.DiagramEq (X := A) (Y := B)
        (seqJoint (seq.family i) Zpar)
        (seqJoint
          (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
          Z) := by
    intro i
    have hraw :=
      P.scheme.diagram_preserved A B f hf (seqJoint (seq.family i) Zpar) hcard hcard
    have hrewrite :
        (fun t => ⟨(seqJoint (seq.family i) Zpar t).1,
            f.onVertex (seqJoint (seq.family i) Zpar t).1
              (seqJoint (seq.family i) Zpar t).2⟩) =
          seqJoint
            (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
            Z := by
      funext t
      cases t <;> rfl
    exact hrewrite ▸ hraw
  have hbound : #β + aleph0 < #seq.κIndex := (add_le_add hβ le_rfl).trans_lt hκ
  let ExcM : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Z0m) (typeJoint (p := p) Z0m)}
  let ExcPar : Set seq.κIndex :=
    {i | ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Zpar) (typeJoint (p := p) Zpar)}
  have hExcM : #ExcM ≤ #β + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Z0m) (typeJoint (p := p) Z0m)} ≤ _
    exact infra_610_majority_eq_type seq Z0m hβ
  have hExcPar : #ExcPar ≤ #β + aleph0 := by
    change # {i : seq.κIndex //
        ¬ P.scheme.DiagramEq (X := A) (Y := p.host)
          (seqJoint (seq.family i) Zpar) (typeJoint (p := p) Zpar)} ≤ _
    exact infra_610_majority_eq_type seq Zpar hβ
  have hex : ∃ i : seq.κIndex, i ∉ ExcM ∧ i ∉ ExcPar := by
    by_contra h
    have hall : (Set.univ : Set seq.κIndex) ⊆ ExcM ∪ ExcPar := by
      intro i _
      by_cases hi : i ∈ ExcM ∪ ExcPar
      · exact hi
      · exact False.elim (h ⟨i, by
          simp only [Set.mem_union, not_or] at hi
          exact hi⟩)
    have hinfκ : aleph0 ≤ #seq.κIndex :=
      (le_add_self (a := aleph0) (b := #β)).trans (le_of_lt hbound)
    have hle : #seq.κIndex ≤ (#β + aleph0) + (#β + aleph0) := by
      have huni : #(Set.univ : Set seq.κIndex) = #seq.κIndex := mk_univ
      rw [← huni]
      exact (mk_le_mk_of_subset hall).trans
        ((mk_union_le _ _).trans (add_le_add hExcM hExcPar))
    exact (not_le_of_gt (add_lt_of_lt hinfκ hbound hbound)) hle
  obtain ⟨i, hiM, hiPar⟩ := hex
  have hgoodM : P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Z0m) (typeJoint (p := p) Z0m) := by
    simpa [ExcM] using hiM
  have hgoodPar : P.scheme.DiagramEq (X := A) (Y := p.host)
      (seqJoint (seq.family i) Zpar) (typeJoint (p := p) Zpar) := by
    simpa [ExcPar] using hiPar
  have hJoint : P.scheme.DiagramEq (X := A) (Y := A)
      (seqJoint (seq.family i) Z0m) (seqJoint (seq.family i) Zpar) :=
    P.scheme.diagram_trans A B A
      (seqJoint (seq.family i) Z0m)
      (seqJoint
        (fun j => ⟨(seq.family i j).1, f.onVertex (seq.family i j).1 (seq.family i j).2⟩)
        Z)
      (seqJoint (seq.family i) Zpar)
      (hmove i) (P.scheme.diagram_symm A B _ _ (hpres i))
  have hTypes : P.scheme.DiagramEq (X := p.host) (Y := p.host)
      (typeJoint (p := p) Z0m) (typeJoint (p := p) Zpar) :=
    P.scheme.diagram_trans p.host A p.host
      (typeJoint (p := p) Z0m) (seqJoint (seq.family i) Z0m) (typeJoint (p := p) Zpar)
      (P.scheme.diagram_symm A p.host _ _ hgoodM)
      (P.scheme.diagram_trans A A p.host
        (seqJoint (seq.family i) Z0m) (seqJoint (seq.family i) Zpar)
        (typeJoint (p := p) Zpar) hJoint hgoodPar)
  have hEqFun : typeJoint (p := p) Zpar = typeJoint (p := q) Z := by
    funext t
    cases t with
    | inl j => rfl
    | inr b => rfl
  have hParQ : P.scheme.DiagramEq (X := p.host) (Y := q.host)
      (typeJoint (p := p) Zpar) (typeJoint (p := q) Z) := by
    rw [hEqFun]
    exact P.scheme.diagram_refl q.host _
  have hViaMove : P.scheme.DiagramEq (X := p.host) (Y := q.host)
      (typeJoint (p := p) Zpar) (typeJoint (p := q) Z) :=
    P.scheme.diagram_trans p.host p.host q.host
      (typeJoint (p := p) Zpar) (typeJoint (p := p) Z0m) (typeJoint (p := q) Z)
      (P.scheme.diagram_symm p.host p.host _ _ hTypes)
      (P.scheme.diagram_trans p.host p.host q.host
        (typeJoint (p := p) Z0m) (typeJoint (p := p) Zpar) (typeJoint (p := q) Z)
        hTypes hParQ)
  have hRound : P.scheme.DiagramEq (X := q.host) (Y := q.host)
      (typeJoint (p := q) Z) (typeJoint (p := q) Z) :=
    P.scheme.diagram_trans q.host p.host q.host
      (typeJoint (p := q) Z) (typeJoint (p := p) Z0h) (typeJoint (p := q) Z)
      (P.scheme.diagram_symm p.host q.host _ _ hBridge) hBridge
  exact P.scheme.diagram_trans p.host q.host q.host
    (typeJoint (p := p) Zpar) (typeJoint (p := q) Z) (typeJoint (p := q) Z)
    hViaMove hRound

/-- Turn the joint diagram into the Theorem 6.6 test at the requested bound. -/
theorem infra_611_of_diagram
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (hνμ : q.ν = μ)
    {β : Type u} (params : β → A.model.carrier)
    (ρ : Cardinal.{u}) (hρinf : aleph0 ≤ ρ) (hρμ : ρ < μ)
    (hjoint : #(q.idx ⊕ β) ≤ ρ)
    (h₀ : P.D.t ρ ≤ Model.card (q.restrict f hf).host.model)
    (h₁ : P.D.t ρ ≤ Model.card q.host.model)
    (hDE : P.scheme.DiagramEq (X := (q.restrict f hf).host) (Y := q.host)
      (typeJoint (p := q.restrict f hf) (fun b => A.occ (params b)))
      (typeJoint (p := q) (fun b =>
        ⟨(A.occ (params b)).1,
          f.onVertex (A.occ (params b)).1 (A.occ (params b)).2⟩))) :
    P.D.same hjoint (q.restrict f hf).host.mem q.host.mem h₀ h₁
      (Sum.elim (fun i => (q.restrict f hf).host.val
          ((q.restrict f hf).val ((Equiv.refl (q.restrict f hf).idx).symm i)))
        (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b)))
      (Sum.elim (fun i => q.host.val (q.val i))
        (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b))) := by
  let p := q.restrict f hf
  let Zpar : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun b => A.occ (params b)
  let Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun b => ⟨(Zpar b).1, f.onVertex (Zpar b).1 (Zpar b).2⟩
  have hαμ : #(q.idx ⊕ β) < μ := hjoint.trans_lt hρμ
  have hαq : #(q.idx ⊕ β) < q.ν := by simpa [← hνμ] using hαμ
  have hSame : P.D.SameD q.host.model q.host.model
      (fun t => q.host.val (typeJoint (p := p) Zpar t))
      (fun t => q.host.val (typeJoint (p := q) Z t)) :=
    (SingleModelData.diagramEq_iff_sameD (P := P) (α := q.idx ⊕ β) q.hν q.hν q.host q.host
      (fun t => q.host.val (typeJoint (p := p) Zpar t))
      (fun t => q.host.val (typeJoint (p := q) Z t))
      hαq hαq).mp hDE
  obtain ⟨_, _, hMc, hNc, hs⟩ := hSame
  let ρ0 : Cardinal.{u} := max #(q.idx ⊕ β) aleph0
  let ρ' : Cardinal.{u} := max ρ (ls K)
  have hρ0inf : aleph0 ≤ ρ0 := le_max_right _ _
  have hρ0le : ρ0 ≤ ρ' :=
    max_le (hjoint.trans (le_max_left _ _)) (hρinf.trans (le_max_left _ _))
  have hls : ls K ≤ ρ' := le_max_right _ _
  have hρle' : ρ ≤ ρ' := le_max_left _ _
  have hρ'μ : ρ' < μ := max_lt hρμ (P.ls_lt hμ)
  have hρ'inf : aleph0 ≤ ρ' := hρinf.trans hρle'
  have hMc' : P.D.t ρ' ≤ Model.card q.host.model :=
    (P.t_lt hμ hρ'inf hρ'μ).le.trans (by simpa [hνμ] using q.host.card.ge)
  have hNc' : P.D.t ρ' ≤ Model.card q.host.model := hMc'
  let valP : (q.idx ⊕ β) → q.host.model.carrier :=
    fun t => q.host.val (typeJoint (p := q.restrict f hf) Zpar t)
  let valQ : (q.idx ⊕ β) → q.host.model.carrier :=
    fun t => q.host.val (typeJoint (p := q) Z t)
  let sumL : (q.idx ⊕ β) → q.host.model.carrier :=
    Sum.elim (fun i => (q.restrict f hf).host.val
        ((q.restrict f hf).val ((Equiv.refl (q.restrict f hf).idx).symm i)))
      (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b))
  let sumR : (q.idx ⊕ β) → q.host.model.carrier :=
    Sum.elim (fun i => q.host.val (q.val i))
      (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b))
  have hsρ : P.D.same hjoint q.host.mem q.host.mem h₀ h₁ valP valQ :=
    P.D.same_relevel (σ := ρ0) (τ := ρ) (σ' := ρ')
      (le_max_left _ _) hρ0inf hρinf hρ0le hρle' hls
      q.host.mem q.host.mem hMc hNc hMc' hNc' h₀ h₁
      _ _ hs hjoint id
  have hL : sumL = valP := by
    funext t
    cases t with
    | inl i => rfl
    | inr b =>
      dsimp [sumL, valP, typeJoint, Zpar, SMObject.occ, oneVertexOcc]
      rfl
  have hR : sumR = valQ := by
    funext t
    cases t with
    | inl i => rfl
    | inr b =>
      dsimp [sumR, valQ, typeJoint, Z, Zpar, TupleOver.restrict, SystemArrow.comp,
        SMObject.occ, oneVertexOcc]
      rfl
  have hsLR : P.D.same hjoint q.host.mem q.host.mem h₀ h₁ sumL sumR :=
    hL.symm ▸ hR.symm ▸ hsρ
  exact hsLR

/-- Theorem 6.6 tests of `p` against `q.restrict`. Queries no larger than `seq.τ` go through
the moved bridge; larger parameter lists are the same restriction tuple read twice. -/
theorem infra_611_tests
    {P : SingleModelData K}
    {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (seq : ApproximationSequence (q.restrict f hf))
    (hνμ : q.ν = μ) (hidxμ : #(q.restrict f hf).idx < μ)
    (hτμ : seq.τ < μ) (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hmaj : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z))
    (σ : Cardinal.{u}) :
    ∀ {β : Type u} (_ : #β ≤ P.g σ + ls K) (ρ : Cardinal.{u}) (_ : aleph0 ≤ ρ)
      (_ : ρ < μ) (params : β → A.model.carrier)
      (hjoint : #(q.idx ⊕ β) ≤ ρ)
      (h₀ : P.D.t ρ ≤ Model.card (q.restrict f hf).host.model)
      (h₁ : P.D.t ρ ≤ Model.card q.host.model),
      P.D.same hjoint (q.restrict f hf).host.mem q.host.mem h₀ h₁
        (Sum.elim (fun i => (q.restrict f hf).host.val
            ((q.restrict f hf).val ((Equiv.refl (q.restrict f hf).idx).symm i)))
          (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b)))
        (Sum.elim (fun i => q.host.val (q.val i))
          (fun b => (q.restrict f hf).incl.onVertex PUnit.unit (params b))) := by
  intro β _hβg ρ hρinf hρμ params hjoint h₀ h₁
  classical
  let p := q.restrict f hf
  let Zpar : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun b => A.occ (params b)
  let Z : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ B) :=
    fun b => ⟨(Zpar b).1, f.onVertex (Zpar b).1 (Zpar b).2⟩
  have hDE : P.scheme.DiagramEq (X := p.host) (Y := q.host)
      (typeJoint (p := p) Zpar) (typeJoint (p := q) Z) := by
    by_cases hβτ : #β ≤ seq.τ
    · exact infra_611_image_agree f hf q seq hidxμ hτμ hκ hmaj params hβτ
    · have hEqFun : typeJoint (p := p) Zpar = typeJoint (p := q) Z := by
        funext t
        cases t with
        | inl j => rfl
        | inr b => rfl
      rw [hEqFun]
      exact P.scheme.diagram_refl q.host _
  exact infra_611_of_diagram f hf q hνμ params ρ hρinf hρμ hjoint h₀ h₁ hDE

/-! ## Free lift and free-from -/

/-- `q` is the free lift of its restriction. The witness sequence is the fresh code, whose
majority values are `q`'s joints, and `SameGaloisType` is the testing criterion. -/
theorem infra_611_isFreeLift
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (seq : ApproximationSequence (q.restrict f hf))
    (hνμ : q.ν = μ) (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (hτμ : seq.τ < μ) (hκ : seq.τ + aleph0 < #seq.κIndex)
    (hmaj : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z)) :
    IsFreeLift (q.restrict f hf) q f hf (Equiv.refl (q.restrict f hf).idx) := by
  let p := q.restrict f hf
  have hνp : p.ν = μ := hνμ
  have hidxp : #p.idx ≤ σ := hidx
  obtain ⟨code, hτ, _, _⟩ :=
    infra_611_fresh_code P σ hσ hμ hrec hσSucc p hνp hidxp seq.τ hτμ
  have hL := infra_610_closed_level P σ hσ hμ hrec
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  refine ⟨?_, code, ?_⟩
  · exact infra_610_same_galois f hf p q (Equiv.refl p.idx) σ hσ hσlt hidxp hνp hνμ hL
      (infra_611_tests f hf q seq hνμ hidxμ hτμ hκ hmaj σ)
  · intro ι Z hι
    have hιseq : #ι ≤ seq.τ := by simpa [hτ] using hι
    obtain ⟨Z0, hcode⟩ :=
      infra_611_code_majority f hf q seq hκ hmaj code hτ.ge Z hιseq
    exact ⟨Z0, typeJoint (p := q) Z, hcode⟩

/-- **Lemma 6.11, same level.** `q` is free from `A`. -/
theorem infra_611_isFreeFrom
    (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : aleph0 ≤ σ)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (hrec : μ ∈ recursionClosedLevels P σ) (hσSucc : Order.succ σ ≤ μ)
    {A B : P.scheme.Object μ hμ}
    (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ B))
    (hf : P.scheme.permitted (X := A) (Y := B) f)
    (q : TupleOver K oneVertexShape P.scheme hμ B)
    (seq : ApproximationSequence (q.restrict f hf))
    (hνμ : q.ν = μ) (hidx : #q.idx ≤ σ) (hidxμ : #q.idx < μ)
    (hτμ : seq.τ < μ) (hκ : seq.τ + aleph0 < #seq.κIndex)
    (_hκμ : #seq.κIndex < μ)
    (hmaj : ∀ {ι : Type u}
      (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ B)),
      #ι ≤ seq.τ →
      ∃ Z0 : ι → Occurrence K oneVertexShape (P.scheme.asSystem hμ A),
        IsMajorityValue seq Z0 q.hν q.host (typeJoint (p := q) Z)) :
    IsFreeFrom f hf q :=
  ⟨q.restrict f hf, Equiv.refl _,
    infra_611_isFreeLift P σ hσ hμ hrec hσSucc f hf q seq hνμ hidx hidxμ hτμ hκ hmaj⟩

end
end AEC
