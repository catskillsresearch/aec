module

public import AEC.Section7.AltTwoTied

@[expose] public section

/-!
# The block restriction of Proposition 7.3

English Prop 7.3 (block proof): "Present `A = F(I)` on a well-order … with more than `σ`
disjoint consecutive blocks, each of order type and cardinality `µ`. Let `J₀` consist of the
supports of the approximation lists, together with an initial segment of order type `χ⁺` in
every candidate block … choose a candidate block `J` whose interior contains neither a hit nor
a cut of either placement. Set `A* = F(J₀ ∪ J) ≤ A` … The restrictions of `q₀` and `q₁` to
`A*` are equal."

* Order combinatorics on `Bk ×ₗ M`: a position of an order extension meets at most one block
  (`infra_73_meetsBlock_unique`), so fewer than `#Bk` positions leave a clean block
  (`infra_73_clean_block`); a small set of positions of a block moves into a reservoir of the
  same block, order preserving and fixing everything outside the block (`infra_73_move`).
* `infra_73_moved_pattern`: against a placement with no position meeting the block, the moved
  parameter terms have the same natural diagram (Lemma 4.6 order pattern).
-/

namespace AEC
section

universe u

open Cardinal Classical FirstOrder Function

attribute [local instance] Classical.propDecidable

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Blocks of a lexicographic order -/

section BlockOrder

variable {Bk M : Type u} [LinearOrder Bk] [LinearOrder M]

/-- A position `x` of an order extension `f` meets block `b` when it lies between two
positions of that block (a hit, or an interior cut). -/
def Infra73MeetsBlock {L : Type u} [LinearOrder L] (f : Bk ×ₗ M ↪o L) (x : L) (b : Bk) : Prop :=
  ∃ m m', f (toLex (b, m)) ≤ x ∧ x ≤ f (toLex (b, m'))

theorem infra_73_meetsBlock_unique {L : Type u} [LinearOrder L] (f : Bk ×ₗ M ↪o L) (x : L)
    {b b' : Bk} (h : Infra73MeetsBlock f x b) (h' : Infra73MeetsBlock f x b') : b = b' := by
  obtain ⟨m1, m1', h1, h1'⟩ := h
  obtain ⟨m2, m2', h2, h2'⟩ := h'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hf : f (toLex (b, m1')) < f (toLex (b', m2)) :=
      f.lt_iff_lt.mpr (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt))
    exact lt_irrefl x (h1'.trans_lt (hf.trans_le h2))
  · have hf : f (toLex (b', m2')) < f (toLex (b, m1)) :=
      f.lt_iff_lt.mpr (Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt))
    exact lt_irrefl x (h2'.trans_lt (hf.trans_le h1))

/-- A position not meeting block `b` compares alike with every position of `b`. -/
theorem infra_73_not_meets {L : Type u} [LinearOrder L] (f : Bk ×ₗ M ↪o L) (x : L) (b : Bk)
    (h : ¬ Infra73MeetsBlock f x b) (m m' : M) :
    (x < f (toLex (b, m)) ↔ x < f (toLex (b, m'))) ∧
      (f (toLex (b, m)) < x ↔ f (toLex (b, m')) < x) := by
  have hne : ∀ m, x ≠ f (toLex (b, m)) := fun m hx => h ⟨m, m, hx.ge, hx.le⟩
  have key : ∀ m m', x < f (toLex (b, m)) → x < f (toLex (b, m')) := by
    intro m m' hm
    by_contra hm'
    exact h ⟨m', m, not_lt.mp hm', hm.le⟩
  refine ⟨⟨key m m', key m' m⟩, ?_⟩
  constructor
  · intro hlt
    rcases lt_trichotomy x (f (toLex (b, m'))) with h1 | h1 | h1
    · exact absurd (key m' m h1) (not_lt.mpr hlt.le)
    · exact absurd h1 (hne m')
    · exact h1
  · intro hlt
    rcases lt_trichotomy x (f (toLex (b, m))) with h1 | h1 | h1
    · exact absurd (key m m' h1) (not_lt.mpr hlt.le)
    · exact absurd h1 (hne m)
    · exact h1

/-- Few positions leave a block met by none of them. -/
theorem infra_73_clean_block {L0 L1 : Type u} [LinearOrder L0] [LinearOrder L1]
    (f0 : Bk ×ₗ M ↪o L0) (f1 : Bk ×ₗ M ↪o L1) (X0 : Set L0) (X1 : Set L1)
    {σ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (h0 : #X0 ≤ σ) (h1 : #X1 ≤ σ) (hBk : σ < #Bk) :
    ∃ b : Bk, (∀ x ∈ X0, ¬ Infra73MeetsBlock f0 x b) ∧
      (∀ x ∈ X1, ¬ Infra73MeetsBlock f1 x b) := by
  let Bad0 : Set Bk := {b | ∃ x ∈ X0, Infra73MeetsBlock f0 x b}
  let Bad1 : Set Bk := {b | ∃ x ∈ X1, Infra73MeetsBlock f1 x b}
  have hB0 : #Bad0 ≤ #X0 := by
    have hw : ∀ b : Bad0, ∃ x : X0, Infra73MeetsBlock f0 x.1 b.1 := by
      rintro ⟨b, x, hx, hm⟩
      exact ⟨⟨x, hx⟩, hm⟩
    choose w hw using hw
    refine mk_le_of_injective (f := w) ?_
    intro b b' hbb
    apply Subtype.ext
    have h := hw b'
    rw [← hbb] at h
    exact infra_73_meetsBlock_unique f0 _ (hw b) h
  have hB1 : #Bad1 ≤ #X1 := by
    have hw : ∀ b : Bad1, ∃ x : X1, Infra73MeetsBlock f1 x.1 b.1 := by
      rintro ⟨b, x, hx, hm⟩
      exact ⟨⟨x, hx⟩, hm⟩
    choose w hw using hw
    refine mk_le_of_injective (f := w) ?_
    intro b b' hbb
    apply Subtype.ext
    have h := hw b'
    rw [← hbb] at h
    exact infra_73_meetsBlock_unique f1 _ (hw b) h
  have hU : #(Bad0 ∪ Bad1 : Set Bk) < #Bk := by
    refine ((mk_union_le _ _).trans ?_).trans_lt hBk
    calc #Bad0 + #Bad1 ≤ σ + σ := add_le_add (hB0.trans h0) (hB1.trans h1)
      _ = σ := add_eq_self hσ
  have hne : ∃ b, b ∉ Bad0 ∪ Bad1 := by
    by_contra hall
    push Not at hall
    have : (Bad0 ∪ Bad1 : Set Bk) = Set.univ := Set.eq_univ_of_forall hall
    rw [this, mk_univ] at hU
    exact lt_irrefl _ hU
  obtain ⟨b, hb⟩ := hne
  simp only [Set.mem_union, not_or] at hb
  refine ⟨b, fun x hx hm => hb.1 ⟨x, hx, hm⟩, fun x hx hm => hb.2 ⟨x, hx, hm⟩⟩

/-- Move the positions of `T` lying in block `b` into the reservoir `ρ` of that block, order
preserving, and fix every other position. -/
def infra_73_mv (b : Bk) {R : Type u} [LinearOrder R] (ρ : R ↪o M) (T : Set (Bk ×ₗ M))
    (emb : {m : M | toLex (b, m) ∈ T} ↪o R) (x : Bk ×ₗ M) : Bk ×ₗ M :=
  if hx : x ∈ T ∧ (ofLex x).1 = b then
    toLex (b, ρ (emb ⟨(ofLex x).2, by
      show toLex (b, (ofLex x).2) ∈ T
      rw [← hx.2]
      exact hx.1⟩))
  else x

theorem infra_73_mv_out (b : Bk) {R : Type u} [LinearOrder R] (ρ : R ↪o M)
    (T : Set (Bk ×ₗ M)) (emb : {m : M | toLex (b, m) ∈ T} ↪o R) (x : Bk ×ₗ M)
    (hx : (ofLex x).1 ≠ b) : infra_73_mv b ρ T emb x = x := by
  unfold infra_73_mv
  rw [dite_eq_right (fun h => hx h.2)]

theorem infra_73_mv_in (b : Bk) {R : Type u} [LinearOrder R] (ρ : R ↪o M)
    (T : Set (Bk ×ₗ M)) (emb : {m : M | toLex (b, m) ∈ T} ↪o R) (x : Bk ×ₗ M)
    (hxT : x ∈ T) (hx : (ofLex x).1 = b) :
    (ofLex (infra_73_mv b ρ T emb x)).1 = b ∧
      (ofLex (infra_73_mv b ρ T emb x)).2 ∈ Set.range ρ := by
  unfold infra_73_mv
  rw [dite_eq_left ⟨hxT, hx⟩]
  exact ⟨rfl, ⟨_, rfl⟩⟩

theorem infra_73_mv_strictMonoOn (b : Bk) {R : Type u} [LinearOrder R] (ρ : R ↪o M)
    (T : Set (Bk ×ₗ M)) (emb : {m : M | toLex (b, m) ∈ T} ↪o R) :
    StrictMonoOn (infra_73_mv b ρ T emb) T := by
  intro x hxT y hyT hxy
  have hlt := Prod.Lex.lt_iff.mp hxy
  by_cases hxb : (ofLex x).1 = b <;> by_cases hyb : (ofLex y).1 = b
  · unfold infra_73_mv
    rw [dite_eq_left ⟨hxT, hxb⟩, dite_eq_left ⟨hyT, hyb⟩]
    apply Prod.Lex.toLex_lt_toLex.mpr
    refine Or.inr ⟨rfl, ρ.lt_iff_lt.mpr (emb.lt_iff_lt.mpr ?_)⟩
    rcases hlt with h | h
    · rw [hxb, hyb] at h
      exact absurd h (lt_irrefl _)
    · exact h.2
  · unfold infra_73_mv
    rw [dite_eq_left ⟨hxT, hxb⟩, dite_eq_right (fun h => hyb h.2)]
    apply Prod.Lex.lt_iff.mpr
    left
    rcases hlt with h | h
    · rw [hxb] at h
      exact h
    · exact absurd (h.1.symm.trans hxb) hyb
  · unfold infra_73_mv
    rw [dite_eq_right (fun h => hxb h.2), dite_eq_left ⟨hyT, hyb⟩]
    apply Prod.Lex.lt_iff.mpr
    left
    rcases hlt with h | h
    · rw [hyb] at h
      exact h
    · exact absurd (h.1.trans hyb) hxb
  · unfold infra_73_mv
    rw [dite_eq_right (fun h => hxb h.2), dite_eq_right (fun h => hyb h.2)]
    exact hxy

end BlockOrder

/-- A set of at most `κ` positions of a well-order embeds into `(κ⁺).ToType`. -/
theorem infra_73_reservoir (κ : Cardinal.{u}) {M : Type u} [LinearOrder M] [WellFoundedLT M]
    (X : Set M) (hX : #X ≤ κ) : Nonempty (X ↪o (Order.succ κ).ord.ToType) := by
  have hlt : Ordinal.type (α := X) (· < ·) < (Order.succ κ).ord := by
    rw [Cardinal.lt_ord, Ordinal.card_type]
    exact hX.trans_lt (Order.lt_succ κ)
  have hle : Ordinal.type (α := X) (· < ·) ≤
      Ordinal.type (α := (Order.succ κ).ord.ToType) (· < ·) := by
    rw [Ordinal.type_toType]
    exact hlt.le
  obtain ⟨r⟩ := Ordinal.type_le_iff'.mp hle
  exact ⟨RelEmbedding.orderEmbeddingOfLTEmbedding r⟩

/-- `o₁ ≤ o₂` embeds `o₁.ToType` into `o₂.ToType`. -/
def infra_73_toType_le {o₁ o₂ : Ordinal.{u}} (h : o₁ ≤ o₂) : o₁.ToType ↪o o₂.ToType :=
  OrderEmbedding.ofStrictMono
    (fun x => Ordinal.ToType.mk ⟨(Ordinal.ToType.mk.symm x).1,
      lt_of_lt_of_le (Ordinal.ToType.mk.symm x).2 h⟩)
    (by
      intro x y hxy
      apply Ordinal.ToType.mk.lt_iff_lt.mpr
      have := Ordinal.ToType.mk.symm.lt_iff_lt.mpr hxy
      exact this)

/-! ## Moving parameter terms inside a clean block -/

/-- Move a term supported in `T` along `mv`. -/
def infra_73_moveTerm {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I]
    (mv : I → I) (T : Set I) (hmono : StrictMonoOn mv T)
    (t : SupportTerm lab arity I) (ht : ∀ k, t.pos k ∈ T) : SupportTerm lab arity I where
  label := t.label
  pos := fun k => mv (t.pos k)
  increasing := fun _ _ hab => hmono (ht _) (ht _) (t.increasing hab)

/-- **Moving inside a clean block keeps the natural diagram** (English: "No position of
either candidate separates the interior of `J`, so the move preserves the natural diagram
with either candidate"). -/
theorem infra_73_moved_pattern {K : AbstractElementaryClass.{u}} {E : OrderPresentation K}
    {D : StableDiagram K} {Bk M : Type u} [LinearOrder Bk] [LinearOrder M]
    [Nonempty (Bk ×ₗ M)] {α β : Type u} {σ : Cardinal.{u}} (hσ : #(α ⊕ β) ≤ σ)
    (Q : Placement E.lab E.arity (Bk ×ₗ M) α) (b : Bk)
    (hclean : ∀ a k, ¬ Infra73MeetsBlock Q.f ((Q.z a).pos k) b)
    (mv : Bk ×ₗ M → Bk ×ₗ M) (T : Set (Bk ×ₗ M)) (hmono : StrictMonoOn mv T)
    (hout : ∀ x ∈ T, (ofLex x).1 ≠ b → mv x = x)
    (hin : ∀ x ∈ T, (ofLex x).1 = b → (ofLex (mv x)).1 = b)
    (s : β → SupportTerm E.lab E.arity (Bk ×ₗ M)) (hs : ∀ j k, (s j).pos k ∈ T) :
    SameNaturalDiagram K E D σ hσ (Q.joint s)
      (Q.joint (fun j => infra_73_moveTerm mv T hmono (s j) (hs j))) := by
  have hz : ∀ a (k : Fin (E.arity (Q.z a).label)) (p : Bk ×ₗ M), p ∈ T →
      ((Q.z a).pos k < Q.f p ↔ (Q.z a).pos k < Q.f (mv p)) ∧
        (Q.f p < (Q.z a).pos k ↔ Q.f (mv p) < (Q.z a).pos k) := by
    intro a k p hp
    by_cases hpb : (ofLex p).1 = b
    · have hq := hin p hp hpb
      have e1 : p = toLex (b, (ofLex p).2) := by rw [← hpb]; rfl
      have e2 : mv p = toLex (b, (ofLex (mv p)).2) := by rw [← hq]; rfl
      have h := infra_73_not_meets Q.f _ b (hclean a k) (ofLex p).2 (ofLex (mv p)).2
      rw [← e1, ← e2] at h
      exact h
    · rw [hout p hp hpb]
      exact ⟨Iff.rfl, Iff.rfl⟩
  refine sameNaturalDiagram_of_pattern _ _ (fun c => by cases c <;> rfl) ?_
  intro c d k l hk hl hk' hl'
  cases c with
  | inl a =>
    cases d with
    | inl a' => exact Iff.rfl
    | inr j => exact (hz a ⟨k, hk⟩ _ (hs j _)).1
  | inr j =>
    cases d with
    | inl a => exact (hz a ⟨l, hl⟩ _ (hs j _)).2
    | inr j' =>
      change Q.f ((s j).pos ⟨k, hk⟩) < Q.f ((s j').pos ⟨l, hl⟩) ↔
        Q.f (mv ((s j).pos ⟨k, hk'⟩)) < Q.f (mv ((s j').pos ⟨l, hl'⟩))
      rw [Q.f.lt_iff_lt, Q.f.lt_iff_lt]
      exact (hmono.lt_iff_lt (hs j _) (hs j' _)).symm

/-! ## Placements answer tests of the base -/

section Lifts

variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 800000 in
/-- Two queries of `A = E(I)` whose placed joints with a placement of `q` have the same natural
diagram get the same answer from `q` (Proposition 4.9: the placement realizes the tests). -/
theorem infra_73_lifts_diagramEq (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) {A : P.scheme.Object μ hμ}
    (q : TupleOver K oneVertexShape P.scheme hμ A) (hqν : q.ν = μ)
    {I : Type u} [LinearOrder I] [Nonempty I] (hI : #I = μ)
    (eA : (P.E.obj I).carrier ≃[K.τ] A.model.carrier)
    (Q : Placement P.E.lab P.E.arity I q.idx) {ρ : Cardinal.{u}} (hρinf : ℵ₀ ≤ ρ)
    (hρμ : ρ < μ) (hls : ls K ≤ ρ) {β : Type u} (hj : #(q.idx ⊕ β) ≤ ρ)
    (p1 p2 : β → (P.E.obj I).carrier)
    (hL1 : Q.Lifts P.E P.D q.host.mem ((q.incl.onVertex PUnit.unit).comp eA.toEmbedding)
      (fun a => q.host.val (q.val a)) ρ hj p1)
    (hL2 : Q.Lifts P.E P.D q.host.mem ((q.incl.onVertex PUnit.unit).comp eA.toEmbedding)
      (fun a => q.host.val (q.val a)) ρ hj p2)
    (hN : SameNaturalDiagram K P.E P.D ρ hj (Q.joint (fun b => supportTermOf P.E (p1 b)))
      (Q.joint (fun b => supportTermOf P.E (p2 b)))) :
    P.scheme.DiagramEq (X := q.host) (Y := q.host)
      (typeJoint (p := q) (fun b => A.occ (eA (p1 b))))
      (typeJoint (p := q) (fun b => A.occ (eA (p2 b)))) := by
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ
  have hcH : Model.card q.host.model = μ := by simpa [hqν] using q.host.card
  have hIc : Model.card (P.E.obj I) = μ := SingleModelData.card_obj_eq (P := P) hμ I hI
  have htρ : P.D.t ρ < μ := P.t_lt hμ hρinf hρμ
  have hcB : P.D.t ρ ≤ Model.card q.host.model := htρ.le.trans hcH.ge
  have hcJ : P.D.t ρ ≤ Model.card (P.E.obj Q.J) :=
    (htρ.le.trans hIc.ge).trans (mk_le_of_injective (P.E.map Q.f).injective)
  have hMJ : K.Mem (P.E.obj Q.J) := orderPresentation_obj_mem P.E Q.J
  have s1 := hL1 hcB hcJ
  have s2 := hL2 hcB hcJ
  have sN := SameNaturalDiagram.same hρinf hN hcJ hcJ hMJ hMJ
  have s := P.D.trans hj q.host.mem hMJ q.host.mem hcB hcJ hcB _ _ _ s1
    (P.D.trans hj hMJ hMJ q.host.mem hcJ hcJ hcB _ _ _ sN (P.D.symm hj q.host.mem hMJ hcB hcJ _ _ s2))
  have hρμ' : ρ < q.ν := by rw [hqν]; exact hρμ
  have hα : #(q.idx ⊕ β) < q.ν := hj.trans_lt hρμ'
  have hmaxμ : max #(q.idx ⊕ β) ℵ₀ < μ := max_lt (hj.trans_lt hρμ) (P.aleph0_lt hμ)
  have htm : P.D.t (max #(q.idx ⊕ β) ℵ₀) < μ := P.t_lt hμ (le_max_right _ _) hmaxμ
  have hcBm : P.D.t (max #(q.idx ⊕ β) ℵ₀) ≤ Model.card q.host.model := htm.le.trans hcH.ge
  let L1 : q.idx ⊕ β → q.host.model.carrier :=
    Sum.elim (fun a => q.host.val (q.val a))
      (fun b => ((q.incl.onVertex PUnit.unit).comp eA.toEmbedding) (p1 b))
  let L2 : q.idx ⊕ β → q.host.model.carrier :=
    Sum.elim (fun a => q.host.val (q.val a))
      (fun b => ((q.incl.onVertex PUnit.unit).comp eA.toEmbedding) (p2 b))
  have sm := P.D.same_relevel (σ := ρ) (τ := max #(q.idx ⊕ β) ℵ₀) (σ' := ρ)
    hj hρinf (le_max_right _ _) le_rfl (max_le hj hρinf) hls q.host.mem q.host.mem
    hcB hcB hcB hcB hcBm hcBm L1 L2 s (le_max_left _ _) id
  have hSameD : P.D.SameD q.host.model q.host.model L1 L2 :=
    ⟨q.host.mem, q.host.mem, hcBm, hcBm, sm⟩
  have hEq : P.scheme.DiagramEq (X := q.host) (Y := q.host) (fun t => q.host.occ (L1 t))
      (fun t => q.host.occ (L2 t)) :=
    (SingleModelData.diagramEq_iff_sameD (P := P) (α := q.idx ⊕ β) q.hν q.hν q.host q.host
      L1 L2 hα hα).mpr hSameD
  refine infra_73_diagramEq_of_eq hEq ?_ ?_
  · intro t
    cases t with
    | inl a => rfl
    | inr b => rfl
  · intro t
    cases t with
    | inl a => rfl
    | inr b => rfl

end Lifts

/-! ## Cardinal bookkeeping -/

theorem infra_73_card_terms {lab : Type u} {arity : lab → ℕ} {I : Type u} [LinearOrder I]
    (J : Set I) :
    #{t : SupportTerm lab arity I // termSupport t ⊆ J} ≤ #lab * max ℵ₀ #J := by
  let F : {t : SupportTerm lab arity I // termSupport t ⊆ J} → lab × List J :=
    fun t => (t.1.label, List.ofFn (fun k => (⟨t.1.pos k, t.2 ⟨k, rfl⟩⟩ : J)))
  have hF : Function.Injective F := by
    rintro ⟨⟨l1, p1, m1⟩, h1⟩ ⟨⟨l2, p2, m2⟩, h2⟩ hEq
    simp only [F, Prod.mk.injEq] at hEq
    obtain ⟨rfl, hL⟩ := hEq
    have hp : p1 = p2 := by
      have h := List.ofFn_injective hL
      funext k
      exact congrArg Subtype.val (congrFun h k)
    subst hp
    rfl
  calc #{t : SupportTerm lab arity I // termSupport t ⊆ J} ≤ #(lab × List J) :=
        mk_le_of_injective hF
    _ = #lab * #(List J) := by rw [mk_prod, lift_id, lift_id]
    _ ≤ #lab * max ℵ₀ #J := mul_le_mul_right (mk_list_le_max _) _

theorem infra_73_card_iUnion_countable {α X : Type u} (f : α → Set X)
    (hf : ∀ a, #(f a) ≤ ℵ₀) : #(⋃ a, f a) ≤ #α * ℵ₀ :=
  (mk_iUnion_le f).trans (mul_le_mul_right (ciSup_le' hf) _)

theorem infra_73_card_termSupport {lab : Type u} {arity : lab → ℕ} {I : Type u}
    [LinearOrder I] (t : SupportTerm lab arity I) : #(termSupport t) ≤ ℵ₀ := by
  have : Countable (termSupport t) := (Set.finite_range t.pos).countable.to_subtype
  exact mk_le_aleph0

/-- `P.scheme` diagrams pass to arbitrary reindexings. -/
theorem infra_73_scheme_comp {K : AbstractElementaryClass.{u}} {P : SingleModelData K}
    {μ ν : Cardinal.{u}} {hμ : μ ∈ P.eligible} {hν : ν ∈ P.eligible}
    {X : P.scheme.Object μ hμ} {Y : P.scheme.Object ν hν} {α γ : Type u}
    {xs : α → Occurrence K oneVertexShape (P.scheme.asSystem hμ X)}
    {ys : α → Occurrence K oneVertexShape (P.scheme.asSystem hν Y)}
    (h : P.scheme.DiagramEq (X := X) (Y := Y) xs ys) (ι : γ → α) :
    P.scheme.DiagramEq (X := X) (Y := Y) (fun c => xs (ι c)) (fun c => ys (ι c)) :=
  SingleModelData.DiagramEq.comp h ι

/-! ## Moved tests get the same answers -/

section Answers

variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 1600000 in
/-- **A type answers a test and its block-moved copy alike.** `q` has a placement `Q` over the
block presentation `A ≅ E(Bk ×ₗ M)` realizing its tests of size at most `χ`; no position of
`Q` meets block `b`; the test terms are moved inside `b` by `mv`. -/
theorem infra_73_moved_answer (P : SingleModelData K) {μ : Cardinal.{u}}
    (hμ : μ ∈ P.eligible) {A : P.scheme.Object μ hμ}
    (q : TupleOver K oneVertexShape P.scheme hμ A) (hqν : q.ν = μ)
    {Bk M : Type u} [LinearOrder Bk] [LinearOrder M] [Nonempty (Bk ×ₗ M)]
    (hI : #(Bk ×ₗ M) = μ)
    (eA : (P.E.obj (Bk ×ₗ M)).carrier ≃[K.τ] A.model.carrier)
    {σ χ : Cardinal.{u}} (hσ : ℵ₀ ≤ σ) (hidx : #q.idx ≤ σ) (hσμ : σ < μ) (hχμ : χ < μ)
    (hls : ls K ≤ σ + χ)
    (Q : Placement P.E.lab P.E.arity (Bk ×ₗ M) q.idx)
    (hQ : ∀ {β : Type u} (_ : #β ≤ χ) (p : β → (P.E.obj (Bk ×ₗ M)).carrier)
      (hj : #(q.idx ⊕ β) ≤ σ + χ),
      Q.Lifts P.E P.D q.host.mem ((q.incl.onVertex PUnit.unit).comp eA.toEmbedding)
        (fun a => q.host.val (q.val a)) (σ + χ) hj p)
    (b : Bk) (hclean : ∀ a k, ¬ Infra73MeetsBlock Q.f ((Q.z a).pos k) b)
    (mv : Bk ×ₗ M → Bk ×ₗ M) (T : Set (Bk ×ₗ M)) (hmono : StrictMonoOn mv T)
    (hout : ∀ x ∈ T, (ofLex x).1 ≠ b → mv x = x)
    (hin : ∀ x ∈ T, (ofLex x).1 = b → (ofLex (mv x)).1 = b)
    {β : Type u} (hβ : #β ≤ χ)
    (s : β → SupportTerm P.E.lab P.E.arity (Bk ×ₗ M)) (hs : ∀ j k, (s j).pos k ∈ T) :
    P.scheme.DiagramEq (X := q.host) (Y := q.host)
      (typeJoint (p := q) (fun j => A.occ (eA (P.E.realize (s j)))))
      (typeJoint (p := q) (fun j => A.occ (eA (P.E.realize
        (infra_73_moveTerm mv T hmono (s j) (hs j)))))) := by
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ
  have hρinf : ℵ₀ ≤ σ + χ := hσ.trans (self_le_add_right σ χ)
  have hρμ : σ + χ < μ := add_lt_of_lt hμinf hσμ hχμ
  have hj : #(q.idx ⊕ β) ≤ σ + χ := by
    rw [mk_sum, lift_id, lift_id]
    exact add_le_add hidx hβ
  let p1 : β → (P.E.obj (Bk ×ₗ M)).carrier := fun j => P.E.realize (s j)
  let p2 : β → (P.E.obj (Bk ×ₗ M)).carrier :=
    fun j => P.E.realize (infra_73_moveTerm mv T hmono (s j) (hs j))
  have n1 : SameNaturalDiagram K P.E P.D (σ + χ) hj
      (Q.joint (fun j => supportTermOf P.E (p1 j))) (Q.joint s) := by
    refine sameNaturalDiagram_of_realize_eq _ _ ?_
    intro c
    cases c with
    | inl a => rfl
    | inr j =>
      change P.E.realize (SupportTerm.along Q.f (supportTermOf P.E (p1 j))) =
        P.E.realize (SupportTerm.along Q.f (s j))
      rw [← P.E.realize_along, ← P.E.realize_along, realize_supportTermOf]
  have n2 := infra_73_moved_pattern (D := P.D) hj Q b hclean mv T hmono hout hin s hs
  have n3 : SameNaturalDiagram K P.E P.D (σ + χ) hj
      (Q.joint (fun j => infra_73_moveTerm mv T hmono (s j) (hs j)))
      (Q.joint (fun j => supportTermOf P.E (p2 j))) := by
    refine sameNaturalDiagram_of_realize_eq _ _ ?_
    intro c
    cases c with
    | inl a => rfl
    | inr j =>
      change P.E.realize (SupportTerm.along Q.f (infra_73_moveTerm mv T hmono (s j) (hs j))) =
        P.E.realize (SupportTerm.along Q.f (supportTermOf P.E (p2 j)))
      rw [← P.E.realize_along, ← P.E.realize_along, realize_supportTermOf]
  have hN := SameNaturalDiagram.trans hρinf (SameNaturalDiagram.trans hρinf n1 n2) n3
  exact infra_73_lifts_diagramEq P hμ q hqν hI eA Q hρinf hρμ hls hj p1 p2
    (hQ hβ p1 hj) (hQ hβ p2 hj) hN

end Answers

/-! ## The block restriction -/

section Main

variable {K : AbstractElementaryClass.{u}}

set_option maxHeartbeats 12800000 in
/-- **English Prop 7.3, block restriction.** At every tail level, the term values `Z₀` on
`J₀` (supports of a long approximation sequence of `q`, and a reservoir of order type `χ⁺` at
the start of each of the `σ⁺` blocks of a presentation `A ≅ E(σ⁺ ×ₗ µ)`) have size at most
`h(σ)`, and every competitor `q'` agreeing with `q` on `Z₀` has the same restriction as `q`
to a copy `A* = E(J₀ ∪ J)` of `A` for a block `J` that neither placement meets; `A ≅ A*`
fixes the sequence (Proposition 4.3, homogeneity). -/
theorem infra_73_block_restriction (P : SingleModelData K) (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) : Infra73BlockRestriction P σ hσ := by
  classical
  intro μ hμT A q uIdx cIdx e hqν hidx
  have hμ : μ ∈ P.eligible := Tail.mem (infra_73_tail P σ hσ) hμT
  have hrec : μ ∈ recursionClosedLevels P σ := infra_73_tail_rec hμT
  have hσSucc : Order.succ σ ≤ μ := infra_73_tail_succ hμT
  have hσlt : σ < μ := (Order.lt_succ σ).trans_le hσSucc
  have hμinf : ℵ₀ ≤ μ := P.aleph0_le hμ
  have hidxμ : #q.idx < μ := hidx.trans_lt hσlt
  have hhμ : infra_73_h P σ < μ := infra_73_h_lt hμ hμT
  obtain ⟨seq, -, hκ, hτge, hlong⟩ := infra_73_sequence P σ hσ hμ hμT q hqν hidx
  -- bounds
  let χ0 : Cardinal.{u} := infra_73_chi P σ
  have hχ0h : Order.succ χ0 ≤ infra_73_h P σ := Order.succ_le_succ (le_max_right _ _)
  have hσh : Order.succ σ ≤ infra_73_h P σ := Order.succ_le_succ (le_max_left _ _)
  have hhinf : ℵ₀ ≤ infra_73_h P σ := hσ.trans ((Order.le_succ σ).trans hσh)
  have hgχ0 : P.g σ + ls K ≤ χ0 :=
    (add_le_add le_rfl (le_max_left _ _)).trans (le_max_right _ _)
  have hχ0inf : ℵ₀ ≤ χ0 :=
    (le_max_right (ls K) ℵ₀).trans (le_add_self.trans (le_max_right _ _))
  have hlsh : ls K ≤ infra_73_h P σ :=
    ((le_max_left (ls K) ℵ₀).trans (le_add_self.trans (le_max_right _ _))).trans
      ((Order.le_succ χ0).trans hχ0h)
  -- the block presentation
  let Bk : Type u := (Order.succ σ).ord.ToType
  let M : Type u := lvlOrder μ
  have hBk : #Bk = Order.succ σ := mk_ord_toType _
  have hM : #M = μ := mk_lvlOrder hμinf
  have hBkne : Nonempty Bk := by
    rw [← mk_ne_zero_iff, hBk]
    exact ((zero_le (a := σ)).trans_lt (Order.lt_succ σ)).ne'
  have : Nonempty (Bk ×ₗ M) := ⟨toLex (Classical.arbitrary Bk, Classical.arbitrary M)⟩
  have hI : #(Bk ×ₗ M) = μ := by
    change #(Bk × M) = μ
    rw [mk_prod, lift_id, lift_id, hBk, hM]
    exact Cardinal.mul_eq_right hμinf hσSucc ((zero_le (a := σ)).trans_lt (Order.lt_succ σ)).ne'
  obtain ⟨eA⟩ := SingleModelData.exists_present_equiv (P := P) hμ A (Bk ×ₗ M) hI
  -- reservoir and `J₀`
  have hres_le : (Order.succ χ0).ord ≤ (max μ 1).ord :=
    Cardinal.ord_le_ord.mpr ((hχ0h.trans hhμ.le).trans (le_max_left _ _))
  let ρres : (Order.succ χ0).ord.ToType ↪o M := infra_73_toType_le hres_le
  let L : seq.κIndex × q.idx → A.model.carrier := fun x => A.val (seq.family x.1 x.2)
  let SeqSupp : Set (Bk ×ₗ M) := ⋃ x, termSupport (supportTermOf P.E (eA.symm (L x)))
  let Res : Set (Bk ×ₗ M) := {x | (ofLex x).2 ∈ Set.range ρres}
  let J0 : Set (Bk ×ₗ M) := SeqSupp ∪ Res
  let ιZ : Type u := {t : SupportTerm P.E.lab P.E.arity (Bk ×ₗ M) // termSupport t ⊆ J0}
  let Z : ιZ → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
    fun t => A.occ (eA (P.E.realize t.1))
  have hSeq : #SeqSupp ≤ infra_73_h P σ := by
    refine (infra_73_card_iUnion_countable _ (fun x => infra_73_card_termSupport _)).trans ?_
    calc #(seq.κIndex × q.idx) * ℵ₀ ≤ infra_73_h P σ * infra_73_h P σ :=
          mul_le_mul' (infra_73_family_card seq hσ hidx hκ) hhinf
      _ = infra_73_h P σ := mul_eq_self hhinf
  have hRes : #Res ≤ infra_73_h P σ := by
    let F : Res → Bk × (Order.succ χ0).ord.ToType :=
      fun x => ((ofLex x.1).1, Classical.choose x.2)
    have hF : Function.Injective F := by
      rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      simp only [F, Prod.mk.injEq] at hxy
      apply Subtype.ext
      change x = y
      have h2 : (ofLex x).2 = (ofLex y).2 := by
        rw [← Classical.choose_spec hx, ← Classical.choose_spec hy, hxy.2]
      exact congrArg toLex (Prod.ext hxy.1 h2)
    refine (mk_le_of_injective hF).trans ?_
    rw [mk_prod, lift_id, lift_id, hBk, mk_ord_toType]
    calc Order.succ σ * Order.succ χ0 ≤ infra_73_h P σ * infra_73_h P σ := mul_le_mul' hσh hχ0h
      _ = infra_73_h P σ := mul_eq_self hhinf
  have hJ0 : #J0 ≤ infra_73_h P σ :=
    (mk_union_le _ _).trans ((add_le_add hSeq hRes).trans (add_eq_self hhinf).le)
  have hιZ : #ιZ ≤ infra_73_h P σ := by
    refine (infra_73_card_terms J0).trans ?_
    have hlab : #P.E.lab ≤ infra_73_h P σ := (P.E.lab_small.trans P.E.ell_eq.le).trans hlsh
    calc #P.E.lab * max ℵ₀ #J0 ≤ infra_73_h P σ * infra_73_h P σ :=
          mul_le_mul' hlab (max_le hhinf hJ0)
      _ = infra_73_h P σ := mul_eq_self hhinf
  refine ⟨seq, hτge, hlong, ιZ, Z, hιZ, ?_⟩
  intro q' e' hq'ν hMarg hDE
  have hidx' : #q'.idx ≤ σ := by rw [← Cardinal.mk_congr (e.trans e'.symm)]; exact hidx
  -- placements of `q` and `q'` (Proposition 4.9)
  have hgσ : P.g σ < μ := (hμ.1.closed P.g (Set.mem_insert_of_mem _ rfl)).below σ hσ hσlt
  have hκμ : max (P.g σ + ls K) (ls K + σ) < μ :=
    max_lt (add_lt_of_lt hμinf hgσ (P.ls_lt hμ)) (add_lt_of_lt hμinf (P.ls_lt hμ) hσlt)
  obtain ⟨χ, hχgt, hχμ, hpow⟩ :=
    exists_power_fixed_below hμ.1.working.strongLimit hσ hσlt hκμ
  have hlsχ : ls K + σ < χ := (le_max_right _ _).trans_lt hχgt
  have hgχ : P.g σ + ls K < χ := (le_max_left _ _).trans_lt hχgt
  have hρinf : ℵ₀ ≤ σ + χ := hσ.trans (self_le_add_right σ χ)
  have hρμ : σ + χ < μ := add_lt_of_lt hμinf hσlt hχμ
  have ht : P.D.t (σ + χ) ≤ μ := (P.t_lt hμ hρinf hρμ).le
  have hls : ls K ≤ σ + χ :=
    (self_le_add_right (ls K) σ).trans (hlsχ.le.trans (self_le_add_left χ σ))
  have : CategoricalUnbounded K := P.D.categoricalUnbounded
  have hIc : Model.card (P.E.obj (Bk ×ₗ M)) = μ :=
    SingleModelData.card_obj_eq (P := P) hμ (Bk ×ₗ M) hI
  have heA : K.Strong eA.toEmbedding := strong_of_equiv K eA (P.hE _)
  have hcH : Model.card q.host.model = μ := by simpa [hqν] using q.host.card
  have hcH' : Model.card q'.host.model = μ := by simpa [hq'ν] using q'.host.card
  obtain ⟨Q0, hQ0⟩ := exists_placement_lifting (hB := q.host.mem)
    (incl := (q.incl.onVertex PUnit.unit).comp eA.toEmbedding)
    (d := fun a => q.host.val (q.val a))
    (K.strong_trans _ _ heA (q.incl.onVertex_strong PUnit.unit)) (P.categorical hμ) hcH hIc
    hσ hidx hlsχ hpow ht
  obtain ⟨Q1, hQ1⟩ := exists_placement_lifting (hB := q'.host.mem)
    (incl := (q'.incl.onVertex PUnit.unit).comp eA.toEmbedding)
    (d := fun a => q'.host.val (q'.val a))
    (K.strong_trans _ _ heA (q'.incl.onVertex_strong PUnit.unit)) (P.categorical hμ) hcH' hIc
    hσ hidx' hlsχ hpow ht
  -- a block met by neither placement
  let X0 : Set Q0.J := ⋃ a, termSupport (Q0.z a)
  let X1 : Set Q1.J := ⋃ a, termSupport (Q1.z a)
  have hX0 : #X0 ≤ σ :=
    (infra_73_card_iUnion_countable _ (fun a => infra_73_card_termSupport _)).trans
      ((mul_le_mul' hidx hσ).trans (mul_eq_self hσ).le)
  have hX1 : #X1 ≤ σ :=
    (infra_73_card_iUnion_countable _ (fun a => infra_73_card_termSupport _)).trans
      ((mul_le_mul' hidx' hσ).trans (mul_eq_self hσ).le)
  obtain ⟨b, hb0, hb1⟩ := infra_73_clean_block Q0.f Q1.f X0 X1 hσ hX0 hX1
    (by rw [hBk]; exact Order.lt_succ σ)
  have clean0 : ∀ a k, ¬ Infra73MeetsBlock Q0.f ((Q0.z a).pos k) b :=
    fun a k => hb0 _ (Set.mem_iUnion.mpr ⟨a, k, rfl⟩)
  have clean1 : ∀ a k, ¬ Infra73MeetsBlock Q1.f ((Q1.z a).pos k) b :=
    fun a k => hb1 _ (Set.mem_iUnion.mpr ⟨a, k, rfl⟩)
  -- `A* = E(J₀ ∪ J)`
  let S : Set (Bk ×ₗ M) := J0 ∪ {x | (ofLex x).1 = b}
  have : Nonempty S := ⟨⟨toLex (b, Classical.arbitrary M), Or.inr rfl⟩⟩
  have hS : #S = μ := by
    refine le_antisymm ((mk_set_le S).trans hI.le) ?_
    rw [← hM]
    refine mk_le_of_injective (f := fun m : M => (⟨toLex (b, m), Or.inr rfl⟩ : S)) ?_
    intro m m' hmm
    have h := congrArg (fun x : S => (ofLex x.1).2) hmm
    exact h
  let incS : S ↪o (Bk ×ₗ M) := OrderEmbedding.subtype _
  have hSc : Model.card (P.E.obj S) = μ := SingleModelData.card_obj_eq (P := P) hμ S hS
  let Astar : SMObject K μ := SMObject.ofModel (P.E.obj S) (P.hE S) hSc
  let φS : (P.E.obj S).carrier ≃[K.τ] Astar.model.carrier :=
    SMObject.ofModelEquiv (P.E.obj S) (P.hE S) hSc
  let ιmap : Language.Embedding K.τ Astar.model.carrier A.model.carrier :=
    eA.toEmbedding.comp ((P.E.map incS).comp φS.symm.toEmbedding)
  have hιmap : K.Strong ιmap :=
    K.strong_trans _ _ (K.strong_trans _ _ (strong_of_equiv K φS.symm Astar.mem)
      (P.E.map_strong incS)) heA
  -- the sequence lies in `A*`
  have hsub : ∀ x, termSupport (supportTermOf P.E (eA.symm (L x))) ⊆ Set.range incS :=
    fun x y hy => ⟨⟨y, Or.inl (Or.inl (Set.mem_iUnion.mpr ⟨x, hy⟩))⟩, rfl⟩
  let Lstar : seq.κIndex × q.idx → Astar.model.carrier :=
    fun x => φS (P.E.realize (SupportTerm.pullback incS _ (hsub x)))
  have hιL : ∀ x, ιmap (Lstar x) = L x := by
    intro x
    change eA (P.E.map incS (φS.symm (φS _))) = L x
    rw [φS.symm_apply_apply, P.E.realize_along, SupportTerm.along_pullback,
      realize_supportTermOf, eA.apply_symm_apply]
  have hLμ : #(seq.κIndex × q.idx) < μ := seq.concat_bounded
  have hD : SingleModelData.DiagramEq (P := P) hμ hμ A Astar L Lstar := by
    have h := SingleModelData.diagramEq_of_strong (P := P) hμ hμ Astar A ιmap hιmap Lstar
      hLμ hLμ
    have heq : (fun i => ιmap (Lstar i)) = L := funext hιL
    rw [heq] at h
    exact h.symm
  obtain ⟨eψ, heψ⟩ :=
    (SingleModelData.diagramEq_iff_equiv (P := P) hμ A Astar L Lstar hLμ).mp hD
  let gEmb : Language.Embedding K.τ A.model.carrier A.model.carrier :=
    ιmap.comp eψ.toEmbedding
  have hgEmb : K.Strong gEmb := K.strong_trans _ _ (strong_of_equiv K eψ A.mem) hιmap
  let g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ A) (P.scheme.asSystem hμ A) :=
    oneVertexArrow gEmb hgEmb
  refine ⟨g, trivial, ?_, ?_⟩
  · intro i j
    have h1 : gEmb (L (i, j)) = L (i, j) := by
      change ιmap (eψ (L (i, j))) = L (i, j)
      rw [heψ, hιL]
    exact congrArg (fun a => (⟨(seq.family i j).1, a⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ A))) h1
  · -- the restrictions to `A*` agree on every test
    by_contra hneq
    obtain ⟨β, Y, hβ, hnot⟩ := infra_73_differing_test P σ hσ hμ hrec hσSucc
      (q.restrict g trivial) (q'.restrict g trivial) e e' hqν hq'ν hidx hidxμ hneq
    apply hnot
    have hβχ0 : #β ≤ χ0 := hβ.trans hgχ0
    have hβχ : #β ≤ χ := hβ.trans hgχ.le
    let w : β → (P.E.obj S).carrier := fun j => φS.symm (eψ (A.val (Y j)))
    let sT : β → SupportTerm P.E.lab P.E.arity (Bk ×ₗ M) :=
      fun j => SupportTerm.along incS (supportTermOf P.E (w j))
    let T : Set (Bk ×ₗ M) := ⋃ j, termSupport (sT j)
    have hsT : ∀ j k, (sT j).pos k ∈ T := fun j k => Set.mem_iUnion.mpr ⟨j, k, rfl⟩
    have hTS : ∀ x ∈ T, x ∈ S := by
      intro x hx
      obtain ⟨j, k, rfl⟩ := Set.mem_iUnion.mp hx
      exact ((supportTermOf P.E (w j)).pos k).2
    have hT : #T ≤ χ0 :=
      (infra_73_card_iUnion_countable _ (fun j => infra_73_card_termSupport _)).trans
        ((mul_le_mul' hβχ0 hχ0inf).trans (mul_eq_self hχ0inf).le)
    let Tb : Set M := {m | toLex (b, m) ∈ T}
    have hTb : #Tb ≤ χ0 := by
      refine (mk_le_of_injective (f := fun m : Tb => (⟨toLex (b, m.1), m.2⟩ : T)) ?_).trans hT
      intro m m' hmm
      apply Subtype.ext
      have h := congrArg (fun x : T => (ofLex x.1).2) hmm
      exact h
    let emb : Tb ↪o (Order.succ χ0).ord.ToType :=
      Classical.choice (infra_73_reservoir χ0 Tb hTb)
    let mv := infra_73_mv b ρres T emb
    have hmono : StrictMonoOn mv T := infra_73_mv_strictMonoOn b ρres T emb
    have hout : ∀ x ∈ T, (ofLex x).1 ≠ b → mv x = x :=
      fun x _ hx => infra_73_mv_out b ρres T emb x hx
    have hin : ∀ x ∈ T, (ofLex x).1 = b → (ofLex (mv x)).1 = b :=
      fun x hx hb => (infra_73_mv_in b ρres T emb x hx hb).1
    let mT : β → SupportTerm P.E.lab P.E.arity (Bk ×ₗ M) :=
      fun j => infra_73_moveTerm mv T hmono (sT j) (hsT j)
    have hmJ0 : ∀ j, termSupport (mT j) ⊆ J0 := by
      rintro j _ ⟨k, rfl⟩
      have hx := hsT j k
      by_cases hxb : (ofLex ((sT j).pos k)).1 = b
      · exact Or.inr (infra_73_mv_in b ρres T emb _ hx hxb).2
      · change mv ((sT j).pos k) ∈ J0
        rw [hout _ hx hxb]
        rcases hTS _ hx with h | h
        · exact h
        · exact absurd h hxb
    let κm : β → ιZ := fun j => ⟨mT j, hmJ0 j⟩
    have a0 := infra_73_moved_answer P hμ q hqν hI eA hσ hidx hσlt hχμ hls Q0 hQ0 b clean0
      mv T hmono hout hin hβχ sT hsT
    have a1 := infra_73_moved_answer P hμ q' hq'ν hI eA hσ hidx' hσlt hχμ hls Q1 hQ1 b clean1
      mv T hmono hout hin hβχ sT hsT
    let Y' : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
      fun j => A.occ (eA (P.E.realize (sT j)))
    let Ym : β → Occurrence K oneVertexShape (P.scheme.asSystem hμ A) :=
      fun j => A.occ (eA (P.E.realize (mT j)))
    have hZ : P.scheme.DiagramEq (X := q.host) (Y := q'.host)
        (alignJoint e (typeJoint (p := q) Ym)) (alignJoint e' (typeJoint (p := q') Ym)) :=
      infra_73_diagramEq_of_eq (infra_73_scheme_comp hDE (Sum.map id κm))
        (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    have al0 : P.scheme.DiagramEq (X := q.host) (Y := q.host)
        (alignJoint e (typeJoint (p := q) Y')) (alignJoint e (typeJoint (p := q) Ym)) :=
      infra_73_diagramEq_of_eq (infra_73_scheme_comp a0 (Sum.map e.symm id))
        (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    have al1 : P.scheme.DiagramEq (X := q'.host) (Y := q'.host)
        (alignJoint e' (typeJoint (p := q') Y')) (alignJoint e' (typeJoint (p := q') Ym)) :=
      infra_73_diagramEq_of_eq (infra_73_scheme_comp a1 (Sum.map e'.symm id))
        (fun t => by cases t <;> rfl) (fun t => by cases t <;> rfl)
    have hY : ∀ j, g.onVertex (Y j).1 (Y j).2 = eA (P.E.realize (sT j)) := by
      intro j
      change ιmap (eψ (Y j).2) = eA (P.E.realize (SupportTerm.along incS _))
      rw [← P.E.realize_along, realize_supportTermOf]
      rfl
    have c1 := P.scheme.diagram_trans q.host q.host q'.host _ _ _ al0 hZ
    have c2 := P.scheme.diagram_trans q.host q'.host q'.host _ _ _ c1
      (P.scheme.diagram_symm q'.host q'.host _ _ al1)
    refine infra_73_diagramEq_of_eq c2 ?_ ?_
    · intro t
      cases t with
      | inl i => rfl
      | inr j =>
        change (⟨PUnit.unit, q.incl.onVertex PUnit.unit (eA (P.E.realize (sT j)))⟩ :
            Occurrence K oneVertexShape (P.scheme.asSystem q.hν q.host)) =
          ⟨(Y j).1, q.incl.onVertex (Y j).1 (g.onVertex (Y j).1 (Y j).2)⟩
        rw [hY j]
        rfl
    · intro t
      cases t with
      | inl i => rfl
      | inr j =>
        change (⟨PUnit.unit, q'.incl.onVertex PUnit.unit (eA (P.E.realize (sT j)))⟩ :
            Occurrence K oneVertexShape (P.scheme.asSystem q'.hν q'.host)) =
          ⟨(Y j).1, q'.incl.onVertex (Y j).1 (g.onVertex (Y j).1 (Y j).2)⟩
        rw [hY j]
        rfl

/-- **English Proposition 7.3 (uniform form).** For `σ ≥ ℵ₀` there are `h(σ)` and a tail of
levels such that every relatively isolated `q` with `#idx ≤ σ` has an isolating fragment of
size at most `h(σ)`. -/
theorem proposition_7_3_uniform (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ) :
    ∃ h : Cardinal.{u} → Cardinal.{u}, ∃ T, ∃ hT : Tail P.eligible T,
      ∀ μ (hμ : μ ∈ T) (A : P.scheme.Object μ (Tail.mem hT hμ))
        (q : TupleOver K oneVertexShape P.scheme (Tail.mem hT hμ) A)
        {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx),
        q.ν = μ → #q.idx ≤ σ → #q.idx < μ → IsRelativelyIsolated q e →
        ∃ (ι : Type u)
          (Z : ι → Occurrence K oneVertexShape (P.scheme.asSystem (Tail.mem hT hμ) A)),
          #ι ≤ h σ ∧ IsIsolatingFragment q e Z :=
  proposition_7_3_uniform_of_block P σ hσ (infra_73_block_restriction P σ hσ)

/-- **Prop 7.3 dichotomy with tied marginal (proved).** At a tail level, a tuple `q` with
`#idx ≤ σ` either has an isolating fragment of size at most `h(σ)`, or has a same-level
extension whose `u`-marginal is the tied free extension while the joint is not tied free
(block restriction, competitor, `infra_73_alt2_tied`). Unlike `proposition_7_3`, the marginal
clause is `IsTiedFree`, not the vacuous untied `IsFreeLift`. -/
theorem infra_78_tied_dichotomy (P : SingleModelData K) (σ : Cardinal.{u}) (hσ : ℵ₀ ≤ σ)
    {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ)
    {A : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)}
    (q : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) A)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ) :
    (∃ (ι : Type u)
        (Z : ι → Occurrence K oneVertexShape
          (P.scheme.asSystem (Tail.mem (infra_73_tail P σ hσ) hμT) A)),
        #ι ≤ infra_73_h P σ ∧ IsIsolatingFragment q e Z) ∨
      (∃ (B : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
        (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
        (hf : P.scheme.permitted (X := A) (Y := B) f)
        (qB : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) B)
        (eB : q.idx ≃ qB.idx),
        qB.ν = μ ∧
        SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) ∧
        IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e)) (Equiv.refl uIdx) ∧
        ¬ IsTiedFree f q qB eB) := by
  have hμel : μ ∈ P.eligible := Tail.mem (infra_73_tail P σ hσ) hμT
  have hrec : μ ∈ recursionClosedLevels P σ := infra_73_tail_rec hμT
  have hσSucc : Order.succ σ ≤ μ := infra_73_tail_succ hμT
  obtain ⟨seq, hτge, hlong, ι, Z, hι, hZ⟩ :=
    infra_73_block_restriction P σ hσ μ hμT A q e hqν hidx
  have hιμ : #ι < μ := hι.trans_lt (infra_73_h_lt hμel hμT)
  by_cases hFrag : IsIsolatingFragment q e Z
  · exact Or.inl ⟨ι, Z, hι, hFrag⟩
  · obtain ⟨q', e', hq'ν, hMarg, hDE, hneq⟩ := infra_73_competitor q e Z hιμ hFrag
    obtain ⟨g, hg, hfix, hres⟩ := hZ q' e' hq'ν hMarg hDE
    exact Or.inr (infra_73_alt2_tied P σ hσ hμel hrec hσSucc q e hqν hidx seq hτge hlong q' e'
      hq'ν hMarg hneq g hg hfix hres)

/-- **Tied nonfree extension at a failing stage (Prop 7.8 matrix step; proved).** If `q`
(at a tail level, `#idx ≤ σ`) is not relatively isolated over its `u`-part, there is a
same-level extension `A → B` and `qB` over `B` extending `q`, at level `μ`, whose
`u`-marginal is tied free from `A` while `qB` is not tied free from `A`. -/
theorem infra_78_nonfree_extension_tied (P : SingleModelData K) (σ : Cardinal.{u})
    (hσ : ℵ₀ ≤ σ) {μ : Cardinal.{u}} (hμT : μ ∈ infra_73_tailSet P σ)
    {A : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT)}
    (q : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) A)
    {uIdx cIdx : Type u} (e : q.idx ≃ uIdx ⊕ cIdx)
    (hqν : q.ν = μ) (hidx : #q.idx ≤ σ) (hnot : ¬ IsRelativelyIsolated q e) :
    ∃ (B : P.scheme.Object μ (Tail.mem (infra_73_tail P σ hσ) hμT))
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem _ A) (P.scheme.asSystem _ B))
      (hf : P.scheme.permitted (X := A) (Y := B) f)
      (qB : TupleOver K oneVertexShape P.scheme (Tail.mem (infra_73_tail P σ hσ) hμT) B)
      (eB : q.idx ≃ qB.idx),
      qB.ν = μ ∧
      SameGaloisType q (qB.restrict f hf) eB (Equiv.refl qB.idx) ∧
      IsTiedFree f (q.marginal e) (qB.marginal (eB.symm.trans e)) (Equiv.refl uIdx) ∧
      ¬ IsTiedFree f q qB eB := by
  rcases infra_78_tied_dichotomy P σ hσ hμT q e hqν hidx with ⟨_, _, _, hF⟩ | h
  · exact absurd (IsRelativelyIsolated.of_fragment hF) hnot
  · exact h

end Main

end
end
end AEC
