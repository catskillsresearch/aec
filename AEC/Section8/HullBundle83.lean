module

public import AEC.Section8.HullReduct83

/-!
# Lemma 8.3: finite pieces from bundled samples

The bundled version of `tpFinPieces`: witnesses of the coherent bundled types
(`tpB_coherent_colors`), their term hulls, and the hull maps along `Prod.map e id` form a
`FinPieces K` when the admitted class has vertex LS witnesses.
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {K : AbstractElementaryClass.{u}} {L : Language.{u, u}}

/-- A realization of a bundled type by bundles with injective sort sequences. -/
structure TpWitB (P : ∀ (M : Type u) [L.Structure M], Prop) {r m : ℕ} (c : TpColorB L r m) where
  M : Type u
  str : L.Structure M
  mem : @P M str
  v : Fin m × Fin r → M
  inj : ∀ i, Function.Injective fun a => v (a, i)
  tp : tpCode v = c

attribute [instance] TpWitB.str

section Pieces

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
  {c : (m : ℕ) → 0 < m → TpColorB L r m}

theorem tpWitB_nonempty (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
    {m : ℕ} (hm : 0 < m) : Nonempty (TpWitB P (c m hm)) := by
  obtain ⟨S, ⟨M, inst, hP, base, hinj, hcol⟩, hκ, hhom⟩ := hc m (m : Cardinal.{u})
  obtain ⟨s, hs⟩ : ∃ s : Finset S.α, s.card = m := by
    obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hκ
    have hfin : t.Finite :=
      Cardinal.lt_aleph0_iff_set_finite.mp (by rw [ht]; exact Cardinal.natCast_lt_aleph0)
    refine ⟨hfin.toFinset, ?_⟩
    have h1 : #(↥(hfin.toFinset : Set S.α)) = (hfin.toFinset.card : Cardinal) :=
      Cardinal.mk_coe_finset
    rw [Set.Finite.coe_toFinset, ht] at h1
    exact_mod_cast h1.symm
  refine ⟨⟨M, inst, hP, bundleOf base s hs, fun i => (hinj i).comp (s.orderEmbOfFin hs).injective,
    ?_⟩⟩
  rw [← hcol m s hs]
  exact hhom m hm le_rfl s hs

/-- The chosen bundled witness at arity `k + 1`. -/
noncomputable def witB (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
    (k : ℕ) : TpWitB P (c (k + 1) (Nat.succ_pos k)) :=
  Classical.choice (tpWitB_nonempty hc (Nat.succ_pos k))

variable (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpResB r f (c m hm))

include hcoh in
theorem tpPieceB_tp {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) :
    tpCode (L := L) (witB hc k).v = tpCode ((witB hc l).v ∘ Prod.map e id) := by
  calc tpCode (L := L) (witB hc k).v = c (k + 1) (Nat.succ_pos k) := (witB hc k).tp
    _ = tpResB r e (c (l + 1) (Nat.succ_pos l)) := hcoh (Nat.succ_pos k) (Nat.succ_pos l) e
    _ = tpResB r e (tpCode (L := L) (witB hc l).v) := by rw [(witB hc l).tp]
    _ = tpCode ((witB hc l).v ∘ Prod.map e id) := tpResB_tpCode e _

variable (φ : K.τ →ᴸ L)

include hcoh in
/-- **The finite pieces of `K` from bundled samples.** -/
noncomputable def tpFinPiecesB (hP : HullStrong φ P) : EM83.FinPieces K where
  obj k := red φ (Hull (L := L) (witB hc k).v)
  mem k := K.strong_mem_dom _ (hP _ (witB hc k).mem (witB hc k).v)
  map e := redEmb φ (hullMapEmb (Prod.map e id) (tpPieceB_tp hc hcoh e))
  map_refl k := by
    ext x
    exact hullMap_id _ (tpPieceB_tp hc hcoh (k := k) (l := k) idEmb) x
  map_trans e f := by
    ext x
    exact (hullMap_comp (Prod.map e id) (Prod.map f id) (tpPieceB_tp hc hcoh e)
      (tpPieceB_tp hc hcoh f) (tpPieceB_tp hc hcoh (e.trans f)) x).symm
  strong e := hullMap_strong hP (witB hc _).mem (witB hc _).mem _ (tpPieceB_tp hc hcoh e)

/-- **Template pieces from bundled samples exist.** -/
theorem exists_tpFinPiecesB (hP : HullStrong φ P)
    (hlarge : ∀ κ : Cardinal.{u}, ∃ (α : Type u) (_ : LinearOrder α) (M : Type u)
      (_ : L.Structure M), P M ∧ κ ≤ #α ∧
      ∃ base : α → Fin r → M, ∀ i, Function.Injective fun a => base a i) :
    ∃ (c : (m : ℕ) → 0 < m → TpColorB L r m) (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Joint (TpSampleB P r) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = tpResB r f (c m hm)),
      ∀ k, (tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP).obj k = red φ (Hull (L := L) (witB hc k).v) := by
  obtain ⟨c, hc, hcoh⟩ := tpB_coherent_colors hlarge
  exact ⟨c, hc, hcoh, fun k => rfl⟩

end Pieces

/-- Bundled terms are few when the function symbols are. -/
theorem card_bundle_terms_le (r : ℕ) (hL : max ℵ₀ #(Σ i, L.Functions i) ≤ ls K) :
    #(Σ n, L.Term (Fin n × Fin r)) ≤ ls K := by
  have hω : ℵ₀ ≤ ls K := le_trans (le_max_left _ _) hL
  let f : (Σ n, L.Term (Fin n × Fin r)) → ℕ × (Σ k, L.Term (Fin k)) := fun a =>
    (a.1, ⟨a.1 * r, Term.relabelEquiv finProdFinEquiv a.2⟩)
  have hf : Function.Injective f := by
    rintro ⟨n, t⟩ ⟨n', t'⟩ h
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have := eq_of_heq (Sigma.mk.inj_iff.mp h2).2
    rw [(Term.relabelEquiv finProdFinEquiv).injective this]
  calc #(Σ n, L.Term (Fin n × Fin r)) ≤ #(ℕ × (Σ k, L.Term (Fin k))) := mk_le_of_injective hf
    _ = ℵ₀ * #(Σ k, L.Term (Fin k)) := by rw [mk_prod, mk_nat]; simp
    _ ≤ ls K * ls K := mul_le_mul' hω (card_terms_le hL)
    _ = ls K := mul_eq_self hω

section Enum

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
  {c : (m : ℕ) → 0 < m → TpColorB L r m}
  (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpResB r f (c m hm))
  (hr : 0 < r)

/-- The term enumeration of the bundled hull pieces. -/
noncomputable def tpEnumB (k : ℕ) (a : Σ n, L.Term (Fin n × Fin r)) :
    Hull (L := L) (witB hc k).v :=
  if h : a.1 = k + 1 then Quotient.mk _ (a.2.relabel (Prod.map (Fin.cast h) id))
  else Quotient.mk _ (Term.var (0, ⟨0, hr⟩))

theorem tpEnumB_surj (k : ℕ) : Function.Surjective (tpEnumB hc hr k) := by
  intro x
  induction x using Quotient.ind with
  | _ t =>
    refine ⟨⟨k + 1, t⟩, ?_⟩
    simp only [tpEnumB, dite_true]
    congr 1
    have : (Prod.map (Fin.cast (rfl : k + 1 = k + 1)) id : Fin (k + 1) × Fin r → _) = id := by
      funext p; rfl
    rw [this]
    exact Term.relabel_id t

include hcoh in
/-- **Enumeration data** for the bundled hull pieces (skeleton: the first entry of the first
bundle), so the generic EM presentation applies. -/
noncomputable def tpPieceEnumB (φ : K.τ →ᴸ L) (hP : HullStrong φ P)
    (hL : max ℵ₀ #(Σ i, L.Functions i) ≤ ls K) :
    EM83.PieceEnum (tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP) where
  Lab := Σ n, L.Term (Fin n × Fin r)
  lab_small := card_bundle_terms_le r hL
  enum k := tpEnumB hc hr k
  surj k := tpEnumB_surj hc hr k
  skelLab := ⟨1, Term.var (0, ⟨0, hr⟩)⟩
  skel_distinct {l} e e' hne heq := by
    have h2 : hullVal (witB hc l).v (hullMap (L := L) (Prod.map (⇑e) id) (tpPieceB_tp hc hcoh e)
        (Quotient.mk _ ((Term.var (0, ⟨0, hr⟩) : L.Term (Fin 1 × Fin r)).relabel
          (Prod.map (Fin.cast rfl) id)))) =
        hullVal (witB hc l).v (hullMap (L := L) (Prod.map (⇑e') id) (tpPieceB_tp hc hcoh e')
        (Quotient.mk _ ((Term.var (0, ⟨0, hr⟩) : L.Term (Fin 1 × Fin r)).relabel
          (Prod.map (Fin.cast rfl) id)))) :=
      congrArg (hullVal (L := L) (witB hc l).v) heq
    rw [hullMap_mk, hullMap_mk, hullVal_mk, hullVal_mk] at h2
    simp only [Term.realize_relabel, Term.realize_var, Function.comp_apply, Prod.map] at h2
    exact hne (by simpa using (witB hc l).inj ⟨0, hr⟩ h2)

include hcoh in
/-- The EM order presentation of the bundled hull pieces. -/
noncomputable def tpPresentationB (φ : K.τ →ᴸ L) (hP : HullStrong φ P)
    (hL : max ℵ₀ #(Σ i, L.Functions i) ≤ ls K) : OrderPresentation K :=
  EM83.presentation (tpPieceEnumB hc hcoh hr φ hP hL)

end Enum

/-- Equal types stay equal after relabelling the variables. -/
theorem tpCode_comp {M N : Type u} [L.Structure M] [L.Structure N] {ι ι' : Type}
    {v : ι → M} {w : ι → N} (h : tpCode (L := L) v = tpCode w) (g : ι' → ι) :
    tpCode (L := L) (v ∘ g) = tpCode (w ∘ g) := by
  ext θ
  have := congrArg (fun c : Set (L.Formula ι) => θ.relabel g ∈ c) h
  simp only [tpCode, Set.mem_setOf_eq, Formula.realize_relabel] at this
  exact Iff.of_eq this

section SubBundle

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
  {c : (m : ℕ) → 0 < m → TpColorB L r m}
  (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpResB r f (c m hm))
  {r₀ : ℕ} (σ : Fin r₀ → Fin r) (φ : K.τ →ᴸ L)

include hcoh in
theorem subBundle_tp {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) :
    tpCode (L := L) ((witB hc k).v ∘ Prod.map id σ) =
      tpCode (((witB hc l).v ∘ Prod.map id σ) ∘ Prod.map e id) :=
  tpCode_comp (tpPieceB_tp hc hcoh e) (Prod.map id σ)

include hcoh in
/-- **Sub-bundle pieces**: the hulls of the selected sort coordinates `σ` of each bundle
(e.g. the `J`-coordinates, giving `X_H = F(J_H)`). -/
noncomputable def subBundlePieces (hP : HullStrong φ P) : EM83.FinPieces K where
  obj k := red φ (Hull (L := L) ((witB hc k).v ∘ Prod.map id σ))
  mem k := K.strong_mem_dom _ (hP _ (witB hc k).mem ((witB hc k).v ∘ Prod.map id σ))
  map e := redEmb φ (hullMapEmb (Prod.map e id) (subBundle_tp hc hcoh σ e))
  map_refl k := by
    ext x
    exact hullMap_id _ (subBundle_tp hc hcoh σ (k := k) (l := k) idEmb) x
  map_trans e f := by
    ext x
    exact (hullMap_comp (Prod.map e id) (Prod.map f id) (subBundle_tp hc hcoh σ e)
      (subBundle_tp hc hcoh σ f) (subBundle_tp hc hcoh σ (e.trans f)) x).symm
  strong e := hullMap_strong hP (witB hc _).mem (witB hc _).mem _ (subBundle_tp hc hcoh σ e)

include hcoh in
/-- **Sub-bundle inclusion** into the full bundled pieces: strong and natural. -/
noncomputable def subBundleHom (hP : HullStrong φ P) :
    EM83.PiecesHom (subBundlePieces hc hcoh σ φ hP) (tpFinPiecesB (hc := hc) (hcoh := hcoh) (φ := φ) hP) where
  app k := redEmb φ (hullMapEmb (v' := (witB hc k).v ∘ Prod.map id σ) (Prod.map id σ) rfl)
  strong k := hullMap_strong hP (witB hc k).mem (witB hc k).mem _ rfl
  natural {k l} e := by
    ext x
    exact (hullMap_comp (Prod.map e id) (Prod.map id σ) (subBundle_tp hc hcoh σ e) rfl
        (subBundle_tp hc hcoh σ e)
        (show Hull (L := L) ((witB hc k).v ∘ Prod.map id σ) from x)).trans
      (hullMap_comp (Prod.map id σ) (Prod.map e id) rfl (tpPieceB_tp hc hcoh e)
        (subBundle_tp hc hcoh σ e)
        (show Hull (L := L) ((witB hc k).v ∘ Prod.map id σ) from x)).symm

end SubBundle


section InSample

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {r : ℕ}
  {c : (m : ℕ) → 0 < m → TpColorB L r m}
  (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSampleB P r) n c κ)

/-- **Pieces live in every homogeneous sample.**  In an admitted bundled sample homogeneous
through arity `n`, each piece of arity `k + 1 ≤ n` embeds (as an `L`-structure) into the
sample structure, sending each variable to the corresponding entry of the bundles
enumerated by any `k + 1` indices.  Thus term equalities and relations of the template are
those of actual homogeneous samples. -/
theorem piece_into_sample {S : ColorSample (TpColorB L r)} {M : Type u} [L.Structure M]
    (base : S.α → Fin r → M)
    (hcol : ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m), S.col m s = tpCode (bundleOf base s h))
    {n : ℕ} (hhom : Homog S n c) {k : ℕ} (hk : k + 1 ≤ n) (s : Finset S.α)
    (hs : s.card = k + 1) :
    ∃ f : Hull (L := L) (witB hc k).v ↪[L] M,
      ∀ p, f (Quotient.mk _ (Term.var p)) = bundleOf base s hs p := by
  have htp : tpCode (L := L) (witB hc k).v = tpCode (bundleOf base s hs ∘ id) := by
    rw [(witB hc k).tp, ← hhom (k + 1) (Nat.succ_pos k) hk s hs, hcol (k + 1) s hs]
    rfl
  refine ⟨(hullEmb (bundleOf base s hs)).comp (hullMapEmb id htp), ?_⟩
  intro p
  rfl

end InSample

end Hull83

namespace EM83

open FirstOrder

variable {F G H : FinPieces K}

/-- Composition of piece transformations (the sort chain `X → Y → L`). -/
noncomputable def PiecesHom.comp (η' : PiecesHom G H) (η : PiecesHom F G) : PiecesHom F H where
  app k := (η'.app k).comp (η.app k)
  strong k := K.strong_trans _ _ (η.strong k) (η'.strong k)
  natural {k l} e := by
    ext x
    have h1 := congrFun (congrArg (⇑) (η.natural e)) x
    have h2 := congrFun (congrArg (⇑) (η'.natural e)) (η.app k x)
    simp only [Language.Embedding.comp_apply] at h1 h2 ⊢
    rw [h1, h2]

/-- The induced map of a composite is the composite of the induced maps. -/
theorem PiecesHom.limMap_comp (η' : PiecesHom G H) (η : PiecesHom F G) (I : Type u)
    [LinearOrder I] [Nonempty I] :
    (η'.comp η).limMap I = (η'.limMap I).comp (η.limMap I) := by
  ext x
  obtain ⟨s, y, rfl⟩ := (F.limit I).joint x
  have h1 := congrFun (congrArg (⇑) ((η'.comp η).limMap_canon I s)) y
  have h2 := congrFun (congrArg (⇑) (η.limMap_canon I s)) y
  have h3 := congrFun (congrArg (⇑) (η'.limMap_canon I s)) (η.app s.1.card.pred y)
  simp only [Language.Embedding.comp_apply, PiecesHom.cocone] at h1 h2 h3 ⊢
  rw [h1, h2]
  erw [h3]
  rfl

end EM83

end AEC
