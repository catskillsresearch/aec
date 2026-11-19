module

public import AEC.Section8.HullTypes83

/-!
# Lemma 8.3: term hulls of tuples and the pieces read off coherent types

The term hull of a tuple `v : Fin m → M` in an `L`-structure is presented as `L`-terms in `m`
variables modulo equality of their values at `v` (`Hull v`), with its embedding into `M`
(`hullEmb`).  Two tuples of the same type have isomorphic hulls, and more generally a map of
positions `g` with `tp(v') = tp(v ∘ g)` induces an `L`-embedding of hulls `hullMap`
(relabelling terms along `g`), functorially.  Instantiated with witnesses of coherent type
colors (`tp_coherent_colors`), this gives the finite pieces of the template at the level of
the expanded language: an `L`-structure for each positive arity and `L`-embeddings along
increasing maps of positions, each piece embedded in an actual homogeneous sample.
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {L : Language.{u, u}}

section HullDef

variable {M : Type u} [L.Structure M] {ι : Type}

/-- Terms identified when they have the same value at `v`. -/
def hullSetoid (v : ι → M) : Setoid (L.Term ι) :=
  Setoid.ker (fun t => t.realize v)

/-- The term hull of `v`, presented by terms. -/
abbrev Hull (v : ι → M) : Type u := Quotient (hullSetoid (L := L) v)

noncomputable instance hullStructure (v : ι → M) : L.Structure (Hull (L := L) v) where
  funMap f xs := Quotient.mk _ (Term.func f (fun i => (xs i).out))
  RelMap r xs := Structure.RelMap r (fun i => (xs i).out.realize v)

/-- The value of a hull element in `M`. -/
def hullVal (v : ι → M) : Hull (L := L) v → M :=
  Quotient.lift (fun t => t.realize v) (fun _ _ h => h)

theorem hullVal_mk (v : ι → M) (t : L.Term ι) :
    hullVal v (Quotient.mk (hullSetoid v) t) = t.realize v := rfl

theorem hullVal_out (v : ι → M) (x : Hull (L := L) v) :
    hullVal v x = x.out.realize v := by
  conv_lhs => rw [← Quotient.out_eq x]
  rfl

theorem hullVal_injective (v : ι → M) : Function.Injective (hullVal (L := L) v) := by
  intro x y h
  induction x using Quotient.ind
  induction y using Quotient.ind
  exact Quotient.sound h

/-- The hull embeds in `M`. -/
noncomputable def hullEmb (v : ι → M) : Hull (L := L) v ↪[L] M where
  toFun := hullVal v
  inj' := hullVal_injective v
  map_fun' {n} f xs := by
    show (Term.func f (fun i => (xs i).out)).realize v = _
    simp only [Term.realize, Function.comp_def, hullVal_out]
  map_rel' {n} r xs := by
    show Structure.RelMap r (fun i => hullVal v (xs i)) ↔
      Structure.RelMap r (fun i => (xs i).out.realize v)
    simp only [hullVal_out]

theorem hullEmb_apply (v : ι → M) (x : Hull (L := L) v) : hullEmb v x = hullVal v x := rfl

end HullDef

/-- Tuples of the same type satisfy the same term equations. -/
theorem term_eq_iff_of_tp {M N : Type u} [L.Structure M] [L.Structure N] {ι : Type}
    {v : ι → M} {w : ι → N} (h : tpCode (L := L) v = tpCode w) (t t' : L.Term ι) :
    t.realize v = t'.realize v ↔ t.realize w = t'.realize w := by
  have := congrArg (fun c : Set (L.Formula ι) => (Term.equal t t' : L.Formula ι) ∈ c) h
  simp only [tpCode, Set.mem_setOf_eq, Formula.realize_equal] at this
  exact Iff.of_eq this

/-- Tuples of the same type satisfy the same atomic relations on terms. -/
theorem rel_iff_of_tp {M N : Type u} [L.Structure M] [L.Structure N] {ι : Type}
    {v : ι → M} {w : ι → N} (h : tpCode (L := L) v = tpCode w) {n : ℕ}
    (r : L.Relations n) (ts : Fin n → L.Term ι) :
    Structure.RelMap r (fun i => (ts i).realize v) ↔
      Structure.RelMap r (fun i => (ts i).realize w) := by
  have := congrArg (fun c : Set (L.Formula ι) => (r.formula ts : L.Formula ι) ∈ c) h
  simp only [tpCode, Set.mem_setOf_eq, Formula.realize_rel] at this
  exact Iff.of_eq this

section HullMap

variable {M N : Type u} [L.Structure M] [L.Structure N] {ι ι' : Type}

/-- The map of hulls along a map of positions `g` with `tp(v') = tp(v ∘ g)`. -/
def hullMap {v' : ι' → N} {v : ι → M} (g : ι' → ι)
    (h : tpCode (L := L) v' = tpCode (v ∘ g)) : Hull (L := L) v' → Hull (L := L) v :=
  Quotient.map (fun t => t.relabel g) (fun t t' (htt : t.realize v' = t'.realize v') => by
    show (t.relabel g).realize v = (t'.relabel g).realize v
    rw [Term.realize_relabel, Term.realize_relabel]
    exact (term_eq_iff_of_tp h t t').mp htt)

theorem hullVal_hullMap {v' : ι' → N} {v : ι → M} (g : ι' → ι)
    (h : tpCode (L := L) v' = tpCode (v ∘ g)) (x : Hull (L := L) v') :
    hullVal v (hullMap g h x) = x.out.realize (v ∘ g) := by
  conv_lhs => rw [← Quotient.out_eq x]
  show (x.out.relabel g).realize v = _
  rw [Term.realize_relabel]

theorem realize_out_mk {v' : ι' → N} {v : ι → M} (g : ι' → ι)
    (h : tpCode (L := L) v' = tpCode (v ∘ g)) (t : L.Term ι') :
    (Quotient.mk (hullSetoid v') t).out.realize (v ∘ g) = t.realize (v ∘ g) :=
  (term_eq_iff_of_tp h _ _).mp (Quotient.mk_out (s := hullSetoid v') t)

/-- The hull map is an `L`-embedding. -/
noncomputable def hullMapEmb {v' : ι' → N} {v : ι → M} (g : ι' → ι)
    (h : tpCode (L := L) v' = tpCode (v ∘ g)) : Hull (L := L) v' ↪[L] Hull (L := L) v where
  toFun := hullMap g h
  inj' := by
    intro x y hxy
    have h1 := congrArg (hullVal v) hxy
    rw [hullVal_hullMap, hullVal_hullMap] at h1
    apply hullVal_injective v'
    rw [hullVal_out, hullVal_out]
    exact (term_eq_iff_of_tp h _ _).mpr h1
  map_fun' {n} f xs := by
    apply hullVal_injective v
    rw [hullVal_hullMap]
    rw [show hullVal v (Structure.funMap f (hullMap g h ∘ xs)) =
      hullEmb v (Structure.funMap f (hullMap g h ∘ xs)) from rfl, (hullEmb v).map_fun]
    simp only [Function.comp_def, hullEmb_apply, hullVal_hullMap]
    show (Quotient.mk (hullSetoid v') (Term.func f (fun i => (xs i).out))).out.realize (v ∘ g) = _
    rw [realize_out_mk g h]
    simp only [Term.realize]
    rfl
  map_rel' {n} r xs := by
    rw [← (hullEmb v).map_rel]
    show Structure.RelMap r (fun i => hullVal v (hullMap g h (xs i))) ↔
      Structure.RelMap r (fun i => (xs i).out.realize v')
    simp only [hullVal_hullMap]
    exact (rel_iff_of_tp h r (fun i => (xs i).out)).symm

theorem hullMapEmb_apply {v' : ι' → N} {v : ι → M} (g : ι' → ι)
    (h : tpCode (L := L) v' = tpCode (v ∘ g)) (x : Hull (L := L) v') :
    hullMapEmb g h x = hullMap g h x := rfl

/-- The hull map along the identity is the identity. -/
theorem hullMap_id (v : ι → M) (h : tpCode (L := L) v = tpCode (v ∘ id))
    (x : Hull (L := L) v) : hullMap id h x = x := by
  apply hullVal_injective v
  rw [hullVal_hullMap, hullVal_out]
  rfl

/-- Hull maps compose. -/
theorem hullMap_comp {P : Type u} [L.Structure P] {ι'' : Type} {v'' : ι'' → P}
    {v' : ι' → N} {v : ι → M} (g' : ι'' → ι') (g : ι' → ι)
    (h' : tpCode (L := L) v'' = tpCode (v' ∘ g')) (h : tpCode (L := L) v' = tpCode (v ∘ g))
    (h'' : tpCode (L := L) v'' = tpCode (v ∘ (g ∘ g'))) (x : Hull (L := L) v'') :
    hullMap g h (hullMap g' h' x) = hullMap (g ∘ g') h'' x := by
  apply hullVal_injective v
  rw [hullVal_hullMap, hullVal_hullMap]
  have h1 : (hullMap g' h' x).out.realize v' = (x.out.relabel g').realize v' := by
    rw [← hullVal_out, hullVal_hullMap, Term.realize_relabel]
  rw [(term_eq_iff_of_tp h _ _).mp h1, Term.realize_relabel]
  rfl

end HullMap

/-- **Witnesses of the coherent types.**  Every extracted type is realized by an injective
tuple in an admitted structure. -/
theorem tp_witness {P : ∀ (M : Type u) [L.Structure M], Prop}
    {c : (m : ℕ) → 0 < m → TpColor L m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSample P) n c κ) {m : ℕ} (hm : 0 < m) :
    ∃ (M : Type u) (_ : L.Structure M), P M ∧ ∃ v : Fin m → M, Function.Injective v ∧
      tpCode v = c m hm := by
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
  refine ⟨M, inst, hP, fun i => base (s.orderEmbOfFin hs i),
    hinj.comp (s.orderEmbOfFin hs).injective, ?_⟩
  rw [← hcol m s hs]
  exact hhom m hm le_rfl s hs

/-- A realization of a type by an injective tuple in an admitted structure. -/
structure TpWit (P : ∀ (M : Type u) [L.Structure M], Prop) {m : ℕ} (c : TpColor L m) where
  M : Type u
  str : L.Structure M
  mem : @P M str
  v : Fin m → M
  inj : Function.Injective v
  tp : tpCode v = c

attribute [instance] TpWit.str

section Pieces

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {c : (m : ℕ) → 0 < m → TpColor L m}

theorem tpWit_nonempty (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSample P) n c κ)
    {m : ℕ} (hm : 0 < m) : Nonempty (TpWit P (c m hm)) := by
  obtain ⟨M, inst, hP, v, hv, htp⟩ := tp_witness hc hm
  exact ⟨⟨M, inst, hP, v, hv, htp⟩⟩

/-- The chosen witness at arity `k + 1`. -/
noncomputable def wit (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSample P) n c κ) (k : ℕ) :
    TpWit P (c (k + 1) (Nat.succ_pos k)) :=
  Classical.choice (tpWit_nonempty hc (Nat.succ_pos k))

variable (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSample P) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpRes f (c m hm))

/-- The piece at arity `k + 1`: the term hull of the witness tuple. -/
abbrev tpPiece (k : ℕ) : Type u := Hull (L := L) (wit hc k).v

include hcoh in
theorem tpPiece_tp {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) :
    tpCode (L := L) (wit hc k).v = tpCode ((wit hc l).v ∘ e) := by
  calc tpCode (L := L) (wit hc k).v = c (k + 1) (Nat.succ_pos k) := (wit hc k).tp
    _ = tpRes e (c (l + 1) (Nat.succ_pos l)) := hcoh (Nat.succ_pos k) (Nat.succ_pos l) e
    _ = tpRes e (tpCode (L := L) (wit hc l).v) := by rw [(wit hc l).tp]
    _ = tpCode ((wit hc l).v ∘ e) := tpRes_tpCode e _

include hcoh in
/-- The piece map along an increasing map of positions. -/
noncomputable def tpPieceMap {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) :
    tpPiece hc k ↪[L] tpPiece hc l :=
  hullMapEmb e (tpPiece_tp hc hcoh e)

theorem tpPieceMap_refl (k : ℕ) (x : tpPiece hc k) :
    tpPieceMap hc hcoh (RelEmbedding.refl (α := Fin (k + 1)) (· ≤ ·)) x = x :=
  hullMap_id _ (tpPiece_tp hc hcoh (k := k) (l := k) (RelEmbedding.refl (· ≤ ·))) x

theorem tpPieceMap_trans {k l n : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1))
    (e' : Fin (l + 1) ↪o Fin (n + 1)) (x : tpPiece hc k) :
    tpPieceMap hc hcoh (e.trans e') x = tpPieceMap hc hcoh e' (tpPieceMap hc hcoh e x) :=
  (hullMap_comp (⇑e) (⇑e') (tpPiece_tp hc hcoh e) (tpPiece_tp hc hcoh e')
    (tpPiece_tp hc hcoh (e.trans e')) x).symm

/-- Each piece embeds in its witness structure, an admitted sample structure. -/
noncomputable def tpPieceEmb (k : ℕ) : tpPiece hc k ↪[L] (wit hc k).M := hullEmb _

/-- **Pieces from coherent types.**  For any class of `L`-structures with arbitrarily large
members there are coherent types and, for each positive arity, an `L`-structure (the term
hull of a realizing tuple in an admitted structure, embedded there) with `L`-embeddings
along increasing maps of positions, functorial in those maps. -/
theorem tp_pieces_exist
    (hlarge : ∀ κ : Cardinal.{u}, ∃ (M : Type u) (_ : L.Structure M), P M ∧ κ ≤ #M) :
    ∃ (c : (m : ℕ) → 0 < m → TpColor L m) (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Joint (TpSample P) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = tpRes f (c m hm)),
      (∀ k (x : tpPiece hc k), tpPieceMap hc hcoh (RelEmbedding.refl (α := Fin (k + 1)) (· ≤ ·)) x = x) ∧
      (∀ {k l n : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (e' : Fin (l + 1) ↪o Fin (n + 1))
        (x : tpPiece hc k),
        tpPieceMap hc hcoh (e.trans e') x = tpPieceMap hc hcoh e' (tpPieceMap hc hcoh e x)) := by
  obtain ⟨c, hc, hcoh⟩ := tp_coherent_colors hlarge
  exact ⟨c, hc, hcoh, fun k x => tpPieceMap_refl hc hcoh k x,
    fun e e' x => tpPieceMap_trans hc hcoh e e' x⟩

end Pieces

end Hull83
end AEC
