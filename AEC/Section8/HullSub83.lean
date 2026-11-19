module

public import AEC.Section8.HullReduct83

/-!
# Lemma 8.3: hulls in a sublanguage

The sort objects of the pair template (`X_H → Y_H → L_H`) are term hulls of one tuple in
nested sublanguages of the expanded sample language.  For `ψ : L₀ →ᴸ L` and
`φ₀ : K.τ →ᴸ L₀`, the `L₀`-hull of a tuple maps into its `L`-hull by `ψ.onTerm`; after
reducts this is a `τ`-embedding over the sample, and it is strong when both hulls are strong
in the sample (coherence).
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- A map that factors one embedding through another (injective) one is an embedding. -/
def embOfComp {A B C : Type u} [K.τ.Structure A] [K.τ.Structure B] [K.τ.Structure C]
    (g : B ↪[K.τ] C) (h : A ↪[K.τ] C) (f : A → B) (hf : ∀ x, g (f x) = h x) :
    A ↪[K.τ] B where
  toFun := f
  inj' x y hxy := h.injective (by rw [← hf, ← hf, hxy])
  map_fun' {n} F xs := g.injective (by
    rw [hf, h.map_fun, g.map_fun]
    congr 1
    funext i
    exact (hf (xs i)).symm)
  map_rel' {n} r xs := by
    rw [← g.map_rel, ← h.map_rel]
    have : (g ∘ fun i => f (xs i)) = h ∘ xs := funext fun i => hf (xs i)
    rw [show (g ∘ (f ∘ xs)) = h ∘ xs from this]

theorem embOfComp_comp {A B C : Type u} [K.τ.Structure A] [K.τ.Structure B]
    [K.τ.Structure C] (g : B ↪[K.τ] C) (h : A ↪[K.τ] C) (f : A → B)
    (hf : ∀ x, g (f x) = h x) : g.comp (embOfComp g h f hf) = h := by
  ext x
  exact hf x

/-- Coherence: a factor of strong embeddings through a strong embedding is strong. -/
theorem embOfComp_strong {A B C : Model K.τ} (g : B.carrier ↪[K.τ] C.carrier)
    (h : A.carrier ↪[K.τ] C.carrier) (f : A.carrier → B.carrier) (hf : ∀ x, g (f x) = h x)
    (hg : K.Strong g) (hh : K.Strong h) : K.Strong (embOfComp g h f hf) :=
  K.coherence _ h g hh hg (embOfComp_comp g h f hf)

variable {L₀ L : Language.{u, u}} (ψ : L₀ →ᴸ L)

section SubHull

variable {M : Type u} [L.Structure M] {ι : Type}

/-- The `L₀`-hull of a tuple of an `L`-structure (computed in the reduct). -/
def subHull (v : ι → M) : Type u := @Hull L₀ M (ψ.reduct M) ι v

/-- The `L₀`-hull maps into the `L`-hull. -/
def subToHull (v : ι → M) : subHull ψ v → Hull (L := L) v :=
  @Quotient.map _ _ (@hullSetoid L₀ M (ψ.reduct M) ι v) (hullSetoid (L := L) v) (ψ.onTerm)
    (fun t t' (htt : @Term.realize L₀ M (ψ.reduct M) _ v t =
        @Term.realize L₀ M (ψ.reduct M) _ v t') => by
      letI := ψ.reduct M
      show (ψ.onTerm t).realize v = (ψ.onTerm t').realize v
      rw [LHom.realize_onTerm, LHom.realize_onTerm]
      exact htt)

theorem hullVal_subToHull (v : ι → M) (x : subHull ψ v) :
    hullVal (L := L) v (subToHull ψ v x) = @hullVal L₀ M (ψ.reduct M) ι v x := by
  letI := ψ.reduct M
  induction x using Quotient.ind with
  | _ t =>
    show (ψ.onTerm t).realize v = t.realize v
    exact LHom.realize_onTerm ψ t v

end SubHull

variable (φ₀ : K.τ →ᴸ L₀)

/-- The `τ`-model of the `L₀`-hull. -/
noncomputable def subHullModel {M : Type u} [L.Structure M] {ι : Type} (v : ι → M) : Model K.τ :=
  @red K L₀ φ₀ (subHull ψ v) (@hullStructure L₀ M (ψ.reduct M) ι v)

/-- The `τ`-model of the sample, seen through `L₀`. -/
def subModel' (M : Type u) [L.Structure M] : Model K.τ := @red K L₀ φ₀ M (ψ.reduct M)

/-- The `L₀`-hull embedding into the sample, after reduct. -/
noncomputable def subHullEmb {M : Type u} [L.Structure M] {ι : Type} (v : ι → M) :
    (subHullModel ψ φ₀ v).carrier ↪[K.τ] (red (ψ.comp φ₀) M).carrier :=
  @redEmb K L₀ φ₀ (subHull ψ v) M (@hullStructure L₀ M (ψ.reduct M) ι v) (ψ.reduct M)
    (@hullEmb L₀ M (ψ.reduct M) ι v)

/-- **Sublanguage hull inclusion.**  The `L₀`-hull of `v` is a `τ`-substructure of its
`L`-hull, compatibly with both embeddings into the sample. -/
noncomputable def subHullIncl {M : Type u} [L.Structure M] {ι : Type} (v : ι → M) :
    (subHullModel ψ φ₀ v).carrier ↪[K.τ] (red (ψ.comp φ₀) (Hull (L := L) v)).carrier :=
  embOfComp (redEmb (ψ.comp φ₀) (hullEmb (L := L) v)) (subHullEmb ψ φ₀ v) (subToHull ψ v)
    (fun x => hullVal_subToHull ψ v x)

/-- The inclusion is strong when both hulls are strong in the sample. -/
theorem subHullIncl_strong {M : Type u} [L.Structure M] {ι : Type} (v : ι → M)
    (hL : K.Strong (redEmb (ψ.comp φ₀) (hullEmb (L := L) v)))
    (hL₀ : K.Strong (subHullEmb ψ φ₀ v)) :
    K.Strong (subHullIncl ψ φ₀ v) :=
  embOfComp_strong _ _ _ _ hL hL₀

theorem onTerm_relabel {α β : Type*} (g : α → β) (t : L₀.Term α) :
    ψ.onTerm (t.relabel g) = (ψ.onTerm t).relabel g := by
  induction t with
  | var => rfl
  | func f ts ih => simp only [Term.relabel, LHom.onTerm, ih]

/-- Equal `L`-types give equal `L₀`-types in the reducts. -/
theorem tpCode_reduct {M N : Type u} [L.Structure M] [L.Structure N] {m : ℕ}
    {v : Fin m → M} {w : Fin m → N} (h : tpCode (L := L) v = tpCode w) :
    @tpCode L₀ M (ψ.reduct M) (Fin m) v = @tpCode L₀ N (ψ.reduct N) (Fin m) w := by
  letI := ψ.reduct M
  letI := ψ.reduct N
  ext θ
  have := congrArg (fun c : TpColor L m => ψ.onFormula θ ∈ c) h
  simp only [tpCode, Set.mem_setOf_eq, LHom.realize_onFormula] at this
  exact Iff.of_eq this

theorem subToHull_hullMap {M N : Type u} [L.Structure M] [L.Structure N] {m m' : ℕ}
    {v' : Fin m' → N} {v : Fin m → M} (g : Fin m' → Fin m)
    (h : tpCode (L := L) v' = tpCode (v ∘ g)) (x : subHull ψ v') :
    subToHull ψ v (@hullMap L₀ M N (ψ.reduct M) (ψ.reduct N) (Fin m) (Fin m') v' v g (tpCode_reduct ψ h) x) =
      hullMap g h (subToHull ψ v' x) := by
  induction x using Quotient.ind with
  | _ t =>
    exact congrArg (Quotient.mk _) (onTerm_relabel ψ g t)

/-- Vertex LS witnesses for the sublanguage hulls. -/
def SubHullStrong (P : ∀ (M : Type u) [L.Structure M], Prop) : Prop :=
  ∀ (M : Type u) [L.Structure M], P M → ∀ {ι : Type} [Finite ι] (v : ι → M),
    K.Strong (subHullEmb ψ φ₀ v)

/-- The admitted `L₀`-structures: reducts of admitted `L`-structures. -/
def reductClass (P : ∀ (M : Type u) [L.Structure M], Prop) :
    ∀ (M : Type u) [L₀.Structure M], Prop :=
  fun M inst₀ => ∃ inst : L.Structure M, @P M inst ∧ inst₀ = @LHom.reduct L₀ L ψ M inst

theorem hullStrong_reductClass {P : ∀ (M : Type u) [L.Structure M], Prop}
    (hP : SubHullStrong ψ φ₀ P) : HullStrong φ₀ (reductClass ψ P) := by
  intro M inst₀ hM ι hι v
  obtain ⟨inst, hPM, rfl⟩ := hM
  exact hP M hPM v

section SubPieces

variable {P : ∀ (M : Type u) [L.Structure M], Prop} {c : (m : ℕ) → 0 < m → TpColor L m}
  (hc : ∀ (n : ℕ) (κ : Cardinal.{u}), Joint (TpSample P) n c κ)
  (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
    c m' hm' = tpRes f (c m hm))

include hcoh in
/-- **The sublanguage pieces** on the same witnesses, as finite pieces of `K`. -/
noncomputable def subFinPieces (hP : SubHullStrong ψ φ₀ P) : EM83.FinPieces K where
  obj k := subHullModel ψ φ₀ (wit hc k).v
  mem k := K.strong_mem_dom _ (hP _ (wit hc k).mem (wit hc k).v)
  map e := @redEmb K L₀ φ₀ _ _ (@hullStructure L₀ _ (ψ.reduct _) _ _)
    (@hullStructure L₀ _ (ψ.reduct _) _ _)
    (@hullMapEmb L₀ _ _ (ψ.reduct _) (ψ.reduct _) _ _ _ _ e
      (tpCode_reduct ψ (tpPiece_tp hc hcoh e)))
  map_refl k := by
    ext x
    exact @hullMap_id L₀ _ (ψ.reduct _) _ _
      (tpCode_reduct ψ (tpPiece_tp hc hcoh (k := k) (l := k) idEmb)) x
  map_trans e f := by
    ext x
    exact (@hullMap_comp L₀ _ _ (ψ.reduct _) (ψ.reduct _) _ _ _ (ψ.reduct _) _ _ _ _
      (⇑e) (⇑f) (tpCode_reduct ψ (tpPiece_tp hc hcoh e)) (tpCode_reduct ψ (tpPiece_tp hc hcoh f))
      (tpCode_reduct ψ (tpPiece_tp hc hcoh (e.trans f))) x).symm
  strong e := @hullMap_strong K L₀ φ₀ (reductClass ψ P) (hullStrong_reductClass ψ φ₀ hP)
    _ _ (ψ.reduct _) (ψ.reduct _) ⟨_, (wit hc _).mem, rfl⟩ ⟨_, (wit hc _).mem, rfl⟩ _ _ _ _ _ _ (⇑e)
    (tpCode_reduct ψ (tpPiece_tp hc hcoh e))

include hcoh in
/-- **Sort inclusion of templates.**  The sublanguage pieces include strongly and naturally
into the full pieces (`φ = ψ ∘ φ₀`). -/
noncomputable def subPiecesHom (hP₀ : SubHullStrong ψ φ₀ P)
    (hP : HullStrong (ψ.comp φ₀) P) :
    EM83.PiecesHom (subFinPieces ψ φ₀ hc hcoh hP₀) (tpFinPieces hc hcoh hP) where
  app k := subHullIncl ψ φ₀ (wit hc k).v
  strong k := subHullIncl_strong ψ φ₀ _ (hP _ (wit hc k).mem _) (hP₀ _ (wit hc k).mem _)
  natural e := by
    ext x
    exact subToHull_hullMap ψ (⇑e) (tpPiece_tp hc hcoh e) x

include hcoh in
/-- **Sort maps of the template.**  On every nonempty order `I`, the EM value of the
sublanguage pieces embeds strongly into the EM value of the full pieces, naturally in order
embeddings (`X_H → L_H`-type maps of the pair template). -/
theorem sub_template_map (hP₀ : SubHullStrong ψ φ₀ P) (hP : HullStrong (ψ.comp φ₀) P) :
    (∀ (I : Type u) [LinearOrder I] [Nonempty I],
      K.Strong ((subPiecesHom ψ φ₀ hc hcoh hP₀ hP).limMap I)) ∧
    ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J] (f : I ↪o J),
      ((subPiecesHom ψ φ₀ hc hcoh hP₀ hP).limMap J).comp
          (EM83.gEmMap (F := subFinPieces ψ φ₀ hc hcoh hP₀) f) =
        (EM83.gEmMap (F := tpFinPieces hc hcoh hP) f).comp
          ((subPiecesHom ψ φ₀ hc hcoh hP₀ hP).limMap I) :=
  ⟨fun I _ _ => (subPiecesHom ψ φ₀ hc hcoh hP₀ hP).limMap_strong I,
    fun f => (subPiecesHom ψ φ₀ hc hcoh hP₀ hP).limMap_natural f⟩

end SubPieces

end Hull83
end AEC
