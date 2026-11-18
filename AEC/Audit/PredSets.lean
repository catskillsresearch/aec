module

public import AEC.Audit.AllSetsMinimal
public import AEC.Section14.Results

@[expose] public section

/-!
# The AEC of sets with a unary predicate (statement audit)

`predAEC`: language with one unary relation symbol `P`, every structure is a member, every
embedding is strong; chain unions are direct limits. `predMinimal`: `M₀ = ℕ` with `P = ∅`, and
the minimal type "new and outside `P`". The class is not categorical in any infinite cardinal
(`P` may be empty or everything), and two pointed models of the same size need not be
isomorphic over the copy of `M₀`: this refutes the unconditional Corollary 14.4.
-/

namespace AEC
namespace Audit
namespace Pred

universe u

open FirstOrder Cardinal

set_option linter.deprecated false

variable {τ : Tau.{u}}

section chain

variable (C : OrdinalChain τ)

/-- Ordinal value of an index. -/
noncomputable def ordOf (i : C.δ.ToType) : _root_.Ordinal.{u} := (Ordinal.ToType.mk.symm i).1

theorem ordOf_lt (i : C.δ.ToType) : ordOf C i < C.δ := (Ordinal.ToType.mk.symm i).2

theorem ordOf_lt_iff {i j : C.δ.ToType} : ordOf C i < ordOf C j ↔ i < j := by
  unfold ordOf
  exact Subtype.coe_lt_coe.trans (OrderIso.lt_iff_lt _)

/-- The transition map along `i ≤ j` (identity on the diagonal). -/
noncomputable def chainMap {i j : C.δ.ToType} (h : i ≤ j) :
    Language.Embedding τ (C.obj (ordOf C i) (ordOf_lt C i)).carrier
      (C.obj (ordOf C j) (ordOf_lt C j)).carrier :=
  if hlt : i < j then C.map _ _ _ _ ((ordOf_lt_iff C).mpr hlt)
  else (le_antisymm h (not_lt.mp hlt)) ▸ Language.Embedding.refl _ _

theorem chainMap_refl (i : C.δ.ToType) :
    chainMap C (le_refl i) = Language.Embedding.refl _ _ := by
  simp only [chainMap, lt_irrefl, ↓reduceDIte]

theorem chainMap_of_lt {i j : C.δ.ToType} (h : i < j) :
    chainMap C h.le = C.map _ _ _ _ ((ordOf_lt_iff C).mpr h) := by
  simp only [chainMap, h, ↓reduceDIte]

theorem chainMap_trans (hcomp : OrdinalChain.map_comp_prop τ C)
    {i j k : C.δ.ToType} (hij : i ≤ j) (hjk : j ≤ k) :
    chainMap C (hij.trans hjk) = (chainMap C hjk).comp (chainMap C hij) := by
  rcases hij.lt_or_eq with hij' | rfl
  · rcases hjk.lt_or_eq with hjk' | rfl
    · rw [chainMap_of_lt C (hij'.trans hjk'), chainMap_of_lt C hij', chainMap_of_lt C hjk']
      exact (hcomp _ _ _ _ _ _ _ _).symm
    · rw [chainMap_refl]
      ext x
      rfl
  · rw [chainMap_refl]
    ext x
    rfl

/-- The chain as a directed system on `δ.ToType`. -/
noncomputable abbrev chainSystem (hcomp : OrdinalChain.map_comp_prop τ C) :
    DirectedSystem τ where
  ι := C.δ.ToType
  nonempty := ⟨Ordinal.ToType.mk ⟨0, pos_iff_ne_zero.mpr C.nonzero⟩⟩
  rel i j := i ≤ j
  refl i := le_refl i
  trans h1 h2 := h1.trans h2
  directed i j := ⟨max i j, le_max_left _ _, le_max_right _ _⟩
  obj i := C.obj (ordOf C i) (ordOf_lt C i)
  map h := chainMap C h
  map_refl i := chainMap_refl C i
  map_trans h1 h2 := chainMap_trans C hcomp h1 h2

/-- Every ordinal below `δ` is `ordOf` of an index. -/
theorem exists_index {i : _root_.Ordinal.{u}} (hi : i < C.δ) :
    ∃ k : C.δ.ToType, ordOf C k = i :=
  ⟨Ordinal.ToType.mk ⟨i, hi⟩, by simp [ordOf]⟩

end chain

section union

variable {C : OrdinalChain τ}

/-- Transport between chain objects at equal ordinals. -/
def trObj {a i : _root_.Ordinal.{u}} (h : a = i) (ha : a < C.δ) (hi : i < C.δ) :
    Language.Embedding τ (C.obj i hi).carrier (C.obj a ha).carrier := by
  subst h
  exact Language.Embedding.refl _ _

theorem trObj_map {a i b j : _root_.Ordinal.{u}} (ha : a = i) (hb : b = j) (ha' : a < C.δ)
    (hi : i < C.δ) (hb' : b < C.δ) (hj : j < C.δ) (hab : a < b) (hij : i < j) :
    (trObj hb hb' hj).comp (C.map i j hi hj hij) = (C.map a b ha' hb' hab).comp (trObj ha ha' hi) := by
  subst ha hb
  ext x
  rfl

/-- Values of two chain elements identified in a union agree under a compatible cocone. -/
theorem union_agree (U : ChainUnion C) {N : Model τ}
    (g : ∀ i (hi : i < C.δ), Language.Embedding τ (C.obj i hi).carrier N.carrier)
    (hcomm : ∀ i j hi hj hij, (g j hj).comp (C.map i j hi hj hij) = g i hi)
    {i j : _root_.Ordinal.{u}} (hi : i < C.δ) (hj : j < C.δ) (y : (C.obj i hi).carrier)
    (y' : (C.obj j hj).carrier) (h : U.incl i hi y = U.incl j hj y') :
    g i hi y = g j hj y' := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have h1 : U.incl j hj (C.map i j hi hj hij y) = U.incl j hj y' := by
      rw [← h]; exact congrArg (fun e => e y) (congrArg DFunLike.coe (U.compat i j hi hj hij))
    have h2 := (U.incl j hj).injective h1
    rw [← h2]
    exact (congrArg (fun e => e y) (congrArg DFunLike.coe (hcomm i j hi hj hij))).symm
  · rw [(U.incl i hi).injective h]
  · have h1 : U.incl i hi (C.map j i hj hi hji y') = U.incl i hi y := by
      rw [h]; exact congrArg (fun e => e y') (congrArg DFunLike.coe (U.compat j i hj hi hji))
    have h2 := (U.incl i hi).injective h1
    rw [← h2]
    exact congrArg (fun e => e y') (congrArg DFunLike.coe (hcomm j i hj hi hji))

theorem union_reflect (U : ChainUnion C) {N : Model τ}
    (g : ∀ i (hi : i < C.δ), Language.Embedding τ (C.obj i hi).carrier N.carrier)
    (hcomm : ∀ i j hi hj hij, (g j hj).comp (C.map i j hi hj hij) = g i hi)
    {i j : _root_.Ordinal.{u}} (hi : i < C.δ) (hj : j < C.δ) (y : (C.obj i hi).carrier)
    (y' : (C.obj j hj).carrier) (h : g i hi y = g j hj y') :
    U.incl i hi y = U.incl j hj y' := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · have h1 : g j hj (C.map i j hi hj hij y) = g j hj y' := by
      rw [← h]; exact congrArg (fun e => e y) (congrArg DFunLike.coe (hcomm i j hi hj hij))
    rw [← (g j hj).injective h1]
    exact (congrArg (fun e => e y) (congrArg DFunLike.coe (U.compat i j hi hj hij))).symm
  · rw [(g i hi).injective h]
  · have h1 : g i hi (C.map j i hj hi hji y') = g i hi y := by
      rw [h]; exact congrArg (fun e => e y') (congrArg DFunLike.coe (hcomm j i hj hi hji))
    rw [← (g i hi).injective h1]
    exact congrArg (fun e => e y') (congrArg DFunLike.coe (U.compat j i hj hi hji))

end union

theorem canon_trObj (C : OrdinalChain τ) (hcomp : OrdinalChain.map_comp_prop τ C)
    {k1 k2 : C.δ.ToType} (e : k1 = k2) (p : ordOf C k1 = ordOf C k2)
    (y : (C.obj (ordOf C k2) (ordOf_lt C k2)).carrier) :
    (algebraicLimit (chainSystem C hcomp)).canon k1 (trObj p (ordOf_lt C k1) (ordOf_lt C k2) y) =
      (algebraicLimit (chainSystem C hcomp)).canon k2 y := by
  subst e
  rfl

/-- The direct limit of a chain as a `ChainUnion`. -/
noncomputable def chainUnionOf (C : OrdinalChain τ)
    (hcomp : OrdinalChain.map_comp_prop τ C) : ChainUnion C := by
  classical
  let k : ∀ i, i < C.δ → C.δ.ToType := fun i hi => Ordinal.ToType.mk ⟨i, hi⟩
  have hk : ∀ i hi, ordOf C (k i hi) = i := fun i hi => by simp [k, ordOf]
  refine
    { obj := (algebraicLimit (chainSystem C hcomp)).obj
      incl := fun i hi => ((algebraicLimit (chainSystem C hcomp)).canon (k i hi)).comp
        (trObj (hk i hi) (ordOf_lt C _) hi)
      compat := fun i j hi hj hij => ?_
      covers := fun x => ?_ }
  · have hkk : k i hi < k j hj := (ordOf_lt_iff C).mp (by rw [hk, hk]; exact hij)
    have hc := (algebraicLimit (chainSystem C hcomp)).compat (i := k i hi) (j := k j hj) hkk.le
    ext x
    have ht := congrArg (fun e => e x) (congrArg DFunLike.coe
      (trObj_map (hk i hi) (hk j hj) (ordOf_lt C _) hi (ordOf_lt C _) hj
        ((ordOf_lt_iff C).mpr hkk) hij))
    simp only [Language.Embedding.comp_apply] at ht
    rw [Language.Embedding.comp_apply, Language.Embedding.comp_apply, Language.Embedding.comp_apply, ht]
    have := congrArg (fun e => e (trObj (hk i hi) (ordOf_lt C _) hi x)) (congrArg DFunLike.coe hc)
    simp only [Language.Embedding.comp_apply] at this
    rw [← this, chainMap_of_lt C hkk]
  · obtain ⟨k', y, hy⟩ := (algebraicLimit (chainSystem C hcomp)).joint x
    refine ⟨ordOf C k', ordOf_lt C k', y, ?_⟩
    have hkk : k (ordOf C k') (ordOf_lt C k') = k' := 
      Ordinal.ToType.mk.apply_symm_apply k'
    rw [← hy, Language.Embedding.comp_apply]
    exact canon_trObj C hcomp hkk _ y


/-- Relation symbols: one unary symbol. -/
def ePRel (n : ℕ) : Type u := {_x : PUnit.{u + 1} // n = 1}

/-- The language with one unary predicate. -/
def eP : Tau.{u} := ⟨fun _ => PEmpty, ePRel⟩

instance (n : ℕ) : IsEmpty (eP.{u}.Functions n) := inferInstanceAs (IsEmpty PEmpty)

/-- The predicate symbol. -/
def rP : eP.{u}.Relations 1 := (⟨PUnit.unit, rfl⟩ : ePRel 1)

/-- The predicate in a model. -/
def Pm (M : Model eP.{u}) (a : M.carrier) : Prop :=
  Language.Structure.RelMap rP (fun _ : Fin 1 => a)

theorem relMap_iff (M : Model eP.{u}) {n : ℕ} (r : eP.{u}.Relations n) (xs : Fin n → M.carrier) :
    Language.Structure.RelMap r xs ↔ ∀ i, Pm M (xs i) := by
  have hn : n = 1 := (r : ePRel n).2
  subst hn
  have hr : r = rP := Subsingleton.elim (α := {_x : PUnit.{u + 1} // (1 : ℕ) = 1}) _ _
  subst hr
  have hxs : xs = fun _ => xs 0 := funext fun i => congrArg xs (Subsingleton.elim i 0)
  constructor
  · intro h i
    rw [Subsingleton.elim i 0]
    rw [hxs] at h
    exact h
  · intro h
    rw [hxs]
    exact h 0

theorem Pm_emb {M N : Model eP.{u}} (e : Language.Embedding eP.{u} M.carrier N.carrier)
    (a : M.carrier) : Pm N (e a) ↔ Pm M a :=
  e.map_rel rP (fun _ => a)

/-- An injective map preserving and reflecting the predicate is an embedding. -/
def embP {M N : Model eP.{u}} (f : M.carrier → N.carrier) (hf : Function.Injective f)
    (hP : ∀ a, Pm N (f a) ↔ Pm M a) : Language.Embedding eP.{u} M.carrier N.carrier where
  toFun := f
  inj' := hf
  map_fun' := fun {_} g => isEmptyElim g
  map_rel' := fun {_} r xs => by
    rw [relMap_iff N r, relMap_iff M r]
    exact forall_congr' fun i => hP (xs i)

/-- The structure on `X` with predicate `S`. -/
@[instance_reducible] def pStr (X : Type u) (S : Set X) : eP.{u}.Structure X where
  funMap := fun f => isEmptyElim f
  RelMap := fun _ xs => ∀ i, xs i ∈ S

def pModel (X : Type u) (S : Set X) : Model eP.{u} := ⟨X, pStr X S⟩

theorem Pm_pModel (X : Type u) (S : Set X) (a : X) : Pm (pModel X S) a ↔ a ∈ S :=
  ⟨fun h => h 0, fun h _ => h⟩

instance : Countable (eP.{u}.Symbols) := by
  unfold Language.Symbols
  have : ∀ n, Countable (eP.{u}.Relations n) := fun n =>
    inferInstanceAs (Countable {_x : PUnit.{u + 1} // n = 1})
  have : ∀ n, Countable (eP.{u}.Functions n) := fun n => inferInstanceAs (Countable PEmpty)
  infer_instance

/-- The AEC of sets with a unary predicate. -/
noncomputable abbrev predAEC : AbstractElementaryClass.{u} where
  τ := eP.{u}
  Mem _ := True
  Strong _ := True
  strong_mem_dom _ _ := trivial
  strong_mem_cod _ _ := trivial
  strong_refl _ _ := trivial
  strong_trans _ _ _ _ := trivial
  strong_antisymm {M N} f g _ _ hgf hfg := by
    refine ⟨⟨⟨f, g, hgf, hfg⟩, fun {_} h => isEmptyElim h, fun {_} r x => f.map_rel r x⟩, ?_⟩
    ext x
    rfl
  iso_closed _ _ := trivial
  transport_strong _ _ _ := trivial
  coherence _ _ _ _ _ _ := trivial
  chain_union C hcomp _ _ := ⟨chainUnionOf C hcomp, trivial, fun _ _ => trivial⟩
  chain_upper C U N g _ _ _ _ _ _ hcomm := by
    classical
    let pick : U.obj.carrier → N.carrier := fun x =>
      g (Classical.choose (U.covers x)) (Classical.choose (Classical.choose_spec (U.covers x)))
        (Classical.choose (Classical.choose_spec (Classical.choose_spec (U.covers x))))
    have hpick : ∀ x, U.incl _ (Classical.choose (Classical.choose_spec (U.covers x)))
        (Classical.choose (Classical.choose_spec (Classical.choose_spec (U.covers x)))) = x :=
      fun x => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (U.covers x)))
    have hval : ∀ x i (hi : i < C.δ) y, U.incl i hi y = x → pick x = g i hi y :=
      fun x i hi y hy => union_agree U g hcomm _ _ _ _ ((hpick x).trans hy.symm)
    refine ⟨embP (M := U.obj) (N := N) pick (fun a b hab => ?_) (fun x => ?_), trivial,
      fun i hi => ?_⟩
    · rw [← hpick a, ← hpick b]
      exact union_reflect U g hcomm _ _ _ _ hab
    · obtain ⟨i, hi, y, hy⟩ := U.covers x
      rw [hval x i hi y hy, Pm_emb, ← hy, Pm_emb]
    · ext y
      exact hval _ i hi y rfl
  lsBound := ℵ₀
  lsBound_infinite := le_rfl
  lsBound_language := Cardinal.add_le_aleph0.mpr ⟨Cardinal.mk_le_aleph0, le_rfl⟩
  ls_axiom M _ A := by
    let N : Model eP.{u} := ⟨A, ⟨fun f => isEmptyElim f,
      fun r xs => Language.Structure.RelMap r (Subtype.val ∘ xs)⟩⟩
    refine ⟨N, embP (M := N) (N := M) Subtype.val Subtype.val_injective (fun _ => Iff.rfl),
      trivial, trivial, fun a ha => ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    exact le_self_add

/-- `ℕ` with empty predicate. -/
def natP : Model eP.{u} := pModel (ULift.{u} ℕ) ∅

theorem card_natP : Model.card natP.{u} = ℵ₀ := by
  simp [Model.card, natP, pModel]

theorem card_optionP {A : Type u} (h : #A = ℵ₀) : #(Option A) = ℵ₀ := by
  rw [Cardinal.mk_option, h]
  exact Cardinal.add_one_of_aleph0_le le_rfl

/-- Minimal data on `predAEC`: the new points outside `P`. -/
noncomputable abbrev predMinimal : MinimalData predAEC.{u} where
  lam0 := ℵ₀
  M0 := natP
  inM0 := trivial
  card_eq := card_natP
  realizes M f a := a ∉ Set.range f ∧ ¬ Pm M a
  productCopies M f l := l = [] ∨ (∃ a, l = [a] ∧ a ∉ Set.range f ∧ ¬ Pm M a) ∨ 2 ≤ l.length
  nonalgebraic a h := h.1 ⟨a, rfl⟩
  singleton M f a := by
    constructor
    · rintro (h | ⟨b, hb, hr⟩ | h)
      · cases h
      · cases hb; exact hr
      · simp at h
    · intro h; exact Or.inr (Or.inl ⟨a, rfl, h⟩)
  empty _ _ := Or.inl rfl
  exists_ext A f _ _ hA := by
    let N : Model eP.{u} := pModel (Option A.carrier) {o | ∃ b, o = some b ∧ Pm A b}
    refine ⟨N, embP (M := A) (N := N) some (Option.some_injective _) (fun a => ?_), none,
      trivial, trivial, card_optionP hA, ⟨?_, ?_⟩, fun b h => by cases h⟩
    · rw [Pm_pModel]
      constructor
      · rintro ⟨b, hb, hp⟩
        cases hb
        exact hp
      · intro h
        exact ⟨a, rfl, h⟩
    · rintro ⟨x, hx⟩
      cases hx
    · rw [Pm_pModel]
      rintro ⟨b, hb, -⟩
      cases hb
  unique_ext A f N1 N2 g1 g2 a1 a2 _ _ _ _ _ _ _ hr1 hr2 hn1 hn2 := by
    classical
    let S : Set (amalgCarrier (N1 := N1.carrier) g2 a2) :=
      {z | Sum.elim (Pm N1) (fun y => Pm N2 y.1) z}
    let N : Model eP.{u} := pModel (amalgCarrier (N1 := N1.carrier) g2 a2) S
    have h2P : ∀ y, Pm N (amalgRight g1 g2 a1 a2 y) ↔ Pm N2 y := by
      intro y
      rw [Pm_pModel]
      unfold amalgRight
      by_cases hy : y = a2
      · rw [dif_pos hy, hy]
        exact iff_of_false hr1.2 hr2.2
      · rw [dif_neg hy]
        by_cases hx : ∃ x, g2 x = y
        · rw [dif_pos hx]
          show Pm N1 (g1 _) ↔ _
          rw [Pm_emb]
          have h := Pm_emb g2 (Classical.choose hx)
          rw [Classical.choose_spec hx] at h
          exact h.symm
        · rw [dif_neg hx]
          exact Iff.rfl
    refine ⟨N, embP (M := N1) (N := N) Sum.inl Sum.inl_injective
      (fun a => by rw [Pm_pModel]; exact Iff.rfl),
      embP (M := N2) (N := N) (amalgRight g1 g2 a1 a2)
        (amalgRight_inj g1 g2 a1 a2 g1.injective g2.injective hn1) h2P, trivial, ?_, fun x => ?_⟩
    · show Sum.inl a1 = amalgRight g1 g2 a1 a2 a2
      unfold amalgRight
      simp
    · show Sum.inl (g1 x) = amalgRight g1 g2 a1 a2 (g2 x)
      have hx : ∃ x', g2 x' = g2 x := ⟨x, rfl⟩
      unfold amalgRight
      rw [dif_neg (hn2 x), dif_pos hx, g2.injective (Classical.choose_spec hx)]
  Delta _ _ := True
  Delta_base := trivial

/-- A pointed model: `ℕ ⊕ X` with predicate `S` on `X`. -/
noncomputable def ptdP (X : Type u) (S : Set X) : PointedModel predAEC.{u} predMinimal.{u} where
  M := pModel (ULift.{u} ℕ ⊕ X) {z | ∃ x, z = Sum.inr x ∧ x ∈ S}
  copy := embP (M := natP) (N := pModel (ULift.{u} ℕ ⊕ X) {z | ∃ x, z = Sum.inr x ∧ x ∈ S})
    Sum.inl Sum.inl_injective (fun a => by
      refine iff_of_false (fun h => ?_) (fun h => h 0)
      obtain ⟨x, hx, -⟩ := (Pm_pModel _ _ _).mp h
      cases hx)
  copy_strong := trivial
  hasDiagram := trivial

theorem card_ptdP {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ) (S : Set κ.out) :
    Model.card (ptdP κ.out S).M = κ := by
  show #(ULift.{u} ℕ ⊕ κ.out) = κ
  rw [Cardinal.mk_sum, Cardinal.mk_out]
  simp only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0, Cardinal.lift_id]
  exact Cardinal.add_eq_right hκ hκ

/-- **Corollary 14.4 without the standing hypothesis is false.** In `predAEC` two pointed
models of the same size (predicate on every new point vs. empty predicate) are not isomorphic. -/
theorem corollary_14_4_unconditional_false :
    ¬ ∀ (K : AbstractElementaryClass.{u}) (D : MinimalData K),
      ∃ γ : Cardinal.{u}, ∀ κ, γ ≤ κ →
        ∀ M N : PointedModel K D, Model.card M.M = κ → Model.card N.M = κ →
          ∃ e : M.M.carrier ≃[K.τ] N.M.carrier,
            K.Strong e.toEmbedding ∧ e.toEmbedding.comp M.copy = N.copy := by
  intro H
  obtain ⟨γ, hγ⟩ := H predAEC.{u} predMinimal.{u}
  have hκ : ℵ₀ ≤ γ + ℵ₀ := le_add_self
  obtain ⟨e, -, -⟩ := hγ (γ + ℵ₀) le_self_add (ptdP _ Set.univ) (ptdP _ ∅)
    (card_ptdP hκ _) (card_ptdP hκ _)
  have hne : Nonempty (γ + ℵ₀).out := by
    rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_out]
    exact (lt_of_lt_of_le Cardinal.aleph0_pos hκ).ne'
  obtain ⟨x⟩ := hne
  have h := (Pm_emb e.toEmbedding (Sum.inr x)).mpr
    ((Pm_pModel _ _ _).mpr ⟨x, rfl, Set.mem_univ _⟩)
  obtain ⟨y, -, hy⟩ := (Pm_pModel _ _ _).mp h
  exact hy

end Pred
end Audit
end AEC
