module

public import AEC.Audit.TinyAEC
public import AEC.Section2.DirectedLimit

@[expose] public section

/-!
# The AEC of all sets (statement audit)

`allSetsAEC`: empty language, every structure is a member, every embedding is strong. Chain
unions are direct limits (`algebraicLimit`).
-/

namespace AEC
namespace Audit

universe u

open FirstOrder Cardinal

section chain

variable (C : OrdinalChain eL.{u})

/-- Ordinal value of an index. -/
noncomputable def ordOf (i : C.δ.ToType) : _root_.Ordinal.{u} := (Ordinal.ToType.mk.symm i).1

theorem ordOf_lt (i : C.δ.ToType) : ordOf C i < C.δ := (Ordinal.ToType.mk.symm i).2

theorem ordOf_lt_iff {i j : C.δ.ToType} : ordOf C i < ordOf C j ↔ i < j := by
  unfold ordOf
  exact Subtype.coe_lt_coe.trans (OrderIso.lt_iff_lt _)

/-- The transition map along `i ≤ j` (identity on the diagonal). -/
noncomputable def chainMap {i j : C.δ.ToType} (h : i ≤ j) :
    Language.Embedding eL.{u} (C.obj (ordOf C i) (ordOf_lt C i)).carrier
      (C.obj (ordOf C j) (ordOf_lt C j)).carrier :=
  if hlt : i < j then C.map _ _ _ _ ((ordOf_lt_iff C).mpr hlt)
  else (le_antisymm h (not_lt.mp hlt)) ▸ Language.Embedding.refl _ _

theorem chainMap_refl (i : C.δ.ToType) :
    chainMap C (le_refl i) = Language.Embedding.refl _ _ := by
  simp only [chainMap, lt_irrefl, ↓reduceDIte]

theorem chainMap_of_lt {i j : C.δ.ToType} (h : i < j) :
    chainMap C h.le = C.map _ _ _ _ ((ordOf_lt_iff C).mpr h) := by
  simp only [chainMap, h, ↓reduceDIte]

theorem chainMap_trans (hcomp : OrdinalChain.map_comp_prop eL.{u} C)
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
noncomputable abbrev chainSystem (hcomp : OrdinalChain.map_comp_prop eL.{u} C) :
    DirectedSystem eL.{u} where
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

/-- Injective maps are embeddings of `eL`-structures (any structures). -/
def embOf {M N : Model eL.{u}} (f : M.carrier → N.carrier) (hf : Function.Injective f) :
    Language.Embedding eL.{u} M.carrier N.carrier where
  toFun := f
  inj' := hf
  map_fun' := fun {_} g => isEmptyElim g
  map_rel' := fun {_} r => isEmptyElim r


section union

variable {C : OrdinalChain eL.{u}}

/-- Transport between chain objects at equal ordinals. -/
def trObj {a i : _root_.Ordinal.{u}} (h : a = i) (ha : a < C.δ) (hi : i < C.δ) :
    Language.Embedding eL.{u} (C.obj i hi).carrier (C.obj a ha).carrier := by
  subst h
  exact Language.Embedding.refl _ _

theorem trObj_map {a i b j : _root_.Ordinal.{u}} (ha : a = i) (hb : b = j) (ha' : a < C.δ)
    (hi : i < C.δ) (hb' : b < C.δ) (hj : j < C.δ) (hab : a < b) (hij : i < j) :
    (trObj hb hb' hj).comp (C.map i j hi hj hij) = (C.map a b ha' hb' hab).comp (trObj ha ha' hi) := by
  subst ha hb
  ext x
  rfl

/-- Values of two chain elements identified in a union agree under a compatible cocone. -/
theorem union_agree (U : ChainUnion C) {N : Model eL.{u}}
    (g : ∀ i (hi : i < C.δ), Language.Embedding eL.{u} (C.obj i hi).carrier N.carrier)
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

theorem union_reflect (U : ChainUnion C) {N : Model eL.{u}}
    (g : ∀ i (hi : i < C.δ), Language.Embedding eL.{u} (C.obj i hi).carrier N.carrier)
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

theorem canon_trObj (C : OrdinalChain eL.{u}) (hcomp : OrdinalChain.map_comp_prop eL.{u} C)
    {k1 k2 : C.δ.ToType} (e : k1 = k2) (p : ordOf C k1 = ordOf C k2)
    (y : (C.obj (ordOf C k2) (ordOf_lt C k2)).carrier) :
    (algebraicLimit (chainSystem C hcomp)).canon k1 (trObj p (ordOf_lt C k1) (ordOf_lt C k2) y) =
      (algebraicLimit (chainSystem C hcomp)).canon k2 y := by
  subst e
  rfl

/-- The direct limit of a chain as a `ChainUnion`. -/
noncomputable def chainUnionOf (C : OrdinalChain eL.{u})
    (hcomp : OrdinalChain.map_comp_prop eL.{u} C) : ChainUnion C := by
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

/-- The AEC of all sets. -/
noncomputable abbrev allSetsAEC : AbstractElementaryClass.{u} where
  τ := eL.{u}
  Mem _ := True
  Strong _ := True
  strong_mem_dom _ _ := trivial
  strong_mem_cod _ _ := trivial
  strong_refl _ _ := trivial
  strong_trans _ _ _ _ := trivial
  strong_antisymm {M N} f g _ _ hgf hfg := by
    refine ⟨⟨⟨f, g, hgf, hfg⟩, fun {_} h => isEmptyElim h, fun {_} r => isEmptyElim r⟩, ?_⟩
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
    refine ⟨embOf (M := U.obj) (N := N) pick (fun a b hab => ?_), trivial, fun i hi => ?_⟩
    · rw [← hpick a, ← hpick b]
      exact union_reflect U g hcomm _ _ _ _ hab
    · ext y
      exact union_agree U g hcomm _ _ _ _ (hpick (U.incl i hi y))
  lsBound := ℵ₀
  lsBound_infinite := le_rfl
  lsBound_language := by
    have : eL.{u}.card = 0 := by
      simp [Language.card, Language.Symbols, eL]
    simp [this]
  ls_axiom M _ A := by
    refine ⟨⟨A, eStr _⟩, embOf (M := ⟨A, eStr _⟩) (N := M) Subtype.val Subtype.val_injective, trivial,
      trivial, fun a ha => ⟨⟨a, ha⟩, rfl⟩, ?_⟩
    exact le_self_add

end Audit
end AEC
