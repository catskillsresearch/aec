module

public import AEC.Section8.EMExtend83

/-!
# Lemma 8.3: the generic Ehrenfeucht–Mostowski order presentation

Port of `AEC.Section2.Presentation` (lines 832–1528: labels, realization, finite-support
submodels, skeleton, cardinality bounds, pattern determination) from Section 2's specific
pieces to any finite-piece functor `F : FinPieces K` equipped with enumeration data
`E : PieceEnum F`: a small label set enumerating every piece, and a distinguished singleton
element whose two copies in the two-element piece differ.  The result
`PieceEnum.presentation E : OrderPresentation K` is the order presentation whose values are
`F`'s generic EM values (`FinPieces.limit`) with the maps `gEmMap`.  Section 2's
`emOrderPresentation` is the instance for `section2Pieces` (to be connected separately).
-/

@[expose] public section

namespace AEC
namespace EM83

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- Enumeration data on a finite-piece functor. -/
structure PieceEnum (F : FinPieces K) where
  Lab : Type u
  lab_small : #Lab ≤ ls K
  enum : ∀ k, Lab → (F.obj k).carrier
  surj : ∀ k, Function.Surjective (enum k)
  skelLab : Lab
  skel_distinct : ∀ {l : ℕ} (e e' : Fin 1 ↪o Fin (l + 1)), e 0 ≠ e' 0 →
    F.map e (enum 0 skelLab) ≠ F.map e' (enum 0 skelLab)

variable {F : FinPieces K} {E : PieceEnum F}

/-- Labels: a positive arity and a piece label. -/
def gLab (E : PieceEnum F) : Type u := ULift {n : ℕ // 0 < n} × E.Lab

def gArity (E : PieceEnum F) (l : gLab E) : ℕ := l.1.down.1

theorem gArity_pos (E : PieceEnum F) (l : gLab E) : 0 < gArity E l := l.1.down.2

theorem gLab_small : #(gLab E) ≤ ls K := by
  rw [gLab, mk_prod, lift_id, lift_id]
  have hpos : #{n : ℕ // 0 < n} ≤ aleph0 := (mk_subtype_le _).trans_eq mk_nat
  have hlift : lift.{u, 0} #{n : ℕ // 0 < n} ≤ aleph0 := by
    rw [← lift_aleph0.{u, 0}]
    exact lift_le.mpr hpos
  have hinf : aleph0 ≤ ls K := (isLSBound_ls K).1
  calc
    lift.{u, 0} #{n : ℕ // 0 < n} * #E.Lab ≤ aleph0 * ls K := mul_le_mul' hlift E.lab_small
    _ = max aleph0 (ls K) := mul_eq_max (le_refl _) hinf
    _ = ls K := max_eq_right hinf

theorem pPiece_card (E : PieceEnum F) (k : ℕ) : Model.card (F.obj k) ≤ ls K :=
  (mk_le_of_surjective (E.surj k)).trans E.lab_small

def pTermIndex {I : Type u} [LinearOrder I] [Nonempty I]
    (t : SupportTerm (gLab E) (gArity E) I) : (F.system I).ι :=
  haveI : Nonempty (Fin (gArity E t.label)) := ⟨⟨0, gArity_pos E t.label⟩⟩
  ⟨Finset.univ.map ⟨t.pos, t.increasing.injective⟩,
   Finset.map_nonempty.mpr Finset.univ_nonempty⟩

theorem pTermIndex_card {I : Type u} [LinearOrder I] [Nonempty I]
    (t : SupportTerm (gLab E) (gArity E) I) :
    (pTermIndex (E := E) t).1.card = gArity E t.label := by
  have : Nonempty (Fin (gArity E t.label)) := ⟨⟨0, gArity_pos E t.label⟩⟩
  simp [pTermIndex, Finset.card_map]

noncomputable def pTermElem {I : Type u} [LinearOrder I] [Nonempty I]
    (t : SupportTerm (gLab E) (gArity E) I) :
    ((F.system I).obj (pTermIndex (E := E) t)).carrier :=
  E.enum (pTermIndex (E := E) t).1.card.pred t.label.2

noncomputable def pEmRealize {I : Type u} [LinearOrder I] [Nonempty I]
    (t : SupportTerm (gLab E) (gArity E) I) : (F.limit I).obj.carrier :=
  (F.limit I).canon (pTermIndex (E := E) t) (pTermElem (E := E) t)

lemma pPieceEnum_enum_heq (k l : ℕ) (h : k = l) (η : E.Lab) :
    HEq (E.enum k η) (E.enum l η) := by
  subst h
  rfl

theorem pEmRealize_surjective {I : Type u} [LinearOrder I] [Nonempty I] :
    Function.Surjective (pEmRealize (E := E) (I := I)) := by
  intro x
  obtain ⟨s, y, rfl⟩ := (F.limit I).joint x
  set k := s.1.card.pred
  have hpos : 0 < k + 1 := Nat.succ_pos k
  obtain ⟨η, hη⟩ := E.surj k y
  have hcard : k + 1 = s.1.card := (Nat.succ_pred (Finset.card_pos.mpr s.2).ne')
  let pos : Fin (k + 1) → I := fun i => s.1.orderEmbOfFin rfl (Fin.cast hcard i)
  have hmono : StrictMono pos := fun a b hab =>
    (s.1.orderEmbOfFin rfl).strictMono ((Fin.castOrderIso hcard).strictMono hab)
  let lab : gLab E := ⟨ULift.up ⟨k + 1, hpos⟩, η⟩
  let t : SupportTerm (gLab E) (gArity E) I := ⟨lab, pos, hmono⟩
  have hrange : Finset.univ.map ⟨pos, hmono.injective⟩ = s.1 := by
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk, pos]
    constructor
    · rintro ⟨i, rfl⟩
      exact Finset.orderEmbOfFin_mem s.1 rfl _
    · intro ha
      obtain ⟨j, hj⟩ := (s.1.orderIsoOfFin rfl).surjective ⟨a, ha⟩
      refine ⟨(Fin.castOrderIso hcard).symm j, ?_⟩
      have hcast_id : Fin.cast hcard ((Fin.castOrderIso hcard).symm j) = j :=
        OrderIso.apply_symm_apply (Fin.castOrderIso hcard) j
      exact hcast_id.symm ▸ congrArg Subtype.val hj
  have hidx : pTermIndex (E := E) t = s := Subtype.ext hrange
  refine ⟨t, ?_⟩
  unfold pEmRealize
  have helem : HEq (pTermElem (E := E) t) y := by
    rw [← hη]
    unfold pTermElem
    have hpred : (pTermIndex (E := E) t).1.card.pred = k := congrArg (fun u : (F.system I).ι => u.1.card.pred) hidx
    exact pPieceEnum_enum_heq (E := E) _ _ hpred η
  exact canon_congr (F.limit I) hidx (pTermElem (E := E) t) y helem

/-- The finite-support model associated with a subset of the linear order. -/
noncomputable def pEmSub {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I) : Model K.τ :=
  if hs : s.Nonempty then (F.system I).obj ⟨s, hs⟩ else F.obj 0

theorem pEmSub_eq {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I) (hs : s.Nonempty) :
    pEmSub (F := F) s = (F.system I).obj ⟨s, hs⟩ :=
  dite_eq_left hs

/-- Inclusion of the small finite-support model into the limit. -/
noncomputable def pEmSubIncl {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I)
    (hs : s.Nonempty) : Language.Embedding K.τ (pEmSub (F := F) s).carrier (F.limit I).obj.carrier :=
  ((F.limit I).canon ⟨s, hs⟩).comp (embeddingOfEq (pEmSub_eq s hs))


theorem pEmSubStrong {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I)
    (hs : s.Nonempty) : K.Strong (pEmSubIncl (F := F) s hs) := by
  have hmem : K.Mem (pEmSub (F := F) s) := by
    rw [pEmSub_eq s hs]
    exact F.mem _
  have hequiv : K.Strong (embeddingOfEq (pEmSub_eq s hs)) :=
    strong_of_equiv K (equivOfEq (pEmSub_eq s hs)) hmem
  exact K.strong_trans (embeddingOfEq (pEmSub_eq s hs)) ((F.limit I).canon ⟨s, hs⟩)
    hequiv ((F.limit_spec I).2.1 ⟨s, hs⟩)

theorem pEmSubCard (E : PieceEnum F) {I : Type u} [LinearOrder I] [Nonempty I] (s : Finset I)
    (hs : s.Nonempty) : Model.card (pEmSub (F := F) s) ≤ ls K := by
  rw [pEmSub_eq s hs]
  exact pPiece_card E s.card.pred


theorem pEmSubMono {I : Type u} [LinearOrder I] [Nonempty I] (s t : Finset I)
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) :
    ∃ g : Language.Embedding K.τ (pEmSub (F := F) s).carrier (pEmSub (F := F) t).carrier,
      K.Strong g ∧ (pEmSubIncl (F := F) t ht).comp g = pEmSubIncl (F := F) s hs := by
  have hrel : (F.system I).rel ⟨s, hs⟩ ⟨t, ht⟩ := hst
  let g := (embeddingOfEq (pEmSub_eq t ht).symm).comp
    (((F.system I).map hrel).comp (embeddingOfEq (pEmSub_eq s hs)))
  have hmem_s_obj : K.Mem ((F.system I).obj ⟨s, hs⟩) :=
    F.mem _
  have hmem_s : K.Mem (pEmSub (F := F) s) := by
    rw [pEmSub_eq s hs]; exact hmem_s_obj
  have hequiv_s : K.Strong (embeddingOfEq (pEmSub_eq s hs)) :=
    strong_of_equiv K (equivOfEq (pEmSub_eq s hs)) hmem_s
  have hmap : K.Strong ((F.system I).map hrel) :=
    F.strong _
  have hmem_t_obj : K.Mem ((F.system I).obj ⟨t, ht⟩) :=
    F.mem _
  have hequiv_t : K.Strong (embeddingOfEq (pEmSub_eq t ht).symm) :=
    strong_of_equiv K (equivOfEq (pEmSub_eq t ht).symm) hmem_t_obj
  have hg : K.Strong g :=
    K.strong_trans _ _ (K.strong_trans _ _ hequiv_s hmap) hequiv_t
  refine ⟨g, hg, ?_⟩
  ext x
  have hcancel := embeddingOfEq_cancel (pEmSub_eq t ht)
    (((F.system I).map hrel) (embeddingOfEq (pEmSub_eq s hs) x))
  have hcan := congrFun (congrArg (⇑) ((F.limit I).compat hrel))
    (embeddingOfEq (pEmSub_eq s hs) x)
  simp only [g, pEmSubIncl, Language.Embedding.comp_apply]
  rw [hcancel]
  exact hcan

theorem pEmSubCover {I : Type u} [LinearOrder I] [Nonempty I]
    (x : (F.limit I).obj.carrier) :
    ∃ s : Finset I, ∃ hs : s.Nonempty, ∃ y : (pEmSub (F := F) s).carrier,
      pEmSubIncl (F := F) s hs y = x := by
  obtain ⟨⟨s, hs⟩, y, rfl⟩ := (F.limit I).joint x
  refine ⟨s, hs, embeddingOfEq (pEmSub_eq s hs).symm y, ?_⟩
  unfold pEmSubIncl
  rw [Language.Embedding.comp_apply, embeddingOfEq_cancel (pEmSub_eq s hs) y]

/-- An order embedding transports a support term by substituting indices. -/
def pMapTerm {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    (t : SupportTerm (gLab E) (gArity E) I) :
    SupportTerm (gLab E) (gArity E) J where
  label := t.label
  pos := f ∘ t.pos
  increasing := f.strictMono.comp t.increasing

theorem pTermIndex_mapTerm {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (t : SupportTerm (gLab E) (gArity E) I) :
    pTermIndex (E := E) (pMapTerm f t) = gSystemImage (F := F) f (pTermIndex (E := E) t) := by
  apply Subtype.ext
  simp only [pTermIndex, pMapTerm, gSystemImage, Finset.map_map]
  rfl


theorem pEmRealize_mapTerm {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (t : SupportTerm (gLab E) (gArity E) I) :
    gEmMap (F := F) f (pEmRealize (E := E) t) = pEmRealize (E := E) (pMapTerm f t) := by
  have hcanon := congrFun (congrArg (⇑) (gEmMap_canon (F := F) f (pTermIndex (E := E) t)))
    (pTermElem (E := E) t)
  simp only [Language.Embedding.comp_apply] at hcanon
  rw [pEmRealize, hcanon, gSubstAt, Language.Embedding.comp_apply, pEmRealize]
  have hidx : gSystemImage (F := F) f (pTermIndex (E := E) t) = pTermIndex (E := E) (pMapTerm f t) :=
    (pTermIndex_mapTerm f t).symm
  have helem : HEq (gSystemComponent (F := F) f (pTermIndex (E := E) t) (pTermElem (E := E) t))
      (pTermElem (E := E) (pMapTerm f t)) := by
    rw [gSystemComponent_apply]
    have hcast : (pTermIndex (E := E) t).1.card.pred =
        (pTermIndex (E := E) (pMapTerm f t)).1.card.pred := by
      rw [pTermIndex_mapTerm]
      simp [gSystemImage, Finset.card_map]
    have h1 : HEq (Eq.mp (congrArg (fun n => (F.obj n).carrier)
        (Nat.succ_injective (congrArg (fun n : ℕ => n.pred + 1)
          (imageIndex_card f (pTermIndex (E := E) t))).symm)) (pTermElem (E := E) t))
        (pTermElem (E := E) t) := eqMp_heq _ _
    have h2 : HEq (pTermElem (E := E) t) (pTermElem (E := E) (pMapTerm f t)) := by
      dsimp [pTermElem, pMapTerm]
      exact pPieceEnum_enum_heq (E := E) _ _ hcast t.label.2
    exact h1.trans h2
  exact canon_congr (F.limit J) hidx _ _ helem

/-- The distinguished element on a singleton order. -/
noncomputable def pEmSkeletonElem :
    (F.obj 0).carrier :=
  E.enum 0 E.skelLab

noncomputable def pEmSkeletonFun
    {I : Type u} [LinearOrder I] [Nonempty I] (i : I) :
    (F.limit I).obj.carrier :=
  (F.limit I).canon ⟨{i}, Finset.singleton_nonempty i⟩ (pEmSkeletonElem (E := E))

/-- The singleton support term. -/
noncomputable def pSkeletonTerm {I : Type u} [LinearOrder I] (i : I) :
    SupportTerm (gLab E) (gArity E) I where
  label := ⟨ULift.up ⟨1, Nat.succ_pos 0⟩, E.skelLab⟩
  pos := fun _ => i
  increasing := fun a b hab => by
    have ha : a.1 < 1 := a.2
    have hb : b.1 < 1 := b.2
    have h : a.1 < b.1 := hab
    omega

theorem pTermIndex_skeletonTerm {I : Type u} [LinearOrder I] [Nonempty I] (i : I) :
    pTermIndex (E := E) (pSkeletonTerm i) = ⟨{i}, Finset.singleton_nonempty i⟩ := by
  apply Subtype.ext
  ext a
  simp only [pTermIndex, pSkeletonTerm, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Finset.mem_singleton]
  constructor
  · rintro ⟨j, -, rfl⟩
    rfl
  · rintro rfl
    exact ⟨⟨0, Nat.succ_pos 0⟩, Finset.mem_univ _, rfl⟩

theorem pEmRealize_skeletonTerm {I : Type u} [LinearOrder I] [Nonempty I] (i : I) :
    pEmRealize (E := E) (pSkeletonTerm i) = pEmSkeletonFun (E := E) i := by
  unfold pEmRealize pEmSkeletonFun
  have hidx : pTermIndex (E := E) (pSkeletonTerm i) = ⟨{i}, Finset.singleton_nonempty i⟩ :=
    pTermIndex_skeletonTerm i
  have helem : HEq (pTermElem (E := E) (pSkeletonTerm i)) (pEmSkeletonElem (E := E)) := by
    dsimp [pTermElem, pEmSkeletonElem, pSkeletonTerm]
    have hcast : (pTermIndex (E := E) (pSkeletonTerm i)).1.card.pred = 0 := by
      rw [hidx]
      rfl
    exact pPieceEnum_enum_heq (E := E) _ _ hcast _
  exact canon_congr (F.limit I) hidx _ _ helem

theorem pEmSkeleton_natural {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (i : I) :
    gEmMap (F := F) f (pEmSkeletonFun (E := E) i) = pEmSkeletonFun (E := E) (f i) := by
  have hmap : pMapTerm (E := E) f (pSkeletonTerm i) = pSkeletonTerm (f i) := by
    apply SupportTerm.ext_of_label_eq (h := rfl)
    intro a; rfl
  have h0 : pEmSkeletonFun (E := E) i = pEmRealize (E := E) (pSkeletonTerm i) :=
    (pEmRealize_skeletonTerm (I := I) i).symm
  have h1 : gEmMap (F := F) f (pEmRealize (E := E) (pSkeletonTerm i)) =
      pEmRealize (E := E) (pMapTerm (E := E) f (pSkeletonTerm i)) :=
    pEmRealize_mapTerm f (pSkeletonTerm i)
  have h2 : pEmRealize (E := E) (pMapTerm (E := E) f (pSkeletonTerm i)) =
      pEmRealize (E := E) (pSkeletonTerm (f i)) :=
    congrArg (pEmRealize (E := E)) hmap
  have h3 : pEmRealize (E := E) (pSkeletonTerm (f i)) = pEmSkeletonFun (E := E) (f i) :=
    pEmRealize_skeletonTerm (I := J) (f i)
  exact (congrArg (gEmMap (F := F) f) h0).trans (h1.trans (h2.trans h3))

/-- The unique order embedding sending `0 ↦ i` and `1 ↦ j` when `i < j`. -/

theorem pEmSkeletonFun_fin2_distinct (E : PieceEnum F) :
    pEmSkeletonFun (E := E) (I := ULift.{u, 0} (Fin 2)) (ULift.up 0) ≠
    pEmSkeletonFun (E := E) (I := ULift.{u, 0} (Fin 2)) (ULift.up 1) := by
  intro h
  let u : (F.system (ULift.{u, 0} (Fin 2))).ι := ⟨Finset.univ, Finset.univ_nonempty⟩
  have hu0 : (F.system (ULift.{u, 0} (Fin 2))).rel ⟨{ULift.up 0}, Finset.singleton_nonempty _⟩ u :=
    Finset.subset_univ _
  have hu1 : (F.system (ULift.{u, 0} (Fin 2))).rel ⟨{ULift.up 1}, Finset.singleton_nonempty _⟩ u :=
    Finset.subset_univ _
  have hcan0 := congrFun (congrArg (⇑) ((F.limit (ULift.{u, 0} (Fin 2))).compat hu0))
    (pEmSkeletonElem (E := E))
  have hcan1 := congrFun (congrArg (⇑) ((F.limit (ULift.{u, 0} (Fin 2))).compat hu1))
    (pEmSkeletonElem (E := E))
  have h_eq : (F.system (ULift.{u, 0} (Fin 2))).map hu0 (pEmSkeletonElem (E := E)) =
      (F.system (ULift.{u, 0} (Fin 2))).map hu1 (pEmSkeletonElem (E := E)) := by
    apply (F.limit (ULift.{u, 0} (Fin 2))).canon u |>.injective
    have hcan0' : (F.limit (ULift.{u, 0} (Fin 2))).canon u
        ((F.system (ULift.{u, 0} (Fin 2))).map hu0 (pEmSkeletonElem (E := E))) =
        pEmSkeletonFun (E := E) (ULift.up 0) := hcan0
    have hcan1' : (F.limit (ULift.{u, 0} (Fin 2))).canon u
        ((F.system (ULift.{u, 0} (Fin 2))).map hu1 (pEmSkeletonElem (E := E))) =
        pEmSkeletonFun (E := E) (ULift.up 1) := hcan1
    rw [hcan0', hcan1']
    exact h
  refine E.skel_distinct (placeSucc hu0 (Finset.singleton_nonempty _) Finset.univ_nonempty)
    (placeSucc hu1 (Finset.singleton_nonempty _) Finset.univ_nonempty) ?_ h_eq
  intro hbase_eq
  have hspec0 := placeEmb_spec hu0 ⟨0, Nat.succ_pos 0⟩
  have hspec1 := placeEmb_spec hu1 ⟨0, Nat.succ_pos 0⟩
  have h_val0 : ({ULift.up (0 : Fin 2)} : Finset (ULift (Fin 2))).orderEmbOfFin rfl ⟨0, Nat.succ_pos 0⟩ = ULift.up 0 :=
    Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ rfl _)
  have h_val1 : ({ULift.up (1 : Fin 2)} : Finset (ULift (Fin 2))).orderEmbOfFin rfl ⟨0, Nat.succ_pos 0⟩ = ULift.up 1 :=
    Finset.mem_singleton.mp (Finset.orderEmbOfFin_mem _ rfl _)
  have h0_eq : (Finset.univ : Finset (ULift (Fin 2))).orderEmbOfFin rfl
      (placeEmb hu0 ⟨0, Nat.succ_pos 0⟩) = ULift.up 0 := by
    rw [hspec0, h_val0]
  have h1_eq : (Finset.univ : Finset (ULift (Fin 2))).orderEmbOfFin rfl
      (placeEmb hu1 ⟨0, Nat.succ_pos 0⟩) = ULift.up 1 := by
    rw [hspec1, h_val1]
  have hplace_eq : placeEmb hu0 ⟨0, Nat.succ_pos 0⟩ = placeEmb hu1 ⟨0, Nat.succ_pos 0⟩ := by
    have hcast_eq : (placeSucc hu0 (Finset.singleton_nonempty _) Finset.univ_nonempty) ⟨0, Nat.succ_pos 0⟩ =
        (placeSucc hu1 (Finset.singleton_nonempty _) Finset.univ_nonempty) ⟨0, Nat.succ_pos 0⟩ := hbase_eq
    unfold placeSucc at hcast_eq
    dsimp only [RelEmbedding.trans_apply, OrderIso.coe_toOrderEmbedding] at hcast_eq
    have h_inj := (Fin.castOrderIso (Nat.succ_pred (Finset.card_pos.mpr (Finset.univ_nonempty (α := ULift (Fin 2)))).ne')).symm.injective hcast_eq
    exact h_inj
  have h_contra : (ULift.up (0 : Fin 2)) = (ULift.up (1 : Fin 2)) := by
    rw [← h0_eq, ← h1_eq, hplace_eq]
  have h01 : (0 : Fin 2) = (1 : Fin 2) := by
    injection h_contra
  have h01_nat : (0 : ℕ) = 1 := congrArg Fin.val h01
  exact Nat.zero_ne_one h01_nat

theorem pEmSkeletonFun_injective 
    {I : Type u} [LinearOrder I] [Nonempty I] :
    Function.Injective (pEmSkeletonFun (E := E) (I := I)) := by
  intro i j hij
  by_contra hne
  obtain (hlt | hgt) := lt_or_gt_of_ne hne
  · have hnat := pEmSkeleton_natural (E := E) (embFin2 i j hlt)
    have h0 : embFin2 i j hlt (ULift.up 0) = i := embFin2_zero i j hlt
    have h1 : embFin2 i j hlt (ULift.up 1) = j := embFin2_one i j hlt
    have h_eq : gEmMap (F := F) (embFin2 i j hlt) (pEmSkeletonFun (E := E) (ULift.up 0)) =
        gEmMap (F := F) (embFin2 i j hlt) (pEmSkeletonFun (E := E) (ULift.up 1)) := by
      rw [hnat (ULift.up 0), hnat (ULift.up 1), h0, h1, hij]
    have h_dis := (gEmMap (F := F) (embFin2 i j hlt)).injective h_eq
    exact pEmSkeletonFun_fin2_distinct E h_dis
  · have hnat := pEmSkeleton_natural (E := E) (embFin2 j i hgt)
    have h0 : embFin2 j i hgt (ULift.up 0) = j := embFin2_zero j i hgt
    have h1 : embFin2 j i hgt (ULift.up 1) = i := embFin2_one j i hgt
    have h_eq : gEmMap (F := F) (embFin2 j i hgt) (pEmSkeletonFun (E := E) (ULift.up 0)) =
        gEmMap (F := F) (embFin2 j i hgt) (pEmSkeletonFun (E := E) (ULift.up 1)) := by
      rw [hnat (ULift.up 0), hnat (ULift.up 1), h0, h1, hij]
    have h_dis := (gEmMap (F := F) (embFin2 j i hgt)).injective h_eq
    exact pEmSkeletonFun_fin2_distinct E h_dis

noncomputable def pEmSkeleton 
    {I : Type u} [LinearOrder I] [Nonempty I] : I ↪ (F.limit I).obj.carrier where
  toFun := pEmSkeletonFun (E := E)
  inj' := pEmSkeletonFun_injective (E := E)

theorem pEmCardLower (E : PieceEnum F) {I : Type u} [LinearOrder I] [Nonempty I] :
    #I ≤ Model.card (F.limit I).obj :=
  Cardinal.mk_le_of_injective (pEmSkeletonFun_injective (E := E))

/-- Injecting support terms into pairs of a label and a finite support set. -/
def pSupportTermToProd {I : Type u} [LinearOrder I]
    (t : SupportTerm (gLab E) (gArity E) I) : gLab E × Finset I :=
  (t.label, Finset.univ.map ⟨t.pos, t.increasing.injective⟩)

theorem pSupportTermToProd_injective {I : Type u} [LinearOrder I] :
    Function.Injective (pSupportTermToProd (E := E) (I := I)) := by
  rintro ⟨l₁, p₁, m₁⟩ ⟨l₂, p₂, m₂⟩ h
  simp only [pSupportTermToProd, Prod.mk.injEq] at h
  obtain ⟨rfl, hset⟩ := h
  have hp : p₁ = p₂ := by
    have hs : Finset.card (Finset.map (⟨p₁, m₁.injective⟩ : Fin (gArity E l₁) ↪ I) Finset.univ) = gArity E l₁ := by simp
    have h1 : p₁ = ⇑((Finset.map ⟨p₁, m₁.injective⟩ Finset.univ).orderEmbOfFin hs) :=
      Finset.orderEmbOfFin_unique hs (fun j => Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩) m₁
    have h2 : p₂ = ⇑((Finset.map ⟨p₂, m₂.injective⟩ Finset.univ).orderEmbOfFin (hset ▸ hs)) :=
      Finset.orderEmbOfFin_unique (hset ▸ hs) (fun j => Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩) m₂
    rw [h1, h2]
    congr
  have : (⟨l₁, p₁, m₁⟩ : SupportTerm (gLab E) (gArity E) I) = ⟨l₁, p₂, m₂⟩ := by
    subst hp; rfl
  exact this

/-- The upper bound on the cardinality of the model. -/
theorem pEmCardUpper (E : PieceEnum F) {I : Type u} [LinearOrder I] [Nonempty I] :
    Model.card (F.limit I).obj ≤ #I + ls K := by
  have h_surj : Model.card (F.limit I).obj ≤ #(SupportTerm (gLab E) (gArity E) I) :=
    Cardinal.mk_le_of_surjective (pEmRealize_surjective (E := E))
  have h_inj : #(SupportTerm (gLab E) (gArity E) I) ≤ #(gLab E × Finset I) :=
    Cardinal.mk_le_of_injective (pSupportTermToProd_injective (E := E))
  have h_prod : #(gLab E × Finset I) = #(gLab E) * #(Finset I) := by
    rw [mk_prod, lift_id, lift_id]
  have h_lab := gLab_small (E := E)
  have h_ls : aleph0 ≤ ls K := (isLSBound_ls K).1
  by_cases hI : Infinite I
  · have h_fin : #(Finset I) = #I := mk_finset_of_infinite I
    have h_I_inf : aleph0 ≤ #I := Cardinal.aleph0_le_mk I
    have h_mul : ls K * #I = max (ls K) #I := mul_eq_max h_ls h_I_inf
    calc
      Model.card (F.limit I).obj ≤ #(gLab E × Finset I) := h_surj.trans h_inj
      _ = #(gLab E) * #(Finset I) := h_prod
      _ ≤ ls K * #I := mul_le_mul' h_lab (le_of_eq h_fin)
      _ = max (ls K) #I := h_mul
      _ = max #I (ls K) := max_comm _ _
      _ ≤ #I + ls K := max_le le_self_add le_add_self
  · have h_fin : ¬ Infinite I := hI
    haveI : Finite I := not_infinite_iff_finite.mp h_fin
    haveI : Fintype I := Fintype.ofFinite I
    have h_finset : #(Finset I) < aleph0 := Cardinal.lt_aleph0_of_finite (Finset I)
    have h_finset_le : #(Finset I) ≤ aleph0 := le_of_lt h_finset
    have h_mul : ls K * aleph0 = max (ls K) aleph0 := mul_eq_max h_ls (le_refl _)
    calc
      Model.card (F.limit I).obj ≤ #(gLab E × Finset I) := h_surj.trans h_inj
      _ = #(gLab E) * #(Finset I) := h_prod
      _ ≤ ls K * aleph0 := mul_le_mul' h_lab h_finset_le
      _ = max (ls K) aleph0 := h_mul
      _ = ls K := max_eq_left h_ls
      _ ≤ #I + ls K := le_add_self

theorem pPattern_equiv_of_embeddings {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f_t : J ↪o I) (f_s : J ↪o I) {n : ℕ}
    (u : Fin n → SupportTerm (gLab E) (gArity E) J)
    (t s : Fin n → SupportTerm (gLab E) (gArity E) I)
    (ht : ∀ i, pMapTerm f_t (u i) = t i)
    (hs : ∀ i, pMapTerm f_s (u i) = s i) :
    (∀ i j, pEmRealize (E := E) (t i) = pEmRealize (E := E) (t j) ↔
            pEmRealize (E := E) (s i) = pEmRealize (E := E) (s j)) ∧
    (∀ {k} (f : K.τ.Functions k) (idx : Fin k → Fin n) (j : Fin n),
      Language.Structure.funMap f (fun a => pEmRealize (E := E) (t (idx a))) = pEmRealize (E := E) (t j) ↔
        Language.Structure.funMap f (fun a => pEmRealize (E := E) (s (idx a))) = pEmRealize (E := E) (s j)) ∧
    (∀ {k₁ k₂ : ℕ} (f₁ : K.τ.Functions k₁) (f₂ : K.τ.Functions k₂)
      (idx₁ : Fin k₁ → Fin n) (idx₂ : Fin k₂ → Fin n),
      Language.Structure.funMap f₁ (fun a => pEmRealize (E := E) (t (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => pEmRealize (E := E) (t (idx₂ a))) ↔
        Language.Structure.funMap f₁ (fun a => pEmRealize (E := E) (s (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => pEmRealize (E := E) (s (idx₂ a)))) ∧
    (∀ {k} (r : K.τ.Relations k) (idx : Fin k → Fin n),
      Language.Structure.RelMap r (fun a => pEmRealize (E := E) (t (idx a))) ↔
        Language.Structure.RelMap r (fun a => pEmRealize (E := E) (s (idx a)))) := by
  have ht_eval : ∀ i, pEmRealize (E := E) (t i) = gEmMap (F := F) f_t (pEmRealize (E := E) (u i)) := by
    intro i; rw [← ht i, pEmRealize_mapTerm]
  have hs_eval : ∀ i, pEmRealize (E := E) (s i) = gEmMap (F := F) f_s (pEmRealize (E := E) (u i)) := by
    intro i; rw [← hs i, pEmRealize_mapTerm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    rw [ht_eval i, ht_eval j, hs_eval i, hs_eval j]
    rw [(gEmMap (F := F) f_t).injective.eq_iff, (gEmMap (F := F) f_s).injective.eq_iff]
  · intro k f idx j
    have ht_fun : (fun a => pEmRealize (E := E) (t (idx a))) =
        (⇑(gEmMap (F := F) f_t)) ∘ (fun a => pEmRealize (E := E) (u (idx a))) := funext (fun a => ht_eval (idx a))
    have hs_fun : (fun a => pEmRealize (E := E) (s (idx a))) =
        (⇑(gEmMap (F := F) f_s)) ∘ (fun a => pEmRealize (E := E) (u (idx a))) := funext (fun a => hs_eval (idx a))
    rw [ht_eval j, hs_eval j, ht_fun, hs_fun]
    rw [← (gEmMap (F := F) f_t).map_fun, ← (gEmMap (F := F) f_s).map_fun]
    rw [(gEmMap (F := F) f_t).injective.eq_iff, (gEmMap (F := F) f_s).injective.eq_iff]
  · intro k₁ k₂ f₁ f₂ idx₁ idx₂
    have ht_fun₁ : (fun a => pEmRealize (E := E) (t (idx₁ a))) =
        (⇑(gEmMap (F := F) f_t)) ∘ (fun a => pEmRealize (E := E) (u (idx₁ a))) := funext (fun a => ht_eval (idx₁ a))
    have ht_fun₂ : (fun a => pEmRealize (E := E) (t (idx₂ a))) =
        (⇑(gEmMap (F := F) f_t)) ∘ (fun a => pEmRealize (E := E) (u (idx₂ a))) := funext (fun a => ht_eval (idx₂ a))
    have hs_fun₁ : (fun a => pEmRealize (E := E) (s (idx₁ a))) =
        (⇑(gEmMap (F := F) f_s)) ∘ (fun a => pEmRealize (E := E) (u (idx₁ a))) := funext (fun a => hs_eval (idx₁ a))
    have hs_fun₂ : (fun a => pEmRealize (E := E) (s (idx₂ a))) =
        (⇑(gEmMap (F := F) f_s)) ∘ (fun a => pEmRealize (E := E) (u (idx₂ a))) := funext (fun a => hs_eval (idx₂ a))
    rw [ht_fun₁, ht_fun₂, hs_fun₁, hs_fun₂]
    rw [← (gEmMap (F := F) f_t).map_fun, ← (gEmMap (F := F) f_t).map_fun,
        ← (gEmMap (F := F) f_s).map_fun, ← (gEmMap (F := F) f_s).map_fun]
    rw [(gEmMap (F := F) f_t).injective.eq_iff, (gEmMap (F := F) f_s).injective.eq_iff]
  · intro k r idx
    have ht_fun : (fun a => pEmRealize (E := E) (t (idx a))) =
        (⇑(gEmMap (F := F) f_t)) ∘ (fun a => pEmRealize (E := E) (u (idx a))) := funext (fun a => ht_eval (idx a))
    have hs_fun : (fun a => pEmRealize (E := E) (s (idx a))) =
        (⇑(gEmMap (F := F) f_s)) ∘ (fun a => pEmRealize (E := E) (u (idx a))) := funext (fun a => hs_eval (idx a))
    rw [ht_fun, hs_fun]
    rw [(gEmMap (F := F) f_t).map_rel, (gEmMap (F := F) f_s).map_rel]

/-- Equality, function values, and relations on realized terms are determined by the order pattern. -/
theorem pEmPatternDetermines {I : Type u} [LinearOrder I] [Nonempty I] {n : ℕ}
    (t s : Fin n → SupportTerm (gLab E) (gArity E) I)
    (hlabel : ∀ i, (t i).label = (s i).label)
    (heq : ∀ i j (a : Fin (gArity E (t i).label)) (b : Fin (gArity E (t j).label)),
      (t i).pos a = (t j).pos b ↔
        (s i).pos (Fin.cast (congrArg (gArity E) (hlabel i)) a) =
          (s j).pos (Fin.cast (congrArg (gArity E) (hlabel j)) b))
    (hlt : ∀ i j (a : Fin (gArity E (t i).label)) (b : Fin (gArity E (t j).label)),
      (t i).pos a < (t j).pos b ↔
        (s i).pos (Fin.cast (congrArg (gArity E) (hlabel i)) a) <
          (s j).pos (Fin.cast (congrArg (gArity E) (hlabel j)) b)) :
    (∀ i j, pEmRealize (E := E) (t i) = pEmRealize (E := E) (t j) ↔
            pEmRealize (E := E) (s i) = pEmRealize (E := E) (s j)) ∧
    (∀ {k} (f : K.τ.Functions k) (idx : Fin k → Fin n) (j : Fin n),
      Language.Structure.funMap f (fun a => pEmRealize (E := E) (t (idx a))) = pEmRealize (E := E) (t j) ↔
        Language.Structure.funMap f (fun a => pEmRealize (E := E) (s (idx a))) = pEmRealize (E := E) (s j)) ∧
    (∀ {k₁ k₂ : ℕ} (f₁ : K.τ.Functions k₁) (f₂ : K.τ.Functions k₂)
      (idx₁ : Fin k₁ → Fin n) (idx₂ : Fin k₂ → Fin n),
      Language.Structure.funMap f₁ (fun a => pEmRealize (E := E) (t (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => pEmRealize (E := E) (t (idx₂ a))) ↔
        Language.Structure.funMap f₁ (fun a => pEmRealize (E := E) (s (idx₁ a))) =
          Language.Structure.funMap f₂ (fun a => pEmRealize (E := E) (s (idx₂ a)))) ∧
    (∀ {k} (r : K.τ.Relations k) (idx : Fin k → Fin n),
      Language.Structure.RelMap r (fun a => pEmRealize (E := E) (t (idx a))) ↔
        Language.Structure.RelMap r (fun a => pEmRealize (E := E) (s (idx a)))) := by
  by_cases hn : n = 0
  · subst hn
    refine ⟨fun i => Fin.elim0 i, fun _ _ j => Fin.elim0 j, ?_, ?_⟩
    · intro k₁ k₂ f₁ f₂ idx₁ idx₂
      by_cases hk₁ : k₁ = 0
      · subst hk₁
        by_cases hk₂ : k₂ = 0
        · subst hk₂
          have h1 : (fun a => pEmRealize (E := E) (t (idx₁ a))) = (fun a => pEmRealize (E := E) (s (idx₁ a))) :=
            funext (fun a => Fin.elim0 a)
          have h2 : (fun a => pEmRealize (E := E) (t (idx₂ a))) = (fun a => pEmRealize (E := E) (s (idx₂ a))) :=
            funext (fun a => Fin.elim0 a)
          rw [h1, h2]
        · exact False.elim (Fin.elim0 (idx₂ ⟨0, Nat.pos_of_ne_zero hk₂⟩))
      · exact False.elim (Fin.elim0 (idx₁ ⟨0, Nat.pos_of_ne_zero hk₁⟩))
    · intro k r idx
      by_cases hk : k = 0
      · subst hk
        have h1 : (fun a => pEmRealize (E := E) (t (idx a))) = (fun a => pEmRealize (E := E) (s (idx a))) :=
          funext (fun a => Fin.elim0 a)
        rw [h1]
      · exact False.elim (Fin.elim0 (idx ⟨0, Nat.pos_of_ne_zero hk⟩))
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    let Idx := Σ i : Fin n, Fin (gArity E (t i).label)
    let pos_t : Idx → I := fun ⟨i, a⟩ => (t i).pos a
    let pos_s : Idx → I := fun ⟨i, a⟩ => (s i).pos (Fin.cast (congrArg (gArity E) (hlabel i)) a)
    let Pt : Finset I := Finset.image pos_t Finset.univ
    have hPt_nonempty : Pt.Nonempty := by
      refine ⟨pos_t ⟨⟨0, hn_pos⟩, ⟨0, gArity_pos E _⟩⟩, ?_⟩
      simp only [Pt, Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨⟨⟨0, hn_pos⟩, ⟨0, gArity_pos E _⟩⟩, rfl⟩
    let J := {x : I // x ∈ Pt}
    let linJ : LinearOrder J := Subtype.instLinearOrder _
    obtain ⟨x0, hx0⟩ := hPt_nonempty
    haveI : Nonempty J := ⟨⟨x0, hx0⟩⟩
    let f_t : J ↪o I := OrderEmbedding.subtype _
    let pick (x : J) : Idx := Classical.choose (Finset.mem_image.mp x.2)
    have pick_spec (x : J) : pos_t (pick x) = x.1 :=
      (Classical.choose_spec (Finset.mem_image.mp x.2)).2
    let f_s_fun (x : J) : I := pos_s (pick x)
    have f_s_mono : StrictMono f_s_fun := by
      intro x y hxy
      have hlt_xy : x.1 < y.1 := hxy
      have hlt_pos : pos_t (pick x) < pos_t (pick y) := by
        rw [pick_spec x, pick_spec y]
        exact hlt_xy
      rcases hx : pick x with ⟨i, a⟩
      rcases hy : pick y with ⟨j, b⟩
      rw [hx, hy] at hlt_pos
      dsimp [f_s_fun]
      rw [hx, hy]
      exact (hlt i j a b).mp hlt_pos
    let f_s : J ↪o I := @OrderEmbedding.ofStrictMono J I linJ _ f_s_fun f_s_mono
    have f_s_apply (p : Idx) : f_s ⟨pos_t p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩ = pos_s p := by
      dsimp [f_s, f_s_fun]
      obtain ⟨i, a⟩ := p
      set x : J := ⟨pos_t ⟨i, a⟩, Finset.mem_image.mpr ⟨⟨i, a⟩, Finset.mem_univ _, rfl⟩⟩
      rcases hpk : pick x with ⟨j, b⟩
      have h_eq : pos_t ⟨j, b⟩ = pos_t ⟨i, a⟩ := by
        have hspec := pick_spec x
        rw [hpk] at hspec
        exact hspec
      exact (heq j i b a).mp h_eq
    let u (i : Fin n) : SupportTerm (gLab E) (gArity E) J := {
      label := (t i).label
      pos := fun a => ⟨(t i).pos a, Finset.mem_image.mpr ⟨⟨i, a⟩, Finset.mem_univ _, rfl⟩⟩
      increasing := fun a b hab => Subtype.mk_lt_mk.mpr ((t i).increasing hab)
    }
    have ht (i : Fin n) : @pMapTerm K F E J I linJ _ f_t (u i) = t i := by
      apply SupportTerm.ext_of_label_eq (t := @pMapTerm K F E J I linJ _ f_t (u i)) (s := t i) rfl
      intro a; rfl
    have hs (i : Fin n) : @pMapTerm K F E J I linJ _ f_s (u i) = s i := by
      apply SupportTerm.ext_of_label_eq (t := @pMapTerm K F E J I linJ _ f_s (u i)) (s := s i) (hlabel i)
      intro a
      exact f_s_apply ⟨i, a⟩
    exact @pPattern_equiv_of_embeddings K F E I J _ linJ _ _ f_t f_s n u t s ht hs

/-- **The generic Ehrenfeucht–Mostowski order presentation** of an enumerated piece functor. -/
noncomputable def presentation (E : PieceEnum F) :
    OrderPresentation K where
  ell := ls K
  ell_eq := rfl
  lab := gLab E
  lab_small := gLab_small
  arity := gArity E
  arity_pos := gArity_pos E
  obj I lin non := (F.limit I).obj
  map {I J} linI linJ nonI nonJ f := gEmMap (F := F) f
  map_strong {I J} linI linJ nonI nonJ f := gEmMap_strong (F := F) f
  map_id {I} lin non := gEmMap_id (F := F)
  map_comp {I J P} linI linJ linP nonI nonJ nonP f g := gEmMap_comp (F := F) f g
  realize {I} lin non t := pEmRealize (E := E) t
  realize_surjective {I} lin non := pEmRealize_surjective (E := E)
  realize_map {I J} linI linJ nonI nonJ f t :=
    pEmRealize_mapTerm (E := E) f t
  pattern_determines {I} lin non n t s hlabel heq hlt :=
    pEmPatternDetermines (E := E) t s hlabel heq hlt
  skeleton {I} lin non := pEmSkeleton (E := E)
  skeleton_natural {I J} linI linJ nonI nonJ f i :=
    pEmSkeleton_natural (E := E) f i
  sub {I} lin non s := pEmSub (F := F) s
  sub_incl {I} lin non s hs := pEmSubIncl (F := F) s hs
  sub_strong {I} lin non s hs := pEmSubStrong (F := F) s hs
  sub_card {I} lin non s hs := pEmSubCard E s hs
  sub_mono {I} lin non s t hs ht hst := pEmSubMono (F := F) s t hs ht hst
  sub_cover {I} lin non x := pEmSubCover (F := F) x
  card_lower {I} lin non := pEmCardLower E
  card_upper {I} lin non := pEmCardUpper E


end EM83
end AEC
