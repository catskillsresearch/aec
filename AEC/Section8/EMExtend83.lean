module

public import AEC.Section2.Presentation

/-!
# Lemma 8.3: generic Ehrenfeucht–Mostowski extension of finite pieces (first step)

Section 2 builds `emOrderPresentation` from one specific functor on finite nonempty orders:
`pieceSucc k` (the model coded by the standard color of arity `k + 1`) with the strong maps
`arityMapSucc`.  Everything downstream of `emSystem` uses only that functoriality.  For the
pair template of Lemma 8.3 the same extension is needed for the pieces coded by the coherent
pair colors.  Here the functor is abstracted (`FinPieces`) and the directed system and its
direct limit in `K` are built for any such functor; Section 2's pieces are an instance.
-/

@[expose] public section

namespace AEC
namespace EM83

universe u

open FirstOrder

variable {K : AbstractElementaryClass.{u}}

/-- A functor from the nonempty finite orders `Fin (k + 1)` (with order embeddings) into `K`
with strong embeddings. -/
structure FinPieces (K : AbstractElementaryClass.{u}) where
  obj : ℕ → Model K.τ
  mem : ∀ k, K.Mem (obj k)
  map : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) → (obj k).carrier ↪[K.τ] (obj l).carrier
  map_refl : ∀ k, map (idEmb (α := Fin (k + 1))) = Language.Embedding.refl K.τ (obj k).carrier
  map_trans : ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1)),
    map (e.trans f) = (map f).comp (map e)
  strong : ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)), K.Strong (map e)

/-- The directed system of finite-support copies of the pieces inside a nonempty order
(the generic `emSystem`). -/
noncomputable def FinPieces.system (F : FinPieces K) (I : Type u) [LinearOrder I] [Nonempty I] :
    DirectedSystem K.τ where
  ι := {s : Finset I // s.Nonempty}
  nonempty := ⟨⟨{Classical.choice ‹Nonempty I›}, Finset.singleton_nonempty _⟩⟩
  rel s t := s.1 ⊆ t.1
  refl s := Finset.Subset.refl s.1
  trans hsu hut := Finset.Subset.trans hsu hut
  directed s t :=
    ⟨⟨s.1 ∪ t.1, by
        obtain ⟨a, ha⟩ := s.2
        exact ⟨a, Finset.mem_union.mpr (Or.inl ha)⟩⟩,
      Finset.subset_union_left, Finset.subset_union_right⟩
  obj s := F.obj s.1.card.pred
  map {s t} h := F.map (placeSucc h s.2 t.2)
  map_refl s := by
    have hp : placeSucc (Finset.Subset.refl s.1) s.2 s.2 =
        idEmb (α := Fin (s.1.card.pred + 1)) :=
      placeSucc_refl s.1 s.2
    simpa [hp] using F.map_refl s.1.card.pred
  map_trans {s t u} hij hjk := by
    have hp : placeSucc (Finset.Subset.trans hij hjk) s.2 u.2 =
        (placeSucc hij s.2 t.2).trans (placeSucc hjk t.2 u.2) :=
      placeSucc_trans hij hjk s.2 t.2 u.2
    simpa [hp] using F.map_trans (placeSucc hij s.2 t.2) (placeSucc hjk t.2 u.2)

/-- The generic EM value: a direct limit of the finite-support copies lying in `K`
(Lemma 2.1, `directLimit_in_class`). -/
theorem FinPieces.limit_exists (F : FinPieces K) (I : Type u) [LinearOrder I] [Nonempty I] :
    ∃ L : DirectLimit (F.system I), IsLimitInClass K L :=
  directLimit_in_class K (F.system I) (fun _ => F.mem _) (fun _ => F.strong _)


/-- The chosen generic EM value. -/
noncomputable def FinPieces.limit (F : FinPieces K) (I : Type u) [LinearOrder I] [Nonempty I] :
    DirectLimit (F.system I) :=
  Classical.choose (F.limit_exists I)

theorem FinPieces.limit_spec (F : FinPieces K) (I : Type u) [LinearOrder I] [Nonempty I] :
    IsLimitInClass K (F.limit I) :=
  Classical.choose_spec (F.limit_exists I)

/-! ### Functoriality of the generic EM values (Section 2's `emMap`, ported to `FinPieces`) -/

section Functor

variable {F : FinPieces K}

noncomputable def gComponentMap {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    (s : {t : Finset I // t.Nonempty}) :
    (F.obj s.1.card.pred).carrier ↪[K.τ]
      (F.obj (imageIndex f s).1.card.pred).carrier :=
  F.map (indexCast f s)

theorem gComponentMap_strong {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    (s : {t : Finset I // t.Nonempty}) : K.Strong (gComponentMap (F := F) f s) :=
  F.strong (indexCast f s)

/-- The image of a system index, kept at the system’s own index type. -/
def gSystemImage {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) (s : (F.system I).ι) : (F.system J).ι :=
  ⟨s.1.map f.toEmbedding, Finset.map_nonempty.mpr s.2⟩

theorem gSystemImage_mono {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) {s t : (F.system I).ι}
    (h : (F.system I).rel s t) :
    (F.system J).rel (gSystemImage (F := F) f s) (gSystemImage (F := F) f t) :=
  Finset.map_subset_map.mpr h

noncomputable def gSystemComponent {I J : Type u} [LinearOrder I] [LinearOrder J]
    [Nonempty I] [Nonempty J] (f : I ↪o J) (s : (F.system I).ι) :
    ((F.system I).obj s).carrier ↪[K.τ]
      ((F.system J).obj (gSystemImage (F := F) f s)).carrier :=
  gComponentMap (F := F) f s

noncomputable def gSubstAt {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) (s : (F.system I).ι) :
    ((F.system I).obj s).carrier ↪[K.τ] (F.limit J).obj.carrier :=
  ((F.limit J).canon (gSystemImage (F := F) f s)).comp
    (gSystemComponent (F := F) f s)

theorem gSystemComponent_strong {I J : Type u} [LinearOrder I] [LinearOrder J]
    [Nonempty I] [Nonempty J] (f : I ↪o J) (s : (F.system I).ι) :
    K.Strong (gSystemComponent (F := F) f s) := by
  unfold gSystemComponent
  exact gComponentMap_strong (F := F) f s

theorem gSubstAt_strong {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) (s : (F.system I).ι) :
    K.Strong (gSubstAt (F := F) f s) :=
  K.strong_trans (gSystemComponent (F := F) f s)
    ((F.limit J).canon (gSystemImage (F := F) f s))
    (gSystemComponent_strong (F := F) f s)
    ((F.limit_spec J).2.1 (gSystemImage (F := F) f s))

theorem g_component_square {I J : Type u} [LinearOrder I] [LinearOrder J] (f : I ↪o J)
    {s t : {u : Finset I // u.Nonempty}} (h : s.1 ⊆ t.1) :
    (gComponentMap (F := F) f t).comp (F.map (placeSucc h s.2 t.2)) =
      (F.map (placeSucc (imageIndex_mono f h) (imageIndex f s).2 (imageIndex f t).2)).comp
        (gComponentMap (F := F) f s) := by
  have horder : (placeSucc h s.2 t.2).trans (indexCast f t) =
      (indexCast f s).trans
        (placeSucc (imageIndex_mono f h) (imageIndex f s).2 (imageIndex f t).2) :=
    placeSucc_map f h s.2 t.2
  unfold gComponentMap
  rw [← F.map_trans (placeSucc h s.2 t.2) (indexCast f t), horder, F.map_trans]

theorem g_system_component_square {I J : Type u} [LinearOrder I] [LinearOrder J]
    [Nonempty I] [Nonempty J] (f : I ↪o J) {s t : (F.system I).ι}
    (h : (F.system I).rel s t) :
    (gSystemComponent (F := F) f t).comp ((F.system I).map h) =
      ((F.system J).map (gSystemImage_mono (F := F) f h)).comp
        (gSystemComponent (F := F) f s) := by
  unfold gSystemComponent
  rw [show (F.system I).map h = F.map (placeSucc h s.2 t.2) from rfl]
  rw [show (F.system J).map (gSystemImage_mono (F := F) f h) =
      F.map (placeSucc (imageIndex_mono f h) (imageIndex f s).2 (imageIndex f t).2) from rfl]
  exact g_component_square (F := F) f h

theorem gSubstAt_compat {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) {s t : (F.system I).ι}
    (h : (F.system I).rel s t) :
    (gSubstAt (F := F) f t).comp ((F.system I).map h) = gSubstAt (F := F) f s := by
  ext x
  rw [gSubstAt, gSubstAt, Language.Embedding.comp_apply, Language.Embedding.comp_apply,
    Language.Embedding.comp_apply]
  have happ := congrFun (congrArg (⇑) (g_system_component_square (F := F) f h)) x
  rw [Language.Embedding.comp_apply, Language.Embedding.comp_apply] at happ
  rw [happ]
  have hcan := congrFun (congrArg (⇑)
      ((F.limit J).compat (gSystemImage_mono (F := F) f h)))
    (gSystemComponent (F := F) f s x)
  rw [Language.Embedding.comp_apply] at hcan
  exact hcan

/-- `E(f)`, induced by substitution on every finite-support copy. -/
noncomputable def gEmMap {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) :
    (F.limit I).obj.carrier ↪[K.τ] (F.limit J).obj.carrier :=
  Classical.choose ((F.limit_spec I).2.2 (F.limit J).obj
    (gSubstAt (F := F) f) (F.limit_spec J).1
    (gSubstAt_strong (F := F) f) (fun h => gSubstAt_compat (F := F) f h))

theorem gEmMap_strong {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) : K.Strong (gEmMap (F := F) f) :=
  (Classical.choose_spec ((F.limit_spec I).2.2 (F.limit J).obj
    (gSubstAt (F := F) f) (F.limit_spec J).1
    (gSubstAt_strong (F := F) f) (fun h => gSubstAt_compat (F := F) f h))).1

theorem gEmMap_canon {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) (s : (F.system I).ι) :
    (gEmMap (F := F) f).comp ((F.limit I).canon s) = gSubstAt (F := F) f s :=
  (Classical.choose_spec ((F.limit_spec I).2.2 (F.limit J).obj
    (gSubstAt (F := F) f) (F.limit_spec J).1
    (gSubstAt_strong (F := F) f) (fun h => gSubstAt_compat (F := F) f h))).2 s

/-- Two maps out of the limit that agree on every finite-support copy are equal. -/
theorem g_em_agreed {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (φ ψ : (F.limit I).obj.carrier ↪[K.τ] (F.limit J).obj.carrier)
    (h : ∀ s : (F.system I).ι,
      φ.comp ((F.limit I).canon s) = ψ.comp ((F.limit I).canon s)) :
    φ = ψ := by
  ext x
  obtain ⟨s, y, rfl⟩ := (F.limit I).joint x
  exact congrFun (congrArg (⇑) (h s)) y ▸ rfl

theorem gSystemImage_refl {I : Type u} [LinearOrder I] [Nonempty I]
    (s : (F.system I).ι) :
    gSystemImage (F := F) (OrderIso.refl I).toOrderEmbedding s = s := by
  apply Subtype.ext
  ext x
  simp [gSystemImage, OrderIso.refl_apply]


theorem gMap_cast {k l : ℕ} (h : k + 1 = l + 1) (x : (F.obj k).carrier) :
    F.map (Fin.castOrderIso h).toOrderEmbedding x =
      Eq.mp (congrArg (fun n => (F.obj n).carrier) (Nat.succ_injective h)) x := by
  have hkl : k = l := Nat.succ_injective h
  subst hkl
  have hid : (Fin.castOrderIso h).toOrderEmbedding = idEmb (α := Fin (k + 1)) := by
    ext i
    simp [idEmb]
  rw [hid, F.map_refl, eqMp_id, Language.Embedding.refl_apply]

theorem gSystemComponent_refl_apply {I : Type u} [LinearOrder I] [Nonempty I]
    (s : (F.system I).ι) (x : ((F.system I).obj s).carrier) :
    gSystemComponent (F := F) (OrderIso.refl I).toOrderEmbedding s x =
      Eq.mp (congrArg (fun i => ((F.system I).obj i).carrier)
        (gSystemImage_refl s).symm) x := by
  unfold gSystemComponent gComponentMap
  let hlen := (congrArg (fun n : ℕ => n.pred + 1)
    (imageIndex_card (OrderIso.refl I).toOrderEmbedding s)).symm
  have hmap := gMap_cast (F := F) hlen x
  exact hmap.trans (eqMp_proof_irrel x)

theorem gSubstAt_refl {I : Type u} [LinearOrder I] [Nonempty I]
    (s : (F.system I).ι) :
    gSubstAt (F := F) (OrderIso.refl I).toOrderEmbedding s =
      (F.limit I).canon s := by
  ext x
  rw [gSubstAt, Language.Embedding.comp_apply, gSystemComponent_refl_apply s x]
  exact canon_transport (F.limit I) (gSystemImage_refl s).symm x

theorem gEmMap_id {I : Type u} [LinearOrder I] [Nonempty I] :
    gEmMap (F := F) (OrderIso.refl I).toOrderEmbedding =
      Language.Embedding.refl K.τ (F.limit I).obj.carrier :=
  g_em_agreed (gEmMap (F := F) (OrderIso.refl I).toOrderEmbedding)
    (Language.Embedding.refl K.τ (F.limit I).obj.carrier)
    (fun s => by rw [gEmMap_canon, gSubstAt_refl, Language.Embedding.refl_comp])

theorem gSystemImage_trans {I J P : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder P]
    [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P)
    (s : (F.system I).ι) :
    gSystemImage (F := F) (f.trans g) s =
      gSystemImage (F := F) g (gSystemImage (F := F) f s) := by
  apply Subtype.ext
  ext x
  simp only [gSystemImage, Finset.mem_map, RelEmbedding.coe_toEmbedding, RelEmbedding.trans_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨f y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩



theorem gSystemComponent_apply {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I]
    [Nonempty J] (f : I ↪o J) (s : (F.system I).ι)
    (x : ((F.system I).obj s).carrier) :
    gSystemComponent (F := F) f s x =
      Eq.mp (congrArg (fun n => (F.obj n).carrier)
        (Nat.succ_injective (congrArg (fun n : ℕ => n.pred + 1)
          (imageIndex_card f s)).symm)) x := by
  unfold gSystemComponent gComponentMap
  exact gMap_cast (F := F)
    (congrArg (fun n : ℕ => n.pred + 1) (imageIndex_card f s)).symm x

theorem gSystemComponent_trans_apply {I J P : Type u} [LinearOrder I] [LinearOrder J]
    [LinearOrder P] [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P)
    (s : (F.system I).ι) (x : ((F.system I).obj s).carrier) :
    gSystemComponent (F := F) (f.trans g) s x =
      Eq.mp (congrArg (fun i => ((F.system P).obj i).carrier)
        (gSystemImage_trans (F := F) f g s).symm)
        (gSystemComponent (F := F) g (gSystemImage (F := F) f s)
          (gSystemComponent (F := F) f s x)) := by
  have hfg := gSystemComponent_apply (F := F) (f.trans g) s x
  have hf := gSystemComponent_apply (F := F) f s x
  have hg := gSystemComponent_apply (F := F) g (gSystemImage (F := F) f s)
    (gSystemComponent (F := F) f s x)
  rw [hfg, hg, hf]
  exact eqMp_triple _ _ _ _ x

theorem gSubstAt_trans {I J P : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder P]
    [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P)
    (s : (F.system I).ι) :
    gSubstAt (F := F) (f.trans g) s =
      (gSubstAt (F := F) g (gSystemImage (F := F) f s)).comp (gSystemComponent (F := F) f s) := by
  ext x
  rw [gSubstAt, gSubstAt, Language.Embedding.comp_apply, Language.Embedding.comp_apply,
    Language.Embedding.comp_apply, gSystemComponent_trans_apply]
  exact canon_transport (F.limit P) (gSystemImage_trans (F := F) f g s).symm
    (gSystemComponent (F := F) g (gSystemImage (F := F) f s)
      (gSystemComponent (F := F) f s x))

theorem gEmMap_comp {I J P : Type u} [LinearOrder I] [LinearOrder J] [LinearOrder P]
    [Nonempty I] [Nonempty J] [Nonempty P] (f : I ↪o J) (g : J ↪o P) :
    gEmMap (F := F) (f.trans g) = (gEmMap (F := F) g).comp (gEmMap (F := F) f) :=
  g_em_agreed (gEmMap (F := F) (f.trans g)) ((gEmMap (F := F) g).comp (gEmMap (F := F) f))
    (fun s => by
      ext x
      have hleft := congrFun (congrArg (⇑) (gEmMap_canon (F := F) (f.trans g) s)) x
      have htrans := congrFun (congrArg (⇑) (gSubstAt_trans (F := F) f g s)) x
      have hf := congrFun (congrArg (⇑) (gEmMap_canon (F := F) f s)) x
      have hg := congrFun (congrArg (⇑) (gEmMap_canon (F := F) g (gSystemImage (F := F) f s)))
        (gSystemComponent (F := F) f s x)
      simp only [Language.Embedding.comp_apply] at hleft htrans hf hg ⊢
      rw [hleft, htrans, hf]
      exact hg.symm)

end Functor


/-! ### Natural transformations of pieces induce natural maps of EM values

For the pair template of Lemma 8.3 the components `X ⊆ Y ⊆ L` are three piece functors with
natural strong maps between them; their EM values inherit strong maps, natural in the index
order. -/

/-- A natural family of strong embeddings between two piece functors. -/
structure PiecesHom (F G : FinPieces K) where
  app : ∀ k, (F.obj k).carrier ↪[K.τ] (G.obj k).carrier
  strong : ∀ k, K.Strong (app k)
  natural : ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)),
    (app l).comp (F.map e) = (G.map e).comp (app k)

namespace PiecesHom

variable {F G : FinPieces K} (η : PiecesHom F G)

/-- The cocone on `F.system I` given by `η` followed by the canonical maps of `G`'s value. -/
noncomputable def cocone (I : Type u) [LinearOrder I] [Nonempty I] (s : (F.system I).ι) :
    ((F.system I).obj s).carrier ↪[K.τ] (G.limit I).obj.carrier :=
  ((G.limit I).canon (show (G.system I).ι from s)).comp (η.app s.1.card.pred)

theorem cocone_strong (I : Type u) [LinearOrder I] [Nonempty I] (s : (F.system I).ι) :
    K.Strong (η.cocone I s) :=
  K.strong_trans _ _ (η.strong _) ((G.limit_spec I).2.1 _)

theorem cocone_compat (I : Type u) [LinearOrder I] [Nonempty I] {s t : (F.system I).ι}
    (h : (F.system I).rel s t) : (η.cocone I t).comp ((F.system I).map h) = η.cocone I s := by
  ext x
  show (G.limit I).canon t (η.app t.1.card.pred (F.map (placeSucc h s.2 t.2) x)) =
    (G.limit I).canon s (η.app s.1.card.pred x)
  have hnat : η.app t.1.card.pred (F.map (placeSucc h s.2 t.2) x) =
      G.map (placeSucc h s.2 t.2) (η.app s.1.card.pred x) := by
    exact congrFun (congrArg (⇑) (η.natural (placeSucc h s.2 t.2))) x
  rw [hnat]
  exact congrFun (congrArg (⇑) ((G.limit I).compat (i := s) (j := t) h))
    (η.app s.1.card.pred x)

/-- The induced map of EM values `F(I) → G(I)`. -/
noncomputable def limMap (I : Type u) [LinearOrder I] [Nonempty I] :
    (F.limit I).obj.carrier ↪[K.τ] (G.limit I).obj.carrier :=
  Classical.choose ((F.limit_spec I).2.2 (G.limit I).obj (η.cocone I) (G.limit_spec I).1
    (η.cocone_strong I) (fun h => η.cocone_compat I h))

theorem limMap_strong (I : Type u) [LinearOrder I] [Nonempty I] : K.Strong (η.limMap I) :=
  (Classical.choose_spec ((F.limit_spec I).2.2 (G.limit I).obj (η.cocone I) (G.limit_spec I).1
    (η.cocone_strong I) (fun h => η.cocone_compat I h))).1

theorem limMap_canon (I : Type u) [LinearOrder I] [Nonempty I] (s : (F.system I).ι) :
    (η.limMap I).comp ((F.limit I).canon s) = η.cocone I s :=
  (Classical.choose_spec ((F.limit_spec I).2.2 (G.limit I).obj (η.cocone I) (G.limit_spec I).1
    (η.cocone_strong I) (fun h => η.cocone_compat I h))).2 s


/-- The induced maps are natural in the index order: `η_J ∘ F(f) = G(f) ∘ η_I`. -/
theorem limMap_natural {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J]
    (f : I ↪o J) :
    (η.limMap J).comp (gEmMap (F := F) f) = (gEmMap (F := G) f).comp (η.limMap I) := by
  ext x
  obtain ⟨s, y, rfl⟩ := (F.limit I).joint x
  have h1 := congrFun (congrArg (⇑) (gEmMap_canon (F := F) f s)) y
  have h2 := congrFun (congrArg (⇑) (η.limMap_canon I s)) y
  have h3 := congrFun (congrArg (⇑) (gEmMap_canon (F := G) f s)) (η.app s.1.card.pred y)
  have h4 := congrFun (congrArg (⇑) (η.limMap_canon J (gSystemImage (F := F) f s)))
    (gSystemComponent (F := F) f s y)
  have hnat := congrFun (congrArg (⇑) (η.natural (indexCast f s))) y
  simp only [Language.Embedding.comp_apply] at h1 h2 h3 h4 ⊢
  rw [h1, h2]
  erw [h3]
  simp only [gSubstAt, Language.Embedding.comp_apply]
  erw [h4]
  simp only [cocone, Language.Embedding.comp_apply]
  exact congrArg ((G.limit J).canon _) hnat

end PiecesHom

/-- Section 2's pieces form a `FinPieces` functor; `F.system` is then Section 2's `emSystem`. -/
noncomputable def section2Pieces (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K] :
    FinPieces K where
  obj k := pieceSucc (K := K) k
  mem k := pieceSucc_mem k
  map e := arityMapSucc (K := K) e
  map_refl k := arityMapSucc_refl k
  map_trans e f := arityMapSucc_trans e f
  strong e := arityMapSucc_strong e

theorem section2Pieces_system (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K]
    (I : Type u) [LinearOrder I] [Nonempty I] :
    (section2Pieces K).system I = emSystem (K := K) I := rfl

end EM83
end AEC
