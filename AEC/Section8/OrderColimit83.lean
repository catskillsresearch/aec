module

public import AEC.Section8.Lemma83SampleLikeY

@[expose] public section

/-!
# Lemma 8.3: directed colimits of chart orders

For a functor of linear orders indexed by the nonempty finite subsets of `I` (along `⊆`),
the directed colimit `J_I` is a linear order with compatible order embeddings
`ι_s : G s ↪o J_I` covering it. Applied to the chart orders of the `X`/`Y`-pieces this gives
`F_X(I) ≅ F(J_I)` and `F_Y(I) ≅ F(Z_I)`.
-/

universe u

open Cardinal FirstOrder FirstOrder.Language

namespace AEC

namespace OCol83

variable {I : Type u} [LinearOrder I]

/-- Nonempty finite supports. -/
abbrev Idx (I : Type u) [LinearOrder I] := {s : Finset I // s.Nonempty}

/-- Union of supports. -/
def up (s t : Idx I) : Idx I := ⟨s.1 ∪ t.1, s.2.mono Finset.subset_union_left⟩

/-- Position of a point of a support in its successor-length enumeration. -/
noncomputable def pos (s : Idx I) (i : I) (hi : i ∈ s.1) : Fin (s.1.card.pred + 1) :=
  Fin.cast (Nat.succ_pred (Finset.card_pos.mpr s.2).ne').symm ((s.1.orderIsoOfFin rfl).symm ⟨i, hi⟩)

theorem pos_place {s t : Idx I} (hst : s.1 ⊆ t.1) (i : I) (hi : i ∈ s.1) :
    placeSucc hst s.2 t.2 (pos s i hi) = pos t i (hst hi) := by
  apply Fin.ext
  simp [placeSucc, placeEmb_apply, pos, Finset.orderEmbOfFin]

/-- Positions are preserved by the cast along the image of an index under an order embedding. -/
theorem pos_indexCast {I' : Type u} [LinearOrder I'] (f : I ↪o I') (s : Idx I) (i : I) (hi : i ∈ s.1) :
    indexCast f s (pos s i hi) = pos (imageIndex f s) (f i) (Finset.mem_map_of_mem f.toEmbedding hi) := by
  apply Fin.ext
  have key : ((imageIndex f s).1.orderIsoOfFin rfl).symm ⟨f i, Finset.mem_map_of_mem f.toEmbedding hi⟩ =
      Fin.cast (imageIndex_card f s).symm ((s.1.orderIsoOfFin rfl).symm ⟨i, hi⟩) := by
    rw [OrderIso.symm_apply_eq]
    apply Subtype.ext
    have h1 := orderEmbOfFin_orderMap f s.1 ((s.1.orderIsoOfFin rfl).symm ⟨i, hi⟩)
    have h2 : s.1.orderEmbOfFin rfl ((s.1.orderIsoOfFin rfl).symm ⟨i, hi⟩) = i := by
      rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]
    rw [h2] at h1
    rw [Finset.coe_orderIsoOfFin_apply]
    exact h1.symm
  simp only [indexCast, pos, Fin.val_cast, OrderIso.coe_toOrderEmbedding, Fin.castOrderIso_apply, key]

theorem pos_strictMono (s : Idx I) (i i' : I) (hi : i ∈ s.1) (hi' : i' ∈ s.1) (h : i < i') :
    pos s i hi < pos s i' hi' := by
  have : (s.1.orderIsoOfFin rfl).symm ⟨i, hi⟩ < (s.1.orderIsoOfFin rfl).symm ⟨i', hi'⟩ :=
    (s.1.orderIsoOfFin rfl).symm.strictMono (show (⟨i, hi⟩ : s.1) < ⟨i', hi'⟩ from h)
  exact this


variable {G : Idx I → Type u} [∀ s, LinearOrder (G s)]
  (φ : ∀ {s t : Idx I}, s.1 ⊆ t.1 → G s ↪o G t)

theorem le_iff_push (hcomp : ∀ {s t u : Idx I} (h1 : s.1 ⊆ t.1) (h2 : t.1 ⊆ u.1) (x : G s),
      φ (h1.trans h2) x = φ h2 (φ h1 x))
    {s t u w : Idx I} (hs : s.1 ⊆ u.1) (ht : t.1 ⊆ u.1) (huw : u.1 ⊆ w.1) (a : G s) (b : G t) :
    φ (hs.trans huw) a ≤ φ (ht.trans huw) b ↔ φ hs a ≤ φ ht b := by
  rw [hcomp hs huw, hcomp ht huw]
  exact (φ huw).le_iff_le

theorem le_indep (hcomp : ∀ {s t u : Idx I} (h1 : s.1 ⊆ t.1) (h2 : t.1 ⊆ u.1) (x : G s),
      φ (h1.trans h2) x = φ h2 (φ h1 x))
    {s t u u' : Idx I} (hs : s.1 ⊆ u.1) (ht : t.1 ⊆ u.1) (hs' : s.1 ⊆ u'.1) (ht' : t.1 ⊆ u'.1)
    (a : G s) (b : G t) : φ hs a ≤ φ ht b ↔ φ hs' a ≤ φ ht' b :=
  (le_iff_push φ hcomp (w := up u u') hs ht Finset.subset_union_left a b).symm.trans
    (le_iff_push φ hcomp (w := up u u') hs' ht' Finset.subset_union_right a b)

theorem eq_indep (hcomp : ∀ {s t u : Idx I} (h1 : s.1 ⊆ t.1) (h2 : t.1 ⊆ u.1) (x : G s),
      φ (h1.trans h2) x = φ h2 (φ h1 x))
    {s t u u' : Idx I} (hs : s.1 ⊆ u.1) (ht : t.1 ⊆ u.1) (hs' : s.1 ⊆ u'.1) (ht' : t.1 ⊆ u'.1)
    (a : G s) (b : G t) : φ hs a = φ ht b ↔ φ hs' a = φ ht' b := by
  rw [le_antisymm_iff, le_antisymm_iff, le_indep φ hcomp hs ht hs' ht',
    le_indep φ hcomp ht hs ht' hs']

/-- Canonical comparison at the union of the supports. -/
def leS (a b : Σ s, G s) : Prop :=
  φ (t := up a.1 b.1) Finset.subset_union_left a.2 ≤
    φ (t := up a.1 b.1) Finset.subset_union_right b.2

/-- Canonical identification at the union of the supports. -/
def eqS (a b : Σ s, G s) : Prop :=
  φ (t := up a.1 b.1) Finset.subset_union_left a.2 =
    φ (t := up a.1 b.1) Finset.subset_union_right b.2

variable (hcomp : ∀ {s t u : Idx I} (h1 : s.1 ⊆ t.1) (h2 : t.1 ⊆ u.1) (x : G s),
      φ (h1.trans h2) x = φ h2 (φ h1 x))
include hcomp

theorem leS_iff {a b : Σ s, G s} {u : Idx I} (ha : a.1.1 ⊆ u.1) (hb : b.1.1 ⊆ u.1) :
    leS φ a b ↔ φ ha a.2 ≤ φ hb b.2 :=
  le_indep φ hcomp _ _ ha hb a.2 b.2

theorem eqS_iff {a b : Σ s, G s} {u : Idx I} (ha : a.1.1 ⊆ u.1) (hb : b.1.1 ⊆ u.1) :
    eqS φ a b ↔ φ ha a.2 = φ hb b.2 :=
  eq_indep φ hcomp _ _ ha hb a.2 b.2

/-- The colimit setoid. -/
def setoid : Setoid (Σ s, G s) where
  r := eqS φ
  iseqv := by
    refine ⟨fun a => rfl, fun {a b} h => ?_, fun {a b c} hab hbc => ?_⟩
    · exact ((eqS_iff φ hcomp (u := up a.1 b.1) Finset.subset_union_right
        Finset.subset_union_left).2 ((eqS_iff φ hcomp _ _).1 h).symm)
    · let w : Idx I := up (up a.1 b.1) c.1
      have ha : a.1.1 ⊆ w.1 := fun x hx => by simp [w, up, hx]
      have hb : b.1.1 ⊆ w.1 := fun x hx => by simp [w, up, hx]
      have hc : c.1.1 ⊆ w.1 := fun x hx => by simp [w, up, hx]
      exact (eqS_iff φ hcomp ha hc).2 (((eqS_iff φ hcomp ha hb).1 hab).trans
        ((eqS_iff φ hcomp hb hc).1 hbc))


/-- **The directed colimit `J_I` of the orders.** -/
def Col : Type u := Quotient (setoid φ hcomp)

/-- The colimit order. -/
def leC : Col φ hcomp → Col φ hcomp → Prop :=
  Quotient.lift₂ (leS φ) fun a b a' b' haa hbb => by
    let w : Idx I := up (up a.1 b.1) (up a'.1 b'.1)
    have ha : a.1.1 ⊆ w.1 := fun x hx => by simp [w, up, hx]
    have hb : b.1.1 ⊆ w.1 := fun x hx => by simp [w, up, hx]
    have ha' : a'.1.1 ⊆ w.1 := fun x hx => by simp [w, up, hx]
    have hb' : b'.1.1 ⊆ w.1 := fun x hx => by simp [w, up, hx]
    have e1 := (eqS_iff φ hcomp ha ha').1 haa
    have e2 := (eqS_iff φ hcomp hb hb').1 hbb
    apply propext
    rw [leS_iff φ hcomp ha hb, leS_iff φ hcomp ha' hb', e1, e2]

noncomputable instance instLinearOrderCol : LinearOrder (Col φ hcomp) :=
  { le := leC φ hcomp
    le_refl := fun x => Quotient.inductionOn x fun a => le_refl _
    le_trans := fun x y z => Quotient.inductionOn₃ x y z fun a b c hab hbc => by
      let w : Idx I := up (up a.1 b.1) c.1
      have ha : a.1.1 ⊆ w.1 := fun x hx => by simp [w, up, hx]
      have hb : b.1.1 ⊆ w.1 := fun x hx => by simp [w, up, hx]
      have hc : c.1.1 ⊆ w.1 := fun x hx => by simp [w, up, hx]
      exact (leS_iff φ hcomp ha hc).2 (((leS_iff φ hcomp ha hb).1 hab).trans
        ((leS_iff φ hcomp hb hc).1 hbc))
    le_antisymm := fun x y => Quotient.inductionOn₂ x y fun a b hab hba =>
      Quotient.sound (le_antisymm hab ((leS_iff φ hcomp (u := up a.1 b.1)
        Finset.subset_union_right Finset.subset_union_left).1 hba))
    le_total := fun x y => Quotient.inductionOn₂ x y fun a b =>
      (le_total (φ (t := up a.1 b.1) Finset.subset_union_left a.2)
        (φ (t := up a.1 b.1) Finset.subset_union_right b.2)).imp id
        (fun h => (leS_iff φ hcomp (u := up a.1 b.1) Finset.subset_union_right
          Finset.subset_union_left).2 h)
    toDecidableLE := Classical.decRel _ }

instance instNonemptyCol [Nonempty I] [∀ s, Nonempty (G s)] : Nonempty (Col φ hcomp) :=
  let s0 : Idx I := ⟨{Classical.arbitrary I}, Finset.singleton_nonempty _⟩
  ⟨Quotient.mk _ ⟨s0, Classical.arbitrary _⟩⟩

variable (hid : ∀ (s : Idx I) (x : G s), φ (Finset.Subset.refl s.1) x = x)
include hid

/-- The colimit injections `ι_s : G s ↪o J_I`. -/
noncomputable def iota (s : Idx I) : G s ↪o Col φ hcomp :=
  OrderEmbedding.ofMapLEIff (fun x => Quotient.mk (setoid φ hcomp) ⟨s, x⟩) fun x y => by
    show leS φ ⟨s, x⟩ ⟨s, y⟩ ↔ x ≤ y
    rw [leS_iff φ hcomp (u := s) (Finset.Subset.refl _) (Finset.Subset.refl _), hid, hid]

theorem iota_comp {s t : Idx I} (hst : s.1 ⊆ t.1) (x : G s) :
    iota φ hcomp hid t (φ hst x) = iota φ hcomp hid s x :=
  Quotient.sound ((eqS_iff φ hcomp (u := t) (Finset.Subset.refl _) hst).2 (hid t _))

/-- **Compatibility of the colimit injections.** -/
theorem iota_compat {s t : Idx I} (hst : s.1 ⊆ t.1) :
    (φ hst).trans (iota φ hcomp hid t) = iota φ hcomp hid s := by
  ext x
  exact iota_comp φ hcomp hid hst x

theorem iota_surj (j : Col φ hcomp) : ∃ s x, iota φ hcomp hid s x = j :=
  Quotient.inductionOn j fun a => ⟨a.1, a.2, rfl⟩

/-- **Finitely many points of `J_I` lie in one `ι_u`.** -/
theorem exists_common [Nonempty I] {m : ℕ} (j : Fin m → Col φ hcomp) :
    ∃ (u : Idx I) (x : Fin m → G u), ∀ i, iota φ hcomp hid u (x i) = j i := by
  classical
  choose s x hx using fun i => iota_surj φ hcomp hid (j i)
  let s0 : Idx I := ⟨{Classical.arbitrary I}, Finset.singleton_nonempty _⟩
  let u : Idx I := ⟨(Finset.univ.sup fun i => (s i).1) ∪ s0.1, s0.2.mono Finset.subset_union_right⟩
  have hsub : ∀ i, (s i).1 ⊆ u.1 := fun i y hy =>
    Finset.mem_union_left _ (Finset.mem_sup.2 ⟨i, Finset.mem_univ _, hy⟩)
  exact ⟨u, fun i => φ (hsub i) (x i), fun i => (iota_comp φ hcomp hid (hsub i) (x i)).trans (hx i)⟩

/-- **The colimit injections cover `F(J_I)`.** -/
theorem cover {K : AbstractElementaryClass.{u}} (E : OrderPresentation K) [Nonempty I]
    [∀ s, Nonempty (G s)] (y : (E.obj (Col φ hcomp)).carrier) :
    ∃ s z, E.map (iota φ hcomp hid s) z = y := by
  obtain ⟨n, a, p, -, rfl⟩ := Lab83.exists_label_value (E := E) y
  obtain ⟨u, x, hx⟩ := exists_common φ hcomp hid p
  refine ⟨u, Lab83.labFun a (fun k => E.skeleton (x k)), ?_⟩
  rw [← Lab83.labFun_map]
  congr 1
  funext k
  rw [E.skeleton_natural, hx]



/-- **Universal property of `J_I`**: compatible order embeddings `κ_s : G s ↪o T` factor
through a unique-on-generators order embedding `J_I ↪o T`. -/
noncomputable def lift {T : Type*} [LinearOrder T] (κ : ∀ s, G s ↪o T)
    (hκ : ∀ {s t : Idx I} (hst : s.1 ⊆ t.1) (x : G s), κ t (φ hst x) = κ s x) :
    Col φ hcomp ↪o T :=
  OrderEmbedding.ofMapLEIff
    (Quotient.lift (fun a : Σ s, G s => κ a.1 a.2) fun a b hab => by
      have h1 := (eqS_iff φ hcomp (u := up a.1 b.1) Finset.subset_union_left
        Finset.subset_union_right).1 hab
      exact (hκ _ a.2).symm.trans ((congrArg _ h1).trans (hκ _ b.2)))
    fun x y => Quotient.inductionOn₂ x y fun a b => by
      show κ a.1 a.2 ≤ κ b.1 b.2 ↔ leS φ a b
      rw [← hκ (t := up a.1 b.1) Finset.subset_union_left a.2,
        ← hκ (t := up a.1 b.1) Finset.subset_union_right b.2]
      exact (κ _).le_iff_le

theorem lift_iota {T : Type*} [LinearOrder T] (κ : ∀ s, G s ↪o T)
    (hκ : ∀ {s t : Idx I} (hst : s.1 ⊆ t.1) (x : G s), κ t (φ hst x) = κ s x)
    (s : Idx I) (x : G s) : lift φ hcomp κ hκ (iota φ hcomp hid s x) = κ s x := rfl

omit hid in
/-- **Size of the colimit order**: if every `G s` has size at most `κ`, then
`#J_I ≤ #(finite supports of I) · κ`. -/
theorem card_col_le (κ : Cardinal.{u}) (hG : ∀ s, #(G s) ≤ κ) :
    #(Col φ hcomp) ≤ #(Idx I) * κ := by
  refine (Cardinal.mk_le_of_surjective (Quotient.mk_surjective (s := setoid φ hcomp))).trans ?_
  rw [Cardinal.mk_sigma]
  exact (Cardinal.sum_le_sum _ _ hG).trans (Cardinal.sum_const' _ _).le

/-- **`I` embeds in the colimit order through coherent coordinates**: if each `G s` carries
coordinates `cs s i` (`i ∈ s`), strictly increasing in `i` and moved by the transition maps
to the coordinates of the same point, then `i ↦ ι_{{i}} (cs {i} i)` is an order embedding
`I ↪o J_I`. -/
theorem exists_coord_embedding
    (cs : ∀ (s : Idx I) (i : I), i ∈ s.1 → G s)
    (hcs : ∀ {s t : Idx I} (hst : s.1 ⊆ t.1) (i : I) (hi : i ∈ s.1),
      φ hst (cs s i hi) = cs t i (hst hi))
    (hmono : ∀ (s : Idx I) (i i' : I) (hi : i ∈ s.1) (hi' : i' ∈ s.1),
      i < i' → cs s i hi < cs s i' hi') :
    ∃ g : I ↪o Col φ hcomp, ∀ (s : Idx I) (i : I) (hi : i ∈ s.1),
      g i = iota φ hcomp hid s (cs s i hi) := by
  classical
  let sg : I → Idx I := fun i => ⟨{i}, Finset.singleton_nonempty i⟩
  let g0 : I → Col φ hcomp := fun i => iota φ hcomp hid (sg i) (cs (sg i) i (Finset.mem_singleton_self i))
  have hg0 : ∀ (s : Idx I) (i : I) (hi : i ∈ s.1), g0 i = iota φ hcomp hid s (cs s i hi) := by
    intro s i hi
    have hsub : (sg i).1 ⊆ s.1 := Finset.singleton_subset_iff.2 hi
    exact (iota_comp φ hcomp hid hsub _).symm.trans (by rw [hcs])
  have hlt : StrictMono g0 := by
    intro i i' hii'
    let u : Idx I := up (sg i) (sg i')
    have hi : i ∈ u.1 := by simp [u, up, sg]
    have hi' : i' ∈ u.1 := by simp [u, up, sg]
    rw [hg0 u i hi, hg0 u i' hi']
    exact (iota φ hcomp hid u).strictMono (hmono u i i' hi hi' hii')
  exact ⟨OrderEmbedding.ofStrictMono g0 hlt, fun s i hi => hg0 s i hi⟩


end OCol83

namespace OCol83

section Natural

variable {H : ℕ → Type u} [∀ k, LinearOrder (H k)]
  (h : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) → H k ↪o H l)
  (hid : ∀ k (p : H k), h (idEmb (α := Fin (k + 1))) p = p)
  (hcomp : ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1))
    (p : H k), h (e.trans f) p = h f (h e p))

/-- The transition maps of the chart orders over the supports of `I`. -/
noncomputable def phiH (I : Type u) [LinearOrder I] :
    ∀ {s t : Idx I}, s.1 ⊆ t.1 → H s.1.card.pred ↪o H t.1.card.pred :=
  fun {s t} hst => h (placeSucc hst s.2 t.2)

include hcomp in
theorem phiH_comp (I : Type u) [LinearOrder I] {s t u : Idx I} (h1 : s.1 ⊆ t.1) (h2 : t.1 ⊆ u.1)
    (x : H s.1.card.pred) : phiH h I (h1.trans h2) x = phiH h I h2 (phiH h I h1 x) := by
  show h (placeSucc (h1.trans h2) s.2 u.2) x = _
  rw [placeSucc_trans h1 h2 s.2 t.2 u.2]
  exact hcomp _ _ x

include hid in
theorem phiH_id (I : Type u) [LinearOrder I] (s : Idx I) (x : H s.1.card.pred) :
    phiH h I (Finset.Subset.refl s.1) x = x := by
  show h (placeSucc (Finset.Subset.refl s.1) s.2 s.2) x = x
  rw [placeSucc_refl s.1 s.2]
  exact hid _ x

/-- **Naturality of the chart colimit in `I`**: an order embedding `f : I ↪o I'` induces an
order embedding `J_f : J_I ↪o J_I'` sending `ι_s x` to `ι_{f(s)} (h (indexCast f s) x)`. -/
noncomputable def colMap {I I' : Type u} [LinearOrder I] [LinearOrder I'] (f : I ↪o I') :
    Col (phiH h I) (phiH_comp h hcomp I) ↪o Col (phiH h I') (phiH_comp h hcomp I') :=
  lift (phiH h I) (phiH_comp h hcomp I)
    (fun s => (h (indexCast f s)).trans
      (iota (phiH h I') (phiH_comp h hcomp I') (phiH_id h hid I') (imageIndex f s)))
    (fun {s t} hst x => by
      show iota (phiH h I') (phiH_comp h hcomp I') (phiH_id h hid I') (imageIndex f t)
          (h (indexCast f t) (h (placeSucc hst s.2 t.2) x)) =
        iota (phiH h I') (phiH_comp h hcomp I') (phiH_id h hid I') (imageIndex f s)
          (h (indexCast f s) x)
      have e1 := (hcomp (placeSucc hst s.2 t.2) (indexCast f t) x).symm.trans
        ((congrArg (fun e => h e x) (placeSucc_map f hst s.2 t.2)).trans (hcomp _ _ x))
      refine (congrArg _ e1).trans ?_
      exact iota_comp (phiH h I') (phiH_comp h hcomp I') (phiH_id h hid I')
        (s := imageIndex f s) (t := imageIndex f t)
        (Finset.map_subset_map.mpr hst) _)

theorem colMap_iota {I I' : Type u} [LinearOrder I] [LinearOrder I'] (f : I ↪o I') (s : Idx I)
    (x : H s.1.card.pred) :
    colMap h hid hcomp f (iota (phiH h I) (phiH_comp h hcomp I) (phiH_id h hid I) s x) =
      iota (phiH h I') (phiH_comp h hcomp I') (phiH_id h hid I') (imageIndex f s)
        (h (indexCast f s) x) := rfl

end Natural

end OCol83


variable {K : AbstractElementaryClass.{u}}

/-- **`F_X(I) ≅ F(J_I)`**: in the pair template over `X`- and `Y`-sample-like structures, the
EM value of the `X`-pieces at every `I` is strongly and bijectively `τ`-isomorphic to `F(J_I)`,
where `J_I` is the directed colimit of the chart orders `H_(|s|-1)` (`s ⊆ I` finite) along the
chart transition maps. -/
theorem infra_83_pairMS2_X_hull_eq_FJ (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N)),
      ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J)
          (m : (((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).limit I).obj.carrier ↪[K.τ] (P.E.obj J).carrier)),
          K.Strong m ∧ Function.Bijective m ∧ Nonempty (I ↪o J) ∧
          #J ≤ #(Finset I) * ls K := by
  obtain ⟨c, hc, hcoh, hXs, ch, h, hid, hcomp, hjc, hL⟩ := infra_83_pairMS2_X_limit_of_cocone P Pr
  refine ⟨c, hc, hcoh, hXs, fun I _ _ => ?_⟩
  let φ : ∀ {s t : OCol83.Idx I}, s.1 ⊆ t.1 → (ch s.1.card.pred).H ↪o (ch t.1.card.pred).H :=
    fun {s t} hst => h (placeSucc hst s.2 t.2)
  have hcφ : ∀ {s t u : OCol83.Idx I} (h1 : s.1 ⊆ t.1) (h2 : t.1 ⊆ u.1) (x : (ch s.1.card.pred).H),
      φ (h1.trans h2) x = φ h2 (φ h1 x) := by
    intro s t u h1 h2 x
    show h (placeSucc (h1.trans h2) s.2 u.2) x = _
    rw [placeSucc_trans h1 h2 s.2 t.2 u.2]
    exact hcomp _ _ x
  have hiφ : ∀ (s : OCol83.Idx I) (x : (ch s.1.card.pred).H), φ (Finset.Subset.refl s.1) x = x := by
    intro s x
    show h (placeSucc (Finset.Subset.refl s.1) s.2 s.2) x = x
    rw [placeSucc_refl s.1 s.2]
    exact hid _ x
  obtain ⟨m, hm, hb⟩ := hL I (OCol83.Col φ hcφ) (fun s => OCol83.iota φ hcφ hiφ s)
    (fun {s t} hst => OCol83.iota_compat φ hcφ hiφ hst) (fun y => OCol83.cover φ hcφ hiφ P.E y)
  obtain ⟨g, -⟩ := OCol83.exists_coord_embedding φ hcφ hiφ
    (fun s i hi => (ch s.1.card.pred).j (OCol83.pos s i hi))
    (fun {s t} hst i hi => by
      show h (placeSucc hst s.2 t.2) _ = _
      rw [hjc, OCol83.pos_place])
    (fun s i i' hi hi' hii' => (ch s.1.card.pred).mono (OCol83.pos_strictMono s i i' hi hi' hii'))
  have hpc : ∀ k, #((ch k).H) ≤ ls K := by
    intro k
    have hsurj : Function.Surjective (fun t : (LS83.pairLangR P.E).Term (Fin (k + 1) × Fin 1) =>
        (Quotient.mk _ t : ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).obj k).carrier)) := fun x => Quotient.exists_rep x
    refine P.E.card_lower.trans ?_
    refine (Cardinal.mk_congr (Equiv.ofBijective _ (ch k).bij)).symm.le.trans ?_
    exact (Cardinal.mk_le_of_surjective hsurj).trans
      ((Cardinal.mk_le_of_injective (sigma_mk_injective (β := fun n => (LS83.pairLangR P.E).Term (Fin n × Fin 1)) (i := k + 1))).trans
        (Hull83.card_bundle_terms_le 1 (LS83.pairLangR_functions_le P.E)))
  have hcard := OCol83.card_col_le φ hcφ (ls K) (fun s => hpc s.1.card.pred)
  exact ⟨OCol83.Col φ hcφ, inferInstance, inferInstance, m, hm, hb, ⟨g⟩,
    hcard.trans (mul_le_mul_left (Cardinal.mk_subtype_le _) _)⟩

/-- **`F_Y(I) ≅ F(Z_I)`**: in the pair template over `X`- and `Y`-sample-like structures, the
EM value of the `Y`-pieces at every `I` is strongly and bijectively `τ`-isomorphic to `F(Z_I)`,
where `Z_I` is the directed colimit of the chart orders `H_(|s|-1)` (`s ⊆ I` finite) along the
chart transition maps. -/
theorem infra_83_pairMS2_Y_hull_eq_FZ (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) (fun N _ => pairMAdmittedS2 P.E Pr.n N)),
      ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J)
          (m : (((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).limit I).obj.carrier ↪[K.τ] (P.E.obj J).carrier)),
          K.Strong m ∧ Function.Bijective m ∧ Nonempty (I ↪o J) ∧
          #J ≤ #(Finset I) * ls K := by
  obtain ⟨c, hc, hcoh, hXs, ch, h, hid, hcomp, hjc, hL⟩ := infra_83_pairMS2_Y_limit_of_cocone P Pr
  refine ⟨c, hc, hcoh, hXs, fun I _ _ => ?_⟩
  let φ : ∀ {s t : OCol83.Idx I}, s.1 ⊆ t.1 → (ch s.1.card.pred).H ↪o (ch t.1.card.pred).H :=
    fun {s t} hst => h (placeSucc hst s.2 t.2)
  have hcφ : ∀ {s t u : OCol83.Idx I} (h1 : s.1 ⊆ t.1) (h2 : t.1 ⊆ u.1) (x : (ch s.1.card.pred).H),
      φ (h1.trans h2) x = φ h2 (φ h1 x) := by
    intro s t u h1 h2 x
    show h (placeSucc (h1.trans h2) s.2 u.2) x = _
    rw [placeSucc_trans h1 h2 s.2 t.2 u.2]
    exact hcomp _ _ x
  have hiφ : ∀ (s : OCol83.Idx I) (x : (ch s.1.card.pred).H), φ (Finset.Subset.refl s.1) x = x := by
    intro s x
    show h (placeSucc (Finset.Subset.refl s.1) s.2 s.2) x = x
    rw [placeSucc_refl s.1 s.2]
    exact hid _ x
  obtain ⟨m, hm, hb⟩ := hL I (OCol83.Col φ hcφ) (fun s => OCol83.iota φ hcφ hiφ s)
    (fun {s t} hst => OCol83.iota_compat φ hcφ hiφ hst) (fun y => OCol83.cover φ hcφ hiφ P.E y)
  obtain ⟨g, -⟩ := OCol83.exists_coord_embedding φ hcφ hiφ
    (fun s i hi => (ch s.1.card.pred).j (OCol83.pos s i hi))
    (fun {s t} hst i hi => by
      show h (placeSucc hst s.2 t.2) _ = _
      rw [hjc, OCol83.pos_place])
    (fun s i i' hi hi' hii' => (ch s.1.card.pred).mono (OCol83.pos_strictMono s i i' hi hi' hii'))
  have hpc : ∀ k, #((ch k).H) ≤ ls K := by
    intro k
    have hsurj : Function.Surjective (fun t : (LS83.pairLangM2 P.E Pr.n).Term (Fin (k + 1) × Fin 2) =>
        (Quotient.mk _ t : ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).obj k).carrier)) := fun x => Quotient.exists_rep x
    refine P.E.card_lower.trans ?_
    refine (Cardinal.mk_congr (Equiv.ofBijective _ (ch k).bij)).symm.le.trans ?_
    exact (Cardinal.mk_le_of_surjective hsurj).trans
      ((Cardinal.mk_le_of_injective (sigma_mk_injective (β := fun n => (LS83.pairLangM2 P.E Pr.n).Term (Fin n × Fin 2)) (i := k + 1))).trans
        (Hull83.card_bundle_terms_le 2 (LS83.pairLangM2_functions_le P.E Pr.n)))
  have hcard := OCol83.card_col_le φ hcφ (ls K) (fun s => hpc s.1.card.pred)
  exact ⟨OCol83.Col φ hcφ, inferInstance, inferInstance, m, hm, hb, ⟨g⟩,
    hcard.trans (mul_le_mul_left (Cardinal.mk_subtype_le _) _)⟩


/-- Parametric form of `infra_83_pairMS2_X_hull_natural`: for any coherent colors `c` (with the `θ`/`ρ` facts) and
any `hXs`. -/
theorem infra_83_pairMS2_X_hull_natural_c (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hθ : ∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin 3),
        (thetaM P.E Pr.n i).relabel (fun _ => (a, i)) ∈ c m hm)
      (hρ : ∀ (m : ℕ) (hm : 0 < m) (a b : Fin m), a < b → ∀ i : Fin 3,
        (rhoM P.E Pr.n i).relabel ![(a, i), (b, i)] ∈ c m hm)
      (hXs : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N)) :
    ∃ (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).obj k) k)
      (h : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) → (ch k).H ↪o (ch l).H)
      (hid : ∀ k (p : (ch k).H), h (idEmb (α := Fin (k + 1))) p = p)
      (hcomp : ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1))
        (p : (ch k).H), h (e.trans f) p = h f (h e p))
      (m : ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).limit I).obj.carrier ↪[K.τ]
          (P.E.obj (OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I))).carrier),
      (∀ k (a : Fin (k + 1)), (ch k).ε (Quotient.mk _ (Term.var (a, (0 : Fin 1))) : ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).obj k).carrier) = P.E.skeleton ((ch k).j a)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (m I) ∧ Function.Bijective (m I)) ∧
      (∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') x,
        m I' (EM83.gEmMap (F := Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs) f x) =
          P.E.map (OCol83.colMap h hid hcomp f) (m I x)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        OCol83.colMap h hid hcomp (OrderIso.refl I).toOrderEmbedding = (OrderIso.refl _).toOrderEmbedding) ∧
      (∀ (I I' I'' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I']
        [LinearOrder I''] [Nonempty I''] (f : I ↪o I') (g : I' ↪o I''),
        OCol83.colMap h hid hcomp (f.trans g) =
          (OCol83.colMap h hid hcomp f).trans (OCol83.colMap h hid hcomp g)) ∧
      ∃ g : ∀ (I : Type u) [LinearOrder I], I ↪o OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I),
        (∀ (I : Type u) [LinearOrder I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1),
          g I i = OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s
            ((ch s.1.card.pred).j (OCol83.pos s i hi))) ∧
        (∀ (I I' : Type u) [LinearOrder I] [LinearOrder I'] (f : I ↪o I') (i : I),
          OCol83.colMap h hid hcomp f (g I i) = g I' (f i)) ∧
        (∀ (I : Type u) [LinearOrder I] [Nonempty I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1)
          (x : ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).obj s.1.card.pred).carrier),
          (ch s.1.card.pred).ε x = P.E.skeleton ((ch s.1.card.pred).j (OCol83.pos s i hi)) →
          m I (((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).limit I).canon s x) = P.E.skeleton (g I i)) ∧
      ∀ (I : Type u) [LinearOrder I],
        #(OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I)) ≤ #(Finset I) * ls K := by
  obtain ⟨ch, h, hid, hcomp, hjc, η, hv, happ, -, hlim⟩ := infra_83_pairMS2_X_F_pieces_c P Pr c hc hcoh hθ hρ hXs
  have hco : ∀ (I : Type u) [LinearOrder I] [Nonempty I], ∃ m' : ((orderPieces83 P.E (fun k => (ch k).H) h hid hcomp).limit I).obj.carrier ↪[K.τ]
        (P.E.obj (OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I))).carrier,
      K.Strong m' ∧ Function.Bijective m' ∧ ∀ s, m'.comp
        (((orderPieces83 P.E (fun k => (ch k).H) h hid hcomp).limit I).canon s) =
        P.E.map (OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s) :=
    fun I _ _ => infra_83_orderPieces_cocone_bij P.E I _ _
      (fun {s t} hst => OCol83.iota_compat _ _ _ hst) (fun y => OCol83.cover _ _ _ P.E y)
  refine ⟨ch, h, hid, hcomp,
    fun I _ _ => (Classical.choose (hco I)).comp (η.limMap I),
    hv,
    fun I _ _ => ⟨K.strong_trans _ _ (hlim I).2 (Classical.choose_spec (hco I)).1,
      (Classical.choose_spec (hco I)).2.1.comp (hlim I).1⟩, ?_⟩
  have hsq : ∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') x,
      (Classical.choose (hco I')).comp (η.limMap I') (EM83.gEmMap (F := Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs) f x) =
        P.E.map (OCol83.colMap h hid hcomp f) ((Classical.choose (hco I)).comp (η.limMap I) x) := by
    intro I I' _ _ _ _ f x
    obtain ⟨s, y, rfl⟩ := ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).limit I).joint x
    have e1 := congrFun (congrArg (⇑) (EM83.gEmMap_canon (F := Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs) f s)) y
    have e2 : ∀ (J : Type u) [LinearOrder J] [Nonempty J] t z,
        η.limMap J (((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).limit J).canon t z) =
          ((orderPieces83 P.E (fun k => (ch k).H) h hid hcomp).limit J).canon t (η.app _ z) :=
      fun J _ _ t z => congrFun (congrArg (⇑) (η.limMap_canon J t)) z
    have e3 : ∀ (J : Type u) [LinearOrder J] [Nonempty J] t w,
        Classical.choose (hco J) (((orderPieces83 P.E (fun k => (ch k).H) h hid hcomp).limit J).canon t w) =
          P.E.map (OCol83.iota (OCol83.phiH h J) (OCol83.phiH_comp h hcomp J) (OCol83.phiH_id h hid J) t) w :=
      fun J _ _ t w => congrFun (congrArg (⇑) ((Classical.choose_spec (hco J)).2.2 t)) w
    have e4 := congrFun (congrArg (⇑) (η.natural (indexCast f s))) y
    simp only [Language.Embedding.comp_apply] at e1 e4 ⊢
    rw [e1]
    show Classical.choose (hco I') (η.limMap I' (((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).limit I').canon _
        ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map (indexCast f s) y))) = _
    have L1 := e2 I' (EM83.gSystemImage (F := Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs) f s)
      ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map (indexCast f s) y)
    have L2 := e3 I' (EM83.gSystemImage (F := Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs) f s)
      (η.app _ ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map (indexCast f s) y))
    refine (congrArg (fun z => Classical.choose (hco I') z) L1).trans (L2.trans ?_)
    rw [e2]
    refine Eq.trans ?_ (congrArg (fun z => P.E.map (OCol83.colMap h hid hcomp f) z)
      (e3 I s (η.app _ y))).symm
    refine (congrArg (fun z => P.E.map (OCol83.iota (OCol83.phiH h I') (OCol83.phiH_comp h hcomp I')
      (OCol83.phiH_id h hid I') (imageIndex f s)) z) e4).trans ?_
    show P.E.map _ (P.E.map (h (indexCast f s)) _) = P.E.map _ (P.E.map _ _)
    have key : (h (indexCast f s)).trans (OCol83.iota (OCol83.phiH h I') (OCol83.phiH_comp h hcomp I')
        (OCol83.phiH_id h hid I') (imageIndex f s)) =
        (OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s).trans
          (OCol83.colMap h hid hcomp f) := RelEmbedding.ext fun z => rfl
    exact (congrFun (congrArg (⇑) (P.E.map_comp _ _)) _).symm.trans
      ((congrArg (fun g => P.E.map g (η.app _ y)) key).trans
        (congrFun (congrArg (⇑) (P.E.map_comp _ _)) _))
  have hsurj : ∀ (I : Type u) [LinearOrder I] [Nonempty I],
      Function.Surjective ((Classical.choose (hco I)).comp (η.limMap I)) :=
    fun I _ _ => ((Classical.choose_spec (hco I)).2.1.comp (hlim I).1).2
  have hpc : ∀ k, #((ch k).H) ≤ ls K := by
    intro k
    have hsurj : Function.Surjective (fun t : (LS83.pairLangR P.E).Term (Fin (k + 1) × Fin 1) =>
        (Quotient.mk _ t : ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).obj k).carrier)) := fun x => Quotient.exists_rep x
    refine P.E.card_lower.trans ?_
    refine (Cardinal.mk_congr (Equiv.ofBijective _ (ch k).bij)).symm.le.trans ?_
    exact (Cardinal.mk_le_of_surjective hsurj).trans
      ((Cardinal.mk_le_of_injective (sigma_mk_injective (β := fun n => (LS83.pairLangR P.E).Term (Fin n × Fin 1)) (i := k + 1))).trans
        (Hull83.card_bundle_terms_le 1 (LS83.pairLangR_functions_le P.E)))
  have hg : ∀ (I : Type u) [LinearOrder I], ∃ g : I ↪o OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I),
      ∀ (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1),
        g i = OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s
          ((ch s.1.card.pred).j (OCol83.pos s i hi)) := fun I _ =>
    OCol83.exists_coord_embedding (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I)
      (fun s i hi => (ch s.1.card.pred).j (OCol83.pos s i hi))
      (fun {s t} hst i hi => by
        show h (placeSucc hst s.2 t.2) _ = _
        rw [hjc, OCol83.pos_place])
      (fun s i i' hi hi' hii' => (ch s.1.card.pred).mono (OCol83.pos_strictMono s i i' hi hi' hii'))
  refine ⟨hsq, fun I _ _ => ?_, fun I I' I'' _ _ _ _ _ _ f g => ?_,
    fun I _ => Classical.choose (hg I), fun I _ => Classical.choose_spec (hg I), ?_, ?_, fun I _ =>
    (OCol83.card_col_le (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (ls K) (fun s => hpc s.1.card.pred)).trans
      (mul_le_mul_left (Cardinal.mk_subtype_le _) _)⟩
  rotate_left 2
  · intro I I' _ _ f i
    let s : OCol83.Idx I := ⟨{i}, Finset.singleton_nonempty i⟩
    have hi : i ∈ s.1 := Finset.mem_singleton_self i
    rw [Classical.choose_spec (hg I) s i hi, OCol83.colMap_iota, hjc, OCol83.pos_indexCast,
      ← Classical.choose_spec (hg I') (imageIndex f s) (f i) (Finset.mem_map_of_mem f.toEmbedding hi)]
  · intro I _ _ s i hi x hx
    have e2 := congrFun (congrArg (⇑) (η.limMap_canon I s)) x
    have e3 := congrFun (congrArg (⇑) ((Classical.choose_spec (hco I)).2.2 s)) (η.app _ x)
    refine (congrArg (fun z => Classical.choose (hco I) z) e2).trans (e3.trans ?_)
    rw [happ, hx]
    exact (P.E.skeleton_natural _ _).trans (congrArg (fun z => P.E.skeleton z) (Classical.choose_spec (hg I) s i hi).symm)
  · apply infra_83_map_faithful P.E
    intro y
    obtain ⟨x, rfl⟩ := hsurj I y
    rw [← hsq, EM83.gEmMap_id, P.E.map_id]
    rfl
  · apply infra_83_map_faithful P.E
    intro y
    obtain ⟨x, rfl⟩ := hsurj I y
    refine (hsq I I'' (f.trans g) x).symm.trans ?_
    rw [EM83.gEmMap_comp]
    refine (hsq I' I'' g _).trans ?_
    rw [hsq I I' f x, P.E.map_comp]
    rfl

/-- **`F_X(I) ≅ F(J_I)` naturally in `I`**: with `J_I` the directed colimit of the `X`-chart
orders, there are strong bijective `τ`-isomorphisms `m_I : F_X(I) → F(J_I)` such that for every
order embedding `f : I ↪o I'`, `m_I' ∘ F_X(f) = F(J_f) ∘ m_I` with `J_f : J_I ↪o J_I'` the
induced map of colimits; moreover `I ↦ J_I`, `f ↦ J_f` is a functor (J_id = id,
J_(g∘f) = J_g ∘ J_f), and `i ↦` (colimit image of the chart coordinate of `i`) is an order
embedding `g_I : I ↪o J_I` natural in `I`: `J_f ∘ g_I = g_I' ∘ f`; `m_I` sends the chart
coordinate of `i` (the element charted to `skeleton(j(pos i))`) to `skeleton(g_I i)`; and
`#J_I ≤ #(Finset I) · ls K`. -/
theorem infra_83_pairMS2_X_hull_natural (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).obj k) k)
      (h : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) → (ch k).H ↪o (ch l).H)
      (hid : ∀ k (p : (ch k).H), h (idEmb (α := Fin (k + 1))) p = p)
      (hcomp : ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1))
        (p : (ch k).H), h (e.trans f) p = h f (h e p))
      (m : ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).limit I).obj.carrier ↪[K.τ]
          (P.E.obj (OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I))).carrier),
      (∀ k (a : Fin (k + 1)), (ch k).ε (Quotient.mk _ (Term.var (a, (0 : Fin 1))) : ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).obj k).carrier) = P.E.skeleton ((ch k).j a)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (m I) ∧ Function.Bijective (m I)) ∧
      (∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') x,
        m I' (EM83.gEmMap (F := Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs) f x) =
          P.E.map (OCol83.colMap h hid hcomp f) (m I x)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        OCol83.colMap h hid hcomp (OrderIso.refl I).toOrderEmbedding = (OrderIso.refl _).toOrderEmbedding) ∧
      (∀ (I I' I'' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I']
        [LinearOrder I''] [Nonempty I''] (f : I ↪o I') (g : I' ↪o I''),
        OCol83.colMap h hid hcomp (f.trans g) =
          (OCol83.colMap h hid hcomp f).trans (OCol83.colMap h hid hcomp g)) ∧
      ∃ g : ∀ (I : Type u) [LinearOrder I], I ↪o OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I),
        (∀ (I : Type u) [LinearOrder I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1),
          g I i = OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s
            ((ch s.1.card.pred).j (OCol83.pos s i hi))) ∧
        (∀ (I I' : Type u) [LinearOrder I] [LinearOrder I'] (f : I ↪o I') (i : I),
          OCol83.colMap h hid hcomp f (g I i) = g I' (f i)) ∧
        (∀ (I : Type u) [LinearOrder I] [Nonempty I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1)
          (x : ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).obj s.1.card.pred).carrier),
          (ch s.1.card.pred).ε x = P.E.skeleton ((ch s.1.card.pred).j (OCol83.pos s i hi)) →
          m I (((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).limit I).canon s x) = P.E.skeleton (g I i)) ∧
      ∀ (I : Type u) [LinearOrder I],
        #(OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I)) ≤ #(Finset I) * ls K := by
  obtain ⟨c, hc, hcoh, hθ, hρ⟩ := infra_83_pairMS2_coherent_colors P Pr
  exact ⟨c, hc, hcoh, fun M _ hM => pairM_subHullStrongX P.E Pr.n M hM.1.1, infra_83_pairMS2_X_hull_natural_c P Pr c hc hcoh hθ hρ (fun M _ hM => pairM_subHullStrongX P.E Pr.n M hM.1.1)⟩

/-- Parametric form of `infra_83_pairMS2_Y_hull_natural`: for any coherent colors `c` (with the `θ`/`ρ` facts) and
any `hXs`. -/
theorem infra_83_pairMS2_Y_hull_natural_c (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hθ : ∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin 3),
        (thetaM P.E Pr.n i).relabel (fun _ => (a, i)) ∈ c m hm)
      (hρ : ∀ (m : ℕ) (hm : 0 < m) (a b : Fin m), a < b → ∀ i : Fin 3,
        (rhoM P.E Pr.n i).relabel ![(a, i), (b, i)] ∈ c m hm)
      (hXs : Hull83.SubHullStrong (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) (fun N _ => pairMAdmittedS2 P.E Pr.n N)) :
    ∃ (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).obj k) k)
      (h : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) → (ch k).H ↪o (ch l).H)
      (hid : ∀ k (p : (ch k).H), h (idEmb (α := Fin (k + 1))) p = p)
      (hcomp : ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1))
        (p : (ch k).H), h (e.trans f) p = h f (h e p))
      (m : ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).limit I).obj.carrier ↪[K.τ]
          (P.E.obj (OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I))).carrier),
      (∀ k (a : Fin (k + 1)), (ch k).ε (Quotient.mk _ (Term.var (a, (1 : Fin 2))) : ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).obj k).carrier) = P.E.skeleton ((ch k).j a)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (m I) ∧ Function.Bijective (m I)) ∧
      (∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') x,
        m I' (EM83.gEmMap (F := Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs) f x) =
          P.E.map (OCol83.colMap h hid hcomp f) (m I x)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        OCol83.colMap h hid hcomp (OrderIso.refl I).toOrderEmbedding = (OrderIso.refl _).toOrderEmbedding) ∧
      (∀ (I I' I'' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I']
        [LinearOrder I''] [Nonempty I''] (f : I ↪o I') (g : I' ↪o I''),
        OCol83.colMap h hid hcomp (f.trans g) =
          (OCol83.colMap h hid hcomp f).trans (OCol83.colMap h hid hcomp g)) ∧
      ∃ g : ∀ (I : Type u) [LinearOrder I], I ↪o OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I),
        (∀ (I : Type u) [LinearOrder I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1),
          g I i = OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s
            ((ch s.1.card.pred).j (OCol83.pos s i hi))) ∧
        (∀ (I I' : Type u) [LinearOrder I] [LinearOrder I'] (f : I ↪o I') (i : I),
          OCol83.colMap h hid hcomp f (g I i) = g I' (f i)) ∧
        (∀ (I : Type u) [LinearOrder I] [Nonempty I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1)
          (x : ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).obj s.1.card.pred).carrier),
          (ch s.1.card.pred).ε x = P.E.skeleton ((ch s.1.card.pred).j (OCol83.pos s i hi)) →
          m I (((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).limit I).canon s x) = P.E.skeleton (g I i)) ∧
      ∀ (I : Type u) [LinearOrder I],
        #(OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I)) ≤ #(Finset I) * ls K := by
  obtain ⟨ch, h, hid, hcomp, hjc, η, hv, happ, -, hlim⟩ := infra_83_pairMS2_Y_F_pieces_c P Pr c hc hcoh hθ hρ hXs
  have hco : ∀ (I : Type u) [LinearOrder I] [Nonempty I], ∃ m' : ((orderPieces83 P.E (fun k => (ch k).H) h hid hcomp).limit I).obj.carrier ↪[K.τ]
        (P.E.obj (OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I))).carrier,
      K.Strong m' ∧ Function.Bijective m' ∧ ∀ s, m'.comp
        (((orderPieces83 P.E (fun k => (ch k).H) h hid hcomp).limit I).canon s) =
        P.E.map (OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s) :=
    fun I _ _ => infra_83_orderPieces_cocone_bij P.E I _ _
      (fun {s t} hst => OCol83.iota_compat _ _ _ hst) (fun y => OCol83.cover _ _ _ P.E y)
  refine ⟨ch, h, hid, hcomp,
    fun I _ _ => (Classical.choose (hco I)).comp (η.limMap I),
    hv,
    fun I _ _ => ⟨K.strong_trans _ _ (hlim I).2 (Classical.choose_spec (hco I)).1,
      (Classical.choose_spec (hco I)).2.1.comp (hlim I).1⟩, ?_⟩
  have hsq : ∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') x,
      (Classical.choose (hco I')).comp (η.limMap I') (EM83.gEmMap (F := Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs) f x) =
        P.E.map (OCol83.colMap h hid hcomp f) ((Classical.choose (hco I)).comp (η.limMap I) x) := by
    intro I I' _ _ _ _ f x
    obtain ⟨s, y, rfl⟩ := ((Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).limit I).joint x
    have e1 := congrFun (congrArg (⇑) (EM83.gEmMap_canon (F := Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs) f s)) y
    have e2 : ∀ (J : Type u) [LinearOrder J] [Nonempty J] t z,
        η.limMap J (((Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).limit J).canon t z) =
          ((orderPieces83 P.E (fun k => (ch k).H) h hid hcomp).limit J).canon t (η.app _ z) :=
      fun J _ _ t z => congrFun (congrArg (⇑) (η.limMap_canon J t)) z
    have e3 : ∀ (J : Type u) [LinearOrder J] [Nonempty J] t w,
        Classical.choose (hco J) (((orderPieces83 P.E (fun k => (ch k).H) h hid hcomp).limit J).canon t w) =
          P.E.map (OCol83.iota (OCol83.phiH h J) (OCol83.phiH_comp h hcomp J) (OCol83.phiH_id h hid J) t) w :=
      fun J _ _ t w => congrFun (congrArg (⇑) ((Classical.choose_spec (hco J)).2.2 t)) w
    have e4 := congrFun (congrArg (⇑) (η.natural (indexCast f s))) y
    simp only [Language.Embedding.comp_apply] at e1 e4 ⊢
    rw [e1]
    show Classical.choose (hco I') (η.limMap I' (((Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).limit I').canon _
        ((Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).map (indexCast f s) y))) = _
    have L1 := e2 I' (EM83.gSystemImage (F := Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs) f s)
      ((Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).map (indexCast f s) y)
    have L2 := e3 I' (EM83.gSystemImage (F := Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs) f s)
      (η.app _ ((Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).map (indexCast f s) y))
    refine (congrArg (fun z => Classical.choose (hco I') z) L1).trans (L2.trans ?_)
    rw [e2]
    refine Eq.trans ?_ (congrArg (fun z => P.E.map (OCol83.colMap h hid hcomp f) z)
      (e3 I s (η.app _ y))).symm
    refine (congrArg (fun z => P.E.map (OCol83.iota (OCol83.phiH h I') (OCol83.phiH_comp h hcomp I')
      (OCol83.phiH_id h hid I') (imageIndex f s)) z) e4).trans ?_
    show P.E.map _ (P.E.map (h (indexCast f s)) _) = P.E.map _ (P.E.map _ _)
    have key : (h (indexCast f s)).trans (OCol83.iota (OCol83.phiH h I') (OCol83.phiH_comp h hcomp I')
        (OCol83.phiH_id h hid I') (imageIndex f s)) =
        (OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s).trans
          (OCol83.colMap h hid hcomp f) := RelEmbedding.ext fun z => rfl
    exact (congrFun (congrArg (⇑) (P.E.map_comp _ _)) _).symm.trans
      ((congrArg (fun g => P.E.map g (η.app _ y)) key).trans
        (congrFun (congrArg (⇑) (P.E.map_comp _ _)) _))
  have hsurj : ∀ (I : Type u) [LinearOrder I] [Nonempty I],
      Function.Surjective ((Classical.choose (hco I)).comp (η.limMap I)) :=
    fun I _ _ => ((Classical.choose_spec (hco I)).2.1.comp (hlim I).1).2
  have hpc : ∀ k, #((ch k).H) ≤ ls K := by
    intro k
    have hsurj : Function.Surjective (fun t : (LS83.pairLangM2 P.E Pr.n).Term (Fin (k + 1) × Fin 2) =>
        (Quotient.mk _ t : ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).obj k).carrier)) := fun x => Quotient.exists_rep x
    refine P.E.card_lower.trans ?_
    refine (Cardinal.mk_congr (Equiv.ofBijective _ (ch k).bij)).symm.le.trans ?_
    exact (Cardinal.mk_le_of_surjective hsurj).trans
      ((Cardinal.mk_le_of_injective (sigma_mk_injective (β := fun n => (LS83.pairLangM2 P.E Pr.n).Term (Fin n × Fin 2)) (i := k + 1))).trans
        (Hull83.card_bundle_terms_le 2 (LS83.pairLangM2_functions_le P.E Pr.n)))
  have hg : ∀ (I : Type u) [LinearOrder I], ∃ g : I ↪o OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I),
      ∀ (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1),
        g i = OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s
          ((ch s.1.card.pred).j (OCol83.pos s i hi)) := fun I _ =>
    OCol83.exists_coord_embedding (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I)
      (fun s i hi => (ch s.1.card.pred).j (OCol83.pos s i hi))
      (fun {s t} hst i hi => by
        show h (placeSucc hst s.2 t.2) _ = _
        rw [hjc, OCol83.pos_place])
      (fun s i i' hi hi' hii' => (ch s.1.card.pred).mono (OCol83.pos_strictMono s i i' hi hi' hii'))
  refine ⟨hsq, fun I _ _ => ?_, fun I I' I'' _ _ _ _ _ _ f g => ?_,
    fun I _ => Classical.choose (hg I), fun I _ => Classical.choose_spec (hg I), ?_, ?_, fun I _ =>
    (OCol83.card_col_le (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (ls K) (fun s => hpc s.1.card.pred)).trans
      (mul_le_mul_left (Cardinal.mk_subtype_le _) _)⟩
  rotate_left 2
  · intro I I' _ _ f i
    let s : OCol83.Idx I := ⟨{i}, Finset.singleton_nonempty i⟩
    have hi : i ∈ s.1 := Finset.mem_singleton_self i
    rw [Classical.choose_spec (hg I) s i hi, OCol83.colMap_iota, hjc, OCol83.pos_indexCast,
      ← Classical.choose_spec (hg I') (imageIndex f s) (f i) (Finset.mem_map_of_mem f.toEmbedding hi)]
  · intro I _ _ s i hi x hx
    have e2 := congrFun (congrArg (⇑) (η.limMap_canon I s)) x
    have e3 := congrFun (congrArg (⇑) ((Classical.choose_spec (hco I)).2.2 s)) (η.app _ x)
    refine (congrArg (fun z => Classical.choose (hco I) z) e2).trans (e3.trans ?_)
    rw [happ, hx]
    exact (P.E.skeleton_natural _ _).trans (congrArg (fun z => P.E.skeleton z) (Classical.choose_spec (hg I) s i hi).symm)
  · apply infra_83_map_faithful P.E
    intro y
    obtain ⟨x, rfl⟩ := hsurj I y
    rw [← hsq, EM83.gEmMap_id, P.E.map_id]
    rfl
  · apply infra_83_map_faithful P.E
    intro y
    obtain ⟨x, rfl⟩ := hsurj I y
    refine (hsq I I'' (f.trans g) x).symm.trans ?_
    rw [EM83.gEmMap_comp]
    refine (hsq I' I'' g _).trans ?_
    rw [hsq I I' f x, P.E.map_comp]
    rfl

/-- **`F_Y(I) ≅ F(Z_I)` naturally in `I`**: with `Z_I` the directed colimit of the `Y`-chart
orders, there are strong bijective `τ`-isomorphisms `m_I : F_Y(I) → F(Z_I)` such that for every
order embedding `f : I ↪o I'`, `m_I' ∘ F_Y(f) = F(Z_f) ∘ m_I` with `Z_f : Z_I ↪o Z_I'` the
induced map of colimits; moreover `I ↦ Z_I`, `f ↦ Z_f` is a functor (Z_id = id,
Z_(g∘f) = Z_g ∘ Z_f), and `i ↦` (colimit image of the chart coordinate of `i`) is an order
embedding `g_I : I ↪o Z_I` natural in `I`: `Z_f ∘ g_I = g_I' ∘ f`; `m_I` sends the chart
coordinate of `i` (the element charted to `skeleton(j(pos i))`) to `skeleton(g_I i)`; and
`#Z_I ≤ #(Finset I) · ls K`. -/
theorem infra_83_pairMS2_Y_hull_natural (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).obj k) k)
      (h : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) → (ch k).H ↪o (ch l).H)
      (hid : ∀ k (p : (ch k).H), h (idEmb (α := Fin (k + 1))) p = p)
      (hcomp : ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1))
        (p : (ch k).H), h (e.trans f) p = h f (h e p))
      (m : ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).limit I).obj.carrier ↪[K.τ]
          (P.E.obj (OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I))).carrier),
      (∀ k (a : Fin (k + 1)), (ch k).ε (Quotient.mk _ (Term.var (a, (1 : Fin 2))) : ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).obj k).carrier) = P.E.skeleton ((ch k).j a)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (m I) ∧ Function.Bijective (m I)) ∧
      (∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') x,
        m I' (EM83.gEmMap (F := Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs) f x) =
          P.E.map (OCol83.colMap h hid hcomp f) (m I x)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        OCol83.colMap h hid hcomp (OrderIso.refl I).toOrderEmbedding = (OrderIso.refl _).toOrderEmbedding) ∧
      (∀ (I I' I'' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I']
        [LinearOrder I''] [Nonempty I''] (f : I ↪o I') (g : I' ↪o I''),
        OCol83.colMap h hid hcomp (f.trans g) =
          (OCol83.colMap h hid hcomp f).trans (OCol83.colMap h hid hcomp g)) ∧
      ∃ g : ∀ (I : Type u) [LinearOrder I], I ↪o OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I),
        (∀ (I : Type u) [LinearOrder I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1),
          g I i = OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s
            ((ch s.1.card.pred).j (OCol83.pos s i hi))) ∧
        (∀ (I I' : Type u) [LinearOrder I] [LinearOrder I'] (f : I ↪o I') (i : I),
          OCol83.colMap h hid hcomp f (g I i) = g I' (f i)) ∧
        (∀ (I : Type u) [LinearOrder I] [Nonempty I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1)
          (x : ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).obj s.1.card.pred).carrier),
          (ch s.1.card.pred).ε x = P.E.skeleton ((ch s.1.card.pred).j (OCol83.pos s i hi)) →
          m I (((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hXs).limit I).canon s x) = P.E.skeleton (g I i)) ∧
      ∀ (I : Type u) [LinearOrder I],
        #(OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I)) ≤ #(Finset I) * ls K := by
  obtain ⟨c, hc, hcoh, hθ, hρ⟩ := infra_83_pairMS2_coherent_colors P Pr
  exact ⟨c, hc, hcoh, fun M _ hM => pairM_subHullStrongY P.E Pr.n M hM.1.1, infra_83_pairMS2_Y_hull_natural_c P Pr c hc hcoh hθ hρ (fun M _ hM => pairM_subHullStrongY P.E Pr.n M hM.1.1)⟩

/-- **One choice of colors for `X`, `Y` and `L`**: a single coherent color family `c` gives the
pair template `F_X → F_Y → F_L` (strong natural piece maps, presentation `E` with values
`F_L(I)`) together with both identifications `F_X(I) ≅ F(J_I)` and `F_Y(I) ≅ F(Z_I)` (natural in
`I`, functorial colimit orders, natural skeleton embeddings, coordinates to skeleton points), all
for the same `F_X`, `F_Y`. -/
theorem infra_83_pairMS2_joint (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hX : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (hY : Hull83.SubHullStrong (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ηXY : EM83.PiecesHom (Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hX) (Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY))
      (FL : EM83.FinPieces K) (ηYL : EM83.PiecesHom (Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY) FL) (E : OrderPresentation K),
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], E.obj I = (FL.limit I).obj) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        K.Strong (ηXY.limMap I) ∧ K.Strong (ηYL.limMap I)) ∧
      (∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J] (f : I ↪o J),
        (ηXY.limMap J).comp (EM83.gEmMap (F := Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hX) f) =
            (EM83.gEmMap (F := Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY) f).comp (ηXY.limMap I) ∧
          (ηYL.limMap J).comp (EM83.gEmMap (F := Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY) f) =
            (EM83.gEmMap (F := FL) f).comp (ηYL.limMap I)) ∧
      (∃ (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hX).obj k) k)
      (h : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) → (ch k).H ↪o (ch l).H)
      (hid : ∀ k (p : (ch k).H), h (idEmb (α := Fin (k + 1))) p = p)
      (hcomp : ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1))
        (p : (ch k).H), h (e.trans f) p = h f (h e p))
      (m : ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hX).limit I).obj.carrier ↪[K.τ]
          (P.E.obj (OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I))).carrier),
      (∀ k (a : Fin (k + 1)), (ch k).ε (Quotient.mk _ (Term.var (a, (0 : Fin 1))) : ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hX).obj k).carrier) = P.E.skeleton ((ch k).j a)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (m I) ∧ Function.Bijective (m I)) ∧
      (∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') x,
        m I' (EM83.gEmMap (F := Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hX) f x) =
          P.E.map (OCol83.colMap h hid hcomp f) (m I x)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        OCol83.colMap h hid hcomp (OrderIso.refl I).toOrderEmbedding = (OrderIso.refl _).toOrderEmbedding) ∧
      (∀ (I I' I'' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I']
        [LinearOrder I''] [Nonempty I''] (f : I ↪o I') (g : I' ↪o I''),
        OCol83.colMap h hid hcomp (f.trans g) =
          (OCol83.colMap h hid hcomp f).trans (OCol83.colMap h hid hcomp g)) ∧
      ∃ g : ∀ (I : Type u) [LinearOrder I], I ↪o OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I),
        (∀ (I : Type u) [LinearOrder I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1),
          g I i = OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s
            ((ch s.1.card.pred).j (OCol83.pos s i hi))) ∧
        (∀ (I I' : Type u) [LinearOrder I] [LinearOrder I'] (f : I ↪o I') (i : I),
          OCol83.colMap h hid hcomp f (g I i) = g I' (f i)) ∧
        (∀ (I : Type u) [LinearOrder I] [Nonempty I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1)
          (x : ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hX).obj s.1.card.pred).carrier),
          (ch s.1.card.pred).ε x = P.E.skeleton ((ch s.1.card.pred).j (OCol83.pos s i hi)) →
          m I (((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hX).limit I).canon s x) = P.E.skeleton (g I i)) ∧
      ∀ (I : Type u) [LinearOrder I],
        #(OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I)) ≤ #(Finset I) * ls K) ∧
      (∃ (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).obj k) k)
      (h : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) → (ch k).H ↪o (ch l).H)
      (hid : ∀ k (p : (ch k).H), h (idEmb (α := Fin (k + 1))) p = p)
      (hcomp : ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1))
        (p : (ch k).H), h (e.trans f) p = h f (h e p))
      (m : ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).limit I).obj.carrier ↪[K.τ]
          (P.E.obj (OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I))).carrier),
      (∀ k (a : Fin (k + 1)), (ch k).ε (Quotient.mk _ (Term.var (a, (1 : Fin 2))) : ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).obj k).carrier) = P.E.skeleton ((ch k).j a)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (m I) ∧ Function.Bijective (m I)) ∧
      (∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') x,
        m I' (EM83.gEmMap (F := Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY) f x) =
          P.E.map (OCol83.colMap h hid hcomp f) (m I x)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        OCol83.colMap h hid hcomp (OrderIso.refl I).toOrderEmbedding = (OrderIso.refl _).toOrderEmbedding) ∧
      (∀ (I I' I'' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I']
        [LinearOrder I''] [Nonempty I''] (f : I ↪o I') (g : I' ↪o I''),
        OCol83.colMap h hid hcomp (f.trans g) =
          (OCol83.colMap h hid hcomp f).trans (OCol83.colMap h hid hcomp g)) ∧
      ∃ g : ∀ (I : Type u) [LinearOrder I], I ↪o OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I),
        (∀ (I : Type u) [LinearOrder I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1),
          g I i = OCol83.iota (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I) (OCol83.phiH_id h hid I) s
            ((ch s.1.card.pred).j (OCol83.pos s i hi))) ∧
        (∀ (I I' : Type u) [LinearOrder I] [LinearOrder I'] (f : I ↪o I') (i : I),
          OCol83.colMap h hid hcomp f (g I i) = g I' (f i)) ∧
        (∀ (I : Type u) [LinearOrder I] [Nonempty I] (s : OCol83.Idx I) (i : I) (hi : i ∈ s.1)
          (x : ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).obj s.1.card.pred).carrier),
          (ch s.1.card.pred).ε x = P.E.skeleton ((ch s.1.card.pred).j (OCol83.pos s i hi)) →
          m I (((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).limit I).canon s x) = P.E.skeleton (g I i)) ∧
      ∀ (I : Type u) [LinearOrder I],
        #(OCol83.Col (OCol83.phiH h I) (OCol83.phiH_comp h hcomp I)) ≤ #(Finset I) * ls K) := by
  obtain ⟨c, hc, hcoh, hθ, hρ⟩ := infra_83_pairMS2_coherent_colors P Pr
  have hX : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
      ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N) :=
    fun M _ hM => pairM_subHullStrongX P.E Pr.n M hM.1.1
  have hY : Hull83.SubHullStrong (psiM P.E Pr.n)
      ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) (fun N _ => pairMAdmittedS2 P.E Pr.n N) :=
    fun M _ hM => pairM_subHullStrongY P.E Pr.n M hM.1.1
  have hL : Hull83.HullStrong ((psiM P.E Pr.n).comp ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))))
      (fun N _ => pairMAdmittedS2 P.E Pr.n N) :=
    fun M _ hM => pairM_hullStrong P.E Pr.n M hM.1.1
  let ηXY := Hull83.subLangMixHom (chiM P.E Pr.n) (psiM P.E Pr.n) ((LS83.pairInlR P.E).comp (LS83.lsInl K))
    hc hcoh (fun i : Fin 2 => i.castSucc) (fun _ : Fin 1 => (0 : Fin 2)) hX hY
  let ηYL := Hull83.subLangChain (psiM P.E Pr.n) ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
    hc hcoh (fun i : Fin 2 => i.castSucc) hY hL
  exact ⟨c, hc, hcoh, hX, hY, ηXY, _, ηYL,
    Hull83.tpPresentationB hc hcoh (by norm_num)
      ((psiM P.E Pr.n).comp ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))))
      hL (LS83.pairLangM3_functions_le P.E Pr.n),
    fun I _ _ => rfl,
    fun I _ _ => ⟨ηXY.limMap_strong I, ηYL.limMap_strong I⟩,
    fun f => ⟨ηXY.limMap_natural f, ηYL.limMap_natural f⟩,
    infra_83_pairMS2_X_hull_natural_c P Pr c hc hcoh hθ hρ hX,
    infra_83_pairMS2_Y_hull_natural_c P Pr c hc hcoh hθ hρ hY⟩

/-- A family of piece elements fixed by every piece map has a well-defined image in every limit
value: all canonical images agree. -/
theorem EM83const_canon (F : EM83.FinPieces K) (d : ∀ k, (F.obj k).carrier)
    (hd : ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)), F.map e (d k) = d l)
    (I : Type u) [LinearOrder I] [Nonempty I] (s t : (F.system I).ι) :
    (F.limit I).canon s (d _) = (F.limit I).canon t (d _) := by
  obtain ⟨u, hsu, htu⟩ := (F.system I).directed s t
  have h1 := congrFun (congrArg (⇑) ((F.limit I).compat hsu)) (d _)
  have h2 := congrFun (congrArg (⇑) ((F.limit I).compat htu)) (d _)
  refine h1.symm.trans (Eq.trans ?_ h2)
  exact congrArg ((F.limit I).canon u)
    ((hd (placeSucc hsu s.2 u.2)).trans (hd (placeSucc htu t.2 u.2)).symm)

/-- ... and these images are preserved by the EM maps `F(f)`. -/
theorem EM83const_gEmMap (F : EM83.FinPieces K) (d : ∀ k, (F.obj k).carrier)
    (hd : ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)), F.map e (d k) = d l)
    {I J : Type u} [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J] (f : I ↪o J)
    (s : (F.system I).ι) (t : (F.system J).ι) :
    EM83.gEmMap (F := F) f ((F.limit I).canon s (d _)) = (F.limit J).canon t (d _) := by
  have h := congrFun (congrArg (⇑) (EM83.gEmMap_canon (F := F) f s)) (d _)
  refine h.trans ?_
  show (F.limit J).canon _ (F.map (indexCast f s) (d _)) = _
  rw [hd]
  exact EM83const_canon F d hd J _ t

/-- The `i`-th mark constant as an element of the `Y`-piece at `k` (the hull class of the
constant term of the mark language). -/
noncomputable def pairMS2_markY (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
    (hY : Hull83.SubHullStrong (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) (fun N _ => pairMAdmittedS2 P.E Pr.n N)) (k : ℕ) (i : Fin Pr.n) : ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).obj k).carrier :=
  Quotient.mk _ (Term.func (Sum.inr (Sum.inr ⟨⟨i⟩, rfl⟩) : (LS83.pairLangM2 P.E Pr.n).Functions 0) Fin.elim0)

/-- The `Y`-piece maps fix the mark constants. -/
theorem pairMS2_markY_map (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
    (hY : Hull83.SubHullStrong (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) (fun N _ => pairMAdmittedS2 P.E Pr.n N)) (i : Fin Pr.n) {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) :
    (Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).map e (pairMS2_markY P Pr c hc hcoh hY k i) = pairMS2_markY P Pr c hc hcoh hY l i := by
  show Quotient.mk _ _ = Quotient.mk _ _
  congr 1
  show Term.func _ _ = Term.func _ _
  congr 1
  funext z
  exact Fin.elim0 z

/-- **Marks as designated terms of the template**: the mark constants give, in every value
`F_Y(I)`, a mark tuple `b_I` (the common canonical image of the piece marks), preserved by every
template map `F_Y(f)`; under any natural identification `m_I : F_Y(I) ≅ F(Z_I)` with
`m_J ∘ F_Y(f) = F(Z_f) ∘ m_I`, the transported marks are carried to each other by `F(Z_f)`. -/
theorem infra_83_pairMS2_Y_marks_c (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
    (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
    (hY : Hull83.SubHullStrong (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) (fun N _ => pairMAdmittedS2 P.E Pr.n N)) :
    ∃ b : ∀ (I : Type u) [LinearOrder I] [Nonempty I], Fin Pr.n → ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).limit I).obj.carrier,
      (∀ (I : Type u) [LinearOrder I] [Nonempty I] (s : ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).system I).ι) (i : Fin Pr.n),
        ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).limit I).canon s (pairMS2_markY P Pr c hc hcoh hY _ i) = b I i) ∧
      (∀ (I J : Type u) [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J] (f : I ↪o J)
        (i : Fin Pr.n), EM83.gEmMap (F := Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY) f (b I i) = b J i) ∧
      ∀ (Z : ∀ (I : Type u) [LinearOrder I] [Nonempty I], Type u)
        [∀ (I : Type u) [LinearOrder I] [Nonempty I], LinearOrder (Z I)]
        [∀ (I : Type u) [LinearOrder I] [Nonempty I], Nonempty (Z I)]
        (Zf : ∀ {I J : Type u} [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J],
          (I ↪o J) → (Z I ↪o Z J))
        (m : ∀ (I : Type u) [LinearOrder I] [Nonempty I],
          ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).limit I).obj.carrier ↪[K.τ] (P.E.obj (Z I)).carrier),
        (∀ (I J : Type u) [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J] (f : I ↪o J) x,
          m J (EM83.gEmMap (F := Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY) f x) = P.E.map (Zf f) (m I x)) →
        ∀ (I J : Type u) [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J] (f : I ↪o J)
          (i : Fin Pr.n), P.E.map (Zf f) (m I (b I i)) = m J (b J i) := by
  let d : Fin Pr.n → ∀ k, ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).obj k).carrier := fun i k => pairMS2_markY P Pr c hc hcoh hY k i
  have hd : ∀ i {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)), (Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).map e (d i k) = d i l :=
    fun i _ _ e => pairMS2_markY_map P Pr c hc hcoh hY i e
  let s0 : ∀ (I : Type u) [LinearOrder I] [Nonempty I], ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).system I).ι :=
    fun I _ _ => ⟨{Classical.choice ‹Nonempty I›}, Finset.singleton_nonempty _⟩
  refine ⟨fun I _ _ i => ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh (fun i : Fin 2 => i.castSucc) hY).limit I).canon (s0 I) (d i _), fun I _ _ s i =>
    EM83const_canon _ (d i) (hd i) I s (s0 I), fun I J _ _ _ _ f i =>
    EM83const_gEmMap _ (d i) (hd i) f (s0 I) (s0 J), ?_⟩
  intro Z _ _ Zf m hm I J _ _ _ _ f i
  rw [← hm]
  exact congrArg (m J) (EM83const_gEmMap _ (d i) (hd i) f (s0 I) (s0 J))

/-- **`X ⊆ Y` in `J`/`Z` coordinates**: given the natural identifications
`m^X_I : F_X(I) ≅ F(J_I)`, `m^Y_I : F_Y(I) → F(Z_I)` (as in `infra_83_pairMS2_joint`) and the strong
natural template map `η : F_X → F_Y`, the inclusion transports to strong `τ`-embeddings
`ι_I : F(J_I) → F(Z_I)` with `ι_I ∘ m^X_I = m^Y_I ∘ η_I`, natural in `I`:
`ι_I' ∘ F(J_f) = F(Z_f) ∘ ι_I`. (They need not be `F` of an order embedding `J_I → Z_I`; the
faithful Lemma 8.3 only uses the vertexwise inclusion.) -/
theorem infra_83_XY_incl_transport (E : OrderPresentation K) (FX FY : EM83.FinPieces K) (η : EM83.PiecesHom FX FY)
    (J Z : ∀ (I : Type u) [LinearOrder I] [Nonempty I], Type u)
    [∀ (I : Type u) [LinearOrder I] [Nonempty I], LinearOrder (J I)]
    [∀ (I : Type u) [LinearOrder I] [Nonempty I], Nonempty (J I)]
    [∀ (I : Type u) [LinearOrder I] [Nonempty I], LinearOrder (Z I)]
    [∀ (I : Type u) [LinearOrder I] [Nonempty I], Nonempty (Z I)]
    (Jf : ∀ {I I' : Type u} [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'],
      (I ↪o I') → (J I ↪o J I'))
    (Zf : ∀ {I I' : Type u} [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'],
      (I ↪o I') → (Z I ↪o Z I'))
    (mX : ∀ (I : Type u) [LinearOrder I] [Nonempty I], (FX.limit I).obj.carrier ↪[K.τ] (E.obj (J I)).carrier)
    (mY : ∀ (I : Type u) [LinearOrder I] [Nonempty I], (FY.limit I).obj.carrier ↪[K.τ] (E.obj (Z I)).carrier)
    (hX : ∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (mX I) ∧ Function.Bijective (mX I))
    (hY : ∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (mY I))
    (hη : ∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (η.limMap I))
    (sqX : ∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') x,
      mX I' (EM83.gEmMap (F := FX) f x) = E.map (Jf f) (mX I x))
    (sqY : ∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') x,
      mY I' (EM83.gEmMap (F := FY) f x) = E.map (Zf f) (mY I x))
    (sqη : ∀ {I I' : Type u} [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I'),
      (η.limMap I').comp (EM83.gEmMap (F := FX) f) = (EM83.gEmMap (F := FY) f).comp (η.limMap I)) :
    ∃ ι : ∀ (I : Type u) [LinearOrder I] [Nonempty I], (E.obj (J I)).carrier ↪[K.τ] (E.obj (Z I)).carrier,
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (ι I)) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I] x, ι I (mX I x) = mY I (η.limMap I x)) ∧
      ∀ (I I' : Type u) [LinearOrder I] [Nonempty I] [LinearOrder I'] [Nonempty I'] (f : I ↪o I') y,
        ι I' (E.map (Jf f) y) = E.map (Zf f) (ι I y) := by
  let eX : ∀ (I : Type u) [LinearOrder I] [Nonempty I], (FX.limit I).obj.carrier ≃[K.τ] (E.obj (J I)).carrier :=
    fun I _ _ => embeddingEquivOfSurjective (mX I) (hX I).2.2
  have heX : ∀ (I : Type u) [LinearOrder I] [Nonempty I] y, mX I ((eX I).symm y) = y :=
    fun I _ _ y => (eX I).apply_symm_apply y
  refine ⟨fun I _ _ => (mY I).comp ((η.limMap I).comp (eX I).symm.toEmbedding), fun I _ _ => ?_,
    fun I _ _ x => ?_, fun I I' _ _ _ _ f y => ?_⟩
  · refine K.strong_trans _ _ (K.strong_trans _ _ ?_ (hη I)) (hY I)
    exact strong_of_equiv K (eX I).symm (K.strong_mem_cod (mX I) (hX I).1)
  · show mY I (η.limMap I ((eX I).symm (mX I x))) = _
    congr 2
    exact (eX I).symm_apply_apply x
  · show mY I' (η.limMap I' ((eX I').symm (E.map (Jf f) y))) =
      E.map (Zf f) (mY I (η.limMap I ((eX I).symm y)))
    obtain ⟨x, rfl⟩ := (hX I).2.2 y
    have h1 : (eX I').symm (E.map (Jf f) (mX I x)) = EM83.gEmMap (F := FX) f x := by
      rw [← sqX]; exact (eX I').symm_apply_apply _
    have h2 : (eX I).symm (mX I x) = x := (eX I).symm_apply_apply x
    rw [h1, h2, ← sqY]
    exact congrArg (mY I') (congrFun (congrArg (⇑) (sqη f)) x)

/-- **The colimit orders have the size of `I` at tail levels**: if `I` is infinite with
`LS(K) ≤ |I|`, an order `J` receiving `I` (e.g. the skeleton embedding `g_I : I ↪o J_I`) with
`|J| ≤ |Finset I| · LS(K)` (the bound in `infra_83_pairMS2_X/Y_hull_natural`) has `|J| = |I|`.
So `F_X(I) ≅ F(J_I)` and `F_Y(I) ≅ F(Z_I)` are values of `F` at orders of size `|I|`. -/
theorem infra_83_colim_card_eq {I J : Type u} (hI : ℵ₀ ≤ #I) (hls : ls K ≤ #I) (g : I ↪ J)
    (hJ : #J ≤ #(Finset I) * ls K) : #J = #I := by
  refine le_antisymm (hJ.trans ?_) (Cardinal.mk_le_of_injective g.injective)
  have : Infinite I := Cardinal.infinite_iff.mpr hI
  rw [Cardinal.mk_finset_of_infinite]
  exact (mul_le_mul_right hls _).trans (Cardinal.mul_eq_self hI).le

/-- **The template values are scheme objects at the level `|I|`**: at an eligible level
`μ = |I|`, a value identified with `F(J)` (`J ⊇ I`, `|J| ≤ |Finset I|·LS(K)`, as for `J_I`, `Z_I`)
is `τ`-isomorphic to an object of the single-model scheme at level `μ` (`SMObject K μ`). -/
theorem infra_83_value_object (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {I J : Type u} [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J] (hI : #I = μ)
    (g : I ↪o J) (hJ : #J ≤ #(Finset I) * ls K) {A : Type u} [K.τ.Structure A]
    (m : A ↪[K.τ] (P.E.obj J).carrier) (hm : Function.Bijective m) :
    ∃ X : SMObject K μ, Nonempty (A ≃[K.τ] X.model.carrier) := by
  have hJI : #J = #I := infra_83_colim_card_eq (K := K) (hI ▸ SingleModelData.aleph0_le hμ)
    (hI ▸ (SingleModelData.ls_lt hμ).le) g.toEmbedding hJ
  have hc := SingleModelData.card_obj_eq hμ J (hJI.trans hI)
  exact ⟨SMObject.ofModel (P.E.obj J) (P.hE J) hc,
    ⟨(SMObject.ofModelEquiv (P.E.obj J) (P.hE J) hc).comp (embeddingEquivOfSurjective m hm.2)⟩⟩

/-- **The template inclusion as an inclusion of scheme objects**: at an eligible level
`μ = |I|`, values `A ≅ F(J)`, `B ≅ F(Z)` (with `J`, `Z` as for `J_I`, `Z_I`) and a strong
`η : A → B` (the template map `F_X(I) → F_Y(I)`) give scheme objects `X`, `Y` at level `μ` with
`τ`-isomorphisms `e_X`, `e_Y` and a strong embedding `incl : X → Y` with `incl ∘ e_X = e_Y ∘ η`
(the underlying data of the pair `X ⊆ Y` of a value of Lemma 8.3). -/
theorem infra_83_value_pair (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    {I J Z : Type u} [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J]
    [LinearOrder Z] [Nonempty Z] (hI : #I = μ)
    (gJ : I ↪o J) (hJ : #J ≤ #(Finset I) * ls K) (gZ : I ↪o Z) (hZ : #Z ≤ #(Finset I) * ls K)
    (A B : Model K.τ) (hB : K.Mem B)
    (η : A.carrier ↪[K.τ] B.carrier) (hη : K.Strong η)
    (mX : A.carrier ↪[K.τ] (P.E.obj J).carrier) (hmX : Function.Bijective mX)
    (mY : B.carrier ↪[K.τ] (P.E.obj Z).carrier) (hmY : Function.Bijective mY) :
    ∃ (X Y : SMObject K μ) (eX : A.carrier ≃[K.τ] X.model.carrier)
      (eY : B.carrier ≃[K.τ] Y.model.carrier) (incl : X.model.carrier ↪[K.τ] Y.model.carrier),
      K.Strong incl ∧ ∀ a, incl (eX a) = eY (η a) := by
  have cJ : #J = #I := infra_83_colim_card_eq (K := K) (hI ▸ SingleModelData.aleph0_le hμ)
    (hI ▸ (SingleModelData.ls_lt hμ).le) gJ.toEmbedding hJ
  have cZ : #Z = #I := infra_83_colim_card_eq (K := K) (hI ▸ SingleModelData.aleph0_le hμ)
    (hI ▸ (SingleModelData.ls_lt hμ).le) gZ.toEmbedding hZ
  have hcJ := SingleModelData.card_obj_eq hμ J (cJ.trans hI)
  have hcZ := SingleModelData.card_obj_eq hμ Z (cZ.trans hI)
  let X := SMObject.ofModel (P.E.obj J) (P.hE J) hcJ
  let Y := SMObject.ofModel (P.E.obj Z) (P.hE Z) hcZ
  let eX : A.carrier ≃[K.τ] X.model.carrier :=
    (SMObject.ofModelEquiv (P.E.obj J) (P.hE J) hcJ).comp (embeddingEquivOfSurjective mX hmX.2)
  let eY : B.carrier ≃[K.τ] Y.model.carrier :=
    (SMObject.ofModelEquiv (P.E.obj Z) (P.hE Z) hcZ).comp (embeddingEquivOfSurjective mY hmY.2)
  refine ⟨X, Y, eX, eY, (eY.toEmbedding.comp η).comp eX.symm.toEmbedding, ?_, fun a => ?_⟩
  · exact K.strong_trans _ _ (strong_of_equiv K (M := X.model) (N := A) eX.symm X.mem)
      (K.strong_trans _ _ hη (strong_of_equiv K (M := B) (N := Y.model) eY hB))
  · show eY (η (eX.symm (eX a))) = eY (η a)
    rw [Language.Equiv.symm_apply_apply]

/-- **Order embeddings give commuting arrows of the value pairs**: if the template maps
`g_X : A → A'`, `g_Y : B → B'` (i.e. `F_X(f)`, `F_Y(f)`) are strong and commute with the template
inclusions (`η' ∘ g_X = g_Y ∘ η`), their transports along the value isomorphisms are strong
arrows `X → X'`, `Y → Y'` commuting with the inclusions (the pair-of-arrows part of a marked
arrow, Lemma 8.3 clause (2)). -/
theorem infra_83_value_arrow {A B A' B' X Y X' Y' : Model K.τ}
    (hX : K.Mem X) (hY : K.Mem Y) (hA' : K.Mem A') (hB' : K.Mem B')
    (η : A.carrier ↪[K.τ] B.carrier) (η' : A'.carrier ↪[K.τ] B'.carrier)
    (eX : A.carrier ≃[K.τ] X.carrier) (eY : B.carrier ≃[K.τ] Y.carrier)
    (eX' : A'.carrier ≃[K.τ] X'.carrier) (eY' : B'.carrier ≃[K.τ] Y'.carrier)
    (incl : X.carrier ↪[K.τ] Y.carrier) (incl' : X'.carrier ↪[K.τ] Y'.carrier)
    (hincl : ∀ a, incl (eX a) = eY (η a)) (hincl' : ∀ a, incl' (eX' a) = eY' (η' a))
    (gX : A.carrier ↪[K.τ] A'.carrier) (gY : B.carrier ↪[K.τ] B'.carrier)
    (hgX : K.Strong gX) (hgY : K.Strong gY) (hsq : ∀ a, η' (gX a) = gY (η a)) :
    ∃ (onX : X.carrier ↪[K.τ] X'.carrier) (onY : Y.carrier ↪[K.τ] Y'.carrier),
      K.Strong onX ∧ K.Strong onY ∧ (∀ a, onX (eX a) = eX' (gX a)) ∧
      (∀ b, onY (eY b) = eY' (gY b)) ∧ ∀ x, onY (incl x) = incl' (onX x) := by
  refine ⟨(eX'.toEmbedding.comp gX).comp eX.symm.toEmbedding,
    (eY'.toEmbedding.comp gY).comp eY.symm.toEmbedding, ?_, ?_, fun a => ?_, fun b => ?_, fun x => ?_⟩
  · exact K.strong_trans _ _ (strong_of_equiv K (M := X) (N := A) eX.symm hX)
      (K.strong_trans _ _ hgX (strong_of_equiv K (M := A') (N := X') eX' hA'))
  · exact K.strong_trans _ _ (strong_of_equiv K (M := Y) (N := B) eY.symm hY)
      (K.strong_trans _ _ hgY (strong_of_equiv K (M := B') (N := Y') eY' hB'))
  · show eX' (gX (eX.symm (eX a))) = _
    rw [Language.Equiv.symm_apply_apply]
  · show eY' (gY (eY.symm (eY b))) = _
    rw [Language.Equiv.symm_apply_apply]
  · obtain ⟨a, rfl⟩ := eX.surjective x
    show eY' (gY (eY.symm (incl (eX a)))) = incl' (eX' (gX (eX.symm (eX a))))
    rw [hincl, Language.Equiv.symm_apply_apply, Language.Equiv.symm_apply_apply, hincl', hsq]

/-- The doubled-shape system of the pair template at `I`: base copy `F_X(I)`, extension copy
`F_Y(I)`, edge the template inclusion `η_I`. -/
noncomputable def pairPresent83 (FX FY : EM83.FinPieces K) (η : EM83.PiecesHom FX FY)
    (I : Type u) [LinearOrder I] [Nonempty I] : SystemObject K oneVertexShape.{u}.doubled where
  obj := Sum.elim (fun _ => (FX.limit I).obj) (fun _ => (FY.limit I).obj)
  inK
    | Sum.inl _ => (FX.limit_spec I).1
    | Sum.inr _ => (FY.limit_spec I).1
  edge {i j} h :=
    match i, j, h with
    | Sum.inl _, Sum.inr _, _ => η.limMap I
    | Sum.inl _, Sum.inl _, h => False.elim h
    | Sum.inr _, Sum.inr _, h => False.elim h
    | Sum.inr _, Sum.inl _, h => False.elim h
  edge_strong {i j} h :=
    match i, j, h with
    | Sum.inl _, Sum.inr _, _ => η.limMap_strong I
    | Sum.inl _, Sum.inl _, h => False.elim h
    | Sum.inr _, Sum.inr _, h => False.elim h
    | Sum.inr _, Sum.inl _, h => False.elim h

/-- The doubled-shape arrow of an order embedding: `F_X(f)` and `F_Y(f)`. -/
noncomputable def pairOnOrder83 (FX FY : EM83.FinPieces K) (η : EM83.PiecesHom FX FY)
    {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J] (f : I ↪o J) :
    SystemArrow K oneVertexShape.{u}.doubled (pairPresent83 FX FY η I) (pairPresent83 FX FY η J) where
  onVertex
    | Sum.inl _ => EM83.gEmMap (F := FX) f
    | Sum.inr _ => EM83.gEmMap (F := FY) f
  onVertex_strong
    | Sum.inl _ => EM83.gEmMap_strong f
    | Sum.inr _ => EM83.gEmMap_strong f
  comm {i j} h :=
    match i, j, h with
    | Sum.inl _, Sum.inr _, _ => (η.limMap_natural f).symm
    | Sum.inl _, Sum.inl _, h => False.elim h
    | Sum.inr _, Sum.inr _, h => False.elim h
    | Sum.inr _, Sum.inl _, h => False.elim h

/-- **The pair template `F^b` as a `TermTemplate` on the doubled shape** (Lemma 8.3): values
`F_X(I) → F_Y(I)`, order maps `F_X(f)`, `F_Y(f)`; functorial by `gEmMap_id` / `gEmMap_comp`. -/
noncomputable def pairTemplate83 (FX FY : EM83.FinPieces K) (η : EM83.PiecesHom FX FY) :
    TermTemplate K oneVertexShape.{u}.doubled where
  present I _ _ := pairPresent83 FX FY η I
  onOrder f := pairOnOrder83 FX FY η f
  onOrder_id
    | Sum.inl _, x => by
        show EM83.gEmMap (F := FX) _ x = x
        rw [EM83.gEmMap_id]; rfl
    | Sum.inr _, x => by
        show EM83.gEmMap (F := FY) _ x = x
        rw [EM83.gEmMap_id]; rfl
  onOrder_comp f g
    | Sum.inl _, x => by
        show EM83.gEmMap (F := FX) _ x = EM83.gEmMap (F := FX) g (EM83.gEmMap (F := FX) f x)
        rw [EM83.gEmMap_comp]; rfl
    | Sum.inr _, x => by
        show EM83.gEmMap (F := FY) _ x = EM83.gEmMap (F := FY) g (EM83.gEmMap (F := FY) f x)
        rw [EM83.gEmMap_comp]; rfl
/-- The edge of the pair template is the template inclusion. -/
theorem pairTemplate83_edge (FX FY : EM83.FinPieces K) (η : EM83.PiecesHom FX FY)
    (I : Type u) [LinearOrder I] [Nonempty I] (v : (oneVertexShape.{u}).Vertex) x :
    ((pairTemplate83 FX FY η).present I).edge
      (show (oneVertexShape.{u}).doubled.specified (Sum.inl v) (Sum.inr v) from rfl) x =
      η.limMap I x := rfl

/-- **Lemma 8.3, clauses (1)–(2) without the mark**: from one coherent color family, the pair
template `F_X → F_Y` (strong inclusion `η`) has, at every `I` of eligible size, values that are
scheme objects `X_I ⊆ Y_I` at level `|I|` (`τ`-isomorphisms `e_X`, `e_Y` carrying `η_I` to the
inclusion), and every order embedding `f : I ↪o J` gives strong arrows `X_I → X_J`, `Y_I → Y_J`
equal to `F_X(f)`, `F_Y(f)` under the isomorphisms and commuting with the inclusions. The mark
constants give mark tuples `b_I` in `F_Y(I)` fixed by `F_Y(f)`, so the `Y`-arrows carry the
transported marks to the marks. (The realized type of the mark and domination remain.) -/
theorem infra_83_pair_values (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (FX FY : EM83.FinPieces K) (η : EM83.PiecesHom FX FY)
      (b : ∀ (I : Type u) [LinearOrder I] [Nonempty I], Fin Pr.n → (FY.limit I).obj.carrier),
      (∀ (I J : Type u) [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J] (f : I ↪o J)
        (i : Fin Pr.n), EM83.gEmMap (F := FY) f (b I i) = b J i) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (η.limMap I)) ∧
      ∃ (X Y : ∀ (I : Type u) [LinearOrder I] [Nonempty I], #I ∈ P.eligible → SMObject K #I)
        (eX : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
          (FX.limit I).obj.carrier ≃[K.τ] (X I hI).model.carrier)
        (eY : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
          (FY.limit I).obj.carrier ≃[K.τ] (Y I hI).model.carrier)
        (incl : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
          (X I hI).model.carrier ↪[K.τ] (Y I hI).model.carrier),
        (∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible),
          K.Strong (incl I hI) ∧ ∀ a, incl I hI (eX I hI a) = eY I hI (η.limMap I a)) ∧
        ∀ (I J : Type u) [LinearOrder I] [Nonempty I] [LinearOrder J] [Nonempty J] (f : I ↪o J)
          (hI : #I ∈ P.eligible) (hJ : #J ∈ P.eligible),
          ∃ (onX : (X I hI).model.carrier ↪[K.τ] (X J hJ).model.carrier)
            (onY : (Y I hI).model.carrier ↪[K.τ] (Y J hJ).model.carrier),
            K.Strong onX ∧ K.Strong onY ∧
            (∀ a, onX (eX I hI a) = eX J hJ (EM83.gEmMap (F := FX) f a)) ∧
            (∀ b, onY (eY I hI b) = eY J hJ (EM83.gEmMap (F := FY) f b)) ∧
            (∀ x, onY (incl I hI x) = incl J hJ (onX x)) ∧
            ∀ i, onY (eY I hI (b I i)) = eY J hJ (b J i) := by
  obtain ⟨c, hc, hcoh, hXs, hYs, ηXY, FL, ηYL, E, hE, hstr, hnat, hXb, hYb⟩ := infra_83_pairMS2_joint P Pr
  obtain ⟨chX, hX', hidX, hcompX, mX, hvX, hmX, -, -, -, gX, -, -, -, hcX⟩ := hXb
  obtain ⟨chY, hY', hidY, hcompY, mY, hvY, hmY, -, -, -, gY, -, -, -, hcY⟩ := hYb
  have key : ∀ (I : Type u) [LinearOrder I] [Nonempty I] (hI : #I ∈ P.eligible), _ :=
    fun I _ _ hI => infra_83_value_pair P hI rfl (gX I) (hcX I) (gY I) (hcY I) _ _
      (EM83.FinPieces.limit_spec _ I).1 (ηXY.limMap I) (hstr I).1 (mX I) (hmX I).2 (mY I) (hmY I).2
  choose X Y eX eY incl hincl using key
  obtain ⟨b, -, hb, -⟩ := infra_83_pairMS2_Y_marks_c P Pr c hc hcoh hYs
  refine ⟨_, _, ηXY, b, fun I J _ _ _ _ f i => hb I J f i, fun I _ _ => (hstr I).1, X, Y, eX, eY,
    incl, hincl, ?_⟩
  intro I J _ _ _ _ f hI hJ
  obtain ⟨onX, onY, h1, h2, h3, h4, h5⟩ := infra_83_value_arrow (X I hI).mem (Y I hI).mem (EM83.FinPieces.limit_spec _ J).1
    (EM83.FinPieces.limit_spec _ J).1 (ηXY.limMap I) (ηXY.limMap J) (eX I hI) (eY I hI)
    (eX J hJ) (eY J hJ) (incl I hI) (incl J hJ) (hincl I hI).2 (hincl J hJ).2
    (EM83.gEmMap f) (EM83.gEmMap f) (EM83.gEmMap_strong f) (EM83.gEmMap_strong f)
    (fun a => congrFun (congrArg (⇑) ((hnat f).1)) a)
  exact ⟨onX, onY, h1, h2, h3, h4, h5, fun i => (h4 _).trans (congrArg _ (hb I J f i))⟩

end AEC
