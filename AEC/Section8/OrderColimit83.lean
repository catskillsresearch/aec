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

end AEC
