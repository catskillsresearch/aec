module

public import AEC.Section2.ColorSelect
public import AEC.Section2.Reindex

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- A cast along a proof that an index equals itself does not change a diagram. -/
theorem cast_family_self {k : ℕ} (h : k = k) (c : FamilyCode K k) :
    cast (congrArg (FamilyCode K) h) c = c := by
  cases h
  rfl

/-- The index forced by `m ≤ n + 1` and `¬ m ≤ n`. -/
theorem extendIndex {m n : ℕ} (h : ¬ m ≤ n) (hm : m ≤ n + 1) : n + 1 = m :=
  le_antisymm (Nat.succ_le_of_lt (Nat.not_le.mp h)) hm

/-- Colors through arity `n`, extended by one new color at arity `n + 1`. -/
def extendColor {n : ℕ} (d : (m : ℕ) → m ≤ n → 0 < m → FamilyCode K m)
    (c : FamilyCode K (n + 1)) (m : ℕ) (hm : m ≤ n + 1) (hm0 : 0 < m) : FamilyCode K m :=
  if h : m ≤ n then d m h hm0
  else cast (congrArg (FamilyCode K) (extendIndex h hm)) c

theorem extendColor_of_le {n : ℕ} (d : (m : ℕ) → m ≤ n → 0 < m → FamilyCode K m)
    (c : FamilyCode K (n + 1)) {m : ℕ} (hm : m ≤ n + 1) (hm0 : 0 < m) (h : m ≤ n) :
    extendColor d c m hm hm0 = d m h hm0 := by
  simp [extendColor, h]

theorem extendColor_top {n : ℕ} (d : (m : ℕ) → m ≤ n → 0 < m → FamilyCode K m)
    (c : FamilyCode K (n + 1)) :
    extendColor d c (n + 1) le_rfl (Nat.succ_pos n) = c := by
  have hnot : ¬ n + 1 ≤ n := Nat.not_le.mpr (Nat.lt_succ_self n)
  simp [extendColor, hnot]

/-- A sample of size at least `κ` whose every positive `m`-tuple, `m ≤ n`, has diagram `d m`. -/
def JointSample (n : ℕ) (d : (m : ℕ) → m ≤ n → 0 < m → FamilyCode K m)
    (κ : Cardinal.{u}) : Prop :=
  ∃ (α : Type u) (_ : LinearOrder α) (M : Model K.τ) (hM : K.Mem M)
    (base : α → M.carrier) (hbase : Function.Injective base),
    κ ≤ #α ∧
      ∀ (m : ℕ) (hm : m ≤ n) (hm0 : 0 < m) (s : Finset α) (hs : s.card = m),
        tupleCode hM base hbase s hs = d m hm hm0

/-- The diagram of an `m`-tuple is unchanged by viewing its indices as elements of a subset. -/
theorem tupleCode_subtype {α : Type u} [LinearOrder α] {M : Model K.τ} (hM : K.Mem M)
    (base : α → M.carrier) (hbase : Function.Injective base) {H : Set α} {m : ℕ}
    (s : Finset (↥H)) (hs : s.card = m) :
    tupleCode hM (fun x : ↥H => base x.1) (fun x y hxy => Subtype.ext (hbase hxy)) s hs =
      tupleCode hM base hbase (s.map (Function.Embedding.subtype H))
        (by rw [Finset.card_map, hs]) := by
  let sα : Finset α := s.map (Function.Embedding.subtype H)
  have hsα : sα.card = m := by rw [Finset.card_map, hs]
  have henum : (fun i => (s.orderEmbOfFin hs i).1) = ⇑(sα.orderEmbOfFin hsα) :=
    Finset.orderEmbOfFin_unique hsα
      (fun i => Finset.mem_map.mpr
        ⟨s.orderEmbOfFin hs i, Finset.orderEmbOfFin_mem s hs i, rfl⟩)
      (fun i j hij => Subtype.coe_lt_coe.mpr ((s.orderEmbOfFin hs).strictMono hij))
  have hbase' : (fun i => base (s.orderEmbOfFin hs i).1) =
      fun i => base (sα.orderEmbOfFin hsα i) := by
    funext i
    exact congrArg base (congrFun henum i)
  simp only [tupleCode]
  exact readFamily_eq hM hbase' _ _

/-- Colors `d₁, …, dₙ` for which arbitrarily large samples are homogeneous at every
arity up to `n`. -/
structure Tower (K : AbstractElementaryClass.{u}) (n : ℕ) where
  color : (m : ℕ) → m ≤ n → 0 < m → FamilyCode K m
  joint : ∀ κ : Cardinal.{u}, aleph0 ≤ κ → JointSample n color κ

variable [ArbitrarilyLarge K]

/-- There is no positive arity at most `0`, so the empty tower asks only for large samples. -/
noncomputable def towerZero : Tower K 0 where
  color m hm hm0 := False.elim (Nat.lt_irrefl 0 (lt_of_lt_of_le hm0 hm))
  joint κ hκ := by
    obtain ⟨M, hM, hbig⟩ := ArbitrarilyLarge.large (K := K) κ
    let α := κ.ord.ToType
    have hα : #α = κ := Cardinal.mk_ord_toType _
    obtain ⟨emb⟩ := (le_def α M.carrier).mp (hα ▸ hbig)
    refine ⟨α, inferInstance, M, hM, emb, emb.injective, ?_, ?_⟩
    · exact le_of_eq hα.symm
    · intro m hm hm0
      exact False.elim (Nat.lt_irrefl 0 (lt_of_lt_of_le hm0 hm))

/-- One new color at arity `n + 1`, chosen so that samples already homogeneous for the
earlier colors thin to arbitrarily large `(n + 1)`-homogeneous samples. -/
theorem exists_extend {n : ℕ} (T : Tower K n) :
    ∃ c : FamilyCode K (n + 1), ∀ κ : Cardinal.{u}, aleph0 ≤ κ →
      JointSample (n + 1) (extendColor T.color c) κ := by
  by_contra hbad
  have hforall : ∀ c : FamilyCode K (n + 1), ∃ κ : Cardinal.{u},
      aleph0 ≤ κ ∧ ¬ JointSample (n + 1) (extendColor T.color c) κ := by
    intro c
    by_contra hc
    apply hbad
    refine ⟨c, ?_⟩
    intro κ hκ
    by_contra hno
    exact hc ⟨κ, hκ, hno⟩
  let κc : FamilyCode K (n + 1) → Cardinal.{u} := fun c => Classical.choose (hforall c)
  have hκc : ∀ c, aleph0 ≤ κc c ∧ ¬ JointSample (n + 1) (extendColor T.color c) (κc c) :=
    fun c => Classical.choose_spec (hforall c)
  let ν : Cardinal.{u} := Order.succ (sum κc)
  have hν : aleph0 ≤ ν :=
    ((hκc default).1.trans (le_sum_apply κc default)).trans (Order.le_succ _)
  let ξ : Cardinal.{u} := #(FamilyCode K (n + 1) ⊕ Enum K)
  have hξ : aleph0 ≤ ξ := by
    refine (isLSBound_ls K).1.trans ?_
    rw [← enum_card]
    exact mk_le_of_injective (f := fun e : Enum K => Sum.inr e) Sum.inr_injective
  let N : ℕ := n + 1
  have hN : 0 < N := Nat.succ_pos n
  let R := recursivePartitionBound N ξ ν
  have htarget : aleph0 ≤ max R ν := hν.trans (le_max_right _ _)
  obtain ⟨α, _, M, hM, base, hbase, hαbig, hhom⟩ := T.joint (max R ν) htarget
  have hαR : R ≤ #α := (le_max_left R ν).trans hαbig
  let color : {s : Finset α // s.card = N} → FamilyCode K N ⊕ Enum K :=
    fun s => Sum.inl (tupleCode hM base hbase s.1 s.2)
  obtain ⟨H, hH, paint, hpaint⟩ := erdos_color hξ hν hN hαR rfl color
  have hHinf : H.Infinite := aleph0_le_mk_set.mp (hν.trans hH)
  obtain ⟨t0, ht0sub, ht0card⟩ := Set.Infinite.exists_subset_card_eq (s := H) hHinf N
  have hpaint0 : color ⟨t0, ht0card⟩ = paint :=
    hpaint t0 ht0card fun x hx => ht0sub hx
  cases paint with
  | inr e =>
      have hbadc :
          Sum.inl (tupleCode hM base hbase t0 ht0card) = Sum.inr e := by
        simpa [color] using hpaint0
      cases hbadc
  | inl c =>
      have hbigH : κc c ≤ #H :=
        (le_sum_apply κc c).trans (Order.le_succ _) |>.trans hH
      have hmono : JointSample N (extendColor T.color c) (κc c) := by
        refine ⟨↥H, inferInstance, M, hM, fun x => base x.1,
          fun x y hxy => Subtype.ext (hbase hxy), ?_, ?_⟩
        · simpa using hbigH
        · intro m hm hm0 s hs
          have hcode := tupleCode_subtype hM base hbase s hs
          let sα : Finset α := s.map (Function.Embedding.subtype H)
          have hsα : sα.card = m := by rw [Finset.card_map, hs]
          by_cases hle : m ≤ n
          · have hprev : tupleCode hM base hbase sα hsα = T.color m hle hm0 :=
              hhom m hle hm0 sα hsα
            rw [hcode, hprev]
            exact (extendColor_of_le T.color c hm hm0 hle).symm
          · have hmeq : m = n + 1 := (extendIndex hle hm).symm
            subst hmeq
            have hsub : ∀ x ∈ sα, x ∈ H := by
              intro x hx
              obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
              rw [← hy]
              exact y.2
            have hpaint' := hpaint sα hsα hsub
            have hc : tupleCode hM base hbase sα hsα = c := by
              have : color ⟨sα, hsα⟩ = Sum.inl c := hpaint'
              simpa [color] using this
            rw [hcode, hc]
            rw [extendColor, dite_eq_right (Nat.not_le.mpr (Nat.lt_succ_self n))]
            exact (cast_family_self
              (extendIndex (Nat.not_le.mpr (Nat.lt_succ_self n)) hm) c).symm
      exact (hκc c).2 hmono

noncomputable def towerSucc {n : ℕ} (T : Tower K n) : Tower K (n + 1) :=
  let spec := exists_extend (K := K) T
  let c := Classical.choose spec
  { color := extendColor T.color c
    joint := Classical.choose_spec spec }

noncomputable def colorTower : (n : ℕ) → Tower K n
  | 0 => towerZero
  | n + 1 => towerSucc (colorTower n)

/-- The standard color `dₙ`. -/
noncomputable def standardColor (n : ℕ) (hn : 0 < n) : FamilyCode K n :=
  (colorTower n).color n le_rfl hn

theorem standardColor_unbounded (n : ℕ) (hn : 0 < n) (κ : Cardinal.{u}) (hκ : aleph0 ≤ κ) :
    MonoSample (K := K) (standardColor (K := K) n hn) κ := by
  obtain ⟨α, _, M, hM, base, hbase, hcard, hhom⟩ := (colorTower (K := K) n).joint κ hκ
  refine ⟨α, inferInstance, M, hM, base, hbase, hcard, ?_⟩
  intro s hs
  simpa [standardColor] using hhom n le_rfl hn s hs

/-- A color stored in a taller tower is the standard color of its own arity. -/
theorem tower_color_eq_standard {n m : ℕ} (hle : m ≤ n) (hm0 : 0 < m) :
    (colorTower (K := K) n).color m hle hm0 = standardColor (K := K) m hm0 := by
  induction n with
  | zero =>
      exact False.elim (Nat.lt_irrefl 0 (lt_of_lt_of_le hm0 hle))
  | succ n ih =>
      by_cases hmn : m ≤ n
      · simp only [colorTower, towerSucc, extendColor, hmn]
        exact ih _
      · have htop : m = n + 1 := (extendIndex hmn hle).symm
        subst htop
        simp only [standardColor, colorTower, towerSucc]

/-- An order embedding of index sets cannot raise cardinality. -/
theorem orderEmb_card_le {m n : ℕ} (e : Fin m ↪o Fin n) : m ≤ n := by
  have hcard : (Finset.univ.map e.toEmbedding).card ≤ Fintype.card (Fin n) :=
    Finset.card_le_univ _
  simpa [Finset.card_map, Finset.card_univ, Fintype.card_fin] using hcard

/-- `dₙ` restricts along every order embedding to the earlier color `dₘ`. -/
theorem standardColor_restrict {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (e : Fin m ↪o Fin n) :
    FamilyCode.pull e (standardColor (K := K) n hn) = standardColor (K := K) m hm := by
  have hmn : m ≤ n := orderEmb_card_le e
  obtain ⟨α, _, M, hM, base, hbase, hcard, hhom⟩ := (colorTower (K := K) n).joint aleph0
    (le_refl _)
  have hinf : Infinite α := Cardinal.aleph0_le_mk_iff.mp hcard
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq α n
  let φ : Fin n → α := s.orderEmbOfFin hs
  have hφmono : StrictMono φ := (s.orderEmbOfFin hs).strictMono
  have htcard : ((Finset.univ : Finset (Fin m)).map
      ⟨fun i => φ (e i), fun i j hij =>
        e.injective ((s.orderEmbOfFin hs).injective hij)⟩).card = m := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  let t : Finset α := (Finset.univ : Finset (Fin m)).map
    ⟨fun i => φ (e i), fun i j hij =>
      e.injective ((s.orderEmbOfFin hs).injective hij)⟩
  have ht : t.card = m := htcard
  have hinc : (fun i => φ (e i)) = ⇑(t.orderEmbOfFin ht) :=
    Finset.orderEmbOfFin_unique ht
      (fun i => Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      (fun i j hij => hφmono (e.lt_iff_lt.mpr hij))
  have hwhole : tupleCode hM base hbase s hs = standardColor n hn := by
    simpa [standardColor] using hhom n le_rfl hn s hs
  have hpart : tupleCode hM base hbase t ht = standardColor m hm := by
    rw [← tower_color_eq_standard (hmn) hm]
    exact hhom m hmn hm t ht
  have hpull : readFamily hM (fun i => base (φ (e i)))
        (hbase.comp ((s.orderEmbOfFin hs).injective.comp e.injective)) =
      FamilyCode.pull e (readFamily hM (fun i => base (φ i))
        (hbase.comp (s.orderEmbOfFin hs).injective)) :=
    readFamily_pull hM e (fun i => base (φ i)) (hbase.comp (s.orderEmbOfFin hs).injective)
  have hleft : readFamily hM (fun i => base (φ (e i)))
      (hbase.comp ((s.orderEmbOfFin hs).injective.comp e.injective)) =
      tupleCode hM base hbase t ht := by
    simp only [tupleCode]
    have hfun : (fun i => base (φ (e i))) = fun i => base (t.orderEmbOfFin ht i) := by
      funext i
      exact congrArg base (congrFun hinc i)
    exact readFamily_eq hM hfun _ _
  have hright : readFamily hM (fun i => base (φ i))
      (hbase.comp (s.orderEmbOfFin hs).injective) = tupleCode hM base hbase s hs := by
    simp only [tupleCode]
    rfl
  rw [← hpart, ← hleft, hpull, hright, hwhole]

end
end AEC
