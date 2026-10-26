module

public import AEC.Section1.ArbitrarilyLarge
public import AEC.Section2.FamilyCode
public import AEC.Section2.Partition
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

noncomputable instance (n : ℕ) : Inhabited (FamilyCode K n) where
  default :=
    { code := fun _ =>
        { same := fun _ _ => True
          hold := fun _ _ => True
          apply := fun _ _ => enumNth K 0 }
      link := fun _ _ _ _ => True }

/-- Reading a family depends only on the enumerated elements, not on which injectivity proof
is supplied. -/
theorem readFamily_eq {n : ℕ} {M : Model K.τ} (hM : K.Mem M)
    {base₁ base₂ : Fin n → M.carrier} (hbase : base₁ = base₂)
    (h₁ : Function.Injective base₁) (h₂ : Function.Injective base₂) :
    readFamily hM base₁ h₁ = readFamily hM base₂ h₂ := by
  subst hbase
  have : h₁ = h₂ := Subsingleton.elim h₁ h₂
  subst this
  rfl

/-- The diagram of `n` increasing indices from an injective tuple. -/
noncomputable def tupleCode {α : Type u} [LinearOrder α] {M : Model K.τ} (hM : K.Mem M)
    (base : α → M.carrier) (hbase : Function.Injective base) {n : ℕ}
    (s : Finset α) (hs : s.card = n) : FamilyCode K n :=
  readFamily hM (fun i => base (s.orderEmbOfFin hs i))
    (fun i j hij => (s.orderEmbOfFin hs).injective (hbase hij))

/-- A sample of size at least `κ` in which every `n`-tuple has diagram `c`. -/
def MonoSample {n : ℕ} (c : FamilyCode K n) (κ : Cardinal.{u}) : Prop :=
  ∃ (α : Type u) (_ : LinearOrder α) (M : Model K.τ) (hM : K.Mem M)
    (base : α → M.carrier) (hbase : Function.Injective base),
    κ ≤ #α ∧ ∀ (s : Finset α) (hs : s.card = n), tupleCode hM base hbase s hs = c

/-- Each summand is at most the indexed sum. -/
theorem le_sum_apply {ι : Type u} (f : ι → Cardinal.{u}) (i : ι) : f i ≤ sum f := by
  rw [sum, ← mk_out (f i)]
  refine mk_le_of_injective (f := fun x : (f i).out => (⟨i, x⟩ : Σ j, (f j).out)) ?_
  intro a b h
  exact eq_of_heq (Sigma.ext_iff.mp h).2

/-- One diagram occurs as the color of every `n`-tuple in arbitrarily large samples.
If every color admitted only samples below some bound, the cardinal successor of the sum of
those bounds would still carry a monochromatic sample by Lemma 2.5. -/
theorem exists_mono_color (n : ℕ) (hn : 0 < n) [ArbitrarilyLarge K] :
    ∃ c : FamilyCode K n, ∀ κ : Cardinal.{u}, aleph0 ≤ κ → MonoSample (K := K) c κ := by
  by_contra hbad
  have hforall : ∀ c : FamilyCode K n, ∃ κ : Cardinal.{u}, aleph0 ≤ κ ∧ ¬ MonoSample c κ := by
    intro c
    by_contra hc
    apply hbad
    refine ⟨c, ?_⟩
    intro κ hκ
    by_contra hno
    exact hc ⟨κ, hκ, hno⟩
  let κc : FamilyCode K n → Cardinal.{u} := fun c => Classical.choose (hforall c)
  have hκc : ∀ c, aleph0 ≤ κc c ∧ ¬ MonoSample c (κc c) := fun c =>
    Classical.choose_spec (hforall c)
  let ν : Cardinal.{u} := Order.succ (sum κc)
  have hν : aleph0 ≤ ν :=
    ((hκc default).1.trans (le_sum_apply κc default)).trans (Order.le_succ _)
  let ξ : Cardinal.{u} := #(FamilyCode K n ⊕ Enum K)
  have hξ : aleph0 ≤ ξ := by
    refine (isLSBound_ls K).1.trans ?_
    rw [← enum_card]
    exact mk_le_of_injective (f := fun e : Enum K => Sum.inr e) Sum.inr_injective
  let R := recursivePartitionBound n ξ ν
  obtain ⟨M, hM, hbig⟩ := ArbitrarilyLarge.large (K := K) (max R ν)
  let α := (max R ν).ord.ToType
  have hαcard : #α = max R ν := Cardinal.mk_ord_toType _
  have hαR : R ≤ #α := by
    rw [hαcard]
    exact le_max_left _ _
  obtain ⟨emb⟩ := (le_def α M.carrier).mp (hαcard ▸ hbig)
  let color : {s : Finset α // s.card = n} → FamilyCode K n ⊕ Enum K :=
    fun s => Sum.inl (tupleCode hM (fun i : α => emb i) emb.injective s.1 s.2)
  obtain ⟨H, hH, paint, hpaint⟩ :=
    erdos_color hξ hν hn (by
      rw [hαcard]
      exact le_max_left _ _) rfl color
  have hHinf : H.Infinite := aleph0_le_mk_set.mp (hν.trans hH)
  obtain ⟨t0, ht0sub, ht0card⟩ := Set.Infinite.exists_subset_card_eq (s := H) hHinf n
  have hpaint0 : color ⟨t0, ht0card⟩ = paint :=
    hpaint t0 ht0card fun x hx => ht0sub hx
  cases paint with
  | inr e =>
      have hbadc : Sum.inl (tupleCode hM (fun i : α => emb i) emb.injective t0 ht0card) =
          Sum.inr e := by
        simpa [color] using hpaint0
      cases hbadc
  | inl c =>
      have hbigH : κc c ≤ #H :=
        (le_sum_apply κc c).trans (Order.le_succ _) |>.trans hH
      have hmono : MonoSample c (κc c) := by
        refine ⟨↥H, inferInstance, M, hM, fun x => emb x.1, ?_, ?_, ?_⟩
        · intro x y hxy
          exact Subtype.ext (emb.injective hxy)
        · simpa using hbigH
        · intro s hs
          let sα : Finset α := s.map (Function.Embedding.subtype H)
          have hsα : sα.card = n := by
            rw [Finset.card_map, hs]
          have hsub : ∀ x ∈ sα, x ∈ H := by
            intro x hx
            obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hx
            rw [← hy]
            exact y.2
          have hcolor := hpaint sα hsα hsub
          have henum : (fun i => (s.orderEmbOfFin hs i).1) = ⇑(sα.orderEmbOfFin hsα) :=
            Finset.orderEmbOfFin_unique hsα
              (fun i => Finset.mem_map.mpr
                ⟨s.orderEmbOfFin hs i, Finset.orderEmbOfFin_mem s hs i, rfl⟩)
              (fun i j hij => Subtype.coe_lt_coe.mpr ((s.orderEmbOfFin hs).strictMono hij))
          have hbase : (fun i => emb (s.orderEmbOfFin hs i).1) =
              fun i => emb (sα.orderEmbOfFin hsα i) := by
            funext i
            exact congrArg emb (congrFun henum i)
          have : tupleCode hM (fun x : ↥H => emb x.1)
              (fun x y hxy => Subtype.ext (emb.injective hxy)) s hs =
              tupleCode hM (fun i : α => emb i) emb.injective sα hsα := by
            simp only [tupleCode]
            exact readFamily_eq hM hbase _ _
          rw [this]
          have : color ⟨sα, hsα⟩ = Sum.inl c := hcolor
          simpa [color] using this
      exact (hκc c).2 hmono

end
end AEC
