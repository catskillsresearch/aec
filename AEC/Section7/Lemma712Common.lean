module

public import AEC.Section7.Lemma712Uniqueness

/-!
# Lemma 7.12 (2): the common objects, packed form (cycle 89)

Level-`μ` objects of the single-model scheme all live on the fixed carrier `μ.ord.ToType`, so an
arrow between them is recorded as a plain function `μ.ord.ToType → μ.ord.ToType` together with the
predicate `infra_712u_IsArr` (it underlies a strong system arrow). This makes the recursion state of
the common objects `N_j` stage-independent.

* `infra_712u_packed_succ`: the successor step (`infra_712u_chain_succ`) in packed form.
* `infra_712u_packed_limit`: the limit step (directed union `infra_78_chain_union_kappa` and
  `infra_712u_factor_continuous` on both chains) in packed form.
-/

@[expose] public section

namespace AEC
noncomputable section
open Cardinal FirstOrder
variable {K : AbstractElementaryClass.{u}}

/-- `f` underlies a strong system arrow `X → Y` between level-`μ` objects. -/
def infra_712u_IsArr {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    (X Y : P.scheme.Object μ hμ) (f : μ.ord.ToType → μ.ord.ToType) : Prop :=
  ∃ a : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y),
    ∀ x, a.onVertex PUnit.unit x = f x

theorem infra_712u_IsArr.of_arrow {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X Y : P.scheme.Object μ hμ}
    (a : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y)) :
    infra_712u_IsArr X Y (fun x => a.onVertex PUnit.unit x) := ⟨a, fun _ => rfl⟩

/-- The arrow underlying an `infra_712u_IsArr` function. -/
def infra_712u_IsArr.arr {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X Y : P.scheme.Object μ hμ} {f : μ.ord.ToType → μ.ord.ToType} (h : infra_712u_IsArr X Y f) :
    SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y) :=
  Classical.choose h

theorem infra_712u_IsArr.arr_apply {P : SingleModelData K} {μ : Cardinal.{u}}
    {hμ : μ ∈ P.eligible} {X Y : P.scheme.Object μ hμ} {f : μ.ord.ToType → μ.ord.ToType}
    (h : infra_712u_IsArr X Y f) (x) : h.arr.onVertex PUnit.unit x = f x :=
  Classical.choose_spec h x

theorem infra_712u_IsArr.comp {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X Y Z : P.scheme.Object μ hμ} {f g : μ.ord.ToType → μ.ord.ToType}
    (hf : infra_712u_IsArr X Y f) (hg : infra_712u_IsArr Y Z g) :
    infra_712u_IsArr X Z (g ∘ f) :=
  ⟨SystemArrow.comp hf.arr hg.arr, fun x => by
    show hg.arr.onVertex PUnit.unit (hf.arr.onVertex PUnit.unit x) = g (f x)
    exact (congrArg (hg.arr.onVertex PUnit.unit) (hf.arr_apply x)).trans (hg.arr_apply _)⟩

theorem infra_712u_IsArr.id {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    (X : P.scheme.Object μ hμ) : infra_712u_IsArr X X id :=
  ⟨SystemArrow.refl _, fun _ => rfl⟩

/-- Two arrows with the same underlying function are equal. -/
theorem infra_712u_arrow_ext {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {X Y : P.scheme.Object μ hμ}
    {a b : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y)}
    (h : ∀ x, a.onVertex PUnit.unit x = b.onVertex PUnit.unit x) : a = b :=
  SystemArrow.ext fun v => by
    have hv : v = PUnit.unit := Subsingleton.elim _ _
    subst hv
    exact DFunLike.ext _ _ h

section Packed
variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
  {A : P.scheme.Object μ hμ} {L L' : TupleList P.scheme hμ A} [LinearOrder L.δ]
  [LinearOrder L'.δ] (C : TiedListWitnessingChain L) (C' : TiedListWitnessingChain L')

/-- **7.12(2) successor, packed form (proved, cycle 89).** `infra_712u_chain_succ` with the
arrows recorded as functions on the fixed carrier. -/
theorem infra_712u_packed_succ (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
    (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i))
    (hm : ∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _))
    (j : L.δ) (k : WithTop L.δ) (hj : (j : WithTop L.δ) < k)
    (k' : WithTop L'.δ) (hj' : ((e j : L'.δ) : WithTop L'.δ) < k')
    (N : P.scheme.Object μ hμ) (G G' : μ.ord.ToType → μ.ord.ToType)
    (hG : infra_712u_IsArr (C.stage j) N G) (hG' : infra_712u_IsArr (C'.stage (e j)) N G')
    (hA : ∀ x, G ((C.into j).onVertex PUnit.unit x) = G' ((C'.into (e j)).onVertex PUnit.unit x)) :
    ∃ (N₁ : P.scheme.Object μ hμ) (G₁ G₁' h : μ.ord.ToType → μ.ord.ToType),
      infra_712u_IsArr N N₁ h ∧ infra_712u_IsArr (C.stage k) N₁ G₁ ∧
      infra_712u_IsArr (C'.stage k') N₁ G₁' ∧
      (∀ x, G₁ ((C.step hj.le).onVertex PUnit.unit x) = h (G x)) ∧
      (∀ x, G₁' ((C'.step hj'.le).onVertex PUnit.unit x) = h (G' x)) ∧
      ∀ a, G₁ (C.mark j k hj a).2 = G₁' (C'.mark (e j) k' hj' (ei j a)).2 := by
  have hcomm : SystemArrow.comp (C.into j) hG.arr = SystemArrow.comp (C'.into (e j)) hG'.arr :=
    infra_712u_arrow_ext fun x => by
      show hG.arr.onVertex PUnit.unit ((C.into j).onVertex PUnit.unit x) =
        hG'.arr.onVertex PUnit.unit ((C'.into (e j)).onVertex PUnit.unit x)
      rw [hG.arr_apply, hG'.arr_apply]
      exact hA x
  obtain ⟨N₁, h, k₁, k₁', H1, H2, H3⟩ := infra_712u_chain_succ P hμ h0 h1 C C' e ei hm j k hj k' hj'
    hG.arr hG'.arr hcomm
  refine ⟨N₁, fun x => k₁.onVertex PUnit.unit x, fun x => k₁'.onVertex PUnit.unit x,
    fun x => h.onVertex PUnit.unit x, infra_712u_IsArr.of_arrow h, infra_712u_IsArr.of_arrow k₁,
    infra_712u_IsArr.of_arrow k₁', fun x => ?_, fun x => ?_, fun a => ?_⟩
  · have := DFunLike.congr_fun (H1 PUnit.unit) x
    exact this.trans (congrArg (h.onVertex PUnit.unit) (hG.arr_apply x))
  · have := DFunLike.congr_fun (H2 PUnit.unit) x
    exact this.trans (congrArg (h.onVertex PUnit.unit) (hG'.arr_apply x))
  · exact eq_of_heq (Sigma.mk.inj_iff.mp (H3 a)).2

/-- A witnessing chain's reflexive step is the identity (idempotent and injective). -/
theorem infra_712u_step_refl {L₀ : TupleList P.scheme hμ A} [LinearOrder L₀.δ]
    (D : TiedListWitnessingChain L₀) (i : WithTop L₀.δ) :
    D.step (le_refl i) = SystemArrow.refl _ :=
  infra_712u_arrow_ext fun x => by
    have h := DFunLike.congr_fun (D.step_comp (le_refl i) (le_refl i) PUnit.unit) x
    exact ((D.step (le_refl i)).onVertex PUnit.unit).injective h

/-- A witnessing chain's steps compose. -/
theorem infra_712u_step_trans {L₀ : TupleList P.scheme hμ A} [LinearOrder L₀.δ]
    (D : TiedListWitnessingChain L₀) {a b c : WithTop L₀.δ} (h₁ : a ≤ b) (h₂ : b ≤ c) :
    D.step (h₁.trans h₂) = SystemArrow.comp (D.step h₁) (D.step h₂) :=
  infra_712u_arrow_ext fun x => (DFunLike.congr_fun (D.step_comp h₁ h₂ PUnit.unit) x).symm

/-- **7.12(2) limit, packed form (proved, cycle 89).** At a limit stage `k` (neither first nor
a successor) with at most `μ` earlier indices, a coherent system of common objects `N i`
(`i < k`, transition functions `n`) receiving both chains compatibly has a directed union `U`
(`infra_78_chain_union_kappa`) which receives both continuous stages `M_k`, `M'_{E k}` over the
earlier ones (`infra_712u_factor_continuous`). -/
theorem infra_712u_packed_limit (E : WithTop L.δ ≃o WithTop L'.δ) (k : WithTop L.δ)
    (hs : ∀ i, ¬ i ⋖ k) (hne : ∃ i, i < k) (hcard : #(WithTop L.δ) ≤ μ)
    (N : Set.Iio k → P.scheme.Object μ hμ) (G G' : Set.Iio k → μ.ord.ToType → μ.ord.ToType)
    (n : Set.Iio k → Set.Iio k → μ.ord.ToType → μ.ord.ToType)
    (hG : ∀ i, infra_712u_IsArr (C.stage i.1) (N i) (G i))
    (hG' : ∀ i, infra_712u_IsArr (C'.stage (E i.1)) (N i) (G' i))
    (hn : ∀ i j, i ≤ j → infra_712u_IsArr (N i) (N j) (n i j))
    (hnid : ∀ i x, n i i x = x)
    (hntr : ∀ i j l, i ≤ j → j ≤ l → ∀ x, n i l x = n j l (n i j x))
    (hnG : ∀ i j (h : i ≤ j) x,
      n i j (G i x) = G j ((C.step (show i.1 ≤ j.1 from h)).onVertex PUnit.unit x))
    (hnG' : ∀ i j (h : i ≤ j) x,
      n i j (G' i x) = G' j ((C'.step (E.monotone (show i.1 ≤ j.1 from h))).onVertex PUnit.unit x)) :
    ∃ (U : P.scheme.Object μ hμ) (Gk Gk' : μ.ord.ToType → μ.ord.ToType)
      (l : Set.Iio k → μ.ord.ToType → μ.ord.ToType),
      infra_712u_IsArr (C.stage k) U Gk ∧ infra_712u_IsArr (C'.stage (E k)) U Gk' ∧
      (∀ i, infra_712u_IsArr (N i) U (l i)) ∧
      (∀ i j, i ≤ j → ∀ x, l j (n i j x) = l i x) ∧
      (∀ i x, Gk ((C.step (le_of_lt i.2)).onVertex PUnit.unit x) = l i (G i x)) ∧
      (∀ i x, Gk' ((C'.step (E.monotone (le_of_lt i.2))).onVertex PUnit.unit x) =
        l i (G' i x)) := by
  classical
  obtain ⟨i0, hi0⟩ := hne
  have : Nonempty (Set.Iio k) := ⟨⟨i0, hi0⟩⟩
  have hι : #(Set.Iio k) ≤ μ := (Cardinal.mk_subtype_le _).trans hcard
  let st : ∀ {a b : Set.Iio k}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hμ (N a)) (P.scheme.asSystem hμ (N b)) :=
    fun {a b} h => (hn a b h).arr
  have hst : ∀ {a b : Set.Iio k} (h : a ≤ b) x, (st h).onVertex PUnit.unit x = n a b x :=
    fun {a b} h x => (hn a b h).arr_apply x
  have hrefl : ∀ a, st (le_refl a) = SystemArrow.refl _ := fun a =>
    infra_712u_arrow_ext fun x => (hst (le_refl a) x).trans (hnid a x)
  have htrans : ∀ {a b c : Set.Iio k} (h₁ : a ≤ b) (h₂ : b ≤ c),
      st (h₁.trans h₂) = SystemArrow.comp (st h₁) (st h₂) := fun {a b c} h₁ h₂ =>
    infra_712u_arrow_ext fun x => by
      show (st (h₁.trans h₂)).onVertex PUnit.unit x =
        (st h₂).onVertex PUnit.unit ((st h₁).onVertex PUnit.unit x)
      rw [hst (h₁.trans h₂), hst h₂, hst h₁]
      exact hntr a b c h₁ h₂ x
  obtain ⟨U, leg, -, hleg, -, -, -⟩ := infra_78_chain_union_kappa hμ hι N st hrefl htrans
  have hlegp : ∀ {a b : Set.Iio k} (h : a ≤ b) x,
      (leg b).onVertex PUnit.unit (n a b x) = (leg a).onVertex PUnit.unit x := by
    intro a b h x
    rw [← hst h x]
    exact DFunLike.congr_fun (congrArg (fun f => f.onVertex PUnit.unit) (hleg h)) x
  obtain ⟨f, hf⟩ := infra_712u_factor_continuous hμ hι (fun a : Set.Iio k => C.stage a.1)
    (fun {a b} h => C.step h) (fun a => infra_712u_step_refl C a.1)
    (fun h₁ h₂ => infra_712u_step_trans C h₁ h₂) (C.stage k) (fun a => C.step (le_of_lt a.2))
    (fun {a b} h => (infra_712u_step_trans C (a := a.1) (b := b.1) h (le_of_lt b.2)).symm)
    (fun x => by
      obtain ⟨i, h, y, hy⟩ := C.continuous k hs ⟨i0, hi0⟩ PUnit.unit x
      exact ⟨⟨i, h⟩, y, hy⟩)
    (fun a => SystemArrow.comp (hG a).arr (leg a))
    (fun {a b} h => infra_712u_arrow_ext fun x => by
      show (leg b).onVertex PUnit.unit ((hG b).arr.onVertex PUnit.unit
        ((C.step h).onVertex PUnit.unit x)) =
        (leg a).onVertex PUnit.unit ((hG a).arr.onVertex PUnit.unit x)
      rw [(hG b).arr_apply, (hG a).arr_apply, ← hnG a b h x]
      exact hlegp h _)
  have hs' : ∀ i', ¬ i' ⋖ E k := fun i' hc => by
    obtain ⟨i, rfl⟩ := E.surjective i'
    exact hs i ((apply_covBy_apply_iff E).1 hc)
  obtain ⟨f', hf'⟩ := infra_712u_factor_continuous hμ hι (fun a : Set.Iio k => C'.stage (E a.1))
    (fun {a b} h => C'.step (E.monotone h)) (fun a => infra_712u_step_refl C' (E a.1))
    (fun h₁ h₂ => infra_712u_step_trans C' _ _) (C'.stage (E k))
    (fun a => C'.step (E.monotone (le_of_lt a.2)))
    (fun {a b} h => (infra_712u_step_trans C' (E.monotone h) (E.monotone (le_of_lt b.2))).symm)
    (fun x => by
      obtain ⟨i', h, y, hy⟩ := C'.continuous (E k) hs' ⟨E i0, E.strictMono hi0⟩ PUnit.unit x
      obtain ⟨i, rfl⟩ := E.surjective i'
      exact ⟨⟨i, E.lt_iff_lt.1 h⟩, y, hy⟩)
    (fun a => SystemArrow.comp (hG' a).arr (leg a))
    (fun {a b} h => infra_712u_arrow_ext fun x => by
      show (leg b).onVertex PUnit.unit ((hG' b).arr.onVertex PUnit.unit
        ((C'.step (E.monotone h)).onVertex PUnit.unit x)) =
        (leg a).onVertex PUnit.unit ((hG' a).arr.onVertex PUnit.unit x)
      rw [(hG' b).arr_apply, (hG' a).arr_apply, ← hnG' a b h x]
      exact hlegp h _)
  refine ⟨U, fun x => f.onVertex PUnit.unit x, fun x => f'.onVertex PUnit.unit x,
    fun i x => (leg i).onVertex PUnit.unit x,
    infra_712u_IsArr.of_arrow f, infra_712u_IsArr.of_arrow f', fun i => infra_712u_IsArr.of_arrow _,
    fun i j hij x => hlegp hij x, fun i x => ?_, fun i x => ?_⟩
  · have := hf i x
    rw [← (hG i).arr_apply]
    exact this
  · have := hf' i x
    rw [← (hG' i).arr_apply]
    exact this

/-- **7.12(2) limit, packed form over a small cofinal set (proved, cycle 89).** As
`infra_712u_packed_limit`, but only a cofinal set `D` of earlier indices with `|D| ≤ μ` is needed
(the union is taken over `D`; every earlier `N i` enters through any `d ≥ i` in `D`). This is the
limit step for long lists of cofinality at most `μ` (`infra_712u_common_long`). -/
theorem infra_712u_packed_limit_cofinal (E : WithTop L.δ ≃o WithTop L'.δ) (k : WithTop L.δ)
    (hs : ∀ i, ¬ i ⋖ k) (D : Set (Set.Iio k)) (hD : #D ≤ μ) (hcof : ∀ i, ∃ d ∈ D, i ≤ d)
    (hne : ∃ i, i < k)
    (N : Set.Iio k → P.scheme.Object μ hμ) (G G' : Set.Iio k → μ.ord.ToType → μ.ord.ToType)
    (n : Set.Iio k → Set.Iio k → μ.ord.ToType → μ.ord.ToType)
    (hG : ∀ i, infra_712u_IsArr (C.stage i.1) (N i) (G i))
    (hG' : ∀ i, infra_712u_IsArr (C'.stage (E i.1)) (N i) (G' i))
    (hn : ∀ i j, i ≤ j → infra_712u_IsArr (N i) (N j) (n i j))
    (hnid : ∀ i x, n i i x = x)
    (hntr : ∀ i j l, i ≤ j → j ≤ l → ∀ x, n i l x = n j l (n i j x))
    (hnG : ∀ i j (h : i ≤ j) x,
      n i j (G i x) = G j ((C.step (show i.1 ≤ j.1 from h)).onVertex PUnit.unit x))
    (hnG' : ∀ i j (h : i ≤ j) x,
      n i j (G' i x) = G' j ((C'.step (E.monotone (show i.1 ≤ j.1 from h))).onVertex PUnit.unit x)) :
    ∃ (U : P.scheme.Object μ hμ) (Gk Gk' : μ.ord.ToType → μ.ord.ToType)
      (l : Set.Iio k → μ.ord.ToType → μ.ord.ToType),
      infra_712u_IsArr (C.stage k) U Gk ∧ infra_712u_IsArr (C'.stage (E k)) U Gk' ∧
      (∀ i, infra_712u_IsArr (N i) U (l i)) ∧
      (∀ i j, i ≤ j → ∀ x, l j (n i j x) = l i x) ∧
      (∀ i x, Gk ((C.step (le_of_lt i.2)).onVertex PUnit.unit x) = l i (G i x)) ∧
      (∀ i x, Gk' ((C'.step (E.monotone (le_of_lt i.2))).onVertex PUnit.unit x) =
        l i (G' i x)) := by
  classical
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨d0, hd0, -⟩ := hcof ⟨i0, hi0⟩
  have : Nonempty D := ⟨⟨d0, hd0⟩⟩
  let st : ∀ {a b : D}, a ≤ b →
      SystemArrow K oneVertexShape (P.scheme.asSystem hμ (N a.1)) (P.scheme.asSystem hμ (N b.1)) :=
    fun {a b} h => (hn a.1 b.1 h).arr
  have hst : ∀ {a b : D} (h : a ≤ b) x, (st h).onVertex PUnit.unit x = n a.1 b.1 x :=
    fun {a b} h x => (hn a.1 b.1 h).arr_apply x
  have hrefl : ∀ a, st (le_refl a) = SystemArrow.refl _ := fun a =>
    infra_712u_arrow_ext fun x => (hst (le_refl a) x).trans (hnid a.1 x)
  have htrans : ∀ {a b c : D} (h₁ : a ≤ b) (h₂ : b ≤ c),
      st (h₁.trans h₂) = SystemArrow.comp (st h₁) (st h₂) := fun {a b c} h₁ h₂ =>
    infra_712u_arrow_ext fun x => by
      show (st (h₁.trans h₂)).onVertex PUnit.unit x =
        (st h₂).onVertex PUnit.unit ((st h₁).onVertex PUnit.unit x)
      rw [hst (h₁.trans h₂), hst h₂, hst h₁]
      exact hntr a.1 b.1 c.1 h₁ h₂ x
  obtain ⟨U, leg, -, hleg, -, -, -⟩ :=
    infra_78_chain_union_kappa hμ hD (fun a : D => N a.1) st hrefl htrans
  have hlegp : ∀ {a b : D} (h : a ≤ b) x,
      (leg b).onVertex PUnit.unit (n a.1 b.1 x) = (leg a).onVertex PUnit.unit x := by
    intro a b h x
    rw [← hst h x]
    exact DFunLike.congr_fun (congrArg (fun f => f.onVertex PUnit.unit) (hleg h)) x
  -- the entry of an arbitrary earlier stage, through a cofinal index above it
  let dOf : Set.Iio k → D := fun i => ⟨(hcof i).choose, (hcof i).choose_spec.1⟩
  have hdOf : ∀ i, i ≤ (dOf i).1 := fun i => (hcof i).choose_spec.2
  let l : Set.Iio k → μ.ord.ToType → μ.ord.ToType :=
    fun i x => (leg (dOf i)).onVertex PUnit.unit (n i (dOf i).1 x)
  have hl_any : ∀ i (d : D), i ≤ d.1 → ∀ x, l i x = (leg d).onVertex PUnit.unit (n i d.1 x) := by
    intro i d hid x
    rcases le_total (dOf i) d with h | h
    · show (leg (dOf i)).onVertex PUnit.unit (n i (dOf i).1 x) = _
      rw [← hlegp h, ← hntr i (dOf i).1 d.1 (hdOf i) h x]
    · show (leg (dOf i)).onVertex PUnit.unit (n i (dOf i).1 x) = _
      rw [← hlegp h, ← hntr i d.1 (dOf i).1 hid h x]
  obtain ⟨f, hf⟩ := infra_712u_factor_continuous hμ hD (fun a : D => C.stage a.1.1)
    (fun {a b} h => C.step h) (fun a => infra_712u_step_refl C a.1.1)
    (fun h₁ h₂ => infra_712u_step_trans C h₁ h₂) (C.stage k) (fun a => C.step (le_of_lt a.1.2))
    (fun {a b} h => (infra_712u_step_trans C (a := a.1.1) (b := b.1.1) h (le_of_lt b.1.2)).symm)
    (fun x => by
      obtain ⟨i, h, y, hy⟩ := C.continuous k hs ⟨i0, hi0⟩ PUnit.unit x
      obtain ⟨d, hd, hid⟩ := hcof ⟨i, h⟩
      refine ⟨⟨d, hd⟩, (C.step (show i ≤ d.1 from hid)).onVertex PUnit.unit y, ?_⟩
      rw [← hy]
      exact DFunLike.congr_fun (C.step_comp (show i ≤ d.1 from hid) (le_of_lt d.2) PUnit.unit) y)
    (fun a => SystemArrow.comp (hG a.1).arr (leg a))
    (fun {a b} h => infra_712u_arrow_ext fun x => by
      show (leg b).onVertex PUnit.unit ((hG b.1).arr.onVertex PUnit.unit
        ((C.step h).onVertex PUnit.unit x)) =
        (leg a).onVertex PUnit.unit ((hG a.1).arr.onVertex PUnit.unit x)
      rw [(hG b.1).arr_apply, (hG a.1).arr_apply, ← hnG a.1 b.1 h x]
      exact hlegp h _)
  have hs' : ∀ i', ¬ i' ⋖ E k := fun i' hc => by
    obtain ⟨i, rfl⟩ := E.surjective i'
    exact hs i ((apply_covBy_apply_iff E).1 hc)
  obtain ⟨f', hf'⟩ := infra_712u_factor_continuous hμ hD (fun a : D => C'.stage (E a.1.1))
    (fun {a b} h => C'.step (E.monotone h)) (fun a => infra_712u_step_refl C' (E a.1.1))
    (fun h₁ h₂ => infra_712u_step_trans C' _ _) (C'.stage (E k))
    (fun a => C'.step (E.monotone (le_of_lt a.1.2)))
    (fun {a b} h => (infra_712u_step_trans C' (E.monotone h) (E.monotone (le_of_lt b.1.2))).symm)
    (fun x => by
      obtain ⟨i', h, y, hy⟩ := C'.continuous (E k) hs' ⟨E i0, E.strictMono hi0⟩ PUnit.unit x
      obtain ⟨i, rfl⟩ := E.surjective i'
      obtain ⟨d, hd, hid⟩ := hcof ⟨i, E.lt_iff_lt.1 h⟩
      refine ⟨⟨d, hd⟩, (C'.step (E.monotone (show i ≤ d.1 from hid))).onVertex PUnit.unit y, ?_⟩
      rw [← hy]
      exact DFunLike.congr_fun (C'.step_comp (E.monotone (show i ≤ d.1 from hid))
        (E.monotone (le_of_lt d.2)) PUnit.unit) y)
    (fun a => SystemArrow.comp (hG' a.1).arr (leg a))
    (fun {a b} h => infra_712u_arrow_ext fun x => by
      show (leg b).onVertex PUnit.unit ((hG' b.1).arr.onVertex PUnit.unit
        ((C'.step (E.monotone h)).onVertex PUnit.unit x)) =
        (leg a).onVertex PUnit.unit ((hG' a.1).arr.onVertex PUnit.unit x)
      rw [(hG' b.1).arr_apply, (hG' a.1).arr_apply, ← hnG' a.1 b.1 h x]
      exact hlegp h _)
  refine ⟨U, fun x => f.onVertex PUnit.unit x, fun x => f'.onVertex PUnit.unit x, l,
    infra_712u_IsArr.of_arrow f, infra_712u_IsArr.of_arrow f', fun i => ?_,
    fun i j hij x => ?_, fun i x => ?_, fun i x => ?_⟩
  · have := (hn i (dOf i).1 (hdOf i)).comp (infra_712u_IsArr.of_arrow (leg (dOf i)))
    exact this
  · rw [hl_any j (dOf j) (hdOf j), hl_any i (dOf j) (hij.trans (hdOf j)),
      hntr i j (dOf j).1 hij (hdOf j)]
  · -- `M_i → M_d → M_k`
    have e1 := DFunLike.congr_fun (C.step_comp (show i.1 ≤ (dOf i).1.1 from hdOf i)
      (le_of_lt (dOf i).1.2) PUnit.unit) x
    show f.onVertex PUnit.unit ((C.step (le_of_lt i.2)).onVertex PUnit.unit x) = l i (G i x)
    exact (congrArg (f.onVertex PUnit.unit) e1.symm).trans ((hf (dOf i) _).trans
      ((congrArg ((leg (dOf i)).onVertex PUnit.unit) ((hG (dOf i).1).arr_apply _)).trans
        (congrArg ((leg (dOf i)).onVertex PUnit.unit) (hnG i (dOf i).1 (hdOf i) x).symm)))
  · have e1 := DFunLike.congr_fun (C'.step_comp (E.monotone (show i.1 ≤ (dOf i).1.1 from hdOf i))
      (E.monotone (le_of_lt (dOf i).1.2)) PUnit.unit) x
    show f'.onVertex PUnit.unit ((C'.step (E.monotone (le_of_lt i.2))).onVertex PUnit.unit x) =
      l i (G' i x)
    exact (congrArg (f'.onVertex PUnit.unit) e1.symm).trans ((hf' (dOf i) _).trans
      ((congrArg ((leg (dOf i)).onVertex PUnit.unit) ((hG' (dOf i).1).arr_apply _)).trans
        (congrArg ((leg (dOf i)).onVertex PUnit.unit) (hnG' i (dOf i).1 (hdOf i) x).symm)))

/-- **Few non-surjective successor steps (proved, cycle 89).** In a witnessing chain at level
`μ`, at most `μ` successor steps `M_β → M_{β+1}` fail to be onto: each such `β` yields an element
of `M_⊤` first appearing at `β + 1`. Counting input for `infra_712u_common_long`. -/
theorem infra_712u_nontrivial_card {L₀ : TupleList P.scheme hμ A} [LinearOrder L₀.δ]
    (D : TiedListWitnessingChain L₀) :
    #{β : WithTop L₀.δ // ∃ k, ∃ h : β ⋖ k,
      ¬ Function.Surjective ((D.step h.le).onVertex PUnit.unit)} ≤ μ := by
  classical
  let F : {β : WithTop L₀.δ // ∃ k, ∃ h : β ⋖ k,
      ¬ Function.Surjective ((D.step h.le).onVertex PUnit.unit)} → μ.ord.ToType := fun b =>
    (D.step (le_top : b.2.choose ≤ ⊤)).onVertex PUnit.unit
      (not_forall.1 b.2.choose_spec.choose_spec).choose
  have key : ∀ b1 b2 : {β : WithTop L₀.δ // ∃ k, ∃ h : β ⋖ k,
      ¬ Function.Surjective ((D.step h.le).onVertex PUnit.unit)}, b1.1 < b2.1 → F b1 ≠ F b2 := by
    intro b1 b2 hlt heq
    have h1 := b1.2.choose_spec.choose
    have h2 := b2.2.choose_spec.choose
    have hk1 : b1.2.choose ≤ b2.1 := le_of_not_gt fun h => h1.2 hlt h
    have hy2 := (not_forall.1 b2.2.choose_spec.choose_spec).choose_spec
    apply hy2
    refine ⟨(D.step hk1).onVertex PUnit.unit (not_forall.1 b1.2.choose_spec.choose_spec).choose, ?_⟩
    have e1 := DFunLike.congr_fun (D.step_comp hk1 h2.le PUnit.unit)
      (not_forall.1 b1.2.choose_spec.choose_spec).choose
    have e2 := DFunLike.congr_fun (D.step_comp (hk1.trans h2.le) (le_top : b2.2.choose ≤ ⊤)
      PUnit.unit) (not_forall.1 b1.2.choose_spec.choose_spec).choose
    apply (D.step (le_top : b2.2.choose ≤ ⊤)).onVertex PUnit.unit |>.injective
    refine (congrArg _ e1).trans (e2.trans ?_)
    exact heq
  refine (Cardinal.mk_le_of_injective (f := F) ?_).trans (Cardinal.mk_ord_toType μ).le
  intro b1 b2 h
  rcases lt_trichotomy b1.1 b2.1 with hl | he | hg
  · exact absurd h (key b1 b2 hl)
  · exact Subtype.ext he
  · exact absurd h.symm (key b2 b1 hg)

/-- One side of `infra_712u_packed_limit_stable`. -/
theorem infra_712u_stable_side {L₀ : TupleList P.scheme hμ A} [LinearOrder L₀.δ]
    (D : TiedListWitnessingChain L₀) (k : WithTop L₀.δ) (hs : ∀ i, ¬ i ⋖ k)
    (b : Set.Iio k) (Nb : P.scheme.Object μ hμ)
    (G : Set.Iio k → μ.ord.ToType → μ.ord.ToType)
    (n : Set.Iio k → Set.Iio k → μ.ord.ToType → μ.ord.ToType)
    (hGb : infra_712u_IsArr (D.stage b.1) Nb (G b))
    (hnb : ∀ i, b ≤ i → ∀ x, n b i x = x)
    (hsb : ∀ i (h : b ≤ i), Function.Surjective ((D.step (show b.1 ≤ i.1 from h)).onVertex PUnit.unit))
    (hnG : ∀ i j (h : i ≤ j) x,
      n i j (G i x) = G j ((D.step (show i.1 ≤ j.1 from h)).onVertex PUnit.unit x)) :
    ∃ Gk : μ.ord.ToType → μ.ord.ToType, infra_712u_IsArr (D.stage k) Nb Gk ∧
      ∀ m, b ≤ m → ∀ w, Gk ((D.step (le_of_lt m.2)).onVertex PUnit.unit w) = G m w := by
  have hsurj : Function.Surjective ((D.step (le_of_lt b.2)).onVertex PUnit.unit) := by
    intro x
    obtain ⟨i, h, y, rfl⟩ := D.continuous k hs ⟨b.1, b.2⟩ PUnit.unit x
    let m : Set.Iio k := ⟨max i b.1, show max i b.1 < k from max_lt h b.2⟩
    have him : i ≤ m.1 := le_max_left _ _
    have hbm : b ≤ m := (le_max_right i b.1 : b.1 ≤ max i b.1)
    obtain ⟨z, hz⟩ := hsb m hbm ((D.step him).onVertex PUnit.unit y)
    refine ⟨z, ?_⟩
    have e1 := DFunLike.congr_fun (D.step_comp (show b.1 ≤ m.1 from hbm) (le_of_lt m.2) PUnit.unit) z
    have e2 := DFunLike.congr_fun (D.step_comp him (le_of_lt m.2) PUnit.unit) y
    exact e1.symm.trans ((congrArg _ hz).trans e2)
  obtain ⟨ψ, -, hψ⟩ := infra_78_struct_inverse (D.step (le_of_lt b.2)) (fun v => by
    obtain rfl : v = PUnit.unit := Subsingleton.elim _ _
    exact ⟨((D.step (le_of_lt b.2)).onVertex PUnit.unit).injective, hsurj⟩)
  refine ⟨fun x => G b (ψ.onVertex PUnit.unit x), (infra_712u_IsArr.of_arrow ψ).comp hGb,
    fun m hbm w => ?_⟩
  obtain ⟨z, rfl⟩ := hsb m hbm w
  have e1 := DFunLike.congr_fun (D.step_comp (show b.1 ≤ m.1 from hbm) (le_of_lt m.2) PUnit.unit) z
  exact (congrArg (fun y => G b (ψ.onVertex PUnit.unit y)) e1).trans
    ((congrArg (G b) (hψ z)).trans ((hnb m hbm (G b z)).symm.trans (hnG b m hbm z)))

/-- **7.12(2) limit, stable case (proved, cycle 89).** At a limit `k` whose system is constant
from some `b < k` on (same `N`, identity transitions, onto chain steps on both sides), the
limit state is `N_b` itself: the functions on `M_k`, `M'_{E k}` are those of `M_b`, `M'_{E b}`
after the inverse of the (onto, by continuity) steps `b → k`. Limit op for
`infra_712u_common_long` at limits of cofinality `> μ`. -/
theorem infra_712u_packed_limit_stable (E : WithTop L.δ ≃o WithTop L'.δ) (k : WithTop L.δ)
    (hs : ∀ i, ¬ i ⋖ k) (b : Set.Iio k)
    (N : Set.Iio k → P.scheme.Object μ hμ) (G G' : Set.Iio k → μ.ord.ToType → μ.ord.ToType)
    (n : Set.Iio k → Set.Iio k → μ.ord.ToType → μ.ord.ToType)
    (hG : infra_712u_IsArr (C.stage b.1) (N b) (G b))
    (hG' : infra_712u_IsArr (C'.stage (E b.1)) (N b) (G' b))
    (hn : ∀ i j, i ≤ j → infra_712u_IsArr (N i) (N j) (n i j))
    (hntr : ∀ i j l, i ≤ j → j ≤ l → ∀ x, n i l x = n j l (n i j x))
    (hNb : ∀ i, b ≤ i → N i = N b) (hnb : ∀ i, b ≤ i → ∀ x, n b i x = x)
    (hsb : ∀ i (h : b ≤ i), Function.Surjective ((C.step (show b.1 ≤ i.1 from h)).onVertex PUnit.unit))
    (hsb' : ∀ i (h : b ≤ i), Function.Surjective
      ((C'.step (E.monotone (show b.1 ≤ i.1 from h))).onVertex PUnit.unit))
    (hnG : ∀ i j (h : i ≤ j) x,
      n i j (G i x) = G j ((C.step (show i.1 ≤ j.1 from h)).onVertex PUnit.unit x))
    (hnG' : ∀ i j (h : i ≤ j) x,
      n i j (G' i x) = G' j ((C'.step (E.monotone (show i.1 ≤ j.1 from h))).onVertex PUnit.unit x)) :
    ∃ (U : P.scheme.Object μ hμ) (Gk Gk' : μ.ord.ToType → μ.ord.ToType)
      (l : Set.Iio k → μ.ord.ToType → μ.ord.ToType),
      infra_712u_IsArr (C.stage k) U Gk ∧ infra_712u_IsArr (C'.stage (E k)) U Gk' ∧
      (∀ i, infra_712u_IsArr (N i) U (l i)) ∧
      (∀ i j, i ≤ j → ∀ x, l j (n i j x) = l i x) ∧
      (∀ i x, Gk ((C.step (le_of_lt i.2)).onVertex PUnit.unit x) = l i (G i x)) ∧
      (∀ i x, Gk' ((C'.step (E.monotone (le_of_lt i.2))).onVertex PUnit.unit x) =
        l i (G' i x)) := by
  obtain ⟨Gk, hGk, HGk⟩ := infra_712u_stable_side C k hs b (N b) G n hG hnb hsb hnG
  have hs' : ∀ i', ¬ i' ⋖ E k := fun i' hc => by
    obtain ⟨i, rfl⟩ := E.surjective i'
    exact hs i ((apply_covBy_apply_iff E).1 hc)
  -- transport the index set along `E` for the primed side
  let mx : Set.Iio k → Set.Iio k := fun i =>
    ⟨max i.1 b.1, show max i.1 b.1 < k from max_lt i.2 b.2⟩
  have hmx1 : ∀ i, i ≤ mx i := fun i => (le_max_left i.1 b.1 : i.1 ≤ max i.1 b.1)
  have hmx2 : ∀ i, b ≤ mx i := fun i => (le_max_right i.1 b.1 : b.1 ≤ max i.1 b.1)
  have hid : ∀ i j, b ≤ i → i ≤ j → ∀ x, n i j x = x := fun i j hbi hij x => by
    have := hntr b i j hbi hij x
    rw [hnb i hbi, hnb j (hbi.trans hij)] at this
    exact this.symm
  let l : Set.Iio k → μ.ord.ToType → μ.ord.ToType := fun i x => n i (mx i) x
  have hl : ∀ i, infra_712u_IsArr (N i) (N b) (l i) := fun i =>
    hNb (mx i) (hmx2 i) ▸ hn i (mx i) (hmx1 i)
  have hl_up : ∀ i (m : Set.Iio k), i ≤ m → b ≤ m → ∀ x, l i x = n i m x := by
    intro i m him hbm x
    rcases le_total (mx i) m with h | h
    · rw [hntr i (mx i) m (hmx1 i) h x, hid (mx i) m (hmx2 i) h]
    · show n i (mx i) x = n i m x
      rw [hntr i m (mx i) him h x, hid m (mx i) hbm h]
  -- the `C'` side via a shifted chain index is not available; argue directly
  have hsurj' : Function.Surjective ((C'.step (E.monotone (le_of_lt b.2))).onVertex PUnit.unit) := by
    intro x
    obtain ⟨i', h, y, rfl⟩ := C'.continuous (E k) hs' ⟨E b.1, E.strictMono b.2⟩ PUnit.unit x
    obtain ⟨i, rfl⟩ := E.surjective i'
    let m : Set.Iio k := ⟨max i b.1, show max i b.1 < k from max_lt (E.lt_iff_lt.1 h) b.2⟩
    have him : i ≤ m.1 := le_max_left _ _
    have hbm : b ≤ m := (le_max_right i b.1 : b.1 ≤ max i b.1)
    obtain ⟨z, hz⟩ := hsb' m hbm ((C'.step (E.monotone him)).onVertex PUnit.unit y)
    refine ⟨z, ?_⟩
    have e1 := DFunLike.congr_fun (C'.step_comp (E.monotone (show b.1 ≤ m.1 from hbm))
      (E.monotone (le_of_lt m.2)) PUnit.unit) z
    have e2 := DFunLike.congr_fun (C'.step_comp (E.monotone him) (E.monotone (le_of_lt m.2))
      PUnit.unit) y
    exact e1.symm.trans ((congrArg _ hz).trans e2)
  obtain ⟨ψ', -, hψ'⟩ := infra_78_struct_inverse (C'.step (E.monotone (le_of_lt b.2))) (fun v => by
    obtain rfl : v = PUnit.unit := Subsingleton.elim _ _
    exact ⟨((C'.step (E.monotone (le_of_lt b.2))).onVertex PUnit.unit).injective, hsurj'⟩)
  have HGk' : ∀ m, b ≤ m → ∀ w,
      G' b (ψ'.onVertex PUnit.unit ((C'.step (E.monotone (le_of_lt m.2))).onVertex PUnit.unit w)) =
        G' m w := by
    intro m hbm w
    obtain ⟨z, rfl⟩ := hsb' m hbm w
    have e1 := DFunLike.congr_fun (C'.step_comp (E.monotone (show b.1 ≤ m.1 from hbm))
      (E.monotone (le_of_lt m.2)) PUnit.unit) z
    exact (congrArg (fun y => G' b (ψ'.onVertex PUnit.unit y)) e1).trans
      ((congrArg (G' b) (hψ' z)).trans ((hnb m hbm (G' b z)).symm.trans (hnG' b m hbm z)))
  refine ⟨N b, Gk, fun x => G' b (ψ'.onVertex PUnit.unit x), l, hGk,
    (infra_712u_IsArr.of_arrow ψ').comp hG', hl, fun i j hij x => ?_, fun i x => ?_,
    fun i x => ?_⟩
  · rw [hl_up i (mx j) (hij.trans (hmx1 j)) (hmx2 j), hntr i j (mx j) hij (hmx1 j) x]
  · have e1 := DFunLike.congr_fun (C.step_comp (show i.1 ≤ (mx i).1 from hmx1 i)
      (le_of_lt (mx i).2) PUnit.unit) x
    rw [← e1]
    exact (HGk (mx i) (hmx2 i) _).trans (hnG i (mx i) (hmx1 i) x).symm
  · have e1 := DFunLike.congr_fun (C'.step_comp (E.monotone (show i.1 ≤ (mx i).1 from hmx1 i))
      (E.monotone (le_of_lt (mx i).2)) PUnit.unit) x
    show G' b (ψ'.onVertex PUnit.unit _) = _
    rw [← e1]
    exact (HGk' (mx i) (hmx2 i) _).trans (hnG' i (mx i) (hmx1 i) x).symm

end Packed

section Assembly
variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
  {A : P.scheme.Object μ hμ} {L L' : TupleList P.scheme hμ A} [LinearOrder L.δ]
  [LinearOrder L'.δ] (C : TiedListWitnessingChain L) (C' : TiedListWitnessingChain L')
  (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i))

/-- A packed state of the common-object recursion: `N` with the functions of `M_k → N`,
`M'_{e k} → N`. -/
abbrev infra_712u_State (P : SingleModelData K) (μ : Cardinal.{u}) (hμ : μ ∈ P.eligible) :=
  P.scheme.Object μ hμ × (μ.ord.ToType → μ.ord.ToType) × (μ.ord.ToType → μ.ord.ToType)

/-- A state is valid at stage `k`: both arrows, compatible over `A`, identifying the marks
below `k`. -/
def infra_712u_StateOK (k : WithTop L.δ) (s : infra_712u_State P μ hμ) : Prop :=
  infra_712u_IsArr (C.stage k) s.1 s.2.1 ∧
  infra_712u_IsArr (C'.stage (e.withTopCongr k)) s.1 s.2.2 ∧
  (∀ x, s.2.1 ((C.into k).onVertex PUnit.unit x) =
    s.2.2 ((C'.into (e.withTopCongr k)).onVertex PUnit.unit x)) ∧
  ∀ (m : L.δ) (hm : (m : WithTop L.δ) < k) (a : L.indexAt m),
    s.2.1 (C.mark m k hm a).2 =
      s.2.2 (C'.mark (e m) (e.withTopCongr k) (e.withTopCongr.strictMono hm) (ei m a)).2

/-- Successor specification. -/
def infra_712u_SuccSpec (β k : WithTop L.δ) (s : infra_712u_State P μ hμ)
    (R : infra_712u_State P μ hμ × (μ.ord.ToType → μ.ord.ToType)) : Prop :=
  infra_712u_StateOK C C' e ei k R.1 ∧ infra_712u_IsArr s.1 R.1.1 R.2 ∧
  ∀ h : β ≤ k, (∀ x, R.1.2.1 ((C.step h).onVertex PUnit.unit x) = R.2 (s.2.1 x)) ∧
    (∀ x, R.1.2.2 ((C'.step (e.withTopCongr.monotone h)).onVertex PUnit.unit x) = R.2 (s.2.2 x))

theorem infra_712u_succ_R (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
    (hm : ∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _))
    (β k : WithTop L.δ) (hβ : β ⋖ k) (s : infra_712u_State P μ hμ)
    (hs : infra_712u_StateOK C C' e ei β s) :
    ∃ R, infra_712u_SuccSpec C C' e ei β k s R := by
  have hβt : β ≠ ⊤ := fun h => by
    subst h
    exact not_top_lt hβ.lt
  obtain ⟨j, rfl⟩ := WithTop.ne_top_iff_exists.1 hβt
  obtain ⟨hG, hG', hA, hmk⟩ := hs
  obtain ⟨N₁, G₁, G₁', h, Hh, HG, HG', H1, H2, H3⟩ := infra_712u_packed_succ C C' h0 h1 e ei hm
    j k hβ.lt (e.withTopCongr k) (e.withTopCongr.strictMono hβ.lt) s.1 s.2.1 s.2.2 hG hG' hA
  refine ⟨((N₁, G₁, G₁'), h), ⟨HG, HG', fun x => ?_, fun m hmk' a => ?_⟩, Hh, fun _ => ⟨H1, H2⟩⟩
  · have e1 := DFunLike.congr_fun (C.into_step hβ.le PUnit.unit) x
    have e2 := DFunLike.congr_fun (C'.into_step (e.withTopCongr.monotone hβ.le) PUnit.unit) x
    show G₁ ((C.into k).onVertex PUnit.unit x) = G₁' ((C'.into (e.withTopCongr k)).onVertex PUnit.unit x)
    rw [← e1, ← e2]
    exact (H1 _).trans ((congrArg h (hA x)).trans (H2 _).symm)
  · have hle : (m : WithTop L.δ) ≤ j := by
      by_contra hc
      exact hβ.2 (lt_of_not_ge hc) hmk'
    rcases hle.lt_or_eq with hlt | heq
    · have m1 := congrArg Sigma.snd (C.mark_step m hlt hβ.le a)
      have m2 := congrArg Sigma.snd (C'.mark_step (e m) (e.withTopCongr.strictMono hlt)
        (e.withTopCongr.monotone hβ.le) (ei m a))
      show G₁ (C.mark m k hmk' a).2 = G₁' (C'.mark (e m) _ _ (ei m a)).2
      rw [← m1, ← m2]
      exact (H1 _).trans ((congrArg h (hmk m hlt a)).trans (H2 _).symm)
    · have hj : m = j := WithTop.coe_injective heq
      subst hj
      exact H3 a

/-- **Trivial successor step, packed (proved, cycle 89).** If the entry at `β` is empty and
both chains' steps `β → k` are onto, the state is kept: `N` unchanged, the new functions are the
old ones after the inverse steps (`infra_78_struct_inverse`), and the transition is the
identity. Successor op for `infra_712u_common_long` at the (all but `μ`) trivial indices. -/
theorem infra_712u_trivial_R (β k : WithTop L.δ) (hβ : β ⋖ k) (s : infra_712u_State P μ hμ)
    (hs : infra_712u_StateOK C C' e ei β s)
    (hemp : ∀ j : L.δ, β = ↑j → IsEmpty (L.indexAt j))
    (hsur : Function.Surjective ((C.step hβ.le).onVertex PUnit.unit))
    (hsur' : Function.Surjective ((C'.step (e.withTopCongr.monotone hβ.le)).onVertex PUnit.unit)) :
    ∃ R, infra_712u_SuccSpec C C' e ei β k s R ∧ R.1.1 = s.1 ∧ R.2 = id := by
  obtain ⟨hG, hG', hA, hmk⟩ := hs
  obtain ⟨ψ, -, hψ⟩ := infra_78_struct_inverse (C.step hβ.le) (fun v => by
    obtain rfl : v = PUnit.unit := Subsingleton.elim _ _
    exact ⟨((C.step hβ.le).onVertex PUnit.unit).injective, hsur⟩)
  obtain ⟨ψ', -, hψ'⟩ := infra_78_struct_inverse (C'.step (e.withTopCongr.monotone hβ.le))
    (fun v => by
      obtain rfl : v = PUnit.unit := Subsingleton.elim _ _
      exact ⟨((C'.step (e.withTopCongr.monotone hβ.le)).onVertex PUnit.unit).injective, hsur'⟩)
  refine ⟨((s.1, fun x => s.2.1 (ψ.onVertex PUnit.unit x),
      fun x => s.2.2 (ψ'.onVertex PUnit.unit x)), id),
    ⟨⟨(infra_712u_IsArr.of_arrow ψ).comp hG, (infra_712u_IsArr.of_arrow ψ').comp hG',
      fun x => ?_, fun m hmk' a => ?_⟩, infra_712u_IsArr.id _,
      fun _ => ⟨fun x => congrArg s.2.1 (hψ x), fun x => congrArg s.2.2 (hψ' x)⟩⟩, rfl, rfl⟩
  · have e1 := DFunLike.congr_fun (C.into_step hβ.le PUnit.unit) x
    have e2 := DFunLike.congr_fun (C'.into_step (e.withTopCongr.monotone hβ.le) PUnit.unit) x
    show s.2.1 (ψ.onVertex PUnit.unit ((C.into k).onVertex PUnit.unit x)) =
      s.2.2 (ψ'.onVertex PUnit.unit ((C'.into (e.withTopCongr k)).onVertex PUnit.unit x))
    rw [← e1, ← e2]
    exact (congrArg s.2.1 (hψ _)).trans ((hA x).trans (congrArg s.2.2 (hψ' _)).symm)
  · have hle : (m : WithTop L.δ) ≤ β := le_of_not_gt fun h => hβ.2 h hmk'
    rcases hle.lt_or_eq with hlt | heq
    · have m1 := congrArg Sigma.snd (C.mark_step m hlt hβ.le a)
      have m2 := congrArg Sigma.snd (C'.mark_step (e m) (e.withTopCongr.strictMono hlt)
        (e.withTopCongr.monotone hβ.le) (ei m a))
      show s.2.1 (ψ.onVertex PUnit.unit (C.mark m k hmk' a).2) =
        s.2.2 (ψ'.onVertex PUnit.unit (C'.mark (e m) _ _ (ei m a)).2)
      rw [← m1, ← m2]
      exact (congrArg s.2.1 (hψ _)).trans ((hmk m hlt a).trans (congrArg s.2.2 (hψ' _)).symm)
    · exact ((hemp m heq.symm).false a).elim

/-- The base state at a first stage. -/
theorem infra_712u_base_R (k : WithTop L.δ) (hk : IsMin k) :
    ∃ s, infra_712u_StateOK C C' e ei k s := by
  have hk' : ∀ j, k ≤ j := fun j => (le_total k j).elim id (fun h => hk h)
  have hE : ∀ j, e.withTopCongr k ≤ j := fun j => by
    obtain ⟨i, rfl⟩ := e.withTopCongr.surjective j
    exact e.withTopCongr.monotone (hk' i)
  obtain ⟨r, hr1, -⟩ := infra_712u_base C k hk'
  obtain ⟨r', hr1', -⟩ := infra_712u_base C' _ hE
  refine ⟨(A, fun x => r.onVertex PUnit.unit x, fun x => r'.onVertex PUnit.unit x),
    infra_712u_IsArr.of_arrow r, infra_712u_IsArr.of_arrow r', fun x => ?_, fun m hm => ?_⟩
  · exact (hr1 x).trans (hr1' x).symm
  · exact absurd hm (not_lt.2 (hk' _))

/-- Limit hypotheses on the earlier states and maps. -/
def infra_712u_LimHyp (k : WithTop L.δ) (cf : Set.Iio k → infra_712u_State P μ hμ)
    (mf : Set.Iio k → Set.Iio k → μ.ord.ToType → μ.ord.ToType) : Prop :=
  (∀ i, ¬ i ⋖ k) ∧ (∃ i, i < k) ∧ (∀ i : Set.Iio k, infra_712u_StateOK C C' e ei i.1 (cf i)) ∧
  (∀ i j, i ≤ j → infra_712u_IsArr (cf i).1 (cf j).1 (mf i j)) ∧
  (∀ i x, mf i i x = x) ∧
  (∀ i j l, i ≤ j → j ≤ l → ∀ x, mf i l x = mf j l (mf i j x)) ∧
  (∀ i j (h : i ≤ j) x,
    mf i j ((cf i).2.1 x) = (cf j).2.1 ((C.step (show i.1 ≤ j.1 from h)).onVertex PUnit.unit x)) ∧
  (∀ i j (h : i ≤ j) x, mf i j ((cf i).2.2 x) =
    (cf j).2.2 ((C'.step (e.withTopCongr.monotone (show i.1 ≤ j.1 from h))).onVertex PUnit.unit x))

/-- Limit specification. -/
def infra_712u_LimSpec (k : WithTop L.δ) (cf : Set.Iio k → infra_712u_State P μ hμ)
    (mf : Set.Iio k → Set.Iio k → μ.ord.ToType → μ.ord.ToType)
    (R : infra_712u_State P μ hμ × (Set.Iio k → μ.ord.ToType → μ.ord.ToType)) : Prop :=
  infra_712u_StateOK C C' e ei k R.1 ∧ (∀ i, infra_712u_IsArr (cf i).1 R.1.1 (R.2 i)) ∧
  (∀ i j, i ≤ j → ∀ x, R.2 j (mf i j x) = R.2 i x) ∧
  (∀ i x, R.1.2.1 ((C.step (le_of_lt i.2)).onVertex PUnit.unit x) = R.2 i ((cf i).2.1 x)) ∧
  (∀ i x, R.1.2.2 ((C'.step (e.withTopCongr.monotone (le_of_lt i.2))).onVertex PUnit.unit x) =
    R.2 i ((cf i).2.2 x))

theorem infra_712u_lim_R (hcard : #(WithTop L.δ) ≤ μ) (k : WithTop L.δ)
    (cf : Set.Iio k → infra_712u_State P μ hμ)
    (mf : Set.Iio k → Set.Iio k → μ.ord.ToType → μ.ord.ToType)
    (H : infra_712u_LimHyp C C' e ei k cf mf) : ∃ R, infra_712u_LimSpec C C' e ei k cf mf R := by
  obtain ⟨hs, hne, hok, hn, hnid, hntr, hnG, hnG'⟩ := H
  obtain ⟨U, Gk, Gk', l, HG, HG', Hl, Hln, H1, H2⟩ := infra_712u_packed_limit C C'
    e.withTopCongr k hs hne hcard (fun i => (cf i).1) (fun i => (cf i).2.1) (fun i => (cf i).2.2)
    mf (fun i => (hok i).1) (fun i => (hok i).2.1) hn hnid hntr hnG hnG'
  obtain ⟨i0, hi0⟩ := hne
  refine ⟨((U, Gk, Gk'), l), ⟨HG, HG', fun x => ?_, fun m hmk a => ?_⟩, Hl, Hln, H1, H2⟩
  · have e1 := DFunLike.congr_fun (C.into_step (le_of_lt hi0) PUnit.unit) x
    have e2 := DFunLike.congr_fun (C'.into_step (e.withTopCongr.monotone (le_of_lt hi0))
      PUnit.unit) x
    show Gk ((C.into k).onVertex PUnit.unit x) = Gk' ((C'.into (e.withTopCongr k)).onVertex PUnit.unit x)
    rw [← e1, ← e2]
    exact (H1 ⟨i0, hi0⟩ _).trans ((congrArg (l ⟨i0, hi0⟩) ((hok ⟨i0, hi0⟩).2.2.1 x)).trans
      (H2 ⟨i0, hi0⟩ _).symm)
  · have : ∃ i, (m : WithTop L.δ) < i ∧ i < k := by
      by_contra hc
      push Not at hc
      exact hs m ⟨hmk, fun i h1 h2 => absurd (hc i h1) (not_le.2 h2)⟩
    obtain ⟨i, hmi, hik⟩ := this
    have m1 := congrArg Sigma.snd (C.mark_step m hmi (le_of_lt hik) a)
    have m2 := congrArg Sigma.snd (C'.mark_step (e m) (e.withTopCongr.strictMono hmi)
      (e.withTopCongr.monotone (le_of_lt hik)) (ei m a))
    show Gk (C.mark m k hmk a).2 = Gk' (C'.mark (e m) _ _ (ei m a)).2
    rw [← m1, ← m2]
    exact (H1 ⟨i, hik⟩ _).trans ((congrArg (l ⟨i, hik⟩) ((hok ⟨i, hik⟩).2.2.2 m hmi a)).trans
      (H2 ⟨i, hik⟩ _).symm)

theorem infra_712u_step_self {L₀ : TupleList P.scheme hμ A} [LinearOrder L₀.δ]
    (D : TiedListWitnessingChain L₀) {i : WithTop L₀.δ} (h : i ≤ i) (x) :
    (D.step h).onVertex PUnit.unit x = x := by
  rw [infra_712u_step_refl D i]
  rfl

variable (h0 : μ ∈ recursionClosedLevels P ℵ₀) (h1 : Order.succ ℵ₀ ≤ μ)
  (hm : ∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _))
  (hcard : #(WithTop L.δ) ≤ μ)

open Classical in
/-- Successor operator of the common-object recursion. -/
def infra_712u_sop (β : WithTop L.δ) (s : infra_712u_State P μ hμ) :
    infra_712u_State P μ hμ × (μ.ord.ToType → μ.ord.ToType) :=
  if H : ∃ k, β ⋖ k ∧ infra_712u_StateOK C C' e ei β s then
    Classical.choose (infra_712u_succ_R C C' e ei h0 h1 hm β H.choose H.choose_spec.1 s
      H.choose_spec.2)
  else (s, id)

open Classical in
/-- Limit operator of the common-object recursion. -/
def infra_712u_lop (k : WithTop L.δ) (cf : Set.Iio k → infra_712u_State P μ hμ)
    (mf : Set.Iio k → Set.Iio k → μ.ord.ToType → μ.ord.ToType) :
    infra_712u_State P μ hμ × (Set.Iio k → μ.ord.ToType → μ.ord.ToType) :=
  if H : infra_712u_LimHyp C C' e ei k cf mf then
    Classical.choose (infra_712u_lim_R C C' e ei hcard k cf mf H)
  else ((A, id, id), fun _ => id)

open Classical in
/-- Base state of the common-object recursion. -/
def infra_712u_s0 : infra_712u_State P μ hμ :=
  if H : ∃ k : WithTop L.δ, IsMin k then
    Classical.choose (infra_712u_base_R C C' e ei H.choose H.choose_spec)
  else (A, id, id)

variable [WellFoundedLT L.δ]

/-- The recursion's stage. -/
def infra_712u_O (k : WithTop L.δ) : infra_712u_State P μ hμ :=
  infra_78_engineObj (infra_712u_s0 C C' e ei) id (fun f g => g ∘ f)
    (infra_712u_sop C C' e ei h0 h1 hm) (infra_712u_lop C C' e ei hcard) k

/-- The recursion's transition functions. -/
def infra_712u_Mp (i k : WithTop L.δ) : μ.ord.ToType → μ.ord.ToType :=
  infra_78_engineMap (infra_712u_s0 C C' e ei) id (fun f g => g ∘ f)
    (infra_712u_sop C C' e ei h0 h1 hm) (infra_712u_lop C C' e ei hcard) i k

/-- Validity of the recursion up to stage `k`. -/
def infra_712u_Good (k : WithTop L.δ) : Prop :=
  infra_712u_StateOK C C' e ei k (infra_712u_O C C' e ei h0 h1 hm hcard k) ∧
  (∀ i (h : i ≤ k),
    infra_712u_IsArr (infra_712u_O C C' e ei h0 h1 hm hcard i).1
      (infra_712u_O C C' e ei h0 h1 hm hcard k).1 (infra_712u_Mp C C' e ei h0 h1 hm hcard i k) ∧
    (∀ x, infra_712u_Mp C C' e ei h0 h1 hm hcard i k
        ((infra_712u_O C C' e ei h0 h1 hm hcard i).2.1 x) =
      (infra_712u_O C C' e ei h0 h1 hm hcard k).2.1 ((C.step h).onVertex PUnit.unit x)) ∧
    (∀ x, infra_712u_Mp C C' e ei h0 h1 hm hcard i k
        ((infra_712u_O C C' e ei h0 h1 hm hcard i).2.2 x) =
      (infra_712u_O C C' e ei h0 h1 hm hcard k).2.2
        ((C'.step (e.withTopCongr.monotone h)).onVertex PUnit.unit x))) ∧
  (∀ x, infra_712u_Mp C C' e ei h0 h1 hm hcard k k x = x) ∧
  (∀ i j, i ≤ j → j ≤ k → ∀ x, infra_712u_Mp C C' e ei h0 h1 hm hcard i k x =
    infra_712u_Mp C C' e ei h0 h1 hm hcard j k (infra_712u_Mp C C' e ei h0 h1 hm hcard i j x))

theorem infra_712u_Mp_self (k : WithTop L.δ) (x) :
    infra_712u_Mp C C' e ei h0 h1 hm hcard k k x = x := by
  unfold infra_712u_Mp
  by_cases hs : ∃ β, β ⋖ k
  · obtain ⟨β, hβ⟩ := hs
    rw [(infra_78_engine_succ_eq _ _ _ _ _ hβ).2 k, if_neg (lt_irrefl k)]
    rfl
  by_cases hk : IsMin k
  · rw [(infra_78_engine_min_eq _ _ _ _ _ hk).2 k]
    rfl
  · rw [(infra_78_engine_lim_eq _ _ _ _ _ hk hs).2 k]
    simp only [lt_irrefl, ↓reduceDIte]
    rfl

/-- **The common-object recursion is valid at every stage (proved, cycle 89).** Well-founded
induction over `WithTop L.δ`: base `infra_712u_base_R`, successor `infra_712u_succ_R`, limit
`infra_712u_lim_R`, driven by the generic engine's unfolding equations. -/
theorem infra_712u_good (k : WithTop L.δ) : infra_712u_Good C C' e ei h0 h1 hm hcard k := by
  classical
  induction k using WellFoundedLT.induction with
  | _ k IH =>
  unfold infra_712u_Good
  set O := infra_712u_O C C' e ei h0 h1 hm hcard with hOdef
  set Mp := infra_712u_Mp C C' e ei h0 h1 hm hcard with hMpdef
  have hself : ∀ j x, Mp j j x = x := infra_712u_Mp_self C C' e ei h0 h1 hm hcard
  by_cases hs : ∃ β, β ⋖ k
  · obtain ⟨β, hβ⟩ := hs
    have IHβ := IH β hβ.lt
    have Hc : ∃ k', β ⋖ k' ∧ infra_712u_StateOK C C' e ei β (O β) := ⟨k, hβ, IHβ.1⟩
    have hck : Hc.choose = k := by
      have h1' := Hc.choose_spec.1
      rcases lt_trichotomy Hc.choose k with hlt | heq | hgt
      · exact absurd hlt (hβ.2 h1'.lt)
      · exact heq
      · exact absurd hgt (h1'.2 hβ.lt)
    have hsop : infra_712u_sop C C' e ei h0 h1 hm β (O β) =
        Classical.choose (infra_712u_succ_R C C' e ei h0 h1 hm β Hc.choose Hc.choose_spec.1
          (O β) Hc.choose_spec.2) := dif_pos Hc
    have spec := Classical.choose_spec (infra_712u_succ_R C C' e ei h0 h1 hm β Hc.choose
      Hc.choose_spec.1 (O β) Hc.choose_spec.2)
    rw [← hsop, hck] at spec
    set R := infra_712u_sop C C' e ei h0 h1 hm β (O β) with hRdef
    obtain ⟨okR, harr, hstep⟩ := spec
    have hO : O k = R.1 := (infra_78_engine_succ_eq _ _ _ _ _ hβ).1
    have hM : ∀ i, Mp i k = if i < k then R.2 ∘ Mp i β else id :=
      (infra_78_engine_succ_eq _ _ _ _ _ hβ).2
    have hle : ∀ i, i < k → i ≤ β := fun i hi => by
      by_contra hc
      exact hβ.2 (lt_of_not_ge hc) hi
    refine ⟨hO ▸ okR, fun i hik => ?_, hself k, fun i j hij hjk x => ?_⟩
    · rcases hik.lt_or_eq with hik | rfl
      · have hiβ := hle i hik
        obtain ⟨a1, a2, a3⟩ := IHβ.2.1 i hiβ
        rw [hM i, if_pos hik, hO]
        refine ⟨a1.comp harr, fun x => ?_, fun x => ?_⟩
        · show R.2 (Mp i β ((O i).2.1 x)) = _
          have := DFunLike.congr_fun (C.step_comp hiβ hβ.le PUnit.unit) x
          exact (congrArg R.2 (a2 x)).trans (((hstep hβ.le).1 _).symm.trans
            (congrArg R.1.2.1 this))
        · show R.2 (Mp i β ((O i).2.2 x)) = _
          have := DFunLike.congr_fun (C'.step_comp (e.withTopCongr.monotone hiβ)
            (e.withTopCongr.monotone hβ.le) PUnit.unit) x
          exact (congrArg R.2 (a3 x)).trans (((hstep hβ.le).2 _).symm.trans
            (congrArg R.1.2.2 this))
      · refine ⟨?_, fun x => ?_, fun x => ?_⟩
        · have : Mp i i = id := funext (hself i)
          rw [this]
          exact infra_712u_IsArr.id _
        · rw [hself]; exact congrArg _ (infra_712u_step_self _ _ x).symm
        · rw [hself]; exact congrArg _ (infra_712u_step_self _ _ x).symm
    · rcases hjk.lt_or_eq with hjk | rfl
      · have hik := lt_of_le_of_lt hij hjk
        rw [hM i, if_pos hik, hM j, if_pos hjk]
        exact congrArg R.2 (IHβ.2.2.2 i j hij (hle j hjk) x)
      · rw [hself]
  by_cases hk : IsMin k
  · have hk' : ∀ j, k ≤ j := fun j => (le_total k j).elim id (fun h => hk h)
    have H : ∃ k : WithTop L.δ, IsMin k := ⟨k, hk⟩
    have hck : H.choose = k := le_antisymm (H.choose_spec (hk' _)) (hk' _)
    have hs0 : infra_712u_s0 C C' e ei = Classical.choose
        (infra_712u_base_R C C' e ei H.choose H.choose_spec) := dif_pos H
    have spec := Classical.choose_spec (infra_712u_base_R C C' e ei H.choose H.choose_spec)
    rw [← hs0, hck] at spec
    have hO : O k = infra_712u_s0 C C' e ei := (infra_78_engine_min_eq _ _ _ _ _ hk).1
    have hieq : ∀ i, i ≤ k → i = k := fun i hi => le_antisymm hi (hk' i)
    refine ⟨hO ▸ spec, fun i hik => ?_, hself k, fun i j hij hjk x => ?_⟩
    · obtain rfl := hieq i hik
      refine ⟨?_, fun x => ?_, fun x => ?_⟩
      · have : Mp i i = id := funext (hself i)
        rw [this]
        exact infra_712u_IsArr.id _
      · rw [hself]; exact congrArg _ (infra_712u_step_self _ _ x).symm
      · rw [hself]; exact congrArg _ (infra_712u_step_self _ _ x).symm
    · obtain rfl := hieq j hjk
      obtain rfl := hieq i (hij.trans hjk)
      rw [hself, hself]
  -- limit stage
  have hs' : ∀ i, ¬ i ⋖ k := fun i h => hs ⟨i, h⟩
  have hne : ∃ i, i < k := by
    rw [not_isMin_iff] at hk
    exact hk
  let cf : Set.Iio k → infra_712u_State P μ hμ := fun j => O j.1
  let mf : Set.Iio k → Set.Iio k → μ.ord.ToType → μ.ord.ToType := fun i j => Mp i.1 j.1
  have HL : infra_712u_LimHyp C C' e ei k cf mf :=
    ⟨hs', hne, fun i => (IH i.1 i.2).1, fun i j h => ((IH j.1 j.2).2.1 i.1 h).1,
      fun i x => hself i.1 x, fun i j l hij hjl x => (IH l.1 l.2).2.2.2 i.1 j.1 hij hjl x,
      fun i j h x => ((IH j.1 j.2).2.1 i.1 h).2.1 x, fun i j h x => ((IH j.1 j.2).2.1 i.1 h).2.2 x⟩
  have hlop : infra_712u_lop C C' e ei hcard k cf mf =
      Classical.choose (infra_712u_lim_R C C' e ei hcard k cf mf HL) := dif_pos HL
  have spec := Classical.choose_spec (infra_712u_lim_R C C' e ei hcard k cf mf HL)
  rw [← hlop] at spec
  set R := infra_712u_lop C C' e ei hcard k cf mf with hRdef
  obtain ⟨okR, harr, hcoh, hst1, hst2⟩ := spec
  have hO : O k = R.1 := (infra_78_engine_lim_eq _ _ _ _ _ hk hs).1
  have hM : ∀ i (hi : i < k), Mp i k = R.2 ⟨i, hi⟩ := fun i hi => by
    have := (infra_78_engine_lim_eq (infra_712u_s0 C C' e ei) id (fun f g => g ∘ f)
      (infra_712u_sop C C' e ei h0 h1 hm) (infra_712u_lop C C' e ei hcard) hk hs).2 i
    rw [dif_pos hi] at this
    exact this
  refine ⟨hO ▸ okR, fun i hik => ?_, hself k, fun i j hij hjk x => ?_⟩
  · rcases hik.lt_or_eq with hik | rfl
    · rw [hM i hik, hO]
      exact ⟨harr ⟨i, hik⟩, fun x => (hst1 ⟨i, hik⟩ x).symm, fun x => (hst2 ⟨i, hik⟩ x).symm⟩
    · refine ⟨?_, fun x => ?_, fun x => ?_⟩
      · have : Mp i i = id := funext (hself i)
        rw [this]
        exact infra_712u_IsArr.id _
      · rw [hself]; exact congrArg _ (infra_712u_step_self _ _ x).symm
      · rw [hself]; exact congrArg _ (infra_712u_step_self _ _ x).symm
  · rcases hjk.lt_or_eq with hjk | rfl
    · have hik := lt_of_le_of_lt hij hjk
      rw [hM i hik, hM j hjk]
      exact (hcoh ⟨i, hik⟩ ⟨j, hjk⟩ hij x).symm
    · rw [hself]

end Assembly

/-- **7.12(2), the common object for lists of length at most the level (statement).** -/
def infra_712u_common_short_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_712_levels P →
    ∀ (A : P.scheme.Object μ hμ) (L L' : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ] [LinearOrder L'.δ] [WellFoundedLT L'.δ]
      (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i)), #L.δ ≤ μ →
      ∀ (C : TiedListWitnessingChain L) (C' : TiedListWitnessingChain L'),
      (∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) →
      ∃ (N : P.scheme.Object μ hμ)
        (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C.stage ⊤))
          (P.scheme.asSystem hμ N))
        (g' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C'.stage ⊤))
          (P.scheme.asSystem hμ N)),
        (∀ v, (g.onVertex v).comp ((C.into ⊤).onVertex v) =
          (g'.onVertex v).comp ((C'.into ⊤).onVertex v)) ∧
        ∀ (i : L.δ) (a : L.indexAt i),
          g.mapOcc (C.mark i ⊤ (WithTop.coe_lt_top i) a) =
            g'.mapOcc (C'.mark (e i) ⊤ (WithTop.coe_lt_top (e i)) (ei i a))

/-- **7.12(2), the common object, `|δ| ≤ μ` (proved, cycle 89).** The packed recursion
(`infra_712u_good`) read off at the top stage. -/
theorem infra_712u_common_short (P : SingleModelData K) : infra_712u_common_short_statement P := by
  intro μ hμ hl A L L' _ _ _ _ e ei hδ C C' hm
  have hw : ℵ₀ < μ := (le_self_add : ℵ₀ ≤ infra_75_wide P ℵ₀).trans_lt hl.2.2
  have h0 : μ ∈ recursionClosedLevels P ℵ₀ := infra_712_recursionClosed_of_615 hl.2.1 le_rfl hw
  have h1 : Order.succ ℵ₀ ≤ μ := Order.succ_le_of_lt hw
  have hcard : #(WithTop L.δ) ≤ μ := by
    show #(Option L.δ) ≤ μ
    rw [Cardinal.mk_option]
    exact Cardinal.add_le_of_le hw.le hδ (Cardinal.one_le_aleph0.trans hw.le)
  obtain ⟨⟨hG, hG', hA, hmk⟩, -⟩ := infra_712u_good C C' e ei h0 h1 hm hcard ⊤
  refine ⟨_, hG.arr, hG'.arr, fun v => ?_, fun i a => ?_⟩
  · obtain rfl : v = PUnit.unit := Subsingleton.elim _ _
    exact DFunLike.ext _ _ fun x =>
      (hG.arr_apply _).trans ((hA x).trans (hG'.arr_apply _).symm)
  · exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq ((hG.arr_apply _).trans
      ((hmk i (WithTop.coe_lt_top i) a).trans (hG'.arr_apply _).symm)))

/-- **7.12(2), the common object for lists longer than the level (statement; open tip
`infra_712u_common_long`).** Total length `≤ μ` but `|δ| > μ`, so all but at most `μ` entries
are empty tuples; the packed recursion's limit unions are then indexed by more than `μ` stages
(`infra_712u_packed_limit` needs `|WithTop δ| ≤ μ`). -/
def infra_712u_common_long_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_712_levels P →
    ∀ (A : P.scheme.Object μ hμ) (L L' : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ] [LinearOrder L'.δ] [WellFoundedLT L'.δ]
      (e : L.δ ≃o L'.δ) (ei : ∀ i, L.indexAt i ≃ L'.indexAt (e i)),
      #(Σ i, L.indexAt i) ≤ μ → #(Σ i, L'.indexAt i) ≤ μ → μ < #L.δ →
      ∀ (C : TiedListWitnessingChain L) (C' : TiedListWitnessingChain L'),
      (∀ i, SameGaloisType (L.one i) (L'.one (e i)) (ei i) (Equiv.refl _)) →
      ∃ (N : P.scheme.Object μ hμ)
        (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C.stage ⊤))
          (P.scheme.asSystem hμ N))
        (g' : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (C'.stage ⊤))
          (P.scheme.asSystem hμ N)),
        (∀ v, (g.onVertex v).comp ((C.into ⊤).onVertex v) =
          (g'.onVertex v).comp ((C'.into ⊤).onVertex v)) ∧
        ∀ (i : L.δ) (a : L.indexAt i),
          g.mapOcc (C.mark i ⊤ (WithTop.coe_lt_top i) a) =
            g'.mapOcc (C'.mark (e i) ⊤ (WithTop.coe_lt_top (e i)) (ei i a))

/-- **7.12(2), the common object from its two length cases (proved glue, cycle 89).** -/
theorem infra_712u_common_of_parts (P : SingleModelData K)
    (hs : infra_712u_common_short_statement P) (hl : infra_712u_common_long_statement P) :
    infra_712u_common_statement P := by
  intro μ hμ hlev A L L' _ _ _ _ e ei h1 h2 C C' hm
  rcases le_or_gt #L.δ μ with hδ | hδ
  · exact hs hμ hlev A L L' e ei hδ C C' hm
  · exact hl hμ hlev A L L' e ei h1 h2 hδ C C' hm

/-- **7.12(2), long lists (open tip `infra_712u_common_long`).** -/
theorem infra_712u_common_long (P : SingleModelData K) : infra_712u_common_long_statement P := by
  sorry

/-- **7.12(2), the common object (glue, cycle 89).** The `|δ| ≤ μ` case is proved
(`infra_712u_common_short`); the long case is the open tip `infra_712u_common_long`. -/
theorem infra_712u_common (P : SingleModelData K) : infra_712u_common_statement P :=
  infra_712u_common_of_parts P (infra_712u_common_short P) (infra_712u_common_long P)

/-- **7.12(2), the marks (glue, cycle 88).** -/
theorem infra_712u_marks (P : SingleModelData K) : infra_712u_marks_statement P :=
  infra_712u_marks_of_common P (infra_712u_common P)

end
end AEC
