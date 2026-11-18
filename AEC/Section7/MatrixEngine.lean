module

public import AEC.Section7.MatrixRecursion
public import AEC.Section7.ChainEngine

@[expose] public section

/-!
# Instantiating the coherent-chain engine for the `ρ⁺` matrix (grokbot cycle 50)

Split of `infra_78_engine_matrix_instantiate`.

* **Fixed carrier (checked, not assumed).** In the single-model scheme the objects at level `κ`
  are `SMObject K κ`, i.e. `K`-structures on the fixed type `κ.ord.ToType`
  (`SingleModelData.scheme`, `Object := fun μ _ => SMObject K μ`), so every object the successor
  and limit steps produce (they are all objects of `P.scheme` at level `κ`) lives on
  `κ.ord.ToType`; `infra_78_carrier_fixed` checks this by `rfl`.
* **Plain-map / arrow conversion** (`infra_78_IsArr`, `infra_78_toArr`, `infra_78_plain`):
  an arrow is determined by its plain carrier map (`infra_78_arrow_ext`), and identity and
  composition of plain maps correspond to `SystemArrow.refl` / `SystemArrow.comp`.
* **Pair chains** (`infra_78_pairMatrix`): stages are `Infra78Stage` (pair `X → Y` as a plain map
  with arrow witness, plus extra non-dependent data `e : E`), steps are pairs of plain maps.
  Feeding `infra_78_coherent_chain_engine` any successor operator producing commuting stage
  arrows, with the limit operator built from `infra_78_limit_pair` (under `ρ⁺ < κ`), yields an
  `Infra78Matrix` with `IdLaw`, `CompLaw`, `ContAtLimits`, and its stages computed by the
  successor operator at successors (`infra_78_pairMatrix_succ`), by the union at limits
  (`infra_78_pairMatrix_limit`) and by the seed at the minimum.

The concrete Prop 7.8 operators (successor via `infra_78_recursion_succ_stage` with the mark,
base and bookkeeping sets carried as plain data in `e`, limit data = union of earlier images)
are tracked as `infra_78_matrix_operators`.
-/

universe u
open Cardinal
namespace AEC
variable {K : AbstractElementaryClass.{u}}

section Carrier
variable {P : SingleModelData K} {κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

/-- The fixed-carrier premise, checked by `rfl`: every object of the single-model scheme at level
`κ` lives on `κ.ord.ToType` (the scheme's objects are `SMObject K κ`). -/
theorem infra_78_carrier_fixed (X : P.scheme.Object κ hκ) :
    ((P.scheme.asSystem hκ X).obj PUnit.unit).carrier = κ.ord.ToType := rfl

/-- A plain carrier map is an arrow `X → Y` of the scheme. -/
def infra_78_IsArr (X Y : P.scheme.Object κ hκ) (f : κ.ord.ToType → κ.ord.ToType) : Prop :=
  ∃ a : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y),
    ∀ x, a.onVertex PUnit.unit x = f x

/-- The plain map of an arrow. -/
def infra_78_plain {X Y : P.scheme.Object κ hκ}
    (a : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y)) :
    κ.ord.ToType → κ.ord.ToType := fun x => a.onVertex PUnit.unit x

noncomputable def infra_78_toArr {X Y : P.scheme.Object κ hκ} {f : κ.ord.ToType → κ.ord.ToType}
    (h : infra_78_IsArr X Y f) :
    SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y) :=
  Classical.choose h

theorem infra_78_toArr_apply {X Y : P.scheme.Object κ hκ} {f : κ.ord.ToType → κ.ord.ToType}
    (h : infra_78_IsArr X Y f) (x) : (infra_78_toArr h).onVertex PUnit.unit x = f x :=
  Classical.choose_spec h x

theorem infra_78_arrow_ext {X Y : P.scheme.Object κ hκ}
    {a b : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y)}
    (h : ∀ x, a.onVertex PUnit.unit x = b.onVertex PUnit.unit x) : a = b := by
  apply SystemArrow.ext
  intro v
  cases v
  exact DFunLike.ext _ _ h

theorem infra_78_isArr_plain {X Y : P.scheme.Object κ hκ}
    (a : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y)) :
    infra_78_IsArr X Y (infra_78_plain a) := ⟨a, fun _ => rfl⟩

theorem infra_78_toArr_plain {X Y : P.scheme.Object κ hκ}
    (a : SystemArrow K oneVertexShape (P.scheme.asSystem hκ X) (P.scheme.asSystem hκ Y)) :
    infra_78_toArr (infra_78_isArr_plain a) = a :=
  infra_78_arrow_ext fun x => infra_78_toArr_apply _ x

theorem infra_78_toArr_congr {X Y : P.scheme.Object κ hκ} {f g : κ.ord.ToType → κ.ord.ToType}
    (hf : infra_78_IsArr X Y f) (hg : infra_78_IsArr X Y g) (h : f = g) :
    infra_78_toArr hf = infra_78_toArr hg := by
  subst h; rfl

theorem infra_78_isArr_id (X : P.scheme.Object κ hκ) : infra_78_IsArr X X id :=
  ⟨SystemArrow.refl _, fun _ => rfl⟩

theorem infra_78_toArr_id (X : P.scheme.Object κ hκ) (h : infra_78_IsArr X X id) :
    infra_78_toArr h = SystemArrow.refl _ :=
  infra_78_arrow_ext fun x => infra_78_toArr_apply h x

theorem infra_78_isArr_comp {X Y Z : P.scheme.Object κ hκ} {f g : κ.ord.ToType → κ.ord.ToType}
    (hf : infra_78_IsArr X Y f) (hg : infra_78_IsArr Y Z g) : infra_78_IsArr X Z (g ∘ f) :=
  ⟨SystemArrow.comp (infra_78_toArr hf) (infra_78_toArr hg), fun x => by
    show (infra_78_toArr hg).onVertex PUnit.unit ((infra_78_toArr hf).onVertex PUnit.unit x) = _
    rw [infra_78_toArr_apply, infra_78_toArr_apply]; rfl⟩

theorem infra_78_toArr_comp {X Y Z : P.scheme.Object κ hκ} {f g : κ.ord.ToType → κ.ord.ToType}
    (hf : infra_78_IsArr X Y f) (hg : infra_78_IsArr Y Z g) (hgf : infra_78_IsArr X Z (g ∘ f)) :
    infra_78_toArr hgf = SystemArrow.comp (infra_78_toArr hf) (infra_78_toArr hg) :=
  infra_78_arrow_ext fun x => by
    rw [infra_78_toArr_apply]
    show _ = (infra_78_toArr hg).onVertex PUnit.unit ((infra_78_toArr hf).onVertex PUnit.unit x)
    rw [infra_78_toArr_apply, infra_78_toArr_apply]; rfl

end Carrier

section PairChain
variable {P : SingleModelData K} {ρ κ : Cardinal.{u}} {hκ : κ ∈ P.eligible}

/-- A stage of the plain-data matrix recursion: a pair `X → Y` at level `κ` (plain map with its
arrow witness) and extra non-dependent stage data `e : E` (e.g. bookkeeping sets). -/
structure Infra78Stage (P : SingleModelData K) {κ : Cardinal.{u}} (hκ : κ ∈ P.eligible)
    (E : Type u) where
  X : P.scheme.Object κ hκ
  Y : P.scheme.Object κ hκ
  p : κ.ord.ToType → κ.ord.ToType
  hp : infra_78_IsArr X Y p
  e : E

/-- Plain step data: maps on the `X` and `Y` carriers. -/
abbrev Infra78Step (κ : Cardinal.{u}) := (κ.ord.ToType → κ.ord.ToType) × (κ.ord.ToType → κ.ord.ToType)

def infra_78_stepId : Infra78Step κ := (id, id)
def infra_78_stepComp (f g : Infra78Step κ) : Infra78Step κ := (g.1 ∘ f.1, g.2 ∘ f.2)

/-- A plain step is an arrow of stages: both maps are arrows and the square commutes. -/
def infra_78_StageArr {E : Type u} (s t : Infra78Stage P hκ E) (f : Infra78Step κ) : Prop :=
  infra_78_IsArr s.X t.X f.1 ∧ infra_78_IsArr s.Y t.Y f.2 ∧ t.p ∘ f.1 = f.2 ∘ s.p

/-- The chain laws below `k` for restricted plain data. -/
def infra_78_ChainOK {ι : Type u} [Preorder ι] {E : Type u} {k : ι}
    (cf : Set.Iio k → Infra78Stage P hκ E) (mf : Set.Iio k → Set.Iio k → Infra78Step κ) : Prop :=
  (∀ i j, i ≤ j → infra_78_StageArr (cf i) (cf j) (mf i j)) ∧ (∀ i, mf i i = infra_78_stepId) ∧
  (∀ i j l, i ≤ j → j ≤ l → mf i l = infra_78_stepComp (mf i j) (mf j l))

/-- What the limit operator must deliver: a cocone of stage arrows, compatible with the chain,
with extra data `eF` of the limit pair and cocone, jointly covering both carriers (continuity at the limit). -/
def infra_78_LimSpec {ι : Type u} [Preorder ι] {E : Type u} {k : ι}
    (cf : Set.Iio k → Infra78Stage P hκ E) (mf : Set.Iio k → Set.Iio k → Infra78Step κ)
    (eF : P.scheme.Object κ hκ → P.scheme.Object κ hκ → (κ.ord.ToType → κ.ord.ToType) →
      (Set.Iio k → Infra78Step κ) → E)
    (out : Infra78Stage P hκ E × (Set.Iio k → Infra78Step κ)) : Prop :=
  (∀ j, infra_78_StageArr (cf j) out.1 (out.2 j)) ∧
  (∀ i j, i ≤ j → infra_78_stepComp (mf i j) (out.2 j) = out.2 i) ∧
  out.1.e = eF out.1.X out.1.Y out.1.p out.2 ∧
  (∀ x, ∃ j y, (out.2 j).1 y = x) ∧ (∀ x, ∃ j y, (out.2 j).2 y = x)

/-- The limit stage exists (from `infra_78_limit_pair`, under `ρ⁺ < κ`). -/
theorem infra_78_limSpec_exists {E : Type u} (hρκ : Order.succ ρ < κ)
    {k : (Order.succ ρ).ord.ToType} (hk : Order.IsSuccLimit k)
    (cf : Set.Iio k → Infra78Stage P hκ E) (mf : Set.Iio k → Set.Iio k → Infra78Step κ)
    (eF : P.scheme.Object κ hκ → P.scheme.Object κ hκ → (κ.ord.ToType → κ.ord.ToType) →
      (Set.Iio k → Infra78Step κ) → E)
    (hok : infra_78_ChainOK cf mf) : ∃ out, infra_78_LimSpec cf mf eF out := by
  obtain ⟨hA, hI, hC⟩ := hok
  let pair := fun j => infra_78_toArr (cf j).hp
  let sX : ∀ {a b : Set.Iio k}, a ≤ b → _ := fun {a b} h => infra_78_toArr (hA a b h).1
  let sY : ∀ {a b : Set.Iio k}, a ≤ b → _ := fun {a b} h => infra_78_toArr (hA a b h).2.1
  have hXr : ∀ a, sX (le_refl a) = SystemArrow.refl _ := fun a =>
    infra_78_arrow_ext fun x => by
      show (infra_78_toArr (hA a a le_rfl).1).onVertex PUnit.unit x = x
      rw [infra_78_toArr_apply, hI a]; rfl
  have hYr : ∀ a, sY (le_refl a) = SystemArrow.refl _ := fun a =>
    infra_78_arrow_ext fun x => by
      show (infra_78_toArr (hA a a le_rfl).2.1).onVertex PUnit.unit x = x
      rw [infra_78_toArr_apply, hI a]; rfl
  have hXt : ∀ {a b c : Set.Iio k} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sX (h₁.trans h₂) = SystemArrow.comp (sX h₁) (sX h₂) := fun {a b c} h₁ h₂ =>
    infra_78_arrow_ext fun x => by
      show (infra_78_toArr (hA a c (h₁.trans h₂)).1).onVertex PUnit.unit x =
        (infra_78_toArr (hA b c h₂).1).onVertex PUnit.unit
          ((infra_78_toArr (hA a b h₁).1).onVertex PUnit.unit x)
      rw [infra_78_toArr_apply, infra_78_toArr_apply, infra_78_toArr_apply, hC a b c h₁ h₂]; rfl
  have hYt : ∀ {a b c : Set.Iio k} (h₁ : a ≤ b) (h₂ : b ≤ c),
      sY (h₁.trans h₂) = SystemArrow.comp (sY h₁) (sY h₂) := fun {a b c} h₁ h₂ =>
    infra_78_arrow_ext fun x => by
      show (infra_78_toArr (hA a c (h₁.trans h₂)).2.1).onVertex PUnit.unit x =
        (infra_78_toArr (hA b c h₂).2.1).onVertex PUnit.unit
          ((infra_78_toArr (hA a b h₁).2.1).onVertex PUnit.unit x)
      rw [infra_78_toArr_apply, infra_78_toArr_apply, infra_78_toArr_apply, hC a b c h₁ h₂]; rfl
  have hcomm : ∀ {a b : Set.Iio k} (h : a ≤ b),
      SystemArrow.comp (pair a) (sY h) = SystemArrow.comp (sX h) (pair b) := fun {a b} h =>
    infra_78_arrow_ext fun x => by
      show (infra_78_toArr (hA a b h).2.1).onVertex PUnit.unit
          ((infra_78_toArr (cf a).hp).onVertex PUnit.unit x) =
        (infra_78_toArr (cf b).hp).onVertex PUnit.unit
          ((infra_78_toArr (hA a b h).1).onVertex PUnit.unit x)
      rw [infra_78_toArr_apply, infra_78_toArr_apply, infra_78_toArr_apply, infra_78_toArr_apply]
      exact (congrFun (hA a b h).2.2 x).symm
  obtain ⟨Xδ, Yδ, lX, lY, pδ, -, -, -, hcX, hcY, hsq, hcovX, hcovY⟩ :=
    infra_78_limit_pair hρκ hk (fun j => (cf j).X) (fun j => (cf j).Y) pair sX sY hXr hYr hXt hYt
      hcomm
  refine ⟨(⟨Xδ, Yδ, infra_78_plain pδ, infra_78_isArr_plain pδ,
      eF Xδ Yδ (infra_78_plain pδ) fun j => (infra_78_plain (lX j), infra_78_plain (lY j))⟩,
    fun j => (infra_78_plain (lX j), infra_78_plain (lY j))), ?_, ?_, rfl, ?_, ?_⟩
  · intro j
    refine ⟨infra_78_isArr_plain _, infra_78_isArr_plain _, ?_⟩
    funext x
    have := DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hsq j)) x
    show pδ.onVertex PUnit.unit ((lX j).onVertex PUnit.unit x) =
      (lY j).onVertex PUnit.unit ((cf j).p x)
    rw [← infra_78_toArr_apply (cf j).hp x]
    exact this.symm
  · intro i j h
    refine Prod.ext (funext fun x => ?_) (funext fun x => ?_)
    · have := DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hcX h)) x
      show (lX j).onVertex PUnit.unit ((mf i j).1 x) = (lX i).onVertex PUnit.unit x
      rw [← infra_78_toArr_apply (hA i j h).1 x]
      exact this
    · have := DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit) (hcY h)) x
      show (lY j).onVertex PUnit.unit ((mf i j).2 x) = (lY i).onVertex PUnit.unit x
      rw [← infra_78_toArr_apply (hA i j h).2.1 x]
      exact this
  · intro x; obtain ⟨j, y, hy⟩ := hcovX x; exact ⟨j, y, hy⟩
  · intro x; obtain ⟨j, y, hy⟩ := hcovY x; exact ⟨j, y, hy⟩


open Classical in
/-- The limit operator: a stage meeting `infra_78_LimSpec` (chosen), or a dummy if none. -/
noncomputable def infra_78_pairLop {ι : Type u} [Preorder ι] {E : Type u}
    (s0 : Infra78Stage P hκ E)
    (limE : (k : ι) → (Set.Iio k → Infra78Stage P hκ E) → (Set.Iio k → Set.Iio k → Infra78Step κ) →
      P.scheme.Object κ hκ → P.scheme.Object κ hκ → (κ.ord.ToType → κ.ord.ToType) →
      (Set.Iio k → Infra78Step κ) → E)
    (k : ι) (cf : Set.Iio k → Infra78Stage P hκ E) (mf : Set.Iio k → Set.Iio k → Infra78Step κ) :
    Infra78Stage P hκ E × (Set.Iio k → Infra78Step κ) :=
  if h : ∃ out, infra_78_LimSpec cf mf (limE k cf mf) out then Classical.choose h
  else (s0, fun _ => infra_78_stepId)

theorem infra_78_pairLop_spec {ι : Type u} [Preorder ι] {E : Type u}
    (s0 : Infra78Stage P hκ E)
    (limE : (k : ι) → (Set.Iio k → Infra78Stage P hκ E) → (Set.Iio k → Set.Iio k → Infra78Step κ) →
      P.scheme.Object κ hκ → P.scheme.Object κ hκ → (κ.ord.ToType → κ.ord.ToType) →
      (Set.Iio k → Infra78Step κ) → E)
    (k : ι) (cf : Set.Iio k → Infra78Stage P hκ E) (mf : Set.Iio k → Set.Iio k → Infra78Step κ)
    (h : ∃ out, infra_78_LimSpec cf mf (limE k cf mf) out) :
    infra_78_LimSpec cf mf (limE k cf mf) (infra_78_pairLop s0 limE k cf mf) := by
  unfold infra_78_pairLop
  rw [dif_pos h]
  exact Classical.choose_spec h

variable (hρκ : Order.succ ρ < κ) {E : Type u} (s0 : Infra78Stage P hκ E)
  (sop : (Order.succ ρ).ord.ToType → Infra78Stage P hκ E → Infra78Stage P hκ E × Infra78Step κ)
  (limE : (k : (Order.succ ρ).ord.ToType) → (Set.Iio k → Infra78Stage P hκ E) →
    (Set.Iio k → Set.Iio k → Infra78Step κ) → P.scheme.Object κ hκ → P.scheme.Object κ hκ →
    (κ.ord.ToType → κ.ord.ToType) → (Set.Iio k → Infra78Step κ) → E)

/-- Stage `k` of the plain-data matrix recursion. -/
noncomputable abbrev infra_78_pcObj (k : (Order.succ ρ).ord.ToType) : Infra78Stage P hκ E :=
  infra_78_engineObj s0 infra_78_stepId infra_78_stepComp sop (infra_78_pairLop s0 limE) k

/-- The plain step from stage `i` to stage `k`. -/
noncomputable abbrev infra_78_pcMap (i k : (Order.succ ρ).ord.ToType) : Infra78Step κ :=
  infra_78_engineMap s0 infra_78_stepId infra_78_stepComp sop (infra_78_pairLop s0 limE) i k

theorem infra_78_stageArr_id {E : Type u} (s : Infra78Stage P hκ E) :
    infra_78_StageArr s s infra_78_stepId :=
  ⟨infra_78_isArr_id _, infra_78_isArr_id _, rfl⟩

theorem infra_78_stageArr_comp {E : Type u} {s t w : Infra78Stage P hκ E} {f g : Infra78Step κ}
    (hf : infra_78_StageArr s t f) (hg : infra_78_StageArr t w g) :
    infra_78_StageArr s w (infra_78_stepComp f g) := by
  refine ⟨?_, ?_, ?_⟩
  · show infra_78_IsArr s.X w.X (g.1 ∘ f.1); exact infra_78_isArr_comp hf.1 hg.1
  · show infra_78_IsArr s.Y w.Y (g.2 ∘ f.2); exact infra_78_isArr_comp hf.2.1 hg.2.1
  funext x
  show w.p (g.1 (f.1 x)) = g.2 (f.2 (s.p x))
  have h1 : t.p (f.1 x) = f.2 (s.p x) := congrFun hf.2.2 x
  have h2 : w.p (g.1 (f.1 x)) = g.2 (t.p (f.1 x)) := congrFun hg.2.2 (f.1 x)
  rw [h2, h1]

include hρκ in
/-- The engine laws for the plain-data matrix recursion. -/
theorem infra_78_pairChain_laws
    (hsop : ∀ β s, infra_78_StageArr s (sop β s).1 (sop β s).2) :
    (∀ i k, i ≤ k → infra_78_StageArr (infra_78_pcObj s0 sop limE i) (infra_78_pcObj s0 sop limE k)
      (infra_78_pcMap s0 sop limE i k)) ∧
    (∀ k, infra_78_pcMap s0 sop limE k k = infra_78_stepId) ∧
    (∀ i j k, i ≤ j → j ≤ k → infra_78_pcMap s0 sop limE i k =
      infra_78_stepComp (infra_78_pcMap s0 sop limE i j) (infra_78_pcMap s0 sop limE j k)) := by
  refine infra_78_coherent_chain_engine s0 infra_78_stepId infra_78_stepComp sop
    (infra_78_pairLop s0 limE) infra_78_StageArr infra_78_stageArr_id
    (fun hf hg => infra_78_stageArr_comp hf hg) (fun _ => rfl) (fun _ _ _ => rfl) hsop ?_
  intro k hmin hs cf mf hA hI hC
  have hk : Order.IsSuccLimit k := ⟨hmin, fun b hb => hs ⟨b, hb⟩⟩
  have := infra_78_pairLop_spec s0 limE k cf mf
    (infra_78_limSpec_exists hρκ hk cf mf _ ⟨hA, hI, hC⟩)
  exact ⟨this.1, this.2.1⟩


variable (hsop : ∀ β s, infra_78_StageArr s (sop β s).1 (sop β s).2)

/-- **The `ρ⁺` matrix from the plain-data recursion.** Objects are the engine stages, steps are
the plain maps turned back into arrows (`infra_78_toArr`); no casts. -/
noncomputable def infra_78_pairMatrix : Infra78Matrix P ρ hκ where
  X i := (infra_78_pcObj s0 sop limE i).X
  Y i := (infra_78_pcObj s0 sop limE i).Y
  pair i := infra_78_toArr (infra_78_pcObj s0 sop limE i).hp
  pair_permitted _ := trivial
  stepX {i j} h := infra_78_toArr ((infra_78_pairChain_laws hρκ s0 sop limE hsop).1 i j h).1
  stepY {i j} h := infra_78_toArr ((infra_78_pairChain_laws hρκ s0 sop limE hsop).1 i j h).2.1
  stepX_permitted _ := trivial
  stepY_permitted _ := trivial
  comm {i j} h := infra_78_arrow_ext fun x => by
    have H := (infra_78_pairChain_laws hρκ s0 sop limE hsop).1 i j h
    show (infra_78_toArr H.2.1).onVertex PUnit.unit
        ((infra_78_toArr (infra_78_pcObj s0 sop limE i).hp).onVertex PUnit.unit x) =
      (infra_78_toArr (infra_78_pcObj s0 sop limE j).hp).onVertex PUnit.unit
        ((infra_78_toArr H.1).onVertex PUnit.unit x)
    rw [infra_78_toArr_apply, infra_78_toArr_apply, infra_78_toArr_apply, infra_78_toArr_apply]
    exact (congrFun H.2.2 x).symm

theorem infra_78_pairMatrix_stepX_apply {i j : (Order.succ ρ).ord.ToType} (h : i ≤ j) (x) :
    ((infra_78_pairMatrix hρκ s0 sop limE hsop).stepX h).onVertex PUnit.unit x =
      (infra_78_pcMap s0 sop limE i j).1 x :=
  infra_78_toArr_apply _ x

theorem infra_78_pairMatrix_stepY_apply {i j : (Order.succ ρ).ord.ToType} (h : i ≤ j) (x) :
    ((infra_78_pairMatrix hρκ s0 sop limE hsop).stepY h).onVertex PUnit.unit x =
      (infra_78_pcMap s0 sop limE i j).2 x :=
  infra_78_toArr_apply _ x

theorem infra_78_pairMatrix_pair_apply (i : (Order.succ ρ).ord.ToType) (x) :
    ((infra_78_pairMatrix hρκ s0 sop limE hsop).pair i).onVertex PUnit.unit x =
      (infra_78_pcObj s0 sop limE i).p x :=
  infra_78_toArr_apply _ x

/-- Identity law of the recursion matrix. -/
theorem infra_78_pairMatrix_idLaw : (infra_78_pairMatrix hρκ s0 sop limE hsop).IdLaw := by
  have H := (infra_78_pairChain_laws hρκ s0 sop limE hsop).2.1
  refine ⟨fun i => infra_78_arrow_ext fun x => ?_, fun i => infra_78_arrow_ext fun x => ?_⟩
  · rw [infra_78_pairMatrix_stepX_apply, H i]; rfl
  · rw [infra_78_pairMatrix_stepY_apply, H i]; rfl

/-- Composition law of the recursion matrix. -/
theorem infra_78_pairMatrix_compLaw : (infra_78_pairMatrix hρκ s0 sop limE hsop).CompLaw := by
  have H := (infra_78_pairChain_laws hρκ s0 sop limE hsop).2.2
  refine ⟨fun {a b c} h₁ h₂ => infra_78_arrow_ext fun x => ?_,
    fun {a b c} h₁ h₂ => infra_78_arrow_ext fun x => ?_⟩
  · show _ = ((infra_78_pairMatrix hρκ s0 sop limE hsop).stepX h₂).onVertex PUnit.unit
      (((infra_78_pairMatrix hρκ s0 sop limE hsop).stepX h₁).onVertex PUnit.unit x)
    rw [infra_78_pairMatrix_stepX_apply, infra_78_pairMatrix_stepX_apply,
      infra_78_pairMatrix_stepX_apply, H a b c h₁ h₂]; rfl
  · show _ = ((infra_78_pairMatrix hρκ s0 sop limE hsop).stepY h₂).onVertex PUnit.unit
      (((infra_78_pairMatrix hρκ s0 sop limE hsop).stepY h₁).onVertex PUnit.unit x)
    rw [infra_78_pairMatrix_stepY_apply, infra_78_pairMatrix_stepY_apply,
      infra_78_pairMatrix_stepY_apply, H a b c h₁ h₂]; rfl

include hρκ hsop in
/-- At a limit stage the recursion matrix is given by the limit operator on the earlier stages. -/
theorem infra_78_pairMatrix_limit {k : (Order.succ ρ).ord.ToType} (hk : Order.IsSuccLimit k) :
    infra_78_LimSpec (fun j : Set.Iio k => infra_78_pcObj s0 sop limE j.1)
      (fun i j : Set.Iio k => infra_78_pcMap s0 sop limE i.1 j.1)
      (limE k (fun j => infra_78_pcObj s0 sop limE j.1)
        (fun i j => infra_78_pcMap s0 sop limE i.1 j.1))
      (infra_78_pcObj s0 sop limE k, fun j => infra_78_pcMap s0 sop limE j.1 k) := by
  have hmin : ¬ IsMin k := hk.not_isMin
  have hs : ¬ ∃ β, β ⋖ k := fun ⟨β, hβ⟩ => hk.isSuccPrelimit β hβ
  obtain ⟨hA, hI, hC⟩ := infra_78_pairChain_laws hρκ s0 sop limE hsop
  obtain ⟨hc, hm⟩ := infra_78_engine_lim_eq s0 infra_78_stepId infra_78_stepComp sop
    (infra_78_pairLop s0 limE) hmin hs
  have hspec := infra_78_pairLop_spec s0 limE k _ _
    (infra_78_limSpec_exists hρκ hk (fun j : Set.Iio k => infra_78_pcObj s0 sop limE j.1)
      (fun i j : Set.Iio k => infra_78_pcMap s0 sop limE i.1 j.1) _
      ⟨fun i j h => hA i j h, fun i => hI i, fun i j l h₁ h₂ => hC i j l h₁ h₂⟩)
  have hout : (infra_78_pcObj s0 sop limE k, fun j : Set.Iio k => infra_78_pcMap s0 sop limE j.1 k) =
      infra_78_pairLop s0 limE k (fun j : Set.Iio k => infra_78_pcObj s0 sop limE j.1)
        (fun i j : Set.Iio k => infra_78_pcMap s0 sop limE i.1 j.1) := by
    refine Prod.ext hc (funext fun j => ?_)
    exact (hm j.1).trans (dif_pos j.2)
  rw [hout]
  exact hspec

/-- Continuity at limits of the recursion matrix. -/
theorem infra_78_pairMatrix_contAtLimits :
    (infra_78_pairMatrix hρκ s0 sop limE hsop).ContAtLimits := by
  refine ⟨fun i hi x => ?_, fun i hi x => ?_⟩
  · obtain ⟨j, y, hy⟩ := (infra_78_pairMatrix_limit hρκ s0 sop limE hsop hi).2.2.2.1 x
    exact ⟨j.1, j.2, y, (infra_78_pairMatrix_stepX_apply hρκ s0 sop limE hsop j.2.le y).trans hy⟩
  · obtain ⟨j, y, hy⟩ := (infra_78_pairMatrix_limit hρκ s0 sop limE hsop hi).2.2.2.2 x
    exact ⟨j.1, j.2, y, (infra_78_pairMatrix_stepY_apply hρκ s0 sop limE hsop j.2.le y).trans hy⟩

include hρκ hsop in
/-- At a successor stage the recursion matrix is given by the successor operator. -/
theorem infra_78_pairMatrix_succ {β k : (Order.succ ρ).ord.ToType} (hβ : β ⋖ k) :
    infra_78_pcObj s0 sop limE k = (sop β (infra_78_pcObj s0 sop limE β)).1 ∧
    infra_78_pcMap s0 sop limE β k = (sop β (infra_78_pcObj s0 sop limE β)).2 := by
  obtain ⟨hc, hm⟩ := infra_78_engine_succ_eq s0 infra_78_stepId infra_78_stepComp sop
    (infra_78_pairLop s0 limE) hβ
  have H : infra_78_engineMap s0 infra_78_stepId infra_78_stepComp sop
      (infra_78_pairLop s0 limE) β β = infra_78_stepId :=
    (infra_78_pairChain_laws hρκ s0 sop limE hsop).2.1 β
  refine ⟨hc, (hm β).trans ?_⟩
  rw [if_pos hβ.lt, H]
  rfl

/-- At the least stage the recursion matrix is the seed `s0`. -/
theorem infra_78_pairMatrix_min {k : (Order.succ ρ).ord.ToType} (hk : IsMin k) :
    infra_78_pcObj s0 sop limE k = s0 :=
  (infra_78_engine_min_eq s0 infra_78_stepId infra_78_stepComp sop (infra_78_pairLop s0 limE) hk).1

end PairChain
end AEC
