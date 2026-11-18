module

public import AEC.Section7.Lemma711Successor
public import AEC.Section7.ClosureLevel
public import AEC.Section7.SuccessorStep
public import AEC.Section7.RetractionPair

/-!
# Lemma 7.12 (1): existence of a tied witnessing chain (split, cycle 85)

The paper builds the chain `(M_i)_{i ≤ δ}` inside one ambient containing `L`: at a successor,
Theorem 7.9 gives an all-dominated realization over `M_i + b_i` and its primeness clause embeds it
into the ambient over the tuple; at limits, unions. Separately, finite domination (Lemma 7.11,
fed by product independence) makes each actual `b_i` free over `M_i` from `A`.

Accordingly `TiedListPreChain L` is `TiedListWitnessingChain L` without the `free` field; the
construction is `infra_712_prechain_statement` (open) and the freeness is
`infra_712_free_marks_statement` (open). `infra_712_existence_at_of_parts` (proved) assembles
clause (1) of `lemma_7_12` at every level satisfying both sets of level hypotheses.

Freeness: `infra_712_free_marks_of_step` (well-founded induction) and
`infra_712_free_step_of_products` (Lemma 7.11 at the level, `infra_711_at_level`, applied to the
truncated chain `TiedListPreChain.truncate` of `TupleList.below i`, whose top stage is `Mᵢ`, with
`x = bᵢ`) reduce it to `infra_712_products_statement` (open). `TiedListPreChain.free_pull` moves a
mark's freeness from the top stage down to any later stage.
-/

@[expose] public section

namespace AEC
noncomputable section

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- A tied list witnessing chain without its freeness field (Definition 7.10 minus
`tp(bᵢ/Mᵢ) = tp(bᵢ/A)^fr`). -/
structure TiedListPreChain {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
    {A : P.scheme.Object μ hμ} (L : TupleList P.scheme hμ A) [LinearOrder L.δ] where
  stage : WithTop L.δ → P.scheme.Object μ hμ
  into : ∀ j, SystemArrow K oneVertexShape (P.scheme.asSystem hμ A)
    (P.scheme.asSystem hμ (stage j))
  into_arrow : ∀ j, P.scheme.permitted (X := A) (Y := stage j) (into j)
  step : ∀ {i j : WithTop L.δ}, i ≤ j →
    SystemArrow K oneVertexShape (P.scheme.asSystem hμ (stage i)) (P.scheme.asSystem hμ (stage j))
  step_arrow : ∀ {i j : WithTop L.δ} (h : i ≤ j),
    P.scheme.permitted (X := stage i) (Y := stage j) (step h)
  step_comp : ∀ {i j k : WithTop L.δ} (hij : i ≤ j) (hjk : j ≤ k) (v : oneVertexShape.Vertex),
    ((step hjk).onVertex v).comp ((step hij).onVertex v) = (step (hij.trans hjk)).onVertex v
  into_step : ∀ {i j : WithTop L.δ} (h : i ≤ j) (v : oneVertexShape.Vertex),
    ((step h).onVertex v).comp ((into i).onVertex v) = (into j).onVertex v
  first : ∀ i, (∀ k, i ≤ k) → ∀ v, Function.Bijective ((into i).onVertex v)
  continuous : ∀ j, (∀ i, ¬ i ⋖ j) → (∃ i, i < j) →
    ∀ v (x : ((P.scheme.asSystem hμ (stage j)).obj v).carrier),
      ∃ i, ∃ h : i < j, ∃ y, (step h.le).onVertex v y = x
  top : P.scheme.Object μ hμ
  toTop : SystemArrow K oneVertexShape (P.scheme.asSystem hμ (stage ⊤)) (P.scheme.asSystem hμ top)
  toTop_arrow : P.scheme.permitted (X := stage ⊤) (Y := top) toTop
  listToTop : SystemArrow K oneVertexShape (P.scheme.asSystem hμ L.host) (P.scheme.asSystem hμ top)
  listToTop_arrow : P.scheme.permitted (X := L.host) (Y := top) listToTop
  comm_A : ∀ v, (toTop.onVertex v).comp ((into ⊤).onVertex v) =
    (listToTop.onVertex v).comp (L.incl.onVertex v)
  mark : ∀ (i : L.δ) (j : WithTop L.δ), (i : WithTop L.δ) < j →
    L.indexAt i → Occurrence K oneVertexShape (P.scheme.asSystem hμ (stage j))
  mark_step : ∀ (i : L.δ) {j k : WithTop L.δ} (hj : (i : WithTop L.δ) < j) (hjk : j ≤ k)
    (a : L.indexAt i), (step hjk).mapOcc (mark i j hj a) = mark i k (lt_of_lt_of_le hj hjk) a
  mark_spec : ∀ (i : L.δ) (a : L.indexAt i),
    toTop.mapOcc (mark i ⊤ (WithTop.coe_lt_top i) a) = listToTop.mapOcc (L.val i a)

namespace TiedListPreChain

variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
  {A : P.scheme.Object μ hμ} {L : TupleList P.scheme hμ A} [LinearOrder L.δ]

/-- All-dominated increments (Definition 7.10). -/
def AllDominatedIncrement (C : TiedListPreChain L) : Prop :=
  ∀ (i : L.δ) (j : WithTop L.δ) (h : (i : WithTop L.δ) ⋖ j),
    AllDominated (C.step h.le) (C.step_arrow h.le) (L.indexAt i) (C.mark i j h.lt)

/-- The freeness field of Definition 7.10 at `i`: `tp(bᵢ/Mᵢ) = tp(bᵢ/A)^fr_{Mᵢ}` (tied). -/
def FreeAt (C : TiedListPreChain L) (i : L.δ) : Prop :=
  IsTiedFree (C.into (i : WithTop L.δ))
    ((asTuple (C.step (le_top : (i : WithTop L.δ) ≤ ⊤)) (C.step_arrow _)
        (C.mark i ⊤ (WithTop.coe_lt_top i))).restrict (C.into (i : WithTop L.δ)) (C.into_arrow _))
    (asTuple (C.step (le_top : (i : WithTop L.δ) ≤ ⊤)) (C.step_arrow _)
      (C.mark i ⊤ (WithTop.coe_lt_top i)))
    (Equiv.refl _)

/-- A pre-chain whose marks are free is a tied witnessing chain. -/
def toChain (C : TiedListPreChain L) (hfree : ∀ i, C.FreeAt i) : TiedListWitnessingChain L where
  stage := C.stage
  into := C.into
  into_arrow := C.into_arrow
  step := C.step
  step_arrow := C.step_arrow
  step_comp := C.step_comp
  into_step := C.into_step
  first := C.first
  continuous := C.continuous
  top := C.top
  toTop := C.toTop
  toTop_arrow := C.toTop_arrow
  listToTop := C.listToTop
  listToTop_arrow := C.listToTop_arrow
  comm_A := C.comm_A
  mark := C.mark
  mark_step := C.mark_step
  mark_spec := C.mark_spec
  free := hfree

theorem toChain_allDominated (C : TiedListPreChain L) (hfree : ∀ i, C.FreeAt i)
    (h : C.AllDominatedIncrement) : (C.toChain hfree).AllDominatedIncrement := h

end TiedListPreChain

section Truncation
variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}
  {A : P.scheme.Object μ hμ}

/-- The entries of a list strictly below `i`. -/
def TupleList.below (L : TupleList P.scheme hμ A) [LinearOrder L.δ] (i : L.δ) :
    TupleList P.scheme hμ A where
  δ := {k : L.δ // k < i}
  host := L.host
  incl := L.incl
  incl_arrow := L.incl_arrow
  indexAt k := L.indexAt k.1
  val k := L.val k.1
  finite_each k := L.finite_each k.1

instance TupleList.below_linearOrder (L : TupleList P.scheme hμ A) [LinearOrder L.δ] (i : L.δ) :
    LinearOrder (L.below i).δ := inferInstanceAs (LinearOrder {k : L.δ // k < i})

instance TupleList.below_wellFoundedLT (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
    [WellFoundedLT L.δ] (i : L.δ) : WellFoundedLT (L.below i).δ :=
  inferInstanceAs (WellFoundedLT {k : L.δ // k < i})

namespace TupleList
variable (L : TupleList P.scheme hμ A) [LinearOrder L.δ] (i : L.δ)

/-- Stages of the truncated chain inside the original one: `⊤ ↦ i`. -/
def belowLift : WithTop (L.below i).δ → WithTop L.δ
  | ⊤ => (i : WithTop L.δ)
  | (k : (L.below i).δ) => ((k.1 : L.δ) : WithTop L.δ)

variable {L i}

theorem belowLift_le (b : WithTop (L.below i).δ) : L.belowLift i b ≤ i := by
  cases b with
  | top => exact le_rfl
  | coe k => exact WithTop.coe_le_coe.2 k.2.le

theorem belowLift_lt_iff {a b : WithTop (L.below i).δ} :
    L.belowLift i a < L.belowLift i b ↔ a < b := by
  cases a with
  | top => cases b with
    | top => simp [belowLift]
    | coe l => exact ⟨fun h => absurd h (not_lt.2 (WithTop.coe_le_coe.2 l.2.le)),
        fun h => absurd h (not_lt.2 le_top)⟩
  | coe k => cases b with
    | top => exact ⟨fun _ => WithTop.coe_lt_top _, fun _ => WithTop.coe_lt_coe.2 k.2⟩
    | coe l => exact ⟨fun h => WithTop.coe_lt_coe.2 (show k < l from (WithTop.coe_lt_coe.1 h : k.1 < l.1)),
        fun h => WithTop.coe_lt_coe.2 (show k.1 < l.1 from (WithTop.coe_lt_coe.1 h : k < l))⟩

theorem belowLift_le_iff {a b : WithTop (L.below i).δ} :
    L.belowLift i a ≤ L.belowLift i b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, belowLift_lt_iff]

theorem belowLift_surj {c : WithTop L.δ} (b : WithTop (L.below i).δ) (h : c ≤ L.belowLift i b) :
    ∃ a, L.belowLift i a = c := by
  have hc := h.trans (belowLift_le b)
  cases c with
  | top => exact absurd hc (not_le.2 (WithTop.coe_lt_top i))
  | coe c =>
    rcases (WithTop.coe_le_coe.1 hc).lt_or_eq with hlt | heq
    · exact ⟨WithTop.some (show (L.below i).δ from ⟨c, hlt⟩), rfl⟩
    · exact ⟨⊤, by rw [heq]; rfl⟩

theorem belowLift_covBy {a b : WithTop (L.below i).δ} :
    L.belowLift i a ⋖ L.belowLift i b ↔ a ⋖ b := by
  constructor
  · rintro ⟨hlt, hno⟩
    exact ⟨belowLift_lt_iff.1 hlt, fun z h1 h2 =>
      hno (belowLift_lt_iff.2 h1) (belowLift_lt_iff.2 h2)⟩
  · rintro ⟨hlt, hno⟩
    refine ⟨belowLift_lt_iff.2 hlt, fun c h1 h2 => ?_⟩
    obtain ⟨z, rfl⟩ := belowLift_surj b h2.le
    exact hno (belowLift_lt_iff.1 h1) (belowLift_lt_iff.1 h2)

end TupleList

namespace TiedListPreChain
variable {L : TupleList P.scheme hμ A} [LinearOrder L.δ]

theorem free_pull (C : TiedListPreChain L) (k : L.δ) (hk : C.FreeAt k) (j : WithTop L.δ)
    (hj : (k : WithTop L.δ) < j) :
    IsTiedFree (C.into (k : WithTop L.δ))
      ((asTuple (C.step hj.le) (C.step_arrow _) (C.mark k j hj)).restrict
        (C.into (k : WithTop L.δ)) (C.into_arrow _))
      (asTuple (C.step hj.le) (C.step_arrow _) (C.mark k j hj)) (Equiv.refl _) := by
  have hfin : #(L.indexAt k) < μ :=
    haveI := L.finite_each k
    (Cardinal.lt_aleph0_of_finite _).trans_le (P.aleph0_le hμ)
  have hjt : j ≤ ⊤ := le_top
  set rj := asTuple (C.step hj.le) (C.step_arrow _) (C.mark k j hj) with hrj
  set rt := asTuple (C.step (le_top : (k : WithTop L.δ) ≤ ⊤)) (C.step_arrow _)
    (C.mark k ⊤ (WithTop.coe_lt_top k)) with hrt
  have hR : infra_78_HostRel rj rt (C.step hjt) (Equiv.refl _) := by
    refine ⟨fun v x => ?_, fun a => ?_⟩
    · show (C.step hjt).onVertex v ((C.step hj.le).onVertex v x) =
        (C.step (le_top : (k : WithTop L.δ) ≤ ⊤)).onVertex v x
      rw [← C.step_comp hj.le hjt v]; rfl
    · show C.mark k ⊤ (WithTop.coe_lt_top k) a = (C.step hjt).mapOcc (C.mark k j hj a)
      exact (C.mark_step k hj hjt a).symm
  have hRp : infra_78_HostRel (rj.restrict (C.into (k : WithTop L.δ)) (C.into_arrow _))
      (rt.restrict (C.into (k : WithTop L.δ)) (C.into_arrow _)) (C.step hjt) (Equiv.refl _) := by
    refine ⟨fun v x => ?_, hR.2⟩
    show (C.step hjt).onVertex v ((C.step hj.le).onVertex v ((C.into _).onVertex v x)) =
        (C.step (le_top : (k : WithTop L.δ) ≤ ⊤)).onVertex v ((C.into _).onVertex v x)
    rw [← C.step_comp hj.le hjt v]; rfl
  have H1 : IsTiedFree (C.into (k : WithTop L.δ))
      (rt.restrict (C.into (k : WithTop L.δ)) (C.into_arrow _)) rj (Equiv.refl _) :=
    (infra_78_tiedFree_host_target (C.into (k : WithTop L.δ))
      (rt.restrict (C.into (k : WithTop L.δ)) (C.into_arrow _)) (C.step_arrow hjt) hR rfl rfl
      hfin (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)).2 (by unfold FreeAt at hk; exact hk)
  exact infra_78_tiedFree_host_source' (C.into (k : WithTop L.δ)) (C.step_arrow hjt) hRp rfl rfl
    hfin rj (Equiv.refl _) (Equiv.refl _) (fun _ => rfl) H1


/-- **The chain truncated at `i`** (a tied witnessing chain of `L.below i` with top stage `Mᵢ`),
given that the marks below `i` are free. -/
def truncate (C : TiedListPreChain L) (i : L.δ) (hfree : ∀ k, k < i → C.FreeAt k) :
    TiedListWitnessingChain (L.below i) where
  stage j := C.stage (L.belowLift i j)
  into j := C.into (L.belowLift i j)
  into_arrow j := C.into_arrow _
  step h := C.step (TupleList.belowLift_le_iff.2 h)
  step_arrow h := C.step_arrow _
  step_comp hij hjk v := C.step_comp _ _ v
  into_step h v := C.into_step _ v
  first j hj v := C.first _ (fun c => by
    cases c with
    | top => exact le_top
    | coe c =>
      by_cases hc : c < i
      · exact TupleList.belowLift_le_iff.2 (hj (WithTop.some (show (L.below i).δ from ⟨c, hc⟩)))
      · exact (TupleList.belowLift_le j).trans (WithTop.coe_le_coe.2 (not_lt.1 hc))) v
  continuous j hno hex v x := by
    obtain ⟨c, hc, y, hy⟩ := C.continuous (L.belowLift i j)
      (fun c hcov => by
        obtain ⟨a, rfl⟩ := TupleList.belowLift_surj j hcov.le
        exact hno a (TupleList.belowLift_covBy.1 hcov))
      (by obtain ⟨a, ha⟩ := hex; exact ⟨_, TupleList.belowLift_lt_iff.2 ha⟩) v x
    obtain ⟨a, rfl⟩ := TupleList.belowLift_surj j hc.le
    exact ⟨a, TupleList.belowLift_lt_iff.1 hc, y, hy⟩
  top := C.top
  toTop := SystemArrow.comp (C.step (le_top : (i : WithTop L.δ) ≤ ⊤)) C.toTop
  toTop_arrow := P.scheme.comp _ _ (C.step_arrow _) C.toTop_arrow
  listToTop := C.listToTop
  listToTop_arrow := C.listToTop_arrow
  comm_A v := by
    show ((C.toTop.onVertex v).comp ((C.step (le_top : (i : WithTop L.δ) ≤ ⊤)).onVertex v)).comp
        ((C.into (i : WithTop L.δ)).onVertex v) = (C.listToTop.onVertex v).comp (L.incl.onVertex v)
    exact (congrArg (fun g => (C.toTop.onVertex v).comp g)
      (C.into_step (le_top : (i : WithTop L.δ) ≤ ⊤) v)).trans (C.comm_A v)
  mark k j h a := C.mark k.1 (L.belowLift i j)
    (TupleList.belowLift_lt_iff.2 h) a
  mark_step k j l hj hjk a := C.mark_step k.1 _ _ a
  mark_spec k a := by
    exact (congrArg C.toTop.mapOcc (C.mark_step k.1 (WithTop.coe_lt_coe.2 k.2)
      (le_top : (i : WithTop L.δ) ≤ ⊤) a)).trans (C.mark_spec k.1 a)
  free k := C.free_pull k.1 (hfree k.1 k.2) i (WithTop.coe_lt_coe.2 k.2)

theorem truncate_allDominated (C : TiedListPreChain L) (hC : C.AllDominatedIncrement) (i : L.δ)
    (hfree : ∀ k, k < i → C.FreeAt k) : (C.truncate i hfree).AllDominatedIncrement :=
  fun k j h => hC k.1 (L.belowLift i j) (TupleList.belowLift_covBy.2 h)

/-- The tuple `bᵢ` over `Mᵢ`, hosted in the top stage. -/
def markTuple (C : TiedListPreChain L) (i : L.δ) :
    TupleOver K oneVertexShape P.scheme hμ (C.stage (i : WithTop L.δ)) :=
  asTuple (C.step (le_top : (i : WithTop L.δ) ≤ ⊤)) (C.step_arrow _)
    (C.mark i ⊤ (WithTop.coe_lt_top i))

end TiedListPreChain

end Truncation

/-- Clause (1) of Lemma 7.12 over a fixed `A` at level `μ`. -/
def infra_712_existence_at (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (A : P.scheme.Object μ hμ) : Prop :=
  ∀ (L : TupleList P.scheme hμ A) [LinearOrder L.δ] [WellFoundedLT L.δ],
    #L.δ ≤ μ → ProductIndependentTied L →
    ∃ C : TiedListWitnessingChain L, C.AllDominatedIncrement

/-- **7.12(1), the chain construction (statement; open tip `infra_712_prechain`).** At a
Theorem 7.9 level (`infra_78_closedTail P ∩ infra_615_closed P`, the tail on which 7.9's
existence clause is proved), every well-ordered list of length `≤ μ` has an all-dominated
increment pre-chain: successors by Theorem 7.9 (realization over `Mᵢ + bᵢ`, embedded over the
tuple into the ambient by its primeness clause), limits by directed unions inside the ambient. -/
def infra_712_prechain_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ infra_78_closedTail P →
    μ ∈ infra_615_closed P →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ], #L.δ ≤ μ →
      ∃ C : TiedListPreChain L, C.AllDominatedIncrement

/-- **7.12(1) successor step (proved, cycle 85c).** At a Theorem 7.9 level, for a stage `X`
embedded into the ambient `N` by `g` and a finite tuple `b'` of `N`: an all-dominated
extension `f : X → Y` with a realization `b` of `tp(b'/X)`, and `h : Y → N` over `X` with
`h b = b'` (Theorem 7.9 existence, then its same-level primeness clause). -/
theorem infra_712_succ (P : SingleModelData K) {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible)
    (ht : μ ∈ infra_78_closedTail P) (hc : μ ∈ infra_615_closed P)
    (X N : P.scheme.Object μ hμ)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ N))
    (hg : P.scheme.permitted (X := X) (Y := N) g) (idx : Type u) [Finite idx]
    (b' : idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ N)) :
    ∃ (Y : P.scheme.Object μ hμ)
      (f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ Y))
      (hf : P.scheme.permitted (X := X) (Y := Y) f)
      (b : idx → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y))
      (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ N)),
      AllDominated f hf idx b ∧ P.scheme.permitted (X := Y) (Y := N) h ∧
        SystemArrow.comp f h = g ∧ ∀ k, h.onVertex (b k).1 (b k).2 = (b' k).2 := by
  let p : TupleOver K oneVertexShape P.scheme hμ X := ⟨μ, hμ, N, g, hg, idx, b'⟩
  have hfin : Finite p.idx := inferInstanceAs (Finite idx)
  obtain ⟨Y, f, hf, b, hAll, hS⟩ :=
    infra_79_existence_at P ⟨infra_79_tail P, infra_79_retraction_pair P⟩ (μ := μ) ⟨ht, hc⟩ X p hfin
  obtain ⟨h, hh, hcomp, hb⟩ := infra_79_primeness_same_level hμ X p hfin Y f hf b hAll hS N g hg b'
    (SameGaloisType.refl p)
  exact ⟨Y, f, hf, b, h, hAll, hh, hcomp, hb⟩


/-- **7.12(1) limit step (statement; open tip `infra_712_limit`).** A nonempty linearly ordered
system of level-`μ` stages of size `≤ μ`, compatibly mapped into an ambient `N`, has a union
stage: compatible maps into it, covering, and a map from it into `N` over the stages
(`SingleModelPackage.exists_directed_union` with its universal property). -/
def infra_712_limit_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible) (N : P.scheme.Object μ hμ) (ι : Type u)
    [LinearOrder ι] [Nonempty ι], #ι ≤ μ →
    ∀ (M : ι → P.scheme.Object μ hμ)
      (m : ∀ {i j : ι}, i ≤ j →
        SystemArrow K oneVertexShape (P.scheme.asSystem hμ (M i)) (P.scheme.asSystem hμ (M j))),
      (∀ {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (v : oneVertexShape.Vertex),
        ((m hjk).onVertex v).comp ((m hij).onVertex v) = (m (hij.trans hjk)).onVertex v) →
      ∀ (g : ∀ i, SystemArrow K oneVertexShape (P.scheme.asSystem hμ (M i))
          (P.scheme.asSystem hμ N)),
        (∀ {i j : ι} (hij : i ≤ j) (v : oneVertexShape.Vertex),
          ((g j).onVertex v).comp ((m hij).onVertex v) = (g i).onVertex v) →
        ∃ (U : P.scheme.Object μ hμ)
          (u : ∀ i, SystemArrow K oneVertexShape (P.scheme.asSystem hμ (M i))
            (P.scheme.asSystem hμ U))
          (h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ U) (P.scheme.asSystem hμ N)),
          (∀ {i j : ι} (hij : i ≤ j) (v : oneVertexShape.Vertex),
            ((u j).onVertex v).comp ((m hij).onVertex v) = (u i).onVertex v) ∧
          (∀ v (x : ((P.scheme.asSystem hμ U).obj v).carrier), ∃ i y, (u i).onVertex v y = x) ∧
          ∀ i (v : oneVertexShape.Vertex), (h.onVertex v).comp ((u i).onVertex v) = (g i).onVertex v

/-- **7.12(1) recursion (statement; open tip `infra_712_recursion`).** The pre-chain by
well-founded recursion along `WithTop L.δ` (the `WellFounded.fix` pattern of `ChainEngine`),
every stage carrying a map into the ambient `L.host` that sends the marks to the list's entries:
successors by `infra_712_succ` (proved), limits by the limit step. -/
def infra_712_recursion_statement (P : SingleModelData K) : Prop :=
  infra_712_limit_statement P → infra_712_prechain_statement P

/-- **The pre-chain from recursion and the limit step (proved glue).** -/
theorem infra_712_prechain_of_parts (P : SingleModelData K) (hr : infra_712_recursion_statement P)
    (hl : infra_712_limit_statement P) : infra_712_prechain_statement P := hr hl

/-- **7.12(1), freeness of the marks (statement; open tip `infra_712_free_marks`).** At a Lemma
7.11 level, in an all-dominated-increment pre-chain of a product-independent list, every actual
`bᵢ` is free over `Mᵢ` from `A` (paper: Lemma 7.11 applied to the chain below `i`, whose
products with the earlier marks are the original ones). -/
def infra_712_free_marks_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ], ProductIndependentTied L →
      ∀ C : TiedListPreChain L, C.AllDominatedIncrement → ∀ i, C.FreeAt i

/-- **7.12(1), products below `i` (statement; open tip `infra_712_products`).** In an
all-dominated pre-chain of a product-independent list whose marks below `i` are free, `bᵢ` (over
`Mᵢ`, the top of the truncated chain) has tied products over `A` with every finite selection of
earlier marks — the hypothesis of Lemma 7.11 for the truncated chain. Paper: these products are
read off product independence of `L` (the finite sublists `bᵢ` + selection). -/
def infra_712_products_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ], ProductIndependentTied L →
      ∀ C : TiedListPreChain L, C.AllDominatedIncrement →
        ∀ (i : L.δ) (hfree : ∀ k, k < i → C.FreeAt k) (n : ℕ) (ix : Fin n → (L.below i).δ),
          Function.Injective ix →
          IsProductTied
            ((C.markTuple i).restrict ((C.truncate i hfree).into ⊤)
              ((C.truncate i hfree).into_arrow ⊤))
            ((C.truncate i hfree).selectionOver (C.markTuple i) n ix)
            ((C.truncate i hfree).jointWith (C.markTuple i) n ix) (Equiv.refl _)

/-- **7.12(1), one freeness step (statement; open tip `infra_712_free_step`).** If the marks
below `i` are free, so is `bᵢ` (paper: Lemma 7.11 for the chain truncated at `i`, with
`x = bᵢ` over `Mᵢ`; its product hypotheses come from product independence of `L`). -/
def infra_712_free_step_statement (P : SingleModelData K) : Prop :=
  ∀ {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible), μ ∈ recursionClosedLevels P ℵ₀ →
    Order.succ ℵ₀ ≤ μ →
    μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀) → Order.succ (infra_75_wide P ℵ₀) ≤ μ →
    ∀ (A : P.scheme.Object μ hμ) (L : TupleList P.scheme hμ A) [LinearOrder L.δ]
      [WellFoundedLT L.δ], ProductIndependentTied L →
      ∀ C : TiedListPreChain L, C.AllDominatedIncrement →
        ∀ i, (∀ k, k < i → C.FreeAt k) → C.FreeAt i

/-- **One freeness step from the products (proved glue, cycle 85).** Lemma 7.11 at the level
(`infra_711_at_level`) for the truncated chain `C.truncate i` and `x = bᵢ`. -/
theorem infra_712_free_step_of_products (P : SingleModelData K)
    (h : infra_712_products_statement P) : infra_712_free_step_statement P := by
  intro μ hμ h0 h1 hw1 hw2 A L _ _ hind C hC i hfree
  exact infra_711_at_level P (infra_711_successor P) hμ h0 h1 hw1 hw2 A (L.below i)
    (C.truncate i hfree) (C.truncate_allDominated hC i hfree) (C.markTuple i) (L.finite_each i) rfl
    (h hμ h0 h1 hw1 hw2 A L hind C hC i hfree)

/-- **Freeness of all marks by well-founded induction (proved glue).** -/
theorem infra_712_free_marks_of_step (P : SingleModelData K)
    (h : infra_712_free_step_statement P) : infra_712_free_marks_statement P := by
  intro μ hμ h0 h1 hw1 hw2 A L _ _ hind C hC i
  induction i using WellFoundedLT.induction with
  | _ i ih => exact h hμ h0 h1 hw1 hw2 A L hind C hC i ih

/-- **Lemma 7.12 (1) from its parts (proved glue).** -/
theorem infra_712_existence_at_of_parts (P : SingleModelData K)
    (h1 : infra_712_prechain_statement P) (h2 : infra_712_free_marks_statement P)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible) (ht : μ ∈ infra_78_closedTail P)
    (hc : μ ∈ infra_615_closed P) (h0 : μ ∈ recursionClosedLevels P ℵ₀)
    (h1' : Order.succ ℵ₀ ≤ μ) (hw1 : μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀))
    (hw2 : Order.succ (infra_75_wide P ℵ₀) ≤ μ) (A : P.scheme.Object μ hμ) :
    infra_712_existence_at P hμ A := by
  intro L _ _ hδ hind
  obtain ⟨C, hC⟩ := h1 hμ ht hc A L hδ
  have hfree := h2 hμ h0 h1' hw1 hw2 A L hind C hC
  exact ⟨C.toChain hfree, C.toChain_allDominated hfree hC⟩

end
end AEC
