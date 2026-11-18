module

public import AEC.Section7.Lemma712Existence
public import AEC.Section7.ChainEngine
public import AEC.Section2.FiniteHull

/-!
# Lemma 7.12 (1): the pre-chain recursion (`infra_712_recursion`, cycle 86)

Stages are strong subsets of the ambient `N = L.host`: a `StrongSub N` is a level-`μ` object
together with a strong embedding into `N` (the subset is its range), so the "subset gives an
object at the level" step is built into the representation and uses only the existing scheme
(objects are coded models; `factorEmbedding` plus the coherence axiom of `K` give the strong
inclusion between nested strong subsets). The transfinite recursion is the non-dependent
`WellFounded.fix` engine of `ChainEngine` (stages `StrongSub N`, maps `Unit`, arrow relation
`⊆`); successors by `infra_712_succ` (Theorem 7.9 at the level, embedded into `N` over the stage
with `bᵢ` sent to the list's entry), limits by `infra_712_limit` (directed union with its map into
`N`, whose image is the union of the images). The scheme arrows of the pre-chain are the
factorizations; marks are the preimages of the list's entries; top is `L.host` with
`listToTop = id`.
-/

@[expose] public section

namespace AEC
noncomputable section
open FirstOrder Cardinal
variable {K : AbstractElementaryClass.{u}}

set_option linter.unusedSectionVars false

namespace Infra712Rec
variable {P : SingleModelData K} {μ : Cardinal.{u}} {hμ : μ ∈ P.eligible}

/-- A strong subset of the ambient `N`, presented by a level-`μ` coding object and a strong
embedding onto it (the subset is the range). -/
def StrongSub (N : P.scheme.Object μ hμ) : Type u :=
  {p : Σ X : P.scheme.Object μ hμ, Language.Embedding K.τ X.model.carrier N.model.carrier //
    K.Strong p.2}

variable {N : P.scheme.Object μ hμ}

/-- The subset. -/
def StrongSub.set (s : StrongSub N) : Set N.model.carrier := Set.range s.1.2

/-- The embedding as a scheme arrow. -/
def StrongSub.arr (s : StrongSub N) :
    SystemArrow K oneVertexShape (P.scheme.asSystem hμ s.1.1) (P.scheme.asSystem hμ N) :=
  oneVertexArrow (hM := s.1.1.mem) (hN := N.mem) s.1.2 s.2

/-- The inclusion between two strong subsets (factor through the larger one; strong by
coherence). -/
def StrongSub.incl (s t : StrongSub N) (h : s.set ⊆ t.set) :
    SystemArrow K oneVertexShape (P.scheme.asSystem hμ s.1.1) (P.scheme.asSystem hμ t.1.1) :=
  oneVertexArrow (hM := s.1.1.mem) (hN := t.1.1.mem)
    (factorEmbedding s.1.2 t.1.2 (fun a => h ⟨a, rfl⟩))
    (K.coherence _ s.1.2 t.1.2 s.2 t.2 (factorEmbedding_comp _ _ _))

theorem StrongSub.incl_spec (s t : StrongSub N) (h : s.set ⊆ t.set) (x) :
    t.1.2 ((s.incl t h).onVertex PUnit.unit x) = s.1.2 x :=
  DFunLike.congr_fun (factorEmbedding_comp s.1.2 t.1.2 (fun a => h ⟨a, rfl⟩)) x

/-- Uniqueness of maps over `N`. -/
theorem StrongSub.arrow_eq {X : P.scheme.Object μ hμ} (t : StrongSub N)
    (f g : SystemArrow K oneVertexShape (P.scheme.asSystem hμ X) (P.scheme.asSystem hμ t.1.1))
    (h : ∀ x, t.1.2 (f.onVertex PUnit.unit x) = t.1.2 (g.onVertex PUnit.unit x)) : f = g := by
  apply SystemArrow.ext
  intro v
  cases v
  ext x
  exact t.1.2.injective (h x)


section Ops
variable (ht : μ ∈ infra_78_closedTail P) (hc : μ ∈ infra_615_closed P)
  {A : P.scheme.Object μ hμ} (L : TupleList P.scheme hμ A) [L.FiniteEach]

/-- The output of one successor step (`infra_712_succ`). -/
structure SuccOut (s : StrongSub L.host) (i : L.δ) where
  Y : P.scheme.Object μ hμ
  f : SystemArrow K oneVertexShape (P.scheme.asSystem hμ s.1.1) (P.scheme.asSystem hμ Y)
  b : L.indexAt i → Occurrence K oneVertexShape (P.scheme.asSystem hμ Y)
  h : SystemArrow K oneVertexShape (P.scheme.asSystem hμ Y) (P.scheme.asSystem hμ L.host)
  dom : AllDominated f trivial (L.indexAt i) b
  comp : SystemArrow.comp f h = s.arr
  val : ∀ k, h.onVertex (b k).1 (b k).2 = (L.val i k).2

include ht hc in
theorem succOut_nonempty (s : StrongSub L.host) (i : L.δ) : Nonempty (SuccOut L s i) := by
  have := L.finite_each i
  obtain ⟨Y, f, hf, b, h, hAll, -, hcomp, hv⟩ :=
    infra_712_succ P hμ ht hc s.1.1 L.host s.arr trivial (L.indexAt i) (L.val i)
  exact ⟨⟨Y, f, b, h, hAll, hcomp, hv⟩⟩

/-- The chosen successor output. -/
def succOut (s : StrongSub L.host) (i : L.δ) : SuccOut L s i :=
  Classical.choice (succOut_nonempty ht hc L s i)

/-- The successor stage: the image of the realization in the ambient. -/
def succStage (s : StrongSub L.host) (i : L.δ) : StrongSub L.host :=
  ⟨⟨(succOut ht hc L s i).Y, (succOut ht hc L s i).h.onVertex PUnit.unit⟩,
    (succOut ht hc L s i).h.onVertex_strong _⟩

/-- The output of one limit step. -/
structure LimOut {ι : Type u} (cf : ι → StrongSub L.host) where
  U : P.scheme.Object μ hμ
  h : Language.Embedding K.τ U.model.carrier L.host.model.carrier
  strong : K.Strong h
  range : ∀ y, (∃ x, h x = y) ↔ ∃ j, y ∈ (cf j).set

theorem limOut_nonempty (hδ : #L.δ ≤ μ) [LinearOrder L.δ] [L.FiniteEach] (k : WithTop L.δ)
    (cf : Set.Iio k → StrongSub L.host) (hne : ∃ j, j < k)
    (hmono : ∀ i j : Set.Iio k, i ≤ j → (cf i).set ⊆ (cf j).set) : Nonempty (LimOut L cf) := by
  obtain ⟨j0, hj0⟩ := hne
  have : Nonempty (Set.Iio k) := ⟨⟨j0, hj0⟩⟩
  have hι : #(Set.Iio k) ≤ μ := by
    refine (Cardinal.mk_le_of_injective Subtype.val_injective).trans ?_
    show #(Option L.δ) ≤ μ
    rw [Cardinal.mk_option]
    exact Cardinal.add_le_of_le (P.aleph0_le hμ) hδ (Cardinal.one_le_aleph0.trans (P.aleph0_le hμ))
  obtain ⟨U, u, h, hu, hcov, hh⟩ := infra_712_limit P hμ L.host (Set.Iio k) hι
    (fun j => (cf j).1.1) (fun {i j} hij => (cf i).incl (cf j) (hmono i j hij))
    (fun {i j l} hij hjl v => by
      cases v
      ext x
      apply (cf l).1.2.injective
      show (cf l).1.2 (((cf j).incl (cf l) (hmono j l hjl)).onVertex PUnit.unit
        (((cf i).incl (cf j) (hmono i j hij)).onVertex PUnit.unit x)) =
        (cf l).1.2 (((cf i).incl (cf l) (hmono i l (hij.trans hjl))).onVertex PUnit.unit x)
      rw [StrongSub.incl_spec, StrongSub.incl_spec, StrongSub.incl_spec])
    (fun j => (cf j).arr)
    (fun {i j} hij v => by
      cases v
      ext x
      exact StrongSub.incl_spec (cf i) (cf j) _ x)
  refine ⟨⟨U, h.onVertex PUnit.unit, h.onVertex_strong _, fun y => ⟨?_, ?_⟩⟩⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨j, z, rfl⟩ := hcov PUnit.unit x
    refine ⟨j, z, ?_⟩
    exact (DFunLike.congr_fun (hh j PUnit.unit) z).symm
  · rintro ⟨j, z, rfl⟩
    exact ⟨(u j).onVertex PUnit.unit z, DFunLike.congr_fun (hh j PUnit.unit) z⟩

end Ops

section Chain
variable (ht : μ ∈ infra_78_closedTail P) (hc : μ ∈ infra_615_closed P)
  {A : P.scheme.Object μ hμ} (L : TupleList P.scheme hμ A) [LinearOrder L.δ] [L.FiniteEach] [WellFoundedLT L.δ]
  (hδ : #L.δ ≤ μ)

/-- The first stage: the image of `A`. -/
def s0 : StrongSub L.host := ⟨⟨A, L.incl.onVertex PUnit.unit⟩, L.incl.onVertex_strong _⟩

include hδ in
open Classical in
/-- The limit stage: the union of the earlier ones (when they form a chain). -/
def limStage (k : WithTop L.δ) (cf : Set.Iio k → StrongSub L.host) : StrongSub L.host :=
  if h : (∃ j, j < k) ∧ ∀ i j : Set.Iio k, i ≤ j → (cf i).set ⊆ (cf j).set then
    ⟨⟨(Classical.choice (limOut_nonempty L hδ k cf h.1 h.2)).U,
      (Classical.choice (limOut_nonempty L hδ k cf h.1 h.2)).h⟩,
      (Classical.choice (limOut_nonempty L hδ k cf h.1 h.2)).strong⟩
  else s0 L

/-- Successor operator of the engine. -/
def sop (β : WithTop L.δ) (s : StrongSub L.host) : StrongSub L.host × Unit :=
  (if hβ : β = ⊤ then s else succStage ht hc L s (β.untop hβ), ())

include hδ in
/-- Limit operator of the engine. -/
def lop (k : WithTop L.δ) (cf : Set.Iio k → StrongSub L.host)
    (_ : Set.Iio k → Set.Iio k → Unit) : StrongSub L.host × (Set.Iio k → Unit) :=
  (limStage L hδ k cf, fun _ => ())

include hδ in
/-- The stages (`WellFounded.fix` via the chain engine). -/
def stage (k : WithTop L.δ) : StrongSub L.host :=
  infra_78_engineObj (s0 L) () (fun _ _ => ()) (sop ht hc L) (lop L hδ) k

theorem sop_mono (β : WithTop L.δ) (s : StrongSub L.host) : s.set ⊆ (sop ht hc L β s).1.set := by
  unfold sop
  by_cases hβ : β = ⊤
  · simp only [hβ, ↓reduceDIte]; exact subset_rfl
  · simp only [hβ, ↓reduceDIte]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit)
      (succOut ht hc L s (β.untop hβ)).comp) x⟩

include hδ in
theorem limStage_spec (k : WithTop L.δ) (cf : Set.Iio k → StrongSub L.host) (hne : ∃ j, j < k)
    (hmono : ∀ i j : Set.Iio k, i ≤ j → (cf i).set ⊆ (cf j).set) (y) :
    y ∈ (limStage L hδ k cf).set ↔ ∃ j, y ∈ (cf j).set := by
  have he : limStage L hδ k cf =
      ⟨⟨(Classical.choice (limOut_nonempty L hδ k cf hne hmono)).U,
        (Classical.choice (limOut_nonempty L hδ k cf hne hmono)).h⟩,
        (Classical.choice (limOut_nonempty L hδ k cf hne hmono)).strong⟩ :=
    dif_pos (⟨hne, hmono⟩ : (∃ j, j < k) ∧ ∀ i j : Set.Iio k, i ≤ j → (cf i).set ⊆ (cf j).set)
  rw [he]
  exact (Classical.choice (limOut_nonempty L hδ k cf hne hmono)).range y

theorem stage_mono {i k : WithTop L.δ} (h : i ≤ k) :
    (stage ht hc L hδ i).set ⊆ (stage ht hc L hδ k).set :=
  (infra_78_coherent_chain_engine (s0 L) () (fun _ _ => ()) (sop ht hc L) (lop L hδ)
    (fun s t _ => s.set ⊆ t.set) (fun _ => subset_rfl) (fun h1 h2 => h1.trans h2)
    (fun _ => rfl) (fun _ _ _ => rfl) (fun β s => sop_mono ht hc L β s)
    (fun k hk _ cf mf hmono _ _ => by
      have hne : ∃ j, j < k := not_isMin_iff.1 hk
      exact ⟨fun j y hy => (limStage_spec L hδ k cf hne
        (fun i j hij => hmono i j hij) y).2 ⟨j, hy⟩, fun _ _ _ => rfl⟩)).1 i k h

end Chain

theorem StrongSub.incl_comp (s t r : StrongSub N) (h1 : s.set ⊆ t.set) (h2 : t.set ⊆ r.set)
    (h3 : s.set ⊆ r.set) (v : oneVertexShape.Vertex) :
    ((t.incl r h2).onVertex v).comp ((s.incl t h1).onVertex v) = (s.incl r h3).onVertex v := by
  cases v
  ext x
  apply r.1.2.injective
  show r.1.2 ((t.incl r h2).onVertex PUnit.unit ((s.incl t h1).onVertex PUnit.unit x)) =
    r.1.2 ((s.incl r h3).onVertex PUnit.unit x)
  rw [StrongSub.incl_spec, StrongSub.incl_spec, StrongSub.incl_spec]

theorem StrongSub.incl_bijective (s t : StrongSub N) (h1 : s.set ⊆ t.set) (h2 : t.set ⊆ s.set)
    (v : oneVertexShape.Vertex) : Function.Bijective ((s.incl t h1).onVertex v) := by
  cases v
  refine ⟨((s.incl t h1).onVertex PUnit.unit).injective, fun y => ?_⟩
  obtain ⟨x, hx⟩ := h2 ⟨y, rfl⟩
  refine ⟨x, t.1.2.injective ?_⟩
  exact (StrongSub.incl_spec s t h1 x).trans hx

section Build
variable (ht : μ ∈ infra_78_closedTail P) (hc : μ ∈ infra_615_closed P)
  {A : P.scheme.Object μ hμ} (L : TupleList P.scheme hμ A) [LinearOrder L.δ] [L.FiniteEach] [WellFoundedLT L.δ]
  (hδ : #L.δ ≤ μ)

theorem stage_succ {β k : WithTop L.δ} (h : β ⋖ k) :
    stage ht hc L hδ k = (sop ht hc L β (stage ht hc L hδ β)).1 :=
  (infra_78_engine_succ_eq (s0 L) () (fun _ _ => ()) (sop ht hc L) (lop L hδ) h).1

theorem stage_min {k : WithTop L.δ} (h : IsMin k) : stage ht hc L hδ k = s0 L :=
  (infra_78_engine_min_eq (s0 L) () (fun _ _ => ()) (sop ht hc L) (lop L hδ) h).1

theorem stage_lim {k : WithTop L.δ} (hk : ¬ IsMin k) (hs : ¬ ∃ β, β ⋖ k) :
    stage ht hc L hδ k = limStage L hδ k (fun j => stage ht hc L hδ j.1) :=
  (infra_78_engine_lim_eq (s0 L) () (fun _ _ => ()) (sop ht hc L) (lop L hδ) hk hs).1

theorem sop_coe (i : L.δ) (s : StrongSub L.host) :
    (sop ht hc L (i : WithTop L.δ) s).1 = succStage ht hc L s i := by
  unfold sop
  simp only [WithTop.coe_ne_top, ↓reduceDIte, WithTop.untop_coe]

theorem exists_cover {x j : WithTop L.δ} (h : x < j) : ∃ k, x ⋖ k ∧ k ≤ j := by
  have hwf := (wellFounded_lt (α := WithTop L.δ))
  let k := hwf.min {y | x < y} ⟨j, h⟩
  refine ⟨k, ⟨hwf.min_mem {y | x < y} ⟨j, h⟩, fun c hc hck => ?_⟩, ?_⟩
  · exact hwf.not_lt_min {y | x < y} hc hck
  · exact not_lt.1 (hwf.not_lt_min {y | x < y} h)

theorem s0_sub (k : WithTop L.δ) : (s0 L).set ⊆ (stage ht hc L hδ k).set := by
  have hwf := (wellFounded_lt (α := WithTop L.δ))
  let m := hwf.min Set.univ ⟨k, trivial⟩
  have hm : IsMin m := fun c _ => not_lt.1 (hwf.not_lt_min Set.univ (Set.mem_univ c))
  have hmk : m ≤ k := not_lt.1 (hwf.not_lt_min Set.univ (Set.mem_univ k))
  have := stage_mono ht hc L hδ hmk
  rwa [stage_min ht hc L hδ hm] at this

theorem val_mem (i : L.δ) (j : WithTop L.δ) (h : (i : WithTop L.δ) < j) (a : L.indexAt i) :
    (L.val i a).2 ∈ (stage ht hc L hδ j).set := by
  obtain ⟨k, hk, hkj⟩ := exists_cover L h
  refine stage_mono ht hc L hδ hkj ?_
  rw [stage_succ ht hc L hδ hk, sop_coe]
  exact ⟨_, (succOut ht hc L _ i).val a⟩

theorem succ_dom (s t : StrongSub L.host) (i : L.δ) (hts : t = succStage ht hc L s i)
    (hsub : s.set ⊆ t.set) (hmem : ∀ a, (L.val i a).2 ∈ t.set) :
    AllDominated (s.incl t hsub) trivial (L.indexAt i)
      (fun a => ⟨PUnit.unit, Classical.choose (hmem a)⟩) := by
  subst hts
  have hf : s.incl (succStage ht hc L s i) hsub = (succOut ht hc L s i).f := by
    apply StrongSub.arrow_eq
    intro x
    rw [StrongSub.incl_spec]
    exact (DFunLike.congr_fun (congrArg (fun e => e.onVertex PUnit.unit)
      (succOut ht hc L s i).comp) x).symm
  have hb : (fun a => (⟨PUnit.unit, Classical.choose (hmem a)⟩ :
      Occurrence K oneVertexShape (P.scheme.asSystem hμ (succStage ht hc L s i).1.1))) =
      (succOut ht hc L s i).b := by
    funext a
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply ((succOut ht hc L s i).h.onVertex PUnit.unit).injective
    exact (Classical.choose_spec (hmem a)).trans ((succOut ht hc L s i).val a).symm
  rw [hb]
  exact hf ▸ (succOut ht hc L s i).dom

end Build

section Assemble
variable (ht : μ ∈ infra_78_closedTail P) (hc : μ ∈ infra_615_closed P)
  {A : P.scheme.Object μ hμ} (L : TupleList P.scheme hμ A) [LinearOrder L.δ] [L.FiniteEach] [WellFoundedLT L.δ]
  (hδ : #L.δ ≤ μ)

/-- The pre-chain of Lemma 7.12(1), built inside `L.host`. -/
def preChain : TiedListPreChain L where
  stage j := (stage ht hc L hδ j).1.1
  into j := (s0 L).incl (stage ht hc L hδ j) (s0_sub ht hc L hδ j)
  into_arrow _ := trivial
  step h := (stage ht hc L hδ _).incl (stage ht hc L hδ _) (stage_mono ht hc L hδ h)
  step_arrow _ := trivial
  step_comp hij hjk v := StrongSub.incl_comp _ _ _ _ _ _ v
  into_step h v := StrongSub.incl_comp _ _ _ _ _ _ v
  first i hi v := by
    have hm : IsMin i := fun c _ => hi c
    exact StrongSub.incl_bijective _ _ _
      (by rw [stage_min ht hc L hδ hm]) v
  continuous j hno hex v x := by
    cases v
    have hk : ¬ IsMin j := not_isMin_iff.2 hex
    have hs : ¬ ∃ β, β ⋖ j := fun ⟨β, hβ⟩ => hno β hβ
    have hx : (stage ht hc L hδ j).1.2 x ∈ (limStage L hδ j (fun i => stage ht hc L hδ i.1)).set := by
      rw [← stage_lim ht hc L hδ hk hs]; exact ⟨x, rfl⟩
    obtain ⟨⟨i, hi⟩, y, hy⟩ := (limStage_spec L hδ j _ hex
      (fun a b hab => stage_mono ht hc L hδ hab) _).1 hx
    refine ⟨i, hi, y, (stage ht hc L hδ j).1.2.injective ?_⟩
    exact (StrongSub.incl_spec _ _ _ y).trans hy
  top := L.host
  toTop := (stage ht hc L hδ ⊤).arr
  toTop_arrow := trivial
  listToTop := SystemArrow.refl _
  listToTop_arrow := trivial
  comm_A v := by
    cases v
    ext x
    exact StrongSub.incl_spec (s0 L) (stage ht hc L hδ ⊤) _ x
  mark i j h a := ⟨PUnit.unit, Classical.choose (val_mem ht hc L hδ i j h a)⟩
  mark_step i j k hj hjk a := by
    refine Sigma.ext rfl (heq_of_eq ?_)
    apply (stage ht hc L hδ k).1.2.injective
    exact (StrongSub.incl_spec _ _ _ _).trans ((Classical.choose_spec
      (val_mem ht hc L hδ i j hj a)).trans
      (Classical.choose_spec (val_mem ht hc L hδ i k (lt_of_lt_of_le hj hjk) a)).symm)
  mark_spec i a := Sigma.ext rfl (heq_of_eq
    (Classical.choose_spec (val_mem ht hc L hδ i ⊤ (WithTop.coe_lt_top i) a)))

theorem preChain_allDominated : (preChain ht hc L hδ).AllDominatedIncrement := by
  intro i j h
  exact succ_dom ht hc L (stage ht hc L hδ i) (stage ht hc L hδ j) i
    ((stage_succ ht hc L hδ h).trans (sop_coe ht hc L i _)) (stage_mono ht hc L hδ h.le)
    (fun a => val_mem ht hc L hδ i j h.lt a)

end Assemble

end Infra712Rec

/-- **7.12(1) recursion (proved, cycle 86).** Stages are strong subsets of the ambient `L.host`
(each with its level-`μ` coding object and strong embedding), built by the `WellFounded.fix`
chain engine `infra_78_coherent_chain_engine` with trivial maps; the scheme arrows between
stages are the factorizations through the embeddings (`factorEmbedding`, strong by coherence).
Successors by `infra_712_succ`, limits by `infra_712_limit`. -/
theorem infra_712_recursion (P : SingleModelData K) : infra_712_recursion_statement P :=
  fun _ _ _ ht hc _ L _ _ _ hδ =>
    ⟨Infra712Rec.preChain ht hc L hδ, Infra712Rec.preChain_allDominated ht hc L hδ⟩

/-- **Lemma 7.12 (1) at a level from the products step (proved glue, cycle 86).** -/
theorem infra_712_existence_at_of_products (P : SingleModelData K)
    (hp : infra_712_products_statement P)
    {μ : Cardinal.{u}} (hμ : μ ∈ P.eligible) (ht : μ ∈ infra_78_closedTail P)
    (hc : μ ∈ infra_615_closed P) (h0 : μ ∈ recursionClosedLevels P ℵ₀)
    (h1 : Order.succ ℵ₀ ≤ μ) (hw1 : μ ∈ recursionClosedLevels P (infra_75_wide P ℵ₀))
    (hw2 : Order.succ (infra_75_wide P ℵ₀) ≤ μ) (A : P.scheme.Object μ hμ) :
    infra_712_existence_at P hμ A :=
  infra_712_existence_at_of_parts P (infra_712_prechain_of_recursion P (infra_712_recursion P))
    (infra_712_free_marks_of_step P (infra_712_free_step_of_products P hp)) hμ ht hc h0 h1 hw1 hw2 A

end
end AEC
