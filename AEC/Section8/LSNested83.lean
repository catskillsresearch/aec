module

public import AEC.Section8.LSExpansion83

/-!
# Lemma 8.3: LS witness expansions respecting a strong chain `X ≤ Y ≤ L`

The sample pairs of Lemma 8.3 consist of `L ∈ K` with strong submodels `X ⊆ Y`.  We choose the
LS hulls so that the hull of a finite subset of `X` (resp. `Y`) is computed inside `X` (resp.
`Y`).  Then, in the witness expansion of `L`, the universes of `X` and `Y` are closed under all
functions of the expanded language, while every nonempty closed subset of `L` is still strong.
-/

@[expose] public section

namespace AEC
namespace LS83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {K : AbstractElementaryClass.{u}} {M : Model K.τ}

/-- A hull chooser respects `R` if hulls of subsets of `R` stay inside `R`. -/
def Respects (ch : ∀ A : Set M.carrier, ChosenHull K M A) (R : Set M.carrier) : Prop :=
  ∀ A ⊆ R, Set.range (ch A).incl ⊆ R

theorem subHull_range_sub {α : Type u} [DecidableEq α] (ch : ∀ A : Set M.carrier, ChosenHull K M A)
    (base : α → M.carrier) {R : Set M.carrier} (hR : Respects ch R) :
    ∀ s : {t : Finset α // t.Nonempty}, displayed base s ⊆ R →
      Set.range (subIncl ch base s) ⊆ R := by
  intro s
  refine WellFounded.induction (C := fun s => displayed base s ⊆ R →
      Set.range (subIncl ch base s) ⊆ R) cardRel_wf s ?_
  intro s ih hs
  have hA : (subHull ch base s).1 ⊆ R := by
    rw [subHull_eq ch base s]
    rintro a (ha | ha)
    · exact hs ha
    · obtain ⟨t, ht⟩ := Set.mem_iUnion.mp ha
      have htm := mem_properSubs.mp t.down.2
      refine ih ⟨t.down.1, htm.2.1⟩ htm.2.2 ?_ ht
      rintro _ ⟨b, hb, rfl⟩
      exact hs ⟨b, htm.1 hb, rfl⟩
  have key : ∀ p : Σ A : Set M.carrier, ChosenHull K M A,
      p = subHullStep ch base s (fun t _ => subHull ch base t) →
        p.1 ⊆ R → Set.range p.2.incl ⊆ R := by
    rintro p rfl h
    exact hR _ h
  exact key _ (subHull_eq ch base s) hA

/-- A hull of a subset of a strong submodel `j : N → M`, computed in `N`. -/
noncomputable def pullHull {N : Model K.τ} (hN : K.Mem N) (j : N.carrier ↪[K.τ] M.carrier)
    (hj : K.Strong j) (A : Set M.carrier) (hA : A ⊆ Set.range j) : ChosenHull K M A where
  obj := (chosenHull hN (j ⁻¹' A)).obj
  incl := j.comp (chosenHull hN (j ⁻¹' A)).incl
  mem := (chosenHull hN (j ⁻¹' A)).mem
  strong := K.strong_trans _ _ (chosenHull hN (j ⁻¹' A)).strong hj
  covers a ha := by
    obtain ⟨b, rfl⟩ := hA ha
    obtain ⟨n, hn⟩ := (chosenHull hN (j ⁻¹' A)).covers b ha
    exact ⟨n, by simp [hn]⟩
  card_le := (chosenHull hN (j ⁻¹' A)).card_le.trans
    (add_le_add (mk_preimage_of_injective _ _ j.injective) le_rfl)

theorem pullHull_range {N : Model K.τ} (hN : K.Mem N) (j : N.carrier ↪[K.τ] M.carrier)
    (hj : K.Strong j) (A : Set M.carrier) (hA : A ⊆ Set.range j) :
    Set.range (pullHull hN j hj A hA).incl ⊆ Set.range j := by
  rintro _ ⟨n, rfl⟩
  exact ⟨(chosenHull hN (j ⁻¹' A)).incl n, rfl⟩

section Chain

variable (hM : K.Mem M) {X Y : Model K.τ} (hX : K.Mem X) (hY : K.Mem Y)
  (jX : X.carrier ↪[K.τ] M.carrier) (jY : Y.carrier ↪[K.τ] M.carrier)
  (sX : K.Strong jX) (sY : K.Strong jY)

open Classical in
/-- The hull chooser for a strong chain `X ⊆ Y ⊆ M`: compute in `X` if possible, else in `Y`
if possible, else in `M`. -/
noncomputable def chainCh (A : Set M.carrier) : ChosenHull K M A :=
  if hx : A ⊆ Set.range jX then pullHull hX jX sX A hx
  else if hy : A ⊆ Set.range jY then pullHull hY jY sY A hy
  else chosenHull hM A

theorem chainCh_respects_X : Respects (chainCh hM hX hY jX jY sX sY) (Set.range jX) := by
  intro A hA
  rw [chainCh, dif_pos hA]
  exact pullHull_range hX jX sX A hA

theorem chainCh_respects_Y (hXY : Set.range jX ⊆ Set.range jY) :
    Respects (chainCh hM hX hY jX jY sX sY) (Set.range jY) := by
  intro A hA
  by_cases hx : A ⊆ Set.range jX
  · rw [chainCh, dif_pos hx]
    exact (pullHull_range hX jX sX A hx).trans hXY
  · rw [chainCh, dif_neg hx, dif_pos hA]
    exact pullHull_range hY jY sY A hA

end Chain

/-- A set respected by the chooser is closed under the witness functions. -/
theorem witFun_mem [DecidableEq M.carrier] (ch : ∀ A : Set M.carrier, ChosenHull K M A)
    {R : Set M.carrier} (hR : Respects ch R) {n : ℕ} (η : Enum K)
    (x : Fin (n + 1) → M.carrier) (hx : ∀ i, x i ∈ R) : witFun ch η x ∈ R := by
  refine subHull_range_sub ch id hR (entries x) ?_ ⟨_, rfl⟩
  rintro _ ⟨b, hb, rfl⟩
  simp only [entries, Finset.coe_image, Finset.coe_univ, Set.image_univ] at hb
  obtain ⟨i, rfl⟩ := hb
  exact hx i

/-- The witness expansion for an arbitrary hull chooser. -/
@[instance_reducible]
noncomputable def lsStrCh [DecidableEq M.carrier] (ch : ∀ A : Set M.carrier, ChosenHull K M A) :
    (lsLang K).Structure M.carrier :=
  @Language.sumStructure _ _ _ M.str (witStr ch)

/-- Every nonempty closed subset is strong, for any chooser. -/
theorem lsClosed_lsStrCh [DecidableEq M.carrier] (ch : ∀ A : Set M.carrier, ChosenHull K M A) :
    @LSClosed K M.carrier (lsStrCh ch) := by
  refine ⟨mem_of_ch ch, fun A hA => ?_⟩
  let _ := lsStrCh ch
  have : Nonempty (Hull83.red (lsInl K) A).carrier := hA.to_subtype
  refine strong_of_witness_closed ch (A := Hull83.red (lsInl K) A)
    (Hull83.redEmb (lsInl K) A.subtype) fun n η x => ?_
  exact ⟨⟨_, A.fun_mem (Sum.inr η : (lsLang K).Functions (n + 1)) (fun i => (x i).1)
    (fun i => (x i).2)⟩, rfl⟩

/-- A respected set that is the range of an embedding is closed under all expanded functions. -/
theorem range_closed [DecidableEq M.carrier] (ch : ∀ A : Set M.carrier, ChosenHull K M A)
    {N : Model K.τ} (j : N.carrier ↪[K.τ] M.carrier) (hR : Respects ch (Set.range j))
    {n : ℕ} (f : (lsLang K).Functions n) (x : Fin n → M.carrier)
    (hx : ∀ i, x i ∈ Set.range j) :
    @Structure.funMap _ M.carrier (lsStrCh ch) n f x ∈ Set.range j := by
  rcases f with f | f
  · choose y hy using hx
    refine ⟨Structure.funMap f y, ?_⟩
    rw [j.map_fun]
    have : (j ∘ y) = x := funext hy
    rw [this]
    rfl
  · cases n with
    | zero => exact PEmpty.elim f
    | succ n => exact witFun_mem ch hR f x hx

/-- **Lemma 8.3 (LS witness expansion respecting a strong chain).**  For `M ∈ K` and strong
submodels `X ⊆ Y` of `M`, there is an expansion of `M` by `LS(K)`-many functions of each
positive arity whose `τ(K)`-reduct is `M`, in which every nonempty substructure has strong
reduct, and in which the universes of `X` and of `Y` are closed under all functions. -/
theorem exists_chain_ls_expansion (hM : K.Mem M) {X Y : Model K.τ} (hX : K.Mem X) (hY : K.Mem Y)
    (jX : X.carrier ↪[K.τ] M.carrier) (jY : Y.carrier ↪[K.τ] M.carrier)
    (sX : K.Strong jX) (sY : K.Strong jY) (hXY : Set.range jX ⊆ Set.range jY) :
    ∃ str : (lsLang K).Structure M.carrier,
      @LHom.reduct _ _ (lsInl K) M.carrier str = M.str ∧ @LSClosed K M.carrier str ∧
      (∀ {n} (f : (lsLang K).Functions n) (x : Fin n → M.carrier),
        (∀ i, x i ∈ Set.range jX) → @Structure.funMap _ M.carrier str n f x ∈ Set.range jX) ∧
      (∀ {n} (f : (lsLang K).Functions n) (x : Fin n → M.carrier),
        (∀ i, x i ∈ Set.range jY) → @Structure.funMap _ M.carrier str n f x ∈ Set.range jY) := by
  classical
  let ch := chainCh hM hX hY jX jY sX sY
  exact ⟨lsStrCh ch, rfl, lsClosed_lsStrCh ch,
    fun f x hx => range_closed ch jX (chainCh_respects_X hM hX hY jX jY sX sY) f x hx,
    fun f x hx => range_closed ch jY (chainCh_respects_Y hM hX hY jX jY sX sY hXY) f x hx⟩

end LS83
end AEC
