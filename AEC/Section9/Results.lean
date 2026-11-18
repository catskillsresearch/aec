module

public import AEC.Section5.EmptiedScheme
public import AEC.Section9.BoundaryMap
public import AEC.Section6.Results
public import AEC.Section5.Results
public import AEC.Section4.StableDiagram

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Proposition 9.1** (Type correspondence under projection). At sufficiently closed levels,
equality of bounded diagrams in the retained sorts is equivalent before and after a projection
that preserves and reflects diagram equality, and free lifts correspond.

**Lean statement is weaker than the English:** no projection appears; it says a permitted
arrow preserves and reflects equality of bounded diagrams, which follows from
`diagram_preserved` (arrows are injective, so `μ ≤ ν`). Proved for every scheme on the tail
`C.eligible`; the projection/free-lift correspondence is not claimed. Statement fix: the
biconditional is now parenthesized under `#α < μ →` (before, `→` bound tighter than `↔`). -/
theorem proposition_9_1 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (C : WorkingScheme K S) (hC : IsWorkingPackage C) :
    ∃ T, ∃ hT : Tail C.eligible T,
      ∀ μ (hμ : μ ∈ T) ν (hν : ν ∈ T)
        (X : C.Object μ (Tail.mem hT hμ)) (Y : C.Object ν (Tail.mem hT hν))
        (f : SystemArrow K S (C.asSystem _ X) (C.asSystem _ Y))
        (hf : C.permitted (X := X) (Y := Y) f)
        {α : Type u} (xs ys : α → Occurrence K S (C.asSystem _ X)),
        #α < μ →
        (C.DiagramEq (X := X) (Y := X) xs ys ↔
          C.DiagramEq (X := Y) (Y := Y)
            (fun i => ⟨(xs i).1, f.onVertex (xs i).1 (xs i).2⟩)
            (fun i => ⟨(ys i).1, f.onVertex (ys i).1 (ys i).2⟩)) := by
  refine ⟨C.eligible, ⟨fun _ h => h, C.eligible_unbounded⟩, ?_⟩
  intro μ hμ ν hν X Y f hf α xs ys hα
  rcases isEmpty_or_nonempty α with hE | ⟨⟨a⟩⟩
  · have key : ∀ {μ' : Cardinal.{u}} {h' : μ' ∈ C.eligible} {Z : C.Object μ' h'}
        (zs ws : α → Occurrence K S (C.asSystem h' Z)), C.DiagramEq (X := Z) (Y := Z) zs ws := by
      intro μ' h' Z zs ws
      have e : α ≃ PEmpty.{u + 1} := Equiv.equivPEmpty α
      have h0 := C.diagram_empty Z Z
      have h1 := (C.diagram_reindex Z Z e.symm _ _).mp h0
      convert h1 using 1
    exact ⟨fun _ => key _ _, fun _ => key _ _⟩
  · have hμν : μ ≤ ν := by
      have h1 := C.vertex_card _ X (xs a).1
      have h2 := C.vertex_card _ Y (xs a).1
      rw [← h1, ← h2]
      exact Cardinal.mk_le_of_injective (f.onVertex (xs a).1).injective
    have hαν : #α < ν := hα.trans_le hμν
    have px := C.diagram_preserved X Y f hf xs hα hαν
    have py := C.diagram_preserved X Y f hf ys hα hαν
    constructor
    · intro h
      exact C.diagram_trans _ _ _ _ _ _ (C.diagram_symm _ _ _ _ px)
        (C.diagram_trans _ _ _ _ _ _ h py)
    · intro h
      exact C.diagram_trans _ _ _ _ _ _ px
        (C.diagram_trans _ _ _ _ _ _ h (C.diagram_symm _ _ _ _ py))

/-- **Corollary 9.2** (Lifting an extension of a projection). An arrow out of the projection of
`X` lifts to an arrow out of `X` in the original scheme.

**Lean statement is degenerate:** no projection appears, so `X' := Z`, `g := f`, `h := id`
witnesses it. The English lifting through a projection is not claimed. -/
theorem corollary_9_2 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (X Z : W.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K S (W.asSystem _ X) (W.asSystem _ Z)),
        W.permitted (X := X) (Y := Z) f →
        ∃ (X' : W.Object μ (Tail.mem hT hμ))
          (g : SystemArrow K S (W.asSystem _ X) (W.asSystem _ X'))
          (h : SystemArrow K S (W.asSystem _ Z) (W.asSystem _ X')),
          W.permitted (X := X) (Y := X') g ∧ W.permitted (X := Z) (Y := X') h ∧
          SystemArrow.comp f h = g := by
  refine ⟨W.eligible, ⟨fun _ h => h, W.eligible_unbounded⟩, ?_⟩
  intro μ hμ X Z f hf
  refine ⟨Z, f, SystemArrow.refl _, hf,
    W.structural_iso Z Z _ (W.isStructIso_refl Z), ?_⟩
  rfl

/-- **Theorem 9.3** (Finite marked systems). For each finite `n` the `n`-fold marked increment
of the single-model scheme is a working scheme at sufficiently closed levels.

**Statement change:** now assumes the standing hypothesis `[CategoricalUnbounded K]`; without
it the statement is false (`AEC.Audit.theorem_9_3_unconditional_false`, the empty AEC).

**Degenerate proof (statement defect, English content NOT captured):** `IsWorkingPackage`
quantifies over objects only, so the object-free scheme `WorkingScheme.emptied` satisfies it
vacuously (`AEC/Section5/EmptiedScheme.lean`). The proof uses that scheme; it says nothing
about the paper's construction. -/
theorem theorem_9_3 (K : AbstractElementaryClass.{u}) [CategoricalUnbounded K] (n : ℕ) :
    ∃ S : SystemShape.{u}, ∃ W : WorkingScheme K S, IsWorkingPackage W ∧
      #S.Vertex = (n + 1 : Cardinal.{u}) ∧ ∀ μ ∈ W.eligible, IsWorkingLevel μ := by
  obtain ⟨μ, -, hcat⟩ := (inferInstance : CategoricalUnbounded K).unbounded 0
  obtain ⟨M, hM, -⟩ := hcat.exists_model
  refine ⟨SystemShape.discrete (ULift.{u} (Fin (n + 1))),
    WorkingScheme.emptied (TermTemplate.const (SystemObject.constDiscrete _ M hM))
      {μ | IsWorkingLevel μ} (fun κ => ⟨_, (le_max_left κ ℵ₀).trans
        (closureTower_le_iSup id id κ 0), closureTower_iSup_isWorkingLevel id id κ⟩),
    WorkingScheme.emptied_isWorkingPackage _ _ _, ?_, fun _ h => h⟩
  simp [SystemShape.discrete]

/-- **Lemma 9.5** (Joint diagrams on the boundary). A boundary map between same-level `n`-axis
objects preserves bounded diagrams of their boundary unions. -/
theorem lemma_9_5 (K : AbstractElementaryClass.{u}) (n : ℕ)
    (J Kf : FaceFamily K n) (h : BoundaryMap K J Kf) (D : StableDiagram K)
    (hpres : ∀ {M N : Model K.τ} {β : Type u}
        (f : Language.Embedding K.τ M.carrier N.carrier) (zs : β → M.carrier)
        (σ : Cardinal.{u}) (hσ : #β ≤ σ) (hM : K.Mem M) (hN : K.Mem N)
        (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N),
        K.Strong f → D.same hσ hM hN hMcard hNcard zs (fun i => f (zs i)))
    (htrans : ∀ {M N P : Model K.τ} {β : Type u}
        (xs : β → M.carrier) (ys : β → N.carrier) (zs : β → P.carrier)
        (σ : Cardinal.{u}) (hσ : #β ≤ σ)
        (hM : K.Mem M) (hN : K.Mem N) (hP : K.Mem P)
        (hMcard : D.t σ ≤ Model.card M) (hNcard : D.t σ ≤ Model.card N)
        (hPcard : D.t σ ≤ Model.card P),
        D.same hσ hM hN hMcard hNcard xs ys →
        D.same hσ hN hP hNcard hPcard ys zs →
        D.same hσ hM hP hMcard hPcard xs zs) :
    ∀ {α : Type u} (s : Set (Fin n)) (hs : IsProper s)
      (xs : α → (J.obj s).carrier) (σ : Cardinal.{u})
      (hσ : #α ≤ σ)
      (hfaceJ : D.t σ ≤ Model.card (J.obj s))
      (hfaceK : D.t σ ≤ Model.card (Kf.obj s))
      (htopJ : D.t σ ≤ Model.card (J.obj Set.univ))
      (htopK : D.t σ ≤ Model.card (Kf.obj Set.univ)),
      D.same hσ (J.inK Set.univ) (Kf.inK Set.univ) htopJ htopK
        (fun i => J.incl (Set.subset_univ s) (xs i))
        (fun i => Kf.incl (Set.subset_univ s) (h.onFace hs (xs i))) := by
  intro α s hs xs σ hσ hfaceJ hfaceK htopJ htopK
  have h1 := hpres (J.incl (Set.subset_univ s)) xs σ hσ (J.inK s) (J.inK Set.univ)
    hfaceJ htopJ (J.incl_strong _)
  have h2 := hpres (h.onFace hs) xs σ hσ (J.inK s) (Kf.inK s) hfaceJ hfaceK
    (h.onFace_strong hs)
  have h3 := hpres (Kf.incl (Set.subset_univ s)) (fun i => h.onFace hs (xs i)) σ hσ
    (Kf.inK s) (Kf.inK Set.univ) hfaceK htopK (Kf.incl_strong _)
  exact htrans _ _ _ σ hσ _ _ _ _ _ _
    (htrans _ _ _ σ hσ _ _ _ _ _ _
      (D.symm hσ _ _ _ _ _ _ h1) h2) h3

/-- **Theorem 9.6** (Amalgamated boundary completion). A boundary map between same-level
objects extends to arrows of both objects into a common same-level extension.

**Lean statement is weaker than the English:** it asks only for boundary maps `J → Star`,
`Kf → Star` commuting with `h` on proper faces, not for arrows of the top objects. It is
proved by `Star := Kf`, `toJ := h`, `toK := id`. The faithful form (top arrows into a common
extension) needs amalgamation hypotheses and is not claimed here. -/
theorem theorem_9_6 (K : AbstractElementaryClass.{u}) (n : ℕ) :
    ∀ (J Kf : FaceFamily K n) (h : BoundaryMap K J Kf),
      ∃ (Star : FaceFamily K n) (toJ : BoundaryMap K J Star) (toK : BoundaryMap K Kf Star),
        ∀ (s : Set (Fin n)) (hs : IsProper s),
          (toK.onFace hs).comp (h.onFace hs) = toJ.onFace hs := by
  intro J Kf h
  refine ⟨Kf, h, ⟨fun {s} _ => Language.Embedding.refl K.τ (Kf.obj s).carrier,
    fun {s} _ => K.strong_refl _ (Kf.inK s), fun hs ht hst => ?_⟩, fun s hs => ?_⟩
  · ext x
    rfl
  · ext x
    rfl

/-- **Lemma 9.7** (Fixed parameters for a boundary test function). A bounded tuple's diagrams
against boundary tuples of length at most `σ` are fixed by boundary automorphisms that fix a
bounded parameter list.

**False as formalized (kept open, needs hypotheses):** a `FaceFamily` may glue two faces in the
top along an overlap that is not a face, and a boundary automorphism need not agree on that
overlap; then two boundary points from different faces can both be sent to the overlap point,
whatever bounded parameter list is fixed (`AEC.Audit.lemma_9_7_false`, two axes, AEC of all
sets, equality-pattern diagram). The English concerns marked-scheme objects whose tops are
generated freely over the boundary. -/
theorem lemma_9_7 (K : AbstractElementaryClass.{u}) {n : ℕ} (J : FaceFamily K n)
    (D : StableDiagram K) {α : Type u} (z : α → (J.obj Set.univ).carrier)
    (σ : Cardinal.{u}) :
    ∃ (β : Type u) (a : β → (J.obj Set.univ).carrier), #β ≤ σ + #α ∧
      ∀ (h : BoundaryMap K J J), IsBoundaryIso h →
        (∀ i, ∃ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
          a i = J.incl (Set.subset_univ s) x ∧ h.onFace hs x = x) →
        ∀ {ι : Type u} (t : ι → (J.obj Set.univ).carrier), #ι ≤ σ →
          (∀ k, ∃ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
            t k = J.incl (Set.subset_univ s) x) →
          ∃ t' : ι → (J.obj Set.univ).carrier,
            (∀ k, ∃ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
              t k = J.incl (Set.subset_univ s) x ∧
              t' k = J.incl (Set.subset_univ s) (h.onFace hs x)) ∧
            ∀ (hσ : #(α ⊕ ι) ≤ σ + #α)
              (hcard : D.t (σ + #α) ≤ Model.card (J.obj Set.univ)),
              D.same hσ (J.inK Set.univ) (J.inK Set.univ) hcard hcard
                (Sum.elim z t) (Sum.elim z t') := by
  sorry

/-- **Theorem 9.8** (Exact boundary lifting). A boundary isomorphism of same-level `n`-axis
objects extends to an isomorphism of the objects. 

**False as stated (kept open, needs hypotheses):** for arbitrary face families it fails already
on `0` axes (`AEC.Audit.theorem_9_8_arbitrary_false`). The English applies to same-level
`n`-axis objects of the marked scheme; that hypothesis is missing. -/
theorem theorem_9_8 (K : AbstractElementaryClass.{u}) (n : ℕ)
    (J Kf : FaceFamily K n) (h : BoundaryMap K J Kf) (hiso : IsBoundaryIso h) :
    ∃ e : (J.obj Set.univ).carrier ≃[K.τ] (Kf.obj Set.univ).carrier,
      K.Strong e.toEmbedding ∧
      ∀ (s : Set (Fin n)) (hs : IsProper s) (x : (J.obj s).carrier),
        e (J.incl (Set.subset_univ s) x) = Kf.incl (Set.subset_univ s) (h.onFace hs x) := by
  sorry

end
end AEC
