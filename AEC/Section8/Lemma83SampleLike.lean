module

public import AEC.Section8.Lemma83PairDemandM
public import AEC.Section8.HullColorsFormula83
public import AEC.Section8.LabRepHull83

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: sample-like admitted structures and `X_H = F(J_H)`

The admitted class is strengthened from "LS-closed" to "LS-closed and sample-like": the
structure is identified by a bijection `g` with some `E(J⁺)` so that `X = E(emb)(E(J))` is
closed under the `X`-language, sets closed under the `X`-language meet `X` in `F` of their
chart, and the `X`-chart relation names the chart points.  The colors record that the
`J`-coordinates are chart points, so in every witness sample the `X`-hull of the
`J`-coordinates is exactly `F(J_H)`.
-/

universe u

open Cardinal FirstOrder FirstOrder.Language

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- The `X`-language funMap of a `pairLangM3`-structure. -/
abbrev xFun (E : OrderPresentation K) (n : ℕ) {N : Type u} [(LS83.pairLangM3 E n).Structure N]
    {k : ℕ} (f : (LS83.pairLangR E).Functions k) (x : Fin k → N) : N :=
  @Structure.funMap _ _ (((psiM E n).comp (chiM E n)).reduct N) k f x

/-- The `τ`-reduct map of the marked full language. -/
abbrev tauRed (E : OrderPresentation K) (n : ℕ) : K.τ →ᴸ LS83.pairLangM3 E n :=
  ((psiM E n).comp (chiM E n)).comp ((LS83.pairInlR E).comp (LS83.lsInl K))

/-- **Sample-like structures** (for the `X`-sort). -/
def XSampleLike (E : OrderPresentation K) (n : ℕ) (N : Type u)
    [(LS83.pairLangM3 E n).Structure N] : Prop :=
  ∃ (J Jp : Type u) (_ : LinearOrder J) (_ : Nonempty J) (_ : LinearOrder Jp) (_ : Nonempty Jp)
    (emb : J ↪o Jp) (g : N ≃ (E.obj Jp).carrier),
    (∀ {k} (f : (LS83.pairLangR E).Functions k) (x : Fin k → N),
      (∀ i, g (x i) ∈ Set.range (E.map emb)) → g (xFun E n f x) ∈ Set.range (E.map emb)) ∧
    (∀ (T : Set (E.obj Jp).carrier) [Nonempty (Lab83.chart emb T)],
      (∀ {k} (f : (LS83.pairLangR E).Functions k) (x : Fin k → N), (∀ i, g (x i) ∈ T) →
        g (xFun E n f x) ∈ T) →
      T ∩ Set.range (E.map emb) = Set.range (E.map (Lab83.chartEmb emb T))) ∧
    (∀ x, chartXM E n x ↔ ∃ j, E.skeleton (emb j) = g x) ∧
    (∀ {k} (f : K.τ.Functions k) (x : Fin k → N),
      g (@Structure.funMap _ _ ((tauRed E n).reduct N) k f x) = Structure.funMap f (g ∘ x)) ∧
    ∀ {k} (r : K.τ.Relations k) (x : Fin k → N),
      (@Structure.RelMap _ _ ((tauRed E n).reduct N) k r x ↔ Structure.RelMap r (g ∘ x))

/-- **`X_H = F(J_H)` in a sample-like structure**: the `X`-language hull of chart points is
(through `g`) exactly `F` of its chart. -/
theorem xHull_eq_chart (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] {J Jp : Type u} [LinearOrder J] [Nonempty J]
    [LinearOrder Jp] [Nonempty Jp] (emb : J ↪o Jp) (g : N ≃ (E.obj Jp).carrier)
    (hX : ∀ {k} (f : (LS83.pairLangR E).Functions k) (x : Fin k → N),
      (∀ i, g (x i) ∈ Set.range (E.map emb)) → g (xFun E n f x) ∈ Set.range (E.map emb))
    (hchart : ∀ (T : Set (E.obj Jp).carrier) [Nonempty (Lab83.chart emb T)],
      (∀ {k} (f : (LS83.pairLangR E).Functions k) (x : Fin k → N), (∀ i, g (x i) ∈ T) →
        g (xFun E n f x) ∈ T) →
      T ∩ Set.range (E.map emb) = Set.range (E.map (Lab83.chartEmb emb T)))
    {ι : Type} [Nonempty ι] (v : ι → N) (j : ι → J) (hv : ∀ i, E.skeleton (emb (j i)) = g (v i)) :
    ∃ _ : Nonempty (Lab83.chart emb (g '' Set.range
        (@Hull83.hullVal _ _ (((psiM E n).comp (chiM E n)).reduct N) ι v))),
      g '' Set.range (@Hull83.hullVal _ _ (((psiM E n).comp (chiM E n)).reduct N) ι v) =
        Set.range (E.map (Lab83.chartEmb emb (g '' Set.range
          (@Hull83.hullVal _ _ (((psiM E n).comp (chiM E n)).reduct N) ι v)))) := by
  letI := ((psiM E n).comp (chiM E n)).reduct N
  set S := Set.range (Hull83.hullVal (L := LS83.pairLangR E) v)
  have hS : S = Set.range fun t : (LS83.pairLangR E).Term ι => t.realize v := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.out, (Hull83.hullVal_out v x).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Quotient.mk _ t, rfl⟩
  have hcl : ∀ {k} (f : (LS83.pairLangR E).Functions k) (x : Fin k → N),
      (∀ i, x i ∈ S) → xFun E n f x ∈ S := by
    intro k f x hx
    rw [hS] at hx ⊢
    choose t ht using hx
    exact ⟨Term.func f t, by simp only [Term.realize, ht]⟩
  have hsub : g '' S ⊆ Set.range (E.map emb) := by
    rw [hS]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    induction t with
    | var i => exact ⟨E.skeleton (j i), (E.skeleton_natural emb _).trans (hv i)⟩
    | func f ts ih => exact hX f _ ih
  have hne : Nonempty (Lab83.chart emb (g '' S)) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine ⟨⟨j i, ?_⟩⟩
    show E.skeleton (emb (j i)) ∈ g '' S
    rw [hv i, hS]
    exact ⟨_, ⟨Term.var i, rfl⟩, rfl⟩
  refine ⟨hne, ?_⟩
  have hcl' : ∀ {k} (f : (LS83.pairLangR E).Functions k) (x : Fin k → N),
      (∀ i, g (x i) ∈ g '' S) → g (xFun E n f x) ∈ g '' S := by
    intro k f x hx
    refine ⟨_, hcl f x fun i => ?_, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hx i
    rwa [← g.injective hyx]
  rw [← hchart (g '' S) hcl', Set.inter_eq_left.mpr hsub]

/-- The coordinate formulas: `J`-coordinates are `X`-chart points, `Z`-coordinates are
`Y`-chart points. -/
def thetaM (E : OrderPresentation K) (n : ℕ) : Fin 3 → (LS83.pairLangM3 E n).Formula (Fin 1) :=
  ![Relations.formula₁ (Sum.inr (Sum.inl ⟨⟨0⟩, rfl⟩)) (Term.var 0),
    Relations.formula₁ (Sum.inr (Sum.inl ⟨⟨1⟩, rfl⟩)) (Term.var 0), ⊤]

theorem thetaM_zero (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] (x : N) :
    (thetaM E n 0).Realize (fun _ => x) ↔ chartXM E n x := by
  simp only [thetaM, Matrix.cons_val_zero, chartXM]
  show Structure.RelMap _ _ ↔ _
  apply iff_of_eq
  congr 1
  funext i
  fin_cases i
  rfl

theorem thetaM_one (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] (x : N) :
    (thetaM E n 1).Realize (fun _ => x) ↔
      Structure.RelMap (L := LS83.pairLangM3 E n) (Sum.inr (Sum.inl ⟨⟨1⟩, rfl⟩)) ![x] := by
  simp only [thetaM, Matrix.cons_val_one]
  show Structure.RelMap _ _ ↔ _
  apply iff_of_eq
  congr 1
  funext i
  fin_cases i
  rfl

/-- The strengthened admitted class: LS-closed and sample-like. -/
abbrev pairMAdmittedS (E : OrderPresentation K) (n : ℕ) (N : Type u)
    [(LS83.pairLangM3 E n).Structure N] : Prop :=
  pairMAdmitted E n N ∧ XSampleLike E n N

/-- **Coherent colors over sample-like structures, recording the chart coordinates.** -/
theorem infra_83_pairMS_coherent_colors (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS P.E Pr.n N) 3) n c κ) ∧
      (∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm)) ∧
      ∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin 3),
        (thetaM P.E Pr.n i).relabel (fun _ => (a, i)) ∈ c m hm := by
  refine Hull83.tpB_coherent_colors_formula (thetaM P.E Pr.n) fun κ => ?_
  obtain ⟨μ, hθ, -, J, i1, i2, -, hJ, M, -, eX, -, -, ι, Jplus, i3, i4, emb, strip, hstrip, -,
    F, -, -, s₀, hcl, hred, hX, hchX, -⟩ := infra_83_pairR_samples P Pr (κ := ℵ₀) le_rfl κ
  obtain ⟨e⟩ : Nonempty (J ≃ strip) := Cardinal.eq.mp (hJ.trans hstrip.symm)
  let str : (LS83.pairLangM3 P.E Pr.n).Structure (P.E.obj Jplus).carrier :=
    @Language.sumStructure _ _ _ (@Language.sumStructure _ _ _
      (@Language.sumStructure _ _ _ s₀ (@Language.sumStructure _ _ _ (@Language.sumStructure _ _ _
        (Lab83.labTStr (fun y => F (ι y))) (Lab83.repTStr (fun y => F (ι y))))
        (Mark83.markStr fun i => F (markY M i)))) Lab83.labStr)
      (Lab83.chartStr emb (fun y => F (ι y)))
  letI := str
  refine ⟨J, i1, (P.E.obj Jplus).carrier, str,
    ⟨hcl, J, Jplus, i1, i2, i3, i4, emb, Equiv.refl _, fun f x hx => hX f x hx,
      fun T _ hT => hchX T hT, fun x => Iff.rfl,
      fun f x => congrArg (fun s' => @Structure.funMap _ _ s' _ f x) hred,
      fun r x => Iff.of_eq (congrArg (fun s' => @Structure.RelMap _ _ s' _ r x) hred)⟩,
    hJ ▸ hθ, jzwBundle (fun j => P.E.skeleton (emb j)) (fun j => F (ι (P.E.skeleton j)))
      (fun j => P.E.skeleton (e j).1), fun i => ?_, fun a i => ?_⟩
  · fin_cases i
    · exact P.E.skeleton.injective.comp emb.injective
    · exact F.injective.comp (ι.injective.comp P.E.skeleton.injective)
    · exact P.E.skeleton.injective.comp (Subtype.val_injective.comp e.injective)
  · fin_cases i
    · exact (thetaM_zero _ _ _).2
        (show ∃ j, P.E.skeleton (emb j) = P.E.skeleton (emb a) from ⟨a, rfl⟩)
    · exact (thetaM_one _ _ _).2
        (show ∃ z, F (ι (P.E.skeleton z)) = F (ι (P.E.skeleton a)) from ⟨a, rfl⟩)
    · simp [thetaM]

/-- **`X_H = F(J_H)` for the template pieces**: in the witness sample of every arity, the
`X`-language hull of the `J`-coordinates (the `X`-piece) is, through the sample identification
`g`, exactly `F` of its chart. -/
theorem infra_83_pairMS_X_pieces (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS P.E Pr.n N) 3) n c κ),
      (∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm)) ∧
      ∀ k : ℕ, ∃ (J Jp : Type u) (_ : LinearOrder J) (_ : Nonempty J) (_ : LinearOrder Jp)
        (_ : Nonempty Jp) (emb : J ↪o Jp) (g : (Hull83.witB hc k).M ≃ (P.E.obj Jp).carrier),
        ∃ _ : Nonempty (Lab83.chart emb (g '' Set.range
          (@Hull83.hullVal _ _ (((psiM P.E Pr.n).comp (chiM P.E Pr.n)).reduct _) _
            ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))))),
        g '' Set.range (@Hull83.hullVal _ _ (((psiM P.E Pr.n).comp (chiM P.E Pr.n)).reduct _) _
            ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))) =
          Set.range (P.E.map (Lab83.chartEmb emb (g '' Set.range
            (@Hull83.hullVal _ _ (((psiM P.E Pr.n).comp (chiM P.E Pr.n)).reduct _) _
              ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))))))) := by
  obtain ⟨c, hc, hcoh, hθ⟩ := infra_83_pairMS_coherent_colors P Pr
  refine ⟨c, hc, hcoh, fun k => ?_⟩
  obtain ⟨J, Jp, i1, i2, i3, i4, emb, g, hX, hch, hcx, -, -⟩ := (Hull83.witB hc k).mem.2
  have hpt : ∀ p : Fin (k + 1) × Fin 1, ∃ j, P.E.skeleton (emb j) =
      g ((Hull83.witB hc k).v (p.1, 0)) := fun p =>
    (hcx _).1 ((thetaM_zero _ _ _).1 (Hull83.witB_realize hc hθ k p.1 0))
  choose j hj using hpt
  exact ⟨J, Jp, i1, i2, i3, i4, emb, g,
    xHull_eq_chart P.E Pr.n emb g hX hch _ j hj⟩

/-- Two embeddings with the same range: the first factors through the second bijectively. -/
theorem emb_equiv_of_range {A B C : Type u} [K.τ.Structure A] [K.τ.Structure B]
    [K.τ.Structure C] (f : A ↪[K.τ] C) (h : B ↪[K.τ] C) (hr : Set.range f = Set.range h) :
    ∃ ε : A ↪[K.τ] B, Function.Bijective ε ∧ ∀ a, h (ε a) = f a := by
  have hmem : ∀ a, ∃ b, h b = f a := fun a => by
    have : f a ∈ Set.range h := hr ▸ ⟨a, rfl⟩
    exact this
  choose F hF using hmem
  refine ⟨Hull83.embOfComp h f F hF, ⟨(Hull83.embOfComp h f F hF).injective, fun b => ?_⟩, hF⟩
  have : h b ∈ Set.range f := hr ▸ ⟨b, rfl⟩
  obtain ⟨a, ha⟩ := this
  exact ⟨a, h.injective ((hF a).trans ha)⟩

/-- The sample identification as a `τ`-embedding. -/
def sampleEmb (E : OrderPresentation K) (n : ℕ) {N : Type u} [(LS83.pairLangM3 E n).Structure N]
    {Jp : Type u} [LinearOrder Jp] [Nonempty Jp] (g : N ≃ (E.obj Jp).carrier)
    (hf : ∀ {k} (f : K.τ.Functions k) (x : Fin k → N),
      g (@Structure.funMap _ _ ((tauRed E n).reduct N) k f x) = Structure.funMap f (g ∘ x))
    (hr : ∀ {k} (r : K.τ.Relations k) (x : Fin k → N),
      (@Structure.RelMap _ _ ((tauRed E n).reduct N) k r x ↔ Structure.RelMap r (g ∘ x))) :
    (Hull83.red (tauRed E n) N).carrier ↪[K.τ] (E.obj Jp).carrier where
  toFun := g
  inj' := g.injective
  map_fun' f x := hf f x
  map_rel' r x := (hr r x).symm

/-- **`X_k ≅ F(J_k)`**: for every arity `k`, the `X`-piece of the template (the `X`-language hull
of the `J`-coordinates of the witness bundle) is `τ`-isomorphic (a bijective `τ`-embedding) to
`F` of its chart, compatibly with the sample identification. -/
theorem infra_83_pairMS_X_pieces_iso (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS P.E Pr.n N) 3) n c κ),
      (∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm)) ∧
      ∀ k : ℕ, ∃ (J Jp : Type u) (_ : LinearOrder J) (_ : Nonempty J) (_ : LinearOrder Jp)
        (_ : Nonempty Jp) (emb : J ↪o Jp) (g : (Hull83.witB hc k).M ≃ (P.E.obj Jp).carrier)
        (H : Set J) (_ : Nonempty H)
        (ε : (Hull83.subHullModel ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K))
          ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))).carrier ↪[K.τ]
          (P.E.obj H).carrier),
        Function.Bijective ε ∧ ∀ x, P.E.map ((OrderEmbedding.subtype (· ∈ H)).trans emb) (ε x) =
          g (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
            ((LS83.pairInlR P.E).comp (LS83.lsInl K))
            ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x) := by
  obtain ⟨c, hc, hcoh, hθ⟩ := infra_83_pairMS_coherent_colors P Pr
  refine ⟨c, hc, hcoh, fun k => ?_⟩
  obtain ⟨J, Jp, i1, i2, i3, i4, emb, g, hX, hch, hcx, hτf, hτr⟩ := (Hull83.witB hc k).mem.2
  have hpt : ∀ p : Fin (k + 1) × Fin 1, ∃ j, P.E.skeleton (emb j) =
      g ((Hull83.witB hc k).v (p.1, 0)) := fun p =>
    (hcx _).1 ((thetaM_zero _ _ _).1 (Hull83.witB_realize hc hθ k p.1 0))
  choose j hj using hpt
  obtain ⟨T, hne, hset⟩ : ∃ (T : Set (P.E.obj Jp).carrier) (_ : Nonempty (Lab83.chart emb T)),
      g '' Set.range (@Hull83.hullVal _ _ (((psiM P.E Pr.n).comp (chiM P.E Pr.n)).reduct _) _
        ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))) =
        Set.range (P.E.map (Lab83.chartEmb emb T)) := by
    obtain ⟨hne, hset⟩ := xHull_eq_chart P.E Pr.n emb g hX hch _ j hj
    exact ⟨_, hne, hset⟩
  let f := (sampleEmb P.E Pr.n g hτf hτr).comp
    (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
      ((LS83.pairInlR P.E).comp (LS83.lsInl K))
      ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))))
  have hrange : Set.range f = Set.range (P.E.map (Lab83.chartEmb emb T)) := by
    rw [← hset]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  obtain ⟨ε, hbij, hε⟩ := emb_equiv_of_range f _ hrange
  exact ⟨J, Jp, i1, i2, i3, i4, emb, g, _, hne, ε, hbij, hε⟩

end AEC
