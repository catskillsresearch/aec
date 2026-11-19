module

public import AEC.Section8.Lemma83SampleLike

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: `Y_k ≅ F(Z_k)`

The admitted class is further strengthened by the `Y`-side sample data: a `τ`-embedding
`e₀ : F(Z) → L` with `Y = range e₀` (through `g`) closed under the `Y`-language, chart
generation for `Y`, the `Y`-chart relation naming the transported chart points, and `X ⊆ Y`.
Then every `Y`-piece is `τ`-isomorphic to `F` of its chart.
-/

universe u

open Cardinal FirstOrder FirstOrder.Language

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- The `Y`-language funMap of a `pairLangM3`-structure. -/
abbrev yFun (E : OrderPresentation K) (n : ℕ) {N : Type u} [(LS83.pairLangM3 E n).Structure N]
    {k : ℕ} (f : (LS83.pairLangM2 E n).Functions k) (x : Fin k → N) : N :=
  @Structure.funMap _ _ ((psiM E n).reduct N) k f x

/-- `Y`-chart predicate. -/
def chartYM (E : OrderPresentation K) (n : ℕ) {N : Type u} [(LS83.pairLangM3 E n).Structure N]
    (x : N) : Prop :=
  Structure.RelMap (L := LS83.pairLangM3 E n) (Sum.inr (Sum.inl ⟨⟨1⟩, rfl⟩)) ![x]

/-- `Y`-chart order in a `pairLangM3`-structure. -/
def chartLtYM (E : OrderPresentation K) (n : ℕ) {N : Type u} [(LS83.pairLangM3 E n).Structure N]
    (x y : N) : Prop :=
  Structure.RelMap (L := LS83.pairLangM3 E n) (Sum.inr (Sum.inr ⟨⟨1⟩, rfl⟩)) ![x, y]

/-- **Sample-like structures, `Y`-side data.** -/
def YSampleLike (E : OrderPresentation K) (n : ℕ) (N : Type u)
    [(LS83.pairLangM3 E n).Structure N] : Prop :=
  ∃ (Z Jp : Type u) (_ : LinearOrder Z) (_ : Nonempty Z) (_ : LinearOrder Jp) (_ : Nonempty Jp)
    (e₀ : (E.obj Z).carrier ↪[K.τ] (E.obj Jp).carrier) (g : N ≃ (E.obj Jp).carrier),
    (∀ {k} (f : (LS83.pairLangM2 E n).Functions k) (x : Fin k → N),
      (∀ i, g (x i) ∈ Set.range e₀) → g (yFun E n f x) ∈ Set.range e₀) ∧
    (∀ (T : Set (E.obj Jp).carrier) [Nonempty (Lab83.chartT e₀ T)],
      (∀ {k} (f : (LS83.pairLangM2 E n).Functions k) (x : Fin k → N), (∀ i, g (x i) ∈ T) →
        g (yFun E n f x) ∈ T) →
      T ∩ Set.range e₀ =
        Set.range (e₀ ∘ E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T)))) ∧
    (∀ x, chartYM E n x ↔ ∃ z, e₀ (E.skeleton z) = g x) ∧
    (∀ x, chartXM E n x → g x ∈ Set.range e₀) ∧
    (∀ {k} (f : K.τ.Functions k) (x : Fin k → N),
      g (@Structure.funMap _ _ ((tauRed E n).reduct N) k f x) = Structure.funMap f (g ∘ x)) ∧
    (∀ {k} (r : K.τ.Relations k) (x : Fin k → N),
      (@Structure.RelMap _ _ ((tauRed E n).reduct N) k r x ↔ Structure.RelMap r (g ∘ x))) ∧
    ∀ x y, chartLtYM E n x y ↔
      ∃ z z', z < z' ∧ e₀ (E.skeleton z) = g x ∧ e₀ (E.skeleton z') = g y

/-- **`Y_H ≅ F(Z_H)` in a sample-like structure** (set level, through `g`). -/
theorem yHull_eq_chart (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] {Z Jp : Type u} [LinearOrder Z] [Nonempty Z]
    [LinearOrder Jp] [Nonempty Jp] (e₀ : (E.obj Z).carrier → (E.obj Jp).carrier)
    (g : N ≃ (E.obj Jp).carrier)
    (hY : ∀ {k} (f : (LS83.pairLangM2 E n).Functions k) (x : Fin k → N),
      (∀ i, g (x i) ∈ Set.range e₀) → g (yFun E n f x) ∈ Set.range e₀)
    (hchart : ∀ (T : Set (E.obj Jp).carrier) [Nonempty (Lab83.chartT e₀ T)],
      (∀ {k} (f : (LS83.pairLangM2 E n).Functions k) (x : Fin k → N), (∀ i, g (x i) ∈ T) →
        g (yFun E n f x) ∈ T) →
      T ∩ Set.range e₀ =
        Set.range (e₀ ∘ E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T))))
    {ι : Type} (v : ι → N) (hv : ∀ i, g (v i) ∈ Set.range e₀) (i₀ : ι) (z₀ : Z)
    (h₀ : e₀ (E.skeleton z₀) = g (v i₀)) :
    ∃ (T : Set (E.obj Jp).carrier) (_ : Nonempty (Lab83.chartT e₀ T)),
      g '' Set.range (@Hull83.hullVal _ _ ((psiM E n).reduct N) ι v) =
        Set.range (e₀ ∘ E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T))) := by
  letI := (psiM E n).reduct N
  set S := Set.range (Hull83.hullVal (L := LS83.pairLangM2 E n) v)
  have hS : S = Set.range fun t : (LS83.pairLangM2 E n).Term ι => t.realize v := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.out, (Hull83.hullVal_out v x).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Quotient.mk _ t, rfl⟩
  have hcl : ∀ {k} (f : (LS83.pairLangM2 E n).Functions k) (x : Fin k → N),
      (∀ i, x i ∈ S) → yFun E n f x ∈ S := by
    intro k f x hx
    rw [hS] at hx ⊢
    choose t ht using hx
    exact ⟨Term.func f t, by simp only [Term.realize, ht]⟩
  have hsub : g '' S ⊆ Set.range e₀ := by
    rw [hS]
    rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    induction t with
    | var i => exact hv i
    | func f ts ih => exact hY f _ ih
  have hne : Nonempty (Lab83.chartT e₀ (g '' S)) := by
    refine ⟨⟨z₀, ?_⟩⟩
    show e₀ (E.skeleton z₀) ∈ g '' S
    rw [h₀, hS]
    exact ⟨_, ⟨Term.var i₀, rfl⟩, rfl⟩
  have hcl' : ∀ {k} (f : (LS83.pairLangM2 E n).Functions k) (x : Fin k → N),
      (∀ i, g (x i) ∈ g '' S) → g (yFun E n f x) ∈ g '' S := by
    intro k f x hx
    refine ⟨_, hcl f x fun i => ?_, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hx i
    rwa [← g.injective hyx]
  refine ⟨g '' S, hne, ?_⟩
  rw [← hchart (g '' S) hcl', Set.inter_eq_left.mpr hsub]

theorem thetaM_one' (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] (x : N) :
    (thetaM E n 1).Realize (fun _ => x) ↔ chartYM E n x :=
  thetaM_one E n x

/-- The pair formulas: increasing `J`-coordinates are in `X`-chart order, increasing
`Z`-coordinates in `Y`-chart order. -/
def rhoM (E : OrderPresentation K) (n : ℕ) : Fin 3 → (LS83.pairLangM3 E n).Formula (Fin 2) :=
  ![Relations.formula₂ (Sum.inr (Sum.inr ⟨⟨0⟩, rfl⟩)) (Term.var 0) (Term.var 1),
    Relations.formula₂ (Sum.inr (Sum.inr ⟨⟨1⟩, rfl⟩)) (Term.var 0) (Term.var 1), ⊤]

theorem rhoM_zero (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] (x y : N) :
    (rhoM E n 0).Realize ![x, y] ↔ chartLtXM E n x y := by
  simp only [rhoM, Matrix.cons_val_zero, chartLtXM]
  show Structure.RelMap _ _ ↔ _
  apply iff_of_eq
  congr 1
  funext i
  fin_cases i <;> rfl

theorem rhoM_one (E : OrderPresentation K) (n : ℕ) {N : Type u}
    [(LS83.pairLangM3 E n).Structure N] (x y : N) :
    (rhoM E n 1).Realize ![x, y] ↔ chartLtYM E n x y := by
  simp only [rhoM, Matrix.cons_val_one, chartLtYM]
  show Structure.RelMap _ _ ↔ _
  apply iff_of_eq
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The admitted class with both `X`- and `Y`-side sample data. -/
abbrev pairMAdmittedS2 (E : OrderPresentation K) (n : ℕ) (N : Type u)
    [(LS83.pairLangM3 E n).Structure N] : Prop :=
  pairMAdmittedS E n N ∧ YSampleLike E n N

/-- **Coherent colors over `X`- and `Y`-sample-like structures, recording chart coordinates.** -/
theorem infra_83_pairMS2_coherent_colors (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ) ∧
      (∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm)) ∧
      (∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin 3),
        (thetaM P.E Pr.n i).relabel (fun _ => (a, i)) ∈ c m hm) ∧
      ∀ (m : ℕ) (hm : 0 < m) (a b : Fin m), a < b → ∀ i : Fin 3,
        (rhoM P.E Pr.n i).relabel ![(a, i), (b, i)] ∈ c m hm := by
  refine Hull83.tpB_coherent_colors_formula2 (thetaM P.E Pr.n) (rhoM P.E Pr.n) fun κ => ?_
  obtain ⟨μ, hθ, -, J, i1, i2, -, hJ, M, -, eX, -, -, ι, Jplus, i3, i4, emb, strip, hstrip, -,
    F, -, hF, s₀, hcl, hred, hX, hchX, hY, hchY, -, -, hlabX⟩ :=
    infra_83_pairR_samples P Pr (κ := ℵ₀) le_rfl κ
  obtain ⟨e⟩ : Nonempty (J ≃ strip) := Cardinal.eq.mp (hJ.trans hstrip.symm)
  let str : (LS83.pairLangM3 P.E Pr.n).Structure (P.E.obj Jplus).carrier :=
    @Language.sumStructure _ _ _ (@Language.sumStructure _ _ _
      (@Language.sumStructure _ _ _ s₀ (@Language.sumStructure _ _ _ (@Language.sumStructure _ _ _
        (Lab83.labTStr (fun y => F (ι y))) (Lab83.repTStr (fun y => F (ι y))))
        (Mark83.markStr fun i => F (markY M i)))) Lab83.labStr)
      (Lab83.chartStr emb (fun y => F (ι y)))
  letI := str
  let e₀ : (P.E.obj J).carrier ↪[K.τ] (P.E.obj Jplus).carrier := F.comp ι.toEmbedding
  have he₀ : ∀ y, e₀ y = F (ι y) := fun _ => rfl
  have hrF : Set.range F ⊆ Set.range e₀ := by
    rintro _ ⟨y, rfl⟩
    exact ⟨ι.symm y, by rw [he₀]; exact congrArg F (ι.apply_symm_apply y)⟩
  have hre : Set.range e₀ = Set.range (fun y => F (ι y)) := rfl
  refine ⟨J, i1, (P.E.obj Jplus).carrier, str,
    ⟨⟨hcl, J, Jplus, i1, i2, i3, i4, emb, Equiv.refl _, fun f x hx => hX f x hx,
      fun T _ hT => hchX T hT, fun x => Iff.rfl,
      fun f x => congrArg (fun s' => @Structure.funMap _ _ s' _ f x) hred,
      fun r x => Iff.of_eq (congrArg (fun s' => @Structure.RelMap _ _ s' _ r x) hred),
      fun x y => Iff.rfl, fun a y hy => (hlabX a y).trans (Lab83.labR_of_mem a y hy)⟩,
     J, Jplus, i1, i2, i3, i4, e₀, Equiv.refl _, ?_, ?_, fun x => Iff.rfl, ?_,
      fun f x => congrArg (fun s' => @Structure.funMap _ _ s' _ f x) hred,
      fun r x => Iff.of_eq (congrArg (fun s' => @Structure.RelMap _ _ s' _ r x) hred),
      fun x y => Iff.rfl⟩,
    hJ ▸ hθ, jzwBundle (fun j => P.E.skeleton (emb j)) (fun j => F (ι (P.E.skeleton j)))
      (fun j => P.E.skeleton (e j).1), fun i => ?_, fun a i => ?_, fun a b hab i => ?_⟩
  · intro k f x hx
    have hx' : ∀ i, x i ∈ Set.range F := fun i => by
      obtain ⟨y, hy⟩ := hx i
      exact ⟨ι y, hy⟩
    rcases f with f | (f | f)
    · exact hrF (hY (Sum.inl f) x hx')
    · exact hrF (hY (Sum.inr f) x hx')
    · exact hrF (Mark83.mark_mem (fun i => F (markY M i)) (S := Set.range F)
        (fun i => Set.mem_range_self _) f x)
  · intro T hTne hT
    exact @hchY T hTne fun f x hx => by
      rcases f with f | f
      · exact hT (Sum.inl f) x hx
      · exact hT (Sum.inr (Sum.inl f)) x hx
  · intro x hx
    obtain ⟨j, rfl⟩ : ∃ j, P.E.skeleton (emb j) = x := hx
    exact hrF ⟨_, (hF (P.E.skeleton j)).trans (P.E.skeleton_natural emb j)⟩
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
  · fin_cases i
    · exact (rhoM_zero _ _ _ _).2 (show ∃ j j', j < j' ∧ P.E.skeleton (emb j) =
        P.E.skeleton (emb a) ∧ P.E.skeleton (emb j') = P.E.skeleton (emb b) from
        ⟨a, b, hab, rfl, rfl⟩)
    · exact (rhoM_one _ _ _ _).2 (show ∃ z z', z < z' ∧ F (ι (P.E.skeleton z)) =
        F (ι (P.E.skeleton a)) ∧ F (ι (P.E.skeleton z')) = F (ι (P.E.skeleton b)) from
        ⟨a, b, hab, rfl, rfl⟩)
    · simp [rhoM]

/-- **`X_k ≅ F(J_k)` and `Y_k ≅ F(Z_k)`** for the template pieces over `X`- and
`Y`-sample-like structures: bijective `τ`-embeddings onto `F` of the charts. -/
theorem infra_83_pairMS2_pieces_iso (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ),
      (∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm)) ∧
      ∀ k : ℕ,
        (∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (H : Set J) (_ : Nonempty H)
          (ε : (Hull83.subHullModel ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
            ((LS83.pairInlR P.E).comp (LS83.lsInl K))
            ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))).carrier ↪[K.τ]
            (P.E.obj H).carrier), Function.Bijective ε) ∧
        (∃ (Z : Type u) (_ : LinearOrder Z) (_ : Nonempty Z) (H : Set Z) (_ : Nonempty H)
          (ε : (Hull83.subHullModel (psiM P.E Pr.n)
            ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
            ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc))).carrier ↪[K.τ]
            (P.E.obj H).carrier), Function.Bijective ε) := by
  obtain ⟨c, hc, hcoh, hθ, hρ⟩ := infra_83_pairMS2_coherent_colors P Pr
  refine ⟨c, hc, hcoh, fun k => ⟨?_, ?_⟩⟩
  · obtain ⟨J, Jp, i1, i2, i3, i4, emb, g, hX, hch, hcx, hτf, hτr, -⟩ := (Hull83.witB hc k).mem.1.2
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
    obtain ⟨ε, hbij, -⟩ := emb_equiv_of_range f _ hrange
    exact ⟨J, i1, i2, _, hne, ε, hbij⟩
  · obtain ⟨Z, Jp, i1, i2, i3, i4, e₀, g, hY, hch, hcy, hXY, hτf, hτr, -⟩ := (Hull83.witB hc k).mem.2
    have hv : ∀ p : Fin (k + 1) × Fin 2,
        g (((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)) p) ∈
          Set.range e₀ := by
      rintro ⟨a, b⟩
      fin_cases b
      · exact hXY _ ((thetaM_zero _ _ _).1 (Hull83.witB_realize hc hθ k a 0))
      · obtain ⟨z, hz⟩ := (hcy _).1 ((thetaM_one _ _ _).1 (Hull83.witB_realize hc hθ k a 1))
        exact ⟨_, hz⟩
    obtain ⟨z₀, hz₀⟩ := (hcy _).1 ((thetaM_one _ _ _).1 (Hull83.witB_realize hc hθ k 0 1))
    obtain ⟨T, hne, hset⟩ := yHull_eq_chart P.E Pr.n e₀ g hY hch
      ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)) hv (0, 1) z₀ hz₀
    let f := (sampleEmb P.E Pr.n g hτf hτr).comp
      (Hull83.subHullEmb (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
        ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)))
    have hrange : Set.range f = Set.range (e₀.comp (P.E.map (OrderEmbedding.subtype
        (fun z => z ∈ Lab83.chartT e₀ T)))) := by
      have h2 : Set.range (e₀.comp (P.E.map (OrderEmbedding.subtype
          (fun z => z ∈ Lab83.chartT e₀ T)))) =
          Set.range (e₀ ∘ P.E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T))) :=
        rfl
      rw [h2, ← hset]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨_, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
    obtain ⟨ε, hbij, -⟩ := emb_equiv_of_range f _ hrange
    exact ⟨Z, i1, i2, _, hne, ε, hbij⟩

/-- The pair template over `X`- and `Y`-sample-like structures: as
`infra_83_pairMS_template`, with both `X_k ≅ F(J_k)` and `Y_k ≅ F(Z_k)`. -/
theorem infra_83_pairMS2_template (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (FX FY FL : EM83.FinPieces K) (ηXY : EM83.PiecesHom FX FY) (ηYL : EM83.PiecesHom FY FL)
      (E : OrderPresentation K),
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], E.obj I = (FL.limit I).obj) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        K.Strong (ηXY.limMap I) ∧ K.Strong (ηYL.limMap I) ∧
          (ηYL.comp ηXY).limMap I = (ηYL.limMap I).comp (ηXY.limMap I)) ∧
      (∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J] (f : I ↪o J),
        K.Strong (EM83.gEmMap (F := FX) f) ∧ K.Strong (EM83.gEmMap (F := FY) f) ∧
        K.Strong (EM83.gEmMap (F := FL) f) ∧
        (ηXY.limMap J).comp (EM83.gEmMap (F := FX) f) =
            (EM83.gEmMap (F := FY) f).comp (ηXY.limMap I) ∧
          (ηYL.limMap J).comp (EM83.gEmMap (F := FY) f) =
            (EM83.gEmMap (F := FL) f).comp (ηYL.limMap I)) ∧
      ∀ k : ℕ,
        (∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (H : Set J) (_ : Nonempty H)
          (ε : (FX.obj k).carrier ↪[K.τ] (P.E.obj H).carrier), Function.Bijective ε) ∧
        (∃ (Z : Type u) (_ : LinearOrder Z) (_ : Nonempty Z) (H : Set Z) (_ : Nonempty H)
          (ε : (FY.obj k).carrier ↪[K.τ] (P.E.obj H).carrier), Function.Bijective ε) := by
  obtain ⟨c, hc, hcoh, hiso⟩ := infra_83_pairMS2_pieces_iso P Pr
  let σ : Fin 2 → Fin 3 := fun i => i.castSucc
  let τ : Fin 1 → Fin 2 := fun _ => 0
  let φ₀ := (LS83.pairInlR P.E).comp (LS83.lsInl K)
  have hX : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n)) φ₀
      (fun N _ => pairMAdmittedS2 P.E Pr.n N) :=
    fun M _ hM => pairM_subHullStrongX P.E Pr.n M hM.1.1
  have hY : Hull83.SubHullStrong (psiM P.E Pr.n) ((chiM P.E Pr.n).comp φ₀)
      (fun N _ => pairMAdmittedS2 P.E Pr.n N) :=
    fun M _ hM => pairM_subHullStrongY P.E Pr.n M hM.1.1
  have hL : Hull83.HullStrong ((psiM P.E Pr.n).comp ((chiM P.E Pr.n).comp φ₀))
      (fun N _ => pairMAdmittedS2 P.E Pr.n N) :=
    fun M _ hM => pairM_hullStrong P.E Pr.n M hM.1.1
  let ηXY := Hull83.subLangMixHom (chiM P.E Pr.n) (psiM P.E Pr.n) φ₀ hc hcoh σ τ hX hY
  let ηYL := Hull83.subLangChain (psiM P.E Pr.n) ((chiM P.E Pr.n).comp φ₀) hc hcoh σ hY hL
  refine ⟨_, _, _, ηXY, ηYL,
    Hull83.tpPresentationB hc hcoh (by norm_num) ((psiM P.E Pr.n).comp ((chiM P.E Pr.n).comp φ₀))
      hL (LS83.pairLangM3_functions_le P.E Pr.n),
    fun I _ _ => rfl,
    fun I _ _ => ⟨ηXY.limMap_strong I, ηYL.limMap_strong I, EM83.PiecesHom.limMap_comp _ _ I⟩,
    fun f => ⟨EM83.gEmMap_strong f, EM83.gEmMap_strong f, EM83.gEmMap_strong f,
      ηXY.limMap_natural f, ηYL.limMap_natural f⟩, fun k => ?_⟩
  exact hiso k

/-- **Local form of the limit pieces**: in the pair template over `X`- and `Y`-sample-like
structures, every element of the limit value `F_X(I)` (resp. `F_Y(I)`) is the image under a
canonical map of an element of a finite-support piece, and every finite piece is
`τ`-isomorphic to `F(J_k)` (resp. `F(Z_k)`). (The global identification `F_X(I) ≅ F(J_I)`,
coherent along the piece maps, is the open tip `infra_83_X_hull_eq_FJ`.) -/
theorem infra_83_pairMS2_limit_local (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (FX FY : EM83.FinPieces K),
      (∀ k : ℕ,
        (∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (H : Set J) (_ : Nonempty H)
          (ε : (FX.obj k).carrier ↪[K.τ] (P.E.obj H).carrier), Function.Bijective ε) ∧
        (∃ (Z : Type u) (_ : LinearOrder Z) (_ : Nonempty Z) (H : Set Z) (_ : Nonempty H)
          (ε : (FY.obj k).carrier ↪[K.τ] (P.E.obj H).carrier), Function.Bijective ε)) ∧
      ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        (∀ x : (FX.limit I).obj.carrier, ∃ (s : (FX.system I).ι) (y : (FX.obj s.1.card.pred).carrier),
          (FX.limit I).canon s y = x) ∧
        (∀ x : (FY.limit I).obj.carrier, ∃ (s : (FY.system I).ι) (y : (FY.obj s.1.card.pred).carrier),
          (FY.limit I).canon s y = x) := by
  obtain ⟨FX, FY, -, -, -, -, -, -, -, hiso⟩ := infra_83_pairMS2_template P Pr
  exact ⟨FX, FY, hiso, fun I _ _ => ⟨fun x => (FX.limit I).joint x,
    fun x => (FY.limit I).joint x⟩⟩

/-- **`X_k ≅ F(J_k)` sends coordinates to skeleton points**: the `τ`-isomorphism of the
`X`-piece onto `F(J_k)` maps the hull element of the `a`-th `J`-coordinate to the skeleton
point of an injectively chosen `j a ∈ J_k`. -/
theorem infra_83_pairMS2_X_pieces_coord (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ),
      (∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm)) ∧
      ∀ k : ℕ,
        ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (H : Set J) (_ : Nonempty H)
          (ε : (Hull83.subHullModel ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
            ((LS83.pairInlR P.E).comp (LS83.lsInl K))
            ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))).carrier ↪[K.τ]
            (P.E.obj H).carrier) (jH : Fin (k + 1) → H),
          Function.Bijective ε ∧ Function.Injective jH ∧
          ∀ x a, Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
              ((LS83.pairInlR P.E).comp (LS83.lsInl K))
              ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x =
              (Hull83.witB hc k).v (a, 0) →
            ε x = P.E.skeleton (jH a) := by
  obtain ⟨c, hc, hcoh, hθ, hρ⟩ := infra_83_pairMS2_coherent_colors P Pr
  refine ⟨c, hc, hcoh, fun k => ?_⟩
  obtain ⟨J, Jp, i1, i2, i3, i4, emb, g, hX, hch, hcx, hτf, hτr, -⟩ := (Hull83.witB hc k).mem.1.2
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
  have hmem : ∀ a : Fin (k + 1), j (a, 0) ∈ Lab83.chart emb T := fun a => by
    have h1 : P.E.skeleton (emb (j (a, 0))) ∈ Set.range (P.E.map (Lab83.chartEmb emb T)) := by
      rw [← hset, hj (a, 0)]
      exact ⟨_, ⟨Quotient.mk _ (Term.var (a, 0)), rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := Lab83.skeleton_mem_range (E := P.E) (Lab83.chartEmb emb T) h1
    have : y.1 = j (a, 0) := emb.injective hy
    exact this ▸ y.2
  refine ⟨J, i1, i2, _, hne, ε, fun a => ⟨j (a, 0), hmem a⟩, hbij, ?_, ?_⟩
  · intro a b hab
    have h2 : j (a, 0) = j (b, 0) := congrArg Subtype.val hab
    have h3 := (hj (a, 0)).symm.trans ((congrArg (fun z => P.E.skeleton (emb z)) h2).trans (hj (b, 0)))
    exact (Hull83.witB hc k).inj 0 (g.injective h3)
  · intro x a hx
    apply (P.E.map (Lab83.chartEmb emb T)).injective
    rw [hε x, P.E.skeleton_natural]
    show g _ = _
    rw [hx]
    exact (hj (a, 0)).symm

/-- The coordinate chart of one `X`-piece, for given colors recording `thetaM`. -/
theorem pairMS2_X_coord_of (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
    (hθ : ∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin 3),
        (thetaM P.E Pr.n i).relabel (fun _ => (a, i)) ∈ c m hm)
    (hρ : ∀ (m : ℕ) (hm : 0 < m) (a b : Fin m), a < b → ∀ i : Fin 3,
        (rhoM P.E Pr.n i).relabel ![(a, i), (b, i)] ∈ c m hm) (k : ℕ) :
        ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J) (H : Set J) (_ : Nonempty H)
          (ε : (Hull83.subHullModel ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
            ((LS83.pairInlR P.E).comp (LS83.lsInl K))
            ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))).carrier ↪[K.τ]
            (P.E.obj H).carrier) (jH : Fin (k + 1) → H),
          Function.Bijective ε ∧ Function.Injective jH ∧ StrictMono jH ∧
          (∀ x a, Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
              ((LS83.pairInlR P.E).comp (LS83.lsInl K))
              ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x =
              (Hull83.witB hc k).v (a, 0) →
            ε x = P.E.skeleton (jH a)) ∧
          (∀ x, (∃ p, ε x = P.E.skeleton p) ↔ chartXM (M := (Hull83.witB hc k).M) P.E Pr.n (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
              ((LS83.pairInlR P.E).comp (LS83.lsInl K))
              ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x :
              (Hull83.witB hc k).M)) ∧
          (∀ x x' p p', ε x = P.E.skeleton p → ε x' = P.E.skeleton p' →
            (p < p' ↔ chartLtXM (M := (Hull83.witB hc k).M) P.E Pr.n (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
              ((LS83.pairInlR P.E).comp (LS83.lsInl K))
              ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x :
              (Hull83.witB hc k).M)
              (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
              ((LS83.pairInlR P.E).comp (LS83.lsInl K))
              ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x' :
              (Hull83.witB hc k).M))) ∧
          ∀ {m} (a : (Lab83.labLang P.E).Functions m) (xs : Fin m → (Hull83.subHullModel ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
            ((LS83.pairInlR P.E).comp (LS83.lsInl K))
            ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))).carrier)
            (x : (Hull83.subHullModel ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
            ((LS83.pairInlR P.E).comp (LS83.lsInl K))
            ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))).carrier),
            (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
              ((LS83.pairInlR P.E).comp (LS83.lsInl K))
              ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x :
              (Hull83.witB hc k).M) = xFun (N := (Hull83.witB hc k).M) P.E Pr.n (Sum.inl (Sum.inr a))
              (fun i => (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
              ((LS83.pairInlR P.E).comp (LS83.lsInl K))
              ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) (xs i) :
              (Hull83.witB hc k).M)) →
            ε x = Lab83.labFun a (fun i => ε (xs i)) := by
  obtain ⟨J, Jp, i1, i2, i3, i4, emb, g, hX, hch, hcx, hτf, hτr, hlt, hlab⟩ := (Hull83.witB hc k).mem.1.2
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
  have hmem : ∀ a : Fin (k + 1), j (a, 0) ∈ Lab83.chart emb T := fun a => by
    have h1 : P.E.skeleton (emb (j (a, 0))) ∈ Set.range (P.E.map (Lab83.chartEmb emb T)) := by
      rw [← hset, hj (a, 0)]
      exact ⟨_, ⟨Quotient.mk _ (Term.var (a, 0)), rfl⟩, rfl⟩
    obtain ⟨y, hy⟩ := Lab83.skeleton_mem_range (E := P.E) (Lab83.chartEmb emb T) h1
    have : y.1 = j (a, 0) := emb.injective hy
    exact this ▸ y.2
  refine ⟨J, i1, i2, _, hne, ε, fun a => ⟨j (a, 0), hmem a⟩, hbij, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    have h2 : j (a, 0) = j (b, 0) := congrArg Subtype.val hab
    have h3 := (hj (a, 0)).symm.trans ((congrArg (fun z => P.E.skeleton (emb z)) h2).trans (hj (b, 0)))
    exact (Hull83.witB hc k).inj 0 (g.injective h3)
  · intro a b hab
    obtain ⟨j1, j2, h12, h1, h2⟩ := (hlt _ _).1
      ((rhoM_zero _ _ _ _).1 (Hull83.witB_realize2 hc hρ k hab 0))
    have e1 : j1 = j (a, 0) := emb.injective (P.E.skeleton.injective (h1.trans (hj (a, 0)).symm))
    have e2 : j2 = j (b, 0) := emb.injective (P.E.skeleton.injective (h2.trans (hj (b, 0)).symm))
    show j (a, 0) < j (b, 0)
    rw [← e1, ← e2]
    exact h12
  · intro x a hx
    apply (P.E.map (Lab83.chartEmb emb T)).injective
    rw [hε x, P.E.skeleton_natural]
    show g _ = _
    rw [hx]
    exact (hj (a, 0)).symm
  · intro x
    constructor
    · rintro ⟨p, hp⟩
      have h1 := hε x
      rw [hp, P.E.skeleton_natural] at h1
      exact (hcx _).2 ⟨p.1, h1⟩
    · intro hx
      obtain ⟨j0, hj0⟩ := (hcx _).1 hx
      have h1 : P.E.skeleton (emb j0) ∈ Set.range (P.E.map (Lab83.chartEmb emb T)) := by
        rw [← hset, hj0]
        exact ⟨_, ⟨x, rfl⟩, rfl⟩
      obtain ⟨y, hy⟩ := Lab83.skeleton_mem_range (E := P.E) (Lab83.chartEmb emb T) h1
      refine ⟨y, (P.E.map (Lab83.chartEmb emb T)).injective ?_⟩
      rw [hε x, P.E.skeleton_natural, hy]
      exact hj0.symm
  · intro x x' p p' hp hp'
    have h1 := hε x
    rw [hp, P.E.skeleton_natural] at h1
    have h2 := hε x'
    rw [hp', P.E.skeleton_natural] at h2
    constructor
    · intro hpp
      exact (hlt _ _).2 ⟨p.1, p'.1, hpp, h1, h2⟩
    · intro hl
      obtain ⟨j1, j2, h12, e1, e2⟩ := (hlt _ _).1 hl
      have f1 : j1 = p.1 := emb.injective (P.E.skeleton.injective (e1.trans h1.symm))
      have f2 : j2 = p'.1 := emb.injective (P.E.skeleton.injective (e2.trans h2.symm))
      show p.1 < p'.1
      rw [← f1, ← f2]
      exact h12
  · intro m a xs x hx
    have hmem : ∀ i, g (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K))
          ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) (xs i) :
          (Hull83.witB hc k).M) ∈ Set.range (P.E.map emb) := fun i => by
      have h1 := congrFun (congrArg (⇑) (P.E.map_comp
        (OrderEmbedding.subtype (fun j => j ∈ Lab83.chart emb T)) emb)) (ε (xs i))
      exact ⟨_, h1.symm.trans (hε (xs i))⟩
    apply (P.E.map (Lab83.chartEmb emb T)).injective
    rw [hε x, ← Lab83.labFun_map]
    simp only [hε]
    show g _ = _
    rw [hx]
    exact hlab a _ hmem


/-- **`Y_k ≅ F(Z_k)` sends coordinates to skeleton points**: the `τ`-isomorphism of the
`Y`-piece onto `F(Z_k)` maps the hull element of the `a`-th `Z`-coordinate to the skeleton
point of an injectively chosen `z a ∈ Z_k`. -/
theorem infra_83_pairMS2_Y_pieces_coord (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ),
      (∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm)) ∧
      ∀ k : ℕ,
        ∃ (Z : Type u) (_ : LinearOrder Z) (_ : Nonempty Z) (H : Set Z) (_ : Nonempty H)
          (ε : (Hull83.subHullModel (psiM P.E Pr.n)
            ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
            ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc))).carrier ↪[K.τ]
            (P.E.obj H).carrier) (zH : Fin (k + 1) → H),
          Function.Bijective ε ∧ Function.Injective zH ∧
          ∀ x a, Hull83.subHullEmb (psiM P.E Pr.n)
              ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
              ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)) x =
              (Hull83.witB hc k).v (a, 1) →
            ε x = P.E.skeleton (zH a) := by
  obtain ⟨c, hc, hcoh, hθ, hρ⟩ := infra_83_pairMS2_coherent_colors P Pr
  refine ⟨c, hc, hcoh, fun k => ?_⟩
  obtain ⟨Z, Jp, i1, i2, i3, i4, e₀, g, hY, hch, hcy, hXY, hτf, hτr, -⟩ := (Hull83.witB hc k).mem.2
  have hv : ∀ p : Fin (k + 1) × Fin 2,
      g (((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)) p) ∈
        Set.range e₀ := by
    rintro ⟨a, b⟩
    fin_cases b
    · exact hXY _ ((thetaM_zero _ _ _).1 (Hull83.witB_realize hc hθ k a 0))
    · obtain ⟨z, hz⟩ := (hcy _).1 ((thetaM_one _ _ _).1 (Hull83.witB_realize hc hθ k a 1))
      exact ⟨_, hz⟩
  have hpt : ∀ a : Fin (k + 1), ∃ z, e₀ (P.E.skeleton z) = g ((Hull83.witB hc k).v (a, 1)) :=
    fun a => (hcy _).1 ((thetaM_one _ _ _).1 (Hull83.witB_realize hc hθ k a 1))
  choose z hz using hpt
  obtain ⟨T, hne, hset⟩ := yHull_eq_chart P.E Pr.n e₀ g hY hch
    ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)) hv (0, 1) (z 0) (hz 0)
  let f := (sampleEmb P.E Pr.n g hτf hτr).comp
    (Hull83.subHullEmb (psiM P.E Pr.n)
      ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
      ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)))
  let h := e₀.comp (P.E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T)))
  have hrange : Set.range f = Set.range h := by
    have h2 : Set.range h =
        Set.range (e₀ ∘ P.E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T))) :=
      rfl
    rw [h2, ← hset]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  obtain ⟨ε, hbij, hε⟩ := emb_equiv_of_range f h hrange
  have hmem : ∀ a : Fin (k + 1), z a ∈ Lab83.chartT e₀ T := fun a => by
    have h1 : e₀ (P.E.skeleton (z a)) ∈ Set.range h := by
      rw [← hrange, hz a]
      exact ⟨Quotient.mk _ (Term.var (a, 1)), rfl⟩
    obtain ⟨y, hy⟩ := h1
    have hy' : P.E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T)) y =
        P.E.skeleton (z a) := e₀.injective hy
    obtain ⟨w, hw⟩ := Lab83.skeleton_mem_range (E := P.E)
      (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T)) ⟨y, hy'⟩
    exact hw ▸ w.2
  refine ⟨Z, i1, i2, _, hne, ε, fun a => ⟨z a, hmem a⟩, hbij, ?_, ?_⟩
  · intro a b hab
    have h2 : z a = z b := congrArg Subtype.val hab
    have h3 := (hz a).symm.trans ((congrArg (fun w => e₀ (P.E.skeleton w)) h2).trans (hz b))
    exact (Hull83.witB hc k).inj 1 (g.injective h3)
  · intro x a hx
    apply (P.E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T))).injective
    apply e₀.injective
    have h4 : h (ε x) = f x := hε x
    refine h4.trans ?_
    rw [P.E.skeleton_natural]
    exact (congrArg g hx).trans (hz a).symm

/-- The coordinate chart of one `Y`-piece, for given colors recording `thetaM`. -/
theorem pairMS2_Y_coord_of (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme)
    {c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m}
    (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
    (hθ : ∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin 3),
        (thetaM P.E Pr.n i).relabel (fun _ => (a, i)) ∈ c m hm)
    (hρ : ∀ (m : ℕ) (hm : 0 < m) (a b : Fin m), a < b → ∀ i : Fin 3,
        (rhoM P.E Pr.n i).relabel ![(a, i), (b, i)] ∈ c m hm) (k : ℕ) :
        ∃ (Z : Type u) (_ : LinearOrder Z) (_ : Nonempty Z) (H : Set Z) (_ : Nonempty H)
          (ε : (Hull83.subHullModel (psiM P.E Pr.n)
            ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
            ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc))).carrier ↪[K.τ]
            (P.E.obj H).carrier) (zH : Fin (k + 1) → H),
          Function.Bijective ε ∧ Function.Injective zH ∧ StrictMono zH ∧
          ∀ x a, Hull83.subHullEmb (psiM P.E Pr.n)
              ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
              ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)) x =
              (Hull83.witB hc k).v (a, 1) →
            ε x = P.E.skeleton (zH a) := by
  obtain ⟨Z, Jp, i1, i2, i3, i4, e₀, g, hY, hch, hcy, hXY, hτf, hτr, hlt⟩ := (Hull83.witB hc k).mem.2
  have hv : ∀ p : Fin (k + 1) × Fin 2,
      g (((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)) p) ∈
        Set.range e₀ := by
    rintro ⟨a, b⟩
    fin_cases b
    · exact hXY _ ((thetaM_zero _ _ _).1 (Hull83.witB_realize hc hθ k a 0))
    · obtain ⟨z, hz⟩ := (hcy _).1 ((thetaM_one _ _ _).1 (Hull83.witB_realize hc hθ k a 1))
      exact ⟨_, hz⟩
  have hpt : ∀ a : Fin (k + 1), ∃ z, e₀ (P.E.skeleton z) = g ((Hull83.witB hc k).v (a, 1)) :=
    fun a => (hcy _).1 ((thetaM_one _ _ _).1 (Hull83.witB_realize hc hθ k a 1))
  choose z hz using hpt
  obtain ⟨T, hne, hset⟩ := yHull_eq_chart P.E Pr.n e₀ g hY hch
    ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)) hv (0, 1) (z 0) (hz 0)
  let f := (sampleEmb P.E Pr.n g hτf hτr).comp
    (Hull83.subHullEmb (psiM P.E Pr.n)
      ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
      ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)))
  let h := e₀.comp (P.E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T)))
  have hrange : Set.range f = Set.range h := by
    have h2 : Set.range h =
        Set.range (e₀ ∘ P.E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T))) :=
      rfl
    rw [h2, ← hset]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  obtain ⟨ε, hbij, hε⟩ := emb_equiv_of_range f h hrange
  have hmem : ∀ a : Fin (k + 1), z a ∈ Lab83.chartT e₀ T := fun a => by
    have h1 : e₀ (P.E.skeleton (z a)) ∈ Set.range h := by
      rw [← hrange, hz a]
      exact ⟨Quotient.mk _ (Term.var (a, 1)), rfl⟩
    obtain ⟨y, hy⟩ := h1
    have hy' : P.E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T)) y =
        P.E.skeleton (z a) := e₀.injective hy
    obtain ⟨w, hw⟩ := Lab83.skeleton_mem_range (E := P.E)
      (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T)) ⟨y, hy'⟩
    exact hw ▸ w.2
  refine ⟨Z, i1, i2, _, hne, ε, fun a => ⟨z a, hmem a⟩, hbij, ?_, ?_, ?_⟩
  · intro a b hab
    have h2 : z a = z b := congrArg Subtype.val hab
    have h3 := (hz a).symm.trans ((congrArg (fun w => e₀ (P.E.skeleton w)) h2).trans (hz b))
    exact (Hull83.witB hc k).inj 1 (g.injective h3)
  · intro a b hab
    obtain ⟨z1, z2, h12, h1, h2⟩ := (hlt _ _).1
      ((rhoM_one _ _ _ _).1 (Hull83.witB_realize2 hc hρ k hab 1))
    have e1 : z1 = z a := P.E.skeleton.injective (e₀.injective (h1.trans (hz a).symm))
    have e2 : z2 = z b := P.E.skeleton.injective (e₀.injective (h2.trans (hz b).symm))
    show z a < z b
    rw [← e1, ← e2]
    exact h12
  · intro x a hx
    apply (P.E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT e₀ T))).injective
    apply e₀.injective
    have h4 : h (ε x) = f x := hε x
    refine h4.trans ?_
    rw [P.E.skeleton_natural]
    exact (congrArg g hx).trans (hz a).symm

/-- A chart of a finite piece `A` over `k + 1` coordinates: a `τ`-isomorphism onto `F(H)` for
some `H ⊆ J`, with an injective, strictly increasing coordinate map into `H`. -/
structure PieceChart (E : OrderPresentation K) (A : Model K.τ) (k : ℕ) where
  J : Type u
  [lo : LinearOrder J]
  [ne : Nonempty J]
  H : Set J
  [hne : Nonempty H]
  ε : A.carrier ↪[K.τ] (E.obj H).carrier
  bij : Function.Bijective ε
  j : Fin (k + 1) → H
  inj : Function.Injective j
  mono : StrictMono j

attribute [instance] PieceChart.lo PieceChart.ne PieceChart.hne

/-- **Coherent coordinate charts of the `X`-pieces**: in the pair template over `X`- and
`Y`-sample-like structures, the `X`-pieces carry charts `ε_k : X_k ≅ F(H_k)` sending the
`a`-th coordinate to the skeleton point `j_k a`, and the piece map of `e` sends the
`a`-th coordinate to the element charted by `j_l (e a)`. -/
theorem infra_83_pairMS2_X_charts_coherent (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3))
        hXs).obj k) k),
      ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) x (a : Fin (k + 1)),
        Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K))
          ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x =
          (Hull83.witB hc k).v (a, 0) →
        (ch k).ε x = P.E.skeleton ((ch k).j a) ∧
        (ch l).ε ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3))
          hXs).map e x) = P.E.skeleton ((ch l).j (e a)) := by
  obtain ⟨c, hc, hcoh, hθ, hρ⟩ := infra_83_pairMS2_coherent_colors P Pr
  have hXs : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
      ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N) :=
    fun M _ hM => pairM_subHullStrongX P.E Pr.n M hM.1.1
  have hk := fun k => pairMS2_X_coord_of P Pr hc hθ hρ k
  choose J lo ne H hne ε jH hb hi hmo hcoord hsk hord hlb using hk
  refine ⟨c, hc, hcoh, hXs, fun k =>
    { J := J k, lo := lo k, ne := ne k, H := H k, hne := hne k, ε := ε k, bij := hb k,
      j := jH k, inj := hi k, mono := hmo k }, fun {k l} e x a hx => ⟨hcoord k x a hx, ?_⟩⟩
  exact hcoord l _ (e a)
    (Hull83.subLangPieces_coord _ _ hc hcoh _ hXs e x a 0 hx)

/-- **Coherent coordinate charts of the `Y`-pieces** (`Z`-coordinates), as
`infra_83_pairMS2_X_charts_coherent`. -/
theorem infra_83_pairMS2_Y_charts_coherent (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hYs : Hull83.SubHullStrong (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
        (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh
        (fun i : Fin 2 => i.castSucc) hYs).obj k) k),
      ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) x (a : Fin (k + 1)),
        Hull83.subHullEmb (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
          ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc)) x =
          (Hull83.witB hc k).v (a, 1) →
        (ch k).ε x = P.E.skeleton ((ch k).j a) ∧
        (ch l).ε ((Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh
          (fun i : Fin 2 => i.castSucc) hYs).map e x) = P.E.skeleton ((ch l).j (e a)) := by
  obtain ⟨c, hc, hcoh, hθ, hρ⟩ := infra_83_pairMS2_coherent_colors P Pr
  have hYs : Hull83.SubHullStrong (psiM P.E Pr.n)
      ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
      (fun N _ => pairMAdmittedS2 P.E Pr.n N) :=
    fun M _ hM => pairM_subHullStrongY P.E Pr.n M hM.1.1
  have hk := fun k => pairMS2_Y_coord_of P Pr hc hθ hρ k
  choose Z lo ne H hne ε zH hb hi hmo hcoord using hk
  refine ⟨c, hc, hcoh, hYs, fun k =>
    { J := Z k, lo := lo k, ne := ne k, H := H k, hne := hne k, ε := ε k, bij := hb k,
      j := zH k, inj := hi k, mono := hmo k }, fun {k l} e x a hx => ⟨hcoord k x a hx, ?_⟩⟩
  exact hcoord l _ (e a)
    (Hull83.subLangPieces_coord _ _ hc hcoh _ hYs e x a 1 hx)

/-- **Transported piece maps of the `X`-charts form a functor**: with
`θ_e := ε_l ∘ F_X(e) ∘ ε_k⁻¹ : F(H_k) → F(H_l)`, each `θ_e` is injective and sends the skeleton
point of `j_k a` to that of `j_l (e a)`, `θ_id = id`, and `θ_{e ≫ f} = θ_f ∘ θ_e`; each
`θ_e` is a strong `τ`-embedding. -/
theorem infra_83_pairMS2_X_chart_maps (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3))
        hXs).obj k) k)
      (θ : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) →
        (P.E.obj (ch k).H).carrier ↪[K.τ] (P.E.obj (ch l).H).carrier),
      (∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)), Function.Injective (θ e)) ∧
      (∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)), K.Strong (θ e)) ∧
      (∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) x,
        θ e ((ch k).ε x) = (ch l).ε ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3))
          hXs).map e x)) ∧
      (∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (a : Fin (k + 1)),
        θ e (P.E.skeleton ((ch k).j a)) = P.E.skeleton ((ch l).j (e a))) ∧
      (∀ (k : ℕ) (y : (P.E.obj (ch k).H).carrier), θ (idEmb (α := Fin (k + 1))) y = y) ∧
      ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1))
        (y : (P.E.obj (ch k).H).carrier), θ (e.trans f) y = θ f (θ e y) := by
  obtain ⟨c, hc, hcoh, hXs, ch, hch⟩ := infra_83_pairMS2_X_charts_coherent P Pr
  let FX := Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
    ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs
  let eq : ∀ k, (FX.obj k).carrier ≃[K.τ] (P.E.obj (ch k).H).carrier := fun k =>
    embeddingEquivOfSurjective (ch k).ε (ch k).bij.2
  let inv : ∀ k, (P.E.obj (ch k).H).carrier ↪[K.τ] (FX.obj k).carrier := fun k =>
    (eq k).symm.toEmbedding
  have hinvR : ∀ k y, (ch k).ε (inv k y) = y := fun k y => (eq k).apply_symm_apply y
  have hεs : ∀ k, K.Strong (ch k).ε := fun k => strong_of_equiv K (eq k) (FX.mem k)
  have hinvs : ∀ k, K.Strong (inv k) := fun k => strong_of_equiv K (eq k).symm
    (K.strong_mem_dom _ (P.E.map_strong (OrderIso.refl (ch k).H).toOrderEmbedding))
  have hinvL : ∀ k x, inv k ((ch k).ε x) = x := fun k x => (ch k).bij.1 (hinvR k _)
  refine ⟨c, hc, hcoh, hXs, ch, fun {k l} e => (ch l).ε.comp ((FX.map e).comp (inv k)),
    fun {k l} e y y' h => ?_,
    fun {k l} e => K.strong_trans _ _ (K.strong_trans _ _ (hinvs k) (FX.strong e)) (hεs l),
    fun {k l} e x => by
      show (ch l).ε (FX.map e (inv k ((ch k).ε x))) = _
      rw [hinvL],
    fun {k l} e a => ?_, fun k y => ?_, fun {k l m} e f y => ?_⟩
  · have := FX.map e |>.injective ((ch l).bij.1 h)
    exact (hinvR k y).symm.trans ((congrArg (ch k).ε this).trans (hinvR k y'))
  · obtain ⟨x, hx⟩ := (ch k).bij.2 (P.E.skeleton ((ch k).j a))
    have hcx : Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K))
        ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))
        (@Quotient.mk _ (@Hull83.hullSetoid _ _ (((psiM P.E Pr.n).comp (chiM P.E Pr.n)).reduct _) _
          ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3)))) (Term.var (a, 0))) =
        (Hull83.witB hc k).v (a, 0) := rfl
    have h1 := (hch e _ a hcx).1
    show (ch l).ε (FX.map e (inv k _)) = _
    rw [← h1]; erw [hinvL]
    exact (hch e _ a hcx).2
  · show (ch k).ε (FX.map _ (inv k y)) = y
    rw [FX.map_refl]
    exact hinvR k y
  · show (ch m).ε (FX.map (e.trans f) (inv k y)) =
      (ch m).ε (FX.map f (inv l ((ch l).ε (FX.map e (inv k y)))))
    rw [hinvL, FX.map_trans]
    rfl

/-- **Transported piece maps of the `Y`-charts form a functor**: with
`θ_e := ε_l ∘ F_Y(e) ∘ ε_k⁻¹ : F(H_k) → F(H_l)`, each `θ_e` is injective and sends the skeleton
point of `j_k a` to that of `j_l (e a)`, `θ_id = id`, and `θ_{e ≫ f} = θ_f ∘ θ_e`; each
`θ_e` is a strong `τ`-embedding. -/
theorem infra_83_pairMS2_Y_chart_maps (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
        (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh
        (fun i : Fin 2 => i.castSucc) hXs).obj k) k)
      (θ : ∀ {k l : ℕ}, (Fin (k + 1) ↪o Fin (l + 1)) →
        (P.E.obj (ch k).H).carrier ↪[K.τ] (P.E.obj (ch l).H).carrier),
      (∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)), Function.Injective (θ e)) ∧
      (∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)), K.Strong (θ e)) ∧
      (∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) x,
        θ e ((ch k).ε x) = (ch l).ε ((Hull83.subLangPieces (psiM P.E Pr.n)
          ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh
          (fun i : Fin 2 => i.castSucc) hXs).map e x)) ∧
      (∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (a : Fin (k + 1)),
        θ e (P.E.skeleton ((ch k).j a)) = P.E.skeleton ((ch l).j (e a))) ∧
      (∀ (k : ℕ) (y : (P.E.obj (ch k).H).carrier), θ (idEmb (α := Fin (k + 1))) y = y) ∧
      ∀ {k l m : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) (f : Fin (l + 1) ↪o Fin (m + 1))
        (y : (P.E.obj (ch k).H).carrier), θ (e.trans f) y = θ f (θ e y) := by
  obtain ⟨c, hc, hcoh, hXs, ch, hch⟩ := infra_83_pairMS2_Y_charts_coherent P Pr
  let FX := Hull83.subLangPieces (psiM P.E Pr.n)
    ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh
    (fun i : Fin 2 => i.castSucc) hXs
  let eq : ∀ k, (FX.obj k).carrier ≃[K.τ] (P.E.obj (ch k).H).carrier := fun k =>
    embeddingEquivOfSurjective (ch k).ε (ch k).bij.2
  let inv : ∀ k, (P.E.obj (ch k).H).carrier ↪[K.τ] (FX.obj k).carrier := fun k =>
    (eq k).symm.toEmbedding
  have hinvR : ∀ k y, (ch k).ε (inv k y) = y := fun k y => (eq k).apply_symm_apply y
  have hεs : ∀ k, K.Strong (ch k).ε := fun k => strong_of_equiv K (eq k) (FX.mem k)
  have hinvs : ∀ k, K.Strong (inv k) := fun k => strong_of_equiv K (eq k).symm
    (K.strong_mem_dom _ (P.E.map_strong (OrderIso.refl (ch k).H).toOrderEmbedding))
  have hinvL : ∀ k x, inv k ((ch k).ε x) = x := fun k x => (ch k).bij.1 (hinvR k _)
  refine ⟨c, hc, hcoh, hXs, ch, fun {k l} e => (ch l).ε.comp ((FX.map e).comp (inv k)),
    fun {k l} e y y' h => ?_,
    fun {k l} e => K.strong_trans _ _ (K.strong_trans _ _ (hinvs k) (FX.strong e)) (hεs l),
    fun {k l} e x => by
      show (ch l).ε (FX.map e (inv k ((ch k).ε x))) = _
      rw [hinvL],
    fun {k l} e a => ?_, fun k y => ?_, fun {k l m} e f y => ?_⟩
  · have := FX.map e |>.injective ((ch l).bij.1 h)
    exact (hinvR k y).symm.trans ((congrArg (ch k).ε this).trans (hinvR k y'))
  · obtain ⟨x, hx⟩ := (ch k).bij.2 (P.E.skeleton ((ch k).j a))
    have hcx : Hull83.subHullEmb (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
        ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc))
        (@Quotient.mk _ (@Hull83.hullSetoid _ _ ((psiM P.E Pr.n).reduct _) _
          ((Hull83.witB hc k).v ∘ Prod.map id (fun i : Fin 2 => i.castSucc))) (Term.var (a, 1))) =
        (Hull83.witB hc k).v (a, 1) := rfl
    have h1 := (hch e _ a hcx).1
    show (ch l).ε (FX.map e (inv k _)) = _
    rw [← h1]; erw [hinvL]
    exact (hch e _ a hcx).2
  · show (ch k).ε (FX.map _ (inv k y)) = y
    rw [FX.map_refl]
    exact hinvR k y
  · show (ch m).ε (FX.map (e.trans f) (inv k y)) =
      (ch m).ε (FX.map f (inv l ((ch l).ε (FX.map e (inv k y)))))
    rw [hinvL, FX.map_trans]
    rfl

/-- **The `X`-pieces are naturally isomorphic to chart pieces `k ↦ F(H_k)`**: a piece functor
`F_X^c` with values `F(H_k)` and a strong natural `PiecesHom F_X → F_X^c` that is bijective in
every arity (componentwise the charts `ε_k`); hence the induced maps of EM values
`F_X(I) → F_X^c(I)` are strong and bijective. -/
theorem infra_83_pairMS2_X_chart_pieces (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3))
        hXs).obj k) k)
      (FXc : EM83.FinPieces K)
      (η : EM83.PiecesHom (Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3))
        hXs) FXc),
      (∀ k, FXc.obj k = P.E.obj (ch k).H) ∧ (∀ k, Function.Bijective (η.app k)) ∧
      ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        Function.Bijective (η.limMap I) ∧ K.Strong (η.limMap I) := by
  obtain ⟨c, hc, hcoh, hXs, ch, θ, -, hs, hnat, -, hid, hcomp⟩ :=
    infra_83_pairMS2_X_chart_maps P Pr
  let FXc : EM83.FinPieces K :=
    { obj := fun k => P.E.obj (ch k).H
      mem := fun k => K.strong_mem_dom _ (P.E.map_strong (OrderIso.refl (ch k).H).toOrderEmbedding)
      map := fun e => θ e
      map_refl := fun k => by ext y; exact hid k y
      map_trans := fun e f => by ext y; exact hcomp e f y
      strong := fun e => hs e }
  refine ⟨c, hc, hcoh, hXs, ch, FXc,
    { app := fun k => (ch k).ε
      strong := fun k => strong_of_equiv K (embeddingEquivOfSurjective (ch k).ε (ch k).bij.2)
        ((Hull83.subLangPieces _ _ hc hcoh _ hXs).mem k)
      natural := fun e => by ext x; exact (hnat e x).symm }, fun _ => rfl, fun k => (ch k).bij,
    fun I _ _ => ⟨EM83.PiecesHom.limMap_bijective _ I (fun k => (ch k).bij.2),
      EM83.PiecesHom.limMap_strong _ I⟩⟩

/-- **The `Y`-pieces are naturally isomorphic to chart pieces `k ↦ F(H_k)`**: a piece functor
`F_Y^c` with values `F(H_k)` and a strong natural `PiecesHom F_Y → F_Y^c` that is bijective in
every arity (componentwise the charts `ε_k`); hence the induced maps of EM values
`F_Y(I) → F_Y^c(I)` are strong and bijective. -/
theorem infra_83_pairMS2_Y_chart_pieces (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K)))
        (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh
        (fun i : Fin 2 => i.castSucc) hXs).obj k) k)
      (FXc : EM83.FinPieces K)
      (η : EM83.PiecesHom (Hull83.subLangPieces (psiM P.E Pr.n)
        ((chiM P.E Pr.n).comp ((LS83.pairInlR P.E).comp (LS83.lsInl K))) hc hcoh
        (fun i : Fin 2 => i.castSucc) hXs) FXc),
      (∀ k, FXc.obj k = P.E.obj (ch k).H) ∧ (∀ k, Function.Bijective (η.app k)) ∧
      ∀ (I : Type u) [LinearOrder I] [Nonempty I],
        Function.Bijective (η.limMap I) ∧ K.Strong (η.limMap I) := by
  obtain ⟨c, hc, hcoh, hXs, ch, θ, -, hs, hnat, -, hid, hcomp⟩ :=
    infra_83_pairMS2_Y_chart_maps P Pr
  let FXc : EM83.FinPieces K :=
    { obj := fun k => P.E.obj (ch k).H
      mem := fun k => K.strong_mem_dom _ (P.E.map_strong (OrderIso.refl (ch k).H).toOrderEmbedding)
      map := fun e => θ e
      map_refl := fun k => by ext y; exact hid k y
      map_trans := fun e f => by ext y; exact hcomp e f y
      strong := fun e => hs e }
  refine ⟨c, hc, hcoh, hXs, ch, FXc,
    { app := fun k => (ch k).ε
      strong := fun k => strong_of_equiv K (embeddingEquivOfSurjective (ch k).ε (ch k).bij.2)
        ((Hull83.subLangPieces _ _ hc hcoh _ hXs).mem k)
      natural := fun e => by ext x; exact (hnat e x).symm }, fun _ => rfl, fun k => (ch k).bij,
    fun I _ _ => ⟨EM83.PiecesHom.limMap_bijective _ I (fun k => (ch k).bij.2),
      EM83.PiecesHom.limMap_strong _ I⟩⟩

/-- **The `X`-piece maps send chart skeleton points to chart skeleton points, in order**: in the
coherent charts, if `ε_k x` is the skeleton point of `p ∈ H_k` then `ε_l (F_X(e) x)` is the
skeleton point of some `q ∈ H_l`, and for two such points `p < p' ↔ q < q'`. -/
theorem infra_83_pairMS2_X_chart_skeleton (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).obj k) k),
      (∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) x (p : (ch k).H),
        (ch k).ε x = P.E.skeleton p → ∃ q : (ch l).H, (ch l).ε ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map e x) = P.E.skeleton q) ∧
      ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) x x' (p p' : (ch k).H) (q q' : (ch l).H),
        (ch k).ε x = P.E.skeleton p → (ch k).ε x' = P.E.skeleton p' →
        (ch l).ε ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map e x) = P.E.skeleton q →
        (ch l).ε ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map e x') = P.E.skeleton q' → (p < p' ↔ q < q') := by
  obtain ⟨c, hc, hcoh, hθ, hρ⟩ := infra_83_pairMS2_coherent_colors P Pr
  have hXs : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
      ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N) :=
    fun M _ hM => pairM_subHullStrongX P.E Pr.n M hM.1.1
  have hk := fun k => pairMS2_X_coord_of P Pr hc hθ hρ k
  choose J lo ne H hne ε jH hb hi hmo hcoord hsk hord hlb using hk
  have hX1 : ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) x,
      chartXM (M := (Hull83.witB hc k).M) P.E Pr.n (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K))
        ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x :
        (Hull83.witB hc k).M) ↔
      chartXM (M := (Hull83.witB hc l).M) P.E Pr.n (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K))
        ((Hull83.witB hc l).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map e x) :
        (Hull83.witB hc l).M) := by
    intro k l e x
    have h := Hull83.subLangPieces_rel _ _ hc hcoh _ hXs e
      (Sum.inr (Sum.inl ⟨⟨0⟩, rfl⟩) : (LS83.pairLangM3 P.E Pr.n).Relations 1) ![x]
    unfold chartXM
    refine (iff_of_eq (congrArg _ (funext fun i => ?_))).trans (h.trans
      (iff_of_eq (congrArg _ (funext fun i => ?_))))
    · fin_cases i; rfl
    · fin_cases i; rfl
  have hX2 : ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)) x x',
      chartLtXM (M := (Hull83.witB hc k).M) P.E Pr.n (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K))
        ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x :
        (Hull83.witB hc k).M) (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K))
        ((Hull83.witB hc k).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) x' :
        (Hull83.witB hc k).M) ↔
      chartLtXM (M := (Hull83.witB hc l).M) P.E Pr.n (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K))
        ((Hull83.witB hc l).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map e x) :
        (Hull83.witB hc l).M)
        (Hull83.subHullEmb ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K))
        ((Hull83.witB hc l).v ∘ Prod.map id (fun _ : Fin 1 => (0 : Fin 3))) ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map e x') :
        (Hull83.witB hc l).M) := by
    intro k l e x x'
    have h := Hull83.subLangPieces_rel _ _ hc hcoh _ hXs e
      (Sum.inr (Sum.inr ⟨⟨0⟩, rfl⟩) : (LS83.pairLangM3 P.E Pr.n).Relations 2) ![x, x']
    unfold chartLtXM
    refine (iff_of_eq (congrArg _ (funext fun i => ?_))).trans (h.trans
      (iff_of_eq (congrArg _ (funext fun i => ?_))))
    · fin_cases i <;> rfl
    · fin_cases i <;> rfl
  refine ⟨c, hc, hcoh, hXs, fun k =>
    { J := J k, lo := lo k, ne := ne k, H := H k, hne := hne k, ε := ε k, bij := hb k,
      j := jH k, inj := hi k, mono := hmo k }, ?_, ?_⟩
  · intro k l e x p hp
    exact (hsk l _).2 ((hX1 e x).1 ((hsk k x).1 ⟨p, hp⟩))
  · intro k l e x x' p p' q q' hp hp' hq hq'
    exact (hord k x x' p p' hp hp').trans ((hX2 e x x').trans (hord l _ _ q q' hq hq').symm)

/-- **Induced chart order embeddings**: for every piece map `e` there is an order embedding
`h_e : H_k ↪o H_l` of the charts with `ε_l (F_X(e) x) = skeleton (h_e p)` whenever
`ε_k x = skeleton p`. -/
theorem infra_83_pairMS2_X_chart_orderEmb (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m)
      (hc : ∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS2 P.E Pr.n N) 3) n c κ)
      (hcoh : ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm))
      (hXs : Hull83.SubHullStrong ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) (fun N _ => pairMAdmittedS2 P.E Pr.n N))
      (ch : ∀ k, PieceChart P.E ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).obj k) k),
      ∀ {k l : ℕ} (e : Fin (k + 1) ↪o Fin (l + 1)), ∃ h : (ch k).H ↪o (ch l).H,
        ∀ x (p : (ch k).H), (ch k).ε x = P.E.skeleton p →
          (ch l).ε ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
        ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map e x) = P.E.skeleton (h p) := by
  obtain ⟨c, hc, hcoh, hXs, ch, hpt, hord⟩ := infra_83_pairMS2_X_chart_skeleton P Pr
  refine ⟨c, hc, hcoh, hXs, ch, fun {k l} e => ?_⟩
  have hx : ∀ p : (ch k).H, ∃ x, (ch k).ε x = P.E.skeleton p := fun p => (ch k).bij.2 _
  choose x hx using hx
  have hq : ∀ p : (ch k).H, ∃ q : (ch l).H, (ch l).ε ((Hull83.subLangPieces ((psiM P.E Pr.n).comp (chiM P.E Pr.n))
          ((LS83.pairInlR P.E).comp (LS83.lsInl K)) hc hcoh (fun _ : Fin 1 => (0 : Fin 3)) hXs).map e (x p)) =
      P.E.skeleton q := fun p => hpt e (x p) p (hx p)
  choose q hq using hq
  have hmono : StrictMono q := fun p p' hpp => (hord e _ _ p p' _ _ (hx p) (hx p') (hq p) (hq p')).1 hpp
  refine ⟨OrderEmbedding.ofStrictMono q hmono, fun y p hy => ?_⟩
  have : y = x p := (ch k).bij.1 (hy.trans (hx p).symm)
  subst this
  exact hq p

end AEC
