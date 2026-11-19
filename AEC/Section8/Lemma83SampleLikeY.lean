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
    ∀ {k} (r : K.τ.Relations k) (x : Fin k → N),
      (@Structure.RelMap _ _ ((tauRed E n).reduct N) k r x ↔ Structure.RelMap r (g ∘ x))

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
      ∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin 3),
        (thetaM P.E Pr.n i).relabel (fun _ => (a, i)) ∈ c m hm := by
  refine Hull83.tpB_coherent_colors_formula (thetaM P.E Pr.n) fun κ => ?_
  obtain ⟨μ, hθ, -, J, i1, i2, -, hJ, M, -, eX, -, -, ι, Jplus, i3, i4, emb, strip, hstrip, -,
    F, -, hF, s₀, hcl, hred, hX, hchX, hY, hchY, -⟩ :=
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
      fun r x => Iff.of_eq (congrArg (fun s' => @Structure.RelMap _ _ s' _ r x) hred)⟩,
     J, Jplus, i1, i2, i3, i4, e₀, Equiv.refl _, ?_, ?_, fun x => Iff.rfl, ?_,
      fun f x => congrArg (fun s' => @Structure.funMap _ _ s' _ f x) hred,
      fun r x => Iff.of_eq (congrArg (fun s' => @Structure.RelMap _ _ s' _ r x) hred)⟩,
    hJ ▸ hθ, jzwBundle (fun j => P.E.skeleton (emb j)) (fun j => F (ι (P.E.skeleton j)))
      (fun j => P.E.skeleton (e j).1), fun i => ?_, fun a i => ?_⟩
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
  obtain ⟨c, hc, hcoh, hθ⟩ := infra_83_pairMS2_coherent_colors P Pr
  refine ⟨c, hc, hcoh, fun k => ⟨?_, ?_⟩⟩
  · obtain ⟨J, Jp, i1, i2, i3, i4, emb, g, hX, hch, hcx, hτf, hτr⟩ := (Hull83.witB hc k).mem.1.2
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
  · obtain ⟨Z, Jp, i1, i2, i3, i4, e₀, g, hY, hch, hcy, hXY, hτf, hτr⟩ := (Hull83.witB hc k).mem.2
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

end AEC
