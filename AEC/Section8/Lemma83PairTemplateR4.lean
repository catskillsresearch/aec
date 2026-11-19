module

public import AEC.Section8.Lemma83PairTemplateR
public import AEC.Section8.ChartRel83

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: the template with chart relations

As `Lemma83PairTemplateR`, with the full language `pairLangR4` adding the chart relations
(`X`- and `Y`-chart predicates and chart orders), so that the coherent colors record the charts.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- The admitted class of the samples with representation positions: LS-closed `lsLang K`-reduct. -/
abbrev pairR4Admitted (E : OrderPresentation K) (N : Type u) [(LS83.pairLangR4 E).Structure N] :
    Prop :=
  @LS83.LSClosed K N ((LS83.pairInlR4 E).reduct N)

/-- `X`-language hulls are strong in admitted samples with representation positions. -/
theorem pairR4_subHullStrongX (E : OrderPresentation K) :
    Hull83.SubHullStrong (((Language.LHom.sumInl : LS83.pairLangR3 E →ᴸ LS83.pairLangR4 E).comp
      (Language.LHom.sumInl : LS83.pairLangR2 E →ᴸ LS83.pairLangR3 E)).comp
      (Language.LHom.sumInl : LS83.pairLangR E →ᴸ LS83.pairLangR2 E))
      ((LS83.pairInlR E).comp (LS83.lsInl K)) (fun N _ => pairR4Admitted E N) :=
  fun M _ hM _ _ _ v =>
    @LS83.hullStrong_pairR K E M ((((Language.LHom.sumInl : LS83.pairLangR3 E →ᴸ LS83.pairLangR4 E).comp
      (Language.LHom.sumInl : LS83.pairLangR2 E →ᴸ LS83.pairLangR3 E)).comp
      (Language.LHom.sumInl : LS83.pairLangR E →ᴸ LS83.pairLangR2 E)).reduct M) hM _ _ _ v

/-- `Y`-language hulls are strong in admitted samples with representation positions. -/
theorem pairR4_subHullStrongY (E : OrderPresentation K) :
    Hull83.SubHullStrong ((Language.LHom.sumInl : LS83.pairLangR3 E →ᴸ LS83.pairLangR4 E).comp
      (Language.LHom.sumInl : LS83.pairLangR2 E →ᴸ LS83.pairLangR3 E))
      ((Language.LHom.sumInl : LS83.pairLangR E →ᴸ LS83.pairLangR2 E).comp
        ((LS83.pairInlR E).comp (LS83.lsInl K))) (fun N _ => pairR4Admitted E N) :=
  fun M _ hM _ _ _ v =>
    @LS83.hullStrong_pairR2 K E M
      (((Language.LHom.sumInl : LS83.pairLangR3 E →ᴸ LS83.pairLangR4 E).comp
      (Language.LHom.sumInl : LS83.pairLangR2 E →ᴸ LS83.pairLangR3 E)).reduct M) hM _ _ _ v

/-- Full-language hulls are strong in admitted samples with representation positions. -/
theorem pairR4_hullStrong (E : OrderPresentation K) :
    Hull83.HullStrong (((Language.LHom.sumInl : LS83.pairLangR3 E →ᴸ LS83.pairLangR4 E).comp
      (Language.LHom.sumInl : LS83.pairLangR2 E →ᴸ LS83.pairLangR3 E)).comp
      ((Language.LHom.sumInl : LS83.pairLangR E →ᴸ LS83.pairLangR2 E).comp
        ((LS83.pairInlR E).comp (LS83.lsInl K)))) (fun N _ => pairR4Admitted E N) :=
  LS83.hullStrong_pairR4 E

/-- **Coherent colors of the three-sort skeleton bundles in the three-copy pair language**
(`J`-skeleton in `X`, the `ι`-image of the `Z`-skeleton in `Y`, a strip skeleton in `L`). -/
theorem infra_83_pairR4_coherent_colors (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangR4 P.E) 3 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairR4Admitted P.E N) 3) n c κ) ∧
      ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm) := by
  refine Hull83.tpB_coherent_colors fun κ => ?_
  obtain ⟨μ, hθ, -, J, i1, i2, -, hJ, M, -, eX, -, -, ι, Jplus, i3, i4, emb, strip, hstrip, -,
    F, -, -, s₀, hcl, -⟩ := infra_83_pairR_samples P Pr (κ := ℵ₀) le_rfl κ
  obtain ⟨e⟩ : Nonempty (J ≃ strip) := Cardinal.eq.mp (hJ.trans hstrip.symm)
  refine ⟨J, i1, (P.E.obj Jplus).carrier, @Language.sumStructure _ _ _ (@Language.sumStructure _ _ _
      (@Language.sumStructure _ _ _ s₀ (@Language.sumStructure _ _ _ (Lab83.labTStr (fun y => F (ι y))) (Lab83.repTStr (fun y => F (ι y))))) Lab83.labStr)
      (Lab83.chartStr emb (fun y => F (ι y))), hcl,
    hJ ▸ hθ, jzwBundle (fun j => P.E.skeleton (emb j)) (fun j => F (ι (P.E.skeleton j)))
      (fun j => P.E.skeleton (e j).1), fun i => ?_⟩
  fin_cases i
  · exact P.E.skeleton.injective.comp emb.injective
  · exact F.injective.comp (ι.injective.comp P.E.skeleton.injective)
  · exact P.E.skeleton.injective.comp (Subtype.val_injective.comp e.injective)

/-- **The three-language pair template `X → Y → L`** (Lemma 8.3).  `F_X`: `X`-language hulls of
the `J`-coordinates; `F_Y`: `Y`-language hulls of the `J, Z`-coordinates; `F_L`: full hulls of
all coordinates; strong natural transformations `F_X → F_Y → F_L`, an order presentation of
`K` with values `F_L(I)`, and strong induced maps natural in order embeddings. -/
theorem infra_83_pairR4_template (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (FX FY FL : EM83.FinPieces K) (ηXY : EM83.PiecesHom FX FY) (ηYL : EM83.PiecesHom FY FL)
      (E : OrderPresentation K),
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], E.obj I = (FL.limit I).obj) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        K.Strong (ηXY.limMap I) ∧ K.Strong (ηYL.limMap I) ∧
          (ηYL.comp ηXY).limMap I = (ηYL.limMap I).comp (ηXY.limMap I)) ∧
      ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J] (f : I ↪o J),
        (ηXY.limMap J).comp (EM83.gEmMap (F := FX) f) =
            (EM83.gEmMap (F := FY) f).comp (ηXY.limMap I) ∧
          (ηYL.limMap J).comp (EM83.gEmMap (F := FY) f) =
            (EM83.gEmMap (F := FL) f).comp (ηYL.limMap I) := by
  obtain ⟨c, hc, hcoh⟩ := infra_83_pairR4_coherent_colors P Pr
  let σ : Fin 2 → Fin 3 := fun i => i.castSucc
  let τ : Fin 1 → Fin 2 := fun _ => 0
  let χ := (Language.LHom.sumInl : LS83.pairLangR P.E →ᴸ LS83.pairLangR2 P.E)
  let ψ₂ := ((Language.LHom.sumInl : LS83.pairLangR3 P.E →ᴸ LS83.pairLangR4 P.E).comp
      (Language.LHom.sumInl : LS83.pairLangR2 P.E →ᴸ LS83.pairLangR3 P.E))
  let φ₀ := (LS83.pairInlR P.E).comp (LS83.lsInl K)
  let ηXY := Hull83.subLangMixHom χ ψ₂ φ₀ hc hcoh σ τ (pairR4_subHullStrongX P.E)
    (pairR4_subHullStrongY P.E)
  let ηYL := Hull83.subLangChain ψ₂ (χ.comp φ₀) hc hcoh σ (pairR4_subHullStrongY P.E)
    (pairR4_hullStrong P.E)
  exact ⟨_, _, _, ηXY, ηYL,
    Hull83.tpPresentationB hc hcoh (by norm_num) (ψ₂.comp (χ.comp φ₀)) (pairR4_hullStrong P.E)
      (LS83.pairLangR4_functions_le P.E),
    fun I _ _ => rfl,
    fun I _ _ => ⟨ηXY.limMap_strong I, ηYL.limMap_strong I, EM83.PiecesHom.limMap_comp _ _ I⟩,
    fun f => ⟨ηXY.limMap_natural f, ηYL.limMap_natural f⟩⟩

/-- **Template strongness** (Lemma 8.3 proof, "The vertex LS witnesses prove `X_H → Y_H → L_H`
componentwise strong ... also for maps induced by order embeddings of `H`, including mixed
sizes"): for the three-language template, the sort maps are strong, the maps induced by any order
embedding `f : I ↪o J` (any sizes) are strong on each sort, and the sort maps commute with them. -/
theorem infra_83_pairR4_template_strong (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (FX FY FL : EM83.FinPieces K) (ηXY : EM83.PiecesHom FX FY) (ηYL : EM83.PiecesHom FY FL)
      (E : OrderPresentation K),
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], E.obj I = (FL.limit I).obj) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        K.Strong (ηXY.limMap I) ∧ K.Strong (ηYL.limMap I) ∧
          K.Strong ((ηYL.limMap I).comp (ηXY.limMap I))) ∧
      ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J] (f : I ↪o J),
        K.Strong (EM83.gEmMap (F := FX) f) ∧ K.Strong (EM83.gEmMap (F := FY) f) ∧
        K.Strong (EM83.gEmMap (F := FL) f) ∧
        (ηXY.limMap J).comp (EM83.gEmMap (F := FX) f) =
            (EM83.gEmMap (F := FY) f).comp (ηXY.limMap I) ∧
          (ηYL.limMap J).comp (EM83.gEmMap (F := FY) f) =
            (EM83.gEmMap (F := FL) f).comp (ηYL.limMap I) := by
  obtain ⟨FX, FY, FL, ηXY, ηYL, E, hE, hs, hn⟩ := infra_83_pairR4_template P Pr
  refine ⟨FX, FY, FL, ηXY, ηYL, E, hE, fun I _ _ => ⟨(hs I).1, (hs I).2.1, ?_⟩,
    fun f => ⟨EM83.gEmMap_strong f, EM83.gEmMap_strong f, EM83.gEmMap_strong f, hn f⟩⟩
  rw [← (hs I).2.2]
  exact (ηYL.comp ηXY).limMap_strong I

end AEC
