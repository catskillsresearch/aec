module

public import AEC.Section8.Lemma83PairTemplateR4
public import AEC.Section8.PairLangM83
public import AEC.Section8.Lemma83MarkValues

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: the template with the mark as designated terms

As `Lemma83PairTemplateR4`, with the mark constants (`Fin Pr.n`, interpreted by the sample's
mark in `Y`) in the `Y`-language `pairLangM2`, and the full language `pairLangM3`.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- The sublanguage maps of the marked chain. -/
abbrev chiM (E : OrderPresentation K) (n : ℕ) : LS83.pairLangR E →ᴸ LS83.pairLangM2 E n :=
  Language.LHom.sumInl

abbrev psiM (E : OrderPresentation K) (n : ℕ) : LS83.pairLangM2 E n →ᴸ LS83.pairLangM3 E n :=
  (Language.LHom.sumInl : (LS83.pairLangM2 E n).sum (Lab83.labLang E) →ᴸ LS83.pairLangM3 E n).comp
    Language.LHom.sumInl

abbrev pairMAdmitted (E : OrderPresentation K) (n : ℕ) (N : Type u)
    [(LS83.pairLangM3 E n).Structure N] : Prop :=
  @LS83.LSClosed K N ((LS83.pairInlM3 E n).reduct N)

theorem pairM_subHullStrongX (E : OrderPresentation K) (n : ℕ) :
    Hull83.SubHullStrong ((psiM E n).comp (chiM E n)) ((LS83.pairInlR E).comp (LS83.lsInl K))
      (fun N _ => pairMAdmitted E n N) :=
  fun M _ hM _ _ _ v =>
    @LS83.hullStrong_pairR K E M (((psiM E n).comp (chiM E n)).reduct M) hM _ _ _ v

theorem pairM_subHullStrongY (E : OrderPresentation K) (n : ℕ) :
    Hull83.SubHullStrong (psiM E n) ((chiM E n).comp ((LS83.pairInlR E).comp (LS83.lsInl K)))
      (fun N _ => pairMAdmitted E n N) :=
  fun M _ hM _ _ _ v =>
    @LS83.hullStrong_exp K _ ((chiM E n).comp (LS83.pairInlR E)) M ((psiM E n).reduct M) hM
      _ _ _ v

theorem pairM_hullStrong (E : OrderPresentation K) (n : ℕ) :
    Hull83.HullStrong ((psiM E n).comp ((chiM E n).comp ((LS83.pairInlR E).comp (LS83.lsInl K))))
      (fun N _ => pairMAdmitted E n N) :=
  LS83.hullStrong_pairM3 E n

/-- **Coherent colors with the mark as designated terms.** -/
theorem infra_83_pairM_coherent_colors (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmitted P.E Pr.n N) 3) n c κ) ∧
      ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm) := by
  refine Hull83.tpB_coherent_colors fun κ => ?_
  obtain ⟨μ, hθ, -, J, i1, i2, -, hJ, M, -, eX, -, -, ι, Jplus, i3, i4, emb, strip, hstrip, -,
    F, -, -, s₀, hcl, -⟩ := infra_83_pairR_samples P Pr (κ := ℵ₀) le_rfl κ
  obtain ⟨e⟩ : Nonempty (J ≃ strip) := Cardinal.eq.mp (hJ.trans hstrip.symm)
  refine ⟨J, i1, (P.E.obj Jplus).carrier, @Language.sumStructure _ _ _ (@Language.sumStructure _ _ _
      (@Language.sumStructure _ _ _ s₀ (@Language.sumStructure _ _ _ (@Language.sumStructure _ _ _
        (Lab83.labTStr (fun y => F (ι y))) (Lab83.repTStr (fun y => F (ι y))))
        (Mark83.markStr fun i => F (markY M i)))) Lab83.labStr)
      (Lab83.chartStr emb (fun y => F (ι y))), hcl,
    hJ ▸ hθ, jzwBundle (fun j => P.E.skeleton (emb j)) (fun j => F (ι (P.E.skeleton j)))
      (fun j => P.E.skeleton (e j).1), fun i => ?_⟩
  fin_cases i
  · exact P.E.skeleton.injective.comp emb.injective
  · exact F.injective.comp (ι.injective.comp P.E.skeleton.injective)
  · exact P.E.skeleton.injective.comp (Subtype.val_injective.comp e.injective)

/-- **The marked three-language template** with strongness: sort maps strong, order-embedding
maps strong on each sort and commuting with the sort maps. -/
theorem infra_83_pairM_template_strong (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (FX FY FL : EM83.FinPieces K) (ηXY : EM83.PiecesHom FX FY) (ηYL : EM83.PiecesHom FY FL)
      (E : OrderPresentation K),
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], E.obj I = (FL.limit I).obj) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I],
        K.Strong (ηXY.limMap I) ∧ K.Strong (ηYL.limMap I) ∧
          (ηYL.comp ηXY).limMap I = (ηYL.limMap I).comp (ηXY.limMap I)) ∧
      ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J] (f : I ↪o J),
        K.Strong (EM83.gEmMap (F := FX) f) ∧ K.Strong (EM83.gEmMap (F := FY) f) ∧
        K.Strong (EM83.gEmMap (F := FL) f) ∧
        (ηXY.limMap J).comp (EM83.gEmMap (F := FX) f) =
            (EM83.gEmMap (F := FY) f).comp (ηXY.limMap I) ∧
          (ηYL.limMap J).comp (EM83.gEmMap (F := FY) f) =
            (EM83.gEmMap (F := FL) f).comp (ηYL.limMap I) := by
  obtain ⟨c, hc, hcoh⟩ := infra_83_pairM_coherent_colors P Pr
  let σ : Fin 2 → Fin 3 := fun i => i.castSucc
  let τ : Fin 1 → Fin 2 := fun _ => 0
  let φ₀ := (LS83.pairInlR P.E).comp (LS83.lsInl K)
  let ηXY := Hull83.subLangMixHom (chiM P.E Pr.n) (psiM P.E Pr.n) φ₀ hc hcoh σ τ
    (pairM_subHullStrongX P.E Pr.n) (pairM_subHullStrongY P.E Pr.n)
  let ηYL := Hull83.subLangChain (psiM P.E Pr.n) ((chiM P.E Pr.n).comp φ₀) hc hcoh σ
    (pairM_subHullStrongY P.E Pr.n) (pairM_hullStrong P.E Pr.n)
  exact ⟨_, _, _, ηXY, ηYL,
    Hull83.tpPresentationB hc hcoh (by norm_num) ((psiM P.E Pr.n).comp ((chiM P.E Pr.n).comp φ₀))
      (pairM_hullStrong P.E Pr.n) (LS83.pairLangM3_functions_le P.E Pr.n),
    fun I _ _ => rfl,
    fun I _ _ => ⟨ηXY.limMap_strong I, ηYL.limMap_strong I, EM83.PiecesHom.limMap_comp _ _ I⟩,
    fun f => ⟨EM83.gEmMap_strong f, EM83.gEmMap_strong f, EM83.gEmMap_strong f,
      ηXY.limMap_natural f, ηYL.limMap_natural f⟩⟩

end AEC
