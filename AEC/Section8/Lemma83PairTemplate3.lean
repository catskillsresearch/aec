module

public import AEC.Section8.Lemma83PairSamples3
public import AEC.Section8.HullSubMix83
public import AEC.Section8.Lemma83PairTemplate

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: the three-language sort chain

`X_H` are hulls in `pairLang` (τ, LS witnesses, retractions, labels restricted to `X`), `Y_H`
hulls in `pairLang2` (plus the labels transported along `Y ≅ F(Z)`), `L_H` hulls in `pairLang3`
(plus the full labels).  The sort maps `X_H → Y_H → L_H` are strong and natural.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- The admitted class of the three-copy samples: LS-closed `lsLang K`-reduct. -/
abbrev pair3Admitted (E : OrderPresentation K) (N : Type u) [(LS83.pairLang3 E).Structure N] :
    Prop :=
  @LS83.LSClosed K N ((LS83.pairInl3 E).reduct N)

/-- `X`-language hulls are strong in admitted three-copy samples. -/
theorem pair3_subHullStrongX (E : OrderPresentation K) :
    Hull83.SubHullStrong ((Language.LHom.sumInl : LS83.pairLang2 E →ᴸ LS83.pairLang3 E).comp
      (Language.LHom.sumInl : LS83.pairLang E →ᴸ LS83.pairLang2 E))
      ((LS83.pairInl E).comp (LS83.lsInl K)) (fun N _ => pair3Admitted E N) :=
  fun M _ hM _ _ _ v =>
    @LS83.hullStrong_pair K E M (((Language.LHom.sumInl : LS83.pairLang2 E →ᴸ LS83.pairLang3 E).comp
      (Language.LHom.sumInl : LS83.pairLang E →ᴸ LS83.pairLang2 E)).reduct M) hM _ _ _ v

/-- `Y`-language hulls are strong in admitted three-copy samples. -/
theorem pair3_subHullStrongY (E : OrderPresentation K) :
    Hull83.SubHullStrong (Language.LHom.sumInl : LS83.pairLang2 E →ᴸ LS83.pairLang3 E)
      ((Language.LHom.sumInl : LS83.pairLang E →ᴸ LS83.pairLang2 E).comp
        ((LS83.pairInl E).comp (LS83.lsInl K))) (fun N _ => pair3Admitted E N) :=
  fun M _ hM _ _ _ v =>
    @LS83.hullStrong_pair2 K E M
      ((Language.LHom.sumInl : LS83.pairLang2 E →ᴸ LS83.pairLang3 E).reduct M) hM _ _ _ v

/-- Full-language hulls are strong in admitted three-copy samples. -/
theorem pair3_hullStrong (E : OrderPresentation K) :
    Hull83.HullStrong ((Language.LHom.sumInl : LS83.pairLang2 E →ᴸ LS83.pairLang3 E).comp
      ((Language.LHom.sumInl : LS83.pairLang E →ᴸ LS83.pairLang2 E).comp
        ((LS83.pairInl E).comp (LS83.lsInl K)))) (fun N _ => pair3Admitted E N) :=
  LS83.hullStrong_pair3 E

/-- **Coherent colors of the three-sort skeleton bundles in the three-copy pair language**
(`J`-skeleton in `X`, the `ι`-image of the `Z`-skeleton in `Y`, a strip skeleton in `L`). -/
theorem infra_83_pair3_coherent_colors (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLang3 P.E) 3 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pair3Admitted P.E N) 3) n c κ) ∧
      ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm) := by
  refine Hull83.tpB_coherent_colors fun κ => ?_
  obtain ⟨μ, hθ, -, J, i1, i2, -, hJ, M, -, eX, -, -, ι, Jplus, i3, i4, emb, strip, hstrip, -,
    F, -, -, s₀, hcl, -⟩ := infra_83_pair3_samples P Pr (κ := ℵ₀) le_rfl κ
  obtain ⟨e⟩ : Nonempty (J ≃ strip) := Cardinal.eq.mp (hJ.trans hstrip.symm)
  refine ⟨J, i1, (P.E.obj Jplus).carrier, @Language.sumStructure _ _ _
      (@Language.sumStructure _ _ _ s₀ (Lab83.labTStr (fun y => F (ι y)))) Lab83.labStr, hcl,
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
theorem infra_83_pair3_template (P : SingleModelData K)
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
  obtain ⟨c, hc, hcoh⟩ := infra_83_pair3_coherent_colors P Pr
  let σ : Fin 2 → Fin 3 := fun i => i.castSucc
  let τ : Fin 1 → Fin 2 := fun _ => 0
  let χ := (Language.LHom.sumInl : LS83.pairLang P.E →ᴸ LS83.pairLang2 P.E)
  let ψ₂ := (Language.LHom.sumInl : LS83.pairLang2 P.E →ᴸ LS83.pairLang3 P.E)
  let φ₀ := (LS83.pairInl P.E).comp (LS83.lsInl K)
  let ηXY := Hull83.subLangMixHom χ ψ₂ φ₀ hc hcoh σ τ (pair3_subHullStrongX P.E)
    (pair3_subHullStrongY P.E)
  let ηYL := Hull83.subLangChain ψ₂ (χ.comp φ₀) hc hcoh σ (pair3_subHullStrongY P.E)
    (pair3_hullStrong P.E)
  exact ⟨_, _, _, ηXY, ηYL,
    Hull83.tpPresentationB hc hcoh (by norm_num) (ψ₂.comp (χ.comp φ₀)) (pair3_hullStrong P.E)
      (LS83.pairLang3_functions_le P.E),
    fun I _ _ => rfl,
    fun I _ _ => ⟨ηXY.limMap_strong I, ηYL.limMap_strong I, EM83.PiecesHom.limMap_comp _ _ I⟩,
    fun f => ⟨ηXY.limMap_natural f, ηYL.limMap_natural f⟩⟩

end AEC
