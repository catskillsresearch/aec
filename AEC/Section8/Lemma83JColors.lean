module

public import AEC.Section8.Lemma83ExpSamples
public import AEC.Section8.LSPairLang83
public import AEC.Section8.HullBundle83
public import AEC.Section8.PairChain83

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: coherent colors of the `J`-skeleton in LS-expanded samples

The first sort of the pair samples: in the LS-expanded samples `L = F(J⁺)` of
`infra_83_ls_expanded_samples`, the skeleton of `J` (pushed along `J ↪ J⁺`, lying in
`X = F(J)`) is an injective sequence indexed by an arbitrarily large order.  The coherent type
colors of these sequences (`Hull83.tpB_coherent_colors`) exist, with arbitrarily large
homogeneous LS-closed samples.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Arbitrarily long `J`-skeleton sequences in LS-closed expanded samples.**  For every bound
`κ` there is an order `J` with `κ ≤ #J`, an LS-closed expansion of a sample `L = F(J⁺)`, and the
injective skeleton sequence `j ↦ skeleton (emb j) = F(emb)(skeleton j)`, whose entries lie in
the closed sort `X = range F(emb)`. -/
theorem infra_83_J_skeleton_large (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) (κ : Cardinal.{u}) :
    ∃ (J : Type u) (_ : LinearOrder J) (Jplus : Type u) (_ : LinearOrder Jplus)
      (_ : Nonempty Jplus) (emb : J ↪o Jplus) (_ : Nonempty J)
      (str : (LS83.lsLang K).Structure (P.E.obj Jplus).carrier),
      @LS83.LSClosed K _ str ∧ κ ≤ #J ∧
      (∀ j, P.E.skeleton (emb j) = P.E.map emb (P.E.skeleton j)) ∧
      Function.Injective (fun j => P.E.skeleton (emb j)) := by
  obtain ⟨μ, hθ, -, -, J, i1, i2, -, -, hJ, -, M, -, eX, -, -, -, Jplus, i3, i4, emb, -, -, -, -,
    -, -, -, -, -, -, str, -, hcl, -, -⟩ :=
    infra_83_ls_expanded_samples P Pr (κ := ℵ₀) le_rfl κ
  refine ⟨J, i1, Jplus, i3, i4, emb, i2, str, hcl, hJ ▸ hθ, fun j => ?_, ?_⟩
  · exact (P.E.skeleton_natural emb j).symm
  · exact P.E.skeleton.injective.comp emb.injective

/-- **Coherent colors of the `J`-skeleton** (one-sort bundles in the LS language): bundled
types at all positive arities, coherent under restriction, with arbitrarily large homogeneous
samples in LS-closed structures. -/
theorem infra_83_J_coherent_colors (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.lsLang K) 1 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => LS83.LSClosed (K := K) N) 1) n c κ) ∧
      ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 1 f (c m hm) := by
  refine Hull83.tpB_coherent_colors fun κ => ?_
  obtain ⟨J, i1, Jplus, i3, i4, emb, i2, str, hcl, hκ, -, hinj⟩ :=
    infra_83_J_skeleton_large P Pr κ
  exact ⟨J, i1, (P.E.obj Jplus).carrier, str, hcl, hκ,
    fun j _ => P.E.skeleton (emb j), fun _ => hinj⟩

/-- The two-sort bundle (`J`-skeleton in `X`, copy of the skeleton in `Y`). -/
def jzBundle {α M : Type u} (a b : α → M) : α → Fin 2 → M := fun j => ![a j, b j]

/-- **Arbitrarily long two-sort skeleton sequences** (sorts `J` and `Z` of the pair samples).
For every bound `κ` there are an order `J` with `κ ≤ #J`, an LS-closed expansion of a sample
`L = F(J⁺)` with closed sorts `X = range F(emb)` and `Y = range F_Y`, the injective
`J`-skeleton in `X`, and an injective sequence in `Y` (the skeleton of `F(Z)`, `Z = J`, carried
into `Y ≅ F(Z)` and on into `L`). -/
theorem infra_83_JZ_skeleton_large (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) (κ : Cardinal.{u}) :
    ∃ (J : Type u) (_ : LinearOrder J) (Jplus : Type u) (_ : LinearOrder Jplus)
      (_ : Nonempty Jplus) (emb : J ↪o Jplus) (_ : Nonempty J)
      (str : (LS83.lsLang K).Structure (P.E.obj Jplus).carrier)
      (y : J → (P.E.obj Jplus).carrier) (Ymap : Set (P.E.obj Jplus).carrier),
      @LS83.LSClosed K _ str ∧ κ ≤ #J ∧
      Function.Injective (fun j => P.E.skeleton (emb j)) ∧ Function.Injective y ∧
      (∀ j, P.E.skeleton (emb j) ∈ Set.range (P.E.map emb)) ∧ (∀ j, y j ∈ Ymap) ∧
      Set.range (P.E.map emb) ⊆ Ymap ∧
      (∀ {n} (f : (LS83.lsLang K).Functions n) (x : Fin n → (P.E.obj Jplus).carrier),
        (∀ i, x i ∈ Ymap) → @Language.Structure.funMap _ _ str n f x ∈ Ymap) := by
  obtain ⟨μ, hθ, -, -, J, i1, i2, -, -, hJ, -, M, -, eX, -, -, hZ, Jplus, i3, i4, emb, -, -, -, -,
    -, -, -, F, -, hF, str, -, hcl, -, hY⟩ :=
    infra_83_ls_expanded_samples P Pr (κ := ℵ₀) le_rfl κ
  obtain ⟨ι⟩ := hZ J hJ
  refine ⟨J, i1, Jplus, i3, i4, emb, i2, str, fun j => F (ι (P.E.skeleton j)), Set.range F, hcl,
    hJ ▸ hθ, P.E.skeleton.injective.comp emb.injective,
    F.injective.comp (ι.injective.comp P.E.skeleton.injective),
    fun j => ⟨P.E.skeleton j, P.E.skeleton_natural emb j⟩,
    fun j => ⟨_, rfl⟩, ?_, hY⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨_, hF x⟩

/-- **Coherent colors of the two-sort skeleton bundles** (`J` in `X`, `Z` in `Y`). -/
theorem infra_83_JZ_coherent_colors (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.lsLang K) 2 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => LS83.LSClosed (K := K) N) 2) n c κ) ∧
      ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 2 f (c m hm) := by
  refine Hull83.tpB_coherent_colors fun κ => ?_
  obtain ⟨J, i1, Jplus, i3, i4, emb, i2, str, y, Ymap, hcl, hκ, hinj, hy, -⟩ :=
    infra_83_JZ_skeleton_large P Pr κ
  refine ⟨J, i1, (P.E.obj Jplus).carrier, str, hcl, hκ,
    jzBundle (fun j => P.E.skeleton (emb j)) y, fun i => ?_⟩
  fin_cases i
  · exact hinj
  · exact hy

/-- **The `X → Y` template of the two-sort skeleton colors** (Lemma 8.3, `X_H = F(J_H)` inside
`Y_H`).  From the coherent `J`/`Z` colors: piece functors `F_X` (hulls of the `J`-coordinates)
and `F_Y` (hulls of both coordinates) with a strong natural transformation `F_X → F_Y`, an order
presentation of `K` whose values are the EM values of `F_Y`, and induced maps `F_X(I) → F_Y(I)`
that are strong and natural in order embeddings. -/
theorem infra_83_JZ_template (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ (FX FY : EM83.FinPieces K) (η : EM83.PiecesHom FX FY) (E : OrderPresentation K),
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], E.obj I = (FY.limit I).obj) ∧
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Strong (η.limMap I)) ∧
      ∀ {I J : Type u} [LinearOrder I] [LinearOrder J] [Nonempty I] [Nonempty J] (f : I ↪o J),
        (η.limMap J).comp (EM83.gEmMap (F := FX) f) =
          (EM83.gEmMap (F := FY) f).comp (η.limMap I) := by
  obtain ⟨c, hc, hcoh⟩ := infra_83_JZ_coherent_colors P Pr
  let σX : Fin 1 → Fin 2 := fun _ => 0
  let η := Hull83.subBundleHom hc hcoh σX (LS83.lsInl K) LS83.hullStrong_lsClosed
  exact ⟨_, _, η,
    Hull83.tpPresentationB hc hcoh (by norm_num) (LS83.lsInl K) LS83.hullStrong_lsClosed
      LS83.lsLang_functions_le,
    fun I _ _ => rfl, fun I _ _ => η.limMap_strong I, fun f => η.limMap_natural f⟩

/-- The three-sort bundle (`J` in `X`, `Z` in `Y`, `W` in `L`). -/
def jzwBundle {α M : Type u} (a b w : α → M) : α → Fin 3 → M := fun j => ![a j, b j, w j]

/-- **Arbitrarily long three-sort skeleton sequences** (sorts `J`, `Z`, `W`).  As in
`infra_83_JZ_skeleton_large`, plus an injective `W`-sequence: the skeleton of `J⁺` along an
injection of `J` into the fresh strip of `J⁺` (of the same size `μ`). -/
theorem infra_83_JZW_skeleton_large (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) (κ : Cardinal.{u}) :
    ∃ (J : Type u) (_ : LinearOrder J) (Jplus : Type u) (_ : LinearOrder Jplus)
      (_ : Nonempty Jplus) (emb : J ↪o Jplus) (_ : Nonempty J)
      (str : (LS83.lsLang K).Structure (P.E.obj Jplus).carrier)
      (y : J → (P.E.obj Jplus).carrier) (strip : Set Jplus) (w : J → strip),
      @LS83.LSClosed K _ str ∧ κ ≤ #J ∧
      Function.Injective (fun j => P.E.skeleton (emb j)) ∧ Function.Injective y ∧
      Function.Injective w ∧ IsConvexRegion strip := by
  obtain ⟨μ, hθ, -, -, J, i1, i2, -, -, hJ, -, M, -, eX, -, -, hZ, Jplus, i3, i4, emb, strip, -, -,
    hconv, hstrip, -, -, F, -, -, str, -, hcl, -, -⟩ :=
    infra_83_ls_expanded_samples P Pr (κ := ℵ₀) le_rfl κ
  obtain ⟨ι⟩ := hZ J hJ
  obtain ⟨e⟩ : Nonempty (J ≃ strip) := Cardinal.eq.mp (hJ.trans hstrip.symm)
  exact ⟨J, i1, Jplus, i3, i4, emb, i2, str, fun j => F (ι (P.E.skeleton j)), strip, e, hcl,
    hJ ▸ hθ, P.E.skeleton.injective.comp emb.injective,
    F.injective.comp (ι.injective.comp P.E.skeleton.injective), e.injective, hconv⟩

/-- **Coherent colors of the three-sort skeleton bundles** (`J`, `Z`, `W`). -/
theorem infra_83_JZW_coherent_colors (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.lsLang K) 3 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => LS83.LSClosed (K := K) N) 3) n c κ) ∧
      ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm) := by
  refine Hull83.tpB_coherent_colors fun κ => ?_
  obtain ⟨J, i1, Jplus, i3, i4, emb, i2, str, y, strip, w, hcl, hκ, hinj, hy, hw, -⟩ :=
    infra_83_JZW_skeleton_large P Pr κ
  refine ⟨J, i1, (P.E.obj Jplus).carrier, str, hcl, hκ,
    jzwBundle (fun j => P.E.skeleton (emb j)) y (fun j => P.E.skeleton (w j).1), fun i => ?_⟩
  fin_cases i
  · exact hinj
  · exact hy
  · exact P.E.skeleton.injective.comp (Subtype.val_injective.comp hw)

/-- **The `X → Y → L` template of the three-sort skeleton colors** (Lemma 8.3: `X_H = F(J_H)`,
`Y_H` from `J_H, Z_H`, `L_H = F(J_H + W_H)`).  Piece functors `F_X`, `F_Y`, `F_L` (hulls of the
`J`-, `J,Z`-, and all coordinates) with strong natural transformations `F_X → F_Y → F_L`, an
order presentation of `K` with values `F_L(I)`, and induced maps `F_X(I) → F_Y(I) → F_L(I)`,
strong and natural in order embeddings, whose composite is the induced map of the composite. -/
theorem infra_83_JZW_template (P : SingleModelData K)
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
  obtain ⟨c, hc, hcoh⟩ := infra_83_JZW_coherent_colors P Pr
  let σ : Fin 2 → Fin 3 := fun i => i.castSucc
  let τ : Fin 1 → Fin 2 := fun _ => 0
  let ηXY := Hull83.subSubBundleHom hc hcoh σ τ (LS83.lsInl K) LS83.hullStrong_lsClosed
  let ηYL := Hull83.subBundleHom hc hcoh σ (LS83.lsInl K) LS83.hullStrong_lsClosed
  exact ⟨_, _, _, ηXY, ηYL,
    Hull83.tpPresentationB hc hcoh (by norm_num) (LS83.lsInl K) LS83.hullStrong_lsClosed
      LS83.lsLang_functions_le,
    fun I _ _ => rfl,
    fun I _ _ => ⟨ηXY.limMap_strong I, ηYL.limMap_strong I, EM83.PiecesHom.limMap_comp _ _ I⟩,
    fun f => ⟨ηXY.limMap_natural f, ηYL.limMap_natural f⟩⟩

end AEC
