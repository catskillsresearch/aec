module

public import AEC.Section8.Lemma83ExpSamples
public import AEC.Section8.LSRet83
public import AEC.Section8.Lemma83JColors

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: the retraction evaluation in the LS-expanded samples

"Include a sort of retraction indices and an evaluation function for a family `r_i : Y → X` from
Corollary 6.16."  In the LS-expanded samples `X ≤ Y ≤ L = F(J⁺)` the retraction indices are
coded by elements of `X = F(J)` (the index set has the level size), and
`ret(x, y) = r_i(y)` when `x` codes `i` and `y ∈ Y`, `ret(x, y) = x` otherwise.  The sorts `X`
and `Y` stay closed and the hulls stay strong.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Retraction-expanded samples.** -/
theorem infra_83_ret_samples (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (θ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, θ ≤ μ ∧ κ < μ ∧
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J), OrderSat83.OrderSaturated κ J ∧ #J = μ ∧
    ∃ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ = μ ∧
      ∃ eX : Language.Embedding K.τ (P.E.obj J).carrier
          ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier,
        Function.Bijective eX ∧ K.Strong eX ∧
        (∀ (Z : Type u) [LinearOrder Z] [Nonempty Z], #Z = μ →
          Nonempty ((P.E.obj Z).carrier ≃[K.τ]
            ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier)) ∧
      ∃ (Jplus : Type u) (_ : LinearOrder Jplus) (_ : Nonempty Jplus) (emb : J ↪o Jplus)
        (strip : Set Jplus), #strip = μ ∧ IsConvexRegion strip ∧
      ∃ (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
          (P.E.obj Jplus).carrier),
        K.Strong F ∧ (∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x) ∧
      ∃ (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
        (code : R.index → (P.E.obj J).carrier) (str : (LS83.lsLang K).Structure (P.E.obj Jplus).carrier)
        (g : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier),
        Function.Injective code ∧
        @LS83.LSClosed K _ str ∧
        @Language.LHom.reduct _ _ (LS83.lsInl K) _ str = (P.E.obj Jplus).str ∧
        (∀ {n} (f : (LS83.retLang K).Functions n) (x : Fin n → (P.E.obj Jplus).carrier),
          (∀ i, x i ∈ Set.range (P.E.map emb)) →
            @Language.Structure.funMap _ _ (LS83.retExp str g) n f x ∈ Set.range (P.E.map emb)) ∧
        (∀ {n} (f : (LS83.retLang K).Functions n) (x : Fin n → (P.E.obj Jplus).carrier),
          (∀ i, x i ∈ Set.range F) →
            @Language.Structure.funMap _ _ (LS83.retExp str g) n f x ∈ Set.range F) ∧
        ∀ (i : R.index) (y : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier),
          g (P.E.map emb (code i)) (F y) =
            F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)) := by
  classical
  obtain ⟨μ, h1, h2, h3, J, i1, i2, h4, -, hJ, -, M, h8, eX, h9, sX, hZ, Jplus, i3, i4, emb,
    strip, -, -, hconv, hstrip, -, -, F, sF, hF, str, hred, hcl, hX, hY⟩ :=
    infra_83_ls_expanded_samples P Pr hκ θ
  have hM615 : M.μ ∈ infra_615_closed P := h8 ▸ h3.2
  obtain ⟨R⟩ := infra_83_samples_retractions P Pr M hM615
  have hcJ : Model.card (P.E.obj J) = μ := SingleModelData.card_obj_eq h3.1.1 J hJ
  have hRc : #R.index = μ := R.index_card.trans h8
  obtain ⟨code⟩ : Nonempty (R.index ↪ (P.E.obj J).carrier) := by
    rw [← Cardinal.le_def]
    exact hRc.le.trans hcJ.ge
  let jX : (P.E.obj J).carrier → (P.E.obj Jplus).carrier := P.E.map emb
  let ev : R.index → ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier →
      (P.E.obj Jplus).carrier := fun i y =>
    F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y))
  let g : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier :=
    fun a b => if h : (∃ i, jX (code i) = a) ∧ (∃ y, F y = b) then ev h.1.choose h.2.choose
      else a
  have hjX : Function.Injective (fun i => jX (code i)) :=
    (P.E.map emb).injective.comp code.injective
  have hev : ∀ i y, ev i y ∈ Set.range jX := fun i y => by
    obtain ⟨z, hz⟩ := h9.2 ((R.retr i).onVertex PUnit.unit y)
    exact ⟨z, by simp only [jX, ev, ← hF z, hz]⟩
  have hXY : Set.range jX ⊆ Set.range F := by
    rintro _ ⟨z, rfl⟩
    exact ⟨_, hF z⟩
  have hgX : ∀ a b, a ∈ Set.range jX → b ∈ Set.range jX → g a b ∈ Set.range jX := by
    intro a b ha _
    simp only [g]
    split_ifs
    · exact hev _ _
    · exact ha
  have hgY : ∀ a b, a ∈ Set.range F → b ∈ Set.range F → g a b ∈ Set.range F := by
    intro a b ha _
    simp only [g]
    split_ifs
    · exact hXY (hev _ _)
    · exact ha
  refine ⟨μ, h1, h2, J, i1, i2, h4, hJ, M, h8, eX, h9, sX, hZ, Jplus, i3, i4, emb, strip, hstrip,
    hconv, F, sF, hF, R,
    code, str, g, code.injective, hcl, hred, fun f x hx => LS83.retExp_closed str g hX hgX f x hx,
    fun f x hx => LS83.retExp_closed str g hY hgY f x hx, fun i y => ?_⟩
  have h : (∃ i', jX (code i') = jX (code i)) ∧ (∃ y', F y' = F y) := ⟨⟨i, rfl⟩, ⟨y, rfl⟩⟩
  have key : g (jX (code i)) (F y) = ev h.1.choose h.2.choose := dif_pos h
  have e1 : h.1.choose = i := hjX h.1.choose_spec
  have e2 : h.2.choose = y := F.injective h.2.choose_spec
  refine key.trans ?_
  rw [e1, e2]

/-- The admitted class of the retraction-expanded samples: LS-closed `lsLang K`-reduct. -/
abbrev retAdmitted (N : Type u) [(LS83.retLang K).Structure N] : Prop :=
  @LS83.LSClosed K N ((Language.LHom.sumInl : LS83.lsLang K →ᴸ LS83.retLang K).reduct N)

/-- **Coherent colors of the three-sort skeleton bundles in the retraction language.** -/
theorem infra_83_ret_coherent_colors (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.retLang K) 3 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => retAdmitted (K := K) N) 3) n c κ) ∧
      ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm) := by
  refine Hull83.tpB_coherent_colors fun κ => ?_
  obtain ⟨μ, hθ, -, J, i1, i2, -, hJ, M, -, eX, -, -, hZ, Jplus, i3, i4, emb, strip, hstrip, -,
    F, -, -, R, code, str, g, -, hcl, -, -, -, -⟩ :=
    infra_83_ret_samples P Pr (κ := ℵ₀) le_rfl κ
  obtain ⟨ι⟩ := hZ J hJ
  obtain ⟨e⟩ : Nonempty (J ≃ strip) := Cardinal.eq.mp (hJ.trans hstrip.symm)
  refine ⟨J, i1, (P.E.obj Jplus).carrier, LS83.retExp str g, hcl, hJ ▸ hθ,
    jzwBundle (fun j => P.E.skeleton (emb j)) (fun j => F (ι (P.E.skeleton j)))
      (fun j => P.E.skeleton (e j).1), fun i => ?_⟩
  fin_cases i
  · exact P.E.skeleton.injective.comp emb.injective
  · exact F.injective.comp (ι.injective.comp P.E.skeleton.injective)
  · exact P.E.skeleton.injective.comp (Subtype.val_injective.comp e.injective)

/-- **The `X → Y → L` template of the retraction-expanded samples** (pair language: `τ(K)`,
LS witnesses, retraction evaluation; sorts `J`, `Z`, `W`).  Piece functors `F_X → F_Y → F_L`
with strong natural transformations, an order presentation of `K` with values `F_L(I)`, and
strong induced maps natural in order embeddings. -/
theorem infra_83_ret_template (P : SingleModelData K)
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
  obtain ⟨c, hc, hcoh⟩ := infra_83_ret_coherent_colors P Pr
  let σ : Fin 2 → Fin 3 := fun i => i.castSucc
  let τ : Fin 1 → Fin 2 := fun _ => 0
  let φ := (Language.LHom.sumInl : LS83.lsLang K →ᴸ LS83.retLang K).comp (LS83.lsInl K)
  let ηXY := Hull83.subSubBundleHom hc hcoh σ τ φ LS83.hullStrong_ret
  let ηYL := Hull83.subBundleHom hc hcoh σ φ LS83.hullStrong_ret
  exact ⟨_, _, _, ηXY, ηYL,
    Hull83.tpPresentationB hc hcoh (by norm_num) φ LS83.hullStrong_ret LS83.retLang_functions_le,
    fun I _ _ => rfl,
    fun I _ _ => ⟨ηXY.limMap_strong I, ηYL.limMap_strong I, EM83.PiecesHom.limMap_comp _ _ I⟩,
    fun f => ⟨ηXY.limMap_natural f, ηYL.limMap_natural f⟩⟩

end AEC
