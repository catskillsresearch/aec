module

public import AEC.Section8.Lemma83ExpSamples
public import AEC.Section8.LSPairLang83

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

end AEC
