module

public import AEC.Section8.Lemma83PairSamples3
public import AEC.Section8.PairLangR83

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: samples with representation positions

The three-copy samples with the representation positions of `X` added to the `X`-language.
Every subset of `L` closed under the `X`-language meets `X` exactly in `F(J_S)` for its chart
`J_S` (both directions of generation).
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Pair samples with representation positions.** -/
theorem infra_83_pairR_samples (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) {κ : Cardinal.{u}} (hκ : ℵ₀ ≤ κ)
    (θ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, θ ≤ μ ∧ κ < μ ∧
    ∃ (J : Type u) (_ : LinearOrder J) (_ : Nonempty J), OrderSat83.OrderSaturated κ J ∧ #J = μ ∧
    ∃ M : MarkedPair K oneVertexShape P.scheme Pr, M.μ = μ ∧
      ∃ eX : Language.Embedding K.τ (P.E.obj J).carrier
          ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier,
        Function.Bijective eX ∧ K.Strong eX ∧
      ∃ ι : (P.E.obj J).carrier ≃[K.τ] ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier,
      ∃ (Jplus : Type u) (_ : LinearOrder Jplus) (_ : Nonempty Jplus) (emb : J ↪o Jplus)
        (strip : Set Jplus), #strip = μ ∧ IsConvexRegion strip ∧
      ∃ (F : Language.Embedding K.τ ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier
          (P.E.obj Jplus).carrier),
        K.Strong F ∧ (∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x) ∧
      ∃ sR : (LS83.pairLangR P.E).Structure (P.E.obj Jplus).carrier,
        @LS83.LSClosed K _ (@Language.LHom.reduct _ _ (LS83.pairInlR P.E) _ sR) ∧
        @Language.LHom.reduct _ _ ((LS83.pairInlR P.E).comp (LS83.lsInl K)) _ sR =
          (P.E.obj Jplus).str ∧
        (∀ {n} (f : (LS83.pairLangR P.E).Functions n) (x : Fin n → (P.E.obj Jplus).carrier),
          (∀ i, x i ∈ Set.range (P.E.map emb)) →
            @Language.Structure.funMap _ _ sR n f x ∈ Set.range (P.E.map emb)) ∧
        (∀ (S : Set (P.E.obj Jplus).carrier) [Nonempty (Lab83.chart emb S)],
          (∀ {n} (f : (LS83.pairLangR P.E).Functions n) (x : Fin n → (P.E.obj Jplus).carrier),
            (∀ i, x i ∈ S) → @Language.Structure.funMap _ _ sR n f x ∈ S) →
          S ∩ Set.range (P.E.map emb) = Set.range (P.E.map (Lab83.chartEmb emb S))) ∧
        (∀ {n} (f : (LS83.pairLangR2 P.E).Functions n) (x : Fin n → (P.E.obj Jplus).carrier),
          (∀ i, x i ∈ Set.range F) →
            @Language.Structure.funMap _ _
              (@Language.sumStructure _ _ _ sR (@Language.sumStructure _ _ _ (Lab83.labTStr (fun y => F (ι y))) (Lab83.repTStr (fun y => F (ι y))))) n f x ∈
              Set.range F) ∧
        (∀ (S : Set (P.E.obj Jplus).carrier) [Nonempty (Lab83.chartT (fun y => F (ι y)) S)],
          (∀ {n} (f : (LS83.pairLangR2 P.E).Functions n) (x : Fin n → (P.E.obj Jplus).carrier),
            (∀ i, x i ∈ S) → @Language.Structure.funMap _ _
              (@Language.sumStructure _ _ _ sR (@Language.sumStructure _ _ _
                (Lab83.labTStr (fun y => F (ι y))) (Lab83.repTStr (fun y => F (ι y))))) n f x ∈ S) →
          S ∩ Set.range (fun y => F (ι y)) = Set.range ((fun y => F (ι y)) ∘
            P.E.map (OrderEmbedding.subtype (fun z => z ∈ Lab83.chartT (fun y => F (ι y)) S)))) ∧
        (∀ t : SupportTerm P.E.lab P.E.arity J,
          @Language.Structure.funMap _ _
            (@Language.sumStructure _ _ _ sR (@Language.sumStructure _ _ _ (Lab83.labTStr (fun y => F (ι y))) (Lab83.repTStr (fun y => F (ι y))))) _
            (Sum.inr (Sum.inl ⟨t.label, rfl⟩)) (fun k => F (ι (P.E.skeleton (t.pos k)))) =
            F (ι (P.E.realize t))) ∧
        (∀ t : SupportTerm P.E.lab P.E.arity Jplus,
          @Language.Structure.funMap _ _ (@Language.sumStructure _ _ _
            (@Language.sumStructure _ _ _ sR (@Language.sumStructure _ _ _ (Lab83.labTStr (fun y => F (ι y))) (Lab83.repTStr (fun y => F (ι y))))) Lab83.labStr) _
            (Sum.inr ⟨t.label, rfl⟩) (fun k => P.E.skeleton (t.pos k)) = P.E.realize t) := by
  classical
  obtain ⟨μ, h1, h2, J, i1, i2, h4, hJ, M, h8, eX, h9, sX, ι, Jplus, i3, i4, emb, strip, hs, hc,
    F, sF, hF, s₀, hcl, hred, hX, -, hY, hYlab, hfull, hlabR⟩ := infra_83_pair3_samples P Pr hκ θ
  have hXF : Set.range (P.E.map emb) ⊆ Set.range F := by
    rintro _ ⟨z, rfl⟩
    exact ⟨_, hF z⟩
  refine ⟨μ, h1, h2, J, i1, i2, h4, hJ, M, h8, eX, h9, sX, ι, Jplus, i3, i4, emb, strip, hs, hc,
    F, sF, hF, @Language.sumStructure _ _ _ s₀ (Lab83.repStr emb), hcl, hred, ?_, ?_, ?_, ?_,
    fun t => hYlab t, fun t => hfull t⟩
  · intro n f x hx
    rcases f with f | f
    · exact hX f x hx
    · exact Lab83.repFun_mem emb le_rfl _ (hx _)
  · intro S _ hS
    refine Lab83.inter_eq_chart emb S (fun a y hy => ?_) (fun x hx k => ?_)
    · have := hS (Sum.inl (Sum.inr a)) y hy
      rwa [show @Language.Structure.funMap _ _ (@Language.sumStructure _ _ _ s₀
        (Lab83.repStr emb)) _ (Sum.inl (Sum.inr a)) y = _ from hlabR a y] at this
    · exact Lab83.rep_closed emb (fun i z hz => hS (Sum.inr ⟨⟨i⟩, rfl⟩) (fun _ => z)
        (fun _ => hz)) x hx k
  · intro n f x hx
    rcases f with (f | f) | (f | f)
    · exact hY (Sum.inl f) x hx
    · exact Lab83.repFun_mem emb hXF _ (hx _)
    · exact hY (Sum.inr f) x hx
    · exact Lab83.repTFun_mem _ (by rintro _ ⟨z, rfl⟩; exact ⟨_, rfl⟩) _ (hx _)
  · intro S _ hS
    have hinj : Function.Injective (fun y => F (ι y)) := F.injective.comp ι.injective
    refine Lab83.inter_eq_chartT _ hinj S (fun a y hy => hS (Sum.inr (Sum.inl a)) y hy)
      (fun x hx k => Lab83.repT_closed _ hinj (fun i z hz => hS (Sum.inr (Sum.inr ⟨⟨i⟩, rfl⟩))
        (fun _ => z) (fun _ => hz)) x hx k)

end AEC
