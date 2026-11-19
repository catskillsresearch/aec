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
            (Sum.inr ⟨t.label, rfl⟩) (fun k => P.E.skeleton (t.pos k)) = P.E.realize t) ∧
        (∀ {n} (a : (Lab83.labLang P.E).Functions n) (x : Fin n → (P.E.obj Jplus).carrier),
          @Language.Structure.funMap _ _ sR n (Sum.inl (Sum.inr a)) x =
            Lab83.labR (Set.range (P.E.map emb)) a x) ∧
        ∃ (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
          (code : R.index → (P.E.obj J).carrier), Function.Bijective code ∧
          ∀ (i : R.index) (y : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier),
            @Language.Structure.funMap _ _ sR 2 (Sum.inl (Sum.inl (Sum.inr PUnit.unit)))
              ![P.E.map emb (code i), F y] =
              F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)) := by
  classical
  obtain ⟨μ, h1, h2, J, i1, i2, h4, hJ, M, h8, eX, h9, sX, ι, Jplus, i3, i4, emb, strip, hs, hc,
    F, sF, hF, s₀, hcl, hred, hX, -, hY, hYlab, hfull, hlabR, hret⟩ := infra_83_pair3_samples P Pr hκ θ
  have hXF : Set.range (P.E.map emb) ⊆ Set.range F := by
    rintro _ ⟨z, rfl⟩
    exact ⟨_, hF z⟩
  refine ⟨μ, h1, h2, J, i1, i2, h4, hJ, M, h8, eX, h9, sX, ι, Jplus, i3, i4, emb, strip, hs, hc,
    F, sF, hF, @Language.sumStructure _ _ _ s₀ (Lab83.repStr emb), hcl, hred, ?_, ?_, ?_, ?_,
    fun t => hYlab t, fun t => hfull t, fun a x => hlabR a x, hret⟩
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

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- **Ret-terms send `Y` into `X`.** Under the evaluation law of a Cor 6.16 family, every
ret-term `ret(c_i, y)` with `y ∈ F(Y)` lies in the `X`-copy `F(J)` of the sample. -/
theorem infra_83_ret_term_into_X (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {J Jplus : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jplus] [Nonempty Jplus]
    {M : MarkedPair K oneVertexShape P.scheme Pr}
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (hsurj : Function.Surjective eX) (emb : J ↪o Jplus)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jplus).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier)
    (G : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier)
    (heval : ∀ i y, G (P.E.map emb (code i)) (F y) =
      F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)))
    (i : R.index) (y : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier) :
    G (P.E.map emb (code i)) (F y) ∈ Set.range (P.E.map emb) := by
  obtain ⟨z, hz⟩ := hsurj ((R.retr i).onVertex PUnit.unit y)
  exact ⟨z, by rw [heval, ← hz, hF]⟩

/-- **Ret-terms fix `X` almost everywhere.** Under the evaluation law of a Cor 6.16 family,
for each `x ∈ J` only finitely many codes `c_i` move `F(x)`: `ret(c_i, F x) = F x` otherwise. -/
theorem infra_83_ret_term_almost_id (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {J Jplus : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jplus] [Nonempty Jplus]
    {M : MarkedPair K oneVertexShape P.scheme Pr}
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (emb : J ↪o Jplus)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jplus).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier)
    (G : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier)
    (heval : ∀ i y, G (P.E.map emb (code i)) (F y) =
      F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)))
    (x : (P.E.obj J).carrier) :
    Finite {i : R.index //
      G (P.E.map emb (code i)) (P.E.map emb x) ≠ P.E.map emb x} := by
  haveI := R.almost_id ⟨_, eX x⟩
  refine Finite.of_injective (β := {i : R.index // (R.retr i).onVertex PUnit.unit
    (M.incl.onVertex PUnit.unit (eX x)) ≠ eX x}) (fun i => ⟨i.1, fun he => i.2 (by
      have := heval i.1 (M.incl.onVertex PUnit.unit (eX x))
      rw [hF x, he, hF x] at this
      exact this)⟩) ?_
  · intro a b hab
    exact Subtype.ext (congrArg Subtype.val hab :)


/-- **Ret-terms fix finite parts of `X` almost everywhere.** For a finite `A ⊆ J`, only finitely
many codes `c_i` move some `F(x)`, `x ∈ A`. -/
theorem infra_83_ret_term_fix_finite (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {J Jplus : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jplus] [Nonempty Jplus]
    {M : MarkedPair K oneVertexShape P.scheme Pr}
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (emb : J ↪o Jplus)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jplus).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier)
    (G : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier)
    (heval : ∀ i y, G (P.E.map emb (code i)) (F y) =
      F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)))
    (A : Finset (P.E.obj J).carrier) :
    {i : R.index | ∃ x ∈ A, G (P.E.map emb (code i)) (P.E.map emb x) ≠ P.E.map emb x}.Finite := by
  have : {i : R.index | ∃ x ∈ A, G (P.E.map emb (code i)) (P.E.map emb x) ≠ P.E.map emb x} =
      ⋃ x ∈ (A : Set (P.E.obj J).carrier),
        {i : R.index | G (P.E.map emb (code i)) (P.E.map emb x) ≠ P.E.map emb x} := by
    ext i; simp
  rw [this]
  refine A.finite_toSet.biUnion fun x _ => ?_
  haveI := infra_83_ret_term_almost_id P eX emb F hF R code G heval x
  exact Set.toFinite _


/-- **Many codes fix a finite part of `X`.** If the Cor 6.16 index set is infinite, the codes
`c_i` with `ret(c_i, F x) = F x` for all `x ∈ A` (finite) have full cardinality `#index`. -/
theorem infra_83_ret_term_fix_card (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {J Jplus : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jplus] [Nonempty Jplus]
    {M : MarkedPair K oneVertexShape P.scheme Pr}
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (emb : J ↪o Jplus)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jplus).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier)
    (G : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier)
    (heval : ∀ i y, G (P.E.map emb (code i)) (F y) =
      F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)))
    (hinf : ℵ₀ ≤ #R.index) (A : Finset (P.E.obj J).carrier) :
    #{i : R.index | ∀ x ∈ A, G (P.E.map emb (code i)) (P.E.map emb x) = P.E.map emb x} =
      #R.index := by
  have hfin := infra_83_ret_term_fix_finite P eX emb F hF R code G heval A
  have hc : {i : R.index | ∀ x ∈ A, G (P.E.map emb (code i)) (P.E.map emb x) = P.E.map emb x} =
      {i : R.index | ∃ x ∈ A, G (P.E.map emb (code i)) (P.E.map emb x) ≠ P.E.map emb x}ᶜ := by
    ext i; simp
  rw [hc]
  haveI : Infinite R.index := Cardinal.infinite_iff.mpr hinf
  exact Cardinal.mk_compl_of_infinite _ ((Cardinal.lt_aleph0_iff_set_finite.mpr hfin).trans_le hinf)


/-- **`μ` codes fix a finite part of `X`.** For a marked pair of infinite size `μ`, the codes
fixing `F(x)` for all `x` in a finite `A ⊆ J` number exactly `μ`. -/
theorem infra_83_ret_term_fix_card_mu (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {J Jplus : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jplus] [Nonempty Jplus]
    {M : MarkedPair K oneVertexShape P.scheme Pr}
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (emb : J ↪o Jplus)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jplus).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier)
    (G : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier)
    (heval : ∀ i y, G (P.E.map emb (code i)) (F y) =
      F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)))
    (hinf : ℵ₀ ≤ M.μ) (A : Finset (P.E.obj J).carrier) :
    #{i : R.index | ∀ x ∈ A, G (P.E.map emb (code i)) (P.E.map emb x) = P.E.map emb x} =
      M.μ := by
  rw [infra_83_ret_term_fix_card P eX emb F hF R code G heval (by rw [R.index_card]; exact hinf) A,
    R.index_card]


/-- **Each ret-translate maps the `Y`-copy into the `X`-copy.** Set form of
`infra_83_ret_term_into_X`: `ret(c_i, ·) '' F(Y) ⊆ F(J)`. -/
theorem infra_83_ret_image_into_X (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {J Jplus : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jplus] [Nonempty Jplus]
    {M : MarkedPair K oneVertexShape P.scheme Pr}
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (hsurj : Function.Surjective eX) (emb : J ↪o Jplus)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jplus).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier)
    (G : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier)
    (heval : ∀ i y, G (P.E.map emb (code i)) (F y) =
      F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)))
    (i : R.index) :
    G (P.E.map emb (code i)) '' Set.range F ⊆ Set.range (P.E.map emb) := by
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  exact infra_83_ret_term_into_X P eX hsurj emb F hF R code G heval i y


/-- **`μ` good codes over a finite part of `X`.** For a marked pair of infinite size `μ` and a
finite `A ⊆ J`, exactly `μ` codes `c_i` both fix `F(A)` pointwise and send `F(Y)` into `F(J)`. -/
theorem infra_83_ret_good_card_mu (P : SingleModelData K)
    {Pr : StationaryPrescription K oneVertexShape P.scheme}
    {J Jplus : Type u} [LinearOrder J] [Nonempty J] [LinearOrder Jplus] [Nonempty Jplus]
    {M : MarkedPair K oneVertexShape P.scheme Pr}
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (hsurj : Function.Surjective eX) (emb : J ↪o Jplus)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jplus).carrier)
    (hF : ∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x)
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier)
    (G : (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier → (P.E.obj Jplus).carrier)
    (heval : ∀ i y, G (P.E.map emb (code i)) (F y) =
      F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y)))
    (hinf : ℵ₀ ≤ M.μ) (A : Finset (P.E.obj J).carrier) :
    #{i : R.index | (∀ x ∈ A, G (P.E.map emb (code i)) (P.E.map emb x) = P.E.map emb x) ∧
      G (P.E.map emb (code i)) '' Set.range F ⊆ Set.range (P.E.map emb)} = M.μ := by
  have : {i : R.index | (∀ x ∈ A, G (P.E.map emb (code i)) (P.E.map emb x) = P.E.map emb x) ∧
      G (P.E.map emb (code i)) '' Set.range F ⊆ Set.range (P.E.map emb)} =
      {i : R.index | ∀ x ∈ A, G (P.E.map emb (code i)) (P.E.map emb x) = P.E.map emb x} := by
    ext i
    exact ⟨fun h => h.1, fun h => ⟨h, infra_83_ret_image_into_X P eX hsurj emb F hF R code G
      heval i⟩⟩
  rw [this]
  exact infra_83_ret_term_fix_card_mu P eX emb F hF R code G heval hinf A

end AEC
