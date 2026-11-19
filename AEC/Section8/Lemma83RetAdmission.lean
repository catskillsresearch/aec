module

public import AEC.Section8.Lemma83SampleLikeY

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: ret-admitted samples

The admitted class of `pairMS2` records LS-closure, sort closure and charts, but not that the
binary `ret` symbol evaluates a Cor 6.16 retraction family.  `RetSampleLike` adds that clause:
an admitted sample carries a marked pair `X ⊆ Y` of infinite size `μ`, a surjection
`eX : F(J) → X`, an injection `F : Y → N` with `F ∘ incl ∘ eX = F(emb)`, an approximate
retraction family `(r_i)` with bijective codes `c_i ∈ F(J)`, and
`ret(F(emb)(c_i), F y) = F (incl (r_i y))`.  The colors over the strengthened class are again
coherent, the admitted witnesses being the `pairR` samples.
-/

universe u

open Cardinal FirstOrder FirstOrder.Language

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- The binary `ret` symbol of the marked full language. -/
abbrev retM3 (E : OrderPresentation K) (n : ℕ) : (LS83.pairLangM3 E n).Functions 2 :=
  Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr PUnit.unit)))))

/-- **Ret-sample-like structures**: `ret` evaluates a Cor 6.16 retraction family of a marked
pair whose `X`-copy is `F(J)` inside `N ≃ E(J⁺)`. -/
def RetSampleLike (P : SingleModelData K) (Pr : StationaryPrescription K oneVertexShape P.scheme)
    (N : Type u) [(LS83.pairLangM3 P.E Pr.n).Structure N] : Prop :=
  ∃ (M : MarkedPair K oneVertexShape P.scheme Pr) (J Jp : Type u) (_ : LinearOrder J)
    (_ : Nonempty J) (_ : LinearOrder Jp) (_ : Nonempty Jp) (emb : J ↪o Jp)
    (g : N ≃ (P.E.obj Jp).carrier)
    (eX : (P.E.obj J).carrier → ((P.scheme.asSystem M.hμ M.X).obj PUnit.unit).carrier)
    (F : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier → (P.E.obj Jp).carrier)
    (R : ApproximateRetraction K oneVertexShape P.scheme M.hμ M.X M.Y M.incl)
    (code : R.index → (P.E.obj J).carrier),
    Function.Surjective eX ∧ Function.Injective F ∧
    (∀ x, F (M.incl.onVertex PUnit.unit (eX x)) = P.E.map emb x) ∧
    Function.Bijective code ∧ ℵ₀ ≤ M.μ ∧
    ∀ (i : R.index) (y : ((P.scheme.asSystem M.hμ M.Y).obj PUnit.unit).carrier),
      g (Structure.funMap (retM3 P.E Pr.n)
        ![g.symm (P.E.map emb (code i)), g.symm (F y)]) =
        F (M.incl.onVertex PUnit.unit ((R.retr i).onVertex PUnit.unit y))

/-- The admitted class with `X`-, `Y`-side sample data and the ret evaluation law. -/
abbrev pairMAdmittedS3 (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) (N : Type u)
    [(LS83.pairLangM3 P.E Pr.n).Structure N] : Prop :=
  pairMAdmittedS2 P.E Pr.n N ∧ RetSampleLike P Pr N

/-- **The ret-admitted class is a subclass** of the `pairMS2` admitted class. -/
theorem pairMAdmittedS3.toS2 {P : SingleModelData K}
    {Pr : StationaryPrescription K oneVertexShape P.scheme} {N : Type u}
    [(LS83.pairLangM3 P.E Pr.n).Structure N] (h : pairMAdmittedS3 P Pr N) :
    pairMAdmittedS2 P.E Pr.n N := h.1

/-- **Coherent colors over ret-admitted samples.** As `infra_83_pairMS2_coherent_colors`, with the
admitted class strengthened by `RetSampleLike`: every admitted sample carries a Cor 6.16 family
whose evaluation law is realized by its `ret` symbol. -/
theorem infra_83_pairMS3_coherent_colors (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}),
        Hull83.Joint (Hull83.TpSampleB (fun N _ => pairMAdmittedS3 P Pr N) 3) n c κ) ∧
      (∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm)) ∧
      (∀ (m : ℕ) (hm : 0 < m) (a : Fin m) (i : Fin 3),
        (thetaM P.E Pr.n i).relabel (fun _ => (a, i)) ∈ c m hm) ∧
      ∀ (m : ℕ) (hm : 0 < m) (a b : Fin m), a < b → ∀ i : Fin 3,
        (rhoM P.E Pr.n i).relabel ![(a, i), (b, i)] ∈ c m hm := by
  refine Hull83.tpB_coherent_colors_formula2 (thetaM P.E Pr.n) (rhoM P.E Pr.n) fun κ => ?_
  obtain ⟨μ, hθ, hμ, J, i1, i2, -, hJ, M, hM, eX, hbij, -, ι, Jplus, i3, i4, emb, strip, hstrip, -,
    F, -, hF, s₀, hcl, hred, hX, hchX, hY, hchY, -, -, hlabX, hret⟩ :=
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
    ⟨⟨⟨hcl, J, Jplus, i1, i2, i3, i4, emb, Equiv.refl _, fun f x hx => hX f x hx,
      fun T _ hT => hchX T hT, fun x => Iff.rfl,
      fun f x => congrArg (fun s' => @Structure.funMap _ _ s' _ f x) hred,
      fun r x => Iff.of_eq (congrArg (fun s' => @Structure.RelMap _ _ s' _ r x) hred),
      fun x y => Iff.rfl, fun a y hy => (hlabX a y).trans (Lab83.labR_of_mem a y hy)⟩,
     J, Jplus, i1, i2, i3, i4, e₀, Equiv.refl _, ?_, ?_, fun x => Iff.rfl, ?_,
      fun f x => congrArg (fun s' => @Structure.funMap _ _ s' _ f x) hred,
      fun r x => Iff.of_eq (congrArg (fun s' => @Structure.RelMap _ _ s' _ r x) hred),
      fun x y => Iff.rfl, fun a y z hy => by
        have hyz : y = fun i => F (ι (z i)) := funext fun i => hy i
        subst hyz
        exact Lab83.labT_apply (fun y => F (ι y)) (F.injective.comp ι.injective) a z⟩, ?_⟩,
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
  · obtain ⟨R, code, hcode, hev⟩ := hret
    exact ⟨M, J, Jplus, i1, i2, i3, i4, emb, Equiv.refl _, eX, F, R, code, hbij.2, F.injective,
      hF, hcode, by rw [hM]; exact hμ.le, fun i y => hev i y⟩
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

end AEC
