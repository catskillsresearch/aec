module

public import AEC.Section5.NamedPackageTransfer
public import AEC.Section5.FixedSupportTerms

@[expose] public section

/-!
# Proposition 5.7: the named scheme with the fixed-support template

The proof of Prop 5.7 regards the presentations `F (J + H)` with the names on `J` as a template
in `H`. `WorkingScheme.withTemplate` replaces the template of a scheme; the clauses of
`IsWorkingPackageCore` do not mention the template, so they transfer unchanged.
-/

namespace AEC
section

universe u

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}

/-- The same scheme with another term template. -/
def WorkingScheme.withTemplate (W : WorkingScheme K S) (F : TermTemplate K S) :
    WorkingScheme K S :=
  { W with template := F }

theorem WorkingScheme.isWorkingPackageCore_withTemplate (W : WorkingScheme K S)
    (F : TermTemplate K S) (h : IsWorkingPackageCore W) :
    IsWorkingPackageCore (W.withTemplate F) :=
  ⟨⟨h.1.union⟩, ⟨h.2.1.downward⟩, ⟨h.2.2.1.saturated⟩, ⟨h.2.2.2.exhaustion⟩⟩

open Cardinal in
/-- **Proposition 5.7, presentation clause.** Chart `X0` as `pres I0`; the named scheme with the
template `H ↦ F (I0 ⊕ₗ H)` and names `F(inl)` of the chart preimages of `c` satisfies
Definition 5.2(2). -/
theorem WorkingScheme.hasTermPresentations_named (W : WorkingScheme K S)
    (hpack : IsWorkingPackage W)
    {μ0 : Cardinal.{u}} {hμ0 : μ0 ∈ W.eligible} (X0 : W.Object μ0 hμ0)
    {ι : Type u} (c : ι → Occurrence K S (W.asSystem hμ0 X0))
    (T : Set Cardinal.{u}) (hT : EligibleSubclass W.eligible T)
    (hι : #ι < μ0) (hTail : ∀ μ ∈ T, μ0 ≤ μ) (hinf : ∀ μ ∈ T, Cardinal.aleph0 ≤ μ) :
    ∃ (I0 : Type u) (_ : LinearOrder I0) (_ : Nonempty I0),
      HasTermPresentations ((W.namedWorkingScheme X0 c T hT hι hTail hinf).withTemplate
        (W.template.withFixedSupport I0)) := by
  classical
  obtain ⟨pres, e, hedge, harr, honto⟩ := hpack.presentations.present
  obtain ⟨Φ⟩ := hpack.presentations.finiteSupport
  obtain ⟨I0, _, _, _, hI0, φ, hφ⟩ := honto hμ0 X0
  have hbij := W.isStructIso_bijective _ _ φ hφ
  choose x hx using fun i => (hbij (c i).1).2 (c i).2
  let c' : ι → Occurrence K S (W.asSystem hμ0 (pres hμ0 I0 hI0)) := fun i => ⟨(c i).1, x i⟩
  have hc' : W.DiagramEq (pres hμ0 I0 hI0) X0 c' c :=
    (W.diagram_iso _ _ c' c hι).2 ⟨φ, hφ, fun i => Sigma.ext rfl (heq_of_eq (hx i).symm)⟩
  have hsz : ∀ {μ : Cardinal.{u}} (hμ : μ ∈ T) (H : Type u), #H = μ → #(I0 ⊕ₗ H) = μ := by
    intro μ hμ H hH
    change #(I0 ⊕ H) = μ
    rw [Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id, hI0, hH]
    exact Cardinal.add_eq_right (hinf μ hμ) (hTail μ hμ)
  have hιT : ∀ {μ : Cardinal.{u}}, μ ∈ T → #ι < μ := fun hμ => hι.trans_le (hTail _ hμ)
  -- the inclusion arrow `pres I0 → pres (I0 ⊕ₗ H)` along `inl`
  have hincl := fun {μ : Cardinal.{u}} (hμ : μ ∈ T) (H : Type u) [LinearOrder H]
      [WellFoundedLT H] [Nonempty H] (hH : #H = μ) =>
    harr hμ0 (EligibleSubclass.mem_source hT hμ) I0 (I0 ⊕ₗ H) hI0 (hsz hμ H hH)
      (sumLexEmbedLeftIncl I0 H)
  let inclArr := fun {μ : Cardinal.{u}} (hμ : μ ∈ T) (H : Type u) [LinearOrder H]
      [WellFoundedLT H] [Nonempty H] (hH : #H = μ) => Classical.choose (hincl hμ H hH)
  have inclSpec := fun {μ : Cardinal.{u}} (hμ : μ ∈ T) (H : Type u) [LinearOrder H]
      [WellFoundedLT H] [Nonempty H] (hH : #H = μ) => Classical.choose_spec (hincl hμ H hH)
  let presN : ∀ {μ : Cardinal.{u}} (hμ : μ ∈ T) (H : Type u) [LinearOrder H]
      [WellFoundedLT H] [Nonempty H], #H = μ →
      NamedObject W X0 c μ (EligibleSubclass.mem_source hT hμ) :=
    fun {μ} hμ H _ _ _ hH =>
      { base := pres (EligibleSubclass.mem_source hT hμ) (I0 ⊕ₗ H) (hsz hμ H hH)
        names := fun i => (inclArr hμ H hH).mapOcc (c' i)
        realizes := W.diagram_trans _ _ _ c c' _
          (W.diagram_symm _ _ c' c hc')
          (W.diagram_preserved _ _ (inclArr hμ H hH) (inclSpec hμ H hH).1 c' hι (hιT hμ)) }
  refine ⟨I0, inferInstance, inferInstance, ⟨⟨Φ.withFixedSupport I0⟩, ?_⟩⟩
  refine ⟨fun {μ} hμ H _ _ _ hH => presN hμ H hH,
    fun {μ} hμ H _ _ _ hH v => e (EligibleSubclass.mem_source hT hμ) (I0 ⊕ₗ H) (hsz hμ H hH) v,
    ?_, ?_, ?_⟩
  · intro μ hμ H _ _ _ hH i j h x
    exact hedge (EligibleSubclass.mem_source hT hμ) (I0 ⊕ₗ H) (hsz hμ H hH) h x
  · intro μ ν hμ hν H H' _ _ _ _ _ _ hH hH' f
    obtain ⟨arr, hperm, hcomm⟩ := harr (EligibleSubclass.mem_source hT hμ)
      (EligibleSubclass.mem_source hT hν) (I0 ⊕ₗ H) (I0 ⊕ₗ H') (hsz hμ H hH) (hsz hν H' hH')
      (sumLexEmbedRight (J := I0) f)
    refine ⟨arr, ⟨hperm, ?_⟩, hcomm⟩
    intro i
    obtain ⟨y, hy⟩ := (e hμ0 I0 hI0 (c i).1).surjective (x i)
    have h1 := (inclSpec hμ H hH).2 (c i).1 y
    have h2 := (inclSpec hν H' hH').2 (c i).1 y
    have hcompEmb : (sumLexEmbedLeftIncl I0 H).trans (sumLexEmbedRight (J := I0) f) =
        sumLexEmbedLeftIncl I0 H' := by
      ext z; rfl
    change (⟨(c i).1, (inclArr hν H' hH').onVertex (c i).1 (x i)⟩ : Occurrence K S _) =
      ⟨(c i).1, arr.onVertex (c i).1 ((inclArr hμ H hH).onVertex (c i).1 (x i))⟩
    congr 1
    rw [← hy, h1, h2, hcomm, ← W.template.onOrder_comp, hcompEmb]
  · intro μ hμ X
    have hμ0' : μ ≠ 0 := (Cardinal.aleph0_pos.trans_le (hinf μ hμ)).ne'
    haveI : Nonempty μ.ord.ToType := by
      rw [Ordinal.nonempty_toType_iff, ne_eq, Cardinal.ord_eq_zero]; exact hμ0'
    let hH : #μ.ord.ToType = μ := Cardinal.mk_ord_toType μ
    have hd : W.DiagramEq (presN hμ μ.ord.ToType hH).base X.base
        (presN hμ μ.ord.ToType hH).names X.names :=
      W.diagram_trans _ _ _ _ c _
        (W.diagram_symm _ _ c _ (presN hμ μ.ord.ToType hH).realizes) X.realizes
    obtain ⟨g, hg, hgn⟩ := (W.diagram_iso _ _ _ _ (hιT hμ)).1 hd
    exact ⟨μ.ord.ToType, inferInstance, inferInstance, inferInstance, hH, g, hg, hgn⟩

end
end AEC
