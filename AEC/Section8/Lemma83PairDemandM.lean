module

public import AEC.Section8.Lemma83PairTemplateM
public import AEC.Section8.Lemma83PairDemand

@[expose] public section

/-!
# Lemma 8.3 for the Prop 5.6 scheme: the joint demand, with the mark as designated terms

"Retain at the same time arbitrarily high prescribed order-saturation bounds.  Treat the requested
homogeneous size and the requested order saturation as one cardinal demand."  The saturation of a
sample is read off its chart relations: the largest `κ ≤ #M` such that the `X`-chart with its
chart order is a `κ`-order-saturated linear order.
-/

universe u

open Cardinal FirstOrder

namespace AEC

variable {K : AbstractElementaryClass.{u}}

/-- `X`-chart predicate in a `pairLangM3`-structure. -/
def chartXM (E : OrderPresentation K) (n : ℕ) {M : Type u} [(LS83.pairLangM3 E n).Structure M] (x : M) :
    Prop :=
  Language.Structure.RelMap (L := LS83.pairLangM3 E n) (Sum.inr (Sum.inl ⟨⟨0⟩, rfl⟩)) ![x]

/-- `X`-chart order in a `pairLangM3`-structure. -/
def chartLtXM (E : OrderPresentation K) (n : ℕ) {M : Type u} [(LS83.pairLangM3 E n).Structure M]
    (x y : M) : Prop :=
  Language.Structure.RelMap (L := LS83.pairLangM3 E n) (Sum.inr (Sum.inr ⟨⟨0⟩, rfl⟩)) ![x, y]

/-- The order saturation of the `X`-chart of a structure (capped at `#M`). -/
noncomputable def chartSatM (E : OrderPresentation K) (n : ℕ) (M : Type u)
    [(LS83.pairLangM3 E n).Structure M] : Cardinal.{u} :=
  sSup {κ | κ ≤ #M ∧ ∃ (J : Type u) (_ : LinearOrder J), OrderSat83.OrderSaturated κ J ∧
    ∃ f : J → M, (∀ j, chartXM E n (f j)) ∧ (∀ x, chartXM E n x → ∃ j, f j = x) ∧
      ∀ j j', j < j' ↔ chartLtXM E n (f j) (f j')}

/-- **Coherent colors under the joint size / order-saturation demand** (template with chart
relations). -/
theorem infra_83_pairM_colors_demand (P : SingleModelData K)
    (Pr : StationaryPrescription K oneVertexShape P.scheme) :
    ∃ c : (m : ℕ) → 0 < m → Hull83.TpColorB (LS83.pairLangM3 P.E Pr.n) 3 m,
      (∀ (n : ℕ) (κ : Cardinal.{u}), ∃ S, Hull83.TpSampleD (fun N _ => pairMAdmitted P.E Pr.n N)
        (fun M _ => chartSatM P.E Pr.n M) 3 S ∧ κ ≤ #S.α ∧ Hull83.Homog S n c) ∧
      ∀ {m m' : ℕ} (hm' : 0 < m') (hm : 0 < m) (f : Fin m' ↪o Fin m),
        c m' hm' = Hull83.tpResB 3 f (c m hm) := by
  classical
  refine Hull83.tpB_coherent_colors_demand _ fun κ => ?_
  obtain ⟨μ, hθ, hκμ, J, i1, i2, hsat, hJ, M, -, eX, -, -, ι, Jplus, i3, i4, emb, strip, hstrip,
    -, F, -, -, s₀, hcl, -⟩ :=
    infra_83_pairR_samples P Pr (κ := max κ ℵ₀) (le_max_right _ _) κ
  obtain ⟨e⟩ : Nonempty (J ≃ strip) := Cardinal.eq.mp (hJ.trans hstrip.symm)
  let sR4 : (LS83.pairLangM3 P.E Pr.n).Structure (P.E.obj Jplus).carrier :=
    @Language.sumStructure _ _ _ (@Language.sumStructure _ _ _
      (@Language.sumStructure _ _ _ s₀ (@Language.sumStructure _ _ _
        (@Language.sumStructure _ _ _ (Lab83.labTStr (fun y => F (ι y)))
          (Lab83.repTStr (fun y => F (ι y)))) (Mark83.markStr fun i => F (markY M i)))) Lab83.labStr)
      (Lab83.chartStr emb (fun y => F (ι y)))
  letI := sR4
  have hinj : Function.Injective fun j => P.E.skeleton (emb j) :=
    P.E.skeleton.injective.comp emb.injective
  have hc1 : ∀ x, chartXM P.E Pr.n x ↔ ∃ j, P.E.skeleton (emb j) = x := fun x => Iff.rfl
  have hc2 : ∀ x y, chartLtXM P.E Pr.n x y ↔ ∃ j j', j < j' ∧ P.E.skeleton (emb j) = x ∧
      P.E.skeleton (emb j') = y := fun x y => Iff.rfl
  have hJM : #J ≤ #(P.E.obj Jplus).carrier := Cardinal.mk_le_of_injective hinj
  have hmem : max κ ℵ₀ ∈ {κ' | κ' ≤ #(P.E.obj Jplus).carrier ∧ ∃ (J' : Type u)
      (_ : LinearOrder J'), OrderSat83.OrderSaturated κ' J' ∧
      ∃ f : J' → (P.E.obj Jplus).carrier, (∀ j, chartXM P.E Pr.n (f j)) ∧
        (∀ x, chartXM P.E Pr.n x → ∃ j, f j = x) ∧ ∀ j j', j < j' ↔ chartLtXM P.E Pr.n (f j) (f j')} := by
    refine ⟨(hκμ.le.trans hJ.symm.le).trans hJM, J, i1, hsat, fun j => P.E.skeleton (emb j),
      fun j => (hc1 _).2 ⟨j, rfl⟩, fun x hx => (hc1 x).1 hx, fun j j' => ?_⟩
    rw [hc2]
    constructor
    · intro h
      exact ⟨j, j', h, rfl, rfl⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      rwa [← hinj ha, ← hinj hb]
  have hle : max κ ℵ₀ ≤ chartSatM P.E Pr.n (P.E.obj Jplus).carrier :=
    le_csSup ⟨_, fun _ h => h.1⟩ hmem
  refine ⟨J, i1, (P.E.obj Jplus).carrier, sR4, hcl,
    (le_max_left _ _).trans (hκμ.le.trans hJ.symm.le), (le_max_left _ _).trans hle,
    jzwBundle (fun j => P.E.skeleton (emb j)) (fun j => F (ι (P.E.skeleton j)))
      (fun j => P.E.skeleton (e j).1), fun i => ?_⟩
  fin_cases i
  · exact hinj
  · exact F.injective.comp (ι.injective.comp P.E.skeleton.injective)
  · exact P.E.skeleton.injective.comp (Subtype.val_injective.comp e.injective)

end AEC
