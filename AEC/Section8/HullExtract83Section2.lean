module

public import AEC.Section2.CoherentColor
public import AEC.Section8.HullExtract83

/-!
# The generic color tower specializes to Section 2

Sanity check of the reuse plan for Lemma 8.3's hull extraction: the generic
`Hull83.coherent_colors`, instantiated with the samples of `K` colored by `tupleCode`
(Section 2's finite-hull diagrams), yields Section 2's coherent colors with arbitrarily large
joint samples (`JointSample`).  The pair instance (`infra_83_pair_sample_family`) is the
same instantiation with the expanded pair samples.
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- Colored samples coming from an injective sequence in a model of `K`, colored by the
finite-hull diagram of each tuple. -/
def KSample (K : AbstractElementaryClass.{u}) (S : ColorSample (FamilyCode K)) : Prop :=
  ∃ (M : Model K.τ) (hM : K.Mem M) (base : S.α → M.carrier) (hbase : Function.Injective base),
    ∀ (m : ℕ) (s : Finset S.α) (h : s.card = m), S.col m s = tupleCode hM base hbase s h

theorem kSample_restrict (S : ColorSample (FamilyCode K)) (H : Set S.α) (hS : KSample K S) :
    KSample K (S.restrict H) := by
  obtain ⟨M, hM, base, hbase, hcol⟩ := hS
  refine ⟨M, hM, fun x => base x.1, fun x y hxy => Subtype.ext (hbase hxy), ?_⟩
  intro m s h
  let s' : Finset ↥H := s
  exact (hcol m (s'.map (Function.Embedding.subtype (· ∈ H))) ((Finset.card_map _).trans h)).trans
    (tupleCode_subtype hM base hbase s' h).symm

theorem kSample_large [ArbitrarilyLarge K] (κ : Cardinal.{u}) :
    ∃ S, KSample K S ∧ κ ≤ #S.α := by
  obtain ⟨M, hM, hbig⟩ := ArbitrarilyLarge.large (K := K) κ
  let α := κ.ord.ToType
  have hα : #α = κ := Cardinal.mk_ord_toType _
  obtain ⟨emb⟩ := (le_def α M.carrier).mp (hα ▸ hbig)
  refine ⟨⟨α, fun m s => if h : s.card = m then tupleCode hM emb emb.injective s h
    else default⟩, ⟨M, hM, emb, emb.injective, fun m s h => by simp [h]⟩, le_of_eq hα.symm⟩

/-- **Section 2 as an instance of the generic tower.**  Coherent colors at all positive
arities with arbitrarily large joint homogeneous samples, obtained from
`Hull83.coherent_colors` for the samples of `K`. -/
theorem section2_coherent_colors [ArbitrarilyLarge K] :
    ∃ c : (m : ℕ) → 0 < m → FamilyCode K m, ∀ (n : ℕ) (κ : Cardinal.{u}),
      JointSample n (fun m _ hm0 => c m hm0) κ := by
  obtain ⟨c, hc⟩ := coherent_colors (P := KSample K) (fun S H hS => kSample_restrict S H hS)
    kSample_large
  refine ⟨c, fun n κ => ?_⟩
  obtain ⟨S, ⟨M, hM, base, hbase, hcol⟩, hκ, hhom⟩ := hc n κ
  refine ⟨S.α, inferInstance, M, hM, base, hbase, hκ, ?_⟩
  intro m hm hm0 s hs
  rw [← hcol m s hs]
  exact hhom m hm0 hm s hs

end Hull83
end AEC
