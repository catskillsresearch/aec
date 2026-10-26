module

public import AEC.Section2.DirectLimit
public import AEC.Section2.DirectedLimit
public import AEC.Section2.ValidCode
public import AEC.Section2.Recovery
public import AEC.Section2.OrderPresentation
public import AEC.Section2.Partition
public import AEC.Section2.Presentation
public import AEC.Section1.UniformThreshold
public import AEC.Section1.UnboundedCategoricity
public import AEC.Section1.CategoricalTail
public import AEC.Section1.ArbitrarilyLarge
public import Mathlib.Data.Finset.Card

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Lemma 2.1** (Directed unions and coherent direct limits). A coherent diagram of strong
maps indexed by a nonempty directed partial order has a direct limit in `K`, with strong
canonical maps. Every compatible family of strong maps from the diagram into a model induces
a strong map from the direct limit. -/
theorem lemma_2_1 (K : AbstractElementaryClass.{u}) (S : DirectedSystem K.τ)
    (hmem : ∀ i, K.Mem (S.obj i))
    (hstrong : ∀ {i j} (hij : S.rel i j), K.Strong (S.map hij)) :
    ∃ L : DirectLimit S,
      K.Mem L.obj ∧
      (∀ i, K.Strong (L.canon i)) ∧
      ∀ (N : Model K.τ)
        (g : ∀ i, Language.Embedding K.τ (S.obj i).carrier N.carrier),
        K.Mem N →
        (∀ i, K.Strong (g i)) →
        (∀ {i j} (hij : S.rel i j), (g j).comp (S.map hij) = g i) →
        ∃ f : Language.Embedding K.τ L.obj.carrier N.carrier,
          K.Strong f ∧ ∀ i, f.comp (L.canon i) = g i :=
  directLimit_in_class K S hmem hstrong

/-- **Lemma 2.2** (Recovery from small models and pairs). An AEC in a finitary language `τ`
of cardinality at most `lam`, with `LS(K) ≤ lam`, is recovered from a set code for its models
of cardinality at most `lam` and the strong inclusions between them. -/
theorem lemma_2_2 {τ : Tau.{u}} {lam : Cardinal.{u}} (K : AbstractElementaryClass.{u})
    (hτ : τ = K.τ) (hcard : τ.card ≤ lam) (hLS : isLSBound K lam) :
    ∃ c : SmallCode τ lam, IsValidCode lam c ∧
      (∀ M : Model K.τ, K.Mem M ↔ DecodedMem (hτ ▸ c) M) ∧
      (∀ {M N : Model K.τ} (f : Language.Embedding K.τ M.carrier N.carrier),
        K.Strong f ↔ DecodedStrong (hτ ▸ c) f) := by
  subst hτ
  refine ⟨aecCode K lam, aecCode_isValidCode hLS, ?_, ?_⟩
  · intro M; exact mem_iff_decodedMem hLS M
  · intro M N f; exact strong_iff_decodedStrong hLS f

/-- **Proposition 2.3** (The uniform reduction). The uniform assertion of Theorem 1.2 is
equivalent to the qualitative assertion that every AEC categorical in unboundedly many
cardinals is categorical above some bound depending on that AEC. -/
theorem proposition_2_3 :
    (∃ μ : Cardinal.{u} → Cardinal.{u}, IsUniformThreshold μ) ↔
      ∀ K : AbstractElementaryClass.{u}, CategoricalUnbounded K → CategoricalOnTail K := by
  constructor
  · intro ⟨μ, hμ⟩ K hK
    have hls : isLSBound K (ls K) := isLSBound_ls K
    obtain ⟨κ, hκ, hcat⟩ := hK.unbounded (μ (ls K))
    exact ⟨μ (ls K), fun κ' hκ' =>
      (hμ.threshold (ls K) hls.1).2 K hls ⟨κ, hκ, hcat⟩ κ' hκ'⟩
  · intro hqual
    let μ : Cardinal.{u} → Cardinal.{u} := fun lam =>
      max (lam + aleph0) (canBound lam + 1)
    refine ⟨μ, ⟨?_⟩⟩
    intro lam hlam
    refine ⟨le_self_add.trans (le_max_left (lam + aleph0) (canBound lam + 1)), ?_⟩
    intro K hLS ⟨κ, hκ, hcat⟩ κ' hκ'
    have h_bound : spectrumBound K ≤ μ lam :=
      (spectrumBound_le_canBound_of_isLSBound hLS).trans
        (le_self_add.trans (le_max_right (lam + aleph0) (canBound lam + 1)))
    have h_le_κ : spectrumBound K ≤ κ := h_bound.trans hκ
    have h_all := categorical_of_ge_spectrumBound K (hqual K) h_le_κ hcat
    have h_le_κ' : spectrumBound K ≤ κ' := h_bound.trans hκ'
    exact h_all κ' h_le_κ'

/-- **Lemma 2.5.** For infinite cardinals `ξ`, `ν` and a positive integer `k`, some infinite
cardinal `R` has the partition property: every coloring of the `k`-element subsets of a set of
cardinality at least `R`, with `ξ` colors, has a homogeneous subset of cardinality `ν`.
Finitely many specified arities can be made homogeneous simultaneously. -/
theorem lemma_2_5 (ξ ν : Cardinal.{u}) (k : ℕ) (hξ : aleph0 ≤ ξ) (hν : aleph0 ≤ ν)
    (hk : 0 < k) :
    ∃ R : Cardinal.{u}, aleph0 ≤ R ∧
      (∀ (ι : Type u), R ≤ #ι →
        ∀ (C : Type u), #C = ξ →
          ∀ color : {s : Finset ι // s.card = k} → C,
            ∃ H : Set ι, ν ≤ #H ∧ ∃ c : C,
              ∀ (s : Finset ι) (hs : s.card = k),
                (∀ x ∈ s, x ∈ H) → color ⟨s, hs⟩ = c) ∧
      ∀ (n : ℕ) (arity : Fin n → ℕ), (∀ i, 0 < arity i) →
        ∃ R' : Cardinal.{u}, R ≤ R' ∧
          ∀ (ι : Type u), R' ≤ #ι →
            ∀ (C : Fin n → Type u), (∀ i, #(C i) = ξ) →
              ∀ color : (i : Fin n) → {s : Finset ι // s.card = arity i} → C i,
                ∃ H : Set ι, ν ≤ #H ∧
                  ∀ i : Fin n, ∃ c : C i,
                    ∀ (s : Finset ι) (hs : s.card = arity i),
                      (∀ x ∈ s, x ∈ H) → color i ⟨s, hs⟩ = c := by
  refine ⟨recursivePartitionBound k ξ ν, partitionBound_infinite hk hξ hν, ?_, ?_⟩
  · intro ι hι C hC color
    exact erdos_color hξ hν hk hι hC color
  · intro n arity hpos
    obtain ⟨R', _, hjoint⟩ := joint_partition hξ n hν arity hpos
    refine ⟨max (recursivePartitionBound k ξ ν) R', le_max_left _ _, ?_⟩
    intro ι hι C hC color
    exact hjoint ι ((le_max_right _ _).trans hι) C hC color

/-- **Theorem 2.6** (Order presentation). An AEC with arbitrarily large models has an
Ehrenfeucht–Mostowski presentation by finitely supported labeled terms, and therefore a model
of every infinite cardinality at least `LS(K)`. -/
theorem theorem_2_6 (K : AbstractElementaryClass.{u}) [ArbitrarilyLarge K] :
    ∃ E : OrderPresentation K,
      (∀ (I : Type u) [LinearOrder I] [Nonempty I], K.Mem (E.obj I)) ∧
      ∀ κ : Cardinal.{u}, aleph0 ≤ κ → ls K ≤ κ →
        ∃ M : Model K.τ, K.Mem M ∧ Model.card M = κ := by
  let E := emOrderPresentation K
  refine ⟨E, fun I => (emLimit_spec (K := K) I).1, ?_⟩
  intro κ hκ hls
  let I := κ.ord.ToType
  have hI_card : #I = κ := Cardinal.mk_ord_toType κ
  haveI : LinearOrder I := inferInstance
  haveI : Nonempty I := by
    rw [← Cardinal.mk_ne_zero_iff, hI_card]
    exact ne_of_gt (aleph0_pos.trans_le hκ)
  let M := E.obj I
  have hM_mem : K.Mem M := (emLimit_spec (K := K) I).1
  have hM_card : Model.card M = κ := by
    apply le_antisymm
    · have hupper := E.card_upper (I := I)
      rw [E.ell_eq] at hupper
      have h_add : #I + ls K = κ := by
        rw [hI_card]
        exact add_eq_left hκ hls
      exact hupper.trans (le_of_eq h_add)
    · have hlower := E.card_lower (I := I)
      rw [hI_card] at hlower
      exact hlower
  exact ⟨M, hM_mem, hM_card⟩

end
end AEC
