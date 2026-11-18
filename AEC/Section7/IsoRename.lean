module

public import AEC.Section7.IsolationTransfer

@[expose] public section

/-!
# Prop 7.8: renaming along a structural isomorphism `X ≃ A` (`infra_78_iso_rename`)

Paper (Prop 7.8 proof, last sentence): "Renaming `U` along this isomorphism gives the asserted
extension of the original `X`." For a structural (bijective) isomorphism `φ : X → A` at one level
and a tuple `t` over `A`, the tuple `t ∘ φ` over `X` (same host and values, inclusion
`φ ≫ incl t`) has the same Galois-type relations and is relatively isolated whenever `t` is.
Parameters are moved with the inverse arrow `ψ : A → X` (`infra_78_struct_inverse`); only
pointwise identities of arrows are used.
-/

universe u

open FirstOrder Cardinal
namespace AEC

variable {K : AbstractElementaryClass.{u}}

section Rename
variable {P : SingleModelData K} {ℓ : Cardinal.{u}} {hℓ : ℓ ∈ P.eligible}

/-- A tuple over `A` re-based over `X` along an arrow into its host (same host and values). -/
def infra_78_withIncl {X A : P.scheme.Object ℓ hℓ}
    (t : TupleOver K oneVertexShape P.scheme hℓ A)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem t.hν t.host)) :
    TupleOver K oneVertexShape P.scheme hℓ X :=
  ⟨t.ν, t.hν, t.host, g, trivial, t.idx, t.val⟩

/-- **Galois types under base change (proved).** If `g_k = φ ≫ incl t_k` pointwise, a Galois
type identity over `A` gives the same identity over `X`. -/
theorem infra_78_sgt_base_change {X A : P.scheme.Object ℓ hℓ}
    (φ : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem hℓ A))
    (t1 t2 : TupleOver K oneVertexShape P.scheme hℓ A) {idx : Type u}
    (e1 : t1.idx ≃ idx) (e2 : t2.idx ≃ idx)
    (g1 : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem t1.hν t1.host))
    (g2 : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem t2.hν t2.host))
    (h1 : ∀ x, g1.onVertex PUnit.unit x =
      t1.incl.onVertex PUnit.unit (φ.onVertex PUnit.unit x))
    (h2 : ∀ x, g2.onVertex PUnit.unit x =
      t2.incl.onVertex PUnit.unit (φ.onVertex PUnit.unit x))
    (H : SameGaloisType t1 t2 e1 e2) :
    SameGaloisType (infra_78_withIncl t1 g1) (infra_78_withIncl t2 g2) e1 e2 := by
  obtain ⟨ρ, hρ, top, f1, f2, hf1, hf2, hinc, hval⟩ := H
  refine ⟨ρ, hρ, top, f1, f2, hf1, hf2, ?_, hval⟩
  intro v
  cases v
  ext x
  have := DFunLike.congr_fun (hinc PUnit.unit) (φ.onVertex PUnit.unit x)
  show f1.onVertex PUnit.unit (g1.onVertex PUnit.unit x) =
    f2.onVertex PUnit.unit (g2.onVertex PUnit.unit x)
  rw [h1, h2]
  exact this

/-- **Inverse of a structural isomorphism (proved).** -/
theorem infra_78_struct_inverse {X A : P.scheme.Object ℓ hℓ}
    (φ : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem hℓ A))
    (hφ : P.scheme.IsStructIso (X := X) (Y := A) φ) :
    ∃ ψ : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ A) (P.scheme.asSystem hℓ X),
      (∀ a, φ.onVertex PUnit.unit (ψ.onVertex PUnit.unit a) = a) ∧
      (∀ x, ψ.onVertex PUnit.unit (φ.onVertex PUnit.unit x) = x) := by
  classical
  let F := φ.onVertex PUnit.unit
  let eq : ((P.scheme.asSystem hℓ X).obj PUnit.unit).carrier ≃[K.τ]
      ((P.scheme.asSystem hℓ A).obj PUnit.unit).carrier :=
    { Equiv.ofBijective F (hφ PUnit.unit) with
      map_fun' := F.map_fun', map_rel' := F.map_rel' }
  refine ⟨infra_69_equivArrow P hℓ X A eq.symm, fun a => ?_, fun x => ?_⟩
  · exact eq.apply_symm_apply a
  · exact eq.symm_apply_apply x

/-- Relative isolation under base change along a structural isomorphism, for any re-based
inclusion `g` agreeing pointwise with `φ ≫ incl t`. -/
theorem infra_78_iso_rename_gen {X A : P.scheme.Object ℓ hℓ}
    (φ : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem hℓ A))
    (hφ : P.scheme.IsStructIso (X := X) (Y := A) φ)
    (t : TupleOver K oneVertexShape P.scheme hℓ A) {uIdx cIdx : Type u}
    (e : t.idx ≃ uIdx ⊕ cIdx)
    (g : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem t.hν t.host))
    (hg : ∀ x, g.onVertex PUnit.unit x =
      t.incl.onVertex PUnit.unit (φ.onVertex PUnit.unit x))
    (hiso : IsRelativelyIsolated t e) :
    IsRelativelyIsolated (infra_78_withIncl t g) e := by
  classical
  obtain ⟨ψ, hφψ, hψφ⟩ := infra_78_struct_inverse φ hφ
  obtain ⟨ι, Z, hι, H⟩ := hiso
  let Z' : ι → Occurrence K oneVertexShape (P.scheme.asSystem hℓ X) :=
    fun j => ⟨(Z j).1, ψ.onVertex (Z j).1 (Z j).2⟩
  refine ⟨ι, Z', hι, ?_⟩
  intro q e' hqν hsg hdeq
  let qA : TupleOver K oneVertexShape P.scheme hℓ A :=
    infra_78_withIncl q (SystemArrow.comp ψ q.incl)
  have hsgA : SameGaloisType (t.marginal e) (qA.marginal e') (Equiv.refl uIdx)
      (Equiv.refl uIdx) :=
    infra_78_sgt_base_change ψ ((infra_78_withIncl t g).marginal e)
      (q.marginal e') (Equiv.refl uIdx) (Equiv.refl uIdx) t.incl (SystemArrow.comp ψ q.incl)
      (fun a => by
        show t.incl.onVertex PUnit.unit a = g.onVertex PUnit.unit (ψ.onVertex PUnit.unit a)
        rw [hg, hφψ])
      (fun _ => rfl) hsg
  have hj : typeJoint (p := infra_78_withIncl t g) Z' = typeJoint (p := t) Z := by
    funext s
    rcases s with k | j
    · rfl
    · show (⟨(Z j).1, g.onVertex (Z j).1 (ψ.onVertex (Z j).1 (Z j).2)⟩ :
          Occurrence K oneVertexShape (P.scheme.asSystem t.hν t.host)) =
        ⟨(Z j).1, t.incl.onVertex (Z j).1 (Z j).2⟩
      generalize Z j = z
      rcases z with ⟨⟨⟩, z⟩
      rw [hg, hφψ]
  rw [hj] at hdeq
  have hres := H qA e' hqν hsgA hdeq
  have hfin := infra_78_sgt_base_change φ t qA e e' g q.incl hg
    (fun x => by
      show q.incl.onVertex PUnit.unit x =
        q.incl.onVertex PUnit.unit (ψ.onVertex PUnit.unit (φ.onVertex PUnit.unit x))
      rw [hψφ])
    hres
  exact hfin

/-- **`infra_78_iso_rename` (relative isolation under base change; proved, both directions).**
For a structural isomorphism `φ : X → A` and a tuple `t` over `A`, the re-based tuple over `X`
with inclusion `φ ≫ incl t` is relatively isolated iff `t` is. -/
theorem infra_78_iso_rename {X A : P.scheme.Object ℓ hℓ}
    (φ : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem hℓ A))
    (hφ : P.scheme.IsStructIso (X := X) (Y := A) φ)
    (t : TupleOver K oneVertexShape P.scheme hℓ A) {uIdx cIdx : Type u}
    (e : t.idx ≃ uIdx ⊕ cIdx) :
    IsRelativelyIsolated (infra_78_withIncl t (SystemArrow.comp φ t.incl)) e ↔
      IsRelativelyIsolated t e := by
  constructor
  · intro h
    obtain ⟨ψ, hφψ, hψφ⟩ := infra_78_struct_inverse φ hφ
    have hψ : P.scheme.IsStructIso (X := A) (Y := X) ψ := fun v => by
      cases v
      exact ⟨Function.LeftInverse.injective (g := φ.onVertex PUnit.unit) hφψ,
        Function.RightInverse.surjective (f := ψ.onVertex PUnit.unit) hψφ⟩
    exact infra_78_iso_rename_gen ψ hψ (infra_78_withIncl t (SystemArrow.comp φ t.incl)) e
      t.incl (fun a => by
        show t.incl.onVertex PUnit.unit a =
          t.incl.onVertex PUnit.unit (φ.onVertex PUnit.unit (ψ.onVertex PUnit.unit a))
        rw [hφψ]) h
  · exact infra_78_iso_rename_gen φ hφ t e _ (fun _ => rfl)

/-- **Galois type under base change (proved, both directions).** -/
theorem infra_78_iso_rename_galois {X A : P.scheme.Object ℓ hℓ}
    (φ : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem hℓ A))
    (hφ : P.scheme.IsStructIso (X := X) (Y := A) φ)
    (t1 t2 : TupleOver K oneVertexShape P.scheme hℓ A) {idx : Type u}
    (e1 : t1.idx ≃ idx) (e2 : t2.idx ≃ idx) :
    SameGaloisType (infra_78_withIncl t1 (SystemArrow.comp φ t1.incl))
      (infra_78_withIncl t2 (SystemArrow.comp φ t2.incl)) e1 e2 ↔
      SameGaloisType t1 t2 e1 e2 := by
  constructor
  · intro H
    obtain ⟨ψ, hφψ, _⟩ := infra_78_struct_inverse φ hφ
    exact infra_78_sgt_base_change ψ (infra_78_withIncl t1 (SystemArrow.comp φ t1.incl))
      (infra_78_withIncl t2 (SystemArrow.comp φ t2.incl)) e1 e2 t1.incl t2.incl
      (fun a => by
        show t1.incl.onVertex PUnit.unit a =
          t1.incl.onVertex PUnit.unit (φ.onVertex PUnit.unit (ψ.onVertex PUnit.unit a))
        rw [hφψ])
      (fun a => by
        show t2.incl.onVertex PUnit.unit a =
          t2.incl.onVertex PUnit.unit (φ.onVertex PUnit.unit (ψ.onVertex PUnit.unit a))
        rw [hφψ]) H
  · exact infra_78_sgt_base_change φ t1 t2 e1 e2 _ _ (fun _ => rfl) (fun _ => rfl)

/-- **Renamed extension in the `proposition_7_8` shape (proved).** With `f := φ ≫ gu : X → U`,
the tuples `(bU, c)` from `U` over `X` (as `asTuple f`, joint list `seqJoint bU c`) are relatively
isolated over `bU` whenever they are over `A` (`infra_78_isolation_over_A`). -/
theorem infra_78_iso_rename_asTuple {X A U : P.scheme.Object ℓ hℓ}
    (φ : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ X) (P.scheme.asSystem hℓ A))
    (hφ : P.scheme.IsStructIso (X := X) (Y := A) φ)
    (gu : SystemArrow K oneVertexShape (P.scheme.asSystem hℓ A) (P.scheme.asSystem hℓ U))
    {uIdx J : Type u} (bU : uIdx → Occurrence K oneVertexShape (P.scheme.asSystem hℓ U))
    (c : J → Occurrence K oneVertexShape (P.scheme.asSystem hℓ U))
    (hiso : IsRelativelyIsolated
      (⟨ℓ, hℓ, U, gu, trivial, uIdx ⊕ J, Sum.elim bU c⟩ :
        TupleOver K oneVertexShape P.scheme hℓ A) (Equiv.refl (uIdx ⊕ J))) :
    IsRelativelyIsolated (asTuple (SystemArrow.comp φ gu) trivial (seqJoint bU c))
      (Equiv.refl (uIdx ⊕ J)) := by
  have h := (infra_78_iso_rename φ hφ _ _).2 hiso
  have hv : (Sum.elim bU c : uIdx ⊕ J → _) = seqJoint bU c := by
    funext s; rcases s with k | j <;> rfl
  have key : ∀ v : uIdx ⊕ J → Occurrence K oneVertexShape (P.scheme.asSystem hℓ U),
      v = seqJoint bU c →
      IsRelativelyIsolated (asTuple (SystemArrow.comp φ gu) trivial v)
        (Equiv.refl (uIdx ⊕ J)) →
      IsRelativelyIsolated (asTuple (SystemArrow.comp φ gu) trivial (seqJoint bU c))
        (Equiv.refl (uIdx ⊕ J)) := by
    rintro v rfl hv'; exact hv'
  exact key _ hv h

end Rename

end AEC
