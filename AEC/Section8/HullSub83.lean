module

public import AEC.Section8.HullReduct83

/-!
# Lemma 8.3: hulls in a sublanguage

The sort objects of the pair template (`X_H → Y_H → L_H`) are term hulls of one tuple in
nested sublanguages of the expanded sample language.  For `ψ : L₀ →ᴸ L` and
`φ₀ : K.τ →ᴸ L₀`, the `L₀`-hull of a tuple maps into its `L`-hull by `ψ.onTerm`; after
reducts this is a `τ`-embedding over the sample, and it is strong when both hulls are strong
in the sample (coherence).
-/

@[expose] public section

namespace AEC
namespace Hull83

universe u

open FirstOrder FirstOrder.Language Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- A map that factors one embedding through another (injective) one is an embedding. -/
def embOfComp {A B C : Type u} [K.τ.Structure A] [K.τ.Structure B] [K.τ.Structure C]
    (g : B ↪[K.τ] C) (h : A ↪[K.τ] C) (f : A → B) (hf : ∀ x, g (f x) = h x) :
    A ↪[K.τ] B where
  toFun := f
  inj' x y hxy := h.injective (by rw [← hf, ← hf, hxy])
  map_fun' {n} F xs := g.injective (by
    rw [hf, h.map_fun, g.map_fun]
    congr 1
    funext i
    exact (hf (xs i)).symm)
  map_rel' {n} r xs := by
    rw [← g.map_rel, ← h.map_rel]
    have : (g ∘ fun i => f (xs i)) = h ∘ xs := funext fun i => hf (xs i)
    rw [show (g ∘ (f ∘ xs)) = h ∘ xs from this]

theorem embOfComp_comp {A B C : Type u} [K.τ.Structure A] [K.τ.Structure B]
    [K.τ.Structure C] (g : B ↪[K.τ] C) (h : A ↪[K.τ] C) (f : A → B)
    (hf : ∀ x, g (f x) = h x) : g.comp (embOfComp g h f hf) = h := by
  ext x
  exact hf x

/-- Coherence: a factor of strong embeddings through a strong embedding is strong. -/
theorem embOfComp_strong {A B C : Model K.τ} (g : B.carrier ↪[K.τ] C.carrier)
    (h : A.carrier ↪[K.τ] C.carrier) (f : A.carrier → B.carrier) (hf : ∀ x, g (f x) = h x)
    (hg : K.Strong g) (hh : K.Strong h) : K.Strong (embOfComp g h f hf) :=
  K.coherence _ h g hh hg (embOfComp_comp g h f hf)

variable {L₀ L : Language.{u, u}} (ψ : L₀ →ᴸ L)

section SubHull

variable {M : Type u} [L.Structure M] {m : ℕ}

/-- The `L₀`-hull of a tuple of an `L`-structure (computed in the reduct). -/
def subHull (v : Fin m → M) : Type u := @Hull L₀ M (ψ.reduct M) m v

/-- The `L₀`-hull maps into the `L`-hull. -/
def subToHull (v : Fin m → M) : subHull ψ v → Hull (L := L) v :=
  @Quotient.map _ _ (@hullSetoid L₀ M (ψ.reduct M) m v) (hullSetoid (L := L) v) (ψ.onTerm)
    (fun t t' (htt : @Term.realize L₀ M (ψ.reduct M) _ v t =
        @Term.realize L₀ M (ψ.reduct M) _ v t') => by
      letI := ψ.reduct M
      show (ψ.onTerm t).realize v = (ψ.onTerm t').realize v
      rw [LHom.realize_onTerm, LHom.realize_onTerm]
      exact htt)

theorem hullVal_subToHull (v : Fin m → M) (x : subHull ψ v) :
    hullVal (L := L) v (subToHull ψ v x) = @hullVal L₀ M (ψ.reduct M) m v x := by
  letI := ψ.reduct M
  induction x using Quotient.ind with
  | _ t =>
    show (ψ.onTerm t).realize v = t.realize v
    exact LHom.realize_onTerm ψ t v

end SubHull

variable (φ₀ : K.τ →ᴸ L₀)

/-- The `τ`-model of the `L₀`-hull. -/
noncomputable def subHullModel {M : Type u} [L.Structure M] {m : ℕ} (v : Fin m → M) : Model K.τ :=
  @red K L₀ φ₀ (subHull ψ v) (@hullStructure L₀ M (ψ.reduct M) m v)

/-- The `τ`-model of the sample, seen through `L₀`. -/
def subModel' (M : Type u) [L.Structure M] : Model K.τ := @red K L₀ φ₀ M (ψ.reduct M)

/-- The `L₀`-hull embedding into the sample, after reduct. -/
noncomputable def subHullEmb {M : Type u} [L.Structure M] {m : ℕ} (v : Fin m → M) :
    (subHullModel ψ φ₀ v).carrier ↪[K.τ] (red (ψ.comp φ₀) M).carrier :=
  @redEmb K L₀ φ₀ (subHull ψ v) M (@hullStructure L₀ M (ψ.reduct M) m v) (ψ.reduct M)
    (@hullEmb L₀ M (ψ.reduct M) m v)

/-- **Sublanguage hull inclusion.**  The `L₀`-hull of `v` is a `τ`-substructure of its
`L`-hull, compatibly with both embeddings into the sample. -/
noncomputable def subHullIncl {M : Type u} [L.Structure M] {m : ℕ} (v : Fin m → M) :
    (subHullModel ψ φ₀ v).carrier ↪[K.τ] (red (ψ.comp φ₀) (Hull (L := L) v)).carrier :=
  embOfComp (redEmb (ψ.comp φ₀) (hullEmb (L := L) v)) (subHullEmb ψ φ₀ v) (subToHull ψ v)
    (fun x => hullVal_subToHull ψ v x)

/-- The inclusion is strong when both hulls are strong in the sample. -/
theorem subHullIncl_strong {M : Type u} [L.Structure M] {m : ℕ} (v : Fin m → M)
    (hL : K.Strong (redEmb (ψ.comp φ₀) (hullEmb (L := L) v)))
    (hL₀ : K.Strong (subHullEmb ψ φ₀ v)) :
    K.Strong (subHullIncl ψ φ₀ v) :=
  embOfComp_strong _ _ _ _ hL hL₀

end Hull83
end AEC
