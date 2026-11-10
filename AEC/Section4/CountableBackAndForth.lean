module

public import AEC.Section4.StableDiagramConstruction
public import AEC.Section2.DirectedLimit
public import Mathlib.Data.Finset.Card

/-!
# Countable back-and-forth → isomorphism (Prop 4.3 infra)

English (text.md): countable alternating partial matches; the union bijection preserves the
atomic diagram because every finite tuple appears at some stage.

Packages:
* a bijection that agrees on every finite set with some language embedding is a `Language.Equiv`;
* a compatible exhausting `SameStrongClass` sequence yields such a bijection / isomorphism.
-/

@[expose] public section

namespace AEC
section

universe u

open Classical FirstOrder Cardinal Function

/-! ### Local embeddings → structure equivalence -/

theorem map_fun_of_finset_local_embeddings {L : Tau.{u}} {M N : Type u}
    [L.Structure M] [L.Structure N] (f : M → N)
    (H : ∀ s : Finset M, ∃ e : M ↪[L] N, ∀ x ∈ s, e x = f x)
    {n : ℕ} (F : L.Functions n) (x : Fin n → M) :
    f (Language.Structure.funMap F x) = Language.Structure.funMap F (f ∘ x) := by
  classical
  let s : Finset M := insert (Language.Structure.funMap F x) (Finset.univ.image x)
  obtain ⟨e, he⟩ := H s
  have hx (i : Fin n) : e (x i) = f (x i) :=
    he _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, by simp, rfl⟩))
  have hval : e (Language.Structure.funMap F x) = f (Language.Structure.funMap F x) :=
    he _ (Finset.mem_insert_self _ _)
  have hembed := e.map_fun' F x
  calc
    f (Language.Structure.funMap F x) = e (Language.Structure.funMap F x) := hval.symm
    _ = Language.Structure.funMap F (e ∘ x) := hembed
    _ = Language.Structure.funMap F (f ∘ x) := by
        congr 1
        ext i
        exact hx i

theorem map_rel_of_finset_local_embeddings {L : Tau.{u}} {M N : Type u}
    [L.Structure M] [L.Structure N] (f : M → N)
    (H : ∀ s : Finset M, ∃ e : M ↪[L] N, ∀ x ∈ s, e x = f x)
    {n : ℕ} (R : L.Relations n) (x : Fin n → M) :
    Language.Structure.RelMap R (f ∘ x) ↔ Language.Structure.RelMap R x := by
  classical
  let s : Finset M := Finset.univ.image x
  obtain ⟨e, he⟩ := H s
  have hx (i : Fin n) : e (x i) = f (x i) :=
    he _ (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
  have hembed := e.map_rel' R x
  convert (hembed : Language.Structure.RelMap R (e ∘ x) ↔ Language.Structure.RelMap R x) using 2
  ext i
  exact (hx i).symm

/-- **Infra: local embeddings + bijection ⇒ language equivalence.** -/
noncomputable def languageEquiv_of_bijective_local_embeddings {L : Tau.{u}} {M N : Type u}
    [L.Structure M] [L.Structure N] (f : M → N)
    (hinj : Injective f) (hsurj : Surjective f)
    (H : ∀ s : Finset M, ∃ e : M ↪[L] N, ∀ x ∈ s, e x = f x) :
    M ≃[L] N :=
  embeddingEquivOfSurjective
    ⟨⟨f, hinj⟩,
      fun {_} F x => map_fun_of_finset_local_embeddings f H F x,
      fun {_} R x => map_rel_of_finset_local_embeddings f H R x⟩
    hsurj

/-! ### SameStrongClass exhaustions -/

/-- A countable back-and-forth sequence of strong-class matches. -/
structure StrongClassBAF (K : AbstractElementaryClass.{u}) (M N : Model K.τ) where
  α : ℕ → Type u
  xs : ∀ n, α n → M.carrier
  ys : ∀ n, α n → N.carrier
  restr : ∀ n, α n → α (n + 1)
  xs_restr : ∀ n i, xs (n + 1) (restr n i) = xs n i
  ys_restr : ∀ n i, ys (n + 1) (restr n i) = ys n i
  matched : ∀ n, SameStrongClass K (xs n) (ys n)
  exh_M : ∀ x : M.carrier, ∃ n i, xs n i = x
  exh_N : ∀ y : N.carrier, ∃ n i, ys n i = y

namespace StrongClassBAF

variable {K : AbstractElementaryClass.{u}} {M N : Model K.τ}

/-- Cast an index along equality of stages. -/
def castα (B : StrongClassBAF K M N) {n m : ℕ} (h : n = m) (i : B.α n) : B.α m :=
  cast (congrArg B.α h) i

theorem xs_castα (B : StrongClassBAF K M N) {n m : ℕ} (h : n = m) (i : B.α n) :
    B.xs m (B.castα h i) = B.xs n i := by
  cases h; rfl

theorem ys_castα (B : StrongClassBAF K M N) {n m : ℕ} (h : n = m) (i : B.α n) :
    B.ys m (B.castα h i) = B.ys n i := by
  cases h; rfl

/-- Lift an index from stage `n` by `k` steps. -/
def lift (B : StrongClassBAF K M N) (n : ℕ) (i : B.α n) : ∀ k, B.α (n + k)
  | 0 => i
  | k + 1 =>
      castα B (Nat.add_assoc n k 1) <|
        B.restr (n + k) (lift B n i k)

theorem xs_lift (B : StrongClassBAF K M N) (n : ℕ) (i : B.α n) :
    ∀ k, B.xs (n + k) (B.lift n i k) = B.xs n i
  | 0 => rfl
  | k + 1 => by
    change B.xs (n + (k + 1))
        (castα B (Nat.add_assoc n k 1) (B.restr (n + k) (B.lift n i k))) =
      B.xs n i
    rw [xs_castα B (Nat.add_assoc n k 1), B.xs_restr (n + k), xs_lift B n i k]

theorem ys_lift (B : StrongClassBAF K M N) (n : ℕ) (i : B.α n) :
    ∀ k, B.ys (n + k) (B.lift n i k) = B.ys n i
  | 0 => rfl
  | k + 1 => by
    change B.ys (n + (k + 1))
        (castα B (Nat.add_assoc n k 1) (B.restr (n + k) (B.lift n i k))) =
      B.ys n i
    rw [ys_castα B (Nat.add_assoc n k 1), B.ys_restr (n + k), ys_lift B n i k]

/-- The partial match as a total function on `|M|`. -/
noncomputable def toFun (B : StrongClassBAF K M N) : M.carrier → N.carrier :=
  fun x =>
    B.ys (Classical.choose (B.exh_M x))
      (Classical.choose (Classical.choose_spec (B.exh_M x)))

theorem toFun_xs (B : StrongClassBAF K M N) (n : ℕ) (i : B.α n) :
    B.toFun (B.xs n i) = B.ys n i := by
  classical
  set x := B.xs n i
  set m := Classical.choose (B.exh_M x)
  set j := Classical.choose (Classical.choose_spec (B.exh_M x))
  have hxj : B.xs m j = x := Classical.choose_spec (Classical.choose_spec (B.exh_M x))
  change B.ys m j = B.ys n i
  let iL := B.lift n i m
  let jR0 := B.lift m j n
  let jR := B.castα (Nat.add_comm m n) jR0
  have hxsL : B.xs (n + m) iL = B.xs n i := B.xs_lift n i m
  have hxsR : B.xs (n + m) jR = B.xs m j :=
    (B.xs_castα (Nat.add_comm m n) jR0).trans (B.xs_lift m j n)
  have hysL : B.ys (n + m) iL = B.ys n i := B.ys_lift n i m
  have hysR : B.ys (n + m) jR = B.ys m j :=
    (B.ys_castα (Nat.add_comm m n) jR0).trans (B.ys_lift m j n)
  have hmatch := B.matched (n + m)
  have : B.xs (n + m) iL = B.xs (n + m) jR := by
    rw [hxsL, hxsR, hxj]
  have hy :=
    (sameStrongClass_preserves_eq K (B.xs (n + m)) (B.ys (n + m)) hmatch iL jR).mp this
  calc
    B.ys m j = B.ys (n + m) jR := hysR.symm
    _ = B.ys (n + m) iL := hy.symm
    _ = B.ys n i := hysL

theorem toFun_injective (B : StrongClassBAF K M N) : Injective B.toFun := by
  intro x₁ x₂ hf
  obtain ⟨n₁, i₁, rfl⟩ := B.exh_M x₁
  obtain ⟨n₂, i₂, rfl⟩ := B.exh_M x₂
  rw [B.toFun_xs n₁ i₁, B.toFun_xs n₂ i₂] at hf
  let iL := B.lift n₁ i₁ n₂
  let iR0 := B.lift n₂ i₂ n₁
  let iR := B.castα (Nat.add_comm n₂ n₁) iR0
  have hxsL : B.xs (n₁ + n₂) iL = B.xs n₁ i₁ := B.xs_lift n₁ i₁ n₂
  have hxsR : B.xs (n₁ + n₂) iR = B.xs n₂ i₂ :=
    (B.xs_castα (Nat.add_comm n₂ n₁) iR0).trans (B.xs_lift n₂ i₂ n₁)
  have hysL : B.ys (n₁ + n₂) iL = B.ys n₁ i₁ := B.ys_lift n₁ i₁ n₂
  have hysR : B.ys (n₁ + n₂) iR = B.ys n₂ i₂ :=
    (B.ys_castα (Nat.add_comm n₂ n₁) iR0).trans (B.ys_lift n₂ i₂ n₁)
  have hmatch := B.matched (n₁ + n₂)
  have : B.ys (n₁ + n₂) iL = B.ys (n₁ + n₂) iR := by
    rw [hysL, hysR, hf]
  have hx :=
    (sameStrongClass_preserves_eq K (B.xs (n₁ + n₂)) (B.ys (n₁ + n₂)) hmatch iL iR).mpr this
  calc
    B.xs n₁ i₁ = B.xs (n₁ + n₂) iL := hxsL.symm
    _ = B.xs (n₁ + n₂) iR := hx
    _ = B.xs n₂ i₂ := hxsR

theorem toFun_surjective (B : StrongClassBAF K M N) : Surjective B.toFun := by
  intro y
  obtain ⟨n, i, rfl⟩ := B.exh_N y
  exact ⟨B.xs n i, B.toFun_xs n i⟩

/-- Lift an appearance at stage `n ≤ N₀` up to stage `N₀`. -/
theorem exists_at_stage (B : StrongClassBAF K M N) (n N₀ : ℕ) (h : n ≤ N₀) (i : B.α n) :
    ∃ i' : B.α N₀, B.xs N₀ i' = B.xs n i ∧ B.ys N₀ i' = B.ys n i := by
  let k := N₀ - n
  have hsum : n + k = N₀ := Nat.add_sub_of_le h
  refine ⟨B.castα hsum (B.lift n i k), ?_, ?_⟩
  · exact (B.xs_castα hsum _).trans (B.xs_lift n i k)
  · exact (B.ys_castα hsum _).trans (B.ys_lift n i k)

theorem local_embeddings (B : StrongClassBAF K M N) (s : Finset M.carrier) :
    ∃ e : M.carrier ↪[K.τ] N.carrier, ∀ x ∈ s, e x = B.toFun x := by
  classical
  -- For each `x ∈ s`, pick a witnessing stage; take the max.
  let wit (z : { x // x ∈ s }) : ℕ × Σ' n : ℕ, B.α n := by
    classical
    let n := Classical.choose (B.exh_M z.1)
    let h := Classical.choose_spec (B.exh_M z.1)
    exact (n, ⟨n, Classical.choose h⟩)
  let N₀ : ℕ := s.attach.sup fun z => (wit z).1
  obtain ⟨e, _he, het⟩ := B.matched N₀
  refine ⟨e, ?_⟩
  intro x hx
  let z : { x // x ∈ s } := ⟨x, hx⟩
  have hn : (wit z).1 ≤ N₀ := Finset.le_sup (f := fun z => (wit z).1) (Finset.mem_attach s z)
  -- Recover the actual index: wit stores (n, ⟨n, i⟩) with xs n i = x.
  set n := Classical.choose (B.exh_M x)
  set hspec := Classical.choose_spec (B.exh_M x)
  set i := Classical.choose hspec
  have hxi : B.xs n i = x := Classical.choose_spec hspec
  have hn' : n ≤ N₀ := by
    -- `wit z` uses the same chooses on `z.1 = x`.
    change (wit z).1 ≤ N₀ at hn
    simpa [wit, z] using hn
  obtain ⟨i', hxs, hys⟩ := B.exists_at_stage n N₀ hn' i
  have : e x = B.ys N₀ i' := by simpa [hxs.trans hxi] using het i'
  have : B.toFun x = B.ys N₀ i' := by
    rw [← hxi, B.toFun_xs n i, hys.symm]
  exact ‹e x = B.ys N₀ i'›.trans this.symm

/-- **Infra: countable SameStrongClass back-and-forth ⇒ structure isomorphism.** -/
noncomputable def toLanguageEquiv (B : StrongClassBAF K M N) :
    M.carrier ≃[K.τ] N.carrier :=
  languageEquiv_of_bijective_local_embeddings B.toFun B.toFun_injective B.toFun_surjective
    B.local_embeddings

theorem toLanguageEquiv_xs (B : StrongClassBAF K M N) (n : ℕ) (i : B.α n) :
    B.toLanguageEquiv (B.xs n i) = B.ys n i :=
  B.toFun_xs n i

end StrongClassBAF

/-- Package form used by Prop 4.3: a countable BAF sequence yields an isomorphism
matching the stage-0 tuples. -/
theorem countable_back_and_forth_iso (K : AbstractElementaryClass.{u})
    {M N : Model K.τ} (B : StrongClassBAF K M N) :
    ∃ e : M.carrier ≃[K.τ] N.carrier, ∀ i, e (B.xs 0 i) = B.ys 0 i :=
  ⟨B.toLanguageEquiv, fun i => B.toLanguageEquiv_xs 0 i⟩

end
end AEC
