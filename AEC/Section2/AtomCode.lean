module

public import AEC.Section2.Enumeration
public import AEC.Section2.DirectedLimit

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- A model enumerated by the ordinals below `LS(K)`, repetitions allowed. -/
structure Enumerated (K : AbstractElementaryClass.{u}) where
  model : Model K.τ
  enum : Enum K → model.carrier
  surj : Function.Surjective enum

/-- The quantifier-free diagram of an enumeration: which names are equal, which relations
hold, and a name for each function value. -/
structure AtomCode (K : AbstractElementaryClass.{u}) where
  same : Enum K → Enum K → Prop
  hold : ∀ {k : ℕ}, K.τ.Relations k → (Fin k → Enum K) → Prop
  apply : ∀ {k : ℕ}, K.τ.Functions k → (Fin k → Enum K) → Enum K

/-- The least enumeration name of an element. A well-ordered set of names has one least
element, whichever nonempty-proof is used to select it. -/
noncomputable def Enumerated.leastName (E : Enumerated K) (x : E.model.carrier) : Enum K :=
  WellFoundedLT.min {η | E.enum η = x}
    ⟨Classical.choose (E.surj x), Classical.choose_spec (E.surj x)⟩

theorem WellFoundedLT.not_lt_min_of {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (s : Set α) (h : s.Nonempty) {x : α} (hx : x ∈ s) : ¬ x < WellFoundedLT.min s h :=
  (Classical.choose_spec (wellFounded_lt.has_min s h)).2 x hx

theorem WellFoundedLT.min_unique {α : Type u} [LinearOrder α] [WellFoundedLT α]
    (s : Set α) (h₁ h₂ : s.Nonempty) :
    WellFoundedLT.min s h₁ = WellFoundedLT.min s h₂ := by
  have h12 : WellFoundedLT.min s h₁ ≤ WellFoundedLT.min s h₂ :=
    not_lt.mp (WellFoundedLT.not_lt_min_of s h₁ (wellFounded_lt.min_mem s h₂))
  have h21 : WellFoundedLT.min s h₂ ≤ WellFoundedLT.min s h₁ :=
    not_lt.mp (WellFoundedLT.not_lt_min_of s h₂ (wellFounded_lt.min_mem s h₁))
  exact le_antisymm h12 h21

theorem Enumerated.enum_leastName (E : Enumerated K) (x : E.model.carrier) :
    E.enum (E.leastName x) = x := by
  have h := wellFounded_lt.min_mem {η : Enum K | E.enum η = x}
    ⟨Classical.choose (E.surj x), Classical.choose_spec (E.surj x)⟩
  simpa [Enumerated.leastName, Set.mem_ofPred_eq] using h

theorem AtomCode.ext {a b : AtomCode K}
    (hs : ∀ η ζ, a.same η ζ = b.same η ζ)
    (hh : ∀ {k} (r : K.τ.Relations k) (xs : Fin k → Enum K), a.hold r xs = b.hold r xs)
    (ha : ∀ {k} (f : K.τ.Functions k) (xs : Fin k → Enum K), a.apply f xs = b.apply f xs) :
    a = b := by
  cases a
  cases b
  congr
  · funext η ζ
    exact hs η ζ
  · funext k r xs
    exact hh r xs
  · funext k f xs
    exact ha f xs

/-- Read the diagram off an enumerated model. Function values are recorded by their least name,
so the diagram depends on the enumeration only. -/
noncomputable def AtomCode.read (E : Enumerated K) : AtomCode K where
  same η ζ := E.enum η = E.enum ζ
  hold r xs := Language.Structure.RelMap r (E.enum ∘ xs)
  apply f xs := E.leastName (Language.Structure.funMap f (E.enum ∘ xs))

/-- Equal carriers and equal enumerations determine the same diagram. The least name of a
value does not depend on which surjectivity proof is used. -/
theorem AtomCode.read_congr {L R : Model K.τ} (hmodel : L = R)
    (eL : Enum K → L.carrier) (eR : Enum K → R.carrier)
    (sL : Function.Surjective eL) (sR : Function.Surjective eR)
    (henum : ∀ η, HEq (eL η) (eR η)) :
    AtomCode.read ⟨L, eL, sL⟩ = AtomCode.read ⟨R, eR, sR⟩ := by
  subst hmodel
  have hfun : eL = eR := funext fun η => eq_of_heq (henum η)
  subst hfun
  refine AtomCode.ext ?_ ?_ ?_
  · intro η ζ
    rfl
  · intro k r xs
    rfl
  · intro k f xs
    let x : L.carrier := Language.Structure.funMap f (eL ∘ xs)
    show WellFoundedLT.min {η | eL η = x}
        ⟨Classical.choose (sL x), Classical.choose_spec (sL x)⟩ =
      WellFoundedLT.min {η | eL η = x}
        ⟨Classical.choose (sR x), Classical.choose_spec (sR x)⟩
    exact WellFoundedLT.min_unique _ _ _

theorem AtomCode.read_apply (E : Enumerated K) {k : ℕ} (f : K.τ.Functions k)
    (xs : Fin k → Enum K) :
    E.enum ((AtomCode.read E).apply f xs) =
      Language.Structure.funMap f (E.enum ∘ xs) := by
  simpa [AtomCode.read] using
    E.enum_leastName (Language.Structure.funMap f (E.enum ∘ xs))

/-- Names that agree in one enumeration agree in the other when the diagrams coincide. -/
theorem AtomCode.same_iff {E F : Enumerated K} (h : AtomCode.read E = AtomCode.read F)
    (η ζ : Enum K) : E.enum η = E.enum ζ ↔ F.enum η = F.enum ζ := by
  have hs : (AtomCode.read E).same η ζ ↔ (AtomCode.read F).same η ζ := by rw [h]
  simpa [AtomCode.read] using hs

theorem AtomCode.hold_iff {E F : Enumerated K} (h : AtomCode.read E = AtomCode.read F)
    {k : ℕ} (r : K.τ.Relations k) (xs : Fin k → Enum K) :
    Language.Structure.RelMap r (E.enum ∘ xs) ↔
      Language.Structure.RelMap r (F.enum ∘ xs) := by
  have hs : (AtomCode.read E).hold r xs ↔ (AtomCode.read F).hold r xs := by rw [h]
  simpa [AtomCode.read] using hs

theorem AtomCode.apply_eq {E F : Enumerated K} (h : AtomCode.read E = AtomCode.read F)
    {k : ℕ} (f : K.τ.Functions k) (xs : Fin k → Enum K) :
    (AtomCode.read E).apply f xs = (AtomCode.read F).apply f xs := by
  rw [h]

/-- The name chosen for an element may be replaced by any name of the same element. -/
theorem AtomCode.enum_choose_eq (E : Enumerated K) (x : E.model.carrier) (η : Enum K)
    (hη : E.enum η = x) :
    E.enum (Classical.choose (E.surj x)) = E.enum η := by
  rw [Classical.choose_spec (E.surj x), hη]

/-- A chosen name for `x` in `E`. -/
noncomputable def Enumerated.name (E : Enumerated K) (x : E.model.carrier) : Enum K :=
  Classical.choose (E.surj x)

theorem Enumerated.enum_name (E : Enumerated K) (x : E.model.carrier) :
    E.enum (E.name x) = x :=
  Classical.choose_spec (E.surj x)

/-- Send each element of `E` to the element of `F` named by the same enumeration index.
Equal diagrams make this a bijective embedding. -/
noncomputable def codeEmbedding {E F : Enumerated K} (h : AtomCode.read E = AtomCode.read F) :
    E.model.carrier ↪[K.τ] F.model.carrier where
  toFun x := F.enum (E.name x)
  inj' x y hxy := by
    have hsame := (AtomCode.same_iff h (E.name x) (E.name y)).mpr hxy
    rw [E.enum_name x, E.enum_name y] at hsame
    exact hsame
  map_fun' {k} f xs := by
    let names : Fin k → Enum K := fun i => E.name (xs i)
    have hE : E.enum ((AtomCode.read E).apply f names) =
        Language.Structure.funMap f xs := by
      rw [AtomCode.read_apply]
      congr 1
      funext i
      exact E.enum_name (xs i)
    have hF : F.enum ((AtomCode.read F).apply f names) =
        Language.Structure.funMap f (fun i => F.enum (E.name (xs i))) := by
      have hread := AtomCode.read_apply F f names
      have hcomp : (F.enum ∘ names) = fun i => F.enum (E.name (xs i)) := by
        funext i
        rfl
      simpa [hcomp] using hread
    have happ : (AtomCode.read E).apply f names = (AtomCode.read F).apply f names :=
      AtomCode.apply_eq h f names
    have hkernel : E.enum (E.name (Language.Structure.funMap f xs)) =
        E.enum ((AtomCode.read E).apply f names) := by
      rw [E.enum_name, hE]
    have htransport := (AtomCode.same_iff h _ _).mp hkernel
    rw [happ] at htransport
    rw [htransport]
    exact hF
  map_rel' {k} r xs := by
    let names : Fin k → Enum K := fun i => E.name (xs i)
    have hleft : ((fun x => F.enum (E.name x)) ∘ xs) = F.enum ∘ names := by
      funext i
      rfl
    have hright : xs = fun i => E.enum (names i) := by
      funext i
      exact (E.enum_name (xs i)).symm
    rw [hleft, hright]
    exact (AtomCode.hold_iff h r names).symm

theorem codeEmbedding_surjective {E F : Enumerated K} (h : AtomCode.read E = AtomCode.read F) :
    Function.Surjective (codeEmbedding h) := by
  intro y
  obtain ⟨η, hη⟩ := F.surj y
  refine ⟨E.enum η, ?_⟩
  have hname : E.enum (E.name (E.enum η)) = E.enum η := E.enum_name (E.enum η)
  have htrans := (AtomCode.same_iff h _ _).mp hname
  show F.enum (E.name (E.enum η)) = y
  rw [htrans, hη]

/-- Equal diagrams give a structure equivalence. -/
noncomputable def codeEquiv {E F : Enumerated K} (h : AtomCode.read E = AtomCode.read F) :
    E.model.carrier ≃[K.τ] F.model.carrier :=
  embeddingEquivOfSurjective (codeEmbedding h) (codeEmbedding_surjective h)

/-- A structure equivalence out of a member of `K` is a strong embedding. -/
theorem codeStrong {E F : Enumerated K} (hE : K.Mem E.model)
    (h : AtomCode.read E = AtomCode.read F) :
    K.Strong (codeEquiv h).toEmbedding :=
  strong_of_equiv K (codeEquiv h) hE

end
end AEC
