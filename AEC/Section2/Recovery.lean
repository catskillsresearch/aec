module

public import AEC.Section2.ValidCode
public import AEC.Section2.DirectedLimit
public import AEC.Section2.SmallStrongSubmodel
public import AEC.Section2.FiniteHull
public import AEC.Section2.SpectrumBound
public import AEC.Section2.Rename
public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

variable {K : AbstractElementaryClass.{u}}

/-- The canonical language for AECs of Löwenheim–Skolem bound `lam`. -/
def canTau (lam : Cardinal.{u}) : Tau.{u} where
  Functions _ := Below lam
  Relations _ := Below lam

/-- The type of small codes over the canonical language of bound `lam`. -/
def CanCode (lam : Cardinal.{u}) : Type u :=
  SmallCode (canTau lam) lam

/-- A valid ordinal code: an ordinal language together with a valid small code. -/
def ValidOrdCode (lam : Cardinal.{u}) : Type u :=
  {c : OrdCode lam // IsValidCode lam c.2}

/-- The replacement bound on all valid ordinal codes (Proposition 2.3). -/
noncomputable def canBound (lam : Cardinal.{u}) : Cardinal.{u} :=
  Cardinal.sum (fun (c : ValidOrdCode lam) =>
    spectrumBound (Classical.choose c.2.decodes))

theorem spectrumBound_le_canBound {lam : Cardinal.{u}}
    (c : OrdCode lam) [hc : IsValidCode lam c.2] :
    spectrumBound (Classical.choose hc.decodes) ≤ canBound lam :=
  le_sum (fun (c : ValidOrdCode lam) =>
    spectrumBound (Classical.choose c.2.decodes)) ⟨c, hc⟩

/-- The canonical small code of an AEC at Löwenheim–Skolem bound `lam`. -/
def aecCode (K : AbstractElementaryClass.{u}) (lam : Cardinal.{u}) : SmallCode K.τ lam where
  model := {M | K.Mem M.toModel}
  pair := {p | K.Mem p.big.toModel ∧ K.Mem p.small.toModel ∧
    K.Strong (M := p.small.toModel) (N := p.big.toModel) p.incl}
  pair_models := fun _p hp => ⟨hp.1, hp.2.1⟩

theorem aecCode_model_mem (lam : Cardinal.{u}) (M : SmallModel K.τ lam) :
    M ∈ (aecCode K lam).model ↔ K.Mem M.toModel := by
  simp [aecCode]

theorem aecCode_pair_mem (lam : Cardinal.{u}) (p : SmallPair K.τ lam) :
    p ∈ (aecCode K lam).pair ↔
      K.Mem p.big.toModel ∧ K.Mem p.small.toModel ∧
        K.Strong (M := p.small.toModel) (N := p.big.toModel) p.incl := by
  simp [aecCode]

/-- Each component of a coded presentation belongs to `K`. -/
theorem codedPresentation_obj_mem {lam : Cardinal.{u}}
    (P : CodedPresentation (aecCode K lam)) (i : P.system.ι) :
    K.Mem (P.system.obj i) := by
  have hrep : (P.rep i) ∈ (aecCode K lam).model := P.rep_mem i
  have hmem : K.Mem (P.rep i).toModel := (aecCode_model_mem lam (P.rep i)).mp hrep
  have hiso : Nonempty ((P.rep i).toModel.carrier ≃[K.τ] (P.system.obj i).carrier) :=
    ⟨(P.iso i).symm⟩
  exact K.iso_closed hiso hmem

/-- Each transition embedding of a coded presentation is strong in `K`. -/
theorem codedPresentation_map_strong {lam : Cardinal.{u}}
    (P : CodedPresentation (aecCode K lam)) {i j : P.system.ι}
    (hij : P.system.rel i j) :
    K.Strong (P.system.map hij) := by
  obtain ⟨p, hp, _hp_small, _hp_big, eSmall, eBig, hcomm⟩ := P.pair_spec hij
  have hstrong_p : K.Strong (M := p.small.toModel) (N := p.big.toModel) p.incl :=
    ((aecCode_pair_mem lam p).mp hp).2.2
  have htrans : K.Strong (M := P.system.obj i) (N := p.big.toModel)
      (eBig.toEmbedding.comp (P.system.map hij)) := by
    have hcomm_eq : (eBig.toEmbedding.comp (P.system.map hij)) = p.incl.comp eSmall.toEmbedding :=
      hcomm.symm
    rw [hcomm_eq]
    have hmem_small : K.Mem (P.system.obj i) := codedPresentation_obj_mem P i
    have heSmall_strong : K.Strong (M := P.system.obj i) (N := p.small.toModel) eSmall.toEmbedding :=
      @strong_of_equiv K (P.system.obj i) p.small.toModel eSmall hmem_small
    exact @K.strong_trans (P.system.obj i) p.small.toModel p.big.toModel
      eSmall.toEmbedding p.incl heSmall_strong hstrong_p
  have hmem_j : K.Mem (P.system.obj j) := codedPresentation_obj_mem P j
  have heBig_strong : K.Strong (M := P.system.obj j) (N := p.big.toModel) eBig.toEmbedding :=
    @strong_of_equiv K (P.system.obj j) p.big.toModel eBig hmem_j
  exact @K.coherence (P.system.obj i) (P.system.obj j) p.big.toModel
    (P.system.map hij) (eBig.toEmbedding.comp (P.system.map hij)) eBig.toEmbedding
    htrans heBig_strong rfl

/-- Direct limit of a coded presentation belongs to `K`. -/
theorem codedPresentation_limit_mem {lam : Cardinal.{u}}
    (P : CodedPresentation (aecCode K lam))
    (U : DirectLimit P.system) :
    K.Mem U.obj :=
  directLimit_mem K P.system
    (codedPresentation_obj_mem P)
    (fun {i j} hij => codedPresentation_map_strong P hij)
    U

/-- If a structure decodes from `aecCode`, it belongs to `K`. -/
theorem mem_of_decodedMem {lam : Cardinal.{u}} {M : Model K.τ}
    (h : DecodedMem (aecCode K lam) M) : K.Mem M := by
  obtain ⟨P, U, ⟨e⟩⟩ := h
  have hU : K.Mem U.obj := codedPresentation_limit_mem P U
  exact K.iso_closed ⟨e⟩ hU

/-- A small model can be presented as an isomorphic small ordinal model. -/
noncomputable def smallModelOfCardLe {lam : Cardinal.{u}} (M : Model K.τ)
    (hcard : Model.card M ≤ lam) :
    {rep : SmallModel K.τ lam // Nonempty (M.carrier ≃[K.τ] rep.toModel.carrier)} := by
  have hle : #(M.carrier) ≤ #(Below lam) := by
    rw [← Model.card, Cardinal.mk_ord_toType]
    exact hcard
  have h_ne := (Cardinal.le_def M.carrier (Below lam)).mp hle
  let f := Classical.choice h_ne
  let D : Set (Below lam) := Set.range f
  let e : M.carrier ≃ ↥D := Equiv.ofInjective f f.injective
  let str : K.τ.Structure (↥D) := _root_.Equiv.inducedStructure e
  let rep : SmallModel K.τ lam := ⟨D, str⟩
  let iso : M.carrier ≃[K.τ] rep.toModel.carrier :=
    _root_.Equiv.inducedStructureEquiv e
  exact ⟨rep, ⟨iso⟩⟩

/-- A small strong submodel of `M` presented on ordinals below `lam`. -/
structure SubmodelRep (K : AbstractElementaryClass.{u}) (lam : Cardinal.{u})
    (M : Model K.τ) where
  model : SmallModel K.τ lam
  mem : model ∈ (aecCode K lam).model
  incl : model.toModel.carrier ↪[K.τ] M.carrier
  strong : K.Strong incl

theorem submodelRep_nonempty {lam : Cardinal.{u}} (hLS : isLSBound K lam)
    {M : Model K.τ} (hM : K.Mem M) : Nonempty (SubmodelRep K lam M) := by
  have hall := hLS.2.2 M hM ∅
  obtain ⟨N, f, hN, hf, _, hcardN⟩ := hall
  have hcard : Model.card N ≤ lam := by
    have hle : Model.card N ≤ # (∅ : Set M.carrier) + lam := hcardN
    simpa using hle
  obtain ⟨rep, ⟨iso⟩⟩ := smallModelOfCardLe N hcard
  have hmem : rep ∈ (aecCode K lam).model := by
    rw [aecCode_model_mem]
    exact K.iso_closed ⟨iso⟩ hN
  let incl := f.comp iso.symm.toEmbedding
  have hstrong : K.Strong incl := by
    have hequiv_strong : K.Strong (M := rep.toModel) (N := N) iso.symm.toEmbedding :=
      @strong_of_equiv K rep.toModel N iso.symm (by rw [← aecCode_model_mem]; exact hmem)
    exact K.strong_trans iso.symm.toEmbedding f hequiv_strong hf
  exact ⟨⟨rep, hmem, incl, hstrong⟩⟩

/-- The directed order between submodels: inclusion of their ranges in `M`. -/
def SubmodelRel {lam : Cardinal.{u}} {M : Model K.τ}
    (A B : SubmodelRep K lam M) : Prop :=
  Set.range A.incl ⊆ Set.range B.incl

theorem submodelRel_refl {lam : Cardinal.{u}} {M : Model K.τ}
    (A : SubmodelRep K lam M) : SubmodelRel A A :=
  Set.Subset.rfl

theorem submodelRel_trans {lam : Cardinal.{u}} {M : Model K.τ}
    {A B C : SubmodelRep K lam M} (hab : SubmodelRel A B) (hbc : SubmodelRel B C) :
    SubmodelRel A C :=
  Set.Subset.trans hab hbc

theorem submodelRel_directed {lam : Cardinal.{u}} (hLS : isLSBound K lam)
    {M : Model K.τ} (hM : K.Mem M) (A B : SubmodelRep K lam M) :
    ∃ C : SubmodelRep K lam M, SubmodelRel A C ∧ SubmodelRel B C := by
  have hcardA : #(Set.range A.incl) ≤ lam := by
    have hrange : #(Set.range A.incl) ≤ #A.model.toModel.carrier := Cardinal.mk_range_le
    have hdom : #A.model.toModel.carrier ≤ #(Below lam) := by
      dsimp [SmallModel.toModel]
      exact Cardinal.mk_subtype_le _
    rw [Cardinal.mk_ord_toType] at hdom
    exact hrange.trans hdom
  have hcardB : #(Set.range B.incl) ≤ lam := by
    have hrange : #(Set.range B.incl) ≤ #B.model.toModel.carrier := Cardinal.mk_range_le
    have hdom : #B.model.toModel.carrier ≤ #(Below lam) := by
      dsimp [SmallModel.toModel]
      exact Cardinal.mk_subtype_le _
    rw [Cardinal.mk_ord_toType] at hdom
    exact hrange.trans hdom
  have hcard_union : #(↥(Set.range A.incl ∪ Set.range B.incl)) ≤ lam := by
    have hle : #(↥(Set.range A.incl ∪ Set.range B.incl)) ≤
        #(↥(Set.range A.incl)) + #(↥(Set.range B.incl)) :=
      Cardinal.mk_union_le (Set.range A.incl) (Set.range B.incl)
    have hsum : #(↥(Set.range A.incl)) + #(↥(Set.range B.incl)) ≤ lam + lam :=
      add_le_add hcardA hcardB
    rw [add_eq_self hLS.1] at hsum
    exact hle.trans hsum
  obtain ⟨N, f, hN, hf, hcov, hcardN⟩ := hLS.2.2 M hM (Set.range A.incl ∪ Set.range B.incl)
  have hN_le : Model.card N ≤ lam := by
    have := hcardN.trans (add_le_add hcard_union (le_refl lam))
    rw [add_eq_self hLS.1] at this
    exact this
  obtain ⟨rep, ⟨iso⟩⟩ := smallModelOfCardLe N hN_le
  have hmem : rep ∈ (aecCode K lam).model := by
    rw [aecCode_model_mem]
    exact K.iso_closed ⟨iso⟩ hN
  let incl := f.comp iso.symm.toEmbedding
  have hstrong : K.Strong incl := by
    have hequiv_strong : K.Strong (M := rep.toModel) (N := N) iso.symm.toEmbedding :=
      @strong_of_equiv K rep.toModel N iso.symm (by rw [← aecCode_model_mem]; exact hmem)
    exact K.strong_trans iso.symm.toEmbedding f hequiv_strong hf
  let C : SubmodelRep K lam M := ⟨rep, hmem, incl, hstrong⟩
  have hrangeC : Set.range incl = Set.range f := by
    ext x
    simp only [incl, Language.Embedding.comp_apply, Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨iso.symm.toEmbedding y, rfl⟩
    · rintro ⟨y, rfl⟩; exact ⟨iso y, by simp [Language.Equiv.coe_toEmbedding]⟩
  refine ⟨C, ?_, ?_⟩
  · intro x hx
    rw [hrangeC]
    obtain ⟨n, hn⟩ := hcov x (Or.inl hx)
    exact ⟨n, hn⟩
  · intro x hx
    rw [hrangeC]
    obtain ⟨n, hn⟩ := hcov x (Or.inr hx)
    exact ⟨n, hn⟩

theorem factorEmbedding_unique {L : Tau.{u}} {A B C : Type u}
    [L.Structure A] [L.Structure B] [L.Structure C]
    (f : A ↪[L] C) (g : B ↪[L] C) (h₁ h₂ : A ↪[L] B)
    (h_comp₁ : g.comp h₁ = f) (h_comp₂ : g.comp h₂ = f) : h₁ = h₂ := by
  ext x
  apply g.injective
  have := congrFun (congrArg (⇑) (h_comp₁.trans h_comp₂.symm)) x
  simpa [Language.Embedding.comp_apply] using this

/-- The directed system of small strong submodels covering `M`. -/
noncomputable def submodelSystem {lam : Cardinal.{u}} (hLS : isLSBound K lam)
    {M : Model K.τ} (hM : K.Mem M) : DirectedSystem K.τ where
  ι := SubmodelRep K lam M
  nonempty := submodelRep_nonempty hLS hM
  rel := SubmodelRel
  refl := submodelRel_refl
  trans := fun hab hbc => submodelRel_trans hab hbc
  directed := submodelRel_directed hLS hM
  obj A := A.model.toModel
  map {A B} hab := factorEmbedding A.incl B.incl (fun a => by
    obtain ⟨b, hb⟩ := hab ⟨a, rfl⟩
    exact ⟨b, hb⟩)
  map_refl A := by
    apply factorEmbedding_unique A.incl A.incl
    · exact factorEmbedding_comp A.incl A.incl _
    · exact Language.Embedding.comp_refl _
  map_trans {A B C} hab hbc := by
    apply factorEmbedding_unique A.incl C.incl
    · exact factorEmbedding_comp A.incl C.incl _
    · have h1 : C.incl.comp (factorEmbedding B.incl C.incl (fun a => by obtain ⟨b, hb⟩ := hbc ⟨a, rfl⟩; exact ⟨b, hb⟩)) = B.incl :=
        factorEmbedding_comp B.incl C.incl _
      have h2 : B.incl.comp (factorEmbedding A.incl B.incl (fun a => by obtain ⟨b, hb⟩ := hab ⟨a, rfl⟩; exact ⟨b, hb⟩)) = A.incl :=
        factorEmbedding_comp A.incl B.incl _
      change (C.incl.comp (factorEmbedding B.incl C.incl _)).comp (factorEmbedding A.incl B.incl _) = A.incl
      rw [h1, h2]

/-- The presentation of `M` by its small strong submodels. -/
noncomputable def submodelPresentation {lam : Cardinal.{u}} (hLS : isLSBound K lam)
    {M : Model K.τ} (hM : K.Mem M) : CodedPresentation (aecCode K lam) where
  system := submodelSystem hLS hM
  rep A := A.model
  rep_mem A := A.mem
  iso A := Language.Equiv.refl _ _
  pair_spec {A B} hab := by
    let map_AB := (submodelSystem hLS hM).map hab
    have hcomp : B.incl.comp map_AB = A.incl :=
      factorEmbedding_comp A.incl B.incl _
    have hstrong : K.Strong (M := A.model.toModel) (N := B.model.toModel) map_AB :=
      @K.coherence A.model.toModel B.model.toModel M map_AB A.incl B.incl A.strong B.strong hcomp
    let p : SmallPair K.τ lam := ⟨B.model, A.model, map_AB⟩
    have hp : p ∈ (aecCode K lam).pair := by
      rw [aecCode_pair_mem]
      exact ⟨B.mem, A.mem, hstrong⟩
    refine ⟨p, hp, rfl, rfl, Language.Equiv.refl _ _, Language.Equiv.refl _ _, ?_⟩
    ext x
    rfl

/-- The structure equivalence between the direct limit of small submodels and `M`. -/
noncomputable def submodelEquiv {lam : Cardinal.{u}} (hLS : isLSBound K lam)
    {M : Model K.τ} (hM : K.Mem M) :
    (algebraicLimit (submodelSystem hLS hM)).obj.carrier ≃[K.τ] M.carrier := by
  let S := submodelSystem hLS hM
  have Hg : ∀ A B (hab : S.rel A B) (x : (S.obj A).carrier),
      B.incl (S.map hab x) = A.incl x := by
    intro A B hab x
    have hcomp : B.incl.comp (S.map hab) = A.incl :=
      factorEmbedding_comp A.incl B.incl _
    exact congrFun (congrArg (⇑) hcomp) x
  let induced := Language.DirectLimit.lift K.τ (Index S)
    (fun A : Index S => (S.obj A).carrier) (fun A B (h : A ≤ B) => S.map h)
    (fun A => A.incl) Hg
  have hsurj : Function.Surjective induced := by
    intro x
    obtain ⟨N, f, hN, hf, hcov, hcardN⟩ := hLS.2.2 M hM {x}
    have hN_le : Model.card N ≤ lam := by
      have h1 : #({x} : Set M.carrier) = 1 := Cardinal.mk_singleton x
      have hle : Model.card N ≤ 1 + lam := by rw [← h1]; exact hcardN
      have hsum : 1 + lam ≤ lam := by
        rw [add_comm]
        exact add_le_of_le hLS.1 (le_refl _) ((natCast_lt_aleph0 (n := 1)).le.trans hLS.1)
      exact hle.trans hsum
    obtain ⟨rep, ⟨iso⟩⟩ := smallModelOfCardLe N hN_le
    have hmem : rep ∈ (aecCode K lam).model := by
      rw [aecCode_model_mem]
      exact K.iso_closed ⟨iso⟩ hN
    let incl := f.comp iso.symm.toEmbedding
    have hstrong : K.Strong incl := by
      have hequiv_strong : K.Strong (M := rep.toModel) (N := N) iso.symm.toEmbedding :=
        @strong_of_equiv K rep.toModel N iso.symm (by rw [← aecCode_model_mem]; exact hmem)
      exact K.strong_trans iso.symm.toEmbedding f hequiv_strong hf
    let A : SubmodelRep K lam M := ⟨rep, hmem, incl, hstrong⟩
    obtain ⟨n, hn⟩ := hcov x (Set.mem_singleton x)
    refine ⟨(algebraicLimit S).canon A (iso n), ?_⟩
    have hlift := Language.DirectLimit.lift_of (L := K.τ) (ι := Index S)
      (G := fun A : Index S => (S.obj A).carrier)
      (f := fun A B (h : A ≤ B) => S.map h) (fun A => A.incl) Hg (i := A) (iso n)
    have h_app : induced ((algebraicLimit S).canon A (iso n)) = A.incl (iso n) := hlift
    rw [h_app]
    have h_eval : A.incl (iso n) = f n := by
      dsimp [A, incl]
      simp only [Language.Embedding.comp_apply, Language.Equiv.symm_apply_apply]
    rw [h_eval, hn]
  exact embeddingEquivOfSurjective induced hsurj

theorem decodedMem_of_mem {lam : Cardinal.{u}} (hLS : isLSBound K lam)
    {M : Model K.τ} (hM : K.Mem M) : DecodedMem (aecCode K lam) M :=
  ⟨submodelPresentation hLS hM, algebraicLimit (submodelSystem hLS hM), ⟨submodelEquiv hLS hM⟩⟩

theorem mem_iff_decodedMem {lam : Cardinal.{u}} (hLS : isLSBound K lam)
    (M : Model K.τ) : K.Mem M ↔ DecodedMem (aecCode K lam) M :=
  ⟨decodedMem_of_mem hLS, mem_of_decodedMem⟩

theorem submodelEquiv_canon {lam : Cardinal.{u}} (hLS : isLSBound K lam)
    {M : Model K.τ} (hM : K.Mem M) (A : SubmodelRep K lam M)
    (y : (submodelSystem hLS hM).obj A |>.carrier) :
    submodelEquiv hLS hM ((algebraicLimit (submodelSystem hLS hM)).canon A y) = A.incl y := by
  dsimp [submodelEquiv, embeddingEquivOfSurjective]
  exact Language.DirectLimit.lift_of (L := K.τ) (ι := Index (submodelSystem hLS hM))
    (G := fun A : Index (submodelSystem hLS hM) => ((submodelSystem hLS hM).obj A).carrier)
    (f := fun A B (h : A ≤ B) => (submodelSystem hLS hM).map h) (fun A => A.incl)
    (fun A B hab x => by
      have hcomp : B.incl.comp ((submodelSystem hLS hM).map hab) = A.incl :=
        factorEmbedding_comp A.incl B.incl (fun a => by obtain ⟨b, hb⟩ := hab ⟨a, rfl⟩; exact ⟨b, hb⟩)
      exact congrFun (congrArg (⇑) hcomp) x)
    (i := A) y

theorem decodedStrong_of_strong {lam : Cardinal.{u}} (hLS : isLSBound K lam)
    {M N : Model K.τ} (f : Language.Embedding K.τ M.carrier N.carrier)
    (hf : K.Strong f) : DecodedStrong (aecCode K lam) f := by
  have hM : K.Mem M := K.strong_mem_dom f hf
  have hN : K.Mem N := K.strong_mem_cod f hf
  let small := submodelPresentation hLS hM
  let big := submodelPresentation hLS hN
  let smallLim := algebraicLimit small.system
  let bigLim := algebraicLimit big.system
  let embedIndex (A : SubmodelRep K lam M) : SubmodelRep K lam N :=
    ⟨A.model, A.mem, f.comp A.incl, K.strong_trans A.incl f A.strong hf⟩
  have embedRel {A B : SubmodelRep K lam M} (hab : SubmodelRel A B) :
      SubmodelRel (embedIndex A) (embedIndex B) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    have hy : A.incl y ∈ Set.range B.incl := hab ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨z, by simp [embedIndex, Language.Embedding.comp_apply, hz]⟩
  let stage (A : SubmodelRep K lam M) :
      Language.Embedding K.τ (small.system.obj A).carrier (big.system.obj (embedIndex A)).carrier :=
    Language.Embedding.refl _ _
  have stage_comm {A B : SubmodelRep K lam M} (hab : SubmodelRel A B) :
      (big.system.map (embedRel hab)).comp (stage A) = (stage B).comp (small.system.map hab) := by
    apply factorEmbedding_unique (embedIndex A).incl (embedIndex B).incl
    · exact factorEmbedding_comp (embedIndex A).incl (embedIndex B).incl _
    · ext y
      have hA := congrFun (congrArg (⇑) (factorEmbedding_comp A.incl B.incl (fun a => by obtain ⟨b, hb⟩ := hab ⟨a, rfl⟩; exact ⟨b, hb⟩))) y
      exact congrArg (⇑f) hA
  have subpair (A : SubmodelRep K lam M) :
      ∃ p : SmallPair K.τ lam, p ∈ (aecCode K lam).pair ∧ p.small = small.rep A ∧
        p.big = big.rep (embedIndex A) ∧
        ∃ (eSmall : (small.system.obj A).carrier ≃[K.τ] ↥p.small.domain)
          (eBig : (big.system.obj (embedIndex A)).carrier ≃[K.τ] ↥p.big.domain),
          p.incl.comp eSmall.toEmbedding = eBig.toEmbedding.comp (stage A) := by
    let p : SmallPair K.τ lam := ⟨A.model, A.model, Language.Embedding.refl _ _⟩
    have hp : p ∈ (aecCode K lam).pair := by
      rw [aecCode_pair_mem]
      exact ⟨A.mem, A.mem, K.strong_refl _ (K.strong_mem_dom A.incl A.strong)⟩
    refine ⟨p, hp, rfl, rfl, Language.Equiv.refl _ _, Language.Equiv.refl _ _, ?_⟩
    ext x; rfl
  have Hg : ∀ A B (hab : small.system.rel A B) (x : (small.system.obj A).carrier),
      (bigLim.canon (embedIndex B)) (stage B (small.system.map hab x)) =
        (bigLim.canon (embedIndex A)) (stage A x) := by
    intro A B hab x
    have hcomp := stage_comm hab
    have hleft : (bigLim.canon (embedIndex B)) (stage B (small.system.map hab x)) =
        (bigLim.canon (embedIndex B)) (((big.system.map (embedRel hab)).comp (stage A)) x) := by
      congr 1
      exact congrFun (congrArg (⇑) hcomp.symm) x
    rw [hleft]
    have hcomp_can := congrFun (congrArg (⇑) (bigLim.compat (embedRel hab))) (stage A x)
    exact hcomp_can
  let induced := Language.DirectLimit.lift K.τ (Index small.system)
    (fun A => (small.system.obj A).carrier) (fun A B h => small.system.map h)
    (fun A => (bigLim.canon (embedIndex A)).comp (stage A)) Hg
  have hinduced_comm (A : SubmodelRep K lam M) :
      induced.comp (smallLim.canon A) = (bigLim.canon (embedIndex A)).comp (stage A) := by
    ext x
    exact Language.DirectLimit.lift_of (L := K.τ) (ι := Index small.system)
      (G := fun A => (small.system.obj A).carrier) (f := fun A B h => small.system.map h)
      (fun A => (bigLim.canon (embedIndex A)).comp (stage A)) Hg (i := A) x
  let I : CodedInclusion (aecCode K lam) := {
    big := big
    small := small
    bigLimit := bigLim
    smallLimit := smallLim
    embedIndex := embedIndex
    embedIndex_rel := fun hab => embedRel hab
    stage := stage
    stage_comm := fun hab => stage_comm hab
    subpair := subpair
    induced := induced
    induced_comm := hinduced_comm
  }
  let eM := submodelEquiv hLS hM
  let eN := submodelEquiv hLS hN
  refine ⟨I, eM, eN, ?_⟩
  ext z
  obtain ⟨A, y, rfl⟩ := smallLim.joint z
  have hind : induced (smallLim.canon A y) = bigLim.canon (embedIndex A) y := by
    have h_comm := congrFun (congrArg (⇑) (hinduced_comm A)) y
    exact h_comm
  change eN.toEmbedding (induced ((smallLim.canon A) y)) = f (eM.toEmbedding ((smallLim.canon A) y))
  have hind' : eN.toEmbedding (induced ((smallLim.canon A) y)) =
      eN.toEmbedding ((bigLim.canon (embedIndex A)) y) := congrArg eN.toEmbedding hind
  rw [hind']
  have hM_canon : eM.toEmbedding ((smallLim.canon A) y) = A.incl y := by
    change submodelEquiv hLS hM ((smallLim.canon A) y) = A.incl y
    exact submodelEquiv_canon hLS hM A y
  have hN_canon : eN.toEmbedding ((bigLim.canon (embedIndex A)) y) = (embedIndex A).incl y := by
    change submodelEquiv hLS hN ((bigLim.canon (embedIndex A)) y) = (embedIndex A).incl y
    exact submodelEquiv_canon hLS hN (embedIndex A) y
  rw [hM_canon, hN_canon]
  rfl

/-- The induced map of a coded inclusion is strong in `K`. -/
theorem codedInclusion_induced_strong {lam : Cardinal.{u}}
    (I : CodedInclusion (aecCode K lam)) :
    K.Strong I.induced := by
  have hmemSmall : K.Mem I.smallLimit.obj :=
    codedPresentation_limit_mem I.small I.smallLimit
  have hmemBig : K.Mem I.bigLimit.obj :=
    codedPresentation_limit_mem I.big I.bigLimit
  obtain ⟨L_s, hL_s⟩ := directLimit_in_class K I.small.system
    (codedPresentation_obj_mem I.small)
    (fun {i j} hij => codedPresentation_map_strong I.small hij)
  obtain ⟨L_b, hL_b⟩ := directLimit_in_class K I.big.system
    (codedPresentation_obj_mem I.big)
    (fun {i j} hij => codedPresentation_map_strong I.big hij)
  let e_Ls_alg : (algebraicLimit I.small.system).obj.carrier ≃[K.τ] L_s.obj.carrier :=
    directLimitEquivAlgebraic I.small.system L_s
  let e_Lb_alg : L_b.obj.carrier ≃[K.τ] (algebraicLimit I.big.system).obj.carrier :=
    (directLimitEquivAlgebraic I.big.system L_b).symm
  let e_s_alg : I.smallLimit.obj.carrier ≃[K.τ] (algebraicLimit I.small.system).obj.carrier :=
    (directLimitEquivAlgebraic I.small.system I.smallLimit).symm
  let e_b_alg : (algebraicLimit I.big.system).obj.carrier ≃[K.τ] I.bigLimit.obj.carrier :=
    directLimitEquivAlgebraic I.big.system I.bigLimit
  let e_s : I.smallLimit.obj.carrier ≃[K.τ] L_s.obj.carrier :=
    e_Ls_alg.comp e_s_alg
  let e_b : L_b.obj.carrier ≃[K.τ] I.bigLimit.obj.carrier :=
    e_b_alg.comp e_Lb_alg
  have hcan_b_strong (j : I.big.system.ι) : K.Strong (I.bigLimit.canon j) := by
    have hfactor : I.bigLimit.canon j = e_b.toEmbedding.comp (L_b.canon j) := by
      ext x
      have h1 : e_b (L_b.canon j x) = e_b_alg (e_Lb_alg (L_b.canon j x)) := rfl
      have h_symm : e_Lb_alg (L_b.canon j x) = (algebraicLimit I.big.system).canon j x := by
        apply (directLimitEquivAlgebraic I.big.system L_b).injective
        simp only [e_Lb_alg, Language.Equiv.apply_symm_apply]
        exact (directLimitEquivAlgebraic_canon I.big.system L_b j x).symm
      simp only [Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding]
      rw [h1, h_symm]
      exact (directLimitEquivAlgebraic_canon I.big.system I.bigLimit j x).symm
    rw [hfactor]
    exact K.strong_trans (L_b.canon j) e_b.toEmbedding (hL_b.2.1 j) (strong_of_equiv K e_b hL_b.1)
  have hg_strong (i : I.small.system.ι) : K.Strong
      ((I.bigLimit.canon (I.embedIndex i)).comp (I.stage i)) := by
    have hstage_strong : K.Strong (I.stage i) := by
      obtain ⟨p, hp, _hp_small, _hp_big, eSmall, eBig, hcomm⟩ := I.subpair i
      have hp_str : K.Strong (M := p.small.toModel) (N := p.big.toModel) p.incl :=
        ((aecCode_pair_mem lam p).mp hp).2.2
      have hmem_si : K.Mem (I.small.system.obj i) := codedPresentation_obj_mem I.small i
      have heSmall_str : K.Strong (M := I.small.system.obj i) (N := p.small.toModel) eSmall.toEmbedding :=
        @strong_of_equiv K (I.small.system.obj i) p.small.toModel eSmall hmem_si
      have hthrough : K.Strong (M := I.small.system.obj i) (N := p.big.toModel)
          (p.incl.comp eSmall.toEmbedding) :=
        @K.strong_trans (I.small.system.obj i) p.small.toModel p.big.toModel
          eSmall.toEmbedding p.incl heSmall_str hp_str
      rw [hcomm] at hthrough
      have hmem_bi : K.Mem (I.big.system.obj (I.embedIndex i)) :=
        codedPresentation_obj_mem I.big (I.embedIndex i)
      have heBig_str : K.Strong (M := I.big.system.obj (I.embedIndex i)) (N := p.big.toModel) eBig.toEmbedding :=
        @strong_of_equiv K (I.big.system.obj (I.embedIndex i)) p.big.toModel eBig hmem_bi
      exact @K.coherence (I.small.system.obj i) (I.big.system.obj (I.embedIndex i)) p.big.toModel
        (I.stage i) (eBig.toEmbedding.comp (I.stage i)) eBig.toEmbedding
        hthrough heBig_str rfl
    exact @K.strong_trans (I.small.system.obj i) (I.big.system.obj (I.embedIndex i)) I.bigLimit.obj
      (I.stage i) (I.bigLimit.canon (I.embedIndex i)) hstage_strong (hcan_b_strong (I.embedIndex i))
  have hmem_bigLim : K.Mem I.bigLimit.obj :=
    codedPresentation_limit_mem I.big I.bigLimit
  obtain ⟨ind_L, hind_L_str, hind_L_comm⟩ := hL_s.2.2 I.bigLimit.obj
    (fun i => (I.bigLimit.canon (I.embedIndex i)).comp (I.stage i))
    hmem_bigLim hg_strong (fun {i j} hij => by
      have hcomm_stage := I.stage_comm hij
      have hcomm_big := I.bigLimit.compat (I.embedIndex_rel hij)
      calc
        ((I.bigLimit.canon (I.embedIndex j)).comp (I.stage j)).comp (I.small.system.map hij)
            = (I.bigLimit.canon (I.embedIndex j)).comp ((I.stage j).comp (I.small.system.map hij)) := by
              simp only [Language.Embedding.comp_assoc]
          _ = (I.bigLimit.canon (I.embedIndex j)).comp ((I.big.system.map (I.embedIndex_rel hij)).comp (I.stage i)) := by
              rw [hcomm_stage]
          _ = ((I.bigLimit.canon (I.embedIndex j)).comp (I.big.system.map (I.embedIndex_rel hij))).comp (I.stage i) := by
              simp only [Language.Embedding.comp_assoc]
          _ = (I.bigLimit.canon (I.embedIndex i)).comp (I.stage i) := by
              rw [hcomm_big])
  have hind_eq : I.induced = ind_L.comp e_s.toEmbedding := by
    apply factorEmbedding_unique (L := K.τ)
      (f := ind_L.comp e_s.toEmbedding) (g := Language.Embedding.refl _ _)
      (h₁ := I.induced) (h₂ := ind_L.comp e_s.toEmbedding)
    · rw [Language.Embedding.refl_comp]
      ext z
      obtain ⟨i, y, rfl⟩ := I.smallLimit.joint z
      have h1 := congrFun (congrArg (⇑) (I.induced_comm i)) y
      simp only [Language.Embedding.comp_apply] at h1 ⊢
      rw [h1]
      have h2 := congrFun (congrArg (⇑) (hind_L_comm i)) y
      have he_s_app : e_s ((I.smallLimit.canon i) y) = L_s.canon i y := by
        have h_symm : e_s_alg ((I.smallLimit.canon i) y) =
            (algebraicLimit I.small.system).canon i y := by
          apply (directLimitEquivAlgebraic I.small.system I.smallLimit).injective
          simp only [e_s_alg, Language.Equiv.apply_symm_apply]
          exact (directLimitEquivAlgebraic_canon I.small.system I.smallLimit i y).symm
        change (e_Ls_alg.comp e_s_alg) ((I.smallLimit.canon i) y) = L_s.canon i y
        rw [Language.Equiv.comp_apply, h_symm]
        exact directLimitEquivAlgebraic_canon I.small.system L_s i y
      simp only [Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding]
      rw [he_s_app]
      exact h2.symm
    · rw [Language.Embedding.refl_comp]
  rw [hind_eq]
  have he_s_str : K.Strong e_s.toEmbedding :=
    strong_of_equiv K e_s hmemSmall
  exact @K.strong_trans I.smallLimit.obj L_s.obj I.bigLimit.obj
    e_s.toEmbedding ind_L he_s_str hind_L_str

theorem strong_of_decodedStrong {lam : Cardinal.{u}} {M N : Model K.τ}
    (f : Language.Embedding K.τ M.carrier N.carrier)
    (h : DecodedStrong (aecCode K lam) f) : K.Strong f := by
  obtain ⟨I, eM, eN, hcomm⟩ := h
  have hind : K.Strong I.induced := codedInclusion_induced_strong I
  have hmemM : K.Mem I.smallLimit.obj := codedPresentation_limit_mem I.small I.smallLimit
  have hmemN : K.Mem I.bigLimit.obj := codedPresentation_limit_mem I.big I.bigLimit
  have heM_str : K.Strong eM.toEmbedding := strong_of_equiv K eM hmemM
  have heN_str : K.Strong eN.toEmbedding := strong_of_equiv K eN hmemN
  have hthrough : K.Strong (eN.toEmbedding.comp I.induced) :=
    K.strong_trans I.induced eN.toEmbedding hind heN_str
  rw [hcomm] at hthrough
  have hmem_real_M : K.Mem M := K.iso_closed ⟨eM⟩ hmemM
  have heM_symm_str : K.Strong eM.symm.toEmbedding :=
    strong_of_equiv K eM.symm hmem_real_M
  have hf_eq : f = (f.comp eM.toEmbedding).comp eM.symm.toEmbedding := by
    ext x
    simp [Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding]
  rw [hf_eq]
  exact K.strong_trans eM.symm.toEmbedding (f.comp eM.toEmbedding) heM_symm_str hthrough

theorem strong_iff_decodedStrong {lam : Cardinal.{u}} (hLS : isLSBound K lam)
    {M N : Model K.τ} (f : Language.Embedding K.τ M.carrier N.carrier) :
    K.Strong f ↔ DecodedStrong (aecCode K lam) f :=
  ⟨decodedStrong_of_strong hLS f, strong_of_decodedStrong f⟩

theorem aecCode_isValidCode {lam : Cardinal.{u}} (hLS : isLSBound K lam) :
    IsValidCode lam (aecCode K lam) := by
  refine ⟨K, rfl, hLS, ?_, ?_⟩
  · intro M; exact mem_iff_decodedMem hLS M
  · intro M N f; exact strong_iff_decodedStrong hLS f

/-- Categoricity for AECs that share a language and agree on `Mem`. -/
theorem categorical_of_mem_eq {K₁ K₂ : AbstractElementaryClass.{u}}
    (hτ : K₁.τ = K₂.τ)
    (hmem : ∀ M : Model K₁.τ, K₁.Mem M ↔ K₂.Mem (hτ ▸ M))
    (κ : Cardinal.{u}) :
    Categorical K₁ κ ↔ Categorical K₂ κ := by
  -- Destructure so `cases` on the language equality succeeds.
  rcases K₁ with ⟨τ₁, Mem₁, Strong₁, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, ls1, ls2, ls3, ls4⟩
  rcases K₂ with ⟨τ₂, Mem₂, Strong₂, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, mt1, mt2, mt3, mt4⟩
  cases hτ
  have hmem' : ∀ M, Mem₁ M ↔ Mem₂ M := hmem
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨M, hM, hc⟩ := h.exists_model
      exact ⟨M, (hmem' M).mp hM, hc⟩
    · intro M N hM hN hκM hκN
      exact h.unique_model M N ((hmem' M).mpr hM) ((hmem' N).mpr hN) hκM hκN
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨M, hM, hc⟩ := h.exists_model
      exact ⟨M, (hmem' M).mpr hM, hc⟩
    · intro M N hM hN hκM hκN
      exact h.unique_model M N ((hmem' M).mp hM) ((hmem' N).mp hN) hκM hκN

theorem SpectrumBounded.mem_eq {K₁ K₂ : AbstractElementaryClass.{u}}
    (hτ : K₁.τ = K₂.τ)
    (hmem : ∀ M : Model K₁.τ, K₁.Mem M ↔ K₂.Mem (hτ ▸ M)) :
    SpectrumBounded K₁ ↔ SpectrumBounded K₂ := by
  have hcat := categorical_of_mem_eq hτ hmem
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.bound
    exact ⟨b, fun μ hμ => hb μ ((hcat μ).mpr hμ)⟩
  · intro h
    obtain ⟨b, hb⟩ := h.bound
    exact ⟨b, fun μ hμ => hb μ ((hcat μ).mp hμ)⟩

theorem spectrumBound_eq_of_mem_eq {K₁ K₂ : AbstractElementaryClass.{u}}
    (hτ : K₁.τ = K₂.τ)
    (hmem : ∀ M : Model K₁.τ, K₁.Mem M ↔ K₂.Mem (hτ ▸ M)) :
    spectrumBound K₁ = spectrumBound K₂ := by
  have hcat := categorical_of_mem_eq hτ hmem
  have hsb := SpectrumBounded.mem_eq hτ hmem
  have hspec : categoricitySpectrum K₁ = categoricitySpectrum K₂ := by
    ext μ; simp only [categoricitySpectrum, Set.mem_ofPred_eq]; exact hcat μ
  apply congrArg sInf
  ext κ
  simp only [spectrumBoundSet, Set.mem_ofPred_eq, hsb, hspec]
  refine and_congr_right' (or_congr ?_ ?_)
  · refine and_congr_right' ?_
    constructor <;> intro h μ hμ <;> exact h μ (by simpa [hspec] using hμ)
  · refine and_congr_right' ?_
    constructor <;> intro h μ hμ <;> simpa [hcat] using h μ hμ

/-- Decoding `aecCode K` recovers an AEC with the same spectrum bound as `K`. -/
theorem spectrumBound_choose_aecCode {lam : Cardinal.{u}} (hLS : isLSBound K lam) :
    spectrumBound (Classical.choose (aecCode_isValidCode (K := K) hLS).decodes) =
      spectrumBound K := by
  let K' := Classical.choose (aecCode_isValidCode (K := K) hLS).decodes
  have hspec := Classical.choose_spec (aecCode_isValidCode (K := K) hLS).decodes
  obtain ⟨hτ, _, hmem, _⟩ := hspec
  -- `hτ : K.τ = K'.τ` and `K'.Mem ↔ DecodedMem (hτ ▸ aecCode)`.
  exact (spectrumBound_eq_of_mem_eq (K₁ := K) (K₂ := K') hτ (fun M => by
    have hiff := mem_iff_decodedMem (K := K) hLS M
    have hK' := hmem (hτ ▸ M)
    have hcast : DecodedMem (aecCode K lam) M ↔
        DecodedMem (hτ ▸ aecCode K lam) (hτ ▸ M) :=
      Eq.rec (motive := fun (τ' : Tau.{u}) (h : K.τ = τ') =>
        DecodedMem (aecCode K lam) M ↔ DecodedMem (h ▸ aecCode K lam) (h ▸ M))
        Iff.rfl hτ
    change K.Mem M ↔ K'.Mem (hτ ▸ M)
    rw [hiff, hcast, hK'])).symm

/-- Language card bound from an LS bound. -/
theorem card_le_of_isLSBound {lam : Cardinal.{u}} (hLS : isLSBound K lam) :
    K.τ.card ≤ lam :=
  (le_self_add).trans hLS.2.1

/-- The ordinal code of an AEC at bound `lam`, after renaming into ordinal symbols. -/
noncomputable def aecOrdCode (K : AbstractElementaryClass.{u}) (lam : Cardinal.{u})
    (hLS : isLSBound K lam) : OrdCode lam :=
  let hcard := card_le_of_isLSBound (K := K) hLS
  let e := ordLangEquiv K.τ lam hcard
  ⟨ordLangOf K.τ lam hcard, aecCode (reindexAEC K e) lam⟩

theorem aecOrdCode_isValidCode {lam : Cardinal.{u}} (hLS : isLSBound K lam) :
    IsValidCode lam (aecOrdCode K lam hLS).2 := by
  let hcard := card_le_of_isLSBound (K := K) hLS
  let e := ordLangEquiv K.τ lam hcard
  exact aecCode_isValidCode (reindexAEC_isLSBound K e hLS)

/-- Replacement: every AEC with LS bound `lam` has `spectrumBound ≤ canBound lam`. -/
theorem spectrumBound_le_canBound_of_isLSBound {lam : Cardinal.{u}}
    (hLS : isLSBound K lam) :
    spectrumBound K ≤ canBound lam := by
  let hcard := card_le_of_isLSBound (K := K) hLS
  let e := ordLangEquiv K.τ lam hcard
  let K' := reindexAEC K e
  have hLS' : isLSBound K' lam := reindexAEC_isLSBound K e hLS
  have : IsValidCode lam (aecOrdCode K lam hLS).2 := aecOrdCode_isValidCode hLS
  have hle : spectrumBound (Classical.choose
      (aecOrdCode_isValidCode (K := K) hLS).decodes) ≤ canBound lam :=
    spectrumBound_le_canBound (aecOrdCode K lam hLS)
  have heq₁ : spectrumBound (Classical.choose
      (aecOrdCode_isValidCode (K := K) hLS).decodes) = spectrumBound K' := by
    simpa [aecOrdCode] using spectrumBound_choose_aecCode (K := K') hLS'
  have heq₂ : spectrumBound K' = spectrumBound K := reindexAEC_spectrumBound_eq K e
  rw [← heq₂, ← heq₁]
  exact hle
