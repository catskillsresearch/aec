module

public import AEC.Section2.SmallCode
public import AEC.Section2.SpectrumBound
public import AEC.Section1.Language
public import AEC.Section1.ChainUnion
public import AEC.Section1.Categorical
public import AEC.Section1.LoewenheimSkolem
public import Mathlib.ModelTheory.LanguageMap
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Logic.Equiv.Set

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- A language whose function and relation symbols are ordinals below `lam`. -/
structure OrdLang (lam : Cardinal.{u}) : Type u where
  Functions : ℕ → Set (Below lam)
  Relations : ℕ → Set (Below lam)

def OrdLang.toTau {lam : Cardinal.{u}} (L : OrdLang lam) : Tau.{u} where
  Functions n := ↥(L.Functions n)
  Relations n := ↥(L.Relations n)

def OrdCode (lam : Cardinal.{u}) : Type u :=
  Σ L : OrdLang lam, SmallCode L.toTau lam

theorem card_functions_le_card (τ : Tau.{u}) (n : ℕ) :
    #(τ.Functions n) ≤ τ.card := by
  let i : τ.Functions n ↪ τ.Symbols :=
    ⟨fun f => Sum.inl ⟨n, f⟩, fun _ _ h => by
      simpa [Language.Symbols] using Sum.inl_injective h⟩
  simpa [Language.card] using mk_le_of_injective i.injective

theorem card_relations_le_card (τ : Tau.{u}) (n : ℕ) :
    #(τ.Relations n) ≤ τ.card := by
  let i : τ.Relations n ↪ τ.Symbols :=
    ⟨fun r => Sum.inr ⟨n, r⟩, fun _ _ h => by
      simpa [Language.Symbols] using Sum.inr_injective h⟩
  simpa [Language.card] using mk_le_of_injective i.injective

noncomputable def embedFunctions (τ : Tau.{u}) (lam : Cardinal.{u})
    (h : τ.card ≤ lam) (n : ℕ) : τ.Functions n ↪ Below lam := by
  have hle : #(τ.Functions n) ≤ #(Below lam) := by
    rw [mk_ord_toType lam]
    exact (card_functions_le_card τ n).trans h
  exact Classical.choice ((Cardinal.le_def _ _).mp hle)

noncomputable def embedRelations (τ : Tau.{u}) (lam : Cardinal.{u})
    (h : τ.card ≤ lam) (n : ℕ) : τ.Relations n ↪ Below lam := by
  have hle : #(τ.Relations n) ≤ #(Below lam) := by
    rw [mk_ord_toType lam]
    exact (card_relations_le_card τ n).trans h
  exact Classical.choice ((Cardinal.le_def _ _).mp hle)

noncomputable def ordLangOf (τ : Tau.{u}) (lam : Cardinal.{u}) (h : τ.card ≤ lam) :
    OrdLang lam where
  Functions n := Set.range (embedFunctions τ lam h n)
  Relations n := Set.range (embedRelations τ lam h n)

noncomputable def funRangeEquiv (τ : Tau.{u}) (lam : Cardinal.{u})
    (h : τ.card ≤ lam) (n : ℕ) :
    τ.Functions n ≃ ↥(Set.range (embedFunctions τ lam h n)) :=
  Equiv.ofInjective _ (embedFunctions τ lam h n).injective

noncomputable def relRangeEquiv (τ : Tau.{u}) (lam : Cardinal.{u})
    (h : τ.card ≤ lam) (n : ℕ) :
    τ.Relations n ≃ ↥(Set.range (embedRelations τ lam h n)) :=
  Equiv.ofInjective _ (embedRelations τ lam h n).injective

noncomputable def ordLangEquiv (τ : Tau.{u}) (lam : Cardinal.{u}) (h : τ.card ≤ lam) :
    τ ≃ᴸ (ordLangOf τ lam h).toTau where
  toLHom := {
    onFunction := fun {n} f => funRangeEquiv τ lam h n f
    onRelation := fun {n} r => relRangeEquiv τ lam h n r
  }
  invLHom := {
    onFunction := fun {n} f => (funRangeEquiv τ lam h n).symm f
    onRelation := fun {n} r => (relRangeEquiv τ lam h n).symm r
  }
  left_inv := by
    apply Language.LHom.funext
    · ext n f; exact (funRangeEquiv τ lam h n).symm_apply_apply f
    · ext n r; exact (relRangeEquiv τ lam h n).symm_apply_apply r
  right_inv := by
    apply Language.LHom.funext
    · ext n f; exact (funRangeEquiv τ lam h n).apply_symm_apply f
    · ext n r; exact (relRangeEquiv τ lam h n).apply_symm_apply r

theorem LEquiv.onFunction_bijective {L L' : Tau.{u}} (e : L ≃ᴸ L') (n : ℕ) :
    Function.Bijective (e.toLHom.onFunction (n := n)) := by
  refine ⟨fun f₁ f₂ hf => ?_, fun f' => ⟨e.invLHom.onFunction f', ?_⟩⟩
  · have := congrArg (e.invLHom.onFunction (n := n)) hf
    have h1 : e.invLHom.onFunction (e.toLHom.onFunction f₁) = f₁ :=
      congrFun (congrFun (congrArg Language.LHom.onFunction e.left_inv) n) f₁
    have h2 : e.invLHom.onFunction (e.toLHom.onFunction f₂) = f₂ :=
      congrFun (congrFun (congrArg Language.LHom.onFunction e.left_inv) n) f₂
    exact h1.symm.trans (this.trans h2)
  · exact congrFun (congrFun (congrArg Language.LHom.onFunction e.right_inv) n) f'

theorem LEquiv.onRelation_bijective {L L' : Tau.{u}} (e : L ≃ᴸ L') (n : ℕ) :
    Function.Bijective (e.toLHom.onRelation (n := n)) := by
  refine ⟨fun r₁ r₂ hr => ?_, fun r' => ⟨e.invLHom.onRelation r', ?_⟩⟩
  · have := congrArg (e.invLHom.onRelation (n := n)) hr
    have h1 : e.invLHom.onRelation (e.toLHom.onRelation r₁) = r₁ :=
      congrFun (congrFun (congrArg Language.LHom.onRelation e.left_inv) n) r₁
    have h2 : e.invLHom.onRelation (e.toLHom.onRelation r₂) = r₂ :=
      congrFun (congrFun (congrArg Language.LHom.onRelation e.left_inv) n) r₂
    exact h1.symm.trans (this.trans h2)
  · exact congrFun (congrFun (congrArg Language.LHom.onRelation e.right_inv) n) r'

theorem LEquiv.card_eq {L L' : Tau.{u}} (e : L ≃ᴸ L') : L.card = L'.card := by
  let φ : L.Symbols ≃ L'.Symbols :=
    Equiv.sumCongr
      (Equiv.sigmaCongrRight fun n => Equiv.ofBijective _ (LEquiv.onFunction_bijective e n))
      (Equiv.sigmaCongrRight fun n => Equiv.ofBijective _ (LEquiv.onRelation_bijective e n))
  simpa [Language.card] using Cardinal.mk_congr φ

/-- Pull a model of `L'` back to a model of `L` along a language map. -/
abbrev Model.pull {L L' : Tau.{u}} (ϕ : L →ᴸ L') (M : Model L') : Model L where
  carrier := M.carrier
  str := ϕ.reduct M.carrier

/-- Push an `L`-structure forward along a language equivalence. -/
@[instance_reducible]
def pushStructure {L L' : Tau.{u}} (e : L ≃ᴸ L') {α : Type u} (s : L.Structure α) :
    L'.Structure α where
  funMap := fun {_n} f xs => s.funMap (e.invLHom.onFunction f) xs
  RelMap := fun {_n} r xs => s.RelMap (e.invLHom.onRelation r) xs

/-- Push a model of `L` forward along a language equivalence. -/
abbrev Model.push {L L' : Tau.{u}} (e : L ≃ᴸ L') (M : Model L) : Model L' where
  carrier := M.carrier
  str := pushStructure e M.str

theorem pull_push {L L' : Tau.{u}} (e : L ≃ᴸ L') (M : Model L) :
    (M.push e).pull e.toLHom = M := by
  cases M with | mk carrier str =>
  refine congrArg (Model.mk carrier) ?_
  ext n f xs
  · change str.funMap (e.invLHom.onFunction (e.toLHom.onFunction f)) xs = str.funMap f xs
    have hto : e.invLHom.onFunction (e.toLHom.onFunction f) = f :=
      congrFun (congrFun (congrArg Language.LHom.onFunction e.left_inv) n) f
    simp [hto]
  · change str.RelMap (e.invLHom.onRelation (e.toLHom.onRelation f)) xs ↔ str.RelMap f xs
    have hto : e.invLHom.onRelation (e.toLHom.onRelation f) = f :=
      congrFun (congrFun (congrArg Language.LHom.onRelation e.left_inv) n) f
    simp [hto]

/-- Cast an embedding along equal structure instances. -/
def castEmbedding {L : Tau.{u}} {α β : Type u}
    {sα sα' : L.Structure α} {sβ sβ' : L.Structure β}
    (hα : sα = sα') (hβ : sβ = sβ')
    (f : @Language.Embedding L α β sα sβ) :
    @Language.Embedding L α β sα' sβ' := by
  subst hα; subst hβ; exact f

theorem castEmbedding_apply {L : Tau.{u}} {α β : Type u}
    {sα sα' : L.Structure α} {sβ sβ' : L.Structure β}
    (hα : sα = sα') (hβ : sβ = sβ')
    (f : @Language.Embedding L α β sα sβ) (x : α) :
    castEmbedding hα hβ f x = f x := by
  subst hα; subst hβ; rfl

/-- Cast an equivalence along equal structure instances. -/
def castEquiv {L : Tau.{u}} {α β : Type u}
    {sα sα' : L.Structure α} {sβ sβ' : L.Structure β}
    (hα : sα = sα') (hβ : sβ = sβ')
    (f : @Language.Equiv L α β sα sβ) :
    @Language.Equiv L α β sα' sβ' := by
  subst hα; subst hβ; exact f

/-- Strongness is preserved when the domain model is replaced by an equal model. -/
theorem strong_model_eq_dom (K : AbstractElementaryClass.{u})
    {M M' N : Model K.τ} (h : M = M')
    (f : Language.Embedding K.τ M.carrier N.carrier)
    (hf : K.Strong (M := M) f) :
    K.Strong (M := M') (h ▸ f) := by
  subst h; exact hf

/-- Strongness is preserved when the codomain model is replaced by an equal model. -/
theorem strong_model_eq_cod (K : AbstractElementaryClass.{u})
    {M N N' : Model K.τ} (h : N = N')
    (f : Language.Embedding K.τ M.carrier N.carrier)
    (hf : K.Strong (N := N) f) :
    K.Strong (N := N') (h ▸ f) := by
  subst h; exact hf

/-- Applying an embedding cast along a domain-model equality. -/
theorem coe_model_eqRec_embedding_dom {L : Tau.{u}} {M M' N : Model L}
    (h : M = M') (f : Language.Embedding L M.carrier N.carrier)
    (x : M'.carrier) :
    (h ▸ f : Language.Embedding L M'.carrier N.carrier) x =
      f (cast (congrArg Model.carrier h.symm) x) := by
  subst h; rfl

/-- Applying an embedding cast along a codomain-model equality. -/
theorem coe_model_eqRec_embedding_cod {L : Tau.{u}} {M N N' : Model L}
    (h : N = N') (f : Language.Embedding L M.carrier N.carrier)
    (x : M.carrier) :
    (h ▸ f : Language.Embedding L M.carrier N'.carrier) x =
      cast (congrArg Model.carrier h) (f x) := by
  subst h; rfl

/-- An `L'`-embedding is an `L`-embedding of the reducts. -/
def embedding_reduct {L L' : Tau.{u}} (ϕ : L →ᴸ L') {M N : Type u}
    [sM : L'.Structure M] [sN : L'.Structure N]
    (f : Language.Embedding L' M N) :=
  let sM' : L.Structure M := ϕ.reduct M
  let sN' : L.Structure N := ϕ.reduct N
  ({ toFun := f.toFun
     inj' := f.injective
     map_fun' := fun {_n} g xs => f.map_fun' (ϕ.onFunction g) xs
     map_rel' := fun {_n} r xs => f.map_rel' (ϕ.onRelation r) xs } :
    @Language.Embedding L M N sM' sN')

/-- Pull an `L'`-embedding to an embedding of pulled models. -/
def pullEmbedding {L L' : Tau.{u}} (ϕ : L →ᴸ L') {M N : Model L'}
    (f : Language.Embedding L' M.carrier N.carrier) :
    Language.Embedding L (Model.pull ϕ M).carrier (Model.pull ϕ N).carrier :=
  embedding_reduct (sM := M.str) (sN := N.str) ϕ f

theorem pullEmbedding_apply {L L' : Tau.{u}} (ϕ : L →ᴸ L') {M N : Model L'}
    (f : Language.Embedding L' M.carrier N.carrier) (x : M.carrier) :
    pullEmbedding ϕ f x = f x := rfl

theorem pullEmbedding_refl {L L' : Tau.{u}} (ϕ : L →ᴸ L') (M : Model L') :
    pullEmbedding ϕ (Language.Embedding.refl L' M.carrier) =
      Language.Embedding.refl L (Model.pull ϕ M).carrier := rfl

theorem pullEmbedding_comp {L L' : Tau.{u}} (ϕ : L →ᴸ L') {M N P : Model L'}
    (f : Language.Embedding L' M.carrier N.carrier)
    (g : Language.Embedding L' N.carrier P.carrier) :
    pullEmbedding ϕ (g.comp f) =
      (pullEmbedding ϕ g).comp (pullEmbedding ϕ f) := rfl

/-- An `L'`-equivalence induces an `L`-equivalence of reducts. -/
def equiv_reduct {L L' : Tau.{u}} (ϕ : L →ᴸ L') {M N : Type u}
    [sM : L'.Structure M] [sN : L'.Structure N]
    (f : Language.Equiv L' M N) :=
  let sM' : L.Structure M := ϕ.reduct M
  let sN' : L.Structure N := ϕ.reduct N
  ({ toEquiv := f.toEquiv
     map_fun' := fun {_n} g xs => f.map_fun' (ϕ.onFunction g) xs
     map_rel' := fun {_n} r xs => f.map_rel' (ϕ.onRelation r) xs } :
    @Language.Equiv L M N sM' sN')

/-- Pull an `L'`-equivalence to an equivalence of pulled models. -/
def pullEquiv {L L' : Tau.{u}} (ϕ : L →ᴸ L') {M N : Model L'}
    (f : Language.Equiv L' M.carrier N.carrier) :
    Language.Equiv L (Model.pull ϕ M).carrier (Model.pull ϕ N).carrier :=
  equiv_reduct (sM := M.str) (sN := N.str) ϕ f

theorem pullEquiv_toEmbedding {L L' : Tau.{u}} (ϕ : L →ᴸ L') {M N : Model L'}
    (f : Language.Equiv L' M.carrier N.carrier) :
    (pullEquiv ϕ f).toEmbedding = pullEmbedding ϕ f.toEmbedding := rfl

/-- Rebuild an `L'`-equivalence from a reduct equivalence. -/
def equiv_of_reduct {L L' : Tau.{u}} (e : L ≃ᴸ L') {M N : Type u}
    [sM : L'.Structure M] [sN : L'.Structure N]
    (f : @Language.Equiv L M N (e.toLHom.reduct M) (e.toLHom.reduct N)) :
    Language.Equiv L' M N where
  toEquiv := @Language.Equiv.toEquiv L M N (e.toLHom.reduct M) (e.toLHom.reduct N) f
  map_fun' := fun {n} g xs => by
    have hto : e.toLHom.onFunction (e.invLHom.onFunction g) = g :=
      congrFun (congrFun (congrArg Language.LHom.onFunction e.right_inv) n) g
    have h :=
      @Language.Equiv.map_fun' L M N (e.toLHom.reduct M) (e.toLHom.reduct N) f n
        (e.invLHom.onFunction g) xs
    rw [← hto]
    exact h
  map_rel' := fun {n} r xs => by
    have hto : e.toLHom.onRelation (e.invLHom.onRelation r) = r :=
      congrFun (congrFun (congrArg Language.LHom.onRelation e.right_inv) n) r
    have h :=
      @Language.Equiv.map_rel' L M N (e.toLHom.reduct M) (e.toLHom.reduct N) f n
        (e.invLHom.onRelation r) xs
    rw [← hto]
    exact h

/-- View a reduct-embedding as an `L'`-embedding. -/
def embedding_as_push {L L' : Tau.{u}} (e : L ≃ᴸ L') {M N : Type u}
    [sM : L'.Structure M] [sN : L'.Structure N]
    (f : @Language.Embedding L M N (e.toLHom.reduct M) (e.toLHom.reduct N)) :
    Language.Embedding L' M N where
  toFun :=
    @DFunLike.coe (@Language.Embedding L M N (e.toLHom.reduct M) (e.toLHom.reduct N))
      M (fun _ => N) _ f
  inj' :=
    (@Language.Embedding.injective L M N (e.toLHom.reduct M) (e.toLHom.reduct N) f)
  map_fun' := fun {n} g xs => by
    have hto : e.toLHom.onFunction (e.invLHom.onFunction g) = g :=
      congrFun (congrFun (congrArg Language.LHom.onFunction e.right_inv) n) g
    have h :=
      @Language.Embedding.map_fun' L M N (e.toLHom.reduct M) (e.toLHom.reduct N) f n
        (e.invLHom.onFunction g) xs
    rw [← hto]
    exact h
  map_rel' := fun {n} r xs => by
    have hto : e.toLHom.onRelation (e.invLHom.onRelation r) = r :=
      congrFun (congrFun (congrArg Language.LHom.onRelation e.right_inv) n) r
    have h :=
      @Language.Embedding.map_rel' L M N (e.toLHom.reduct M) (e.toLHom.reduct N) f n
        (e.invLHom.onRelation r) xs
    rw [← hto]
    exact h

/-- Push an embedding of pulled models forward along a language equivalence. -/
def pushEmbedding {L L' : Tau.{u}} (e : L ≃ᴸ L') {M N : Model L'}
    (f : Language.Embedding L (Model.pull e.toLHom M).carrier
      (Model.pull e.toLHom N).carrier) :
    Language.Embedding L' M.carrier N.carrier :=
  embedding_as_push (sM := M.str) (sN := N.str) e f

theorem pushEmbedding_apply {L L' : Tau.{u}} (e : L ≃ᴸ L') {M N : Model L'}
    (f : Language.Embedding L (Model.pull e.toLHom M).carrier
      (Model.pull e.toLHom N).carrier) (x : M.carrier) :
    pushEmbedding e f x = f x := rfl

/-- Rebuild an `L'`-equivalence from an equivalence of pulled models. -/
def pushEquiv {L L' : Tau.{u}} (e : L ≃ᴸ L') {M N : Model L'}
    (f : Language.Equiv L (Model.pull e.toLHom M).carrier
      (Model.pull e.toLHom N).carrier) :
    Language.Equiv L' M.carrier N.carrier :=
  equiv_of_reduct (sM := M.str) (sN := N.str) e f
/-- Reindex an ordinal chain by taking reducts of stages and transitions. -/
def OrdinalChain.pull {L L' : Tau.{u}} (ϕ : L →ᴸ L') (C : OrdinalChain L') :
    OrdinalChain L where
  δ := C.δ
  nonzero := C.nonzero
  obj := fun i hi => Model.pull ϕ (C.obj i hi)
  map := fun i j hi hj hij => pullEmbedding ϕ (C.map i j hi hj hij)

theorem OrdinalChain.pull_map_comp {L L' : Tau.{u}} (ϕ : L →ᴸ L')
    (C : OrdinalChain L') (h : OrdinalChain.map_comp_prop L' C) :
    OrdinalChain.map_comp_prop L (OrdinalChain.pull ϕ C) := by
  intro i j k hi hj hk hij hjk
  ext x
  exact congr_fun (congrArg DFunLike.coe (h i j k hi hj hk hij hjk)) x

/-- Push a model of the original language along `e`, recovering it by `pull_push`. -/
def pushFromPull {L L' : Tau.{u}} (e : L ≃ᴸ L') (M0 : Model L) : Model L' :=
  M0.push e

theorem pull_pushFromPull {L L' : Tau.{u}} (e : L ≃ᴸ L') (M0 : Model L) :
    Model.pull e.toLHom (pushFromPull e M0) = M0 :=
  pull_push e M0

/-- Cast an embedding out of a pushed model into a pulled-model embedding. -/
def embedding_from_push {L L' : Tau.{u}} (e : L ≃ᴸ L')
    {M0 : Model L} {N : Model L'}
    (f : Language.Embedding L M0.carrier (Model.pull e.toLHom N).carrier) :
    Language.Embedding L (Model.pull e.toLHom (pushFromPull e M0)).carrier
      (Model.pull e.toLHom N).carrier :=
  (pull_pushFromPull e M0).symm ▸ f

theorem pushEmbedding_pullEmbedding {L L' : Tau.{u}} (e : L ≃ᴸ L') {M N : Model L'}
    (f : Language.Embedding L' M.carrier N.carrier) :
    pushEmbedding e (pullEmbedding e.toLHom f) = f := by
  ext x; rfl

theorem pullEmbedding_pushEmbedding {L L' : Tau.{u}} (e : L ≃ᴸ L') {M N : Model L'}
    (f : Language.Embedding L (Model.pull e.toLHom M).carrier
      (Model.pull e.toLHom N).carrier) :
    pullEmbedding e.toLHom (pushEmbedding e f) = f := by
  ext x; rfl

/-- The AEC obtained by renaming the language of `K` along a language equivalence. -/
@[reducible] noncomputable def reindexAEC (K : AbstractElementaryClass.{u}) {L' : Tau.{u}}
    (e : K.τ ≃ᴸ L') : AbstractElementaryClass.{u} where
  τ := L'
  Mem M := K.Mem (Model.pull e.toLHom M)
  Strong := fun {M N} f => K.Strong (pullEmbedding e.toLHom f)
  strong_mem_dom := fun {M N} f hf =>
    K.strong_mem_dom (pullEmbedding e.toLHom f) hf
  strong_mem_cod := fun {M N} f hf =>
    K.strong_mem_cod (pullEmbedding e.toLHom f) hf
  strong_refl := fun M hM => by
    rw [pullEmbedding_refl]
    exact K.strong_refl (Model.pull e.toLHom M) hM
  strong_trans := fun {M N P} f g hf hg => by
    rw [pullEmbedding_comp]
    exact K.strong_trans (pullEmbedding e.toLHom f) (pullEmbedding e.toLHom g) hf hg
  strong_antisymm := fun {M N} f g hf hg hgf hfg => by
    obtain ⟨e0, he0⟩ :=
      K.strong_antisymm (pullEmbedding e.toLHom f) (pullEmbedding e.toLHom g)
        hf hg hgf hfg
    refine ⟨pushEquiv e e0, ?_⟩
    ext x
    have hfun : (pushEquiv e e0).toEmbedding x = e0.toEmbedding x := rfl
    rw [hfun, he0]; rfl
  iso_closed := fun {M N} ⟨eMN⟩ hM =>
    K.iso_closed ⟨pullEquiv e.toLHom eMN⟩ hM
  transport_strong := fun {M N N'} f eNN' hf => by
    have : pullEmbedding e.toLHom (eNN'.toEmbedding.comp f) =
        (pullEquiv e.toLHom eNN').toEmbedding.comp (pullEmbedding e.toLHom f) := by
      rw [pullEquiv_toEmbedding, pullEmbedding_comp]
    rw [this]
    exact K.transport_strong (pullEmbedding e.toLHom f) (pullEquiv e.toLHom eNN') hf
  coherence := fun {M₀ M₁ M₂} f₀₁ f₀₂ f₁₂ hf₀₂ hf₁₂ hcomm => by
    have hcomm' :
        (pullEmbedding e.toLHom f₁₂).comp (pullEmbedding e.toLHom f₀₁) =
          pullEmbedding e.toLHom f₀₂ := by
      rw [← pullEmbedding_comp, hcomm]
    exact K.coherence (pullEmbedding e.toLHom f₀₁) (pullEmbedding e.toLHom f₀₂)
      (pullEmbedding e.toLHom f₁₂) hf₀₂ hf₁₂ hcomm'
  chain_union := fun C hcomp hmem hstrong => by
    let C0 := OrdinalChain.pull e.toLHom C
    have hcomp0 := OrdinalChain.pull_map_comp e.toLHom C hcomp
    obtain ⟨U0, hU0, hU0incl⟩ := K.chain_union C0 hcomp0
      (fun i hi => hmem i hi) (fun i j hi hj hij => hstrong i j hi hj hij)
    let Uobj : Model L' := U0.obj.push e
    have hred : Model.pull e.toLHom Uobj = U0.obj := pull_push e U0.obj
    have hUmem : K.Mem (Model.pull e.toLHom Uobj) := by rw [hred]; exact hU0
    let Uincl : ∀ i hi, Language.Embedding L' (C.obj i hi).carrier Uobj.carrier :=
      fun i hi => pushEmbedding e (hred.symm ▸ U0.incl i hi)
    have Uincl_apply' (i) (hi : i < C.δ) (y : (C.obj i hi).carrier) :
        Uincl i hi y = U0.incl i hi y := by
      simp only [Uincl, pushEmbedding_apply]
      have H := coe_model_eqRec_embedding_cod hred.symm (U0.incl i hi) y
      simp only [cast_eq] at H
      exact H
    refine ⟨⟨Uobj, Uincl, ?_, ?_⟩, hUmem, ?_⟩
    · intro i j hi hj hij
      ext x
      rw [Language.Embedding.comp_apply,
        Uincl_apply' j hj (C.map i j hi hj hij x),
        Uincl_apply' i hi x]
      exact congr_fun (congrArg DFunLike.coe (U0.compat i j hi hj hij)) x
    · intro x
      obtain ⟨i, hi, y, hy⟩ := U0.covers x
      exact ⟨i, hi, y, (Uincl_apply' i hi y).trans hy⟩
    · intro i hi
      change K.Strong (pullEmbedding e.toLHom (Uincl i hi))
      dsimp only [Uincl]
      rw [pullEmbedding_pushEmbedding]
      exact strong_model_eq_cod K hred.symm (U0.incl i hi) (hU0incl i hi)
  chain_upper := fun C U N g hcomp hmem hstrong hUincl hN hg hcomm => by
    let C0 := OrdinalChain.pull e.toLHom C
    have hcomp0 := OrdinalChain.pull_map_comp e.toLHom C hcomp
    let U0 : ChainUnion C0 := {
      obj := Model.pull e.toLHom U.obj
      incl := fun i hi => pullEmbedding e.toLHom (U.incl i hi)
      compat := fun i j hi hj hij => by
        ext x
        exact congr_fun (congrArg DFunLike.coe (U.compat i j hi hj hij)) x
      covers := fun x => by
        obtain ⟨i, hi, y, hy⟩ := U.covers x
        exact ⟨i, hi, y, hy⟩
    }
    obtain ⟨f0, hf0, hf0comm⟩ :=
      K.chain_upper C0 U0 (Model.pull e.toLHom N)
        (fun i hi => pullEmbedding e.toLHom (g i hi))
        hcomp0 (fun i hi => hmem i hi) (fun i j hi hj hij => hstrong i j hi hj hij)
        (fun i hi => hUincl i hi) hN (fun i hi => hg i hi)
        (fun i j hi hj hij => by
          ext x
          exact congr_fun (congrArg DFunLike.coe (hcomm i j hi hj hij)) x)
    let f : Language.Embedding L' U.obj.carrier N.carrier := pushEmbedding e f0
    refine ⟨f, ?_, ?_⟩
    · change K.Strong (pullEmbedding e.toLHom f)
      rw [pullEmbedding_pushEmbedding e f0]
      exact hf0
    · intro i hi
      ext x
      exact congr_fun (congrArg DFunLike.coe (hf0comm i hi)) x
  lsBound := K.lsBound
  lsBound_infinite := K.lsBound_infinite
  lsBound_language := by
    change L'.card + aleph0 ≤ K.lsBound
    rw [← LEquiv.card_eq e]
    exact K.lsBound_language
  ls_axiom := fun M hM A => by
    obtain ⟨N0, f0, hN0, hf0, hA, hcard⟩ :=
      K.ls_axiom (Model.pull e.toLHom M) hM A
    let N : Model L' := N0.push e
    have hred : Model.pull e.toLHom N = N0 := pull_push e N0
    let f0' : Language.Embedding K.τ (Model.pull e.toLHom N).carrier
        (Model.pull e.toLHom M).carrier := hred.symm ▸ f0
    have hf0' : K.Strong (M := Model.pull e.toLHom N) f0' :=
      strong_model_eq_dom K hred.symm f0 hf0
    let f : Language.Embedding L' N.carrier M.carrier := pushEmbedding e f0'
    refine ⟨N, f, ?_, ?_, ?_, ?_⟩
    · change K.Mem _; rwa [hred]
    · change K.Strong (pullEmbedding e.toLHom f)
      rw [pullEmbedding_pushEmbedding e f0']
      exact hf0'
    · intro a ha
      obtain ⟨n, hn⟩ := hA a ha
      refine ⟨n, ?_⟩
      change f0' n = a
      have hcoe := coe_model_eqRec_embedding_dom hred.symm f0 n
      simpa [f0', cast_eq, hcoe] using hn
    · simpa [Model.card, Model.push] using hcard

theorem reindexAEC_categorical_iff (K : AbstractElementaryClass.{u}) {L' : Tau.{u}}
    (e : K.τ ≃ᴸ L') (κ : Cardinal.{u}) :
    Categorical (reindexAEC K e) κ ↔ Categorical K κ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨M, hM, hc⟩ := h.exists_model
      exact ⟨Model.pull e.toLHom M, hM, by simpa [Model.card, Model.pull] using hc⟩
    · intro M N hM hN hκM hκN
      let M' : Model L' := M.push e
      let N' : Model L' := N.push e
      have hredM : Model.pull e.toLHom M' = M := pull_push e M
      have hredN : Model.pull e.toLHom N' = N := pull_push e N
      have hM' : (reindexAEC K e).Mem M' := by
        change K.Mem (Model.pull e.toLHom M'); rw [hredM]; exact hM
      have hN' : (reindexAEC K e).Mem N' := by
        change K.Mem (Model.pull e.toLHom N'); rw [hredN]; exact hN
      obtain ⟨eMN⟩ := h.unique_model M' N' hM' hN'
        (by simpa [Model.card, Model.push] using hκM)
        (by simpa [Model.card, Model.push] using hκN)
      refine ⟨?_⟩
      let e0 := pullEquiv e.toLHom eMN
      have hstrM : (Model.pull e.toLHom M').str = M.str :=
        eq_of_heq (congr_arg_heq Model.str hredM)
      have hstrN : (Model.pull e.toLHom N').str = N.str :=
        eq_of_heq (congr_arg_heq Model.str hredN)
      exact castEquiv hstrM hstrN e0
  · intro h
    refine ⟨?_, ?_⟩
    · obtain ⟨M, hM, hc⟩ := h.exists_model
      refine ⟨(M.push e : Model L'), ?_, by simpa [Model.card, Model.push] using hc⟩
      change K.Mem (Model.pull e.toLHom (M.push e))
      rw [pull_push e M]; exact hM
    · intro M N hM hN hκM hκN
      obtain ⟨eMN⟩ := h.unique_model
        (Model.pull e.toLHom M) (Model.pull e.toLHom N) hM hN
        (by simpa [Model.card, Model.pull] using hκM)
        (by simpa [Model.card, Model.pull] using hκN)
      exact ⟨pushEquiv e eMN⟩

theorem SpectrumBounded.reindex_iff (K : AbstractElementaryClass.{u}) {L' : Tau.{u}}
    (e : K.τ ≃ᴸ L') :
    SpectrumBounded (reindexAEC K e) ↔ SpectrumBounded K := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := h.bound
    exact ⟨b, fun μ hμ => hb μ ((reindexAEC_categorical_iff K e μ).mpr hμ)⟩
  · intro h
    obtain ⟨b, hb⟩ := h.bound
    exact ⟨b, fun μ hμ => hb μ ((reindexAEC_categorical_iff K e μ).mp hμ)⟩

theorem reindexAEC_spectrumBound_eq (K : AbstractElementaryClass.{u}) {L' : Tau.{u}}
    (e : K.τ ≃ᴸ L') :
    spectrumBound (reindexAEC K e) = spectrumBound K := by
  have hcat : ∀ κ, Categorical (reindexAEC K e) κ ↔ Categorical K κ :=
    reindexAEC_categorical_iff K e
  have hsb := SpectrumBounded.reindex_iff K e
  have hspec : categoricitySpectrum (reindexAEC K e) = categoricitySpectrum K := by
    ext μ; simp only [categoricitySpectrum, Set.mem_ofPred_eq]; exact hcat μ
  apply congrArg sInf
  ext κ
  simp only [spectrumBoundSet, Set.mem_ofPred_eq, hsb, hspec]
  refine and_congr_right' (or_congr ?_ ?_)
  · refine and_congr_right' ?_
    constructor <;> intro h μ hμ <;> exact h μ (by simpa [hspec] using hμ)
  · refine and_congr_right' ?_
    constructor <;> intro h μ hμ <;> simpa [hcat] using h μ hμ

theorem reindexAEC_isLSBound (K : AbstractElementaryClass.{u}) {L' : Tau.{u}}
    (e : K.τ ≃ᴸ L') {lam : Cardinal.{u}} (hLS : isLSBound K lam) :
    isLSBound (reindexAEC K e) lam := by
  obtain ⟨hinf, hlang, hls⟩ := hLS
  refine ⟨hinf, ?_, ?_⟩
  · have : L'.card + aleph0 ≤ lam := by rw [← LEquiv.card_eq e]; exact hlang
    simpa [reindexAEC] using this
  · intro M hM A
    obtain ⟨N0, f0, hN0, hf0, hA, hcard⟩ := hls (Model.pull e.toLHom M) hM A
    let N : Model L' := N0.push e
    have hred : Model.pull e.toLHom N = N0 := pull_push e N0
    let f0' : Language.Embedding K.τ (Model.pull e.toLHom N).carrier
        (Model.pull e.toLHom M).carrier := hred.symm ▸ f0
    have hf0' : K.Strong (M := Model.pull e.toLHom N) f0' :=
      strong_model_eq_dom K hred.symm f0 hf0
    let f : Language.Embedding L' N.carrier M.carrier := pushEmbedding e f0'
    refine ⟨N, f, ?_, ?_, ?_, ?_⟩
    · change K.Mem _; rwa [hred]
    · change K.Strong (pullEmbedding e.toLHom f)
      rw [pullEmbedding_pushEmbedding e f0']
      exact hf0'
    · intro a ha
      obtain ⟨n, hn⟩ := hA a ha
      refine ⟨n, ?_⟩
      change f0' n = a
      have hcoe := coe_model_eqRec_embedding_dom hred.symm f0 n
      simpa [f0', cast_eq, hcoe] using hn
    · simpa [Model.card, Model.push] using hcard

end
end AEC
