module

public import AEC.Section1.AbstractElementaryClass
public import AEC.Section2.DirectLimit
public import Mathlib.ModelTheory.DirectLimit
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal
public import Mathlib.SetTheory.Cardinal.Order

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

attribute [local instance] Classical.propDecidable

/-- The index of a directed system, ordered by the system's relation. -/
abbrev Index {τ : Tau.{u}} (S : DirectedSystem τ) := S.ι

instance indexPreorder {τ : Tau.{u}} (S : DirectedSystem τ) : Preorder (Index S) where
  le := S.rel
  le_refl := S.refl
  le_trans _ _ _ := S.trans

instance indexDirected {τ : Tau.{u}} (S : DirectedSystem τ) : IsDirectedOrder (Index S) where
  directed := S.directed

instance indexNonempty {τ : Tau.{u}} (S : DirectedSystem τ) : Nonempty (Index S) :=
  S.nonempty

instance indexSystem {τ : Tau.{u}} (S : DirectedSystem τ) :
    _root_.DirectedSystem (fun i : Index S => (S.obj i).carrier)
      (fun i j (h : i ≤ j) => S.map h) where
  map_self i x := by
    change (S.map (S.refl i)) x = x
    rw [S.map_refl]
    rfl
  map_map k j i hij hjk x := by
    have hle : hij.trans hjk = S.trans hij hjk := rfl
    rw [hle, S.map_trans hij hjk]
    rfl

/-- The mathlib direct limit, packaged as a `τ`-structure. -/
noncomputable def limitModel {τ : Tau.{u}} (S : DirectedSystem τ) : Model τ where
  carrier := Language.DirectLimit (fun i : Index S => (S.obj i).carrier)
    (fun i j (h : i ≤ j) => S.map h)
  str := inferInstance

/-- The canonical embedding of a component into the direct limit. -/
noncomputable def limitCanon {τ : Tau.{u}} (S : DirectedSystem τ) (i : Index S) :
    Language.Embedding τ (S.obj i).carrier (limitModel S).carrier :=
  Language.DirectLimit.of τ (Index S) (fun i : Index S => (S.obj i).carrier)
    (fun i j (h : i ≤ j) => S.map h) i

lemma limitCanon_compat {τ : Tau.{u}} (S : DirectedSystem τ) {i j : Index S} (hij : i ≤ j) :
    (limitCanon S j).comp (S.map hij) = limitCanon S i := by
  ext x
  simp only [limitCanon, Language.Embedding.comp_apply]
  exact Language.DirectLimit.of_f (L := τ) (ι := Index S)
    (G := fun i : Index S => (S.obj i).carrier)
    (f := fun i j (h : i ≤ j) => S.map h) (hij := hij) (x := x)

lemma limitCanon_joint {τ : Tau.{u}} (S : DirectedSystem τ) (x : (limitModel S).carrier) :
    ∃ i : Index S, ∃ y : (S.obj i).carrier, limitCanon S i y = x :=
  Language.DirectLimit.exists_of (L := τ) (ι := Index S)
    (G := fun i : Index S => (S.obj i).carrier)
    (f := fun i j (h : i ≤ j) => S.map h) x

/-- The direct limit packaged with its canonical maps. -/
noncomputable def algebraicLimit {τ : Tau.{u}} (S : DirectedSystem τ) : DirectLimit S where
  obj := limitModel S
  canon := limitCanon S
  compat := limitCanon_compat S
  joint := limitCanon_joint S

/-- A structure isomorphism out of a member of `K` is a strong embedding. -/
lemma strong_of_equiv (K : AbstractElementaryClass.{u}) {M N : Model K.τ}
    (e : M.carrier ≃[K.τ] N.carrier) (hM : K.Mem M) : K.Strong e.toEmbedding := by
  have h := K.transport_strong (Language.Embedding.refl K.τ M.carrier) e (K.strong_refl M hM)
  simpa [Language.Embedding.comp_refl] using h

/-- A bijective embedding is a structure equivalence. -/
noncomputable def embeddingEquivOfSurjective {L : Tau.{u}} {M N : Type u}
    [L.Structure M] [L.Structure N] (f : M ↪[L] N) (hf : Function.Surjective f) :
    M ≃[L] N where
  toFun := f
  invFun := Function.surjInv hf
  left_inv := Function.leftInverse_surjInv ⟨f.injective, hf⟩
  right_inv := Function.rightInverse_surjInv hf
  map_fun' := f.map_fun'
  map_rel' := f.map_rel'

/-- What Lemma 2.1 asks of one direct limit. -/
def IsLimitInClass (K : AbstractElementaryClass.{u}) {S : DirectedSystem K.τ}
    (L : DirectLimit S) : Prop :=
  K.Mem L.obj ∧
    (∀ i, K.Strong (L.canon i)) ∧
      ∀ (N : Model K.τ)
        (g : ∀ i, Language.Embedding K.τ (S.obj i).carrier N.carrier),
        K.Mem N →
        (∀ i, K.Strong (g i)) →
        (∀ {i j} (hij : S.rel i j), (g j).comp (S.map hij) = g i) →
        ∃ f : Language.Embedding K.τ L.obj.carrier N.carrier,
          K.Strong f ∧ ∀ i, f.comp (L.canon i) = g i

/-- A directed system with a greatest index has the member at that index as its limit. -/
lemma directLimit_of_maximum (K : AbstractElementaryClass.{u}) (S : DirectedSystem K.τ)
    (hmem : ∀ i, K.Mem (S.obj i))
    (hstrong : ∀ {i j} (hij : S.rel i j), K.Strong (S.map hij))
    (m : Index S) (hm : ∀ i, i ≤ m) : ∃ L : DirectLimit S, IsLimitInClass K L := by
  let L := algebraicLimit S
  have hsurj : Function.Surjective (L.canon m) := by
    intro z
    obtain ⟨i, y, hy⟩ := L.joint z
    refine ⟨S.map (hm i) y, ?_⟩
    have hcomp : (L.canon m).comp (S.map (hm i)) = L.canon i := L.compat (hm i)
    have happ : (L.canon m) (S.map (hm i) y) = L.canon i y := by
      simpa [Language.Embedding.comp_apply] using congrFun (congrArg DFunLike.coe hcomp) y
    exact happ.trans hy
  let e : (S.obj m).carrier ≃[K.τ] L.obj.carrier :=
    embeddingEquivOfSurjective (L.canon m) hsurj
  have hcoe : e.toEmbedding = L.canon m := rfl
  have hcanm : K.Strong (L.canon m) := by
    simpa [hcoe] using strong_of_equiv K e (hmem m)
  have hmemL : K.Mem L.obj := K.strong_mem_cod (L.canon m) hcanm
  have hcan (i : Index S) : K.Strong (L.canon i) := by
    rw [← L.compat (hm i)]
    exact K.strong_trans (S.map (hm i)) (L.canon m) (hstrong (hm i)) hcanm
  refine ⟨L, hmemL, hcan, ?_⟩
  intro N g _ hg hcompat
  let Hg : ∀ (i j : Index S) (hij : i ≤ j) (x : (S.obj i).carrier),
      g j (S.map hij x) = g i x :=
    fun i j hij x => congrFun (congrArg DFunLike.coe (hcompat hij)) x
  let induced := Language.DirectLimit.lift K.τ (Index S)
    (fun i : Index S => (S.obj i).carrier) (fun i j (h : i ≤ j) => S.map h) g Hg
  have hfactor : induced = (g m).comp e.symm.toEmbedding := by
    ext z
    obtain ⟨y, rfl⟩ := hsurj z
    have hleft : induced (L.canon m y) = g m y := by
      simp only [induced, L, algebraicLimit]
      exact Language.DirectLimit.lift_of (L := K.τ) (ι := Index S)
        (G := fun i : Index S => (S.obj i).carrier)
        (f := fun i j (h : i ≤ j) => S.map h) g Hg (i := m) y
    have hright : ((g m).comp e.symm.toEmbedding) (L.canon m y) = g m y := by
      simp [Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding]
      exact e.left_inv y
    exact hleft.trans hright.symm
  have hsym : K.Strong e.symm.toEmbedding := strong_of_equiv K e.symm hmemL
  refine ⟨induced, ?_, ?_⟩
  · rw [hfactor]
    exact K.strong_trans e.symm.toEmbedding (g m) hsym (hg m)
  · intro i
    ext x
    simp only [induced, L, algebraicLimit, Language.Embedding.comp_apply]
    exact Language.DirectLimit.lift_of (L := K.τ) (ι := Index S)
      (G := fun i : Index S => (S.obj i).carrier)
      (f := fun i j (h : i ≤ j) => S.map h) g Hg (i := i) x

/-- A proof that two models are equal induces a structure equivalence. -/
def equivOfEq {τ : Tau.{u}} {M N : Model τ} (h : M = N) :
    M.carrier ≃[τ] N.carrier :=
  match h with
  | rfl => Language.Equiv.refl τ M.carrier

/-- A proof that two models are equal induces a structure embedding. -/
def embeddingOfEq {τ : Tau.{u}} {M N : Model τ} (h : M = N) :
    Language.Embedding τ M.carrier N.carrier :=
  (equivOfEq h).toEmbedding

lemma embeddingOfEq_rfl {τ : Tau.{u}} (M : Model τ) :
    embeddingOfEq (rfl : M = M) = Language.Embedding.refl τ M.carrier := by
  ext x
  simp [embeddingOfEq, equivOfEq, Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding,
    Language.Embedding.refl_apply]

lemma embeddingOfEq_symm_comp {τ : Tau.{u}} {M N : Model τ} (h : M = N) :
    (embeddingOfEq h.symm).comp (embeddingOfEq h) =
      Language.Embedding.refl τ M.carrier := by
  cases h
  ext x
  simp [embeddingOfEq, equivOfEq, Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding,
    Language.Embedding.refl_apply]

lemma embeddingOfEq_comp_symm {τ : Tau.{u}} {M N : Model τ} (h : M = N) :
    (embeddingOfEq h).comp (embeddingOfEq h.symm) =
      Language.Embedding.refl τ N.carrier := by
  cases h
  ext x
  simp [embeddingOfEq, equivOfEq, Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding,
    Language.Embedding.refl_apply]

lemma map_proof_irrel {τ : Tau.{u}} (S : DirectedSystem τ) {i j : Index S}
    (h₁ h₂ : i ≤ j) : S.map h₁ = S.map h₂ := by
  have h := Subsingleton.elim h₁ h₂
  rw [h]

/-- Enumerate the index and close upward one step at a time. -/
noncomputable def cofinalSeq {τ : Tau.{u}} (S : DirectedSystem τ) (enum : ℕ → Index S) :
    ℕ → Index S :=
  fun n =>
    Nat.rec (motive := fun _ => Index S) (enum 0)
      (fun k prev => Classical.choose (S.directed prev (enum (k + 1)))) n

lemma cofinalSeq_zero {τ : Tau.{u}} (S : DirectedSystem τ) (enum : ℕ → Index S) :
    cofinalSeq S enum 0 = enum 0 := rfl

lemma cofinalSeq_succ {τ : Tau.{u}} (S : DirectedSystem τ) (enum : ℕ → Index S) (n : ℕ) :
    cofinalSeq S enum (n + 1) =
      Classical.choose (S.directed (cofinalSeq S enum n) (enum (n + 1))) := rfl

lemma cofinalSeq_step {τ : Tau.{u}} (S : DirectedSystem τ) (enum : ℕ → Index S) (n : ℕ) :
    cofinalSeq S enum n ≤ cofinalSeq S enum (n + 1) ∧
      enum (n + 1) ≤ cofinalSeq S enum (n + 1) := by
  rw [cofinalSeq_succ]
  exact Classical.choose_spec (S.directed (cofinalSeq S enum n) (enum (n + 1)))

lemma cofinalSeq_mono_add {τ : Tau.{u}} (S : DirectedSystem τ) (enum : ℕ → Index S)
    (n k : ℕ) : cofinalSeq S enum n ≤ cofinalSeq S enum (n + k) := by
  induction k with
  | zero => exact S.refl _
  | succ k ih => exact S.trans ih (cofinalSeq_step S enum (n + k)).1

lemma cofinalSeq_mono {τ : Tau.{u}} (S : DirectedSystem τ) (enum : ℕ → Index S)
    {n m : ℕ} (hnm : n ≤ m) : cofinalSeq S enum n ≤ cofinalSeq S enum m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact cofinalSeq_mono_add S enum n k

lemma cofinalSeq_enum_le {τ : Tau.{u}} (S : DirectedSystem τ) (enum : ℕ → Index S) (n : ℕ) :
    enum n ≤ cofinalSeq S enum n := by
  cases n with
  | zero => exact S.refl _
  | succ n => exact (cofinalSeq_step S enum n).2

/-- The natural number represented by an ordinal below `ω`. -/
noncomputable def natOfOmega (i : _root_.Ordinal.{u}) (hi : i < _root_.Ordinal.omega0) : ℕ :=
  Classical.choose (_root_.Ordinal.lt_omega0.mp hi)

lemma natOfOmega_cast (i : _root_.Ordinal.{u}) (hi : i < _root_.Ordinal.omega0) :
    ((natOfOmega i hi : ℕ) : _root_.Ordinal.{u}) = i :=
  (Classical.choose_spec (_root_.Ordinal.lt_omega0.mp hi)).symm

lemma natOfOmega_nat (n : ℕ) :
    natOfOmega (n : _root_.Ordinal.{u}) (_root_.Ordinal.natCast_lt_omega0 n) = n := by
  apply Nat.cast_injective (R := _root_.Ordinal.{u})
  simpa using natOfOmega_cast (n : _root_.Ordinal.{u}) (_root_.Ordinal.natCast_lt_omega0 n)

/-- Comparing ordinals below `ω` is comparing their natural-number codes. -/
theorem natLtOfOrdinalLt {i j : _root_.Ordinal.{u}} (hi : i < _root_.Ordinal.omega0)
    (hj : j < _root_.Ordinal.omega0) (hij : i < j) :
    natOfOmega i hi < natOfOmega j hj :=
  (Nat.cast_lt (α := _root_.Ordinal.{u})).mp <| by
    rw [natOfOmega_cast i hi, natOfOmega_cast j hj]
    exact hij

/-- The ordinal chain along a monotone `ω`-sequence of indices. -/
noncomputable def omegaChain {τ : Tau.{u}} (S : DirectedSystem τ) (seq : ℕ → Index S)
    (hmono : ∀ {n m : ℕ}, n ≤ m → seq n ≤ seq m) : OrdinalChain τ where
  δ := _root_.Ordinal.omega0
  nonzero := _root_.Ordinal.omega0_ne_zero
  obj := fun i hi => S.obj (seq (natOfOmega i hi))
  map := fun i j hi hj hij => S.map (hmono (natLtOfOrdinalLt hi hj hij).le)

lemma omegaChain_obj {τ : Tau.{u}} (S : DirectedSystem τ) (seq : ℕ → Index S)
    (hmono : ∀ {n m : ℕ}, n ≤ m → seq n ≤ seq m)
    (i : _root_.Ordinal.{u}) (hi : i < _root_.Ordinal.omega0) :
    (omegaChain S seq hmono).obj i hi = S.obj (seq (natOfOmega i hi)) := rfl

lemma omegaChain_map {τ : Tau.{u}} (S : DirectedSystem τ) (seq : ℕ → Index S)
    (hmono : ∀ {n m : ℕ}, n ≤ m → seq n ≤ seq m)
    (i j : _root_.Ordinal.{u}) (hi : i < _root_.Ordinal.omega0) (hj : j < _root_.Ordinal.omega0)
    (hij : i < j) :
    (omegaChain S seq hmono).map i j hi hj hij =
      S.map (hmono (natLtOfOrdinalLt hi hj hij).le) := rfl

lemma omegaChain_obj_nat {τ : Tau.{u}} (S : DirectedSystem τ) (seq : ℕ → Index S)
    (hmono : ∀ {n m : ℕ}, n ≤ m → seq n ≤ seq m) (n : ℕ) :
    (omegaChain S seq hmono).obj n (_root_.Ordinal.natCast_lt_omega0 n) = S.obj (seq n) := by
  rw [omegaChain_obj]
  exact congrArg (fun k => S.obj (seq k)) (natOfOmega_nat n)

lemma omegaChain_map_comp {τ : Tau.{u}} (S : DirectedSystem τ) (seq : ℕ → Index S)
    (hmono : ∀ {n m : ℕ}, n ≤ m → seq n ≤ seq m) :
    OrdinalChain.map_comp_prop τ (omegaChain S seq hmono) := by
  intro i j k hi hj hk hij hjk
  unfold omegaChain
  dsimp
  let p := hmono (natLtOfOrdinalLt hi hj hij).le
  let q := hmono (natLtOfOrdinalLt hj hk hjk).le
  let r := hmono (natLtOfOrdinalLt hi hk (hij.trans hjk)).le
  have hcomp := S.map_trans p q
  exact hcomp.symm.trans (map_proof_irrel S (S.trans p q) r)

/-- Transporting the endpoints of a transition along equal indices is the transported transition. -/
lemma embedding_cast_natural {τ : Tau.{u}} (S : DirectedSystem τ) (seq : ℕ → Index S)
    (hmono : ∀ {n m : ℕ}, n ≤ m → seq n ≤ seq m)
    {a b a' b' : ℕ} (ha : a = a') (hb : b = b') (hab : seq a ≤ seq b) :
    (embeddingOfEq (congrArg (fun k : ℕ => S.obj (seq k)) hb)).comp (S.map hab) =
      (S.map (Eq.mp (congrArg (fun t => seq a' ≤ seq t) hb)
        (Eq.mp (congrArg (fun t => seq t ≤ seq b) ha) hab))).comp
        (embeddingOfEq (congrArg (fun k : ℕ => S.obj (seq k)) ha)) := by
  cases ha
  cases hb
  ext x
  simp [embeddingOfEq, equivOfEq, Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding,
    Language.Embedding.refl_apply]

/-- Moving across `natOfOmega ↑n = n` commutes with a transition of the cofinal sequence. -/
lemma cofinal_cast_natural {τ : Tau.{u}} (S : DirectedSystem τ) (seq : ℕ → Index S)
    (hmono : ∀ {n m : ℕ}, n ≤ m → seq n ≤ seq m) {n m : ℕ} (hnm : n < m) :
    (embeddingOfEq (congrArg (fun k : ℕ => S.obj (seq k)) (natOfOmega_nat m))).comp
        (S.map (hmono (natLtOfOrdinalLt
          (_root_.Ordinal.natCast_lt_omega0 n) (_root_.Ordinal.natCast_lt_omega0 m)
          ((Nat.cast_lt (α := _root_.Ordinal.{u})).mpr hnm)).le)) =
      (S.map (hmono hnm.le)).comp
        (embeddingOfEq (congrArg (fun k : ℕ => S.obj (seq k)) (natOfOmega_nat n))) := by
  let hab := hmono (natLtOfOrdinalLt
    (_root_.Ordinal.natCast_lt_omega0 n) (_root_.Ordinal.natCast_lt_omega0 m)
    ((Nat.cast_lt (α := _root_.Ordinal.{u})).mpr hnm)).le
  have hraw := embedding_cast_natural S seq hmono (natOfOmega_nat n) (natOfOmega_nat m) hab
  have hmap := map_proof_irrel S
    (Eq.mp (congrArg (fun t => seq n ≤ seq t) (natOfOmega_nat m))
      (Eq.mp (congrArg (fun t => seq t ≤ seq (natOfOmega m
        (_root_.Ordinal.natCast_lt_omega0 m))) (natOfOmega_nat n)) hab))
    (hmono hnm.le)
  simpa [hmap] using hraw

/-- A countable directed system is the union of a cofinal `ω`-chain. -/
lemma directLimit_of_countable (K : AbstractElementaryClass.{u}) (S : DirectedSystem K.τ)
    (hmem : ∀ i, K.Mem (S.obj i))
    (hstrong : ∀ {i j} (hij : S.rel i j), K.Strong (S.map hij))
    (hcount : Cardinal.mk (Index S) ≤ aleph0) : ∃ L : DirectLimit S, IsLimitInClass K L := by
  haveI : Countable (Index S) := Cardinal.mk_le_aleph0_iff.mp hcount
  obtain ⟨enum, henum⟩ := exists_surjective_nat (Index S)
  let seq : ℕ → Index S := cofinalSeq S enum
  have hmono : ∀ {n m : ℕ}, n ≤ m → seq n ≤ seq m :=
    fun {n m} hnm => cofinalSeq_mono S enum hnm
  have hcof : ∀ i, ∃ n, i ≤ seq n := by
    intro i
    obtain ⟨n, hn⟩ := henum i
    refine ⟨n, ?_⟩
    rw [← hn]
    exact cofinalSeq_enum_le S enum n
  let stage : Index S → ℕ := fun i => Nat.find (hcof i)
  have hstage : ∀ i, i ≤ seq (stage i) := fun i => Nat.find_spec (hcof i)
  have hstage_min : ∀ i n, i ≤ seq n → stage i ≤ n := fun i n h => Nat.find_min' (hcof i) h
  have hstage_mono : ∀ {i j : Index S}, i ≤ j → stage i ≤ stage j := by
    intro i j hij
    exact hstage_min i (stage j) (S.trans hij (hstage j))
  let C := omegaChain S seq hmono
  have hCcomp : OrdinalChain.map_comp_prop K.τ C := omegaChain_map_comp S seq hmono
  have hCmem : ∀ i hi, K.Mem (C.obj i hi) := by
    intro i hi
    rw [show C.obj i hi = S.obj (seq (natOfOmega i hi)) from omegaChain_obj S seq hmono i hi]
    exact hmem _
  have hCstrong : ∀ i j hi hj hij, K.Strong (C.map i j hi hj hij) := by
    intro i j hi hj hij
    unfold C omegaChain
    dsimp
    exact hstrong _
  obtain ⟨U, hUmem, hUstrong⟩ := K.chain_union C hCcomp hCmem hCstrong
  have hδ : C.δ = _root_.Ordinal.omega0 := rfl
  let hnat (k : ℕ) : (k : _root_.Ordinal.{u}) < C.δ := hδ ▸ _root_.Ordinal.natCast_lt_omega0 k
  let objNat (n : ℕ) := omegaChain_obj_nat S seq hmono n
  let eInto (n : ℕ) := embeddingOfEq (objNat n).symm
  let castInto (n : ℕ) := embeddingOfEq (objNat n)
  let fromSeq (n : ℕ) := (U.incl n (hnat n)).comp (eInto n)
  have hfrom_nat (n m : ℕ) (hnm : n < m) :
      (fromSeq m).comp (S.map (hmono hnm.le)) = fromSeq n := by
    have hroundC (k : ℕ) := embeddingOfEq_symm_comp (objNat k)
    have hroundS (k : ℕ) := embeddingOfEq_comp_symm (objNat k)
    have hcastEq (k : ℕ) :
        castInto k =
          embeddingOfEq (congrArg (fun t : ℕ => S.obj (seq t)) (natOfOmega_nat k)) :=
      congrArg embeddingOfEq
        (Subsingleton.elim (objNat k)
          (congrArg (fun t : ℕ => S.obj (seq t)) (natOfOmega_nat k)))
    let hord : (n : _root_.Ordinal.{u}) < m := (Nat.cast_lt (α := _root_.Ordinal.{u})).mpr hnm
    let cnat := C.map n m (hnat n) (hnat m) hord
    have hmap : cnat = S.map (hmono (natLtOfOrdinalLt
        (_root_.Ordinal.natCast_lt_omega0 n) (_root_.Ordinal.natCast_lt_omega0 m) hord).le) :=
      omegaChain_map S seq hmono n m (hnat n) (hnat m) hord
    have hleft : (castInto m).comp cnat = (S.map (hmono hnm.le)).comp (castInto n) := by
      rw [hcastEq n, hcastEq m, hmap]
      exact cofinal_cast_natural S seq hmono hnm
    have hpull : cnat.comp (eInto n) = (eInto m).comp (S.map (hmono hnm.le)) := by
      ext x
      have hL := congrFun (congrArg DFunLike.coe hleft) (eInto n x)
      have hcancel := congrFun (congrArg DFunLike.coe (hroundS n)) x
      have hback := congrFun (congrArg DFunLike.coe (hroundC m)) (cnat (eInto n x))
      simp only [Language.Embedding.comp_apply, Language.Embedding.refl_apply] at hL hcancel hback ⊢
      rw [← hback, hL, hcancel]
    ext x
    have happ := congrFun (congrArg DFunLike.coe (U.compat n m (hnat n) (hnat m) hord)) (eInto n x)
    have hp := congrFun (congrArg DFunLike.coe hpull) x
    simp only [fromSeq, Language.Embedding.comp_apply] at happ hp ⊢
    rw [← hp, happ]
  let canon (i : Index S) := (fromSeq (stage i)).comp (S.map (hstage i))
  have hcanon_compat {i j : Index S} (hij : i ≤ j) :
      (canon j).comp (S.map hij) = canon i := by
    have hle : stage i ≤ stage j := hstage_mono hij
    ext x
    rcases lt_or_eq_of_le hle with hlt | heq
    · have htrans : (S.map (hstage j)).comp (S.map hij) =
          (S.map (hmono hlt.le)).comp (S.map (hstage i)) := by
        have hleft := (S.map_trans hij (hstage j)).symm
        have hright := S.map_trans (hstage i) (hmono hlt.le)
        exact hleft.trans
          ((map_proof_irrel S (S.trans hij (hstage j))
            (S.trans (hstage i) (hmono hlt.le))).trans hright)
      have hfrom := hfrom_nat (stage i) (stage j) hlt
      simp only [canon, Language.Embedding.comp_apply]
      have hfx := congrFun (congrArg DFunLike.coe htrans) x
      have hff := congrFun (congrArg DFunLike.coe hfrom) (S.map (hstage i) x)
      simp only [Language.Embedding.comp_apply] at hfx hff
      rw [hfx, hff]
    · simp only [canon, Language.Embedding.comp_apply]
      have hjb : j ≤ seq (stage j) := hstage j
      rw [map_proof_irrel S (hstage j) hjb]
      have hab : stage j = stage i := heq.symm
      revert hab hjb
      generalize hb : stage j = b
      intro hjb hab
      subst hab
      have hmaps : S.map hjb (S.map hij x) = S.map (hstage i) x := by
        have hcomp := (S.map_trans hij hjb).symm
        have hirr := map_proof_irrel S (S.trans hij hjb) (hstage i)
        exact congrFun (congrArg DFunLike.coe (hcomp.trans hirr)) x
      rw [hmaps]
  let L := algebraicLimit S
  let Hg : ∀ (i j : Index S) (hij : i ≤ j) (x : (S.obj i).carrier),
      canon j (S.map hij x) = canon i x :=
    fun i j hij x => congrFun (congrArg DFunLike.coe (hcanon_compat hij)) x
  let induced := Language.DirectLimit.lift K.τ (Index S)
    (fun i : Index S => (S.obj i).carrier) (fun i j (h : i ≤ j) => S.map h) canon Hg
  have hlift (i : Index S) (x : (S.obj i).carrier) :
      induced (L.canon i x) = canon i x := by
    simp only [induced, L, algebraicLimit]
    exact Language.DirectLimit.lift_of (L := K.τ) (ι := Index S)
      (G := fun i : Index S => (S.obj i).carrier)
      (f := fun i j (h : i ≤ j) => S.map h) canon Hg (i := i) x
  have hsurj : Function.Surjective induced := by
    intro z
    obtain ⟨i, hi, y, hy⟩ := U.covers z
    obtain ⟨n, rfl⟩ := _root_.Ordinal.lt_omega0.mp hi
    have hhi : hi = _root_.Ordinal.natCast_lt_omega0 n := Subsingleton.elim _ _
    subst hhi
    let yS := castInto n y
    have hz : fromSeq n yS = z := by
      have hround : eInto n (castInto n y) = y := by
        have happ := congrFun (congrArg DFunLike.coe (embeddingOfEq_symm_comp (objNat n))) y
        rw [Language.Embedding.comp_apply, Language.Embedding.refl_apply] at happ
        exact happ
      have hpr : hnat n = _root_.Ordinal.natCast_lt_omega0 n := Subsingleton.elim _ _
      simp only [fromSeq, Language.Embedding.comp_apply]
      rw [hpr]
      exact (congrArg (U.incl n (_root_.Ordinal.natCast_lt_omega0 n)) hround).trans hy
    have ha : stage (seq n) ≤ n := hstage_min (seq n) n (S.refl _)
    rcases lt_or_eq_of_le ha with hlt | heq
    · have hforth : (S.map (hmono hlt.le)).comp (S.map (hstage (seq n))) =
          Language.Embedding.refl K.τ (S.obj (seq n)).carrier := by
        have hcomp := S.map_trans (hstage (seq n)) (hmono hlt.le)
        exact hcomp.symm.trans
          ((map_proof_irrel S (S.trans (hstage (seq n)) (hmono hlt.le)) (S.refl _)).trans
            (S.map_refl _))
      have hyS : yS = S.map (hmono hlt.le) (S.map (hstage (seq n)) yS) := by
        have happ := congrFun (congrArg DFunLike.coe hforth) yS
        simp only [Language.Embedding.comp_apply, Language.Embedding.refl_apply] at happ
        exact happ.symm
      have hfrom := congrFun (congrArg DFunLike.coe (hfrom_nat _ _ hlt))
        (S.map (hstage (seq n)) yS)
      simp only [Language.Embedding.comp_apply] at hfrom
      refine ⟨L.canon (seq n) yS, ?_⟩
      rw [hlift]
      simp only [canon, Language.Embedding.comp_apply]
      rw [← hfrom, ← hyS]
      exact hz
    · refine ⟨L.canon (seq n) yS, ?_⟩
      rw [hlift]
      simp only [canon, Language.Embedding.comp_apply]
      have hfun (b : ℕ) (hb : seq n ≤ seq b) (hb' : b = n) :
          fromSeq b (S.map hb yS) = fromSeq n yS := by
        subst hb'
        rw [map_proof_irrel S hb (S.refl (seq b)), S.map_refl, Language.Embedding.refl_apply]
      exact (hfun (stage (seq n)) (hstage (seq n)) heq).trans hz
  let eLim : L.obj.carrier ≃[K.τ] U.obj.carrier := embeddingEquivOfSurjective induced hsurj
  have hmemL : K.Mem L.obj := K.iso_closed ⟨eLim.symm⟩ hUmem
  have hsym : K.Strong eLim.symm.toEmbedding := strong_of_equiv K eLim.symm hUmem
  have heInto (k : ℕ) : K.Strong (eInto k) :=
    strong_of_equiv K (equivOfEq (objNat k).symm) (hmem (seq k))
  have hfromStrong (k : ℕ) : K.Strong (fromSeq k) :=
    K.strong_trans (eInto k) (U.incl k (hnat k)) (heInto k) (hUstrong k (hnat k))
  have hcanonStrong (i : Index S) : K.Strong (canon i) :=
    K.strong_trans (S.map (hstage i)) (fromSeq (stage i)) (hstrong _) (hfromStrong _)
  have hfac (i : Index S) : L.canon i = eLim.symm.toEmbedding.comp (canon i) := by
    ext x
    simp only [Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding]
    have happ := hlift i x
    have hcoe : eLim (L.canon i x) = induced (L.canon i x) := rfl
    rw [← happ, ← hcoe]
    exact (eLim.left_inv (L.canon i x)).symm
  have hcan (i : Index S) : K.Strong (L.canon i) := by
    rw [hfac i]
    exact K.strong_trans (canon i) eLim.symm.toEmbedding (hcanonStrong i) hsym
  refine ⟨L, hmemL, hcan, ?_⟩
  intro N g hN hg hgcompat
  let gC : ∀ i (hi : i < C.δ), Language.Embedding K.τ (C.obj i hi).carrier N.carrier :=
    fun i hi => g (seq (natOfOmega i hi))
  have hgC (i hi) : K.Strong (gC i hi) := hg _
  have hgCcompat (i j hi hj hij) : (gC j hj).comp (C.map i j hi hj hij) = gC i hi := by
    have hδi : i < _root_.Ordinal.omega0 := by rw [← hδ]; exact hi
    have hδj : j < _root_.Ordinal.omega0 := by rw [← hδ]; exact hj
    rw [omegaChain_map S seq hmono i j hδi hδj hij]
    exact hgcompat (hmono (natLtOfOrdinalLt hδi hδj hij).le)
  have hCstrong' : ∀ i j hi hj hij, K.Strong (C.map i j hi hj hij) := hCstrong
  obtain ⟨fU, hfU, hfUincl⟩ := K.chain_upper C U N gC hCcomp hCmem hCstrong' hUstrong
    hN hgC hgCcompat
  refine ⟨fU.comp eLim.toEmbedding, ?_, ?_⟩
  · exact K.strong_trans eLim.toEmbedding fU (strong_of_equiv K eLim hmemL) hfU
  · intro i
    ext x
    have hthrough : fU (canon i x) = g i x := by
      have hfun (b : ℕ) (hb : i ≤ seq b) :
          fU (fromSeq b (S.map hb x)) = g i x := by
        have hincl := congrFun (congrArg DFunLike.coe (hfUincl b (hnat b))) (eInto b (S.map hb x))
        simp only [fromSeq, gC, Language.Embedding.comp_apply] at hincl ⊢
        have hcancel := congrFun (congrArg DFunLike.coe (embeddingOfEq_comp_symm (objNat b)))
          (S.map hb x)
        simp only [Language.Embedding.comp_apply, Language.Embedding.refl_apply] at hcancel
        have hmove (t : ℕ) (ht : t = b) (z : (S.obj (seq t)).carrier) :
            g (seq t) z =
              g (seq b) (Eq.mp (congrArg (fun s => (S.obj (seq s)).carrier) ht) z) := by
          subst ht
          rfl
        have hpr : hnat b = _root_.Ordinal.natCast_lt_omega0 b := Subsingleton.elim _ _
        have hn : natOfOmega b (hnat b) = b := by rw [hpr]; exact natOfOmega_nat b
        have hz := hmove (natOfOmega b (hnat b)) hn (eInto b (S.map hb x))
        have hgmap := congrFun (congrArg DFunLike.coe (hgcompat hb)) x
        simp only [Language.Embedding.comp_apply] at hgmap
        have hidx (t : ℕ) (ht : t = b) (z : (S.obj (seq t)).carrier) :
            embeddingOfEq (congrArg (fun s => S.obj (seq s)) ht) z =
              Eq.mp (congrArg (fun s => (S.obj (seq s)).carrier) ht) z := by
          subst ht
          simp [embeddingOfEq_rfl, Language.Embedding.refl_apply, Eq.mp]
        have hsame : objNat b = congrArg (fun s => S.obj (seq s)) hn := Subsingleton.elim _ _
        have hcast : Eq.mp (congrArg (fun s => (S.obj (seq s)).carrier) hn)
            (eInto b (S.map hb x)) = S.map hb x := by
          rw [← hidx (natOfOmega b (hnat b)) hn (eInto b (S.map hb x)), ← hsame]
          exact hcancel
        exact (hincl.trans hz).trans (by rw [hcast]; exact hgmap)
      -- canon i x = fromSeq (stage i) (S.map (hstage i) x)
      simpa [canon, Language.Embedding.comp_apply] using hfun (stage i) (hstage i)
    have hlim : eLim (L.canon i x) = canon i x := by
      simp only [eLim, Language.Equiv.coe_toEmbedding]
      exact hlift i x
    simp only [Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding]
    rw [hlim, hthrough]

/-- A chosen common upper bound of two indices. -/
noncomputable def upperBound {τ : Tau.{u}} (S : DirectedSystem τ) (i j : Index S) : Index S :=
  Classical.choose (S.directed i j)

lemma upperBound_spec {τ : Tau.{u}} (S : DirectedSystem τ) (i j : Index S) :
    i ≤ upperBound S i j ∧ j ≤ upperBound S i j :=
  Classical.choose_spec (S.directed i j)

/-- One step of closing a set of indices under chosen upper bounds. -/
def closeStep {τ : Tau.{u}} (S : DirectedSystem τ) (t : Set (Index S)) : Set (Index S) :=
  t ∪ {z | ∃ i ∈ t, ∃ j ∈ t, z = upperBound S i j}

lemma closeStep_mono {τ : Tau.{u}} (S : DirectedSystem τ) {t₁ t₂ : Set (Index S)}
    (h : t₁ ⊆ t₂) : closeStep S t₁ ⊆ closeStep S t₂ := by
  intro z hz
  rcases hz with hz | ⟨i, hi, j, hj, rfl⟩
  · exact Or.inl (h hz)
  · exact Or.inr ⟨i, h hi, j, h hj, rfl⟩

lemma subset_closeStep {τ : Tau.{u}} (S : DirectedSystem τ) (t : Set (Index S)) :
    t ⊆ closeStep S t :=
  Set.subset_union_left

/-- Iterate the closure. Stage `0` is the seed. -/
noncomputable def closeIter {τ : Tau.{u}} (S : DirectedSystem τ) (seed : Set (Index S)) :
    ℕ → Set (Index S)
  | 0 => seed
  | n + 1 => closeStep S (closeIter S seed n)

lemma closeIter_mono_succ {τ : Tau.{u}} (S : DirectedSystem τ) (seed : Set (Index S)) (n : ℕ) :
    closeIter S seed n ⊆ closeIter S seed (n + 1) := by
  cases n with
  | zero => exact subset_closeStep S seed
  | succ n =>
    exact closeStep_mono S (closeIter_mono_succ S seed n)

lemma closeIter_mono_add {τ : Tau.{u}} (S : DirectedSystem τ) (seed : Set (Index S))
    (n k : ℕ) : closeIter S seed n ⊆ closeIter S seed (n + k) := by
  induction k with
  | zero => exact Set.Subset.rfl
  | succ k ih => exact ih.trans (closeIter_mono_succ S seed (n + k))

lemma closeIter_mono {τ : Tau.{u}} (S : DirectedSystem τ) (seed : Set (Index S))
    {n m : ℕ} (hnm : n ≤ m) : closeIter S seed n ⊆ closeIter S seed m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  exact closeIter_mono_add S seed n k

/-- The indices reachable from `seed` by finitely many chosen upper bounds. -/
def closeOf {τ : Tau.{u}} (S : DirectedSystem τ) (seed : Set (Index S)) : Set (Index S) :=
  ⋃ n, closeIter S seed n

lemma closeIter_subset_close {τ : Tau.{u}} (S : DirectedSystem τ) (seed : Set (Index S)) (n : ℕ) :
    closeIter S seed n ⊆ closeOf S seed :=
  Set.subset_iUnion _ n

lemma closeOf_directed {τ : Tau.{u}} (S : DirectedSystem τ) (seed : Set (Index S))
    {i j : Index S} (hi : i ∈ closeOf S seed) (hj : j ∈ closeOf S seed) :
    upperBound S i j ∈ closeOf S seed := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hi
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hj
  let k := max n m
  have hik : i ∈ closeIter S seed k := closeIter_mono S seed (Nat.le_max_left n m) hn
  have hjk : j ∈ closeIter S seed k := closeIter_mono S seed (Nat.le_max_right n m) hm
  refine Set.mem_iUnion.mpr ⟨k + 1, ?_⟩
  exact Or.inr ⟨i, hik, j, hjk, rfl⟩

/-- The directed system of members indexed by a nonempty set closed under chosen upper bounds. -/
noncomputable def subsystem {τ : Tau.{u}} (S : DirectedSystem τ) (s : Set (Index S))
    (hne : s.Nonempty) (hdir : ∀ i ∈ s, ∀ j ∈ s, ∃ k ∈ s, i ≤ k ∧ j ≤ k) : DirectedSystem τ where
  ι := ↥s
  nonempty := ⟨⟨Classical.choose hne, Classical.choose_spec hne⟩⟩
  rel := fun a b => S.rel a.1 b.1
  refl := fun a => S.refl a.1
  trans := fun hab hbc => S.trans hab hbc
  directed := fun a b => by
    obtain ⟨k, hk, hak, hbk⟩ := hdir a.1 a.2 b.1 b.2
    exact ⟨⟨k, hk⟩, hak, hbk⟩
  obj := fun a => S.obj a.1
  map := fun hab => S.map hab
  map_refl := fun a => S.map_refl a.1
  map_trans := fun hab hbc => S.map_trans hab hbc

lemma subsystem_card_le {τ : Tau.{u}} (S : DirectedSystem τ) (s : Set (Index S))
    (hne : s.Nonempty) (hdir : ∀ i ∈ s, ∀ j ∈ s, ∃ k ∈ s, i ≤ k ∧ j ≤ k) :
    Cardinal.mk (Index (subsystem S s hne hdir)) = Cardinal.mk s := rfl

lemma closeStep_card {τ : Tau.{u}} (S : DirectedSystem τ) (t : Set (Index S))
    {μ : Cardinal.{u}} (hμ : aleph0 ≤ μ) (ht : Cardinal.mk t ≤ μ) :
    Cardinal.mk (closeStep S t) ≤ μ := by
  let img : Set (Index S) := {z | ∃ i ∈ t, ∃ j ∈ t, z = upperBound S i j}
  have hsurj : Function.Surjective
      (fun p : ↥t × ↥t => (⟨upperBound S p.1.1 p.2.1,
        ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩⟩ : ↥img)) := by
    intro z
    obtain ⟨i, hi, j, hj, hz⟩ := z.2
    refine ⟨(⟨i, hi⟩, ⟨j, hj⟩), ?_⟩
    apply Subtype.ext
    exact hz.symm
  have hprod : Cardinal.mk (↥t × ↥t) = Cardinal.mk t * Cardinal.mk t := by
    simpa [Cardinal.lift_id] using Cardinal.mk_prod (↥t) (↥t)
  have himg : Cardinal.mk img ≤ Cardinal.mk t * Cardinal.mk t :=
    (Cardinal.mk_le_of_surjective hsurj).trans_eq hprod
  have hmul : Cardinal.mk t * Cardinal.mk t ≤ μ :=
    (mul_le_mul ht ht (Cardinal.zero_le _) (Cardinal.zero_le _)).trans_eq (Cardinal.mul_eq_self hμ)
  have hunion : Cardinal.mk (t ∪ img : Set (Index S)) ≤ Cardinal.mk t + Cardinal.mk img :=
    Cardinal.mk_union_le t img
  have hadd : Cardinal.mk t + Cardinal.mk img ≤ μ := by
    have himgμ : Cardinal.mk img ≤ μ := himg.trans hmul
    have htwo : (2 : Cardinal.{u}) ≤ aleph0 :=
      (show (2 : Cardinal.{u}) < aleph0 from Cardinal.natCast_lt_aleph0).le
    calc
      Cardinal.mk t + Cardinal.mk img ≤ μ + μ := add_le_add ht himgμ
      _ = 2 * μ := by rw [two_mul]
      _ ≤ aleph0 * μ := mul_le_mul htwo le_rfl (Cardinal.zero_le μ) (Cardinal.zero_le aleph0)
      _ = μ := by rw [mul_comm, Cardinal.mul_aleph0_eq hμ]
  have hstep : closeStep S t = t ∪ img := rfl
  rw [hstep]
  exact hunion.trans hadd

lemma closeIter_card {τ : Tau.{u}} (S : DirectedSystem τ) (seed : Set (Index S)) (n : ℕ) :
    Cardinal.mk (closeIter S seed n) ≤ max (Cardinal.mk seed) aleph0 := by
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
    exact closeStep_card S (closeIter S seed n) (le_max_right _ _) ih

lemma closeOf_card {τ : Tau.{u}} (S : DirectedSystem τ) (seed : Set (Index S)) :
    Cardinal.mk (closeOf S seed) ≤ max (Cardinal.mk seed) aleph0 := by
  let μ := max (Cardinal.mk seed) aleph0
  have hμ : aleph0 ≤ μ := le_max_right _ _
  let F : ULift.{u} ℕ → Set (Index S) := fun n => closeIter S seed n.down
  have hcover : closeOf S seed = ⋃ n, F n := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨ULift.up n, hn⟩
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨n.down, hn⟩
  have hiter : ∀ n, Cardinal.mk (F n) ≤ μ := fun n => closeIter_card S seed n.down
  have hindex : Cardinal.mk (ULift.{u} ℕ) = aleph0 := by
    rw [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0]
  have hsum : Cardinal.mk (⋃ n, F n) ≤ Cardinal.sum (fun n : ULift.{u} ℕ => Cardinal.mk (F n)) :=
    Cardinal.mk_iUnion_le_sum_mk
  have hconst : Cardinal.sum (fun n : ULift.{u} ℕ => Cardinal.mk (F n)) ≤
      Cardinal.sum (fun _ : ULift.{u} ℕ => μ) :=
    Cardinal.sum_le_sum _ _ hiter
  have heq : Cardinal.sum (fun _ : ULift.{u} ℕ => μ) = Cardinal.mk (ULift.{u} ℕ) * μ :=
    Cardinal.sum_const' (ULift.{u} ℕ) μ
  calc
    Cardinal.mk (closeOf S seed) = Cardinal.mk (⋃ n, F n) := by rw [hcover]
    _ ≤ Cardinal.mk (ULift.{u} ℕ) * μ := hsum.trans (hconst.trans_eq heq)
    _ = aleph0 * μ := by rw [hindex]
    _ = μ := by rw [mul_comm, Cardinal.mul_aleph0_eq hμ]

lemma closeIter_seed_mono {τ : Tau.{u}} (S : DirectedSystem τ) {seed₁ seed₂ : Set (Index S)}
    (h : seed₁ ⊆ seed₂) (n : ℕ) : closeIter S seed₁ n ⊆ closeIter S seed₂ n := by
  induction n with
  | zero => exact h
  | succ n ih => exact closeStep_mono S ih

lemma closeOf_mono {τ : Tau.{u}} (S : DirectedSystem τ) {seed₁ seed₂ : Set (Index S)}
    (h : seed₁ ⊆ seed₂) : closeOf S seed₁ ⊆ closeOf S seed₂ := by
  intro z hz
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr ⟨n, closeIter_seed_mono S h n hn⟩

lemma limit_ext {τ : Tau.{u}} {S : DirectedSystem τ} (L : DirectLimit S)
    {N : Type u} [τ.Structure N] (f g : L.obj.carrier ↪[τ] N)
    (h : ∀ i, f.comp (L.canon i) = g.comp (L.canon i)) : f = g := by
  ext z
  obtain ⟨i, y, rfl⟩ := L.joint z
  exact congrFun (congrArg DFunLike.coe (h i)) y

/-- A cardinal strictly below an infinite cardinal stays strictly below after adding one. -/
lemma addOne_lt_of_infinite {μ κ : Cardinal.{u}} (hκ : aleph0 ≤ κ) (hμ : μ < κ) : μ + 1 < κ := by
  by_cases hinf : aleph0 ≤ μ
  · rwa [Cardinal.add_one_eq hinf]
  · have hfin : μ < aleph0 := lt_of_not_ge hinf
    have hnat : ∃ n : ℕ, μ = n := Cardinal.lt_aleph0.mp hfin
    obtain ⟨n, rfl⟩ := hnat
    have h1 : (n : Cardinal.{u}) + 1 < aleph0 := by
      rw [← Nat.cast_add_one]
      exact Cardinal.natCast_lt_aleph0
    exact h1.trans_le hκ

lemma canon_transport {τ : Tau.{u}} {S : DirectedSystem τ} (L : DirectLimit S)
    {i j : Index S} (h : i = j) (x : (S.obj i).carrier) :
    L.canon j (Eq.mp (congrArg (fun k => (S.obj k).carrier) h) x) = L.canon i x := by
  subst h
  rfl

lemma eqMp_id {α : Sort _} (h : α = α) (x : α) : Eq.mp h x = x := by
  rw [Subsingleton.elim h rfl]
  rfl

lemma directLimit_in_class (K : AbstractElementaryClass.{u}) (S : DirectedSystem K.τ)
    (hmem : ∀ i, K.Mem (S.obj i))
    (hstrong : ∀ {i j} (hij : S.rel i j), K.Strong (S.map hij)) :
    ∃ L : DirectLimit S, IsLimitInClass K L := by
  suffices H : ∀ κ : Cardinal.{u}, ∀ T : DirectedSystem K.τ, Cardinal.mk (Index T) = κ →
      (∀ i, K.Mem (T.obj i)) →
      (∀ {i j} (hij : T.rel i j), K.Strong (T.map hij)) →
      ∃ L : DirectLimit T, IsLimitInClass K L from
    H _ S rfl hmem hstrong
  intro κ
  induction κ using WellFoundedLT.induction with
  | ind κ IH =>
    intro T hκ hTmem hTstrong
    by_cases hcount : κ ≤ aleph0
    · exact directLimit_of_countable K T hTmem hTstrong (by rw [hκ]; exact hcount)
    · have hbig : aleph0 < κ := lt_of_not_ge hcount
      let α := κ.ord.ToType
      have hα : Cardinal.mk α = κ := Cardinal.mk_ord_toType κ
      have hwell : ord (Cardinal.mk α) = _root_.Ordinal.type (α := α) (· < ·) := by
        rw [hα]
        exact (_root_.Ordinal.type_toType κ.ord).symm
      obtain ⟨e⟩ := Cardinal.eq.mp (hα.trans hκ.symm)
      obtain ⟨cofSet, hcof, _⟩ := _root_.Ordinal.exists_ord_cof_eq α
      let δ : _root_.Ordinal.{u} := _root_.Ordinal.type (α := ↥cofSet) (· < ·)
      have hδ : δ ≠ 0 := by
        obtain ⟨a0⟩ := T.nonempty
        obtain ⟨y, hy, _⟩ := hcof (e.symm a0)
        have : Nonempty (↥cofSet) := ⟨⟨y, hy⟩⟩
        exact _root_.Ordinal.type_ne_zero_of_nonempty (· < ·)
      let enum := _root_.Ordinal.enum (α := ↥cofSet) (· < ·)
      let point (i : _root_.Ordinal) (hi : i < δ) : α := (enum ⟨i, hi⟩).1
      have point_lt (i j : _root_.Ordinal) (hi : i < δ) (hj : j < δ) (hij : i < j) :
          point i hi < point j hj := by
        have hrel : enum ⟨i, hi⟩ < enum ⟨j, hj⟩ := (enum.map_rel_iff).2 hij
        exact hrel
      have point_le (i j : _root_.Ordinal) (hi : i < δ) (hj : j < δ) (hij : i ≤ j) :
          point i hi ≤ point j hj := by
        rcases lt_or_eq_of_le hij with hlt | heq
        · exact (point_lt i j hi hj hlt).le
        · subst heq
          have hpr : hi = hj := Subsingleton.elim _ _
          rw [hpr]
      let seed (i : _root_.Ordinal) (hi : i < δ) : Set (Index T) :=
        e '' {x : α | x ≤ point i hi}
      let stageSet (i : _root_.Ordinal) (hi : i < δ) : Set (Index T) := closeOf T (seed i hi)
      have seed_mono (i j : _root_.Ordinal) (hi : i < δ) (hj : j < δ) (hij : i ≤ j) :
          seed i hi ⊆ seed j hj := by
        intro z hz
        obtain ⟨x, hx, rfl⟩ := hz
        exact ⟨x, hx.trans (point_le i j hi hj hij), rfl⟩
      have stage_mono (i j : _root_.Ordinal) (hi : i < δ) (hj : j < δ) (hij : i ≤ j) :
          stageSet i hi ⊆ stageSet j hj :=
        closeOf_mono T (seed_mono i j hi hj hij)
      have stage_card (i : _root_.Ordinal) (hi : i < δ) : Cardinal.mk (stageSet i hi) < κ := by
        have hio : Cardinal.mk (Set.Iio (point i hi)) < Cardinal.mk α :=
          mk_Iio_lt (point i hi) hwell
        have hIic : Cardinal.mk {x : α | x ≤ point i hi} < Cardinal.mk α := by
          let p := point i hi
          let f : {x : α | x ≤ p} → Set.Iio p ⊕ PUnit.{u + 1} := fun x =>
            if h : x.1 < p then Sum.inl ⟨x.1, h⟩ else Sum.inr PUnit.unit
          have hinj : Function.Injective f := by
            intro x y hxy
            by_cases hx : x.1 < p
            · by_cases hy : y.1 < p
              · have h' : (Sum.inl ⟨x.1, hx⟩ : Set.Iio p ⊕ PUnit.{u + 1}) =
                    Sum.inl ⟨y.1, hy⟩ := by
                  simpa [f, hx, hy] using hxy
                injection h' with hval
                exact Subtype.ext (congrArg (fun z : Set.Iio p => (z : α)) hval)
              · have h' : (Sum.inl ⟨x.1, hx⟩ : Set.Iio p ⊕ PUnit.{u + 1}) = Sum.inr PUnit.unit := by
                  simpa [f, hx, hy] using hxy
                cases h'
            · by_cases hy : y.1 < p
              · have h' : (Sum.inr PUnit.unit : Set.Iio p ⊕ PUnit.{u + 1}) =
                    Sum.inl ⟨y.1, hy⟩ := by
                  simpa [f, hx, hy] using hxy
                cases h'
              · have hxeq : x.1 = p := (lt_or_eq_of_le (Set.mem_ofPred.mp x.2)).resolve_left hx
                have hyeq : y.1 = p := (lt_or_eq_of_le (Set.mem_ofPred.mp y.2)).resolve_left hy
                exact Subtype.ext (hxeq.trans hyeq.symm)
          have hle : Cardinal.mk {x : α | x ≤ p} ≤ Cardinal.mk (Set.Iio p) + 1 := by
            have hsum : Cardinal.mk (Set.Iio p ⊕ PUnit.{u + 1}) =
                Cardinal.mk (Set.Iio p) + Cardinal.mk PUnit.{u + 1} := by
              simpa [Cardinal.lift_id] using Cardinal.mk_sum (Set.Iio p) PUnit.{u + 1}
            have hone : Cardinal.mk PUnit.{u + 1} = 1 := Cardinal.mk_punit
            exact (Cardinal.mk_le_of_injective hinj).trans (by rw [hsum, hone])
          have hplus : Cardinal.mk (Set.Iio p) + 1 < Cardinal.mk α :=
            addOne_lt_of_infinite (show aleph0 ≤ Cardinal.mk α by rw [hα]; exact hbig.le) hio
          exact hle.trans_lt hplus
        have hseed : Cardinal.mk (seed i hi) < κ :=
          (Cardinal.mk_image_eq e.injective).trans_lt (hIic.trans_eq hα)
        exact (closeOf_card T (seed i hi)).trans_lt
          (max_lt hseed hbig)
      have stage_ne (i : _root_.Ordinal) (hi : i < δ) : (stageSet i hi).Nonempty :=
        ⟨e (point i hi), closeIter_subset_close T (seed i hi) 0
          ⟨point i hi, Set.mem_ofPred.mpr le_rfl, rfl⟩⟩
      have stage_dir (i : _root_.Ordinal) (hi : i < δ) :
          ∀ a ∈ stageSet i hi, ∀ b ∈ stageSet i hi, ∃ c ∈ stageSet i hi, a ≤ c ∧ b ≤ c := by
        intro a ha b hb
        refine ⟨upperBound T a b, closeOf_directed T (seed i hi) ha hb, ?_⟩
        exact upperBound_spec T a b
      let stageSys (i : _root_.Ordinal) (hi : i < δ) : DirectedSystem K.τ :=
        subsystem T (stageSet i hi) (stage_ne i hi) (stage_dir i hi)
      have stageExists (i : _root_.Ordinal) (hi : i < δ) :
          ∃ L : DirectLimit (stageSys i hi), IsLimitInClass K L :=
        IH (Cardinal.mk (Index (stageSys i hi)))
          (by rw [subsystem_card_le]; exact stage_card i hi)
          (stageSys i hi) rfl (fun a => hTmem a.1) (fun hab => hTstrong hab)
      let stageLim (i : _root_.Ordinal) (hi : i < δ) : DirectLimit (stageSys i hi) :=
        Classical.choose (stageExists i hi)
      have stageSpec (i : _root_.Ordinal) (hi : i < δ) : IsLimitInClass K (stageLim i hi) :=
        Classical.choose_spec (stageExists i hi)
      let into {i j : _root_.Ordinal} (hi : i < δ) (hj : j < δ) (hij : i ≤ j)
          (a : Index (stageSys i hi)) : Index (stageSys j hj) :=
        ⟨a.1, stage_mono i j hi hj hij a.2⟩
      have stepExists (i j : _root_.Ordinal) (hi : i < δ) (hj : j < δ) (hij : i < j) :
          ∃ f : Language.Embedding K.τ (stageLim i hi).obj.carrier (stageLim j hj).obj.carrier,
            K.Strong f ∧ ∀ a : Index (stageSys i hi),
              f.comp ((stageLim i hi).canon a) =
                (stageLim j hj).canon (into hi hj hij.le a) := by
        refine (stageSpec i hi).2.2 (stageLim j hj).obj
          (fun a => (stageLim j hj).canon (into hi hj hij.le a))
          (stageSpec j hj).1
          (fun a => (stageSpec j hj).2.1 (into hi hj hij.le a)) ?_
        intro a b hab
        have hab' : (stageSys j hj).rel (into hi hj hij.le a) (into hi hj hij.le b) := by
          dsimp [into, stageSys, subsystem]
          exact hab
        exact (stageLim j hj).compat hab'
      let step (i j : _root_.Ordinal) (hi : i < δ) (hj : j < δ) (hij : i < j) :
          Language.Embedding K.τ (stageLim i hi).obj.carrier (stageLim j hj).obj.carrier :=
        Classical.choose (stepExists i j hi hj hij)
      have step_strong (i j : _root_.Ordinal) (hi : i < δ) (hj : j < δ) (hij : i < j) :
          K.Strong (step i j hi hj hij) :=
        (Classical.choose_spec (stepExists i j hi hj hij)).1
      have step_spec (i j : _root_.Ordinal) (hi : i < δ) (hj : j < δ) (hij : i < j)
          (a : Index (stageSys i hi)) :
          (step i j hi hj hij).comp ((stageLim i hi).canon a) =
            (stageLim j hj).canon (into hi hj hij.le a) :=
        (Classical.choose_spec (stepExists i j hi hj hij)).2 a
      have stage_obj (i : _root_.Ordinal) (hi : i < δ) (a : Index (stageSys i hi)) :
          (stageSys i hi).obj a = T.obj a.1 := rfl
      have into_val {i j : _root_.Ordinal} (hi : i < δ) (hj : j < δ) (hij : i ≤ j)
          (a : Index (stageSys i hi)) : (into hi hj hij a).1 = a.1 := rfl
      have step_comp (i j k : _root_.Ordinal) (hi : i < δ) (hj : j < δ) (hk : k < δ)
          (hij : i < j) (hjk : j < k) :
          (step j k hj hk hjk).comp (step i j hi hj hij) =
            step i k hi hk (hij.trans hjk) := by
        apply limit_ext (stageLim i hi)
        intro a
        ext x
        have h1 := congrFun (congrArg DFunLike.coe (step_spec i j hi hj hij a)) x
        have h2 := congrFun (congrArg DFunLike.coe
          (step_spec j k hj hk hjk (into hi hj hij.le a))) x
        have h3 := congrFun (congrArg DFunLike.coe (step_spec i k hi hk (hij.trans hjk) a)) x
        simp only [Language.Embedding.comp_apply] at h1 h3 ⊢
        have h2' : step j k hj hk hjk ((stageLim j hj).canon (into hi hj hij.le a) x) =
            (stageLim k hk).canon (into hj hk hjk.le (into hi hj hij.le a)) x := h2
        have hidx : into hj hk hjk.le (into hi hj hij.le a) =
            into hi hk (hij.trans hjk).le a := Subtype.ext rfl
        have htr := canon_transport (stageLim k hk) hidx.symm x
        have hmp := eqMp_id (congrArg (fun t => ((stageSys k hk).obj t).carrier) hidx.symm) x
        rw [hmp] at htr
        rw [h1]
        convert h2'.trans (htr.trans h3.symm) using 1
      let C : OrdinalChain K.τ :=
        { δ := δ
          nonzero := hδ
          obj := fun i hi => (stageLim i hi).obj
          map := fun i j hi hj hij => step i j hi hj hij }
      have hCmem : ∀ i hi, K.Mem (C.obj i hi) := fun i hi => (stageSpec i hi).1
      have hCstrong : ∀ i j hi hj hij, K.Strong (C.map i j hi hj hij) :=
        fun i j hi hj hij => step_strong i j hi hj hij
      have hCcomp : OrdinalChain.map_comp_prop K.τ C := by
        intro i j k hi hj hk hij hjk
        simpa [C] using step_comp i j k hi hj hk hij hjk
      obtain ⟨W, hWmem, hWstrong⟩ := K.chain_union C hCcomp hCmem hCstrong
      have to_later (a : Index T) (i k : _root_.Ordinal) (hi : i < δ) (hk : k < δ)
          (hik : i ≤ k) (ha : a ∈ stageSet i hi) (x : (T.obj a).carrier) :
          W.incl i hi ((stageLim i hi).canon ⟨a, ha⟩ x) =
            W.incl k hk ((stageLim k hk).canon (into hi hk hik ⟨a, ha⟩) x) := by
        rcases lt_or_eq_of_le hik with hlt | heq
        · have hW := congrFun (congrArg DFunLike.coe (W.compat i k hi hk hlt))
            ((stageLim i hi).canon ⟨a, ha⟩ x)
          have hS := congrFun (congrArg DFunLike.coe (step_spec i k hi hk hlt ⟨a, ha⟩)) x
          simp only [C, Language.Embedding.comp_apply] at hW
          have hS' : step i k hi hk hlt ((stageLim i hi).canon ⟨a, ha⟩ x) =
              (stageLim k hk).canon (into hi hk hlt.le ⟨a, ha⟩) x := hS
          rw [hS'] at hW
          exact hW.symm
        · subst heq
          have hpr : hi = hk := Subsingleton.elim _ _
          subst hpr
          rfl
      let L := algebraicLimit T
      let cofOf (a : Index T) : ↥cofSet :=
        ⟨Classical.choose (hcof (e.symm a)), (Classical.choose_spec (hcof (e.symm a))).1⟩
      have cofOf_le (a : Index T) : e.symm a ≤ (cofOf a).1 :=
        (Classical.choose_spec (hcof (e.symm a))).2
      let stageOrd (a : Index T) : _root_.Ordinal := (enum.symm (cofOf a)).1
      have stageOrd_lt (a : Index T) : stageOrd a < δ := (enum.symm (cofOf a)).2
      have point_stage (a : Index T) :
          point (stageOrd a) (stageOrd_lt a) = (cofOf a).1 := by
        have hsub : (⟨stageOrd a, stageOrd_lt a⟩ : Set.Iio δ) = enum.symm (cofOf a) := by
          apply Subtype.ext
          rfl
        exact congrArg Subtype.val
          ((congrArg enum hsub).trans (enum.apply_symm_apply (cofOf a)))
      have mem_seed (a : Index T) : a ∈ seed (stageOrd a) (stageOrd_lt a) :=
        ⟨e.symm a, by rw [point_stage a]; exact cofOf_le a, e.apply_symm_apply a⟩
      have mem_stage (a : Index T) : a ∈ stageSet (stageOrd a) (stageOrd_lt a) :=
        closeIter_subset_close T (seed (stageOrd a) (stageOrd_lt a)) 0 (mem_seed a)
      let φ (a : Index T) : Language.Embedding K.τ (T.obj a).carrier W.obj.carrier :=
        (W.incl (stageOrd a) (stageOrd_lt a)).comp
          ((stageLim (stageOrd a) (stageOrd_lt a)).canon ⟨a, mem_stage a⟩)
      have through (a : Index T) (i : _root_.Ordinal) (hi : i < δ) (ha : a ∈ stageSet i hi)
          (x : (T.obj a).carrier) :
          W.incl i hi ((stageLim i hi).canon ⟨a, ha⟩ x) = φ a x := by
        let k := max i (stageOrd a)
        have hk : k < δ := max_lt hi (stageOrd_lt a)
        have h1 := to_later a i k hi hk (le_max_left _ _) ha x
        have h2 := to_later a (stageOrd a) k (stageOrd_lt a) hk (le_max_right _ _)
          (mem_stage a) x
        have hidx : into hi hk (le_max_left i (stageOrd a)) ⟨a, ha⟩ =
            into (stageOrd_lt a) hk (le_max_right i (stageOrd a)) ⟨a, mem_stage a⟩ :=
          Subtype.ext rfl
        simp only [φ, Language.Embedding.comp_apply]
        rw [h1]
        have htr := canon_transport (stageLim k hk) hidx x
        have hmp := eqMp_id (congrArg (fun t => ((stageSys k hk).obj t).carrier) hidx) x
        rw [hmp] at htr
        rw [← congrArg (W.incl k hk) htr]
        exact h2.symm
      have φcompat {a b : Index T} (hab : a ≤ b) : (φ b).comp (T.map hab) = φ a := by
        ext x
        let k := max (stageOrd a) (stageOrd b)
        have hk : k < δ := max_lt (stageOrd_lt a) (stageOrd_lt b)
        have hφa := through a (stageOrd a) (stageOrd_lt a) (mem_stage a) x
        have hφb := through b (stageOrd b) (stageOrd_lt b) (mem_stage b) (T.map hab x)
        have hlater_a := to_later a (stageOrd a) k (stageOrd_lt a) hk (le_max_left _ _)
          (mem_stage a) x
        have hlater_b := to_later b (stageOrd b) k (stageOrd_lt b) hk (le_max_right _ _)
          (mem_stage b) (T.map hab x)
        have habk : (stageSys k hk).rel
            (into (stageOrd_lt a) hk (le_max_left _ _) ⟨a, mem_stage a⟩)
            (into (stageOrd_lt b) hk (le_max_right _ _) ⟨b, mem_stage b⟩) := by
          dsimp [into, stageSys, subsystem]
          exact hab
        have hcan := congrFun (congrArg DFunLike.coe ((stageLim k hk).compat habk)) x
        have hcan' : (stageLim k hk).canon
              (into (stageOrd_lt b) hk (le_max_right _ _) ⟨b, mem_stage b⟩) (T.map hab x) =
            (stageLim k hk).canon
              (into (stageOrd_lt a) hk (le_max_left _ _) ⟨a, mem_stage a⟩) x := hcan
        simp only [φ, Language.Embedding.comp_apply] at hφa hφb ⊢
        rw [← hφb, hlater_b, hcan', ← hlater_a, hφa]
      let Hg : ∀ (i j : Index T) (hij : i ≤ j) (x : (T.obj i).carrier),
          φ j (T.map hij x) = φ i x :=
        fun i j hij x => congrFun (congrArg DFunLike.coe (φcompat hij)) x
      let induced := Language.DirectLimit.lift K.τ (Index T)
        (fun i : Index T => (T.obj i).carrier) (fun i j (h : i ≤ j) => T.map h) φ Hg
      have hlift (i : Index T) (x : (T.obj i).carrier) :
          induced (L.canon i x) = φ i x := by
        simp only [induced, L, algebraicLimit]
        exact Language.DirectLimit.lift_of (L := K.τ) (ι := Index T)
          (G := fun i : Index T => (T.obj i).carrier)
          (f := fun i j (h : i ≤ j) => T.map h) φ Hg (i := i) x
      have hsurj : Function.Surjective induced := by
        intro z
        obtain ⟨i, hi, y, hy⟩ := W.covers z
        obtain ⟨a, x, hx⟩ := (stageLim i hi).joint y
        refine ⟨L.canon a.1 x, ?_⟩
        have happ := hlift a.1 x
        have hthrough := through a.1 i hi a.2 x
        have hcan : (stageLim i hi).canon ⟨a.1, a.2⟩ x = (stageLim i hi).canon a x := by
          let f := fun t : Index (stageSys i hi) => ((stageSys i hi).obj t).carrier
          have hfun (b : Index (stageSys i hi)) (hb : a = b) :
              (stageLim i hi).canon b (Eq.mp (congrArg f hb) x) =
              (stageLim i hi).canon a x := by
            subst hb
            rfl
          have hb : a = ⟨a.1, a.2⟩ := (Subtype.ext rfl).symm
          have htr := hfun ⟨a.1, a.2⟩ hb
          have hmp : Eq.mp (congrArg f hb) x = x := eqMp_id (congrArg f hb) x
          rw [hmp] at htr
          exact htr
        simp only [φ, Language.Embedding.comp_apply] at hthrough
        rw [happ, ← hthrough, hcan, hx, hy]
      let eLim : L.obj.carrier ≃[K.τ] W.obj.carrier := embeddingEquivOfSurjective induced hsurj
      have hmemL : K.Mem L.obj := K.iso_closed ⟨eLim.symm⟩ hWmem
      have hsym : K.Strong eLim.symm.toEmbedding := strong_of_equiv K eLim.symm hWmem
      have hφstrong (a : Index T) : K.Strong (φ a) :=
        K.strong_trans
          ((stageLim (stageOrd a) (stageOrd_lt a)).canon ⟨a, mem_stage a⟩)
          (W.incl (stageOrd a) (stageOrd_lt a))
          ((stageSpec (stageOrd a) (stageOrd_lt a)).2.1 ⟨a, mem_stage a⟩)
          (hWstrong (stageOrd a) (stageOrd_lt a))
      have hfac (a : Index T) : L.canon a = eLim.symm.toEmbedding.comp (φ a) := by
        ext x
        simp only [Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding]
        have happ := hlift a x
        have hcoe : eLim (L.canon a x) = induced (L.canon a x) := rfl
        rw [← happ, ← hcoe]
        exact (eLim.left_inv (L.canon a x)).symm
      have hcan (a : Index T) : K.Strong (L.canon a) := by
        rw [hfac a]
        exact K.strong_trans (φ a) eLim.symm.toEmbedding (hφstrong a) hsym
      refine ⟨L, hmemL, hcan, ?_⟩
      intro N g hN hg hgcompat
      have psiExists (i : _root_.Ordinal) (hi : i < δ) :
          ∃ ψ : Language.Embedding K.τ (stageLim i hi).obj.carrier N.carrier,
            K.Strong ψ ∧ ∀ a : Index (stageSys i hi),
              ψ.comp ((stageLim i hi).canon a) = g a.1 :=
        (stageSpec i hi).2.2 N (fun a => g a.1) hN (fun a => hg a.1)
          (fun hab => hgcompat hab)
      let psi (i : _root_.Ordinal) (hi : i < δ) := Classical.choose (psiExists i hi)
      have psi_strong (i : _root_.Ordinal) (hi : i < δ) : K.Strong (psi i hi) :=
        (Classical.choose_spec (psiExists i hi)).1
      have psi_spec (i : _root_.Ordinal) (hi : i < δ) (a : Index (stageSys i hi)) :
          (psi i hi).comp ((stageLim i hi).canon a) = g a.1 :=
        (Classical.choose_spec (psiExists i hi)).2 a
      have psi_comp (i j : _root_.Ordinal) (hi : i < δ) (hj : j < δ) (hij : i < j) :
          (psi j hj).comp (C.map i j hi hj hij) = psi i hi := by
        apply limit_ext (stageLim i hi)
        intro a
        ext x
        have hstep := congrFun (congrArg DFunLike.coe (step_spec i j hi hj hij a)) x
        have hψj := congrFun (congrArg DFunLike.coe (psi_spec j hj (into hi hj hij.le a))) x
        have hψi := congrFun (congrArg DFunLike.coe (psi_spec i hi a)) x
        have hstep' : step i j hi hj hij ((stageLim i hi).canon a x) =
            (stageLim j hj).canon (into hi hj hij.le a) x := hstep
        have hψj' : psi j hj ((stageLim j hj).canon (into hi hj hij.le a) x) = g a.1 x := hψj
        have hψi' : psi i hi ((stageLim i hi).canon a x) = g a.1 x := hψi
        simp only [C, Language.Embedding.comp_apply]
        rw [hstep', hψj', ← hψi']
      obtain ⟨fW, hfW, hfWincl⟩ := K.chain_upper C W N psi hCcomp hCmem hCstrong hWstrong
        hN psi_strong psi_comp
      refine ⟨fW.comp eLim.toEmbedding, ?_, ?_⟩
      · exact K.strong_trans eLim.toEmbedding fW (strong_of_equiv K eLim hmemL) hfW
      · intro a
        ext x
        have hlim : eLim (L.canon a x) = φ a x := by
          simp only [eLim, Language.Equiv.coe_toEmbedding]
          exact hlift a x
        have hthrough : φ a x =
            W.incl (stageOrd a) (stageOrd_lt a)
              ((stageLim (stageOrd a) (stageOrd_lt a)).canon ⟨a, mem_stage a⟩ x) := by
          dsimp [φ]
          rfl
        have hincl := congrFun (congrArg DFunLike.coe
          (hfWincl (stageOrd a) (stageOrd_lt a)))
          ((stageLim (stageOrd a) (stageOrd_lt a)).canon ⟨a, mem_stage a⟩ x)
        have hpsi := congrFun (congrArg DFunLike.coe
          (psi_spec (stageOrd a) (stageOrd_lt a) ⟨a, mem_stage a⟩)) x
        have hpsi' : psi (stageOrd a) (stageOrd_lt a)
            ((stageLim (stageOrd a) (stageOrd_lt a)).canon ⟨a, mem_stage a⟩ x) = g a x := hpsi
        simp only [Language.Embedding.comp_apply, Language.Equiv.coe_toEmbedding] at hincl ⊢
        rw [hlim, hthrough, hincl, hpsi']

/-- Any direct limit of a directed system is isomorphic to the algebraic direct limit. -/
noncomputable def directLimitEquivAlgebraic {τ : Tau.{u}} (S : DirectedSystem τ)
    (U : DirectLimit S) : (algebraicLimit S).obj.carrier ≃[τ] U.obj.carrier := by
  have Hg : ∀ i j (hij : S.rel i j) (x : (S.obj i).carrier),
      U.canon j (S.map hij x) = U.canon i x :=
    fun i j hij x => congrFun (congrArg DFunLike.coe (U.compat hij)) x
  let induced := Language.DirectLimit.lift τ (Index S)
    (fun i : Index S => (S.obj i).carrier) (fun i j (h : i ≤ j) => S.map h) U.canon Hg
  have hsurj : Function.Surjective induced := by
    intro z
    obtain ⟨i, y, rfl⟩ := U.joint z
    refine ⟨(algebraicLimit S).canon i y, ?_⟩
    exact Language.DirectLimit.lift_of (L := τ) (ι := Index S)
      (G := fun i : Index S => (S.obj i).carrier)
      (f := fun i j (h : i ≤ j) => S.map h) U.canon Hg (i := i) y
  exact embeddingEquivOfSurjective induced hsurj

lemma directLimitHg {τ : Tau.{u}} (S : DirectedSystem τ) (U : DirectLimit S)
    (i j : S.ι) (hij : S.rel i j) (x : (S.obj i).carrier) :
    U.canon j (S.map hij x) = U.canon i x :=
  congrFun (congrArg DFunLike.coe (U.compat hij)) x

theorem directLimitEquivAlgebraic_canon {τ : Tau.{u}} (S : DirectedSystem τ)
    (U : DirectLimit S) (i : S.ι) (x : (S.obj i).carrier) :
    directLimitEquivAlgebraic S U ((algebraicLimit S).canon i x) = U.canon i x := by
  dsimp [directLimitEquivAlgebraic, embeddingEquivOfSurjective]
  exact Language.DirectLimit.lift_of (L := τ) (ι := Index S)
    (G := fun i : Index S => (S.obj i).carrier)
    (f := fun i j (h : i ≤ j) => S.map h) U.canon (directLimitHg S U) (i := i) x

/-- Any direct limit of models in `K` with strong maps belongs to `K`. -/
theorem directLimit_mem (K : AbstractElementaryClass.{u}) (S : DirectedSystem K.τ)
    (hmem : ∀ i, K.Mem (S.obj i))
    (hstrong : ∀ {i j} (hij : S.rel i j), K.Strong (S.map hij))
    (U : DirectLimit S) : K.Mem U.obj := by
  obtain ⟨L, hL⟩ := directLimit_in_class K S hmem (fun {_ _} hij => hstrong hij)
  have eL : (algebraicLimit S).obj.carrier ≃[K.τ] L.obj.carrier :=
    directLimitEquivAlgebraic S L
  have eU : (algebraicLimit S).obj.carrier ≃[K.τ] U.obj.carrier :=
    directLimitEquivAlgebraic S U
  have hiso : Nonempty (L.obj.carrier ≃[K.τ] U.obj.carrier) :=
    ⟨eU.comp eL.symm⟩
  exact K.iso_closed hiso hL.1

end
end AEC
