module

public import AEC.Section5.EmptiedScheme
public import AEC.Section8.MarkedPair
public import AEC.Section5.Results
public import AEC.Section5.TermTemplate
public import AEC.Section6.Results

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- The shape of the marked increment `C^b`: two copies of `S` (the base `X` and the extension
`Y` of a marked pair), with the specified maps of each copy and the inclusion `X_v → Y_v`. -/
def SystemShape.doubled (S : SystemShape.{u}) : SystemShape.{u} where
  Vertex := S.Vertex ⊕ S.Vertex
  vertexFinite := by have := S.vertexFinite; infer_instance
  specified
    | Sum.inl i, Sum.inl j => S.specified i j
    | Sum.inr i, Sum.inr j => S.specified i j
    | Sum.inl i, Sum.inr j => i = j
    | Sum.inr _, Sum.inl _ => False

/-- **Standing convention of Section 8 (cycle 95).** English: "Throughout this Section, C is a
working scheme whose arrows are precisely the componentwise strong embeddings preserving its
specified maps and distinguished data. In particular, there is no additional condition on
intersections or on bases." (`SystemArrow` already preserves the specified maps.) A hypothesis,
not a `WorkingScheme` field. -/
def Section8Arrows {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) : Prop :=
  ∀ {μ ν : Cardinal.{u}} {hμ : μ ∈ W.eligible} {hν : ν ∈ W.eligible}
    (X : W.Object μ hμ) (Y : W.Object ν hν)
    (f : SystemArrow K S (W.asSystem hμ X) (W.asSystem hν Y)),
    W.permitted (X := X) (Y := Y) f ↔ ∀ v, K.Strong (f.onVertex v)

/-- The joint tuple `(t, b)` of a bounded tuple `t` of `N.Y` with the mark, viewed over `M.X`
along `e : M.X → N.X` (the mark indexed through `σ : M.bIdx ≃ N.bIdx`). -/
def markedJointOver {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    {W : WorkingScheme K S} {P : StationaryPrescription K S W} (M N : MarkedPair K S W P)
    (e : SystemArrow K S (W.asSystem M.hμ M.X) (W.asSystem N.hμ N.X))
    (he : W.permitted (X := M.X) (Y := N.X) e) (σ : M.bIdx ≃ N.bIdx) {ι : Type u}
    (t : ι → Occurrence K S (W.asSystem N.hμ N.Y)) : TupleOver K S W M.hμ M.X :=
  ⟨N.μ, N.hμ, N.Y, SystemArrow.comp e N.incl, W.comp e N.incl he N.incl_arrow, ι ⊕ M.bIdx,
    Sum.elim t (fun j => N.b (σ j))⟩

/-- Bounded pair tuples `t` of `M` and `t′` of `N` are in the same pair orbit (comparison of
pair tuples): some isomorphism of marked pairs (vertexwise bijective marked arrow) takes `t` to
`t′`. -/
def PairOrbitEq {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    {W : WorkingScheme K S} {P : StationaryPrescription K S W} (M N : MarkedPair K S W P)
    {ι : Type u} (t : ι → Occurrence K S (W.asSystem M.hμ M.Y))
    (t' : ι → Occurrence K S (W.asSystem N.hμ N.Y)) : Prop :=
  ∃ arr : MarkedArrow K S W P M N, (∀ v, Function.Bijective (arr.onX.onVertex v)) ∧
    (∀ v, Function.Bijective (arr.onY.onVertex v)) ∧ ∀ i, arr.onY.mapOcc (t i) = t' i

/-- **Lemma 8.2** (The pair isomorphism test; restated cycle 95 to the English). English:
"After a further closure refinement, marked pairs exist over every object X. An isomorphism
e : X ≅ X′ extends to an isomorphism (X, Y, b) ≅ (X′, Y′, b′). More precisely, for bounded tuples
t and t′ in the respective pair structures, such an extension can take t to t′ if and only if e
takes the indicated base entries to their counterparts and transports tp(t, b/X) to
tp(t′, b′/X′)." Hypotheses are the Section 8 conventions: the working package (Definition 5.2,
`IsWorkingPackage`) and arrows = componentwise strong embeddings (`Section8Arrows`); an
isomorphism is a vertexwise bijective arrow. Further English clauses, also stated: "Same-level arrows preserve bounded
pair orbits. Moreover, comparisons of bounded pair tuples are preserved and reflected when two
pairs at one common small level are mapped to two pairs at a common larger eligible level. All
tuple lengths and the bounds needed for the comparison are strictly below the smaller level."
(clauses 4 and 5, via `PairOrbitEq`). The English also uses "the calculus and isolation results of the
preceding two Sections", which Lean has only for `SingleModelData`; tracked on `lemma_8_2`. -/
theorem lemma_8_2 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (P : StationaryPrescription K S W)
    (_hpack : IsWorkingPackage W) (_harr : Section8Arrows W) :
    ∃ T, ∃ hT : Tail W.eligible T,
      -- marked pairs exist over every object
      (∀ μ (hμ : μ ∈ T) (X : W.Object μ (Tail.mem hT hμ)),
        ∃ M : MarkedPair K S W P, M.μ = μ ∧
          ∃ e : SystemArrow K S (W.asSystem _ X) (W.asSystem _ M.X),
            W.permitted (X := X) (Y := M.X) e ∧ ∀ v, Function.Bijective (e.onVertex v)) ∧
      -- an isomorphism of bases extends to an isomorphism of the pairs
      (∀ (M N : MarkedPair K S W P)
        (e : SystemArrow K S (W.asSystem M.hμ M.X) (W.asSystem N.hμ N.X)),
        M.μ ∈ T → N.μ ∈ T →
        (∀ v, Function.Bijective (e.onVertex v)) →
        W.permitted (X := M.X) (Y := N.X) e →
        ∃ arr : MarkedArrow K S W P M N, arr.onX = e ∧
          ∀ v, Function.Bijective (arr.onY.onVertex v)) ∧
      -- pointed form: the extension can take `t` to `t′` iff `e` matches the base entries and
      -- transports `tp(t, b/X)` to `tp(t′, b′/X′)`
      (∀ (M N : MarkedPair K S W P)
        (e : SystemArrow K S (W.asSystem M.hμ M.X) (W.asSystem N.hμ N.X)),
        M.μ ∈ T → N.μ ∈ T →
        (∀ v, Function.Bijective (e.onVertex v)) →
        ∀ (he : W.permitted (X := M.X) (Y := N.X) e)
          {ι : Type u} (t : ι → Occurrence K S (W.asSystem M.hμ M.Y))
          (t' : ι → Occurrence K S (W.asSystem N.hμ N.Y)), #ι < M.μ →
          ((∃ arr : MarkedArrow K S W P M N, arr.onX = e ∧
              (∀ v, Function.Bijective (arr.onY.onVertex v)) ∧
              ∀ i, arr.onY.mapOcc (t i) = t' i) ↔
            ((∀ i (x : Occurrence K S (W.asSystem M.hμ M.X)), t i = M.incl.mapOcc x →
                t' i = N.incl.mapOcc (e.mapOcc x)) ∧
              ∃ σ : M.bIdx ≃ N.bIdx,
                SameGaloisType (asTuple M.incl M.incl_arrow (Sum.elim t M.b))
                  (markedJointOver M N e he σ t') (Equiv.refl _) (Equiv.refl _)))) ∧
      -- same-level arrows preserve bounded pair orbits
      (∀ (M N : MarkedPair K S W P) (f : MarkedArrow K S W P M N), M.μ ∈ T → M.μ = N.μ →
        ∀ {ι : Type u} (t₁ t₂ : ι → Occurrence K S (W.asSystem M.hμ M.Y)), #ι < M.μ →
          (PairOrbitEq M M t₁ t₂ →
            PairOrbitEq N N (fun i => f.onY.mapOcc (t₁ i)) (fun i => f.onY.mapOcc (t₂ i)))) ∧
      -- comparisons preserved and reflected from a common small level to a common larger level
      (∀ (M₁ M₂ N₁ N₂ : MarkedPair K S W P) (f₁ : MarkedArrow K S W P M₁ N₁)
          (f₂ : MarkedArrow K S W P M₂ N₂),
        M₁.μ ∈ T → M₁.μ = M₂.μ → N₁.μ ∈ T → N₁.μ = N₂.μ → M₁.μ < N₁.μ →
        ∀ {ι : Type u} (t₁ : ι → Occurrence K S (W.asSystem M₁.hμ M₁.Y))
          (t₂ : ι → Occurrence K S (W.asSystem M₂.hμ M₂.Y)), #ι < M₁.μ →
          (PairOrbitEq M₁ M₂ t₁ t₂ ↔
            PairOrbitEq N₁ N₂ (fun i => f₁.onY.mapOcc (t₁ i)) (fun i => f₂.onY.mapOcc (t₂ i)))) := by
  sorry

/-- **Lemma 8.3** (The marked-pair template; restated cycle 95 to the English). English:
"There is a fixed set-sized finitary term template F^b such that, on a further class of
sufficiently closed eligible levels, its values on well-orders are objects of C^b. Order
embeddings give the componentwise arrows of Definition 8.1, also between such levels. Every
marked pair at a level is isomorphic to a value of this template of that size." `F^b` lives on
the doubled shape (base copy `inl`, extension copy `inr`); its value on a well-order `I` of a
tail size is presented by a marked pair `val I` of level `#I`; order embeddings give marked
arrows (also between levels); and every marked pair at a tail level is isomorphic (vertexwise
bijective marked arrow) to the value of that size. Hypotheses: the Section 8 conventions. -/
theorem lemma_8_3 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (P : StationaryPrescription K S W)
    (_hpack : IsWorkingPackage W) (_harr : Section8Arrows W) :
    ∃ F : TermTemplate K S.doubled, ∃ T, ∃ _hT : Tail W.eligible T,
      ∃ val : (I : Type u) → [LinearOrder I] → [WellFoundedLT I] → [Nonempty I] →
          #I ∈ T → MarkedPair K S W P,
        (∀ (I : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I] (hI : #I ∈ T),
          (val I hI).μ = #I ∧
          ∀ v, Nonempty (((F.present I).obj (Sum.inl v)).carrier ≃[K.τ]
                ((W.asSystem (val I hI).hμ (val I hI).X).obj v).carrier) ∧
              Nonempty (((F.present I).obj (Sum.inr v)).carrier ≃[K.τ]
                ((W.asSystem (val I hI).hμ (val I hI).Y).obj v).carrier)) ∧
        (∀ (I J : Type u) [LinearOrder I] [WellFoundedLT I] [Nonempty I]
            [LinearOrder J] [WellFoundedLT J] [Nonempty J] (_f : I ↪o J)
            (hI : #I ∈ T) (hJ : #J ∈ T),
          Nonempty (MarkedArrow K S W P (val I hI) (val J hJ))) ∧
        (∀ M : MarkedPair K S W P, M.μ ∈ T →
          ∃ (I : Type u) (_ : LinearOrder I) (_ : WellFoundedLT I) (_ : Nonempty I)
            (hI : #I ∈ T), #I = M.μ ∧
            ∃ arr : MarkedArrow K S W P M (val I hI),
              (∀ v, Function.Bijective (arr.onX.onVertex v)) ∧
              ∀ v, Function.Bijective (arr.onY.onVertex v)) := by
  sorry

/-- **Lemma 8.4** (Testing beside an isolated small upper object; restated cycle 95 to the
English). English: "Let ν < µ be sufficiently closed levels where Lemma 8.3 holds. Suppose
A ≤ U, A ≤ C, C ≤ T, T′ are underlying arrows, A, U are at level ν, and C, T, T′ are at level µ.
Suppose (A, U, b) is a small marked pair inside T, its specified image (A, U′, b′) is inside T′,
and the map U ≅ U′ fixes A. Suppose further that b/C and b′/C are the prescribed free extensions
and corresponding bounded tuples of U, U′, jointly with the marks, have equal types over C. For
each σ < ν there is a bound k(σ) < ν, uniform in these objects, with the following property. If
v ∈ T and v′ ∈ T′ have length at most σ, their comparisons on joint tests from U and C of total
size at most k(σ) determine their comparisons on all such tests of total size < ν. Tests in U′
are read by the specified map."

Encoding: the small pair is `M` (`A = M.X`, `U = M.Y`, level `ν = M.μ`); its image is `M'` with
a vertexwise bijective marked arrow `iso : M → M'` that fixes `A` over `C` (`iso.onX ≫ aC' = aC`);
`b/C` is the prescribed type (`P.assign C`) read in `T` and in `T′`; tests are pairs `(ZU, ZC)`
read in `T` by `uT`, `cT` and in `T′` by `iso.onY ≫ uT'`, `cT'`. `k` is chosen before the
objects (uniformity). Hypotheses: the Section 8 conventions. -/
theorem lemma_8_4 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (P : StationaryPrescription K S W)
    (_hpack : IsWorkingPackage W) (_harr : Section8Arrows W) :
    ∃ T, ∃ hT : Tail W.eligible T, ∃ k : Cardinal.{u} → Cardinal.{u} → Cardinal.{u},
      ∀ ν, ν ∈ T → ∀ σ, σ < ν → k ν σ < ν ∧
        ∀ μ (hμ : μ ∈ T), ν < μ →
        ∀ (M M' : MarkedPair K S W P), M.μ = ν → M'.μ = ν →
        ∀ (iso : MarkedArrow K S W P M M'),
          (∀ v, Function.Bijective (iso.onX.onVertex v)) →
          (∀ v, Function.Bijective (iso.onY.onVertex v)) →
        ∀ (C Tt Tt' : W.Object μ (Tail.mem hT hμ))
          (aC : SystemArrow K S (W.asSystem M.hμ M.X) (W.asSystem _ C))
          (aC' : SystemArrow K S (W.asSystem M'.hμ M'.X) (W.asSystem _ C))
          (cT : SystemArrow K S (W.asSystem _ C) (W.asSystem _ Tt))
          (cT' : SystemArrow K S (W.asSystem _ C) (W.asSystem _ Tt'))
          (uT : SystemArrow K S (W.asSystem M.hμ M.Y) (W.asSystem _ Tt))
          (uT' : SystemArrow K S (W.asSystem M'.hμ M'.Y) (W.asSystem _ Tt')),
          W.permitted (X := M.X) (Y := C) aC → W.permitted (X := M'.X) (Y := C) aC' →
          ∀ (hcT : W.permitted (X := C) (Y := Tt) cT) (hcT' : W.permitted (X := C) (Y := Tt') cT'),
          W.permitted (X := M.Y) (Y := Tt) uT → W.permitted (X := M'.Y) (Y := Tt') uT' →
          SystemArrow.comp iso.onX aC' = aC →
          SystemArrow.comp M.incl uT = SystemArrow.comp aC cT →
          SystemArrow.comp M'.incl uT' = SystemArrow.comp aC' cT' →
          -- `b/C` and `b′/C` are the prescribed free extensions
          (∃ e, SameGaloisType
            (⟨μ, Tail.mem hT hμ, Tt, cT, hcT, M.bIdx, fun j => uT.mapOcc (M.b j)⟩ :
              TupleOver K S W (Tail.mem hT hμ) C)
            (P.assign (Tail.mem hT hμ) C) e (Equiv.refl _)) →
          (∃ e, SameGaloisType
            (⟨μ, Tail.mem hT hμ, Tt', cT', hcT', M.bIdx,
              fun j => uT'.mapOcc (iso.onY.mapOcc (M.b j))⟩ : TupleOver K S W (Tail.mem hT hμ) C)
            (P.assign (Tail.mem hT hμ) C) e (Equiv.refl _)) →
          -- corresponding bounded tuples of `U`, `U′`, with the marks, have equal types over `C`
          (∀ {ι : Type u} (t : ι → Occurrence K S (W.asSystem M.hμ M.Y)), #ι < ν →
            SameGaloisType
              (⟨μ, Tail.mem hT hμ, Tt, cT, hcT, ι ⊕ M.bIdx,
                Sum.elim (fun i => uT.mapOcc (t i)) (fun j => uT.mapOcc (M.b j))⟩ :
                TupleOver K S W (Tail.mem hT hμ) C)
              (⟨μ, Tail.mem hT hμ, Tt', cT', hcT', ι ⊕ M.bIdx,
                Sum.elim (fun i => uT'.mapOcc (iso.onY.mapOcc (t i)))
                  (fun j => uT'.mapOcc (iso.onY.mapOcc (M.b j)))⟩ :
                TupleOver K S W (Tail.mem hT hμ) C)
              (Equiv.refl _) (Equiv.refl _)) →
          ∀ {α : Type u} (v : α → Occurrence K S (W.asSystem _ Tt))
            (v' : α → Occurrence K S (W.asSystem _ Tt')), #α ≤ σ →
            (∀ {ιU ιC : Type u} (ZU : ιU → Occurrence K S (W.asSystem M.hμ M.Y))
                (ZC : ιC → Occurrence K S (W.asSystem _ C)), #ιU + #ιC ≤ k ν σ →
              W.DiagramEq (X := Tt) (Y := Tt')
                (Sum.elim v (Sum.elim (fun i => uT.mapOcc (ZU i)) (fun i => cT.mapOcc (ZC i))))
                (Sum.elim v' (Sum.elim (fun i => uT'.mapOcc (iso.onY.mapOcc (ZU i)))
                  (fun i => cT'.mapOcc (ZC i))))) →
            ∀ {ιU ιC : Type u} (ZU : ιU → Occurrence K S (W.asSystem M.hμ M.Y))
                (ZC : ιC → Occurrence K S (W.asSystem _ C)), #ιU + #ιC < ν →
              W.DiagramEq (X := Tt) (Y := Tt')
                (Sum.elim v (Sum.elim (fun i => uT.mapOcc (ZU i)) (fun i => cT.mapOcc (ZC i))))
                (Sum.elim v' (Sum.elim (fun i => uT'.mapOcc (iso.onY.mapOcc (ZU i)))
                  (fun i => cT'.mapOcc (ZC i)))) := by
  sorry

/-- **Lemma 8.5** (Chain closure; restated cycle 95 to the English). English: "At further
sufficiently closed levels, C^b has unions of increasing chains of total size equal to the level.
The union is a marked pair. The common-upper-bound clause holds as well, including into an
eligible larger level." Mirrors Definition 5.2(1) (`HasChainUnions`) for marked pairs and marked
arrows: the chain arrows compose on both components, the union `U` is a marked pair at the level
with a cocone of marked arrows, and every cocone of marked arrows into a marked pair at an equal
or larger level of the tail factors through `U`. Hypotheses: the Section 8 conventions. -/
theorem lemma_8_5 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (P : StationaryPrescription K S W)
    (_hpack : IsWorkingPackage W) (_harr : Section8Arrows W) :
    ∃ T, ∃ _hT : Tail W.eligible T,
      ∀ μ, μ ∈ T → ∀ (index : Type u) [LinearOrder index] [Nonempty index]
        (M : index → MarkedPair K S W P),
        (∀ i, (M i).μ = μ) →
        ∀ (le : ∀ i j, i ≤ j → MarkedArrow K S W P (M i) (M j)),
        (∀ i j k (hij : i ≤ j) (hjk : j ≤ k),
          SystemArrow.comp (le i j hij).onX (le j k hjk).onX = (le i k (hij.trans hjk)).onX ∧
          SystemArrow.comp (le i j hij).onY (le j k hjk).onY = (le i k (hij.trans hjk)).onY) →
        #index ≤ μ →
        ∃ U : MarkedPair K S W P, U.μ = μ ∧
          ∃ incl : ∀ i, MarkedArrow K S W P (M i) U,
            (∀ i j (hij : i ≤ j),
              SystemArrow.comp (le i j hij).onX (incl j).onX = (incl i).onX ∧
              SystemArrow.comp (le i j hij).onY (incl j).onY = (incl i).onY) ∧
            ∀ (Z : MarkedPair K S W P), Z.μ ∈ T → μ ≤ Z.μ →
              ∀ (toZ : ∀ i, MarkedArrow K S W P (M i) Z),
              (∀ i j (hij : i ≤ j),
                SystemArrow.comp (le i j hij).onX (toZ j).onX = (toZ i).onX ∧
                SystemArrow.comp (le i j hij).onY (toZ j).onY = (toZ i).onY) →
              ∃ toU : MarkedArrow K S W P U Z, ∀ i,
                SystemArrow.comp (incl i).onX toU.onX = (toZ i).onX ∧
                SystemArrow.comp (incl i).onY toU.onY = (toZ i).onY := by
  sorry

/-- **Theorem 8.6** (The marked-increment working package). Let `C` be a working scheme with
componentwise arrows and a stationary finite prescription. Assume the eligible-subclass
hypothesis. On an unbounded further class of sufficiently closed eligible levels, `C^b` is again
a working scheme, with componentwise arrows, fixed template and mixed arrows between these levels;
the output class retains the eligible-subclass hypothesis.

**Statement (restated, honest form, open):** the input `W` is a working package with objects at
every eligible level; the output `W'` lives on the doubled shape (`SystemShape.doubled`), is a
working package on an eligible subclass of `R`, has objects at every eligible level, every object
is (vertexwise isomorphic to) a marked pair `(X, Y, b)` of Definition 8.1 at its level, and every
marked pair at an eligible level of `W'` is isomorphic to an object. The former statement had
no nonemptiness and was proved by the object-free `WorkingScheme.emptied` (degenerate). The
correspondence of permitted arrows with `MarkedArrow`s is not yet stated. -/
theorem theorem_8_6 {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) (hW : IsWorkingPackage W)
    (hne : ∀ μ (hμ : μ ∈ W.eligible), Nonempty (W.Object μ hμ))
    (P : StationaryPrescription K S W)
    (R : Set Cardinal.{u}) (hR : EligibleSubclass W.eligible R) :
    ∃ W' : WorkingScheme K S.doubled,
      IsWorkingPackage W' ∧ EligibleSubclass R W'.eligible ∧
      (∀ μ (hμ : μ ∈ W'.eligible), Nonempty (W'.Object μ hμ)) ∧
      (∀ μ (hμ : μ ∈ W'.eligible) (X' : W'.Object μ hμ),
        ∃ M : MarkedPair K S W P, M.μ = μ ∧
          (∀ v, Nonempty (((W'.asSystem hμ X').obj (Sum.inl v)).carrier ≃[K.τ]
            ((W.asSystem M.hμ M.X).obj v).carrier)) ∧
          (∀ v, Nonempty (((W'.asSystem hμ X').obj (Sum.inr v)).carrier ≃[K.τ]
            ((W.asSystem M.hμ M.Y).obj v).carrier))) ∧
      (∀ M : MarkedPair K S W P, ∀ hμ' : M.μ ∈ W'.eligible,
        ∃ X' : W'.Object M.μ hμ',
          (∀ v, Nonempty (((W'.asSystem hμ' X').obj (Sum.inl v)).carrier ≃[K.τ]
            ((W.asSystem M.hμ M.X).obj v).carrier)) ∧
          (∀ v, Nonempty (((W'.asSystem hμ' X').obj (Sum.inr v)).carrier ≃[K.τ]
            ((W.asSystem M.hμ M.Y).obj v).carrier))) := by
  sorry

end
end AEC
