module

public import AEC.Section11.GeometricSystem
public import AEC.Section11.LargestActiveLabel
public import AEC.Section11.JointFreshness
public import AEC.Section5.Results
public import AEC.Section6.Results

@[expose] public section

namespace AEC
section

universe u

set_option linter.unusedVariables false

open FirstOrder Cardinal

/-- **Lemma 11.2** (Combinatorics of shapes). An admissible family contains `∅`, is closed
under unions, and every set of axes has a largest active subset. In a geometric system an
inactive vertex equals the vertex of that largest active subset. -/
theorem lemma_11_2 {n : ℕ} {L : Set (Finset (Fin n))} (hL : Admissible n L) :
    (∃ e : Finset (Fin n), e ∈ L ∧ e = ∅) ∧
    (∀ s t, s ∈ L → t ∈ L → s ∪ t ∈ L) ∧
    (∀ t : Finset (Fin n), ∃ u, IsLargestActive L t u) ∧
    ∀ (K : AbstractElementaryClass.{u}) (X : GeometricSystem K n L) (t : Finset (Fin n))
      (u : Finset (Fin n)),
      IsLargestActive L t u → ¬ t ∈ L →
      ∃ h : u ⊆ t, Function.Bijective (X.le h) := by
  refine ⟨⟨∅, hL.empty_mem, rfl⟩, fun s t hs ht => hL.union_mem hs ht, hL.exists_largest, ?_⟩
  intro K X t u hu ht
  sorry

/-- **Lemma 11.4** (Replacement and extension of relative bases). Any choice of bases of the
active pieces over the relative spans is a witnessing partition, and an arrow extends a
witnessing partition of its domain to one of its codomain. -/
theorem lemma_11_4 (K : AbstractElementaryClass.{u}) {n : ℕ} {L : Set (Finset (Fin n))}
    (X Y : GeometricSystem K n L) (f : GeometricArrow K X Y) :
    (∀ s (hs : s ∈ L), f.onVertex s '' X.piece s hs ⊆ Y.piece s hs) ∧
    ∀ t, f.onVertex t '' RelativeSpan K X t ⊆ RelativeSpan K Y t := by
  refine ⟨f.extends_piece, ?_⟩
  intro t y hy
  obtain ⟨x, hx, rfl⟩ := hy
  -- Pieces extend, so lower piece-spans map into the corresponding lower spans of `Y`.
  have lower_image : ∀ u, f.onVertex u '' X.lower u ⊆ Y.lower u := by
    intro u z hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨s, hs, hsu, v, hv, rfl⟩ := hw
    refine ⟨s, hs, hsu, f.onVertex s v, f.extends_piece s hs ⟨v, hv, rfl⟩, ?_⟩
    exact (DFunLike.congr_fun (f.comm hsu) v).symm
  -- Hence `inP` maps, by transporting finite independence along the arrow.
  have inP_image : ∀ u, f.onVertex u '' X.inP u ⊆ Y.inP u := by
    intro u z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hw' : InClosure (X.indep u) (X.lower u) w := by
      rw [X.span_lower u] at hw
      exact hw
    have hcl : InClosure (Y.indep u) (f.onVertex u '' X.lower u) (f.onVertex u w) :=
      InClosure.image (f.onVertex u) (f.onVertex u).injective (f.indep_image u) hw'
    have hcl' : InClosure (Y.indep u) (Y.lower u) (f.onVertex u w) :=
      InClosure.mono (lower_image u) hcl
    rw [Y.span_lower u]
    exact hcl'
  -- Relative-span generators are images of lower `inP`s; they map by `comm` and `inP_image`.
  change InClosure (Y.indep t)
      {y | ∃ r, ∃ hrt : r ⊂ t, ∃ z, z ∈ Y.inP r ∧ Y.le (le_of_lt hrt) z = y}
      (f.onVertex t x)
  have himg :
      InClosure (Y.indep t)
        (f.onVertex t ''
          {y | ∃ r, ∃ hrt : r ⊂ t, ∃ z, z ∈ X.inP r ∧ X.le (le_of_lt hrt) z = y})
        (f.onVertex t x) :=
    InClosure.image (f.onVertex t) (f.onVertex t).injective (f.indep_image t) hx
  refine InClosure.mono ?_ himg
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hz
  obtain ⟨r, hrt, v, hv, rfl⟩ := hw
  refine ⟨r, hrt, f.onVertex r v, inP_image r ⟨v, hv, rfl⟩, ?_⟩
  exact (DFunLike.congr_fun (f.comm (le_of_lt hrt)) v).symm

/-- **Lemma 11.5** (Structural properties and the last-axis description). Geometric arrows
compose, and restriction to a subset of the axes preserves systems and arrows. -/
theorem lemma_11_5 (K : AbstractElementaryClass.{u}) {n : ℕ} {L : Set (Finset (Fin n))}
    (X Y Z : GeometricSystem K n L) (f : GeometricArrow K X Y) (g : GeometricArrow K Y Z) :
    ∃ h : GeometricArrow K X Z,
      ∀ t, h.onVertex t = (g.onVertex t).comp (f.onVertex t) := by
  refine ⟨{
    onVertex := fun t => (g.onVertex t).comp (f.onVertex t)
    onVertex_strong := fun t =>
      K.strong_trans (f.onVertex t) (g.onVertex t) (f.onVertex_strong t) (g.onVertex_strong t)
    comm := by
      intro s t h
      ext x
      have hf := DFunLike.congr_fun (f.comm h) x
      have hg := DFunLike.congr_fun (g.comm h) (f.onVertex s x)
      simp only [Language.Embedding.comp_apply] at hf hg ⊢
      rw [hf]
      exact hg
    extends_piece := by
      intro s hs z hz
      obtain ⟨x, hx, hxz⟩ := hz
      have hxY : f.onVertex s x ∈ Y.piece s hs :=
        f.extends_piece s hs ⟨x, hx, rfl⟩
      have hzZ : g.onVertex s (f.onVertex s x) ∈ Z.piece s hs :=
        g.extends_piece s hs ⟨f.onVertex s x, hxY, rfl⟩
      simpa only [Language.Embedding.comp_apply] using hxz ▸ hzZ
    indep_image := by
      intro t S
      have himg :
          (fun x => (g.onVertex t).comp (f.onVertex t) x) '' S =
            g.onVertex t '' (f.onVertex t '' S) := by
        ext z
        simp [Set.mem_image, Language.Embedding.comp_apply]
      constructor
      · intro hS
        have hY : Y.indep t (f.onVertex t '' S) := (f.indep_image t S).mp hS
        have hZ : Z.indep t (g.onVertex t '' (f.onVertex t '' S)) :=
          (g.indep_image t _).mp hY
        simpa [himg] using hZ
      · intro hS
        have hZ : Z.indep t (g.onVertex t '' (f.onVertex t '' S)) := by
          simpa [himg] using hS
        exact (f.indep_image t S).mpr ((g.indep_image t _).mpr hZ)
  }, fun _ => rfl⟩

/-- **Proposition 11.6** (Tiled presentations). For an admissible shape and every sufficiently
large `μ`, there is a geometric system of level `μ` in which every active piece has
cardinality `μ`. -/
theorem proposition_11_6 (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (hL : Admissible n L) (μ : Cardinal.{u})
    (hμ : aleph0 ≤ μ) :
    ∃ X : GeometricSystem K n L, X.level = μ ∧
      ∀ s (hs : s ∈ L), #(X.piece s hs) = μ := by
  sorry

/-- **Proposition 11.7** (Conditional working package). If the geometric systems of one
admissible shape are categorical on an unbounded countably closed class of eligible levels,
a further subclass carries the working package. -/
theorem proposition_11_7 (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (hL : Admissible n L)
    (S : SystemShape.{u}) (W : WorkingScheme K S) (T : Set Cardinal.{u})
    (hT : EligibleSubclass W.eligible T) :
    ∃ W' : WorkingScheme K S, IsWorkingPackage W' ∧ EligibleSubclass T W'.eligible := by
  sorry

/-- **Theorem 11.9** (Classification with prescribed basis maps). At sufficiently closed
uniform levels, bijections of the nonroot pieces of two systems of the same shape extend to
a system isomorphism. In particular the shape is categorical at those levels. -/
theorem theorem_11_9 (K : AbstractElementaryClass.{u}) {n : ℕ}
    {L : Set (Finset (Fin n))} (hL : Admissible n L) :
    ∃ μ0 : Cardinal.{u}, ∀ μ, μ0 ≤ μ →
      ∀ X Y : GeometricSystem K n L, X.level = μ → Y.level = μ →
        (∀ s (hs : s ∈ L), ∃ e : X.piece s hs ≃ Y.piece s hs, True) →
        ∃ f : GeometricArrow K X Y, ∀ t, Function.Bijective (f.onVertex t) := by
  sorry

/-- A scheme object read as a geometric system, vertex by vertex. -/
structure SchemeFace {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (W : WorkingScheme K S) {μ : Cardinal.{u}} (hμ : μ ∈ W.eligible) (X : W.Object μ hμ)
    {n : ℕ} {L : Set (Finset (Fin n))} (G : GeometricSystem K n L) where
  vertex : S.Vertex ≃ Finset (Fin n)
  carrier : ∀ v, ((W.asSystem hμ X).obj v).carrier ≃ (G.vertex (vertex v)).carrier

/-- The scheme occurrence of a geometric coordinate. -/
def SchemeFace.toOccurrence {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    {W : WorkingScheme K S} {μ : Cardinal.{u}} {hμ : μ ∈ W.eligible} {X : W.Object μ hμ}
    {n : ℕ} {L : Set (Finset (Fin n))} {G : GeometricSystem K n L}
    (F : SchemeFace W hμ X G) (c : Coordinate G) :
    Occurrence K S (W.asSystem hμ X) :=
  ⟨F.vertex.symm c.label,
    (F.carrier (F.vertex.symm c.label)).symm
      (castCarrier (F.vertex.apply_symm_apply c.label).symm c.val)⟩

/-- The scheme arrow and the geometric arrow are the same map of vertices. -/
def SchemeFacesAgree {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    {W : WorkingScheme K S} {μ ν : Cardinal.{u}} {hμ : μ ∈ W.eligible} {hν : ν ∈ W.eligible}
    {X : W.Object μ hμ} {Y : W.Object ν hν} {n : ℕ} {L : Set (Finset (Fin n))}
    {Gx Gy : GeometricSystem K n L} (f : GeometricArrow K Gx Gy)
    (sf : SystemArrow K S (W.asSystem hμ X) (W.asSystem hν Y))
    (Fx : SchemeFace W hμ X Gx) (Fy : SchemeFace W hν Y Gy) : Prop :=
  ∀ v, ∃ h : Fx.vertex v = Fy.vertex v, ∀ x,
    Fy.carrier v (sf.onVertex v x) =
      castCarrier h (f.onVertex (Fx.vertex v) (Fx.carrier v x))

/-- **Claim 11.10** (Uniqueness of finite fresh types). For a fixed base and a finite ordered
list of active labels, all jointly fresh tuples with those labels have the same type over the
base. -/
theorem claim_11_10 (K : AbstractElementaryClass.{u}) {n : ℕ} {L : Set (Finset (Fin n))} :
    ∃ μ0 : Cardinal.{u}, ∀ μ, μ0 ≤ μ →
      ∀ (X Y0 Y1 : GeometricSystem K n L),
        X.level = μ → Y0.level = μ → Y1.level = μ →
        ∀ (f0 : GeometricArrow K X Y0) (f1 : GeometricArrow K X Y1) (k : ℕ)
          (labs : Fin k → Finset (Fin n)) (hlabs : ∀ i, labs i ∈ L)
          (b0 : ∀ i, (Y0.vertex (labs i)).carrier)
          (b1 : ∀ i, (Y1.vertex (labs i)).carrier),
          JointlyFreshIndexed f0 labs hlabs b0 →
          JointlyFreshIndexed f1 labs hlabs b1 →
          SameGeometricType f0 f1 labs b0 b1 := by
  sorry

/-- **Claim 11.11** (Free lifts preserve freshness). The free lift of the fresh singleton type
at an active label, along an arrow `X → V`, is fresh over `V`. A finite jointly fresh tuple
has the product of those singleton types. A bounded jointly fresh list has one type, fixed by
its labels, and an all-dominated hull. -/
theorem claim_11_11 (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (W : WorkingScheme K S) (hpack : IsWorkingPackage W) {n : ℕ}
    {L : Set (Finset (Fin n))} :
    ∃ T, ∃ hT : Tail W.eligible T,
      (∀ μ (hμ : μ ∈ T) (X V : W.Object μ (Tail.mem hT hμ))
        (f : SystemArrow K S (W.asSystem _ X) (W.asSystem _ V))
        (hf : W.permitted (X := X) (Y := V) f)
        (p : TupleOver K S W (Tail.mem hT hμ) X)
        (q : TupleOver K S W (Tail.mem hT hμ) V)
        (e : p.idx ≃ q.idx) (ep : p.idx ≃ PUnit.{u+1})
        (s : Finset (Fin n)) (hs : s ∈ L)
        (GX GV GP GQ : GeometricSystem K n L)
        (geoXV : GeometricArrow K GX GV) (geoXP : GeometricArrow K GX GP)
        (geoVQ : GeometricArrow K GV GQ)
        (FX : SchemeFace W (Tail.mem hT hμ) X GX)
        (FV : SchemeFace W (Tail.mem hT hμ) V GV)
        (FP : SchemeFace W p.hν p.host GP)
        (FQ : SchemeFace W q.hν q.host GQ),
        GX.level = μ → GV.level = μ → GP.level = p.ν → GQ.level = q.ν →
        IsFreeLift p q f hf e →
        SchemeFacesAgree geoXV f FX FV →
        SchemeFacesAgree geoXP p.incl FX FP →
        SchemeFacesAgree geoVQ q.incl FV FQ →
        (∃ hvt : FP.vertex ((p.val (ep.symm PUnit.unit)).1) = s,
          JointlyFreshIndexed geoXP (fun _ : PUnit.{u+1} => s) (fun _ => hs)
            (fun _ => castCarrier hvt
              (FP.carrier ((p.val (ep.symm PUnit.unit)).1)
                ((p.val (ep.symm PUnit.unit)).2)))) →
        ∃ hvt : FQ.vertex ((q.val (e (ep.symm PUnit.unit))).1) = s,
          JointlyFreshIndexed geoVQ (fun _ : PUnit.{u+1} => s) (fun _ => hs)
            (fun _ => castCarrier hvt
              (FQ.carrier ((q.val (e (ep.symm PUnit.unit))).1)
                ((q.val (e (ep.symm PUnit.unit))).2)))) ∧
      (∀ μ (hμ : μ ∈ T) (X Y : W.Object μ (Tail.mem hT hμ))
        (sf : SystemArrow K S (W.asSystem _ X) (W.asSystem _ Y))
        (hsf : W.permitted (X := X) (Y := Y) sf)
        (GX GY : GeometricSystem K n L) (geo : GeometricArrow K GX GY)
        (FX : SchemeFace W (Tail.mem hT hμ) X GX)
        (FY : SchemeFace W (Tail.mem hT hμ) Y GY)
        (k : ℕ) (labs : Fin k → Finset (Fin n)) (hlabs : ∀ i, labs i ∈ L)
        (b : ∀ i, (GY.vertex (labs i)).carrier),
        GX.level = μ → GY.level = μ →
        SchemeFacesAgree geo sf FX FY →
        JointlyFreshIndexed geo labs hlabs b →
        ∃ p : Fin k → TupleOver K S W (Tail.mem hT hμ) X,
          (∀ i, ∃ (e : (p i).idx ≃ PUnit.{u+1}) (GP : GeometricSystem K n L)
              (FP : SchemeFace W (p i).hν (p i).host GP)
              (geoP : GeometricArrow K GX GP),
              GP.level = (p i).ν ∧
              SchemeFacesAgree geoP (p i).incl FX FP ∧
              ∃ hvt : FP.vertex ((p i).val (e.symm PUnit.unit)).1 = labs i,
                JointlyFreshIndexed geoP (fun _ : PUnit.{u+1} => labs i) (fun _ => hlabs i)
                  (fun _ => castCarrier hvt
                    (FP.carrier ((p i).val (e.symm PUnit.unit)).1
                      ((p i).val (e.symm PUnit.unit)).2))) ∧
          ∃ joint : TupleOver K S W (Tail.mem hT hμ) X,
            ∃ e : ULift.{u} (Fin k) ≃ joint.idx,
              IsFiniteProduct k p joint ∧
              SameGaloisType
                (asTuple sf hsf (fun i : ULift.{u} (Fin k) =>
                  FY.toOccurrence (⟨labs i.down, hlabs i.down, b i.down⟩ : Coordinate GY)))
                joint e (Equiv.refl joint.idx) ∧
              ∀ i : Fin k, ∃ e' : (p i).idx ≃ PUnit.{u+1},
                SameGaloisType (p i)
                  (asTuple sf hsf (fun _ : PUnit.{u+1} =>
                    FY.toOccurrence (⟨labs i, hlabs i, b i⟩ : Coordinate GY)))
                  e' (Equiv.refl _)) ∧
      (∀ μ (hμ : μ ∈ T) (X Y0 Y1 : W.Object μ (Tail.mem hT hμ)) {ι : Type u}
        (sf0 : SystemArrow K S (W.asSystem _ X) (W.asSystem _ Y0))
        (hf0 : W.permitted (X := X) (Y := Y0) sf0)
        (sf1 : SystemArrow K S (W.asSystem _ X) (W.asSystem _ Y1))
        (hf1 : W.permitted (X := X) (Y := Y1) sf1)
        (GX GY0 GY1 : GeometricSystem K n L)
        (g0 : GeometricArrow K GX GY0) (g1 : GeometricArrow K GX GY1)
        (FX : SchemeFace W (Tail.mem hT hμ) X GX)
        (FY0 : SchemeFace W (Tail.mem hT hμ) Y0 GY0)
        (FY1 : SchemeFace W (Tail.mem hT hμ) Y1 GY1)
        (labs : ι → Finset (Fin n)) (hlabs : ∀ i, labs i ∈ L)
        (b0 : ∀ i, (GY0.vertex (labs i)).carrier)
        (b1 : ∀ i, (GY1.vertex (labs i)).carrier),
        #ι < μ → GX.level = μ → GY0.level = μ → GY1.level = μ →
        SchemeFacesAgree g0 sf0 FX FY0 →
        SchemeFacesAgree g1 sf1 FX FY1 →
        JointlyFreshIndexed g0 labs hlabs b0 →
        JointlyFreshIndexed g1 labs hlabs b1 →
        SameGaloisType
          (asTuple sf0 hf0 (fun i =>
            FY0.toOccurrence (⟨labs i, hlabs i, b0 i⟩ : Coordinate GY0)))
          (asTuple sf1 hf1 (fun i =>
            FY1.toOccurrence (⟨labs i, hlabs i, b1 i⟩ : Coordinate GY1)))
          (Equiv.refl ι) (Equiv.refl ι) ∧
        ∃ (Z : W.Object μ (Tail.mem hT hμ))
          (incl : SystemArrow K S (W.asSystem _ X) (W.asSystem _ Z))
          (hincl : W.permitted (X := X) (Y := Z) incl)
          (c : ι → Occurrence K S (W.asSystem _ Z)),
          AllDominated incl hincl ι c ∧
          SameGaloisType
            (asTuple sf0 hf0 (fun i =>
              FY0.toOccurrence (⟨labs i, hlabs i, b0 i⟩ : Coordinate GY0)))
            (asTuple incl hincl c) (Equiv.refl ι) (Equiv.refl ι)) := by
  sorry

/-- **Claim 11.12** (Bounded rank cost and chosen coordinates). A finite tuple in the target
of an arrow sits in a subextension whose complementary pieces are finite. A bounded tuple
sits in a subextension whose complementary pieces have total size at most `max(|d|, ℵ₀)`.
If a complementary partition of the target is specified, those pieces can be taken inside
it. -/
theorem claim_11_12 (K : AbstractElementaryClass.{u}) {n : ℕ} {L : Set (Finset (Fin n))} :
    ∃ μ0 : Cardinal.{u}, ∀ μ, μ0 ≤ μ → aleph0 ≤ μ →
      ∀ (X Y : GeometricSystem K n L), X.level = μ → Y.level = μ →
        ∀ f : GeometricArrow K X Y,
          (∀ {ι : Type u} (d : ι → Σ t : Finset (Fin n), (Y.vertex t).carrier),
            #ι < aleph0 →
            ∃ (U : GeometricSystem K n L) (g : GeometricArrow K X U)
              (h : GeometricArrow K U Y)
              (extra : ∀ s, s ∈ L → Set (U.vertex s).carrier),
              U.level = μ ∧ FactorsThrough f g h ∧ CoordinatesInImage h d ∧
              IsPieceExtension g extra ∧ ∀ s hs, #(↥(extra s hs)) < aleph0) ∧
          (∀ {ι : Type u} (d : ι → Σ t : Finset (Fin n), (Y.vertex t).carrier),
            #ι < μ →
            ∃ (U : GeometricSystem K n L) (g : GeometricArrow K X U)
              (h : GeometricArrow K U Y)
              (extra : ∀ s, s ∈ L → Set (U.vertex s).carrier),
              U.level = μ ∧ FactorsThrough f g h ∧ CoordinatesInImage h d ∧
              IsPieceExtension g extra ∧ complementTotal extra ≤ max (#ι) aleph0) ∧
          (∀ (C : ∀ s, s ∈ L → Set (Y.vertex s).carrier), IsPieceExtension f C →
            ∀ {ι : Type u} (d : ι → Σ t : Finset (Fin n), (Y.vertex t).carrier),
              #ι < μ →
              ∃ (U : GeometricSystem K n L) (g : GeometricArrow K X U)
                (h : GeometricArrow K U Y)
                (extra : ∀ s, s ∈ L → Set (U.vertex s).carrier),
                U.level = μ ∧ FactorsThrough f g h ∧ CoordinatesInImage h d ∧
                IsPieceExtension g extra ∧ complementTotal extra ≤ max (#ι) aleph0 ∧
                ∀ s hs, h.onVertex s '' extra s hs ⊆ C s hs) := by
  sorry

/-- **Claim 11.13** (Primeness over bounded complementary pieces). If a bounded list
enumerates every complementary piece of `X → U`, then `U` is all-dominated over `X` plus
that list. `U` embeds over `X` into any extension that realizes a prescribed matching of
these coordinates. -/
theorem claim_11_13 (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (W : WorkingScheme K S) (hpack : IsWorkingPackage W) {n : ℕ}
    {L : Set (Finset (Fin n))} :
    ∃ T, ∃ hT : Tail W.eligible T,
      ∀ μ (hμ : μ ∈ T) (Xg Ug : GeometricSystem K n L) (f : GeometricArrow K Xg Ug)
        {ι : Type u} (label : ι → Finset (Fin n)) (active : ∀ i, label i ∈ L)
        (b : ∀ i, (Ug.vertex (label i)).carrier),
        Xg.level = μ → Ug.level = μ → #ι < μ →
        EnumeratesComplements f label active b →
        (∀ (Xs Us : W.Object μ (Tail.mem hT hμ))
          (sf : SystemArrow K S (W.asSystem _ Xs) (W.asSystem _ Us))
          (hsf : W.permitted (X := Xs) (Y := Us) sf)
          (FX : SchemeFace W (Tail.mem hT hμ) Xs Xg)
          (FU : SchemeFace W (Tail.mem hT hμ) Us Ug),
          SchemeFacesAgree f sf FX FU →
          AllDominated sf hsf ι (fun i =>
            FU.toOccurrence (⟨label i, active i, b i⟩ : Coordinate Ug))) ∧
        ∀ (Yg : GeometricSystem K n L) (g : GeometricArrow K Xg Yg)
          (c : ∀ i, (Yg.vertex (label i)).carrier),
          Yg.level = μ →
          JointlyFreshIndexed g label active c →
          ∃ h : GeometricArrow K Ug Yg,
            FactorsThrough g f h ∧ ∀ i, h.onVertex (label i) (b i) = c i := by
  sorry

end
end AEC
