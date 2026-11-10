module

public import AEC.Section5.NamedWorkingScheme
public import AEC.Section5.PackageClauses
public import Mathlib.SetTheory.Cardinal.Arithmetic

@[expose] public section

/-!
# Package transfer for `namedWorkingScheme` (Proposition 5.7)

If `W` is a working package and `T` lies above the naming threshold for the fixed list `c`,
then `namedWorkingScheme W X0 c T hT` is again a working package.

Threshold hypotheses: `#ι < μ0`, every level of `T` is `≥ μ0`, and every level of `T` is
infinite.
-/

namespace AEC
section

universe u

open FirstOrder Cardinal

namespace WorkingScheme

variable {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}

theorem named_index_lt_of_tail {μ0 : Cardinal.{u}} {ι : Type u} {T : Set Cardinal.{u}}
    (hι : #ι < μ0) (hTail : ∀ μ ∈ T, μ0 ≤ μ) {μ : Cardinal.{u}} (hμ : μ ∈ T) :
    #ι < μ :=
  lt_of_lt_of_le hι (hTail μ hμ)

theorem sum_mk_lt_of_lt {α β : Type u} {μ : Cardinal.{u}}
    (hinf : aleph0 ≤ μ) (hα : #α < μ) (hβ : #β < μ) : #(α ⊕ β) < μ := by
  rw [← add_def]
  exact add_lt_of_lt hinf hα hβ

/-- Saturation: named diagrams are `W`-diagrams of names followed by the further list. -/
theorem isSaturated_namedWorkingScheme
    (W : WorkingScheme K S) (hSat : IsSaturated W)
    {μ0 : Cardinal.{u}} {hμ0 : μ0 ∈ W.eligible} (X0 : W.Object μ0 hμ0)
    {ι : Type u} (c : ι → Occurrence K S (W.asSystem hμ0 X0))
    (T : Set Cardinal.{u}) (hT : EligibleSubclass W.eligible T)
    (hι : #ι < μ0) (hTail : ∀ μ ∈ T, μ0 ≤ μ) (hinf : ∀ μ ∈ T, aleph0 ≤ μ) :
    IsSaturated (namedWorkingScheme W X0 c T hT) where
  saturated := fun {μ ν} {hμ} {hν} {α β} X Y xs base ext hα hβ hEq => by
    have hμT : μ ∈ T := hμ
    have hιμ : #ι < μ := named_index_lt_of_tail hι hTail hμT
    let extW : (ι ⊕ α) ⊕ β → Occurrence K S Y.system := fun i =>
      match i with
      | Sum.inl (Sum.inl j) => Y.names j
      | Sum.inl (Sum.inr a) => ext (Sum.inl a)
      | Sum.inr b => ext (Sum.inr b)
    obtain ⟨Z0, f0, zs0, hf0, hzs0, hEqZ⟩ :=
      hSat.saturated (X := X.base) (Y := Y.base)
        (xs := Sum.elim X.names xs) (base := Sum.elim Y.names base) (ext := extW)
        (sum_mk_lt_of_lt (hinf μ hμT) hιμ hα) hβ hEq
    let Z : NamedObject W X0 c μ (EligibleSubclass.mem_source hT hμT) :=
      ⟨Z0, fun j => zs0 (Sum.inl (Sum.inl j)), by
        have hpush : W.DiagramEq X.base Z0 X.names (fun j => zs0 (Sum.inl (Sum.inl j))) := by
          have h := W.diagram_preserved X.base Z0 f0 hf0 X.names
          have heq : (fun j => zs0 (Sum.inl (Sum.inl j))) =
              (fun j => f0.mapOcc (X.names j)) := by
            funext j; exact hzs0 (Sum.inl j)
          simpa [heq, SystemArrow.mapOcc] using h
        exact W.diagram_trans X0 X.base Z0 c X.names _ X.realizes hpush⟩
    let zs : α ⊕ β → Occurrence K S (W.asSystem (EligibleSubclass.mem_source hT hμT) Z0) :=
      fun i => match i with
        | Sum.inl a => zs0 (Sum.inl (Sum.inr a))
        | Sum.inr b => zs0 (Sum.inr b)
    refine ⟨Z, f0, zs, ⟨hf0, ?_⟩, ?_, ?_⟩
    · intro j
      change zs0 (Sum.inl (Sum.inl j)) =
          ⟨(X.names j).1, f0.onVertex (X.names j).1 (X.names j).2⟩
      have h := hzs0 (Sum.inl j)
      have occ_eq : Sum.elim X.names xs (Sum.inl j) = X.names j :=
        Sum.elim_inl X.names xs j
      rw [occ_eq] at h
      exact h
    · intro i
      change zs0 (Sum.inl (Sum.inr i)) =
          ⟨(xs i).1, f0.onVertex (xs i).1 (xs i).2⟩
      have h := hzs0 (Sum.inr i)
      have occ_eq : Sum.elim X.names xs (Sum.inr i) = xs i :=
        Sum.elim_inr X.names xs i
      rw [occ_eq] at h
      exact h
    · -- Reassociate `(ι ⊕ α) ⊕ β` back to `ι ⊕ (α ⊕ β)` for `NamedDiagramEq`.
      let e := sumAssocNamesLeft ι α β
      have h' :=
        (W.diagram_reindex Z0 Y.base e.symm zs0 extW).mp hEqZ
      have heqX : (fun b => zs0 (e b)) = Sum.elim Z.names zs := by
        funext b; cases b with
          | inl _ => rfl
          | inr ab => cases ab <;> rfl
      have heqY : (fun b => extW (e b)) = Sum.elim Y.names ext := by
        funext b; cases b with
          | inl _ => rfl
          | inr ab => cases ab <;> rfl
      have h'' : W.DiagramEq Z.base Y.base (Sum.elim Z.names zs) (Sum.elim Y.names ext) := by
        simpa [heqX, heqY] using h'
      exact h''

/-- Mixed downward: request names together with the given occurrences. -/
theorem hasMixedDownward_namedWorkingScheme
    (W : WorkingScheme K S) (hMix : HasMixedDownward W)
    {μ0 : Cardinal.{u}} {hμ0 : μ0 ∈ W.eligible} (X0 : W.Object μ0 hμ0)
    {ι : Type u} (c : ι → Occurrence K S (W.asSystem hμ0 X0))
    (T : Set Cardinal.{u}) (hT : EligibleSubclass W.eligible T)
    (hι : #ι < μ0) (hTail : ∀ μ ∈ T, μ0 ≤ μ) (hinf : ∀ μ ∈ T, aleph0 ≤ μ) :
    HasMixedDownward (namedWorkingScheme W X0 c T hT) where
  downward := fun {μ ν} hμ hν X γ occ hνμ hγ => by
    have hμT : μ ∈ T := hμ
    have hνT : ν ∈ T := hν
    have hιν : #ι < ν := named_index_lt_of_tail hι hTail hνT
    have hsum : #(ι ⊕ γ) ≤ ν := by
      rw [← add_def]
      exact Cardinal.add_le_of_le (hinf ν hνT) (le_of_lt hιν) hγ
    obtain ⟨Y0, f0, hf0, hocc⟩ :=
      hMix.downward (hμ := EligibleSubclass.mem_source hT hμT)
        (hν := EligibleSubclass.mem_source hT hνT) X.base (ι ⊕ γ)
        (Sum.elim X.names occ) hνμ hsum
    let hnamesY : ι → Occurrence K S (W.asSystem (EligibleSubclass.mem_source hT hνT) Y0) :=
      fun j => Classical.choose (hocc (Sum.inl j))
    have hnamesY_spec : ∀ j, X.names j = f0.mapOcc (hnamesY j) :=
      fun j => Classical.choose_spec (hocc (Sum.inl j))
    refine ⟨⟨Y0, hnamesY, ?_⟩, f0, ⟨hf0, fun j => hnamesY_spec j⟩, ?_⟩
    · have hpush : W.DiagramEq Y0 X.base hnamesY X.names := by
        have h := W.diagram_preserved Y0 X.base f0 hf0 hnamesY
        have heq : X.names = (fun j => f0.mapOcc (hnamesY j)) := by
          funext j; exact hnamesY_spec j
        simpa [heq, SystemArrow.mapOcc] using h
      exact W.diagram_trans X0 X.base Y0 c X.names hnamesY X.realizes
        (W.diagram_symm Y0 X.base hnamesY X.names hpush)
    · intro i
      obtain ⟨y, hy⟩ := hocc (Sum.inr i)
      exact ⟨y, hy⟩

/-- Exhaustion transfer at one level: recover name preservation by the double-name
`diagram_iso` match, then cancel the name prefix by `diagram_restrict`. -/
theorem satisfiesExhaustion_namedWorkingScheme
    (W : WorkingScheme K S) (hEx : SatisfiesExhaustion W)
    {μ0 : Cardinal.{u}} {hμ0 : μ0 ∈ W.eligible} (X0 : W.Object μ0 hμ0)
    {ι : Type u} (c : ι → Occurrence K S (W.asSystem hμ0 X0))
    (T : Set Cardinal.{u}) (hT : EligibleSubclass W.eligible T)
    (hι : #ι < μ0) (hTail : ∀ μ ∈ T, μ0 ≤ μ) (_hinf : ∀ μ ∈ T, aleph0 ≤ μ) :
    SatisfiesExhaustion (namedWorkingScheme W X0 c T hT) where
  exhaustion := fun {μ} {hμ} X Y f hdiag => by
    have hμT : μ ∈ T := hμ
    have hιμ : #ι < μ := named_index_lt_of_tail hι hTail hμT
    have hn : PreservesNames X Y f := by
      have hN := hdiag (xs := X.names) hιμ
      obtain ⟨ψ, _, hψ⟩ := (W.diagram_iso X.base Y.base
          (Sum.elim X.names X.names)
          (Sum.elim Y.names (fun j => f.mapOcc (X.names j)))).mp hN
      intro j
      exact (hψ (Sum.inl j)).trans (hψ (Sum.inr j)).symm
    refine ⟨?_, hn⟩
    refine hEx.exhaustion X.base Y.base f ?_
    intro γ zs hγ
    have hN := hdiag (xs := zs) hγ
    have hN' : W.DiagramEq X.base Y.base (Sum.elim X.names zs)
        (Sum.elim Y.names (fun i => f.mapOcc (zs i))) := hN
    have hN'' : W.DiagramEq X.base Y.base (Sum.elim X.names zs)
        (Sum.elim (fun j => f.mapOcc (X.names j)) (fun i => f.mapOcc (zs i))) := by
      convert hN' using 1
      funext i
      cases i with
      | inl j => exact (hn j).symm
      | inr j => rfl
    exact (W.diagram_restrict X.base Y.base X.names
      (fun j => f.mapOcc (X.names j)) zs (fun i => f.mapOcc (zs i)) hN'').2

/-- Chain-union transfer for nonempty chains, using cocone naturality from `W`. -/
theorem hasChainUnions_namedWorkingScheme
    (W : WorkingScheme K S) (hU : HasChainUnions W)
    {μ0 : Cardinal.{u}} {hμ0 : μ0 ∈ W.eligible} (X0 : W.Object μ0 hμ0)
    {ι : Type u} (c : ι → Occurrence K S (W.asSystem hμ0 X0))
    (T : Set Cardinal.{u}) (hT : EligibleSubclass W.eligible T)
    (_hι : #ι < μ0) (_hTail : ∀ μ ∈ T, μ0 ≤ μ) (_hinf : ∀ μ ∈ T, aleph0 ≤ μ) :
    HasChainUnions (namedWorkingScheme W X0 c T hT) where
  union := fun {μ} hμ index _inst obj le le_arrow hcomp hidx => by
    classical
    have hμT : μ ∈ T := hμ
    let hμW : μ ∈ W.eligible := EligibleSubclass.mem_source hT hμT
    obtain ⟨U0, incl0, hincl0, hnat, hub⟩ :=
      hU.union (hμ := hμW) (index := index) (obj := fun i => (obj i).base)
        (le := fun i j => le i j) (fun i j => (le_arrow i j).1) hcomp hidx
    obtain ⟨i0⟩ : Nonempty index := _inst
    let namesU : ι → Occurrence K S (W.asSystem hμW U0) :=
      fun j => (incl0 i0).mapOcc ((obj i0).names j)
    have hreal : W.DiagramEq X0 U0 c namesU :=
      W.diagram_trans X0 (obj i0).base U0 c (obj i0).names namesU (obj i0).realizes
        (W.diagram_preserved (obj i0).base U0 (incl0 i0) (hincl0 i0) (obj i0).names)
    let U : NamedObject W X0 c μ hμW := ⟨U0, namesU, hreal⟩
    have hinclNamed : ∀ i, NamedPermitted (obj i) U (incl0 i) := by
      intro i
      refine ⟨hincl0 i, ?_⟩
      intro j
      change namesU j = (incl0 i).mapOcc ((obj i).names j)
      have hpath : SystemArrow.comp (le i i0) (incl0 i0) = incl0 i := hnat i i0
      have hn := (le_arrow i i0).2 j
      calc
        namesU j = (incl0 i0).mapOcc ((obj i0).names j) := rfl
        _ = (incl0 i0).mapOcc ((le i i0).mapOcc ((obj i).names j)) :=
          congrArg (fun x => (incl0 i0).mapOcc x) hn
        _ = (SystemArrow.comp (le i i0) (incl0 i0)).mapOcc ((obj i).names j) :=
          (SystemArrow.mapOcc_comp (le i i0) (incl0 i0) ((obj i).names j)).symm
        _ = (incl0 i).mapOcc ((obj i).names j) :=
          congrArg (fun f => f.mapOcc ((obj i).names j)) hpath
    refine ⟨U, incl0, hinclNamed, ?_, ?_⟩
    · intro i j
      exact hnat i j
    · intro ν hν Z toZ htoZ hμν
      have hνT : ν ∈ T := hν
      let hνW : ν ∈ W.eligible := EligibleSubclass.mem_source hT hνT
      obtain ⟨toU, htoU, hfac⟩ :=
        hub hνW Z.base (fun i => toZ i) (fun i => (htoZ i).1) hμν
      refine ⟨toU, ⟨htoU, ?_⟩, hfac⟩
      intro j
      have hZ := (htoZ i0).2 j
      calc
        Z.names j = toU.mapOcc ((incl0 i0).mapOcc ((obj i0).names j)) := by
          rw [← SystemArrow.mapOcc_comp, hfac i0]; exact hZ
        _ = toU.mapOcc (namesU j) := rfl

/-- Full working-package transfer for the named scheme of Proposition 5.7. -/
theorem isWorkingPackage_namedWorkingScheme
    (W : WorkingScheme K S) (hpack : IsWorkingPackage W)
    {μ0 : Cardinal.{u}} {hμ0 : μ0 ∈ W.eligible} (X0 : W.Object μ0 hμ0)
    {ι : Type u} (c : ι → Occurrence K S (W.asSystem hμ0 X0))
    (T : Set Cardinal.{u}) (hT : EligibleSubclass W.eligible T)
    (hι : #ι < μ0) (hTail : ∀ μ ∈ T, μ0 ≤ μ) (hinf : ∀ μ ∈ T, aleph0 ≤ μ) :
    IsWorkingPackage (namedWorkingScheme W X0 c T hT) :=
  ⟨hasChainUnions_namedWorkingScheme W hpack.1 X0 c T hT hι hTail hinf,
    hasMixedDownward_namedWorkingScheme W hpack.2.1 X0 c T hT hι hTail hinf,
    isSaturated_namedWorkingScheme W hpack.2.2.1 X0 c T hT hι hTail hinf,
    satisfiesExhaustion_namedWorkingScheme W hpack.2.2.2 X0 c T hT hι hTail hinf⟩

end WorkingScheme

end
end AEC
