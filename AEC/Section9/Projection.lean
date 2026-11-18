module

public import AEC.Section5.Results
public import AEC.Section6.Results

@[expose] public section

namespace AEC
section

universe u

open FirstOrder Cardinal

/-- A **projection** `P : C → D` of working schemes (Proposition 9.1): `D`'s vertices are
retained vertices of `C` (`vmap`), every `C`-level is a `D`-level, `P` takes objects to objects
(with vertexwise isomorphisms onto the retained components) and permitted arrows, including
mixed-level ones, to permitted arrows, compatibly with those isomorphisms. -/
structure SchemeProjection {K : AbstractElementaryClass.{u}} {S S' : SystemShape.{u}}
    (C : WorkingScheme K S) (D : WorkingScheme K S') where
  vmap : S'.Vertex → S.Vertex
  levels : ∀ {μ : Cardinal.{u}}, μ ∈ C.eligible → μ ∈ D.eligible
  obj : ∀ {μ : Cardinal.{u}} {hμ : μ ∈ C.eligible}, C.Object μ hμ → D.Object μ (levels hμ)
  iso : ∀ {μ : Cardinal.{u}} {hμ : μ ∈ C.eligible} (X : C.Object μ hμ) (v : S'.Vertex),
    ((C.asSystem hμ X).obj (vmap v)).carrier ≃[K.τ] ((D.asSystem (levels hμ) (obj X)).obj v).carrier
  arr : ∀ {μ ν : Cardinal.{u}} {hμ : μ ∈ C.eligible} {hν : ν ∈ C.eligible}
    (X : C.Object μ hμ) (Y : C.Object ν hν)
    (f : SystemArrow K S (C.asSystem hμ X) (C.asSystem hν Y)), C.permitted (X := X) (Y := Y) f →
    SystemArrow K S' (D.asSystem (levels hμ) (obj X)) (D.asSystem (levels hν) (obj Y))
  arr_permitted : ∀ {μ ν : Cardinal.{u}} {hμ : μ ∈ C.eligible} {hν : ν ∈ C.eligible}
    (X : C.Object μ hμ) (Y : C.Object ν hν)
    (f : SystemArrow K S (C.asSystem hμ X) (C.asSystem hν Y))
    (hf : C.permitted (X := X) (Y := Y) f),
    D.permitted (X := obj X) (Y := obj Y) (arr X Y f hf)
  arr_comm : ∀ {μ ν : Cardinal.{u}} {hμ : μ ∈ C.eligible} {hν : ν ∈ C.eligible}
    (X : C.Object μ hμ) (Y : C.Object ν hν)
    (f : SystemArrow K S (C.asSystem hμ X) (C.asSystem hν Y))
    (hf : C.permitted (X := X) (Y := Y) f) (v : S'.Vertex) (x),
    (arr X Y f hf).onVertex v (iso X v x) = iso Y v (f.onVertex (vmap v) x)

namespace SchemeProjection

variable {K : AbstractElementaryClass.{u}} {S S' : SystemShape.{u}}
  {C : WorkingScheme K S} {D : WorkingScheme K S'} (P : SchemeProjection C D)

/-- A tuple of occurrences in the retained sorts of a `C`-system. -/
abbrev Retained {μ : Cardinal.{u}} {hμ : μ ∈ C.eligible} (X : C.Object μ hμ) (α : Type u) :=
  α → Σ v : S'.Vertex, ((C.asSystem hμ X).obj (P.vmap v)).carrier

/-- The retained tuple read in `C`. -/
def full {μ : Cardinal.{u}} {hμ : μ ∈ C.eligible} {X : C.Object μ hμ} {α : Type u}
    (xs : P.Retained X α) : α → Occurrence K S (C.asSystem hμ X) :=
  fun i => ⟨P.vmap (xs i).1, (xs i).2⟩

/-- The retained tuple read in the projection `P X`. -/
def proj {μ : Cardinal.{u}} {hμ : μ ∈ C.eligible} {X : C.Object μ hμ} {α : Type u}
    (xs : P.Retained X α) : α → Occurrence K S' (D.asSystem (P.levels hμ) (P.obj X)) :=
  fun i => ⟨(xs i).1, P.iso X _ (xs i).2⟩

/-- **Diagram comparison hypothesis** of Proposition 9.1: for bounded retained tuples (bounded at
both levels), equality of `C`-diagrams is equivalent to equality of projected `D`-diagrams. -/
def Comparison : Prop :=
  ∀ {μ ν : Cardinal.{u}} {hμ : μ ∈ C.eligible} {hν : ν ∈ C.eligible}
    (X : C.Object μ hμ) (Y : C.Object ν hν) {α : Type u}
    (xs : P.Retained X α) (ys : P.Retained Y α), #α < μ → #α < ν →
    (C.DiagramEq (X := X) (Y := Y) (P.full xs) (P.full ys) ↔
      D.DiagramEq (X := P.obj X) (Y := P.obj Y) (P.proj xs) (P.proj ys))

/-- A tuple over a `C`-object whose entries lie in retained sorts. -/
structure RetainedOver {μ : Cardinal.{u}} (hμ : μ ∈ C.eligible) (X : C.Object μ hμ) where
  ν : Cardinal.{u}
  hν : ν ∈ C.eligible
  host : C.Object ν hν
  incl : SystemArrow K S (C.asSystem hμ X) (C.asSystem hν host)
  incl_arrow : C.permitted (X := X) (Y := host) incl
  idx : Type u
  val : P.Retained host idx

/-- The `C`-type it determines (parameters: all of `X`, forgotten components included). -/
def RetainedOver.toFull {μ : Cardinal.{u}} {hμ : μ ∈ C.eligible} {X : C.Object μ hμ}
    (p : P.RetainedOver hμ X) : TupleOver K S C hμ X :=
  ⟨p.ν, p.hν, p.host, p.incl, p.incl_arrow, p.idx, P.full p.val⟩

/-- Its projection: a `D`-type over `P X`. -/
def RetainedOver.toProj {μ : Cardinal.{u}} {hμ : μ ∈ C.eligible} {X : C.Object μ hμ}
    (p : P.RetainedOver hμ X) : TupleOver K S' D (P.levels hμ) (P.obj X) :=
  ⟨p.ν, P.levels p.hν, P.obj p.host, P.arr X p.host p.incl p.incl_arrow,
    P.arr_permitted X p.host p.incl p.incl_arrow, p.idx, P.proj p.val⟩

end SchemeProjection

end
end AEC
