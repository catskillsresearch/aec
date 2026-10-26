module

public import AEC.Section5.SystemObject

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A system embedding is a family of commuting embeddings of the vertices, one for each
vertex. An arrow is such an embedding whose vertex maps are strong. No condition on
intersections of images is part of this definition. -/
structure SystemArrow (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (X Y : SystemObject K S) where
  onVertex : ∀ v, Language.Embedding K.τ (X.obj v).carrier (Y.obj v).carrier
  onVertex_strong : ∀ v, K.Strong (onVertex v)
  comm : ∀ {i j} (h : S.specified i j),
    (onVertex j).comp (X.edge h) = (Y.edge h).comp (onVertex i)

/-- Occurrence of an element in a system: a vertex together with an element of that vertex. -/
abbrev Occurrence (K : AbstractElementaryClass.{u}) (S : SystemShape.{u})
    (X : SystemObject K S) :=
  Σ v : S.Vertex, (X.obj v).carrier

/-- Compose system embeddings: first `f`, then `g`. -/
def SystemArrow.comp {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    {X Y Z : SystemObject K S} (f : SystemArrow K S X Y) (g : SystemArrow K S Y Z) :
    SystemArrow K S X Z where
  onVertex v := (g.onVertex v).comp (f.onVertex v)
  onVertex_strong v :=
    K.strong_trans (f.onVertex v) (g.onVertex v) (f.onVertex_strong v) (g.onVertex_strong v)
  comm := by
    intro i j h
    ext x
    have hf := DFunLike.congr_fun (f.comm h) x
    have hg := DFunLike.congr_fun (g.comm h) (f.onVertex i x)
    simp only [Language.Embedding.comp_apply] at hf hg ⊢
    rw [hf]
    exact hg

/-- The identity system arrow. -/
def SystemArrow.refl {K : AbstractElementaryClass.{u}} {S : SystemShape.{u}}
    (X : SystemObject K S) : SystemArrow K S X X where
  onVertex v := Language.Embedding.refl K.τ (X.obj v).carrier
  onVertex_strong v := by
    have hmem : K.Mem (X.obj v) := X.inK v
    simpa using K.strong_refl (X.obj v) hmem
  comm := by
    intro i j h
    ext x
    simp [Language.Embedding.comp_apply, Language.Embedding.refl_apply]

end
end AEC
