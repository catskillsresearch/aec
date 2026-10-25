module

public import AEC.Section2.SmallCode
public import AEC.Section2.DirectLimit

@[expose] public section

namespace AEC
section

universe u

open FirstOrder

/-- A directed system of allowed small models, with the transition embeddings matching
allowed pairs after transport to the ordinal presentations. -/
structure CodedPresentation {τ : Tau.{u}} {lam : Cardinal.{u}} (c : SmallCode τ lam) where
  system : DirectedSystem τ
  rep : system.ι → SmallModel τ lam
  rep_mem : ∀ i, rep i ∈ c.model
  iso : ∀ i, (system.obj i).carrier ≃[τ] ↥(rep i).domain
  pair_spec : ∀ {i j} (hij : system.rel i j),
    ∃ p : SmallPair τ lam, p ∈ c.pair ∧ p.small = rep i ∧ p.big = rep j ∧
      ∃ (eSmall : (system.obj i).carrier ≃[τ] ↥p.small.domain)
        (eBig : (system.obj j).carrier ≃[τ] ↥p.big.domain),
        p.incl.comp eSmall.toEmbedding = eBig.toEmbedding.comp (system.map hij)

end
end AEC
