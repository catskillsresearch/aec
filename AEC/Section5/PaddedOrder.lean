module

public import Mathlib.SetTheory.Cardinal.Basic

@[expose] public section

namespace AEC
section

universe u

open Cardinal

/-- Lemma 5.4. A linear order is padded when it contains a well-ordered subset of the
same cardinality. Order embeddings of padded orders of eligible cardinality induce arrows
of the working scheme. -/
class IsPadded (I : Type u) [LinearOrder I] : Prop where
  padded : ∃ s : Set I, #s = #I ∧ WellFounded ((· < ·) : s → s → Prop)

end
end AEC
