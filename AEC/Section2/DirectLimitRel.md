# Direct-limit relation

From [Lemma 2.1](Lemma_2.1.md).

For a diagram $(M_i, f_{ij})$ indexed by a directed partial order, form the quotient of the disjoint union of its underlying sets by

$$(i, x) \sim (j, y) \iff (\exists k \ge i, j)\ f_{ik}(x) = f_{jk}(y).$$

Directedness and coherence make this an equivalence relation.

**[DirectLimitRel.lean](DirectLimitRel.lean)**

@import "DirectLimitRel.lean"
