# Product of types

From [Proposition 6.12](Proposition_6.12.md).

Proposition 6.12 (Products of bounded types). For bounded types $p(x)$, $q(y)$ over $A$, realize $p$ in an extension $B \ge A$ and then realize $q^B$ in a further extension. The joint type of $(x, y)$ over $A$, denoted $p \otimes q$, is independent of all choices. Binary products are symmetric, with the indicated permutation of coordinates. Finite products associate, are permutation invariant, and commute with coordinate projections. Furthermore

$$(p \otimes q)^B = p_B \otimes q^B.$$

These assertions hold across eligible levels when all originating arities and uniform testing costs are bounded at the smallest level.

**Done** for same-level existence and anchored independence via [`Proposition_6.12.md`](Proposition_6.12.md) / `proposition_6_12`. `IsProduct` is the witness (a realization of `p`, a free lift of `q`, and the joint). Symmetry, `IsFiniteProduct`, base change, mixed levels, and untied free-lift stationarity stay deferred.

**[ProductType.lean](ProductType.lean)**

@import "ProductType.lean"
