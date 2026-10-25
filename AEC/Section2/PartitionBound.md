# Partition bound

From [Lemma 2.5](Lemma_2.5.md).

Lemma 2.5. For infinite cardinals $\xi$, $\nu$ and a positive integer $k$, there is an infinite cardinal $R_k(\xi, \nu)$ such that every coloring of the $k$-element subsets of an ordinal of cardinality at least $R_k(\xi, \nu)$ into $\xi$ colors has a homogeneous subset of cardinality $\nu$. Finitely many specified arities can be made homogeneous simultaneously by enlarging the initial cardinal.

For example, the recursion just proved allows $R_{k+1}(\xi, \nu) = (\xi^{R_k(\xi, \nu)})^+$ after increasing the initial $R_1$ as needed.

**[PartitionBound.lean](PartitionBound.lean)**

@import "PartitionBound.lean"
