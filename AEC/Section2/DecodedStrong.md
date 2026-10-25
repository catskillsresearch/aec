# Decoded strong inclusion

From [Lemma 2.2](Lemma_2.2.md).

To recover the strong relation, require a directed presentation $N = \bigcup D$ of this kind and a nonempty directed subfamily $E \subseteq D$ with $M = \bigcup E$. If $M \le_K N$, use $D = D(N)$ and $E = D(M)$; transitivity makes the second a subfamily of the first. In the reverse direction, every member of $E$ is strong in $N$ by the union clause for $D$. The common-upper-bound clause for $E$ then gives $M \le_K N$.

**[DecodedStrong.lean](DecodedStrong.lean)**

@import "DecodedStrong.lean"
