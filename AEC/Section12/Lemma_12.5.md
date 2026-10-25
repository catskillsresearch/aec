# Lemma 12.5

Lemma 12.5 (Testing on rationally tiled parameter orders). Fix the finite-support order template $E$ and its natural stabilized $K$-diagrams. Fix a nonempty set-sized initial order $J_0$, finitely many tile labels $i < m$, and a finite family $A$ of subsets of $m$. These are fixed descriptor data. For

well-orders $H_i$, put

$$
J = J_0 + \sum_{i<m}(H_i \times \mathbb{Q}),
$$

with lexicographic order on each product. For $A \in A$, let $J_A$ consist of $J_0$ and the tiles whose labels belong to $A$. Let $B$ be the union of the designated term sets $E(J_A)$, with the term representations inherited from $E$. Occurrences may retain their designated-part tags. There is a monotone cardinal bound $g_A(\sigma, \tau)$, depending also on $E$ and $J_0$, with the following property whenever $|J| = \mu$ and $\mu$ is a sufficiently closed level above the input cardinals, $|J_0|$, and this bound. Let $c$ be a fixed tuple in $E(J)$ of length at most $\tau$, with fixed term representations. Two placements of tuples of length at most $\sigma$ in arbitrary order enlargements of $J$ have the same comparison over $B$ together with the fixed tuple $c$ if they agree on every parameter query from $B$ of size at most $g_A(\sigma, \tau)$, with $c$ retained as fixed data. Here $\sigma$ and $\tau$ may be increased to infinite cardinals. The bound is independent of the horizontal order lengths and of $\mu$, and is uniform over a fixed set of descriptors of bounded hereditary size. The candidate placements need not be terms of a horizontal reindexing of the tiled template.

**[Results.lean](Results.lean)**

@import "Results.lean"
