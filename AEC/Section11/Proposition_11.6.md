# Proposition 11.6

Proposition 11.6 (Tiled presentations). Let $L$ be admissible and let $\mu$ be sufficiently large for the pointed pregeometry and the no-proper-pair conclusion. The order template $E$ gives a presentation in $G_L$ as follows. Choose a fixed initial order carrying the whole enumeration of $M_0$. For each active label $t$, choose a tile Tt, preceded by a buffer Bt, and concatenate these finitely many pairs after the initial order, in any fixed order. Every tile and buffer is a dense linear order without endpoints of size $\mu$. In vertex $s$ retain the initial order, all buffers, and just the tiles with labels $t \subseteq s$. These presentations have the following properties.

1. Each active relative piece has rank $\mu$.

2. Order embeddings of the corresponding tiles and buffers, fixing the initial pointed data, induce arrows, including between different eligible levels.

3. A presentation has an extension by an arrow gaining $\mu$ independent complementary coordinates at every active label simultaneously.

4. Tiles may be chosen with $\mu$ pairwise disjoint convex substrips, each of size $\mu$. Further insertions of such substrips preserve the preceding assertions and the naturalness of the underlying $K$-diagrams. No categoricity assumption about $G_L$ is used here.

**[Results.lean](Results.lean)**

@import "Results.lean"
