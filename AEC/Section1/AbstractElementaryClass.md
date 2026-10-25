# Abstract elementary class

From [Definition 1.1](Definition_1.1.md).

Definition 1.1 (Abstract elementary class). An abstract elementary class (AEC) is a pair $K = (C, \le_K)$, where $C$ is a class of structures in a fixed language $\tau$ and $\le_K$ is a partial order satisfying the following conditions.

(1) The class is closed under isomorphism. If $M \le_K N$, then $M$ is a $\tau$-substructure of $N$. If $f : N \cong N'$ and $M \le_K N$, then $f[M] \le_K N'$.

(2) Coherence: if $M_0$ is a $\tau$-substructure of $M_1$, and $M_0 \le_K M_2$ and $M_1 \le_K M_2$, then $M_0 \le_K M_1$.

(3) For every nonzero ordinal $\delta$ and increasing chain $(M_i : i < \delta)$ under $\le_K$, its union $U$ belongs to $C$ and $M_i \le_K U$ for all $i < \delta$. If also $M_i \le_K N$ for every $i$, then $U \le_K N$.

(4) There is an infinite cardinal $\ell \ge |\tau| + \aleph_0$ such that, for every $M \in C$ and $A \subseteq |M|$, there is $N \le_K M$ with $A \subseteq |N|$ and $\|N\| \le |A| + \ell$.

The least possible $\ell$ is denoted $\mathrm{LS}(K)$. A strong map is an isomorphism onto a strong substructure of its codomain. The class is categorical in $\kappa$ if it has a model of cardinality $\kappa$ and all its models of that cardinality are isomorphic.

The chain axioms equivalently give unions and the common-upper-bound clause for nonempty set-indexed directed systems of strong inclusions. We also use the corresponding direct limits of coherent strong maps, obtained by renaming their injective images. No intersection axiom is included.

**[AbstractElementaryClass.lean](AbstractElementaryClass.lean)**

@import "AbstractElementaryClass.lean"
