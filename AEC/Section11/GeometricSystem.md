# Geometric system

From [Definition 11.1](Definition_11.1.md).

A geometric system of shape $L$ is a family $(X_t : t \subseteq A)$ of pointed models in a common top model, with $X_t \le_K X_u$ when $t \subseteq u$, satisfying the following condition. There is a partition $(H_s : s \in L)$ of a basis of $P(X_A)$ such that $H_s \subseteq P(X_s)$ and

$$P(X_t) = \mathrm{cl}_{P(X_A)}\Big(\bigcup_{s \in L,\, s \subseteq t} H_s\Big) \quad (t \subseteq A).$$

At uniform level $\mu$ we require $|H_s| = \mu$ for every $s \in L$. The resulting scheme is denoted $G_L$. The basis partition witnesses the definition; it is not named in the system structure.

For a vertex $t$, write

$$D_t(X) = \mathrm{cl}_{P(X_A)}\Big(\bigcup_{r \subsetneq t} P(X_r)\Big).$$

For $t = \emptyset$ this is the closure of the empty set in the pregeometry. An arrow $X \to Y$ is a commuting family of pointed strong embeddings for which a witnessing partition for $X$ extends to a witnessing partition for $Y$. Equivalently, after identifying $X$ with its image, each finite tuple from $P(X_t)$ independent over $D_t(X)$ remains independent over $D_t(Y)$.

**[GeometricSystem.lean](GeometricSystem.lean)**

@import "GeometricSystem.lean"
