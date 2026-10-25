# Marked pair

From [Definition 8.1](Definition_8.1.md).

An object of $C_b$ at level $\mu$ is a triple

$$(X, Y, b), \qquad X \le Y,$$

where $X, Y$ are objects of $C$ at level $\mu$, $b \in Y$ realizes $p_X$, and $Y$ is all-dominated over $X + b$. The inclusions and the mark are part of the structure. An arrow is a commuting pair of componentwise strong embeddings taking the mark to the mark. The notation $X \le Y$ records an actual inclusion; arbitrary arrows are put into this form by replacing the codomain with an isomorphic copy.

Recall that all-domination quantifies over every tuple of length strictly below the level. It is not just domination for the members of one fixed exhaustion of $Y$.

**[MarkedPair.lean](MarkedPair.lean)**

@import "MarkedPair.lean"
