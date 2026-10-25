# All-dominated

From [Definition 7.4](Definition_7.4.md).

Definition 7.4. Let $X \le Y$ be same-level objects and let $b$ be a bounded tuple in $Y$. We say that $Y$ is all-dominated over $X + b$ if, for every bounded tuple $c$ from $Y$, the type $\mathrm{tp}(b, c/X)$ is isolated relative to $b$.

The quantifier over all bounded tuples is part of this definition. It is not enough to verify isolation for individual entries, or for the tuples in one chosen countable exhaustion of $Y$.

**[AllDominated.lean](AllDominated.lean)**

@import "AllDominated.lean"
