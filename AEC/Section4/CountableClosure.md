# Closure point

From [Proposition 4.3](Proposition_4.3.md).

Proposition 4.3 (Categoricity at countably cofinal closure points). Suppose $\zeta > \ell$ is an infinite cardinal of countable cofinality and

$$t(\sigma) < \zeta \quad \text{for every infinite } \sigma < \zeta.$$

Then $K$ is categorical in $\zeta$. Moreover any diagram match between bounded tuples in two $\zeta$-models extends to an isomorphism between those models. Here and throughout the paper, bounded at a level means of cardinality strictly less than that level.

The closure cardinals in Proposition 4.3 are unbounded. For example, starting above any specified cardinal, choose a strictly increasing sequence $(\alpha_n : n < \omega)$ such that $\alpha_{n+1}$ exceeds all $t(\sigma)$ for $\sigma \le \alpha_n$. Its supremum has the required closure and countable cofinality. Including $2^{\alpha_n}$ in these requirements makes the supremum a strong limit. We will use these stronger closure points below.

**[CountableClosure.lean](CountableClosure.lean)**

@import "CountableClosure.lean"
