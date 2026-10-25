# Reversal

From [Theorem 3.11](Theorem_3.11.md).

Theorem 3.11 (Eventual reversal at categoricity cardinals). For each infinite cardinal $\theta$ there is a cardinal $b_K(\theta)$ such that, whenever $\kappa \ge b_K(\theta)$ is a categoricity cardinal, $M \in K$ has size $\kappa$, $f : M \to M$ is strong, and $\bar a$ is a tuple of length at most $\theta$ in $M$, there is a strong $g : M \to M$ with

$$g(f(a_i)) = a_i \text{ for every coordinate } i.$$

The bound concerns all sufficiently large categoricity cardinals, of arbitrary cofinality. No equality of the form $\kappa^\theta = \kappa$ is assumed.

**[Reversal.lean](Reversal.lean)**

@import "Reversal.lean"
