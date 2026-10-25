# Relative isolation

From [Definition 7.1](Definition_7.1.md).

Definition 7.1. Let $q = \mathrm{tp}(u, c/A)$ and $p = \mathrm{tp}(u/A)$, where the concatenation $(u, c)$ is bounded. We say that $q$ is isolated relative to $u$ if there is a bounded set $Z \subseteq A$ such that, for every $q' = \mathrm{tp}(u', c'/A)$,

$$\mathrm{tp}(u'/A) = p \text{ and } D(u', c', Z) = D(u, c, Z) \implies q' = q.$$

Here and below a parameter set in a diagram is supplied with a fixed enumeration, and the same enumeration is used on both sides. We call $Z$ an isolating fragment. A projection retains the entire tuple $u$ unless explicitly stated otherwise.

**[RelativeIsolation.lean](RelativeIsolation.lean)**

@import "RelativeIsolation.lean"
