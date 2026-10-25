# Forces

From [Definition 10.3](Definition_10.3.md).

We give a precise meaning to the containment test used in constructing closure. Fix a finite configuration $F \cup \{x\} \subseteq P(M)$ and a size-$\lambda_0$ section $N$ containing it and $M_0$. Say that $F$ forces $x$ if, whenever $f : N \to W$ is a strong embedding fixing $M_0$, with $W$ of size $\lambda_0$, and $M_0 \le_K D \le_K W$ has size $\lambda_0$ and contains $f[F]$, one has $f(x) \in D$. Thus the test permits a common extension of the finite configuration and the proposed model; it does not presume that intersections of strong models are strong models.

**[Forces.lean](Forces.lean)**

@import "Forces.lean"
