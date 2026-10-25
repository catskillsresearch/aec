# Witnessing chain

From [Definition 7.10](Definition_7.10.md).

A witnessing chain is a continuous chain $(M_i)_{i \le \delta}$ of objects, with $M_0 = A$, such that $b_i$ lies in $M_{i+1}$ and

$$\mathrm{tp}(b_i/M_i) = \mathrm{tp}(b_i/A)^{\mathrm{fr}}_{M_i}.$$

It is an all-dominated-increment chain if, in addition, $M_{i+1}$ is all-dominated over $M_i + b_i$. In uses at level $\mu$, the chain has total size $\mu$, in particular $|\delta| \le \mu$.

**[WitnessingChain.lean](WitnessingChain.lean)**

@import "WitnessingChain.lean"
