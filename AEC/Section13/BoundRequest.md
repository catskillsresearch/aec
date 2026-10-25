# Bound request

From [13.2 A fixed register of bound requests](13.2.md).

In this notation $q$ belongs to the finite register below. The notation does not permit an arbitrary formula as a value of $q$, or an arbitrary class as a parameter $S$.

For a bound request with ordinal input $\alpha$ and descriptor $d$, write

$$B_q(d, \alpha; S) = \begin{cases} \text{the least ordinal satisfying the request, if such an ordinal exists,} \\ 0, \text{ otherwise.} \end{cases}$$

**[CommonMajorant.lean](CommonMajorant.lean)**

@import "CommonMajorant.lean"
