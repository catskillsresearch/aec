# Pattern code

From [5.6 A set-theoretic code for diagram equality](5.6.md).

For an arity bound $\sigma$, a pattern records an indexed list of labels, finite increasing support lists for them, and the order on the union of these supports. Use canonical support universes of cardinality at most $\sigma$ and index sets of cardinality at most $\sigma$. These codes form a set, denoted by $P_F(\sigma)$. Two codes representing the same terms need not be identified in advance.

**[PatternCode.lean](PatternCode.lean)**

@import "PatternCode.lean"
