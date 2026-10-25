# Working-package clauses

From [Definition 5.2](Definition_5.2.md).

1. Structural arrows and unions. For an increasing nonempty chain of objects at level $\mu$, whose union has total cardinality $\mu$, the union is an object at that level and the inclusions into it are arrows. If all members of the chain map by the inclusions into one object $Z$ at an eligible level $\nu \ge \mu$, then the inclusion of the union into $Z$ is an arrow.

2. Presentations and mixed downward closure. If $\nu \le \mu$ are eligible and $A$ is a set of at most $\nu$ vertex occurrences in an object of level $\mu$, there is an arrow inclusion of an object of level $\nu$ containing $A$.

3. Diagrams, homogeneity, and saturation. A possible joint diagram of bounded length extending the diagram of an actual bounded list is realized over that list at its level. Here "possible" includes a diagram witnessed at any larger eligible level, provided the total requested length is bounded at the receiving level.

4. Exhaustion criterion for arrows. Suppose a map is obtained from compatible diagram matches on increasing bounded lists which exhaust its domain object. Include in these lists, for every vertex $V$, nested enumerations of strong submodels $V_n \le_K V$ of sizes below the source level, with union $V$. The image of each such enumeration must enumerate a strong submodel of the corresponding target vertex. Under these conditions the map is an arrow.

**[PackageClauses.lean](PackageClauses.lean)**

@import "PackageClauses.lean"
