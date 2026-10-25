# Working scheme

From [Definition 5.2](Definition_5.2.md).

Definition 5.2 (Working package). Fix an unbounded definable class $S$ of eligible levels, a finite system shape, and a set-sized finite-support term template $F$. A working scheme consists of classes $C_\mu$, for $\mu \in S$, arrows between their objects, and comparisons $D$ of bounded lists, with the following properties. Every vertex of an object in $C_\mu$ has cardinality $\mu$.

1. Structural arrows and unions. Arrows include all structural isomorphisms, compose, and are invariant under isomorphisms. They are coherent: if $X$ is a subsystem of $Y$, and both inclusions into $Z$ are arrows, then $X \to Y$ is an arrow. For an increasing nonempty chain of objects at level $\mu$, whose union has total cardinality $\mu$, the union is an object at that level and the inclusions into it are arrows. If all members of the chain map by the inclusions into one object $Z$ at an eligible level $\nu \ge \mu$, then the inclusion of the union into $Z$ is an arrow.

2. Presentations and mixed downward closure. For every well-order $I$ of eligible cardinality $\mu$, $F(I)$ is an object of $C_\mu$. Its elements are represented by labels applied to finite increasing lists from $I$; equality, the symbols of the system structure, and the specified maps are evaluated from the labels and the finite order and equality patterns. Substitution of positions along an order embedding induces an arrow, including when the source and target levels differ. Every object at a level is isomorphic to a well-ordered presentation. If $\nu \le \mu$ are eligible and $A$ is a set of at most $\nu$ vertex occurrences in an object of level $\mu$, there is an arrow inclusion of an object of level $\nu$ containing $A$. Fixed distinguished data are included in this request.

3. Diagrams, homogeneity, and saturation. For each index set of bounded cardinality there is an equivalence relation, denoted by equality of $D$-diagrams, on the corresponding lists in all eligible objects large enough for that index set. It includes the atomic diagram of the entire coded system, respects restrictions and reindexing, and sends every list to a $D$-equal list under every arrow, including mixed-level arrows. At each level, two bounded lists have the same diagram if and only if a structural isomorphism between their objects takes one list to the other. The number of diagrams at a fixed arity has a set-sized bound independent of the level. A possible joint diagram of bounded length extending the diagram of an actual bounded list is realized over that list at its level. Here "possible" includes a diagram witnessed at any larger eligible level, provided the total requested length is bounded at the receiving level. On term lists diagrams are natural: they depend only on labels and the order and equality pattern of all positions used, including in comparisons between eligible levels.

4. Exhaustion criterion for arrows. Suppose a map is obtained from compatible diagram matches on increasing bounded lists which exhaust its domain object. Include in these lists, for every vertex $V$, nested enumerations of strong submodels $V_n \le_K V$ of sizes below the source level, with union $V$. The image of each such enumeration must enumerate a strong submodel of the corresponding target vertex. Under these conditions the map is an arrow. Component strongness follows from the chain union and common-upper-bound axioms of $K$; an additional arrow condition, when present, must be proved for this construction separately.

The empty list is included in the third condition, and has one diagram. Consequently all objects at any one eligible level are isomorphic.

**[WorkingScheme.lean](WorkingScheme.lean)**

@import "WorkingScheme.lean"
