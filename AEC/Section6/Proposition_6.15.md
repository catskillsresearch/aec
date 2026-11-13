# Proposition 6.15

Proposition 6.15 (Universality of a fresh strip). Let $C$ already satisfy the working package. In addition to its fixed template $F$, one may use a presentation $G$ with the following properties: it has a fixed set of finite-support labels; every presentation $G(J)$ used below, for an order of size $\mu$, is an object of $C$ at level $\mu$; order embeddings give $C$-arrows; and the diagrams of its term lists are natural, including in the order enlargements and padded orders used. Assume also that these labels represent every element of $G(J)$. Require $\mu$ to exceed the cardinality of the label set of $G$ and to be closed under the bounds below with that cardinal included in their fixed input data. Put $A = G(J)$. Insert into $J$ a fresh convex strip of size $\mu$ with countably many disjoint convex substrips, each of size $\mu$, and denote the resulting object by $A^+$. Then every same-level extension of $A$ embeds into $A^+$ over $A$. In particular this applies to $G = F$ and to well-ordered presentations. No separate union or categoricity assertion for a category of $G$-presentations is required.

**Done** for a terminal strip with `G = P.E` on a well-ordered `J` ([`FreshStrip.lean`](FreshStrip.lean), wired in [`Results.lean`](Results.lean)). The tail is closed for every length below `μ`. `lemma_6_14` is widened to χ-indexed queries plus a fixed `T★`, and the exhaustion uses Theorem 6.6 amalgamation (`ClosedLevel.exists_tuple_amalgam`) one fiber at a time. No `HasChainUnions` and no use of Proposition 6.13 (that paper-number edge is soft).

**Deferred.** A general presentation `G ≠ F`, and two-sided strips. Both are what Corollary 6.16 needs, so 6.16 and 6.17 stay blocked.

**[Results.lean](Results.lean)**

@import "Results.lean"
