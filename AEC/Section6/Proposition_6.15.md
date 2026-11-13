# Proposition 6.15

Proposition 6.15 (Universality of a fresh strip). Let $C$ already satisfy the working package. In addition to its fixed template $F$, one may use a presentation $G$ with the following properties: it has a fixed set of finite-support labels; every presentation $G(J)$ used below, for an order of size $\mu$, is an object of $C$ at level $\mu$; order embeddings give $C$-arrows; and the diagrams of its term lists are natural, including in the order enlargements and padded orders used. Assume also that these labels represent every element of $G(J)$. Require $\mu$ to exceed the cardinality of the label set of $G$ and to be closed under the bounds below with that cardinal included in their fixed input data. Put $A = G(J)$. Insert into $J$ a fresh convex strip of size $\mu$ with countably many disjoint convex substrips, each of size $\mu$, and denote the resulting object by $A^+$. Then every same-level extension of $A$ embeds into $A^+$ over $A$. In particular this applies to $G = F$ and to well-ordered presentations. No separate union or categoricity assertion for a category of $G$-presentations is required.

**Done** for `G = P.E` ([`FreshStrip.lean`](FreshStrip.lean), wired in [`Results.lean`](Results.lean)). A cut of `J` inserts `ℕ ×ₗ lvlOrder μ` so old points lie on both sides. The strip splits into countably many convex μ-fibers. Side-of-cut color is passed to Lemma 6.14 and used when a realized support sits in the fresh fiber. The exhaustion embeds every same-level strong extension of `E(J)` into `E(J⁺)` over `E.map emb`. The one-sided enlargement is **`infra_615_terminal`**, not this theorem. General `G ≠ P.E` is out of scope. Corollary 6.16 and Lemma 6.17 are done. **Next tip:** Lemma 7.2.

**[Results.lean](Results.lean)**

@import "Results.lean"
