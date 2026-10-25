# 12 Exact isomorphisms of geometric systems


We continue with the pointed pregeometry of Theorem 10.5, above the threshold of Corollary 10.10. A shape and its active labels have the meaning of Definition 11.1. Unless otherwise stated, every active basis piece in this section has cardinality equal to the uniform level µ. The bases remain auxiliary choices.

Definition 12.1 (A prescribed boundary isomorphism). Let a be a finite ordered set of axes, and let$X^{−} = (X_{s^{−}}: s ⊆$a) and$X^{+} = (X_{s^{+}}: s ⊆$a) be systems of the same shape. A prescribed boundary isomorphism is a family

$h_{s}: X_{s^{−}} −→ X_{s^{+}}$(s ⊊ a)

of pointed isomorphisms such that$h_{t}$↾$X_{s^{−}} = h_{s}$whenever s ⊆ t ⊊ a. This condition refers to the displayed inclusions. It does not add an assumption about intersections of two incomparable vertices inside the top.

A list on the boundary can consequently be specified by assigning a proper face to each of its occurrences. Before consistency on actual intersections has been proved, its prescribed image means the list obtained by applying the corresponding$h_{s}$to each occurrence. In particular, the assertion that two occurrences name the same element is one of the atomic comparisons that must be preserved.

Theorem 12.2 (Exact geometric boundary lifting). For every finite allowed shape, at all sufficiently closed uniform levels, every prescribed boundary isomorphism between two systems of that shape extends to a pointed isomorphism of their tops. The top isomorphism, together with its prescribed restrictions, is an isomorphism of the systems.

The refinements of the eligible levels needed for a fixed shape use only the one-dimensional bounds for its working scheme, the bounds for its tiling layouts, and the corresponding assertions for shapes on fewer axes. In particular these refinements have the uniformity specified in Section 13.

We prove the theorem by induction on the number of axes. At zero axes it is pointed categoricity. The induction at a positive number of axes has two parts: preserving the joint diagrams of the entire boundary, and realizing successive extensions of a partial match inside the given target. The first part supplies, among other things, the missing compatibility on actual intersections.

Lemma 12.3 (Joint boundary comparisons). Assume exact geometric boundary lifting for all allowed shapes on fewer than n axes. At a sufficiently closed uniform level, a prescribed boundary isomorphism between two n-axis systems preserves the bounded K-diagram of every occurrence-tagged boundary list, computed in the respective top models.

Proof. If the top label is inactive, let u be the largest active label. It is a proper subset of the axis set, and the top vertex is$X_{u}.$Every vertex is the vertex at its largest active lower label, which is contained in u. Thus the map at u already gives all the comparisons in question. We may assume the top label is active.

Write the axis set as a ∪ {k}, with k last and |a| = n − 1. Splitting off k writes the two systems as$X^{−} −→ Y^{−}, X^{+} −→ Y^{+}$

in the scheme$G_{L}$on a. Its categoricity is supplied by Theorem 11.9; after refining the levels, Proposition 11.7 supplies its working package. The arrows add rank µ at the labels in a fixed upward closed Q ⊆ L and add no rank at the other labels. Call such a step a step of shape Q. The boundary prescription gives a full system isomorphism e:$X^{−} ≃ X^{+}$and compatible isomorphisms

$h_{s}: Y_{s^{−}} ≃ Y_{s^{+}}$(s ⊊ a)

whose restrictions to$X_{s^{−}}$agree with e.

If joint comparison fails, choose bounded lists f from$X^{−}$and$d^{−}$from the proper vertices of$Y^{−}$witnessing failure, and put$d^{+} = h(d^{−}).$All occurrences from the lower layer may be included in f; all the remaining occurrences lie in these upper proper vertices. The comparisons of

(f,$d^{−})$in$Y^{−}$and (e(f),$d^{+})$in$Y^{+}$(13)

differ. The notation in (13) includes the indicated vertex occurrences. If there is no upper test$d^{−},$the base isomorphism and the strong arrows already give equality, so this case cannot witness failure.

A system isomorphism matching these lists would in particular be a K-isomorphism of the tops matching them. Hence the working$G_{L}$-diagrams of the lists in (13) also differ. Choose an infinite cardinal σ < µ bounding the lengths of the lists. Enlarge a cardinal χ < µ so that$χ^{σ} =$χ, it bounds the relevant labels and parameter-orbit constants, so that Lemma 6.1 gives at most χ orbits of σ-lists over χ parameters. Choose µ closed far enough that all the following tree costs are below it. Let ϵ be the least infinite cardinal with$2^{ϵ} >$χ. There are at most χ nodes below height ϵ, and$2^{ϵ} <$µ leaves.

We construct a binary tree of branch worlds$C_{η}$in$G_{L},$for η ∈ ≤ϵ2, and a single increasing

reference chain$(R_{i}: i ≤$ϵ) in that scheme. All these objects have level µ. A branch world carries a copy$f_{η}$of f. For every node η of length i the invariant also includes a prescribed isomorphism

$b_{η}: ∂C_{η} ≃ ∂R_{i}.$(14)

Along a branch, these boundary maps commute with the inclusions into later branch and reference worlds. At each splitting node, the two new copies of its upper test d have the same image in the next reference boundary. Those images will be retained at all later stages.

Start with$C_{∅} = R_{0} = X^{−}$and the identity boundary map. Suppose the objects at level i have been constructed. Choose a reference step$R_{i} → R_{i+1}$of shape Q. Such a step exists: categoricity of$G_{L}$identifies$R_{i}$with$X^{−},$and we transport the given extension$X^{−} → Y^{−}$along that identification.

i

For each η ∈ 2, an isomorphism$X^{−} ≃ C_{η}$can be chosen to take f to$f_{η}.$Indeed arrows along

the branch preserve its bounded diagram, and equality of bounded diagrams in the working scheme is implemented by an isomorphism. Transport the minus and plus extensions along this return isomorphism, using e on the plus base. They give children$C_{η^{⌢_{0}}}$and$C_{η^{⌢_{1}}}$over$C_{η},$with opposite comparisons to$f_{η}$and with the given identification between their proper upper vertices. On their lower proper vertices that identification is the identity of the current branch world.

It remains to extend (14) to the children; merely choosing arbitrary isomorphisms of the new worlds would not suffice. First do this for the plus child. Process all proper subsets s ⊊ a in increasing cardinality. Consider the restriction of the plus step to the axes s ∪ {k} and the corresponding restriction of$R_{i} → R_{i+1}.$On the base vertex, the prescribed map is$(b_{η})_{s}.$On every other proper vertex it is either a restriction of that map or one of the upper maps already constructed at a proper subset of s. These maps commute on all indicated subfaces by construction. The restriction has at most n − 1 axes, so the induction hypothesis lifts this boundary prescription onto its upper vertex. This supplies the map at s, whether that vertex is active or repeated from a smaller active one. The resulting family is the required plus boundary map. Compose it with the given minus-to-plus boundary identification to obtain the minus boundary map. Both extend$b_{η},$and the two copies of the test have equal reference images.

At a limit i ≤ ϵ, take unions along each branch and in the reference chain. The lower-dimensional working scheme has the chain and common-upper-bound properties, and these unions have size µ. The coherent boundary maps have unions which are onto the reference boundary: each previous reference vertex was already the image of the corresponding branch vertex. Thus the invariant persists. No assertion that a limit inclusion is itself a step of shape Q is needed. At its next successor stage a fresh step of that shape is available over the union by categoricity.

At a leaf, apply the induction hypothesis once more, this time to the (n − 1)-axis worlds$C_{η}$and$R_{ϵ},$with the boundary prescription$b_{η}.$Obtain a full isomorphism$j_{η}: C_{η} ≃ R_{ϵ}.$Let A be the list of all reference images of the splitting tests. Its length is at most χ, since there were at most χ splitting nodes and each test had length at most σ.

For two different leaves, use their first splitting node. The associated test has the same image in A on both branches, whereas its comparison with the images of f is opposite. Arrow preservation of diagrams carries this distinction to the leaves, and$j_{η}$preserves it in$R_{ϵ}.$Consequently the$2^{ϵ}$lists$j_{η} (f_{η})$lie in different orbits over A. This contradicts the bound χ. Joint boundary comparison follows.

Remark 12.4. The proof just given applies to equalities between occurrences from incomparable faces. It therefore proves that the prescribed maps have a well-defined injective union on the actual union of the boundary vertices. Applying the same observation to the inverse family proves that this union is a bijection between the two boundary unions. Equality of actual intersections was not an input to the argument.

The boundary prescription now respects actual intersections and all bounded joint diagrams. The remaining task is to extend a bounded match inside the prescribed target. We first establish testing for its tiled boundary layout, then use a strip avoided by all boundary supports to realize the resulting comparison without enlarging that target.

Lemma 12.5 (Testing on rationally tiled parameter orders). Fix the finite-support order template E and its natural stabilized K-diagrams. Fix a nonempty set-sized initial order$J_{0},$finitely many tile labels i < m, and a finite family A of subsets of m. These are fixed descriptor data. For well-orders$H_{i},$put

$J = J_{0} +$i<mX$(H_{i} ×$Q),

with lexicographic order on each product. For A ∈ A, let$J_{A}$consist of$J_{0}$and the tiles whose labels belong to A. Let B be the union of the designated term sets$E(J_{A}),$with the term representations inherited from E. Occurrences may retain their designated-part tags.

There is a monotone cardinal bound$g_{A}$(σ, τ), depending also on E and$J_{0},$with the following property whenever |J| = µ and µ is a sufficiently closed level above the input cardinals,$|J_{0} |,$and this bound. Let c be a fixed tuple in E(J) of length at most τ, with fixed term representations. Two placements of tuples of length at most σ in arbitrary order enlargements of J have the same comparison over B together with the fixed tuple c if they agree on every parameter query from B of size at most$g_{A}$(σ, τ), with c retained as fixed data. Here σ and τ may be increased to infinite cardinals. The bound is independent of the horizontal order lengths and of µ, and is uniform over a fixed set of descriptors of bounded hereditary size. The candidate placements need not be terms of a horizontal reindexing of the tiled template.

Proof. Amalgamate the two supporting order enlargements over J and discard all added positions not supporting either candidate. Let T be the union of the supporting positions of the two candidates and the chosen old supports of c. Put

ζ = max σ, τ,$|J_{0} |,$|E|,$ℵ_{0}.$

Thus |T | ≤ ζ. A fiber means the old convex copy {h} × Q at a horizontal position in some$H_{i}.$Call an old fiber exceptional if it contains a position of T, or if some added position of T \ J has old fiber positions strictly below and strictly above it. Each position of T hits or splits at most one old fiber: two distinct fibers are disjoint convex suborders. Hence at most ζ fibers are exceptional.

Freeze the entire initial order$J_{0},$every rational position of every exceptional fiber, and all positions of T. The resulting ordered set F has cardinality at most ζ, since every fiber is countable. Also freeze the following record: which positions of F are old, the tile label and rational coordinate of each old position in an exceptional fiber, the exceptional-fiber grouping, the labels and supporting lists of both candidates and c, and all order comparisons and equalities among these positions. The fixed copy of$J_{0}$is retained literally. Up to renaming the other positions on a set of size at most ζ, these records form a set. In particular, arbitrary cuts made by added supports within a rational fiber are part of this bounded record; those supports have not been replaced by horizontal-template terms.

Every nonexceptional old fiber lies wholly in one strict cut of F: it contains no point of F, no candidate support splits it, and distinct exceptional fibers are convex and disjoint from it. For each tile label i and strict cut u of F, record the ordinal length$α_{i,u}$of the horizontal positions of nonexceptional fibers of tile i lying in that cut. These positions form an interval of the well-order$H_{i}.$There is a set of coordinates (i, u); the set of cuts can have cardinality as large as$2^{|F|},$which still has a bound depending only on ζ. We do not assume that the supporting order T, or the set of its cuts, is discrete or well-ordered.

For a fixed frozen record, retain only ordinal vectors giving valid configurations of the displayed tiled form. The vector and frozen record determine the parameter order and both candidate support patterns up to the specified order identifications. If two valid vectors satisfy$α_{i,u} ≤ β_{i,u}$at every coordinate, embed the shorter ordinal interval into the longer one at each coordinate, and send each full rational fiber by the identity on its rational coordinate. Together with the identity on F, these maps give an order embedding of the two configurations, fixing the candidate supports and the old frozen data. Every old position stays in its tile, and$J_{0}$stays fixed. Consequently a designated term remains a term of the same designated part$E(J_{A}),$with the same occurrence tag. Naturality of the stabilized K-diagrams preserves each joint diagram comparison under this embedding.

Consider the definable class of valid vectors for which the two candidate comparisons differ on some parameter query. Diagrams on any particular set-sized query can be evaluated in a sufficiently large eligible padded presentation, as in Proposition 4.8. Thus this is a first-order definable class with the fixed record as a set parameter. Apply Lemma 4.7 to obtain a set of valid unequal vectors such that every valid unequal vector dominates one of them. No assertion that an arbitrary ordinal vector describes a valid horizontal well-order is needed. Coordinatewise domination between the two valid configurations gives the embedding just constructed, so the query witnessing inequality in the smaller configuration still witnesses inequality after that embedding.

The old parameter orders in this set of witnesses have a common cardinal bound. The number of designated finite-support terms on one such order is at most its cardinality plus |E|$+ ℵ_{0}.$Bound this cardinal over the set of witnesses and then over the set of frozen records. An unequal comparison in any valid configuration therefore differs on a designated parameter query of at most that bounded cardinality, retaining c as fixed data. Increase the bound to dominate the input cardinals and take monotone majorants in σ and τ. This defines the required$g_{A}$independently of the level. Taking the same supremum over a fixed set of bounded descriptors proves the last uniformity assertion.

We next record the realization step, with its support calculation explicit. A permitted parameter layout means either a natural layout covered by Proposition 6.3 or a rationally tiled designated-part layout covered by Lemma 12.5. A bounded list of additional fixed parameters is allowed in either case. A testing bound for a permitted layout will always mean the bound supplied by the corresponding one of these two results.

Lemma 12.6 (Realization using an unoccupied strip). Let E(J) be a pointed K-presentation of cardinality µ at a sufficiently closed uniform level. Let V ⊆ J be a convex substrip of cardinality µ. Let B ⊆ E(J) be a permitted parameter layout, with chosen representations of all its entries using positions in J \ V. Include the fixed point data among these represented parameters.

Suppose a bounded tuple$z^{∗}$in a presentation$E(J^{∗}),$where$J ⊆ J^{∗},$has a placed comparison over B. Then a tuple z of E(J) has the same comparison over every bounded list from B. Any specified bounded old entries of$z^{∗}$are retained as actual entries of z, provided their chosen representations avoid V.

Proof. Shrink$J^{∗}$to J together with supports for$z^{∗},$so its cardinality is still µ. Include the old entries to be retained in the tuple under consideration and in the bounded fixed data of the layout. Choose a bounded test cardinal χ < µ at least the tuple length and the testing bound for this permitted layout. Let$T^{∗}$be the chosen supporting positions of$z^{∗}$in$J^{∗}.$For the invocation of Lemma 6.14, replace V by its convex hull in$J^{∗}.$Since V is convex in J, this hull meets J in exactly V. Thus its old complement is still J \ V, and the side of this convex hull on the old complement is the side of the original strip. The support-closure lemma therefore has the required convex strip in the ambient order; the actual realization still uses E(S ∪ V). By Lemma 6.14, there is a bounded S ⊆ J \ V containing the supports of the fixed old entries and the point such that the following holds. Given a list Q of at most χ positions in J \ V and at most χ positions R in S, one can move Q to a list in S, preserving all order comparisons and equalities relative to R and$T^{∗},$as well as its side of V.

For completeness, the size requirement on this use of support closure is bounded independently of µ. If λ < µ bounds χ, the initial supports, and$T^{∗},$the witnesses can be chosen through$χ^{+}$stages inside a set of size at most$2^{λ}.$At each stage there are at most$2^{λ}$realized requests over at most χ old positions, since$(2^{λ})^{χ} = 2^{λ}.$Every at-most-χ subset of the union occurs at an earlier stage. Strong-limit closure keeps the resulting set S below µ.

The subpresentation E(S ∪ V) is a strong submodel of E(J) and has cardinality µ. The complete list of elements generated by S is bounded, since the number of labels and |S| are below µ. Saturation for bounded K-diagrams in E(S ∪ V) therefore realizes the joint diagram of$z^{∗}$with this entire list, producing z. The diagram on that parameter list is the same in both presentations by naturalness. Equalities to its entries preserve the specified old assignments.

Choose representations of z using positions T ⊆ S ∪ V. Let q be a test of at most χ parameters from B, with its chosen supports Q ⊆ J \ V. Apply support closure with R = T ∩ S; this set has size at most χ. It gives a moved parameter list q' whose terms use only S. The joint order pattern of the supports of (z, q) agrees with that of (z, q'): comparisons to T ∩ S are retained, and comparisons to T ∩ V are forced by the retained side of the convex strip. The pattern of$(z^{∗},$q) likewise agrees with that of$(z^{∗},$q'), because comparisons with$T^{∗}$were retained. Naturality and the diagram chosen in E(S ∪ V) give

$D^{K}$(z, q)$= D^{K}$(z, q')$= D^{K} (z^{∗},$q')$= D^{K} (z^{∗},$q).

Here q' need not belong to B: all terms on S were included in the saturation request. This proves equality on tests of size at most χ. Both tuples have placed comparisons over the original permitted layout, so its testing bound gives equality on every bounded test, as asserted.

Proof of Theorem 12.2. Continue the induction on the number of axes. The zero-axis and inactive-top cases were addressed above. Suppose the top is active and exact lifting is available on fewer axes. Refine the uniform levels for Lemma 12.3, the working packages, and the indicated one-dimensional layout bounds. The compatible face maps have a bijective union h:$B^{−} → B^{+}$preserving all bounded joint K-diagrams in the tops.

Use Proposition 11.6 and geometric categoricity to present the two systems by tiled presentations. Choose each tile and buffer as$H_{i} ×$Q, where$H_{i}$is a well-order of cardinality µ. In the top-only tile choose$H_{i}$of order type µ · µ; its µ consecutive intervals of order type µ give pairwise disjoint convex substrips of cardinality µ. Every proper face is generated on the fixed point positions, all buffers, and its designated tiles, so its chosen representations omit the top-only tile. The finite family of these designated parts is exactly a parameter layout covered by Lemma 12.5. That lemma also allows the bounded old matched tuple as fixed data. Use its testing bound for this layout in the following placement and realization arguments.

Construct nested bounded tuple matches in alternating directions. The invariant for a match$a^{−}$7→$a^{+}$is

$D^{K} (a^{−},$b)$= D^{K} (a^{+},$h(b)) for every bounded occurrence-tagged b in$B^{−}.$(15)

It includes the equality comparisons needed for a partial injection, and initially holds with the empty tuple by Lemma 12.3.

For a forward step, enlarge$a^{−}$to a requested bounded tuple$v^{−}$in the source top. Prescribe its joint comparisons with$B^{+}$by transport along h, and prescribe the actual values$a^{+}$for the old coordinates. Every bounded local request is possible in the target top. To see this, collect all its boundary parameters into one bounded list. The invariant matches that list jointly with$a^{−}.$

Bounded diagram homogeneity, or the equivalent saturation clause, then realizes the requested extension$v^{−}$over its target copy and the actual old tuple.

Apply Lemma 6.4 to the chosen boundary parameter set, keeping the old tuple fixed. The underlying E-order need not be well-ordered, so use its padded-order clause with the coherent locally possible prescriptions on every bounded subset. For each bounded desired test size, closure under the full profile-count recursion in that lemma supplies a placement in an enlargement of this E-order realizing all prescriptions through that size. Choose the test size at least the bound from Lemma 12.5, including the old tuple as fixed data. Any two such outputs agree on that bound, so the lemma identifies their full placed comparisons. Fix one output. For any bounded query choose another output at a test size including that query; their equality proves that the fixed output also has the prescribed value there. Thus a bounded tuple$v^{∗}$has the required placed comparison on every bounded query, with the previous coordinate equalities included. These are actual placements in arbitrary enlargements of the E-order; no horizontal-term representation of their new supports is assumed.

All boundary supports avoid the top-only tile, and the old matched tuple has boundedly many supporting positions. Some convex substrip of cardinality µ in that tile avoids those positions as well. Apply Lemma 12.6 to this substrip. It realizes the placed comparison by a tuple$v^{+}$inside the actual target, retaining$a^{+}$and satisfying (15) for the larger tuple. This completes the forward step. Interchanging the two systems and using$h^{−1}$gives the backward step with the same invariant.

Since cf(µ)$= ℵ_{0},$choose countable bounded exhaustions of both tops and alternate these two steps so that both are covered. Include in the requested tuples the enumerations of smaller strong submodels used in the working-package map criterion. The union map is onto and preserves every atomic formula and its negation, because any finite tuple occurs in a stage. It is therefore a K-isomorphism of the tops; the same map criterion also supplies strongness directly. Equality tests in (15) show that its restriction to each proper face is the prescribed$h_{s}.$It is consequently an isomorphism of the whole geometric systems.

For a fixed finite shape the dimension induction used only its finitely many proper restrictions. The remaining refinements were the uniform arity bounds for working diagrams, the fixed tiling layouts, support closure, and the bounded tree costs. These are the finite recipes recorded in Section 13, establishing the last assertion of the theorem.
