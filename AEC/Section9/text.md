# 9 Finite iteration and exact boundary maps


We work with schemes whose arrows are componentwise strong system embeddings, preserving the specified distinguished data. All levels in this section are eligible strong limit cardinals of countable cofinality. The additional closure requirements below are imposed for each fixed finite iteration depth. A common choice for all finite depths will be made separately in Theorem 13.5. Unboundedness after the refinements, including the supply of smaller completion levels for exact lifting, uses the eligible-subclass hypothesis of Convention 5.3. In the finite marked application, Section 13 verifies this hypothesis by maintaining containment of$G_{j}$for some finite j, in the hierarchy previewed in Section 5.

Completion and uniqueness for finite systems are central in multidimensional independence. Shelah developed dimension-raising existence and uniqueness methods in [She83, Sections 3– 5]; compare the distinction between extension, uniqueness, and strong uniqueness in [SV24, Definition 8.16]. Here amalgamated completion and extension onto the prescribed target are proved separately.

## 9.1 Forgetting components and recovering types

Iteration requires more than forgetting vertices of an object: a type prescribed in the root must determine a unique type over the entire system. The following correspondence supplies that requirement and shows that it is compatible with free lifting.

Proposition 9.1 (Type correspondence under projection). Let P: C −→ D forget some components of systems. Suppose that both schemes satisfy the working package, that P takes objects and arrows to objects and arrows, including mixed arrows, and that the following diagram comparison holds: for bounded tuples in the retained sorts, equality of their C-diagrams is equivalent to equality of their D-diagrams after projection. The comparisons are made at arities bounded at both levels when levels differ.

At sufficiently closed levels, restriction induces a bijection on types of bounded tuples in any fixed list of retained sorts, given by

$tp_{C}$(v/X) 7−→$tp_{D}$(v/P X).

The parameters on the left are all of X, including its forgotten components. The bijection commutes with restriction and isomorphisms, and with free lifting along arrows, including mixed arrows when the tuple arities and the required testing bounds lie below the smaller level. It also takes witnessed free products to their projected witnessed free products.

Proof. First consider surjectivity at a level µ. Present X = F (I) on a well-order, and let p be a projected type over P X. For a bounded list a of parameters from P X, saturation in D realizes the prescribed joint diagram of (v, a) in P X itself. Such a realization has term representations in the retained sorts of F (I). Thus every one of the simultaneous local requests used in compact placement has an actual placement in the chart of X.

Here we prescribe projected diagrams only; diagrams involving the forgotten sorts have yet to be chosen. The proof of Lemma 6.4 applies to this form of request as well. To verify this explicitly, fix a sufficiently large bounded cardinal$χ = χ^{|v|+ℵ_{0}},$larger than the label and testing bounds. A profile records the labels of v, its ordered supports, and their comparisons with the chosen representations of the projected parameters under consideration. There are at most χ profiles over at most χ parameters. If a continuation of a profile fails a prescribed projected diagram, record a witnessing projected test and add it to the next parameter set. The comparison of continuations with no new event uses equality of natural C-diagrams on retained sorts; the hypothesis on P then gives equality of the requested D-diagrams. Consequently the same new-hit or new-separation argument as in Lemma 6.4 rules out failure at every step. The local possibility used at the final step is the simultaneous request on the entire final bounded parameter set, which is realizable in P X by saturation.

The resulting placement in an enlargement of I satisfies the projected requests up to χ. Taking χ beyond the testing bound in D makes its projected type equal to p. The placement itself defines a C-type over all of X, which proves surjectivity. In particular, no diagram on a forgotten parameter was assumed to have been prescribed in advance.

Next let$q = tp_{C}$(v/X). Its approximation lists from Lemma 6.9 consist of tuples in the same retained sorts as v. A query whose parameters lie in the projection sorts can be moved over such an approximation list using the working package. The projection comparison identifies precisely the equality tests used in this computation. The majority answer and its exception estimate therefore compute the projected free lift. Increasing the approximation length or the test arity gives the same answers by the compatibility part of the approximation construction. Thus free lifts project to free lifts. This reasoning uses bounds below the originating level and consequently applies also to mixed arrows. Projecting the witnessing chain of a free product now gives its claimed projected witnessing chain.

For injectivity, suppose$q_{0}$̸=$q_{1}$have the same projection. Choose a bounded tuple f from X witnessing their inequality: the diagrams of (v, f) for the two types have distinct values$δ_{0}$and$δ_{1}.$Choose a bounded infinite χ such that

$χ^{|f|+ℵ_{0}} =$χ,

and such that χ bounds |v| and the label and orbit-counting costs. All constructions below fit below µ: in particular$2^{χ} <$µ, and a tuple of χ many copies of v remains bounded at µ.

χ

For each η ∈ 2, construct a genuine witnessed free sequence$(v_{i^{η}}: i <$χ) over X with successive

marginal$q_{η(i)}.$Successor steps use free extension and amalgamation; limit steps use the chain axiom. The uniqueness of whole types of witnessed chains in Lemma 7.12 applies also to these bounded tuple entries. Their projected marginal types are all the same, so their projected sequences have the same whole type over P X. In particular their parameter-free projected diagrams agree. By the hypothesis on P, their whole C-diagrams agree as well.

Fix one such sequence$a = (a_{i}: i <$χ) in a level-µ object. Bounded diagram homogeneity gives, for every η, an isomorphism from the object containing$v^{η}$onto this fixed object, carrying$v_{i^{η}}$to$a_{i}$for every i. Write$f_{η}$for the image of f. Preservation of diagrams gives

$D_{C} (a_{i}, f_{η}) = δ_{η(i)}.$

If η ̸= η', a coordinate where they differ shows that$f_{η}$and$f_{η'}$have different orbits over the entries of a. There would be$2^{χ}$such orbits of |f |-tuples over at most χ parameters. Lemma 6.1 bounds their number by χ, a contradiction.

Restriction and transport commute with projection directly. Surjectivity and injectivity, together with the free-lift calculation, give all the stated compatibilities. In particular a projected extension of a type is free exactly when its corresponding full extension is free: the free full extension has the required projection, and injectivity makes it the only possible full lift.

Corollary 9.2 (Lifting an extension of a projection). Under the hypotheses of Proposition 9.1, let X and Z be at the same eligible level, and let P X −→ Z be an arrow. There are a C-extension$X −→ X^{∗}$and a D-arrow$Z −→ P X^{∗}$whose composite on P X is the projection of$X −→ X^{∗}.$

Proof. Identify the given base with its image. Choose nested bounded lists$d_{i}$exhausting Z for i < ω. In each vertex include enumerations of increasing smaller strong submodels exhausting that vertex. We construct extensions$X → X_{i}$and assignments of$d_{i}$into$P X_{i}$that extend the previous assignments and have the correct type over P X.

Suppose the assignment of$d_{i}$is given. Amalgamation in D, with identification of the already matching tuple, puts Z and$P X_{i}$in a common extension, agreeing on P X and on$d_{i}.$The type there of$d_{i+1}$over$P X_{i}$lifts by Proposition 9.1 to a type over$X_{i}.$Realize it in a C-extension$X_{i+1}.$The part corresponding to$d_{i}$is already a tuple of parameters from$P X_{i},$so its equality diagram forces the new assignment to extend the old one. At the first step use the same argument with the empty tuple.

Take the union of the$X_{i}.$The assigned lists match all their bounded diagrams, and the included vertex submodel enumerations give componentwise strongness by the working-package map criterion. Thus their union is the required arrow from Z.

## 9.2 The finite systems and their faces

Theorem 9.3 (Finite marked systems). Start with the single-model scheme, allowing fixed bounded named data of a fixed diagram. Let r be a prescribed, definable, isomorphism-invariant stationary type of a finite tuple in its root sort. Stationarity here includes free lifting under mixed arrows at eligible levels. For each finite n, the n-fold marked increment construction gives a working scheme$C_{n}$at sufficiently closed levels. Its objects are systems indexed by the subsets of {1,..., n}, with the prescribed marks and componentwise strong arrows.

For s ⊆ {1,..., n}, retaining the axes in s in their induced order gives a projection

$P_{s}: C_{n} −→ C_{|s|}.$

Every such projection takes objects and arrows to objects and arrows, including mixed arrows, and preserves and reflects diagram equality on bounded tuples in its retained sorts. It consequently has the exact type correspondence of Proposition 9.1. The type in the root sort lying over r exists uniquely over every whole system and lifts freely.

These conclusions include the projection to the base root and each single-axis projection. In a single-axis projection the upper object is all-dominated over its lower object together with the prescribed mark; forgetting other axes does not remove that assertion.

Proof. We induct on the number of axes. At depth zero the working package and the prescription r are the given ones. Suppose the assertion is known for$C_{n}.$By the exact type correspondence for the root projection, r determines a unique type over every$C_{n}-object.$Projection commutes with free lifting, so this prescription is stationary, including under mixed arrows. Theorem 8.6 therefore supplies the working scheme$C_{n+1} = (C_{n})^{b}.$

First forget its last axis. The result is its lower object X. If two bounded tuples in the lower objects have equal$C_{n}-diagrams, a$lower-object isomorphism matches them. It transports the prescribed type of b, and hence extends to an isomorphism of the marked pairs by Lemma 8.2. This proves diagram reflection; preservation follows by restriction. Objects and arrows plainly project to their lower objects and arrows.

Next apply an earlier projection P:$C_{n} → C_{k}$to both layers of (X ≤ Y, b). The marginal of b over P X is the required type, by Proposition 9.1. We must verify all-domination of P Y over P X + b. Suppose it fails for a bounded tuple a from P Y. The nonisolation alternative of Proposition 7.3 gives an extension of

$tp_{C_{k}}$(b, a/P X)

to an enlarged parameter object V ≥ P X that is nonfree, although its b-marginal is free. By Corollary 9.2, put V inside the projection of an extension X' of X. Freely extend the chosen joint type to P X'. It remains nonfree from P X, since otherwise its restriction to V would have been free. Its b-marginal remains free from P X by transitivity.

Lift this type to X' by the exact type correspondence. Its restriction to X is the original type of (b, a), because their projections agree and the correspondence is injective. Its b-marginal is the free lift of the original one, again by injectivity and compatibility with free lifting. Its joint type is nonfree: a free joint type would project to a free one. This contradicts the relative isolation of$tp_{C_{n}}$(b, a/X) and Lemma 7.2. The projected pair is thus all-dominated as required. Componentwise projection of an arrow preserves the prescribed mark and gives an arrow of these pairs.

It remains to reflect pair diagrams. Suppose bounded retained tuples in two projected pairs have equal diagrams. The projected pair isomorphism test gives an isomorphism of their projected bases transporting their types jointly with b; any indicated base entries are included in this match. Choose in the first base sufficiently long approximation lists for this joint type, at arities exceeding the full and projected testing bounds. Their entries are in retained sorts. Carry these lists, together with the indicated base entries, by the projected base isomorphism. The inductive reflection hypothesis and bounded homogeneity give an isomorphism of the full bases making precisely these bounded matches.

The transported approximation lists compute the same projected joint type over the second projected base. Exact type correspondence therefore says that the full base isomorphism transports the entire joint type with b. The full pair isomorphism test now extends it to an isomorphism of marked pairs matching the original tuple. Preservation is immediate from projection of an isomorphism. The same calculation uses free lifting and the mixed preservation and reflection in Lemma 8.2 when comparing eligible levels; all the tuple and approximation bounds are below the smaller one. Composing elementary axis deletions proves the assertion for every$P_{s}.$This completes the finite induction.

Definition 9.4 (Boundary). For an n-axis object J, its boundary ∂J consists of all the proper-axis projections$P_{s}$J, with their specified inclusions. For n = 0 the boundary is empty. A boundary map h: ∂J → ∂K is a compatible family of arrows$h_{s}: P_{s} J → P_{s} K$for proper s. A boundary isomorphism is such a family of isomorphisms.

Lists in a boundary are lists of occurrences in its vertex sorts. The diagram of a joint list records the specified inclusion maps and all resulting equalities. In particular, entries supplied from different faces can coincide in a containing vertex. Compatibility on the named subfaces alone is not asserted to settle these extra equalities; their preservation will be part of the next argument.

## 9.3 Completing a boundary into an extension

Lemma 9.5 (Joint diagrams on the boundary). At the levels used for$C_{n},$every boundary map between two n-axis objects at the same level preserves all bounded$C_{n}-diagrams$on their boundary unions. This includes joint diagrams of entries from different faces and all equality information on their actual overlaps.

Theorem 9.6 (Amalgamated boundary completion). For each finite n, at sufficiently closed levels the following holds. If J and K are$C_{n}-objects$at the same level and h: ∂J → ∂K is a boundary map, there are arrows$K −→ K^{∗}, J −→ K^{∗}$

in$C_{n}$such that the second restricts to the composite of h with the first on every proper projection. The extension is in the same scheme and at the same level. No assertion about completion between distinct levels is needed here.

Proof of Lemma 9.5 and Theorem 9.6. We prove the two assertions together by induction on n. For n = 0 the diagram assertion is empty, and joint embedding gives completion. At a positive dimension, after proving the diagram assertion we shall derive completion by a placement argument. Thus only lower-dimensional completion will be used in proving the next diagram assertion.

For n = 1, its only proper projection is its base. Theorem 9.3 identifies the full-scheme diagrams on that base with its projected diagrams. The given base arrow preserves the latter, proving the assertion.

Let n = m + 1 with m ≥ 1, and write the source and target as

$(X^{−} ≤ Y^{−}, b^{−}), (X^{+} ≤ Y^{+}, b^{+})$

over$C_{m}. A$boundary map gives a full base arrow e:$X^{−} → X^{+}$and a boundary map h:$∂Y^{−} → ∂Y^{+}$agreeing with e on$∂X^{−};$the upper faces also specify$h(b^{−}) = b^{+}.$Let v be a bounded tuple from$∂Y^{−},$enlarged to include$b^{−}.$We first claim that its type over$X^{−}$in$C_{m}$equals the restriction along e of the type of h(v).

Suppose instead that a bounded tuple f from$X^{−}$witnesses a difference. Put

$δ_{0} = D_{C_{m}}$(f, v),$δ_{1} = D_{C_{m}}$(e(f), h(v)),$δ_{0}$̸=$δ_{1}.$

Choose an infinite bounded χ satisfying$χ^{|f|+ℵ_{0}} =$χ, bounding |v| and all the label and orbit-counting costs. Let ϵ be the least cardinal with$2^{ϵ} >$χ. Cantor’s Theorem gives ϵ ≤ χ, and minimality gives$2^{|i|} ≤ χ$for every i < ϵ. Consequently

<ϵ

2 ≤ χ,$2^{ϵ} ≤ 2^{χ} <$µ,

where µ is the common level. Every accumulator and branch world below will have size µ, and the total number of amalgamations remains below µ.

≤ϵ

We construct branch worlds$W_{s} ∈ C_{m}$for s ∈ 2, carrying tuples$f_{s},$with coherent full arrows

along each branch. Their proper boundaries have compatible arrows

$q_{s}: ∂W_{s} −→$∂A

into an increasing common accumulator$A ∈ C_{m}.$The accumulator may be enlarged at each operation; existing boundary arrows are always composed with its enlargement arrow. The invariant requires coherence of these boundary arrows with the branch arrows. It does not require full maps of all the branch worlds into the accumulator to be retained.

Start with$W_{∅} = X^{−},$its tuple f, and the identity boundary map into$A = X^{−}.$At a node s, diagram preservation along the branch shows that$D(f_{s}) =$D(f). Bounded homogeneity supplies an isomorphism$k_{s}: X^{−} −→^{≃} W_{s}, k_{s}$(f)$= f_{s}.$

There is no coherence requirement on the choices of$k_{s}.$Choose the minus child to be a copy of$Y^{−}$attached over$W_{s}$by$k_{s^{−1}},$and the plus child to be a copy of$Y^{+}$attached by$ek_{s^{−1}}.$These choices give the full branch arrows. In each child, f denotes the image of$f_{s};$the corresponding upper boundary lists have diagrams$δ_{0}$and$δ_{1}$with it. Transporting h gives a boundary arrow

$h_{s}: ∂W_{s0} −→ ∂W_{s1}$

over$∂W_{s},$matching the two copies of v.

Apply the already proved completion theorem in dimension m to$q_{s}.$After enlarging the accumulator, this gives a full map$W_{s} → A_{0}$extending$q_{s}.$Ordinary amalgamation in$C_{m}$then puts the plus child in an enlargement$A_{1}$over this full map. Let$G_{1}: W_{s1} → A_{1}$be the resulting arrow. Retain its boundary restriction as$q_{s1},$and define

$q_{s0} = q_{s1} h_{s}.$

Both restrict to the preceding$q_{s},$after enlargement, and the two boundary copies of v have one common image$v_{s}$in$A_{1}.$The temporary full maps to$A_{0}$and$A_{1}$are no longer part of the invariant. In particular the minus child has not been required to send its copy of f to the temporary image of$f_{s}$in the accumulator.

Process the nodes of each level successively. At a limit height take the union of the worlds along each branch and the union of the accumulators constructed so far. Their sizes are still µ. The boundary arrows into the union accumulator exist by the chain and common-upper-bound

$W_{s}, f_{s}$

$W_{s0}, f_{s0} W_{s1}, f_{s1}$

boundary boundary

$∂W_{s0} h_{s} ∂W_{s1} G_{1}$

$q_{s0} q_{s1}$

$A_{1}$∋$v_{s}$

Figure 2: A return-tree split. Solid arrows between worlds are retained along their separate branches. Dashed boundary maps persist in the common accumulator and agree on the test$v_{s}.$Each dashed arrow denotes a compatible family of maps into the proper projections of$A_{1}.$The dotted full map is used to choose the plus boundary map and need not be retained at later splits. Full maps of all leaf worlds are installed only after the splitting tests have been fixed.

clauses in every proper projection. Full branch arrows and the carried tuples also pass to the unions. This establishes the invariant through height ϵ.

At that height, apply lower-dimensional completion to each leaf boundary map, successively ϵ

enlarging the accumulator. This supplies a full map of each$W_{η},$for η ∈ 2, extending its retained

boundary map. There are fewer than µ leaves, so the final union is still at level µ. If two leaves first differ after a node s, their images of f have diagrams$δ_{0}$and$δ_{1}$over the common tuple$v_{s}.$Indeed the corresponding copy of v was in that child’s boundary, remained there along that branch, and its boundary image was never changed except by composition with an accumulator arrow.

<ϵ

Thus the final images of f occupy more than χ orbits over the entries of$(v_{s}: s ∈$2). This

parameter list has size at most χ. The orbit bound of Lemma 6.1 gives the contradiction. The claimed equality of types of v follows.

To pass from this type equality to the full pair diagrams, retain an arbitrary bounded tuple a from the lower face$X^{−}.$The marginal of$b^{+}$over$X^{+}$is the prescribed free lift from$e(X^{−}).$Relative isolation of the source type of$(b^{−},$v) and Lemma 7.2 therefore identify the actual type of$(b^{+},$h(v)) over$X^{+}$with the free lift of that source type.

Choose sufficiently long bounded approximation lists in$X^{−}$computing the source type. Their images under e compute its free lift over$X^{+}$by Theorem 6.10. Base homogeneity gives an isomorphism$X^{−} ≃ X^{+}$matching a and these lists with their images under e, since e preserves their joint bounded diagram. The transport assertion for the approximation lists says that this isomorphism carries the whole source type to the type of$(b^{+},$h(v)). Lemma 8.2 now extends it to an isomorphism of the marked pairs matching (a, v) with (e(a), h(v)). Every bounded boundary list is of this form. Thus its full$C_{n}-diagram$is preserved, including cross-face equalities.

We finish the induction by deriving completion from this diagram equality. Present the source J on a well-order. Its boundary union is a natural collection of the designated term sorts in that presentation. Choose nested bounded lists$d_{i}$exhausting J, including increasing strong submodel enumerations in every vertex. We construct extensions$K_{i}$of K and compatible assignments of$d_{i}$into$K_{i}$satisfying

$D_{J} (d_{i},$u)$= D_{K_{i}} (d_{i'},$h(u)) for every bounded boundary list u. (C)

Here and subsequently h is composed with the current extension arrow. At the start the assertion for the empty list is exactly the boundary diagram equality just proved.

For the next list prescribe the source joint diagrams on the parameter set consisting of the boundary images and the previous assignment. Each bounded local request, including the whole previous assigned list, is possible by saturation: the parameter diagram agrees by (C). This also checks repetitions and equalities between old entries and boundary entries, so the requests define one coherent prescription. Apply compact placement in a well-ordered chart of$K_{i},$keeping these previous entries fixed. Work at one bounded cardinal large enough for the profile count, the new tuple, and the testing bound for the source boundary layout with the previous tuple included. The resulting placement lies in a level-µ extension$K_{i+1}.$

To check (C) beyond that initial testing cardinal, pull the candidate diagrams back along h to the natural boundary layout of J. Their local possibility there follows from the boundary diagram equality and saturation. Lemma 6.4 compactifies these requests over this source layout, and Proposition 6.3 says that agreement at the chosen testing bound determines all bounded comparisons. The actual images of the boundary inside$K_{i}$have not been assumed to form a natural layout. All uses of that hypothesis are on the source layout after pullback.

Continue through ω steps and take the union of the$K_{i}.$The working-package criterion, with the included strong submodel enumerations, makes the union assignment an arrow$J → K^{∗}.$Whenever a boundary entry is first included in$d_{i},$its equality test against that boundary entry forces its assigned image to be h of that entry. The union arrow therefore extends the entire boundary map. The map from K is the chain inclusion. This proves completion and closes the induction.

## 9.4 A bounded support for boundary tests

We have extended boundary maps into common extensions. Exact lifting must instead land onto the given target. The next lemma supplies bounded data that control a tuple’s boundary comparisons at a fixed bounded test arity. Together with uniform testing, this permits back-and-forth to remain inside the two given systems.

Lemma 9.7 (Fixed parameters for a boundary test function). Fix n < ω. At further sufficiently closed levels, let$J ∈ C_{n},$let z be a bounded tuple of J, and let σ be a bounded infinite test arity. There is a bounded list a in ∂J such that every boundary automorphism α fixing a pointwise satisfies

$D_{J}$(z, u)$= D_{J}$(z, α(u)) for every boundary tuple u of length at most σ. (F)

A boundary automorphism means a compatible family of isomorphisms of all proper projections; a full automorphism of J is not assumed.

Proof. The assertion is immediate for the empty boundary. Suppose it fails otherwise. Choose a bounded infinite χ with$χ^{|z|+ℵ_{0}} =$χ, bounding σ and the orbit-counting and label costs. Let ϵ be the least cardinal with$2^{ϵ} >$χ. Choose a smaller eligible level ν such that

|z|$+ σ + 2^{χ} < ν <$µ,

where µ is the level of J, with all required testing bounds below ν and with Theorem 9.6 available at ν. The further closure requirement on the level of J ensures this choice. It is a finite refinement for this fixed n.

Fix a well-ordered presentation$J = F_{n}$(I). Construct continuous subpresentations$J_{i}$of size ν for i ≤ ϵ, beginning with z in$J_{0}.$At step i, the boundary of$J_{i}$is a bounded parameter set in J. By the assumed failure, a boundary automorphism$α_{i}$of J fixes it pointwise and changes the value of the function at some tuple$u_{i}$of length at most σ. Thus

$D_{J}$(z,$u_{i})$̸=$D_{J}$(z,$α_{i} (u_{i})).$(S)

We choose$J_{i+1}$containing both tests so that$α_{i}$restricts to an automorphism of its boundary.

Here is the support closure for this choice. Begin with the positions for$J_{i},$z,$u_{i},$and$α_{i} (u_{i}),$padding to size ν. For every element of every proper projected subpresentation currently generated, add positions for its image and its inverse image under the corresponding face map of$α_{i}.$There are finitely many faces and ν elements in their union, and each representation uses finitely many positions. Repeat this operation countably many times. The resulting position set still has size ν. Every element generated at its union appeared at a finite stage, so both its image and inverse image are generated in the union. Hence all restricted face maps are onto and remain compatible with the specified inclusions. They give the asserted boundary automorphism of$J_{i+1}.$At a limit use the union of the position sets. Mixed diagram preservation transfers (S) to$J_{i+1},$since |z| + σ < ν.

Now build a binary tree of boundary embeddings

i

$q_{s}: ∂J_{i} −→$∂A, s ∈ 2,

where A is an increasing accumulator of size ν. Start with$A = J_{0}$and the identity map on$∂J_{0}.$At a successor node first apply completion to$q_{s}$on$J_{i}$and then amalgamate$J_{i+1}$over that full copy of$J_{i}.$This yields an arrow$G_{s}: J_{i+1} → A'$whose boundary extends$q_{s}.$Define the two next boundary embeddings by$q_{s0} = ∂G_{s}, q_{s1} = (∂G_{s})α_{i^{−1}}.$

They restrict to the same old$q_{s},$because$α_{i}$fixes$∂J_{i}$pointwise. The common parameter test$G_{s} (u_{i})$is the image of$u_{i}$on branch s0 and of$α_{i} (u_{i})$on branch s1. Only these boundary embeddings are retained for later steps; the full map$G_{s}$is temporary.

At limits the continuity of the$J_{i}$and the common-upper-bound clauses give the boundary maps into the union accumulator. At height ϵ, complete the boundary maps to full maps of$J_{ϵ}, i$

one leaf at a time. The full maps at the leaves carry z. If two leaves first separate at s ∈ 2, their

images of z have the two distinct diagrams from (S) over the one retained test$G_{s} (u_{i}).$This follows from preservation by their final full maps and from coherence of their boundary maps with the chosen maps at the split.

There are at most χ nonterminal nodes, hence at most χ parameters in all the splitting tests. There are$2^{ϵ} > χ$distinguishable leaf images of z. All leaf completions and all unions remain at level ν, since$2^{χ} <$ν. Lemma 6.1 again contradicts this number of orbits over the tests. Thus the bounded fixing list a exists.

Theorem 9.8 (Exact boundary lifting). For each finite n, at further sufficiently closed levels every boundary isomorphism h: ∂J$−→^{≃}$∂K between$C_{n}-objects$at the same level extends to an isomorphism J ≃ K onto the given target. All the prescribed marks and bounded named data are preserved.

Proof. We build a back-and-forth sequence of matches a 7→ a' of bounded tuples, maintaining

$D_{J}$(a, u)$= D_{K}$(a', h(u)) for every bounded boundary tuple u. (BF)

For the empty tuple this is Lemma 9.5. Suppose that a match satisfying (BF) has been chosen, and let z be any bounded enlargement of a in J.

Take a bounded infinite σ at least the uniform testing bound for a tuple of length |z| over the natural boundary layout of$a C_{n}-object.$Choose fixing data c for z, σ in ∂J by Lemma 9.7. The maintained equality with the particular boundary list c gives

$D_{J}$(a, c)$= D_{K}$(a', h(c)).

Working-package homogeneity supplies a full isomorphism H: J ≃ K carrying a to a' and c to h(c). Put$α = (∂H)^{−1}$h. This is a boundary automorphism of J fixing c pointwise. Therefore, for every boundary tuple u of length at most σ,

$D_{K}$(H(z), h(u))$= D_{J}$(z, α(u))

$= D_{J}$(z, u). (BT)

We justify explicitly the passage from these tests to all bounded boundary tests. By Theorem 9.6, embed J into a same-level extension$K^{∗}$of K by an arrow j extending h. Both j(z) and H(z) are now tuples in$K^{∗},$and (BT) says that their diagrams agree over boundary tests from K of size at most σ. The boundary of K, in a well-ordered chart of K, is a natural collection of term sorts. The types of these two tuples over K have order placements by the one-dimensional calculus. Proposition 6.3 restricted to this natural boundary layout therefore gives equality over every bounded boundary test. Preservation by j then shows

$D_{K}$(H(z), h(u))$= D_{J}$(z, u)

for all bounded u. Thus z 7→ H(z) extends the previous match and satisfies (BF).

Apply this extension step alternately to J, K with h, and to K, J with$h^{−1}.$Their level has countable cofinality, so countably many bounded enlargements can exhaust both systems. In each vertex choose increasing smaller strong submodels whose enumerations are included in these tuples. The union assignment is onto in every component and is an arrow by the working-package map criterion; the reverse construction gives its inverse arrow. If an entry lies on the boundary, its equality test with that boundary entry in (BF) forces its image to be exactly the image under h. The resulting isomorphism therefore extends all of h, as required.
