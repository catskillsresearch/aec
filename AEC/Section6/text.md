# 6 The one-dimensional calculus


Throughout this Section, C is a scheme satisfying the working package of Definition 5.2. Its fixed presentation is denoted by F, and b is an infinite cardinal bounding the set of labels and the finite amount of structural data in the scheme. We use the occurrence sorts of that Definition: a tuple in several vertices is a tuple of tagged occurrences, and a map of systems commutes with every specified structural map. No choice of a hull or a basis is part of a diagram. A level is an eligible strong limit cardinal of countable cofinality. All further closure requirements below are requirements on functions of bounded arities and fixed scheme data. For the supply of unbounded refinements and larger auxiliary levels, we use the eligible-subclass hypothesis of Convention 5.3: the input class contains a fixed definable unbounded subclass closed under suprema of strictly increasing countable sequences. This subclass is used only to supply levels; the bounds below depend on fixed scheme data and bounded arities.

Stationary independence and local character are central to the theory of good frames; see [She09, II.2.1]. The assertions below are proved from the working package for bounded tuples and finite systems. Their role is to supply the independence and descent properties needed for the next isolation construction.

A query is an enumerated parameter set Z together with the diagram of the displayed tuple and that enumeration. Repetitions in an enumeration are allowed. Saying that an answer is correct on Z means equality of the whole joint diagram, rather than equality only on finite subtuples. At a level µ, every tuple or query called bounded has cardinality less than µ.

## 6.1 Testing, placement, and amalgamation

Lemma 6.1 (Parameter orbits for a scheme). Fix an infinite σ. If χ > b + σ and$χ^{σ} =$χ, then, at every sufficiently closed level greater than χ, there are at most χ diagrams of σ-tuples over a fixed parameter tuple of length at most χ. Moreover, natural diagrams are unchanged by simultaneous disjoint block transpositions: within each of a family of disjoint convex regions, interchange an adjoining block belonging exclusively to the first tuple family with one belonging exclusively to the second, retaining each block’s internal order.

Proof. Present the parameter object on a well-order. After choosing one term representation of each parameter, its supporting positions form a well-ordered set of size at most χ. There are at most χ slots and positions relative to this set. Labels, comparisons and coincidences for at most σ additional positions therefore have at most$χ^{σ} = χ$possibilities. Equal profiles give equal natural diagrams. The diagram-isomorphism clause of the working package turns this into the asserted orbit bound over the actual parameters.

Here are the hypotheses needed for the block argument in Lemma 4.6. We have just proved its parameter orbit bound. Repeating the two blocks along an arbitrary order is permitted after padding: the scheme has the union and common-upper-bound clauses, so Lemma 5.4 supplies the padded presentations and their order arrows. Naturalness compares the two patterns at a common higher eligible level. If the transposition changed a diagram, the repeated patterns would distinguish cuts by whether the first block preceded or followed a parameter block. A binary tree of least height ϵ with$2^{ϵ} > χ$has at most χ nonterminal nodes and more than χ branches. Divider points at those nodes give at most χ parameter blocks and more than χ different diagrams over them. The preceding orbit bound gives a contradiction. The repetition uses only a set of positions, so a higher eligible level can contain the entire test. This proves the assertion also when there are boundedly many simultaneous transpositions.

Definition 6.2 (Natural parameter layouts). A natural parameter layout consists of finitely many well-ordered segments, a fixed finite set of colors and their prescribed order, and specified families of terms on specified collections of those positions. Its parameters are all the designated terms; vertex sorts may be among the designations. The data must have the following monotonicity property: after freezing bounded extra supports, increasing the ordinal lengths of the remaining slots gives an embedding of layouts that preserves the designated parameter terms. Bounded frozen parameters are permitted and count towards the input arity. The layout, labels and color conventions are fixed set data.

The whole object F (H), with H well-ordered, is a natural layout. Unions of designated vertex sorts generated on specified segments are further examples. An arbitrary subset of the parameters in an unrelated target chart is not asserted to be a natural layout.

Proposition 6.3 (Uniform testing for natural layouts). For each fixed natural layout there is a monotone cardinal function g(σ) with the following property. Two placed comparison types of tuples of length at most σ over that layout are equal if and only if they agree on parameter queries of size at most g(σ). The bound is independent of the eligible level. The extra tuple supports may lie in a non-well-ordered extension of the layout. The assertion is uniform when the fixed layout and frozen bounded data range over a fixed set of descriptors of bounded size.

Proof. Amalgamate the orders containing the two placements over the parameter order. Freeze the labels of the two tuples, their combined ordered support T, the coincidences with old positions, and the colors. There are set-many such frozen patterns at the prescribed bound. The unfrozen well-ordered parameter positions are described by a vector of ordinal lengths, one coordinate for each strict slot and each prescribed segment. There are set-many coordinates, even when T itself is not well-ordered. By the monotonicity requirement in Definition 6.2, a pointwise increase embeds the old layout and its designated terms into the new one. Unequal comparisons remain unequal because diagrams are preserved by the induced arrows.

For a fixed frozen pattern, apply Lemma 4.7 to the upward closure, among all ordinal vectors, of its valid unequal configurations. It gives a set of generators, which can be chosen from valid unequal configurations. Each generator has a set-sized parameter order. Take a cardinal above the sizes of the terms on all these orders, then above the resulting bounds for all the frozen patterns. An unequal configuration contains one of the generating configurations and is consequently witnessed on at most that many parameters. Increasing the bound monotonically gives g. This is precisely the ordinal-vector proof of Proposition 4.8; its required ingredients here are natural diagrams, their preservation, and the explicit monotonicity of the layout, all verified above. Taking the same supremum over a set of descriptors proves the last assertion.

Lemma 6.4 (Compact placement for a scheme). Let P be any chosen parameter set in a well-ordered presentation, with one fixed term representation for each parameter. Let v have length at most σ, and let χ > b + σ,$χ^{σ} =$χ.

Suppose that coherent diagrams for (v, X) are prescribed for every X ⊆ P of size at most χ, and that each individual prescription has a placement. At a sufficiently closed eligible level containing the data, one order enlargement realizes all these prescriptions simultaneously. The same assertion holds with bounded frozen data, after adding its size to σ.

For a padded order that need not be well-ordered, it suffices instead to have locally possible coherent prescriptions on every bounded subset and closure under the profile-count growth used in the proof. The conclusion then holds simultaneously at any one specified bounded test size. All the bounds are uniform in the fixed scheme and layout data.

Proof. For X ⊆ P, let$S_{X}$be the union of its chosen supports. A profile records the labels of v, its formal ordered support, and all comparisons and coincidences with$S_{X}.$If |X| ≤ χ, there are at most χ profiles. In each strict slot over$S_{X},$all the new positions there form one cluster. A profile has a continuation over the whole old order with no new event: place each cluster intact into a single strict slot of the old order extending its slot over$S_{X}.$Order enlargement supplies positions if necessary. A new event on enlarging X means a new hit of an old position or a separation of two previously unseparated new positions by an old position.

Two continuations with no new event over$S_{Y},$for Y ⊇ X, have the same diagram over Y. Indeed, their differences consist of moving whole clusters past blocks of parameter supports. The regions belong to distinct slots, so the block transpositions in Lemma 6.1 apply simultaneously.

If simultaneous realization fails, choose$X_{0}$of size at most χ. For each profile over$X_{i},$choose a no-new-event continuation and one prescribed query where it fails. Adjoin those queries to$X_{i}$to obtain$X_{i+1};$at limits take unions. There are at most χ profiles, each chosen query has size at most χ, and$σ^{+} ≤$χ. Thus every$X_{i},$including$X_{σ^{+}},$has size at most χ. Choose a placement realizing the prescription on$X_{σ^{+}}.$At every earlier step this placement must have a new event, since otherwise the no-event comparison would transfer the chosen failure to it. There are at most σ possible hits and at most σ pairs of new positions. Each event can occur for the first time only once. This contradicts the$σ^{+}$steps.

|+σ+b

In a non-well-ordered chart, the number of profiles over$X_{i}$is at most$2^{|X_{i}}.$Starting with

the desired test size, use this as the next cardinal bound and include a failed query of at most that original test size for every profile. The larger sets$X_{i}$have prescriptions because those were supplied on all bounded subsets. More explicitly, start with an infinite$β_{0}$above the desired test +σ+b

size and set$β_{i+1} = 2^{β_{i}},$taking suprema at limits. Require the single bound$sup_{i≤σ^{+}} β_{i}$to be

strictly below the level. This is closure under the whole indicated recursion, rather than merely closure under each individual exponentiation. It keeps the final set bounded even though the level has countable cofinality. Its prescription is available by hypothesis, and the identical event count is a contradiction. This is a set recursion depending only on the starting arity and fixed data.

For later reference, fix a convenient explicit threshold for the whole object layout. Increase g so that g(σ) ≥ b + σ, and put

c(σ, τ)$= 2^{g(σ)+b+σ+τ},$c(σ) = c(σ,$ℵ_{0}).$(1)

These cardinals exceed the displayed arities and satisfy c(σ,$τ)^{σ} =$c(σ, τ). We close levels under these functions and their successors, as well as under the diagram and rich order bounds at the resulting arities. For a different fixed natural layout, use its testing function in the same formula.

Lemma 6.5 (Placed comparisons of actual tuples). Suppose A → N is an arrow between same-level objects and v is a bounded tuple in N. Its diagrams over bounded subsets of A have a placed comparison over a well-ordered presentation of A. This comparison is unique as a diagram over all of A. Two such actual tuples have equal comparisons if and only if their diagrams agree over queries in A of size at most g(|v|$+ ℵ_{0}).$The conclusion also holds over any natural parameter layout for which the same coherent local diagrams are given.

Proof. A single bounded request is possible in a presentation: the parameter diagram is preserved by the arrow, and saturation realizes its desired extension over the actual parameters in a level object. Apply Lemma 6.4 at χ = c(|v|$+ ℵ_{0},$τ), for any desired bounded query size τ. Two outputs agree on all tests of size at most g(|v|$+ ℵ_{0}),$and Proposition 6.3 identifies their full placed comparisons. For any bounded query, choose τ large enough to include it. The unique comparison therefore computes every actual bounded diagram. This argument does not require an amalgamation relation on types.

Theorem 6.6 (Amalgamation and types for a scheme). At sufficiently closed levels, C has amalgamation. If$A → B_{0}, B_{1}$are arrows and$v_{i}$are equally indexed bounded tuples in$B_{i},$then an amalgam over A identifying$v_{0}$and$v_{1}$exists if and only if their diagrams agree on all parameter queries in A of size at most$g(|v_{i} | + ℵ_{0}).$

Consequently tp(v/A; B), defined by identification in an amalgam over A, is an equivalence class. It is determined by these bounded diagrams and has an order placement. Restriction of a type means restriction of its actual tuple and parameter diagrams.

Proof. Write arrows as inclusions by taking renamed copies. We prove the stronger construction with a prescribed identification of bounded tuples; omit the tuples for ordinary amalgamation. Let the target initially be$N_{0} = B_{1}.$Choose increasing bounded lists$d_{n}$exhausting$B_{0},$starting with$d_{0} = v_{0}$(or the empty list when no identification is prescribed). In each vertex also choose an increasing countable exhaustion by strong submodels of cardinality less than the level, and include their enumerations in the$d_{n}$’s. Such exhaustions exist by the component LS property, coherence and cf(µ) = ω.

We construct targets$N_{n}$and compatible images of$d_{n}.$The invariant is equality of all bounded joint diagrams of$(d_{n},$A) with their original diagrams in$B_{0}.$For the prescribed initial tuple this is the hypothesis and Lemma 6.5; the empty initial tuple is automatic.

Suppose an image of$d_{n}$has been chosen. In a well-ordered chart of$N_{n},$regard A and this whole image as the parameter set P. For a bounded subset of P, its required joint diagram with$d_{n+1}$is read in$B_{0},$interpreting the old image as$d_{n}.$This prescription is well-defined on repetitions and coincidences by the invariant. It is locally possible: equality on the old parameters and saturation give a realization in$N_{n}.$Choose a test cardinal of the form (1), large enough also for the length of$d_{n},$and apply Lemma 6.4. The resulting tuple lies in an order enlargement$N_{n+1}$and retains the old assignments.

To verify the invariant, use a natural well-ordered chart of the source A. Both the desired tuple and the newly placed tuple have comparisons there by Lemma 6.5. Their agreement on the chosen tests includes the testing bound for the joint arity, so Proposition 6.3 makes their comparisons equal. They therefore agree on every bounded query in A. We have not applied uniform layout testing to the possibly unnatural image of A in the target chart; compact placement alone was used on that image.

Take the union of the countable target chain. Its total size is µ, so the union and upper-bound clauses of the package give an object and an arrow from$B_{1}.$The assignments define a map from$B_{0}$into this union. They match diagrams on increasing lists that exhaust$B_{0}$and include the component strong-submodel exhaustions. The image of each such small submodel is strong: the matching diagram of its enumeration is implemented by an isomorphism between its original containing object and the target object. The arrow criterion of the package consequently makes this map an arrow, including any extra basis condition already checked for the current scheme. The initial tuples have the same image. Necessity of diagram equality follows from preservation in any amalgam.

Amalgamation makes the identification relation transitive: amalgamate two witnesses over their common intervening object. Reflexivity and symmetry follow from identity maps and interchange of the two legs. The equivalence and testing descriptions now follow from the proved criterion and Lemma 6.5.

Corollary 6.7 (Realization into a larger level). Let ν < µ be sufficiently closed eligible levels. If A → B are ν-objects and A → N is an arrow into a µ-object, then there is an arrow B → N extending the given arrow on A. One may prescribe the image of a tuple of length less than ν whose diagrams over queries in A below ν already match. Types of tuples of length less than ν over A obtained in a larger object are actual ν-types, and the mixed diagram comparisons at those arities agree.

Proof. Use the countable exhaustion in the preceding proof, with all source lists and testing thresholds below ν. Perform the compact placement in a chart of N. The placed tuple, all of A, and the previously assigned list together have cardinality at most ν, which is bounded at µ. Saturation at µ therefore realizes their whole joint diagram back in the actual N, fixing the existing parameters. Continue there, without enlarging the final target. For component strongness, first place the source object at level µ by a presentation arrow. Mixed preservation and an isomorphism of µ-objects implementing the matching enumeration show that every small source strong submodel has strong image in N. The exhaustion criterion now gives the arrow.

To interpret a tuple of length less than ν over A inside a larger object, take a ν-subobject containing A and the tuple, using mixed LS. Coherence makes it an extension of A. Mixed preservation identifies its diagrams with those in the larger object. The testing criterion shows independence of the chosen subobject. This also justifies the source-level type comparisons used during the construction.

## 6.2 Approximations and stationary free extensions

Amalgamation has made types over a whole object available. We now choose their free extensions by means of sequences in the base: on each bounded parameter query, almost all entries of the sequence give the same answer. The next two results construct these sequences and show that their answers determine an actual type, independently of the choices.

Definition 6.8 (Approximation sequence). An approximation sequence for p = tp(v/A) at query size τ is an indexed family$I = (v_{i}: i <$κ) in A, each$v_{i}$having the same index set as v, such that the concatenation of the family is bounded and, for every Z ⊆ A of size at most τ,

{i < κ:$D(v_{i},$Z) ̸= p↾Z} ≤ |Z|$+ ℵ_{0}.$(2)

Here p↾Z denotes its joint diagram, and a sequence is always indexed: different indices may carry the same tuple. We use the same terminology for all projections of the displayed tuple. Whenever κ > |Z|$+ ℵ_{0},$the unique value assumed outside at most |Z|$+ ℵ_{0}$indices is called its majority value on Z.

Lemma 6.9 (Uniform majority approximations). Let |v| ≤ σ and let$τ ≥ ℵ_{0}$be bounded. At sufficiently closed levels there are approximation sequences for p = tp(v/A) at size τ, of every prescribed bounded infinite length κ. They satisfy (2) simultaneously for all subtuples of v. The construction has bounds depending only on b, σ, τ, κ, rather than on the level or the type.

In particular, take τ = c(σ) and$κ = c(σ)^{+}.$The concatenated sequence then has a uniform bounded length depending only on σ and the fixed scheme. Its diagram is a code for p in the precise transport sense proved in Theorem 6.10 below.

Proof. By the rich-order and padding constructions of Lemmas 5.5 and 5.4, present A on a padded dense order sufficiently saturated for every support size used below. The presentation is an object of the current scheme; categoricity in the package gives an isomorphism with A. Lemma 6.5, or its compact-placement proof in the padded chart, places p correctly at size τ.

Keep every extra supporting position that belongs to the old chart. Partition the other supporting positions into clusters according to their strict cut over the entire old order. For every pair of distinct cuts choose an old position separating them. Include the shared supporting positions as well. This gives a bounded anchor set of size at most$σ + ℵ_{0}.$Each unshared cluster now belongs to a different strict slot over the anchors.

In each such anchor slot, choose κ pairwise disjoint convex regions in the old order and, in the ith region, put a copy of the corresponding cluster with its internal order. The prescribed richness supplies these patterns; its required arity is bounded in terms of σ + κ. Use the original labels and the unchanged shared positions to obtain$v_{i} ∈$A.

Choose a query Z and one finite support for each of its elements. If these supports avoid every region used for the ith copies, then each copied cluster and the original cluster can differ relative to the query only by passing whole blocks of parameter positions. There are no hits or separations inside a cluster. Their anchor slots are disjoint, so Lemma 6.1 gives$D(v_{i},$Z) = p↾Z. Every supporting position of Z belongs to at most one of the regions, and therefore excludes at most one index i. Finitarity of supports gives at most |Z|$+ ℵ_{0}$excluded indices. The same set of good indices works for every subtuple of v. Only bounded support patterns, the fixed labels, rich orders at bounded arities, and the compact-placement bounds were used. This proves the uniformity assertions.

Theorem 6.10 (Stationary free extension). Let A → B be an arrow at a sufficiently closed level and let p = tp(v/A), where |v| ≤ σ. There is a specified actual type$p^{B}$over B, called its free lift, extending p. At every desired query size whose approximation and testing costs are bounded at the originating level, it is computed by transporting sufficiently long approximations in A. At one level this includes every bounded query size; in a mixed-level use the costs must remain below the level of A. It has the following properties.

1. The answer is independent of the approximation sequence, its length, and the auxiliary test size used in its construction.

2. Free lifts commute with restriction of the tuple, are invariant under isomorphisms, and satisfy$(p^{B})^{C} = p^{C}$whenever A → B → C.

3. If A has an eligible size ν and B has a larger eligible size, the construction still works for |v| < ν, with its construction thresholds and approximation lists below ν. The restriction to A is the actual ν-type of Corollary 6.7.

4. A sequence from Lemma 6.9 at the fixed threshold c(σ) is bounded code data. If an equally indexed sequence in any sufficiently closed eligible object has the same diagram, it determines a unique corresponding type there by the same majority prescription. Arrows carrying one such sequence to another carry the corresponding type to its free lift. In particular an isomorphism carrying the code sequence transports the type.

We say that an actual type over B is free from A when it is the free lift of its restriction to A.

Proof. First fix a query bound τ and take an approximation sequence$I = (v_{i}: i <$κ) in A with$κ > τ + ℵ_{0}.$Given a query Z in B of size at most τ, saturation moves it into A over the entire sequence: there is$Z_{0} ⊆$A, with the same enumeration, such that

D(I, Z) = D(I,$Z_{0}).$(3)

The total length |I| + |Z| is bounded. For mixed levels it is bounded at the originating level, and the mixed saturation clause applies. Define the answer on Z to be the majority of$D(v_{i},$Z), equivalently the answer$p↾Z_{0}.$Equation (3) preserves every entry of the sequence, so this definition is independent of the chosen$Z_{0}$and retains the same exception estimate.

If I' is another sufficiently long approximation sequence, move Z into A over I ∪ I'. On that moved query both majorities compute the original p. Thus the answers agree. This proof requires saturation over the concatenation of the sequences; it does not require either approximation estimate to hold for a query containing that concatenation. The averaging queries still have size at most τ. The identical argument compares different query bounds on their common domain. It also proves coherence under restrictions and reindexing of queries.

We next obtain an actual type. Use τ = c(σ) and$κ = τ^{+}.$In a well-ordered chart of B prescribe the majority answers on every query of size at most τ. For each single query these are realized by some$v_{i} ∈ A ⊆$B, since fewer than κ indices are exceptional. Thus they have local placements. Lemma 6.4 gives a placement realizing all of them in an order enlargement of B. This is an actual tuple in an extension object, and Theorem 6.6 makes its type unique, since τ ≥ g(σ). This type is$p^{B}.$Its restriction to A equals p by the same testing criterion.

For a larger desired bounded query size τ', repeat with a power closed bound at least c(σ, τ'). The comparison of sequences just proved identifies the resulting type with$p^{B}$on the initial testing threshold and hence everywhere. In a mixed-level use, this additional direct majority evaluation is asserted only when its costs remain below the originating level. The type itself is already actual over B, and its diagrams at larger arities are those of this actual type; no averaging inside a smaller model at unbounded arities is being asserted.

Restriction to a subtuple commutes with every majority evaluation. Choose the threshold large enough for both arities and use testing to obtain equality of types. Isomorphism invariance follows by applying the isomorphism to the sequences and their query diagrams. For transitivity, let J ⊆ B be a canonical approximation sequence for$p^{B}$at a sufficient fixed threshold, and retain an original sequence I ⊆ A at that threshold. The latter computes$p^{B}$on queries in B by the construction. Move a query in C into B over I ∪ J. The two sequences give the same answer there, because each computes$p^{B}.$The first also computes$p^{C},$and the second computes$(p^{B})^{C}.$Testing proves transitivity. All these sequence lengths can be chosen as the uniform bounds in Lemma 6.9, below the smallest originating level. This proves the mixed-level assertions as well.

Finally, suppose J ⊆ B has the same whole diagram as a fixed code I ⊆ A at threshold c(σ). For each query Z in B of that size, saturation realizes D(J, Z) over I in A. The resulting majority is therefore well-defined, with the same exception estimate. For each query one of the entries of J realizes the answer in B. Coherence, compact placement and testing give an actual unique type, as in the preceding construction. Moving queries over code sequences shows that an arrow carrying J into a larger object gives exactly its free lift there. The code length and every threshold used here depend only on σ and the fixed scheme, which proves the final assertion.

Lemma 6.11 (An average criterion for descent). Let A → B have eligible sizes ν ≤ µ, and let q = tp(d/B) be actual, with |d| = σ < ν. Choose χ ≥ c(σ) below ν. Suppose that a bounded sequence$I = (d_{i}: i <$κ) in A, with$χ + ℵ_{0} < κ <$ν, has majority value q↾Z on every query Z ⊆ B of size at most χ, with at most |Z|$+ ℵ_{0}$exceptions. Then q is the free lift of its actual ν-restriction to A.

Proof. Let p = q↾A and choose a canonical sequence J ⊆ A approximating p at size χ. For a query Z ⊆ B of that size, mixed saturation moves it to$Z_{0}$in A over the whole I ∪ J. The total length is less than ν. The majority from I on Z computes q, and on$Z_{0}$computes p. These answers agree by diagram preservation. The majority from J on$Z_{0}$also computes p, and on Z computes$p^{B}.$Hence q and$p^{B}$agree on all χ-queries. Apply the testing criterion. The same proof works for an arbitrary longer indexed family whenever a bounded subsequence of the displayed length retains the exception estimate.

## 6.3 Products and local character

Proposition 6.12 (Products of bounded types). For bounded types p(x), q(y) over A, realize p in an extension B ≥ A and then realize$q^{B}$in a further extension. The joint type of (x, y) over A, denoted p ⊗ q, is independent of all choices. Binary products are symmetric, with the indicated permutation of coordinates. Finite products associate, are permutation invariant, and commute with coordinate projections. Furthermore

(p ⊗$q)^{B} = p^{B}$⊗$q^{B}.$(4)

These assertions hold across eligible levels when all originating arities and uniform testing costs are bounded at the smallest level.

If x/B is free from A and x, d have product type over B, then x and (d, e) have product type over A for every bounded tuple e from B.

Proof. Two realizations of p can be identified over A by amalgamation. In a common model containing their witnessing extensions, the free lifts of q agree by stationarity and restriction. A second type-identifying amalgamation identifies the realizations of q. This proves independence of the choices in the definition.

We give the cardinal calculation for symmetry. Fix a bounded query Z in A, and put e = |Z| + |x| + |y|$+ ℵ_{0}.$Choose approximation sequences$(a_{i}: i <$κ) for p and$(b_{j}: j <$λ) for q, sufficient for queries of size e, where

$κ = e^{+}, λ = κ^{+}.$

All these cardinals lie below a sufficiently closed level. For the array$M_{ij} = D(a_{i}, b_{j},$Z), first realize x and freely realize y. The resulting answer R is obtained by first taking the majority in i and then in j. Except at at most e columns, the column majority is R, and in each such column at most e entries differ from R. Reversing the realization order gives an answer S: except at at most e rows, its row majority is S, with at most e exceptions in each such row. The bounds concern the size of (x, Z) or (y, Z), not the lengths of the sequences.

There are κ good rows. Their exceptional columns together number at most κe = κ. Since λ > κ, choose a column outside this set and outside the at most e bad columns. Every good-row entry in that column equals S, whereas all but at most e entries equal R. As κ > e, some entry has both values. Thus R = S. This explains why two equally sized sequences would not suffice for the argument. Testing gives symmetry of the joint types.

For (4), take the two sequences just used in A and a sequence K ⊆ A approximating the actual old product. Choose their accuracy at a common sufficient test threshold. Given a query Z in the enlarged base B, move it into A over these three whole sequences. Both successive free evaluations over B are the iterated majority of the same array$D(a_{i}, b_{j},$Z). Transitivity permits the original sequence for the second factor to be used after the first factor has been realized. The query movement identifies this array with the old array in A, where it computes p ⊗ q. The sequence K evaluates that old product and computes its free lift on the original query. The answers therefore agree. Testing proves the formula. All the lists fixed during the query movement are bounded, including in the mixed case.

Now realize x, y, z successively along a chain of free lifts from A. The first two form p ⊗ q, and z is free over a model containing them, so the joint type is (p ⊗ q) ⊗ r. Over a model containing x, the last two have type$q^{B}$⊗$r^{B} =$(q ⊗$r)^{B},$by the formula just proved. Thus the same joint type is p ⊗ (q ⊗ r). This proves associativity. Projection follows from the projection property of free lifts in each successive realization. Associativity and the binary symmetry permit every permutation of a finite list of factors.

For the final assertion, use symmetry and a type-identifying amalgam to realize the given joint type by first putting d in a model containing B and then realizing x freely over it from B. Since x/B is itself free from A, transitivity makes this last realization free from A. The tuple (d, e) is in the intervening model, so the definition of product gives the assertion. The amalgam identifies the full original tuple over B, and hence retains its actual joint type over A.

Proposition 6.13 (Local character and continuity). Let$(A_{i}: i <$δ) be an increasing chain of objects at one eligible level µ, whose union A has size µ, and let δ be a nonzero limit ordinal. If p = tp(v/A) and either v is finite or |v| < cf(δ), then p is free from some$A_{i}.$If, in addition, every restriction$tp(v/A_{i})$is free from a fixed base$X ≤ A_{0},$then p is free from X.

Proof. Pass to a cofinal chain indexed by the regular cardinal γ = cf(δ). Choose a sufficient testing size χ ≥ c(|v|$+ ℵ_{0})$below µ. If γ is larger than the size of an approximation sequence for p at that threshold, the whole sequence lies in one stage. Its exception estimate is still correct on all queries in A, so Lemma 6.11, at the same level, applies.

In the other case γ < µ. Choose a regular κ < µ above γ, χ, |v| and the needed bounds, and take κ approximations inside A. Every whole approximation tuple belongs to some stage: this uses finiteness, or the hypothesis |v| < γ. If every stage contained fewer than κ of the tuples, regularity of κ and γ < κ would make their union contain fewer than κ tuples. Thus one stage contains κ of them. Pass to those indices. The exception estimate survives unchanged, and Lemma 6.11 again identifies p as the free lift from that stage.

For the final assertion, local character makes p free from some$A_{i}.$Its restriction there is free from X by hypothesis. Transitivity in Theorem 6.10 makes p free from X.

## 6.4 Universal strips and approximate retractions

The remaining construction provides maps from an extension back into its base which fix each individual base element at all but finitely many indices. It will allow isolation to descend from a larger level without requiring a bounded tuple to lie in one stage of a countable exhaustion.

Lemma 6.14 (Closure of a bounded support set). Let$J ⊆ J^{∗}$be linear orders, let V be a convex strip in$J^{∗},$and put$J_{0} = J$\ V. Allow any fixed finite coloring of positions in$J_{0},$including their side of V. Let$T^{∗} ⊆ J^{∗}$and$S_{0} ⊆ J_{0}$be bounded sets. Given an infinite χ, choose an infinite λ with

$λ ≥ χ + |T^{∗} | + |S_{0} |, κ = 2^{λ}.$

There is$S ⊆ J_{0},$of size at most κ, containing$S_{0} ∪ (T^{∗} ∩ J_{0}),$with this property: for every R ⊆ S of size at most χ and every indexed tuple Q of at most χ positions from$J_{0},$there is an equally indexed tuple Q' in S having the same order, equality and color pattern over$R ∪ T^{∗}.$In particular all positions named by R are fixed whenever they occur in Q.

At a strong limit level with the displayed input bounded, S is bounded. The assertion needs no well-order hypothesis on J.

Proof. Build$S_{α}$for$α < χ^{+},$starting with the required set. At a successor stage, for every$R ⊆ S_{α}$of size at most χ, and every order, equality and color pattern of at most χ further positions over$R ∪ T^{∗}$that is actually realized in$J_{0},$choose one realizing tuple and adjoin its positions. Use unions at limits. If$|S_{α} | ≤$κ, the number of choices of R is at most$κ^{χ} =$κ, and the number of patterns for each R is at most$2^{λ} =$κ. Each chosen tuple adds at most χ positions. Consequently every stage and their union have size at most κ.

For R contained in the final union, regularity of$χ^{+}$puts all of R into a single stage. The actual tuple Q witnesses that its pattern was among the requirements processed at the next stage. Its chosen witness is the required Q'. Equality with elements of R and$T^{∗}$is part of the pattern, so it is preserved literally. This also covers arbitrary enumerations and repetitions in Q.

Proposition 6.15 (Universality of a fresh strip). Let C already satisfy the working package. In addition to its fixed template F, one may use a presentation G with the following properties: it has a fixed set of finite-support labels; every presentation G(J) used below, for an order of size µ, is an object of C at level µ; order embeddings give C-arrows; and the diagrams of its term lists are natural, including in the order enlargements and padded orders used. Assume also that these labels represent every element of G(J). Require µ to exceed the cardinality of the label set of G and to be closed under the bounds below with that cardinal included in their fixed input data.

Put A = G(J). Insert into J a fresh convex strip of size µ with countably many disjoint convex substrips, each of size µ, and denote the resulting object by$A^{+}.$Then every same-level extension of A embeds into$A^{+}$over A. In particular this applies to G = F and to well-ordered presentations. No separate union or categoricity assertion for a category of G-presentations is required.

Proof. We first realize a bounded type p(v/A) using just one fresh substrip V. Choose a testing threshold χ ≥ c(|v|$+ ℵ_{0})$large enough also for |v| and the number of labels of G. Take a sequence I in A approximating p at query size χ. Represent its entries by G-terms and collect their old supports in$S_{0} ⊆$J. Apply Lemma 6.14, with the side of V recorded, to obtain a bounded S ⊆ J. Its closure permits every at-most-χ old query pattern to move into S over any at-most-χ subset of S. The approximation supports, which may be larger than χ, can instead be included as the fixed set$T^{∗}$in that Lemma. Thus all of them are fixed during every such movement.

Let$P_{S}$be the set of all G-terms on S. It is bounded, since G has a bounded set of finite-support labels. The natural parameter diagram of$P_{S}$is the same in A and in G(S ∪ V). The latter is a level object because |V | = µ. Saturation there realizes the desired whole joint diagram of (v,$P_{S}),$giving a tuple w whose supporting positions belong to S ∪ V. Only at most |v|$+ ℵ_{0} ≤ χ$of its supporting positions are old; call them R ⊆ S.

For any query Z in A of size at most χ, move its chosen support tuple into S over R and the fixed approximation supports, preserving the side of V. Let Z' be the resulting term tuple. All comparisons with the new supporting positions of w in V are forced by that side. Naturalness therefore gives D(w, Z) = D(w, Z'), D(I, Z) = D(I, Z').

The majority from I computes p on both queries. The chosen realization of (v,$P_{S})$gives D(w, Z') = p↾Z'. It follows that D(w, Z) = p↾Z. Testing of actual types, using a natural F-chart of A if G differs from F, proves tp(w/A) = p. Naturality of G was used only for the displayed support movements; the testing and saturation are those already proved in C.

Now let B ≥ A be arbitrary and choose increasing bounded lists$d_{n}$exhausting it, including countable strong-submodel exhaustions in every vertex. Use the first substrip to realize the type of$d_{0}$over A. At subsequent step n, the target base consists of A and the whole previously used substrips. Suppose$d_{n}$has already been assigned there with its correct type over A. Theorem 6.6 amalgamates B with this target base over A, identifying that entire assigned tuple. In this amalgam,$d_{n+1}$has an actual bounded type over the target base. Apply the one-substrip construction to the next fresh substrip. Since its type includes equality with the already assigned coordinates, the new assignment extends the previous one. The final union of the assignments lands in$A^{+}.$The arrow criterion applies to the included strong-submodel exhaustions, so it is an arrow$B → A^{+}$over A.

Corollary 6.16 (Approximate retractions). For same-level A ≤ B there are arrows$(r_{i}: B →$A: i < µ) such that, for every a ∈ A,

{i < µ:$r_{i}$(a) ̸= a}$< ℵ_{0}.$

The maps are not asserted to fix all of A at once.

Proof. Present A by F on a well-order consisting of µ disjoint convex blocks$J_{i},$each of cardinality µ and itself containing countably many convex substrips of that size. The whole order still has cardinality µ, and the working package identifies its presentation with A. Let$A_{i}$be the presentation on the complement of$J_{i}.$It is a level subobject of A. Proposition 6.15, with$J_{i}$as the inserted strip, embeds B into A over$A_{i};$call the arrow$r_{i}.$Choose one finite supporting set for a. It meets only finitely many$J_{i}.$For every other index,$a ∈ A_{i}$and$r_{i}$(a) = a.

Lemma 6.17 (Descent through approximate retractions). Let A ≤ U be objects at an eligible level µ, and let A' ≤ U' be objects at an eligible level ν ≤ µ, with compatible arrows A' ≤ A and U' ≤ U. Suppose there are arrows$(r_{i}: U →$A: i < ν) such that every a ∈ A is fixed for all but finitely many i, and$r_{i}$[U'] ⊆ A' for all i < ν. Then for every tuple d in U' of length less than ν, its actual type over A is the free lift of tp(d/A'; U'). All comparisons are comparisons of the working diagrams, including mixed-level diagrams at arities bounded at ν.

Proof. Coherence makes$r_{i}$↾U': U' → A' an arrow: its image and A' are subobjects of A, and its image is contained in A'. Put σ = |d|$+ ℵ_{0},$choose χ ≥ c(σ) below ν, and choose$χ^{+} ≤ κ <$ν. Retain any κ indices and form$I = (r_{i}$(d)) on them. This is a bounded concatenated list in A'.

For a query Z ⊆ A of size at most χ, at most |Z|$+ ℵ_{0}$indices fail to fix every element of Z. At every other index, arrow preservation gives

$D(r_{i}$(d), Z)$= D(r_{i}$(d),$r_{i}$(Z)) = D(d, Z).

Thus I has the required majority estimate for the actual type over A. On queries in A' the same identity is a comparison at level ν, using the restricted arrows. Mixed preservation identifies it with the larger-level identity.

Apply Lemma 6.11 to A' ≤ A. Its restriction type is precisely tp(d/A'; U'), by Corollary 6.7. The conclusion is therefore the stated free lifting of the actual type, including tuples that span a chosen resolution of U'.

The preceding calculus will be applied only after the working package has been established for the relevant scheme. Its approximation, testing and support-closure bounds are functions of fixed scheme data and bounded input arities. This is the uniformity needed when the schemes are iterated at finite depths.
