# 8 Adjoining a marked increment


Throughout this Section, C is a working scheme whose arrows are precisely the componentwise strong embeddings preserving its specified maps and distinguished data. In particular, there is no additional condition on intersections or on bases. We use the working package of Definition 5.2, and the calculus and isolation results of the preceding two Sections, at sufficiently closed eligible levels. All refinements in this Section have fixed set parameters: the input scheme and template, the prescription below, and, after it is chosen, the new template. An unbounded output class is asserted under the eligible-subclass hypothesis of Convention 5.3. This supplies both arbitrarily large closed samples and levels that remain eligible while having cofinally many smaller template-valid levels. Theorem 13.5 supplies the simultaneous closure bookkeeping.

Definition 8.1 (A stationary prescription and its marked pairs). A stationary finite prescription for C assigns to every object X a type$p_{X}$of a finite tuple, with specified component sorts. The assignment commutes with isomorphisms, and, for every arrow X → X', including an arrow between eligible levels,$p_{X'}$is the free extension of$p_{X},$after identifying the base by that arrow. The prescription is given by fixed set-coded data of the kind used in the applications.

An object of$C^{b}$at level µ is a triple

(X, Y, b), X ≤ Y,

where X, Y are objects of C at level µ, b ∈ Y realizes$p_{X},$and Y is all-dominated over X + b. The inclusions and the mark are part of the structure. An arrow is a commuting pair of componentwise strong embeddings taking the mark to the mark. The notation X ≤ Y records an actual inclusion; arbitrary arrows are put into this form by replacing the codomain with an isomorphic copy.

Recall that all-domination quantifies over every tuple of length strictly below the level. It is not just domination for the members of one fixed exhaustion of Y.

Lemma 8.2 (The pair isomorphism test). After a further closure refinement, marked pairs exist over every object X. An isomorphism e: X ≃ X' extends to an isomorphism

(X, Y, b) ≃ (X', Y', b').

More precisely, for bounded tuples t and t' in the respective pair structures, such an extension can take t to t' if and only if e takes the indicated base entries to their counterparts and transports

tp(t, b/X) to tp(t', b' /X').

Entries are occurrence-tagged when more than one component is used.

Same-level arrows preserve bounded pair orbits. Moreover, comparisons of bounded pair tuples are preserved and reflected when two pairs at one common small level are mapped to two pairs at a common larger eligible level. All tuple lengths and the bounds needed for the comparison are strictly below the smaller level.

Proof. Existence is Theorem 7.9 applied to the finite prescription. The pointed existence and uniqueness assertions follow from Proposition 7.5: its back-and-forth form retains prescribed bounded tuples with the same type together with the mark. Necessity of the displayed type condition follows from invariance.

Suppose first that a pair maps to another pair at the same level. The prescribed type of the mark in the second base is the free extension of its type in the first base. For each bounded t in the first upper object, Lemma 7.2 therefore says that its joint type with the mark in the second base is the free extension of its old joint type. Choose bounded approximation lists in the old base computing this joint type and its mark marginal at the needed testing arities, and include the base entries of t. An isomorphism of the two bases matching these lists exists by bounded diagram homogeneity in C. The approximation calculation and the testing bound show that it transports the whole joint type. The first part of the Lemma gives an isomorphism of the pairs taking the old tuple to its image.

The argument also proves preservation when two small pairs with a bounded match are mapped to a common larger level. Their joint types with the marks lift freely by the mixed-level form of Lemma 7.2. Matched small approximation lists can be matched in the two large bases by underlying homogeneity. Those lists compute the transported types, and the pair isomorphism test applies at the large level.

For reflection, let a large pair isomorphism match the two images. It transports the first small approximation list into the second large base. Inside the second small base, realize a copy of this list over the second small approximation list and the required base entries. This is a bounded realization problem: the diagram of the second list is unchanged under its mixed embedding, and mixed saturation in the underlying scheme realizes the joint diagram. Small-level homogeneity extends this match to an isomorphism of the small bases.

To check that the small isomorphism transports the types, test a parameter tuple of the size required by the uniform testing bound. Match that test upstairs over both approximation lists. Each list computes the free extension of its small type there, and the large pair isomorphism identifies the answers. Transport back to the small bases. The answers agree on all tests up to the bound, and Theorem 6.6 identifies the whole types. Apply the small pair isomorphism test. All lists used have bounds in the input arities; closure puts them below the small level.

## 8.1 A template before chain closure

We first construct a template whose individual values are marked pairs. The proof first transfers isolation for tuples with a common finite bound on the support of each entry, then removes that restriction by embedding into an all-dominated object. Neither step uses chain closure for marked pairs. That remaining assertion is proved only after the two-part testing bound is available.

Lemma 8.3 (The marked-pair template). There is a fixed set-sized finitary term template$F^{b}$such that, on a further class of sufficiently closed eligible levels, its values on well-orders are objects of$C^{b}.$Order embeddings give the componentwise arrows of Definition 8.1, also between such levels. Every marked pair at a level is isomorphic to a value of this template of that size.

At this stage the following properties are available without using chain closure in$C^{b}:$mixed downward Löwenheim–Skolem, preservation and reflection of bounded diagram comparisons, bounded diagram saturation, and the exhaustive-list criterion for being an arrow.

Proof. The samples and their language. Let F be the template of C. At arbitrarily high closed input levels choose a pair X = F (J) ≤ Y, Y ≃ F (Z),

with Y all-dominated over X + b. Choose the presentations sufficiently rich for any prescribed set-sized order-saturation bound. We may take J, Z, and a further order W, to be padded dense orders. Padding means that the order has a well-ordered subset of its own cardinality. In addition, W has many disjoint convex substrips, each of the level size. Proposition 6.15, in its presentation-invariant form, puts Y over X into

L = F (J + W).

All these choices concern the already working scheme C.

Expand a sample by sorts for the orders and charts, chart evaluation maps, the inclusions, and the mark. For each element of a chart choose a representing label and its finite list of positions. Representation tags record the label arity; coordinate functions have default values outside their arity. Include a sort of retraction indices and an evaluation function for a family

$r_{i}: Y −→ X$

from Corollary 6.16. Distinct indices are retained as distinct indices, even if two of their maps happen to be equal.

Finally include finitary LS witness functions for the underlying K-vertices. For each finite list in a vertex choose a small strong submodel containing it and the models already chosen for its proper sublists, and enumerate that model. Coherence gives strong inclusions between these small models. Perform this in all the finitely many vertex occurrences, including the required inclusion data. In the term closure of any generating set, these enumerated small submodels form a directed cover of each vertex intersection: every finite tuple has its witness model there, and a witness for a combined tuple contains the earlier witnesses. Thus the intersection is strong by the directed-union axioms. Designated entries keep the necessary sorts nonempty.

This is one fixed set-sized finitary expansion. It names neither the diagram table nor all the elements of a high sample. Its number of terms has a bound in the old template language and the fixed input data.

Homogeneous finite hulls. In each sample take a long ordinal-indexed sequence bundling an increasing sequence in each order sort and a sequence of distinct retraction indices. Color a finite index set by the complete labelled atomic diagram, with negations and equalities, of its term hull and the inclusions among the hulls of its subsets. The palette has a fixed set bound. The finite-arity extraction used in Theorem 2.6 chooses compatible colors at all finite arities while retaining arbitrarily large homogeneous samples. Retain at the same time arbitrarily high prescribed order-saturation bounds. Treat the requested homogeneous size and the requested order saturation as one cardinal demand. If each possible next color had a bound on the demands it could meet, the supremum of those set-many bounds would contradict the availability of samples. Thus a single next color retains unbounded demands. Thinning the horizontal sequence does not change the saturation of its ambient chart orders.

Let H be a well-order of a sufficiently closed input size λ, and evaluate the extracted term data on H. Write the resulting chart orders as$J_{H}, W_{H}, Z_{H},$and the underlying objects as$X_{H}, Y_{H}, L_{H}.$The evaluation and representation functions give both directions of generation:

$X_{H} = F (J_{H}), Y_{H} ≃ F (Z_{H}), L_{H} = F (J_{H} + W_{H}).$

Representation equalities concern fixed finite tuples of terms and therefore hold in actual homogeneous samples. The increasing distinguished sequences pad the chart orders. Extending the old template to padded orders uses only the underlying scheme’s chain and directed-union properties.

The vertex LS witnesses prove

$X_{H} −→ Y_{H} −→ L_{H}$

componentwise strong over$X_{H} → L_{H}.$They also prove this for maps induced by order embeddings of H, including mixed sizes. Each witness model is an isomorphic copy of its sample model, and the full component map is a directed union of these strong maps. Since arrows of C are componentwise, these are underlying arrows. All-domination remains to be proved.

Bounded horizontal arity. Fix a bounded list u = (b, c) from$Y_{H}$such that each individual entry has a term representation using at most q horizontal indices, for one common finite q. This is a bound per entry: the union of the supports of the whole bounded list may be infinite. Term depths need not be bounded. Coordinate functions and representations preserve finite support. Thus the positions representing u in$J_{H} + W_{H}$use a fixed finite number of indices per position. The positions representing$r_{i}$(u) in$J_{H},$for the λ distinguished retraction indices, require only the additional index i. Comparing two such positions requires at most twice a fixed finite arity.

Take an actual sample homogeneous at these arities, with a horizontal index set containing an order copy of H. The specified positions match those representing an actual tuple$u_{∗} ∈ Y$and its images under the corresponding actual retractions. Choose the sample with order saturation above λ. Extend the partial matches to embeddings of the entire orders$J_{H}, W_{H}$into the respective sample orders. In a recursion of at most λ steps, each next position specifies an order pattern over at most λ earlier positions, and sample order saturation realizes it. The initial partial maps are order embeddings by the recorded comparisons. We are not extending a map of the entire expanded term hull.

The host-order embedding identifies u with$u_{∗}$and embeds$X_{H}$into X. The mixed stationary prescription first shows that the mark in$Y_{H}$realizes$p_{X_{H}}.$We next prove the stronger assertion needed for isolation:$tp(u_{∗}$/X) is the free extension of$tp(u/X_{H}).$(7)

The images of$u_{∗}$under the λ selected actual retractions belong to the embedded$X_{H},$because their representing positions were included in the partial matching. Choose a test bound χ < λ above the costs for the arity of u, and retain a set of κ selected retractions with$χ + ℵ_{0} < κ <$λ. Their images of$u_{∗}$form a bounded list in$X_{H}.$For each Z ⊆ X with |Z| ≤ χ, all but at most |Z|$+ ℵ_{0}$of these retractions fix Z pointwise. At every other index, diagram preservation identifies the diagram of its image of$u_{∗}$with Z with the diagram of$u_{∗}$with Z. Thus this image list computes the actual type over X with the majority estimate of Lemma 6.11. That Lemma gives (7). Only images of the tested tuple have been placed in$X_{H};$closure of the entire small upper object under these retractions is neither claimed nor needed here.

The actual sample pair is all-dominated. Apply Lemma 7.6 to (7); its fragment bound is below λ by closure. It follows that tp(b,$c/X_{H})$is isolated relative to b.

Removing the arity restriction. Let V be all-dominated over$X_{H} +$b', with b' of the prescribed type. We construct an arrow$Y_{H} −→ V$

over$X_{H},$taking b to b'. Choose nested bounded lists exhausting$Y_{H}$in countably many steps. They may be chosen so that at each step every entry uses at most a fixed finite number of horizontal indices: increase a cardinal bound cofinally to λ and the finite index-arity bound at the same time. Every term has finite arity. Include also full enumerations of small vertex witness models for finite index sets in the corresponding bounded part of H. Their enumerated entries still have uniformly finite horizontal arity per entry, independently of term depth.

At each step the whole new list, the preceding list, and b satisfy the isolation conclusion already proved. The constructive primeness argument of Proposition 7.5 realizes the new list over the previous assignment and$X_{H}.$Its isolating fragment together with the preceding list is bounded; underlying saturation supplies the realization. Isolation gives equality of the full types over$X_{H}.$The included vertex witness models give strongness of the union map. Every bounded tuple of its image in V has isolated joint type with the mark. Consequently every bounded tuple of$Y_{H},$with no arity restriction, has this property. Thus$Y_{H}$is all-dominated.

The remaining pre-closure properties. Any marked pair at the level has a base isomorphic to$X_{H},$and Lemma 8.2 extends this to a pair isomorphism. The same Lemma gives orbit preservation and mixed reflection. For a set of at most ν entries in a larger pair, take its horizontal supports and a well-ordered subpresentation of size ν containing them. Its value is a marked pair by the individual template assertion just proved; coherence gives mixed downward Löwenheim–Skolem.

Naturalness on well-orders follows by putting any fixed bounded patterns into a common well-order enlargement and using orbit preservation. Mixed reflection makes these comparisons independent of the eligible level. Here are the remaining diagram details, without assuming the union clause in Definition 5.2. Define comparison of bounded term patterns by their pair isomorphism orbits at any eligible level. The preservation and reflection just proved make this independent of the level. At each fixed arity, the labels and order patterns belong to a fixed set, giving a uniform orbit bound. A mixed arrow factors, by mixed downward Löwenheim–Skolem and coherence, through a subpresentation of the target at its source level. Same-level orbit preservation in this factor and the level-independent pattern comparison give mixed diagram preservation. For saturation, represent a possible joint diagram in a larger well-ordered pair presentation. Its support has size below the receiving level, so that well-ordered support pattern embeds in a well-order at the receiving level. Evaluating$F^{b}$there realizes the joint diagram. The old subtuple has the orbit of the prescribed actual old tuple, so an isomorphism of the pairs carries the new realization over that tuple. An exhaustive diagram match is componentwise strong by its small vertex enumerations and respects the inclusions and mark, so it is a pair arrow. No union-object assertion for$C^{b}$was used.

## 8.2 A testing bound beside an old small pair

The following form of testing will be used when extending a partial map. It separates the use of the pair template from pair-chain closure, which is still to be proved.

Lemma 8.4 (Testing beside an isolated small upper object). Let ν < µ be sufficiently closed levels where Lemma 8.3 holds. Suppose

A ≤ U, A ≤ C, C ≤ T, T'

are underlying arrows, A, U are at level ν, and C, T, T' are at level µ. Suppose (A, U, b) is a small marked pair inside T, its specified image (A, U', b') is inside T', and the map U ≃ U' fixes A. Suppose further that b/C and b' /C are the prescribed free extensions and corresponding bounded tuples of U, U', jointly with the marks, have equal types over C.

For each σ < ν there is a bound k(σ) < ν, uniform in these objects, with the following property. If v ∈ T and v' ∈ T' have length at most σ, their comparisons on joint tests from U and C of total size at most k(σ) determine their comparisons on all such tests of total size < ν. Tests in U' are read by the specified map.

Proof. Present (A, U, b) as$F^{b}$(H) on a well-order of size ν. Given a questioned bounded tuple from C, include it over A in a level-ν subobject V ≤ C. Append a universal strip to H, retaining size ν, to obtain H'. The base presentation of the pair template is a natural term presentation into the already working scheme C. The presentation-invariant universal-strip result embeds V over A into$A_{H'}.$Corollary 6.7 then embeds$A_{H'}$into C over this copy of V.

The joint bounded diagrams of U and$A_{H'}$inside T are the diagrams of the natural layout

$U_{H} ∪ A_{H'}$inside$U_{H'}.$(8)

Indeed, each bounded tuple of U, together with b, is isolated over A, whereas the marginal of b over$A_{H'}$is the prescribed free extension. Lemma 7.2 determines its joint type. The argument applies both to (8) and to the specified image inside T'. It includes equalities between the two parts of the layout; an additional actual overlap is not ignored.

For a bounded candidate tuple in either ambient, each bounded test over the layout has a local realization in$U_{H'},$by mixed diagram saturation in C. Apply Lemma 6.4 to lift its comparisons to a placed comparison over (8). The layout has two well-ordered horizontal segments with designated term parts. Proposition 6.3 gives a bound depending on the candidate arity and the fixed template, not on H, H' or V.

If the two candidates disagree on the questioned test, their placed comparisons disagree and yield a witness within that bound. Its second-part parameters lie in$A_{H'},$already embedded into C; its first-part parameters lie in the original U. This is the required small witness. Close ν under the testing and placement costs for this fixed layout.

All padded-order repetitions here concern the horizontal top presentation as a functor into C. Its extension to padded orders uses chain closure of C, not of$C^{b}.$

## 8.3 Chain closure with all bounded tuple lengths

Lemma 8.5 (Chain closure). At further sufficiently closed levels,$C^{b}$has unions of increasing chains of total size equal to the level. The union is a marked pair. The common-upper-bound clause holds as well, including into an eligible larger level.

Proof. Fix a level µ closed under the bounds of Lemma 8.4, with cofinally many smaller levels at which Lemma 8.3 and the required underlying results hold. We do not require pair-chain closure at the smaller levels.

Write the chain, replacing arrows by inclusions, as

$(C_{i}, T_{i},$b) (i < α),

and its component unions as C, T. The underlying scheme gives C ≤ T and its union maps. The actual marginal of the finite mark over C is$p_{C}:$the marginals at proper stages are the prescribed free extensions, and Proposition 6.13 gives stationary continuity for this finite tuple.

Induct on the chain length. The shorter-length assertion allows intermediate limit unions to be inserted. Restricting cofinally, we may consider a continuous chain indexed by a regular cardinal δ. If a bounded tuple d ∈ T is contained in some$T_{i},$its type with b is isolated over$C_{i};$Lemma 7.2 gives isolation over C.

Suppose d is not contained in a proper stage. Its entries occur at cofinally many indices, so

δ ≤ |d| < µ.

Choose an eligible ν < µ strictly above |d|$+ δ + ℵ_{0},$closed under the arity, isolation, approximation, and two-part testing bounds to be used. Small pair objects below will come from Lemma 8.3 or from explicit descent; pair-chain closure at ν is not an induction hypothesis. Choose

B ≥ C all-dominated over C + b',$b' |= p_{C}.$

It suffices to find an image d' in B with tp(b, d/C) = tp(b', d' /C), because the type on the right is isolated relative to b'. We obtain this image by building small pairs inside the given chain and compatible maps from their upper objects into B. The maps must preserve types over the entire union base C, including for tuples that span a limit of the small pairs.

Specifically, we construct continuous systems of underlying level-ν objects$A_{i} ≤ U_{i}$inside$C_{i} ≤ T_{i},$for i < δ, and compatible arrows$f_{i}: U_{i} →$B, satisfying:

1.$b ∈ U_{i}, f_{i}$(b) = b', and$f_{i}$fixes$A_{i};$

2.$(A_{i}, U_{i},$b) is a marked pair;

3. for every tuple u from$U_{i}$of length < ν,

tp(b, u/C) = tp(b',$f_{i}$(u)/C); (9)

4. every entry of d is eventually included.

Equation (9) is computed in the actual underlying ambients T, B.

Retractions prepared for the limits. For every nonzero limit j ≤ δ, put$C_{δ} =$C, and choose in advance families of ν approximate retractions

$r^{j_{ξ}}: T → C_{j},$s:$B → C_{j}$(ξ < ν). (10) jξ

They exist in the underlying scheme since$C_{j} ≤$T, B; each old parameter of$C_{j}$is fixed outside a finite set of indices in each family. At a limit we require

$r^{j_{ξ}} [U_{j}] ∪ s [f_{j} [U_{j}]] ⊆ A_{j}$(ξ < ν). (11) jξ

We describe the scheduling. Once an entry x and its image$f_{i}$(x) have been chosen at stage i < j, each value in (10) belongs to$C_{j},$hence to some$C_{k}$with k < j by continuity. Assign its inclusion in the small base to a successor stage k' with i < k' < j and k ≤ k'. Such a stage exists because j is a limit. A value is never requested before it is available. New entries and images create at most ν · ν · |δ| = ν requests at a stage. The union of the requests assigned to any one stage still has size at most ν: there are < ν stages, each of size ν. Underlying mixed downward Löwenheim–Skolem can therefore include all of them. This also schedules j = δ, whose families were chosen in advance.

Small objects at a nonlimit stage. At an initial or successor stage i, include the preceding small base in the new base and the preceding small top in the new top, the requests now due, and the designated entries of d available in$T_{i}.$Choose ν approximate retractions$T_{i} → C_{i}.$Alternate for ω steps the following operations: choose a level-ν subobject of$C_{i}$containing the current base, all due base entries, and all the chosen retraction images of the current top; then choose a level-ν subobject of$T_{i}$containing that base, the current top, and required top entries. Each request has size at most ν. Underlying coherence gives increasing arrows and the base-to-top arrows. Take underlying unions to obtain$A_{i} ≤ U_{i}.$

The marginal of b over$A_{i}$is$p_{A_{i}},$by restriction of the mixed prescription from$C_{i}.$Lemma 6.17 says that every < ν tuple from$U_{i},$jointly with b, has actual type over$C_{i}$freely extended from$A_{i}.$Its type over$C_{i}$is isolated relative to b, since the given large pair is all-dominated. The uniform fragment bounds are below ν. Lemma 7.6 proves that$(A_{i}, U_{i},$b) is a small marked pair. Only underlying unions were used in obtaining it.

Extending the map at a nonlimit stage. Let$U^{−}, A^{−}, f^{−}$be the preceding small top, base, and map, when present. The old map fixes every element of$U^{−} ∩$C, not just$A^{−}:$apply (9) with that element as a parameter. Thus fixing$A_{i}$is compatible with the old map on their overlap.

Enumerate$U_{i}$by nested bounded lists in countably many steps, including the mark and whole smaller strong vertex submodels. Place these lists in B, retaining the old map, and require equality on all joint tests of size < ν from$U^{−}$and C. For a current source list v, let$χ_{0} < ν$be the bound of Lemma 8.4. With no preceding stage, use whole-base testing instead.

For every old test u from$U^{−}$of length at most$χ_{0},$the tuple (b, u, v) lies in$T_{i}.$Its type over$C_{i}$is isolated, and its actual mark marginal over C is free. Lemma 7.2 gives an isolated type over C. Choose an isolating fragment

$Z_{u} ⊆$C,$|Z_{u} | ≤$h(|b, u, v|) < ν.

Include the empty old test. The union of the fragments has size at most$ν^{χ_{0}} ·$h(|b|$+ χ_{0} +$|v|). This may exceed ν, but it is less than µ, since µ is strong limit and ν < µ.

The placement parameters are$f^{−} [U^{−}],$the fragments, b', previous assignments in the current exhaustion, and the required fixed entries of$A_{i}.$Their total size is < µ. Choose a test size χ < ν large enough for$χ_{0},$the current list, the fragment bounds, all relevant equalities, and the compact-placement costs. Specify joint diagrams on all parameter tests of size at most χ, using the actual source diagrams.

Every such simultaneous local request is possible in B. A query of size at most χ may meet many of the fragments$Z_{u},$but all those entries together form one tuple from C of size at most χ.

Combine that tuple, its old entries from$U^{−},$fixed base entries, and previous assignments into one parameter list. For the first placement, (9) matches its old entries over C; if there is no old stage, the prescribed mark types give the initial match. At later placement steps, the maintained joint comparisons give the match also with previous assigned entries. The combined list has size < ν. Underlying saturation in B realizes the diagram of the new source list over these parameters.

The compact-placement cost depends on the current tuple arity,$χ_{0},$the uniform fragment bound, and the fixed labels, rather than on the size of the entire union of fragments. For an infinite σ < ν bounding the current tuple arity, choose χ < ν above these costs with$χ^{σ} =$χ. Each parameter subset of size at most χ then has at most χ support profiles. The hit-and-separation construction tests only a final parameter set of size at most χ. Apply Lemma 6.4 to the coherent local requests in a well-ordered presentation of B. It gives a placement in an order enlargement. The whole parameter set has size < µ, so underlying saturation realizes its joint diagram with that placement back inside B. In particular the realization agrees on every$Z_{u}$and all previously imposed equalities. Its mark marginal over C is$p_{C}.$Isolation gives the correct whole type over C for (b, u, v) when |u|$≤ χ_{0}.$Lemma 8.4 upgrades this to all joint tests of size < ν. Continue.

The union is an underlying arrow$f_{i}: U_{i} →$B, by the included strong vertex enumerations. It fixes$A_{i}$and takes b to b'. A < ν tuple of$U_{i}$might span this countable exhaustion. For such a tuple, the completed arrow gives the correct small type over$A_{i}.$The small pair is all-dominated, and both actual mark marginals over C are the prescribed free extensions. Mixed Lemma 7.2 identifies their types over C. This proves (9) for every < ν tuple.

Proper limit stages. For a nonzero limit j < δ, take underlying unions

⋃ ⋃ ⋃

$A_{j} =$i<j$A_{i}, U_{j} =$i<j$U_{i}, f_{j} =$i<j$f_{i}.$

They are underlying objects and an underlying arrow by the chain and mixed upper-bound clauses of C. Their size is ν, since |j| < ν. Scheduling gives (11). For every < ν tuple of$U_{j},$apply Lemma 6.17 on each side: its actual type over$C_{j}$is the free extension of its type over the common$A_{j}.$These small types agree because$f_{j}$fixes$A_{j}.$

The given large pair$(C_{j}, T_{j},$b) is all-dominated. Downward isolation transfer proves all-domination over$A_{j} +$b, without small-pair chain closure. The equality over$C_{j},$isolation there, and prescribed free mark marginals over C then give equality over C by Lemma 7.2. All proper-stage invariants are established.

The final limit. Take underlying unions$A_{δ}, U_{δ}, f_{δ}.$The families prepared for j = δ, condition (11), and Lemma 6.17 give equality of the actual types over C from their common type over$A_{δ}.$No isolation assertion for the final source pair has been used. In particular,

tp(b, d/C) = tp(b',$f_{δ}$(d)/C),

since |d| < ν and all its entries were included. The right-hand type is isolated by all-domination of B; hence the left-hand type is isolated relative to b. This covers every bounded tuple not already contained in a proper stage, and proves all-domination of T over C + b.

The union maps are componentwise strong by the underlying scheme. If all stages lie in a common marked pair, the underlying upper-bound clause gives a componentwise strong union map preserving the data and mark. That is precisely a pair arrow. The argument includes a larger eligible common upper bound.

Theorem 8.6 (The marked-increment working package). Let C be a working scheme with componentwise arrows and a stationary finite prescription as in Definition 8.1. Assume the eligible-subclass hypothesis of Convention 5.3. On an unbounded further class of sufficiently closed eligible levels,$C^{b}$is again a working scheme, with componentwise arrows, fixed template$F^{b},$and mixed arrows between these levels. The output class retains the eligible-subclass hypothesis.

The added language and bound recipes at this step have set-sized bounds in the input template and prescription. Thus the construction can be performed at each fixed finite depth without class-sized parameters or a language size depending on the level.

Proof. Lemma 8.2 gives the isomorphism test, orbit preservation, and mixed reflection. Lemma 8.3 gives individual template values and their mixed arrows, mixed downward Löwenheim–Skolem, natural bounded diagrams and saturation, and the exhaustive-list arrow criterion. Lemma 8.5 supplies the missing union-object and upper-bound assertions. Composition and coherence are componentwise.

The extraction added only finitary chart, representation, retraction, and LS-witness symbols with a fixed set bound. Further bounds were testing and placement costs for the old template and the fixed two-part layout of the new template, isolation and approximation costs, and a refinement permitting cofinally many smaller template-valid levels. These are fixed-parameter operations in the closure bookkeeping. No step requires small-pair chain closure before it is proved.
