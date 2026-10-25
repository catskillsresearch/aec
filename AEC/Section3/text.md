# 3 Reversing maps on bounded tuples


Throughout this Section, K is categorical unboundedly often, ℓ = LS(K), and E is the presentation of Theorem 2.6. The aim is to reverse a strong self-map on any one fixed bounded tuple in every sufficiently large categoricity model. We first construct index orders with uniformly controlled short-tuple orbits. Homogeneous-order orbit bounds already play a role in Shelah’s work; compare [She09, IV.5.1]. The alignment and elimination below establish the form needed at arbitrary categoricity cardinals.

For comparison, [BV15, Fact 1.4 and the discussion of Claim 1.5, pp. 3–4] records syntactic-characterization results under exponentiation or cofinality conditions and a gap in the attempted unrestricted extension. The bounded-tuple reversal needed here is proved directly in Theorem 3.11.

## 3.1 Finite-support orders and their cuts

Definition 3.1. For an infinite limit ordinal δ, set

)

$Γ_{δ} = Z^{(δ)},$H(δ)$= Q^{(Γ_{δ}}.$

Parentheses denote finite support. Both groups are ordered by their greatest differing coordinate. Write$e_{α}$for the integer basis vector at α < δ and$u_{g}$for the rational basis vector at$g ∈ Γ_{δ}.$The rank of a nonzero vector is its greatest support coordinate. Unless group operations are explicitly mentioned, H(δ) is used as a pure linear order; in particular Aut(H(δ)) means its order automorphism group.

A cut of an order L is a partition$(L^{−}, L^{+})$with$L^{−} < L^{+}.$It is an interior nonprincipal cut when both sides are nonempty,$L^{−}$has no greatest element, and$L^{+}$has no least element. Its two characters are$cf(L^{−})$and$ci(L^{+}).$It is balanced if these cardinals are equal. Cofinality and coinitiality here refer to the indicated linear orders.

Lemma 3.2. The order H(δ) is dense without endpoints and has cardinality |δ|. Its points have character cf(δ) on both sides. All nonempty bounded open intervals have one order type. All left rays have one order type, and all right rays have one order type. An increasing map between ordinal position sets induces an order embedding between the corresponding Γ and H orders by moving positions and padding by zero. Each point of H(δ) has a code using finitely many ordinal positions and integer and rational coefficients; comparisons are determined by these discrete coefficients and the order/equality pattern of the ordinal positions.

Proof. Finite-support counting gives$|Γ_{δ} | =$|H(δ)| = |δ|. The group$Γ_{δ}$has least positive element$e_{0},$so every g has predecessor$g − e_{0}.$Its cofinality and coinitiality are both cf(δ). Indeed, the vectors$e_{α}$for α in a cofinal subset of δ are cofinal, and their negatives are coinitial. The supports of fewer than cf(δ) vectors are bounded in δ, so such a family is neither cofinal nor coinitial.

The order H(δ) is a divisible nonzero ordered abelian group, and hence is dense and has no endpoints. If$(g_{i})$is coinitial in$Γ_{δ},$then$(u_{g_{i}})$is coinitial in the positive cone of H(δ): given a positive vector of rank g, choose$g_{i} <$g. Conversely, the ranks of fewer than cf(δ) positive vectors have a strict lower bound in$Γ_{δ},$and a positive basis vector at that lower rank lies below all of them. Thus the positive cone has coinitiality cf(δ). Translation and negation give that character at every point on both sides.

Translations move points and therefore identify rays of a fixed direction. We show that any positive vector can be sent to any other by an increasing automorphism. First translate the index group$Γ_{δ}$so that their greatest support coordinates agree, say at g. Write the two vectors as

$au_{g} +$v,$bu_{g} +$w, a,$b ∈ Q_{>0},$rk(v), rk(w) < g,

allowing zero lower parts. Fix all other basis vectors and replace$u_{g}$by

b w − v

$a u_{g} +$a.

This is an invertible triangular rational-linear map. It preserves the sign of every nonzero vector, since it either fixes the greatest nonzero coordinate or multiplies its coefficient by b/a > 0. It sends the first displayed vector to the second. Combining this map with translations sends any ordered pair of distinct points to any other such pair. Restricting gives the interval assertion.

Finally, an increasing map on ordinal positions preserves the greatest differing position of two integer vectors. The induced map on these integer vectors preserves the greatest differing position of rational vectors as well. This proves the embedding claim. Expanding the finitely many integer-vector positions used by a rational vector gives the asserted finite code and comparison rule.

Lemma 3.3 (Balance of cuts). Every interior nonprincipal cut of$Γ_{δ},$and every such cut of H(δ), is balanced.

Proof. First consider a cut (L, R) of$Γ_{δ}.$Among the ranks of r − l, with l ∈ L and r ∈ R, choose the least ordinal α. Fix one crossing pair of that rank and its common head above α. In that head, each fiber with a fixed integer coefficient at α lies wholly on one side: a crossing pair within a fiber would have smaller rank. The resulting cut in the integer coefficients separates two adjacent integers. A point with a head above the fixed head would exceed the fixed upper point, and a point with a head below it would precede the fixed lower point. The two bordering fibers are therefore cofinal and coinitial toward the original cut, and their tails are copies of$Z^{(α)}.$Their end characters agree by negation in that tail group. The case α = 0 would give a last lower and a first upper point, and is excluded. This proves balance in$Γ_{δ}.$

Now let (L, R) be an interior nonprincipal cut of H = H(δ), and put

T = {rk(r − l): l ∈ L, r ∈ R}$⊆ Γ_{δ}.$

This is a final segment: from a crossing pair of rank g, subtract a positive basis vector at any h > g from its lower point. The new pair still crosses and has rank h.

Suppose first that T has a least member g. Fix a crossing head above g. Every fiber with a fixed rational coefficient at g lies on just one side of the cut. Otherwise a crossing difference would have rank below g. The induced cut of Q is nonempty and proper. If neither coefficient side has a nearest rational, countable rational approximations are cofinal and coinitial in the original cut. If the lower coefficients have a greatest member, the entire fiber at that coefficient lies on the lower side and is cofinal there. Its tail, supported below g, has greatest available rank$g − e_{0},$and the vectors$nu_{g−e_{0}}$and$−nu_{g−e_{0}}$show that both its end characters are$ℵ_{0}.$On the upper side, rational coefficients decreasing to the greatest lower coefficient give coinitiality$ℵ_{0}.$If instead the upper coefficients have a least member, the reversed calculation gives cofinality and coinitiality$ℵ_{0}.$These cases exhaust the rational cuts, so the original cut is balanced.

Suppose that T has no least member, and let ϵ = ci(T). Put$S = Γ_{δ}$\ T and let$H_{S}$be the subgroup supported on S. We prove that the lower character is ϵ by separating two cases.

Assume there is l ∈ L for which

{rk(r − l): r ∈ R} is coinitial in T.

The coset$l + H_{S}$is contained in L, since a crossing within it would have rank in S. It is cofinal in L. In fact, if a point l' ∈ L lay above the entire coset, l' − l would have positive rank h ∈ T. Choose r ∈ R with rk(r − l) < h. Then r − l < l' − l, contradicting r > l'. The set S is nonempty, since otherwise the cofinal coset would be the singleton {l}. It has no greatest member: if s were greatest,$s + e_{0}$would be the least member of T. Balance in$Γ_{δ},$applied to (S, T), gives cf(S) = ϵ. The cofinality of$H_{S}$at its upper end equals cf(S). A cofinal set of ranks gives cofinal positive basis vectors, while fewer ranks are bounded and cannot give a cofinal family of vectors. Hence cf(L) = ϵ in this case.

In the other case, each l ∈ L has a bound$t_{l} ∈ T$strictly below all ranks rk(r − l), r ∈ R. Choose crossing pairs$(l_{i}, r_{i}), i <$ϵ, whose ranks are coinitial in T. For fixed l ∈ L, choose i with$rk(r_{i} − l_{i}) ≤ t_{l}.$If$l_{i} ≤$l, then$0 < r_{i} − l ≤ r_{i} − l_{i},$whence$rk(r_{i} −$l)$≤ rk(r_{i} − l_{i}) ≤ t_{l}, a$contradiction. Thus$(l_{i})_{i<ϵ}$is cofinal in L. If fewer than ϵ points of L were cofinal, their bounds$t_{l}$would have a common strict lower bound in T, since ϵ = ci(T). A crossing pair below that bound would have its lower point above all those points by the same calculation. This is impossible, proving cf(L) = ϵ.

Apply the proved lower-side calculation after negating the order and exchanging L and R. Negation preserves every difference rank, so it has the same T and ϵ. It yields ci(R) = ϵ. This proves balance also in the no-least-rank case.

## 3.2 The orbit record of a short sequence

For a subset A of a linear order L and a cut$A = A^{−}$⊔$A^{+},$including cuts with an empty side, define its strict slot by

$S_{L} (A^{−}, A^{+}) =${x ∈ L \ A:$A^{−} < x < A^{+} }.$

Its occupancy is the assertion that this set is nonempty. The order/equality diagram of a sequence identifies its distinct entries and the cuts of their induced order, so the occupancy data can be indexed without choosing an enumeration of the cuts.

Lemma 3.4 (Segments approaching a small cut). Let L be a dense linear order without endpoints, all of whose points have character κ on both sides. Suppose all bounded open intervals have one order type and every interior nonprincipal cut is balanced. For every infinite regular ϵ < κ, the following segment types depend only on ϵ and the indicated direction:

[p, c) = {x$∈ L_{c^{−}}: p ≤$x}, (c, p] = {x$∈ L_{c^{+}}: x ≤$p},

where c is an interior nonprincipal cut of balanced character ϵ and p belongs to the appropriate side. The isomorphisms can be chosen to match the displayed endpoint.

Proof. We prove both directions simultaneously by induction on the infinite regular cardinal ϵ. Consider two lower-side segments and choose strictly increasing sequences$(p_{i})_{i<ϵ}$and$(q_{i})_{i<ϵ}$cofinal in their respective cut sides, with the indicated endpoints at index zero. At a stage i < ϵ, fewer than ϵ preceding points are not cofinal, so one can choose the next point above them and above the next point of a fixed cofinal sequence. This gives the required strictly increasing sequences.

Partition the first segment into blocks as follows:

$B_{0} = {p_{0} }, B_{j+1} = (p_{j}, p_{j+1}].$

For a nonzero limit i < ϵ, set

$D_{i} =${x ∈ L: (∃j < i)$x ≤ p_{j} }, U_{i} = L$\$D_{i}, c_{i} = (D_{i}, U_{i}), B_{i} = (c_{i}, p_{i}].$

The cut$c_{i}$is interior and nonprincipal. Its lower side has no greatest point and has cofinality cf(i): the strictly increasing i-sequence is cofinal there, and any smaller proposed cofinal family would give a cofinal set of indices in i. Its upper side contains$p_{i}.$If that side had a least point u, the earlier sequence would give$cf(L_{<u}) =$cf(i) < κ, contradicting point character. Balance therefore gives$c_{i}$character cf(i) on both sides. Since i < ϵ, this is a regular cardinal strictly below ϵ.

Make the corresponding blocks from the$q_{i}.$Successor blocks are isomorphic by bounded-interval homogeneity, adjoining their greatest points. At a nonzero limit index i, use the upper-side induction assertion at cf(i) to match the blocks. Match the singleton blocks at zero. These are ordered partitions of the two segments. Indeed, for any point in the first segment take the least i such that it is at most$p_{i};$the three cases for i put it in exactly the block just specified. Gluing the block maps proves the lower-side assertion.

For the upper-side assertion choose strictly decreasing coinitial sequences. The blocks are${p_{0} }$and$[p_{j+1}, p_{j})$at successors. At a nonzero limit i, put

$V_{i} =${x ∈ L: (∃j < i)$p_{j} ≤$x},$W_{i} = L$\$V_{i}, d_{i} = (W_{i}, V_{i}).$

The set$V_{i}$has no least point and has coinitiality cf(i). The set$W_{i}$contains$p_{i};$if it had a greatest point, that point’s upper character would be cf(i) < κ. Thus$d_{i}$is nonprincipal, and balance gives character cf(i) on both sides. The block at i is$[p_{i}, d_{i}),$to which the lower-side induction assertion at cf(i) applies. The least index with$p_{i} ≤ x$verifies that these blocks, in reverse index order, partition the upper-side segment. For ϵ$= ℵ_{0}$there are no nonzero limit indices below ϵ, so this simultaneous induction starts with just the successor blocks. All displayed endpoint points are matched.

Theorem 3.5 (Short-sequence order orbits). Let δ be an infinite limit ordinal and let θ be an infinite cardinal with θ < cf(δ). Two sequences of length at most θ in H(δ) lie in the same Aut(H(δ))-orbit if and only if they have the same order/equality diagram and the same occupancies of all strict slots over their distinct entries.

Proof. Necessity follows from preservation of order. For sufficiency, the order/equality diagrams give an increasing bijection f: A −→ B between the sets of distinct entries, matching the indexed sequences. We extend it separately on each occupied slot.

Choose a point p in a slot over$A = A^{−}$⊔$A^{+}.$The portion of the slot at or below p has one of three forms. If$A^{−} = ∅,$it is (−∞, p]. If$A^{−}$has greatest member a, it is (a, p]. Otherwise put

D = {x: (∃a$∈ A^{−}) x ≤$a}, U = H(δ) \ D.

The cut (D, U) has no greatest lower point, has p on its upper side, and has lower character$cf(A^{−}) ≤$θ. Its upper side has no first point, since such a point would have character at most θ. By Lemma 3.3 this is an interior nonprincipal cut of balanced character$cf(A^{−}).$The slot portion is ((D, U), p].

In the first case its type is fixed by ray homogeneity; in the second case by bounded-interval homogeneity; in the third case by Lemma 3.4. The portion at or above p has the corresponding classification using$A^{+}, a$least member when present, and otherwise$ci(A^{+}).$The same descriptions show that the slot has neither endpoint.

The order map f preserves which boundary case occurs and the cofinality or coinitiality of the relevant part of A. Thus the corresponding occupied slot over B has matching two halves. Choose an interior point q there and match the two halves with their common point p sent to q. They glue to a slot isomorphism. The occupancy assumption ensures that empty slots also correspond. The entry sets and their occupied slots partition the whole order. Choice for this set of slots and gluing with f produce an increasing bijection of H(δ), as required.

## 3.3 Bounded names for model orbits

We now pass from automorphisms of the index order to automorphisms of its model. At the cofinalities covered by the orbit theorem, a support record determines a model orbit, but different records may determine the same orbit. Only a uniform upper bound on their number is needed for reversal.

Fix an infinite tuple length θ. A presentation of a θ-tuple in E(H(δ)) specifies its labels and their finite index lists. Flatten those lists into an indexed sequence of at most θ points of H(δ). Its presentation record consists of the labels, the order/equality diagram of this flattened sequence, and all its slot occupancies.

Lemma 3.6 (Uniform orbit bound). There is a fixed set$R_{θ}$of possible presentation records, depending only on ℓ and θ, with$|R_{θ} | ≤$B(ℓ, θ):=$2^{2^{ℓ+θ}}.$

For every categoricity cardinal κ ≥ max(ℓ,$θ^{+}),$the set of automorphism orbits of θ-tuples in its model has cardinality at most B(ℓ, θ). This applies also when κ is singular. If |δ| = κ and cf(δ) > θ, each realized record in E(H(δ)) determines exactly one such model orbit.

Proof. The finitely many positions belonging to each tuple entry can be indexed in θ × ω. Choices of arities and labels number at most$2^{ℓ+θ}.$The flattened order/equality diagrams number at most$2^{θ};$their sets of cuts have size at most$2^{θ},$and occupancy subsets number at most$2^{2^{θ}}.$The displayed generous bound therefore bounds a universal record set.

For a fixed δ with cf(δ) > θ, equal records give an order automorphism matching the flattened lists by Theorem 3.5. Applying E gives an automorphism of the model matching the tuples. Hence a realized record determines one model orbit. Every tuple has a labeled presentation, so the number of orbits is bounded by the number of records.

For any κ ≥ max(ℓ,$θ^{+}),$the ordinal$δ = κ + θ^{+},$with ordinal addition here, has cardinality κ and cofinality$θ^{+}.$The model E(H(δ)) has cardinality κ and is therefore a copy of the categoricity model. This proves the bound without any condition on cf(κ).

Choose a model$C_{κ}$at each categoricity size needed in a given set-sized construction. On its θ-tuple orbits put p −→ r when some strong self-map sends a representative of p to a representative of r. This relation is reflexive and transitive: compose maps after using an automorphism to align the intermediate representatives. Choose an injection of the orbit set into the fixed cardinal B = B(ℓ, θ), once for each κ. These are its orbit names. For any copy of$C_{κ}, a$tuple’s name is independent of the isomorphism used to$C_{κ},$because two such isomorphisms differ by an automorphism.

For a suitable δ of size κ, let$F_{κ,δ}$be the partial function from$R_{θ}$to B sending each realized record to its orbit name. The profile of this presentation consists of its named arrow relation and$F_{κ,δ}.$The profiles belong to a fixed set of cardinality at most$2^{B};$in particular this bound is independent of κ and δ.

## 3.4 Preserving every short record in a small subpresentation

Lemma 3.7 (Closure of ordinal supports). Let$θ^{+} ≤ a$be infinite cardinals and let β be an ordinal of cofinality greater than a. Every subset S ⊆ β of size at most a is contained in a set$T_{0} ⊆ β$of size at most a with the following property: for every$P ⊆ T_{0}$of size at most θ and every finite tuple from β, there is a tuple from$T_{0}$having the same order/equality diagram over P. Moreover$T_{0}$is bounded in β and has cofinality greater than θ in its induced order.

Proof. Construct increasing sets$S_{i} ⊆ β$for$i < θ^{+},$starting with S. At a successor stage consider all strict slots over the entire well-ordered set$S_{i}.$There are at most$|S_{i} | + 1 ≤ a$of them. In each finite slot add every point; in each infinite slot add a countably infinite subset. Together with$S_{i}$this realizes every finite order/equality pattern over$S_{i}$which occurs in β. At limits take unions. The cardinality stays at most a throughout.

S

$θ^{+}. SetForT_{0}a$given= i<θfinite+$S_{i}.$tuple,Every keepset Pany⊆$T_{0}coordinatesof$size at mostalreadyθ$isincontainedS_{i}$and matchin$someitsS_{i}other,$by regularitycoordinatesof

in their respective slots using the next stage. This proves the asserted property over P. Since$|T_{0} | ≤ a <$cf(β),$T_{0}$is bounded in β. Each$S_{i}$is bounded too, and its uppermost slot is infinite. The next stage therefore contains points above all of$S_{i}.$Every at-most-θ subset of$T_{0}$is bounded in this way, proving$cf(T_{0}) >$θ.

Lemma 3.8 (Appending a long indecomposable segment). Under the hypotheses of Lemma 3.7, suppose β is additively indecomposable. Let$T_{0}$be as there, and let δ < β be additively indecomposable, with$otp(T_{0}) < δ$and cf(δ) > θ. Place a consecutive segment J of order type δ strictly after$T_{0}$in β, and set$T = T_{0} ∪$J. Then otp(T) = δ, and T has the same finite-pattern matching property over its at-most-θ subsets. Consequently H(T) ⊆ H(β) computes correctly the occupancies of every strict slot over any sequence of at most θ of its points.

Proof. Choose α < β above$T_{0}.$Indecomposability of β gives α + δ < β, so J = [α, α + δ) is available. Indecomposability of δ gives$otp(T_{0}) + δ =$δ.

Fix a parameter subset P ⊆ T of size at most θ and a finite tuple in β. Match the coordinates below α into$T_{0}$over$P ∩ T_{0}$using Lemma 3.7. Keep coordinates in J fixed. The parameters in J, together with these finitely many retained coordinates, are bounded in J because cf(δ) > θ. Match all coordinates at or beyond the end of J by suitably many distinct points of J above that bound, retaining any repetitions. The three portions stay in their correct mutual order, and this gives the required finite tuple over P.

A sequenceHere$Γ_{T}$of=$Z^{(T)}at$mostis identifiedθ points withof H(Tits)imageuses atin$mostΓ_{β},$andθ ordinalH(T)$=positionsQ^{(Γ_{T}})$within itsits finiteimagecodes.in H(β).A

witness in H(β) to an occupied strict slot uses only finitely many additional ordinal positions. Match those into T over all the parameter positions and retain the integer and rational coefficients. Lemma 3.2 makes every comparison with the sequence unchanged. The resulting point of H(T) witnesses that slot. The reverse implication follows from inclusion.

Proposition 3.9 (Alignment of model orbits). Fix the record set and orbit naming at an infinite length θ. Let a < µ be categoricity cardinals with a ≥ max(ℓ,$θ^{+}).$Suppose the following data have one common profile:

1. a presentation E(H(β)) of$C_{µ},$where β is additively indecomposable, |β| = µ, and cf(β) > a;

2. presentations E(H(δ)) of$C_{a}$for a cofinal subset of$a^{+}$of additively indecomposable ordinals δ of size a and cofinality greater than θ.

Then in any copy N of$C_{µ},$every subset of size at most a is contained in$A ≤_{K} N$of size a such that the orbit name of every θ-tuple in A, computed as a tuple of$C_{a},$is the same as its name computed in N.

Proof. Identify N with the presentation in the first item. Represent the requested set by labeled elements and collect the ordinal positions in the finite codes of their indices. There are at most a positions. Apply Lemma 3.7 to obtain$T_{0}.$Its order type is below$a^{+}.$Choose a profile occurrence δ from the second item above$otp(T_{0}).$Since$a^{+} ≤$cf(β) ≤ β and$δ < a^{+},$Lemma 3.8 applies and gives T of order type δ.

The subpresentation A = E(H(T)) is strong in N and has cardinality a. It contains the requested set. For any θ-tuple in A, use a labeled presentation there. Its record is identical in E(H(T)) and E(H(β)) by the last assertion of Lemma 3.8. The order isomorphism δ ≃ T identifies its record in the former with the same record for E(H(δ)). The two record-to-name functions belong to the common profile and hence agree. This proves alignment simultaneously for all θ-tuples of A.

## 3.5 The elimination argument

Alignment compares every short tuple in a small submodel with its image in a larger model. We now use repeated profiles at two categoricity sizes to rule out an orbit arrow with no reverse. The larger size will absorb the cost of processing all tuples of the small model.

Lemma 3.10. If κ is an infinite cardinal and τ ≤ κ is infinite regular, the additively indecomposable ordinals$δ < κ^{+}$with |δ| = κ and cf(δ) = τ are cofinal in$κ^{+}.$

Proof. Given$η < κ^{+},$choose a limit ordinal ρ > η with$κ ≤ ρ < κ^{+}$and cf(ρ) = τ, for example by appending an ordinal segment of type τ beyond η + κ. Set$δ = ω^{ρ}.$It is additively indecomposable. A cofinal sequence of exponents gives a cofinal sequence in$ω^{ρ}$by continuity of exponentiation. Fewer than cf(ρ) ordinals below$ω^{ρ}$have all their Cantor-normal-form exponents bounded below ρ, and are therefore bounded in$ω^{ρ}.$This proves cf(δ) = cf(ρ) = τ. Every ordinal below$ω^{ρ}$has a finite Cantor normal form with exponents below ρ. Thus |δ|$≤ max(ℵ_{0},$|ρ|) = κ. Since δ ≥ ρ ≥ κ and ρ > η, we have |δ| = κ,$δ < κ^{+},$and δ > η.

Theorem 3.11 (Eventual reversal at categoricity cardinals). For each infinite cardinal θ there is a cardinal$b_{K}$(θ) such that, whenever$κ ≥ b_{K}$(θ) is a categoricity cardinal, M ∈ K has size κ, f: M −→ M is strong, and ā is a tuple of length at most θ in M, there is a strong g: M −→ M with g(f$(a_{i})) = a_{i}$for every coordinate i.

The bound concerns all sufficiently large categoricity cardinals, of arbitrary cofinality. No equality of the form$κ^{θ} = κ$is assumed.

Proof. It suffices to treat length exactly θ; pad a nonempty shorter tuple by repetitions, and use any strong self-map for the empty tuple. In a categoricity model, the asserted reversal is equivalent to symmetry of the arrow relation on its θ-tuple orbits. Indeed a reverse orbit arrow can be precomposed and postcomposed with automorphisms to match the particular image tuple and original tuple. The converse follows by applying reversal to a map witnessing an arrow.

Suppose that symmetry fails at unboundedly many categoricity cardinals. Let P be an infinite cardinal bounding the profile palette; for example take$P = 2^{B}.$Choose a strictly increasing list of failing categoricity cardinals$(κ_{i})_{i<P^{+}}.$At each step choose it large enough that there is an infinite regular$τ_{i} ≤ κ_{i}$exceeding ℓ, θ, and every preceding$κ_{j},$and that

$κ_{i} >$P,$κ_{i} >$κθj (j < i).

Such choices are possible by unbounded failure: first bound the set of preceding cardinals and their powers, then choose a regular successor cardinal above the first bounds and a failing cardinal beyond all of them. This is a set-sized recursion.

At size$κ_{i},$fix its orbit naming. By Lemma 3.10, the ordinals of size$κ_{i}$and cofinality$τ_{i}$used there are cofinal in$κ_{i^{+}}.$One profile occurs cofinally often among them: otherwise the supremum of at most$P < κ_{i^{+}}$bounded fibers would be below the regular cardinal$κ_{i^{+}}.$Since there are$P^{+}$sizes and at most P profiles, choose two sizes a < µ with the same cofinally recurring profile. They satisfy$θ^{+} ≤$a,$a^{θ} ≤$µ,$τ_{µ} >$a.

Their common named arrow relation has p −→ r but no r −→ p. Both names occur in both sizes. Proposition 3.9 applies inside every µ-sized model, using any of its cofinal profile occurrences.

We construct$θ^{+}$rounds of an increasing strong chain of µ-sized models. At the start of round$i < θ^{+},$choose an aligned a-sized submodel$A_{i}$containing all previous$A_{j}.$This is possible because their union has cardinality at most a. They are all strong in the current large model, and coherence will make$A_{j} ≤_{K} A_{i}$for j < i.

Enumerate all θ-tuples of$A_{i},$using$a^{θ}$steps. At the step for a tuple ū, if its current large-model orbit cannot reach p, leave it as it is. If it can reach p, compose such an arrow with p −→ r and realize the composite by a strong self-map of the current model. Regard this map as an inclusion into an isomorphic extension: rename its codomain so that the image of each old element becomes that old element. With the transported identification of the codomain, the tuple now has name r. At every later large stage its orbit remains unable to reach p. Otherwise transitivity from r would give r −→ p. An orbit already unable to reach p has the same persistence property.

Take strong unions at every limit step, including between rounds. The entire construction has at most$θ^{+} · a^{θ} ≤$µ many stages in cardinality. Every large union therefore has size µ and is a copy of$C_{µ}$by categoricity. Every transition between such copies gives an arrow of the common relation, so the persistence assertion also holds at limit stages.

The aligned submodels form a strong increasing chain: for j < i, their underlying sets are included and both are strong in the large model at the start of round i, so coherence applies. Its union

A = i<θ⋃+$A_{i}$

belongs to K, has cardinality a, and is a copy of$C_{a}.$Any θ-tuple of A is contained in some$A_{i},$since$cf(θ^{+}) >$θ. After round i it cannot reach p in a large model. At the next aligned small model its small orbit has the same name, and therefore cannot reach p in the common relation. The inclusion of that small model into A gives an arrow from this earlier small orbit to its orbit in A. If the latter could reach p, transitivity would contradict the former exclusion. Thus no tuple in A can have an orbit reaching p.

But$A ≃ C_{a},$so the orbit named p occurs in A; it reaches itself by the identity map. This contradiction proves that the failing categoricity cardinals are bounded. A cardinal above their bound is$b_{K}$(θ), and the first paragraph gives the claimed reversals, including all shorter lengths.
