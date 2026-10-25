# 2 Set codes and models indexed by orders


We first separate the uniformity over AECs from the transfer argument for one AEC. All directed families below are nonempty and set-indexed. We begin by deriving the directed forms of the chain axioms in Definition 1.1.

Lemma 2.1 (Directed unions and coherent direct limits). If a nonempty set of models is directed under strong inclusion, its union belongs to K and every member is strong in the union. If every member is strong in a common model N, its union is strong in N. More generally, a coherent diagram of strong maps indexed by a nonempty directed partial order has a direct limit in K, with strong canonical maps. Every compatible family of strong maps from the diagram into a model induces a strong map from the direct limit.

Proof. The union is a well-defined τ-structure: finitely many arguments are contained in one family member, and any two choices of such a member agree after passing to a common strong upper member. Here finitarity is used for functions and relations alike. We prove the union and common-upper-bound assertions together by induction on the cardinality of the family. A finite directed family has a member containing every other member, so its union is that member. A countable directed family has a cofinal increasing sequence: enumerate the family and successively choose a member above the previous choice and the next enumerated member. The chain axioms apply to this sequence, including their common-upper-bound clause.

Suppose the family is indexed by a set I of uncountable cardinality κ, and the two assertions hold for smaller families. Choose an operation assigning to each pair of indices an index of a strong upper bound. Express I as the union of an increasing continuous sequence$(I_{α})_{α<cf(κ)}$of nonempty subsets of size less than κ, each closed under that operation. To obtain this sequence, enumerate I by κ, use a cofinal sequence of ordinals below κ to specify the required initial segments, close each stage under the binary operation by countably many iterations, and take unions at limit stages. A union of fewer than cf(κ) sets of size less than κ still has size less than κ; countable closure preserves the size of each infinite stage. This construction also works when κ is a successor cardinal, using κ many stages.

Let$U_{α}$be the union of the family on$I_{α}.$The induction hypothesis gives$U_{α} ∈$K. For α < β, every member indexed by$I_{α}$is strong in$U_{β}.$The inductive common-upper-bound assertion therefore gives$U_{α} ≤_{K} U_{β}.$The chain axioms now give the required union over I. If the original

Unbounded categoricity

Orderand orbitpresentationsreversal

Single-model diagrams

Uniformcompacttestingplacementand

Working schemes

ExtensionsFreerelativecontrolledextensionisolationandby a mark

Minimal type

Fixed pointed models

Finite marked systems

Exactatboundaryfixed depthlifting AllCommonfinite markedmarkeddepthslevel

No proper extension

withmodelBasisunchangedsizesizeonequalsapointstail

Common geometric level

Exact liftingGeometricand relativefor eachsystemsbasesfinite shape growthAllAbovefinitethresholdtheshapesno-

Induction through

Categoricitylarger cardinalitieson a tail

Figure 1: The qualitative proof, ordered by its principal dependencies. The two dashed boxes are separate applications of Section 13. The first makes all finite marked depths available for the no-growth argument over the fixed point. The second is chosen after that argument and supplies the starting cardinal for the final transfer. These classes of common levels need not contain a tail. The small-code reduction then gives the uniform threshold of Theorem 1.2.

family is strong in N, induction first gives$U_{α} ≤_{K} N$for every α, and the chain common-upperbound clause gives the same conclusion for their union. This completes the induction.

For a diagram$(M_{i}, f_{ij})$indexed by a directed partial order, form the quotient of the disjoint union of its underlying sets by

(i, x) ∼ (j, y) ⇐⇒ (∃k ≥ i, j)$f_{ik}$(x)$= f_{jk}$(y).

Directedness and coherence make this an equivalence relation. The canonical map from each$M_{i}$is injective. Interpret any finitary function or relation in a common later model containing representatives of its arguments; coherence and the fact that the maps are structure embeddings make this interpretation well-defined. The images of the$M_{i}$are models forming a directed family of strong inclusions. The first assertion puts their union, which is the quotient just constructed, in K and makes all canonical maps strong.

Finally, compatible strong maps$g_{i}: M_{i} −→ N$induce a map on that quotient. It is injective: if two images agree, compare their representatives in a common later$M_{k}$and use injectivity of$g_{k}.$The same argument gives a structure embedding. Its image is the directed union of the strong submodels$g_{i} [M_{i}]$of N, so the common-upper-bound assertion makes the induced map strong. The quotient construction also gives uniqueness, and hence the stated direct-limit property.

Lemma 2.2 (Recovery from small models and pairs). Fix an infinite cardinal λ and a finitary language τ of cardinality at most λ. An AEC in τ with LS(K) ≤ λ is determined by its models of cardinality at most λ and its strong inclusions between such models, both taken up to isomorphism. These data have a set code, and the recovered class and strong-submodel relation are uniformly first-order definable in set theory from that code.

Proof. Represent small structures on ordinals of cardinality at most λ. Represent a small pair M ⊆ N by such a representative for N together with the distinguished subset that is the domain of M. The possible structures and pairs form sets. A code specifies which structure types and which pair types are allowed. Testing whether a given small structure or pair has an allowed type is a set-theoretic condition: quantify over the relevant isomorphisms.

For an actual M ∈ K, let

D(M) = {A$≤_{K}$M: ∥A∥ ≤ λ}.

This is a set. It is nonempty by the LS axiom applied to the empty set, and its union is M by the LS axiom applied to singletons. If A, B ∈ D(M), the LS axiom inside M supplies a small strong submodel containing |A| ∪ |B|. Coherence makes both A and B strong in that submodel. Thus D(M) is directed.

Conversely, suppose a structure M is the union of a nonempty directed family of small structures whose membership and pair inclusions are allowed by the code of K. These are actual members and strong inclusions of K, so the directed-union axiom gives M ∈ K. Consequently the following condition recovers membership, including for structures not already assumed to belong to K:

M is a union of a nonempty directed family of allowed small models, with all its directed inclusions allowed by the small-pair code.

S

nonemptyTo recoverdirectedthe strongsubfamilyrelation,E ⊆ Drequirewith Ma =directedS E. IfpresentationM$≤_{K}$N, useND== D(ND of) thisand kindE = D(Mand);a

transitivity makes the second a subfamily of the first. In the reverse direction, every member of

E is strong in N by the union clause for D. The common-upper-bound clause for E then gives$M ≤_{K}$N.

Each presentation can be quantified over as a set of substructures of the structure being decoded. All the preceding conditions are thus first-order set-theoretic formulas with the small code as parameter. They recover both the class and the order, as asserted.

The equivalence below is the usual Hanf-number reduction; compare [Vas17a, Remark 1.3]. We spell out the set coding to make the uniform quantifier explicit.

Proposition 2.3 (The uniform reduction). The uniform assertion in Theorem 1.2 is equivalent to the following qualitative assertion:

Every AEC categorical in unboundedly many cardinals is categorical in all cardinals above some bound depending on that AEC.

Proof. At a fixed LS bound λ, the languages can be renamed into a fixed set of symbols with specified finite arities. By Lemma 2.2, the possible AECs in those languages are determined by members of a set of small codes. A code is valid exactly when its decoded class and relation satisfy the AEC axioms with LS bound λ. This is a first-order condition on the code, so the valid codes form a set.

Assume the qualitative assertion. For each valid code c, its categoricity spectrum is either bounded or unbounded. In the bounded case choose the least infinite cardinal$b_{c}$strictly above every categoricity cardinal. In the unbounded case choose the least infinite cardinal$b_{c}$such that the decoded AEC is categorical in every cardinal at least$b_{c}.$These choices are definable, and the second choice exists by the qualitative assertion. Replacement bounds the set of all$b_{c}.$Choose a cardinal µ(λ) ≥ λ strictly above that set of bounds. If an AEC with LS number at most λ is categorical at some κ ≥ µ(λ), its code cannot be in the bounded-spectrum case. It is therefore categorical at every$κ' ≥ b_{c},$in particular at every κ' ≥ µ(λ). This is exactly the same threshold in the premise and conclusion.

Conversely, for an AEC categorical unboundedly often, apply the uniform assertion with λ = LS(K). Some categoricity cardinal crosses the resulting threshold, and the asserted tail follows.

Remark 2.4. Lemma 2.2 also supplies the usual ZFC interpretation of quantification over AECs: one quantifies over their set codes and uses the decoded class predicates. No choice of representatives from a proper class and no class choice axiom is needed. Below we fix one AEC categorical unboundedly often and write ℓ = LS(K). It has arbitrarily large models because categoricity includes existence.

## 2.1 A finite-arity partition argument

The following end-homogeneous argument belongs to classical partition calculus; compare Erdős and Rado [ER56, Theorem 39 and its corollary]. We prove the finite-arity form and bounds used by the order-template construction.

Lemma 2.5. For infinite cardinals ξ, ν and a positive integer k, there is an infinite cardinal$R_{k}$(ξ, ν) such that every coloring of the k-element subsets of an ordinal of cardinality at least$R_{k}$(ξ, ν) into ξ colors has a homogeneous subset of cardinality ν. Finitely many specified arities can be made homogeneous simultaneously by enlarging the initial cardinal.

Proof. For k = 1, a set of cardinality greater than ξ · ν cannot be partitioned into ξ sets all of cardinality less than ν. Suppose the assertion is known for k. Choose an infinite initial ordinal α large enough for that k-ary assertion with target ν, and put$b = ξ^{|α|}.$Consider a coloring c of the (k + 1)-element subsets of an ordinal Ω with |Ω| > b.

Construct a tree of residual subsets of Ω through height α. Its root is Ω. At a nonempty node, name and remove its least point x. The previously named points on its branch, together with x, form an increasing sequence. Partition the remaining residual set according to all values

u 7−→ c(s ∪ {u}), s a k-subset of that sequence.

The nonempty parts are the children. At a limit height, a branch has as its residual set the intersection of the earlier residual sets; retain the node precisely when this intersection is nonempty.

At each node there are at most |α| coordinates to record and hence at most b children. The total number of possible nodes through height α is at most$b^{|α|} =$b. This includes the limit nodes, which are specified by their branches. At most b points are removed as node labels. Choose u ∈ Ω which is never removed. At every height it belongs to one residual set; at limit heights it belongs to the intersection on that branch. Consequently it determines a branch with α named points and nonempty remainder.

For every k-subset s of these named points, all later named points give the same value of c(s ∪ {x}): that value was fixed by the partition immediately after the last point of s was named. Therefore c on increasing (k +1)-tuples from the branch depends only on their first k entries. Apply the k-ary induction hypothesis to this induced coloring on the branch. Its homogeneous ν-subset is (ξ,ν)

homogeneous for c as well. For example, the recursion just proved allows$R_{k+1}$(ξ, ν)$= (ξ^{R_{k}})^{+}$

after increasing the initial$R_{1}$as needed.

For a finite list of arities, work backward to choose a bound large enough for the last desired thinning after all the earlier ones. Successive thinning preserves homogeneity already obtained. This proves the final assertion.

## 2.2 A fixed presentation on every order

The construction is an Ehrenfeucht–Mostowski presentation [EM56]; for its AEC form compare [She09, Definition IV.0.8 and Claims IV.0.9, IV.0.12]. We include the finite-support construction in the label notation used below.

Theorem 2.6 (Order presentation). Suppose K has arbitrarily large models and LS(K) = ℓ. There are at most ℓ labels, each of positive finite arity, and a functor E from nonempty linear orders and order embeddings to K and strong maps, with the following properties.

1. Every element of E(I) is a label evaluated on an increasing finite list from I. Equality and all structure relations and function values are determined by the labels and the order/equality pattern of the finitely many indices involved.

2. E(I) contains distinct distinguished elements$(a_{i})_{i∈I}.$An order embedding f: I −→ J sends$a_{i}$to$a_{f(i)},$and its action on any labeled element is position substitution.

3. For every finite nonempty s ⊆ I, the elements labeled on s form a strong submodel$E_{s}$(I) of S

cardinality at most ℓ. For s ⊆ t these submodels are strongly included, and E(I)$= s E_{s}$(I).

4. |I| ≤ ∥E(I)∥ ≤ |I| + ℓ. In particular, for every infinite κ ≥ ℓ, K has a model of cardinality exactly κ.

Here a subpresentation is identified with its image under the canonical strong map when an inclusion of underlying universes is convenient.

Proof. Take an arbitrarily large M ∈ K and distinct elements$(a_{i})_{i∈A}$indexed by a large ordinal A. Recursively on the positive finite size of s ⊆ A, choose$M_{s} ≤_{K} M$of cardinality at most ℓ containing the displayed elements on s and every$M_{t}$for nonempty t ⊊ s. There are only finitely many such t, so the LS axiom applies with bound ℓ. Coherence gives$M_{t} ≤_{K} M_{s}.$

Choose a surjective enumeration$(m_{s,η})_{η<ℓ}$of each$M_{s},$allowing repetitions. If$s = {i_{0} < · · · < i_{n−1} },$require$m_{s,j} = a_{i_{j}}$for j < n. For an n-element set s, its color is the complete atomic diagram, including negations and equalities, of all the enumerations

$(m_{t,η})_{η<ℓ}, ∅$̸= t ⊆ s,

with the subsets of s named by their relative positions. This diagram includes formulas involving entries from different enumerations. There are at most ℓ names and atomic formulas for each fixed n, so its possible colors belong to a fixed set of cardinality at most$2^{ℓ}.$

We choose colors$d_{n},$for n ≥ 1, so that for every finite n there are samples of arbitrarily large cardinality homogeneous in colors$d_{1},..., d_{n}.$Suppose$d_{1},..., d_{n−1}$have been chosen with this property. For any prescribed target cardinal, choose such a sample large enough for Lemma 2.5 at arity n and thin it to an n-homogeneous set of the target cardinality. The earlier colors are retained. If every possible n-color supported only boundedly large such thinnings, the supremum of the bounds over the set of colors would bound all thinnings, a contradiction. Thus one color$d_{n}$supports arbitrarily large thinnings. It restricts on every smaller subset to the previously chosen colors. This proves the recursion and its coherence. It asserts finite-stage realizability in arbitrarily large samples; it does not require an infinite simultaneous homogeneous set inside one sample.

For a nonempty linear order I, introduce symbols (s, η) for each finite nonempty s ⊆ I and η < ℓ, with s listed increasingly. Equate (s, η) and (t, ζ) when the color$d_{|s∪t|}$says that the corresponding entries are equal. Coherence makes this independent of passage to a larger finite set of indices. Reflexivity, symmetry, and transitivity hold because any finite instance occurs in a realized color. Form the quotient by this equivalence relation.

Interpret a relation on finitely many quotient elements in a color on the union of their supports. For a function symbol, evaluate it in the enumerated model on that union and use a name for its value. All its arguments belong to that enumerated model, and the model is a substructure, so the value has such a name. Changing representatives or enlarging the finite support gives the same quotient element by the complete atomic diagram and coherence. A constant can be evaluated using any one nonempty finite support. Two such evaluations agree in a color on their union. Thus these rules define a τ-structure E(I).

Let$E_{s}$(I) consist of the elements named by (s, η), η < ℓ. The color$d_{|s|}$makes this a full enumerated copy of one of the actual models$M_{s}$in a sample. Names with support t ⊆ s are included in this copy: their equalities with names in the enumeration on s were recorded. If s ⊆ u, the pair$E_{s}$(I)$⊆ E_{u}$(I) is isomorphic to an actual pair$M_{s} ≤_{K} M_{u}$from a realization of$d_{|u|}.$Isomorphism invariance therefore makes the inclusion strong. The family of these small models is directed and covers the constructed structure. Its directed union belongs to K, with all$E_{s}$(I)$≤_{K}$E(I).

For an order embedding f: I −→ J, substitution (s, η) 7→ (f [s], η) respects every defining diagram and every inequality of names. It therefore induces an embedding E(f): E(I) −→ E(J). On each finite-support model it is an isomorphism onto$E_{f[s]}$(J)$≤_{K}$E(J). The common-upperbound clause applied to their directed union shows that the whole image is strong in E(J). Substitution also proves E(id) = id and E(g ◦ f) = E(g) ◦ E(f).

Define$a_{i}$by the first designated name on the singleton {i}. The recorded equalities identify this with the designated name for i on any larger finite support. Distinct indices give distinct elements because every relevant sample had that property. The labels are indexed by (n, η) with n ≥ 1 finite and η < ℓ, so there are at most ℓ of them. Counting finite supports proves the upper bound on size, and the distinct displayed elements prove the lower bound.
