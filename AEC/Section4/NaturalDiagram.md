# Natural diagram

From [Definition 4.4](Definition_4.4.md).

Definition 4.4 (Natural and placed diagrams). Consider a set-sized list of terms in an order presentation. Each term consists of a label and an increasing finite list of positions. Extend the order to size at least the threshold for the list and compute its diagram there. The result is its natural diagram. If $A = E(I)$, a placement of an additional tuple $d$ over $A$ is a labeled representation in an order extension of $I$, retaining the positions and chosen representations of the parameters in $A$. Its placed comparison over $A$ is the natural diagram of $(d, a_A)$, where $a_A$ is a fixed enumeration of $A$.

The natural diagram is independent of the extension used. Indeed, linear orders amalgamate over a common suborder: for each cut of the suborder, place the remaining portions of the two orders in that cut while preserving each portion’s order. Extending the amalgam further if necessary gives a common sufficiently large presentation. Strong order maps and Proposition 4.2 identify the two diagrams. The same argument shows that only the labels and the joint order/equality pattern of their supports matter. All diagrams with parameters use matching parameter enumerations. One may instead list all labels on the base order, allowing repetitions: restriction gives an enumeration of the elements, and reinserting the repetitions is forced by their equalities.

A placed comparison over a whole $\mu$-model is evaluated in a sufficiently large presentation. It is not, by this definition, an assertion that the original $\mu$-model itself lies above the threshold for diagrams of length $\mu$.

**[NaturalDiagram.lean](NaturalDiagram.lean)**

@import "NaturalDiagram.lean"
