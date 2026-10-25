# Test cardinal

From [6.1 Testing, placement, and amalgamation](6.1.md).

For later reference, fix a convenient explicit threshold for the whole object layout. Increase $g$ so that $g(\sigma) \ge b + \sigma$, and put

$$c(\sigma, \tau) = 2^{g(\sigma)+b+\sigma+\tau}, \qquad c(\sigma) = c(\sigma, \aleph_0).$$

These cardinals exceed the displayed arities and satisfy $c(\sigma, \tau)^\sigma = c(\sigma, \tau)$. We close levels under these functions and their successors, as well as under the diagram and rich order bounds at the resulting arities. For a different fixed natural layout, use its testing function in the same formula.

**[TestCardinal.lean](TestCardinal.lean)**

@import "TestCardinal.lean"
