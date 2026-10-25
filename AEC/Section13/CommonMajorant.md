# Common majorant

From [13.3 The common majorant and its limit refinements](13.3.md).

Choose a cardinal $\vartheta$ above the hereditary sizes of the normalized descriptor set and all fixed parameters. This is one cutoff, chosen before any finite-depth induction; it includes all candidate templates, not just those already selected. For $\alpha \in \mathrm{Ord}$, take the supremum of the values of all the functions in the expanded finite register, for every descriptor and for all ordinal inputs at most $\alpha$. Finite lists of size inputs are included by taking all their coordinates at most $\alpha$. Each such collection is a set, and each request has been totalized, so Replacement bounds its values. We may therefore choose a fixed, monotone definable ordinal function $\Phi$ such that

$$\Phi(\alpha) > \vartheta, \quad \Phi(\alpha) > \alpha, \quad B_q(d, \vec{\beta}) < \Phi(\alpha) \quad (\max \vec{\beta} \le \alpha).$$

**[CommonMajorant.lean](CommonMajorant.lean)**

@import "CommonMajorant.lean"
