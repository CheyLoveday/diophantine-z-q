# CCL unit index

**Stopped under the no-new-hypothesis rule.** The tree drops the unit factor
from Cai–Chen–Liu, Trans. Amer. Math. Soc. 370 (2018), Thm 2.15, p. 3730
(read: AI reading of the journal page). The manuscript already excludes
the exceptional fields at tex 2839–2840 and uses this at tex 2921–2922.
The proposed mod-8 argument has an arithmetic error: −4 is a square
modulo 8. The level condition `4 ∣ N` is sufficient using modulo 16.

The generic transport and anchor lemmas still promise unweighted norms
for arbitrary admissible conductors, including one. A Heegner form at
generic level does not give the exclusion. The staged chain has a prime
dividing every old conductor, and its actual constructor also has the
companion exclusions needed for `c = d, m = 1`. The older chain does not
supply either discharge through its present interface. Using `m = d`
instead needs a separate check of the print's conductor restrictions.

The two Mathlib imports built separately and
`scratch/ccl-unit-index/Check.lean` compiled. Its six declarations use
only standard axioms. The leaf and every production consumer were left
unchanged. The [report](../docs/research/ccl-unit-index.md) records the
six dictionary steps and the [inventory](../scratch/ccl-unit-index/consumers.md)
locates the callers. The remaining work is to carry the factor through
generic transport and resolve the older unrestricted guarantee before
changing the leaf.
