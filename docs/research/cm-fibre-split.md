# cm-fibre-split: `CMBranch.CMFibreSplit` (diophantine_zq.tex L581-586)

Task cm-fibre-split (2026-11-17). Base: `origin/wip/cox-lattice` 6298e108 with `origin/main` 67950e829 merged
(merge commit 096c052c7). Results log: `scratch/cm-fibre-split/log.md`. Marks: VERIFIED (compiled, or read in the
tree / the manuscript), STANDARD (published, exact reference), UNVERIFIED (numbers from memory; no network), SPECULATIVE.

## 1. Result

DRAFT — filled in at the end of the task.

## 2. What `CMFibreSplit` packs, and the manuscript's own argument

`CMFibreSplit` (ZInQKernel/Contrib/OneProof/CMBranch.lean) says: at a fibre with a CM point (`¬ NoCMAt u`), there
are a number field `L` with `[L:ℚ] ≤ D`, a model `A/L` of the fibre surface (`FibreOver`), an elliptic curve `E/L`
whose geometric endomorphism ring is an order `R` of an imaginary quadratic field `k`, the product `E² = E × E`, and
an `L`-isogeny `E² → A`. The manuscript's text (thm:height, proof, L581-586):

* L582: "Suppose End⁰(A_Q̄) = M₂(k)." This is the second case of the dichotomy of L563-577.
* L583: "All its elements are defined over L." Here `L = EK` is A8's field (L544-561): `E` is the kernel field of
  `G_ℚ` acting on the geometric endomorphism lattice of `W₀ = Res_{K/ℚ} A`, and L560-561 already state that `L`
  "defines every geometric endomorphism".
* L583-585: "Multiples of matrix units therefore give an elliptic curve E/L with complex multiplication and an
  L-isogeny E² → A."

The manuscript uses no Weil restriction in L581-586 itself. The Weil restriction `W₀` appears only in A8 (L546),
which defines the field `L`; cm-branch2 §2.3 calls this route "Weil restriction" for that reason. The argument
followed here is the manuscript's: A8's Hom field, then matrix units.
