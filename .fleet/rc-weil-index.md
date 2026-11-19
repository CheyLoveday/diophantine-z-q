# rc-weil-index

Implementation and report SHA: 0ed522a45b3e7660ff1b3003ab8b93fa0a3b7979.
This file is the following handoff commit; its SHA can be read with
git log -1 --format=%H -- .fleet/rc-weil-index.md.

The actual finite indices, gaussGamma, are constructed by normalized
Gauss sums and proved to give the shifted oscillatory Haar integrals
for the manuscript's negative finite phase. The dyadic eighth roots
are evaluated explicitly; the real Gaussian limit gives the inherited
gammaReal. The actual finite factors have finite support on every
rational diagonal list.

Quadratic reciprocity with its two supplements proves the full
WeilIndexProductFormula for the explicit eighth-root family finiteGamma,
including both rectangular lists. Passing product one to gaussGamma
has one remaining finite arithmetic input: the signed value of the
normalized odd Gauss sum at unit 1. The square and unit twist compile.
No metaplectic lifts or actions were changed.

The actual odd and dyadic determinant quotients give the manuscript's
Legendre and mod-four factors. With the conductor bounds at the given
old level, the old character descends and equals the product of the
root characters times Jacobi(m,d) on positive representatives. The
identification with the fixed-pool character is reduced to one exact
canonical residue test in the report; it remains an ELLIOT input.

All ten WeilIndex Lean files pass sequential lake env lean. All 125
theorem audits use only propext, Classical.choice and Quot.sound.
No new print, axiom, or manuscript error was identified in scope.
See docs/research/rc-weil-index.md for the exact remaining hypotheses.
