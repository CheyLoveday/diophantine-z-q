# Derived Kummer comparison: fifth edition (Resolution.lean)

`Resolution.lean` imports the unchanged fourth-edition module `Actual.lean` and adds the fifth edition.

Final declaration: `ComparisonEvaluation.contraction_of_print`. For a number field `K`, a finite place
`w`, `F = w.adicCompletion K` and an elliptic curve `B` over `F`, it constructs a contraction of the cone
of the actual based comparison map of the completed point module, built on the genuine based resolution
`FiniteLocalDegreeBound.basedResolution_of_print`. Along the way: the genuine completed-point source
resolution, the two residue comparison squares `commE` and `commO`, and the integral Nakayama contraction.
No `hred` hypothesis, assumed comparison bijectivity or assumed reduced-realization quasi-isomorphism is
used.

Printed inputs (Prop parameters, not axioms):

1. `MilneLocalDualityPrint` (existing; Milne, Arithmetic Duality Theorems, I, Corollary 3.4);
2. `MilneFiniteLocalDualityPrint` (existing; Milne ADT I, Corollary 2.3, finiteness and the degree-one
   and degree-two perfect comparisons);
3. `FiniteLocalDegreeBound.MilneFiniteDegreeBoundPrint` (new in this edition): the finite higher-degree
   part of the same local statement for the two finite coefficient families used here (the elliptic
   Tate levels and the cyclotomic units).

All 166 public theorems of the file depend only on `propext`, `Classical.choice` and `Quot.sound`.
