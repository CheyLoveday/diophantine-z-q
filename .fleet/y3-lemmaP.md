# Relative Lemma P for full level three

**Scoped stop.** `Y3LemmaP.QMAbSchemePPol` states the polarized problem over
the original abelian schemes, using a normalized biadditive line bundle class
on the twofold fibre product in place of an unavailable relative dual abelian
scheme. The class fixes the manuscript's Rosati involution and tests principal
polarization on geometric fibres, including tests on nonreduced schemes to
detect infinitesimal kernels.

**VERIFIED:** `ZInQKernel/Contrib/OneProof/Y3LemmaP.lean` and
`scratch/y3-lemmaP/Audit.lean` compile. All eleven theorem axiom checks give
only `propext`, `Classical.choice` and `Quot.sound`.
`y3FullThreeRepZ30Pol_iff` proves the representability comparison conditional
on `RelativeLemmaP`. That named Prop asks for existence on every test object
and preservation by the exact cartesian identifications used by the universal
property; the identity square gives uniqueness. Construction in families,
including the positive characteristic fibres, and rigidity over nonreduced
bases remain open.

**Source issue:** L467 and L474–475 use the canonical principal polarization
without supplying the relative comparison. Whether Buzzard already supplies
it at the auxiliary level is **UNVERIFIED**. At L421–422, the numbers 4, 6 and 2
are normalizer orbifold orders; the coarse level-one quotient has index two at
each of the three branch values. The text should say which indices it means.

The ELLIOT row retains ON THE SPOT. No leaf was added and nothing was folded.
Full report: `docs/research/y3-lemmaP.md`.
