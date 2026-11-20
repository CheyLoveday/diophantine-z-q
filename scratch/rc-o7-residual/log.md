# Results log

- Merged the local torus branch into the requested assembly base.
- Selector: all admissible rows in tex 8209–8217, 8298–8306, 9265–9279, 9439–9443. Fixed selector needs all-admissible isSome; existing interface only guarantees simple-zero coverage.
- IdealNorm.lean: passed `lake env lean`. Equal ideal exponents above p imply equal p-exponents in absolute norm; any integral local block has the same valuations as a single nonzero global integer.
- Orbit quotient: evaluation of the idele-to-double-class equivalence on a representative checked. Dependent based-fibre reduction still being checked.
- ReducedNorm.lean: passed `lake env lean`. Reduced norm restricts to field norm by the two conjugations and the determinant of multiplication. The completed block theorem uses the chart's integral unit kernel. The normalized formula includes partner primes by the block-one choice and coprimality.
- OrbitQuotient.lean: passed `lake env lean`. The two equivalences evaluate on the chosen double-coset representative; equality of double classes removes the internal choice.
