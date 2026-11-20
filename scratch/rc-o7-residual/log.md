# Results log

- Merged the local torus branch into the requested assembly base.
- Selector: all admissible rows in tex 8209–8217, 8298–8306, 9265–9279, 9439–9443. Fixed selector needs all-admissible isSome; existing interface only guarantees simple-zero coverage.
- IdealNorm.lean: passed `lake env lean`. Equal ideal exponents above p imply equal p-exponents in absolute norm; any integral local block has the same valuations as a single nonzero global integer.
- ReducedNorm.lean: passed `lake env lean`. Reduced norm restricts to field norm by the two conjugations and the determinant of multiplication. The completed block theorem uses the chart's integral unit kernel. The normalized formula includes partner primes by the block-one choice and coprimality.
- OrbitQuotient.lean: passed `lake env lean`. The two equivalences evaluate on the chosen double-coset representative; equality of double classes removes the internal choice.
- Orbit.lean: passed `lake env lean`. If `toClassGroup (a c) = c`, the orbit at `(b,c)` is represented by `e(a c) z_b`.
- Artin.lean: passed `lake env lean`. The direct dependent comparison timed out; the character and inverse Artin projections compile separately, then the integer sign equality on `J'.pic c` proves `artinMatchAt`.
