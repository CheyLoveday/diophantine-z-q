# Results

- VERIFIED (repository): base `636c2761`, clean at start; `fowlerProp27` is a published-kind row rated GLUE/GLUE.
- VERIFIED (source): `NumberFieldOrder.discr_eq_index_sq_mul` and `finite_pic` already exist.
  Mathlib's `ClassGroup.equivPic` applies to all domains. The vendored multiplier-ring result supplies
  invertible ⇒ proper without a quadratic-degree hypothesis.
- VERIFIED (manuscript): L585–593 assign Δ to the full endomorphism order, bound its class number by
  `d ≤ D`, and apply Fowler at `n = D`. The human PDF reading on fork issue #14, comment 6973387139,
  records the negative-discriminant and residue conditions and confirms no exceptional-field exclusion.
- VERIFIED (dry run): on 29 H rows, strict and strictest counts both change from 4 LEAF / 25 GLUE
  to 5 LEAF / 24 GLUE. `autofold-output.txt` retains the relevant stdout lines. No fold was applied.
- VERIFIED (Lean): `FowlerBridgesDiscriminant.lean` compiled with `lake env lean`. The lattice identity holds
  for any finite ℤ-basis, and both printed discriminant conditions are lemmas.
- VERIFIED (Lean): the same discriminant file compiled with the local `toOrder` adapter. The remaining
  imports of the contribution do not require the wider class field application.
- VERIFIED (Lean): `FowlerBridgesIdeals.lean` compiled, including Picard finiteness and positivity,
  fractional-ideal lattice rank two, and properness iff invertibility.
- VERIFIED (Lean): `FowlerBridges.lean` compiled. `card_pic_eq_properClassNumber` identifies the finite
  count, and `fowlerProp27_of_print` proves the live row from the one printed proposition.
