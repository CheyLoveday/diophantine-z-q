# Singleton packet sizing and verification

- VERIFIED (base report and code): the fourth seed handoff row in
  `docs/research/rc-ksplit-seed.md` is the consumer. `KSplitSeed/Seed.lean`
  consumes an exact five-part local packet and a fresh-prime match;
  `KSplitSeed/Fresh.lean` produces the latter from the specified scalar descent
  modulo integer two and the good Hecke coefficient. No change to the seed.
- VERIFIED (operator, tex 9754–9760, 9866–9889, 10326–10331):
  `O12Local.Stage` and `combine` give support, the actual candidate operator
  and ramified diagonal lines, including the Eisenstein sector if realized.
  `O12.o12_charZero` supplies the conjugation pattern. It uses zero inertia
  differences on the old space; it gives no polynomial there.
  `CuspidalData.oldUp` is an arbitrary linear map; the generic Eisenstein
  sector also carries no old matrix. `GoodRec` and
  `O12Formwise.AtLevel.good_values` supply the two scalar ingredients after
  the lower-level source and Galois representation are identified. The missing
  comparison is the actual p-old multiplicity action (two degeneracy copies
  per away-from-p copy), including factor separation. Name `OldBlockCubic`
  and prove it from a spanning family of old pairs and their Fourier action.
- VERIFIED (shift, tex 9844–9854, 10330): `WhittakerComparison` has all-index
  Fourier normalization but action and integral translation only at one.
  `Sector.UpAtOne` also only reads one. The explicit ramified Eisenstein
  operator has `eisensteinUp_shift` at all positive indices; the abstract
  Stage does not bind its Eisenstein operator to it. Name `UpShift` for
  the additional shifts at p and p²; use the existing shift at one.
- VERIFIED (determinants, tex 10355–10379): the model stores the genuine
  coordinatewise operators but no blockwise character or topology on its
  coefficient field. `weightTwist_frob` gives the cyclotomic value at odd p;
  the ratio is the character of the square root of positive p (not in
  general the character of the square root of p-star).
  `dense_arithmeticFrobenius` can transport a continuous determinant
  comparison given at all good arithmetic Frobenius elements. Need actual
  block supports, the character comparison on those supports, and the integral
  character value in the selected subring.
- VERIFIED (assembly interface): `thetaMul_linear` and `Hp` use the same
  three summands and scalar coefficients as the seed. Need a singleton packet
  extending a given Stage with the preceding comparisons and block realization;
  no new literature input. Use an explicit reading of index zero as well
  as `FourierData.index` on positive indices, since `DphiBlocks` quantifies
  over every natural number. The realization lane, integrality, old-unit
  comparison and trace descent retain their existing owners.
- VERIFIED (manuscript scope): the operator identity holds on each actual
  conductor-one ramified line and each level-prime-to-p two-degeneracy space
  at level exponent one, with the Eisenstein good recursion on old Eisenstein
  pairs. It does not follow from the old inertia-difference argument alone.

## Build checkpoint

- VERIFIED (dependency scan): the requested direct base imports reach a
  large repository dependency cone absent from the copied `.lake`; it
  reaches neither `ZInQKernel.OneProof.Main` nor `Contrib/TYZGenus`.
  The offline Lake build serializes Lean invocations and checks host load
  and available memory at each invocation.
- VERIFIED (build): Lake built all requested imports offline.
- VERIFIED (Lean): `Operator.lean` compiles serially. On the ramified
  coordinates the matrix comparison and scalar algebra prove both
  equations; the split proof adds the old contribution given
  `OldBlockCubic`.
