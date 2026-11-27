# The oriented Picard torsor at the actual (O.7) stage

**Scoped stop at the local classification.** Given the exact support bridge
on the trace-zero norm sphere, the visibility stage of an actual
`StageAt` has an orientation map from its weighted support orbits to
`Orientations N.primeFactors.card`. It reads the split Eichler quotient at
each prime of the level and the residue of the square root at the division
prime. At split maximal orders the same companion matrix works for every
supported generator, including at primes ramified in the quadratic field.
The existing Voight implication yields the rational reference embedding
after checking its two field hypotheses.

`integralSupport` supplies `DatumAt.support`, and `orientation` supplies
`OrbitFibers.orientation`. The outstanding global hypothesis, formally
`PicardFibers` specialized to `IntegralSupport.classGroup`, is exactly
one equivalence per tuple:
```text
∀ t : Orientations N.primeFactors.card,
  ClassGroup (𝓞 F) ≃ {P : OrbitSet s.visibility (index s D) // orientation s H P = t}
```
It is a parameter of `orbitFibers`. It is not asserted as a theorem, and
there is no postulate about coefficients or sums. `TorusWeights` and
`PreLeaves.odd_staged` are not constructed.

The proof uses `d = D · (−s.weights.m)` and writes `d = 1 − 4c`. The
monogenic model in the assumed `QuadraticBasis` means that the affine
generator `(1+√d)/2` specifies the embedding. The local arguments are
given in that generator coordinate, including at two. At the odd division
prime the square root itself determines the generator. The two nonzero
opposite reduced roots distinguish the two embeddings of the inert
quadratic residue field. The choice of which root is labeled true has no
arithmetic content. The local tuple set has `2^(N.primeFactors.card + 1)`
elements by the host's `card_orientations`. This does not establish that
every tuple occurs on the actual global support.

## Statements and consumers

All names below are in `ZInQ.Manuscript.RC.O7Orbits`. An orientation
consumer supplies part of `OrbitFibers.orientation`; the reference
embedding is preparatory work for `OrbitFibers.fiber`.

| Declarations | Statement and consumer |
| --- | --- |
| `unitConj_iff_level_of_projectors` | Trace-one idempotents with level value zero or one are integral-unit conjugate iff their level values coincide (orientation). |
| `projector_recovers` | A unit-separated affine root gives a trace-one projector; the affine generator is recovered from it by multiplication by the gap and addition of the other eigenvalue (orientation). |
| `split_level_conj_iff` | Trace-one generators of the same split polynomial with unit root gap are conjugate iff their images on the level quotient agree (orientation). |
| `split_level_labels` | Two diagonal matrices realize the two distinct level images, for every positive exponent, with determinant `a(1-a)` (orientation). |
| `division_conj_iff_red`, `division_labels` | Equal squares and nonzero residue give conjugacy iff residues agree; the only possible residues are the reference residue and its distinct negative (orientation). |
| `padic_prime_sq_not_dvd` | A squarefree rational discriminant is not divisible by the square of the uniformizer in any `ℤ_p` (orientation). |
| `exists_cyclicColumns`, `cyclicColumns_companion` | When the matrix discriminant is not divisible by `p²`, some `(v,Xv)` is an integral basis; for trace one it takes `X` to the companion matrix (orientation). |
| `maximal_split_normalForm` | Every trace-one generator with determinant `c` and discriminant prime exponent at most one is conjugate to `[[0,-c],[1,1]]` (orientation). |
| `split_branch_of_residue`, `split_branch_odd`, `split_branch_two` | Lift a simple residue root of `T²−T+c`, with a unit gap; the admissible odd Legendre test or `d ≡ 1 mod 8` at two supplies that root (orientation). |
| `division_root_exists` | At the detecting prime with nonsquare discriminant residue, an integral trace-zero root exists with nonzero residue (orientation). |
| `SupportBridge.half`, `integralSupport`, `actualSupport_iff_optimal` | The exact given bridge supplies `IntegralSupport.half` and both directions of the support/optimality test; with the given quadratic basis, negativity and the congruence modulo eight, this constructs `DatumAt.support`. |
| `splitOrderChart`, `divisionOrderChart`, `splitOrderChart_compatible` | Restrict the actual ambient split and division charts to the completions of the specified level order; the integral split chart recovers the ambient chart under coefficient inclusion (orientation). |
| `unitConjRing_apply`, `unitConjRing_map`, `unitConjRing_mul` | Conjugation is given by the unit and its inverse, commutes with ring maps, and composes by multiplication (orientation). |
| `localGenerator_spec`, `localGenerator_square` | Twice the actual local affine generator minus one is the transported supported vector and squares to the discriminant (orientation). |
| `localClassUnit_mem`, `localGenerator_conj`, `residue_eq_of_unitConj` | A class-order unit transports to an integral unit at the chosen representative; the transported affine generators are conjugate, so they have equal commutative residue values (orientation). |
| `levelPrime_ne_detecting` | No indexed level prime is the detecting prime; this uses the actual geometry's Eichler coprimality (orientation). |
| `matrix_trace_det_of_affine`, `split_generator_trace_det` | A nonscalar matrix satisfying the affine quadratic equation has trace one and the prescribed determinant; the actual split matrix is nonscalar and satisfies the equation (orientation). |
| `residueBit_swap_ne`, `split_level_residue_cases`, `split_level_bit_iff`, `division_bit_iff` | Distinct opposite labels give different bits; the split and division bits distinguish exactly the integral conjugacy classes in their charts (orientation). |
| `divisionGenerator_square`, `division_red_ne_zero_of_sq`, `generatorOrientation_last` | The actual division chart has the discriminant square relation, a nonzero discriminant residue forces a nonzero root residue, and the last coordinate reads that root's bit (orientation). |
| `actual_level_bit_iff`, `actual_division_bit_iff`, `actual_maximal_split_normalForm` | On actual support, equality of the corresponding coordinate is exactly conjugacy in the positive-level or division chart; away from both distinguished places the actual affine generator has the common maximal matrix normal form (orientation). |
| `generatorOrientation`, `orientation`, `orbitFibers` | Form the product of the local bits, descend through the actual support orbit relation, and package the map with an independently supplied `PicardFibers` into `OrbitFibers`. |
| `quadratic_hom_conj_iff` | Conjugation of the image of the generator is equivalent to conjugation of the entire local algebra map in the monogenic quadratic model (orientation). |
| `levelPrime_exp`, `split_branch_of_splitsIn`, `level_bit_of_filter`, `division_bit_of_filter` | The indexed level prime has positive exponent. Under the fixed split and detecting conditions the two actual bit tests apply with no separately chosen local root (orientation). |
| `detecting_nonsquare`, `padic_nonsquare_of_residue`, `tensor_isField_of_nonsquare`, `exists_reference_embedding` | Multiply the detecting-prime Legendre symbols, lift the nonsquare test, use quadratic base change at each ramified place, and apply the existing conditional Voight print (fiber). |

In the next step the admissible adelic representatives should be those
`z` for which `z⁻¹ ι₀((1+√d)/2) z` belongs to the completed order at
every prime. With two such representatives in the same tuple, the local
intertwiners should factor one as `a z_t r` with (a) in the centralizer
and (r) integral. Outside the finite set where the representatives are
not both integral, one can take the centralizer component to be `1`.
Formalizing this still requires the dictionary between the restricted
product of the quadratic local unit groups and ideles indexed by primes
of `𝓞 F`. It is that dictionary, together with the optimal unit
intersection, that permits the class-group quotient and the norm
character to use the same representatives.

The companion-basis proof, integral intertwiners and the passage through
the chosen local and class charts are on-the-spot (provenance (c)).
The square-root lifting and tensor calculation use existing formal
results. No further literature claim is introduced as a print.

## Remaining hypotheses

| Owner | Exact boundary and why it is upstream of (O.7) |
| --- | --- |
| `rc-theta-join` | Actual `PMLocal` and the exact `SupportBridge`: on the trace-zero norm sphere, `s.visibility.f z x ≠ 0 ↔ HalfIntegral (classOrder … z) x`. For later weight transport, identify `f` and `χN` with the fixed adelic functions evaluated at the chosen representatives. These are local or pointwise statements about inputs even before a point evaluation is chosen. |
| `rc-o7-character` | `QuadraticBasis F d` and, for `D > 1`, `NormCharacterDescent F hstar`. These concern only the quadratic field and ideals. For `D = 1` use the existing `normCharacterDescent_self` with the quadratic, odd field discriminant; there is no new descent hypothesis in that case. |
| Existing Voight input | `Voight1467VToIII` (GLUE) produces a rational algebra embedding from the two proved field conditions, independently of any level structure, support, or weight. |
| Global torsor follow-up | `PicardFibers`, as displayed above. The remaining construction is substantial: choose adelic realizations of the local tuples with the restricted product condition; exhaust each tuple after rational conjugation; group finite completions of `F` by rational prime and identify the embedded centralizer and its integral units; then send finite ideles to fractional ideals by their valuations. `classesEquiv`, `rational_conjugacy`, `centralizer_span`, and `doubleCoset_restrict` are already available. The new local conjugacy criteria supply the tuple condition, but do not prove the restricted product or ideal quotient comparison. The fiber statement sees no weight values or detector. |
| Torus weight follow-up (with `rc-theta-join` and `rc-o7-character`) | Supply `DatumAt.weights`: for the torus parametrization choose `a_c z_t`, compare to the chosen representative by a rational unit and a right order unit, and use that *same right unit* in both transport equations. The norm factor picks up its character, and the Schwartz factor picks up the inverse character. Match the torus norm character with the descended ideal character; derive both base orders from the local weight values. All identities are on individual orbits and contain no `P_M`. |
| Normalizer follow-up / `pm-adelic-join` | `DatumAt.moves`: the actual one-bit Atkin–Lehner and division moves must give the corresponding orbit reindexing and pointwise class and weight equalities. This compares individual terms without using the reference reduction. |
| `rc-pm-geometry`, existing Cornut–Jetchev print, `rc-stage-ident`, `rc-stage-selector` | `DatumAt.reference` is the selected tuple matching the reference enhanced CM data. `DatumAt.reduce` relates that single tuple to the lift of the detector via the actual specialization and same-place evaluation. Neither uses the other tuples or the raw theta coefficient. |

“Weaker” here means a strictly smaller obligation in the proof of (O.7).
In particular, none asks for a comparison of the full theta coefficient
with the detector. A congruence of total sums need not imply their
pointwise ingredients; no reverse logical implication is claimed.

## Verification

All eight deliverable files compiled individually with `lake env lean
--threads=1`. The check in `scratch/rc-o7-orbits/Axioms.lean` reports
the axiom dependencies of all 47 new theorems and 20 definitions or
abbreviations. The only axiom names reported were the three in the table.

| `#print axioms` result | Declarations |
| --- | --- |
| `propext`, `Classical.choice`, `Quot.sound` | All other 59 declarations. |
| `propext`, `Quot.sound` | `quadratic_hom_conj_iff`, `cyclicColumns`. |
| `propext` | `unitConjRing`, `unitConjRing_apply`, `unitConjRing_map`, `unitConjRing_mul`, `residue_eq_of_unitConj`. |
| None | `UnitConj`. |

## Known issues

- The comment on `Visibility.ThetaStage.χN` calls the adelic
  norm-character factor itself well defined on the double quotient. It is
  defined on classes via chosen representatives, but the bare adelic
  character need not descend: at a split prime dividing `|h_*|`, the
  determinant on maximal order units is surjective onto local units and
  the quadratic character on those units is nontrivial. Tex 8571–8578 and
  8612–8614 assert independence of the combined summand, where the
  Schwartz factor cancels the change. The manuscript's assertion about the
  combined summand is unaffected.
- The support bridge needs the admissible filter; the known
  `D = N = 193` counterexample outside the filter is not covered.
- Voight Prop. 14.6.7, (v) ⇒ (iii), at tex 9154 is GLUE and UNVERIFIED.
  The argument checks the hypotheses of the existing type and does not
  audit the cited printed wording. The existing Jetchev–Kane level-one
  issue is noted in `docs/research/rc-pm-geometry.md`; it is not used here.

## Manuscript check

- 9105–9108, 2492, 8372, 9205–9208 — gap filled: the chosen stage supplies the negative detecting character of the partner; the product residue is nonsquare and the local scalar extension is a field.
- 9121–9123 — OK: take the odd fundamental discriminant and the split filter as given; their consequences for the local polynomials include squarefreeness and `d ≡ 1 mod 8`.
- 9123–9134 — gap filled conditional on the exact support and basis inputs: apply the given half-integrality criterion to the actual norm sphere and pass to the completed chosen left order.
- 9136–9139 — gap filled: a cyclic basis of the integral matrix proves the unique local normal form, even when the quadratic discriminant has valuation one.
- 9139–9144 — gap filled: the projector recovers the affine generator and its image on the cyclic quotient gives exactly two classes, with a simple affine root also at two.
- 9145–9148 — gap filled: in the division model the two roots have distinct residues, and their common-residue lifts are conjugate by an integral unit. The product of the local bits descends to actual support orbits.
- 9150–9154 — unverified: the Voight locator and wording were not read; the provided implication has its real and finite field hypotheses checked.
- 9155–9160 — unverified: the restricted-product realization and exhaustion of the tuple still need the global construction.
- 9161–9169 — unverified: the quadratic integral-unit intersection and valuation-to-fractional-ideal comparison remain.
- 9171–9179, 9297–9305 — OK: the raw adelic formulas use centralization and norm multiplicativity; for chosen representatives the compensating unit must occur in both factors. Actual transport remains.
- 9180–9194 — unverified here: use the separate descent input for `D > 1` and the host's trivial character proof for `D = 1`.
- 9308–9316 — gap filled for the distinct division orientations of opposite roots; the stabilizer calculation itself is inherited from `IntegralSupport.stabilizer`.
