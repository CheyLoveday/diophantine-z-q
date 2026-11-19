# (O.7) on the actual stage

**Scoped stop.** The comparison constructor uses the visibility stage of
`pmLift` on the explicit `Adelic.levelOrder`. It builds
`Visibility.ComparisonInputs` and the corresponding family
`Odd.ThetaComparison` from the separate orbit, weight, normalizer, and
pointwise geometry data. The construction does not yet supply those data
for every admissible parameter. In particular it does not close
`PreLeaves.odd_staged`: the main missing proof is the identification of
the actual weighted support orbits with the oriented adelic Picard
torsors. No (O.7) congruence is taken as an input.

The actual integer representative follows *after* the raw (O.7)
congruence: `c₀ · 2^ω · lam` represents the coefficient after phase
removal. For an independently chosen coefficient, the requisite equality
identifies it with the raw phase-removed theta coefficient, independently
of the reduction side. The denominator in the orbit count is handled
before any congruence, by the existing `Visibility.O7_of_inputs`.

The missing support theorem cannot follow from `PMLocal` alone. Its
fields still permit setting `f` and each frame's weight `F` to zero while
leaving the frame vectors and integral data fixed. Conjugation and scaling
then preserve zero, the nonzero support is empty, and the affected frame
equalities become equalities of zero sums. Such a stage has no support
orbits, whereas the orientation set and the Picard group are both nonempty.

The following inputs remain. Each concerns fewer objects than the
comparison: it can be stated before the sum or without one of its two
sides. An isolated claim is not, in the strict logical sense, implied by
a congruence of two sums (cancellation can mask failures of its summands).
Here “weaker” means an upstream, independently meaningful obligation with
no requested equality of the final coefficient and the evaluation.

| Owner | Exact boundary and size |
| --- | --- |
| `rc-theta-join` | Supply the actual `PMLocal`, with its integral `f, χN` equal to the fixed adelic weights on the chosen representatives. The current type has conjugation invariance and finiteness but no condition characterizing where `f ≠ 0`. The minimal support bridge on the trace-zero norm sphere is nonzero weight iff the affine generator belongs to the class left order. This uses local support membership at each place, the filter exclusions, and the rational intersection in `Adelic.mem_leftRing_iff`; it is about individual vectors. |
| Missing quadratic and adelic theory | Identify the selected quadratic datum with the rational square-root model and its maximal order with the span of `1, (1+√(Dh_*))/2` (`QuadraticBasis`); this is a small integral-basis calculation. The allowed `Voight1467VToIII` is GLUE, UNVERIFIED; it gives the rational embedding only. The local classification still needs the away-from-level principal local ideals and the ramified residual embedding classes. Globally, the restricted-product argument must exhaust the embedding orbits and identify the centralizer intersection with the finite ideles of the maximal order. The smallest joint output is an orientation map and one genuine Picard equivalence to each fiber (`OrbitFibers`); neither the detector nor its point values occur. This is a substantial development spanning local and global arithmetic. |
| ELLIOT (character) | For `D > 1`, `NormCharacterDescent` is just that the quadratic norm symbol on ideals prime to `h_*` factors through `Pic(𝒪_F)`. Instantiate it independently from unramifiedness of the biquadratic extension and reciprocity, or from triviality of the norm symbol on principal ideal relations. Identify the resulting character with the one used by the selected datum (the pointwise Artin character match of `lamOf_reduction_at`). Neither claim involves the theta function. |
| Missing weight transport and `pm-adelic-join` | Transport the chosen class representatives through the torus and the right local operations. The exact remaining identities are the two factors in `TorusWeights` (common inverse right-unit factors and the known local root orders), and `Normalizers`' pointwise orbit reindexing/class projections and pointwise norm-times-Schwartz signs. The signs can be derived from the local character rules, using the same right-unit correction in both factors. The normalizers and good level/lattice charts come from the adelic inputs; the transport through the embedding orbits is separate medium-sized work. There is no statement here about any weighted contribution sum. |
| `rc-pm-geometry`, existing Cornut–Jetchev print, and `pm-adelic-join` | Supply `GeometricInput` and `InputsAtDatum` on the actual class set (the named Jetchev–Kane, special-fibre and pointwise CM reduction inputs). Realize the print at conductor one, with just the reference sign and fixed level orientations, and identify the target class projection on each translate. `cj_lamOf_reduction` uses the printed action plus the existing pointwise geometry. These claims concern the reduction of individual enhanced CM points and the specialization of the parametrization. The resulting single-tuple sum is independent of the other tuples and the theta coefficient. |
| `rc-stage-ident` and `rc-stage-selector` | Select a conductor-one datum at every admissible point (including off the simple zeros), identify its prime, precision and reduction place, and match the composites at that datum: the evaluation in `actualForStages.ev` equals `PM.lam` composed with `datumReduction` at the same place and embedding. The match must use the same detector transported from the twist, and the same integer multiplier `L`. A local identification of homomorphisms and a selection of data are independent of the orbits and coefficient. |
| Comparison wiring | The character field and its place above two are those of `LocalWeights.coefficientRing`; `ring_two` discharges contraction. If wiring prescribes its own `aθ`, identify it as a representative of the phase-removed raw theta coefficient. Alternatively use the integer representative constructed here after the raw congruence. In either case the comparison does not use a premise equating `aθ` to the detector. |

## Formal statements

Here `d = Dh_*`, `d = 4k+1`, `R_z` is the left order of the chosen class
representative, `u` is the integer lift of `P_M`, and `z(t,c)` is the
projection of an orbit to its class. Divisibility is in the coefficient
ring unless the integers are specified.

| Declaration | Statement and field supplied |
| --- | --- |
| `quadratic_parameter_le` | A negative `d = 4k+1` congruent to 1 modulo 8 has `k ≤ −2` (`stab`). |
| `quadratic_norm_one` | For `k ≤ −2`, every norm-one element of `ℤ[ω]`, `ω² = k+ω`, is `±1` (`stab`). |
| `exists_basisHom` | If `x² = 4k+1` and `(1+x)/2 ∈ R_z`, there is an integral algebra homomorphism taking `ω` to `(1+x)/2` (`param`, `stab`). |
| `halfIntegral_of_basisHom` | Conversely the image `x = 2f(ω)−1` is half-integral in the order (`param`, `stab`). |
| `order_isIntegral` | Every member of a quaternion order is integral over `ℤ` (`param`, `stab`). |
| `optimal_of_maps_integers` | If `ι : F → B` maps `𝒪_F` into the order, `ι(y)` is in the order iff `y` is integral (`param`, `stab`). |
| `halfIntegral_iff_optimal` | On the trace-zero sphere of norm `−d`, the half-integrality test is equivalent to an optimal embedding sending the chosen square root to `x`, given `QuadraticBasis` (`param`, `stab`). |
| `supp_iff_optimal_on_sphere` | With the exact weight support bridge, membership in `supp z` on the sphere is equivalent to that optimal embedding condition (`param`, `stab`). |
| `classG_norm_one` | The units of the chosen class order `R_z` have reduced norm one (`stab`). |
| `centralizer_span` | The quaternion centralizer of a nonzero trace-zero element is the rational span of `1,x` (`param`, `stab`). |
| `rational_conjugacy` | Two nonzero trace-zero rational quaternions of the same norm in the definite algebra are related by unit conjugation (`param`). |
| `basis_norm` | The reduced norm in the indicated integral basis equals the integral quadratic norm (`stab`). |
| `optimal_commuting_unit_sign` | An order unit centralizing an optimally embedded square root of negative `d ≡ 1 mod 8` is `±1` (`stab`). |
| `actual_stabilizer`, `IntegralSupport.stabilizer` | The stabilizer of each supported vector for the actual conjugation action has cardinality two; the latter only asks for half-integrality and the discriminant/basis data (`stab`). |
| `classOrder_mem_adelic` | Membership in the chosen rational class order is equivalent to membership in all conjugate completions of the underlying order (`param`, `stab`). |
| `projector_first_normalForm` | A trace-one integral idempotent with level image zero is conjugate to `diag(1,0)` in the split Eichler order (`param`). |
| `projector_forms_distinct`, `projector_two_normalForms` | For `e > 0` the two diagonal idempotents are inequivalent under Eichler-order units, and they exhaust trace-one projectors with level image zero or one (`param`). |
| `levelRoot_projector_normalForm` | The actual spectral projector selecting the level quotient is conjugate to `diag(0,1)` (`param`). |
| `card_residue_embeddings` | The quadratic finite field has two embeddings over the prime field into itself (`param`). |
| `card_orientations` | The `ω+1` orientation bits give cardinality `2^(ω+1)` (`card_Tup`). |
| `doubleCoset_restrict`, `doubleCoset_orbitEquiv` | In the ambient `L\G/U` quotient the image of `Hz` is `L\H/(H ∩ zUz⁻¹)` when `L ≤ H`; respectively, the equivalence relation and its quotient (`param`). |
| `OrbitFibers.param` | An orientation map with a Picard equivalence on each fiber gives `Tup × Cl ≃ Σ z, orbits(z)` (`param`). |
| `torsor_weight`, `TorusWeights.weight` | The inverse right-unit factors cancel, giving `χN·f = ζ₀(t)·χF(c)` (`weight`). |
| `norm_character_self_prime`, `norm_character_self_ideal`, `normCharacterDescent_self` | In a quadratic field of odd discriminant the norm symbol for the discriminant is one on eligible prime ideals, then on eligible integral ideals, hence descends by the trivial Picard character (`weight`, `reduction`; `D = 1`). |
| `twoPower_mul`, `unit_of_twoPower`, `TorusWeights.phase_unit` | A product of two roots of two-power order has two-power order and is a unit (`phase_unit`). |
| `bit_induction` | An invariant at a reference tuple persists across the cube if it persists across each single flip (`orientation`). |
| `cancel_edge_sign`, `atkin_edge`, `uniformizer_edge` | Equal square-one signs cancel in a single weighted term; the latter two statements use the actual `PM` lift identities (`orientation`). |
| `orientation_sum`, `Normalizers.orientation` | Edge congruences under a permutation of the class index imply that the weighted sums at every tuple agree modulo `2^M`; the latter uses the actual class projections, weights and lifts (`orientation`). |
| `cj_reference_class` | On the reference sign, each source translate reduces to the projection of the corresponding target translate (`reduction`). |
| `cj_lamOf_reduction`, `actual_reference_read` | The reference sum is congruent to `lamOf` under the pointwise matching hypotheses; at an admissible selected row this integer is the lift of the evaluation of the reduced scaled genus point (`reduction`). |
| `ring_two` | Divisibility by `2^M` of a cast integer in the actual coefficient ring implies divisibility in `ℤ` (`ring_two`). |
| `actual_representative`, `DatumAt.representative` | `2^M` divides `ζ₀(t₀)·(c₀·2^ω·lam) − thetaCoeff(S,mD)` once the separate fields above hold (`representative`). |
| `comparisonInputs`, `DatumAt.inputs` | The separate datum plus the chosen integer reading of the raw theta coefficient gives `ComparisonInputs` on `pmLift.geom` (`all`). |
| `thetaComparison_actual` | On the explicit level orders, a datum and coefficient reading at every admissible pair give `Odd.ThetaComparison Mθ aθ lam admissible ω(N)` (`all`). |

## Verification

All 11 files compiled individually with `lake env lean`. The separate
`scratch/rc-o7-actual/Axioms.lean` check printed the axiom dependencies of
all 44 new theorems and 19 definitions. There were no other dependencies
than the sets listed here; in particular neither the print nor the named
descent input is declared as an axiom.

| `#print axioms` result | Declarations |
| --- | --- |
| `propext`, `Classical.choice`, `Quot.sound` | The other 57 checked declarations, including `DatumAt.inputs`, `thetaComparison_actual`, both reference reduction theorems, and `actual_stabilizer`. |
| `propext`, `Quot.sound` | `quadratic_parameter_le`, `cancel_edge_sign` |
| `propext` | `twoPower_mul`, `torsor_weight` |
| None | `Orientations`, `flip` |

## Known issues

- `PMLocal` alone does not ensure an exact weighted support at the bad
  primes. It cannot be used to infer the existence or exhaustion of the
  embedding orbits.
- Normalizer formulas on *chosen* representatives require keeping the
  same compensating right-order-unit factor on both sides. The bare norm
  and local Schwartz identities are computed on adelic representatives;
  their product is the invariant used by the constructor.
- The existing abstract Cornut–Jetchev print does not by itself identify
  its objects with the actual geometric reduction. That identification
  remains the existing pointwise input; the theorem is used on a single
  sign. Its external locators were not rechecked. The wording of Voight
  Proposition 14.6.7, (v) ⇒ (iii) is UNVERIFIED, as cited at tex 9150–9155.
- The existing Jetchev–Kane source audit notes a level-one scope issue;
  see the known issues in `docs/research/rc-pm-geometry.md`. This work
  makes no independent application at level one.
- No new error in the comparison argument was established. The remaining
  translation and formalization gaps are listed above.

## Manuscript check

- 9101–9117 — unverified: the family is conditional on the actual orbit and geometry identifications.
- 9119–9120 — gap filled: the negative discriminant congruent to one modulo eight gives the norm-one bound in the integral quadratic basis.
- 9123–9135 — gap filled up to the support and integral-basis bridge: apply `nrd_eq_mul_iff`, the quadratic universal property, and integrality for optimality.
- 9136–9139 — unverified: away-from-level local orbit classification is not yet instantiated.
- 9140–9146 — gap filled in the split order chart by the integral projector calculation; the identification with the actual local embedding orbits must still be carried through.
- 9146–9148 — unverified: the two residual embeddings still need to be shown to exhaust the division-order orbits. The bit count is proved.
- 9149–9170 — gap filled for rational conjugacy, the subgroup restriction identity, and assembly of the orientation fibers; the rational existence citation and the global adelic-to-Picard identification remain unverified here.
- 9171–9179, 9297–9305 — gap filled: the common right-unit transport cancels from the norm and Schwartz factors.
- 9180–9190 — unverified: for `D > 1` the biquadratic unramifiedness and reciprocity proof of norm descent remains.
- 9191–9194 — gap filled: for `D = 1` the norm symbol is trivial by the quadratic decomposition law and multiplicativity.
- 9195–9264 — OK in the existing abstract specialization: invoke `thm3_1KappaOne_of_print` at a supplied realization with one sign; the realization at the actual point is an input.
- 9265–9296 — gap filled for the reference sum from the supplied pointwise geometry and the same-place detector. The geometric interpretation and matching of the maps are inputs.
- 9308–9316 — gap filled for stabilizers once the optimal embeddings and integral basis are supplied. Distinct residual orientations of the opposite roots are part of the remaining local identification.
- 9321–9327 — OK: the base product has two-power order and is a unit in the coefficient ring.
- 9329–9364 — gap filled from the pointwise normalizer and weight transport: the actual `P_M` lift congruences, square-one signs and reindexing give equality of the orientation contributions modulo the same power.
- 9366–9390 — OK: propagate along all coordinates and use the existing integer orbit count; there is no division of a congruence by two.
- 2081–2084, 2538 — OK: use a representative at the retained precision and contract from the coefficient ring to the integers.

The coordinate centralizer and rational intertwiner, the integral projector
change of basis, the subgroup restriction calculation, the integral basis
extension lemma, and the connectivity argument for the orientation cube are
on-the-spot arguments (provenance (c)). The pointwise reduction uses only the
existing Cornut–Jetchev print and the same-place geometry already in the tree.
