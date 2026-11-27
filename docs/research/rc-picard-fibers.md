# Picard fibers at the actual (O.7) stage

**Scoped stop at two placewise statements.** The class group quotient
and the transport to the actual weighted support orbits are proved.
Given a chosen rational embedding, `picardFibers_of_local` gives one
`ClassGroup (𝓞 F)` equivalence to each actual orientation fiber.
`orbitFibers_of_local` supplies the existing `orbitFibers` constructor.
The unproved inputs are the placewise torus chart and the placewise
existence of a prescribed orientation; their exact statements are
below. No unconditional `PicardFibers` is asserted.

The comparison uses the orbit of `a z_t` for the class of the finite
idele `a`. At the fixed orientation the action is transitive, and
the class of `a z_t` is the base class exactly when `a` is a product
of a diagonal field unit and an integral idele. With the local inputs
this gives the stabilizer in the manuscript, not a cardinality match.
The valuation, restricted product patching, representative transport,
and quotient bookkeeping are on-the-spot (provenance (c)).

All eleven modules compiled with `lake env lean`. The [axiom audit](../../scratch/rc-picard-fibers/Axioms.lean)
checked 292 theorems, including generated proofs, and 59 definitions.
It found only `propext`, `Classical.choice`, and `Quot.sound`.
The [`#print axioms` output](../../scratch/rc-picard-fibers/axioms.txt) lists all 69 written theorems.

## Known issues

- No new error in the manuscript was identified in tex 9150–9169. The
  restricted product and the two local integral structures need explicit
  comparison in Lean.
- The source comment about the bare adelic norm character in
  `Visibility.ThetaStage.χN` remains subject to the correction in
  `docs/research/rc-o7-orbits.md`. The combined summand in tex 8612–8614
  is the invariant object. The present argument does not descend the
  bare character.
- The earlier case `D = N = 193` is excluded by splitting at all primes
  of `2N`. The full filter also retains positive squarefree `D`,
  coprimality with the fixed partner, the detecting condition, and the
  odd fundamental discriminant.
- Voight Proposition 14.6.7, (v) ⇒ (iii), tex 9154, is the existing
  GLUE (UNVERIFIED / unread) input to
  `O7Orbits.exists_reference_embedding`. No new print or leaf is used.
  The cited Cornut–Jetchev reduction in tex 9195–9295 is a separate
  step and is not used to count the Picard fibers.

## Statements and consumers

Lean names are in `ZInQ.Manuscript.RC.PicardFibers`. The finite
idele and centralizer results prepare `OrbitFibers.fiber`; local
conjugacy relates that field to the already existing
`OrbitFibers.orientation`.

| Declarations | Statements |
| --- | --- |
| `ideleExponent_eq_zero_iff`, `ideleExponent_mul`, `ideleExponent_cofinite` | The negative logarithm of the multiplicative valuation vanishes exactly on valuation one, adds on products, and is zero outside a finite set. |
| `ideleVal_ne_zero`, `fractionalIdeal_eq_of_counts`, `count_idealOfIdele`, `intValuation_eq_count` (private) | An idele has nonzero local valuation; nonzero fractional ideals are equal if all exponents agree; the ideal product has the prescribed local count; the valuation of a nonzero ring element is the exponential of minus the count of its principal fractional ideal. |
| `ideleToIdeal`, `count_ideleToIdeal`, `mem_ker_ideleToIdeal`, `ideleToIdeal_surjective`, `ideleToIdeal_diagonal` | The valuation product is a homomorphism to nonzero fractional ideals, with the specified prime counts, kernel the unit ideles, surjectivity by local uniformizers, and the principal ideal on diagonal units. |
| `ideleClassMap_surjective`, `ker_ideleClassMap`, `ideleClassEquiv` | The map to the class group is onto. Its kernel is the product of diagonal field units and integral ideles. The quotient by that subgroup is multiplicatively equivalent to the ideal class group. |
| `regroup`, `rationalPrimeUnder_finite`, `groupIdeles`, `groupIdeles_apply`, `rationalPrimeEquiv`, `mem_ker_ideleToIdeal_iff_grouped` | One can regroup a restricted product along a map with finite fibers. Contraction from the primes of the ring of integers to the primes of the integers has finite fibers. The grouped idele has the old coordinate at every place; over the rational prime `p` the ideal is `(p)`. The kernel is exactly the ideles with integral units in every block. |
| `commute_factor`, `intertwines_factor` (private), `adelic_factor_iff` | An integral intertwiner `r` for the two local conjugates gives the centralizer element `w r⁻¹ z⁻¹`, and conversely. The local intertwiners exist everywhere iff `w = g z r` adelically, with centralizer element `g` and everywhere integral `r`. |
| `rationalCentralizer_eq_range` | The rational ambient units commuting with the trace-zero reference root are the image of `Fˣ` under the given embedding. |
| `leftRel_sup_iff_doubleCoset`, `doubleCoset_mulEquiv_iff` (private), `ideleOrbitEquiv` | In a commutative group the left relation modulo `L ⊔ U` is the double coset relation for `L, U`. A multiplicative equivalence preserving the two subgroups preserves that relation. With the indicated subgroup comparison, `ClassGroup R` is equivalent to the double classes represented by `g z` for centralizer elements `g`. |
| `AdmissibleD.mod_eight`, `AdmissibleD.disc_squarefree` | The full odd filter implies `d ≡ 1 mod 8` and squarefreeness of `d`. |
| `unitConj_map`, `unitConj_symm`, `unitConj_trans`, `unitConj_iff_map`, `unitConj_affine`, `exists_levelPrime` (private) | Unit conjugacy can be mapped, reversed, composed and reflected by an isomorphism; comparing `2X−1` and `2Y−1` is equivalent to comparing `X` and `Y`; every prime dividing the level occurs in the level enumeration. |
| `actual_local_conj_iff`, `reframe_root` (private), `unitConj_iff_intertwines` (private), `actual_orientation_factor_iff` | The actual orientation is an exact test of local affine generator conjugacy. Rationally reframing the chosen class representative turns the local root into the transported fixed root. Completed order conjugacy is the ambient intertwining equality with an integral unit. With two rational frames, equality of actual tuples is equivalent to adelic centralizer and integral unit factorization. |
| `patch_admissible_adele`, `transport_local` (private), `local_mem_conj_iff`, `exists_frame` | Patch the local witnesses by the identity away from the labeled primes and finitely many denominators. Transporting a rational generator through the representative change conjugates its local image just by the remaining right unit. That conjugation preserves membership in the completed order. Every representative has a rational and integral translation to the stage's chosen class representative. |
| `supportFromFrame`, `orbitFromRep`, `adelicClass_eq_of_translate` (private), `class_stabilizer_iff` (private) | An admissible representative yields a supported generator after an appropriate rational translation and hence a weighted support orbit. Such translations preserve the ideal class. The rational stabilizer of the chosen ideal is exactly the left order unit group. |
| `frame_cancel_forward`, `frame_cancel_backward`, `conj_value_commute`, `same_class_orbit_iff` (private) | Comparing two frames and a stabilizer gives the diagonal-centralizer relation; the converse recovers the stabilizer. A conjugated unit equals the original iff it commutes. Inside a fixed chosen class, equality of support orbit classes amounts to left rational centralizer and right integral translation. |
| `orbitFromRep_eq_iff`, `adelicClass_classRepresentative` (private), `orbitFromRep_eq_frame` (private), `orbitFromRep_surjective` | The same double coset criterion holds across all classes. The chosen representative maps to its own class; any frame to that class gives the same orbit. Rational conjugacy exhausts the actual weighted support. |
| `reframe_frame`, `cancel_right_factor` (private), `orbitFromRep_orientation_iff` | Reframing cancels the left rational multiplier, and changing either representative by right integral factors does not affect its adelic centralizer orbit. Two representatives map to the same actual tuple iff they differ by an adelic centralizer element and a right integral unit. |
| `diagonalCentralizer_le`, `centralizer_mul_admissible`, `basedFiberEquiv`, `picardFibers_of_comparison` | The rational centralizer is contained in the adelic one. Centralizing adeles act on admissible representatives by left multiplication. With a representative of a tuple, the double classes represented by its centralizer orbit are equivalent to the actual orientation fiber. Composing with the idele quotient yields `PicardFibers` once the rational and integral subgroup comparisons and the representatives are supplied. |
| `primeBelow_finite`, `idelePrimeBlocks`, `idelePrimeBlocks_apply`, `idele_kernel_primeBlocks` | Use the same regrouping and valuation-one kernel in the quaternion order's natural-prime convention. Every rational prime still has a finite block, and regrouping preserves each coordinate. |
| `conjugate_mem_iff` (private), `blocksCentralizerEquiv`, `ideleCentralizerEquiv` | Conjugation by a subgroup member preserves subgroup membership. The local unit charts glue to the adelic centralizer by checking integrality off the finitely many nonintegral places of one admissible representative. Regrouping then gives the equivalence from finite ideles. |
| `ideleCentralizerEquiv_diagonal`, `ideleCentralizerEquiv_integral`, `ideleCentralizerEquiv_rational` | The equivalence respects the embedded diagonal exactly, identifies every chosen conjugate integral subgroup with the valuation kernel, and identifies the rational centralizer with the range of the diagonal idele embedding. |
| `labelAt_conj`, `levelBit_conj`, `divisionBit_conj`, `chosen_generator` (private), `realize_tuple` | In a commutative residue ring, unit conjugation preserves the residue. The level and division bits survive normalization to the chosen class representative. The locally labeled witnesses give an admissible adele whose actual orbit has the prescribed tuple. |
| `AdmissibleD.disc_neg`, `reference_sq` (private), `referenceAffine_spec`, `referenceUnit_sphere` | The discriminant is negative by the filter; the image of the square root has square `d`, is twice the affine generator minus one, and lies in the actual rational trace-zero norm sphere. |
| `picardFibers_of_local`, `orbitFibers_of_local` | Supply `OrbitFibers.fiber` on the actual orientation for every tuple from the two local obligations below; the package supplies `DatumAt.orbits` for `integralSupport`. |

## Remaining hypotheses

The reference quantities are `d = D · (−s.weights.m)`,
`x₀ = ι₀(√d)` and `α = ι₀((1 + √d)/2)`. Write `C_p` for the
centralizer of `x₀` in `B_p^×`. The two arithmetic obligations are
`∀ p, Nonempty (LocalTorusChart (ActualOrder s) ι₀ x₀ α p)`
and `∀ t, HasLocalRealizations s α t`:

1. **Completed torus and maximal order (missing theory, tex 9161–9166).**
   For every rational prime `p`, there is a multiplicative equivalence
   `e_p : (∏_{v|p} F_v^×) ≃* C_p`, with
   `e_p((k)_v) = ι₀(k)` for each `k ∈ Fˣ`. For every
   `u ∈ B_p^×` with `u⁻¹αu ∈ R_p` and every block `a`,
   `u⁻¹ e_p(a) u ∈ R_p^× ↔ ∀ v | p, a_v ∈ 𝓞_v^×`.
   The size is a local algebra comparison for arbitrary split, inert
   and ramified primes, including the integral intersection. A route
   is the completion of the finite free quadratic order at `p`,
   its decomposition via the Chinese remainder theorem applied to
   powers of the prime ideals over `p`, then inversion of `p` and
   the centralizer computation in the ambient quaternion algebra.
   The integral intersection follows once the completed ring of
   integers is identified with the integral closure of `ℤ_p` and
   generated by the affine element. One inclusion uses the
   generator in the completed order, and the other uses integrality
   of elements of a finite `ℤ_p` order. Apply the same test to the
   inverse to get the unit intersection.
   Every statement here is about a single prime; it implies no
   nonemptiness or count of global orientation fibers.
2. **Realize each local tuple (missing local conjugacy construction,
   tex 9136–9156).** For every tuple `t` and rational prime `p`,
   there exists a unit `u_p ∈ B_p^×` with
   `X_p = u_p⁻¹αu_p ∈ R_p`. If `p = levelPrime N j`, the
   `LocalWeights.level` value of the split chart of `X_p`
   must have bit `t j.castSucc` when compared to its complement.
   If `p = ℓ₀`, the residue of the division chart of `2X_p−1`
   must have bit `t (Fin.last _)` when compared to its negative.
   Else there is no label condition. This is the local ambient
   conjugacy from the reference generator to the chosen integral
   normal form, with a prescribed root or its opposite at the
   labeled places. The base proves classification of integral
   forms on existing support. Constructing a local unit from
   the rational reference to the model is a separate existence
   argument. This asks for one local unit at a time; it has
   neither a restricted support condition nor an ideal class.

The intermediate assembler `picardFibers_of_comparison` takes an
adelic equivalence with only its two subgroup membership tests and a
point meeting each tuple. The local hypotheses imply those inputs by
`ideleCentralizerEquiv_…` and `realize_tuple`. The point condition
gives nonemptiness only. `AdelicAdmissible`, used in the transport,
asserts only that the conjugated affine generator is integral at every
prime. Neither condition identifies two orbits or their classes.

The upstream actual stage inputs are as follows. The comments about
relative size refer to the scope of the obligations: no reverse logical
implication from a bare equivalence of types is needed.

| Owner | Hypothesis and source |
| --- | --- |
| ELLIOT input | `AdmissibleD s D`, tex 9105–9108, 9121–9134: positive squarefree `D`, `IsCoprime D (−s.weights.m)`, detecting Legendre symbol `+1`, odd fundamental `d`, and split at all primes dividing `2N`. The partner has detecting symbol `−1`, tex 8372 and 9205–9208. These conditions constrain only rational arithmetic. |
| `rc-theta-join` | `StageAt` with the actual `PMLocal`, and `SupportBridge s D`, tex 9123–9134: on the stated rational norm sphere, `f z x ≠ 0 ↔ HalfIntegral (classOrder … z) x`. This is a pointwise membership test prior to any orientation or fiber comparison. |
| `rc-o7-character` | `QuadraticBasis F d`, tex 9121–9131, supplying the quadratic model and the integral affine basis. No norm character is used for the torsor. |
| Existing ELLIOT / Voight GLUE | A chosen `ι₀ : F →ₐ[ℚ] B` from `O7Orbits.exists_reference_embedding`, tex 9150–9154. The existing implication is unchanged. The embedding has neither an integral condition nor a chosen orientation. |

The downstream inputs remain assigned separately: `DatumAt.weights`
(tex 9171–9194 and 9297–9305; torus weights and character lanes),
`DatumAt.moves` (tex 9317–9357; normalizer brief), and
`DatumAt.reference` / `DatumAt.reduce` (tex 9195–9295; geometry and
reference reduction lanes). No part of those statements is used to
identify the class group of a fiber.

## Manuscript check

- 9105–9108, 9121–9134 — OK: the full filter and the exact pointwise support interpretation are kept; splitting at two is used in the modulo eight consequence.
- 9136–9148 — gap filled: the existing local classification detects equality of actual tuples exactly at every prime, including the split maximal charts outside the distinguished set.
- 9150–9154 — unverified: the cited Voight wording is unread; only the existing conditional implication via `exists_reference_embedding` is available.
- 9155–9156 — unverified: realizing the prescribed local forms from the chosen reference at each prime still requires the local ambient conjugating units.
- 9157–9160 — gap filled: outside the union of the two finite nonintegral sets the centralizer component can be one and the intertwiner `z_p⁻¹ w_p`.
- 9161–9164 — gap filled: the rational centralizer comes from `Fˣ` by the span computation, and restricting a double coset fixes the conjugated integral subgroup.
- 9164–9165 — unverified: the embedded completed quadratic torus and its integral units need the placewise comparison above.
- 9165–9166 — gap filled: finite valuations give a surjective fractional ideal map with integral kernel and send diagonal units to principal fractional ideals; the kernel after passage to classes is the stated product.
- 9168–9169 — OK conditional on the two local obligations: the quotient is by the exact stabilizer, so the resulting class-group parametrization has one point per class.
- 9195–9295 — unverified in this lane: the later Cornut–Jetchev specialization uses the identified fiber for reduction and is outside the torsor proof.
