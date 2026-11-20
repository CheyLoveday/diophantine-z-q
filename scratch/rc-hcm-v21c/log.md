# Detector quaternion comparison: results log

**VERIFIED (base inventory).** The preceding conductor-one reports and audits describe the analytic and adelic torsors and the separate detector consumer. The base contains all of those new Lean files; the companion `RC/CMField2`, `RC/X0Branch` and `RC/O7Actual` sources are not on the pinned branch. The companion split-projector calculation is available at commit `81b4f7066`. No merge is required for its mathematical argument.

| Step | VERIFIED source inventory and boundary |
|---|---|
| Geometry | `RC/PMGeometry/Geometry.lean` gives `GeometricInput.classes`, its coarse Hecke-divisor comparison, and the Frobenius comparison. The coarse divisor only records a multiset; it supplies no map on individual kernels, endomorphism rings, or labelled actions. `RC/Eichler/Ideals.lean` defines the right ideals and their left orders independently of curves. Mathlib's elliptic-curve directory has no Deuring ideal-class theorem. |
| Tangent action | Tau Ceti's `Isogeny/Hom/Differential.lean` proves additive and contravariantly multiplicative pullback of invariant differentials. `RC/LocalDivision/Residue.lean` gives reduction, its principal kernel, and the uniformizer's Frobenius action. `RC/DivisionJoin` identifies the completion of the explicit order at the detector with that division order. |
| Primes of the level | `RC/Eichler/Local.lean` gives the standard Eichler matrix shape, and `RC/LocalWeights/LevelSupport.lean` gives the level character and the integral spectral projector. The companion split calculation diagonalizes projectors by order units. |
| Reciprocity and normalizations | `RingClassLattice.lean` gives the idele intersection/colon formula, the lattice for an integral ideal, and passage to the Artin image. The preceding `ShimuraJ` module leaves the equality with the inverse ideal lattice explicit. The covariant Hom lattice `Hom(A₀,A)` and the annihilator right ideal at the source are different uses of right ideals. Their inverses must be tracked before comparing with the adelic action. |
| Previous steps and consumer | The conductor-one logs record the singular-modulus integrality, Néron extension, étale torsion, and inert criterion. Tex 9245–9279 uses the sign fibre and identifies the actual reduction; tex 9279–9295 uses that pointwise identification and the separate parametrization square. `Consumer` forwards an oriented correspondence to `PMGeometry.InputsAtDatum`. |

## First verified calculation tranche

**VERIFIED (Lean 4.35.0):** `RamifiedCoset`, `RightIdealCoordinates`, and
`RestrictedCosets` passed direct `lake env lean` checks. The division
calculation is for the explicit order already used by the detector
(`q ≡ 3 mod 4`, tex 8437). The right-ideal calculation uses the
covariant Hom lattice, so the generator read from a prime-to-detector
ideal quotient is inverse to the positive ideal generator; the
annihilator on the source uses the reverse Hom group.

**VERIFIED (Lean 4.35.0):** `InverseLattice` passed direct checking after
building the pinned `ShimuraJ` import and its dependency graph.
The preimage of the completed reference lattice under the finite
idele is the completion of the reference fractional ideal divided by
the positive ideal. The fixed-idele Artin lift and the previous
Shimura consequence now give the arithmetic formula with the same
inverse convention, with no new reciprocity input.

**VERIFIED (Lean 4.35.0):** `SplitCoset` passed direct checking
after building `LocalWeights.LevelSupport`. For each positive
exponent, including at two, the standard idempotent and its
complement give the two chain exponents and the two labelled
diagonal-torus double coset representatives. The selected root of
the in-tree spectral projector has level image one.

**VERIFIED (Lean 4.35.0):** `GeometricOrders` and the strengthened
`SplitCoset` passed. Multiplication by the level lands in the geometric
level order, whose realized span equals the full order's span when the
level is a unit. Actual subgroup-preserving Hom groups and the source
annihilator are defined in scheme coordinates. The split standard chain
has exactly the Eichler matrix stabilizer, and the level projector is
zero or one without a further premise.

**STANDARD, locator UNVERIFIED:** `DeuringSupersingularEndOrder` states
the level-one maximal-order theorem (Voight, GTM 288; Deuring 1941).
The proposition elaborates over actual abelian varieties of dimension
one and integer quaternion orders; it has no provider. It is the only
new printed candidate.

**VERIFIED (Lean 4.35.0):** `GeometricKernel` and `InverseOrbit`
passed direct checks. Kernel containment descends along finite étale
surjective maps in any characteristic, giving the integral annihilator
and the corresponding Tate lattice; target factor maps carry the
actual level and labels. For completed adelic coordinates at the
reference, the prior torsor argument assembles the inverse action and
the quadratic sum reindexes by inversion. The geometry file uses the
kernel, descent and Tate modules directly, with the three small
comparison proofs adapted from `GRUniformQuasiInverse`. It does not
import the latter's unrelated height and effective isogeny dependencies.
