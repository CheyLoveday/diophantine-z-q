# Calibration inputs: proof report

## Result

The canonical reduction input is proved, including the actual local Kummer conditions. For every precision, including zero, the canonical comparison is an isomorphism of complexes and therefore a quasi-isomorphism.

The cohomology shape is proved conditionally from named arithmetic inputs. It is not claimed to be completely discharged: the existing universal-coefficient interface still requires its genuine coefficient/Kummer comparison, and integral Kummer self-duality still requires its comparison. The geometric curve binding is also explicit. The integral block model and its DiskTie are assembled from these inputs without assuming either the calibration shape or a canonical-reduction quasi-isomorphism.

## Files

- `ZInQKernel/Contrib/RC53Assist/CalibrationShape/CalibrationDischarge.lean`: standalone proof source; no imports of temporary new modules.
- `ZInQKernel/Contrib/RC53Assist/CalibrationShape/AxiomAudit.txt`: every explicitly named theorem's complete elaborated type and its axiom dependencies, followed by the principal model definitions.
- `ZInQKernel/Contrib/RC53Assist/CalibrationShape/ProofReport.md`: this report.

Proof-source SHA-256: `313b324762eb3be70a9717b9d35bf0231e18951d9fa648f974224ce1c05939ed`.

Proof-source size: 95,735 bytes.

## Reduction input

In namespace `ZInQ.Contrib.RC53Assist.CalibrationShape`, with
`{K : Type} [Field K] [NumberField K] {E₀ : WeierstrassCurve ℚ} {hZ : ℤ}`:

```lean
theorem canonicalCentralReduction_bijective
    (D : GenuineKummerData K E₀ hZ) (i : ℕ) (n : ℤ) :
    Function.Bijective ((canonicalCentralReductionMap D i).f n).hom

theorem canonicalCentralReductionMap_isIso
    (D : GenuineKummerData K E₀ hZ) (i : ℕ) :
    IsIso (canonicalCentralReductionMap D i)

theorem canonicalCentralReductionMap_quasiIso
    (D : GenuineKummerData K E₀ hZ) (i : ℕ) :
    QuasiIso (canonicalCentralReductionMap D i)
```

The local proof is not merely reduction of Kummer generators. It proves saturation of the integral Kummer lattice under every power of two. A division tower is shifted, adjusted by the degree-zero Tate vector of a coboundary, and descended to a rational local point. The quotient by the Kummer lattice is torsion-free, so its inclusion stays injective after coefficient extension. Finite Kummer generators and coboundaries give surjectivity. Product and Selmer-cone tensor decompositions then prove bijectivity of the actual canonical map, including its equality transport.

## Cohomological support and ranks

### Support

`compactCentral_outside` proves vanishing outside degrees one through three. Its inputs are:

- `MilneLocalFiniteness` and `MilneGlobalFiniteness`, as in the existing finiteness interface;
- `MilneLocalDimensionTwo` and `MilneGlobalDimensionTwo`, defined as the exact finite-module vanishing statements used by the proof;
- a totally complex number field;
- support containing the primes above two; its finiteness is already a field of the genuine data;
- finiteness of the rational two-primary torsion subgroup of the actual central curve.

The zeroth-cohomology proof uses actual Galois descent of Tate coordinates and finiteness of rational two-primary torsion. An integer annihilates every coordinate, and torsion-freeness of the Tate module forces the vector to vanish. Injectivity of the degree-zero local Kummer inclusions gives vanishing for the full Selmer cone.

For higher degrees, finite-level vanishing is lifted to the two-adic limit using surjective reductions, the power-of-two kernel description, residual finiteness, separatedness and completeness. The local Kummer conditions vanish above degree one. The two exact sequences of the Selmer cone yield vanishing above degree three.

The print locators are:

- Milne, *Arithmetic Duality Theorems*, second edition, Theorem I.4.10(c), p. 57: higher global cohomology is the product of the real-place contributions, which is zero for a totally complex field.
- Milne, Corollary I.2.3, p. 28, for the local finite-module duality and vanishing above degree two.
- Source: https://www.jmilne.org/math/Books/ADTnot.pdf.

### First-cohomology rank

`compactCentral_rank_one` applies the existing `arithmeticRank_eq_one`, with its degree-one and degree-two finiteness inputs constructed from integral finite generation. Quotienting by integral torsion does not change rank.

The hypothesis is `SelmerCorankOneOverK ℓ k`, the manuscript's full Selmer-corank-one assumption, including the divisible part of the Shafarevich--Tate group. See `diophantine_zq.tex`, lines 4332--4352 and 5264--5312. No finite-Shafarevich--Tate assumption is made.

The complex is bound geometrically before this arithmetic theorem is used:

```lean
hcurve : centralCurve D = (Ecurve ℓ).baseChange (QuadraticField k)
```

A corank theorem for `Ecurve ℓ` cannot determine the rank of the central twist for arbitrary unrelated genuine data.

### Reflected integral ranks

`finrank_range_dualMap_pid` proves equality of the image ranks of a map and its dual over a principal ideal domain, using Smith normal form. `homology_finrank_sum` is integral rank-nullity for cohomology. `dualCx_homology_finrank` consequently proves reflected cohomology ranks for every finite free complex.

The integral duality input is exactly:

```lean
def IntegralCentralKummerDuality : Prop :=
  Nonempty (HomotopyEquiv (centralRetainedGCx D hfinite).toCC
    (dualCx (centralRetainedGCx D hfinite) 3).toCC)
```

Here `centralRetainedGCx` is the actual relation-indexed version of `retainedCentralComplex D hfinite`, not an arbitrary complex. Its finite freeness, bounded support from cohomological support, and `TermwiseDualComputesRHom` are proved. Thus the certificate represents the full integral statement

```text
C_K ≃ RHom_Z₂(C_K,Z₂)[-3].
```

It is not a rank certificate or merely a rational pairing. In particular, it constrains integral torsion as well as ranks.

Locator: Nekovář, *Selmer complexes*, Theorem 6.3.4, p. 143, in the setting of 6.2.5(B), pp. 139--140, after the Weil-pairing and derived Kummer-orthogonality identifications.

Source: https://www.numdam.org/item/AST_2006__310__R1_0.pdf.

The resulting `integralCentralDuality_ranks` identifies ranks in degrees `n` and `3 - n`. It gives rank one in degree two from degree one, and rank zero in degree three from vanishing in degree zero.

## Shape, integral model and DiskTie

`calibrationShape_of_arithmetic` constructs

```lean
CalibrationCohomologyShape (compactCentralComplex D)
```

from the arithmetic inputs above. `integralCentralModel_of_arithmetic` then applies `integralBlockCentralModel`, supplying the proved canonical quasi-isomorphisms itself.

`diskTie_of_arithmetic` has conclusion

```lean
DiskTie D
  (centralDiskMatrix D hfinite 1).det
  (centralDiskMatrix D hfinite 2).det
  (centralDiskMatrix D hfinite 3).det
```

The complete quantifiers and hypotheses are printed in `AxiomAudit.txt`. With the three determinants denoted by δ₁, δ₂ and δ₃, this gives, for sufficiently large precision `i`,

```text
Nat.card (D.selH i 0) = cycOrder i δ₁
Nat.card (D.selH i 2) = 2^(i*i) * cycOrder i δ₂ * cycOrder i δ₃
Nat.card (D.selH i 3) = cycOrder i δ₃.
```

The matrices are the constructed integral Smith disk matrices. Their determinants are nonzero by the existing retained-model construction. No disk-order equality is an input.

## What remains

1. The existing `KummerCoefficientComparison` must be instantiated with its actual cochain comparison and quasi-isomorphism:

   ```lean
   comparison :
     (integerCoefficientComplex
       (arithmeticCoefficientComplex ℓ k D.S
         (arithmeticCentralFull ℓ k D hcurve))).truncLE 1 ⟶
       discreteSelmerComplex ℓ k
   quasiIso : QuasiIso comparison
   ```

   Its finite-support field is available from `D.hSfin`; its comparison and quasi-isomorphism are not constructed by this contribution. The existing universal-coefficient theorems remain conditional on this interface.

2. The full integral Kummer-duality comparison above must be supplied or derived with its pairing and derived local-orthogonality identifications. The finite-coefficient duality interface alone is not an integral two-adic comparison.

3. For arbitrary genuine data, the actual central twist must be bound to the curve covered by the manuscript's standing corank assumption. The explicit geometric equality used here is stronger than a bare cohomology identification and must not be silently assumed.

4. The exact Milne predicates and finite rational two-primary torsion fact remain named arithmetic inputs if their proofs are not already supplied. `centralCohomologyFinite` constructs the finite-generation witness from the finiteness predicates, so finite generation is not an additional unexplained calibration-shape assumption.

The separate `DiskArith`, arithmetic torsion identifications, rational calibration-coordinate transfer and remaining Theorem 5.3 inputs are not discharged here.

## Verification

The standalone file compiled with the required single-file command, from the repository root:

```sh
PATH=$HOME/.elan/bin:$PATH LEAN_NUM_THREADS=6 \
  taskset -c 112-127 nice -n 10 lake env lean \
  ZInQKernel/Contrib/RC53Assist/CalibrationShape/CalibrationDischarge.lean
```

Its maximum heartbeat setting is 800000. Only specific modules are imported directly. The proof source contains no proof placeholders, new axioms, evaluation commands, added parser extensions or final inspection directives.

Every explicitly named theorem and the principal model definitions are audited in `AxiomAudit.txt`. The audit completed with exit status zero: 76 named theorems and three model definitions, 79 dependency records, and no nonstandard axiom. Seventy-eight records depend on `[propext, Classical.choice, Quot.sound]`; `scalarResidue_identity` depends only on `[propext]`. The inspection commands are confined to temporary scratch source, not the final proof file.

Audit SHA-256: `fd4c47786fafb5823332cdcd33952e5a10d69259e7c384e56c894b5388667570`.

Audit size: 77,051 bytes.

All work is confined to new files under `ZInQKernel/Contrib/RC53Assist/CalibrationShape/`. No original file, existing compiled cache or repository history was changed. No repository operation, broad build or publication to the repository was performed.
