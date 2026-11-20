# CM field descent sizing and results

Base `60b162a0d`; merged `cb118b8c28` as `33937701f`. Sizing recorded before running Lean. Source checks below are VERIFIED by reading; proposals are on the spot (c).

| Step | Available and missing |
| --- | --- |
| 1a: integrality | Vendored `eval_jLattice_eq_zero_of_isAddCyclic` and `isUnit_leadingCoeff_diag_of_not_isSquare` take a genuine cyclic sublattice and give the diagonal equation and a unit leading coefficient. Normalizing it is small. Remaining lattice work: period basis of an embedded fractional ideal, homothety invariance, primitive multiplier gives cyclic quotient and its index is the positive norm, and choose a nonsquare norm. |
| 1b: multiplicities | Root membership, monicity and degree do **not** imply the asserted product at a repeated-root specialization. The vendored formal `eq_cosetTwoVarPoly_of_forall_isRoot` uses distinct Laurent series; the analytic product can instead use pairwise distinct translates near the cusp then analytic continuation. The merged `orbitPoly` has the corresponding SL₂ coset degree and analytic coefficients; identifying this product with the primitive triangular coset reps needs the orbit/coset dictionary. |
| 1b: exact order and Pic | `jLattice_surjective` gives a complex period pair; the existing cyclic-sublattice theorem goes from sublattices to roots, not from roots to sublattices. Tau Ceti already defines `Pic O` as invertible fractional ideals modulo principal ideals; `mkPic` is onto and Mathlib's class group API characterizes equal representatives. Fowler's `proper_iff_isUnit` on fork main supplies the proper-to-invertible direction for quadratic orders, after passage to a fractional ideal. An arbitrary period lattice still needs rescaling into the embedded quadratic field, and identifying its **exact** multiplier order under conjugacy. The imported degree print would bypass the step and is excluded. |
| 2: ring class field | `ringClassArtinEquiv` describes arithmetic Frobenius on the class field. `GlobalExistence/NormLimitation.lean` and `Correspondence.lean` give norm subgroup comparisons for finite abelian layers. Chebotarev supplies primes in a prescribed conjugacy class; split-prime inclusion can be proved by applying it to a finite Galois compositum. Neither identifies the analytic class invariants. `KroneckerCongruence` is an unproved polynomial identity over ZMod ℓ (no CM theory in its statement); getting the correct oriented Frobenius on singular moduli additionally needs integral reduction and a way to choose the correct factor. Closure of the j-set under conjugacy does not alone prove the action consists of Picard translations. |
| 2: Heegner coordinates | The paper calculation uses `(A,B,C) ↦ (A/N,B,NC)` with the same primitive discriminant, and the product of the two-generated ideals. Need the bridge from these embedded lattices to invertible ideals in the given abstract order. |
| 3: branch | `finitePointEval` and affine chart injectivity support descent of the evaluation map by range restriction. Level one has just the j-coordinate (need compare its normal model to the j-line). The denominator in `exists_analyticJN_ratio` represents j_N by chart sections, i.e. in the opposite direction from expressing all chart sections in the two coordinates. Its nonvanishing alone is not a descent criterion; a local presentation of the normalization over the plane pair would suffice. Level two provides a diagnostic collision. |
| Integration | `CMFieldOfDefinition` does not appear in `docs/one-proof/kinds.tsv` or `docs/one-proof/OPEN.md` at the merge. No discharge count, spec, or autofold dry run applies. |

- VERIFIED (source): Tau Ceti supplies the split-prime criterion
  `ncard_primesOver_ringClassField_eq_finrank_iff`. For inclusion only, it suffices
  to compare Frobenius at rational primes that split in the quadratic field and
  whose primes there split completely in the ring class field. This asks for the
  diagonal Kronecker congruence and excludes a finite set of primes separating
  conjugates. No selection of an oriented congruence factor is needed.
- SPECULATIVE (formal roadmap): count cyclic self-isogenies at the least nontrivial
  cyclic degree to recover the trace parity of the multiplier order. This uses
  the analytic product with multiplicities, the inverse index-to-lattice
  dictionary, and a separate argument for the two orders with extra units.
- VERIFIED (build): the first serialized import build reached the normalized
  curve's affine and overlap modules. Several queued imports were stopped by
  the load guard (exit 77); the run was held while the one-minute load was
  above 150. Previously built objects remain available for the resumption.
- VERIFIED (Lean): `Frobenius.lean` compiled using `lake env lean`. In a
  field the diagonal Kronecker factors force `x ^ p = x`; separating
  reductions for each automorphism of the overfield fixing the proposed
  subfield imply membership by Galois correspondence. Both theorems use
  only `propext`, `Classical.choice` and `Quot.sound`.
- VERIFIED (Lean): `Diagonal.lean` compiles with the three standard axioms.
  Diagonal evaluation specializes both slots; embeddings preserve the
  multiplicity of the diagonal root. A cyclic self-isogeny of nonsquare
  degree gives a monic integral equation, and every quadratic norm
  polynomial of negative discriminant has a value between consecutive
  positive integer squares.
### Lattices and cyclic quotients

VERIFIED with the guarded local Lean check: `Lattices.lean` constructs period pairs from invertible fractional ideals, proves scale invariance, and shows that the singular modulus depends only on the Picard class. `Cyclic.lean` proves the rank-two primitive sublattice quotient criterion by Smith normal form. Each new theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

### Kronecker congruence

VERIFIED (Lean): `Kronecker.lean` proves `kroneckerCongruence_of_prime` for the existing vendored definition, and `pow_eq_of_modularPolynomial_diagonal_root` for any characteristic-`p` residue field. It reduces the integral Laurent-series relation, applies characteristic-`p` Frobenius and transcendence, then uses symmetry, monicity and degree to identify the entire polynomial. All axiom checks returned only `propext`, `Classical.choice`, and `Quot.sound`.

### Specialized coset product

VERIFIED (Lean): `Factorization.lean` proves the product with multiplicities at every analytic specialization. For transcendental parameters, coincident translates would give a nonzero quadratic relation over ℚ; the vanishing coefficient case forces the two triangular representatives to agree. The monic degree count at such parameters is extended by density and continuity. `CosetLattice.lean` constructs a cyclic sublattice for each specialized root, proves surjectivity of analytic j, and transfers a detected cyclic self-isogeny degree to every embedded conjugate. All declarations checked with the three standard axioms.

### Algebraic integrality

VERIFIED (Lean): `Integrality.lean` proves `singularModulus_isIntegral` for every proper invertible ideal in an imaginary quadratic order. The integer index of a scaled sublattice equals the real determinant of multiplication, i.e. squared complex norm. The basis `[1,ω]` and invertibility show that a scalar `n+ω` is primitive in the ideal's multiplier ring. The nonsquare norm lemma and the cyclic quotient criterion then give the monic equation. The same file verifies the norm identity for principal integral ideals and the prime-level diagonal equation for any order multiplier of prime norm. The axiom checks returned only `propext`, `Classical.choice`, and `Quot.sound`.

