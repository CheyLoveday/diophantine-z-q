# Inner-limit arithmetic contributions: classification of the contracts

This directory contains the arithmetic side of the inner limit along moving derivative primes in
the proof of Theorem 5.3 (manuscript lines 4391–4451, 4748–4907, 4976–5135). The classification
below follows the independent review of the first round and states which declarations are
genuine producers and which are conditional adapters. A conditional adapter proves its conclusion
from inputs that are not themselves produced here; such inputs remain open obligations and must
not be counted as discharged arithmetic.

## Genuine producers (no arithmetic input beyond the stated prints)

* Actual continuous cochains and their evaluation, cocycle and coboundary identities
  (`evalOne`, `evalOne_mul`, `evalOne_d_zero`, `evalTwo_d`), tame coordinates of actual
  one-cocycles (`tameCoord`, `tameCoordH1`), the actual unramified condition in tame coordinates
  (`tameCoord_urCondCocycle`), localization at a prime outside `S` (`tameCoord_localizeCocycle`).
* Moving labels from any sequence of primes outside `S` (`MovingLabel.ofPrimes`), and the limit
  Frobenius in the compact group `G_{K,S}` (`MovingLabel.limitFrob`).
* Actual derivative primes by finite Chebotarev at every stage (`DerivativePrimes`,
  `exists_derivativePrimes`), with `ℓ_i ≡ −1 mod 2^i` (`DerivativePrimes.ell_mod`), the
  determinant of the conjugation (`det_tateMatrix_conj`), and convergence of the rational
  Frobenius elements (`DerivativePrimes.tendsto_frob`).
* The conjugation in the coefficient basis: `tateSEquiv`, `rhoK`, `rhoKMatrix`, `conjMatrixK`,
  `conjTate_eq_rhoK`, `conjMatrix_eq_conjMatrixK` (the fibre duality's `conjMatrix` is the
  specialization of `ρ_T(τ)`), `det_conjMatrixK`, `conjMatrixK_sq`.
* Flatness and freeness of the actual stage cochain and Selmer cochain modules
  (`StageFlat.lean`).
* `StageInputs.lean`, from the prints named there: finiteness of the cohomology of the actual
  Selmer complexes with finite coefficients, at every stage for the actual module `M_i`
  (`galoisSelmerCohomologyFinite_of_prints`, `stageSelmerCohomologyFinite`, from Milne I.2.3 and
  I.4.10); chain-level reciprocity of the trace on the compact cone (`trace_reciprocity`,
  `trace_localization_of_cocycle`); Nekovář's global duality and Selmer duality at the stage
  `A_i` for `M_i`, `M_i(α⁻¹)` and the Weil pairing (`stageGlobalDuality`, `stageSelmerDuality`,
  `exists_stageTrace`, from Nekovář 5.4.1 and 5.4.3).
* `ArithLabel.lean`: one compatible arithmetic label (`CompatibleArithmeticLabel`) for the curve
  `E`, its base change `E_K`, the conjugation, the derivative primes and the stage primes with
  residue size `ℓ_i²`; the twisted derivative congruence (`CompatibleArithmeticLabel.htriv`) and
  the realized derivative matrices with `J = conjMatrix` at every fibre are derived from it.

## Conditional adapters (inputs are open obligations)

* `realizedDerivative`, `realizedDerivativeK`, `RealizedLabel.derivative`: the input `htriv`
  (the Frobenius of the stage prime acts trivially on `𝕋 / I_i 𝕋`) is equivalent to the
  stage-matrix congruence `phi_congr`; it is assumed, not derived. `realizedDerivativeK_of_match`
  replaces it by `FrobeniusMatchesLabel` and the character constraint, which are still inputs.
  Not bound by these constructors: `W = E.baseChange K`, inertness of the stage primes, residue
  size `(ℓ_i)^2` at the stage prime, and the relation between the two Frobenius families.
* `DegreeOneRealization`, `SelmerRealization`: witness contracts, not model identifications.
  Zero witnesses satisfy them, the cocycle map need not be injective, and with the cofinite and
  inertia conditions they force the relaxed image into the finite plane. They must not be used
  as the retained model comparison with the unchanged old conditions and the class/functional
  maps, which remains open.
* `detectedLimitNonquadStep`, `realizedFibreLimitNonquadStep`, `retainedNonquadStep`,
  `finPlane_le_limitRelaxed_U`, `exists_detecting_partner`: the detecting pair (`hdet`) is
  equivalent to the consumer's rank-two detection field; detection of prescribed classes at a
  compatible realized prime is not produced.
* `DegreeOneRealization.finPlane_le_U_of_signs`, `DegreeOneRealization.exists_plus_detection`:
  the conjugation `conj` and the action `T` are free parameters; they must be bound to the
  actual conjugation and the Tate action at integration, and the nonzero sign components are
  inputs.
* `exists_tameCoord_surjective`, `exists_tameCoord_surjective_at`, `innerLimit_local_surjective`:
  conditional on the local Galois group fixing the `2^i`-th roots of unity, on trivial
  coefficient action, and on chosen Frobenius and inertia elements; they are coordinate
  surjectivity helpers, not the retained local cochain comparison (inverse maps, degree zero and
  two, cup product, orientation).
* `retainedNonquadStep`: duality from the retained stage data of the fibre duality, and the
  limit diagram must be the realized one; the retained data themselves are produced elsewhere.

## Open arithmetic obligations (exact shapes in `StageInputs.lean`, `ArithLabel.lean` and
`Conjugation.lean`)

* `FrobeniusMatchesLabel` (`Conjugation.lean`; the field `frobMatch` of
  `CompatibleArithmeticLabel`): the Frobenius of the label at `q_i` is a `G_{K,S}`-conjugate of
  the restriction of `e⁻¹ Fr_i² e`. Also the field `character` (the character constraint in the
  finite quotient of the Chebotarev selection).
* `ResidualCohomologyFinite` for the stage Selmer complexes: the base-change comparison
  `k ⊗ C_cont(G, M) ≅ C_cont(G, k ⊗ M)` for discrete `M`, compatible with the Selmer cone and the
  local conditions, and finiteness of the residual cohomology of the local-condition complexes.
* `LocalDegreeTwoCoordinate` and `LocalDegreeTwoNormalized` at the stage prime: the coordinate
  `H²(K_{q_i}, M_i) ≅ M_i` oriented by the tame cup product.
* The orthogonality (`OrthogonalComplementsT`) of the actual old conditions at `A_i` with
  truncated isotropy data, the input of `stageSelmerDuality`.
* The reverse maps and both homotopies of the stage duality exist on the bounded finite free
  models (a quasi-isomorphism of bounded complexes of finite free modules is a homotopy
  equivalence); they are not asserted on the unbounded cochain complexes.
