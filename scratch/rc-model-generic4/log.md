# rc-model-generic4 results log

Base: wip/rc-model-neron 64a338f4 merged with main 29bfbc3f (merge commit 5e02195ad).

## Route for (b1)
- Vendor odd-step function-field hom with place seam:
  `WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed`.
- Vendor lift to ℂ: `PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`.
- No vendored function-field hom for the order-two Vélu step (`veluQuotient2`): only the point map
  `exists_addMonoidHom_coe_eq_veluPointMap2`.

## Compiled (QuotientFunctionField, LatticeQuotient)
- `exists_oddStep`: odd prime Vélu step of the vendored iteration induced by a function-field map whose
  place restriction is the actual Vélu point map (fixed centred gates `gate`).
- `exists_quotientSeam_of_steps`, `exists_quotientSeam_odd`: composite over the iteration; kernel = H.
- `j_eq_analyticJN_of_seam`: any such function-field map onto the period curve of ℤτ+ℤ with kernel
  ⟨u(1/N)⟩ has target j = j(Nτ) (lift z ↦ αz + c, preimage ℤτ + ℤ/N, homothety to ℤNτ + ℤ).
- `pairQuotientJ_analyticCyclicPair_of_odd`: (b1) for odd N. Axioms: propext, Classical.choice, Quot.sound.
- Missing for even N: the order-two step function-field map (`veluQuotient2`) with place seam.

## (b1) closed for every N (OrderTwoStep, LatticeQuotient)
- `twoFFHom`: order-two Vélu map of function fields (x ↦ x + G/(x−x₀), y ↦ y − G(a₁(x−x₀)+y−y₀)/(x−x₀)²);
  `twoFFHom_finiteAlong`, `twoFFHom_isIntegral`, `twoFFHom_seam` (place restriction = `veluPointMap2`).
- `stepSeam_two`, `exists_quotientSeam` (all n ≥ 1).
- `pairQuotientJ_analyticCyclicPair : pairQuotientJ (analyticCyclicPair τ) = X0Model.analyticJN N τ`
  for every τ ∈ ℍ, N ≥ 1. Axioms: propext, Classical.choice, Quot.sound. No sorry.

## (b2), (b3) compiled (GenericSpecialization, Density)
- `dense_transcendental_analyticJ : Dense {τ : ℍ | Transcendental ℚ (X0Model.analyticJ τ)}`.
- `pairQuotientJ_rationalPoints_comp`: pairQuotientJ ∘ rationalPoints commutes with σ : K₁ →ₐ[ℚ] K₂
  (alg. closed, char 0), via the vendored base-change lemma on the short cover.
- `pairQuotientJ_rationalPoints_of_transcendental`: x(rationalQuotientCoordinate) = pairQuotientJ(rationalPoints x)
  when x(J) is transcendental (x factors through Kbar via ι : ℚ(j) → ℂ, j ↦ x(J)).
- `rationalPoints_rationalPointAtParameter_of_transcendental`: item 1 at every τ with j(τ) transcendental.
