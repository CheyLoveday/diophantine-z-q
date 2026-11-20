Scoped stop: the conductor-one CM field of definition gives every
`PreparedParamValue` once the canonical model of `X₀(N)` and its rational
parametrization at the fixed analytic scale are supplied. The missing
comparison is `AlgebraicParametrizationAtScale`: one morphism over `ℚ`
whose evaluation on the upper half plane agrees with the existing
`phiAn` at this `κ`.

The proof composes the CM field-valued point with the morphism. It evaluates
in the actual Weierstrass model, including infinity, and proves that
evaluation commutes with the chosen complex embedding. The conductor-one
specialization uses exactly the selector's field and form.
`missingParamValues` supplies the Stage Kummer selector input.
`gz34CompAt_of_scaledParametrization` installs the same family in the
rough (3.4) assembly without an independent `halgG`.
The conductor-`|h|` value, period rationality, and stage comparison
remain separate.

All four new Lean files pass serial `lake env lean -j1`. All eleven
theorem audits list only `propext`, `Classical.choice`, and `Quot.sound`.
The sole printed-form leaf is GLUE (unread). Tex 2915–2919 supplies the
manuscript statement; the archived Cai–Chen–Liu locator is for the trace
theorem. The separate field-of-definition locator remains to be checked.
The exact hypotheses and manuscript checks are in
`docs/research/rc-prepared-param.md`.

Final implementation and report SHA: `7761da4e67f00f09499d912b6ceb281c0a54cc38`.
