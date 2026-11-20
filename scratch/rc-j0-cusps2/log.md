# Results

- Base: `dd5d7c7e4aa483cac5b1fd2ddc233e8eacb25181`. Prior proof reduces all cusps of nonzero quadratic weight to the orbit of zero. The prior comparison still needs a limit in the complex scheme topology.
- `LaurentLimit.powerSeries_analytic_sum` (namespace `J0Cusps`): one convergent sum of the power-series coefficients at a nonzero argument gives an analytic sum in a neighborhood of zero with value its constant coefficient.
- `J0Cusps.tendsto_powerSeries_eval`: along any nontrivial filter with parameter tending to zero, values represented by the power series tend to its constant coefficient. Standalone `lake env lean` and both axiom audits passed.
- `J0Cusps.exists_primitive_triangular`: an integral determinant-`N` matrix with a primitive bottom row is `g * !![a,b;0,d]` with `g ∈ SL₂(ℤ)`, `a*d=N`, `b<d` and `gcd(a,b,d)=1`. Standalone `lake env lean` and axiom audit passed.
