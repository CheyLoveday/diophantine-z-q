# igusa-alg results log

- Base: b5ff0474 + merge of origin/wip/theta-glue (336ec1fd).
- py/sforms.py (VERIFIED, exact, sympy 1.14 via `uv --offline`): with s_i = U_i², every identity
  IgusaAlg k (k = 3..9) holds as an identity in Q[s0..s3] of degree 4k after grouping the ten θ⁸ into
  four singletons y_{00,b} and three pairs {(01,00),(01,10)}, {(10,00),(10,01)}, {(11,00),(11,11)}
  (block (y+y', yy') is a polynomial in s). Ψ4 = 4ψ4, Ψ6 = 4ψ6, X10 = ∏θ² = −2¹⁴χ10, X12 = 2¹⁷·3·χ12
  have 11, 24, 48, 85 terms in s. Integer forms: D_k e_k = Σ n·Ψ4^i Ψ6^j X10^l X12^m with
  D = 432, 6912, 3456, 186624, 5184, 1728, 216 for k = 3..9 (py/sforms.py output).
- Kernel grid evaluation (SpeedTest.lean, generic CommRing evaluation at ℤ): 2000 grid points for k = 9
  hit a kernel deterministic timeout after 4 min at 38 GB (VERIFIED). Grid/simplex interpolation not viable.
- Kernel single-point Kronecker evaluation (VERIFIED): Gen₉(1, N, N^37, N^(37²)) = 0 with N = 2^75
  (values ~3.8·10⁶ bits) checked by `decide +kernel` in ~2 s (whole file 6 s, 7 GB); the same check
  with D₉ changed from 216 to 217 fails (kernel type mismatch), so the evaluation is genuine.
  Plan: Kronecker substitution + coefficient majorant + base-N digit uniqueness.
