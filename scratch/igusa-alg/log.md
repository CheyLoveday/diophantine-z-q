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
- Core.lean COMPILES (VERIFIED, 6 s): `PE` expressions, `E` (block esymm) and memoized `EV`,
  `Data.gen_eq_zero` (homogeneous identity of degree 4k over every CommRing from: blocks homogeneous of
  degrees 4/8, rhs homogeneous 4k, `genAbs 1 1 1 1 < N`, `genFast 1 N N^D N^{D²} = 0`, D = 4k+1).
  Proof: `IsHomogeneous` via syntactic `PE.hd`; Kronecker map `kron D` injective on homogeneous
  polynomials of degree D−1 (`kron_eq_zero`, base-D digits); coefficient majorant `Maj` (abs-coefficient
  expression); `eq_zero_of_eval_eq_zero_of_coeff_lt` (|coeffs| ≤ M < N, p(N) = 0 ⇒ p = 0, via divX).
- Inst.lean (Core + generated data) COMPILES (VERIFIED): `gen3_eq_zero` … `gen9_eq_zero`, the seven
  s-identities over every CommRing, each from `decide +kernel` side conditions; whole file 8 s, 7.2 GB;
  axioms [propext, Classical.choice, Quot.sound].
- Bridge.lean (Mathlib only; verbatim copies of theta-glue's definitions from gen/alg_prefix.lean and
  of `PkgI1.Char2`, `PkgI1.evenChars` from LPrefix, namespace ThetaGlueAlg) COMPILES (VERIFIED):
  `igusaAlg3` … `igusaAlg9 : IgusaAlg k`, no sorry, axioms [propext, Classical.choice, Quot.sound];
  1 min 55 s, peak 11.2 GB. Bridge: `esymmL_blocks` (pairing), `blocks_eval`, `psi4T_eq`, `psi6T_eq`,
  `chi10T_eq`, `chi12T_eq` (ring, degree ≤ 24 in U), `rhsK_eq` (ring over atoms), `igusaAlg_of_data`.
