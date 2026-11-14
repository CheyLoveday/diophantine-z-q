# theta-glue results log

## 2026-11-14

- Setup: `.lake/build` and `lean/.lake/build` copied from the t5-glue worktree (its ZInQKernel tree differs
  from this base only in TailZ10-Z15, Main, Contrib/TYZGenus/CM.lean, none upstream of TailA).
  `lake env lean scratch/theta-glue/T0.lean` (imports `ZInQKernel.OneProof.H.TailA`) COMPILES, 14 s.
- No sympy available (no `~/pyenv`, no network): exact algebra uses `py/poly.py` (pure-python
  multivariate polynomials over Q, `fractions`).
- `py/dup_num.py` (VERIFIED, computed, double precision, 5 random Ω ∈ 𝔥₂, all 10 even chars):
  duplication formula in the project's convention (`thetaConst m Ω = Σ_n exp(πi vᵀΩv + πi v·b)`,
  `v = n + a/2`): `θ[a;b](Ω)² = Σ_{c ∈ {0,1}²} (−1)^{(c⊕a)·b} U_c U_{c⊕a}`, `U_c = θ[c;0](2Ω)`;
  worst relative error 1.2e-15.
- `py/dup_sym.py` (VERIFIED, exact): with `θ_m² = S_m(U)` (the ten explicit quadratic forms above),
  `4 Σ_m S_m⁸ − (Σ_m S_m⁴)² = 0` in `Q[U0..U3]`. So `ThetaEightSquare` follows from the duplication
  formula by a degree-16 polynomial identity.
