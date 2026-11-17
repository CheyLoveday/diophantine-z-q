# lcal-one results log

Task: prove `ZInQ.Contrib.TYZDecomp.TYZLcalOne : lcalSq 1 = 1` (Leaves.lean:266).

## Setup (2026-11-16 22:20)
- Merged origin/main (no change) and origin/wip/tyz-genus (clean).
- Copied tyz-genus's `.lake/build`; `lake build` of Lcal, JacobiLambdaDeriv, WeilJacobi, EtaTheta, TYZThm11Genus: OK (9 min).

## Normalizations (VERIFIED, read)
- `lcalSq 1 = lValOne 1 / (2^(0-3) * omegaTYZ 1)`, `omegaTYZ 1 = 2 * omegaInt`; tree lemma
  `TYZLcal.lcalSq_one : lcalSq 1 = lValOne 1 / (omegaInt / 4)`. So the target is `lValOne 1 = omegaInt / 4`,
  `omegaInt = ∫_{(1,∞)} dx/√(x³−x)` (= lemniscate constant ϖ ≈ 2.62206).
- `TYZChain.Lcal.lValOne_one_eq : lValOne 1 = Σ_{j ∈ (Fin 4)²} cU j * (1/4) * (π * gaussLambda (j/4) 1)`,
  `gaussLambda a b 1 = mellin (gaussTheta a b) 1 = ∫_{(0,∞)} gaussTheta a b`.

## Route (plan)
1. (A) `lValOne 1 = 2π ∫_{(0,∞)} fC(i t) dt`, `fC = η(4τ)²η(8τ)²` (block decomposition of the lattice
   theta kernels + grouping by the norm + gz-theta's `etaThetaIdentity`).
2. (B) On the imaginary axis `x(it)`, `y(it)` (x0-32's eta model, `y² = x³ + 4x`) are real, `y < 0`, `fC > 0`,
   `x' = −4π fC y` (x0-32 `EtaModelDifferential`, proved by gz-weil), `x → 2` as `t → 0+` (theta S-law),
   `x → ∞` as `t → ∞`. With `u = x/4 + 1/x` (the 2-isogeny `32a1 → y² = x³ − 16x`, rescaled to `C₁`):
   `u'/√(u³ − u) = 8π fC`, `u: (0,∞) → (1,∞)`. FTC on `(0,∞)` for `K(u(t))`, `K(u) = ¼∫_u^∞ dv/√(v³−v)`:
   `2π ∫ fC(it) dt = K(1) = omegaInt/4`.
