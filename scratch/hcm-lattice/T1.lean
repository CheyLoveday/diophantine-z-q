import ZInQKernel.Contrib.OneProof.ShimuraMainCM
open scoped PeriodPair
example (L : PeriodPair) (z : ℂ) (hP'd : DifferentiableAt ℂ ℘'[L] z) :
    HasDerivAt (fun w => ℘'[L] w ^ 2) (2 * ℘'[L] z * deriv ℘'[L] z) z := by
  have := hP'd.hasDerivAt.mul hP'd.hasDerivAt
  convert this using 1
  · funext w; ring
  · ring
example (L : PeriodPair) (z : ℂ) (hP'd : DifferentiableAt ℂ ℘'[L] z) :
    HasDerivAt (fun w => ℘'[L] w ^ 2) (2 * ℘'[L] z * deriv ℘'[L] z) z := by
  have := (hasDerivAt_pow 2 (℘'[L] z)).comp z hP'd.hasDerivAt
  convert this using 1
  · rfl
  · push_cast; ring
