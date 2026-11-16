import ZInQKernel.Contrib.OneProof.PeriodOdd
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
open UpperHalfPlane Filter Topology
open ZInQ.GZHeegner (tay coeff_tay tay_congr tay_add tay_sub tay_mul tay_const tay_pow tay_cmul tay_X_pow RegularAt)
example (Gx Gy : ℂ → ℂ) (hx : AnalyticAt ℂ Gx 0) (hy : AnalyticAt ℂ Gy 0) (A1 : ℂ) (kx : ℕ) :
    AnalyticAt ℂ (fun w => A1 * Gx w * Gy w * w ^ (2 * kx)) 0 := by fun_prop
example (Gx Gy : ℂ → ℂ) (hx : AnalyticAt ℂ Gx 0) (hy : AnalyticAt ℂ Gy 0) (A1 : ℂ) (kx : ℕ) :
    tay (fun w => A1 * Gx w * Gy w * w ^ (2 * kx) - Gy w ^ 2) = PowerSeries.C A1 * tay Gx * tay Gy * PowerSeries.X ^ (2 * kx) - tay Gy ^ 2 := by
  rw [tay_sub (by fun_prop) (by fun_prop)]
  rw [tay_mul (by fun_prop) (by fun_prop), tay_mul (by fun_prop) (by fun_prop), tay_mul (by fun_prop) (by fun_prop), tay_const, tay_X_pow, tay_pow hy]
example (w : ℂ) (u t B : ℂ) (kx ky : ℕ) (h : (u*t)^(3*kx) = 1) : u^(3*kx+2*ky) * (B * t^(3*kx)) = u^(2*ky) * B := by
  linear_combination (u^(2*ky) * B) * h
