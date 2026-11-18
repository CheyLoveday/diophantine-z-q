import ZInQKernel.Contrib.OneProof.RC.Even.Membership
import ZInQKernel.Contrib.OneProof.RC.Rings.LambdaHalfCoeff

/-!
# Lane RC22 (glue sweep), even share: lane RC11's coefficient model of `Λ` and `Λ[1/2]` is the
# genuine one

Lane RC11 models `Λ = ℤ₂[[t]]` and `A = Λ[1/2]` inside `ℚ₂[[t]]` by coefficients (its DEPARTURE
D1; `InLam u`: all coefficients in `ℤ₂`; `InLamHalf u`: bounded denominators, tex 6835–6843,
7600–7610). Lane RC20 builds the genuine rings (`Uniform.Lambda = PowerSeries ℤ_[2]`,
`Uniform.LambdaHalf = Localization.Away 2`) with the coefficientwise embeddings
`Rings.lambdaToPowerSeries` and `Rings.halfToPowerSeries` (injective), and PROVES that the image of
`Λ[1/2]` is exactly the series with bounded denominators (`Rings.mem_range_halfToPowerSeries_iff`).
So lane RC11's memberships `InLam`, `InLamHalf` — in (3.2) (`EvenScalar32`), in the field
`charEval_mem` of `EvenFamilyOutput` and in (E.5) — are memberships in the genuine `Λ` and
`Λ[1/2]`:

* `inLam_iff_mem_range` — `InLam u ↔ u ∈ range (Λ → ℚ₂[[t]])`;
* `inLamHalf_iff_mem_range` — `InLamHalf u ↔ u ∈ range (Λ[1/2] → ℚ₂[[t]])`.

This identifies the model; it does not discharge the GLUE (Krull: `A` is the intersection of its
height-one valuation rings, tex 7590–7592) inside the ELLIOT field `charEval_mem`. All results
here are `PROVED`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.GlueSweep.Even

/-- **Lane RC11's `InLam` is membership in the genuine `Λ = ℤ₂[[t]]`** (PROVED; tex 6835–6843):
`u ∈ ℚ₂[[t]]` has all coefficients in `ℤ₂` iff it is in the image of lane RC20's coefficientwise
embedding `Rings.lambdaToPowerSeries : Λ → ℚ₂[[t]]`. From lane RC11's `inLam_iff`. -/
theorem inLam_iff_mem_range (u : PowerSeries ℚ_[2]) :
    ZInQ.Manuscript.RC.Even.InLam u ↔ u ∈ ZInQ.Manuscript.RC.Rings.lambdaToPowerSeries.range := by
  rw [ZInQ.Manuscript.RC.Even.inLam_iff, RingHom.mem_range]
  rfl

/-- **Lane RC11's `InLamHalf` is membership in the genuine `Λ[1/2] = Λ_2`** (PROVED;
tex 6841, 7591–7610): `u ∈ ℚ₂[[t]]` has bounded denominators (`2^e u ∈ ℤ₂[[t]]` for some `e`) iff
it is in the image of lane RC20's embedding `Rings.halfToPowerSeries : Λ[1/2] → ℚ₂[[t]]` of the
genuine localization `Localization.Away (2 : Λ)`. From lane RC20's
`mem_range_halfToPowerSeries_iff` and `‖2^e x‖ = 2^{-e} ‖x‖` (lane RC20's `norm_two_padic`). -/
theorem inLamHalf_iff_mem_range (u : PowerSeries ℚ_[2]) :
    ZInQ.Manuscript.RC.Even.InLamHalf u ↔
      u ∈ ZInQ.Manuscript.RC.Rings.halfToPowerSeries.range := by
  rw [ZInQ.Manuscript.RC.Rings.mem_range_halfToPowerSeries_iff]
  unfold ZInQ.Manuscript.RC.Even.InLamHalf
  refine exists_congr fun e => forall_congr' fun n => ?_
  rw [norm_mul, norm_pow, ZInQ.Manuscript.RC.Rings.norm_two_padic, inv_pow,
    inv_mul_le_iff₀ (by positivity), mul_one]

end ZInQ.Manuscript.RC.GlueSweep.Even
