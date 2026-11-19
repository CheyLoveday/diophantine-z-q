import Research.DerivativeSwitch.Coordinate

/-!
# The terminal cofactor bound

The class and the scaled functional row keep their original integral
coefficients. A single cofactor detects the denominator of their coordinate.
-/

namespace Research.DerivativeSwitch.ScalarRatio

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- Over a DVR this gives the lower bound `-a-b` when `scale` has valuation
`a` and the chosen cofactor has finite valuation `b`. The integral product
identity includes the case of zero row or coordinate. -/
theorem scaled_coordinate_mul_cofactor_mem (R : Subring K) (D : Matrix n n K)
    (z row : n → K) (u scale : K) (hu : HasCoordinate D z row u)
    (hz : ∀ i, z i ∈ R) (hrow : ∀ j, scale * row j ∈ R) (i j : n) :
    scale * u * D.adjugate i j ∈ R := by
  have h := congrArg (fun M : Matrix n n K => M i j) hu
  change z i * row j = u * D.adjugate i j at h
  rw [mul_assoc, ← h, mul_left_comm]
  exact R.mul_mem (hz i) (hrow j)

end Research.DerivativeSwitch.ScalarRatio
