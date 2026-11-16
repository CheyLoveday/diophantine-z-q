# t21-proof log

Base 2880fef1. Build tree copied from ~/dzq-check2 (same commit).

## Step 1: reduction (T21Reduce.lean) — VERIFIED (compiles, 6 s)
`tyzThm21At31_of_glue : BrandtValueAt3 → LcalUnitOneThree → TYZThm21At31`.
- `torsionOrder_three : torsionOrder (QNeg 3) = 6` (Mathlib `IsCyclotomicExtension.Rat.torsionOrder_eq`).
- `classSum_eq`: Cl_3 subsingleton (pid_three), class sum = f 1 (tv_eq_of_toClassGroup_eq).
- `int_eq_pm_one_of_sq`: a ∈ ℤ, a² = z, 0 < ‖z‖ < 4 → a = ±1.
Glue left: `BrandtValueAt3` (∀ admissible τ, ∀ test vector f, f 1 = ±3), `LcalUnitOneThree`
(0 < ‖lcalSq m‖ < 4 at m = 1, 3).
