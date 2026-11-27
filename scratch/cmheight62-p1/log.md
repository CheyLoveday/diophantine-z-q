# cmheight62-p1 results log

Base: 96f3a26b70770167ba4e9005a601a737dc618133 (confirmed `git rev-parse HEAD`).

## Order-of-work 1: builds
- `lake build ZInQKernel.Contrib.RC53Assist.HodgeLineBinding.All ZInQKernel.Contrib.RC53Assist.HodgeLatticeIdeal.All`:
  Build completed successfully (10688 jobs), 4m58s. Only module-system import warnings. VERIFIED.
- Probe: CMHeight62 is stated over `_root_.ZInQ.DefFaltings.{GroupModel, stableFaltingsHeight}` (same types as
  HodgeLatticeIdeal); `IsPeriodAt` uses `HDec.LeafAdopt.abVarEquiv`. VERIFIED (#print).

## Archimedean.lean (steps 3, 5, 6 abstract) — compiles (lake env lean, no errors). VERIFIED
- `exists_mem_coefficientFractionalIdeal_ne_zero`
- `finrank_mul_modelHeight_eq` (step 3): d·h(M) = −log N(Jη) − Σ_σ log ‖η‖_σ, any M : MetrizedModel E L 1, any η ≠ 0.
  Proof: a ∈ Jη nonzero, a•η ∈ lattice, degreeAt(a•η), secIndex_detLattice_eq_norm_div, product formula.
- `sum_log_norm_eq` (step 5): Σ log|σD| = log|N_{L/ℚ}D|.
- `finrank_mul_modelHeight_eq_summand62` (step 6 abstract): from per-σ hypothesis
  |σD|·‖η‖_σ^12 = |discAn τ_σ|·(Im τ_σ)^6, d·h = Σ summand62 + (1/12)(log|N D| − 12 log N Jη).
