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

## Step 0 — Model.lean compiles. VERIFIED
- `exists_metrizedModel (hdim : E.dim = 1) (𝒢 : GroupModel E L) : ∃ M : MetrizedModel E L 1, M.model = 𝒢`
  from `ZInQ.HeightGlue.metrizationOfUniformization` + `ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists`
  + `HDec.CMBranch.CMjBridges.uniformization_exists` (T35, proved in tree).
- T35 audit (#print axioms, VERIFIED):
  'HDec.CMBranch.CMjBridges.uniformization_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
  'ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists' depends on axioms: [propext, Classical.choice, Quot.sound]
- `abVarFunctionFieldGenusOne` is proved (ZInQKernel/Contrib/OneProof/JDescent4Genus.lean:14), so the short model of
  JDescent5Sections is unconditional.
- NOTE: from 21:2x the sandbox hook blocks systemd-run; Lean runs continue as LEAN_NUM_THREADS=4 nice lake ... (one at a time).

## Step 4 (second bullet) — Discriminant.lean compiles. VERIFIED
- `weierstrassCurve_ofTau_Δ (τ : ℍ) : (PeriodPair.ofTau τ).weierstrassCurve.Δ = CMBranch.discAn τ`
  (vendored kw_discriminant_ofTau_eq + Mathlib discriminant_eq_E₄_cube_sub_E₆_sq + discriminant = η^24).

## Step 2 (definitions) — ShortModel.lean compiles. VERIFIED
- `ShortData A` (bundles abVar_shortSections_of_genusOne output), `shortData A hdim` (choice).
- `D.W := ⟨0,0,0,a,b⟩`, `W_Δ_ne_zero`, `fXY = −X/Y`, `ord_fXY = 1`, `tE` (germ in 𝒪_{E,0} with image −x/y),
  `tE_mem_maximalIdeal`, `bcProj`, `bcProj_identity` (projection E_L → E fixes identity), `tL`, `tG 𝒢 ∈ 𝔪_ξ`,
  `etaW 𝒢 := 𝒢.wedge ![tG 𝒢]`.

## Assembly.lean compiles. VERIFIED
- `ArchIdentity : Prop` (steps 1, 2-nonvanishing, 4): open sub-step at this point.
- `Step7 : Prop`.
- `finrank_mul_modelHeight_eq_exact (hA : ArchIdentity) ...` (step 6 exact formula, any smooth model).
- `cmHeight62_of_step7 (hA : ArchIdentity) (h7 : Step7) : HDec.CMBranch.CMHeight62`.
- Tree facts found (VERIFIED, read): JDescent2 `shortWeierstrassComparison_of_doublePole` +
  JDescent5 `abVar_period_abscissa_even`, `abVar_evaluatedPole_of_order`, `abVar_period_mem_punctured` give, for
  any IsPeriodAt-uniformization (Λ,Φ,s) of E at σ|K, u ≠ 0 with x(Φ(sz)) = u²℘(z), y(Φ(sz)) = u³℘'(z)/2 off the
  lattice (CM hypotheses of CMPeriodShortCoordinatesDoublePole unused in its proof).
