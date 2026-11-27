import ZInQKernel.Contrib.OneProof.BergerComparison.SurveyTransfer

open ZInQ.Manuscript.BergerComparison

#print axioms mem_crystallineIntegral
#print axioms polynomial_mem_restricted
#print axioms frobBeforeDescent_polynomial
#print axioms maxToImage_surjective
#print axioms integralFrobenius_polynomial
#print axioms logSmallTeich_eq_logTeich
#print axioms cyclotomicCoordinate_eq_of_normalized
#print axioms exists_cyclotomic_correction
#print axioms exists_small_power_of_correction
#print axioms exists_cyclotomic_small_unit
#print axioms cyclotomicCoordinate_adjoin_eq
#print axioms pDvd_iff_coeff
#print axioms exists_restricted_limit
#print axioms restricted_isAdicComplete
#print axioms dividedPowerRestricted_isAdicComplete
#print axioms integralFrobenius_zp
#print axioms integralFrobenius_logTeich
#print axioms maximalEval_polynomial
#print axioms integralFrobenius_galois
#print axioms localizedFrobenius_integral
#print axioms localizedFrobenius_logTeich
#print axioms coefficientFrobenius_galois
#print axioms exists_maximal_denominator
#print axioms clear_maximal_log_relation
#print axioms exists_scaledInverse
#print axioms negativeLogSeries_eval
#print axioms scaledNegativeLog_coeff
#print axioms scaledNegativeLog_mod_p
#print axioms residueLog_independent_of_lift
#print axioms logSmallTeich_eq_residueLog
#print axioms logSmallTeich_mul
#print axioms xiPow_dvd_of_mod_every_pPow
#print axioms wittLogTerm_one
#print axioms pLogTerm_eq_mul_pow
#print axioms pLog_agrees_logPlus_on_overlap
#print axioms eq_zero_of_integral_log_relation
#print axioms maximalEval_relation
#print axioms pow_p_dvd_of_dvd_xi_mul
#print axioms maximalEval_zero_iff
#print axioms amax_eq_zero_of_pDvd
#print axioms exists_polynomial_mod_pPow
#print axioms restricted_to_amax_ext
#print axioms restrictedEval_polynomial
#print axioms logPTilde_notInFrac
#print axioms logPTilde_transcendental
#print axioms fontainePolynomialEmbedding
#print axioms frobeniusTransport
#print axioms bergerPaperStComparison
#print axioms bergerSurveyF_of_cyclotomic_basis
#print axioms deRhamBasis_of_isDeRhamU
#print axioms evaluateMaximalSt_val
#print axioms evaluateMaximalSt_surjective
#print axioms evaluateMaximalSt_injective
#print axioms semistableFrobenius_coeff
#print axioms semistableFrobenius_log
#print axioms semistableFrobenius_galois
#print axioms semistableFrobenius_intertwines
#print axioms pLog_add

-- Check the allowlist also on private theorems and definitions.
open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let modules := #[
    `ZInQKernel.Contrib.OneProof.BergerComparison.CoefficientFrobenius,
    `ZInQKernel.Contrib.OneProof.BergerComparison.CyclotomicBranch,
    `ZInQKernel.Contrib.OneProof.BergerComparison.CyclotomicUnit,
    `ZInQKernel.Contrib.OneProof.BergerComparison.DeRhamBasis,
    `ZInQKernel.Contrib.OneProof.BergerComparison.DividedPowerCompletion,
    `ZInQKernel.Contrib.OneProof.BergerComparison.FrobeniusTeichLog,
    `ZInQKernel.Contrib.OneProof.BergerComparison.IntegralEquivariance,
    `ZInQKernel.Contrib.OneProof.BergerComparison.LocalizedFrobenius,
    `ZInQKernel.Contrib.OneProof.BergerComparison.LogDenominators,
    `ZInQKernel.Contrib.OneProof.BergerComparison.LogLiftIndependence,
    `ZInQKernel.Contrib.OneProof.BergerComparison.LogOverlap,
    `ZInQKernel.Contrib.OneProof.BergerComparison.LogarithmRelations,
    `ZInQKernel.Contrib.OneProof.BergerComparison.LogTranscendence,
    `ZInQKernel.Contrib.OneProof.BergerComparison.MaximalEvaluation,
    `ZInQKernel.Contrib.OneProof.BergerComparison.MaximalSeparation,
    `ZInQKernel.Contrib.OneProof.BergerComparison.RestrictedEvaluation,
    `ZInQKernel.Contrib.OneProof.BergerComparison.SemistableComparison,
    `ZInQKernel.Contrib.OneProof.BergerComparison.SemistableDescent,
    `ZInQKernel.Contrib.OneProof.BergerComparison.SurveyTransfer,
    `ZInQKernel.Contrib.OneProof.BergerComparison.WittLogAdd
  ]
  let mut checked : Nat := 0
  let mut theorems : Nat := 0
  for (name, info) in env.constants.map₁.toList do
    let some idx := env.getModuleIdxFor? name | continue
    unless modules.contains env.header.modules[idx.toNat]!.module do continue
    let isTheorem := match info with | .thmInfo _ => true | _ => false
    unless (match info with | .defnInfo _ => true | _ => isTheorem) do continue
    let ax ← collectAxioms name
    unless ax.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "{name} has unexpected axioms: {ax}"
    if isTheorem then
      theorems := theorems + 1
      if isPrivateName name then
        logInfo m!"'{privateToUserName name}' (private) depends on axioms: {ax.qsort Name.lt |>.toList}"
    checked := checked + 1
  unless checked ≥ 100 do throwError "Missing imported comparison declarations"
  logInfo m!"Checked the axiom allowlist for {checked} declarations, including {theorems} theorems."
