import ZInQKernel.Contrib.OneProof.BergerComparison.Transport
import ZInQKernel.Contrib.OneProof.BergerComparison.ResidueLog
import ZInQKernel.Contrib.OneProof.BergerComparison.FrobeniusGenerator

open ZInQ.Manuscript.BergerComparison

#print axioms isAdmissibleT_of_equivariant
#print axioms isAdmissibleT_fontaine_iff
#print axioms isAdmissibleT_paper_iff
#print axioms bergerPaperStComparison_of_frobenius
#print axioms isPstFBasis_of_paper
#print axioms exists_pLog
#print axioms pLog_spec
#print axioms pLog_zero
#print axioms exists_residue_factors
#print axioms logXi_mem_amax
#print axioms residueLog_mem_amax
#print axioms residueLog_mul_kernelUnit
#print axioms logSmallTeich_mem_amax
#print axioms coordinateFromUnit_adjoin_eq
#print axioms frobenius_xi_add_neg_pow_dvd
#print axioms frobenius_xi_div_p_mem_acris
#print axioms eval₂_wittFrobenius_mem_acris

-- Also check private lemmas and fail the check on any extra axiom.
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modulePrefix := `ZInQKernel.Contrib.OneProof.BergerComparison
  let mut checked : Nat := 0
  for (name, info) in env.constants.map₁.toList do
    unless (match info with | .thmInfo _ => true | _ => false) do continue
    let some idx := env.getModuleIdxFor? name | continue
    unless modulePrefix.isPrefixOf env.header.modules[idx.toNat]!.module do continue
    let ax ← collectAxioms name
    unless ax.all (fun a => a == `propext || a == `Classical.choice || a == `Quot.sound) do
      throwError "{name} has unexpected axioms: {ax}"
    if isPrivateName name then
      logInfo m!"'{privateToUserName name}' (private) depends on axioms: {ax.qsort Name.lt |>.toList}"
    checked := checked + 1
  unless checked ≥ 26 do throwError "Missing imported Berger comparison theorems"
  logInfo m!"Checked the axiom allowlist for {checked} theorems."
