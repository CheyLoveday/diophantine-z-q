# bdr-inv results log

Target: `DeRhamPrint.BdRInvariantsPrinted` (ZInQKernel/Contrib/OneProof/DeRhamPrint.lean:70), used verbatim by import.
Base fe2f0d4a5 (wip/leaf-fold33b). Build tree copied (reflink) from ~/dzq-wt/javanpeykar-direct (same HEAD).

## Inputs found in the import closure of DeRhamPrint (VERIFIED, Probe.lean #check)
- `thetaPlusCp_bdrPlusMap` (θ⁺ equivariant), `exists_hensel_lift`, `hensel_lift_natural`, `thetaAlg`, `sPlus`,
  `henselian_thetaAlg`, `isUnit_of_thetaAlg_ne_zero` (G9 copies in the OneProof chain, namespace ZInQ.Contrib.G9).
- `range_gfToGqp_eq`, `fieldF`, `phiF`, `finrank_fieldF`, `qpToBdR_eq`, `bdrPlusMap_ofLoc`, `locMap_algebraMap`.
- TDict: `RootSystem`, `eps`, `xe`, `xe_not_mem_sq`, `plus`, `mkSeq`.
- KerTheta: `isDiscreteValuationRing_BDeRhamPlus`, `isFractionRing_BDeRham`, `ker_fontaineTheta_Cp`.
- `ZInQ.Contrib.CloudB3W11.axSenTate_proof : AxSenTate`, `tateTwistInvariants_proof : TateTwistInvariants`
  (imports ZInQKernel.Contrib.OneProof.AxSenTate / TateTwistInvariants, both import OneProof.H.TailS: compatible).

## Compile log
- 00:50 BdRInv.lean §1 (roots of unity zq in ℚ̄_p, RootSystem Zq, cpAct_zq via cyclotomicCharacter.spec): OK.
- 00:52 §2 (rhoC/rhoO/rho, untilt_rho, preTiltMap_eps: σ(ε) = ε^{a_m} ρ^{p^m}), §3 (thetaPlusCp_plus, bdrPlusMap_teich): OK.
- 00:55 §4 (T = xe Zq, T = ξ·v with v a unit, irreducible_T, teich_sub_one bound, bdrPlus_T_approx): OK after 2 rw fixes.
- 01:04 §4-§6 (bdrPlus_T: θ(w) = χ(σ); tate_step; key: invariants are units of B_dR^+; bdRInvariantsPrinted_proof):
  OK; `#print axioms BdRInv.bdRInvariantsPrinted_proof` = [propext, Classical.choice, Quot.sound]. VERIFIED.
- 01:15 ZInQKernel/Contrib/OneProof/BdRInvariants.lean (new file, copy of scratch):
  `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.BdRInvariants`
  success (16039 jobs; new module 54 s). VERIFIED.
- 01:16 `#discharges` (Discharges.lean): DISCHARGES [OpenResearchLeaves39.bdRInvariantsPrinted] by
  BdRInv.bdRInvariantsPrinted_proof, still assumes [], axioms standard. VERIFIED (discharges-output.txt).
- 01:16 `autofold.py scratch/bdr-inv/autofold.json --dry-run`: strict 16/15 on 31 -> 16/14 on 30; strictest
  16/15 -> 16/14. Dry-run module (count line stripped) compiles; sixContactMin_of_open58 axioms standard. VERIFIED.

## Result
`DeRhamPrint.BdRInvariantsPrinted` PROVED outright (statement imported verbatim), no new leaf, no open field used.
