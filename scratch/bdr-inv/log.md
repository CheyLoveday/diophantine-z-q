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
