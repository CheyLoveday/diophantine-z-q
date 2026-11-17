import ZInQKernel.Contrib.OneProof.DeRhamPrint
import ZInQKernel.Contrib.OneProof.AxSenTate
import ZInQKernel.Contrib.OneProof.TateTwistInvariants

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
#check @DeRhamPrint.BdRInvariantsPrinted
#check @thetaPlusCp_bdrPlusMap
#check @exists_hensel_lift
#check @hensel_lift_natural
#check @thetaAlg
#check @sPlus
#check @isUnit_of_thetaAlg_ne_zero
#check @henselian_thetaAlg
#check @range_gfToGqp_eq
#check @fieldF
#check @phiF
#check @finrank_fieldF
#check @qpToBdR_eq
#check @bdrPlusMap_ofLoc
#check @locMap_algebraMap
#check @DeRhamPrint.TDict.xe_not_mem_sq
#check @DeRhamPrint.TDict.plus
#check @BdrKer.Cp.isDiscreteValuationRing_BDeRhamPlus
#check @BdrKer.Cp.isFractionRing_BDeRham
#check @ZInQ.Contrib.CloudB3W11.axSenTate_proof
#check @ZInQ.Contrib.CloudB3W11.tateTwistInvariants_proof
#check @thetaPlusCp_zp_eq
#check @IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
#check @cyclotomicCharacter.spec
example (p : ℕ) [Fact p.Prime] (i : ℕ) : HasEnoughRootsOfUnity (PadicAlgCl p) (p^i) := inferInstance
